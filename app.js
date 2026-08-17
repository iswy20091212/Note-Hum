/* =========================================================
 * HumScore（ハムスコア）
 * ハミング採譜アプリ — 鼻歌をリアルタイムで五線譜に変換
 *
 * 技術構成:
 *  - Web Audio API（マイク入力 / AnalyserNode）
 *  - YINアルゴリズムによるピッチ推定（自前実装）
 *  - メディアンフィルタ + ヒステリシスによるノート補正
 *  - VexFlow による五線譜レンダリング
 *  - MIDI / MusicXML / PNG エクスポート
 *
 * v2 修正点（「歌っても反応しないときがある」問題への対策）:
 *  1. AudioContext を getUserMedia の await 前に生成し resume() を保証
 *     （Safari/iOS で suspended のまま波形がゼロになる問題を解消）
 *  2. 無音ゲートを 0.015 → 0.005 に緩和し、HUD に入力レベルを常時表示
 *  3. YIN の探索範囲を 55〜1600Hz に対応する tau に限定
 *     （高い歌声を拾えるようにしつつ、ノイズ由来の誤検出→無音化も防止）
 *  4. オンセット判定を「丸め値の連続一致」→「中央値の近接滞在」に変更
 *     （ビブラート・ポルタメントで音符が永遠に開始しない問題を解消）
 *  5. 検出ラグ分の時刻補正 + MIN_NOTE_MS 緩和（短い音符の取りこぼし防止）
 * ========================================================= */
"use strict";

/* ---------- 音符ユーティリティ ---------- */
const NOTE_NAMES = ["C","C#","D","D#","E","F","F#","G","G#","A","A#","B"];
const XML_STEPS  = ["C","C","D","D","E","F","F","G","G","A","A","B"];
const XML_ALTERS = [0,1,0,1,0,0,1,0,1,0,1,0];

function midiToVexKey(m) {
  const name = NOTE_NAMES[m % 12].toLowerCase(); // 例: "c#"
  const oct = Math.floor(m / 12) - 1;
  return `${name}/${oct}`;
}
function midiToName(m) {
  return NOTE_NAMES[m % 12] + (Math.floor(m / 12) - 1);
}
function median(arr) {
  const s = [...arr].sort((a, b) => a - b);
  const mid = Math.floor(s.length / 2);
  return s.length % 2 ? s[mid] : (s[mid - 1] + s[mid]) / 2;
}

/* ---------- 検音パラメータ ---------- */
const MIN_FREQ = 55;        // 検出下限（男性の低いハミングも拾える）
const MAX_FREQ = 1600;      // 検出上限（1200Hz だと高い歌声が無音扱いになる）
const RMS_GATE = 0.005;     // 無音ゲート（0.015 だと静かなハミングを拾えない）
const YIN_THRESHOLD = 0.2;  // YIN のしきい値（0.15 は息漏れのある声に厳しい）

/* ---------- YIN ピッチ推定 ---------- */
function yinPitch(buf, sampleRate) {
  const half = Math.floor(buf.length / 2);
  // 検出したい周波数帯に対応する tau のみ探索する。
  // 小さすぎる tau まで探すとノイズで誤った極小値を掴み、
  // 帯域外として捨てられる＝「無音扱い」の原因になる
  const minTau = Math.max(2, Math.floor(sampleRate / MAX_FREQ));
  const maxTau = Math.min(half - 2, Math.ceil(sampleRate / MIN_FREQ));

  // 1. 差分関数（CMND の正規化を正しくするため tau=1 から計算）
  const d = new Float32Array(half);
  for (let tau = 1; tau <= maxTau; tau++) {
    let sum = 0;
    for (let i = 0; i < half; i++) {
      const diff = buf[i] - buf[i + tau];
      sum += diff * diff;
    }
    d[tau] = sum;
  }

  // 2. 累積平均正規化差分関数
  const cmnd = new Float32Array(half);
  cmnd[0] = 1;
  let running = 0;
  for (let tau = 1; tau <= maxTau; tau++) {
    running += d[tau];
    cmnd[tau] = running === 0 ? 1 : (d[tau] * tau) / running;
  }

  // 3. 絶対しきい値法（意味のある tau の範囲だけ探す）
  let tau = minTau;
  let tauEst = -1;
  while (tau <= maxTau) {
    if (cmnd[tau] < YIN_THRESHOLD) {
      while (tau + 1 <= maxTau && cmnd[tau + 1] < cmnd[tau]) tau++;
      tauEst = tau;
      break;
    }
    tau++;
  }
  if (tauEst === -1) return -1; // 無音・無周期

  // 4. 放物線補間で精度向上
  const x0 = tauEst > minTau ? cmnd[tauEst - 1] : cmnd[tauEst];
  const x1 = cmnd[tauEst];
  const x2 = tauEst < maxTau ? cmnd[tauEst + 1] : cmnd[tauEst];
  const a = (x0 + x2 - 2 * x1) / 2;
  const b = (x2 - x0) / 2;
  const betterTau = a !== 0 ? tauEst - b / (2 * a) : tauEst;
  return sampleRate / betterTau;
}

/* ---------- ノートトラッカー ----------
 * ハミングの揺らぎを補正する核心部分。
 * - メディアンフィルタでピッチ軌跡を平滑化
 * - オンセットは「中央値が候補の近くに滞在」で判定（寛容＝取りこぼし防止）
 * - 音程変化は「丸め値の連続一致」で判定（慎重＝ビブラートでの分裂防止）
 * - 検出ラグ分を遡って時刻補正し、短い音符の破棄を防ぐ
 */
const MIN_NOTE_MS = 70;
const ONSET_FRAMES = 2;
const CHANGE_FRAMES = 3;
const SILENCE_FRAMES = 5;
const ONSET_TOL = 0.5; // オンセット判定の許容誤差（半音=1.0）

function createTracker(onNote) {
  return {
    win: [], midi: null, startT: 0,
    candF: null, candN: 0, silence: 0,
    feed(midiF, t, dt) {
      if (midiF === null) { // 無音
        this.silence++;
        this.win.length = 0;
        this.candF = null; this.candN = 0;
        if (this.midi !== null && this.silence >= SILENCE_FRAMES) {
          this.commit(t - SILENCE_FRAMES * dt, onNote);
        }
        return;
      }
      this.silence = 0;
      this.win.push(midiF);
      if (this.win.length > 5) this.win.shift();
      const medF = median(this.win); // 丸める前の値で判定するのがポイント
      const rounded = Math.round(medF);

      if (this.midi === null) {
        // 音符の立ち上がり: ビブラートで丸め値が毎フレーム揺れても
        // 中央値が候補の近くに留まっていれば確定させる
        if (this.candF !== null && Math.abs(medF - this.candF) <= ONSET_TOL) this.candN++;
        else { this.candF = medF; this.candN = 1; }
        if (this.candN >= ONSET_FRAMES) {
          this.midi = Math.round(this.candF);
          this.startT = t - ONSET_FRAMES * dt; // 確認＋メディアン窓のラグ分を遡る
          this.candF = null; this.candN = 0;
        }
      } else if (rounded === this.midi) {
        this.candF = null; this.candN = 0;
      } else {
        // 音程変化: 保持中のビブラートで誤分裂しないよう、
        // こちらは従来通り「丸め値の連続一致」で慎重に判定
        if (this.candF !== null && Math.round(this.candF) === rounded) this.candN++;
        else { this.candF = medF; this.candN = 1; }
        if (this.candN >= CHANGE_FRAMES) {
          const endT = t - CHANGE_FRAMES * dt;
          this.commit(endT, onNote);
          this.midi = Math.round(this.candF);
          this.startT = endT;
          this.candF = null; this.candN = 0;
        }
      }
    },
    commit(endT, onNote) {
      const dur = endT - this.startT;
      if (dur >= MIN_NOTE_MS) {
        onNote({ midi: this.midi, startMs: this.startT, durMs: dur });
      }
      this.midi = null;
    },
    flush(t, onNote) {
      if (this.midi !== null) this.commit(t, onNote);
    }
  };
}

/* ---------- リズム量子化（拍への丸め） ---------- */
const GRID = [0.25, 0.5, 0.75, 1, 1.5, 2, 3, 4]; // 16分〜全音符（拍単位）
const DUR_MAP  = { 0.25:"16", 0.5:"8", 0.75:"8", 1:"q", 1.5:"q", 2:"h", 3:"h", 4:"w" };
const XML_TYPE = { 0.25:"16th", 0.5:"eighth", 0.75:"eighth", 1:"quarter", 1.5:"quarter", 2:"half", 3:"half", 4:"whole" };
const DOT_SET = new Set([0.75, 1.5, 3]); // 付点音符

function beatsOf(ms, bpm) { return (ms / 60000) * bpm; }
function quantizeBeats(b) {
  let best = GRID[0], bd = Infinity;
  for (const g of GRID) {
    const d = Math.abs(g - b);
    if (d < bd - 1e-9) { bd = d; best = g; }
  }
  return best;
}
function largestGridLE(x) {
  let r = GRID[0];
  for (const g of GRID) if (g <= x + 1e-9) r = g;
  return r;
}

// 録音した音符列を「4/4拍子の小節に収まる音符・休符列」に変換
function buildEvents(notes, bpm) {
  const events = [];
  let cursor = 0; // 拍カーソル
  for (const n of notes) {
    const startB = beatsOf(n.startMs, bpm);
    let gap = startB - cursor;
    while (gap >= 0.25 - 1e-9) { // 隙間は休符で埋める
      const r = quantizeBeats(Math.min(gap, 4));
      events.push({ type: "rest", beats: r });
      cursor += r; gap -= r;
    }
    let remaining = quantizeBeats(beatsOf(n.durMs, bpm));
    while (remaining > 1e-9) { // 小節線をまたぐ音は分割
      const space = 4 - (cursor % 4);
      const chunk = largestGridLE(Math.min(remaining, space));
      events.push({ type: "note", midi: n.midi, beats: chunk });
      cursor += chunk; remaining -= chunk;
    }
  }
  return events;
}

/* ---------- 譜面レンダリング（VexFlow） ---------- */
function renderScore() {
  const div = document.getElementById("score");
  div.innerHTML = "";
  const VF = Vex.Flow;
  const events = buildEvents(committedNotes, getBpm());
  const measures = [[]];
  let acc = 0;
  for (const e of events) {
    if (acc >= 4 - 1e-9) { measures.push([]); acc = 0; }
    measures[measures.length - 1].push(e);
    acc += e.beats;
  }
  if (measures[0].length === 0) measures[0].push({ type: "rest", beats: 4 });

  const perRow = 3, sw = 360, sh = 140;
  const rows = Math.ceil(measures.length / perRow);
  const renderer = new VF.Renderer(div, VF.Renderer.Backends.SVG);
  renderer.resize(sw * perRow + 20, sh * rows + 20);
  const ctx = renderer.getContext();

  measures.forEach((meas, i) => {
    const row = Math.floor(i / perRow), col = i % perRow;
    const stave = new VF.Stave(10 + col * sw, 10 + row * sh, sw - 20);
    if (i === 0) stave.addClef("treble").addTimeSignature("4/4");
    else if (col === 0) stave.addClef("treble");
    stave.setContext(ctx).draw();

    const tickables = meas.map(e => {
      const base = DUR_MAP[e.beats];
      const sn = new VF.StaveNote({
        keys: [e.type === "rest" ? "b/4" : midiToVexKey(e.midi)],
        duration: base + (e.type === "rest" ? "r" : "")
      });
      if (DOT_SET.has(e.beats)) VF.Dot.buildAndAttach([sn], { all: true });
      return sn;
    });

    const voice = new VF.Voice({ numBeats: 4, beatValue: 4 }).setStrict(false);
    voice.addTickables(tickables);
    new VF.Formatter().joinVoices([voice]).format([voice], sw - 80);
    voice.draw(ctx, stave);
  });
}

/* ---------- 録音まわり ---------- */
let audioCtx = null, analyser = null, mediaStream = null, timeBuf = null;
let recording = false, startTime = 0, prevT = 0;
let committedNotes = [];
let tracker = null;

const $ = id => document.getElementById(id);

function getBpm() {
  const v = parseInt($("bpm").value, 10);
  return Math.min(240, Math.max(40, isNaN(v) ? 100 : v));
}

function onNote(n) {
  committedNotes.push(n);
  renderScore(); // 音符が確定するたび即座に譜面へ反映（リアルタイム性の肝）
}

async function startRecording() {
  // ★ AudioContext は必ずクリック直後（await の前）に作る。
  //   await を挟むとユーザージェスチャが切れ、Safari/iOS では
  //   suspended のまま＝マイクは取れているのに波形が全部ゼロ、になる
  audioCtx = new (window.AudioContext || window.webkitAudioContext)();

  try {
    mediaStream = await navigator.mediaDevices.getUserMedia({
      audio: { echoCancellation: false, noiseSuppression: false, autoGainControl: false }
    });
  } catch (e) {
    alert("マイクへのアクセスが拒否されました。ブラウザの設定でマイクを許可してください。");
    audioCtx.close();
    audioCtx = null;
    return;
  }
  if (audioCtx.state === "suspended") await audioCtx.resume(); // 保険
  console.log("AudioContext state:", audioCtx.state); // "running" であることを確認

  const src = audioCtx.createMediaStreamSource(mediaStream);
  analyser = audioCtx.createAnalyser();
  analyser.fftSize = 2048;
  src.connect(analyser);
  timeBuf = new Float32Array(analyser.fftSize);

  committedNotes = [];
  tracker = createTracker(onNote);
  startTime = performance.now();
  prevT = 0;
  recording = true;
  $("recordBtn").textContent = "■ 停止";
  requestAnimationFrame(loop);
}

function stopRecording() {
  recording = false;
  const t = performance.now() - startTime;
  if (tracker) tracker.flush(t, onNote);
  if (mediaStream) mediaStream.getTracks().forEach(tr => tr.stop());
  if (audioCtx) { audioCtx.close(); audioCtx = null; }
  $("recordBtn").textContent = "🎤 録音開始";
  renderScore();
}

function loop() {
  if (!recording) return;
  const t = performance.now() - startTime;
  // タブ復帰直後などの巨大な dt をクランプ（時刻補正の破綻を防ぐ）
  const dt = prevT ? Math.min(t - prevT, 100) : 16.7;
  prevT = t;

  analyser.getFloatTimeDomainData(timeBuf);
  let sum = 0;
  for (let i = 0; i < timeBuf.length; i++) sum += timeBuf[i] * timeBuf[i];
  const rms = Math.sqrt(sum / timeBuf.length);

  let midiF = null, freq = 0;
  if (rms > RMS_GATE) { // 無音ゲート
    freq = yinPitch(timeBuf, audioCtx.sampleRate);
    if (freq >= MIN_FREQ && freq <= MAX_FREQ) {
      midiF = 69 + 12 * Math.log2(freq / 440);
    } else {
      freq = 0;
    }
  }

  tracker.feed(midiF, t, dt);
  updateHud(freq, midiF, rms);
  requestAnimationFrame(loop);
}

function updateHud(freq, midiF, rms) {
  // 入力レベル（Lv）を常時表示: 反応しないときに
  // 「レベル不足」か「ピッチ推定の失敗」かが一目で分かる
  $("pitchDisplay").textContent =
    (freq > 0 ? `♪ ${freq.toFixed(1)} Hz` : "♪ --- Hz") + `  (Lv ${rms.toFixed(3)})`;
  $("noteDisplay").textContent = midiF !== null ? midiToName(Math.round(midiF)) : "--";
}

/* ---------- 再生（デモ用・シンプルなシンセ） ---------- */
function playNotes() {
  if (!committedNotes.length) { alert("先に鼻歌を録音してください"); return; }
  const ctx = new (window.AudioContext || window.webkitAudioContext)();
  const start0 = committedNotes[0].startMs;
  const base = ctx.currentTime + 0.1;
  for (const n of committedNotes) {
    const osc = ctx.createOscillator();
    const gain = ctx.createGain();
    osc.type = "sine";
    osc.frequency.value = 440 * Math.pow(2, (n.midi - 69) / 12);
    const s = base + (n.startMs - start0) / 1000;
    const e = s + n.durMs / 1000;
    gain.gain.setValueAtTime(0.0001, s);
    gain.gain.exponentialRampToValueAtTime(0.3, s + 0.02);
    gain.gain.exponentialRampToValueAtTime(0.0001, e);
    osc.connect(gain).connect(ctx.destination);
    osc.start(s);
    osc.stop(e + 0.05);
  }
}

/* ---------- エクスポート ---------- */
function saveBlob(blob, name) {
  const a = document.createElement("a");
  a.href = URL.createObjectURL(blob);
  a.download = name;
  a.click();
  setTimeout(() => URL.revokeObjectURL(a.href), 5000);
}

function toVarLen(v) {
  const bytes = [v & 0x7F];
  v >>= 7;
  while (v > 0) { bytes.unshift((v & 0x7F) | 0x80); v >>= 7; }
  return bytes;
}

function downloadMidi() {
  if (!committedNotes.length) { alert("先に鼻歌を録音してください"); return; }
  const bpm = getBpm();
  const TPQ = 480;
  const evs = [];
  for (const n of committedNotes) {
    const s = Math.round(beatsOf(n.startMs, bpm) * TPQ);
    const e = Math.round(beatsOf(n.startMs + n.durMs, bpm) * TPQ);
    evs.push({ tick: s, type: 0x90, midi: n.midi });
    evs.push({ tick: e, type: 0x80, midi: n.midi });
  }
  // 同ティックではノートオフ(0x80)を先に（0x80 < 0x90 なので型番号順でOK）
  evs.sort((a, b) => a.tick - b.tick || a.type - b.type);

  const track = [];
  const mpq = Math.round(60000000 / bpm);
  track.push(0x00, 0xFF, 0x51, 0x03, (mpq >> 16) & 0xFF, (mpq >> 8) & 0xFF, mpq & 0xFF); // テンポ
  track.push(0x00, 0xC0, 0x00); // 音色: ピアノ
  let last = 0;
  for (const ev of evs) {
    track.push(...toVarLen(ev.tick - last));
    last = ev.tick;
    track.push(ev.type, ev.midi, ev.type === 0x90 ? 100 : 64);
  }
  track.push(...toVarLen(0), 0xFF, 0x2F, 0x00); // 終端

  const header = [0x4D,0x54,0x68,0x64, 0,0,0,6, 0,0, 0,1, (TPQ >> 8) & 0xFF, TPQ & 0xFF];
  const trkH = [0x4D,0x54,0x72,0x6B,
    (track.length >>> 24) & 0xFF, (track.length >>> 16) & 0xFF,
    (track.length >>> 8) & 0xFF, track.length & 0xFF];
  saveBlob(new Blob([new Uint8Array([...header, ...trkH, ...track])], { type: "audio/midi" }), "humscore.mid");
}

function downloadMusicXML() {
  if (!committedNotes.length) { alert("先に鼻歌を録音してください"); return; }
  const bpm = getBpm();
  const events = buildEvents(committedNotes, bpm);
  let xml = `<?xml version="1.0" encoding="UTF-8"?>\n`;
  xml += `<!DOCTYPE score-partwise PUBLIC "-//Recordare//DTD MusicXML 4.0 Partwise//EN" "http://www.musicxml.org/dtds/partwise.dtd">\n`;
  xml += `<score-partwise version="4.0">\n<part-list><score-part id="P1"><part-name>HumScore</part-name></score-part></part-list>\n<part id="P1">\n`;
  xml += `<measure number="1">\n<attributes><divisions>4</divisions><key><fifths>0</fifths></key><time><beats>4</beats><beat-type>4</beat-type></time><clef><sign>G</sign><line>2</line></clef></attributes>\n<direction><sound tempo="${bpm}"/></direction>\n`;

  let measureNo = 1, acc = 0;
  for (const e of events) {
    if (acc >= 4 - 1e-9) {
      xml += `</measure>\n<measure number="${++measureNo}">\n`;
      acc = 0;
    }
    const dur = Math.round(e.beats * 4); // divisions=4（4分音符=4）
    const dotted = DOT_SET.has(e.beats) ? "<dot/>" : "";
    if (e.type === "rest") {
      xml += `<note><rest/><duration>${dur}</duration><type>${XML_TYPE[e.beats]}</type>${dotted}</note>\n`;
    } else {
      const step = XML_STEPS[e.midi % 12];
      const alter = XML_ALTERS[e.midi % 12];
      const oct = Math.floor(e.midi / 12) - 1;
      xml += `<note><pitch><step>${step}</step>${alter ? `<alter>${alter}</alter>` : ""}<octave>${oct}</octave></pitch><duration>${dur}</duration><type>${XML_TYPE[e.beats]}</type>${dotted}</note>\n`;
    }
    acc += e.beats;
  }
  xml += `</measure>\n</part>\n</score-partwise>`;
  saveBlob(new Blob([xml], { type: "application/vnd.recordare.musicxml+xml" }), "humscore.musicxml");
}

function downloadPng() {
  const svg = document.querySelector("#score svg");
  if (!svg) { alert("先に鼻歌を録音してください"); return; }
  const data = new XMLSerializer().serializeToString(svg);
  const url = URL.createObjectURL(new Blob([data], { type: "image/svg+xml;charset=utf-8" }));
  const img = new Image();
  img.onload = () => {
    const w = svg.viewBox.baseVal.width || 1100;
    const h = svg.viewBox.baseVal.height || 300;
    const canvas = document.createElement("canvas");
    canvas.width = w * 2; canvas.height = h * 2;
    const c = canvas.getContext("2d");
    c.fillStyle = "#ffffff";
    c.fillRect(0, 0, canvas.width, canvas.height);
    c.drawImage(img, 0, 0, canvas.width, canvas.height);
    URL.revokeObjectURL(url);
    const a = document.createElement("a");
    a.download = "humscore.png";
    a.href = canvas.toDataURL("image/png");
    a.click();
  };
  img.src = url;
}

/* ---------- イベント登録 ---------- */
$("recordBtn").addEventListener("click", () => (recording ? stopRecording() : startRecording()));
$("playBtn").addEventListener("click", playNotes);
$("clearBtn").addEventListener("click", () => { committedNotes = []; renderScore(); });
$("midiBtn").addEventListener("click", downloadMidi);
$("xmlBtn").addEventListener("click", downloadMusicXML);
$("pngBtn").addEventListener("click", downloadPng);
$("bpm").addEventListener("change", renderScore);
renderScore();