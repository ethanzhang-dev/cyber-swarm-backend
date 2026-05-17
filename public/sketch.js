// ======================================================
// CYBER SWARM: ROCKSTAR MEGA HOST (V4.3)
// 修正：
// - 去掉麦克风
// - 字幕修正：LEFT+TOP对齐，固定安全区，不出画面
// - 张嘴撕裂音：Web Audio原生WaveShaper失真 + pitch sweep
// - droneOsc张嘴时过载推入失真
// - 撕裂感独立于TTS，TTS只负责语言内容
// ======================================================

let stepCount = 0;
let lastStutterStep = -1;

p5.disableFriendlyErrors = true;

const ONE_LINE_PATH = [
  10,338,297,332,284,251,389,356,454,323,361,288,397,365,379,378,400,377,152,148,176,149,150,136,172,58,132,93,234,127,162,21,54,103,67,109,10,
  70,63,105,66,107,33,160,158,133,153,144,33,285,295,282,283,276,263,387,385,373,380,263,168,6,197,195,5,4,
  19,0,267,269,270,409,291,375,321,405,314,17,84,181,91,146,61,185,40,39,37,0
];

// ================= [ 模块 1: 全局状态 ] =================
let faceMesh, video, faces = [], smoothedKeypoints = [];
let options = { maxFaces:1, refineLandmarks:true, flipHorizontal:true };

// Reddit队列
let calmQueue = [];
let roarQueue  = [];

const SUBREDDITS = ['all','worldnews','technology','collapse','dataisbeautiful'];
let redditFetchIndex = 0;
let lastFetchTime    = -999999;
const FETCH_INTERVAL = 60000;
let isFetching       = false;
let dataSourceLabel  = "INITIALIZING...";

const VERB_TIERS = {
  violent: ["kill","destroy","crash","explode","collapse","burn","attack","die","dead","war","bomb","murder","riot","fail","break","crush","ban","block","cut","fire","shoot","storm","flood","freeze","bleed","abandon","betray"],
  tense:   ["warn","fear","risk","threat","force","demand","fight","struggle","resist","arrest","charge","claim","deny","reject","leak","expose","reveal","accuse","protest","strike","surge","drop","spike","fall","rise","hit","lose","win"],
  kinetic: ["launch","build","push","drive","run","race","jump","pull","send","move","spread","grow","expand","reach","break","cross","enter","leave","return","open","close","start","stop","change","shift","turn"]
};
const ALL_VERBS = [...VERB_TIERS.violent, ...VERB_TIERS.tense, ...VERB_TIERS.kinetic];

// 二阶动力学
let mouthEnergy   = 0;
let prevMouthDist = 0;
const SPRING_TENSION      = 0.97;
const SPRING_TENSION_FAST = 0.93;

// TTS状态
let voiceStarted = false, isScreamingMode = false;
let targetVoiceEN = null;
let prevNose = {x:0,y:0}, smoothedNoseSpeed = 0, currentlyOpen = false;
let activeWord = "", remainingText = "";
let lastWordStartTime = 0;    // 当前词开始时间（ms）
// 张嘴时最大词持续时间：超过这个时间就强制切下一个词
// 极慢rate下一个词可能拖8-10秒，太无聊，最多5秒就换
const MAX_ROAR_WORD_MS = 5000;

// ================= [ 词云粒子系统 ] =================
// 张嘴时单词从鼻子位置向外爆发飞散，2-3秒淡出消失
let wordParticles = [];
let lastParticleWord = "";

// 鼻子的屏幕坐标（镜像修正后），供粒子系统使用
// 在renderVisuals里每帧更新
let noseScreenX = 0;
let noseScreenY = 0;

// 侧脸检测：0=正脸，1=完全侧脸
// 用左右耳x坐标差值判断，平滑过渡
let faceAngleRatio = 0;  // 0正脸，1侧脸，smoothed
let faceAlpha = 255;     // 人脸渲染透明度，侧脸时淡出

// 乐队
let socket, bandMembers = {}, roleCounter = 0;
let roleNames = ["01_PULSE","02_RIFT","03_VOID","04_GLITCH","05_SURGE"];
let isHiveMode = false, chaosMeter = 0, audioInitialized = false;

// p5音频振荡器
let droneOsc, droneFilter, metalOsc, metalReverb;
let alarmOsc, alarmFilter, ghostNoise, ghostSine;
let distOsc, howlOsc, distFilter;
let shepardOscs = [], baseFreq = 45;
let schedulerNextBeatTime = 0;

// 节拍密度：闭嘴115ms（约130BPM），张嘴时压缩到70ms（约170BPM）
// 能量积累到阈值时切换，产生爆发感
let currentStepDuration = 0.115; // 秒，AudioContext时间单位
let targetStepDuration  = 0.115;

// Web Audio原生节点：kick + 高频噪音层
let kickGain      = null;
let hiNoiseGain   = null;
let hiNoiseSource = null;
let hiNoiseFilter = null;

// 贝斯线：跟着kick节拍的低频正弦，比kick衰减慢，产生持续推动感
let bassGainNode = null; // 贝斯总增益

// ================= [ Formant合成系统 ] =================
// 模拟人声声道共振峰，产生机器喉音
// 张嘴时激活，随d（张嘴幅度）和鼻子X位置实时变形
let formantActive = false;
let formantSrc    = null;  // 锯齿波声源（模拟声带振动）
let formantGain   = null;  // 总音量
let formantF1     = null;  // 第一共振峰（决定开口度，啊/哦/嗯）
let formantF2     = null;  // 第二共振峰（决定前后，伊/啊/乌）
let formantF3     = null;  // 第三共振峰（音色明亮度）
let formantF1G    = null;  // F1增益节点
let formantF2G    = null;  // F2增益节点
let formantF3G    = null;  // F3增益节点
let formantDist   = null;  // 轻微失真（让机器声更粗糙）

// ================= [ 撕裂音系统：Web Audio原生节点 ] =================
// 这套独立于p5.sound，直接操作AudioContext
// 产生真实的摇滚失真撕裂感
let tearAudioCtx = null;   // 直接引用AudioContext
let tearGain     = null;   // 撕裂总音量控制
let tearOsc1     = null;   // 撕裂振荡器1：基频
let tearOsc2     = null;   // 撕裂振荡器2：轻微失谐，产生拍频
let tearShaper   = null;   // WaveShaper：波形折叠失真
let sweepLFO     = null;   // LFO：频率扫描，产生嚎叫感
let sweepGain    = null;   // LFO深度控制
let tearActive   = false;  // 撕裂层是否激活

// 生成WaveShaper失真曲线
// amount：失真量，0=无失真，400=极度失真
function makeDistortionCurve(amount) {
  let n = 256;
  let curve = new Float32Array(n);
  let deg = Math.PI / 180;
  for (let i = 0; i < n; i++) {
    let x = (i * 2) / n - 1;
    // 软削波（soft clipping）公式：保留动态但产生泛音
    curve[i] = ((3 + amount) * x * 20 * deg) /
               (Math.PI + amount * Math.abs(x));
  }
  return curve;
}

function initTearSystem(ac) {
  tearAudioCtx = ac;

  tearGain = ac.createGain();
  tearGain.gain.value = 0;
  tearGain.connect(ac.destination);

  tearShaper = ac.createWaveShaper();
  tearShaper.curve = makeDistortionCurve(350);
  tearShaper.oversample = '4x';
  tearShaper.connect(tearGain);

  // filter sweep LFO：持续扫描产生演化感
  // 这是张嘴时声音不静止的关键——0.15Hz极慢扫描，约6秒一个周期
  // 听起来像电吉他feedback在空气里慢慢旋转
  let filterSweepLFO  = ac.createOscillator();
  let filterSweepGain = ac.createGain();
  filterSweepLFO.type = 'sine';
  filterSweepLFO.frequency.value = 0.15;  // 极慢，6秒一周期
  filterSweepGain.gain.value = 60;         // 扫描幅度±60Hz
  filterSweepLFO.connect(filterSweepGain);
  filterSweepLFO.start();

  // 带通滤波器：让中频段周期性凸显，产生wah-wah感
  let wahFilter = ac.createBiquadFilter();
  wahFilter.type = 'bandpass';
  wahFilter.frequency.value = 400;
  wahFilter.Q.value = 3.0;
  filterSweepGain.connect(wahFilter.frequency); // LFO调制滤波器频率
  tearShaper.connect(wahFilter);
  wahFilter.connect(tearGain);

  sweepLFO  = ac.createOscillator();
  sweepGain = ac.createGain();
  sweepLFO.type = 'sine';
  sweepLFO.frequency.value = 3.5;
  sweepGain.gain.value = 0;
  sweepLFO.connect(sweepGain);
  sweepLFO.start();

  tearOsc1 = ac.createOscillator();
  tearOsc1.type = 'sawtooth';
  tearOsc1.frequency.value = 80;
  sweepGain.connect(tearOsc1.frequency);
  tearOsc1.connect(tearShaper);
  tearOsc1.start();

  tearOsc2 = ac.createOscillator();
  tearOsc2.type = 'sawtooth';
  tearOsc2.frequency.value = 83;
  tearOsc2.connect(tearShaper);
  tearOsc2.start();

  tearActive = true;
}

// ================= [ Kick鼓系统 ] =================
// 电子音乐kick的物理本质：短暂正弦波从高频极速下扫到极低频
// 产生胸腔可感知的低频冲击，不依赖扬声器尺寸也有物理存在感
function fireKick(ac, time, energy) {
  if (!kickGain) return;

  let vol = map(energy, 0, 100, 0.4, 1.3);

  let osc  = ac.createOscillator();
  let gain = ac.createGain();
  osc.connect(gain);
  gain.connect(kickGain);

  // 频率下扫：180Hz → 28Hz，70ms完成（原来40ms，加长产生更厚的punch）
  // 起始频率提高到180Hz，让"咚"头更清晰
  osc.frequency.setValueAtTime(180, time);
  osc.frequency.exponentialRampToValueAtTime(28, time + 0.07);

  // 音量包络：瞬间起音，120ms内衰减（原来80ms，尾音更长，身体感知更强）
  gain.gain.setValueAtTime(vol, time);
  gain.gain.exponentialRampToValueAtTime(0.001, time + 0.12);

  osc.start(time);
  osc.stop(time + 0.15);
}

// ================= [ 贝斯线 ] =================
// 跟着kick节奏的低频正弦音，比kick更低（40-60Hz），衰减更慢（200ms）
// 产生持续的低频推动感，是摇摆身体的物理驱动力
// 闭嘴：固定45Hz（一个音），有律动无变化
// 张嘴：频率随energy上升（45→80Hz），产生紧张上升感
function fireBass(ac, time, energy, isOpen) {
  if (!bassGainNode) return;

  // 贝斯频率：闭嘴固定45Hz，张嘴时随energy上升
  // 45→80Hz对应摇滚低音吉他的低把位
  let freq = isOpen
    ? map(energy, 30, 100, 45, 80)
    : 45;

  let vol = isOpen
    ? map(energy, 30, 100, 0.3, 0.7)
    : 0.35; // 闭嘴时贝斯较轻，不盖过kick

  let osc  = ac.createOscillator();
  let gain = ac.createGain();
  osc.type = 'sine'; // 纯正弦，低频最干净
  osc.frequency.setValueAtTime(freq, time);
  osc.connect(gain);
  gain.connect(bassGainNode);

  // 贝斯包络：比kick更慢的衰减（200ms），产生持续推力
  gain.gain.setValueAtTime(vol, time);
  gain.gain.exponentialRampToValueAtTime(0.001, time + 0.20);

  osc.start(time);
  osc.stop(time + 0.25);
}

// ================= [ 高频噪音层初始化 ] =================
// 持续的高频白噪声，经高通滤波保留4kHz以上
// 音量极低但填充声场高频空间，让整体声音有"压迫感"
// 张嘴时音量和滤波频率随能量变化
function initHiNoise(ac) {
  // 生成1秒白噪声buffer
  let bufferSize = ac.sampleRate;
  let buffer     = ac.createBuffer(1, bufferSize, ac.sampleRate);
  let data       = buffer.getChannelData(0);
  for (let i = 0; i < bufferSize; i++) {
    data[i] = Math.random() * 2 - 1;
  }

  // BufferSource循环播放
  hiNoiseSource = ac.createBufferSource();
  hiNoiseSource.buffer = buffer;
  hiNoiseSource.loop   = true;

  // 高通滤波：只保留4kHz以上
  hiNoiseFilter = ac.createBiquadFilter();
  hiNoiseFilter.type            = 'highpass';
  hiNoiseFilter.frequency.value = 4000;
  hiNoiseFilter.Q.value         = 0.5;

  // 总增益（初始极小）
  hiNoiseGain = ac.createGain();
  hiNoiseGain.gain.value = 0.015; // 很低，几乎感知不到，但去掉会觉得"空"

  hiNoiseSource.connect(hiNoiseFilter);
  hiNoiseFilter.connect(hiNoiseGain);
  hiNoiseGain.connect(ac.destination);
  hiNoiseSource.start();
}

// 张嘴时调用：推入撕裂层
// energy：0-100，控制撕裂强度
function activateTear(energy) {
  if (!tearActive || !tearAudioCtx) return;
  let t = tearAudioCtx.currentTime;

  // 音量：能量越高撕裂越响
  let targetVol = map(energy, 30, 100, 0.05, 0.45);
  tearGain.gain.cancelScheduledValues(t);
  tearGain.gain.setTargetAtTime(targetVol, t, 0.02); // 20ms攻击

  // 频率：能量越高，基频越高（向上撕裂）
  let targetFreq = map(energy, 30, 100, 60, 180);
  tearOsc1.frequency.cancelScheduledValues(t);
  tearOsc1.frequency.setTargetAtTime(targetFreq, t, 0.05);
  tearOsc2.frequency.setTargetAtTime(targetFreq + 3, t, 0.05);

  // LFO深度：能量越高，弯弦幅度越大
  let sweepDepth = map(energy, 30, 100, 20, 120);
  sweepGain.gain.setTargetAtTime(sweepDepth, t, 0.1);

  // 失真量随能量动态变化
  tearShaper.curve = makeDistortionCurve(map(energy, 30, 100, 150, 500));
}

// 闭嘴时调用：撕裂层慢慢衰减（余震感）
function deactivateTear() {
  if (!tearActive || !tearAudioCtx) return;
  let t = tearAudioCtx.currentTime;
  // 慢慢衰减到0，不是瞬间截断
  tearGain.gain.cancelScheduledValues(t);
  tearGain.gain.setTargetAtTime(0, t, 0.3); // 300ms衰减
  sweepGain.gain.setTargetAtTime(0, t, 0.2);
}

// ================= [ 模块 2: 初始化 ] =================
function preload() { faceMesh = ml5.faceMesh(options); }

function setup() {
  createCanvas(windowWidth, windowHeight);
  video = createCapture(VIDEO);
  video.size(windowWidth, windowHeight);
  video.hide();
  video.elt.onloadedmetadata = () => faceMesh.detectStart(video, results => faces = results);

  try {
    socket = io("https://cyber-swarm-backend.onrender.com");
    socket.on('shake', (data) => {
      if (data.isHost) return;
      console.log('手机数据:', JSON.stringify(data));
      let now = millis();
      if (!bandMembers[data.id]) {
        let assignedRole = roleCounter % 5; // 0-4，五个角色循环分配
        bandMembers[data.id] = { role: assignedRole, intensity: 0, lastSeen: now };
        roleCounter++;
        socket.emit('shake', { isHost: true, targetId: data.id, role: assignedRole });
      }
      bandMembers[data.id].intensity = data.val;
      bandMembers[data.id].lastSeen  = now;
    });
  } catch(e) { console.log("Socket bypassed."); }

  initVoices();
  initBandAudio();

  // TTS心跳
  setInterval(() => {
    if (voiceStarted && window.speechSynthesis.speaking) {
      window.speechSynthesis.pause();
      window.speechSynthesis.resume();
    }
  }, 10000);
}

// ================= [ 模块 3: 声音 ] =================
function initVoices() {
  let voices = window.speechSynthesis.getVoices();
  targetVoiceEN = voices.find(v => v.lang === 'en-US')
               || voices.find(v => v.lang.startsWith('en'))
               || voices[0];
}
window.speechSynthesis.onvoiceschanged = initVoices;

function initBandAudio() {
  droneFilter = new p5.LowPass();
  droneOsc    = new p5.Oscillator('sawtooth');
  droneOsc.disconnect(); droneOsc.connect(droneFilter);

  metalReverb = new p5.Reverb();
  metalOsc    = new p5.Oscillator('sine');
  metalOsc.disconnect(); metalReverb.process(metalOsc, 6, 2);

  alarmFilter = new p5.LowPass(); alarmFilter.res(25);
  alarmOsc    = new p5.Oscillator('square');
  alarmOsc.disconnect(); alarmOsc.connect(alarmFilter);

  ghostNoise = new p5.Noise('pink'); ghostNoise.amp(0);
  ghostSine  = new p5.Oscillator('sine'); ghostSine.amp(0);

  distFilter = new p5.LowPass();
  distOsc    = new p5.Oscillator('sawtooth');
  distOsc.disconnect(); distOsc.connect(distFilter);

  howlOsc = new p5.Oscillator('sine');

  for (let i = 0; i < 5; i++) {
    let osc = new p5.Oscillator('sine');
    osc.freq(baseFreq * pow(2, i));
    shepardOscs.push(osc);
  }
}

// ================= [ 模块 4: Reddit ] =================
async function fetchRedditData() {
  if (isFetching) return;
  isFetching = true;
  let sub = SUBREDDITS[redditFetchIndex % SUBREDDITS.length];
  redditFetchIndex++;
  let url = `https://www.reddit.com/r/${sub}/hot.json?limit=25&raw_json=1`;
  try {
    let response = await fetch(url);
    if (!response.ok) throw new Error(`HTTP ${response.status}`);
    let data  = await response.json();
    let posts  = data.data.children;
    let titles = posts.map(p => p.data.title)
                      .filter(t => t && t.length > 10 && t.length < 120);
    dataSourceLabel = `r/${sub} · ${titles.length} · ${new Date().toLocaleTimeString()}`;
    processTitlesIntoQueues(titles);
  } catch(e) {
    dataSourceLabel = `FETCH FAIL: ${e.message}`;
    if (calmQueue.length < 3) injectFallbackContent();
  }
  isFetching = false;
}

function processTitlesIntoQueues(titles) {
  for (let title of titles) {
    let cv = transformForCalm(title);
    if (cv) calmQueue.push(cv);
    let rv = extractForRoar(title);
    if (rv) roarQueue.push(rv);
  }
  if (calmQueue.length > 80) calmQueue = calmQueue.slice(-60);
  if (roarQueue.length  > 80) roarQueue  = roarQueue.slice(-60);
}

function transformForCalm(title) {
  let clean = title.replace(/[^\w\s]/g,' ').replace(/\s+/g,' ').trim().toLowerCase();
  let words  = clean.split(' ').filter(w => w.length > 2);
  if (words.length < 3) return null;
  const STOP = new Set(['the','a','an','and','or','but','in','on','at','to','for','of','with','by','from','is','are','was','were','be','been','have','has','had','will','would','could','should','may','might','that','this','these','those','it','its','not','no','as','up','out','if','about','after','before','over','under','into','than']);
  let meaningful = words.filter(w => !STOP.has(w));
  if (meaningful.length < 2) return clean;
  for (let i = meaningful.length-1; i > 0; i--) {
    let j = Math.floor(Math.random()*(i+1));
    [meaningful[i], meaningful[j]] = [meaningful[j], meaningful[i]];
  }
  return meaningful.slice(0,6).join(' ');
}

function extractForRoar(title) {
  let clean   = title.toLowerCase().replace(/[^\w\s]/g,' ');
  let words   = clean.split(' ').filter(w => w.length > 0);
  let verbs   = words.filter(w => ALL_VERBS.includes(w));
  let numbers = title.match(/\d+(?:[,.\d]*)?(?:\s*(?:billion|million|thousand|%|km|mph))?/gi) || [];
  verbs.sort((a,b) => {
    let ta = VERB_TIERS.violent.includes(a)?3:VERB_TIERS.tense.includes(a)?2:1;
    let tb = VERB_TIERS.violent.includes(b)?3:VERB_TIERS.tense.includes(b)?2:1;
    return tb-ta;
  });
  let combined = [...verbs.slice(0,3), ...numbers.slice(0,2)];
  if (combined.length === 0) return words[words.length-1] || null;
  return combined.join(' ');
}

const FALLBACK_CALM = [
  "neural buffer overflow cascade","topology logic grid failure",
  "vertex matrix depth collapse","retinal projection sync lost",
  "synaptic snapshot cascade error","kernel depth threshold breach",
  "probability weight distribution null","coordinate system anchor lost"
];
const FALLBACK_ROAR = [
  "collapse fail crash","break burn die",
  "surge drop spike","destroy breach null",
  "overflow terminate kill","collapse null error"
];

function injectFallbackContent() {
  for (let t of FALLBACK_CALM) calmQueue.push(t);
  for (let t of FALLBACK_ROAR) roarQueue.push(t);
}

// ================= [ Formant合成系统初始化 ] =================
function initFormantSynth(ac) {
  // 声源：锯齿波，富含所有谐波，通过滤波器塑造音色
  // 频率约80Hz（男性低音声带基频范围）
  formantSrc = ac.createOscillator();
  formantSrc.type = 'sawtooth';
  formantSrc.frequency.value = 80;

  // 总增益（初始0，张嘴时推上来）
  formantGain = ac.createGain();
  formantGain.gain.value = 0;
  formantGain.connect(ac.destination);

  // 轻微失真：让机器声有粗糙质感，不是纯净合成音
  formantDist = ac.createWaveShaper();
  formantDist.curve = makeDistortionCurve(80); // 轻失真，不要盖过音色
  formantDist.oversample = '2x';
  formantDist.connect(formantGain);

  // 三个带通滤波器，各有独立增益节点
  // F1：第一共振峰，控制开口度
  //   闭嘴元音（乌/哦）：F1低（300-500Hz）
  //   开口元音（啊）：F1高（700-900Hz）
  formantF1  = ac.createBiquadFilter();
  formantF1G = ac.createGain();
  formantF1.type = 'bandpass';
  formantF1.frequency.value = 400; // 初始中性
  formantF1.Q.value = 5;           // 较窄带宽，共振峰要有特征
  formantF1G.gain.value = 1.0;

  // F2：第二共振峰，控制前后音色
  //   后元音（乌）：F2低（700-1000Hz）
  //   前元音（伊）：F2高（1800-2500Hz）
  formantF2  = ac.createBiquadFilter();
  formantF2G = ac.createGain();
  formantF2.type = 'bandpass';
  formantF2.frequency.value = 1200;
  formantF2.Q.value = 4;
  formantF2G.gain.value = 0.7;

  // F3：第三共振峰，音色明亮度
  //   固定约2500-3000Hz，随能量微调
  formantF3  = ac.createBiquadFilter();
  formantF3G = ac.createGain();
  formantF3.type = 'bandpass';
  formantF3.frequency.value = 2800;
  formantF3.Q.value = 6;
  formantF3G.gain.value = 0.4;

  // 连接：声源 → 三路并联滤波器 → 各自增益 → 失真 → 总增益
  formantSrc.connect(formantF1);
  formantSrc.connect(formantF2);
  formantSrc.connect(formantF3);
  formantF1.connect(formantF1G); formantF1G.connect(formantDist);
  formantF2.connect(formantF2G); formantF2G.connect(formantDist);
  formantF3.connect(formantF3G); formantF3G.connect(formantDist);

  formantSrc.start();
  formantActive = true;
}

// 每帧更新formant参数
// mouthD：实时张嘴距离（0-30），noseX：鼻子屏幕X坐标（已翻转）
function updateFormant(ac, mouthD, noseX, energy) {
  if (!formantActive) return;
  let t = ac.currentTime;

  if (energy > 15 || mouthD > 8) {
    // 声源音量：随energy推高
    let vol = map(energy, 15, 100, 0.06, 0.35);
    formantGain.gain.setTargetAtTime(vol, t, 0.05);

    // 声源基频：随energy轻微上升（声带拉紧）
    // 加轻微颤抖（5Hz模拟声带不稳定）
    let baseF0   = map(energy, 15, 100, 70, 120);
    let wobbleF0 = Math.sin(Date.now() * 0.005) * 3;
    formantSrc.frequency.setTargetAtTime(baseF0 + wobbleF0, t, 0.08);

    // F1：随张嘴幅度d变化
    // d小（刚张）→ F1低（约350Hz，哦/嗯感）
    // d大（全开）→ F1高（约850Hz，啊感）
    let f1 = map(constrain(mouthD, 5, 28), 5, 28, 350, 850);
    formantF1.frequency.setTargetAtTime(f1, t, 0.08);

    // F2：随鼻子X轴变化（左=后元音乌，右=前元音伊）
    // noseX已翻转，0=左，width=右
    let f2 = map(constrain(noseX, 0, width), 0, width, 800, 2400);
    formantF2.frequency.setTargetAtTime(f2, t, 0.12);

    // F3：随energy微调明亮度
    let f3 = map(energy, 15, 100, 2500, 3200);
    formantF3.frequency.setTargetAtTime(f3, t, 0.15);

    // F1增益随张嘴幅度推高（开口越大F1越显著）
    formantF1G.gain.setTargetAtTime(map(mouthD, 5, 28, 0.6, 1.4), t, 0.08);

  } else {
    // 闭嘴：音量慢慢衰减到0（余震感）
    formantGain.gain.setTargetAtTime(0, t, 0.4);
  }
}

// ================= [ 模块 5: TTS ] =================
// ================= [ TTS设计说明 ] =================
// 摇滚撕裂感的物理来源：
// 1. rate极慢（0.03-0.1）：音素被拉伸，声道共振结构暴露，数字化颤抖出现
// 2. rate不是匀速：d（即时距离）提供即时响应，mouthEnergy提供惯性余震
// 3. 偶发喘息：能量极高时随机插入一个rate=0.6的词，撕裂里的突然正常，
//    制造Swans/Diamanda Galás式的张力——安静往往比嚎叫更令人不安
// 4. pitch在低频区滑动（0.01-0.30）：向左崩溃，向右紧张
// 5. 鼻子速度产生颤音（vibrato）：约4Hz，模拟弯弦滑动感
//
// 注意：Web Speech API的rate硬下限约0.1（浏览器会截断更低的值）
// 0.03会被截到0.1，但不同TTS引擎截断行为不同——macOS/Chrome会产生
// 额外的数字化颤抖，本身就是撕裂感的一部分，保留这个极端值有意义。
function performVocal(txt, isDragMode, noseX, mouthD, noseSpd, forceNew=false) {
  if (forceNew) window.speechSynthesis.cancel();
  if (!txt || txt.length===0) return;

  let msg  = new SpeechSynthesisUtterance();
  msg.lang = 'en-US';
  if (targetVoiceEN) msg.voice = targetVoiceEN;
  msg.volume = 1.0;
  msg.text   = txt;

  if (isDragMode || isHiveMode) {
    // --- rate：d（即时）和mouthEnergy（惯性）混合 ---
    // d映射：8（刚张嘴）→ 0.35，30（全开）→ 0.03
    // 比之前更极端：下限从0.05降到0.03
    let rateFromD = map(constrain(mouthD, 8, 30), 8, 30, 0.35, 0.03);

    // mouthEnergy映射：惯性层
    let rateFromEnergy = map(constrain(mouthEnergy, 30, 100), 30, 100, 0.35, 0.03);

    // 混合：d占60%（即时响应），energy占40%（惯性）
    let blendedRate = rateFromD * 0.6 + rateFromEnergy * 0.4;

    // 偶发喘息：能量>80时，约15%概率插入一个较快的词
    // 这是摇滚嚎叫里最有张力的时刻——撕裂里突然出现的正常
    if (mouthEnergy > 80 && random() < 0.15) {
      blendedRate = random(0.5, 0.8);
    }

    msg.rate = constrain(blendedRate, 0.03, 0.35);

    // --- pitch：鼻子X轴在低音调区间滑动 ---
    let basePitch   = map(noseX, 0, width, 0.01, 0.30);
    // 颤音：鼻子速度映射抖动深度，4Hz周期
    let vibratoDepth  = map(constrain(noseSpd, 0, 12), 0, 12, 0, 0.09);
    let vibratoOffset = sin(frameCount * 0.25) * vibratoDepth;
    msg.pitch = constrain(basePitch + vibratoOffset, 0.01, 0.35);

  } else {
    // 平静模式：正常语速，完整pitch范围
    msg.rate  = 0.95;
    let dynamicPitch = map(noseX, 0, width, 0.05, 2.0);
    msg.pitch = constrain(dynamicPitch, 0.05, 2.0);
  }

  window.speechSynthesis.speak(msg);
}

// ================= [ 模块 6: 音频调度器 ] =================
function startAudioScheduler() {
  let ac = getAudioContext();
  schedulerNextBeatTime = ac.currentTime;
  scheduleLoop();
}

function scheduleLoop() {
  let ac = getAudioContext();

  // 节拍密度换档：只在强拍（stepCount将变成0时）才切换
  // 不用平滑lerp，用明确的换档感——听众能感知到"加速"这个事件
  if (mouthEnergy > 60) targetStepDuration = 0.070;
  else if (mouthEnergy < 30) targetStepDuration = 0.115;

  while (schedulerNextBeatTime < ac.currentTime + 0.1) {
    fireScheduledBeat(ac, schedulerNextBeatTime);
    // 只在stepCount回到0时才切换步长（强拍对齐）
    if (stepCount === 0) {
      currentStepDuration = targetStepDuration;
    }
    schedulerNextBeatTime += currentStepDuration;
  }
  setTimeout(scheduleLoop, 25);
}

function fireScheduledBeat(ac, time) {
  let localStep = stepCount;
  stepCount = (stepCount+1) % 16;

  if (localStep===0||localStep===4||localStep===8||localStep===10||localStep===12) {
    if (!audioInitialized) return;

    // metalOsc：联动energy
    if (mouthEnergy > 30 || currentlyOpen) {
      let amp     = map(mouthEnergy, 30, 100, 0.6, 1.4);
      let decayMs = map(mouthEnergy, 30, 100, 150, 450);
      metalOsc.setType('square');
      metalOsc.freq(map(mouthEnergy, 30, 100, 300, 500), 0.001);
      metalOsc.amp(amp, 0.003);
      setTimeout(()=>{ if(audioInitialized) metalOsc.amp(0, 0.04); }, decayMs);
    } else {
      metalOsc.setType('sine');
      metalOsc.freq(100, 0.001);
      metalOsc.amp(0.6, 0.01);
      setTimeout(()=>{ if(audioInitialized) metalOsc.amp(0,0.05); }, 200);
    }

    // kick：强拍必打，弱拍张嘴时打
    if (ac && kickGain) {
      let isDownbeat = (localStep === 0 || localStep === 8);
      if (isDownbeat) {
        fireKick(ac, time, max(mouthEnergy, 40));
      } else if (mouthEnergy > 30) {
        fireKick(ac, time, mouthEnergy * 0.6);
      }
    }

    // 贝斯线：所有强拍都弹，闭嘴固定音，张嘴时频率随energy上升
    // 强拍（0、8步）贝斯更响，弱拍（4、10、12步）略轻
    if (ac && bassGainNode) {
      let isDownbeat = (localStep === 0 || localStep === 8);
      let bassEnergy = isDownbeat ? max(mouthEnergy, 30) : mouthEnergy * 0.75;
      fireBass(ac, time, bassEnergy, currentlyOpen || mouthEnergy > 30);
    }
  }

  // 切分拍：能量>70时，在3、7、11、15步加ghost kick
  if (mouthEnergy > 70 && ac && kickGain) {
    if (localStep===3||localStep===7||localStep===11||localStep===15) {
      fireKick(ac, time, mouthEnergy * 0.35);
      // 切分拍也加轻贝斯（能量的40%），让切分有低频支撑
      if (bassGainNode) fireBass(ac, time, mouthEnergy * 0.40, true);
    }
  }
}

// ================= [ 模块 7: 主循环 ] =================
function draw() {
  let ts = millis(), d = 0;
  let rolesData = {0:0, 1:0, 2:0, 3:0, 4:0};

  if (voiceStarted && ts - lastFetchTime > FETCH_INTERVAL) {
    lastFetchTime = ts;
    fetchRedditData();
  }

  for (let id in bandMembers) {
    if (ts - bandMembers[id].lastSeen > 2000) { delete bandMembers[id]; continue; }
    let r = bandMembers[id].role;
    rolesData[r] = max(rolesData[r] || 0, bandMembers[id].intensity);
  }

  let faceScale = 1.0;
  if (faces.length > 0) {
    let rawKp = faces[0].keypoints;
    if (smoothedKeypoints.length !== rawKp.length) {
      smoothedKeypoints = rawKp.map(p => ({x:p.x,y:p.y}));
    } else {
      for (let i=0; i<rawKp.length; i++) {
        smoothedKeypoints[i].x = lerp(smoothedKeypoints[i].x, rawKp[i].x, 0.35);
        smoothedKeypoints[i].y = lerp(smoothedKeypoints[i].y, rawKp[i].y, 0.35);
      }
    }
    faceScale = dist(smoothedKeypoints[10].x,smoothedKeypoints[10].y,
                     smoothedKeypoints[152].x,smoothedKeypoints[152].y) / 250.0;
    faceScale = constrain(faceScale, 0.3, 2.0);

    let rawMD = dist(smoothedKeypoints[13].x,smoothedKeypoints[13].y,
                     smoothedKeypoints[14].x,smoothedKeypoints[14].y);
    d = rawMD / max(0.1, faceScale);

    // 二阶动力学
    let mv = d - prevMouthDist;
    if (mv > 1.5)  mouthEnergy += mv * 8.0;
    else if (d>15) mouthEnergy += 1.0;
    let tension  = mouthEnergy > 50 ? SPRING_TENSION_FAST : SPRING_TENSION;
    mouthEnergy *= tension;
    mouthEnergy  = constrain(mouthEnergy, 0, 100);
    prevMouthDist = d;

    if (voiceStarted) {
      if (!currentlyOpen && mouthEnergy>30) currentlyOpen = true;
      else if (currentlyOpen && mouthEnergy<10) currentlyOpen = false;
    }

    if (audioInitialized) {
      let cs = dist(smoothedKeypoints[1].x,smoothedKeypoints[1].y,prevNose.x,prevNose.y);
      smoothedNoseSpeed = lerp(smoothedNoseSpeed, cs, 0.25);
      prevNose.x = smoothedKeypoints[1].x;
      prevNose.y = smoothedKeypoints[1].y;
    }
  }

  if (audioInitialized) {
    updateAmbientAudio(rolesData, smoothedNoseSpeed);

    // 撕裂层：随mouthEnergy实时更新
    if (currentlyOpen || mouthEnergy > 15) {
      activateTear(mouthEnergy);
    } else {
      deactivateTear();
    }

    // Formant合成：实时更新声道参数
    if (formantActive) {
      if (formantSoloMode) {
        // solo模式：直接用d和noseX更新音色参数，但不改音量（保持0.8）
        updateFormant(getAudioContext(), d, width - prevNose.x, 80);
      } else {
        updateFormant(getAudioContext(), d, width - prevNose.x, mouthEnergy);
      }
    }

    // 高频噪音层：张嘴时音量和滤波频率随能量变化
    // 闭嘴：极低底噪（0.015），填充声场不显眼
    // 张嘴：音量推高到0.06，滤波频率从4kHz降到2kHz（更多中高频进来，更压迫）
    if (hiNoiseGain && hiNoiseFilter) {
      let ac = getAudioContext();
      let t  = ac.currentTime;
      if (currentlyOpen || mouthEnergy > 20) {
        let targetVol  = map(mouthEnergy, 20, 100, 0.02, 0.07);
        let targetFreq = map(mouthEnergy, 20, 100, 4000, 2000);
        hiNoiseGain.gain.setTargetAtTime(targetVol,  t, 0.1);
        hiNoiseFilter.frequency.setTargetAtTime(targetFreq, t, 0.1);
      } else {
        hiNoiseGain.gain.setTargetAtTime(0.015, t, 0.3);
        hiNoiseFilter.frequency.setTargetAtTime(4000, t, 0.3);
      }
    }

    // kickGain总音量：正常0.8，张嘴时推到1.4（kick更重）
    if (kickGain) {
      let ac = getAudioContext();
      let targetKickVol = currentlyOpen ? map(mouthEnergy, 30, 100, 0.8, 1.4) : 0.8;
      kickGain.gain.setTargetAtTime(targetKickVol, ac.currentTime, 0.05);
    }

    // SURGE（role4）对chaos贡献最大，×15加速推进
    let baseIntensity = rolesData[0]+rolesData[1]+rolesData[2]+rolesData[3]+(rolesData[4]*15);
    if (baseIntensity>250) chaosMeter+=1;
    if (currentlyOpen)     chaosMeter+=3;
    if (baseIntensity<=250 && !currentlyOpen) chaosMeter-=1.5;
    chaosMeter = constrain(chaosMeter, 0, 300);

    if (chaosMeter>=300 && !isHiveMode) triggerHiveProtocol();
    else if (chaosMeter<=150 && isHiveMode) { isHiveMode=false; roleCounter=0; }
  }

  if (voiceStarted) {
    let stateChangedThisFrame = false;

    if (currentlyOpen && !isScreamingMode) {
      isScreamingMode = true;
      stateChangedThisFrame = true;
    } else if (!currentlyOpen && isScreamingMode) {
      isScreamingMode = false;
      window.speechSynthesis.cancel();
      stateChangedThisFrame = true;
    }

    // 张嘴强制切词：超过MAX_ROAR_WORD_MS就强制cancel，换下一个词
    // 极慢rate下一个词可能拖8-10秒，超过5秒就太无聊
    // 这让张嘴期间词的密度提高，声音持续有变化
    if (isScreamingMode && window.speechSynthesis.speaking) {
      if (millis() - lastWordStartTime > MAX_ROAR_WORD_MS) {
        window.speechSynthesis.cancel(); // 强制结束当前词
        // cancel后speaking=false，下面的调度块会立刻触发下一个词
      }
    }

    // stutter斩波器：能量>70时才启用
    if (isScreamingMode && window.speechSynthesis.speaking && mouthEnergy > 70) {
      if (stepCount !== lastStutterStep) {
        lastStutterStep = stepCount;
        if (stepCount % 4 === 3) window.speechSynthesis.pause();
        else                      window.speechSynthesis.resume();
      }
    }

    if (!window.speechSynthesis.speaking && !stateChangedThisFrame) {
      lastWordStartTime = millis(); // 记录新词开始时间

      if (isHiveMode) {
        let rawWord = roarQueue.length>0 ? roarQueue.shift() : random(FALLBACK_ROAR);
        activeWord = rawWord; remainingText = rawWord;
        let savedEnergy = mouthEnergy;
        mouthEnergy = 100;
        performVocal(activeWord, true, width-prevNose.x, d, smoothedNoseSpeed, true);
        mouthEnergy = savedEnergy;

      } else if (isScreamingMode) {
        if (roarQueue.length < 3) injectFallbackContent();
        let rw = roarQueue.shift() || random(FALLBACK_ROAR);
        activeWord = rw; remainingText = rw;
        performVocal(activeWord, true, width-prevNose.x, d, smoothedNoseSpeed, true);

      } else {
        if (calmQueue.length < 3) { injectFallbackContent(); lastFetchTime = -999999; }
        let cw = calmQueue.shift() || random(FALLBACK_CALM);
        activeWord = cw; remainingText = cw;
        performVocal(activeWord, false, width-prevNose.x, d, smoothedNoseSpeed, true);
      }
    }
  }

  renderVisuals(remainingText, d, currentlyOpen, rolesData, faceScale);
}

// ================= [ 模块 8: 环境音 ] =================
function updateAmbientAudio(roles, noseSpeed) {
  let ts = millis();
  let s  = constrain(noseSpeed, 0, 15);

  droneFilter.freq(map(s, 0, 15, 150, 4000));

  // drone pitch：闭嘴时固定，张嘴时加wobble（轻微颤抖）
  // wobble频率约0.3Hz，幅度随mouthEnergy增大
  // 这是让底噪在张嘴期间持续演化、不静止的关键
  let droneBaseFreq = 35 + s * 0.5;
  if (currentlyOpen || mouthEnergy > 20) {
    let wobbleDepth = map(mouthEnergy, 20, 100, 1, 8); // Hz
    let wobble = sin(millis() * 0.002) * wobbleDepth;  // 约0.3Hz周期
    droneOsc.freq(droneBaseFreq + wobble);
  } else {
    droneOsc.freq(droneBaseFreq);
  }

  // 张嘴时drone音量加倍（配合撕裂层形成厚重底噪）
  let bassGate   = (stepCount%4===2) ? 0.1 : 1.0;
  if (mouthEnergy>30) bassGate = map(mouthEnergy, 30, 100, 1.0, 2.5);
  let baseVolume = map(constrain(mouthEnergy,0,100), 0, 100, 0.05, 0.4);
  droneOsc.amp(baseVolume*bassGate, 0.05);

  // ===== 五台手机角色音频效果 =====

  // ROLE 0: PULSE — hi-hat镲片层
  if (roles[0] > 15) {
    let bf = map(roles[0], 15, 180, 5000, 9000);
    alarmOsc.setType('square');
    alarmOsc.freq(bf + sin(ts * 0.05) * 300);
    alarmFilter.freq(bf * 1.1);
    alarmFilter.res(25);
    // 音量大幅推高：0.02→0.08 改为 0.08→0.35
    alarmOsc.amp(map(roles[0], 15, 180, 0.08, 0.35), 0.03);
  } else {
    alarmOsc.amp(0, 0.1);
  }

  // ROLE 1: RIFT — 旋律层，E小调五声音阶
  // 问题修复：ghostSine音量太小，推高到0.5；加入sawtooth增加音色厚度
  if (roles[1] > 15) {
    const pentatonic = [82.4, 123.5, 146.8, 164.8, 196.0, 220.0, 246.9];
    let noteIdx = floor(map(roles[1], 15, 180, 0, pentatonic.length - 1));
    noteIdx = constrain(noteIdx, 0, pentatonic.length - 1);
    let noteFreq = pentatonic[noteIdx];
    // 基音 + 八度，两个声部叠加
    ghostSine.freq(noteFreq * 2);
    ghostSine.amp(map(roles[1], 15, 180, 0.15, 0.50), 0.1); // 大幅推高
    ghostNoise.amp(map(roles[1], 15, 180, 0.03, 0.12), 0.1);
    // 用droneOsc作为第二旋律声部（sawtooh更有摇滚质感）
    // 注意：只在RIFT激活时临时借用droneOsc的高频，正常底噪逻辑不变
    droneOsc.freq(noteFreq); // 基音
  } else {
    ghostSine.amp(0, 0.15);
    ghostNoise.amp(0, 0.15);
  }

  // ROLE 2: VOID — 次低频共鸣层
  // 问题修复：20-45Hz在小扬声器上几乎听不到，改为60-90Hz可感知低频
  // 同时增大音量
  if (roles[2] > 15) {
    let voidFreq = map(roles[2], 15, 180, 55, 90); // 提高到可感知频段
    let amDepth  = map(roles[2], 15, 180, 0.4, 1.0);
    let amRate   = map(roles[2], 15, 180, 0.4, 1.2);
    let amMod    = (sin(ts * amRate * 0.001 * TWO_PI) * 0.5 + 0.5) * amDepth + (1 - amDepth);
    distOsc.freq(voidFreq + random(-1, 1));
    distFilter.freq(map(roles[2], 15, 180, 150, 400));
    // 音量大幅推高：0.08→0.35 改为 0.2→0.7
    distOsc.amp(map(roles[2], 15, 180, 0.20, 0.70) * amMod, 0.04);
  } else {
    distOsc.amp(0, 0.2);
  }

  // ROLE 3: GLITCH — 故障触发层
  if (roles[3] > 30) {
    let glitchProb = map(roles[3], 30, 180, 0.02, 0.18);
    if (random() < glitchProb && tearActive) {
      tearShaper.curve = makeDistortionCurve(random(100, 700));
      if (formantActive && formantF2) {
        let ac = getAudioContext();
        formantF2.frequency.setValueAtTime(random(200, 3500), ac.currentTime);
      }
    }
    howlOsc.freq(map(roles[3], 30, 180, 600, 4000) + sin(frameCount * 0.4) * 150);
    // 推高音量：0.02→0.12 改为 0.08→0.35
    howlOsc.amp(map(roles[3], 30, 180, 0.08, 0.35), 0.04);
  } else {
    howlOsc.amp(0, 0.15);
  }

  // ROLE 4: SURGE — 全局能量推进器
  if (roles[4] > 15) {
    let surgeRatio = map(roles[4], 15, 180, 0, 1);
    let sp = map(roles[4], 15, 180, 1.001, 1.020);
    for (let i = 0; i < 5; i++) {
      let osc = shepardOscs[i];
      let nf  = osc.getFreq() * sp;
      if (nf > baseFreq * pow(2, 5)) nf = baseFreq;
      osc.freq(nf);
      // 推高Shepard音量：0.12 改为 0.22
      osc.amp(sin(map(log(nf/baseFreq)/log(2), 0, 5, 0, 1) * PI) * surgeRatio * 0.22, 0.05);
    }
    if (kickGain) {
      let ac = getAudioContext();
      kickGain.gain.setTargetAtTime(map(surgeRatio, 0, 1, 0.8, 2.2), ac.currentTime, 0.08);
    }
    if (bassGainNode) {
      let ac = getAudioContext();
      bassGainNode.gain.setTargetAtTime(map(surgeRatio, 0, 1, 1.0, 2.5), ac.currentTime, 0.08);
    }
  } else {
    shepardOscs.forEach(o => o.amp(0, 0.2));
    if (kickGain)    { let ac=getAudioContext(); kickGain.gain.setTargetAtTime(0.8, ac.currentTime, 0.2); }
    if (bassGainNode){ let ac=getAudioContext(); bassGainNode.gain.setTargetAtTime(1.0, ac.currentTime, 0.2); }
  }
}

// ================= [ 模块 9: 视觉渲染 ] =================
function renderVisuals(txt, d, isRoaring, roles, faceScale) {
  background(0);
  let activeD   = constrain(d, 5, 30);
  let forceRoar = isRoaring || isHiveMode;

  // ===== 手机角色视觉联动 =====
  // 在人脸渲染之前画，作为背景层

  // ROLE 0: PULSE — 画面四边闪烁光条，随摇晃节奏脉冲
  if (roles[0] > 15) {
    let pulseAlpha = map(roles[0], 15, 180, 20, 120);
    let barW = map(roles[0], 15, 180, 3, 18);
    noStroke(); fill(0, 255, 180, pulseAlpha);
    // 四条边光条
    rect(0, 0, barW, height);              // 左
    rect(width-barW, 0, barW, height);     // 右
    rect(0, 0, width, barW);              // 上
    rect(0, height-barW, width, barW);    // 下
  }

  // ROLE 1: RIFT — 人脸线条颜色漂移（通过改变gradient色调实现）
  // 存储RIFT强度，供下面人脸渲染使用
  let riftStrength = roles[1] > 15 ? map(roles[1], 15, 180, 0, 1) : 0;

  // ROLE 2: VOID — 背景低频波纹，缓慢涟漪
  if (roles[2] > 15) {
    let waveAlpha = map(roles[2], 15, 180, 8, 40);
    let waveCount = 4;
    noFill(); stroke(80, 0, 255, waveAlpha);
    strokeWeight(1);
    for (let i = 0; i < waveCount; i++) {
      let phase = (millis() * 0.0005 + i * 0.5) % 1;
      let r = phase * max(width, height) * 0.8;
      ellipse(width/2, height/2, r * 2, r * 1.2);
    }
    noStroke();
  }

  // ROLE 3: GLITCH — 随机扫描线故障
  if (roles[3] > 30) {
    let glitchLines = floor(map(roles[3], 30, 180, 0, 8));
    for (let i = 0; i < glitchLines; i++) {
      if (random() < 0.4) {
        let y   = random(height);
        let h   = random(2, 12);
        let col = random() < 0.5 ? color(255, 0, 80, random(60, 180))
                                 : color(0, 255, 200, random(40, 120));
        fill(col); noStroke();
        rect(0, y, width, h);
        // 水平位移故障：复制一条错位的线
        let offset = random(-40, 40);
        let sliceW = random(50, 200);
        let sliceX = random(width - sliceW);
        fill(255, 0, 80, random(80, 200));
        rect(sliceX + offset, y, sliceW, h);
      }
    }
  }

  // ROLE 4: SURGE — 全画面亮度脉冲（白色闪光叠加）
  if (roles[4] > 15) {
    let surgeAlpha = map(roles[4], 15, 180, 0, 60);
    // 柔和的金黄色光晕叠加
    fill(255, 220, 0, surgeAlpha);
    noStroke();
    rect(0, 0, width, height);
  }

  push();
  // 震动：mouthEnergy驱动 + SURGE(role4)放大
  let surgeBoost = roles[4] > 15 ? map(roles[4], 15, 180, 1.0, 2.5) : 1.0;
  if (forceRoar || mouthEnergy > 20) {
    let er     = map(mouthEnergy, 0, 100, 0, 1);
    let shakeX = map(er, 0, 1, 1, 8) * surgeBoost;
    let shakeY = map(er, 0, 1, 0.5, 4) * surgeBoost;
    translate(random(-shakeX, shakeX), random(-shakeY, shakeY));
  }
  translate(width,0); scale(-1,1);

  if (smoothedKeypoints.length>0 && voiceStarted) {
    let kp   = smoothedKeypoints, nose = kp[1];

    function getSmallPt(idx) {
      if (!kp[idx]) return {x:width/2,y:height/2};
      return {
        x: lerp(kp[idx].x,nose.x,0.22)+width/2-nose.x,
        y: lerp(kp[idx].y,nose.y,0.22)+height/2-nose.y+50
      };
    }

    // 保存鼻子屏幕坐标（镜像修正）供粒子系统使用
    let nosePt = getSmallPt(1);
    noseScreenX = width - nosePt.x;
    noseScreenY = nosePt.y;

    // ===== 侧脸检测 =====
    // 用左耳(234)和右耳(454)的原始x坐标差值判断侧脸程度
    // 正脸：两耳x差值大（约150-250px）
    // 侧脸：差值趋近于0，一侧耳朵被遮挡
    let leftEarX  = kp[234] ? kp[234].x : 0;
    let rightEarX = kp[454] ? kp[454].x : 0;
    let earSpan   = abs(rightEarX - leftEarX); // 两耳水平距离

    // 用脸部高度（额顶到下巴）归一化耳距，避免距离摄像头远近的影响
    let faceH     = dist(kp[10].x,kp[10].y, kp[152].x,kp[152].y);
    // 正脸时 earSpan/faceH 约0.7-1.0，侧脸时趋近于0
    let earRatio  = faceH > 0 ? earSpan / faceH : 1.0;

    // earRatio < 0.35 开始淡出，< 0.15 完全透明
    // 平滑过渡：lerp避免突变
    let targetAngleRatio = map(constrain(earRatio, 0.15, 0.45), 0.45, 0.15, 0, 1);
    faceAngleRatio = lerp(faceAngleRatio, targetAngleRatio, 0.1);

    // alpha：正脸255，侧脸趋向0
    faceAlpha = map(faceAngleRatio, 0, 1, 255, 0);
    // 用drawingContext.globalAlpha控制整个人脸层的透明度
    drawingContext.globalAlpha = faceAlpha / 255;

    let gradient = drawingContext.createLinearGradient(0,height/2-150,0,height/2+150);
    if (forceRoar) {
      gradient.addColorStop(0,   'rgb(255,0,0)');
      gradient.addColorStop(0.35,'rgb(255,50,0)');
      gradient.addColorStop(1,   'rgb(255,255,0)');
    } else if (riftStrength > 0.1) {
      // RIFT激活：青色向橙色漂移
      let r1 = Math.round(lerp(150, 255, riftStrength));
      let g1 = Math.round(lerp(0,   100, riftStrength));
      let b1 = Math.round(lerp(255, 0,   riftStrength));
      let r2 = Math.round(lerp(0,   255, riftStrength));
      let g2 = Math.round(lerp(255, 150, riftStrength));
      let b2 = Math.round(lerp(255, 0,   riftStrength));
      gradient.addColorStop(0,   `rgb(${r1},${g1},${b1})`);
      gradient.addColorStop(0.35,`rgb(${r2},${g2},${b2})`);
      gradient.addColorStop(1,   `rgb(${r2},${g2},${b2})`);
    } else {
      gradient.addColorStop(0,   'rgb(150,0,255)');
      gradient.addColorStop(0.35,'rgb(0,255,255)');
      gradient.addColorStop(1,   'rgb(0,255,255)');
    }

    drawingContext.shadowBlur  = forceRoar ? 25 : 15;
    drawingContext.shadowColor = forceRoar ? 'rgba(255,50,0,0.8)' : 'rgba(0,255,255,0.6)';
    stroke(255); drawingContext.strokeStyle = gradient; noFill();

    if (forceRoar) {
      let hairIdx = [127,162,21,54,103,67,109,10,338,297,332,284,251,389,356];
      strokeWeight(4*faceScale);
      beginShape();
      for (let i=0; i<hairIdx.length-1; i++) {
        let pt = getSmallPt(hairIdx[i]);
        vertex(pt.x,pt.y);
        if (i%2===0) {
          let vx   = pt.x-width/2;
          let dirX = vx*0.03, dirY=-1.2;
          let mag  = max(0.1,dist(0,0,dirX,dirY));
          dirX = (dirX/mag)+random(-0.1,0.1); dirY=dirY/mag;
          let ex      = map(mouthEnergy,0,100,0.3,4.5);
          let baseLen = map(abs(vx),0,100,220,100)*faceScale;
          vertex(pt.x+dirX*baseLen*ex*random(0.8,1.2),
                 pt.y+dirY*baseLen*ex*random(0.8,1.2));
        }
      }
      vertex(getSmallPt(356).x,getSmallPt(356).y);
      endShape();
    }

    strokeWeight((forceRoar?3.5:2.5)*faceScale);
    beginShape();
    for (let i=0; i<ONE_LINE_PATH.length; i++) {
      let pt = getSmallPt(ONE_LINE_PATH[i]);
      curveVertex(pt.x,pt.y);
      if (i===0||i===ONE_LINE_PATH.length-1) curveVertex(pt.x,pt.y);
    }
    endShape();

    let earScale = 110*faceScale;
    function drawEar(idx,isRight) {
      let p=getSmallPt(idx),chin=getSmallPt(152),top=getSmallPt(10);
      let outX=p.x-(width/2),outY=p.y-(height/2+50),outLen=dist(0,0,outX,outY);
      let ux=outX/outLen,uy=outY/outLen;
      let upX=top.x-chin.x,upY=top.y-chin.y,fL=dist(0,0,upX,upY);
      let nx=upX/fL,ny=upY/fL;
      beginShape(); curveVertex(p.x,p.y); curveVertex(p.x,p.y);
      if (isRight) {
        vertex(p.x+ux*earScale*0.1+nx*earScale*0.3,p.y+uy*earScale*0.1+ny*earScale*0.3);
        vertex(p.x+ux*earScale*0.3+nx*earScale*0.05,p.y+uy*earScale*0.3+ny*earScale*0.05);
        vertex(p.x+ux*earScale*0.15-nx*earScale*0.25,p.y+uy*earScale*0.15-ny*earScale*0.25);
      } else {
        vertex(p.x+ux*earScale*0.15-nx*earScale*0.25,p.y+uy*earScale*0.15-ny*earScale*0.25);
        vertex(p.x+ux*earScale*0.3+nx*earScale*0.05,p.y+uy*earScale*0.3+ny*earScale*0.05);
        vertex(p.x+ux*earScale*0.1+nx*earScale*0.3,p.y+uy*earScale*0.1+ny*earScale*0.3);
      }
      curveVertex(p.x,p.y); curveVertex(p.x,p.y); endShape();
    }
    drawEar(454,true); drawEar(234,false);

    if (forceRoar) {
      push();
      let blurAmt=50*faceScale,eW=45*faceScale,eH=28*faceScale,pi=12*faceScale;
      drawingContext.shadowBlur=blurAmt; drawingContext.shadowColor='rgba(120,0,70,0.5)';
      fill(60,0,30,150); noStroke();
      let le=getSmallPt(33); ellipse(le.x+pi,le.y,eW,eH);
      let re=getSmallPt(263); ellipse(re.x-pi,re.y,eW,eH);

      let eyeSize=8*faceScale;
      drawingContext.shadowBlur=15*faceScale; drawingContext.shadowColor='red';
      let lp=kp[468]?getSmallPt(468):null;
      let rp=kp[473]?getSmallPt(473):null;
      fill(255,0,0); noStroke();
      if (lp&&rp&&lp.x!==undefined) {
        ellipse(lp.x,lp.y,eyeSize,eyeSize); ellipse(rp.x,rp.y,eyeSize,eyeSize);
      } else {
        let lC={x:(getSmallPt(159).x+getSmallPt(145).x)/2,y:(getSmallPt(159).y+getSmallPt(145).y)/2};
        let rC={x:(getSmallPt(386).x+getSmallPt(374).x)/2,y:(getSmallPt(386).y+getSmallPt(374).y)/2};
        ellipse(lC.x,lC.y,eyeSize,eyeSize); ellipse(rC.x,rC.y,eyeSize,eyeSize);
      }

      noFill(); stroke(220); strokeWeight(2.8*faceScale);
      drawingContext.shadowBlur=10*faceScale;
      let brow=getSmallPt(70); ellipse(brow.x,brow.y,9*faceScale,15*faceScale);
      let lpLip=getSmallPt(17); ellipse(lpLip.x,lpLip.y+10*faceScale,8*faceScale,14*faceScale);

      let rEyeB=getSmallPt(374),rMouth=getSmallPt(291),rCheek=getSmallPt(323);
      let bPt={x:lerp(rEyeB.x,rCheek.x,0.4),y:lerp(rEyeB.y,rMouth.y,0.5)-5*faceScale};
      let ls=faceScale*0.75;
      let bG=drawingContext.createLinearGradient(bPt.x,bPt.y-40*ls,bPt.x,bPt.y+40*ls);
      bG.addColorStop(0,'#FFEA00'); bG.addColorStop(1,'#FF1100');
      drawingContext.strokeStyle=bG; drawingContext.shadowColor='#FF4400';
      drawingContext.shadowBlur=15*ls; strokeWeight(3.5*ls);
      beginShape();
      vertex(bPt.x-15*ls,bPt.y-40*ls); vertex(bPt.x+15*ls,bPt.y-45*ls);
      vertex(bPt.x-2*ls, bPt.y-5*ls);  vertex(bPt.x+18*ls, bPt.y-8*ls);
      vertex(bPt.x-15*ls,bPt.y+30*ls); vertex(bPt.x,       bPt.y);
      vertex(bPt.x-25*ls,bPt.y+5*ls);
      endShape(CLOSE);
      pop();
    }
  }
  pop();

  // Canvas 2D不受p5 push/pop管理，必须手动清零
  drawingContext.shadowBlur  = 0;
  drawingContext.shadowColor = 'transparent';
  drawingContext.globalAlpha = 1.0; // 重置透明度，不影响后续HUD和字幕渲染

  // HUD 左上角：序号 + 名字，简洁
  let hudColor = forceRoar ? color(255,100,0) : color(0,255,255);
  noStroke(); textAlign(LEFT,TOP); textSize(11); textFont('monospace');
  for (let i=0; i<5; i++) {
    fill(roles[i]>15 ? color(255,50,0) : hudColor);
    text(`${i}  ${roleNames[i]}`, 20, 20+i*14);
  }

  // 调试模式提示
  if (formantSoloMode) {
    fill(255, 255, 0);
    textSize(11);
    text('[ FORMANT SOLO ]  F=exit  move head + open mouth', 20, 115);
  }

  // 数据源右上角（小字，调试用）
  fill(forceRoar ? color(255,80,0,120) : color(0,200,200,80));
  textSize(9); textAlign(RIGHT,TOP);
  text(dataSourceLabel, width-15, 15);

  // ===== 字幕渲染 =====
  // 闭嘴：居中，底部固定位置
  // 张嘴：词在原位放大，抖动，带旋转，向下掉落淡出
  const SUB_Y     = height - 110;
  const SUB_MAX_W = width - 80;
  const SZ_NORMAL = 26;
  const SZ_ROAR   = 38;

  if (voiceStarted && txt && txt.length > 0) {
    push();
    drawingContext.shadowBlur  = 0;
    drawingContext.shadowColor = 'transparent';
    textFont('monospace'); noStroke();

    if (forceRoar) {
      // 张嘴：只在新词出现时生成一次粒子
      // 词从字幕位置出现，被震动抖落，消失后屏幕空白直到下一个词
      if (lastParticleWord !== txt) {
        lastParticleWord = txt;

        // 先把旧粒子加速消失（新词来了，旧词快速退场）
        for (let p of wordParticles) p.decay = max(p.decay, 0.08);

        let words = txt.split(' ').filter(w => w.length > 0);
        textSize(SZ_ROAR); textStyle(BOLD);

        // 计算居中起始X
        let totalW = 0;
        for (let w of words) totalW += textWidth(w) + SZ_ROAR * 0.4;
        let curX = width/2 - totalW/2;

        for (let i = 0; i < words.length; i++) {
          let w  = words[i];
          let ww = textWidth(w);
          let wx = curX + ww/2;
          let wy = SUB_Y + SZ_ROAR/2;

          // 每个词有短暂的出现延迟（i * 40ms），错落感
          // 用life从略大于1开始，让词先"停在原位"再掉落
          // life > 1 的部分作为静止等待期，life <= 1 才开始掉落
          let holdFrames = i * 3; // 词i比词0晚3帧开始掉落

          // 向下掉落：能量越高初始速度越大，像被狠狠一震
          let vy = random(0.8, 2.0) * map(mouthEnergy, 30, 100, 0.6, 2.2);
          let vx = random(-1.2, 1.2);

          // 旋转：向下掉落时自然倾斜
          let ang  = random(-8, 8);   // 初始小角度
          let spin = random(-3.5, 3.5); // 掉落过程中旋转

          let g = constrain(map(mouthEnergy, 30, 100, 220, 40) + random(-15,15), 0, 255);
          let b = constrain(map(mouthEnergy, 30, 100, 80,  0)  + random(-10,10), 0, 255);

          wordParticles.push({
            word: w, x: wx, y: wy,
            vx, vy, angle: ang, spin,
            sz: SZ_ROAR * random(0.9, 1.1),
            r: 255, g, b,
            alpha: 255, life: 1.0 + holdFrames * 0.02,
            decay: random(0.014, 0.024),
            gravity: random(0.10, 0.22),
            held: holdFrames, // 还剩多少帧静止
          });
          curX += ww + SZ_ROAR * 0.4;
        }
      }

      // 更新并渲染粒子
      wordParticles = wordParticles.filter(p => p.life > 0);
      for (let p of wordParticles) {
        if (p.held > 0) {
          // 静止等待期：词在原位轻微抖动（被震动的感觉）
          p.held--;
          let jx = random(-2, 2);
          let jy = random(-1, 1);
          push();
          translate(p.x + jx, p.y + jy);
          rotate(radians(p.angle + random(-1,1)));
          textSize(p.sz); textStyle(BOLD); textAlign(CENTER, CENTER);
          fill(p.r, p.g, p.b, p.alpha);
          text(p.word, 0, 0);
          pop();
        } else {
          // 掉落期：物理运动 + 淡出
          p.x += p.vx; p.y += p.vy;
          p.vy += p.gravity;
          p.vx *= 0.97;
          p.angle += p.spin;
          p.life  -= p.decay;
          p.alpha  = constrain(p.life * 255, 0, 255);
          push();
          translate(p.x, p.y); rotate(radians(p.angle));
          textSize(p.sz); textStyle(BOLD); textAlign(CENTER, CENTER);
          fill(p.r, p.g, p.b, p.alpha);
          text(p.word, 0, 0);
          pop();
        }
      }

    } else {
      // 闭嘴：加速清除残留粒子
      for (let p of wordParticles) p.decay = max(p.decay, 0.05);
      wordParticles = wordParticles.filter(p => p.life > 0);
      for (let p of wordParticles) {
        p.x += p.vx; p.y += p.vy;
        p.vy += p.gravity; p.vx *= 0.98; p.vy *= 0.99;
        p.angle += p.spin; p.life -= p.decay; p.alpha = p.life * 255;
        push();
        translate(p.x, p.y); rotate(radians(p.angle));
        textSize(p.sz); textStyle(BOLD); textAlign(CENTER, CENTER);
        fill(p.r, p.g, p.b, p.alpha);
        text(p.word, 0, 0);
        pop();
      }

      // 底部字幕：居中，白色
      textSize(SZ_NORMAL); textStyle(NORMAL); textAlign(CENTER, TOP);
      fill(255);
      let dispTxt = fitTextToWidth(txt, SUB_MAX_W, SZ_NORMAL);
      text(dispTxt, width/2, SUB_Y);
    }
    pop();

  } else if (!voiceStarted) {
    drawStandbyScreen();
  }
}

function fitTextToWidth(txt, maxW, sz) {
  if (!txt||txt.length===0) return "";
  textSize(sz);
  if (textWidth(txt) <= maxW) return txt;
  let ell   = "...";
  let avail = maxW - textWidth(ell);
  let result = "";
  for (let i=0; i<txt.length; i++) {
    if (textWidth(result+txt[i]) > avail) break;
    result += txt[i];
  }
  return result + ell;
}

function drawStandbyScreen() {
  push();
  drawingContext.shadowBlur = 0;
  textFont('monospace'); textAlign(CENTER, CENTER);

  let pulse = sin(frameCount * 0.04) * 0.5 + 0.5;
  let glow  = map(pulse, 0, 1, 80, 255);

  // 主行：ARE YOU READY
  drawingContext.shadowBlur  = map(pulse, 0, 1, 8, 35);
  drawingContext.shadowColor = `rgba(0,255,100,${map(pulse,0,1,0.3,1.0)})`;
  fill(0, glow, map(pulse, 0, 1, 50, 110));
  textSize(52); textStyle(BOLD);
  text("ARE YOU READY", width/2, height/2 - 30);

  // 第二行：HIT IT — 闪烁
  let blink = (sin(frameCount * 0.12) > 0.3) ? 220 : 40;
  drawingContext.shadowBlur  = 6;
  drawingContext.shadowColor = `rgba(0,255,100,0.5)`;
  fill(0, 200, 80, blink);
  textSize(22); textStyle(NORMAL);
  text("HIT IT", width/2, height/2 + 28);

  drawingContext.shadowBlur = 0;
  pop();
}

// ================= [ 模块 10: 交互事件 ] =================
function mousePressed() {
  if (getAudioContext().state!=='running') getAudioContext().resume();

  if (!audioInitialized) {
    userStartAudio();
    droneOsc.start(); droneOsc.amp(0.02,0.5);
    metalOsc.start(); alarmOsc.start();
    ghostNoise.start(); ghostSine.start();
    distOsc.start(); howlOsc.start();
    shepardOscs.forEach(o=>o.start());
    audioInitialized = true;
    startAudioScheduler();

    let ac = getAudioContext();

    // kick总增益节点
    kickGain = ac.createGain();
    kickGain.gain.value = 0.8;
    kickGain.connect(ac.destination);

    // 贝斯线总增益节点
    bassGainNode = ac.createGain();
    bassGainNode.gain.value = 1.0;
    bassGainNode.connect(ac.destination);

    // 高频噪音层
    initHiNoise(ac);

    // Formant合成：机器声道
    initFormantSynth(ac);

    // 撕裂系统
    initTearSystem(ac);
  }

  if (!voiceStarted) {
    voiceStarted  = true;
    lastFetchTime = -999999;
    injectFallbackContent();
    activeWord    = "neural buffer overflow cascade";
    remainingText = activeWord;
    performVocal(activeWord, false, width/2, 0, 0, true);
  }
}

function triggerHiveProtocol() {
  isHiveMode = true;
  window.speechSynthesis.cancel();
  // HIVE：所有手机继续各自角色，电脑端进入极端状态
  // 不再强制改变手机角色（没有role5了）
}

// 调试模式标志
let formantSoloMode = false; // F键：只听formant，其他层静音
let ttsMuted        = false; // T键：静音TTS

function keyPressed() {
  if (key==='r'||key==='R') {
    isHiveMode=false; chaosMeter=0; roleCounter=0; bandMembers={}; mouthEnergy=0;
  }

  // F键：formant solo模式
  // 开启时把tear、drone、kick、hiNoise全部静音，只留formant
  // 方便单独确认formant是否在工作、音色是否正确
  if (key==='f'||key==='F') {
    formantSoloMode = !formantSoloMode;
    if (!audioInitialized) return;
    let ac = getAudioContext();
    let t  = ac.currentTime;
    if (formantSoloMode) {
      // 静音其他所有层
      if (tearGain)    tearGain.gain.setTargetAtTime(0, t, 0.05);
      if (kickGain)    kickGain.gain.setTargetAtTime(0, t, 0.05);
      if (bassGainNode) bassGainNode.gain.setTargetAtTime(0, t, 0.05);
      if (hiNoiseGain) hiNoiseGain.gain.setTargetAtTime(0, t, 0.05);
      droneOsc.amp(0, 0.1);
      metalOsc.amp(0, 0.1);
      if (formantGain) formantGain.gain.setTargetAtTime(0.8, t, 0.05);
      window.speechSynthesis.cancel();
    } else {
      // 恢复所有层
      if (kickGain)     kickGain.gain.setTargetAtTime(0.8, t, 0.1);
      if (bassGainNode) bassGainNode.gain.setTargetAtTime(1.0, t, 0.1);
      if (hiNoiseGain)  hiNoiseGain.gain.setTargetAtTime(0.015, t, 0.1);
    }
  }

  // 刷新Reddit数据（原来F键的功能移到G键）
  if (key==='g'||key==='G') lastFetchTime = -999999;
}
