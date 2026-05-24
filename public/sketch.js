// SWARM — Live Performance System
// The performer controls sound and visuals using face movements (mouth open/close, head position).
// Audience members join by scanning a QR code on their phones and shaking to trigger effects.
// Up to 5 phones can connect at the same time, each assigned a different role.
// Audio layers: TTS speech + distortion + formant synthesis + kick/bass + 5 phone roles
// Visual layers: ml5 FaceMesh face outline + each phone role adds its own visual effect
// Built with: p5.js + ml5.js + Web Audio API + Socket.io

let stepCount = 0;
let lastStutterStep = -1;

p5.disableFriendlyErrors = true;

const ONE_LINE_PATH = [
  10,338,297,332,284,251,389,356,454,323,361,288,397,365,379,378,400,377,152,148,176,149,150,136,172,58,132,93,234,127,162,21,54,103,67,109,10,
  70,63,105,66,107,33,160,158,133,153,144,33,285,295,282,283,276,263,387,385,373,380,263,168,6,197,195,5,4,
  19,0,267,269,270,409,291,375,321,405,314,17,84,181,91,146,61,185,40,39,37,0
];

// Global variables — faceMesh and video are used by ml5, smoothedKeypoints stores the smoothed landmark positions
let faceMesh, video, faces = [], smoothedKeypoints = [];
let options = { maxFaces:1, refineLandmarks:true, flipHorizontal:true };

// Two queues for TTS content — calm is read when mouth is closed, roar when mouth is open
let calmQueue = [];
let roarQueue  = [];

const SUBREDDITS = ['all','worldnews','technology','collapse','dataisbeautiful'];
let redditFetchIndex = 0;
let lastFetchTime    = -999999;
const FETCH_INTERVAL = 60000;
let isFetching       = false;
let dataSourceLabel  = "SIGNAL PENDING";

const VERB_TIERS = {
  violent: ["kill","destroy","crash","explode","collapse","burn","attack","die","dead","war","bomb","murder","riot","fail","break","crush","ban","block","cut","fire","shoot","storm","flood","freeze","bleed","abandon","betray"],
  tense:   ["warn","fear","risk","threat","force","demand","fight","struggle","resist","arrest","charge","claim","deny","reject","leak","expose","reveal","accuse","protest","strike","surge","drop","spike","fall","rise","hit","lose","win"],
  kinetic: ["launch","build","push","drive","run","race","jump","pull","send","move","spread","grow","expand","reach","break","cross","enter","leave","return","open","close","start","stop","change","shift","turn"]
};
const ALL_VERBS = [...VERB_TIERS.violent, ...VERB_TIERS.tense, ...VERB_TIERS.kinetic];

// mouthEnergy tracks how open the mouth is, smoothed with a spring-damper model so it feels physical
let mouthEnergy   = 0;
let prevMouthDist = 0;
const SPRING_TENSION      = 0.97;
const SPRING_TENSION_FAST = 0.93;

// TTS state variables
let voiceStarted = false, isScreamingMode = false;
let targetVoiceEN = null;
let prevNose = {x:0,y:0}, smoothedNoseSpeed = 0, currentlyOpen = false;
let activeWord = "", remainingText = "";
let lastWordStartTime = 0;    // timestamp when the current word started
// Maximum time for one word during roar mode — at very slow TTS rate a word can last 8-10s, which is too long
const MAX_ROAR_WORD_MS = 5000;

// Word particle system — when mouth opens, words fly out from the nose position and fade away
let wordParticles = [];
let lastParticleWord = "";

// Nose screen coordinates (after mirror correction), used by the word particle system
let noseScreenX = 0;
let noseScreenY = 0;

// Key face point screen coordinates (mirror corrected) — updated each frame in renderVisuals, used by phone visual effects
let mouthScreenX = 0; // mouth center, used by SURGE spiral
let mouthScreenY = 0;
let leftEarScreenX = 0;  // left ear position
let leftEarScreenY = 0;
let rightEarScreenX = 0;
let rightEarScreenY = 0;

// Announce events — when a new phone joins, a visual burst plays to signal the change
let announceEvents = []; // {role, startTime, duration}

// Silence mode — press S to drop all audio to near zero, press again to burst back
let silenceMode = false;
let silenceTarget = false;    // target silence state
let silenceFade = 0;          // 0 = normal, 1 = fully silent

// TTS beat alignment — new words only trigger on the downbeat
let ttsWaitForBeat = false;   // waiting for the next downbeat
let pendingWord = "";          // word waiting to be triggered on the beat

// Side-face detection — uses the ratio of ear span to face height, face fades out when turning sideways
let faceAngleRatio = 0;  // 0 = facing forward, 1 = fully side-on, smoothed
let faceAlpha = 255;     // face render opacity, fades out when turning sideways

// Phone connection state and role assignment
let socket, bandMembers = {}, roleCounter = 0;
let roleNames = ["01 PULSE","02 RIFT","03 VOID","04 GLITCH","05 SURGE"];
let isHiveMode = false, chaosMeter = 0, audioInitialized = false;

// p5.js oscillators for the main sound layers
let droneOsc, droneFilter, metalOsc, metalReverb;
let alarmOsc, alarmFilter, ghostNoise, ghostSine;
let distOsc, howlOsc, distFilter;
let shepardOscs = [], baseFreq = 45;
let schedulerNextBeatTime = 0;

// Step duration — 130BPM when calm, speeds up to 170BPM when mouth opens
let currentStepDuration = 0.115; // in seconds, AudioContext time units
let targetStepDuration  = 0.115;

// Native Web Audio nodes for kick drum and high-frequency noise layer
let kickGain      = null;
let hiNoiseGain   = null;
let hiNoiseSource = null;
let hiNoiseFilter = null;

// Bass line gain node
let bassGainNode = null; // bass master gain node

// Formant synthesis — simulates vocal tract resonance to create a robotic throat sound
// Activates when mouth opens, changes shape based on mouth distance and nose X position
let formantActive = false;
let formantSrc    = null;  // sawtooth oscillator as vocal source
let formantGain   = null;  // master gain
let formantF1     = null;  // first formant — controls vowel openness
let formantF2     = null;  // second formant — controls front/back of vowel
let formantF3     = null;  // third formant — controls brightness
let formantF1G    = null;  // F1 gain node
let formantF2G    = null;  // F2 gain node
let formantF3G    = null;  // F3 gain node
let formantDist   = null;  // light distortion to roughen the robotic voice

// Tear/distortion system — built with native Web Audio nodes, separate from p5.sound
// Creates the heavy distorted sound when the performer opens their mouth
let tearAudioCtx = null;   // direct reference to the AudioContext
let tearGain     = null;   // tear system master gain
let tearOsc1     = null;   // tear oscillator 1: fundamental frequency
let tearOsc2     = null;   // tear oscillator 2: slightly detuned to create beating
let tearShaper   = null;   // WaveShaper for hard distortion
let sweepLFO     = null;   // LFO for frequency sweep — creates the howling effect
let sweepGain    = null;   // LFO depth control
let tearActive   = false;  // whether the tear system is active

// Creates a WaveShaper distortion curve — higher amount means more distortion
function makeDistortionCurve(amount) {
  let n = 256;
  let curve = new Float32Array(n);
  let deg = Math.PI / 180;
  for (let i = 0; i < n; i++) {
    let x = (i * 2) / n - 1;
    // Soft clipping formula — keeps some dynamics but adds harmonic overtones
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

  // filter sweep LFO — very slow oscillator that keeps the sound evolving
  // 0.15Hz = one cycle every 6 seconds, slow enough to feel like breathing
  // sounds like a guitar feedback slowly rotating in space
  let filterSweepLFO  = ac.createOscillator();
  let filterSweepGain = ac.createGain();
  filterSweepLFO.type = 'sine';
  filterSweepLFO.frequency.value = 0.15;  // very slow — one cycle every 6 seconds
  filterSweepGain.gain.value = 60;         // sweep range ±60Hz
  filterSweepLFO.connect(filterSweepGain);
  filterSweepLFO.start();

  // Bandpass filter modulated by the LFO to create a wah-wah effect
  let wahFilter = ac.createBiquadFilter();
  wahFilter.type = 'bandpass';
  wahFilter.frequency.value = 400;
  wahFilter.Q.value = 3.0;
  filterSweepGain.connect(wahFilter.frequency); // LFO modulates the filter frequency
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

// Kick drum — a short sine wave that sweeps from 180Hz down to 28Hz in 70ms
// This creates a physical impact feeling in the chest even on small speakers
function fireKick(ac, time, energy) {
  if (!kickGain) return;

  let vol = map(energy, 0, 100, 0.4, 1.3);

  let osc  = ac.createOscillator();
  let gain = ac.createGain();
  osc.connect(gain);
  gain.connect(kickGain);

  // frequency sweep: 180Hz down to 28Hz in 70ms — longer sweep gives a thicker kick
  osc.frequency.setValueAtTime(180, time);
  osc.frequency.exponentialRampToValueAtTime(28, time + 0.07);

  // Volume envelope: instant attack, decays over 120ms — longer tail makes it feel heavier
  gain.gain.setValueAtTime(vol, time);
  gain.gain.exponentialRampToValueAtTime(0.001, time + 0.12);

  osc.start(time);
  osc.stop(time + 0.15);
}

// Bass line — follows the kick rhythm, lower frequency (40-60Hz), slower decay (200ms)
// When mouth is closed: stays on 45Hz. When open: rises to 80Hz with energy, adding tension
function fireBass(ac, time, energy, isOpen) {
  if (!bassGainNode) return;

  // bass frequency: 45Hz when calm, rises to 80Hz when mouth opens
  let freq = isOpen
    ? map(energy, 30, 100, 45, 80)
    : 45;

  let vol = isOpen
    ? map(energy, 30, 100, 0.3, 0.7)
    : 0.35; // lighter when calm so it does not overpower the kick

  let osc  = ac.createOscillator();
  let gain = ac.createGain();
  osc.type = 'sine'; // pure sine wave — cleanest shape for low frequencies
  osc.frequency.setValueAtTime(freq, time);
  osc.connect(gain);
  gain.connect(bassGainNode);

  // Bass envelope: slower decay than kick (200ms) to give a sustained push
  gain.gain.setValueAtTime(vol, time);
  gain.gain.exponentialRampToValueAtTime(0.001, time + 0.20);

  osc.start(time);
  osc.stop(time + 0.25);
}

// High-frequency noise layer — fills the top end of the sound
// Very quiet normally, but adds a sense of pressure. Gets louder when mouth opens
function initHiNoise(ac) {
  // Generate 1 second of white noise
  let bufferSize = ac.sampleRate;
  let buffer     = ac.createBuffer(1, bufferSize, ac.sampleRate);
  let data       = buffer.getChannelData(0);
  for (let i = 0; i < bufferSize; i++) {
    data[i] = Math.random() * 2 - 1;
  }

  // Loop the buffer continuously
  hiNoiseSource = ac.createBufferSource();
  hiNoiseSource.buffer = buffer;
  hiNoiseSource.loop   = true;

  // High-pass filter: only keeps frequencies above 4kHz
  hiNoiseFilter = ac.createBiquadFilter();
  hiNoiseFilter.type            = 'highpass';
  hiNoiseFilter.frequency.value = 4000;
  hiNoiseFilter.Q.value         = 0.5;

  // master gain, starts very low
  hiNoiseGain = ac.createGain();
  hiNoiseGain.gain.value = 0.015; // very quiet, barely noticeable, but removing it makes the sound feel empty

  hiNoiseSource.connect(hiNoiseFilter);
  hiNoiseFilter.connect(hiNoiseGain);
  hiNoiseGain.connect(ac.destination);
  hiNoiseSource.start();
}

// Push the tear/distortion layer up when mouth opens
function activateTear(energy) {
  if (!tearActive || !tearAudioCtx) return;
  let t = tearAudioCtx.currentTime;

  // volume scales with energy — louder when more open
  let targetVol = map(energy, 30, 100, 0.05, 0.45);
  tearGain.gain.cancelScheduledValues(t);
  tearGain.gain.setTargetAtTime(targetVol, t, 0.02); // 20ms attack time

  // pitch rises with energy — sounds like tearing upward
  let targetFreq = map(energy, 30, 100, 60, 180);
  tearOsc1.frequency.cancelScheduledValues(t);
  tearOsc1.frequency.setTargetAtTime(targetFreq, t, 0.05);
  tearOsc2.frequency.setTargetAtTime(targetFreq + 3, t, 0.05);

  // LFO depth increases with energy — more pitch wobble when screaming
  let sweepDepth = map(energy, 30, 100, 20, 120);
  sweepGain.gain.setTargetAtTime(sweepDepth, t, 0.1);

  // distortion amount changes dynamically with energy
  tearShaper.curve = makeDistortionCurve(map(energy, 30, 100, 150, 500));
}

// When mouth closes, let the distortion fade slowly rather than cutting it off
function deactivateTear() {
  if (!tearActive || !tearAudioCtx) return;
  let t = tearAudioCtx.currentTime;
  tearGain.gain.cancelScheduledValues(t);
  tearGain.gain.setTargetAtTime(0, t, 0.3);
  sweepGain.gain.setTargetAtTime(0, t, 0.2);
}

// Sound events when a new phone joins — each role has its own announcement sound
// each role has its own announcement sound so the audience can hear the change
function announceNewMember(role) {
  if (!audioInitialized) return;
  let ac = getAudioContext();
  let t  = ac.currentTime;

  if (role === 0) {
    // PULSE joins: two heavy kicks 0.3s apart
    fireKick(ac, t,       100);
    fireKick(ac, t + 0.3, 100);
    fireBass(ac, t, 100, false);
  } else if (role === 1) {
    // RIFT joins: E major chord appears suddenly and holds for 1.5s
    // ghostSine plays E5, howlOsc plays B5, metalOsc plays E5
    ghostSine.freq(659.3); ghostSine.amp(0.7, 0.05);
    howlOsc.freq(987.8);   howlOsc.amp(0.5, 0.05);
    metalOsc.setType('sine'); metalOsc.freq(659.3, 0.001); metalOsc.amp(0.6, 0.01);
    // return to normal after 1.5s
    setTimeout(() => {
      if(audioInitialized) {
        ghostSine.amp(0.2, 0.3);
        howlOsc.amp(0.15, 0.3);
        metalOsc.amp(0, 0.3);
      }
    }, 1500);
  } else if (role === 2) {
    // VOID joins: bass slides from 45Hz down to 30Hz — a sinking feeling
    if (bassGainNode) {
      let osc  = ac.createOscillator();
      let gain = ac.createGain();
      osc.type = 'sine';
      osc.frequency.setValueAtTime(45, t);
      osc.frequency.exponentialRampToValueAtTime(30, t + 1.5);
      gain.gain.setValueAtTime(0.8, t);
      gain.gain.exponentialRampToValueAtTime(0.001, t + 2.0);
      osc.connect(gain); gain.connect(ac.destination);
      osc.start(t); osc.stop(t + 2.2);
    }
  } else if (role === 3) {
    // GLITCH joins: one full-spectrum explosion then back to normal
    if (tearActive) {
      tearGain.gain.setValueAtTime(0.8, t);
      tearGain.gain.setTargetAtTime(0, t + 0.08, 0.05);
      tearShaper.curve = makeDistortionCurve(900);
      setTimeout(() => { if(audioInitialized) tearShaper.curve = makeDistortionCurve(350); }, 200);
    }
    metalOsc.setType('square'); metalOsc.freq(329.6, 0.001);
    metalOsc.amp(1.2, 0.001);
    setTimeout(() => { if(audioInitialized) metalOsc.amp(0, 0.05); }, 120);
    // SURGE joins: all layers push up 1.8x for 0.3s then pull back — signals the peak is coming
      if (kickGain)    kickGain.gain.setValueAtTime(kickGain.gain.value * 1.8, t);
    if (bassGainNode) bassGainNode.gain.setValueAtTime(bassGainNode.gain.value * 1.8, t);
    if (tearGain)    tearGain.gain.setValueAtTime(0.5, t);
    fireKick(ac, t, 100);
    fireKick(ac, t + 0.15, 80);
    fireKick(ac, t + 0.25, 60);
    setTimeout(() => {
      if(audioInitialized) {
        if (kickGain)    kickGain.gain.setTargetAtTime(0.8, ac.currentTime, 0.2);
        if (bassGainNode) bassGainNode.gain.setTargetAtTime(1.0, ac.currentTime, 0.2);
      }
    }, 400);
  }
}

// Setup — create canvas, start camera, connect to Socket.io server
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
      console.log('phone data:', JSON.stringify(data));
      let now = millis();
      if (!bandMembers[data.id]) {
        let assignedRole = roleCounter % 5;
        bandMembers[data.id] = { role: assignedRole, intensity: 0, lastSeen: now };
        roleCounter++;
        socket.emit('shake', { isHost: true, targetId: data.id, role: assignedRole });
        // trigger announcement sound and visual burst when a new phone joins
        if (audioInitialized) announceNewMember(assignedRole);
        announceEvents.push({ role: assignedRole, startTime: millis(), duration: 1800 });
      }
      bandMembers[data.id].intensity = data.val;
      bandMembers[data.id].lastSeen  = now;
    });
  } catch(e) { console.log("Socket bypassed."); }

  initVoices();
  initBandAudio();

  // TTS heartbeat — keeps the speech synthesis alive in some browsers
  setInterval(() => {
    if (voiceStarted && window.speechSynthesis.speaking) {
      window.speechSynthesis.pause();
      window.speechSynthesis.resume();
    }
  }, 10000);
}

// Create all the p5.js oscillators used in the main sound layers
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

// Fetch Reddit headlines and process them into word queues for TTS
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
    dataSourceLabel = `SIGNAL ACTIVE`;
    processTitlesIntoQueues(titles);
  } catch(e) {
    dataSourceLabel = `SIGNAL LOST`;
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

// Initialize the formant vocal tract synthesizer
function initFormantSynth(ac) {
  // sound source: sawtooth wave, rich in harmonics, shaped by the filters
  // frequency around 80Hz (typical male vocal fundamental range)
  formantSrc = ac.createOscillator();
  formantSrc.type = 'sawtooth';
  formantSrc.frequency.value = 80;

  // master gain, starts at 0 and rises when mouth opens
  formantGain = ac.createGain();
  formantGain.gain.value = 0;
  formantGain.connect(ac.destination);

  // light distortion to make the robotic voice feel rough, not clean
  formantDist = ac.createWaveShaper();
  formantDist.curve = makeDistortionCurve(80); // light distortion — should not overpower the formant tone
  formantDist.oversample = '2x';
  formantDist.connect(formantGain);

  // three bandpass filters for the three formant resonances, each with its own gain
  // F1: first formant — controls vowel openness
  //   closed vowels (oo/oh): F1 low (300-500Hz)
  //   open vowels (ah): F1 high (700-900Hz)
  formantF1  = ac.createBiquadFilter();
  formantF1G = ac.createGain();
  formantF1.type = 'bandpass';
  formantF1.frequency.value = 400; // neutral starting frequency
  formantF1.Q.value = 5;           // narrow bandwidth — formants need to be distinct
  formantF1G.gain.value = 1.0;

  // F2: second formant — controls front/back of the vowel
  //   back vowels: F2 low (700-1000Hz)
  //   front vowels: F2 high (1800-2500Hz)
  formantF2  = ac.createBiquadFilter();
  formantF2G = ac.createGain();
  formantF2.type = 'bandpass';
  formantF2.frequency.value = 1200;
  formantF2.Q.value = 4;
  formantF2G.gain.value = 0.7;

  // F3: third formant — controls brightness, stays around 2500-3000Hz
  formantF3  = ac.createBiquadFilter();
  formantF3G = ac.createGain();
  formantF3.type = 'bandpass';
  formantF3.frequency.value = 2800;
  formantF3.Q.value = 6;
  formantF3G.gain.value = 0.4;

  // signal chain: source -> three parallel filters -> each gain -> distortion -> master gain
  formantSrc.connect(formantF1);
  formantSrc.connect(formantF2);
  formantSrc.connect(formantF3);
  formantF1.connect(formantF1G); formantF1G.connect(formantDist);
  formantF2.connect(formantF2G); formantF2G.connect(formantDist);
  formantF3.connect(formantF3G); formantF3G.connect(formantDist);

  formantSrc.start();
  formantActive = true;
}

// Update formant parameters each frame based on mouth distance and nose X position
function updateFormant(ac, mouthD, noseX, energy) {
  if (!formantActive) return;
  let t = ac.currentTime;

  if (energy > 15 || mouthD > 8) {
    // source volume rises with energy
    let vol = map(energy, 15, 100, 0.06, 0.35);
    formantGain.gain.setTargetAtTime(vol, t, 0.05);
    // source pitch rises slightly with energy, small wobble simulates unstable vocal cords
      let baseF0   = map(energy, 15, 100, 70, 120);
    let wobbleF0 = Math.sin(Date.now() * 0.005) * 3;
    formantSrc.frequency.setTargetAtTime(baseF0 + wobbleF0, t, 0.08);

    // F1 changes with mouth distance d
    // small d -> F1 low (oh/mm sound), large d -> F1 high (ah sound)
    let f1 = map(constrain(mouthD, 5, 28), 5, 28, 350, 850);
    formantF1.frequency.setTargetAtTime(f1, t, 0.08);

    // F2 changes with nose X position — left gives oo sound, right gives ee sound
    // noseX is already flipped: 0 = left, width = right
    let f2 = map(constrain(noseX, 0, width), 0, width, 800, 2400);
    formantF2.frequency.setTargetAtTime(f2, t, 0.12);

    // F3 adjusts brightness slightly with energy
    let f3 = map(energy, 15, 100, 2500, 3200);
    formantF3.frequency.setTargetAtTime(f3, t, 0.15);

    // F1 gain increases with mouth opening — more resonance when wider open
    formantF1G.gain.setTargetAtTime(map(mouthD, 5, 28, 0.6, 1.4), t, 0.08);

  } else {
    // when mouth closes, volume fades out slowly
    formantGain.gain.setTargetAtTime(0, t, 0.4);
  }
}

// TTS — sends text to the browser speech synthesis API
// Rate and pitch change in real time based on mouth state and head movement
// TTS design notes:
// The distorted vocal effect comes from:
// 1. Very slow rate (0.03-0.1) — phonemes stretch, digital artifacts appear
// 2. Rate is not fixed — mouth distance gives instant response, mouthEnergy adds inertia
// 3. Random breath moments — when energy is very high, 15% chance of a faster word
//    inspired by Swans and Diamanda Galas — sudden quiet is more unsettling than screaming
// 4. Pitch slides in the low range (0.01-0.30) — left collapses, right is tense
// 5. Nose movement speed creates vibrato — about 4Hz, like bending a guitar string
//
// Note: the Web Speech API has a minimum rate of about 0.1 (browser clips lower values)
// Setting 0.03 gets clipped to 0.1, but different engines clip differently —
// on macOS/Chrome this produces extra digital noise which is actually useful here
function performVocal(txt, isDragMode, noseX, mouthD, noseSpd, forceNew=false) {
  if (forceNew) window.speechSynthesis.cancel();
  if (!txt || txt.length===0) return;

  let msg  = new SpeechSynthesisUtterance();
  msg.lang = 'en-US';
  if (targetVoiceEN) msg.voice = targetVoiceEN;
  msg.volume = 1.0;
  msg.text   = txt;

  if (isDragMode || isHiveMode) {
    // rate: blend of d (instant) and mouthEnergy (inertia)
    // d range: 8 (just opening) -> 0.35, 30 (fully open) -> 0.03
    let rateFromD = map(constrain(mouthD, 8, 30), 8, 30, 0.35, 0.03);

    // mouthEnergy layer adds inertia to the rate
    let rateFromEnergy = map(constrain(mouthEnergy, 30, 100), 30, 100, 0.35, 0.03);

    // blend: 60% from d (fast response), 40% from energy (slower inertia)
    let blendedRate = rateFromD * 0.6 + rateFromEnergy * 0.4;

    // random breath: when energy is very high, 15% chance of inserting a faster word
    // sudden normal speech in the middle of screaming creates tension
    if (mouthEnergy > 80 && random() < 0.15) {
      blendedRate = random(0.5, 0.8);
    }

    msg.rate = constrain(blendedRate, 0.03, 0.35);

    // pitch: nose X position slides across the low pitch range
    let basePitch   = map(noseX, 0, width, 0.01, 0.30);
    // vibrato: nose movement speed controls the wobble depth, around 4Hz
    let vibratoDepth  = map(constrain(noseSpd, 0, 12), 0, 12, 0, 0.09);
    let vibratoOffset = sin(frameCount * 0.25) * vibratoDepth;
    msg.pitch = constrain(basePitch + vibratoOffset, 0.01, 0.35);

  } else {
    // calm mode: normal speech rate, full pitch range
    msg.rate  = 0.95;
    // pitch follows nose position when calm
    let dynamicPitch = map(noseX, 0, width, 0.05, 2.0);
    msg.pitch = constrain(dynamicPitch, 0.05, 2.0);
  }

  window.speechSynthesis.speak(msg);
}

// Beat scheduler — uses AudioContext timing for precise scheduling, not setInterval
function startAudioScheduler() {
  let ac = getAudioContext();
  schedulerNextBeatTime = ac.currentTime;
  scheduleLoop();
}

function scheduleLoop() {
  let ac = getAudioContext();

  // Only switch tempo on the downbeat so the change feels deliberate, not gradual
  if (mouthEnergy > 60) targetStepDuration = 0.070;
  else if (mouthEnergy < 30) targetStepDuration = 0.115;

  while (schedulerNextBeatTime < ac.currentTime + 0.1) {
    fireScheduledBeat(ac, schedulerNextBeatTime);
    // Only change step duration at the downbeat
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

    // metalOsc frequency and type changes with energy
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

    // kick: always fires on the downbeat, fires on other beats when mouth is open
    if (ac && kickGain) {
      let isDownbeat = (localStep === 0 || localStep === 8);
      if (isDownbeat) {
        fireKick(ac, time, max(mouthEnergy, 40));
      } else if (mouthEnergy > 30) {
        fireKick(ac, time, mouthEnergy * 0.6);
      }
    }

    // bass: plays on all strong beats. Louder on the downbeat, lighter on weak beats
    if (ac && bassGainNode) {
      let isDownbeat = (localStep === 0 || localStep === 8);
      let bassEnergy = isDownbeat ? max(mouthEnergy, 30) : mouthEnergy * 0.75;
      fireBass(ac, time, bassEnergy, currentlyOpen || mouthEnergy > 30);
    }
  }

  // Add ghost kicks on the off-beats when energy is high
  if (mouthEnergy > 70 && ac && kickGain) {
    if (localStep===3||localStep===7||localStep===11||localStep===15) {
      fireKick(ac, time, mouthEnergy * 0.35);
      // Light bass on the off-beat kick too, so it has low-end support
      if (bassGainNode) fireBass(ac, time, mouthEnergy * 0.40, true);
    }
  }
}

// Main draw loop — updates face data, audio state, and TTS each frame
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

    // Second-order dynamics for mouth energy smoothing
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

    // update tear/distortion layer based on current mouth energy
    if (currentlyOpen || mouthEnergy > 15) {
      activateTear(mouthEnergy);
    } else {
      deactivateTear();
    }

    // update formant parameters every frame
    if (formantActive) {
      if (formantSoloMode) {
        // solo mode: update parameters but keep volume at 0.8 for testing
        updateFormant(getAudioContext(), d, width - prevNose.x, 80);
      } else {
        updateFormant(getAudioContext(), d, width - prevNose.x, mouthEnergy);
      }
    }
    // hi-noise layer: near silent when calm, louder and broader when mouth opens
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

    // kick master volume: 0.8 normally, rises to 1.4 when mouth is open
    if (kickGain) {
      let ac = getAudioContext();
      let targetKickVol = currentlyOpen ? map(mouthEnergy, 30, 100, 0.8, 1.4) : 0.8;
      kickGain.gain.setTargetAtTime(targetKickVol, ac.currentTime, 0.05);
    }

    // SURGE contributes 15x more to the chaos meter than other roles
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

    // force a new word if current one has run too long — slow TTS rate can drag a word for 8s
    if (isScreamingMode && window.speechSynthesis.speaking) {
      if (millis() - lastWordStartTime > MAX_ROAR_WORD_MS) {
        window.speechSynthesis.cancel(); // force-end the current word
        // after cancel, speaking=false so the scheduler below triggers the next word immediately
      }
    }

    // stutter effect — only activates when energy is very high
    if (isScreamingMode && window.speechSynthesis.speaking && mouthEnergy > 70) {
      if (stepCount !== lastStutterStep) {
        lastStutterStep = stepCount;
        if (stepCount % 4 === 3) window.speechSynthesis.pause();
        else                      window.speechSynthesis.resume();
      }
    }

    if (!window.speechSynthesis.speaking && !stateChangedThisFrame) {
      lastWordStartTime = millis(); // record when this word started

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

// Update ambient audio each frame — drone oscillator and the five phone role sounds
function updateAmbientAudio(roles, noseSpeed) {
  let ts = millis();
  let s  = constrain(noseSpeed, 0, 15);

  // filter cutoff rises with head movement speed
  droneFilter.freq(map(s, 0, 15, 150, 4000));

  // drone pitch: fixed when calm, adds a slow wobble when mouth opens
  // wobble is about 0.3Hz — keeps the sound evolving so it never feels static
  let droneBaseFreq = 35 + s * 0.5;
  if (currentlyOpen || mouthEnergy > 20) {
    let wobbleDepth = map(mouthEnergy, 20, 100, 1, 8); // Hz
    let wobble = sin(millis() * 0.002) * wobbleDepth;  // about 0.3Hz — a slow natural wobble
    droneOsc.freq(droneBaseFreq + wobble);
  } else {
    droneOsc.freq(droneBaseFreq);
  }

  // drone volume increases when mouth opens to thicken the sound
  let bassGate   = (stepCount%4===2) ? 0.1 : 1.0;
  if (mouthEnergy>30) bassGate = map(mouthEnergy, 30, 100, 1.0, 2.5);
  let baseVolume = map(constrain(mouthEnergy,0,100), 0, 100, 0.05, 0.4);
  droneOsc.amp(baseVolume*bassGate, 0.05);


  // five phone role audio effects — all frequencies use the E harmonic series (41.2Hz root)
  // keeps everything in tune with the main bass and drone
  const E_HARMONICS = [41.2, 82.4, 123.6, 164.8, 206.0, 247.0, 329.6, 494.4, 659.3, 988.0];

  // ROLE 0: PULSE — fires on the off-beats to answer the kick
  // kick hits beats 1 and 3, PULSE hits 2 and 4
  // sound: noise burst, not a steady tone — like a drum brush or hand slap
  if (roles[0] > 15) {
    let pr       = map(roles[0], 15, 180, 0, 1);
    // off-beat: fires on steps 2, 6, 10, 14 (kick fires on 0, 4, 8, 10, 12)
    let isOffbeat = (stepCount === 2 || stepCount === 6 ||
                     stepCount === 10 || stepCount === 14);
    // sound: alarmOsc as a noise-like texture in the 800-2000Hz range
    // sits above the metalOsc (100-500Hz) so they do not clash
    let noiseFreq = map(pr, 0, 1, 800, 2000);
    alarmOsc.setType('sawtooth'); // sawtooth is broader than square wave
    alarmOsc.freq(noiseFreq * (1 + random(-0.05, 0.05))); // slight random detuning to make it sound more like noise
    alarmFilter.freq(noiseFreq * 2.5);
    alarmFilter.res(8); // low Q = wide bandwidth, sounds more like noise than a pitched tone

    // envelope: burst on the off-beat, near silence otherwise
    // PULSE only has presence on the off-beat, so it does not interfere with the kick
    let targetAmp = isOffbeat
      ? map(pr, 0, 1, 0.15, 0.65)
      : map(pr, 0, 1, 0.01, 0.08); // very quiet background level
    alarmOsc.amp(targetAmp, isOffbeat ? 0.005 : 0.05);
  } else {
    alarmOsc.amp(0, 0.08);
  }

  // ROLE 1: RIFT — harmonic pad layer at E5+B5 (659-988Hz)
  // placed above metalOsc (100-500Hz) so they do not clash
  if (roles[1] > 15) {
    let rr = map(roles[1], 15, 180, 0, 1);
    let detuneAmt = map(rr, 0, 1, 1.5, 4.0);
    ghostSine.freq(659.3 + sin(millis() * 0.0007) * detuneAmt); // E5
    ghostSine.amp(map(rr, 0, 1, 0.18, 0.55), 0.08);
    ghostNoise.amp(map(rr, 0, 1, 0.03, 0.12), 0.08);
    howlOsc.freq(987.8 - sin(millis() * 0.0009) * detuneAmt * 0.7); // B5
    howlOsc.amp(map(rr, 0, 1, 0.12, 0.40), 0.08);
  } else {
    ghostSine.amp(0, 0.10);
    ghostNoise.amp(0, 0.10);
    if (roles[3] <= 20) howlOsc.amp(0, 0.10);
  }

  // ROLE 2: VOID — low frequency resonance (90-110Hz)
  // when VOID is active it replaces the drone rather than stacking on top of it
  if (roles[2] > 15) {
    let vr     = map(roles[2], 15, 180, 0, 1);
    let vFreq  = map(vr, 0, 1, 90, 110);
    let amRate = map(vr, 0, 1, 1.5, 4.0);
    let amMod  = sin(millis() * amRate * 0.001 * TWO_PI) * 0.5 + 0.5;
    amMod      = amMod * map(vr, 0, 1, 0.4, 0.9) + (1 - map(vr, 0, 1, 0.4, 0.9));
    distOsc.freq(vFreq * (1 + random(-0.003, 0.003)));
    distFilter.freq(vFreq * 2.5);
    distOsc.amp(map(vr, 0, 1, 0.35, 0.90) * amMod, 0.02);
    if (!currentlyOpen) droneOsc.amp(map(vr, 0, 1, 0.15, 0.03), 0.08);
  } else {
    distOsc.amp(0, 0.10);
  }

  // ROLE 3: GLITCH — rare trigger events, low probability but each one is intense
  if (roles[3] > 20) {
    let gr         = map(roles[3], 20, 180, 0, 1);
    let glitchProb = map(gr, 0, 1, 0.005, 0.055);
    if (random() < glitchProb) {
      if (tearActive) tearShaper.curve = makeDistortionCurve(random(300, 900));
      if (formantActive && formantF2) {
        let ac = getAudioContext();
        formantF2.frequency.setValueAtTime(random(E_HARMONICS) * random([1,2]), ac.currentTime);
      }
      let gf = random(E_HARMONICS.slice(3));
      metalOsc.freq(gf, 0.0005);
      metalOsc.amp(map(gr, 0, 1, 0.6, 1.4), 0.0005);
      setTimeout(() => { if(audioInitialized) metalOsc.amp(0, 0.02); }, floor(random(15, 60)));
    }
    if (roles[1] <= 15) {
      howlOsc.freq(E_HARMONICS[5] + sin(frameCount * 0.5) * 10);
      howlOsc.amp(map(gr, 0, 1, 0.05, 0.22), 0.04);
    }
  } else {
    if (roles[1] <= 15) howlOsc.amp(0, 0.08);
  }

  // ROLE 4: SURGE — Shepard Tone, corrected speed for a real endless-rising illusion
  // old speed (sp=1.030/frame) rose 5.9x per second — too fast to perceive as continuous
  // new speed (sp=1.0008/frame) rises about half a semitone per second — feels truly endless
  if (roles[4] > 15) {
    let sr = map(roles[4], 15, 180, 0, 1);
    let sp = map(sr, 0, 1, 1.00005, 1.00080);
    for (let i = 0; i < 5; i++) {
      let osc   = shepardOscs[i];
      let baseF = 41.2 * pow(2, i);
      let nf    = osc.getFreq() * sp;
      if (nf > baseF * 2) nf = baseF;
      osc.freq(nf);
      let normPos = log(nf/41.2)/log(2)/5;
      osc.amp(sin(normPos * PI) * sr * 0.45, 0.03);
    }
    if (kickGain)    { let ac=getAudioContext(); kickGain.gain.setTargetAtTime(map(sr,0,1,0.8,3.5), ac.currentTime, 0.05); }
    if (bassGainNode){ let ac=getAudioContext(); bassGainNode.gain.setTargetAtTime(map(sr,0,1,1.0,3.5), ac.currentTime, 0.05); }
    if (tearGain)    { let ac=getAudioContext(); tearGain.gain.setTargetAtTime(map(sr,0,1,0,0.50), ac.currentTime, 0.08); }
  } else {
    shepardOscs.forEach(o => o.amp(0, 0.10));
    if (kickGain)    { let ac=getAudioContext(); kickGain.gain.setTargetAtTime(0.8, ac.currentTime, 0.12); }
    if (bassGainNode){ let ac=getAudioContext(); bassGainNode.gain.setTargetAtTime(1.0, ac.currentTime, 0.12); }
  }



}

// Render visuals — background phone effects first, then the face on top
function renderVisuals(txt, d, isRoaring, roles, faceScale) {
  background(0);
  let activeD = constrain(d, 5, 30);
  let forceRoar = isRoaring || isHiveMode;

  // pre-calculate each role intensity (0-1) — used in both background and face rendering
  let pulseR  = roles[0] > 15 ? map(roles[0], 15, 180, 0, 1) : 0;
  let riftR   = roles[1] > 15 ? map(roles[1], 15, 180, 0, 1) : 0;
  let voidR   = roles[2] > 15 ? map(roles[2], 15, 180, 0, 1) : 0;
  let glitchR = roles[3] > 20 ? map(roles[3], 20, 180, 0, 1) : 0;
  let surgeR  = roles[4] > 15 ? map(roles[4], 15, 180, 0, 1) : 0;

  // Visual burst when a new phone joins — a ring expands from the center
  announceEvents = announceEvents.filter(e => millis() - e.startTime < e.duration);
  for (let ev of announceEvents) {
    let t  = (millis() - ev.startTime) / ev.duration; // 0→1
    let a  = (1 - t) * 255;
    const roleColorsAnnounce = [
      [0,255,220], [0,200,255], [150,0,255], [255,50,0], [255,200,0]
    ];
    let rc = roleColorsAnnounce[ev.role];
    // large ring expanding from the center
    noFill(); stroke(rc[0], rc[1], rc[2], a);
    strokeWeight(map(t, 0, 1, 8, 1));
    let r = t * max(width, height) * 0.9;
    ellipse(width/2, height/2, r*2, r*2);
    // second inner ring
    if (t < 0.5) {
      stroke(rc[0], rc[1], rc[2], a * 0.5);
      ellipse(width/2, height/2, r*1.5, r*1.5);
    }
    noStroke();
  }

  // Use face coordinates if available, otherwise fall back to screen center
  let faceAvail = smoothedKeypoints.length > 0 && voiceStarted;
  let originX = faceAvail ? noseScreenX : width/2;
  let originY = faceAvail ? noseScreenY : height/2;
  let mouthX  = faceAvail ? mouthScreenX : width/2;
  let mouthY  = faceAvail ? mouthScreenY : height * 0.6;
  let lEarX   = faceAvail ? leftEarScreenX  : width * 0.3;
  let lEarY   = faceAvail ? leftEarScreenY  : height * 0.5;
  let rEarX   = faceAvail ? rightEarScreenX : width * 0.7;
  let rEarY   = faceAvail ? rightEarScreenY : height * 0.5;

  // ROLE 0: PULSE — main effect is the face outline wave (see ONE_LINE_PATH section)
  // this part just adds a edge flash on the off-beat to mark the rhythm
  if (pulseR > 0) {
    let isOff = (stepCount===2||stepCount===6||stepCount===10||stepCount===14);
    if (isOff) {
      // SURGE amplifies the PULSE edge flash
      let surgeMult = 1 + surgeR * 1.8;
      let alpha = map(pulseR, 0, 1, 40, 160) * surgeMult;
      let bw    = map(pulseR, 0, 1, 2, 8) * surgeMult;
      alpha = constrain(alpha, 0, 255);
      bw    = constrain(bw, 2, width * 0.15);
      noStroke(); fill(0, 255, 220, alpha);
      rect(0, 0, bw, height);
      rect(width-bw, 0, bw, height);
      rect(0, 0, width, bw);
      rect(0, height-bw, width, bw);
    }
    noStroke();
  }

  // ROLE 1: RIFT — rendered inside the face coordinate system (after mirror transform), see below



  // ROLE 2: VOID — black hole particle swirl in the background layer, does not cover the face
  // particles use Keplerian angular velocity (faster near center) + Perlin noise turbulence
  // center area is kept clear so the face stays visible
  if (voidR > 0) {
    let cx = width / 2;
    let cy = height / 2;
    let roarBoost = currentlyOpen ? map(mouthEnergy, 0, 100, 1.0, 2.0) : 1.0;
    let t = millis() * 0.001;

    let safeR = map(voidR, 0, 1, width * 0.20, width * 0.26);

    // particle system
    let particleCount = floor(map(voidR, 0, 1, 250, 500));
    noStroke();

    for (let i = 0; i < particleCount; i++) {
      let seed     = i * 137.508;
      let armIndex = i % 3;

      let baseR = safeR + (noise(seed * 0.01) * (max(width,height)*0.78 - safeR));

      let k      = map(voidR, 0, 1, 0.08, 0.25) * roarBoost;
      let angVel = constrain(k / pow(max(baseR, 30), 0.5), 0, 0.12);
      let baseAngle = (TWO_PI / 3) * armIndex + seed * 0.1;
      let angle     = baseAngle + t * angVel;

      let noiseFactor = noise(cos(angle)*0.3 + seed*0.05,
                              sin(angle)*0.3 + t*0.08) - 0.5;
      let r = baseR + noiseFactor * map(voidR, 0, 1, 25, 100);
      r = max(r, safeR);

      let px = cx + cos(angle) * r;
      let py = cy + sin(angle) * r;

      let proximity = 1 - constrain((r - safeR) / (max(width,height)*0.45), 0, 1);
      let pSize = map(proximity, 0, 1, 2, 20) * voidR;

      let armColors = currentlyOpen
        ? [[255, 80, 200], [200, 0, 255], [255, 120, 255]]
        : [[140, 0, 240], [90,  0, 220], [180, 0, 255]];
      let [cr, cg, cb] = armColors[armIndex];
      if (currentlyOpen) {
        cr = floor(lerp(cr, 255, mouthEnergy/100));
        cg = floor(lerp(cg, 120, mouthEnergy/100));
      }

      // denser and brighter at the outer edge, sparse and dim in the center
      let outerW = 1 - proximity * 0.78;
      let alpha  = map(outerW, 0, 1, 20, 255) * voidR;
      alpha     *= (0.6 + 0.4 * noise(seed*0.2, t*0.3));
      pSize      = map(outerW, 0, 1, 1.2, 24) * voidR;

      // glow effect: shadowBlur is larger for outer particles
      drawingContext.shadowBlur  = pSize * 6 * voidR * outerW;
      drawingContext.shadowColor = `rgba(${cr},${cg>>1},${cb},0.9)`;
      fill(cr, cg, cb, alpha);
      ellipse(px, py, pSize, pSize);
    }

    // spiral arm highlight lines
    drawingContext.shadowBlur = 0;
    noFill();
    for (let arm = 0; arm < 3; arm++) {
      // rotation speed reduced to match the slower particles
      let armBase = (TWO_PI / 3) * arm + t * map(voidR,0,1,0.02,0.08) * roarBoost;
      let cr2 = currentlyOpen ? floor(lerp(150,255,mouthEnergy/100)) : 100;
      let cb2 = currentlyOpen ? floor(lerp(255,150,mouthEnergy/100)) : 255;
      stroke(cr2, 0, cb2, map(voidR,0,1,80,180));
      strokeWeight(map(voidR,0,1,1.0,2.5));
      beginShape();
      for (let s = 0; s <= 60; s++) {
        let st  = s / 60;
        let ang = armBase + st * PI * map(voidR,0,1,1.2,2.5);
        let r2  = safeR + pow(st, 0.55) * (max(width,height)*0.65 - safeR);
        r2 += sin(st * PI * 4 + t * 0.8 + arm) * map(voidR,0,1,8,35);
        r2  = max(r2, safeR);
        let sa = sin(st * PI) * map(voidR,0,1,80,180);
        stroke(cr2, 0, cb2, sa);
        curveVertex(cx + cos(ang)*r2, cy + sin(ang)*r2);
        if (s===0||s===60) curveVertex(cx+cos(ang)*r2, cy+sin(ang)*r2);
      }
      endShape();
    }

    // inner ring: open arc segments, never a full circle
    // multiple disconnected arcs around the face, no hard circular boundary
    noFill();
    let arcLayerCount = floor(map(voidR, 0, 1, 3, 7));
    for (let arc2 = 0; arc2 < arcLayerCount; arc2++) {
      // each arc has a different base radius, distributed around the safe zone
      let arcR   = safeR + noise(arc2 * 2.3, t * 0.03) * map(voidR,0,1,20,80)
                   - map(voidR,0,1,10,40);
      arcR = max(arcR, safeR * 0.8);

      // arc start angle and length are noise-driven — never covers the full circle
      let arcStart  = noise(arc2 * 1.7, t * 0.02) * TWO_PI;
      let arcLength = map(noise(arc2 * 3.1, t * 0.015), 0, 1,
                         PI * 0.15,   // shortest: about 27 degrees
                         PI * 0.85);  // longest: about 150 degrees — never a full circle

      let cr3 = currentlyOpen ? floor(lerp(180,255,mouthEnergy/100)) : 120;
      let cb3 = currentlyOpen ? floor(lerp(255,150,mouthEnergy/100)) : 255;
      let rA  = map(arc2, 0, arcLayerCount-1, map(voidR,0,1,120,220), 30) * voidR;
      let rSW = map(arc2, 0, arcLayerCount-1, map(voidR,0,1,2,6), 0.8);

      drawingContext.shadowBlur  = rSW * 4 * voidR;
      drawingContext.shadowColor = `rgba(${cr3},0,${cb3},0.5)`;
      stroke(cr3, 0, cb3, rA);
      strokeWeight(rSW);

      beginShape();
      let arcSteps = 30;
      for (let s = 0; s <= arcSteps; s++) {
        let pct = s / arcSteps;
        let ang = arcStart + pct * arcLength + t * 0.04 * (arc2%2===0?1:-1);
        // noise added to the arc radius so it is not a perfect curve
        let rN  = arcR + noise(pct * 2 + arc2 * 1.5, t * 0.05)
                  * map(voidR,0,1,6,25) - map(voidR,0,1,3,12);
        // fade out at both ends of each arc
        let endFade = sin(pct * PI);
        stroke(cr3, 0, cb3, rA * endFade);
        curveVertex(cx + cos(ang)*rN, cy + sin(ang)*rN);
        if (s===0||s===arcSteps) curveVertex(cx+cos(ang)*rN, cy+sin(ang)*rN);
      }
      endShape();
    }

    drawingContext.shadowBlur  = 0;
    drawingContext.shadowColor = 'transparent';
    noStroke();
  }

  // ROLE 3: GLITCH — scan lines and vertical tears in the background
  if (glitchR > 0) {
    let lc=floor(map(glitchR,0,1,1,22));
    noStroke();
    for (let i=0;i<lc;i++) {
      if (random()<0.5) {
        let y=random(height), h2=random(1,map(glitchR,0,1,4,32));
        fill(random()<0.5 ? color(255,50,0,random(50,190))
                          : color(0,255,200,random(40,150)));
        rect(0,y,width,h2);
      }
    }
    if (glitchR>0.4) {
      let tc=floor(map(glitchR,0.4,1,1,7));
      for (let i=0;i<tc;i++) {
        stroke(255,map(glitchR,0.4,1,80,0),0, random(80,210));
        strokeWeight(random(1.5,3.5));
        let tx=random(width);
        line(tx,0, tx+random(-22,22),height);
      }
      noStroke();
    }
  }

  if (surgeR > 0) {
    let st = millis() * 0.001;
    let cx2 = width / 2;
    let cy2 = height / 2;

    // layer 1: orange-gold color wash
    noStroke();
    fill(255, map(surgeR,0,1,140,200), 0, map(surgeR,0,1,15,80));
    rect(0, 0, width, height);

    // layer 2: rays converging inward from the screen edges, varying thickness
    let rayCount = floor(map(surgeR, 0, 1, 20, 60));
    let shrinkSpeed = map(surgeR, 0, 1, 0.08, 0.35);

    for (let i = 0; i < rayCount; i++) {
      let baseAng  = (TWO_PI / rayCount) * i;
      let angJitter = noise(i * 0.7, st * 0.1) * 0.3;
      let ang      = baseAng + angJitter;
      let phase    = (st * shrinkSpeed + i * 0.618) % 1;

      let outerLen = max(width, height) * 0.85;
      let innerLen = max(width, height) * 0.15;
      let startR   = outerLen * (1 - phase * 0.8);
      let endR     = innerLen + outerLen * (1 - phase) * 0.2;
      let rayAlpha = map(phase, 0, 1, map(surgeR,0,1,40,180), 0);

      // line thickness varies with noise — ranges from hair-thin to 5px
      let thickNoise = noise(i * 1.3, st * 0.05);
      let rayWidth   = map(thickNoise, 0, 1, 0.3, map(surgeR,0,1,2,5));

      stroke(255, map(surgeR,0,1,160,220), 0, rayAlpha);
      strokeWeight(rayWidth);
      line(cx2 + cos(ang)*startR, cy2 + sin(ang)*startR,
           cx2 + cos(ang)*endR,   cy2 + sin(ang)*endR);
    }
    noStroke();

    // layer 3: corner glows using radial gradients, no hard edges
    let cornerAlpha = map(surgeR, 0, 1, 0, 0.55);
    let cornerSize  = map(surgeR, 0, 1, width*0.18, width*0.55);
    const corners   = [[0,0],[width,0],[0,height],[width,height]];
    for (let [cx3,cy3] of corners) {
      let grad = drawingContext.createRadialGradient(cx3,cy3,0, cx3,cy3,cornerSize);
      grad.addColorStop(0,   `rgba(255,190,0,${cornerAlpha})`);
      grad.addColorStop(0.4, `rgba(255,140,0,${cornerAlpha*0.5})`);
      grad.addColorStop(1,   `rgba(255,100,0,0)`);
      drawingContext.fillStyle = grad;
      drawingContext.fillRect(0, 0, width, height);
    }

    // layer 4: center glow that pulses with the kick
    let isDownbeat   = (stepCount === 0 || stepCount === 8);
    let pulseIntensity = isDownbeat
      ? map(surgeR, 0, 1, 0, 0.7)
      : map(surgeR, 0, 1, 0, 0.28);
    let glowSize = isDownbeat
      ? map(surgeR, 0, 1, width*0.12, width*0.55)
      : map(surgeR, 0, 1, width*0.08, width*0.35);

    if (pulseIntensity > 0) {
      let cGrad = drawingContext.createRadialGradient(cx2,cy2,0, cx2,cy2,glowSize);
      cGrad.addColorStop(0,   `rgba(255,240,100,${pulseIntensity})`);
      cGrad.addColorStop(0.25,`rgba(255,200,0,${pulseIntensity*0.6})`);
      cGrad.addColorStop(0.6, `rgba(255,140,0,${pulseIntensity*0.2})`);
      cGrad.addColorStop(1,   `rgba(255,100,0,0)`);
      drawingContext.fillStyle = cGrad;
      drawingContext.fillRect(0, 0, width, height);
    }

    // reset fillStyle so it does not affect subsequent p5 drawing
    drawingContext.fillStyle = 'rgba(0,0,0,0)';
    noStroke();
  }


  push();
  // screen shake: driven by mouthEnergy, amplified by SURGE
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
      let bx = lerp(kp[idx].x,nose.x,0.22)+width/2-nose.x;
      let by = lerp(kp[idx].y,nose.y,0.22)+height/2-nose.y+50;

      // GLITCH: adds a sin distortion to all keypoints at the same time
      // the whole face warps in sync — looks like real deformation, not random noise
      if (glitchR > 0.1) {
        let gt    = millis() * 0.008;
        let gampX = glitchR * 30;
        let gampY = glitchR * 18;
        bx += sin(gt + by * 0.015) * gampX;
        by += cos(gt * 1.3 + bx * 0.012) * gampY;
      }
      // VOID: low-frequency wave makes the face float slightly
      if (voidR > 0.1) {
        let wPhase = millis() * 0.001 * map(voidR,0,1,0.5,2.0);
        bx += sin(wPhase + by * 0.01) * voidR * 12;
        by += cos(wPhase + bx * 0.008) * voidR * 6;
      }
      return {x: bx, y: by};
    }

    // Save nose screen position (mirror corrected) for the word particle system
    let nosePt = getSmallPt(1);
    noseScreenX = width - nosePt.x;
    noseScreenY = nosePt.y;

    // Save mouth and ear positions (mirror corrected) for phone visual effects
    // Mouth center — used as origin for SURGE spiral
    let mouthPt = getSmallPt(13);
    mouthScreenX = width - mouthPt.x;
    mouthScreenY = mouthPt.y;
    // Ear positions — used for PULSE visual effects
    let lEarPt = getSmallPt(234);
    leftEarScreenX  = width - lEarPt.x;
    leftEarScreenY  = lEarPt.y;
    let rEarPt = getSmallPt(454);
    rightEarScreenX = width - rEarPt.x;
    rightEarScreenY = rEarPt.y;

    // Side-face detection: uses ear span ratio, face fades out when turning sideways
    let leftEarX  = kp[234] ? kp[234].x : 0;
    let rightEarX = kp[454] ? kp[454].x : 0;
    let earSpan   = abs(rightEarX - leftEarX);
    let faceH     = dist(kp[10].x,kp[10].y, kp[152].x,kp[152].y);
    let earRatio  = faceH > 0 ? earSpan / faceH : 1.0;
    let targetAngleRatio = map(constrain(earRatio, 0.15, 0.45), 0.45, 0.15, 0, 1);
    faceAngleRatio = lerp(faceAngleRatio, targetAngleRatio, 0.1);
    faceAlpha = map(faceAngleRatio, 0, 1, 255, 0);
    drawingContext.globalAlpha = faceAlpha / 255;

    // VOID affects the face glow amount
    let voidGlow = forceRoar ? 25 : 15;
    voidGlow += voidR * 30; // VOID adds up to 30px extra glow
    let voidShadowColor = voidR > 0.3
      ? `rgba(${floor(lerp(0,120,voidR))},0,${floor(lerp(200,255,voidR))},${map(voidR,0,1,0.3,0.9)})`
      : (forceRoar ? 'rgba(255,50,0,0.8)' : 'rgba(0,255,255,0.6)');

    let gradient = drawingContext.createLinearGradient(0,height/2-150,0,height/2+150);
    if (forceRoar) {
      // roaring: red to yellow gradient
      gradient.addColorStop(0,   'rgb(255,0,0)');
      gradient.addColorStop(0.35,'rgb(255,50,0)');
      gradient.addColorStop(1,   'rgb(255,255,0)');
    } else if (riftR > 0.1) {
      // RIFT active: face color shifts from cyan toward orange
      let r1 = floor(lerp(150, 255, riftR));
      let g1 = floor(lerp(0,   100, riftR));
      let b1 = floor(lerp(255, 0,   riftR));
      let r2 = floor(lerp(0,   255, riftR));
      let g2 = floor(lerp(255, 150, riftR));
      let b2 = floor(lerp(255, 0,   riftR));
      gradient.addColorStop(0,   `rgb(${r1},${g1},${b1})`);
      gradient.addColorStop(0.35,`rgb(${r2},${g2},${b2})`);
      gradient.addColorStop(1,   `rgb(${r2},${g2},${b2})`);
    } else {
      // default calm: purple to cyan
      gradient.addColorStop(0,   'rgb(150,0,255)');
      gradient.addColorStop(0.35,'rgb(0,255,255)');
      gradient.addColorStop(1,   'rgb(0,255,255)');
    }

    drawingContext.shadowBlur  = voidGlow;
    drawingContext.shadowColor = voidShadowColor;
    stroke(255); drawingContext.strokeStyle = gradient; noFill();

    // Face line thickness changes based on active phone roles
    // Base: 2.5 normal, 3.5 when roaring. SURGE adds up to +2.0, PULSE pulses on the beat
    let baseSW   = (forceRoar ? 3.5 : 2.5) * faceScale;
    let surgeSW  = surgeR * 2.0;
    let pulseSW  = (stepCount === 2 || stepCount === 6) ? pulseR * 1.5 : 0;
    let voidSW   = voidR * 0.8;
    let finalSW  = baseSW + surgeSW + pulseSW + voidSW;

    if (forceRoar) {
      let hairIdx = [127,162,21,54,103,67,109,10,338,297,332,284,251,389,356];
      strokeWeight(finalSW + 0.5);
      beginShape();
      for (let i=0; i<hairIdx.length-1; i++) {
        let pt = getSmallPt(hairIdx[i]);
        vertex(pt.x,pt.y);
        if (i%2===0) {
          let vx   = pt.x-width/2;
          let dirX = vx*0.03, dirY=-1.2;
          let mag  = max(0.1,dist(0,0,dirX,dirY));
          dirX = (dirX/mag)+random(-0.1,0.1); dirY=dirY/mag;
          // SURGE increases hair length
          let ex      = map(mouthEnergy,0,100,0.3,4.5) * (1 + surgeR * 0.6);
          let baseLen = map(abs(vx),0,100,220,100)*faceScale;
          vertex(pt.x+dirX*baseLen*ex*random(0.8,1.2),
                 pt.y+dirY*baseLen*ex*random(0.8,1.2));
        }
      }
      vertex(getSmallPt(356).x,getSmallPt(356).y);
      endShape();
    }

    strokeWeight(finalSW);
    beginShape();
    for (let i=0; i<ONE_LINE_PATH.length; i++) {
      let pt = getSmallPt(ONE_LINE_PATH[i]);

      // PULSE wave: travels along the face outline as a sine wave
      // path position normalized 0-1, wave spreads from the top of the head
      if (pulseR > 0) {
        let pathPos = i / (ONE_LINE_PATH.length - 1); // 0 to 1
        // wave speed increases with shake intensity
        let waveSpeed = map(pulseR, 0, 1, 1.5, 6.0);
        // amplitude: outward offset along the normal direction
        let waveAmp   = map(pulseR, 0, 1, 3, 22) * faceScale;
        // two travelling waves in opposite directions — their interference creates complexity
        let wave1 = sin(pathPos * TWO_PI * 3 - millis() * 0.001 * waveSpeed) * waveAmp;
        let wave2 = sin(pathPos * TWO_PI * 2 + millis() * 0.0008 * waveSpeed) * waveAmp * 0.4;
        // offset direction: outward from the center (approximated normal)
        let dx = pt.x - width/2;
        let dy = pt.y - height/2;
        let dl = max(0.1, sqrt(dx*dx + dy*dy));
        let nx2 = dx/dl, ny2 = dy/dl;
        pt.x += nx2 * (wave1 + wave2);
        pt.y += ny2 * (wave1 + wave2);
      }

      curveVertex(pt.x, pt.y);
      if (i===0||i===ONE_LINE_PATH.length-1) curveVertex(pt.x,pt.y);
    }
    endShape();

      // rendered in face coordinate space using getSmallPt — perfectly follows the face
      if (riftR > 0) {
      let rc2 = floor(lerp(0, 255, riftR));
      let gc2 = floor(lerp(255, 140, riftR));
      let bc2 = floor(lerp(200, 0, riftR));
      let layerCount2 = floor(map(riftR, 0, 1, 1, 3));
      let deformSpd   = map(riftR, 0, 1, 0.8, 3.0);

      for (let layer = 0; layer < layerCount2; layer++) {
        // offset increases with each layer — inner layer close, outer layer far
        let baseOff = map(layer, 0, max(1, layerCount2-1),
                          map(riftR, 0, 1, 20, 55),
                          map(riftR, 0, 1, 60, 160)) * faceScale;
        // SURGE amplifies RIFT lines — thicker and brighter
        let surgeMult2 = 1 + surgeR * 1.5;
        let layAlpha = map(layer, 0, max(1, layerCount2-1), 210, 70) * riftR * surgeMult2;
        let layerSW  = map(riftR, 0, 1, 1.5, 4.0) * (1 - layer * 0.3) * surgeMult2;

        stroke(rc2, gc2, bc2, layAlpha);
        strokeWeight(layerSW);
        noFill();

        beginShape();
        for (let i = 0; i < ONE_LINE_PATH.length; i++) {
          // use getSmallPt so GLITCH and VOID distortions apply to the RIFT lines too
          // this keeps the RIFT perfectly in sync with the face when roaring
          let pt2 = getSmallPt(ONE_LINE_PATH[i]);
          let bx  = pt2.x;
          let by  = pt2.y;

          // normal vector: from the point outward away from screen center
          let dx2  = bx - width/2;
          let dy2  = by - (height/2 + 50);
          let dl2  = max(0.1, sqrt(dx2*dx2 + dy2*dy2));
          let nx2  = dx2/dl2, ny2 = dy2/dl2;

          // irregular deformation: two sin waves at different frequencies going opposite ways
          let pp = i / (ONE_LINE_PATH.length - 1);
          let d1 = sin(pp * PI * 6 + millis() * 0.002 * deformSpd + layer * 1.3)
                   * map(riftR, 0, 1, 6, 35) * faceScale;
          let d2 = cos(pp * PI * 4 - millis() * 0.0015 * deformSpd + layer * 0.9)
                   * map(riftR, 0, 1, 3, 18) * faceScale;
          let off = baseOff + d1 + d2;

          let ox = bx + nx2 * off;
          let oy = by + ny2 * off;
          curveVertex(ox, oy);
          if (i===0 || i===ONE_LINE_PATH.length-1) curveVertex(ox, oy);
        }
        endShape();
      }

      // Restore stroke settings for face drawing
      stroke(255);
      drawingContext.strokeStyle = gradient;
      strokeWeight(finalSW);
      noFill();
    }

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
      let blurAmt=50*faceScale, pi=12*faceScale;
      let le=getSmallPt(33);
      let re=getSmallPt(263);

      // eye socket glow: radial gradient, dark red to transparent, no hard edge
      let eGlowR = 38 * faceScale; // glow radius
      [[le.x+pi, le.y], [re.x-pi, re.y]].forEach(([ex, ey]) => {
        let eGrad = drawingContext.createRadialGradient(ex, ey, 0, ex, ey, eGlowR);
        eGrad.addColorStop(0,   'rgba(120,0,40,0.75)');
        eGrad.addColorStop(0.4, 'rgba(80,0,20,0.35)');
        eGrad.addColorStop(1,   'rgba(60,0,10,0)');
        drawingContext.fillStyle = eGrad;
        drawingContext.fillRect(ex - eGlowR, ey - eGlowR, eGlowR*2, eGlowR*2);
      });

      // red pupil: radial gradient glow, no hard edge
      let eyeGlowR = 22 * faceScale;
      let lp=kp[468]?getSmallPt(468):null;
      let rp=kp[473]?getSmallPt(473):null;
      let lC = lp&&lp.x!==undefined ? lp
               : {x:(getSmallPt(159).x+getSmallPt(145).x)/2,
                  y:(getSmallPt(159).y+getSmallPt(145).y)/2};
      let rC = rp&&rp.x!==undefined ? rp
               : {x:(getSmallPt(386).x+getSmallPt(374).x)/2,
                  y:(getSmallPt(386).y+getSmallPt(374).y)/2};

      [[lC.x,lC.y],[rC.x,rC.y]].forEach(([px2,py2]) => {
        // outer red glow with radial gradient — no edge
        let pGrad = drawingContext.createRadialGradient(px2, py2, 0, px2, py2, eyeGlowR);
        pGrad.addColorStop(0,   'rgba(255,0,0,0.9)');
        pGrad.addColorStop(0.25,'rgba(220,0,0,0.6)');
        pGrad.addColorStop(0.6, 'rgba(180,0,0,0.2)');
        pGrad.addColorStop(1,   'rgba(150,0,0,0)');
        drawingContext.fillStyle = pGrad;
        drawingContext.fillRect(px2-eyeGlowR, py2-eyeGlowR, eyeGlowR*2, eyeGlowR*2);
      });

      // reset fillStyle
      drawingContext.fillStyle = 'rgba(0,0,0,0)';

      noFill(); stroke(220); strokeWeight(2.8*faceScale);
      drawingContext.shadowBlur=10*faceScale;
      drawingContext.shadowColor='rgba(255,255,255,0.5)';
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

  // Canvas 2D context properties are not managed by p5 push/pop, must reset manually
  drawingContext.shadowBlur  = 0;
  drawingContext.shadowColor = 'transparent';
  drawingContext.globalAlpha = 1.0; // reset opacity so it does not affect HUD and subtitle rendering

  // HUD top-left: role names
  let hudColor = forceRoar ? color(255,100,0) : color(0,255,255);
  noStroke(); textAlign(LEFT,TOP); textSize(11); textFont('monospace');
  for (let i=0; i<5; i++) {
    fill(roles[i]>15 ? color(255,50,0) : hudColor);
    text(roleNames[i], 20, 20+i*14);
  }

  // F key debug label
  if (formantSoloMode) {
    fill(255, 255, 0); textSize(10);
    text('FORMANT SOLO  —  F TO EXIT', 20, 95);
  }

  // signal status top-right
  fill(forceRoar ? color(255,80,0,100) : color(0,200,200,70));
  textSize(9); textAlign(RIGHT,TOP);
  text(dataSourceLabel, width-15, 15);

  // Subtitle rendering — static at the bottom when calm, words shake and fall when roaring
  // calm: text centered at the bottom
  // roaring: words shake and fall with physics
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
      // when roaring: generate word particles only when a new word appears
      // words appear at the subtitle position, shake and fall, screen is blank until the next word
      if (lastParticleWord !== txt) {
        lastParticleWord = txt;

        // speed up old particles so they clear before the new word appears
        for (let p of wordParticles) p.decay = max(p.decay, 0.08);

        let words = txt.split(' ').filter(w => w.length > 0);
        textSize(SZ_ROAR); textStyle(BOLD);

        // calculate starting X to center the words
        let totalW = 0;
        for (let w of words) totalW += textWidth(w) + SZ_ROAR * 0.4;
        let curX = width/2 - totalW/2;

        for (let i = 0; i < words.length; i++) {
          let w  = words[i];
          let ww = textWidth(w);
          let wx = curX + ww/2;
          let wy = SUB_Y + SZ_ROAR/2;

          // each word has a slight delay before falling, so they stagger rather than all at once
          // life starts slightly above 1 — the extra amount is the hold time before falling
          let holdFrames = i * 3; // each word delays 3 frames more than the previous

          // fall speed scales with energy — high energy throws the words harder
          let vy = random(0.8, 2.0) * map(mouthEnergy, 30, 100, 0.6, 2.2);
          let vx = random(-1.2, 1.2);

          // rotation: words tilt naturally as they fall
          let ang  = random(-8, 8);   // small initial angle
          let spin = random(-3.5, 3.5); // rotation speed while falling

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
            held: holdFrames, // frames remaining in the hold phase
          });
          curX += ww + SZ_ROAR * 0.4;
        }
      }

      // Update and render word particles
      wordParticles = wordParticles.filter(p => p.life > 0);
      for (let p of wordParticles) {
        if (p.held > 0) {
          // Hold phase — word shakes slightly in place before falling
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
          // Fall phase — word moves with physics and fades out
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
      // When calm, speed up the decay of any remaining particles
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

      // Static subtitle at the bottom, white, centered
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

  // main title
  drawingContext.shadowBlur  = map(pulse, 0, 1, 12, 50);
  drawingContext.shadowColor = `rgba(0,255,100,${map(pulse,0,1,0.3,1.0)})`;
  fill(0, glow, map(pulse, 0, 1, 50, 110));
  textSize(72); textStyle(BOLD);
  text("SWARM", width/2, height/2 - 40);

  // subtitle, blinking
  let blink = (sin(frameCount * 0.10) > 0.3) ? 200 : 35;
  drawingContext.shadowBlur  = 5;
  drawingContext.shadowColor = `rgba(0,255,100,0.4)`;
  fill(0, 180, 70, blink);
  textSize(16); textStyle(NORMAL);
  text("OPEN YOUR MOUTH TO BEGIN", width/2, height/2 + 32);

  drawingContext.shadowBlur = 0;
  pop();
}

// Interaction events — click to initialize audio, keyboard shortcuts
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

    // kick master gain node
    kickGain = ac.createGain();
    kickGain.gain.value = 0.8;
    kickGain.connect(ac.destination);

    // bass line master gain node
    bassGainNode = ac.createGain();
    bassGainNode.gain.value = 1.0;
    bassGainNode.connect(ac.destination);

    // high-frequency noise layer
    initHiNoise(ac);

    // initialize the formant vocal synthesizer
    initFormantSynth(ac);

    // initialize the tear/distortion system
    initTearSystem(ac);
  }

  // start voice on first click
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
  // all phones keep their roles, the computer enters an extreme state
}

// debug mode flags
let formantSoloMode = false; // F key: solo the formant layer, mutes everything else
let ttsMuted        = false; // T key: mute TTS

function keyPressed() {
  if (key==='r'||key==='R') {
    isHiveMode=false; chaosMeter=0; roleCounter=0; bandMembers={}; mouthEnergy=0;
  }

  // S key: silence mode
  // press to drop all audio to near zero over 3 seconds
  // press again to bring everything back in 0.5s — maximum dynamic contrast
  if (key==='s'||key==='S') {
    silenceMode = !silenceMode;
    if (!audioInitialized) return;
    let ac = getAudioContext();
    let t  = ac.currentTime;
    if (silenceMode) {
      // entering silence: slow 3-second fade
      if (kickGain)    kickGain.gain.linearRampToValueAtTime(0.05, t + 3.0);
      if (bassGainNode) bassGainNode.gain.linearRampToValueAtTime(0.05, t + 3.0);
      if (tearGain)    tearGain.gain.linearRampToValueAtTime(0, t + 3.0);
      droneOsc.amp(0.02, 3.0);
      metalOsc.amp(0, 2.0);
      alarmOsc.amp(0, 2.0);
      ghostSine.amp(0, 2.0);
      ghostNoise.amp(0, 2.0);
      howlOsc.amp(0, 2.0);
      distOsc.amp(0, 2.0);
      window.speechSynthesis.cancel();
      // exit silence: 0.5s burst, one heavy kick marks the return
      if (kickGain)    kickGain.gain.setTargetAtTime(0.8, t, 0.1);
      if (bassGainNode) bassGainNode.gain.setTargetAtTime(1.0, t, 0.1);
      droneOsc.amp(0.15, 0.2);
          if (kickGain) fireKick(ac, t, 90);
    }
  }

  // F key: formant solo mode — mutes everything except formant for testing
  if (key==='f'||key==='F') {
    formantSoloMode = !formantSoloMode;
    if (!audioInitialized) return;
    let ac = getAudioContext();
    let t  = ac.currentTime;
    if (formantSoloMode) {
      if (tearGain)    tearGain.gain.setTargetAtTime(0, t, 0.05);
      if (kickGain)    kickGain.gain.setTargetAtTime(0, t, 0.05);
      if (bassGainNode) bassGainNode.gain.setTargetAtTime(0, t, 0.05);
      if (hiNoiseGain) hiNoiseGain.gain.setTargetAtTime(0, t, 0.05);
      droneOsc.amp(0, 0.1);
      metalOsc.amp(0, 0.1);
      if (formantGain) formantGain.gain.setTargetAtTime(0.8, t, 0.05);
      window.speechSynthesis.cancel();
    } else {
      if (kickGain)     kickGain.gain.setTargetAtTime(0.8, t, 0.1);
      if (bassGainNode) bassGainNode.gain.setTargetAtTime(1.0, t, 0.1);
      if (hiNoiseGain)  hiNoiseGain.gain.setTargetAtTime(0.015, t, 0.1);
    }
  }

  if (key==='g'||key==='G') lastFetchTime = -999999;
}
