// ======================================================
// CYBER SWARM: MOBILE CLIENT (纯摇晃版)
// 所有角色统一用摇晃强度控制
// val = 摇晃强度（0-180），越用力摇越大
// ======================================================
p5.disableFriendlyErrors = true;

let socket, myDeviceId;
let myRole = -1;
let isConnected = false;
let smoothedShake = 0;

const roleNames = ["01_PULSE", "02_RIFT", "03_VOID", "04_GLITCH", "05_SURGE"];
const roleColors = [
  [0, 255, 180],    // PULSE：青绿
  [255, 100, 0],    // RIFT：橙
  [80, 0, 255],     // VOID：深紫
  [255, 0, 80],     // GLITCH：红粉
  [255, 220, 0],    // SURGE：金黄
];
const roleInstructions = [
  "SHAKE TO THE BEAT",
  "SHAKE FOR MELODY",
  "SHAKE FOR BASS",
  "SHAKE TO GLITCH",
  "SHAKE FOR SURGE",
];

function setup() {
  let cnv = createCanvas(windowWidth, windowHeight);
  // 把canvas放到最底层，不遮挡HTML按钮
  cnv.style('z-index', '0');
  cnv.style('position', 'fixed');
  myDeviceId = Math.floor(Math.random() * 1000000);
  textFont('monospace');

  // 用原生HTML按钮，不用p5.js的createButton
  // 原因：iOS要求陀螺仪权限必须在原生用户手势事件里同步触发
  // p5.js的mousePressed有时被浏览器认为不是直接手势，会被拦截
  let btn = document.createElement('button');
  btn.innerText = 'JOIN THE BAND';
  btn.style.cssText = `
    position: fixed;
    top: 50%;
    left: 50%;
    transform: translate(-50%, -50%);
    padding: 28px 40px;
    font-size: 22px;
    font-family: monospace;
    font-weight: bold;
    background: #00ff88;
    color: #000;
    border: none;
    border-radius: 6px;
    cursor: pointer;
    z-index: 9999;
    -webkit-tap-highlight-color: transparent;
    touch-action: manipulation;
  `;

  btn.addEventListener('click', () => {
    userStartAudio();
    // iOS 13+陀螺仪权限：必须在原生click事件里同步调用
    if (typeof DeviceMotionEvent !== 'undefined' &&
        typeof DeviceMotionEvent.requestPermission === 'function') {
      DeviceMotionEvent.requestPermission()
        .then(state => {
          if (state === 'granted') isConnected = true;
        })
        .catch(e => {
          console.error(e);
          isConnected = true; // 权限失败也让它继续，只是没有传感器数据
        });
    } else {
      // Android或不需要权限的设备
      isConnected = true;
    }
    btn.remove();
  });

  document.body.appendChild(btn);

  // 连接后端
  socket = io("https://cyber-swarm-backend.onrender.com");

  // 接收主机分配的角色
  socket.on('shake', (data) => {
    if (data.isHost && data.targetId === myDeviceId) {
      myRole = data.role;
    }
  });
}

function draw() {
  if (!isConnected) {
    background(0);
    fill(255, 150);
    textSize(14); textAlign(CENTER, CENTER);
    text("TAP TO JOIN", width/2, height/2 + 80);
    return;
  }

  // 计算摇晃强度
  let rawShake = abs(accelerationX) + abs(accelerationY) + abs(accelerationZ);
  smoothedShake = lerp(smoothedShake, rawShake, 0.25);
  let val = constrain(smoothedShake, 0, 180);

  // 发送给电脑端
  if (socket && socket.connected) {
    socket.emit('shake', { id: myDeviceId, val: val });
  }

  // 视觉：根据角色颜色和摇晃强度
  let bgIntensity = map(val, 0, 180, 0, 80);

  if (myRole >= 0 && myRole < 5) {
    let c = roleColors[myRole];
    background(
      c[0] * bgIntensity / 80,
      c[1] * bgIntensity / 80,
      c[2] * bgIntensity / 80
    );

    // 摇晃强度条
    let barH = map(val, 0, 180, 0, height * 0.5);
    noStroke();
    fill(c[0], c[1], c[2], 180);
    rect(0, height - barH, width, barH);

    // 角色名和指示
    fill(c[0], c[1], c[2]);
    textAlign(CENTER, CENTER);
    textSize(11); textStyle(NORMAL);
    text("YOUR ROLE", width/2, height/2 - 70);
    textSize(28); textStyle(BOLD);
    text(roleNames[myRole], width/2, height/2 - 30);
    textSize(15); textStyle(NORMAL);
    fill(c[0], c[1], c[2], 200);
    text(roleInstructions[myRole], width/2, height/2 + 20);

    // 强度数值
    textSize(13);
    fill(c[0], c[1], c[2], 150);
    text(nfc(val, 0), width/2, height/2 + 60);

  } else {
    // 待机：等待主机分配
    background(0);
    fill(0, 200, 100);
    textAlign(CENTER, CENTER);
    textSize(16); textStyle(NORMAL);
    text("CONNECTED", width/2, height/2 - 30);
    textSize(13);
    fill(100, 200, 150);
    text("WAITING FOR HOST...", width/2, height/2 + 20);
  }
}

// 禁止手机浏览器的下拉刷新
function touchMoved() { return false; }
