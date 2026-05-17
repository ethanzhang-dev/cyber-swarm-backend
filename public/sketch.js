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
  createCanvas(windowWidth, windowHeight);
  myDeviceId = Math.floor(Math.random() * 1000000);
  textFont('monospace');

  // JOIN按钮
  let btn = createButton('JOIN THE BAND');
  btn.style('padding', '28px 40px');
  btn.style('font-size', '20px');
  btn.style('font-family', 'monospace');
  btn.style('background', '#00ff88');
  btn.style('color', '#000');
  btn.style('border', 'none');
  btn.style('border-radius', '4px');
  btn.style('font-weight', 'bold');
  btn.position(width/2 - 120, height/2 - 35);

  btn.mousePressed(() => {
    userStartAudio();
    // iOS陀螺仪权限请求
    if (typeof DeviceMotionEvent !== 'undefined' &&
        typeof DeviceMotionEvent.requestPermission === 'function') {
      DeviceMotionEvent.requestPermission()
        .then(state => { if (state === 'granted') isConnected = true; })
        .catch(console.error);
    } else {
      isConnected = true;
    }
    btn.hide();
  });

  // 连接后端
socket = io("/"); // 直接连当前服务器，不用写死URL

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
