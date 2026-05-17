// 引入必要的网络模块
const express = require('express');
const http = require('http');
const { Server } = require('socket.io');

// 创建基础服务器
const path = require('path');
const app = express();
app.use(express.static(path.join(__dirname, 'public')));
const server = http.createServer(app);

// 初始化 Socket.io，并配置跨域 (CORS)
// 允许所有来源 (*) 连接，这样你的 p5 Web Editor 才能连得上
const io = new Server(server, {
  cors: {
    origin: "*",
    methods: ["GET", "POST"]
  }
});

// 当有设备（手机或电脑）连上服务器时
io.on('connection', (socket) => {
  console.log('有新设备接入，ID:', socket.id);

  // 监听名为 'shake' 的事件（这将由你的手机端发送）
  socket.on('shake', (data) => {
    // 收到数据后，使用 broadcast.emit 瞬间广播给除了发送者以外的所有人（即你的电脑端）
    socket.broadcast.emit('shake', data);
  });

  // 设备断开连接时
  socket.on('disconnect', () => {
    console.log('设备断开连接，ID:', socket.id);
  });
});

// Render 会自动分配端口给 process.env.PORT，本地测试时默认 3000
const PORT = process.env.PORT || 3000;
server.listen(PORT, () => {
  console.log(`蜂群控制服务器已启动，正在监听端口 ${PORT}`);
});
