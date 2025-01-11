export class WebSocketClient {
  constructor(url, protocols = [], options = {}) {
    this.url = url;
    this.protocols = protocols;
    this.reconnectAttempts = 0;
    this.maxReconnectAttempts = options.maxReconnectAttempts || 5;
    this.reconnectInterval = options.reconnectInterval || 3000; // 3 seconds
    this.heartbeatInterval = options.heartbeatInterval || 30000; // 30 seconds
    this.heartbeatTimeout = options.heartbeatTimeout || 5000; // 5 seconds
    this.onOpen = options.onOpen;
    this.onMessage = options.onMessage;
    this.onError = options.onError;
    this.onClose = options.onClose;

    this.socket = null;
    this.heartbeatTimer = null;
    this.heartbeatTimeoutTimer = null;

    this.connect();
  }

  connect() {
    try {
      this.socket = new WebSocket(this.url, this.protocols);

      this.socket.onopen = (event) => {
        console.log('WebSocket connection opened:', event);
        this.reconnectAttempts = 0;
        if (typeof this.onOpen === 'function') this.onOpen(event);
        this.startHeartbeat();
      };

      this.socket.onmessage = (event) => {
        if (typeof this.onMessage === 'function') this.onMessage(event.data);
        if (this.isHeartbeatResponse(event.data)) {
          this.resetHeartbeatTimeout();
        }
      };

      this.socket.onerror = (error) => {
        console.error('WebSocket error:', error);
        if (typeof this.onError === 'function') this.onError(error);
      };

      this.socket.onclose = (event) => {
        console.log('WebSocket connection closed:', event);
        if (typeof this.onClose === 'function') this.onClose(event);
        this.stopHeartbeat();

        // Attempt to reconnect if not closed intentionally
        if (event.wasClean === false && this.reconnectAttempts < this.maxReconnectAttempts) {
          setTimeout(() => {
            this.reconnectAttempts++;
            this.connect();
          }, this.reconnectInterval);
        }
      };
    } catch (err) {
      console.error('Failed to create WebSocket:', err);
      if (typeof this.onError === 'function') this.onError(err);
    }
  }

  send(data) {
    if (this.socket && this.socket.readyState === WebSocket.OPEN) {
      this.socket.send(data);
    } else {
      console.warn('WebSocket is not open. Ready state:', this.socket ? this.socket.readyState : 'null');
    }
  }

  close(code = 1000, reason = '') {
    if (this.socket) {
      this.stopHeartbeat();
      this.socket.close(code, reason);
    }
  }

  startHeartbeat() {
    this.stopHeartbeat(); // Clear any existing timers before starting a new one
    this.heartbeatTimer = setInterval(() => {
      if (this.socket && this.socket.readyState === WebSocket.OPEN) {
        this.sendHeartbeat();
      }
    }, this.heartbeatInterval);
  }

  stopHeartbeat() {
    clearInterval(this.heartbeatTimer);
    clearTimeout(this.heartbeatTimeoutTimer);
  }

  sendHeartbeat() {
    const heartbeatMessage = JSON.stringify({ type: 'heartbeat' });
    this.socket.send(heartbeatMessage);
    this.setHeartbeatTimeout();
  }

  setHeartbeatTimeout() {
    this.heartbeatTimeoutTimer = setTimeout(() => {
      console.warn('Heartbeat timeout detected. Closing connection.');
      this.close(1006, 'Heartbeat timeout'); // Close with a specific code indicating heartbeat failure
    }, this.heartbeatTimeout);
  }

  resetHeartbeatTimeout() {
    clearTimeout(this.heartbeatTimeoutTimer);
    this.setHeartbeatTimeout();
  }

  isHeartbeatResponse(data) {
    try {
      const message = JSON.parse(data);
      return message.type === 'heartbeat';
    } catch (e) {
      return false;
    }
  }
}
