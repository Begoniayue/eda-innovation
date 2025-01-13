export const createWebSocketClient = (url, protocols = [], options = {}) => {
  let socket = null
  let heartbeatTimer = null
  let heartbeatTimeoutTimer = null
  let reconnectAttempts = 0

  const defaults = {
    maxReconnectAttempts: 5,
    reconnectInterval: 3000, // 3 seconds
    heartbeatInterval: 3000, // 3 seconds
    heartbeatTimeout: 5000, // 5 seconds
    onOpen: () => {
    },
    onMessage: () => {
    },
    onError: () => {
    },
    onClose: () => {
    }
  }

  const settings = { ...defaults, ...options }

  function connect() {
    try {
      socket = new WebSocket(url, protocols)

      socket.onopen = (event) => {
        console.log('WebSocket connection opened:', event)
        // resetReconnectAttempts()
        settings.onOpen(event)
        startHeartbeat()
      }

      socket.onmessage = (event) => {
        settings.onMessage(event.data)
        // if (isHeartbeatResponse(event.data)) {
        //   resetHeartbeatTimeout()
        // }
      }

      socket.onerror = (error) => {
        console.error('WebSocket error:', error)
        settings.onError(error)
      }

      socket.onclose = (event) => {
        console.log('WebSocket connection closed:', event)
        stopHeartbeat()
        settings.onClose(event)

        // Attempt to reconnect if not closed intentionally
        // if (!event.wasClean && getReconnectAttempts() < settings.maxReconnectAttempts) {
        //   setTimeout(() => {
        //     incrementReconnectAttempts()
        //     connect()
        //   }, settings.reconnectInterval)
        // }
      }
    } catch (err) {
      console.error('Failed to create WebSocket:', err)
      settings.onError(err)
    }
  }

  function send(data) {
    if (socket && socket.readyState === WebSocket.OPEN) {
      socket.send(data)
    } else {
      console.warn('WebSocket is not open. Ready state:', socket ? socket.readyState : 'null')
    }
  }

  function close(code = 1000, reason = '') {
    if (socket) {
      stopHeartbeat()
      socket.close(code, reason)
    }
  }

  function startHeartbeat() {
    stopHeartbeat() // Clear any existing timers before starting a new one
    heartbeatTimer = setInterval(() => {
      if (socket && socket.readyState === WebSocket.OPEN) {
        sendHeartbeat()
      }
    }, settings.heartbeatInterval)
  }

  function stopHeartbeat() {
    clearInterval(heartbeatTimer)
    // clearTimeout(heartbeatTimeoutTimer)
  }

  function sendHeartbeat() {
    const heartbeatMessage = JSON.stringify({ type: 'heartbeat' })
    socket.send(heartbeatMessage)
    // setHeartbeatTimeout()
  }

  function setHeartbeatTimeout() {
    heartbeatTimeoutTimer = setTimeout(() => {
      console.warn('Heartbeat timeout detected. Closing connection.')
      // close(1006, 'Heartbeat timeout') // Close with a specific code indicating heartbeat failure
    }, settings.heartbeatTimeout)
  }

  function resetHeartbeatTimeout() {
    clearTimeout(heartbeatTimeoutTimer)
    setHeartbeatTimeout()
  }

  function isHeartbeatResponse(data) {
    try {
      const message = JSON.parse(data)
      return message.type === 'heartbeat'
    } catch (e) {
      return false
    }
  }

  function resetReconnectAttempts() {
    setReconnectAttempts(0)
  }

  function incrementReconnectAttempts() {
    setReconnectAttempts(getReconnectAttempts() + 1)
  }

  function setReconnectAttempts(value) {
      reconnectAttempts = value
  }

  function getReconnectAttempts() {
    return reconnectAttempts || 0
  }

  connect()

  return {
    send,
    close
  }
}
