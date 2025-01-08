<script setup>
import { ref, watch } from 'vue'

const props = defineProps({
  progress: {
    type: Number,
    default: 0,
    required: true
  }
})

// 动态更新进度条的样式
const progressStyle = ref({})

watch(() => props.progress, (newProgress) => {
  // 设置环形进度条的 CSS 样式
  const progress = newProgress < 0 ? 0 : newProgress > 100 ? 100 : newProgress
  const degree = (progress / 100) * 360
  progressStyle.value = {
    background: `conic-gradient(#6786f8a3 ${degree}deg, #c8d3e7 0deg)`
  }
}, {
  immediate: true
})
</script>

<template>
  <div class="progress-wrapper">
    <div class="circle-background"></div>
    <div class="circle-progress" :style="progressStyle"></div>
    <div class="progress-text">{{ progress }}%</div>
  </div>
</template>

<style scoped lang="less">
.progress-wrapper {
  position: relative;
  width: 180px;
  height: 180px;
  display: flex;
  justify-content: center;
  align-items: center;
  font-family: Arial, sans-serif;
}

.circle-background {
  position: absolute;
  width: 100%;
  height: 100%;
  background: #e6e6e6;
  border-radius: 50%;
  box-sizing: border-box;
  display: flex;
  justify-content: center;
  align-items: center;
}

.circle-progress {
  position: absolute;
  width: 100%;
  height: 100%;
  border-radius: 50%;
  background: conic-gradient(#1d49a8 0deg, #00abf1 0deg); /* 默认空白 */
  transition: background 0.3s ease;
}

.progress-text {
  position: absolute;
  font-size: 24px;
  font-weight: bold;
  color: #fff;
}

@keyframes glow {
  0% {
    filter: drop-shadow(0 0 5px rgba(255, 255, 255, 0.2)) blur(5px);
  }
  50% {
    filter: drop-shadow(0 0 20px rgba(255, 255, 255, 0.3)) blur(5px);
  }
  100% {
    filter: drop-shadow(0 0 5px rgba(255, 255, 255, 0.2)) blur(5px);
  }
}

.circle-progress {
  animation: glow 1.5s infinite alternate;
}
</style>
