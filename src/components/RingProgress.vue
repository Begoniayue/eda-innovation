<script setup>
import { computed } from 'vue';

const props = defineProps({
  percentage: {
    type: Number,
    required: true,
    validator(value) {
      return value >= 0 && value <= 100;
    }
  }
});

// 计算渐变的颜色角度
const circleStyle = computed(() => ({
  '--progress': `${props.percentage * 3.6}deg`, // 将百分比转换为角度
  '--gradient-start': 'hsl(200, 100%, 50%)', // 开始颜色
  '--gradient-end': 'hsl(120, 100%, 50%)' // 结束颜色
}));
</script>

<template>
  <div class="progress-container">
    <div class="circular-progress" :style="circleStyle">
      <span class="percentage">{{ percentage }}%</span>
    </div>
  </div>
</template>

<style scoped lang="less">
.progress-container {
  display: flex;
  justify-content: center;
  align-items: center;
  width: 120px;
  height: 120px;
}

.circular-progress {
  position: relative;
  width: 80px;
  height: 80px;
  border-radius: 50%;
  background: conic-gradient(
    var(--gradient-start) 0deg,
    var(--gradient-end) var(--progress),
    #e0e0e0 var(--progress),
    #e0e0e0 360deg
  );
  transition: background 0.35s ease-out;
}

.circular-progress::before {
  content: '';
  position: absolute;
  top: 10px;
  left: 10px;
  right: 10px;
  bottom: 10px;
  background: #fff;
  border-radius: 50%;
}

.percentage {
  position: absolute;
  top: 50%;
  left: 50%;
  transform: translate(-50%, -50%);
  font-size: 14px;
  color: #333;
}
</style>
