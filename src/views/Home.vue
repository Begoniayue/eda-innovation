<script setup>
import { onMounted, ref, watch, nextTick } from 'vue'
import * as monaco from 'monaco-editor'
import LanguageSelector from '@/components/LanguageSelector.vue'
import CircularProgress from '@/components/CircularProgress.vue'
import TinyEditor from '@/components/editor.vue'
import hljs from 'highlight.js'

const ref_answerEditorContainer = ref(null)
let answerEditor = null
let decorationsCollection = null

const answerLanguage = ref('python')

// 初始代码
const initialCode = {
  javascript: `let a = 10;
const b = 20;
console.log(a + b);
console.log(c); // This will cause an error.`,
  python: `def solveNQueens(n):
    def is_safe(board, row, col):
        for i in range(row):
            if board[i] == col or board[i] - i == col - row or board[i] + i == col + row:
                return False
        return True

    def solve(board, row):
        if row == n:
            result.append(["." * i + "Q" + "." * (n - i - 1) for i in board])
            return
        for col in range(n):
            if is_safe(board, row, col):
                board[row] = col
                solve(board, row + 1)
                board[row] = -1

    result = []
    solve([-1] * n, 0)
    return result`,
  java: `public class Main {
    public static void main(String[] args) {
        int a = 10;
        int b = 20;
        System.out.println(a + b);
        System.out.println(c);  // This will cause an error
    }
}`,
  typescript: `let a: number = 10;
let b: number = 20;
console.log(a + b);
console.log(c);  // This will cause an error`,
  cpp: `#include <iostream>
using namespace std;

int main() {
    int a = 10;
    int b = 20;
    cout << a + b << endl;
    cout << c;  // This will cause an error
    return 0;
}`
}
const initSpec = ref(``)
onMounted(() => {
  answerEditor = monaco.editor.create(ref_answerEditorContainer?.value, {
    value: '',
    language: answerLanguage.value,
    theme: 'vs-light',
    automaticLayout: true,
    lineNumbers: 'on'
  })
  decorationsCollection = answerEditor.createDecorationsCollection()
})
// 获取题目
const getQuestion = async () => {
  try {
    return ''
  } catch (e) {

  }
}
const submit = () => {
  console.log(answerEditor.getValue())
}
const setHighLightStyle = () => {
  const style = document.createElement('style')
  style.innerHTML = `
    .highlight-error-line {
        background-color: rgba(165, 42, 42, 0.5);
    }
`
  document.head.appendChild(style)
}
const clearHighLight = () => {
  if (!decorationsCollection) {
    return
  }
  decorationsCollection.clear()
}
const setHighLight = (options) => {
  if (!decorationsCollection) {
    return
  }
  const decorationOptions = [{
    range: new monaco.Range(5, 1, 5, 1),
    options: {
      isWholeLine: true,
      className: 'highlight-error-line'
    }
  }]

  decorationsCollection.set(decorationOptions)
}
const init = () => {
  getQuestion()
  setHighLightStyle()
}
watch(answerLanguage, (value) => {
  answerEditor.setModel(monaco.editor.createModel('', value))
})
init()

///

// 控制台日志数组
const logs = ref([])

// 用户输入的消息
const inputMessage = ref('')

// 选中的日志
const selectedLog = ref(null)

// 添加日志到左侧的日志列表
const logMessage = () => {
  runCode()
  logs.value.push({
    type: 'info',
    message: 'Info: Page loaded successfully!'
  })
  logs.value.push({
    type: 'warning',
    message: 'Warning: Your session will expire soon.'
  })
  logs.value.push({
    type: 'error',
    message: 'Error: Something went wrong.'
  })
}
const analyseLog = ref([])
const analyerMessage = () => {
  runCode()
  analyseLog.value.push({
    type: 'info',
    message: 'Info: Page loaded successfully!'
  })
  analyseLog.value.push({
    type: 'warning',
    message: 'Warning: Your session will expire soon.'
  })
  analyseLog.value.push({
    type: 'error',
    message: 'Error: Something went wrong.'
  })
}

const code = ref('{\n' +
  '    "Email": "string",\n' +
  '    "Wxid": "string"\n' +
  '}')
const err = ref()
// 初始化动态的 data
const data = ref(`{
import heapq

class MedianFinder:

    def __init__(self):
        self.min_heap = []  # 存储较大的一半
        self.max_heap = []  # 存储较小的一半

    def addNum(self, num: int) -> None:
        heapq.heappush(self.min_heap, num)
        heapq.heappush(self.max_heap, -heapq.heappop(self.min_heap))
        if len(self.min_heap) < len(self.max_heap):
            heapq.heappush(self.min_heap, -heapq.heappop(self.max_heap))

    def findMedian(self) -> float:
        if len(self.min_heap) > len(self.max_heap):
            return self.min_heap[0]
        return (self.min_heap[0] - self.max_heap[0]) / 2.0
}`)

const displayedCode = ref('') // 用于保存逐步显示的代码

const codeElement = ref(null) // 用于引用 <code> 元素

// 运行代码
const runCode = () => {
  err.value = `  <pre>
    <code>
    编译出错
      Line 5: Char 5: error: non-void function does not return a value [-Werror,-Wreturn-type]
      5 |     }
      |     ^
      1 error generated.
    </code>
  </pre>`
  setHighLight()
  typingEffect()
}
// 模拟逐字打字效果
let index = 0
const typingEffect = () => {
  if (index < data.value.length) {
    displayedCode.value += data.value[index]  // 逐字添加
    index++
    setTimeout(typingEffect, 50)  // 每50ms显示一个字符
  }
}

// 在代码更新时应用语法高亮
watch(displayedCode, () => {
  nextTick(() => {
    if (codeElement.value) {
      hljs.highlightElement(codeElement.value) // 高亮更新后的代码
    }
  })
})
// 进度progress
const progress = ref(0)
const functionCoverage = ref(0)
const lineCoverage = ref(0)
const startIncrement = () => {
  // 设置一个定时器，每100毫秒增加一次进度
  const interval = setInterval(() => {
    // 累加进度条的值
    if (lineCoverage.value < 100) {
      lineCoverage.value = Math.min(lineCoverage.value + 2, 500);
    }
    if (functionCoverage.value < 100) {
      functionCoverage.value = Math.min(functionCoverage.value + 1, 600);
    }
    if (progress.value < 100) {
      progress.value = Math.min(progress.value + 10, 200);
    }

    // 如果所有进度条都已经到达 100，停止定时器
    if (lineCoverage.value === 100 && functionCoverage.value === 100 && progress.value === 100) {
      clearInterval(interval);
    }
  }, 100); // 每100毫秒增加一次进度
};
const repairCode = () => {
  runCode()
  logs.value = []
  analyseLog.value = []
  clearHighLight()
};
const testBuild = () => {
  runCode()
  startIncrement()
};
const domScoll = () => {
  const element = document.getElementById('main-content')
  element.scrollIntoView({ behavior: 'smooth' })
}
</script>

<template>
  <div class="app">
    <div class="app-header">
      <div class="buttons">
        <div class="logo">
          iDebug
        </div>
      </div>
      <div class="logo">
        <img src="https://www.nctieda.com/images/logo1.png" alt="" width="400"></img>
      </div>

    </div>
    <div class="app-content">
      <div class="banner-content-bg">
        <div class="title">
          <div>欢迎来到iDebug,有什么可以帮忙的？</div>
          <div class="try-button" @click="domScoll">立即体验</div>
        </div>
        <video autoplay="" loop="" muted=""
               src="https://res-video.hc-cdn.com/cloudbu-site/china/zh-cn/advertisement/Fixed/banner/1725874846387175930.mp4" style="opacity: 1;">
        </video>
        <div class="events-container"></div>
      </div>
    </div>
    <div class="main-content">
      <div class="left">
        <div class="header">
          <h2>Spec Input</h2>
        </div>
        <div style="background: #f5f5f5;border-radius: 15px;height: calc(100% - 44px)">
          <TinyEditor v-model="initSpec" :height="515" :language="'json'" />
        </div>
      </div>
      <div class="right">
        <div class="header">
          <h2>Debug Log</h2>
        </div>
        <div class="code-print">
          <div class="code-light code-light-top">
          </div>
          <div class="code-light">
            <div v-html="displayedCode"></div>
          </div>
        </div>
      </div>
      <div class="middle">
        <div class="header">
          <h2>Design Code Input</h2>
          <LanguageSelector v-model="answerLanguage" />
        </div>
        <div ref="ref_answerEditorContainer" class="monaco-editor"></div>
      </div>
    </div>
    <div class="main-content">
      <div class="left">
        <div style="background: #ffffff">
          <div class="button-list">
            <div class="button" @click="testBuild">测试生成</div>
            <div class="button" @click="logMessage">仿真</div>
            <div class="button" @click="analyerMessage">分析</div>
            <div class="button" @click="repairCode">修复</div>
          </div>
          <div class="animate-fade">
            <img src="@/assets/images/shuju.png">
          </div>
          <div class="coverage">
            <div class="progress-item">
              <div class="title">功能覆盖率</div>
              <div class="desc">code coverage</div>
              <CircularProgress :progress="progress" />
            </div>
            <div class="progress-item">
              <div class="title">行覆盖率</div>
              <div class="desc"> line coverage </div>
              <CircularProgress :progress="lineCoverage" />
            </div>
            <div class="progress-item">
              <div class="title">翻转覆盖率</div>
              <div class="desc">function coverage</div>
              <CircularProgress :progress="functionCoverage" />
            </div>
          </div>
        </div>

      </div>
      <div class="left">
        <div class="console-output-section">
          <h2 class="console-header">结果Result</h2>
          <div class="console-output">
            <div v-if="logs.length>0">
              <div v-for="(log, index) in logs" :key="index" :class="log.type">
                {{ log.message }}
              </div>
            </div>
            <div v-else class="no-log">Select a log to see details...</div>
          </div>
        </div>
      </div>
      <div class="right">

        <div class="console-output-section">
          <h2 class="console-header">分析Analyze</h2>
          <div class="console-output">
            <div v-if="logs.length>0">
              <div v-for="(log, index) in analyseLog" :key="index" :class="log.type">
                {{ log.message }}
              </div>
            </div>
            <div v-else class="no-log">Select a log to see details...</div>
          </div>
        </div>
      </div>
    </div>
    <div class="title">
    </div>
  </div>

</template>
<style scoped lang="less">
.app {
  display: flex;
  flex-direction: column;
  color: #333333;
  background-color: #f7f7f7;
  .app-header {
    display: flex;
    justify-content: space-between;
    align-items: center;
    width: 100%;
    padding: 20px 50px;
    background-color: #fff; /* 背景色 */
    box-shadow: 0 2px 10px rgba(0, 0, 0, 0.1); /* 阴影效果 */

    .logo {
      font-size: 24px;
      font-weight: bold;
      color: #333333;
      font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", "Roboto", "Helvetica Neue", "Arial", sans-serif;
    }

    .buttons {
      display: flex;
      gap: 10px;

      .apple-button {
        padding: 10px 15px;
        background: linear-gradient(145deg, #a8e063, #56ab2f); /* Apple 风格的渐变背景 */
        border: none;
        border-radius: 15px; /* 苹果风格的圆角 */
        color: white;
        font-size: 14px;
        font-weight: bold;
        box-shadow: 2px 2px 5px rgba(0, 0, 0, 0.2); /* 添加阴影效果 */
        cursor: pointer;
        transition: all 0.3s ease; /* 平滑过渡效果 */
      }

      .apple-button:hover {
        transform: translateY(-2px); /* 鼠标悬停时按钮稍微上浮 */
      }

      .apple-button:active {
        transform: translateY(2px); /* 按下时按钮稍微下沉 */
      }
    }
  }

  .main-content {
    display: grid;
    padding: 20px;
    grid-template-columns: 1fr 1fr 1fr;
    grid-template-rows:560px 0px 0px;
    grid-gap: 10px;
    padding-bottom: 0px;
    margin-top: -28px;

    .left, .middle, .right {
      position: relative;
      flex: 1;
      display: flex;
      flex-direction: column;

      h2 {
        margin-bottom: 15px;
        font-size: 24px;
        font-weight: bold;
        color: #333333;

      }
    }

    .item-4 {
      grid-column-start: 1;
      grid-column-end: 3;
      color: #333333;
      border: 1px solid #fff;
      background: linear-gradient(to bottom, #ffffff, #87A2D2FF);
      border: 8px;
      display: flex;
      justify-content: space-around;
      align-items: center;

      .button {
        background-color: #f0f0f0; /* 浅灰色背景 */
        color: #333; /* 字体颜色 */
        border: 1px solid #ccc; /* 灰色边框 */
        padding: 10px 20px; /* 内边距 */
        font-size: 16px; /* 字体大小 */
        border-radius: 25px; /* 圆角 */
        cursor: pointer; /* 鼠标悬停时显示为手形 */
        transition: all 0.3s ease; /* 平滑过渡效果 */
      }

      /* 鼠标悬停时 */
      .button:hover {
        background-color: #e0e0e0; /* 悬停时变为稍微深一点的灰色 */
        border-color: #bbb; /* 边框颜色变深 */
        box-shadow: 0 2px 6px rgba(0, 0, 0, 0.1); /* 悬停时的阴影效果 */
      }

      /* 鼠标点击时 */
      .button:active {
        background-color: #d0d0d0; /* 点击时变为更深的灰色 */
        border-color: #aaa; /* 边框颜色变更深 */
        transform: translateY(2px); /* 点击时按钮稍微下沉 */
      }
    }

    .item-5 {
      grid-column-start: 3;
      grid-column-end: 4;
      grid-row-start: 2;
      grid-row-end: 4;
      color: #FFFFFF;
      background: #f0f0f0;

      .output-common {
        height: 50%;
      }

      .output-common:last-child {
        border-top: 1px solid #fff;
      }
    }

    .item-6 {
      grid-column-start: 1;
      grid-column-end: 3;
      color: #FFFFFF;
      border: 1px solid #fff;
      display: flex;
      align-items: center;
      justify-content: space-around;

    }

    .left {
      overflow-y: auto;

      .header {
        display: flex;
        justify-content: center;
      }
    }

    .middle {
      overflow-y: auto;

      .header {
        display: flex;
        justify-content: center;
      }
    }

    .right {
      overflow: hidden;

      .header {
        padding-left: 20px;
        display: flex;
        justify-content: center;
      }
    }

    .monaco-editor {
      border-radius: 15px;
      overflow: hidden;
      width: 100%;
      height: calc(100% - 44px);
    }
  }

  .title {
    font-size: 20px;
    font-weight: bold;
    color: #333333;
    padding: 10px 30px;
    //margin: 0 20px;
    //background: linear-gradient(#0e143f 20%, #5b5959); /* 渐变背景 */
    text-align: center;
  }

  .placeholder {
    width: 100%; /* 占满整个宽度 */
    height: 500px; /* 设置高度为500px */
  }

  .section-block {
    height: 360px;
    background-position: center;
    background-size: cover;
    padding-top: 200px;
    text-align: center;

    h1 {
      text-align: center;
      color: #333333;
      font-weight: normal;
      letter-spacing: 2px;
    }
  }
}


.run-btn {
  display: flex;
  justify-content: center;
  align-items: center;
  cursor: pointer;
  color: #fff;
  /* background: #181819; */
  border-radius: 13px;
  border: 1px solid #fff;
  margin-bottom: 15px;
  padding: 5px 8px;
}

.response-params {
  margin-top: 45px;
  color: #fff;
  line-height: 40px;
}

//
.console-container {
  display: flex;
  width: 100%;
  height: 400px;
  margin: 20px auto;
  background-color: #ffffff;
  color: #fff;
  border-radius: 8px;
}

.console-input-section {
  width: 50%;
  padding: 10px;
  background-color: #fff;
  display: flex;
  flex-direction: column;
}

.console-output-section {
  width: 100%;
  padding: 10px;
  background-color: #fff;
  margin-bottom: 20px;
  color: #333333;
  display: flex;
  flex-direction: column;
  overflow-y: auto;
  height: 320px;
  text-align: left;
  border-radius: 12px;
}

.console-header {
  padding: 10px;
  text-align: center;
  font-weight: bold;
  color: #333333;
}

.log-list {
  flex-grow: 1;
  overflow-y: auto;
  margin-bottom: 10px;
}

.log-item {
  padding: 8px;
  cursor: pointer;
  border-bottom: 1px solid #444;
}

.log-item:hover {
  background-color: #fff;
}

.console-input-container {
  display: flex;
  padding: 10px;
  background-color: #fff;
}

input {
  flex-grow: 1;
  padding: 8px;
  font-size: 14px;
  border: none;
  border-radius: 4px;
  color: #fff;
  background-color: #fff;

  &:focus {
    outline: none;
  }
}

button {
  padding: 8px 12px;
  margin-left: 10px;
  background-color: #409eff;
  border: none;
  border-radius: 4px;
  color: #fff;
  cursor: pointer;
}

button:hover {
  background-color: #66b1ff;
}

.console-output {
  flex-grow: 1;
  padding: 10px;
  font-family: 'Courier New', monospace;
  font-size: 14px;
  background-color: #fff;
  overflow-y: auto;
}

.log-detail {
  color: #7ec8e3;
}

.no-log {
  color: #888;
}

/* 不同类型的日志 */
.info {
  color: #7ec8e3;
}

.warning {
  color: #e6a23c;
}

.error {
  color: #f87171;
}

.console-button {
  color: #ffffff;
  line-height: 20px;
  background: #0071e3;
  border-radius: 25px;
  padding: 5px 20px;

  .icon {
    display: inline-block;
  }
}

.button-item {
  display: flex;
  justify-content: center;
  align-items: center;
  cursor: pointer;
}

/* 自定义滚动条样式 */
.log-list, .console-output {
  scrollbar-width: thin;
  scrollbar-color: #ddd #333; /* 滚动条轨道颜色 #333 背景，滑块颜色 #409eff */
}

.log-list::-webkit-scrollbar, .console-output::-webkit-scrollbar {
  width: 8px; /* 设置滚动条宽度 */
}

.log-list::-webkit-scrollbar-thumb, .console-output::-webkit-scrollbar-thumb {
  background-color: #ddd; /* 滑块颜色 */
  border-radius: 8px;
  border: 2px solid #333; /* 滑块的边框颜色 */
}

.log-list::-webkit-scrollbar-track, .console-output::-webkit-scrollbar-track {
  background-color: #333; /* 滚动条轨道背景颜色 */
  border-radius: 8px;
}

.log-list::-webkit-scrollbar-thumb:hover, .console-output::-webkit-scrollbar-thumb:hover {
  background-color: #66b1ff; /* 鼠标悬停时的滑块颜色 */
}

///* 代码块样式 */
.code-light-top {
  line-height: 21px;
}

pre {
  background-color: #2d2d2d;
  color: #f8f8f2;
  border-radius: 4px;
  font-size: 16px;
  line-height: 1.5;
}

code {
  display: block;
  padding: 10px;
}

.code-print {
  height: calc(100% - 44px);
  border-radius: 15px;
  background-color: #ffffff;
  color: #333;
  font-size: 20px;
  width: 100%;
  line-height: 40px;
  padding: 20px;
  white-space: wrap;
  overflow-y: auto;
  font-family: monospace;
  &:hover {
    box-shadow: 0 4px 12px rgba(0, 0, 0, .08);
    z-index: 1;
  }
}

/* 定义滚动条整体样式 */
.code-print::-webkit-scrollbar {
  width: 10px; /* 设置竖直滚动条宽度 */
  height: 10px; /* 设置水平滚动条高度 */
}

/* 滚动条轨道（背景） */
.code-print::-webkit-scrollbar-track {
  background: #f0f0f0; /* 滚动条轨道背景 */
  border-radius: 10px;
}

/* 滚动条滑块（可滑动部分） */
.code-print::-webkit-scrollbar-thumb {
  background: #888; /* 滚动条滑块的颜色 */
  border-radius: 10px; /* 滚动条滑块的圆角 */
}

/* 滚动条滑块悬浮时的样式 */
.code-print::-webkit-scrollbar-thumb:hover {
  background: #555; /* 滑块悬浮时的颜色 */
}

/* 横向滚动条样式 */
.code-print::-webkit-scrollbar-horizontal {
  height: 8px;
}

/* 竖向滚动条样式 */
.code-print::-webkit-scrollbar-vertical {
  width: 8px;
}
.bottom{

  display: flex;
  margin: 20px;
  margin-top: -10px;
  .left, .right {
    width: 50%; /* 每个部分占 50% 宽度 */
  }
  .left {
    width: 35%;
    text-align: center;
    margin-right: 20px;
    background: #ffffff;
    border-radius: 12px;
    padding: 25px;
    position: relative;
  }
  .right {
    width: 64%;
    text-align: center;
    border-radius: 12px;

  }
}
.button-list{
  display: flex;
  justify-content: start;
  padding-top: 20px;
  margin-bottom: -30px;
  padding-left: 15px;
  .button{
    background-color: #e7f1ff;
    color: #1677ff;
    border: 1px solid #8abbff;
    padding: 10px 20px;
    font-size: 16px;
    border-radius: 5px;
    cursor: pointer;
    transition: all 0.3s ease;
    margin-right: 10px;
  }
  .button:hover {
    background-color: #1677ff;
    border-color: #ffffff;
    color: #ffffff;
  }

  /* 鼠标点击时 */
  .button:active {
    background-color: #1677ff;
    border-color: #ffffff;
    color: #ffffff;
  }
}
.coverage{
  display: flex;
  justify-content: space-between;
  margin-top: 60px;
}
.progress-item{
  color: #333333;
  .desc{
    text-align: center;
    margin-bottom: 20px;
  }
}
.animate-fade{
  animation: matrixTopTranslate 3s steps(60) infinite;
  position: absolute;
  right: 15px;
  top: 10px;
  img{
    height: 70px;
    width: 60px;
    display: inline-block;
    margin-top: 10px;
  }
}
@keyframes matrixTopTranslate {
  0% {
    top: 0
  }

  50% {
    top: -10px
  }

  to {
    top: 0
  }
}
.banner-content-bg{
  position: relative;
  height: 100%;
  .title{
    color: #333333;
    font-size: 30px;
    position: absolute;
    top: 32%;
    left: 1%;
    opacity: 0; /* 动画前初始状态 */
    transform: translateY(30px); /* 初始位置向下 */
    animation: slideUpFade 1s ease-out 0.5s forwards; /* 延迟0.5s出现 */
    transition: all 0.3s ease-in-out;
  }
  video{
    height: 100%;
    width: 100%;
  }
}
.try-button{
  width: 200px;
  border: 1px solid #595959;
  border-radius: 30px;
  -webkit-box-sizing: border-box;
  box-sizing: border-box;
  font-size: 18px;
  height: 60px;
  line-height: 60px;
  padding: 0 32px;
  text-align: center;
  margin-top: 30px;
  cursor: pointer;
  opacity: 0; /* 动画前初始状态 */
  transform: translateY(30px); /* 初始位置向下 */
  animation: slideUpFade 1s ease-out 0.5s forwards; /* 延迟0.5s出现 */
  transition: all 0.3s ease-in-out;
  z-index: 999999;
}
.events-container {
  -webkit-backdrop-filter: blur(20px);
  backdrop-filter: blur(20px);
  background: hsla(0, 0%, 99%, .2);
  bottom: 0;
  height: 40px;
  width: 100%;
  z-index: 99;
  margin-top: -20px;
}

/* 向上移动和淡入的动画 */
@keyframes slideUpFade {
  from {
    opacity: 0;
    transform: translateY(30px); /* 初始位置向下 */
  }
  to {
    opacity: 1;
    transform: translateY(0); /* 目标位置 */
  }
}
</style>
