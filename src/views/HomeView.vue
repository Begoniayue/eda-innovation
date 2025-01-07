<script setup>
import { onMounted, ref, watch, nextTick } from 'vue'
import * as monaco from 'monaco-editor'
import LanguageSelector from '@/components/LanguageSelector.vue'
import CircularProgress from '@/components/CircularProgress.vue'
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

onMounted(() => {
  answerEditor = monaco.editor.create(ref_answerEditorContainer?.value, {
    value: '',
    language: answerLanguage.value,
    theme: 'vs-dark',
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
  if (inputMessage.value) {
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
    inputMessage.value = '' // 清空输入框
  }
}

// 模拟自动输出不同类型的日志
setInterval(() => {
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
}, 5000) // 每隔5秒输出日志
//
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

</script>

<template>
  <div class="app">
    <!--    <div class="app-header">-->
    <!--      <div class="logo">-->
    <!--        logo-->
    <!--      </div>-->
    <!--      <div class="buttons">-->
    <!--        <div class="logo">-->
    <!--          iDebug-->
    <!--        </div>-->
    <!--      </div>-->
    <!--    </div>-->
    <div class="app-content">
      <div class="section-block">
        <h1>欢迎来到iDebug,有什么可以帮忙的？</h1>
      </div>
    </div>
    <div class="main-content">
      <div class="left">
        <div class="header">
          <h2>Spec Input:</h2>
        </div>
        <div style="background: #1e1e1e;border-radius: 15px;height: calc(100% - 44px)">
          文字 图片 上传 富文本编辑器
        </div>
      </div>
      <div class="right">
        <div class="header">
          <h2>Debug Log:</h2>
        </div>
        <div class="code-print">
          <div class="code-light code-light-top">
            <div v-html="err" style="color: red"></div>
          </div>
          <div class="code-light">
            <highlightjs language="Xml" :code="displayedCode" />
          </div>
        </div>
      </div>
      <div class="middle">
        <div class="header">
          <h2>Design Code Input:</h2>
          <LanguageSelector v-model="answerLanguage" />
          <div class="button-item run-btn" @click="runCode">
            <svg t="1736214690658" class="icon" viewBox="0 0 1024 1024" version="1.1" xmlns="http://www.w3.org/2000/svg"
                 p-id="2516" width="20" height="20">
              <path
                d="M396.5 661.9V110c0-6.1 7.5-9 11.6-4.6l366.6 394.3c2.4 2.6 2.4 6.6 0 9.1L408.1 903.2c-4.1 4.5-11.6 1.5-11.6-4.6V661.9z"
                fill="#67B47A" p-id="2517"></path>
            </svg>
            run
          </div>
        </div>
        <div ref="ref_answerEditorContainer" class="monaco-editor"></div>
      </div>
      <div class="item-4">
        <div class="button">1</div>
        <div class="button">2</div>
        <div class="button">3</div>
        <div class="button">4</div>
        <div class="button">5</div>
      </div>
      <div class="item-5">
        <div class="output-common">1</div>
        <div class="output-common">2</div>
      </div>
      <div class="item-6">
        <div class="progress-item">
          <div class="title">功能覆盖率</div>
          <div class="desc">code coverage</div>
          <CircularProgress :progress="68" />
        </div>
        <div class="progress-item">
          <div class="title">功能覆盖率</div>
          <div class="desc">code coverage</div>
          <CircularProgress :progress="88" />
        </div>
        <div class="progress-item">
          <div class="title">功能覆盖率</div>
          <div class="desc">code coverage</div>
          <CircularProgress :progress="68" />
        </div>
      </div>
    </div>
    <div class="console-container">
      <!-- 左侧输入区域 -->
      <div class="console-input-section">
        <div class="console-header" style="display: flex;justify-content: space-between;align-items: center">
          Input Log
          <div class="button-item console-button" @click="logMessage">
            <svg t="1736214728261" class="icon" viewBox="0 0 1024 1024" version="1.1" xmlns="http://www.w3.org/2000/svg"
                 p-id="3688" width="28" height="28">
              <path
                d="M715.872 473.392c-15.472-112.736-103.616-196.864-207.36-196.864-103.68 0-191.872 84.064-207.344 196.864h414.72z m-463.072 0l0.192-1.712c16.72-138.08 125.376-243.152 255.52-243.152 130.752 0 239.728 105.984 255.744 244.864h45.488a16 16 0 0 1 16 16v16a16 16 0 0 1-16 16H208a16 16 0 0 1-16-16v-16a16 16 0 0 1 16-16h44.8z m486.656 117.92c13.888 3.472 12.352 13.472 10.912 18.208-34.8 113.696-131.088 192.912-242.08 192.912-110.144 0-205.856-78.016-241.312-190.432-1.536-4.896-4.64-14.432 10.832-18.848l16.528-4.32c15.52-3.968 17.392 5.52 18.864 10.096 29.728 92.56 107.376 155.504 195.088 155.504 88 0 165.824-63.36 195.36-156.304 1.536-4.864 3.616-14.88 19.936-10.832l15.872 4.032z m54.624 84.16h16a16 16 0 0 1 16 16v125.568a16 16 0 0 1-16 16h-125.552a16 16 0 0 1-16-16v-16a16 16 0 0 1 16-16h93.552v-93.568a16 16 0 0 1 16-16z m-570.08 0a16 16 0 0 1 16 16v93.568h93.568a16 16 0 0 1 16 16v16a16 16 0 0 1-16 16H208a16 16 0 0 1-16-16v-125.568a16 16 0 0 1 16-16h16z m570.08-325.92a16 16 0 0 1-16-16V240h-93.552a16 16 0 0 1-16-16v-16a16 16 0 0 1 16-16h125.552a16 16 0 0 1 16 16v125.568a16 16 0 0 1-16 16h-16z m-570.08 0h-16a16 16 0 0 1-16-16V208a16 16 0 0 1 16-16h125.568a16 16 0 0 1 16 16v16a16 16 0 0 1-16 16H240v93.568a16 16 0 0 1-16 16zM591.168 648.32c10.224 11.68 1.04 18.976-3.84 21.648-21.648 11.824-49.536 18.384-78.96 18.384-28.912 0-56.368-6.336-77.872-17.792-5.12-2.736-14.08-9.36-4.32-22.336l10.528-14.016c7.824-11.088 16.048-5.984 20.736-3.84 13.648 6.224 31.584 9.984 50.928 9.984 18.928 0 36.496-3.6 50-9.568 5.168-2.288 12.512-7.664 22.816 4.384l9.984 13.152z"
                fill="#fff" p-id="3689"></path>
            </svg>
            Test
          </div>
        </div>
        <div class="console-input-container">
          <input v-model="inputMessage" type="text" placeholder="Enter log message..." />
        </div>
      </div>

      <!-- 右侧输出区域 -->
      <div class="console-output-section">
        <div class="console-header">Console Output</div>
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
    <div class="title">
    </div>
  </div>

</template>
<style scoped lang="less">
.app {
  display: flex;
  flex-direction: column;
  color: #333;
  background-color: #171616;


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
      color: #0071e3;
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
    grid-template-rows:700px 200px 500px;
    grid-gap: 20px;
    margin-top: -115px;

    .left, .middle, .right {
      position: relative;
      flex: 1;
      display: flex;
      flex-direction: column;

      h2 {
        margin-bottom: 15px;
        font-size: 24px;
        font-weight: bold;
        color: #fff;
      }
    }

    .item-4 {
      grid-column-start: 1;
      grid-column-end: 3;
      color: #FFFFFF;
      border: 1px solid #fff;
      display: flex;
      justify-content: space-around;
      align-items: center;

      .button {
        border: 1px solid #fff;
        display: flex;
        align-items: center;
        justify-content: center;
        width: 16%;
        height: 50%;
      }
    }

    .item-5 {
      grid-column-start: 3;
      grid-column-end: 4;
      grid-row-start: 2;
      grid-row-end: 4;
      color: #FFFFFF;
      border: 1px solid #fff;

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
        justify-content: space-between;
      }
    }

    .middle {
      overflow-y: auto;

      .header {
        display: flex;
        justify-content: space-between;
      }
    }

    .right {
      overflow: hidden;

      .header {
        padding-left: 20px;
        width: 50%;
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
    font-size: 24px;
    font-weight: bold;
    text-transform: uppercase;
    color: #ffffff;
    padding: 10px 30px;
    //margin: 0 20px;
    //background: linear-gradient(#0e143f 20%, #5b5959); /* 渐变背景 */
    box-shadow: 2px 2px 5px rgba(0, 0, 0, 0.2); /* 阴影效果 */
    text-align: center;
  }

  .placeholder {
    width: 100%; /* 占满整个宽度 */
    height: 500px; /* 设置高度为500px */
  }

  .section-block {
    height: 320px;
    background-image: linear-gradient(to bottom, rgba(0, 0, 0, 0) 90%, rgba(0, 16, 33, 1)), url('../assets/images/back-center.png');
    background-position: center;
    background-size: cover;
    padding-top: 110px;
    text-align: center;

    h1 {
      text-align: center;
      color: #FFF;
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
  background-color: #1e1e1e;
  color: #fff;
  border-radius: 8px;
}

.console-input-section {
  width: 50%;
  padding: 10px;
  background-color: #333;
  display: flex;
  flex-direction: column;
}

.console-output-section {
  width: 50%;
  padding: 10px;
  background-color: #222;
  color: #fff;
  display: flex;
  flex-direction: column;
}

.console-header {
  padding: 10px;
  background-color: #444;
  text-align: center;
  font-weight: bold;
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
  background-color: #555;
}

.console-input-container {
  display: flex;
  padding: 10px;
  background-color: #333;
}

input {
  flex-grow: 1;
  padding: 8px;
  font-size: 14px;
  border: none;
  border-radius: 4px;
  color: #fff;
  background-color: #333;

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
  background-color: #222;
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
  background-color: #2d2d2d;
  width: 100%;
  white-space: wrap;
  overflow-y: auto;
  font-family: monospace;
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
</style>
