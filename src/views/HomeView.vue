<script setup>
import { onMounted, ref, watch } from 'vue'
import * as monaco from 'monaco-editor'
import LanguageSelector from '@/components/LanguageSelector.vue'
import CircularProgress from '@/components/CircularProgress.vue'

const ref_questionEditorContainer = ref(null)
const ref_answerEditorContainer = ref(null)
let answerEditor = null
let questionEditor = null
let decorationsCollection = null

const questionLanguage = ref('javascript')
const answerLanguage = ref('javascript')

// 初始代码
const initialCode = {
  javascript: `let a = 10;
const b = 20;
console.log(a + b);
console.log(c); // This will cause an error.`,
  python: `a = 10
b = 20
print(a + b)
print(c)  # This will cause an error`,
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

  questionEditor = monaco.editor.create(ref_questionEditorContainer?.value, {
    value: initialCode[questionLanguage.value],
    language: questionLanguage.value,
    theme: 'vs-dark',
    automaticLayout: true,
    lineNumbers: 'on',
    readOnly: true  // 设置右侧为只读模式
  })
  decorationsCollection = answerEditor.createDecorationsCollection()
})
// 设置题目
const setQuestion = (question) => {
  questionEditor.setValue(question)
}
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
    range: new monaco.Range(1, 1, 1, 5),
    options: {
      isWholeLine: true,
      className: 'highlight-error-line'
    }
  }, {
    range: new monaco.Range(3, 1, 3, 5),
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
watch(questionLanguage, async (value) => {
  try {
    const res = await getQuestion()
    questionEditor.setModel(monaco.editor.createModel(initialCode[value], value))
  } catch (e) {

  }
})
watch(answerLanguage, (value) => {
  answerEditor.setModel(monaco.editor.createModel('', value))
})
init()

//

const logs = ref([])

// 用户输入的消息
const inputMessage = ref('')

// 添加日志到控制台
const logMessage = () => {
  if (inputMessage.value) {
    logs.value.push({
      type: 'info', // 默认信息类型
      message: inputMessage.value
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





</script>

<template>
  <div class="app">
    <div class="app-header">
      <div class="logo">
        logo
      </div>
      <div class="buttons">
        <div class="logo">
          iDebug
        </div>
      </div>
    </div>
    <div class="app-content">
      <div class="section-block">
        <h1>欢迎来到iDebug,有什么可以帮忙的？</h1>
      </div>
    </div>
    <div class="main-content">
      <div class="left">
        <div class="header">
          <h2>Spec Input:</h2>
          <LanguageSelector v-model="questionLanguage" />
        </div>
        <div ref="ref_questionEditorContainer" class="monaco-editor"></div>
      </div>
      <div class="middle">
        <div class="header">
          <h2>Design Code Input:</h2>
          <LanguageSelector v-model="answerLanguage" />
        </div>
        <div ref="ref_answerEditorContainer" class="monaco-editor"></div>
      </div>
      <div class="right">
        <div class="right-header">
          <h2>Debug Log:</h2>
        </div>
      </div>
    </div>
    <div class="button-container">
      <div class="button-item">
        <svg t="1736214610331" class="icon" viewBox="0 0 1024 1024" version="1.1" xmlns="http://www.w3.org/2000/svg" p-id="1519" width="20" height="20"><path d="M516.5 607.6l-62.7 62.7 6 9V736h56.7v53.8h-56.7v3c-2 19.9-7 37.8-14.9 53.8l71.7 74.7-38.8 38.8-62.7-62.7c-13.9 19.9-31.9 35.3-53.8 46.3s-44.8 16.4-68.7 16.4-46.8-5.5-68.7-16.4-39.8-26.4-53.8-46.3l-62.7 62.7-38.8-38.8 71.7-71.7c-8-17.9-12.9-35.8-14.9-53.8v-3H68.7v-56.7h56.7v-56.7l9-9-65.7-62.7 38.8-38.8 50.8 47.8c8-29.9 24.4-54.8 49.3-74.7s53.3-29.9 85.1-29.9 60.2 10 85.1 29.9c24.9 19.9 41.3 44.8 49.3 74.7l50.8-47.8 38.8 38.8z m-224-38.9c-23.9 0-43.8 8-59.7 23.9-15.9 15.9-23.9 35.8-23.9 59.7h167.3c0-23.9-8-43.8-23.9-59.7s-35.8-23.9-59.7-23.9zM406 709.1H182v83.6c2 29.9 13.4 55.3 34.3 76.2 20.9 20.9 46.3 32.4 76.2 34.3 29.9-2 55.3-13.4 76.2-34.3 20.9-20.9 33.4-46.3 37.3-76.2v-83.6zM391 64l-41.8 23.9v376.3c19.9 6 38.8 14.9 56.7 26.9V138.7l483.8 307.6-316.6 200.1v65.7l382.3-241.9v-47.8L391 64z" p-id="1520"></path></svg>
        debug
      </div>
      <div class="button-item">
        <svg t="1736214690658" class="icon" viewBox="0 0 1024 1024" version="1.1" xmlns="http://www.w3.org/2000/svg" p-id="2516" width="20" height="20"><path d="M396.5 661.9V110c0-6.1 7.5-9 11.6-4.6l366.6 394.3c2.4 2.6 2.4 6.6 0 9.1L408.1 903.2c-4.1 4.5-11.6 1.5-11.6-4.6V661.9z" fill="#67B47A" p-id="2517"></path></svg>
        run
      </div>
      <div class="button-item">
        <svg t="1736214728261" class="icon" viewBox="0 0 1024 1024" version="1.1" xmlns="http://www.w3.org/2000/svg" p-id="3688" width="20" height="20"><path d="M715.872 473.392c-15.472-112.736-103.616-196.864-207.36-196.864-103.68 0-191.872 84.064-207.344 196.864h414.72z m-463.072 0l0.192-1.712c16.72-138.08 125.376-243.152 255.52-243.152 130.752 0 239.728 105.984 255.744 244.864h45.488a16 16 0 0 1 16 16v16a16 16 0 0 1-16 16H208a16 16 0 0 1-16-16v-16a16 16 0 0 1 16-16h44.8z m486.656 117.92c13.888 3.472 12.352 13.472 10.912 18.208-34.8 113.696-131.088 192.912-242.08 192.912-110.144 0-205.856-78.016-241.312-190.432-1.536-4.896-4.64-14.432 10.832-18.848l16.528-4.32c15.52-3.968 17.392 5.52 18.864 10.096 29.728 92.56 107.376 155.504 195.088 155.504 88 0 165.824-63.36 195.36-156.304 1.536-4.864 3.616-14.88 19.936-10.832l15.872 4.032z m54.624 84.16h16a16 16 0 0 1 16 16v125.568a16 16 0 0 1-16 16h-125.552a16 16 0 0 1-16-16v-16a16 16 0 0 1 16-16h93.552v-93.568a16 16 0 0 1 16-16z m-570.08 0a16 16 0 0 1 16 16v93.568h93.568a16 16 0 0 1 16 16v16a16 16 0 0 1-16 16H208a16 16 0 0 1-16-16v-125.568a16 16 0 0 1 16-16h16z m570.08-325.92a16 16 0 0 1-16-16V240h-93.552a16 16 0 0 1-16-16v-16a16 16 0 0 1 16-16h125.552a16 16 0 0 1 16 16v125.568a16 16 0 0 1-16 16h-16z m-570.08 0h-16a16 16 0 0 1-16-16V208a16 16 0 0 1 16-16h125.568a16 16 0 0 1 16 16v16a16 16 0 0 1-16 16H240v93.568a16 16 0 0 1-16 16zM591.168 648.32c10.224 11.68 1.04 18.976-3.84 21.648-21.648 11.824-49.536 18.384-78.96 18.384-28.912 0-56.368-6.336-77.872-17.792-5.12-2.736-14.08-9.36-4.32-22.336l10.528-14.016c7.824-11.088 16.048-5.984 20.736-3.84 13.648 6.224 31.584 9.984 50.928 9.984 18.928 0 36.496-3.6 50-9.568 5.168-2.288 12.512-7.664 22.816 4.384l9.984 13.152z" fill="#000000" p-id="3689"></path></svg>
        test
      </div>
    </div>
    <div class="console-container">
      <!-- 控制台头部 -->
      <div class="console-header">Test Console Output</div>

      <!-- 控制台输出区域 -->
      <div class="console-output">
        <div v-for="(log, index) in logs" :key="index" :class="log.type">
          {{ log.message }}
        </div>
      </div>

      <!-- 控制台输入框 -->
      <div class="console-input-container">
        <input v-model="inputMessage" type="text" placeholder="Enter log message..." />
        <button @click="logMessage">Log</button>
      </div>
    </div>
    <div class="title">
      <div class="progress-container">
        <!-- 环形进度条 -->
        <div class="progress-item">
          <div class="title">功能覆盖率</div>
          <div class="desc">code coverage</div>
          <CircularProgress :progress="68"/>
        </div>
        <div class="progress-item">
          <div class="title">功能覆盖率</div>
          <div class="desc">code coverage</div>
          <CircularProgress :progress="68"/>
        </div>
        <div class="progress-item">
          <div class="title">功能覆盖率</div>
          <div class="desc">code coverage</div>
          <CircularProgress :progress="68"/>
        </div>
      </div>
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
    min-height: 600px;
    padding: 20px 20px 20px 20px;
    grid-template-columns: 35% 35% 30%;
    margin-top: -115px;

    .left, .middle, .right {
      position: relative;
      flex: 1;
      margin: 0 10px;
      display: flex;
      flex-direction: column;

      h2 {
        margin-bottom: 15px;
        font-size: 24px;
        font-weight: bold;
        color: #fff;
      }
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

      .right-header {
        position: absolute;
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
    margin: 0 20px;
    background: linear-gradient(#0e143f 20%, #fff); /* 渐变背景 */
    border-radius: 30px;
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

.progress-container {
  display: flex;
  justify-content: space-around;
  align-items: center;
}
.button-container{
  display: flex;
  background: #ffffff;
  justify-content: center;
  font-size: 18px;
  height: 32px;
  line-height: 32px;
  .button-item{
    display: flex;
    justify-content: center;
    align-items: center;
  }
}


//
.console-container {
  width: 80%;
  height: 400px;
  margin: 20px auto;
  background-color: #1e1e1e;
  color: #fff;
  border-radius: 8px;
  overflow: hidden;
  display: flex;
  flex-direction: column;
}

.console-header {
  padding: 10px;
  background-color: #333;
  text-align: center;
  font-weight: bold;
}

.console-output {
  flex-grow: 1;
  padding: 10px;
  overflow-y: auto;
  font-family: 'Courier New', monospace;
  font-size: 14px;
  background-color: #222;
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
  border: 1px solid #444;
  border-radius: 4px;
  color: #fff;
  background-color: #333;
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

</style>
