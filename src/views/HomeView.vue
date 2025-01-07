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

</style>
