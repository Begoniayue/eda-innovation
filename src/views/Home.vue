<script setup>
import { onMounted, ref, watch, nextTick } from 'vue'
import * as monaco from 'monaco-editor'
import LanguageSelector from '@/components/LanguageSelector.vue'
import CircularProgress from '@/components/CircularProgress.vue'

const ref_editor = ref(null)
const ref_answerEditorContainer = ref(null)
let answerEditor = null
let decorationsCollection = null
const answerLanguage = ref('python')

// 初始代码
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
  $('#summernote').summernote({
    tabsize: 2,
    toolbar: [
      ['style', ['style']],
      ['font', ['bold', 'underline', 'clear']],
      ['color', ['color']],
      ['para', ['ul', 'ol', 'paragraph']],
      ['table', ['table']],
      ['insert', ['link', 'picture', 'video']],
      ['view', ['fullscreen', 'codeview', 'help']]
    ]
  })
})
const setHighLightStyle = () => {
  const style = document.createElement('style')
  style.innerHTML = `
    .highlight-error-line {
        background-color: rgba(165, 42, 42, 0.5);
    }
`
  document.head.appendChild(style)
}
const appendCodeLine = () => {
  const model = answerEditor.getModel()
  const lastLine = model.getLineCount() // 获取最后一行的行号
  const newLineContent = `// Line ${lastLine + 1}: This is a new line!`
  // 将新的一行代码追加到编辑器内容
  model.applyEdits([
    {
      range: new monaco.Range(lastLine + 1, 1, lastLine + 1, 1),
      text: `\n${newLineContent}`,
      forceMoveMarkers: true
    }
  ])
  // 滚动到最后一行
  answerEditor.revealLine(lastLine + 1)
}
const replaceCodeLine = (lineNumber, newContent) => {
  const model = answerEditor.getModel() // 获取模型

  // 获取指定行的范围
  const range = new monaco.Range(lineNumber, 1, lineNumber, model.getLineMaxColumn(lineNumber))

  // 替换指定行的代码
  model.applyEdits([
    {
      range: range,
      text: newContent,
      forceMoveMarkers: true
    }
  ])
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
    range: new monaco.Range(113, 1, 113, 1),
    options: {
      isWholeLine: true,
      className: 'highlight-error-line'
    }
  }]
  decorationsCollection.set(decorationOptions)
}
const init = () => {
  setHighLightStyle()
}
const progress = ref(0)
const functionCoverage = ref(0)
const lineCoverage = ref(0)
const startIncrement = () => {
  // 设置一个定时器，每100毫秒增加一次进度
  const interval = setInterval(() => {
    // 累加进度条的值
    if (lineCoverage.value < 100) {
      lineCoverage.value = Math.min(lineCoverage.value + 2, 500)
    }
    if (functionCoverage.value < 100) {
      functionCoverage.value = Math.min(functionCoverage.value + 1, 600)
    }
    if (progress.value < 100) {
      progress.value = Math.min(progress.value + 10, 200)
    }

    // 如果所有进度条都已经到达 100，停止定时器
    if (lineCoverage.value === 100 && functionCoverage.value === 100 && progress.value === 100) {
      clearInterval(interval)
    }
  }, 100) // 每100毫秒增加一次进度
}
const logMessages = ref([])
const analyzeLogMessages = ref([])
const resultLogMessages = ref([])
const appendLog = ({ log, target }) => {
  switch (target) {
    case 'log':
      logMessages.value.push(log)
      break
    case 'result':
      resultLogMessages.value.push(log)
      break
    case 'analyze':
      analyzeLogMessages.value.push(log)
      break
  }
}
const reset = () => {
  // clear debug log
  logMessages.value = []
  // clear code input
  answerEditor.setModel(monaco.editor.createModel('', answerLanguage.value))
  // reset process pie
  progress.value = 0
  functionCoverage.value = 0
  lineCoverage.value = 0
  // clear result log
  resultLogMessages.value = []
  // reset analyzer log
  analyzeLogMessages.value = []
}
const testBuild = () => {
  // append log
  setInterval(() => {
    appendLog({
      log: {
        type: 'normal',
        message: '[    0] proven                   (non_vacuous)  -  ct_pmp_regs.assert_p_pmp0cfg_executeable_assignment'
      },
      target: 'log'
    })
  }, 1000)
  // process start
  startIncrement()
}
const assertCreate = () => {
  // append log
  setInterval(() => {
    appendLog({
      log: {
        type: 'normal',
        message: '[    3] proven                   (non_vacuous)  -  ct_pmp_regs.assert_p_pmp1cfg_executeable_assignment'
      },
      target: 'log'
    })
  }, 1000)
  // append code in code input
  appendCodeLine()
}
const emulation = () => {
  if (!repairButtonClicked.value) {
    // append log
    setInterval(() => {
      appendLog({
        log: {
          type: 'normal',
          message: '[   13] proven                   (non_vacuous)  -  ct_pmp_regs.assert_p_pmp4cfg_readable_assignment'
        },
        target: 'log'
      })
    }, 1000)
    // append result
    appendLog({
      log: {
        type: 'error',
        message: '[20] proven                   (non_vacuous)  -  ct_pmp_regs.assert_p_pmp6cfg_writable_assignment'
      },
      target: 'result'
    })
    return
  }
  // after fix button clear result log and append success info
  resultLogMessages.value = []
  appendLog({
    log: {
      type: 'success',
      message: 'Success!'
    },
    target: 'result'
  })
}
const analyze = () => {
  // append log
  setInterval(() => {
    appendLog({
      log: {
        type: 'normal',
        message: '[   37] proven                   (non_vacuous)  -  ct_pmp_regs.assert_p_pmp_updt_pmpaddr5_blocking_assignment'
      },
      target: 'log'
    })
  }, 1000)
  // append analyzer log
  setInterval(() => {
    appendLog({
      log: {
        type: 'normal',
        message: 'The default state of pmp5cfg_readable is incorrectly set to 1 during reset, which should be 0. It affects the value of pmpcfg0_value being read.'
      },
      target: 'analyze'
    })
  }, 1000)
  // error code highlight
  setHighLight()
}
const repairButtonClicked = ref(false)
const repairCode = () => {
  repairButtonClicked.value = true
  // append log
  setInterval(() => {
    appendLog({
      log: {
        type: 'normal',
        message: '55555555'
      },
      target: 'log'
    })
  }, 1000)
  // fix error line
  replaceCodeLine(5, '// asdfasdfasdfasdf')
  clearHighLight()
}
const mainContent = ref(null);
const isVisible = ref(true);

const domScroll = () => {
  if (mainContent.value) {
    mainContent.value.scrollIntoView({ behavior: 'smooth' });
    setTimeout(() => {
      isVisible.value = false;
    }, 1000); // 1秒后隐藏元素，可以根据需要调整时间
  }
};

watch(answerLanguage, (value) => {
  answerEditor.setModel(monaco.editor.createModel('', value))
})
init()
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
        <img src="https://www.nctieda.com/images/logo1.png" alt="" width="400" />
      </div>
    </div>
    <div class="app-content" v-if="isVisible">
      <div class="banner-content-bg">
        <div class="title">
          <div>欢迎来到iDebug,有什么可以帮忙的？</div>
          <div class="try-button" @click="domScroll">立即体验</div>
        </div>
        <video
          autoplay="" loop="" muted=""
          src="https://res-video.hc-cdn.com/cloudbu-site/china/zh-cn/advertisement/Fixed/banner/1725874846387175930.mp4"
          style="opacity: 1;"
        />
        <div class="events-container"></div>
      </div>
    </div>
    <div class="main-content" ref="mainContent">
      <div class="item item-1">
        <div class="header">
          <h2>Spec Input</h2>
          <div  @click="reset" style="margin-top: 5px;margin-left: 5px">
            <svg t="1736471478981" class="icon" viewBox="0 0 1024 1024" version="1.1" xmlns="http://www.w3.org/2000/svg" p-id="1676" width="20" height="20"><path d="M861.866667 349.866667l-102.4 102.4C733.866667 341.333333 631.466667 256 512 256c-140.8 0-256 115.2-256 256s115.2 256 256 256c136.533333 0 251.733333-106.666667 256-243.2l76.8-76.8c4.266667 21.333333 8.533333 42.666667 8.533333 68.266667 0 187.733333-153.6 341.333333-341.333333 341.333333s-341.333333-153.6-341.333333-341.333333 153.6-341.333333 341.333333-341.333334c110.933333 0 213.333333 55.466667 273.066667 136.533334l8.533333-12.8h119.466667l-51.2 51.2z" fill="#1677ff" p-id="1677"></path></svg>
          </div>
        </div>
        <div style="height: calc(100% - 44px)">
          <div id="summernote" ref="ref_editor" style="height: 100%"></div>
        </div>
      </div>
      <div class="item item-2">
        <div class="header">
          <h2>Log</h2>
          <div @click="reset"  style="margin-top: 5px;margin-left: 5px">
            <svg t="1736471478981" class="icon" viewBox="0 0 1024 1024" version="1.1" xmlns="http://www.w3.org/2000/svg" p-id="1676" width="20" height="20"><path d="M861.866667 349.866667l-102.4 102.4C733.866667 341.333333 631.466667 256 512 256c-140.8 0-256 115.2-256 256s115.2 256 256 256c136.533333 0 251.733333-106.666667 256-243.2l76.8-76.8c4.266667 21.333333 8.533333 42.666667 8.533333 68.266667 0 187.733333-153.6 341.333333-341.333333 341.333333s-341.333333-153.6-341.333333-341.333333 153.6-341.333333 341.333333-341.333334c110.933333 0 213.333333 55.466667 273.066667 136.533334l8.533333-12.8h119.466667l-51.2 51.2z" fill="#1677ff" p-id="1677"></path></svg>
          </div>
        </div>
        <div class="console-output-section">
          <div class="console-output" v-auto-scroll>
            <template v-if="logMessages.length>0">
              <div v-for="(log, index) in logMessages" :key="index" :class="log.type">
                {{ log.message }}
              </div>
            </template>
            <div v-else class="normal">...</div>
          </div>
        </div>
      </div>
      <div class="item item-3">
        <div class="header">
          <h2>Design Code Input</h2>
          &nbsp;&nbsp;
          <LanguageSelector v-model="answerLanguage" />
        </div>
        <div ref="ref_answerEditorContainer" class="monaco-editor"></div>
      </div>
      <div class="item item-4">
        <div style="background: #ffffff">
          <div class="button-list">
            <div class="button" @click="testBuild">测试生成</div>
            <div class="button" @click="assertCreate">断言生成</div>
            <div class="button" @click="emulation">仿真</div>
            <div class="button" @click="analyze">分析</div>
            <div class="button" @click="repairCode">修复</div>
          </div>
          <div class="coverage">
            <div class="progress-item">
              <div class="title">功能覆盖率</div>
              <div class="desc">code coverage</div>
              <CircularProgress :progress="progress" />
            </div>
            <div class="progress-item">
              <div class="title">行覆盖率</div>
              <div class="desc"> line coverage</div>
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
      <div class="item item-5">
        <div class="header">
          <h2>结果Result</h2>
        </div>
        <div class="console-output-section">
          <div class="console-output"  v-auto-scroll>
            <template v-if="resultLogMessages.length>0">
              <div v-for="(log, index) in resultLogMessages" :key="index" :class="log.type">
                {{ log.message }}
              </div>
            </template>
            <div v-else class="normal">...</div>
          </div>
        </div>
      </div>
      <div class="item item-6">
        <div class="header">
          <h2>分析Analyze</h2>
        </div>
        <div class="console-output-section">
          <div class="console-output" v-auto-scroll>
            <template v-if="analyzeLogMessages.length>0">
              <div v-for="(log, index) in analyzeLogMessages" :key="index" :class="log.type">
                {{ log.message }}
              </div>
            </template>
            <div v-else class="normal">...</div>
          </div>
        </div>
      </div>
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
    grid-template-rows:560px 315px;
    grid-gap: 10px;
    padding-bottom: 0px;
    margin-top: -28px;
    margin-bottom: 30px;

    .item {
      position: relative;
      flex: 1;
      display: flex;
      flex-direction: column;
      overflow-y: auto;
      border-radius: 15px;
      background: #FFFFFF;

      .header {
        display: flex;
        justify-content: center;
        align-items: center;
        height: 44px;

        h2 {
          font-size: 24px;
          font-weight: bold;
          color: #333333;
        }
      }


      .button-list {
        display: flex;
        justify-content: space-around;
        padding-top: 20px;

        .button {
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

      .coverage {
        display: flex;
        justify-content: space-between;
        margin-top: 22px;
      }

      .console-output-section {
        width: 100%;
        padding: 10px;
        background-color: #fff;
        color: #333333;
        display: flex;
        flex-direction: column;
        overflow-y: auto;
        height: calc(100% - 44px);
        text-align: left;
        border-radius: 12px;

        .console-output {
          flex-grow: 1;
          padding: 10px;
          font-family: 'Courier New', monospace;
          font-size: 14px;
          background-color: #fff;
          overflow-y: auto;
        }
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


.normal {
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

.success {
  color: #04f808;
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


.progress-item {
  color: #333333;

  .desc {
    text-align: center;
    margin-bottom: 20px;
  }
}

.banner-content-bg {
  position: relative;
  height: 100%;

  .title {
    color: #333333;
    font-size: 30px;
    position: absolute;
    z-index: 1;
    top: 32%;
    left: 1%;
    opacity: 0; /* 动画前初始状态 */
    transform: translateY(30px); /* 初始位置向下 */
    animation: slideUpFade 1s ease-out 0.5s forwards; /* 延迟0.5s出现 */
    transition: all 0.3s ease-in-out;

    .try-button {
      cursor: pointer;
      width: 200px;
      border: 1px solid #595959;
      border-radius: 30px;
      box-sizing: border-box;
      font-size: 18px;
      height: 60px;
      line-height: 60px;
      padding: 0 32px;
      text-align: center;
      margin-top: 30px;
      opacity: 0; /* 动画前初始状态 */
      transform: translateY(30px); /* 初始位置向下 */
      animation: slideUpFade 1s ease-out 0.5s forwards; /* 延迟0.5s出现 */
      transition: all 0.3s ease-in-out;
    }
  }

  video {
    height: 100%;
    width: 100%;
  }
}

.events-container {
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
