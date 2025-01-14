<script setup>
import {onMounted, ref, watch} from 'vue'
import * as monaco from 'monaco-editor'
import LanguageSelector from '@/components/LanguageSelector.vue'
import Vditor from '@/components/Vditor.vue'
import ModuleCard from '@/components/ModuleCard.vue'
import {testLog, assertLog, emulationLog1, emulationLog2, analyzeLog} from '@/datas/logs'
import {createWebSocketClient} from '@/utils/websocket'
import TechProgress from '@/components/TechProgress.vue'
import {assertCode, error, specPost} from "@/apis/data";

const ref_answerEditorContainer = ref(null)
let answerEditor = null
let decorationsCollection = null
const answerLanguage = ref('verilog')

onMounted(() => {
  answerEditor = monaco.editor.create(ref_answerEditorContainer?.value, {
    language: answerLanguage.value,
    theme: 'vs-light',
    automaticLayout: true,
    lineNumbers: 'on',
    minimap: {enabled: false},
    overviewRulerLanes: 0, // 移除右侧 Overview Ruler 的标记
    overviewRulerBorder: false, // 移除 Overview Ruler 的边框
  })
  decorationsCollection = answerEditor.createDecorationsCollection()
})
const setHighLightStyle = () => {
  const style = document.createElement('style')
  style.innerHTML = `
    .highlight-error-line {
        background-color: rgba(165, 42, 42, 0.5);
    }
    .highlight-success-line {
        background-color: rgba(0, 255, 0, 0.5);
    }
`
  document.head.appendChild(style)
}
const appendCode = ref(null)
const appendCodeLine = async () => {
  const model = answerEditor.getModel()
  const lastLine = model.getLineCount() // 获取最后一行的行号
  // 将新的一行代码追加到编辑器内容
  model.applyEdits([
    {
      range: new monaco.Range(lastLine + 1, 1, lastLine + 1, 1),
      text: `\n${appendCode.value}`,
      forceMoveMarkers: true
    }
  ])
  // 滚动到最后一行
  answerEditor.revealLine(lastLine + 1)
  assertFlag.value = true
  emulationFlag.value = false
}
const deleteCodeLine = (lineNumber) => {
  const model = answerEditor.getModel() // 获取模型

  // 获取该行的范围
  const range = new monaco.Range(lineNumber, 1, lineNumber, model.getLineMaxColumn(lineNumber))

  // 使用 applyEdits 删除指定行的内容
  model.applyEdits([
    {
      range: range,
      text: '', // 删除内容，空字符串
      forceMoveMarkers: true
    }
  ])
}
const replaceCodeLine = (lineNumber, newContent) => {

}
const clearHighLight = () => {
  if (!decorationsCollection) {
    return
  }
  decorationsCollection.clear()
}
const setHighLight = async (options) => {
  let errorCode
  if (!decorationsCollection) {
    return
  }
  try {
    const response = await error()
    if (response.code === 200) {
      errorCode = [[114, 1, 114, 1],[145,1,167,1]]
      // errorCode = response.data?.error_code
    }
  } catch (error) {
  }
  const decorations = errorCode.map(([startLineNumber, startColumn, endLineNumber, endColumn]) => ({
    range: new monaco.Range(startLineNumber, startColumn, endLineNumber, endColumn),
    options: {
      isWholeLine: true,
      className: 'highlight-error-line'
    }
  }));
  decorationsCollection.set(decorations);
  analyzeFlag.value = true
  repairFlag.value = false
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
      lineCoverage.value = Math.min(lineCoverage.value + 10, 100)
    }

    // 判断 assertFlag，只有 assertFlag 为 false 时，functionCoverage 不能达到 100
    if (!assertFlag.value && functionCoverage.value < 100) {
      functionCoverage.value = Math.min(functionCoverage.value + 5, 100)  // 限制 functionCoverage 在 99 以内
    } else if (assertFlag.value && functionCoverage.value < 100) {
      functionCoverage.value = Math.min(functionCoverage.value + 10, 99)  // 当 assertFlag 为 true 时，可以增加到 100
    }

    if (progress.value < 100) {
      progress.value = Math.min(progress.value + 20, 100)
    }

    // 如果所有进度条都已经到达 100，停止定时器
    if (lineCoverage.value === 100 && progress.value === 100) {
      clearInterval(interval)
    }

    // 如果 assertFlag 为 true，且 functionCoverage 达到 100，清除定时器
    if (assertFlag.value && functionCoverage.value === 100) {
      clearInterval(interval)
    }
  }, 1000)
}

const logMessages = ref([])
const analyzeAndResultLogMessages = ref([])
const appendLog = (info, type) => {
  console.log(info, type,'234')
  switch (type) {
    case 'log':
      logMessages.value.push(info.data)
      break
    case 'result':
      analyzeAndResultLogMessages.value.push(info.data)
      break
    case 'analyze':
      analyzeAndResultLogMessages.value.push(info.data)
      break
    case 'stats':
      analyzeAndResultLogMessages.value.push(info.data)
      break
  }
}
const reset = () => {
  // clear debug log
  logMessages.value = []
  // clear code input
  answerEditor.setModel(monaco.editor.createModel('', answerLanguage.value))
  clearHighLight()
  // reset process pie
  progress.value = 0
  functionCoverage.value = 0
  lineCoverage.value = 0
  // clear result and analyzer log
  analyzeAndResultLogMessages.value = []
  testFlag.value = false
  assertFlag.value = true
  repairFlag.value = true
  analyzeFlag.value = true
  emulationFlag.value = true
}
const testBuild = () => {
  testBuildDate()
  startIncrement()
}
const assertCreate = async () => {
  try {
    const response = await assertCode();
    if (response.code === 200) {
      appendCode.value = response.data.assert;
    }
  } catch (error) {
    return;
  }
}
const emulation = () => {
  if (!repairButtonClicked.value) {
    appendLog({
      info: {
        type: 'error',
        message: emulationLog1
      },
      target: 'result'
    })
    setTimeout(() => {
      appendLog({
        info: {
          type: 'error',
          message: emulationLog2
        },
        target: 'result'
      })
    }, 2000)

    return
  }
  // after fix button clear result log and append success info
  analyzeAndResultLogMessages.value = []
  appendLog({
    info: {
      type: 'success',
      message: 'Success!'
    },
    target: 'result'
  })
}
const analyze = () => {
  // append analyzer log
  appendLog({
    info: {
      type: 'normal',
      message: analyzeLog
    },
    target: 'analyze'
  })

}
const repairButtonClicked = ref(false)
const repairCode = () => {
  repairButtonClicked.value = true;

  const replacements = [
    {lineNumber: 113, text: "pmp5cfg_readable <= 11'b0;"},
    {lineNumber: 125, text: "pmp5cfg_readable <= 11'b0;"},
  ];

  const model = answerEditor.getModel(); // 获取模型

  const edits = replacements.map(({lineNumber, text}) => {
    const range = new monaco.Range(lineNumber, 1, lineNumber, model.getLineMaxColumn(lineNumber));
    return {
      range,
      text,
      forceMoveMarkers: true
    };
  });

  const decorations = replacements.map(({lineNumber, text}) => {
    const range = new monaco.Range(lineNumber, 1, lineNumber, model.getLineMaxColumn(lineNumber));
    return {
      range,
      options: {
        isWholeLine: true,
        className: 'highlight-success-line'
      }
    };
  });

  model.applyEdits(edits);
  decorationsCollection.set(decorations);
}
const mainContent = ref(null)
const isVisible = ref(true)

const domScroll = () => {
  if (mainContent.value) {
    mainContent.value.scrollIntoView({behavior: 'smooth'})
    setTimeout(() => {
      isVisible.value = false
    }, 1000) // 1秒后隐藏元素，可以根据需要调整时间
  }
}

watch(answerLanguage, (value) => {
  answerEditor.setModel(monaco.editor.createModel('', value))
})
init()
const wsClient = createWebSocketClient('ws://satan2333.icu:18765', [], {
  onOpen: () => console.log('Connection established.'),
  onMessage: (data) => {
    console.log(data, 'data')

    try {
      const json = JSON.parse(data);
      console.log(json, 'parsed data', json.type);
      if (json.type) {
        appendLog(json, json.type);
        if (json.isEnd) {
          todoEnd(json.stage)
        }
      }
    } catch (e) {
      console.log('Error parsing JSON:', e);
      console.log('Original data:', data); // 打印原始数据以便调试
    }
  },
  onError: (error) => console.error('Error occurred:', error),
  onClose: (event) => console.log('Connection closed.', event)
})

// Sending a message
wsClient.send(JSON.stringify({type: 'greeting', content: 'Hello Server!'}))
const specHtml = ref(null)

const testFlag = ref(false)
const assertFlag = ref(true)
const emulationFlag = ref(true)
const analyzeFlag = ref(true)
const repairFlag = ref(true)
// 测试生成
const testBuildDate = async () => {
  const params = {
    spec: specHtml.value,
    code: answerEditor.getValue()
  }
  try {
    const response = await specPost(params)
    if (response.code === 200) {

    }
  } catch (error) {
    console.error('请求失败:', error)
  }
}
const todoEnd = (stage) => {
  switch (stage) {
    case 'test':
      assertFlag.value = false
      testFlag.value = true
      break
    case 'assert':
      deleteCodeLine(answerEditor.getModel().getLineCount())
      appendCodeLine()
      break
    case 'emulation':
      emulationFlag.value = true
      analyzeFlag.value = false
      break
    case 'analyze':
      setHighLight()
      break
    case 'repairCode':
      repairFlag.value = true;
      emulationFlag.value = false;
      break
  }

}

</script>

<template>
  <div class="app">
    <div class="app-header">
      <div class="logo">
        <img src="https://www.nctieda.com/images/logo1.png" alt="" style="width: 400px"/>
      </div>
      <div class="title">
        <img class="logo" src="../assets/images/debug-log.png" alt="" width="50"/>
        欢迎来到iDebug，有什么可以帮忙的？
      </div>
    </div>
    <div class="app-banner" v-if="isVisible">
      <img src="../assets/images/welcome.png" alt="" width="609" style="margin-top: 106px">
      <div class="try-button" @click="domScroll">
        <div class="try-button-text">
          立即体验
        </div>
      </div>
    </div>
    <div class="main-content" ref="mainContent">
      <div class="item">
        <ModuleCard height="552px">
          <template #title>
            Spec Input
            <img
              src="../assets/images/refresh-icon.png" style="width: 16px;height: 16px;margin-left: 16px" alt=""
              @click="reset">
          </template>
          <template #default>
            <Vditor
              v-model="specHtml"
              :height="520"
              :value="specHtml"
              :options="{
                height: 520,
                cache: {
                  enable: false
                }
              }"
            />
          </template>
        </ModuleCard>
        <div style="margin-bottom: 20px"></div>
        <ModuleCard height="308px">
          <template #title>
            Log
          </template>
          <template #default>
            <div class="console-output-section">
              <div class="console-output" v-auto-scroll>
                <template v-if="logMessages.length>0">
                  <div v-for="(log, index) in logMessages" :key="index" :class="log.status">
                    {{ log.message }}
                  </div>
                </template>
                <div v-else class="normal">...</div>
              </div>
            </div>
          </template>
        </ModuleCard>
      </div>
      <div class="item">
        <ModuleCard height="880px">
          <template #title>
            Design Code Input
            &nbsp;&nbsp;
            <img
              src="../assets/images/refresh-icon.png" style="width: 16px;height: 16px;margin-left: 16px" alt=""
              @click="reset"
            >&nbsp;&nbsp;
            <LanguageSelector v-model="answerLanguage"/>
          </template>
          <template #default>
            <div ref="ref_answerEditorContainer" class="monaco-editor"></div>
          </template>
        </ModuleCard>
      </div>
      <div class="item">
        <ModuleCard height="356px">
          <template #title>
            <div class="button-list">
              <button class="button" @click="testBuild" :disabled="testFlag">测试生成</button>
              <button class="button" @click="assertCreate" :disabled="assertFlag">断言生成</button>
              <button class="button" @click="emulation" :disabled="emulationFlag">仿真</button>
              <button class="button" @click="analyze" :disabled="analyzeFlag">分析</button>
              <button class="button" @click="repairCode" :disabled="repairFlag">修复</button>
            </div>
          </template>
          <template #default>
            <div class="coverage">
              <div class="progress-item">
                <div class="title">行覆盖率</div>
                <div class="desc"> line coverage</div>
                <TechProgress :progress="progress"/>
              </div>
              <div class="progress-item">
                <div class="title">翻转覆盖率</div>
                <div class="desc">toggle coverage</div>
                <TechProgress :progress="lineCoverage"/>
              </div>
              <div class="progress-item">
                <div class="title">功能覆盖率</div>
                <div class="desc">function coverage</div>
                <TechProgress :progress="functionCoverage"/>
              </div>
            </div>
          </template>
        </ModuleCard>
        <div style="margin-bottom: 20px"></div>
        <ModuleCard height="504px">
          <template #title>
            分析&结果 Analyze&Result
          </template>
          <template #default>
            <div class="console-output-section">
              <div class="console-output" v-auto-scroll>
                <template v-if="analyzeAndResultLogMessages.length>0">
                  <div v-for="(log, index) in analyzeAndResultLogMessages" :key="index" :class="log.status">
                    {{ log.message }}
                  </div>
                </template>
                <div v-else class="normal">...</div>
              </div>
            </div>
          </template>
        </ModuleCard>
      </div>
    </div>
  </div>

</template>
<style scoped lang="less">
.app {
  .app-header {
    display: flex;
    align-items: center;
    width: 100%;
    height: 100px;
    background: url("@/assets/images/page-header-bg.png") no-repeat;
    background-size: 100% 100px;
    box-shadow: 0 2px 10px rgba(0, 0, 0, 0.1); /* 阴影效果 */
    position: relative;

    .logo {
      margin-left: 80px;
      font-size: 24px;
      font-weight: bold;
      color: #333333;
    }

    .title {
      font-weight: 500;
      font-size: 18px;
      color: #2D80FF;
      line-height: 27px;
      text-align: left;
      font-style: normal;
      position: absolute;
      right: 80px;
      display: flex;
      align-items: center;

      .logo {
        margin-right: 33px;
      }
    }
  }

  .app-banner {
    display: flex;
    align-items: center;
    flex-direction: column;
    height: 470px;
    width: 100%;
    background: url("@/assets/images/banner.png") no-repeat;
    background-size: cover;

    .try-button {
      cursor: pointer;
      width: 240px;
      height: 63px;
      background: rgba(0, 0, 0, 0.4);
      box-shadow: 0px 2px 4px 0px rgba(0, 0, 0, 0.5);
      border-radius: 39px;
      backdrop-filter: blur(4px);
      display: flex;
      align-items: center;
      justify-content: center;
      font-weight: 500;
      font-size: 22px;

      .try-button-text {
        background: linear-gradient(34.9789664967228deg, #54FFF5 0%, #5488FF 100%);
        -webkit-background-clip: text;
        -webkit-text-fill-color: transparent;
      }
    }
  }

  .main-content {
    display: grid;
    padding: 30px 40px 38px 40px;
    grid-template-columns: 450px auto 450px;
    grid-gap: 20px;

    .item {
      position: relative;

      .button-list {
        width: 100%;
        display: flex;
        justify-content: space-around;

        .button {
          width: 80px;
          height: 33px;
          background: #F3F3F3;
          border-radius: 8px;
          font-weight: 500;
          font-size: 14px;
          color: #222222;
          display: flex;
          align-items: center;
          justify-content: center;
          cursor: pointer;
          border: none;

          &:disabled {
            cursor: not-allowed;
            opacity: .6;
          }
        }

        .button:hover {
          color: #1990FB;
          background: #E5F1FF;
          border-radius: 8px;
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
        justify-content: space-around;
        margin-top: 47px;
        position: relative;


        .progress-item {
          position: relative;
          color: #333333;
          display: flex;
          align-items: center;
          justify-content: center;
          flex-direction: column;

          .desc {
            text-align: center;
            margin-bottom: 20px;
          }
        }
      }

      .console-output-section {
        width: 100%;
        padding: 10px;
        background-color: #fff;
        color: #333333;
        display: flex;
        flex-direction: column;
        overflow-y: auto;
        height: 100%;
        text-align: left;
        border-radius: 12px;

        .console-output {
          flex-grow: 1;
          padding: 10px;
          font-family: 'Courier New', monospace;
          font-size: 12px;
          background-color: #fff;
          overflow-y: auto;
        }
      }

      .monaco-editor {
        border-radius: 15px;
        overflow: hidden;
        width: 100%;
        height: 100%;
        border: none;
      }
    }


  }

}


.normal {
  color: #888;
}

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

</style>
