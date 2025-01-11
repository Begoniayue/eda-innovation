<script setup>
import Vditor from 'vditor'
import {onMounted, ref} from 'vue'
const vditor = ref(null)

onMounted(() => {
  vditor.value = new Vditor('vditor', {
    // 规定编辑器总高度，如果不设置，高度将自适应，页面比较难看
    // 需要根据实际情况自己修改它
    height: 500,
    width: '100%',
    lang: 'zh_CN',
    toolbarConfig: {
      pin: true,
      hide:true
    },
    cache: {
      enable: false,
    },
    after: () => {
      // 编辑器启动后，直接插入一段`Hello`，正式使用视情况修改
      // vditor.setValue('hello, Vditor + Vue!')
    },
  })
})
</script>

<template>
  <!-- 编辑器的容器，注意id要和 new Vditor 绑定的值一致-->
  <div id="vditor">
  </div>
</template>

<style scoped>
</style>
