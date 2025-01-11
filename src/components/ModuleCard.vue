<script setup>
const props = defineProps({
  height: {
    type: String,
    default: ''
  }
})

</script>

<template>
  <div class="module-card" :style="{height: props.height}">
    <div class="header">
      <div class="divider" />
      <div class="title">
        <slot name="title" />
      </div>
    </div>
    <div class="module-content">
      <slot name="default"/>
    </div>
  </div>
</template>

<style lang="less">
.module-card {
  position: relative;
  background: rgba(255, 255, 255, 0.96);
  box-shadow: 0px 2px 10px 0px rgba(95, 101, 135, 0.2);
  border-radius: 16px;
  border-image: linear-gradient(180deg, rgba(255, 255, 255, 1), rgba(255, 255, 255, 0)) 1 1;
  backdrop-filter: blur(0px);

  .header {
    width: 100%;
    height: 76px;
    border-bottom: 2px solid #F6F6F6;
    display: flex;
    align-items: center;

    .divider {
      width: 6px;
      height: 33px;
      background: linear-gradient(180deg, #36C1FE 0%, #198EFC 100%);
      border-radius: 0px 3px 3px 0px;
    }

    .title {
      margin-left: 24px;
      height: 100%;
      width: 100%;
      font-weight: 500;
      font-size: 18px;
      color: #222222;
      line-height: 27px;
      display: flex;
      align-items: center;
    }
  }

  .module-content {
    height: calc(100% - 76px);
    overflow-y: auto;
  }
}
</style>
