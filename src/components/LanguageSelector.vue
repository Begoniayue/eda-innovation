<script setup>
const selectedLanguage = defineModel()
</script>

<template>
  <div class="language-selector">
    <label for="language">选择编程语言: </label>
    <select id="language" v-model="selectedLanguage">
      <option value="javascript">JavaScript</option>
      <option value="python">Python</option>
      <option value="java">Java</option>
      <option value="typescript">TypeScript</option>
      <option value="cpp">C++</option>
    </select>
  </div>
</template>

<style scoped lang="less">
.language-selector {
  display: inline-flex;
  align-items: center;
  margin-left: 15px;
  font-size: 16px;
  color: #fff;
  margin-bottom: 15px;
  padding-right: 10px;

  label {
    margin-right: 10px;
  }

  select {
    padding: 5px 15px;
    border: none;
    background-color: #f0f0f5;
    color: #333;
    font-size: 16px;
    border-radius: 15px;
    box-shadow: 0 2px 5px rgba(0, 0, 0, 0.1);
    transition: background-color 0.3s ease, transform 0.3s ease;

    &:hover {
      background-color: #e0e0e5;
      //transform: scale(1.05);
    }

    &:focus {
      outline: none;
      background-color: #d0d0d5;
    }
  }
}
</style>
