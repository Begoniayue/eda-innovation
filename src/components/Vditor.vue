<script setup>

import Vditor from "vditor";
import { onMounted, ref, watch, toRaw, onUnmounted } from "vue";

const emit = defineEmits([
  "update:modelValue",
  "after",
  "focus",
  "blur",
  "esc",
  "ctrlEnter",
  "select"
]);

const props = defineProps({
  options: {
    type: Object,
    default() {
      return {};
    }
  },
  modelValue: {
    type: String,
    default: ""
  }
});

const editor = ref(null);
const markdownRef = ref(null);

onMounted(() => {
  editor.value = new Vditor(markdownRef.value,{
    ...props.options,
    value: props.modelValue,
    cache: {
      enable: false
    },

    fullscreen: {
      index: 10000
    },
    after() {
      emit("after", toRaw(editor.value));
    },
    input(value) {
      emit("update:modelValue", value);
    },
    focus(value) {
      emit("focus", value);
    },
    blur(value) {
      emit("blur", value);
    },
    esc(value) {
      emit("esc", value);
    },
    ctrlEnter(value) {
      emit("ctrlEnter", value);
    },
    select(value) {
      emit("select", value);
    }
  });
});

watch(
  () => props.modelValue,
  newVal => {
    if (newVal !== editor.value?.getValue()) {
      editor.value?.setValue(newVal);
    }
  }
);

onUnmounted(() => {
  const editorInstance = editor.value;
  if (!editorInstance) return;
  try {
    editorInstance?.destroy?.();
  } catch (error) {
    console.log(error);
  }
});
</script>

<template>
  <div ref="markdownRef" />
</template>
