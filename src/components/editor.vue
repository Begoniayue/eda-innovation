<script setup>
import tinymce from 'tinymce/tinymce'
import Editor from '@tinymce/tinymce-vue'
import 'tinymce/themes/silver' //编辑器主题，不引入则报错
import 'tinymce/icons/default' //引入编辑器图标icon，不引入则不显示对应图标
// import 'tinymce/themes/silver/theme'
// import 'tinymce/icons/default/index.js'
// import '../plugins/rspace'
import {onMounted, reactive, watch, ref} from "vue";

defineOptions({
  name: 'TinyEditor'
})

const inputValue = defineModel({ type: String });

const { disabled, height, resize, inline, placeholder, plugins, toolbar, uploadParams,isDark } = defineProps({
  disabled: {
    type: Boolean,
    default: false
  },
  height: {
    type: [ Number, String ],
    default: 300
  },
  resize: {
    type: Boolean,
    default: false
  },
  inline: {
    type: Boolean,
    default: false
  },
  placeholder: {
    type: String,
    default: ''
  },
  plugins: {
    type: [String, Array],
    default: 'advlist anchor autolink autosave code codesample charmap directionality emoticons fullscreen ' +
             'image insertdatetime link lists media nonbreaking pagebreak preview save searchreplace ' +
             'table visualblocks visualchars wordcount'
  },
  toolbar: {
    type: [String, Array],
    default: 'fullscreen preview | forecolor backcolor bold italic underline image strikethrough link anchor | \
              alignleft aligncenter alignright alignjustify | outdent indent lineheight | \
              bullist numlist | blockquote subscript superscript removeformat | cut copy paste pastetext | \
              table rspace  media charmap emoticons hr pagebreak insertdatetime | \
              searchreplace codesample code undo redo restoredraft print '
  },
  uploadParams: {
    type: Object,
    default: null
  },
  isDark:{
    type: Boolean,
    default: false
  }
})

const emit = defineEmits([ 'input', 'onClick' ])
const iTinyRef = ref(null);
const editorConfig = reactive({
  base_url: '/tinymce/',
  suffix: '.min',
  language_url: '/tinymce/langs/zh_CN.js',
  language: 'zh_CN',
  // skin_url: '/tinymce/skins/ui/oxide',
  // icons: 'ax-color',
  // icons_url: '/tinymce/icons/ax-color/icons.js',
  content_css:isDark ? 'dark' : null,
  skin:isDark ? 'oxide-dark' :null,
  resize: resize,
  height: height,
  plugins: plugins,
  toolbar: toolbar,
  placeholder: placeholder,
  inline: inline,
  branding: false,
  menubar: false,     // 顶部菜单
  toolbar_mode: 'sliding',   // 'wrap',
  default_link_target: '_blank',
  link_title: false,
  convert_urls: false,
  fontsize_formats: '12px 14px 16px 18px 24px 36px 48px 56px 72px',
  font_formats: '微软雅黑=Microsoft YaHei,Helvetica Neue,PingFang SC,sans-serif;苹果苹方=PingFang SC,Microsoft YaHei,sans-serif;宋体=simsun,serif;仿宋体=FangSong,serif;黑体=SimHei,sans-serif;Arial=arial,helvetica,sans-serif;Arial Black=arial black,avant garde;Book Antiqua=book antiqua,palatino;Comic Sans MS=comic sans ms,sans-serif;Courier New=courier new,courier;Georgia=georgia,palatino;Helvetica=helvetica;Impact=impact,chicago;Symbol=symbol;Tahoma=tahoma,arial,helvetica,sans-serif;Terminal=terminal,monaco;Times New Roman=times new roman,times;Verdana=verdana,geneva;Webdings=webdings;Wingdings=wingdings,zapf dingbats;知乎配置=BlinkMacSystemFont, Helvetica Neue, PingFang SC, Microsoft YaHei, Source Han Sans SC, Noto Sans CJK SC, WenQuanYi Micro Hei, sans-serif;小米配置=Helvetica Neue,Helvetica,Arial,Microsoft Yahei,Hiragino Sans GB,Heiti SC,WenQuanYi Micro Hei,sans-serif',
  paste_data_images: false,
});

onMounted(() => {

});

const onClick = (e) => {
  emit('onClick', e, tinymce)
}

const onInit = (e, editor) => {
  // editor.$editorVue = this;
}

const clear = () => {
  inputValue.value = ''
}

watch(inputValue, (newValue) => {
  emit('input', newValue)
})

watch(() => height, (val) => {
  if(val && val > 0) {
    editorConfig.height = val;
    // iTinyRef.value?.rerender({ height: val });
  }
})

watch(() => resize, (val) => {
  editorConfig.resize = val;
  // iTinyRef.value?.rerender({ resize: resize });
})
watch(() => disabled, (val) => {
  editorConfig.disabled = val;
})
watch(() => inline, (val) => {
  editorConfig.inline = val;
})
watch(() => placeholder, (val) => {
  editorConfig.placeholder = val;
})
watch(() => plugins, (val) => {
  editorConfig.plugins = val;
})
watch(() => toolbar, (val) => {
  editorConfig.toolbar = val;
})

watch(editorConfig, () => {
  iTinyRef.value?.rerender(editorConfig);
})

</script>
<template>
  <div class="tinymce-editor">
    <editor
      v-model="inputValue"
      :init="editorConfig"
      :disabled="disabled"
      ref="iTinyRef"
      @init="onInit"
      @click="onClick">
    </editor>
  </div>
</template>
