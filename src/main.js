import './assets/base.css'
import { createApp } from 'vue'
import { createPinia } from 'pinia'
import App from './App.vue'
import router from './router'
import 'highlight.js/styles/a11y-dark.min.css'
import 'highlight.js/lib/common'
import hljsVuePlugin from '@highlightjs/vue-plugin'

const app = createApp(App)

app.use(createPinia())
app.use(router)
app.use(hljsVuePlugin)
app.mount('#app')
