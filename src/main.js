import './assets/base.css'
import { createApp } from 'vue'
import { createPinia } from 'pinia'
import App from './App.vue'
import router from './router'
import Directives from './directives'
import "vditor/src/assets/less/index.less"

const app = createApp(App)

app.use(Directives)
app.use(createPinia())
app.use(router)
app.mount('#app')
