import autoScroll from './auto-scroll'

const directives = {
  'auto-scroll': autoScroll
}

export default {
  install(Vue) {
    Object.keys(directives).forEach((item) => {
      Vue.directive(item, directives[item])
    })
  }
}
