export default {
  mounted(el) {
    const observer = new MutationObserver(() => {
      el.scrollTop = el.scrollHeight
    })

    observer.observe(el, { childList: true })
    el._autoScrollObserver = observer
  },
  unmounted(el) {
    if (el._autoScrollObserver) {
      el._autoScrollObserver.disconnect()
    }
  }
}
