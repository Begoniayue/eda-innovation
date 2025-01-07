// 将blob对象下载为文件
/**
 * 将Blob对象转换为文件，并触发浏览器下载
 *
 * @param {Blob} blob 要转换的Blob对象
 * @param {string} fileName 文件名，包括扩展名
 */
export const blobToFile = (blob, fileName) => {
  // 创建一个隐藏的<a>元素，用于触发文件下载
  const link = document.createElement('a')
  link.download = fileName
  link.style.display = 'none'
  link.href = URL.createObjectURL(blob)
  // 将<a>元素添加到文档中，以便能够触发点击事件
  document.body.appendChild(link)
  // 触发<a>元素的点击事件，开始下载过程
  link.click()
  // 下载完成后，释放掉创建的ObjectURL
  URL.revokeObjectURL(link.href)
  // 从文档中移除<a>元素，清理现场
  document.body.removeChild(link)
}
