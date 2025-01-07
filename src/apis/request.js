import axios from 'axios'
import { blobToFile } from '@/utils/blob-to-file.js'

/**
 * 创建FormData对象并添加数据
 *
 * 此函数通过遍历输入的对象数据，将其每个属性值添加到FormData对象中
 * 它主要用于在进行网络请求时，准备包含文件或其他二进制数据的数据包
 *
 * @param {Object} data - 包含需要添加到FormData的数据的对象
 * @returns {FormData} - 返回填充了数据的FormData对象
 */
const createFormData = data => {
  // 创建一个新的FormData对象
  const formData = new FormData()
  // 遍历输入对象的每个属性
  for (const key in data) {
    // 将当前属性的键值对添加到FormData对象中
    formData.append(key, data[key])
  }
  // 返回填充了数据的FormData对象
  return formData
}
/**
 * 处理Axios请求错误的函数
 *
 * 当Axios请求失败时，此函数用于分析错误原因并返回一个包含错误信息的对象
 * 它根据错误的不同情况返回不同的错误信息，以便于前端可以统一处理错误
 *
 * @param {Object} e - 错误对象，由Axios抛出
 * @returns {Object} - 返回一个包含错误码和错误信息的对象
 */
const handleAxiosError = e => {
  // 当e.response存在时，表示请求已发送到服务器，但服务器返回了非2xx的状态码
  if (e.response) {
    return {
      code: e.response.status,
      message: e.response.statusText || 'Request failed',
    }
  }
  // 当e.request存在时，表示请求已发出，但没有收到服务器响应
  // 通常这是因为网络问题或服务器宕机导致的
  if (e.request) {
    return {
      code: e.code || 'ECONNABORTED',
      message: e.message || 'Request timed out',
    }
  }
  // 当e.response和e.request都不存在时，表示请求在初始化过程中发生了错误
  // 这可能是由于配置错误或其他未知原因导致的
  return {
    code: e.code || 'UNKNOWN_ERROR',
    message: e.message || 'An unknown error occurred',
  }
}

/**
 * 异步请求函数，封装了axios请求，支持认证和多种数据格式
 *
 * @param {Object} params 请求参数对象
 * @param {string} params.url 请求URL，默认为空字符串
 * @param {string} params.method 请求方法，默认为'get'
 * @param {Object} params.data 请求数据，默认为空对象
 * @param {boolean} params.isAuth 是否需要认证，默认为true
 * @param {string} params.requestType 请求数据类型，默认为'string'
 * @param {string} params.responseType 响应数据类型，默认为'json'
 * @returns {Promise} 返回一个Promise对象， resolves to the response data
 */
export const request = async params => {
  // 解构请求参数，提供默认值
  const { url = '', method = 'get', data = {}, isAuth = true, requestType = 'string', responseType = 'json' } = params

  // 配置axios请求选项
  const axiosConfig = {
    headers: { 'Content-Type': 'application/json' },
    timeout: 10000,
    url: `${import.meta.env.VITE_REQUEST_BASE_URL}${url}`,
    method: method.toLowerCase(),
    responseType: responseType.toLowerCase(),
  }

  // 根据请求方法，处理请求数据
  if (['get'].includes(axiosConfig.method)) {
    axiosConfig.params = data
  } else {
    if (requestType === 'FormData') {
      axiosConfig.headers['Content-Type'] = 'multipart/form-data'
      axiosConfig.data = createFormData(data)
    } else {
      axiosConfig.data = data
    }
  }

  // 如果需要认证，添加认证令牌到请求头
  if (isAuth) {
    const access_token = localStorage.getItem('access_token')
    axiosConfig['headers']['Authorization'] = `bearer ${access_token}`
  }

  try {
    // 发起请求，并处理响应
    const result = await axios(axiosConfig)
    const data = result.data

    // 如果是Blob类型响应，处理文件名
    if (responseType === 'Blob') {
      const contentDisposition = result.headers['content-disposition']
      let filename = ''
      if (contentDisposition) {
        try {
          filename = decodeURIComponent(contentDisposition.split('=')[1])
        } catch (e) {
          console.error('Failed to decode filename:', e)
        }
      }
      return blobToFile(data, filename)
    }

    // 默认返回数据
    return data
  } catch (e) {
    console.log(e)
    return handleAxiosError(e)
  }
}
