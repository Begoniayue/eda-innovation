import { request } from '@/apis/request'

/**
 * 示例调用方法
 * @param {Object} data - 传递的参数
 */
export const specPost = async (data) => {
  try {
    // 准备请求参数
    const params = {
      url: '/api/spec',
      method: 'POST',
      data,
    }
    const response = await request(params)
    console.log('API 调用成功:', response)
    return response
  } catch (error) {
    console.error('API 调用失败:', error.message)
    throw error
  }
}
export const assertCode = async (data) => {
  try {
    // 准备请求参数
    const params = {
      url: '/api/assert',
      method: 'GET',
      data,
      requestType: 'string',
      responseType: 'json',
    }
    const response = await request(params)
    console.log('API 调用成功:', response)
    return response
  } catch (error) {
    console.error('API 调用失败:', error.message)
    throw error
  }
}
export const error = async (data) => {
  try {
    // 准备请求参数
    const params = {
      url: '/api/error',
      method: 'GET',
      data,
      requestType: 'string',
      responseType: 'json',
    }
    const response = await request(params)
    console.log('API 调用成功:', response)
    return response
  } catch (error) {
    console.error('API 调用失败:', error.message)
    throw error
  }
}

