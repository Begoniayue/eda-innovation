import {request} from '@/apis/request'

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
    return await request(params)
  } catch (error) {
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
    return await request(params)
  } catch (error) {
    throw error
  }
}
export const sim = async (data) => {
  try {
    // 准备请求参数
    const params = {
      url: '/api/sim',
      method: 'GET',
      data,
      requestType: 'string',
      responseType: 'json',
    }
    return await request(params)
  } catch (error) {
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
    return await request(params)
  } catch (error) {
    throw error
  }
}
export const repair = async (data) => {
  try {
    // 准备请求参数
    const params = {
      url: '/api/repair',
      method: 'GET',
      data,
      requestType: 'string',
      responseType: 'json',
    }
    return await request(params)
  } catch (error) {
    throw error
  }
}
