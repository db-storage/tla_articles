# WriteThroughCache

## 什么是Write Through

- 写Cache的同时，需要更新主存(但这个不是原子操作)。

## 模型

- 多进程
- 每个进程有自己的Cache
- Memory的读写操作是顺序的



## 支持的操作

- Read

- Write


## 一些思考和改动

### 改变下Coherence



### 读写Memory不排队



### 各个进程的请求分别排队



