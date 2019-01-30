# WriteThroughCache

## 什么是 Write Through Cache

- 简单来说，在Cache的同时，也要写主存
- 与Write Back相对应，Write Back是先写到Cache，在合适的时候写回主存
- 在下面要解释的TLA Spec 中，在一次状态变更中，完成写Cache的同时，产生更新主存的请求(只是请求进入队列。而真正的写主存，则由单独的状态变更完成)。

## 模型

- 多进程
- 每个进程有自己的Cache
- 每个进程最多只有一个待执行的请求(包括读/写)，这个通过ctl[p]的状态来控制
- 主存的读写操作按照FIFO方式进行



## 支持的接口

### 1. Read

### 2. Write

### 3. Evict

- 由于Evict哪个cache项以及什么时候Evict不影响正确性，只影响效率，所以随机选择一个Cache元素去Evict 

  



## Spec分析

### Spec组成

### 各个操作的含义解析

```tla
(* wmem is a function,  Adr -> Val                                          *)
(* f[0] =  wmem, so f[0] is a function:    Adr -> Val                       *)
(* f is a function,  [0 .. Len(memQ)] -> ([Adr] -> Val)                     *)
(* vmem == f[Len(memQ)], the LAST ITEM in f,  it's a map: Map[Adr] -> Val   *)

(* For i > 0,                                                               *)
(*     IF memQ[i] is a "Rd", skip it, so f[i] = f[i-1]                      *)
(*     ELSE f[i] = f[i-1] EXECPT f[i][memQ[i][2].adr] =memQ[i][2].val       *)
(* Conclusiong: vmem is: wmem + all writes in memQ                          *)
vmem  ==  
  LET f[i \in 0 .. Len(memQ)] == 
        IF i=0 THEN wmem
               ELSE IF memQ[i][2].op = "Rd"
                      THEN f[i-1]
                      ELSE [f[i-1] EXCEPT ![memQ[i][2].adr] =
                                              memQ[i][2].val]
  IN f[Len(memQ)] 
```



### 为什么需要MemQRd 和 MemQWr？




## 

## 尝试做些改动

### 改变下Coherence



```tla

Coherence == \A p, q \in Proc, a \in Adr : 
                (NoVal \notin {cache[p][a], cache[q][a]})
                      => (cache[p][a]=cache[q][a]) 

```

修改为：

```tla

Coherence == \A p \in Proc, a \in Adr : 
                (NoVal \neq cache[p][a]) =>
                      => (cache[p][a]= vmem[a]) 
```





### 不读vmem，直接读取wmem

### 每个Process可以有多个并发请求



## 如何对应到代码实现

### - DoWrite()操作的原子性保证？锁总线



