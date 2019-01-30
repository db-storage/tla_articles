# WriteThroughCache

## 什么是Write Through

- 简单来说，在Cache的同时，也要写缓存
- 在一次状态变更中，完成写Cache的同时，产生更新主存的请求(只是请求进入队列，真正写主存，是单独的状态变更)。

## 模型

- 多进程
- 每个进程有自己的Cache
- Memory的读写操作是顺序的



## 支持的操作

### 1. Read

### 2. Write

### 3. Evict

- 由于Evict哪个cache项以及什么时候Evict不影响正确性，只影响效率，所以随机选择一个Cache元素去Evict 

## 

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




## 一些思考和改动

### 改变Write请求进入memQ的位置(Head还是Tail?)

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
                      => (cache[p][a]= wmem[a]) 
```



### 读写Memory不排队



### 各个进程的请求分别排队



