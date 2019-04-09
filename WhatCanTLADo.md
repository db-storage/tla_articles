# 1. TLA+能做什么？

Temporal Logic of Actions (TLA) 是 Lamport 在1980年代发明的一种形式化描述语言，它使用单个公式(Formula)来描述系统。但是后来发现单个公式没法描述复杂的工程化系统，于是又发明了TLA+语言。

我们可以用 TLA+ 语言描述自己的算法/模型(这些文件称为 Specification)。用TLA+写的描述称为Specification，简称为Spec。Spec 形式化地描述系统的状态以及在每个状态下可能有哪些行为(Action/Step)。有了 Spec 后，可以使用 TLC Model Checker 这个工具，来验证 Spec 描述的模型的正确性。

所谓正确性验证，实际上包括 **Safety 和 Liveness** 两个方面的验证。其中最重要的是 Safety。

**Safety** 是模型设计者想要保证的内容，或者说是系统的设计底线。例如，在分布式数据库系统中，对于某一个 2PC 事务，要保证的底线可能是：不能有部分参与者认为 Rollback 了，另外一部分认为 Commit 了，或者一个参与者先认为 Commit 了，后来又认为 Rollback 了。

**Liveness** 则是指满足条件的 Action 能够被执行，而不是一直原地踏步。

下面举几个例子，说明下 Safety 和 Liveness 大致是什么。但是每个模型的 Safety 和  Liveness 都是需要使用者自己定义的，TLA+ 只是提供描述语言，不是模型本身。

> 后续我们详细解释liveness时会发现，其实liveness里面还包含了公平性在里面，暂时没想到合适的汉语词汇对应。所以在文中沿用 Safety 和 Liveness 两个词。关于 Liveness，wiki上有段解释，参见 [这里](https://en.wikipedia.org/wiki/Liveness)。

| 模型                    | Safety                                                       | Liveness                                                     |
| ----------------------- | ------------------------------------------------------------ | ------------------------------------------------------------ |
| 分布式事务(2PC)         | 考虑单个事务的执行过程，关于 Commit 还是 Rollback 这个决策，必须是唯一且不变的。所有参与者、协调者，不能有部分认为Commit了，部分认为 Rollback 了，也不能一会决定 Commit，一会决定 Rollback。 | 一个事务，最终要么 Commit，要么 Rollback，不能一直处于未决状态。 |
| 读写锁                  | 不能有两个请求者同时获得了写锁；不能在有请求者获得了写锁的同时，有请求者获得了读锁。 | 所有加锁请求，无论读写，最终都能满足(不考虑公平性)           |
| 分布式Key/Value缓存模型 | 即为 Cache Coherency。如果某节点缓存了某一个 key，那么对应 Value 必须与后端存储是相同的。 | 最终每个读请求都能执行完成                                   |



# 2. 既然有软件测试，为什么还需要 TLA+ 去验证？

虽然软件测试能发现很多问题，但是它不能替代 TLA+。如果我们把一个系统的运行看成一些列的状态变更，那么软件测试存在下面两方面问题：

1. 很难明确到底应该出现哪些状态序列，其中哪些序列在测试中已经出现了。尤其是并发导致的大量不同状态序列。代码覆盖率这种静态指标并不能解决这个问题。 
2. 缺乏全局视角和验证手段： 即使在测试过程中所有状态序列都出现了，我们也难以在每一个状态，都去验证是否违背了 Safety。比如，考虑上面提到的 2PC 分布式事务，在实际系统中，如何验证分布在多个节点上的参与者以及协调者，对于事务 Commit/Rollback 的认识是一致的？我们不可能让所有的程序都暂停下来，收集所有状态值，然后进行判断。



以分布式 key/value 缓存为例，对应为：

- 如何确认没有未测试的 Corner Case?

  > 即使系统运行了很久，使用各种单元加系统测试手段，也难以确信没有任何 corner case，因为我们的用例是非常有限的。

- 如何在运行过程中每一个可能的状态都检查 Cache Coherency?

  

除了在验证过程的优势，我们利用 TLA+的方式去做形式化思考，可以帮我们清晰地认识和描述：系统里面到底应该有哪些行为，哪些行为是原子的，系统正确性(底线)到底是什么。这些形式化的思考和验证，在实现系统之前就应该完成。



# 3. TLA+ 有啥实际应用和效果？

以亚马逊的云服务部门 AWS 为例，下表给出了一些重要模块的使用 TLA+ 进行形式化验证的收获。这篇文章是2014年的，当时 AWS 的服务比现在少得多，但是我们仍然能看到 AWS 的一些重量级服务：S3, DynamoDB, EBS使用了它进行模型验证。

其中，有不少是利用 PlusCal 写的。PlusCal 是 TLA+ 的语法糖，写起来更简单。PlusCal 可以自动转换为TLA+，再进行验证。但是 PlusCal 不能支持所有的 TLA+ 的功能和语法。我们暂时不涉及 PlusCal。

| System                             | Components                                               | Line count(excl. comments) | Benefit                                                      |
| ---------------------------------- | -------------------------------------------------------- | -------------------------- | ------------------------------------------------------------ |
| S3                                 | Fault-tolerant low-level network algorithm               | 804 行PlusCal              | Found **2 bugs**. Found further bugs in proposed optimizations. |
| S3                                 | Background redistribution of data                        | 645行 PlusCal              | Found **1 bug,** and found a bug in the first proposed fix.  |
| DynamoDB                           | Replication & groupmembership system                     | 939 行TLA+                 | Found **3 bugs**, some requiring traces of 35 steps          |
| EBS                                | Volume management                                        | 102 行PlusCal              | Found **3 bugs**.                                            |
| Internal  distributed lock manager | Lock-free data structure                                 | 223 行PlusCal              | Improved confidence. Failed to find a liveness bug as we did not<br/>check liveness. |
| Internal  distributed lock manager | Fault tolerant replication and reconfiguration algorithm | 318 行 TLA+                | Found **1 bug**. Verified an aggressive optimization.        |


表格来源： [链接](https://lamport.azurewebsites.net/tla/formal-methods-amazon.pdf)



# 4. TLA+ 是如何进行形式化验证的？

TLC Model Cheker 对 Spec的正确性验证过程，可以大致按照如下方式理解：

- 按照 Spec 描述的初始状态条件，计算初始状态(满足初始条件的状态，可能是多个)。
- 按照深度优先或者广度优先的方式，按照描述的状态变更步骤，得出各种不同的状态，并记录状态变更序列。
- 对于每个状态，都会验证是否满足 Safety 条件。对于不满足 Safety 条件的状态，给出相应的状态序列。

在了解TLA+的语法之前，先不写spec，而是用一个简单代码例子来思考下(这段代码没有什么实际用途)：

```c
//假设lock()与unlock()是正确实现了的加锁和解锁函数

void thread_func(void *p) {
  int running = 0;
  while(true) {
    //atomic step 0
    lock(); 
    gRunning++; //gRunning是全局变量
    running = gRunning;
    unlock();

    //这里可以执行其他不修改读取running的操作，但是不使用gRunning。先省略。
    
    //atomic step 1， 包含下面三行
    lock();
    gRunning--;
    running  = gRunning；
    unlock();
  }//while(true)
}
```

代码中lock()与unlock()之间的临界区代码都可以被认为是一个原子步骤。 上述代码一共定义了两个原子步骤: s0, s1。为了避免对哪些操作是一个atomic step产生疑虑，我们在代码中使用了lock/unlock，虽然这并非必须的。

## 4.1 几个简单的常用语法符号

简单说明下，Spec用到的几个常用符号：

| 符号      | 含义                                                         |
| --------- | ------------------------------------------------------------ |
| ```==```  | 符号的右边是符号左边标识符的定义                             |
| ```=```   | 逻辑表达式，判断符号两边相等。“a = b” 表示 “a 和 b相等""，**注意不是赋值** |
| ```\/```  | 逻辑运算符 OR，即 \|\|                                       |
| ```/\```  | 逻辑运算符 AND，即 &&                                        |
| ```\in``` | 集合运算中的属于, ```a \in S``` 表示 a 是 S 的一个元素       |
| \|->      | 左边的域，映射为右边值，可以简单理解为结构体成员的名称和对应值 |
| ```\A```  | 任意一个 (for all)                                           |
| ```\E```  | 存在 (there exists)                                          |
| ```[ ]``` | 恒成立 (always true)                                         |

$$

$$



## 4.2 Spec的组成部分

一个完整的Spec主要包含以下几个Section，后面的例子中，我们用分割线做了分割，可以对应到这几个部分。

Spec中除了一些变量和常量定义，其余内容都是逻辑表达式(值为TRUE/FALSE的式子)。后续会结合实际内容解释这些式子。

| Section                   | 是否为逻辑表达式 | 说明                                                         |
| ------------------------- | ---------------- | ------------------------------------------------------------ |
| 常量、变量和辅助操作定义  | 否               |                                                              |
| 允许出现的Atomic Step定义 | 是               | 一般都定义当前状态需要满足的条件以及 Step 完成后，下一个状态需要满足的条件。这些 Step 会被原子执行。 |
| 初始状态                  | 是               | 定义初始状态需要满足的条件的逻辑表达式。表达式一般只定义条件，不是具体值。满足条件的初始状态可能是多个。 |
| 允许的状态变化(Next)      | 是               | 在初始状态后，允许执行哪些 Atomic Step。                     |
| Spec                      | 是               | 一般为: ```Init /\ [ ] [Next]_vars``` 形式。                 |
| Safety Property           | 是               | 运行中在每个状态需要检查的不变式。                           |



## 4.3 与代码对应的Spec

对于前面的代码，我们可以写出下面的 spec，里面有比较详细的注释。注意有几个地方在代码里面是没有的：

- 为每个线程增加了一个next变量，用于记录线程下一步应该执行的步骤。
- 增加了 TypeInv 和 StateInv 两个 Safety Property，并且在TLC工具执行时指定了要检查这两个属性。

> 由于这个例子比较特殊，我们描述的是一个循环，所以需要next变量。在后续的很多例子中，往往描述的是更抽象的逻辑，状态是用其他变量描述的，并不需要next变量。

```tla
----------------------- MODULE ThreadSample -----------------------
EXTENDS  Naturals, Sequences, FiniteSets, TLC
----------------------(*Constants 和 Variables*)-------------------
(* 运行时，需要在配置中指定 CONSTANT的值，它是一个集合 *)
CONSTANT ThreadIds
VARIABLE thread, gRunning

(* 一共只有2个 Step *)
kNumSteps == 2
(* tThread类似于一个结构体类型定义, 每线程有两个变量：next 和 running。
   next 实际上类似于汇编中的eip寄存器，表明下一步执行的语句。
*)
tThread == [ next : 0 .. kNumSteps - 1,  running : Nat ]
(* 所有的变量列表 *)
allVars == <<thread, gRunning>>

-----------------------(* utility operations *)---------------------
(* 取模操作封装。定义为 先加1 再取模。得到的还是个整数 *)
NextValue(cur) == 
  (cur + 1) % kNumSteps

(* 判断线程 t 下一步要执行的等于s，注意 "=" 不是赋值，而是判断两边相等 *)
AtStep(t, s) == 
  thread[t].next = s

---------------------------(* 两个Step的定义 *)-----------------------
(* 注意 带单引号'的变量，表示在下一个状态中，该变量需要满足的条件。
   它不是赋值式，而是个逻辑表达式。
   例如，下面的 "gRunning' = gRunning + 1" 解释为： 
           在下一个状态中，gRunning的值，等于当前状态中gRunning的值加1
    如果我们将其理解为赋值操作，那么就不可能与其他表达式做 && 运算了。           
*)


(* 下面式子的含义：线程 t 执行step 0。
   具体定义为多个表达式的逻辑与。只有前面判断条件成立，才会进入下一个状态。
   LET 只是个临时变量定义，减少重复书写，没特别意义。LET 后面的三行，含义为：
   && 前提条件： thread t 的 Next Step 是 0
   && 下一个状态中，gRunning的值是当前值 + 1
   && 下一个状态中，所有thread 中，只有 thread[t] 的状态有变化，其他thread不变
 *)
AtomicStep0(t) == 
   LET cur == thread[t].next IN
     /\ AtStep(t, 0)  
     /\ gRunning' = gRunning + 1  
     /\ thread' =  
       [ thread EXCEPT ![t] = [next |-> NextValue(cur), running |-> gRunning' ] ]

(* 线程 t 执行step 1，与上面类似 *)
AtomicStep1(t) == 
   LET cur == thread[t].next IN
      /\ AtStep(t, 1)
      /\ gRunning' = gRunning - 1
      /\ thread' =  
         [ thread EXCEPT ![t] = [next |-> NextValue(cur), running |-> gRunning'] ]

-------------------------(* 初始状态的表达式定义 *)-------------------------
(* 合法的初始状态需要满足的公式。实际上只有一个状态能满足，即每个thread 的running
   都是0，下一个要执行的步骤都是Step0
*)
Init == 
  /\ thread = [ tid \in ThreadIds |->  [ running |-> 0, next |-> 0] ]
  /\ gRunning = 0

-----------------------------(* Next操作 *)--------------------------------
(* 存在一个线程，能执行 Step0 或者 Step1。注意着也是个逻辑表达式 *)
Next ==
  \E  t \in ThreadIds:
    \/ AtomicStep0(t)
    \/ AtomicStep1(t)

(* 初始状态为TRUE && 总是能执行Next或者保持不变。_allVars是个特殊写法 *)
Spec == Init /\ [][Next]_allVars

---------------------------(* 两个Safety Check *)----------------- --------
(* TypeInv 和 StateInv 是添加的不变式，不具体对应例子代码中的某个部分 *)
(* 类型不变式 *)
TypeInv == 
  /\ thread \in [ ThreadIds ->  tThread ]
  /\ gRunning \in Nat
 
(* 状态不变式 *)
StateInv ==
  /\ gRunning  <= Cardinality(ThreadIds)
  /\ \A t \in ThreadIds: 
      /\ thread[t].running <= Cardinality(ThreadIds)
      /\ thread[t].running <= gRunning

=============================================================================
```



## 4.4 配置单个Thread ID，执行 Model Check 结果

在运行 TLC Model Checker 时，我们配置ThreadIds = { "A"}，即集合中只有一个thread，然后执行，可以得到以下的简单状态变更：

![1thread](https://github.com/db-storage/tla_articls/blob/master/Figures/1thread.jpg)

由于单线程，一共就两个状态，执行 Step 2后，又回到初始状态，虽然可以一直运行，但是不同的状态数量就两个。两个状态中，各个变量的值变化我们也可以手工对应下。



## 4.5 配置两个Thread ID，执行 Model Check 结果

如果配置 ThreadIds = { "A"，"B"}，执行后很快就出现 Error，因为 StateInv 不满足。并且明确告知这个错误状态是如何达到的。

![1thread](https://github.com/db-storage/tla_articls/blob/master/Figures/2thread_err.jpg)

这个错误，实际上是由于Spec中存在bug导致的。读者可以思考下，**为什么这个Error，在配置单线程Check时没有表现出来，而配置两个线程再Check就出现了**？



# 5. TLA+的一些FAQ

#### 哪里有TLA+的资源？

参见 Lamport 在Microsoft Azure 的[主页](http://lamport.azurewebsites.net/tla/tla.html)。 这实际上就是官网了，有文档以及相关工具下载。



#### 利用TLA+ 验证后的模型，能自动转换成代码么？如何保证对应的代码是正确的？

TLA+实际上只能用于验证关键算法/模型的正确性，在model check过程中，可能的状态序列必须在有限时间内验证完成。

TLA+ spec **不能自动转变为代码**。

代码的正确性取决于很多因素，同一个算法，不同的人实现出来也会不同。因此，算法正确性不等于代码正确性。



#### TLA+ 能验证算法的性能么？

不能。



#### TLA+只能用于验证分布式系统的正确性么？

否。

虽然 Lamport 的大量研究成果都和分布式相关(例如Paxos、Logical Clock、Distributed Snapshot)，但是TLA+并非分布式系统专用。各类系统设计，包括硬件设计，都可以抽象出数学模型用TLA+描述并进行验证。







