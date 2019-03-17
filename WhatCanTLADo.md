# TLA+能做什么？

TLA+ 是一种形式化描述语言，使用者用TLA+语言描述自己的算法/模型后(这些文件称为specification)，使用TLC Model Checker工具，来验证模型的正确性。

所谓正确性，实际上包括**Safety和Liveness**两个方面。最重要的是Safety。

Safety可以认为是系统要保证的内容，或者说是底线。例如，对于一个2PC事务，我们要保证的底线：不能有部分参与者认为rollback了，部分认为commit了。至于决策花了多久，各个参与者执行commit/rollback的时间相差多少，这是相对次要的问题。

下面举几个例子，说明下Safety和Liveness大致是什么。但是每个模型的Safety和 Liveness都是需要使用者自己定义的。

> 后续我们详细解释liveness时会发现，其实liveness里面还包含了公平性在里面，暂时没想到合适的汉语对应。所以在文中沿用Safety和Liveness两个词。关于Liveness，wiki上有段解释，参见 [这里](https://en.wikipedia.org/wiki/Liveness)。

| 模型                    | Safety                                                       | Liveness                                                     |
| ----------------------- | ------------------------------------------------------------ | ------------------------------------------------------------ |
| 分布式事务(2PC)         | 考虑单个事务的执行过程，关于commit还是rollback这个决策，必须是一致的。所有参与者、协调者，不能有部分认为commit了，部分认为rollback了，而且也不能先commit，后rollback。 | 一个事务，最终要么commit，要么rollback，不能一直出于未决状态。 |
| 读写锁                  | 不能有两个请求者同时获得了写锁；不能在有请求者获得了写锁的同时，有请求者获得了读锁。 | 所有请求，无论读写，最终都能满足(不考虑公平性)               |
| 分布式Key/Value缓存模型 | 如果某节点缓存了某一个key的数据，那么缓存的Value，应该与后端存储是相同的； | 最终每个读请求都能完成                                       |



# 常规的测试验证存在哪些问题？

1. 很多状态序列在实际系统中出现概率比较低，在短期能没法测试到。一些并发case甚至不知道测试到了没有。尤其是并发导致的大量不同状态序列，代码覆盖率这些指标也没意义。

   > 虽然系统是并发的，但是站在全局视角，仍然可以把所有的并发event看成按照发生的顺序组成一个状态序列。

2. 缺乏全局视角和验证手段： 即使在测试过程中所有状态序列都出现了，我们也难以验证是否存在某个状态违背了Safety。比如，考虑上面提到的2PC分布式事务，在实际系统中，如何查看分布在多个节点上的参与者以及协调者，对于事务Commit/Rollback的认识是一致的？



以分布式key/value 缓存为例 ：

- 如何确认没有未测试的 Corner Case?

  > 即使系统运行了很久，使用各种单元加系统测试手段，也难以确信没有任何 corner case，因为我们的用例是非常有限的。

- 如何在运行过程中每一个可能的状态都检查Cache Coherency?

  > 从实现的角度，一个分布式系统无法在每一步都去检查Cache Coherency。





# TLA+实际应用于哪里了？

以亚马逊的云服务部门AWS为例，原文给出了一些重要模块的使用 TLA+ 进行形式化验证的收获。这篇文章是2014年的，当时AWS的服务比现在少得多。但是我们能看到AWS的一些重量级服务：S3, DynamoDB, EBS。

其中，有不少是利用PlusCal写的。PlusCal是TLA+的语法糖，写起来更简单。PlusCal可以自动转换为TLA+，再进行验证。但是PlusCal不能支持所有的TLA+功能和语法。

| System                             | Components                                               | Line count(excl. comments) | Benefit                                                      |
| ---------------------------------- | -------------------------------------------------------- | -------------------------- | ------------------------------------------------------------ |
| S3                                 | Fault-tolerant low-level network algorithm               | 804 行PlusCal              | Found **2 bugs**. Found further bugs in proposed optimizations. |
| S3                                 | Background redistribution of data                        | 645行 PlusCal              | Found **1 bug,** and found a bug in the first proposed fix.  |
| DynamoDB                           | Replication & groupmembership system                     | 939 行TLA+                 | Found **3 bugs**, some requiring traces of 35 steps          |
| EBS                                | Volume management                                        | 102 行PlusCal              | Found **3 bugs**.                                            |
| Internal  distributed lock manager | Lock-free data structure                                 | 223 行PlusCal              | **Improved confidence**. Failed to find a liveness bug as we did not
check liveness. |
| Internal  distributed lock manager | Fault tolerant replication and reconfiguration algorithm | 318 行 TLA+                | Found **1 bug**. Verified an aggressive optimization.        |
表格数据来源： [链接](https://lamport.azurewebsites.net/tla/formal-methods-amazon.pdf)



# TLA+是如何进行形式化验证的？

TLC Model Cheker在对spec的正确性验证，大致按照如下方式理解：

- 全局视野/上帝视野： 把整个spec描述的系统(可能是分布式系统)，看成一个宇宙(Universe)。

- 宇宙中所有可能的event，按照深度优先或者广度优先的方式，得出各种可能的状态序列。

- 对每个序列的每个状态，验证是否满足正确性条件(可以认为宇宙暂停运转，上帝查看所有事物(变量)的状态十分满足正确性要求。

在了解TLA+的语法之前，先不写spec，而是用一个简单的伪代码例子来思考下：

```c
while(true){
  //假设语句1和语句2都是单cpu指令，原子执行 
  语句1; //event1
  语句2; //event2
  lock();   //下面三行，整体是原子的，认为是event3
    语句3;  
  unlock();
}
```

假设有两个线程 (T1, T2)在同时运行上述代码，我们可以认为上述伪代码一共定义了三个event。

- 在每个线程内部，执行event的顺序是确定的。

- 在T1在执行event1和event2之间，T2可能执行了哪些event序列？可以简单列举几个： {1}, {2}, {3}, {1,2}, {2,3}, {3, 1}, {1,2,3}, {1,2, 3,1}...

可以看出，系统可能出现的状态组合非常多。不同的并发执行，产生的结果状态可能是不同的，也可能相同。

TLC Model Checker，从用户定义的初始状态开始，在每一个状态，默认以广度优先方式，搜索可能的下一个event，对于每个不同的event序列进行记录。在计算过程中，为每个状态计算一个Fingerprint。避免对相同的状态重复搜索next。

比较 Fingerprint的方式是存在误判的，TLC通过在多次运行中使用不同的随机函数来解决。



# TLA+的一些FAQ

#### 利用TLA+ 验证后的模型，能自动转换成代码么？如何保证代码是正确的？

TLA+实际上只能用于验证关键算法/模型的正确性，不能用于验证完整的系统。一般只在有限规模下验证关键的算法、模型。

TLA+ spec也不能自动转变为代码。

代码的正确性取决于很多因素，同一个算法，不同的人实现出来也会不同。因此，算法正确性不等于代码正确性。



#### TLA+ 能验证算法的性能么？

不能，性能不是模型该验证的。



#### TLA+只能用于验证分布式系统的正确性么？

虽然Lamport先生的大量著名研究成果都和分布式相关(例如Paxos, Logical Clock, Latex)，但是TLA+并非分布式系统专用。大部分系统，都可以抽象出数学模型进行验证。







