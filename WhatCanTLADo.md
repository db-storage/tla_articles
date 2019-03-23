# TLA+能做什么？

TLA+ 是一种形式化描述语言，我们可以用TLA+语言描述自己的算法/模型后(这些文件称为specification)，使用TLC Model Checker，来验证模型的正确性。

所谓正确性，实际上包括**Safety和Liveness**两个方面。最重要的是Safety。

**Safety**是系统设计者要保证的内容，或者说是底线。例如，对于某一个2PC事务，我们要保证的底线：不能有部分参与者认为rollback了，部分认为commit了，或者一个参与者先认为commit了，后来又认为rollback了。至于决策花了多久，各个参与者执行commit/rollback的时间相差多少，这是相对次要的问题。

下面举几个例子，说明下Safety和Liveness大致是什么。但是每个模型的Safety和 Liveness都是需要使用者自己定义的，TLA+只是描述语言，不是模型本身。

> 后续我们详细解释liveness时会发现，其实liveness里面还包含了公平性在里面，暂时没想到合适的汉语对应。所以在文中沿用Safety和Liveness两个词。关于Liveness，wiki上有段解释，参见 [这里](https://en.wikipedia.org/wiki/Liveness)。

| 例子                    | Safety                                                       | Liveness                                                     |
| ----------------------- | ------------------------------------------------------------ | ------------------------------------------------------------ |
| 分布式事务(2PC)         | 考虑单个事务的执行过程，关于commit还是rollback这个决策，必须是唯一且不变的。所有参与者、协调者，不能有部分认为commit了，部分认为rollback了，也不能一会决定commit，一会决定rollback。 | 一个事务，最终要么commit，要么rollback，不能一直处于未决状态。 |
| 读写锁                  | 不能有两个请求者同时获得了写锁；不能在有请求者获得了写锁的同时，有请求者获得了读锁。 | 所有加锁请求，无论读写，最终都能满足(不考虑公平性)           |
| 分布式Key/Value缓存模型 | 如果某节点缓存了某一个key，那么对应Value必须与后端存储是相同的。 | 最终每个读请求都能执行完成                                   |



# 既然有软件测试，为什么还需要TLA+去验证？

虽然软件测试能发现很多问题，但是它不能替代 TLA+。如果我们把一个系统的运行看成一些列的状态变更，那么软件测试存在下面两方面问题：

1. 很难明确到底应该出现哪些状态序列，其中哪些序列在测试中已经出现了。尤其是并发导致的大量不同状态序列。我们获得代码覆盖率并不能解决这个问题。

    

2. 缺乏全局视角和验证手段： 即使在测试过程中所有状态序列都出现了，我们也难以在每一个状态，都去验证是否违背了Safety。比如，考虑上面提到的2PC分布式事务，在实际系统中，如何验证分布在多个节点上的参与者以及协调者，对于事务Commit/Rollback的认识是一致的？我们不可能让所有的程序都暂停下来，收集所有状态值，然后进行判断。



以分布式key/value 缓存为例，对应为：

- 如何确认没有未测试的 Corner Case?

  > 即使系统运行了很久，使用各种单元加系统测试手段，也难以确信没有任何 corner case，因为我们的用例是非常有限的。

- 如何在运行过程中每一个可能的状态都检查Cache Coherency?

  

除了在验证过程的优势，我们利用TLA+的方式去做形式化思考，可以帮我们清晰地认识和描述：系统里面到底应该有哪些行为，哪些行为是原子的，系统正确性(底线)到底是什么。



# TLA+实际应用于哪里了？

以亚马逊的云服务部门AWS为例，下表给出了一些重要模块的使用 TLA+ 进行形式化验证的收获。这篇文章是2014年的，当时AWS的服务比现在少得多，但是我们能看到AWS的一些重量级服务：S3, DynamoDB, EBS使用了它进行模型验证。

其中，有不少是利用PlusCal写的。PlusCal是TLA+的语法糖，写起来更简单。PlusCal可以自动转换为TLA+，再进行验证。但是PlusCal不能支持所有的TLA+功能和语法。

| System                             | Components                                               | Line count(excl. comments) | Benefit                                                      |
| ---------------------------------- | -------------------------------------------------------- | -------------------------- | ------------------------------------------------------------ |
| S3                                 | Fault-tolerant low-level network algorithm               | 804 行PlusCal              | Found **2 bugs**. Found further bugs in proposed optimizations. |
| S3                                 | Background redistribution of data                        | 645行 PlusCal              | Found **1 bug,** and found a bug in the first proposed fix.  |
| DynamoDB                           | Replication & groupmembership system                     | 939 行TLA+                 | Found **3 bugs**, some requiring traces of 35 steps          |
| EBS                                | Volume management                                        | 102 行PlusCal              | Found **3 bugs**.                                            |
| Internal  distributed lock manager | Lock-free data structure                                 | 223 行PlusCal              | Improved confidence. Failed to find a liveness bug as we did not<br/>check liveness. |
| Internal  distributed lock manager | Fault tolerant replication and reconfiguration algorithm | 318 行 TLA+                | Found **1 bug**. Verified an aggressive optimization.        |


表格数据来源： [链接](https://lamport.azurewebsites.net/tla/formal-methods-amazon.pdf)



# TLA+是如何进行形式化验证的？

TLC Model Cheker在对spec的正确性验证，大致按照如下方式理解：

- 全局视野/上帝视野： 把整个spec描述的系统(可能是分布式系统)，看成一个宇宙(Universe)。

- 按照深度优先或者广度优先的方式，得出各种可能的状态变更序列。

- 对每个序列的每个状态，验证是否满足正确性条件(这个验证，可以认为小宇宙暂停运转，上帝查看所有变量的状态是否满足正确性要求)。

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

代码中lock()与unlock()之间的临界区代码都可以被认为是一个原子步骤。  上述代码一共定义了两个原子步骤: s0, s1。



假设整个系统只有一个线程 T1在运行上述代码，也就是在执行无限循环。那么这个系统一共只有2个状态：

| 状态id             | Running | gRunning |
| ------------------ | ------- | -------- |
| 0 (也是最开始状态) | 0       | 0        |
| 1                  | 1       | 1        |

后续文章会介绍上述代对应的TLA+ spec。这里我们先贴一个TLC Model Checker输出的状态迁移图。蓝色和绿色，分别代表执行step 0和step 1，以及前后状态变化。由于只有单个线程(名字为：A)，实际上非常简单。 



![1thread](https://github.com/db-storage/tla_articls/blob/master/Figures/1thread.jpg)

TLC Model Checker从用户定义的初始状态开始，在每一个状态，默认以广度优先方式，搜索可能的下一个event，对于每个不同的状态变更序列进行记录，直到所有的序列都被搜索完成。在计算过程中，为每个状态计算一个Fingerprint，避免对相同的状态重复搜索next。比较 Fingerprint的方式是存在误判的，TLC通过在每次运行中使用不同的seed来解决。

在上面的例子中，如果我们定义两个线程A和B，产生多少个状态呢？ 大家可以先思考下，后续会给出实际结果。



# TLA+的一些FAQ

#### 利用TLA+ 验证后的模型，能自动转换成代码么？如何保证代码是正确的？

TLA+实际上只能用于验证关键算法/模型的正确性，在model check过程中，可能的状态序列必须在有限时间内验证完成。

TLA+ spec不能自动转变为代码。

代码的正确性取决于很多因素，同一个算法，不同的人实现出来也会不同。因此，算法正确性不等于代码正确性。



#### TLA+ 能验证算法的性能么？

不能。



#### TLA+只能用于验证分布式系统的正确性么？

虽然Lamport先生的大量研究成果都和分布式相关(例如Paxos、Logical Clock、Distributed Snapshot)，但是TLA+并非分布式系统专用。大部分系统，甚至硬件设计，都可以抽象出数学模型进行验证。







