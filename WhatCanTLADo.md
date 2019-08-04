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



#  4. TLA+基本知识

TLC Model Cheker 对 Spec的正确性验证过程，可以大致按照如下方式理解：

- 按照 Spec 描述的初始状态条件，计算初始状态(满足初始条件的状态，可能是多个)。

- 按照深度优先或者广度优先的方式，按照描述的状态变更步骤，得出各种不同的状态，并记录状态变更序列。

- 对于每个状态，都会验证是否满足 Safety 条件。对于不满足 Safety 条件的状态，给出相应的状态序列。

  

## 4.1 几个简单的常用语法符号

简单说明下，Spec用到的几个常用符号：

| 符号  | 含义                                                         |
| :---- | :----------------------------------------------------------- |
| `==`  | 符号的右边是符号左边标识符的定义                             |
| `=`   | 逻辑表达式，判断符号两边相等。“a = b” 表示 “a 和 b相等""，**注意不是赋值** |
| `\/`  | 逻辑运算符 OR，即 \|\|                                       |
| `/\`  | 逻辑运算符 AND，即 &&                                        |
| `\in` | 集合运算中的属于, `a \in S` 表示 a 是 S 的一个元素           |
| \|->  | 左边的域，映射为右边值，可以简单理解为结构体成员的名称和对应值 |
| `\A`  | 任意一个 (for all)                                           |
| `\E`  | 存在 (there exists)                                          |
| `[ ]` | 恒成立 (always true)                                         |



## 4.2 Spec的组成部分

一个完整的Spec主要包含以下几个Section，后面的例子中，我们用分割线做了分割，可以对应到这几个部分。

Spec中除了一些变量和常量定义，其余内容都是逻辑表达式(值为TRUE/FALSE的式子)。后续会结合实际内容解释这些式子。

| Section                   | 是否为逻辑表达式 | 说明                                                         |
| :------------------------ | :--------------- | :----------------------------------------------------------- |
| 常量、变量和辅助操作定义  | 否               |                                                              |
| 允许出现的Atomic Step定义 | 是               | 一般都定义当前状态需要满足的条件以及 Step 完成后，下一个状态需要满足的条件。这些 Step 会被原子执行。 |
| 初始状态(Init)            | 是               | 定义初始状态需要满足的条件的逻辑表达式。满足条件的初始状态可能是多个。 |
| 允许的状态变化(Next)      | 是               | 在初始状态后，允许执行哪些 Atomic Step。                     |
| Spec                      | 是               | 常见为: `Init /\ [ ] [Next]_vars` 形式。可以加入其他内容，暂时不扩展。 |
| Safety Property           | 是               | 运行中在每个状态需要检查的不变式。                           |

# 5. TLA+ 是如何进行形式化验证的？





## 5.2 与代码对应的Spec

> [spec文件](https://github.com/db-storage/tla_articles/blob/master/Examples/Clock/HourMinuteClock.tla)直接下载

```tla
---------------------------- MODULE HourMinuteClock ----------------------------
EXTENDS Naturals, TLC

----------------------------------------------------------------------------
(* Variables 和 constants 定义部分 *)
----------------------------------------------------------------------------
VARIABLES hour, minute
(* 所有变量组成的tuple，在Spec中用到 *)
vars == <<hour, minute>>
(* 允许在运行TLC Model Checker时配置。使用较小的值，便于测试、图形化显示结果等*)
CONSTANT HoursPerDay
CONSTANT MinPerHour

----------------------------------------------------------------------------
(* State Predicate定义 *)
----------------------------------------------------------------------------
(* hour和minute的取值范围，用谓词表示 *)
HourTypeOK == hour \in (0 .. HoursPerDay -1)
MinuteTypeOK == minute \in (0 .. MinPerHour-1)
(* 所有变量的取值范围限制谓词 *)
TypeInv == HourTypeOK /\ MinuteTypeOK

----------------------------------------------------------------------------
(* State Change 相关定义 *)
----------------------------------------------------------------------------
(* 初始化状态，正好与TypeInv式子相同。从任意一个时间点开始都可以 *)
Init == HourTypeOK /\ MinuteTypeOK
MinNext == minute' = (minute + 1) % MinPerHour
HourNext == hour' = IF minute # (MinPerHour-1) THEN hour ELSE (hour + 1) % HoursPerDay
(* Tick可以理解伪Clock走了以下 *)
Tick == MinNext /\ HourNext
Next == Tick /\ PrintT(<<hour, minute>>)

----------------------------------------------------------------------------
(* Behavior Properity 相关定义 *)
----------------------------------------------------------------------------

Spec == Init /\ [][Next]_vars /\ WF_vars(Tick)  /\ []TypeInv 
=============================================================================
```



## 5.3 配置较小的范围，执行 Model Check 结果

在运行 TLC Model Checker 时，我们配置HoursPerDay= 3，MinPerHour =4, 能看到一个的简单状态变更：

![hour_3_min_4](https://github.com/db-storage/tla_articles/blob/master/Figures/3_hour_minute_clock_1.jpg)









