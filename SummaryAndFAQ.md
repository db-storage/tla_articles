# 一些要点

## 把算法的执行看出状态机，用熟悉描述状态机
-  想要准确描述算法，最可行的是用状态机
> The practical way to precisely describe algorithms is with state machines.来自 [If You’re Not Writing a Program, Don’t Use a Programming Language](http://bulletin.eatcs.org/index.php/beatcs/article/view/539/532)

## 此状态机非彼状态机
- 整个算法/系统是一个状态机，而不是某个进程是个状态机。
- 考虑一个3节点的Paxos集群，整个集群的运行，被看作一个状态机，而不是每个节点一个状态机。
- 定义状态机的执行过程中需要满足的约束条件。
- 检验状态机执行是否满足约束条件(Safety, Liveness, Faireness等)。

## State vs Behavior
- 以下来自Lamport的文章 [If You’re Not Writing a Program, Don’t Use a Programming Language](http://bulletin.eatcs.org/index.php/beatcs/article/view/539/532)
> An execution of an algorithm is represented mathematically as a sequence of states, where a state is an assignment of values to variables. A sequence of states is called a behavior. 

### State Change
- 算法的执行，可以描述为一系列的State；
- State Change就是给一个或者多个变量的赋值。

### Spec中的Next与变量赋值的关系
- Spec中出现的Next本质上是一个谓词公式，它描述的是当前State和Next State之间需要满足的条件；
- 谓词本质上是个返回TRUE/FALSE的公式(表达式)；
- 谓词的形式可以是 x = 10 /\ x' = x+1 这种，也可以写成 x= 10 /\ x' \in  1..1000 这种。即如果当前状态中 x == 10，那么下一状态中，x应该是什么样的值，如果符合这个谓词，那么就返回TRUE。

### Behavior
- Behavior: 一个状态序列

## State predicate vs Behavior property
- State predicate： 每个状态需要满足的条件，例如类型，某些变量之间的关系，也经常称为Invariance。
- Behavior property: 不是看某个状态，而是整个序列需要满足的条件。例如Init/\[]Next，Liveness, Fairness，都不是单个状态的属性。
- 有时候二者是可替换的，比如，对于每一个状态都需要保证的 "TypeOK"，既可以放到Invariants里面(作为state predicate)，也可以写成[]TypeOK，放到 Behavior Properities里面。
- 但是Liveness/Fairness这种本身就是针对Beheviour的，对于单个状态并无意义或者不会成立，只能作为Behavior Property。

## TLA的spec里面一些不容易理解的地方
### 状态变更描述比较麻烦
- 不是像我们写代码一样，修改某个或者某几个变量就行
- 为什么这样？ 因为Lamport认为描述的每个系统类似于一个宇宙，不能只描述一部分。另外，需要判断每个值满足的条件。


# 一些FAQ

## 哪里有TLA+的资源？

参见 Lamport 在Microsoft Azure 的[主页](http://lamport.azurewebsites.net/tla/tla.html)。 这实际上就是官网了，有文档以及相关工具下载。



## 利用TLA+ 验证后的模型，能自动转换成代码么？如何保证对应的代码是正确的？

TLA+实际上只能用于验证关键算法/模型的正确性，在model check过程中，可能的状态序列必须在有限时间内验证完成。

TLA+ spec **不能自动转变为代码**。

代码的正确性取决于很多因素，同一个算法，不同的人实现出来也会不同。因此，算法正确性不等于代码正确性。



## TLA+ 能验证算法的性能么？

不能。



## TLA+只能用于验证分布式系统的正确性么？

否。

虽然 Lamport 的大量研究成果都和分布式相关(例如Paxos、Logical Clock、Distributed Snapshot)，但是TLA+并非分布式系统专用。各类系统设计，包括硬件设计，都可以抽象出数学模型用TLA+描述并进行验证。



## Init /\ []Next_vars到底是什么含义？

- 针对的是一个Behavior，而不是一个State，它就是一个Behavior Properity。
- Behavior的初始状态需要满足 Init公式;
- Behavior的后续状态需要满足Next的条件，或者什么也不变。什么也不变称为为Stuttering Step，vars里面的变量都不修改，本文档后面有解释。

## 为什么paxos的TLA+ spec那么简单？
- 对比Raft的TAL+ spec，发现 paxos的内容确实非常少。
- 实际是Lamport主要关注算法的Correctness/Safety，而不是是Liveness/Performance。在"The TLA+ book"里面，也提到以Correctness为主。
- 虽然在"paxos made simple"一文中描述了有leader大致怎么做，但是没有作为重点。因为Lamport认为有没有Leader都一样是正确的，有了leader只要遵循基本协议，也是正确的。这个导致很多人到现在仍然认为paxos没有leader。

## TLA+ spec这么复杂，我的代码上万行或者更多，怎么验证？
- TLA+主要验证重要算法和模型，尤其是那些需要上帝视角的算法；
- 并发是典型的适合用TLA+做验证的，但是其他算法也可以。

## Stuttering Steps 有啥用？
- 考虑一个只有Hour和Minute两个变量的clock(AlgHM)，它作为有Hour,Minute，Second的Clock(AlgHMS)的Refine, AlgHMS作为AlgHM的一个实现，它共用AlgHM定义的Hour和Minute，但是自己定义了Second变量。 AlgHMS 可能只修改了Second变量，那么对于AlgHM来说，就是个Stuttering step，它必须允许自己看到的Hour和Minute都不变。(以下来自 [If You’re Not Writing a Program, Don’t Use a Programming Language](http://bulletin.eatcs.org/index.php/beatcs/article/view/539/532))
> Steps allowed by AlgHMS that change only sec are stuttering steps of AlgHM , allowed by the next-state predicate (17). Therefore, AlgHMS will imply AlgHM. 
