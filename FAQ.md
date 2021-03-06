# 

## 简单说下下TLA+的特点?

- 把算法的执行看出状态机，用数学描述这个状态机；
- 定义状态机的执行过程中需要满足的约束条件；
- 检验状态机执行是否满足约束条件(Safety, Liveness, Faireness等)。



## 状态机跟我们平时说的有区别么？

- 整个算法/系统是一个状态机，而不是某个进程是个状态机。
- 考虑一个3节点的Paxos集群，整个集群的运行，被看作一个状态机(实际上是个宇宙)，而不是每个节点一个状态机。



## 比较下 State 和 Behavior？

- 状态可以看出是给变量赋值，而行为是状态序列。
- 以下来自Lamport的文章 [If You’re Not Writing a Program, Don’t Use a Programming Language](http://bulletin.eatcs.org/index.php/beatcs/article/view/539/532)
> An execution of an algorithm is represented mathematically as a sequence of states, where a state is an assignment of values to variables. A sequence of states is called a behavior. 



## Spec中的Next是描述如何给变量赋值么？

- Spec中出现的Next本质上是一个谓词公式，它描述的是当前State和Next State之间需要满足的条件，而不是赋值操作本身；
- 谓词本质上是个返回TRUE/FALSE的公式(表达式)；
- 谓词的形式可以是 x = 10 /\ x' = x+1 这种，也可以写成 x= 10 /\ x' \in  1..1000 这种。即如果当前状态中 x == 10，那么下一状态中，x应该是什么样的值，如果符合这个谓词，那么就返回TRUE。



## 比较下 State Predicate 和 Behavior Property?

- State Predicate： 每个状态需要满足的条件，例如类型，某些变量之间的关系，也经常称为Invariance。它把每个状态看成独立的个体，不考虑两个或者更多状态之间的关系。

- Behavior property: 不是看某个状态，而是整个序列需要满足的条件。例如Init/\[]Next，Liveness, Fairness，都不是针对单个状态的。

- 有时候二者是可替换的，比如，如果每一个状态都需要保证的 "TypeOK"，既可以放到Invariants里面(作为state predicate)，也可以写成[]TypeOK，放到 Behavior Properities里面。

- 但是Liveness/Fairness这种本身就是针对Beheviour的，描述单个状态并无意义或者不会成立，只能作为Behavior Property。



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

- 它实际上是一个Behavior Properity。
- 针对的是一个Behavior，而不是一个State。
- Behavior的初始状态需要满足 Init公式(注意，不是[]Init，是Init);
- Behavior 需要满足[]Next_vars，即Next成立或者什么vars的值不变(注意这里有个[])；
- 假设一个Behavior由S0, S1, S2, .., Sn这些状态组成，那么只有S0需要满足Init。而后面的所有状态变更，S0 --> S1, S2 --> S2，Sn-1 --> Sn这些，都需要满足Next约束；
- 什么都不变称为为Stuttering Step，vars里面的变量都不修改，本文档后面有解释。



## TLA+ Spec这么复杂，我的代码上万行或者更多，怎么验证？

- TLA+主要验证核心算法和模型，尤其是那些需要上帝视角的算法；
- 并发是典型的适合用TLA+做验证的，但是其他算法也可以。



## Stuttering Steps 有啥用？

- 考虑一个只有Hour和Minute两个变量的clock(AlgHM)，它作为有Hour,Minute，Second的Clock(AlgHMS)的Refine, AlgHMS作为AlgHM的一个实现，它共用AlgHM定义的Hour和Minute，但是自己定义了Second变量。 AlgHMS 可能只修改了Second变量，那么对于AlgHM来说，就是个Stuttering step，它必须允许自己看到的Hour和Minute都不变。(以下来自 [If You’re Not Writing a Program, Don’t Use a Programming Language](http://bulletin.eatcs.org/index.php/beatcs/article/view/539/532))



## 为什么Paxos的TLA+ spec那么简单？

- 对比Paxos 和Raft的TAL+ spec，发现 Paxos的内容确实非常少。
- Lamport的原话：  “Don't think about what may go wrong，think what must go right”。
- 也就是说，保证执行的事件的正确性即可；那些未发生或者丢失的事件，不重要(相当于Behavior中这些事件被无限延迟，这是允许的)。



## 哪里有TLA+的资源？

参见 Lamport 在Microsoft Azure 的[主页](http://lamport.azurewebsites.net/tla/tla.html)。 这实际上就是官网了，有文档以及相关工具下载。