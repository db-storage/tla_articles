# tla_articls

## 状态机是核心
-  准确描述算法，最可行的是用状态机
> The practical way to precisely describe algorithms is with state machines.来自 [If You’re Not Writing a Program, Don’t Use a Programming Language](http://bulletin.eatcs.org/index.php/beatcs/article/view/539/532)

## 此状态机非彼状态机
- 整个算法/系统是一个状态机，而不是某个进程是个状态机。
- 状态机的状态变化需要符合Properity约束

## State vs Behaviour
## Behaviour
-  状态变更，组成的序列

## State predicate vs Behavior property
- State predicate： 每个状态需要满足的条件，例如类型，某些变量之间的关系，也经常称为Invariance。
- Behavior property: 不是看某个状态，而是整个序列需要满足的条件。例如Init/\[]Next，Liveness, Fairness，都不是单个状态的属性。

## TLA的spec里面一些不容易理解的地方
### 状态变更描述比较麻烦
- 不是像我们写代码一样，修改某个或者某几个变量就行
- 状态变更实际是也是赋值，某些变量还是旧值，某些是新值，所以全部都得列出来。这样最主要是Next及相关步骤看起来一般比较复杂。
- 为什么这样？ 因为Lamport认为描述的每个系统类似于一个宇宙，不能只描述一部分。另外，需要判断每个值满足的条件(State Predicate，返回 TRUE/FALSE)。
- 以下来自Lamport的文章 [If You’re Not Writing a Program, Don’t Use a Programming Language](http://bulletin.eatcs.org/index.php/beatcs/article/view/539/532)
> An execution of an algorithm is represented mathematically as a sequence of states, where a state is an assignment of values to variables. A sequence of states is called a behavior. 


## 为什么paxos的TLA+ spec那么简单？
- 对比Raft的TAL+ spec，发现 paxos的内容非常少;
- 实际是Lamport主要关注算法的Correctness，而不是Liveness/Performance。在"The TLA+ book"里面，也提到以Correctness为主。
- 虽然在"paxos made simple"一文中描述了有leader大致怎么做，但是没有作为重点。因为他认为有没有Leader都一样是正确的，有了leader只要遵循基本协议，也是正确的。这个导致很多人到现在仍然认为paxos没有leader。


## TLA+ spec这么复杂，我的代码上万行，怎么验证？
- TLA+主要验证重要算法和模型，尤其是那些需要上帝视角的算法；
- 并发是典型的适合用TLA+做验证的，但是其他算法也可以。
