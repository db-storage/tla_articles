# 偏序、全序和状态机: Lamport 分布式理论基础

# 1. 概要

本文把Lamport关于状态机的几篇文章串起来。包括：偏序和全序关系；如何把分布式计算(Total Ordering)用串行化状态机描述[1]；然后介绍基于状态机和不变式的强归纳法证明[2]。

之前我曾经写过几篇博客介绍Lamport的一些经典paper，包括分布式快照和Paxos的正确性证明。后来偶然在Lamport的主页上看到关于一些状态机的论述，才意识到状态机理论是他的系列理论的基础：无论单机系统还是分布式系统，都是可以理解成一个串行化状态机的不同实现。Lamport在自己的主页上说，"Time, Clocks" [1]是他的文章中被引用最多的一篇，但是**他几乎没遇到谁明白这篇文章是在写状态机**，而他的初衷恰恰就是为了探讨分布式状态机。摘录一段[3]：

> A **distributed system** can be described as a particular **sequential state machine** that is implemented with a network of processors. The ability to totally order the input requests leads immediately to an algorithm to implement an arbitrary state machine by a network of processors, and hence to implement any distributed system. So, **I wrote this paper, which is about how to implement an arbitrary distributed state machine.** As an illustration, I used the simplest example of a distributed system I could think of--a distributed mutual exclusion algorithm. 
>
> This is my most often cited paper. Many computer scientists claim to have read it. **But I have rarely encountered anyone who was aware that the paper said anything about state machines.** People seem to think that it is about either the causality relation on events in a distributed system, or the distributed mutual exclusion problem. People have insisted that there is nothing about state machines in the paper. I've even had to go back and reread it to convince myself that I really did remember what I had written. 



状态机贯穿了 Lamport 的大量研究。例如，Paxos/FastPaxos的归纳法推导基于状态机、不变式和强归纳法；Lamport 近年大力推广的形式化验证( TLA+)是基于状态机模型；"Distributed Snapshot"一文的正确性推导也基于状态机理论。但是大部分读者都忽略了状态机的重要性，更没有注意到，Lamport的分布式理论的基础，就是把**整个分布式计算，描述成了一个串行化状态机(**sequential state machine**)**。

为什么要用状态机描述来不同的计算？按照 Lamport 的观点，包括：

1) 大部分计算都可以用状态机来描述，无论是一段代码、一个分布式算法还是图灵机，也不论是用何种语言来描述的；

2) 状态机的本质是数学，且只使用了简单的数学模型(集合、逻辑运算等)，通过数学更容易看到问题的本质，发现共通的东西。很多时候我们沉迷于某种编程语言的特点，而忽视了问题的本身。注意，这里并不是说实现不重要，而是说在讨论原理性、正确性问题时，更需要用数学方法，在解决原理性问题后，具体语言和实现的方式就变得很重要。



个人对Lamport一些理论间的关系，总结如下：

[在这里画的图](https://app.lucidchart.com/documents/edit/191d2421-6e8c-4233-ab5d-563d1c65875d/0_0) (ppt)



# 2. 计算和状态机

**简单来说**：一次计算过程可以看成一系列的状态变化，称为一个行为(Behavior)。一个状态机由初始状态集合和行为集合构成。分布式计算也是一个状态机。

**形式化描述**：包括状态集合 $ \mathcal{S}$ ，初始状态集合 $ \mathcal{L}$ 和$ \mathcal{S}$ 上的Next-State  关系 $ \mathcal{N}$ 。其中 $ \mathcal{L} \subseteq  \mathcal{S}$ ，  $ \mathcal{N} \subseteq  \mathcal{S} \times \mathcal{S}$ 。  它产生各种行为，每个行为可以表示成 $s_1 \rightarrow s_2 \rightarrow s_3...$ 的形式，并且满足：
$$
\begin{split}
&S1. \quad s_1  \in \mathcal{I} \\
&S2. \quad \forall i,  <s_i, s_{i+1}>  \in \mathcal{N}\\
&S3. 如果一个行为是有限的，那么: 它终结于状态 s 且不存在某个状态t，<s,t>\in\mathcal{N}\\
\end{split}
$$

其中，$<s_i, s_{i+1}>$表示从状态 $s_i$ 转变到状态 $s_{i+1}$。如果一个状态机的 NestState 关系 $\mathcal{N}$ 是个函数，即对于任意状态 $s$，只有一个状态$t$，满足$<s, t> \in \mathcal{N}$，则该状态机的是确定性的(Deterministic)。非确定性的则是允许从一个状态转变为多个候选状态。

简单来说，可以把 $ \mathcal{N}$ 理解成输入和输出都属于$ \mathcal{S}$ 的动作。



# 3. 如何把整个分布式计算看成一个状态机？

计算行为可以分为有限的和无限的两种，通常讨论的计算行为都是有限的，都会正常结束或者死锁。但是有些行为是无限的，比如一台冯诺依曼计算机，把它看成个状态机，则状态可以认为是无限的。

## 3.1 状态机行为的串行性 vs 分布式计算的并行性

虽然状态机的行为是个集合，即允许有很多种行为，但是在每一次运行过程，是按照某一个行为的状态序列一步步顺序变化的。但是如果考虑一个多节点的分布式计算过程，多个节点是可以并行执行的，它如何对应到串行化的状态机行为上？

简单来说，分布式计算中，只有少数 event 之间是真的有因果关系的(Partial Order/偏序关系)，且是确定的。而很多event 间的顺序并不重要(即使在物理上确实有先后)，在保持因果关系的前提下，把无因果关系的 event 做排序后，整个运算过程就可以看成一个串行的序列。这也相当于给所有的 event 做了个排序，这个顺序被称为Total Order/全部有序。



## 3.2 如何把分布式系统变成串行的状态机？ 

狭义相对论说，不存在一个不变的时空中事件的总顺序，不同的观察者可能就两个事件谁先发生产生分歧。但是部分顺序是存在的，对于有因果关系的事件，不同观察者观察到的顺序都相同。

事实上，从狭义相对论的角度，发生在不同地点的两个事件，同时性是相对的，会因惯性参考系的不同而不同。在某个观察者看来是同时发生的事件，对另一个作相对运动的观察者来说也许不是同时发生的；反之亦然。不同观测者看到的无因果关系的事件间顺序可能是不同的。但是对于任何观察者来说，**时间不会倒流，因果关系不会被颠倒**。

具有因果关系的各个事件间本来就是串行的，在保持因果序的前提下，把其他**无因果关系的事件按照任意顺序排序**，即可以变成一个**全序(即全部有序)**，这个全序就可以对应到一个行为。一个因果序对应的全序可能有多种。

### 3.2.1 来自生活中的例子

假设小明和小华想把他们周末某一天的生活记录下来，做成一个短视频。他们各自用手机自拍了一些镜头，让你负责剪辑，做成一个短视频。在剪辑过程中，哪些顺序是不能变的？哪些是可以变的？

假设短视频包括的画面如下：

1. 小明和小华早起后各自刷牙洗脸、下楼(假设他们住在不同的房子里，不用抢洗手间)；
2. 两人一起坐西郊观光线去香山公园；
3. 两人在公园门口各买了一个山东煎饼；
4. 两人在香炉峰、双清别墅各自拍照；
6. 两人一起坐西郊观光线回家；
7. 两人回家后各自发朋友圈。

如果不考虑倒叙，部分画面的顺序是不能调整的，而部分是可以的。比如： 

- 小明和小华的刷牙顺序，哪个先放？ 无所谓，可调整。
- 小明刷牙与小华洗脸，哪个先放？ 无所谓，可调整。
- 先放小华在公园拍照，然后再放小明在家洗脸，那就有点不合逻辑了，因为它们一起坐车去的公园。
- 先放小明在公园吃煎饼，再放他刷牙？ 也不合逻辑。  

显然，你可以通过合理的剪辑，把小明和小华一天的生活，做成一个看起来不穿帮的小视频，每一帧代表一个event，构成了一个全序关系。甚至本来小明比小华刷牙更早，但是你剪辑后，小华刷牙的画面在前面，却没有任何问题。

明明是两个独立的人，看起来完全并发，为什么把他两的部分生活画面按照某个顺序剪辑出来，即使有些被颠倒顺序，看起来却没有穿帮，好像很合理呢？而有些画面顺序又不能调整？ 这就要回到 Lamport 的paper的关键概念： Partial Order 和 Total Order。      

### 3.2.2 Partial Order 和 Total Order

Partial order (偏序关系)具**有非对称、传递性和反自反性**。

而 Total Order(全序) 是指所有事件之间都有顺序。这个顺序不一定跟物理发生顺序相同，但是不违背因果关系。

比如，观众在观看上述纪录片时，看到了小华洗脸发生在小明洗脸之前，但是物理上不一定如此，这依赖于如何剪辑影片。我们把最终剪辑的短视频中的每一幕看成一个 event，那么观众看的这个短视频，每一幕之间实际上都是有序的，这就是一个全序。

不过这里有个要求，即不能把物理时间在每一幕都展示，如果每一幕都带着物理时间，那么可能就出现另外一个问题了。剪辑时得非常小心，免得让观众感觉时钟一会正着走，一会反着走。



为什么有些画面不能调整顺序？因为它们之间有因果关系，包括两种：

- **一个人的多个动作间的因果序**，比如，小明先刷牙后洗脸，然后打电话约小华，游览完成才发朋友圈。如果纪录片中小明先发了在公园玩朋友圈，后坐车去公园，就穿帮了。
- **交互或传递性引起的因果序**。不同的人，所做的事情间可能有因果关系，这是因为他们之间的某种**交互**引起的。比如，小明跟小华一起坐车去公园这一刻，就是一个明确的时间点，它让二者之间建立了一个交互，小明在公园拍照，不可能在小华刷牙之前，因为二者一起坐车去的公园。如果我们用箭头$\rightarrow$ 表示因果关系，那么有 "小华刷牙" $\rightarrow$  "二人坐车去公园" $\rightarrow$ "小明在公园拍照"。所以按照传递性法则，有 ""小华刷牙"   $\rightarrow$  "小明在公园拍照""。在分布式系统中，**交互一般是消息传递**。

  

### 3.2.3 怎么确定一个Total Order?

文章 [1] 中提到结合逻辑时间和host id，可以确定Total Order：

- 首先使用事件的Logical Time，作为确定Partial Order的第一依据；
- 对于Logical Time 相同的 event (他们之间没有因果关系)，根据 host id 来定一个顺序(host id 预先产生和分配，只要是确定的、不重叠的就可以)。



# 4. 状态机的不变式和归纳法证明

​    回忆下我们上学时学习的归纳法，它实际上就是个串行化过程，为了证明一个谓词在$n =k$时成立，往往依赖于该谓词$n = k-1$时成立，或者要求$n =k-1$和$n=k-2$时都成立。这就有个前提，即串行化地考虑 $n$ 的不同取值，而不能并发。



## 4.1 基本概念和过程 

如果一个状态机的每一个可达状态都满足某个谓词，则称该谓词是状态机的一个不变式(Invariant)。证明过程就是归纳法。

下面部分会用到几个**数学符号**，主要有： $\land$： 并且；$\lor$：或者； $\implies$：蕴含。

一个状态变化谓词(Transition Predicate) $T$，当且仅当  $Inv \land T \implies Inv'$ 成立时，称其$T$ 保持不变式 $Inv$ 成立。这个式子的含义：在当前状态下，$Inv$成立，执行$T$达到的新状态，也满足$Inv$。$Inv'$ 表示执行变化$T$后，新状态还满足式子 $Inv$。下面是把它们泛化描述。

如果一个状态机在初始状态($Init$) 满足$Inv$，且其 $NextState$ 函数保证变化后 $Inv$  成立，那么 $Inv$ 就是这个状态机的不变式。也被称为状态机的**归纳不变式**($Inductive \space Invariant$)。在证明状态机满足某个不变式 $P$ (称为目标不变式) 时，可能先找到另外一个更苛刻的不变式$Inv$，然后证明$Inv$是状态机的归纳不变式。再结合$Inv \implies P$，即可证明$P$是状态机的不变式。注意，借助$Inv$，是因为不能直接证明 $ P \land Next \implies P'$。简单来说，归纳法证明某个状态机满足 $P$ 可以用下面的式子表示：
$$
\begin{split}
&I1.\quad Init \implies Inv\\
&I2.\quad Inv \land Next \implies Inv'\\
&I3.\quad Inv \implies P
\end{split}
$$

注意，NextState函数往往是根据不同的当前状态，作出不同的动作。比如下面GCD的例子。

## 4.2 一个简单的例子

以的求最大公约数的Euclid方法为例。GCD 实现的形式化验证spec如下([来自这里](https://tla.msr-inria.inria.fr/tlaps/content/Documentation/Tutorial/The_example.html))。这个Spec中，NextState函数(对应定义为$Next$) 有 $x<y$ 和 $x>y$ 两个分支，虽然两个分支是类似的。当$x=y$时，没有下一步动作，x或者y就是结果。


$$
\begin{split}
&EXTENDS \quad Integer\\
&p | q \triangleq \exists d \in 1..q : q = p * d\\
&Divisors(q) \triangleq {d \in 1..q : d | q}\\
&Maximum(S) \triangleq CHOOSE \quad x \in S : \forall y \in S : x >= y\\
&GCD(p,q) \triangleq Maximum(Divisors(p) \cap Divisors(q))\\
&Number \triangleq Nat 	\setminus {0}\\
&CONSTANTS \quad M, N \\
&VARIABLES \quad x, y \\
&Init \triangleq (x = M) \land (y = N) \\
&Next \triangleq \\ 
&\lor \quad \land x < y \\
&  \qquad \land y' = y - x\\
&  \qquad \land x' = x\\
&   \or \quad \and y < x\\
&  \qquad \land  x' = x - y\\
&  \qquad \land y' = y\\
&Spec \triangleq Init \land \Box [Next]_<x,y>\\
&ResultCorrect \triangleq (x = y) => x = GCD(M, N)\\
&THEOREM Correctness \triangleq Spec => \Box ResultCorrect\\
\end{split}
$$


对于上面的计算，不变式是：$Inv \triangleq GCD(M,N) = GCD(x,y) $。按照归纳法，基本过程及推导：

1） $Init \implies Inv$

​    由于Init时，$x=M \land y = N$, $Inv$ 显然成立。

2) $Inv \land Next \implies Inv$

​    假设当前状态满足Inv，假设$GCD(x,y)=GCD(M,N)=g$,即 $\exists g \in Numbers:  x=m \times g \land y = n \times g$。

​    如果$x>y$，那么 $x'=x-y=(m-n)\times g$，所以 $x'|g \land y|g$  成立。如果 $g$ 不是 $GCD(x', y)$，即$\exist h \in Numbers: h>g \land x'|h \land y|h$，那么根据 $x'= x-y$ 可以得出，$x|h \land y|h$，与 $GCD(x,y) = g$ 矛盾。所以，$GCD(x',y) = GCD(x,y) =GCD(M, N)$，新状态仍然满足$Inv$。$y>x$ 与 $x>y$ 实际上是类似的。

3) 在状态机执行结束时，$ x=y=GCD(x,y)=GCD(M,N)$。



## 4.3 抽象粒度和原子性

在上述的求最大公约数的例子中，无论是 $x>y$ 还是$y>x$ 分支，判断和修改都是一个原子操作。在这种递归实现中，不涉及并发问题，所以比较简单。

如果我们考虑一个分布式系统，那么Next操作的步骤是什么样的抽象粒度，就是一个重要问题。如果抽象粒度过隙，则让计算过程的描述特别复杂；如果抽象粒度过粗，则抽象出来的步骤可能不是原子的。比如：

1）发送一个网络消息的过程，实际上包括网络协议各层的多个子操作，从指令的层面，并不是原子的。但是我们描述一个分布式系统时，一般会把发送消息当作一个步骤，不会进一步细化。

2) 以 Paxos 的两个阶段为例，一般认为Phase1a,1b, 2a, 2b 都是原子操作，而没有进一步细化。例如，Phase1a可以包含判断当前状态、持久化承诺等细化步骤，是一个比较耗时的过程。这个粒度的抽象，也对实现提出了要求，比如一个Acceptor 执行Phase1b的过程中，不能处理其他的Phase1a/Phase2a消息，必须用锁等机制来保证原子性。



## 4.4 在Paxos正确性证明中的应用

参考之前我的一篇文章：[Paxos的正确性证明](https://zhuanlan.zhihu.com/p/104463008)，也是基于不变式归纳法。



# 5. FAQ

## FAQ 1.  Total Order 的意义是什么？

从[1] 中我们可以看出，一旦有了一个total order，就可以把单机系统和分布式系统看成同一个串行化状态机的不同实现。例如，单机很容易做一个请求排队系统，但是分布式系统怎么做呢？如果有了total order，这样可以让一个分布式系统像单机系统一样提供一个排队服务，且无需时钟强同步。但是在很多时候，不需要给每个用户请求做全局有序的排队，获得 Total Order 不是目的，但是对于我们理解一个系统的正确性却是必要的。从归纳法证明正确性的角度，基本方法是：

1） 先确定当 $n=0$ 是某个式子成立；

2） 证明如果当 $n<=k-1$时某个式子成立，$n=k$ 时也成立。

如果我们不能将其串行化，这个归纳法模型是什么呢？从数学的角度就很难说清楚。因此，证明有意义的Total Ordering存在是能进行归纳法证明的前提条件。



## FAQ 2: Total Order可以有多个，在归纳法证明时，选哪个?

在证明过程中，并不需要某一个具体的 Total Order。只要确定 $Init$ 和 $Next$ 分别满足和保证什么，能得出相应结论即可。如果$Inv$ 是状态机的归纳不变式，则无论哪个满足因果关系的 Total Order都是一样的。



参考：

[1]  **Time, Clocks and the Ordering of Events in a Distributed System**, Lamport, *Communications of the ACM 21*, 7  (July 1978), 558-565

[2] **Computation and State Machines**,  https://lamport.azurewebsites.net/pubs/state-machine.pdf

[3] Lamport个人主页：https://lamport.azurewebsites.net/pubs/pubs.html

