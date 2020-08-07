# 用串行化状态机描述分布式系统？总结下Lamport分布式理论的基础

# 0. 概要

本文把Lamport关于状态机的几篇文章串起来，以及这些文章间的关系。包括如何把分布式计算中并发的 event 顺序化(Total Ordering )并用状态机描述[1]；然后介绍下基于状态机和不变式的强归纳法证明[2]。

状态机贯穿了Lamport的大量研究。例如，“Time, Clocks"一文就是在写状态机(见下文)；Paxos/FastPaxos的归纳法推导基于状态机、不变式和强归纳法；Lamport 近年来集中精力做的 TLA+的形式化验证是基于状态机模型；"Distributed Snapshot"一文的有效性证明也基于状态机。但是大部分读者都忽略了状态机的重要性，更没有注意到，Lamport的分布式理论的基础，就是把**整个分布式计算，描述成了一个串行化状态机(**sequential state machine**)**。

为什么用状态机描述不同的计算？按照Lamport的观点，包括：

1) 大部分计算都可以用状态机来描述，无论是一段代码、一个分布式算法还是图灵机，也不论是用何种语言来描述的；

2) 状态机的本质是数学，且只使用了简单的数学模型(集合、逻辑运算等)，通过数学更容易看到问题的本质，发现共通的东西，而大部分人沉迷于某种语言的特点，而忽视了问题的本身。注意，这里并不是说实现不重要，而是说在讨论原理性、正确性问题时，更需要用数学方法，在解决原理性问题后，具体语言和实现的方式就变得很重要。

Lamport在自己的主页上说，"Time, Clocks" [1]是他的文章中被引用最多的一篇，但是**他几乎没遇到谁明白这篇文章是在写状态机**，而他写此文恰恰就是为了探讨分布式状态机。摘录一段[来自这里](http://lamport.azurewebsites.net/pubs/pubs.html#time-clocks)：

> A distributed system can be described as a particular **sequential state machine** that is implemented with a network of processors. The ability to totally order the input requests leads immediately to an algorithm to implement an arbitrary state machine by a network of processors, and hence to implement any distributed system. So, **I wrote this paper, which is about how to implement an arbitrary distributed state machine.** As an illustration, I used the simplest example of a distributed system I could think of--a distributed mutual exclusion algorithm. 
>
>This is my most often cited paper. Many computer scientists claim to have read it. **But I have rarely encountered anyone who was aware that the paper said anything about state machines.** People seem to think that it is about either the causality relation on events in a distributed system, or the distributed mutual exclusion problem. People have insisted that there is nothing about state machines in the paper. I've even had to go back and reread it to convince myself that I really did remember what I had written. 



个人对Lamport一些理论间的关系，总结如下：

[在这里画的图](https://app.lucidchart.com/documents/edit/191d2421-6e8c-4233-ab5d-563d1c65875d/0_0) (ppt)





# 1. 计算和状态机

**简单来说**：一个计算过程可以看成一系列的状态变化/步骤，称为一个行为(Behavior)。一个状态机由初始状态集合和行为集合构成。分布式系统也可以看出一个计算或者一个状态机，只不过是由多个节点/进程实现的。

**形式化描述**：状态机可以从以下几个方面来描述：状态集合 $ \mathcal{S}$ ，初始状态集合 $ \mathcal{L}$ 和$ \mathcal{S}$ 上的Next-State  关系 $ \mathcal{N}$ 。其中 $ \mathcal{L} \subseteq  \mathcal{S}$ ，  $ \mathcal{N} \subseteq  \mathcal{S} \times \mathcal{S}$ 。  它产生各种行为，每个行为可以表示成 $s_1 \rightarrow s_2 \rightarrow s_3...$ 的形式，并且满足：
$$
\begin{split}
&S1. \quad s_1  \in \mathcal{I} \\
&S2. \quad \forall i,  <s_i, s_{i+1}>  \in \mathcal{N}\\
&S3. 如果一个行为是有限的，那么: 它终结于状态 s 且不存在某个状态t，<s,t>\in\mathcal{N}\\
\end{split}
$$

其中，$<s_i, s_{i+1}>$表示从状态 $s_i$ 转变到状态 $s_{i+1}$。如果一个状态机的 next-state 关系 $\mathcal{N}$是个函数，即对于任意状态 $s$，只有一个状态$t$，满足$<s, t> \in \mathcal{N}$，则该状态机的是确定性的(Deterministic)。非确定性的则是允许从一个状态转变为多个状态。

简单来说，可以把 $ \mathcal{N}$ 理解成输入和输出都属于$ \mathcal{S}$ 的动作。

总之，按照Lamport的观点，**计算/行为才是本质，而不是语言或者形式**。



# 2. 如何把整个分布式计算看成一个状态机？

Behavior 分为有限和无限的，通常讨论的计算行为都是有限的，都会正常结束或者死锁。但是有些行为是无限的，比如一台冯诺依曼计算机，把它看成个状态机，则状态可以认为是无限的。

## 2.1 状态机行为的串行性 vs 分布式计算的并行性

虽然状态机的行为是个集合，即允许有很多种行为，但是在每一次运行过程，是按照某一个Bahavior 中的状态序列在一步一步顺序变化的。但是如果考虑一个多节点的分布式计算，多个节点是可以并行执行的，是否可以对应到串行化的状态机行为上？

简单来说，分布式计算中，只有少数 event 之间是真的有因果关系的(Partial Order，有时称为偏序/部分有序)，且是确定的。而大部分事件间的顺序并不重要(即使在物理上确实有先后)，在保持因果关系的前提下，可以把所有的 event 看成一个顺序化的序列，相当于给所有的 event 做了个排序，这个顺序被称为Total Order。



## 2.2 如何把分布式系统变成串行的状态机？ 

狭义相对论告诉我们，不存在一个不变的时空中事件的总顺序，不同的观察者可能就两个事件谁先发生产生分歧。但是部分顺序是存在的，对于有因果关系的事件，不同观察者观察到的顺序都相同。

事实上，从狭义相对论的角度，发生在不同地点的两个事件，同时性是相对的，会因惯性参考系的不同而不同。在某个观察者看来是同时发生的事件，对另一个作相对运动的观察者来说也许不是同时发生的；反之亦然。不同观测者看到的无因果关系的事件间顺序可能是不同的。但是对于任何观察者来说，**时间不会倒流，因果关系不会颠倒**。

具有因果关系的各个事件间本来就是串行的，在保持因果关系的前提下，把其他**无因果关系的事件按照任意顺序排序**，都可以变成一个**全序(即全部有序)**，这个全序就可以对应到一个行为。一个部分序对应的全序可能有多种，但是它们执行的结果是相同的。

### 2.2.1 举个生活中的例子

假设小明和小华想把他们周末某一天的生活记录下来，做成一个短视频。他们各自用手机自拍了一些镜头，让你负责剪辑，做成一个短视频。在剪辑过程中，哪些顺序是不能随便改变的？哪些是无所谓的？

假设短视频包括的画面如下：

1. 小明和小华早起后各自刷牙洗脸、下楼(假设他们住在不同的房子里，不用抢洗手间)；
2. 小明和小华一起坐西郊观光线去香山公园；
3. 他们一起在公园门口各买了一个山东煎饼；
4. 他们在香炉峰、双清别墅各自拍照；
6. 他们一起坐西郊观光线回家；
7. 他们回家后各自发朋友圈。

如果不考虑倒叙，部分画面的顺序是不能调整的，而部分是可以的。比如： 

- 小明和小华的刷牙顺序，哪个先放？ 无所谓，可调整。
- 小明刷牙在小华洗脸，哪个先放？ 无所谓，可调整。
- 先放小华在公园拍照，然后再放小明在家洗脸，那就有点不合逻辑了，因为它们一起坐车去的公园。
- 先放小明在公园吃煎饼，再放他刷牙？ 也不合逻辑。  

显然，你可以通过合理的剪辑，把小明和小华一天的生活，做成一个看起来不穿帮的小视频，每一帧代表一个event，构成了一个全序关系。甚至本来小明比小华刷牙更早，但是你剪辑后，小华刷牙的画面在前面，却没有任何问题。

明明是两个独立的人，看起来完全并发，为什么把他两的部分生活画面按照某个顺序剪辑出来，即使有些被颠倒顺序，看起来却没有穿帮，好像很合理呢？而有些画面顺序又不能调整？ 这就要回到 Lamport 的paper的关键概念： Partial Order 和 Total Order。      

### 2.2.2 Partial Order 和 Total Order

Partial order (偏序关系)具**有非对称、传递性和反自反性**。

而 Total Order(全序) 是指给所有事件都排个顺序。这个顺序不一定跟物理发生顺序相同，但是不违背逻辑(因果关系)。

比如，观众在观看上述纪录片时，看到了小华洗脸发生在小明洗脸之前，但是物理上不一定如此，这依赖于如何剪辑影片。我们把最终剪辑的短视频中的每一幕看成一个 event，那么观众看的这个短视频，每一幕之间实际上都是有序的，这就是一个全序。

不过这里有个要求，即不能把物理时间在每一幕都展示，如果每一幕都带着物理时间，那么可能就出现另外一个问题了。剪辑时得非常小心，免得让观众感觉时钟一会正着走，一会反着走。



为什么有些画面不能调整顺序？因为有偏序关系，包括两种：

- **每个人自己完成的事情间的顺序**，比如，小明先刷牙后洗脸，然后打电话约小华，游览完成才发朋友圈。如果纪录片中小明先发了在公园玩朋友圈，后坐车去公园，就穿帮了。
- **交互或传递性引起的因果关系**。不同的人，所做的事情间有些也有顺序，这些顺序是因为他们之间的某种**交互**引起的。比如，小明跟小华一起坐车去公园这一刻，就是一个明确的时间点，它让二者之间建立了一个交互，小明在公园拍照，不可能在小华刷牙之前，因为二者一起坐车去的公园。 ""小华刷牙"" $\rightarrow$  "二人坐车去公园" $\rightarrow$ "小明在公园拍照"。所以有 ""小华刷牙"   $\rightarrow$  "小明在公园拍照""。在分布式系统中，**交互一般是消息传递**。

  

为什么需要用状态序列去描述？

- 可以用数学去描述过程，并可以做适当的事件顺序调整，例如“分布式快照”一文正确性证明过程，就依赖于可以将一个状态序列S1，经过不违背偏序的变换，变成序列S2，从而证明快照是个可达的合法状态，即使它不是真的在某个时刻存在过；
- 把系统看成状态序列后，可以使用基于不变式的归纳法证明系统特性。直接证明一个运行了很久的分布式系统的状态满足某个式子是不是不可能？但是如果把分布式系统看成一个事件序列，按照归纳法来证明就变的可能。
- 在做形式化验证时，可以穷举状态序列，去验证每个状态是否都满足某个预设的条件(不变式)，从而验证算法或者协议的正确性。例如，验证分布式cache算法会不会出现同一个对象在两个cache有不同的版本且都可访问。如果没有状态序列的概念，完全看成杂乱无章的变化，连穷举都不可能。

  

### 2.2.3 怎么确定一个Total Order?

文章[1]中提到结合逻辑时间和host id，来确定Total Order：

- 首先使用事件Logical Time，作为确定Partial Order的依据；
- 对于Logical Time相同的event，根据 host id 来排序(host id 预先分配)。



# 3. 基于串行化状态的不变式和归纳法

回忆下我们上学时学习的归纳法，它实际上就是个串行化过程，为了证明一个谓词在n =k时成立，往往依赖于n = k-1时成立，或者要求n =k-1和n=k-2时都成立。这就有个前提，即串行化考虑 n 的不同取值，而不能并发。



## 3.1 基本概念和过程 

如果一个状态机的每一个可达状态都满足某个谓词，则称该谓词是状态机的一个不变式(Invariant)。证明过程就是归纳法。

一个状态变化谓词(Transition Predicate) $T$，当且仅当  $Inv \land T \implies Inv'$ 成立时，称其$T$ 保持不变式 $Inv$ 成立，其中$Inv'$表示执行状态变化后，新状态还满足式子 $Inv$。也就是说，如果当前状态 $s$ 满足$Inv$，并且状态变化 $<s, t>$ 满足 T，那么状态 $t$ 也满足$Inv$。这里的 $s$ 和 $t$ 是两个具体的状态，$<s,t>$只是一次变化，下面是把它们泛化描述。

如果一个状态机在初始状态($Init$) 满足$Inv$，且其 $NextState$ 函数保证 $Inv$  成立，那么 $Inv$ 就是这个状态机的不变式。也被称为状态机的**归纳不变式**($Inductive \space Invariant$)。在证明状态机满足某个不变式 $P$ (称为目标不变式) 时，可能先找到另外一个更苛刻的不变式$Inv$，然后证明$Inv$是状态机的归纳不变式。再结合$Inv \implies P$，即可证明$P$是状态机的不变式。注意，借助$Inv$，是因为不能直接证明 $ P \land Next \implies P'$。简单来说，归纳法证明某个状态机满足 $P$ 可以用下面的式子表示：
$$
\begin{split}
&I1.\quad Init \implies Inv\\
&I2.\quad Inv \land Next \implies Inv'\\
&I3.\quad Inv \implies P
\end{split}
$$

## 3.2 在Paxos正确性证明中的应用

参考之前我的一篇文章：[Paxos的正确性证明](https://zhuanlan.zhihu.com/p/104463008)，本质上也是上述的不变式归纳方法。具体来说，Paxos的Voting过程保证的Inv是：

$Inv \triangleq VotesSafe \land OneVote$

其中：

$VotesSafe \triangleq \forall a \in Acceptor, b \in Ballot, v \in Value : VotedFor(a, b, v) => SafeAt(b, v)$

$ OneVote \triangleq   \forall a \in Acceptor, b \in Ballot, v, w \in Value : VotedFor(a, b, v) \land VotedFor(a, b, w) \implies (v = w)$



Paxos 的 Next-State 即为 Phase 1a, 1b, 2a, 2b等。



# 4. FAQ

## FAQ 1.  Total Order 的意义是什么？

从[1] 中我们可以看出，给每个用户请求排个序，让所有节点按照这个顺序得到统一的优先级，并按照统一的优先级做一致的决定，也是一个用途。

但是在很多时候，获得 Total Order 不是目的。从归纳法证明正确性的角度，基本方法是：

1） 先确定当 $n=0$ 是某个式子成立；

2） 假设当 $n<=k-1$时某个式子成立，证明$n=k$时也成立。

如果我们不能将其串行化，这个归纳法模型是什么呢？从数学的角度就很难说清楚。因此，证明有意义的Total Ordering存在是能进行归纳法证明的前提条件。



## FAQ 2: Total Order既然可以有很多个，在归纳法证明时，选哪个?

在证明过程中，并不需要某一个具体的 Total Order。只要确定 $Init$ 和 $Next$ 分别满足和保证什么，能得出相应结论即可。如果$Inv$ 是状态机的归纳不变式，则无论哪个符合$Next$ 函数的 Total Order都是满足的。



[1]  **Time, Clocks and the Ordering of Events in a Distributed System**, Lamport, *Communications of the ACM 21*, 7  (July 1978), 558-565

[2]**Computation and State Machines**,  https://lamport.azurewebsites.net/pubs/state-machine.pdf

