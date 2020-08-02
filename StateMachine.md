# N个节点的分布式计算用一个状态机描述？串一下Lampor关于状态机的几篇文章

# 0. 概要

本文把Lamport关于状态机的几篇文章串起来，以及这些文章间的关系。包括如何把分布式计算中并发的event顺序化(Total Ordering )并用状态机描述[1]；然后介绍下基于状态机和不变式的强归纳法证明[2]。

状态机贯穿了Lamport的大量研究。例如，Paxos/FastPaxos的归纳法推导基于状态机、不变式和强归纳法；TLA+的验证基于状态机模型和 Model Checker 运行过程中对不变式的验证，"Distributed Snapshot"的有效性证明，也基于状态机。但是大部分读者都忽略了状态机的重要性，更没有注意到，Lamport的分布式理论的基础，就是把**整个分布式计算，描述成了一个状态机**。

为什么用状态机描述不同的计算？按照Lamport的观点，包括：1) 大部分计算都可以用状态机来描述，无论是一段代码、一个分布式算法还是图灵机，无论它是用何种语言来描述的；2) 状态机的本质是数学，且只使用了简单的数学模型(集合、逻辑运算等)，通过数学更容易看到问题的本质，发现共通的东西，而大部分人沉迷于某种语言的特点，而忽视了问题的本身。注意，理解问题本质并不是说实现不重要，而是说在讨论原理性、正确性问题时，更需要用数学方法，在解决原理性问题后，具体语言和实现的方式就变得很重要。

Lamport在自己的主页上说，"Time, Clocks" [1]是他的文章中被引用最多的一篇，但是**他几乎没遇到谁明白这篇文章是在写状态机**，而他写此文恰恰就是为了探讨分布式状态机。[原文链接](http://lamport.azurewebsites.net/pubs/pubs.html#time-clocks)

> A distributed system can be described as a particular sequential state machine that is implemented with a network of processors. The ability to totally order the input requests leads immediately to an algorithm to implement an arbitrary state machine by a network of processors, and hence to implement any distributed system. So, **I wrote this paper, which is about how to implement an arbitrary distributed state machine.** As an illustration, I used the simplest example of a distributed system I could think of--a distributed mutual exclusion algorithm. 
>
>This is my most often cited paper. Many computer scientists claim to have read it. **But I have rarely encountered anyone who was aware that the paper said anything about state machines.** People seem to think that it is about either the causality relation on events in a distributed system, or the distributed mutual exclusion problem. People have insisted that there is nothing about state machines in the paper. I've even had to go back and reread it to convince myself that I really did remember what I had written. 



个人对Lamport一些理论间的关系，总结如下：

[在这里画的图](https://app.lucidchart.com/documents/edit/191d2421-6e8c-4233-ab5d-563d1c65875d/0_0) (ppt)





# 1. 计算和状态机

状态机可以从以下几个方面来描述：状态集合 $ \mathcal{S}$ ，初始状态集合 $ \mathcal{L}$ 和$ \mathcal{S}$ 上的next-state 关系 $ \mathcal{N}$ 。其中 $ \mathcal{L} \subseteq  \mathcal{S}$ ，  $ \mathcal{N} \subseteq  \mathcal{S} \times \mathcal{S}$ 。  它产生各种行为(behavior)，每个behavior可以表示成 $s_1 \rightarrow s_2 \rightarrow s_3...$ 的形式，并且满足：
$$
\begin{split}
&S1. \quad s_1  \in \mathcal{I} \\
&S2. \quad \forall i,  <s_i, s_{i+1}>  \in \mathcal{N}\\
&S3. 如果一个行为是有限的，那么它终结于状态s，且不存在<s,t>\in\mathcal{N}\\
\end{split}
$$

其中，$<s_i, s_{i+1}>$表示从状态$s_i$转变到状态$s_{i+1}$。如果一个状态机的是确定性的(deterministic)，如果它的next-state 关系 $\mathcal{N}$是个函数，即对于任意状态$s$，只有一个状态$t$，满足$<s, t> \in \mathcal{N}$。非确定性的则是允许从一个状态转变为多个状态。

简单来说，可以把 $ \mathcal{N}$ 理解成输入和输出都属于$ \mathcal{S}$ 的动作。

The purpose of this note is to indicate how computation is expressed with
state machines and how doing so can clarify the concepts underlying the
disparate languages for describing computations. 



For now, I take the simplest: a computation is a
sequence of steps, which I call a behavior.



There are three common choices
for what a step is, leading to three difierent kinds of behavior:



Figure 1 里面的三个C程序，看起来相近的，其实不是最近的，如果用状态机表示的计算来说。

**计算/行为才是本质，而不是语言或者形式**。



# 2. 如何把整个分布式计算看成一个状态机？

注意，行为分为有限和无限的。我们通常讨论的计算行为都是有限的，都会正常结束或者死锁。但是有些行为是无限的，比如一台冯诺依曼计算机，把它看成个状态机，则状态可以认为是无限的。

## 2.1 状态机行为的串行性 vs 分布式计算的并行性

观察状态机的执行过程，我们会发现，虽然状态机的行为是个集合，即允许有很多种行为，但是在每次运行过程中，是按照某一个Bahavior 中的状态序列在一步一步顺序变化的。但是如果考虑一个多节点的分布式计算，多个节点是可以并行执行的，如何对应到串行化的状态机行为上？

简单来说，分布式计算中，只有少数event之间是真的有顺序依赖关系的(Partial Ordering)，且是确定的。而大部分事件间的顺序并不重要，即使在物理上确实有先后，只要保证了那些确定性的Partial Order被保持，就可以把所有的并发event看成一个顺序化的event 序列，相当于给所有的event做了个排序，这个顺序被称为Total Order。



## 2.2 如何把分布式系统变成串行的状态机？ 

狭义相对论告诉我们，不存在一个不变的时空中事件的总顺序，不同的观察者可能就两个事件谁先发生产生分歧。但是部分顺序是存在的，对于有因果关系的事件，不同观察者观察到的顺序都相同。

事实上，从狭义相对论的角度，发生在不同地点的两个事件，同时性是相对的，会因惯性参考系的不同而不同。在某个观察者看来是同时发生的事件，对另一个作相对运动的观察者来说也许不是同时发生的；反之亦然。不同观测者看到的无因果关系的事件间顺序可能是不同的。但是对于任何观察者来说，**时间不会倒流，因果关系不会颠倒**。

具有因果关系的各个事件间本来就是串行的，在保持因果关系的前提下，把其他无因果关系的事件按照任意顺序排序，都可以变成一个全序(即全部有序)，这个全序就可以对应到一个状态机。一个部分序对应的全序可能有多种，但是它们执行的结果是相同的。

### 2.2.1 一个来自生活中的例子

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

Partial ordering 是指那些有因果关系的事件之间的顺序，不能修改。偏序关系具**有非对称、传递性和反自反性**。

而 Total Order(全序) 是指给所有事件都排个顺序。在分布式系统中，这并不容易，所以才有了Lamport的"Time, Clock"一文。

比如，小王在观看这个纪录片时，看到了小华洗脸发生在小明洗脸之前，但是事实上不一定如此，这依赖于如何剪辑影片。我们把最终剪辑的短视频中的每一幕看成一个 event，那么小王看的这个短视频，每一幕之间实际上都是有序的，这个顺序就是一个 Total Ordering。有逻辑依赖关系的event之间的顺序，必须在 total order 中被保持。

不过这里有个要求，即不能把物理时间在每一幕都展示，如果每一幕都带着物理时间，那么可能就出现另外一个问题了。剪辑时得非常小心，免得让小王感觉时钟一会正着走，一会反着走。这也是不赞成分布式系统依赖于物理时间的原因之一。



为什么有些画面不能调整顺序？因为有依赖关系，包括两种：

- **每个人自己完成的事情间的顺序**，比如，小明先刷牙后洗脸，然后打电话约小华，游览完成才发朋友圈。如果纪录片中小明先发朋友圈，后坐车去公园，就乱套了。
- **交互或传递性引起的因果关系**。不同的人，所做的事情间有些也有顺序，这些顺序是因为他们之间的某种交互引起的。比如，小明跟小华一起坐车去公园这一刻，就是一个明确的时间点，它让二者之间建立了一个交互，小明在公园拍照，不可能在小华刷牙之前，因为二者一起坐车去的公园。 ""小华刷牙"" $\rightarrow$  "二人坐车去公园" $\rightarrow$ "小明在公园拍照"。所以有 ""小华刷牙"   $\rightarrow$  "小明在公园拍照""。

 

1. Partial Order 是唯一且确定的。

2. Total Order 可以有多个，可以选择按照其中一个执行，结果相同。

    

为什么需要用状态序列去描述？

- 可以用数学去描述过程，并可以做适当的事件顺序调整，例如分布式快照一文正确性证明过程，就依赖于可以将一个状态序列S1，经过不违背Partial  Ordering的变换，变成快照状态S2，从而证明快照是个可达的合法状态，即使不是真的在某个时刻存在过；
- 基于不变式的归纳法证明，也是基于状态机理论。
- 在做形式化验证时，可以穷举状态序列，去验证每个状态序列是否违背了某个条件(一般是某个个不变式)，从而验证算法或者协议的正确性。例如，验证分布式cache算法会不会出现同一个对象在两个cache有不同的版本且都可访问。如果没有状态序列的概念，完全看成杂乱无章的变化，连穷举都不可能。

  

### 2.2.3 怎么确定一个total order?

- Logical time自身的值，作为Partial Order的依据；
- Logical time 相同的event，根据 host id 来排序(host id 预先分配)。



# 3. 不变式和归纳法证明

## 3.1 基本概念和过程 

如果一个状态机的每一个可达状态都满足某个谓词，则称该谓词是状态机的一个不变式(invariant)。

一个状态变化谓词(transition predicate) $T$，当且仅当  $Inv \land T \implies Inv'$ 成立时，称其$T$ 保持不变式 $Inv$ 成立，其中$Inv'$表示执行状态变化后，新状态还满足式子 $Inv$。也就是说，如果状态 $s$ 满足$Inv$，并且状态变化 $<s, t>$ 满足 T，那么状态 $t$ 也满足$Inv$。

如果一个状态机在初始状态($Init$) 满足$Inv$，且其 $Next-State$ 函数保持 $Inv$  成立，那么 $Inv$ 就是这个状态机的不变式。这个不变式也被称为状态机的**归纳不变式**($Inductive \space Invariant$)。在证明状态机满足某个不变式 $P$ (姑且称为目标不变式) 时，可能先找到另外一个更苛刻的谓词$Inv$，然后证明$Inv$是状态机的归纳不变式。再结合$Inv \implies P$，即可证明$P$是状态机的不变式。注意，借助$Inv$，是因为不能得出 $ P \land Next \implies P'$。简单来说，归纳法证明某个状态机满足 $P$ 可以用下面的式子表示：
$$
\begin{split}
&I1.\quad Init \implies Inv\\
&I2.\quad Inv \land Next \implies Inv'\\
&I3.\quad Inv \implies P
\end{split}
$$



## 3.2 Paxos的证明，如何对应到这个式子？



$Inv \triangleq VotesSafe \land OneValuePerBallot$

$VotesSafe \triangleq \forall a \in Acceptor, b \in Ballot, v \in Value : VotedFor(a, b, v) => SafeAt(b, v)$

$$
\begin{split}
\begin{aligned}
DidNotVoteAt(a, b) \triangleq \forall v \in Value : ~ VotedFor(a, b, v) \\
CannotVoteAt(a, b) \triangleq \land maxBal[a] > b \\
                      \land DidNotVoteAt(a, b)\\
NoneOtherChoosableAt(b, v) \triangleq \\
   \exists Q \in Quorum :  \forall a \in Q : VotedFor(a, b, v) \lor CannotVoteAt(a, b)\\
SafeAt(b, v) \triangleq \forall c \in 0..(b-1) : NoneOtherChoosableAt(c, v)\\
\end{aligned}
\end{split}
$$
$AllSafeAtZero \triangleq \forall v \in Value : SafeAt(0, v)$

$AllSafeAtZero \implies Inv$



### Init 时成立

$I1: Init \implies AllSafeAtZero$





### 对 Phase1a 成立



$Inv \land Phase1a  \implies Inv'$

修改的变量，不影响任何Inv的成立。

1) 没有产生任何的 $VotedFor(a, b, v)$；

2) 没有产生任何的(b, v)，不影响 $OneValuePerBallot$

由于没有改变任何 Acceptor 的状态，$VotesSafe$ 和$OneValuePerBallot$ 都不受影响。



### 对 Phase1b 成立

**要点：** 假设当前的ballot是b，执行的acceptor是$a$，对于任意已经存在的$<b_1, v_1>$，可以分为三种情况：

1) $b == b_1$，之前$a$一定不属于保证$<b_1, v_1>$的Quorum

2) $b<b_1$, 之前$a$一定不属于保证$<b_1, v_1>$的Quorum

3) $b>b_1$，之前$a$可能属于保证$<b_1, v_1>$的Quorum，也可能不属于。如果不属于，无所谓。如果属于，那么保障的条件，只涉及a在 $<b_1$的quorum上的动作， $>b_1$是不受限制的，不违背承诺。

**其实对于 2b也类似。**

**对于Phase2a，因为它产生了一个新的<b, v>，所以是要考虑自身的Safety以及其他既存的vote**



$Inv \land Phase1b  => Inv'$

没有执行Accept，也没有产生新的Value。需要证明的是：已有的Vote/Value，是安全的。



主要是证明$VotesSafe$，即已经$VotedFor(a,b,v) \implies SafeAt(b,v)$ 
$$
\begin{split}SafeAt(b, v) &\triangleq \\ &\forall c \in [0,(b-1)] : NoneOtherChoosableAt(c, v)\end{split}
$$

$$
\begin{split}
NoneOther&ChoosableAt(b, v) \triangleq \\
&\exists Q \in Quorum : \\
     & \qquad \forall a \in Q : VotedFor(a, b, v) \lor CannotVoteAt(a, b)
     \end{split}
$$



$$
\begin{split}

(CannotVoteAt(a_1, b) \lor VotedFor(a_1, b, v))\land Phase1b(a_1, b_1) \\
 => CannotVoteAt(a_1, b) \lor VotedFor(a_1, b, v)\\

\end{split}
$$
 。因为Phase1b能执行，则必须有 $b<b1$，执行Phase1b后仍然成立。



### 对 Phase2a 成立

$Inv \land Phase2a  => Inv'$

产生了新的 $<b, v>$。需要证明它不影响 $OneValuePerBallot$。

由于Phase1a 是 $>$，不是$>=$，同一个Ballot不可能出现两个Value。

如何证明 $SafeAt(b,v)$? 



### 对 Phase2b 成立

$Inv \land Phase2b  => Inv'$

不产生新的$<b, v>$，只是影响了$VotedFor(a, b, v)$。那么这个Vote是否Safe? 

实际上Phase2a已经解决了SafeAt(b, v)的问题。

如果某个voter，在Phase2b前，执行了一个ballot更大的 Phase1b，**现在再执行2b，从这个证明过程中能体现出来么**？

==> 感觉是在证明Phase2a时，用了这个特性？ 否则就保证不了 $SafeAt(b,v)$。



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

