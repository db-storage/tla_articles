#  觉得Paxos是对的却不知为啥？探讨下Paxos背后的数学

---

**前言**

Paxos [1]是著名的共识协议，但也以难懂著称。即使是简化版的"Paxos Made Simple"一文[1]，把Paxos的两个阶段描述的比较具体，但是很多人仍然有疑惑。很多读者的感受是：觉得应该是对的，但是不知道为什么是对的。

本人在理解Paxos的TLA+ Spec [3] (TLA+是一种形式化验证语言)的过程中，发现其中隐含了对于Paxos正确性的基于不变式(Invariance)的归纳推理。本文抽取一部分必要的部分，大部分改用公式表示，并辅以图形和文字，来理解为什么它是正确的(少部分内容仍然是 TLA+格式的)。希望能有所帮助。

这些内容是从Paxos的TLA+ Spec根据自己的理解抽取和组织的，并非新东西，如果有发现不准确的地方，欢迎指正。Lamport在2019年的一个系列讲座[2]中，也讲解过这个Spec。Lamport在讲座中提到，他当年大致就是按照“Consensus => Voting => Paxos” 一步步抽象来思考问题的，而不是一步到位，不过当年并没有按照TLA+去形式化成Spec。

Paoxs已经这么难懂，为什么还要用偏形式化的方法去说推理？个人的观点是：Paxos本身是严格的，不形式化难以理解为什么是对的；形式化是更准确的，对于理解为什么是有帮助的。比如：**$SafeAt(b,v)$ 表示：”不可能用小于b的任何Ballot Number，选定value v以外的任何值“**。虽然文字描述在意义上也没用问题，但是太繁琐，而且在做推理或者证明时变得难以描述。

理解本文的关键在于：理解投票安全性的含义，即上面的$SafaAt(b,v)$以及执行中如何始终保证它成立。即：如果每一次投票(即Phase2b)，都能保证$SafeAt(b,v)$，并且提能够保证$OneValuePerBallot$(每个Bal只有一个Value，从字面理解即可，相对比较简答)，那么就可以通过强归纳法得出，每次投票都是安全的，因此不可能形成两个不同的决议。注意，这个$SafeAt(b,v)$实际上是向更小的Ballot Number看的，**保证更小的Ballot Number不会形成不同的决议，**而不需要保证更大的Ballot Number怎么样。



本文主要组织如下(主要内容来自paxos相关的三个TLA + spec文件)：

Ch1 从 Consensus.tla 抽取Consensus的定义，即最终要保证的目标；Ch2是从Voting.tla抽取的对投票过程的模型化和正确性推理，这个部分不考虑具体实现，仅仅讨论在投票过程只要保证哪些限定条件(不变式)，就能保证Conesensus；Ch3 开始涉及Paxos这个具体协议，用公式形式回顾Paxos的两个阶段；Ch4 讨论Paxos的两阶段如何保证Ch2提出的限定条件，其中最复杂的是Phase2a。Ch5 是一些集中的FAQ。 

# 1. "对的" 是啥含义？

我们总觉得Paxos是”对的“，但是想不明白为什么。那么怎么算”对的“？我们知道Paxos是一种共识协议，我们先看下Consensus的本身的定义：

- Consensus的定义：chosen的元素个数小于等于1。chosen是被选定的Value集合，下面会提到。
  $$
  \begin{split}
  Consensus \triangleq  Cardinality(chosen) \leq 1
  \end{split}
  $$

所以，共识可以理解成一种最终的安全性要求，而我们后面描述的Paxos实际上只是一种实现。

所谓**”对的“**，就是满足Consensus自身的定义，即不会选定$\ge2$个值。展开一下：

- 没选定任何Value，是对的；
- 只选定了某个Value一次，是对的；
- 多次选定同一个Value，也是对的；
- 选定了两个或者多个不同的Value，是错的。



# 2. Voting模型和正确性推导

下面这些定义不是Paxos两阶段的一部分，主要来自Voting.tla，这个TLA+ Spec是对投票过程的抽象，聚焦于正确性。其目的在于：理解投票过程中满足哪些更具体的限定条件，就可以保证正确。

## 2.1 一些基本函数定义


$$
\begin{split}VotedFor(a, b, v) &\triangleq \space <<b, v>> \in votes[a]\\
ChosenAt(b, v) &\triangleq \space  \exists Q \in Quorum :   \\
&  \qquad \qquad  \forall a \in Q : VotedFor(a, b, v) \\
chosen &\triangleq \{v \in Value : \exists b \in Ballot : ChosenAt(b, v)\}\\  DidNotVoteAt(a, b) &\triangleq \forall v \in Value : \lnot VotedFor(a, b, v) \\
CannotVoteAt(a, b) &\triangleq \land maxBal[a] > b\\            
& \quad \space \land DidNotVoteAt(a, b)\\
chosen &\triangleq  \{v \in Value : \exists b \in Ballot : ChosenAt(b, v)\}\\
\end{split}
$$

### VotedFor(a,b,v)

- $VotedFor(a, b, v)$:  如果Acceptor a曾经Accept了选票$<b,v>$，本函数为true。注意Voted/Accepted两个词会交换使用。

### ChosenAt(b, v)

- $ChosenAt(b, v)$:  存在一个Quorum Q，Q里面每个Acceptor都曾经投票给($b$, $v$)。我们常说的形成决议/形成多数派/选定一个值/Commit，都是ChosenAt的含义；

### DidNotVoteAt(a, b)

- $DidNotVoteAt(a, b)$:  Acceptor a 从未给 $Bal = b$ 的选票投票(**这是对历史的判断**)；

### CannotVoteAt(a, b)

- $CannotVoteAt(a, b)$： Acceptor a 承诺不会给任何 $Bal = b$ 的选票投票而且以前也没有投过(过去、现在和未来都不会给$Bal=b$的选票投票，**既有对历史的判断，也有承诺** )。即$maxBal[a] >b$并且DidNotVoteAt(a, b)。

  约定：在后面的很多式子中，我们经常用到逻辑与($\land$)和逻辑或($\lor$)，它们与我们在关系代数中学到的含义一样。对于 $a \land b$，如果$a$的为false，则不会去尝试计算后面的$b$，这一点对于状态变更很重要，因为只有条件成立才执行后面的某个动作，而整体用一个逻辑表达式来表示。

### chosen

- 这个集合是动态计算出来的，包含所有被选定的Value。

  

### NoneOtherChoosableAt(b, v) 

$$
\begin{split}
NoneOther&ChoosableAt(b, v) \triangleq \\
&\exists Q \in Quorum : \\
     & \qquad \forall a \in Q : VotedFor(a, b, v) \lor CannotVoteAt(a, b)
     \end{split}
$$

- 意义:不可能用 Bal b选定 $v$ 以外的其他值。
- **注意**：这个公式，不代表**$ChosenAt(b,v)$**一定为true。即它只是阻止他人用Bal b成功，并没有肯定自己能成功。
- 实际判断方法: 存在一个Quorum Q，其中任意一个Acceptor a，要么已经投票给了<b, v>，即$VotedFor(a, b,v) = true$，要么没有为Bal b投票且承诺永远不会为Bal = b的选票投票。



### SafeAt(b, v) ：不可能以更小的Bal选定v以外的值

- 含义： 不可能用小于b的某个Bal，选定v以外的任何值。这个本质上就是把NoneOtherChoosableAt 的 Bal 范围定义扩展到一个区间$[0, b-1]$; 

- 注意：不能被选定，**不代表不能被Accept/Vote**，只要Vote不形成Quorum即可;

- 公式：

$$
\begin{split}
  SafeAt(b, v) &\triangleq \\ 
  &\forall c \in [0,(b-1)] : NoneOtherChoosableAt(c, v)
  \end{split}
$$

### 不变式 Inv

所谓不变式，即在执行过程中的每一个状态都是成立的式子。

- Voting过程的不变式：$Inv \triangleq VotesSafe \land OneValuePerBallot$

- VotesSafe: 要求每个 Acceptor在确认投票安全的情况下才能投票（即大家都遵守安全规则去投票，不能随便投，说没有撒谎的)；
  $$
  \begin{split}VotesSafe &\triangleq \\
  &\forall a \in Acceptor, b \in Ballot, v \in Value : \\             
  & \qquad VotedFor(a, b, v) => SafeAt(b, v)\end{split}
  $$
  
- OneValuePerBallot: 同一个Ballot的任意两个投票(不同的Acceptor)，对应的 Value必定相同

$$
\begin{split} OneValue&PerBallot \triangleq\\
&\forall a1, a2 \in Acceptor, b \in Ballot, v1, v2 \in Value : \\     
& \qquad VotedFor(a1, b, v1) \land VotedFor(a2, b, v2) => (v1 = v2) \end{split}
$$

**注意:**

* $A=>B$表示 **A蕴含B**。即：如果A成立，B一定成立，不允许$A=true， B=false$ 。

* 上面的Inv是**历史上所有发生过的投票**都必须满足的限制条件，而不是针对某一次投票。

  

## 2.2 保证Consensus的充分条件

只要保证$VotesSafe$ 和 $OneVote$，就能保证 Consensus。可以用下面的式子表示：
$$
\begin {split}VotesSafe&ImpliesConsistency  \triangleq \\          & \land VotesSafe \\          & \land OneVote \\          & => \qquad \lor chosen = \{\} \\             & \qquad \qquad \lor \exists v \in Value : chosen = \{v\}\end{split}
$$
OneVote:  同一个Ballot的Value必定是相同的，实际上OneValuePerBallot 已经蕴含了 OneVote。
$$
\begin{split}
OneVote \triangleq \forall a \in &Acceptor, b \in Ballot, v, w \in Value : \\
              &VotedFor(a, b, v) \land VotedFor(a, b, w) => (v = w)
              \end{split}
$$


## 2.2.1 反证法

假设VotesSafeImpliesConsistency不成立，即在保证$VotesSafe$ 和 $OneVote$的前提下，仍然会选定两个或者多个不同的值，选定两个值用式子表示为(多个也类似)：
$$
\begin{split}
\exists b_1, b_2 & \in Ballot, v_1, v_2 \in Value: \\
 & \land ChosenAt(b_1, v_1) \land  ChosenAt(b_2, v_2)\land v_1 \neq v_2
 \end{split}
$$

这个式子分为$b_1\neq b_2$和$b_1=b_2$两种情况：

#### **Case 1:** $b_1\neq b_2$

不失一般性，假设$b_1>b_2$。根据 $VotesSafe$ 的定义， $ChosenAt(b_1, v_1) => SafeAt(b_1, v_1)$，而后者展开为：
$$
\begin{split}
SafeAt(b_1, v_1) &\triangleq \\ 
&\forall c \in [0,(b_1-1)] : NoneOtherChoosableAt(c, v_1)
\end{split}
$$
由于$b_2 \in [0, b_1-1]$，所以有$NoneOtherChoosableAt(b_2, v_1)$成立，这与$ChosenAt(b_2,v_2)$矛盾。

#### **Case 2:** $b_1=b_2$

这与 OneVote矛盾，不会出现。



## 2.3 如何产生满足Inv的Value？

$VotesSafe$和$OneVote$都是限定条件，它规定什么是不能违反的，但是没说明按照什么规则去产生选票<b, v>。如果不知道如何产生安全的选票$<b, v>$，就没法高效地运转。 

先不考虑具体协议。假设Proposer有上帝视角，可以看到所有 Acceptor的状态，怎么产生选票$<b, v>$ ?  实际上基于下面的定理：

### ShowsSafety 定理

含义：在之前所有状态都保证了 $VotesSafe$ 和 $OneValuePerBallot$的前提下，满足 $ShowsSafeAt(Q, b, v)$ 的 $<b, v>$，就是安全的，它蕴含了$SafeAt(b, v)$。
$$
\begin{split}定理 Shows&Safety  \triangleq \\ &\land VotesSafe \\&\land OneValuePerBallot \\&  \quad =>   \forall Q \in Quorum, b \in Ballot, v \in Value :\\& \qquad \qquad \qquad    ShowsSafeAt(Q, b, v) => SafeAt(b, v)            \end{split}
$$

### ShowsSafeAt(Q, b, v)

$$
\begin{split}Shows&SafeAt(Q, b, v) \triangleq \\ 
&\land \forall a \in Q : maxBal[a] \geq b \\  
&\land \exists c \in [-1,(b-1)]: \\ 
&\qquad \land (c \neq -1) => \exists a \in Q : VotedFor(a, c, v) \\  
&\qquad \land \forall d \in [(c+1), (b-1)], a \in Q : DidNotVoteAt(a, d)\\
\end{split}
$$

- 含义：存在一个Quorum Q，同时满足下面的Cond 1和Cond2：
- **Cond 1:** Q 内任意一个Acceptor a，满足$maxBal[a] >= b$，注意这实际上是承诺；
- **Cond2:** 存在一个小于 b 的Ballot Number c，同时满足下面两个限定条件：
  - **Cond 2.1:** 如果 $c \ne -1$，需要满足：Q中至少有一个Acceptor a给(b, v)投过票。注意，如果 $c = -1$，则本限定条件为空，这是一个特殊场景，即所有Acceptor都没有投过票。
  - **Cond 2.2:** Q 中没有任何Acceptor a，给[c+1, b-1]之间的任何Bal投过票(DidNotVoteAt)。即Q里面的所有 Acceptor在[c+1, b-1]这个区间，都完全没有投票。

其中：

- Cond 1和Cond 2.2 的结合，保证了Q里面所有Acceptor在$[c+1, b-1]$这个区间的CannotVoteAt成立，所以这个区间不可能选定任何Value；

- Cond 2.1的定义，如果 $c \ne -1$，则有$VotedFor(a,c,v)$，那么根据$VotesSafe$前提，它已经蕴含了$SafeAt(c,v)$；而 $VotedFor(a,c,v)$ 和 $OneValuePerBallot$，保证了$NoneOtherChoosableAt(c, v)$；

  

上面的式子实际上可以对应到Paxos的Phase2a，后面我们会再讨论。为了便于下面画图，我们定义另外一个式子(不是来自于Paxos的Spec)：
$$
\begin{split} Cannot&VoteBetween(a, start, end) \triangleq \\   
&\forall b \in [start+1, end-1]: CanntVoteAt(a, b) 
\end{split}
$$


下面是一个例子，假设某个quorum Q包含了$a_1, a_2, a_3$这三个 Acceptor，它们投票过的**Ballot Number最大的选票**分别是$<b_1, v_1>, <b_2, v_2> 和 <b_3, v_3>$。那么$a_1$的状态蕴含了 : 
$$
\begin{split}
 CannotVoteBetween(a_1, b_1, b) \land SafeAt(b_1, v_1)
\end{split}
$$



![2a](Figures/Phase2a.png)



其他几个也类似。假设$ b_1>=b_2>=b_3$且$b_1>-1$，那么可以得出：
$$
\begin{split}
&\land SafeAt(b_1, v_1) \\
&\land \forall a \in Q: \\
& \qquad \land maxBal[a] \geq b \\
& \qquad \land CannotVoteBetwwn(a, b_1, b)
\end{split}
$$
**为了满足Cond2.2，$c$ 必须取这几个Bal的最大值，即 $c = b_1$**。据此可以推导出  $SafeAt(Q, b, v_1)$，具体推导见下一节。

考虑特殊情况，$b_1=b_2=b_3=-1$，那么取$c=-1$，由于$[0,b-1]$区间不可能选定任何Value，所以无论给定的v是什么，都能满足  $ShowsSafeAt(Q, b, v)$。



### 从ShowsSafeAt 推导 SafeAt

**在之前的运行已经保证 $VotesSafe$ 和 $OneValuePerBallot$的前提下，我们从SafeAt的本意去理解和推导**。继续按照上面的例子来思考，$ShowsSafeAt(Q, b, v)$ 能否保证 $SafeAt(b, v)$?  回顾下$SafeAt$的定义：
$$
\begin{split}SafeAt(b, v) &\triangleq \\ &\forall c \in [0,(b-1)] : NoneOtherChoosableAt(c, v)\end{split}
$$

要证明它成立 ，我们把 $[0, b-1]$分为三个区间：$[0, b_1-1], [b_1, b_1], [b_1+1, b-1]$， 然后分别得出三个区间的NoneOtherChoosableAt成立。

#### (A). 区间$[0, b_1-1]$

由于已知$VoteFor(a_1, b_1, v_1)$为true，根据$VotesSafe$，它隐含了$SafeAt(b_1, v_1)$为true。根据$SafeAt$的定义，成立。
$$
\begin{split}
VotesSafe \land VoteFor(a_1, b_1, v_1) => SafeAt(b_1,v_1)
\end{split}
$$

#### (B). 区间$[b_1, b_1]$

这个单值区间只有$b_1$一个Bal，基于下面的式子推理： 
$$
\begin{split}
OneValue&PerBallot \land VotedFor(a_1, b_1, v_1) \\
&=> NoneOtherChoosableAt(b_1, v_1)
\end{split}
$$

#### (C). 区间$[b_1+1, b-1]$

$ShowsSafeAt(Q, b, v)$已经说明
$$
\begin{split}
\exist Q \in &Quorum: \\
   & \forall a \in Q: CannotVoteBetween(a, b_1, b)
   \end{split}
$$
而$b_1$是最大的，那么在区间$[b_1+1, b-1]$，即上图中灰色区间的最短部分(公共部分)，就不可能选定任何值，因为任意两个Quorum都相交的。



#### FAQ：ShowsSafeAt的物理意义是什么？

对应到后面的paxos，它就是Proposer在Phase2a 判断是否可以发送”2a“消息以及应该提议哪个Value实际判断条件。



#### FAQ:  ShowsSafety的含义？

这个定理表明，如果之前所有操作都满足了Inv，只要Acceptor a判断$ShowsSafeAt(Q, b, v)$成立，就可以推导出$SafeAt(b, v)$。

到目前为止，我们尚没有展开paxos的内容。但是我们知道：从上帝视角看，满足什么条件的投票是安全的，以及如何去产生$<b, v>$。下面我们将回忆下paxos的两个阶段，然后梳理下paxos如何满足$VotesSafe$ 和 $OneValuePerBallot$。



# 3. Paxos的两阶段回顾

这一部分回顾下"Paxos Made Simple"一文的描述的Paxos的两个阶段。但是从具体形式上，使用了公式化描述。这些公式来自[3]。

不过下面这些形式化描述，与Paper里面描述的还是有所区别的，主要包括以下方面：

- 没有具体的Proposer角色，Phase1a和Phase2a都没有体现出哪个Proposer在执行；
- 由于没有体现Proposer角色，与实际系统产生了差异，尤其是消息的可见性。比如Phase2a会判断是$msgs$里面是否有相同Bal的"2a"消息，这个在实际的多Proposer系统中是没法保证可见的，更不用说原子性。
- 我们在后面推导OneValuePerBallot时，并没有依赖于这种全局的消息可见性，而是假设Proposer存在，仅要求每个Proposer能看到发给自己的消息。

## 3.1 常量和变量定义部分

我们先抽取一些必要的变量和常量定义。其中Set和Map与编程语言中的概念相同，这些对于有计算机或者数学基础的读者不难。其中常量是需要预先给定值的。

| 名称     | 类型 | 含义                                                         |
| -------- | ---- | ------------------------------------------------------------ |
| Acceptor | Set  | 所有Acceptor的集合                                           |
| Quorum   | Set  | 里面的每个成员，例如Q1，也是一个Set。且Q1是Acceptor的SubSet  |
| maxBal   | Map  | 即Max Ballot。maxBal[a]表示acceptor a响应/Accept过的最大Ballot Number，在phase1b/phase2b修改。**只增不减**。 |
| maxVBal  | Map  | 即Max Voted Ballot。maxVBal[a]表示Acceptor a曾经Vote过的最大的Ballot Number，在phase2b修改。**只增不减**。 |
| maxVal   | Map  | 即Max Voted Value。 maxVal[a]表示acceptor a曾经Vote过的最大的Ballot Number对应的Value，如果maxVBal[a]为-1，则maxVal[a]为Null。在phase2b修改。 |
| Votes    | Map  | votes[a] 记录Acceptor a曾经accept/vote过的<Bal, Value>元组。 |
| msgs     | Set  | 所有发过的消息集合(在Paxos的TLA+ Spec中，所有消息放在一起，且不删除) |
| Chosen   | Set  | 被选定的Value的集合                                          |



```tla
CONSTANT Acceptor, 
         Quorum     \* The set of "quorums", where a quorum" is a 
                    \*   "large enough" set of acceptors
CONSTANT Ballot

VARIABLE
        votes,   \* votes[a] is the set of votes cast by acceptor a
        maxBal   \* maxBal[a] is a ballot number.  Acceptor a will cast
                  \*   further votes only in ballots numbered \geq maxBal[a]      
        maxVBal, \* <<maxVBal[a], maxVal[a]>> is the vote with the largest
        maxVal,    \* ballot number cast by a; it equals <<-1, None>> if
                    \* a has not cast any vote.
        msgs     \* The set of all messages that have been sent.
                  VARIABLE chosen       
        chosen    \*The set of all values that can be chosen.
```



关于Quorum的假设和定理：

$$
\begin{split}
前提条件 \quad Quorum&Assumption \triangleq\\ 
& \land \forall Q \in Quorum : Q \subseteq Acceptor\\                           & \land  \forall Q1, Q2 \in Quorum : Q1 \cap Q2 \neq \{\}  \\
定理 \quad Quorum&NonEmpty \triangleq \\
&\forall Q \in Quorum : Q \neq \{\} \\\end{split}
$$

感兴趣的读者可以自己计算下，要满足上面Assumption的式子，Q1, Q2的成员个数**不一定**都需要达到Acceptor的半数以上，它们的成员个数也不一定是相等的。虽然在实际应用中往往都简化为多数派。

在TLA+ Spec中，每一个步骤都被认为是**原子的**，而整个分布式系统的运行，被认为是一系列步骤/状态变更组成的序列。具体到paxos的Spec，Phase1a, Phase1b, Phase2a, Phase2b这些步骤都被认为是原子的。



## 3.2 Phase1a

Phase1a即Proposer给各个Acceptor发送"1a"消息，其中参数b为Ballot Number。

**发送Phase1a无需任何前提条件**，直接发送1a消息，它不带有任何承诺，随意发送也不会引起正确性问题。注意"1a"消息，是一个二元组。

”UNCHANGED“是TLA+ spec的语法，说明一些变量保持不变，放在这里只是为了保持式子的完整性，读者可以忽略这些“UNCHANGED” 部分。
$$
\begin{split}
Phas&e1a(b) \triangleq \\
&\land Send([type |-> "1a", bal |-> b])\\
&\land UNCHANGED <<maxBal, maxVBal, maxVal>>\\
\end{split}
$$
Send的含义：
$$
\begin{split}
Send(m) &\triangleq \\
& msgs' = msgs \cup \{m\}
\end{split}
$$
在Paxos的TLA+ spec里面，没有模拟多个通信信道，而是把所有消息放到一个集合里面，通过type和bal等来区分。Send(m)在逻辑上就是把m放到集合中。

$msgs'$的含义：在状态机中，变量$msgs$的下一个状态的值。其他变量也用这个方式表示状态变化。

## 3.3 Phase1b

Phase1b过程，是Acceptor a根据自己的变量去判断，是否应该响应一个 “1a”消息，如果符合条件，则回复一个"1b"消息。参数 a是Acceptor自己的标识。
$$
\begin{split}
Phase&1b(a) \triangleq \\
& \land \exists m \in msgs : \\
& \qquad \land m.type = "1a"  \land \space m.bal > maxBal[a]\\  
& \qquad \land maxBal' = [maxBal\space EXCEPT \space ![a] = m.bal]\\                  & \qquad \land Send([type |-> "1b", acc |-> a, bal |-> m.bal, \\
& \qquad \qquad mbal |-> maxVBal[a], mval |-> maxVal[a]])\\              
& \qquad \land UNCHANGED <<maxVBal, maxVal>>
\end{split}
$$


其中最重要的前提条件是：存在一个类型为"1a"的消息m，$m.bal > maxBal[a]$。

注意，在前提成立的情况下，Phase1b做了两件事(其他所有变量都是Unchanged)：

1) 修改$maxBal[a]' = m.bal$;   这个实际上是承诺。注意这里用到了一个TLA+的EXCEPT语法**，表示对于$maxBal$ 这个map，只修改$maxBal[a]$，其他成员不变。

2) 构建 "1b"消息四元组:$ <"1b", a, m.bal, maxVBal[a], maxVal[a]>$。注意如果a从未成功执行过phase2b，$maxVBal[a]$就是-1，此时$maxVal[a]$为空 。

3) Send  “1b"消息。**注意：** Phase1b等每个操作都被认为是原子的，一旦发送了"1b"，$maxBal[a]$ 必然也增加了。如果下次再收到相同Bal的"1a"消息m，$m.bal > maxBal[a]$ 这个前提条件就不成立了，不会再回复"1b"，**这是OneValuePerBallot的基础**。

后面会看到多个类似下面的式子（phase1b也属于这种），只有前提条件成立时，才执行状态变更。"UNCHANGED"部分在理解本文时可以跳过，只是为了保持公式完整性而保留在这里。
$$
\begin{split}
State&Change \triangleq \\
&\land 前提条件 \\
&\land 一个或者多个变量的状态修改\\
&\land 不变的部分\\
\end{split}
$$


## 3.4 Phase2a

**前提条件：**

​      1) 没有发送过Bal为b的“2a”消息；

​       2) 存在一个Quorum Q，里面的每个Acceptor都回复过相应的“1b”。

**确定Value v，构建2a消息:**

​      1) 定义临时变量Q1b为： Q里面所有Acceptor发送的Phase1b消息集合；

​      2) 定义临时变量Q1bv为： Q1b中，所有$m.mbal \geq 0$的消息集合；

​      3) 如果Q1bv为空，说明Q里面所有成员都没有Vote过，所以v由Proposer自己决定Value；

​     4) 如果Q1bv不为空，那么v必须是Q1bv中对应mbal最大的那个(即Q里面成员Vote过的最大的Bal对应的value)。
$$
\begin{align*}
Pha&se2a(b, v) \triangleq\\ 
  & \land \lnot \exists m \in msgs : m.type = "2a" \land m.bal = b\\
  & \land \exists Q \in Quorum :\\
  & \qquad   LET \space Q1b = \{m \in msgs :   \land m.type = "1b"\\
  & \qquad \qquad  \qquad  \qquad  \qquad \qquad \quad \land m.acc \in Q\\
  & \qquad \qquad  \qquad  \qquad  \qquad \qquad \quad \land m.bal = b \}\\
  & \qquad \qquad     Q1bv = \{m \in Q1b : m.mbal \geq 0\}\\
  &\qquad   IN  \land \forall a \in Q: \exists m \in Q1b : m.acc = a \\
  &\qquad  \quad \space \,  \land \quad \lor Q1bv = \{\}\\
  &\qquad \qquad  \space \, \quad \lor \exists m \in Q1bv: \\
  &\qquad \qquad  \qquad \quad    \land m.mval = v \\
  &\qquad \qquad  \qquad \quad   \land \forall mm \in Q1bv : m.mbal \geq mm.mbal \\
  &\land Send([type |-> "2a", bal |-> b, val |-> v])\\
  \end{align*}
$$

上面式子中，发送消息$<"2a", b, v>$前确认 $<b, v>$是否安全的部分，对比下2.3节的$ShowsSafeAt(Q, b, v)$公式和图，它们实际上是相同的，只是上面的判断是基于看到的“1b”消息。

#### 与$ShowsSafeAt(Q,b, v)$的对应：

- $Q1bv$为空集合时，对应$ShowsSafeAt(Q,b, v)$ 中 $c=-1$ 的分支。上面的式子中没有对$v$做任何限制，但是实际上在整个状态机的Next函数中，已经在外围做了限制，即 $v\in Value$。

$$
\begin{split}
Next \triangleq &\lor \exists b \in Ballot : \lor Phase1a(b)\\
   & \qquad \qquad \qquad \space \space \, \lor \exists v \in Value : Phase2a(b, v)\\
        & \lor \exists a \in Acceptor : Phase1b(a) \or Phase2b(a)
        \end{split}
$$

- $Q1bv$非空时，对应了$ShowsSafeAt(Q,b, v)$ 中 $c \neq -1$ 的分支，取$mbal$最大值及对应的$mbal$。

**FAQ**：上面式子中，为什么需要通过前提条件的1)，来避免两次执行phase2a?

- 因为Value可能是Proposer自己决定的($Q1bv$为空时)，而Paxos的Spec 里面的msg全部保留不删除。如果Proposer用同一个Bal执行两次Phase2a，$ShowsSafeAt(Q, b, v)$可能两次都成立，这样两次会生成不同的Value，导致OneValuePerBallot被违背。

**FAQ**:  实际上的paxos实现，一个Poposer如何判断前提条件1)是否成立?

- 在有多个Proposer的情况下，这个是没法判断的，没法保证每个Proposer可以看到所有的"2a"消息。

- OneValuePerBallot依赖于自己收到的"1b"消息隐含的承诺，而不是检查已有的"2a"消息，后面讨论正确性时有具体内容。

  

## 3.5 Phase2b

Acceptor a执行Phase2b的过程，分为以下几个部分。

### 前提条件

​    存在一个"2a"消息m，且满足 $m.bal \geq maxBal[a]$。 

​    注意：这里的判断符号是$\geq$，与Phase1b是不同的。

### 修改本Acceptor的变量

​       $ maxBal[a]'=m.bal$

​       $maxVBal[a]' = m.bal $

​       $maxVal[a]'= m.val$

### 发送"2b"消息(即投票)

  "2b"消息带有Acceptor的ID(a)，包含从"2a"消息$m$里面获取的$m.bal$和$m.val$ 。具体为四元组$<"2b", a, m.bal, m.val>$。 注意这些都用了EXCEPT语法，即只修改map的一个成员，其他成员不变。
$$
\begin{split}
Phase2b(a) \triangleq \exists m \in msgs : &\land m.type = "2a"\\
               &\land m.bal \geq maxBal[a]\\
               &\land maxBal' = [maxBal \space EXCEPT \space ![a] = m.bal] \\
               &\land maxVBal' = [maxVBal \space EXCEPT \space ![a] = m.bal] \\
               &\land maxVal' = [maxVal \space EXCEPT \space ![a] = m.val]\\
               & \land Send([type |-> "2b", acc |-> a,\\
               &  \qquad \qquad   bal |-> m.bal, val |-> m.val]) 
\end{split}
$$

FAQ:  为什么Phase1b和Phase2b都修改 $maxBal[a]'$ ？ 

- 因为执行Phase2b的Acceptor，之前不一定执行了Phase1b 。



# 4. Paxos的正确性

本章先描述下Paxos各个消息隐含的承诺，然后讨论Paxos协议过程如何满足不变式Inv。这是因为ShowsSafety定理依赖于Inv。

在paxos.tla中，有一个定义和定理如下。其基本含义是：Paxos在运行过程中，必须要满足Voting模型里面的不变式Inv。这里不用理解具体语法，只需要知道含义即可。
$$
\begin{split}
V \triangleq INSTANCE \space Voting \\
THEOREM \quad Spec => V!Spec
\end{split}
$$


## 4.1 各个消息隐含的承诺

### “1a”消息 : $<"1a", b>$

- 无任何承诺。

### "1b"消息: $<"1b", a, b, maxVBal[a], maxVal[a]>$

- 记录了$maxBal[a]'=b$，**承诺a不会再响应任何 $Bal <= m.bal$的Phase1a，**承诺a不会Accept任何 $Bal <m.bal$的Phase2a；
- 如果$maxVBal[a] \neq -1 $ ，表明 $VotedFor(a, maxVBal[a], maxVal[a])$  ，它**如实转达**了最近一次投票隐含的$SafeAt(maxVBal[a], maxVal[a])$；
- 如果$maxVBal[a] = -1 $，表明a没有Accept过任何“1a”消息，这是个特殊场景。

**因此，“1b"实际上隐含了**：

​                 $CannotVoteBetween(a, maxVBal[a], b) \land SafeAt(maxVBal[a], maxVal[a])$  

其中前一部分是a的承诺，后一部分是转达已有的Vote蕴含的SafeAt。



### "2a"消息: $<"2a",b,v>$

- 隐含承诺了$SasfAt(b, v)$

  Proposer判断$ShowsSafeAt(Q, b, v)$成立 ，才发送$<b,v>$，它蕴含了$SafeAt(b, v)$。

  


### "2b": $<"2b",a, b, v>$

- 记录了$maxBal[a]'=b$，具体承诺内容参见"1b"的相应描述。如果这个acceptor正好也发送过对应的“1b”，那么实际上在执行Phase1b时已经承诺过。
- 记录了$maxVBal[a]'=b, maxVal[a]'=v$，按照前面的讨论，这个记录隐含了$SafeAt(b, v)$。也表示 a **承诺会如实转达**$SafeAt(b,v)$。



### **FAQ**: 承诺如何兑现？

Phase1b和Phase2b都有自己的前提条件，比如 Acceptor a 在Phase1b修改了$maxBal[a]'=b$，只要它保存了这个数值不丢失，那么后续任意 $Bal \leq b$ 的"1a"消息肯定会被拒绝，因为前提条件不成立。 



## 4.2 Paxos 如何保证不变式 Inv 成立?

Voting模型的Inv就是 $OneValuePerBallot \land VotesSafe$。Paxos在执行过程中，保证不变式 Inv 在每一步都成立。

由于$VotesSafe$和$OneValuePerBallot$都是对已发生的所有投票的限定条件，而新的状态如果会产生新的投票，也会成为被约束的对象。因此，被Inv约束的对象是不断变化的，其本身是个滚动过程。

#### 4.2.1 Paxos 如何保证 OneValuePerBallot？

$$
\begin{split} One&ValuePerBallot \triangleq \\
 &\forall a1, a2 \in Acceptor, b \in Ballot, v1, v2 \in Value : \\       
 &VotedFor(a1, b, v1) \land VotedFor(a2, b, v2) => (v1 = v2) \end{split}
$$

OneValuePerBallot由于只涉及同一个Bal的比较，相对独立，先用反证法证明它成立。

**反证法**：所有$<b, v>$是Phase2a产生的，假设OneValuePerBallot不成立，即有一个Bal $b_x$，有两个Proposer $P1$和$P2$分别发送了"2a"消息$<b_x, v_1>$和$<b_x, v_2>$。那么P1必然收到了某个Quorum $Q_1$里面所有成员的"1b"消息；而P2收到了某个Quorum Q2里面所有成员的"1b"消息。但是这是不可能的，因为每个Acceptor a在发送"1b"时，已经保证$maxBal[a] > b_x$，所以不可能再次响应Bal同为$b_x$的"1a"。而根据Quorum的定义，$Q1$和$Q2$必然有交集，矛盾。

所以，Paxos协议能保证OneValuePerBallot 恒成立。

注意：上面的反证法没有依赖于$msgs$的全局可见性，而是按照实际系统中每个Proposer执行Phase2a时可见的消息来推导。在回顾Paxos时，我们曾经提到Paxos的Spec为了简化，没有体现出多个Proposer，依赖于$msgs$的全局可见性。

### 4.2.2 Paxoss如何保证 Inv?

根据上一段证明，OneValuePerBallot 恒成立。而$Inv = OneValuePerBallot \land VotesSafe$， 我们只要讨论 VotesSafe 是否始终成立即可。

回顾下 VotesSafe 的定义，它要求所有已经发生的投票都是安全的。
$$
\begin{split}VotesSafe \triangleq &\forall a \in Acceptor, b \in Ballot, v \in Value : \\              &VotedFor(a, b, v) => SafeAt(b, v)\end{split}
$$
**思路**：在 Phase2a 产生选票(”2a"消息)时，就要保证安全性，该选票无论是否被Accept都不影响选票的安全性。我们要推导的是：每一次 Phase2a 的执行，如果在执行前 Inv 成立，在执行后 Inv 也成立。其中一个关键点是：Phase2a确定Value的过程，就是判断$ShowsSafeAt(Q,b, v)$成立的过程。

- 由于执行过程中总有一个选票是第一个被产生的。不妨假设第1个产生的选票是$<b_1,v_1>$，它的Phase2a被执行时，还没有任何选票，不可能有任何一个投票发生过，因此$VotesSafe$成立。根据$ShowsSafety$定理，$ShowsSafeAt(Q, b_1, v_1)$蕴含了$SafeAt(b_1, v_1)$。本步骤执行后只有这一个可能的选票, 它是安全的，故Inv 依然成立。
- 假设第2个执行Phase2a的产生的选票是$<b_2, v_2>$，也就是说它之前产生的选票仅有$<b_1, v_1>$(但是 $<b_1, v_1>$不一定被Accept过)，那么$Phase2a(b_2, v_2)$被执行时，只有$<b_1, v_1>$可能被Vote过，根据上一步描述，此时Inv(含VotesSafe)成立。$Phase2a(b_2, v_2)$ 被执行时，根据$ShowsSafety$定理，$ShowsSafeAt(Q, b_2, v_2)$蕴含了$SafeAt(b_2, v_2)$ 。本步骤执行后只有2个选票，它们都是安全的，故Inv 依然成立。
- **强归纳**：假设第$n$个成功执行Phase2a的选票是$<b_n, v_n>$，在它之前产生的选票有$<b_1, v_1>, <b_2, v_2>,... <b_{n-1}, v_{n-1}>$ ，这些选票已经分别保证了$SafeAt(b_1, v_1), SafeAt(b_2, v_2), ..., SafeAt(b_{n-1}, v_{n-1})$成立，所以本步骤执行前Inv成立。根据$ShowsSafety$定理, $ShowSafeAt(Q, b_n, v_n)$ 产生的$<b_n, v_n>$蕴含了$SafeAt(b_n, v_n)$，因此本步骤执行后执行后一共有n个选票，它们都是安全的，故Inv依然成立。



#### FAQ: 讨论Paxos如何满足Inv时，为什么不讨论Phase1a, Phase1b, Phase2b?

- Phase1a：不涉及任何影响 VotesSafe 和 OneValuePerBallot 的因素的变化，因此不影响Inv是否成立。
- Phase1b:  某个Acceptor执行Phase1b本身不产生选票也不涉及投票。其唯一可能的修改是增大$maxBal[a]$，而增大$maxBal[a]$不会违背任何承诺，不会使得Inv从true变为false (但是减小$maxBal[a]$会导致违背承诺)。
- Phase2b： Phase2a在产生选票$<b, v>$时，已经保证了选票的安全性$SafeAt(b,v)$，这个式子的成立不依赖于这个选票是否被Accept，或者被Accept了几次，所以$VoteFor(a, b, v)$​不会使得Inv从true变为false，而增大$maxBal[a]$也不影响Inv。

#### FAQ：两个Phase1a完全并行，如何保证Inv？

- 假设并行的两个$Phase2a(b_x, v_x)$和$Phase2a(b_y, v_y)$，由于两个并行的Phase2a只能是在两个不同的Proposer上执行(假设为P0和P1)，P0和P1已经分别接收了足够的"1b"消息并按照收到的"1b"消息做决策，发送自己的"2a"消息，在执行过程中没有共享读写的变量，所以两个步骤之间没有任何因果(Causal Order)关系。它们无论谁先执行，还是并行执行，执行完成后可达的下一个状态实际上是相同的，所以完全可以认为它们是串行的。实际上，任意两个没有因果关系的事件，都可以被调整顺序。关于Causal Order和Partial Order，参见[4]。

  

#### FAQ：为什么增大$maxBal[a]$不影响Inv?

- **简单来说**，**增大$maxBal[a]$在任何时候都不违背任何承诺**。
- 因为增加 $maxBal[a]$ 实际上增大了承诺的不投票范围，而不投票不会使得某个 $SafeAt(b, v)$ 从true变为false。
- OneValuePerBallot 也不会受到影响，对于某个Acceptor a来说，如果它已经发送过某个"1b"消息，即$maxBal[a]=b$，那么增加$maxBal[a]$显然不会让它再响应同一个Bal b的"1a"，不违背承诺。



# 5 一些FAQ

## 5.1 有一个选票$<b_1, v_1>$还未被选定，如果将来形成共识，value会是$v_1$么？

不一定，假设只有$a_1$ Accept了这个"2a"，然后宕机了，而其他节点都没有收到这个"2a"消息。如果其他节点再形成共识，就仿佛这个"2a"没发生过。

按照之前我们讨论的定义，"2a"消息蕴含了$SafeAt(b_1, v_1)$，即只阻止了$<b_1$部分的Bal选定其他值，不能保证用$>b_1$的Bal选定的值还是$v_1$。只有$ChosenAt(b_1, v_1)$真正成就了自己。



## 5.2 多个Acceptor分别选定了不同的选票，会如何？

假设一共有5个Acceptor $\{a1, a2, a3, a4, a5\}$，$VotedFor(a_1,b_1,v_1)$, $ VotedFor(a_2,b_2, v_2)$ 和 $VotedFor(a_3,b_3, v_3)$都成立，且$b_1 \neq b_2 \neq b_3$,  $v_1\neq v_2  \neq v_3$，而$a_4, a_5$都没有Vote过，如果将来形成共识，value会是哪个？

1）假设有个比$\{b_1,b_2,b_3\}$中任何一个都大的Bal $b_x$, 它的Phase1只有$a_1, a_4, a_5$参加了，并形成共识，那么选定的就是$v_1$。

2）如果$a_1, a_2，a_3$都参加了$b_x$的Phase1，那么就根据$b_1, b_2, b_3$的最大值来决定，选取相应的Value。参见$ShowsSafeAt(Q, b, v)$。

**思考**：5个Acceptor中，会不会出现4个Acceptor，分别Vote了**不同**的Value(不同的Bal)? 为什么？



## 5.3 Instance是什么？

- 假设某西方国家议会每天只形成一个决议（或者说通过一个提案），但是每个州代表都有自己的提案，大家都抢着提，希望本州的提案早日被通过。那么，每一天形成一个决议的过程，就是一个Instance的执行过程，相当于一年有365个Instance。Instance之间的相对顺序是有意义的，1号决议不能在 2号决议后执行，甚至2号决议可能还声称从某天开始废除1号决议。

- Ballot Number跟Instance之间的关系：每个州代表都在做提案，但是一天只能通过一个提案，今天到底通过哪一个？可以想象成各个州在竞标，把Ballot Number想象成不断增加的竞标出价，只要没形成决议，可以不断提高竞价来抢。




## 5.4 每个步骤的原子性是必须的么？是否可以拆分？

$$
\begin{align}
Phase&1b(a) \triangleq \\
& \land \exists m \in msgs : \\
& \qquad \land m.type = "1a"  \land \space m.bal > maxBal[a]\\  
& \qquad \land maxBal' = [maxBal\space EXCEPT \space ![a] = m.bal]\\                  & \qquad \land Send([type |-> "1b", acc |-> a, bal |-> m.bal, \\
& \qquad \qquad mbal |-> maxVBal[a], mval |-> maxVal[a]])\\              
\end{align}
$$

- 以Phase1b为例，上面的(3)是前提条件判断，(4)是修改$maxBal[a]$，这两个显然是紧密关联，必须原子；
- (5)和(6)是同一件事，我们用(5)表示。(5)需要读取多个值($m.bal, maxBVal[a]和maxVal[a]$)，这些值的读取需要是原子的，即对应某个时刻的值，否则就不是如实转达已发生的投票；所以，即使实际的网络发送与(3)/(4)不是原子的，消息的生成也必须是与(3)(4)是原子的。



[1] Leslie Lamport: Paxos Made Simple

[2] Leslie Lamport的讲座视频：The Paxos algorithm or how to win a Turing Award. 

[3] Paxos的TLA+ Spec: https://github.com/tlaplus/Examples/tree/master/specifications/Paxos

[4] Leslie Lamport: Time, Clocks, and the Ordering of Events in a Distributed System




