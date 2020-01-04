#  从TLA+ Spec看Paxos的正确性推导

---

**前言**

在理解Paxos的TLA+ Spec过程中，发现其中其实隐含了Paxos正确性的基于不变式(Invariance)的推理。由于TLA+  spec不易理解，且基本没有高亮显示，所以先抽取其中相对易于理解的部分，大部分改用Latex公式表示，并辅以图形和文字，希望能抛砖引玉。部分内容仍然是 TLA+格式的，但是近来通过文字或者表格来辅助理解。

这些内容是从Paxos的TLA+ Spec根据自己的理解抽取和组织的，并非新东西，如果有发现不准确的地方，欢迎批评指正。

Paoxs已经这么难懂，为什么还要用偏理论的方法去说理论？其实形式化往往是更准确的，在理想情况下可能还是极简的，不一定是复杂的。比如：$SafeAt(b,v)$ 表示：”不可能用<b的任何Ballot Number，选定value v以外的任何值“。虽然后者意义上也没用问题，但是太繁琐，而且在做推理或者证明时变得极其繁琐而事实上难以描述。

理解本文的关键在于：理解投票安全性的含义，即一个Acceptor为某个$<b, v>$投票时，需要确认是安全的，那么安全的含义是什么? 就是：不可能有人用小于b的Ballot Number选定v以外的值。注意，这个保证实际上是向更小的Ballot Number看的，**保证更小的Ballot Number需要满足某个条件**，**而不需要保证更大的Ballot Number怎么样**。实际上不需要在两个方向都保证，也不可能有这种保证。

# 1. 共识 (Consensus)的极简定义

## 1.1 Consensus的定义

- Consensus的定义：chosen的元素个数小于等于1。chosen是个集合，下面会提到。
  $$
  Consensus =  Cardinality(chosen) \leq 1
  $$

# 2. Paxos的两个阶段回顾

这一部分回顾下Paxos的两个阶段，从paxos的 TLA+ Spec里面摘取了其公式表示。跟"Paxos Made Simple"一文的描述是相同的，但更多是数学描述。

## 2.1 常量和变量定义部分

我们先抽取一些必要的变量和常量定义 。这些对于有计算机或者数学基础的读者应该不难 。其中常量是需要预先给定值的。

| 名称     | 类型 | 含义                                                         |
| -------- | ---- | ------------------------------------------------------------ |
| Acceptor | Set  | 所有接收者的集合                                             |
| Quorum   | Set  | 里面的每个成员，例如Q1，也是一个Set。且Q1是Acceptor的SubSet  |
| maxBal   | Map  | maxBal[a]表示acceptor a响应/Accept过的最大Ballot Number，在phase1b/phase2b修改。只增不减。 |
| maxVBal  | Map  | Max Voted Ballot。maxVBal[a]表示acceptor a曾经Vote过的最大的Ballot Number，在phase2b修改。只增不减。 |
| maxVal   | Map  | Max Voted Value。 maxVal[a]表示acceptor a曾经Vote过的最大的Ballot Number对应的Value，在phase2b修改。<"2b", a, maxVBal[a], maxVal[a]>构成了一个Phase2b消息四元组。 |
| Votes    | Map  | votes[a] 记录acceptor a曾经vote过的<Bal, Value>元组          |
| msgs     | Set  | 所有发过的消息集合(在Paxos的TLA+ Spec中，msg不删除)          |
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



对Quorum的要求：

$$
\begin{split}ASSUME\space\space QuorumAssumption =\\ & \land \forall Q \in Quorum : Q \subseteq Acceptor\\                           &\land  \forall Q1, Q2 \in Quorum : Q1 \cap Q2 \neq \{\}  \\THEOREM \space\space QuorumNonEmpty = \\ &\forall Q \in Quorum : Q \neq \{\} \\\end{split}
$$

感兴趣的读者可以自己计算下，要满足上面的式子，Q1, Q2的成员个数不一定都需要达到Acceptor的半数以上，它们的成员个数不一定是相等的。

在后面的很多式子中，我们经常用到逻辑与$\land$和逻辑或$\lor$，它们与我们在关系代数中学到的含义一样。对于 $a \land b$，如果$a$的为false，则不会去尝试计算后面的$b$。

## 2.2 Phase1a

Phase1a即Proposer给各个Acceptor发送phase1a消息，参数b为Ballot Number。

**发送Phase1a无需任何前提条件**，直接发送1a消息，它不带有任何承诺。注意1a消息，是一个二元组，可以理解成一个结构体。

”UNCHANGED“是TLA+ spec的语法，说名某些变量不变，保留这些只是为了保持完整性，读者可以忽略这些“UNCHANGED” 部分。
$$
\begin{split}
Phase1a(b) = &\land Send([type |-> "1a", bal |-> b])\\
              &\land UNCHANGED <<maxBal, maxVBal, maxVal>>\\
\end{split}
$$
Send的含义：
$$
Send(m) = msgs' = msgs \cup \{m\}
$$
在Paxos的TLA+ spec里面，没有模拟许多通信信道，而是把所有msg放到一个集合(msgs)里面，通过type和bal来区分。Send(m)就是修改msgs，使得msgs的新状态为：msgs和{m}的并集。$msg'$表示msg被修改后的状态。

$msgs'$的含义：在状态机中，变量$msg$的下一个状态的值。其他变量也类似。

## 2.3 Phase1b

Phase1b过程，是Acceptor 根据自己的变量去判断，能否响应一个 Phase1a消息，如果符合条件，则响应一个Phase1b。参数 a是Acceptor自己的标识。
$$
\begin{split}Phase1b(a) = & \land \exists m \in msgs : \\                  & \qquad \land m.type = "1a"  \land \space m.bal > maxBal[a]\\                  & \qquad \land maxBal' = [maxBal\space EXCEPT \space ![a] = m.bal]\\                  & \qquad \land Send([type |-> "1b", acc |-> a, bal |-> m.bal, \\                  & \qquad\qquad mbal |-> maxVBal[a], mval |-> maxVal[a]])\\              &\land UNCHANGED <<maxVBal, maxVal>>\end{split}
$$


其中最重要的前提条件是：存在一个 "1a" msg m，m.bal 大于maxBal[a]。即：

​           $ m.type = "1a" \land \space m.bal > maxBal[a]$。

注意，在前提成立的情况下，Phase1b做了两件事(其他所有变量都是Unchanged)：

1) 修改maxBal[a]：$maxBal[a]' = m.bal$;

2) 构建 "1b"消息四元组:$ <"1b", a, m.bal, maxVBal[a], maxVal[a]>$。注意如果a从未执行过phase2b，maxVBal[a]就是-1，此时maxBal[a]为空 。

3) Send  “1b"消息，Send的含义在前面有解释。**注意：** Phase1b等各种操作都被认为是原子的，一旦发送了"1b"，$maxBal[a]$ 必然也增加了，所以下次收到Bal相同的Phase1a，$m.bal > maxBal[a]$ 这个前提条件就不成立了，这是OneValuePerBallot的基础。

## 2.4 Phase2a

**前提条件：**

​      1) 没有发送过bal为b的2a消息(避免重复)；

​       2) 存在一个Quorum Q，里面的每个成员都回复过Phase1b。

**确定val，构建Phase2a消息:**

​      1) 定义临时变量Q1b为该 Q发送的Phase1b消息集合；

​      2) 定义临时变量Q1bv为Q1b中，所有$m.mbal \geq 0$的消息集合；

​      3) 如果Q1bv为空，说明Q里面所有成员都没有Vote过，所以v由proposer自己决定；

​     4) 如果Q1bv不为空，那么v必须是Q1bv中对应mbal最大的那个(即Q里面成员Vote过的最大的Ballot Number对应的value)。
$$
\begin{split}
Ph&ase2a(b, v) =\\ 
  & \land \lnot \exists m \in msgs : m.type = "2a" \land m.bal = b\\
  &  \land \exists Q \in Quorum :\\
  & \qquad       LET \space Q1b = \{m \in msgs :   \land m.type = "1b"\\
  &  \qquad \qquad  \qquad  \qquad  \qquad \qquad \quad \land m.acc \in Q\\
  &  \qquad \qquad  \qquad  \qquad  \qquad \qquad \quad \land m.bal = b \}\\
  &  \qquad \qquad     Q1bv = \{m \in Q1b : m.mbal \geq 0\}\\
  & \qquad      IN  \land \forall a \in Q : \exists m \in Q1b : m.acc = a \\
  & \qquad  \quad \space   \land \lor Q1bv = \{\}\\
  & \qquad \qquad  \space   \lor \exists m \in Q1bv : \\
  & \qquad \qquad  \qquad \qquad    \land m.mval = v\\
  & \qquad \qquad  \qquad \qquad    \land \forall mm \in Q1bv : m.mbal \geq mm.mbal \\
  &\land Send([type |-> "2a", bal |-> b, val |-> v])\\
  &\land UNCHANGED <<maxBal, maxVBal, maxVal>>\\
  \end{split}
$$


## 2.5 Phase2b

​     一个Acceptor执行Phase2b的过程，分为以下几个部分。

### 检查前提条件

​    存在一个"2a"消息m，满足 $m.bal \geq maxBal[a]$。 

### 修改本Acceptor的变量

​       $ maxBal[a]'=m.bal$

​       $maxVBal[a]' = m.bal] $

​       $maxVal[a]'= m.val]$

### 发送"2b"消息(即Vote)

   "2b"消息带有Acceptor的ID(参数a)，包含从"2a"消息m里面获取的$m.bal$和$m.val$ 。具体为四元组$<"2b", a, m.bal, m.bal>$。
$$
\begin{split}
Phase2b(a) = \exists m \in msgs : &\land m.type = "2a"\\
               &\land m.bal \geq maxBal[a]\\
               &\land maxBal' = [maxBal \space EXCEPT \space ![a] = m.bal] \\
               &\land maxVBal' = [maxVBal \space EXCEPT \space ![a] = m.bal] \\
               &\land maxVal' = [maxVal \space EXCEPT \space ![a] = m.val]\\
               & \land Send([type |-> "2b", acc |-> a,\\
               &  \qquad \qquad   bal |-> m.bal, val |-> m.val]) 
\end{split}
$$


**FAQ:  为什么Phase1b和Phase2b都修改 $maxBal[a]'$** ？ 

- 因为执行Phase2b的Acceptor，不一定执行了Phase1b 。

# 3. 相关的式子

下面这些定义不是Paxos两阶段的一部分，但是对于理解两阶段为什么是对的，却是很重要的。

## 3.2 基本函数定义

- VotedFor(a, b, v):  Acceptor a曾经Vote了选票($b$, $v$)，即发送过对应的Phase2b消息。注意Voted/Accepted会交换使用。

- ChosenAt(b, v): 存在一个Quorum Q，Q里面每个成员都曾经投票给($b$, $v$)。我们常说的形成决议/形成多数派/选定一个值/Commit，都是ChosenAt的含义；

- DidNotVoteAt(a, b):  Acceptor a从未给 $Bal = b$ 的选票投票；

- CannotVoteAt(a, b)： Acceptor a不能给任何 $Bal = b$的选票投票，因为$maxBal[a] >b$并且DidNotVoteAt(a, b)。 
  $$
  \begin{split}
  VotedFor(a, b, v) =\space &<<b, v>> \in votes[a]\\
  ChosenAt(b, v) = \space  &\exists Q \in Quorum :   \\
                     &  \forall a \in Q : VotedFor(a, b, v) \\
  chosen = &\{v \in Value : \exists b \in Ballot : ChosenAt(b, v)\}\\
    
  DidNotVoteAt(a, b) = &\forall v \in Value : \lnot VotedFor(a, b, v) \\
  CannotVoteAt(a, b) = &\land maxBal[a] > b\\
              &\land DidNotVoteAt(a, b)\\
  \end{split}
  $$
  



#### FAQ: 为什么需要CannotVoteAt里面要包含 DidNotVoteAt?

- 如果没有DidNotVoteAt，假设有个v和 Q1，满足： 
  $$
  \begin{split}
  \exists  v \in Values, Q_1 \in &Quorum: \\ 
  &\forall a \in Q_1: VotedFor(a, b, v) \land maxBal[a]>b
  \end{split}
  $$
  即Q1里面的成员虽然现在不能再VoteFor(b, v)，但是之前已经都Vote过了，那么可能$ChosenAt(b,v)$早已经为true。

### 3.2.1  NoneOtherChoosableAt(b, v)

$$
\begin{split}
NoneOtherChoosableAt(b, v) = \\
\exists Q \in Quorum : \\
     & &\forall a \in Q : VotedFor(a, b, v) \lor CannotVoteAt(a, b)
     \end{split}
$$

- 意义: 除了v以外，不可能用 Bal b选定其他Value。
- **注意**：这个公式，只说别的value没法用b选定，**没有隐含$ChosenAt(b,v)$**一定为true。即它只是否定部分别人，并没有肯定自己。
- 实际判断方法: 存在一个Quorum Q，其中任意一个Acceptor a，要么已经Vote了<b, v>，即$VotedFor(a, b,v) = true$，要么没有为Bal b投票且承诺永远不会为Bal = b的选票投票。
- 反证：假设存在某个Value $w$, $w\ne v$, 有ChosenAt(b, w)。则必须有某个 Quorum R，满足： $\forall a \in R, VotedFor(a, b, w)$，根据Quorum的含义，R必然与 Q有交集，假设这个交集包含 acceptor $a_1$，那么有: $a_1: a_1 \in Q VotedFor(a_1, b, w)$这与前提矛盾。

**FAQ**: 为什么$NoneOtherChoosableAt(b,v)$不是$NoneOtherChoosableAt(a, b, v)$?

因为NoneOtherChoosableAt是个全局概念，不是某个Acceptor的承诺，而是纵观所有acceptor，$(b, v)$之前一定没有被选定，将来也不会被选定 。

### 3.2.2 SafeAt(b, v)

- 含义： 不可能用小于b的Ballot Number，选定v以外的任何值。这个本质上就是把NoneOtherChoosableAt的Bal范围定义到到一个区间$[0, b-1]$.

- 注意：不能被选定，**不代表不能Accept/Vote**， 只要vote不形成Quorum即可。

- 公式：
$$
  \begin{split}
  SafeAt(b, v) &= \\ 
  &\forall c \in 0..(b-1) : NoneOtherChoosableAt(c, v)
  \end{split}
$$

### 3.2.3 ShowsSafeAt(Q, b, v)

$$
\begin{split}
ShowsSafeAt(Q, b, v) = \\
  &\land \forall a \in Q : maxBal[a] \geq b \\
  &\land \exists c \in -1..(b-1) : \\
  &\land (c \neq -1) => \exists a \in Q : VotedFor(a, c, v) \\
  &\land \forall d \in (c+1)..(b-1), a \in Q : DidNotVoteAt(a, d)
\end{split}
$$

- 含义：存在一个Quorum Q，同时满足下面的Cond 1和Cond2：
- **Cond 1:** Q内任意一个Acceptor a，满足$maxBal[a] >= b$
- **Cond2:** 存在一个小于b的Ballot c，同时满足下面两个条件：
  - **Cond 2.1:** 如果 $c \ne -1$，则满足：Q中至少有一个Acceptor a, a给(b, v)投过票。注意，如果 $c = -1$，则没有限制，这是一个特殊场景，即所有Acceptor都没有投过票。
  - **Cond 2.2:** Q中没有任何Acceptor a，给[c+1, b-1]之间的任何Ballot Number投过票。即Q里面的所有 Acceptor在[c+1, b-1]这个区间，都完全没有投票，只增加了maxBal。

其中：

- Cond 1和Cond 2.2 保证了[c+1, b-1]这个区间不可能选定任何Value。
- Cond 2.1的定义，如果c不等于-1，则有VotedFor(a,c,v)，那么这个Vote发生时已经保证了SafeAt(c,v)；
  VotedFor(a,c,v)和OneValuePerBallot，保证了NoneOtherChoosableAt(c, v)；

$$
\begin{split}
定理 \space ShowsSafety & = VotesSafe \land OneValuePerBallot => \\
       & \qquad \qquad \forall Q \in Quorum, b \in Ballot, v \in Value :\\
       & \qquad \qquad \qquad    ShowsSafeAt(Q, b, v) => SafeAt(b, v)
            \end{split}
$$

### 3.2.4 几个不变式

- 任意两个不同Acceptor，如果给同一Bal的Phase1a选票投票，那么Value必须相同；
- 与OneVote的区别是：OneValuePerBallot讨论的是不同的Acceptor之间的关系：

$$
\begin{split}
VotesSafe = &\forall a \in Acceptor, b \in Ballot, v \in Value : \\
              &VotedFor(a, b, v) => SafeAt(b, v)\\
 OneVote = &\forall a \in Acceptor, b \in Ballot, v, w \in Value : \\
              &VotedFor(a, b, v) \land VotedFor(a, b, w) => (v = w)\\
OneValuePerBallot =  
    &\forall a1, a2 \in Acceptor, b \in Ballot, v1, v2 \in Value : \\
       & VotedFor(a1, b, v1) \land VotedFor(a2, b, v2) => (v1 = v2)
\end{split}
$$

# 4. 推理

## 4.1 各个消息的隐含的承诺(不变式)

### Phase1a消息 <"1a", b>:

- 它本身无任何保证，随便发送。

### Phase1b消息$<"1b", a, b, maxVBal[a], maxBal[a]>$：

- 记录了$maxBal[a]'=b$，**承诺**a不会再响应 $Bal <= m.bal$的Phase1a，**承诺**a不会Accept任何 $Bal <m.bal$的Phase2a;
- 如果$maxVBal[a] \neq -1 $  ，表明 $VotedFor(a, maxBal[a], maxVBal[a])$  ，它**如实转达**了$SafeAt(maxBal[a], maxVBal[a])$；我们认为，如实转达也是一种承诺，参见phase2b描述。
- 如果$maxVBal[a] = -1 $  ，表明a没有Accept过任何请求Phase1a，这仅仅是个特例； 

为了便于描述，我们定义另外一个式子：
$$
\begin{split} CannotVoteBetween(a, start, end) &= \\   &\forall x \in [start+1, end-1]: CanntVoteAt(a, x) \end{split}
$$
**因此，Phase1b实际上隐含了**：

​                 $CannotVoteBetween(a, maxVBal[a], b) \land SafeAt(maxBal[a], maxVBal[a])$  

其中前一部分是a的承诺，后面的SafeAt是转达。

### Phase2a消息 $phase2a(b, v)$ :

- $ShowSasfAt(Q, b, v)$

  ShowsSafeAt(Q, b, v)是Proposer在发现收到了某个Quorum Q的所有成员的Phase1b后，计算出来一个新的Value v，并且认为$phase2a(b, v)$是安全的。

  下面是一个例子，假设某个quorum Q包含了$a_1, a_2, a_3$这三个 Acceptor，它们回复的Phase1b四元组分别为$<b, a_1, b_1, v_1>, <b, a_2, b_2, v_2>, <b, a_3, b_3, v_3>$。那么$Phase1b(a_1)$ 隐含了 : 
  $$
  maxBal[a] \geq b \land CannotVoteBetween(a1, b1, b) \land SafeAt(b1, v1)，
  $$
  其他几个也类似。假设$ b_1>=b_2>=b_3$且b1>-1，那么我们得出：                          
  $$
  \begin{split}
  &\land SafeAt(b1, v1) \\
  &\land \forall a \in Q: \\
  & &\land maxBal[a] \geq b \\
  & &\land CannotVoteBetwwn(a, b1, b)
  \end{split}
  $$
  如果取$c = b_1$，那么可以得出   $ShowsSafeAt(Q, b, v)$；

  考虑特殊情况，$b_1=b_2=b_3=-1$，那么取$c=-1$，也能满足  $ShowsSafeAt(Q, b, v)$。

  

  ![2a](Figures/Phase2a.png)

  

- $OneValuePerBallot$

  不同的Proposer，不会用相同的Ballot Number；如果同一个Proposer用相同的Bal执行两次phase1，不会两次都能收到Quorum的响应(因为执行Phase1b(a)后，maxBal[a]被增加了)。

  

### Phase2b消息$phase2b(a, b, v)$：

- 记录了$maxBal[a]'=b$，具体承诺内容参见Phase1b的相应描述。如果这个acceptor正好也发送过对应的phase1b，那么已经承诺过。
- 记录了$maxVBal[a]'=b, maxVal[a]=v'$，按照前面的讨论，这个式子隐含了$SafeAt(b, v)$。这个记录也表示**承诺会如实转达**给后续Bal 更大的Phase1请求。



## 4.3 基于不变式的推导

前面的$ShowSasfAt(Q, b, v)$是如何得出来的？

我们总结下上面的步骤可以发现: Phase1a不会影响正确性，Phase1b是Acceptor根据自己的局部信息在做决策；Phase2a是最复杂的，它根据各个Acceptor的反馈在做决策，而这些Acceptor的状态是变化的(起码maxBal可能变化)；Phase2b 实际上也是各个Acceptor根据局部信息在做决策。

Phase2a计算的v，已经决定了SafeAt(b, v)的成立，它跟Phase2b是否成立无关，如果一个 Acceptor拒绝了 Phase2a，那么是由于$maxBal[a]>b$，而SafeAt(b, v)考察的是 $ < b$的那部分Bal。

### 4.3.1 分三个区间推导

继续按照上面的例子来思考，我们可以把 $<=b$ 的Bal分为三个区间：

$[0, b_1-1], [b_1+1, b-1]$

假设一个Acceptor收到了一个Phase2a，它如何确认自己可以安全地Vote呢？能否保证$SafeAt(b, v)$  回顾下SafeAt的式子：
$$
\begin{split}
SafeAt(b, v) &= \\ 
&\forall c \in 0..(b-1) : NoneOtherChoosableAt(c, v)
\end{split}
$$
我们分三个区间来讨论：

#### 区间$[0, b_1-1]$

在发送Phase2a前，已经收到了$a_1$的四元组$<b, a_1, b_1, v_1>$，即$VoteFor(a_1, b_1, v_1)$为true，这个本身隐含了$SafeAt(b_1, v_1)$为true。

#### 区间$[b_1, b_1]$

这个基于下面的式子推理： 
$$
OneValuePerBallot \land VotedFor(a_1, b_1, v_1) =>\\
    \qquad  \qquad   \qquad  \qquad  \qquad  NoneOtherChoosableAt(b_1, v_1)
$$

#### 区间$[b_1+1, b-1]$

$ShowsSafeAt(Q, b, v)$已经说明
$$
\exist Q \in Quorum: \\
   \qquad \qquad \forall a \in Q: CannotVoteBetween(a, b_1, b)
$$
那么在区间$[b_1+1, b-1]$就不可能选定任何Value，因为任意两个Quorum都是相交的。



## 4.4 一张图说明推导过程

  ![allinone](Figures/AllInOne.png)



# 5 再分析下并发场景

简单来说，如果一轮未能进入Phase2的过程(Phase1b未构成Quorum)，不够成任何value的选定，不可能影响chosen的值。所以我们跳过这种问题。只有进入phase2a的过程，才有可能导致value被选定，才会影响Consensus。也就是说，无休止的重试是合法的。

假设Propser p1顺利完成了phase1，收到了某个quorum Q1内所有成员的phase1b消息，然后发送phase2a$phase2a(b,v)$。但是在p1收齐某个Quorum Q2的phase2b之前，另外一个proposer p2开始了phase1。我们假设p2使用的Ballot Number  $b'$。

### 假设:  $b'<b$

这个场景下，p2的消息，都会被Q1内所有acceptor拒绝，所以p2不可能进入Phase2a阶段。由于$b' < b$，对 p1的phase2也没有任何影响。

### 假设:  $b'>b$

- **场景一:** 假设存在至少一个Quorum Q2，Q2里面所有的acceptor在给p1发送了phase2b后，才处理p2的phase1。这就表示$ChosenAt(b, v)$ 成立。剩下的问题时：p2如何保证不会选定v以外的Value。由于 Q2是多数派，p2收到的phase1b消息中，至少有一个包含了<b, v>，也就是保证了SafeAt(b, v)。
- **场景二:** 场景一以外的其他情况，即：对于任何一个Quorum Q, Q里至少有一个acceptor，先处理了p2的phase1a，然后才处理p1的phase2a。先处理p2的$phase1a(b')$的acceptor a, maxBal[a] 变成了 $b'$，所以不会Accept phase2a(b, v)，导致<b, v>无法被选定，因为根本不够成Quorum。既然$(b,v)$不可能被选定，不影响chosen的值。 p2的执行过程，跟p1是一样的。

 把上面例子中的p2换成p2, p3等多个，且对应的Bal都大于b，那么分析过程也是结论是类似的。







