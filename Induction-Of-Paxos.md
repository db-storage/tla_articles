#  Paxos的归纳法推理-(从TLA+ Spec抽取)

---

**初衷**

在理解Paxos的TLA+ Spec过程中，发现其中其实隐含了Paxos正确性的基于不变式(Invariance)的归纳法证明。由于TLA+  spec不易理解，且基本没有高亮显示，所以先抽取其中相对易于理解的部分，大部分改用Latex公式表示，并辅以一些图形，希望能抛砖引玉。部分内容仍然是 TLA+格式的，但是近来通过文字或者表格来辅助理解。

这些证明是从Paxos的TLA+ Spec根据自己的理解抽取的，并非新东西，如果有发现不准确的地方，欢迎批评指正。

**为什么要写这么理论化的东西？**

Paoxs已经这么难懂，为什么还要用形式化方法去说理论？其实形式化往往是更准确的，在理想情况下可能还是极简的，不一定是复杂的。比如：$SafeAt(b,v)$ 表示：不可能用<=b的任何Ballot Number，选定value v以外的任何值。虽然后者意义上也没用问题，但是很容易让人抓不住重点，而且在做推理或者证明时变得极其繁琐而事实上难以描述。

# 1. 共识 (Consensus)的极简定义

## 1.1 Consensus的定义

- Consensus的定义：chosen的元素小于等于1
  $$
  Consensus =  Cardinality(chosen) \leq 1
  $$

# 2. Paxos的两个阶段回顾

这一部分回顾下Paxos的两个阶段，从paxos的 TLA+里面摘取了其公式表示。

## 2.1 常量和变量定义部分

我们先抽取一些必要的变量和常量定义 。这些对于有计算机或者数学基础的读者应该不难 。

| 名称     | 类型 | 含义                                                         |
| -------- | ---- | ------------------------------------------------------------ |
| Acceptor | Set  | 所有接收者的集合                                             |
| Quorum   | Set  | 里面的每个成员，例如Q1，也是一个Set。且Q1是Acceptor的subset  |
| maxBal   | Map  | maxBal[a]表示acceptor a响应过的最大Ballot Number，在phase1b修改。只增不减 |
| maxVBal  | Map  | Max Voted Ballot。maxVBal[a]表示acceptor a曾经Vote过的最大的Ballot Number，在phase2b修改。只增不减 |
| maxVal   | Map  | Max Voted Value。 maxVal[a]表示acceptor a曾经Vote过的最大的Ballot Number对应的Value，在phase2b修改。<"2b", a, maxVBal[a], maxVal[a]>构成了一个Phase2b消息四元组 |
| Votes    | Map  | votes[a] 记录acceptor a曾经vote过<Bal, Value>元组            |
| msgs     | Set  | 所有发过的消息集合(在这个验证模型中，msg一直保留)            |
| Chosen   | Set  | 被选定的Value的集合                                          |



```tla
CONSTANT Acceptor, 
         Quorum     \* The set of "quorums", where a quorum" is a 
                    \*   "large enough" set of acceptors
CONSTANT Ballot

VARIABLE maxBal   \* maxBal[a] is a ballot number.  Acceptor a will cast
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

感兴趣的读者可以自己计算下，满足上面的式子，Q1, Q2不一定都达到Acceptor的半数以上。

在后面的很多式子中，我们用到逻辑与$\land$和逻辑或$\lor$，它们与我们在关系代数中学到的含义一样。对于 $a \land b$，如果$a$的为false，则不会去尝试计算后面的$b$。

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
在Paxos的TLA+ spec里面，没有模拟许多通信信道，而是把所有msg放到一个集合(msgs)里面。Send(m)就是修改msgs，使得msgs的新状态为：msgs和{m}的并集。$msg'$表示msg被修改后的状态。

## 2.3 Phase1b

Phase1b过程，是Acceptor 根据自己变量去判断，能否响应一个 Phase1a消息，如果符合条件，则响应一个Phase1b。参数 a是Acceptor自己的标识。
$$
\begin{split}Phase1b(a) = & \land \exists m \in msgs : \\                  & \qquad \land m.type = "1a"  \land \space m.bal > maxBal[a]\\                  & \qquad \land maxBal' = [maxBal\space EXCEPT \space ![a] = m.bal]\\                  & \qquad \land Send([type |-> "1b", acc |-> a, bal |-> m.bal, \\                  & \qquad\qquad mbal |-> maxVBal[a], mval |-> maxVal[a]])\\              &\land UNCHANGED <<maxVBal, maxVal>>\end{split}
$$


其中最重要的前提条件是：存在一个 "1a" msg m，m.bal 大于a自己的maxBal。即：

​           $ m.type = "1a" \land \space m.bal > maxBal[a]$。

注意，在前提成立的情况下，Phase1b做了两件事(其他所有变量都是Unchanged)：

1) 把maxBal做了修改，实际就是：$maxBal[a]' = m.bal$;

2) 构建 "1b"消息四元组: <"1b", a, m.bal, maxVBal[a], maxBal[a]>。注意如果a从未执行过phase2b，maxVBal[a]就是-1，此时maxBal[a]为空 。

3) Send  “1b"消息，Send的含义在前面有解释。**注意：**一旦发送了"1b"，$maxBal[a]$ 就增加了，所以下次收到Ballot Number相同的Phase1a，不会再相应。

## 2.4 Phase2a

**前提条件：**

​      1) 没有发送过bal为b的2a消息(避免重复)；

​       2) 存在一个Quorum Q，里面的每个成员都回复过Phase1b。

**确定val，构建Phase2a消息:**

​      1) Q1b为该Qurom Q发送的Phase1b消息集合；

​      2) Q1bv为Q1b中，所有$m.mbal \geq 0$的消息集合；

​      3）如果Q1bv为空，说明Q里面所有成员都没有Vote过，所以v由proposer自己决定；

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

​     一个Acceptor执行Phase2b的过程，也分为大致以下几个部分。

### 检查前提条件

​    存在一个"2a"消息m，满足 $m.bal \geq maxBal[a]$。

### 修改本Acceptor的变量

​       $ maxBal[a]'=m.bal$

​       $maxVBal[a]' = m.bal] $

​       $maxVal[a]'= m.val]$

### 发送"2b"消息(代表Vote)

   "2b"消息带有Acceptor的ID(参数a)，以及从"2a"消息m里面获取的$m.bal$和$m.val$ 。
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
**FAQ: 为什么我还需要修改 $maxBal[a]'$?** 

- 因为执行Phase2b的Acceptor，不一定执行了Phase1b ，所以可能根本没有修改。

# 3. 推理相关的函数/不变式定义

下面这些定义不是2阶段的一部分，但是对于理解两阶段为什么是对的，却是很重要的。

## 3.2 基本函数定义

- VotedFor(a, b, v):  Acceptor a曾经投票给选票($b$, $v$)；

- ChosenAt(b, v): 存在一个Quorum Q，Q里面每个成员都曾经投票给($b$, $v$)。我们常说的形成决议/形成多数派/选定一个值/Commit，都是这个含义；

- DidNotVoteAt(a, b):  Acceptor a从未给 $BN = b$ 的选票投票；

- CannotVoteAt(a, b)： Acceptor a不能再给任何 $BN = b$的选举投票，因为$maxBal[a] >b$并且DidNotVoteAt(a, b)。 为什么需要 DidNotVoteAt? 实际上允许同一个phase2a 请求重复被应答。
  $$
  \begin{split}
  VotedFor(a, b, v) =\space &<<b, v>> \in votes[a]\\
  ChosenAt(b, v) = \space  &\exists Q \in Quorum :   \\
                     &  \forall a \in Q : VotedFor(a, b, v) \\
  chosen = &\{v \in Value : \exists b \in Ballot : ChosenAt(b, v)\}\\
    
  DidNotVoteAt(a, b) = &\forall v \in Value : ~ VotedFor(a, b, v) \\
  CannotVoteAt(a, b) = &\land maxBal[a] > b\\
              &\land DidNotVoteAt(a, b)\\
  \end{split}
  $$
  

### 3.2.1 NoneOtherChoosableAt(b, v)

- 意义: 除了v以外，不可能用 Bal b选定其他value。注意：这个谓词公式，并**没有隐含$ChosenAt(b,v)$**为true。

- 定义/实际判断方法: 存在一个Quorum Q，其中任意一个Acceptor a，要么已经投票 (b,v)，要么没有为Ballot b投票，且永远不会为b投票。

- 反证：假设不成立，即存在某个Value $w$, $w\ne v$, 并且有ChosenAt(b, w)。则必须有某个 Quorum R，R内所有Acceptor都需要给(b, w)投票，根据Quorum的含义，R必然与 Q有交集，这与前提矛盾。
  $$
  \begin{split}
  NoneOtherChoosableAt(b, v) = \\
  \exists Q \in Quorum : \\
       & &\forall a \in Q : VotedFor(a, b, v) \lor CannotVoteAt(a, b)
       \end{split}
  $$
  

### 3.2.2 SafeAt(b, v)

- 含义： 不可能用小于b的Ballot Number，选定v以外的任何值。

- 注意：不能选定，**不代表不能Accept/Vote**， 只要vote不形成Quorum即可。

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

- 存在一个Quorum Q，同时满足下面的Cond 1和Cond2：
- **Cond 1:** Q内任意一个Acceptor a，满足$maxBal[a] >= b$
- **Cond2:** 存在一个小于b的Ballot c，同时满足下面两个条件：
  - **Cond 2.1:** 如果 $c \ne -1$，则满足：Q中至少有一个Acceptor a, a给(b, v)投过票。注意，如果 $c == -1$，则没有限制，这是一个特殊场景，即所有Acceptor都没有投过票。
  - **Cond 2.2:** Q中没有任何Acceptor a，给[c+1, b-1]之间的任何Ballot Number投过票。即Q里面的所有 Acceptor在[c+1, b-1]这个区间，都完全没有投票，只增加了maxBal。

其中：

- Cond 1和Cond 2.2 保证了[c+1, b-1]这个区间不可能选定任何值(因为已经有一个 quorum，其成员不可能在这个Bal区间内Vote)。
- Cond 2.2的定义，如果c不等于-1，则有VotedFor(a,c,v)，那么这个Vote发生时已经保证了SafeAt(c,v)；
  VotedFor(a,c,v)和OneValuePerBallot，保证了如果Ballot c选定了某个值，那么这个值只能是v，也就是NoneOtherChoosableAt(c, v)；
- ShowsSafeAt(Q, b, v) 与 SafeAt(b, v)的最大不同点：前者只需要收集某个Quorum的response，而不需要全部，是个可行的Enabling Condition。

### 3.2.4 几个不变式

- 任意两个不同Acceptor，如果给同一Bal的Phase1a选票投票，那么Value必须相同
- 与OneVote的区别是：OneValuePerBallot讨论的是不同的Acceptor之间的关系：

$$
\begin{split}
VotesSafe = &\forall a \in Acceptor, b \in Ballot, v \in Value : \\
              &VotedFor(a, b, v) => SafeAt(b, v)\\
 OneVote = &\forall a \in Acceptor, b \in Ballot, v, w \in Value : \\
              &VotedFor(a, b, v) \land VotedFor(a, b, w) => (v = w)\\
OneValuePerBallot =  
    &\forall a1, a2 \in Acceptor, b \in Ballot, v1, v2 \in Value : \\
       & VotedFor(a1, b, v1) /\ VotedFor(a2, b, v2) => (v1 = v2)
\end{split}
$$

# 4. 归纳推理

## 4.1 各个消息的隐含的不变式

### Phase1a消息 $phase1a(b, v)$

- 它本身无任何保证，随便发送。

### Phase1b消息 $phase1b(a, b_1, v_1)$

- 这里先不考虑$b_1$为 -1的场景

- $VotedFor(a, b_1, v_1)$  ，它隐含了$SafeAt(b_1,v_1)$

- $\forall x \in [b_1+1, b-1]: CannotVoteAt(a,x)$

- 为了后续描述方便，这里增加一个定义，注意lower和upper不在$x$的范围内：
  $$
  \begin{split}
  CannotVoteBetween(a, lower, upper) &= \\ 
  &\forall x \in [lower+1, upper-1]: CannotVoteAt(a,x)
  \end{split}
  $$
  

### Phase2a消息$phase2a(b, v)$：

- $ShowSasfAt(Q, b, v)$

  综合phase1b消息得出

- $OneValuePerBallot$

  不同的Proposer，不会用相同的Ballot Number；即使用相同的Ballot Number，执行两次phase1，只有一个能收到Quorum的回复。

### Phase2b消息$phase2b(a, b, v)$

- $VoteFor(a, b, v) => SafeAt(b,v)$

 

## 4.3 基于不变式的归纳推理

==Voting.tla 里面的部分才是Paxos的核心。Paxos.tla 更多是这个理论的具体实现。==

在前述部分的基础上，我们可以描述Voting模块部分的推理过程。假设OneValuePerBallot可以保证(先不管如何做到的)，且每个Voter的每次投票，都需要保证安全是否可以做到呢？

我们首先得知道投票安全的含义是什么，然后说怎么保证。下面是个简单的过程描述。



![tu](https://github.com/db-storage/tla_articles/raw/master/Figures/VoteFor-Safety.png)



下面是最核心部分，我们先用图说明如何从ShowSafeAt(Q, b, v)推理出SafeAt(b,v)，这个推理成立，即可保证VotesSafe。



## 4.4 还在纠结并发导致的问题？

假设在Propser p1顺利完成了phase1a，收到了了某个quorum Q1内所有成员的phase1b消息，然后发送phase2a消息$phase2a(b,v)$，但是在p1收到phase2b消息之前，另外一个proposer p2开始了phase1。我们假设p2使用的Ballot Number  $b'$。

### 场景1:  $b'<b$

这个场景下，p2的消息，都会被Q1内所有acceptor拒绝，所以没法形成Quorum。对 p1的phase2没有任何影响。

### 场景2:  $b'>b$

- 存在一个Quorum Q2，它们在给p1发送了phase2b后，才收到了p2的phase1。那么Q2内所有成员给p2发送的phase1b消息，都会包含$VotedFor(b, v)$，这就保证了$VotesSafe(b, v)$
- 其他情况， Accept p1的phase2b消息构不成Quorum，其他成员先收到了p2的phase1，那么它们的maxBal 变成了 $b'$，不可能再让$(b, v)$被选定。
- 既然$(b,v)$不可能被选定，那么整个问题就变成了p2用更大的Ballot Number $b'$ 执行paxos过程如何保证不会选定多个value的问题。曾经accept过$(b,v)$的少数派Acceptor，即使完全宕机，也不影响正确性。

## 4.4 其他部分解析

### 3.4.1 定理 AllSafeAtZero

- 这个理论之所以成立，是因为不可能用$<0$ 的Ballot形成决议，因为$<0$的选票，不会被 Accept.

### 3.4.2 定理 ChoosableThm

- 这个是对"选定"的一个断言：只要 ChosenAt(b, v)成立，NoneOtherChoosableAt(b, v)一定成立。
  $$
  \begin{split} 
  NoneOtherChoosableAt(b, v) =   \space &\exists Q \in Quorum : \\
          &\forall a \in Q : VotedFor(a, b, v) \lor CannotVoteAt(a, b)\\
          SafeAt(b, v) = & \space \forall  c \in 0..(b-1) : NoneOtherChoosableAt(c, v)
  \end{split}
  $$
  

  

### 3.4.3 OneVote

- 如果某个Acceptor先后给(b, v) 和 (b, w)投票，那么v一定跟w相等
- 这个实际上隐含了: 一个 Acceptor给同一Ballot投票多次是允许的，只要Value不变

### 3.4.4 定理 VotesSafeImpliesConsistency

- 如果能满足 VotesSafe和OneVote都成立，那么选定的最多只有一个值，不会选定多个。其中:
  - VotesSafe: 保证更小的**Ballot不会形成其他Value的决议**
  - OneVote: **同一Ballot**，不会有多个Value被投票，所以不会选定多个值



### 3.4.5 定理 ShowsSafety

- 定理的含义:  如果 VotesSafe 和 OneValuePerBallot成立，那么ShowsSafeAt(Q, b, v) => SafeAt(b, v)。
- 这个定理就是3.3节推理过程图的形式化描述。

$$
\begin{split}
THEOREM \space \space OneValuePerBallot => &OneVote\\
THEOREM \space \space VotesSafeImpliesConsistency = \\
          &TypeOK \land VotesSafe \land OneVote\\
          &=> chosen = \{\}  \lor \exists v \in Value : chosen = \{v\} \\
\end{split}
$$

$$
\begin{split}
ShowsSafeAt(Q, b, v) = \\
  &\land \forall a \in Q : maxBal[a] \geq b \\
  &\land \exists c \in -1..(b-1) : \\
     &  \quad \land (c \neq -1) => \exists a \in Q : VotedFor(a, c, v) \\
     &  \quad \land \forall d \in (c+1)..(b-1), a \in Q : DidNotVoteAt(a, d) \\
\end{split}
$$

$$
\begin{multline}
THEOREM \space \space ShowsSafety = \\
         TypeOK \land VotesSafe \land OneValuePerBallot =>\\
               \forall Q \in Quorum, b \in Ballot, v \in Value : \\
               ShowsSafeAt(Q, b, v) => SafeAt(b, v)
 \end{multline}
$$





## 3.5 Voting的一些FAQ

### 3.5.1 如何用归纳法证明 ShowsSafety?

- 根据ShowSafeAt(Q, b, v)的定义，我们将Ballot分为3个区间，[-1, c-1]、c和[c+1, b-1]。

- 如果 $c == -1$，，则Q内Acceptor都没有投过， SafeAt(b, v)成立。

- 如果$c \ne -1$，分别考察三个区间，证明这三个区间都不可能选定v 以外的值。

  
  
  * SafeAt(c, v)本身就意味着[-1, c-1]这段没问题
  
  $$
  ShowsSafeAt(Q, b, v) \land c \neq -1\\ 
     => \exists a \in Q: VotedFor(a, c, v) \\
     => SafeAt(c, v)
  $$
  
  
  
  - NoneOtherChoosableAt(c, v)
  
  $$
  \begin{split}
  OneValuePerBallot \land VotedFor(a, c, v) \\
      =>  & \nexists w \in Value, a \in Q :\\
             &   &              \land w \neq v \\
             & &              \land  VotedFor(a, c, w)\\ 
  \end{split}
  $$
  
  
  

(* ShowSafeAt本身 和 C 不等于-1，蕴含了 Q内所有成员，不会为[c+1, b-1]区间 *)
  (* 的任意一个BN 投票，再考虑 QuorumAssumption 限制，即任意两个Quorum必然  *)
  (* 相交，所以不可能有某个Quorum R存在，它用[c+1, b-1]区间的某个BN形成决议  *)
$$
  \begin{split}
  ShowsSafeAt(Q, b, v) \and c \neq -1\\
    =>   &\land \forall a \in Q : maxBal[a] \geq b \\
         &\land \forall d \in (c+1)..(b-1), a \in Q : DidNotVoteAt(a, d)\\
   =>  &\forall a \in Q, d \in (c+1)..(b-1): CannotVoteAt(a, d)\\
  \forall a \in Q, d \in (c+1)..(b-1): \\
  &CannotVoteAt(a, d) \land QuorumAssumption \\
  =>  &\forall d \in (c+1)..(b-1), v \in Value: \lnot ChosenAt(d, w) 
  \end{split}
$$

  


### 3.5.2 ShowSafeAt，并没有要求maxBal[a]<=b，而是maxBal[a]>=b，那么怎么阻止<=b的ballot去形成决议呢？

$$
ShowsSafeAt(Q, b, v) =
  \forall a \in Q : maxBal[a] \geq b
$$



- 虽然要求Quorum的 maxBal[a] >= b，但是VoteFor时，必须有maxBal[a] <= b。这样就只可能为b形成决议，而 < b的x，VoteFor 不会被执行。
  $$
  \begin{split}
  VoteFor(a, b, v) =\\
      & \land maxBal[a] \leq b\\
      & \land ...
      \end{split}
  $$
  

###  3.5.3 Voting.tla 里面 OneValuePerBallot 是怎么保证的？

- 参见VoteFor的条件，实际上是检查了所有acceptor的vote，对于数学抽象可以这么写。但是实际上系统中很难原子地检查所有Acceptor的vote。

$$
\begin{split}
VoteFor(a, b, v) =&\\
   &\land ... \\
   &\land \forall c \in Acceptor 	\setminus {a} : \\
    & &       \forall vt \in votes[c] : (vt[1] = b) => (vt[2] = v)\\
 \end{split}
$$



- 对于Paxos，实际上从两方面保证：1) 不同的Proposer可用的Ballot Number是不同的；2) 同一Proposer，在使用同一个Ballot Number发送Phase2a时，不会修改Value。3) 如果用同一个Ballot Number执行两次Phase1，那么第二次时



