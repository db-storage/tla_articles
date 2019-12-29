#  Paxos的归纳法推理-(从TLA+ Spec抽取)

---

**初衷**

在理解Paxos的TLA+ Spec过程中，发现其中其实隐含了Paxos正确性的基于不变式的归纳法证明。由于TLA+  spec不易理解，且基本没有高亮显示，所以先抽取其中相对易于理解的部分，用Latex公式表示，并辅以一些图形，希望能抛砖引玉。

这些证明是从Paxos的TLA+ Spec根据自己的理解抽取的，并非新东西。

**为什么要写这么理论化的东西？**

Paoxs已经这么难懂，为什么还要用形式化方法去说理论？形式化后可能是极简的，不一定是复杂的。其实用公式描述很多内容往往更简单，比如：$SafeAt(b,v)$ 表示：不可能用<=b的任何Ballot Number，选定value v以外的任何值。虽然后者意义上也没用问题，但是很容易让人抓不住重点，在推理或者证明时变得极其繁琐。

# 1. 共识 (Consensus)的极简定义

- 集合chosen: 选定的值的集合

- Consensus的定义：被选定的Value个数小于等于1
  $$
  Consensus =  Cardinality(chosen) \leq 1
  $$
  

# 2. Paxos形成共识的两个阶段

回顾下Paxos的两个阶段：

# 3. 一些定义

## 3.1 常量和变量定义部分

//TODO: 换成表格

```tla
------------------------------- MODULE Voting ------------------------------- 
EXTENDS Integers 
-----------------------------------------------------------------------------
CONSTANT Value,     \* The set of choosable values.
         Acceptor,  \* A set of processes that will choose a value.
         Quorum     \* The set of "quorums", where a quorum" is a 
                    \*   "large enough" set of acceptors
CONSTANT Ballot

VARIABLE votes,   \* votes[a] is the set of votes cast by acceptor a
         maxBal   \* maxBal[a] is a ballot number.  Acceptor a will cast
                  \*   further votes only in ballots numbered \geq maxBal[a]      
```


$$
\begin{split}

ASSUME\space\space QuorumAssumption =\\ & \land \forall Q \in Quorum : Q \subseteq Acceptor\\
                           &\land  \forall Q1, Q2 \in Quorum : Q1 \cap Q2 \neq \{\}  \\


THEOREM \space\space QuorumNonEmpty = \\ 
&\forall Q \in Quorum : Q \neq \{\} \\
\end{split}
$$



## 3.2 基本函数定义

- VotedFor(a, b, v):  Acceptor a曾经投票给选票($b$, $v$)

- ChosenAt(b, v): 存在一个Quorum Q，Q里面每个成员都曾经投票给($b$, $v$)。我们常说的形成决议/形成多数派/选定一个值，都是这个含义。

- DidNotVoteAt(a, b):  Acceptor a从未给 BN = b 的选票投票

- CannotVoteAt(a, b)： Acceptor a不能再给任何 BN = b的选举投票，因为maxBal[a] >b并且DidNotVoteAt(a, b)。 为什么需要 DidNotVoteAt? 实际上允许同一个phase2a 请求重复被应答。
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

- 定义: 存在一个Quorum Q，其中任意一个Acceptor a，要么已经投票 (b,v)，要么没有为Ballot b投票，且永远不会为b投票。

- 意义: 除了 v以外，不可能有任何其他value，可以用Ballot  b被选定

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

- 注意：不能选定，**不代表不能Accept**，只是不会形成多数派

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

- Cond 1和Cond 2.2 保证了[c+1, b-1]这个区间不可能选定任何值。
- Cond 2.1的定义，如果c不等于-1，则有VotedFor(a,c,v)，那么这个Vote发生时已经保证了SafeAt(c,v)；
  VotedFor(a,c,v)和OneValuePerBallot，保证了如果Ballot c选定了某个值，那么这个值只能是v，也就是NoneOtherChoosableAt(c, v)；
- ShowsSafeAt(Q, b, v) 与 SafeAt(b, v)的最大不同点：前者只需要收集Quorum的response，而不需要全部，是个可行的Enabling Condition。

### 3.2.4 OneValuePerBallot

- 任意2个不同Acceptor，如果给同一Ballot的选票投票，那么Value必须相同
- 与OneVote的区别是：OneValuePerBallot讨论的是不同的Acceptor

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

### Phase1a消息

无任何保证，随便发送

### 每一条Phase1b消息 $phase1b(a, b_1, v_1)$

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



## 4.4 还在担心并发导致的问题？

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



- 对于Paxos，实际上从两方面保证：1) 不同的Proposer可用的Ballot Number是不同的；2) 同一Proposer，在使用同一个Ballot Number发送Phase2a时，不会修改Value。

### 3.5.4 有了Voting.tla，为什么还需要Paxos?

- Voting是纯粹的理论和推理，描述了要做到Consensus，需要保证什么。其中很多内容没有考虑具体实现，例如，VoteFor里面的判断所有Acceptor状态、投票都认为是原子操作。但是实际不可能让别的Acceptor停下来，等待自己干完活。

- Paxos描述如何实现，基于分布式系统和消息通信机制。


### 3.5.5 Voting.tla 里有没有类似于Phase1的操作？

-  IncreaseMaxBal比较接近。但是非常简要，纯数学抽象表示，没有描述消息过程。

- 如果没有IncreaseMaxBal这个步骤，那么就没法取得进展了。因为 ShowsSafeAt就需要各个Acceptor的 maxBal[a]>=b，就是隐含执行了phase1a。





