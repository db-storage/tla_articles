## 3.2 Paxos的证明，如何对应到状态及证明公式？

Paxos.tla里面，写的Inv是这样的(可能需要把 Voting 里面的正确性理论和Paxos的Inv分开，但是又能关联上)：

其中一点： Paxos的不变式包含了对2a的保证，**即只要有<b,v>这个msg存在，就已经安全了**。这个跟我之前的证明是一致的。

Inv == /\ TypeOK

​    /\ \A a \in Acceptor : IF maxVBal[a] = -1

​                THEN maxVal[a] = None

​                ELSE <<maxVBal[a], maxVal[a]>> \in votes[a]

​    /\ \A m \in msgs : 

​       /\ (m.type = "1b") => /\ maxBal[m.acc] \geq m.bal

​                  /\ (m.mbal \geq 0) =>  

​                    <<m.mbal, m.mval>> \in votes[m.acc]

​       /\ (m.type = "2a") => /\ \E Q \in Quorum : 

​                     V!ShowsSafeAt(Q, m.bal, m.val)

​                  /\ \A mm \in msgs : /\ mm.type = "2a"

​                            /\ mm.bal = m.bal

​                            => mm.val = m.val

​    /\ V!Inv





整体来说，证明基于以下方法：

1) 初始状态安全；

2）每个新产生的选票是安全的；

3) 每一步，对于已有的选票是安全的。



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

**要点：** 假设当前的ballot是b，执行的acceptor是$a$，对于任意已经存在的选票$<b_1, v_1>$，那么必有一个Quorum $Q1$，它保证了$SafeAt(b_1,v_1)$。可以分为三种情况：

1) $b == b_1$，之前$a$一定不属于$Q1$;

2) $b<b_1$, 之前$a$一定不属于$Q1$;

3) $b>b_1$，之前$a$可能属于$Q1$，也可能不属于。如果不属于，不影响。如果属于，那么保障的条件，只涉及a在 $<b_1$的Ballot上的动作， $>b_1$是不受限制的，不违背承诺。



**其实对于 2b也类似。**

**对于Phase2a，因为它产生了一个新的<b, v>，所以是要考虑自身的Safety以及其他既存的vote**



$Inv \land Phase1b  => Inv'$

没有执行Accept，也没有产生新的Value。需要证明的是：已有的Vote/Value，是安全的。



### 对 Phase2a 成立

$Inv \land Phase2a  => Inv'$

产生了新的 $<b, v>$。需要证明它不影响 $OneValuePerBallot$。

由于Phase1a 是 $>$，不是$>=$，同一个Ballot不可能出现两个Value。

如何证明 $SafeAt(b,v)$? 



### 对 Phase2b 成立

$Inv \land Phase2b  => Inv'$

不产生新的$<b, v>$，只是影响了$VotedFor(a, b, v)$。那么这个Vote是否Safe? 

实际上Phase2a已经解决了SafeAt(b, v)的问题，即<b, v>自身的安全性。

仍然考虑某个VotedFor如果 a 属于某个$<b_1, v_1>$ 的 Quorum $Q1$，那么。。。