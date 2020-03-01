把">"写成">="会带来多大差异？ 对比下Paxos的TLA+ Spec和Phxpaxos

# 1. 简介

我在春节期间写过一篇关于Paxos正确性背后的数学的文章（[链接](https://zhuanlan.zhihu.com/p/104463008)）。那么这类形式化的东西到底有没有用？对于工程实践的作用到底有多少？我想读者中有顾虑的不少。

这篇文章从Paxos的 Phase1b公式出发，去理解下微信团队的phxpaxos的实现，分析该实现中与TLA+ spce的差异，以及这种差异在什么场景下会存在什么问题。

先说下结论： 

- 虽然phxpaxos的文档里面说是遵照paxos made simple一文实现的，但是事实上phxpaxos的代码Phase1b与标准Paxos协议是有差异的；
- 就目前phxpaxos的实现来说，这个差异并没有导致正确性问题，但是代码是以串行化了一些操作为代价的；
- 但是如果把phxpaxos的代码稍微修改，去掉这个串行化，并制造一些特殊的事件序列，可以演示出这种差异会带来的问题(违背了OneValuePerBallot)。



# 2. 差异在哪？

## 2.1 原文里的描述

Phase 1. (a) A proposer selects a proposal number n and sends a prepare request with number n to a majority of acceptors.

(b) If an acceptor receives a prepare **request with number n greater than** that of any prepare request to which it has already responded, then it responds to the request with a promise not to accept any more proposals numbered less than n and with the highest-numbered pro- posal (if any) that it has accepted.



## 2.2 TLA+ Spec里的式子

在TLA+ spec中，Phase1b的描述如下：
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


## 2.3 Phxpaxos里面的对应代码

Acceptor对应Phase1b的函数是OnPrepare()。

```c++
int Acceptor :: OnPrepare(const PaxosMsg & oPaxosMsg)
{
    //省略。。。    
    BallotNumber oBallot(oPaxosMsg.proposalid(), oPaxosMsg.nodeid());
    // 注意，是 >=，不是>
    if (oBallot >= m_oAcceptorState.GetPromiseBallot())
    {
       //......
     }
  ...
}
```



## 2.4 差异

可以看出，Phxpaxos的Phase1b 实现，与标准paxos协议是有差异的。$">"$ 变成了$">="$。在之前的文章中我们提过，这个$">"$对于保证OneValuePerBallot是必须的，没有它就没有了正确性保证。

那么Phxpaxos 这么实现，是不是一定有问题呢？这里面分两个方面：

### 2.4.1 两个不同的Proposer，会用相同的BallotNumber么？



```c++
class BallotNumber
{
    //省略
    bool operator >= (const BallotNumber & other) const
    {
        if (m_llProposalID == other.m_llProposalID)
        {
            return m_llNodeID >= other.m_llNodeID;
        }
        else
        {
            return m_llProposalID >= other.m_llProposalID;
        }
    }
    //...
    uint64_t m_llProposalID;
    nodeid_t m_llNodeID;
};
```



- Ballot里面，实际上包含了NodeID。
- 不同的Proposer，NodeID不同(这里没有展开分析，假定一定可以做到不同)。

所以，如果NodeID是不同的，phxpaxos不会出现不同的proposer共用BallotNumber的情况。



### 2.4.2 同一个Proposer，会用相同的BallotNumber么？

如果正常运行的proposer，代码很容易做到不重用相同的ProposalID。但是考虑如下情形：

1. Proposer P1发送BallotNumber为b1的Phase1a消息；
2. P1收到了Quorum个Acceptor回复的在"1b"消息，但是不包括自己(假设P1自己的磁盘太忙，log迟迟没有写成功)。
3. P1发送 2a消息$<b1, v1>$给各个Acceptor，然后自己宕机。
4. P1重启，自己没有关于b1的任何记录。
5. P1再次用Ballot Number b1执行Phase1，又成功。
6. P1提议$<b1, v2>$，又被Accept。



上面的顺序在Phxpaxos中会发生么？我们看看代码：



```c++
void Proposer :: Prepare(const bool bNeedNewBallot)
{
     PaxosMsg oPaxosMsg;
    oPaxosMsg.set_msgtype(MsgType_PaxosPrepare);
    oPaxosMsg.set_instanceid(GetInstanceID());
    oPaxosMsg.set_nodeid(m_poConfig->GetMyNodeID());
    oPaxosMsg.set_proposalid(m_oProposerState.GetProposalID());

    m_oMsgCounter.StartNewRound();

    AddPrepareTimer();
    //只有一个参数，RunType是默认值BroadcastMessage_Type_RunSelf_First
    BroadcastMessage(oPaxosMsg);
}

```



```c++

int Base :: BroadcastMessage(const PaxosMsg & oPaxosMsg, const int iRunType, const int iSendType)
{
    //...
    if (iRunType == BroadcastMessage_Type_RunSelf_First)
    {   //现在本地执行 OnReceivePaxosMsg
        if (m_poInstance->OnReceivePaxosMsg(oPaxosMsg) != 0)
        {
            return -1;
        }
    }
    //后面才真正发送网络消息    
    string sBuffer;
    int ret = PackMsg(oPaxosMsg, sBuffer);
    if (ret != 0)
    {
        return ret;
    }

    ret = m_poMsgTransport->BroadcastMessage(m_poConfig->GetMyGroupIdx(), sBuffer, iSendType);
}
```



对于MsgType_PaxosPrepare，OnReceivePaxosMsg会走到OnPrepare。可以看出，这个函数中，已经把BallotNumber做了持久化。

```c++
int Acceptor :: OnPrepare(const PaxosMsg & oPaxosMsg)
{
      //省略 
        m_oAcceptorState.SetPromiseBallot(oBallot);
        int ret = m_oAcceptorState.Persist(GetInstanceID(), GetLastChecksum());
        if (ret != 0)
        {
            BP->GetAcceptorBP()->OnPreparePersistFail();
            PLGErr("Persist fail, Now.InstanceID %lu ret %d",
                    GetInstanceID(), ret);
            
            return -1;
        }
}
```



只要完成了持久化，对照上面的步骤4，P1重启后就可以查到之前用过的ProposalID，下次不会用重复的BallotNumber。

所以，在这个代码实现中，同一个proposer 也不会用相同的BallotNumber。**但这是有代价的**：在本地完成持久化之后，才能给其他节点发送"1a"消息，增加了一次持久化的延迟。在现有的环境下，存储持久化的延迟，往往远大于局域网的延迟。



# 修改代码验证下 用">="可能带来的问题

之前我们已经看到，phxpaxos虽然与标准paxos不一致，但是由于在Ballot Number中包含了NodeID，并且总是让节点的Acceptor先执行Phase1b，所以并没有出现正确性问题。

但是如果不让本节点的Acceptor先执行Phase1b，真的会出现问题么？如果Proposer给所有Acceptor并发发送“1a"，那么理论上本地的Acceptor可能最后完成持久化，那么可能出现不同的问题。

对phxpaxos代码稍微做了修改，然后借助其自带的phxecho验证下这么修改带来的问题。



## 代码修改：

- Proposer不给本地节点发送Phase1a (模拟本地节点最后执行Prepare的场景)；
- Proposer在收到quorum个"1b"后，不是立即执行phase2a，而是打印消息，并sleep一会。
- Proposer在执行Phase2a时，解析下提议的value，如果包含一个特殊字符串 ”badguy"，则在发送Phase2a后，主动exit；
- 让所有Acceptor在执行Accept (phase2b)时，打印下Accept的具体Value (用于验证结果)。



## 测试步骤

1. 启动phxecho Server S0 - S4，一共5个；
2. 在S4上键入Propose的value, "badguy";
3. 在S4收到Quorum个reply，并打印sleep消息后，手工kill掉S1, S3, S3；
4. S4会在发送Accept请求给S0 - S3后，主动exit process；实际上只有S0 accept了这个Value (检验S0的log即可)；
5. Kill 掉S0 (S0已经Accept了 ”badguy")；
6. Restart S1, S2, S3 (这几个Server没有Accept "badguy"，**不启动S0**)；
7. Restart S4;
8. 在S4上提议"goodguy"
9. 能看到S1, S2, S3 Accept了"googguy"，但是Proposal Number没变。



#### S0的log:

229 12:44:16.111819 65293 logger_google.cpp:103] [44;37m Imp(0): PN8phxpaxos8AcceptorE::OnAccept START Msg.InstanceID 0 Msg.from_nodeid 72058139498785643 **Msg.ProposalID 2 Msg.ValueLen 10, badguy** [0m

####S1的log:

W0229 12:45:53.102106 65361 logger_google.cpp:103] [44;37m Imp(0): PN8phxpaxos8AcceptorE::OnAccept START Msg.InstanceID 0 Msg.from_nodeid 72058139498785643 **Msg.ProposalID 2 Msg.ValueLen 23, iamagoodguyhahahaha** [0m
W0229



可以看出，不同的Acceptor  Accept了不同的Value，且InstanceID, ProposalID, from_nodeid都相同，只是value不同。

如果我们的第9步之前，Kill掉S2, S3，不让它们Accept "goodguy"，那么就形成了一个状态：S0和S1都Accept了相同的Ballot Number的不同的Value，已经违背了OneValuePerBallot。虽然这是还没有形成冲突的决议，但是已经具备了形成冲突的决议的基础。

OneValuePerBallot被违背带来了什么问题？

大家可以想象下两个proposer P2, P3分别用Ballot m, n (m<n) 执行请求。

1. P2用BallotNumber m执行Phase1, 得到了$\{S0, S2, S3\}$ 的响应;
2. P3用BallotNumber n执行Phase1, 得到了$\{S1, S2, S3\}$的响应；
3. P2用m执行











我不知道phxpaxos的代码这么串行化做是不是为了解决这个问题。



TODO:  通过配置，让IsIMFollower成立？然后就不会给自己发了1a了？

   ==> Instance :: CheckNewValue() 里面有检查，估计根本不会提议出去。

