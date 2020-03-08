# ">"还是">="？ 对比下标准Paxos和Phxpaxos实现

# 1. 前言

我在春节期间写过一篇关于Paxos正确性背后的数学的文章（[链接](https://zhuanlan.zhihu.com/p/104463008)）。那么这类形式化的东西对于工程实践的作用到底有多少？这篇文章从Paxos的 Phase1b公式出发，去理解下微信团队的phxpaxos的实现 （[链接](https://github.com/tencent/phxpaxos)），分析该实现中与标准Paxos(以及TLA+ spec)的差异，以及这种差异在什么场景下会存在什么问题。

先简要说下结论： 

- 虽然phxpaxos的文档里面说是遵照paxos made simple一文实现的(原话是: Purely based on Paxos Made Simple by Lamport.)，但是phxpaxos的代码与标准Paxos协议是有重要差异的(就是模型上“$>$”和“$>=$”的差异，违背了OneValuePerBallot这一正确性基石)；
- 这个差异本来会引起正确性问题，但是目前phxpaxos的代码对一些原本并发的操作做了串行处理，所以实际上不会出现问题。
- 如果把phxpaxos的代码稍微修改，去掉这个串行化，并手工制造一些特殊的事件序列，可以演示出这种差异会带来的问题(两个Acceptor，分别Accept了同一Ballot 的不同的Value)。



这里顺便给大家挖个坑： Phase1b是"$>$"号，**为什么Phase2b里面判断条件又是"$>=$"号？**



# 2. 差异在哪？

## 2.1 原文里Phase1a描述

我们看下Lamport的原文描述，可以看到Acceptor响应一个Ballot 的前提是： 收到的“1a”消息的Ballot，大于之前已经响应过的Request 的 Ballot 。

> Phase 1. (a) A proposer selects a proposal number n and sends a prepare request with number n to a majority of acceptors.
>
> (b) If an acceptor receives a prepare request with number n **greater than** that of any prepare request to which it has already responded, then it responds to the request with a promise not to accept any more proposals numbered less than n and with the highest-numbered pro- posal (if any) that it has accepted.



## 2.2 TLA+ Spec里的式子

我们在看看Paxos的在TLA+ spec里面对于Phase1b的公式描述，$m.bal>maxBal[a]$，也是一个大于号。对  TLA+感兴趣的同学，可以把$>$改为$>=$，再执行下TLA+的model checker，很快就能发现潜在问题。不过这篇文章我们侧重于代码，不过多讨论TLA+。
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


## 2.3 Phxpaxos里面的代码

Phxpaxos里面对应Phase1b的函数是Acceptor::OnPrepare，能够看出判断条件是$>=$。

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



## 2.4 差异及问题

可以看出，Phxpaxos的Phase1b 实现，与标准paxos协议是有差异的。$">"$ 变成了$">="$。在之前的文章中（[链接](https://zhuanlan.zhihu.com/p/104463008)）我们提过，这个$">"$对于保证OneValuePerBallot是必须的，没有它就没有了正确性保证。

那么Phxpaxos 这么实现，是不是有问题呢？这里面分两个方面分析相同Ballot Number的出现条件：

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
- 不同的Proposer，NodeID可以做到不同(这里没有展开分析NodeID的生成)。

所以，只要NodeID是不同的，phxpaxos不会出现两个的proposer共用Ballot的情况。



### 2.4.2 同一个Proposer，会用相同的Ballot么？

正常运行的proposer，代码很容易做到不重用相同的ProposalID(比如每次都自增)。但是考虑如下情形(一个可能的event序列)：

1. Proposer P1发送Ballot为b1的Phase1a消息；
2. P1收到了Quorum个Acceptor回复的"1b"消息，但是不包括自己(假设P1自己的磁盘太忙，phase1b的持久化过程迟迟没有完成)。
3. P1发送 2a消息$<b1, v1>$给各个Acceptor，然后自己宕机。
4. P1重启，自己没有关于b1的任何记录。
5. P1再次用Ballot Number b1执行Phase1，又成功（因为符合$>=$条件）。
6. P1提议$<b1, v2>$，又被Accept。



上面的event序列在Phxpaxos中会发生么？我们看看代码：



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



- BroadcastMessage的原型，带有默认的参数BroadcastMessage_Type_RunSelf_First。



```c++
    virtual int BroadcastMessage(
            const PaxosMsg & oPaxosMsg, 
            const int bRunSelfFirst = BroadcastMessage_Type_RunSelf_First,
            const int iSendType = Message_SendType_UDP);
```



- BroadcastMessage的实现，BroadcastMessage_Type_RunSelf_First的先在本地执行。

```c++

int Base :: BroadcastMessage(const PaxosMsg & oPaxosMsg, const int iRunType, const int iSendType)
{
    //...
    if (iRunType == BroadcastMessage_Type_RunSelf_First)
    {   //先在本地执行 OnReceivePaxosMsg
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



- Prepare的消息类型是MsgType_PaxosPrepare，OnReceivePaxosMsg会走到OnPrepare。可以看出，这个函数中，已经把BallotNumber做了持久化。

```c++
int Acceptor :: OnPrepare(const PaxosMsg & oPaxosMsg)
{
        //省略 
        m_oAcceptorState.SetPromiseBallot(oBallot);
        //Persist可以保证宕机后能找到之前写的内容标
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



只要完成了持久化，对照上面的步骤4，P1重启后就可以查到之前自己提议的Proposal ID，下次不会用重复的Proposal ID。

所以，在Phxpaxos的代码中，同一个proposer 也不会用相同的BallotNumber。**但这是有代价的**：proposer在本地的acceptor先完成Phase1b(写盘持久化)之后，才能给其他节点发送"1a"消息，增加了一次同步操作的延迟。在现有的大部分环境下，存储持久化的延迟，往往大于局域网的延迟。

不知道phxpaxos的代码这么串行化做是不是为了解决用错的$>=$带来的问题，但是确实是避开了。



# 3. 修改代码验证用错的">="可能会带来的问题

之前我们已经看到，phxpaxos虽然与标准paxos不一致，但是做到了下面两点，所以并没有出现正确性问题。

1) 在Ballot Number中包含了NodeID，让不同的Proposer不可能使用相同的Ballot Number。

2) 每个Proposer在发送"1a"时，总是让本节点的Acceptor先执行完Phase1b，然后再发送“1a"消息给其他节点。

但是如果不让本节点的Acceptor先执行Phase1b，真的会出现问题么？如果Proposer给所有Acceptor并发发送“1a"，那么理论上本地的Acceptor可能最后完成“1b”操作的持久化，那么会带来什么问题呢？

对phxpaxos代码稍微做了修改，然后借助phxpaxos其自带的phxecho验证下这么修改带来的问题。



## 3.1 代码修改

- 修改Proposer的代码(Base :: BroadcastMessage函数)，不给本地节点发送“1a”消息 (模拟本地节点某次执行"1b"超慢的场景)；
- Proposer在执行Phase2a时解析下提议的value，如果包含一个特殊字符串 ”badguy"，则在发送Phase2a后，**主动exit**(退出进程，模拟在这个环节自己宕机了)。

```diff
--- a/src/algorithm/base.cpp
+++ b/src/algorithm/base.cpp
@@ -239,7 +239,8 @@ int Base :: BroadcastMessage(const PaxosMsg & oPaxosMsg, const int iRunType, con
     }

     BP->GetInstanceBP()->BroadcastMessage();
+    //注释掉那个BroadcastMessage_Type_RunSelf_First对应分支
+    /*
     if (iRunType == BroadcastMessage_Type_RunSelf_First)
     {
         if (m_poInstance->OnReceivePaxosMsg(oPaxosMsg) != 0)
@@ -247,6 +248,7 @@ int Base :: BroadcastMessage(const PaxosMsg & oPaxosMsg, const int iRunType, con
             return -1;
         }
     }
+    */
     string sBuffer;
     int ret = PackMsg(oPaxosMsg, sBuffer);
@@ -256,6 +258,20 @@ int Base :: BroadcastMessage(const PaxosMsg & oPaxosMsg, const int iRunType, con
     }

     ret = m_poMsgTransport->BroadcastMessage(m_poConfig->GetMyGroupIdx(), sBuffer, iSendType);
+    if (MsgType_PaxosAccept == oPaxosMsg.msgtype()){
+        if (std::string::npos != oPaxosMsg.value().find("badguy")) {
+            sleep(1);
+            fprintf(stdout, "Accept, value: \n");
+            auto value = oPaxosMsg.value();
+            for (unsigned int i = 0; i < value.size(); i++) {
+                char c = value[i];
+                fprintf(stdout, "%c", c);
+            }
+            fprintf(stdout, "\nexiting process\n");
+            exit(0);
+        } else {}
+    } else {}

     if (iRunType == BroadcastMessage_Type_RunSelf_Final)
     {
```



- 修改Proposer的代码，在收到Quorum个"1b"的Response后，不是立即执行phase2a，而是**打印一个提示消息，并sleep一会**(我 的实现是20s，让自己在看到消息后可以执行几个kill 进程的操作，这一步可以进一步自动化)。

```diff
-- a/src/algorithm/proposer.cpp
+++ b/src/algorithm/proposer.cpp
@@ -359,6 +358,8 @@ void Proposer :: OnPrepareReply(const PaxosMsg & oPaxosMsg)
         BP->GetProposerBP()->PreparePass(iUseTimeMs);
         PLGImp("[Pass] start accept, usetime %dms", iUseTimeMs);
         m_bCanSkipPrepare = true;
+        fprintf(stdout, "I will sleep 20 seconds before Accept, you can kill 1-3\n");
+        sleep(20);
         Accept();
     }
```





- 让所有Acceptor在执行Accept (Acceptor::OnAccept)时，打印下Accept的具体Value等信息 (用于验证结果)。由于"2a"的消息做了封装，所以需要稍微hack下获得原字符串。

```diff
void Acceptor :: OnAccept(const PaxosMsg & oPaxosMsg)
 {
-    PLGHead("START Msg.InstanceID %lu Msg.from_nodeid %lu Msg.ProposalID %lu Msg.ValueLen %zu",
-            oPaxosMsg.instanceid(), oPaxosMsg.nodeid(), oPaxosMsg.proposalid(), oPaxosMsg.value().size());
+        PLGHead("START Msg.InstanceID %lu Msg.from_nodeid %lu Msg.ProposalID %lu Msg.ValueLen %zu, %s",
+                oPaxosMsg.instanceid(), oPaxosMsg.nodeid(), oPaxosMsg.proposalid(), oPaxosMsg.value().size(), oPaxosMsg.value().c_str()+4);
```



## 3.2 怎么测试

Phxpaxos自带了一个phxecho程序，它基于basic paxos执行。每个Server是proposer, acceptor的集成体。用户可以从终端键入想提议的字符串，在形成共识后，会打印proposal number, instance number和提议的value等。

我们在按照前述方法修改了phxpaxos的实现后，可以用phxecho来做测试。



## 3.3 测试步骤

按照下面的Event序列执行：

1. 启动5个phxecho Server: S0 - S4。启动后可以做些常规的Propose测试，然后开始下面的手工测试过程：
2. 在S4上键入提议的value, 即一个字符串，我们键入： "badguy";
3. 在S4收到多数派的reponse，并打印提示消息后，尽快手工kill掉S1, S3, S3 (需要在S4的的sleep完成前)；
4. S4会在sleep结束后，发送Accept("2a")请求，然后主动exit(退出进程)。实际上只有S0 真正Accept了这个Value (检验S0的log即可)； **注意**，Proposer发送"2a"给自己是在发送给其他Server之后，已经exit process了，自己没有执行Accept。
5. Kill 掉S0 (S0已经Accept了 ”badguy")；
6. Restart S1, S2, S3 (这几个Server没有Accept过 "badguy")，**不启动S0**；
7. Restart S4;
8. 在S4上提议新的Value: "iamagoodguyhahahaha"
9. 能看到S1, S2, S3 Accept了"iamagoodguyhahahaha"，但是Ballot Number没变。



直接看下S0和S1输出的log，这已经违背了OneValuePerBallot。

#### S0的log:

229 12:44:16.111819 65293 logger_google.cpp:103] [44;37m Imp(0): PN8phxpaxos8AcceptorE::OnAccept START Msg.InstanceID 0 Msg.from_nodeid 72058139498785643 **Msg.ProposalID 2 Msg.ValueLen 10, badguy** [0m

####S1的log:

W0229 12:45:53.102106 65361 logger_google.cpp:103] [44;37m Imp(0): PN8phxpaxos8AcceptorE::OnAccept START Msg.InstanceID 0 Msg.from_nodeid 72058139498785643 **Msg.ProposalID 2 Msg.ValueLen 23, iamagoodguyhahahaha **[0m


可以看出，S0和S1分别Accept了不同的Value，且InstanceID, ProposalID, from_nodeid都相同。



## 3.4 违背OneValuePerBallot会带来什么问题？

下面举一个例子，会选定两个不同的Value。但是还可以有其他导致选定两个Value的event序列。

如果我们在前面的第9步之前，Kill掉S2, S3，不让它们Accept "iamagoodguyhahahaha"，那么就形成了一个状态：只有S0和S1分别Accept了Proposal number 2的不同的Value。



假设随后Server都启动了，S0和S1分别用某个Ballot m, n (2<=m<n) 执行了完整的paxos过程。

1. S0用BallotNumber m执行Phase1, 得到了$\{S0, S2, S3\}$ 的响应(”1b")，只有S0带回了value "badguy"。
2. S1用BallotNumber n执行Phase1, 得到了$\{S1, S2, S3\}$的响应("1b")，只有S1带回了value "iamagoodguyhahahaha"；
3. S2用m执行phase2，选定Value "badguy"。
4. S3用n执行phase2，选定Value "iamagoodguyhahahaha"。**注意前提是n>m**。



本文至此结束，希望大家在理解Paxos时，不仅仅是记住了步骤，而是知道背后的原因。如果你想加深对原理的理解，可以思考了下我在文章开始挖的坑：**为什么Phase2b里面判断条件是"$>=$"号？**。



# 用TLA+spec 验证这个问题

## 修改Phase1b

```

Phase1b(a) == /\ \E m \in msgs : 
                  /\ m.type = "1a"
                  //这一行做了修改： > 变为 >=
                  /\ m.bal >= maxBal[a]
                  /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
                  /\ Send([type |-> "1b", acc |-> a, bal |-> m.bal,
                            mbal |-> maxVBal[a], mval |-> maxVal[a]])
              /\ UNCHANGED <<maxVBal, maxVal>>
```



## 修改Phase2a

默认不允许发送 Ballot相同的Phase2a(防止Queue已知增加消息，认为是不同的状态)，我修改下。

否则，model checker检查不出问题来。

```
Phase2a(b, v) ==
  //这一行做了修改，增加了 /\ m.val = v
  /\ ~ \E m \in msgs : m.type = "2a" /\ m.bal = b /\ m.val = v
  /\ \E Q \in Quorum :
        LET Q1b == {m \in msgs : /\ m.type = "1b"
                                 /\ m.acc \in Q
                                 /\ m.bal = b}
            Q1bv == {m \in Q1b : m.mbal \geq 0}
        IN  /\ \A a \in Q : \E m \in Q1b : m.acc = a
            /\ \/ Q1bv = {}
               \/ \E m \in Q1bv :
                    /\ m.mval = v
                    /\ \A mm \in Q1bv : m.mbal \geq mm.mbal
  /\ Send([type |-> "2a", bal |-> b, val |-> v])
  /\ UNCHANGED <<maxBal, maxVBal, maxVal>>
```

