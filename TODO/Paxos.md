1. Consensus (不仅仅是一个单独的spec，而是要理解什么是Consensus)
2. Voting()
3. Paxos

通过以上三步：

- 明确描述了什么是Consensus(共识)，参照下Cache Coherency，才知道"一致"这个词多么不准确！
- Paxos就是保证了Consensus，里面的具体变更，只是具体协议。在外界看来，就是保证Consensus里面的Property。



## 存在的问题:

- 没有明确哪些内容需要持久化；

- Phase2b为例，它真的是个atomic step么？

- 宕机有什么影响呢？消息丢了什么影响？ 如果丢的是response，而不仅仅是个request？ 

  maxVBal是个内存值？还是持久化的值？如果是两个值，谁先修改？修改过程中，有新的请求来了，需要比较怎么办？