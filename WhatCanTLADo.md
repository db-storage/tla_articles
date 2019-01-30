

# 为什么需要TLA?

#### 我实现了一个Cache模块，这个Cache有没有问题呢？



#### 我实现了一个基于etcd/consul选主的高可用系统，还是使用了lease机制，我如何确定我设计没有漏洞？会不会出现双主呢？



大部分设计，是围绕功能/接口去展开，比如，Cache模块，我们首先想到的是支持Read/Write/Evict这类接口，然后每个接口对应什么流程/数据结构，哪些地方需要临界区保护等。然后我们会脑补各种并发场景，分析可能存在的corner case，然后设计测试用例，运行测试，找bug。

从实现功能的角度，上述做法很正常。但是如果我们考虑下图的一个Cache模型(暂不支持 Evict)，系统实现后，运行了一段时间测试，Read/Write都很正常，所有测试用例都过了。这时候我仍然会有些疑问：

- 有没有Cache 一致性(Coherency)问题？

- 测试能证明没问题了么？

  

### Cache Coherency的例子

这个问题起码可以对应为两个问题：

- Cache Coherency具体是什么？比如下面两个，是不是看起来都正确？

  > 1. 如果某个进程的Cache里面有地址a1的数据，那么Cache里面的数据与主存中地址a1 对应的数据应该是相同的。
  > 2. 如果两个进程的Cache里面都有某个地址a1的数据，那么它们应该是相同的。 

- 如何在运行过程中每一个可能的状态都保证Cache Coherency?

  > 我们不可能在实际系统的代码中不断检查Cache Coherency，但是TLA的Model Checker可以。



### 测试分支覆盖问题

如果把系统运行看出一系列的状态变更，那么问题变成：

- 测试过程中，如何穷举所有可能发生的状态？

  

  
