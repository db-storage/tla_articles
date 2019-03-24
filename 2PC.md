最基本的spec(只描述模型，要保证什么)



有具体实现的2PC spec



宕机事件及隐含条件：

  持久化



无状态的SQL Executor带来的问题



参与者在Commit后保留事务状态多久？

- 如果先持久化txn decision，之后才允许commit，那么实际上不存在询问RM事务状态的问题

   能否不持久化txn的begin, prepared状态？ 只写decision?

  

- 如果不持久化txn decision就通知commit/rollback，则参与者必须先持久化txn decision。且在其他RM了结该事务之前，不能删除decision

超时处理

   只要所有参与者进入了prepared状态，必需就得Commit?

   如果TM在接受所有的prepared Ok消息之前，timeout了？或者有一个参与者记录Prepared日志后，宕机了一小时？

   Commit/Rollback，以Decision为准。



某个RM作为TM (Spanner)

  关键点：Leader RM的Decision和Commit合一