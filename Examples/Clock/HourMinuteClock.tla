---------------------------- MODULE HourMinuteClock ----------------------------
EXTENDS Naturals, TLC

----------------------------------------------------------------------------
(* Variables 和 constants 定义部分 *)
----------------------------------------------------------------------------
VARIABLES hour, minute
(* 所有变量组成的tuple，在Spec中用到 *)
vars == <<hour, minute>>
(* 允许在运行TLC Model Checker时配置。使用较小的值，便于测试、图形化显示结果等*)
CONSTANT HoursPerDay
CONSTANT MinPerHour

----------------------------------------------------------------------------
(* State Predicate定义 *)
----------------------------------------------------------------------------
(* hour和minute的取值范围，用谓词表示 *)
HourTypeOK == hour \in (0 .. HoursPerDay -1)
MinuteTypeOK == minute \in (0 .. MinPerHour-1)
(* 所有变量的取值范围限制谓词 *)
TypeInv == HourTypeOK /\ MinuteTypeOK

----------------------------------------------------------------------------
(* State Change 相关定义 *)
----------------------------------------------------------------------------
(* 初始化状态，正好与TypeInv式子相同。从任意一个时间点开始都可以 *)
Init == HourTypeOK /\ MinuteTypeOK
MinNext == minute' = (minute + 1) % MinPerHour
HourNext == hour' = IF minute # (MinPerHour-1) THEN hour ELSE (hour + 1) % HoursPerDay
(* Tick可以理解伪Clock走了以下 *)
Tick == MinNext /\ HourNext
Next == Tick /\ PrintT(<<hour, minute>>)

----------------------------------------------------------------------------
(* Behavior Properity 相关定义 *)
----------------------------------------------------------------------------

Spec == Init /\ [][Next]_vars /\ WF_vars(Tick)  /\ []TypeInv 
=============================================================================
