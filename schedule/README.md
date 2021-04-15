# Zab TLA+ specification schedule

## 一些问题  
1.	election中，对msgs的处理，目前的选择是对Q内任意两个server间的缓冲区均置为空，是否合理？  
	-关于这一点，也可以设计msgs为set类型，但是需要用2Darray模拟按序已发送/已接受的消息的最大ID，这样可以避免election时msgs的处理  

2.	目前实现中没有用到原文中的Q，这是对leader的broadcast和某节点restart后的处理等都有关系的，是否需要使用Q？  
	-这里如果采用Q会有一些连锁反应，宕机和网络延迟变得可以表现出来，因为要对那么超出heartbeat的节点踢出Q中。
	-restart也是肯定需要修改的，进而Q也可能被更改，从而election可能需要被调用。因为一个server可能原本就在Q内，它宕机后迅速重启，leader能够ping通它；server也有可能宕机后过段时间才重启，leader认为heartbeat内无法ping通故(当然这也有可能是网络延迟故障)把它从Q中移除，此时若Q不满足多数派，那么还要执行election。

3.	目前没有区分某个server发送给另一个server的输入/输出缓冲区，为了更好的表达延迟，输入缓冲区和输出缓冲区是否需要分开，即msgs会被分为sendMsgs和recvMsgs？  

4.	验证liveness properties的困难
  
5.	restart的server是如何加入集群的？目前规约中用的是leader的broadcast是给所有server发送，故restart的server能够通过此加入集群，也就不用考虑该问题  
	-如果不是这样实现，可能需要参考VSR中recover后的server给其他所有副本发送RECOVERY报文并根据多数派回复更新状态，我们可以在Zab中做类似恢复机制，然后再承接我规约中的Leader Handle CEPOCH/ACKE/ACKLD in Phase3(HandleACKE由于不需要处理在DiscardStaleMessage中简要处理) 
 
6.	leader的broadcast是应该在一个转移动作内做完，还是每一个转移动作发出一条消息？(Raft TLA+是每个转移动作发送一条消息，而Paxos的proposer在每个转移动作内直接往msgs中存入一个不含source和dst的消息，相当于广播)每个动作发送一个更合理，因为能模拟可能发到一半leader节点就宕机的情况，但是在Zab中过于麻烦

## 注意点
1.	3种state，9种msg type，是否都进行了考虑？(否则缓冲区会堵塞)

## 可做的code优化
1.	基于工程角度，ACK-E和NEWLEADER通常不会发送整条log，故若这样设计，需要在之前的报文中得到follower的log信息，如log长度、commitIndex等。
2.	如今的Zab在选主阶段通常使用fast leader election，使得选出的prospective leader具有最up-to-date的性质(latest epoch and highest last zxid)，从而日志内容从双向同步变成了单向同步，在phase1、phase2阶段能够省略很多处理。

## Model checking问题
1.	关于状态爆炸，假如我们不限制每一轮内可commit的事务数量，那么似乎状态空间是枚举不完的，因为history可以任意长，怎么在做checking时来做限制？(是否可以参照之前，譬如对history的长度做限定)
