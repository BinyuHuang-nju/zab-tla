# Zab TLA+ specification schedule

## 一些问题  
1.	election中，对msgs的处理，目前的选择是对Q内任意两个server间的缓冲区均置为空，是否合理？  
	- 关于这一点，也可以设计msgs为set类型，但是需要用2Darray模拟按序已发送/已接受的消息的最大ID，这样可以避免election时msgs的处理  

2.	目前实现中没有用到原文中的Q，这是对leader的broadcast和某节点restart后的处理等都有关系的，是否需要使用Q？  
	- 这里如果采用Q会有一些连锁反应，宕机和网络延迟变得可以表现出来，因为要对那么超出heartbeat的节点踢出Q中。
	- broadcast需要修改为仅对Q内成员发送msg
	- restart也是肯定需要修改的，进而Q也可能被更改，从而election可能需要被调用。因为一个server可能原本就在Q内，它宕机后迅速重启，leader能够ping通它；server也有可能宕机后过段时间才重启，leader认为heartbeat内无法ping通故(当然这也有可能是网络延迟故障)把它从Q中移除，此时若Q不满足多数派，那么还要执行election。故leader处的restart则election，follower处的restart则调用leader处的Timeout。
	- 故加入Q后，我们就应该引入Timeout，这样才能对Q进行增删元素，若为Leader端的Timeout则将对应follower移除出Q，并当Q不满足quorum时调用election；若为follower端的Timeout则进行election

3.	目前没有区分某个server发送给另一个server的输入/输出缓冲区，为了更好的表达延迟，输入缓冲区和输出缓冲区是否需要分开，即msgs会被分为sendMsgs和recvMsgs？  

4.	验证liveness properties的困难
  
5.	restart的server是如何加入集群的？目前规约中用的是leader的broadcast是给所有server发送，故restart的server能够通过此加入集群，也就不用考虑该问题  
	- 如果不是这样实现，可能需要参考VSR中recover后的server给其他所有副本发送RECOVERY报文并根据多数派回复更新状态，我们可以在Zab中做类似恢复机制，然后再承接我规约中的Leader Handle CEPOCH/ACKE/ACKLD in Phase3(HandleACKE由于不需要处理在DiscardStaleMessage中简要处理) 
 
6.	leader的broadcast是应该在一个转移动作内做完，还是每一个转移动作发出一条消息？(Raft TLA+是每个转移动作发送一条消息，而Paxos的proposer在每个转移动作内直接往msgs中存入一个不含source和dst的消息，相当于广播)每个动作发送一个更合理，因为能模拟可能发到一半leader节点就宕机的情况，但是在Zab中过于麻烦


7.	一个漏考虑的点，election后整个cluster内的epoch暂时还没有增加，这时候原先的leader发送消息，某个server接收到时发现epoch和自己的相同(或比自己大)，就将leaderOracle指向它，导致新leader失去多数派支持？	(也就是说，可能在新leader发送NEWEPOCH前失去多数派导致新一轮的election)
	- 这个问题目前没有去考虑，我们可以认为这轮的recovery失败，然后重新开始election。

## 注意点
1.	3种state，9种msg type，是否都进行了考虑？(否则缓冲区会堵塞)

2.	在规约properties的时候，仅靠当前定义的变量无法表达某个leader广播了某个事务，或某个follower接收或apply了某个事务。如果想要更准确表达properties，需要补上msgs传输和接收记录。
	- 这里我想要补上set类型的broadcastMsgsLog，和array型的deliverIndex(阅读论文得知deliver replica类似于 apply state machine),原本想要定义的deliverLog可以省略，因为已deliver的log必然能在history中找到，否则该共识协议是有漏洞的。
	- 除此以外，也许会有疑惑，我们可以假设每个committed的log立即被apply，那么默认deliverIndex = commitIndex，就不需要deliverIndex变量，这里我的想法是在Raft中可以这么想因为commitIndex不可能回退一个更小的值，但是在Zab中，宕机恢复/选主恢复阶段可能实现时会先让commitIndex=0

## 与论文描述的差异
1.	论文中leader接收到一个quorum消息才做某某动作，但这显然降低了可用性，因为leader本身自己应该也算入quorum中，否则对于3台服务器，若有一台down，那么leader的quorum最多只会有一台server不满足多数派的性质而无法运行下去，这显然是不合理的
2.	文中对于message中的epoch与本地epoch不同时，通常是选择进行新一轮的election，但可能某些msg仅仅是过期的消息，接收后直接丢掉就可以而不需要重新进行选主降低效率

## 可做的code优化
1.	基于工程角度，ACK-E和NEWLEADER通常不会发送整条log，故若这样设计，需要在之前的报文中得到follower的log信息，如log长度、commitIndex等。

2.	如今的Zab在选主阶段通常使用fast leader election，使得选出的prospective leader具有最up-to-date的性质(latest epoch and highest last zxid)，从而日志内容从双向同步变成了单向同步，在phase1、phase2阶段能够省略很多处理。

## Model checking问题
1.	关于状态爆炸，假如我们不限制每一轮内可commit的事务数量，那么似乎状态空间是枚举不完的，因为history可以任意长，怎么在做checking时来做限制？(是否可以参照之前，譬如对history的长度做限定)


## 附：TCP协议
TCP是在不可靠的IP层之上实现的可靠的数据传输协议，它主要解决传输的可靠、有序、无丢失和不重复问题。TCP是TCP/IP体系中非常复杂的一个协议，主要特点如下：  
	- TCP是面向连接的传输层协议  
	- 每条TCP连接只能有两个端点，每条TCP连接只能是点对点的  
	- TCP提供可靠的交付服务，保证传送的数据无差错、不丢失、不重复且有序  
	- TCP提供全双工通信，允许通信双方的应用进程在任何时候都能发送数据，为此TCP连接的两端都设有发送缓存和接收缓存，用来临时存放双向通信的数据  
	- 发送缓存包含1)发送应用程序传送给发送方TCP准备发送的数据2)TCP已发送但尚未收到确认的数据  
	- 接收缓存包含1)按序到达但尚未被接收应用读取的数据2)不按序到达的数据
