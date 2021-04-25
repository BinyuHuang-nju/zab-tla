# Document of TLA+ specification for Zab(中文版，日后翻译到英文)

## 概述
-	本实验是由论文"Junqueira F P, Reed B C, Serafini M. Zab: High-performance broadcast for primary-backup systems[C]//2011 IEEE/IFIP 41st International Conference on Dependable Systems & Networks (DSN). IEEE, 2011: 245-256."启发。本实验根据该论文描述的Zab协议进行了Zab的TLA+规约。
-	我们对Zab使用TLA+工具做了形式化规约，并在此基础上做了一定量的模型检验来验证Zab的正确性。
-	由于论文中对Zab算法描述的精简和细节上的忽略，在进行规约时协议中的一些细节由本实验作者进行补充和增加。如有疑问，欢迎指出。

## 注意点

### Note x
在规约中，每一个action都是原子的，但实际执行不是原子的，这不影响协议规约层的正确性，因此不做过多考虑。

### Note x
除了Election动作外，其余所有动作都是作用于某一具体服务器上的，这体现了"distributed"这一特性。因为论文不注重选主过程，所以在规约中我们抽象了选主过程，将其在Election动作中体现。Election动作是规约中唯一一个被抽象的动作。

### Note x
我们关心的是系统内状态的一致，不关心client向系统请求和系统向client回复的细节和各个服务器向副本/状态机deliver的细节。因此我们粗化了ClientRequest，省略了向client的回复。我们假设每一个committed的transaction会被立即deliver到副本中，故可用变量history[i][1..commitIndex]来模拟节点i向副本deliver的transaction序列。

## 差异

### Issue x Line: xx, Action: Election
在论文Step l.1.1，Stepl.2.2中，当leader接收到一个quorum的followers的消息才会作出下一个动作，这显然降低了系统可用性，我们应该把leader自身也算入到quorum中。考虑这样一种情况，系统内有3台服务器，其中有一台宕机，那么剩余两台服务器组成的集群中，leader接收到的某一消息最多只会来自于另一台，从而导致无法做出下一个动作，整个系统无法推进，这显然是违背了共识协议的高可用性的。于是，我们在动作Election中对变量cepochRecv和ackldRecv重置时就将leader节点ID加入到集合中。

### Issue x Line: xx, Action: LeaderHandleACKE; Line: xx, Action: LeaderDiscovery2Sync1
在论文Step l.1.2中，leader接收到Q中每一个follower的ACK后在此选出最佳的数据进行更新。我们认为这个条件比较苛刻，在规约中当leader接收到一个quorum的follower后就会选出最佳的数据进行更新。无论是选择论文中的做法，还是本实验中的做法，对算法的正确性不构成威胁。

### Issue x Line: xx, Action: 
在论文Step f.2.1中，某一follower接收到NEWLEADER消息中的epoch与本地的epoch不同时，会选择进行新一轮的election

## 增加

### Issue x Line: xx, Action: 
