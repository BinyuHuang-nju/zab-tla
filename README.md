# Zab-tla

## Note
	- This is Binyu Huang's specification of Zab with TLA+.
	- Zab's full name is Zookeeper Atomic Broadcast, the core broadcast algorithm in Zookeeper.
	- You will find Zab.tla in the root directory, which represents specification of Zab in the implementation of TLA+ toolbox.
	- You will find ZabWithQ.tla in the root directory, and the difference from Zab.tla is that leader has a cluster Q and broadcasts messages to servers only in Q.


## Requirements
	- TLA+ toolbox version 1.7.0

## Reference 
 	The experiment draws lessons from 
	- My junior Xingchen Yi(https://github.com/Starydark/PaxosStore-tla) 
	- Raft's author(https://github.com/ongardie/raft.tla)