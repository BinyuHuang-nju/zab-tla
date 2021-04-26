# Zab-tla

## Overview
This project is devoted to provide formal specification and verification using TLA+ for the Zookeeper Atomic Broadcast(Zab) consensus protocol proposed in *Junqueira F P, Reed B C, Serafini M. Zab: High-performance broadcast for primary-backup systems[C]//2011 IEEE/IFIP 41st International Conference on Dependable Systems & Networks (DSN). IEEE, 2011: 245-256*.  

We have made a formal specification for Zab using TLA+ toolbox, and we have done a certain scale of model checking to verify the correctness of Zab.

Due to the simplification of Zab algorithm description in the paper, some details in specification were modified and added. If you have any question, please point out.

## Requirements
TLA+ toolbox version 1.7.0

## Run
Create specification and run models in the usual way

## Notes

### Note 1
Except for the action *Election*, all actions perform on a specific server to reflect the feature of distributed. Since the paper does not pay attention to the process of selecting a leader, we abstract this process and it can be reflected in action *Election*. *Election* and actions which call it are the only actions that are abstracted in the whole specification.

### Note 2
Communication in Zab is based on TCP channels, so there is no packet loss, redundancy, or disorder in message delivery. We use module *Sequence* in TLA+ to simulate the property of receiving messages in order.  
We believe it can simulate message delay when a server does not perform the action of receiving messages. And it can simulate a failuere of server when a server does not perform any action.

### Note 3