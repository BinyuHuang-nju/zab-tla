-------------------------------- MODULE ZabQ -------------------------------

\* This is the formal specification for the Zab consensus algorithm,
\* which means Zookeeper Atomic Broadcast.

\* This work is driven by Flavio P. Junqueira,"Zab: High-performance broadcast for primary-backup systems"

EXTENDS Integers, FiniteSets, Sequences, Naturals, TLC

\* The set of server identifiers
CONSTANT Server

\* The set of requests that can go into history
CONSTANT Value

\* Server states
CONSTANTS Follower, Leader, ProspectiveLeader

\* Message types
CONSTANTS CEPOCH, NEWEPOCH, ACKE, NEWLEADER, ACKLD, COMMITLD, PROPOSE, ACK, COMMIT

\* the maximum round of epoch (initially {0,1,2})
CONSTANT Epoches
----------------------------------------------------------------------------
\* Return the maximum value from the set S
Maximum(S) == IF S = {} THEN -1
                        ELSE CHOOSE n \in S: \A m \in S: n >= m

\* Return the minimum value from the set S
Minimum(S) == IF S = {} THEN -1
                        ELSE CHOOSE n \in S: \A m \in S: n <= m

Quorums == {Q \in SUBSET Server: Cardinality(Q)*2 > Cardinality(Server)}
ASSUME QuorumsAssumption == /\ \A Q \in Quorums: Q \subseteq Server
                            /\ \A Q1, Q2 \in Quorums: Q1 \cap Q2 /= {}                           

(*
Messages == [mtype:{CEPOCH}, msource:Server, mdest:Server, mepoch:Epoches]
            \union
            [mtype:{NEWEPOCH}, msource:Server, mdest:SUBSET Server, mepoch:Epoches]
            \union
            [mtype:{ACKE}, msource:Server, mdest: Server, lastEpoch:Epoches, hf:]
*)

None == CHOOSE v: v \notin Value

NullPoint == CHOOSE p: p \notin Server
----------------------------------------------------------------------------
\* The server's state(Follower,Leader,ProspectiveLeader).
VARIABLE state

\* The leader's epoch or the last new epoch proposal the follower acknowledged(f.p in paper).
VARIABLE currentEpoch

\* The last new leader proposal the follower acknowledged(f.a in paper).
VARIABLE leaderEpoch

\* The identifier of the leader for followers.
VARIABLE leaderOracle

\* The history of servers as the sequence of transactions.
VARIABLE history

\* The messages repersenting requests and responses sent from one server to another.
\* msgs[i][j] means the input buffer of server j from server i.
VARIABLE msgs

\* The set of followers which the leader thinks follow it.
VARIABLE leaderQuorum

\* The set of followers who has successfully sent CEPOCH to pleader in pleader.
VARIABLE cepochRecv

\* The set of followers who has successfully sent ACK-E to pleader in pleader.
VARIABLE ackeRecv

\* The set of followers who has successfully sent ACK-LD to pleader in pleader.
VARIABLE ackldRecv

\* ackIndex[i][j] means leader i has received how many ACK messages from follower j.
\* So ackIndex[i][i] is not used.
VARIABLE ackIndex

\* currentCounter[i] means the count of transactions client requests leader.
VARIABLE currentCounter

\* sendCounter[i] means the count of transactions leader has broadcast.
VARIABLE sendCounter

\* initialHistory[i] means the initial history of leader i in epoch currentEpoch[i].
VARIABLE initialHistory

\* commitIndex[i] means leader/follower i should commit how many proposals and sent COMMIT messages.
VARIABLE commitIndex

\* commitIndex[i] means leader i has committed how many proposals and sent COMMIT messages.
VARIABLE committedIndex

\* Hepler matrix for follower to stop sending CEPOCH to pleader in followers.
\* Because CEPOCH is the sole message which follower actively sends to pleader.
VARIABLE cepochSent

\* the maximum epoch in CEPOCH pleader received from followers.
VARIABLE tempMaxEpoch

\* the maximum leaderEpoch and most up-to-date history in ACKE pleader received from followers.
VARIABLE tempMaxLastEpoch

VARIABLE tempInitialHistory

serverVars == <<state, currentEpoch, leaderEpoch, leaderOracle, history, commitIndex>>
leaderVars == <<leaderQuorum, cepochRecv, ackeRecv, ackldRecv, ackIndex, currentCounter, sendCounter, initialHistory, committedIndex>>
tempVars   == <<tempMaxEpoch, tempMaxLastEpoch, tempInitialHistory>>

vars == <<serverVars, msgs, leaderVars, tempVars, cepochSent>>
----------------------------------------------------------------------------
LastZxid(his) == IF Len(his) > 0 THEN <<his[Len(his)].epoch,his[Len(his)].counter>>
                                 ELSE <<-1, -1>>

\* Add a message to msgs - add a message m to msgs[i][j]
Send(i, j, m) == msgs' = [msgs EXCEPT ![i][j] = Append(msgs[i][j], m)]

\* Remove a message from msgs - discard head of msgs[i][j]
Discard(i, j) == msgs' = IF msgs[i][j] /= << >> THEN [msgs EXCEPT ![i][j] = Tail(msgs[i][j])]
                                                ELSE msgs

\* Leader/Pleader broadcasts a message to all other servers
Broadcast(i, m) == msgs' = [ii \in Server |-> [ij \in Server |-> IF ii = i /\ ij /= i THEN Append(msgs[ii][ij], m)
                                                                                      ELSE msgs[ii][ij]]] 

\* Combination of Send and Discard - discard head of msgs[j][i] and add m into msgs[i][j]
Reply(i, j, m) == msgs' = [msgs EXCEPT ![j][i] = Tail(msgs[j][i]),
                                       ![i][j] = Append(msgs[i][j], m)]

Reply2(i, j, m1, m2) == msgs' = [msgs EXCEPT ![j][i] = Tail(msgs[j][i]),
                                             ![i][j] = Append(Append(msgs[i][j], m1), m2)]
(*
TypeOK == /\ state \in [Server -> {Follower, Leader, ProspectiveLeader}]
          /\ currentEpoch \in [Server -> Epoches]
          /\ leaderEpoch \in [Server -> Epoches]
          /\ leaderOracle \in [Server -> Server]
*)
----------------------------------------------------------------------------
\* Define initial values for all variables 
Init == /\ state              = [s \in Server |-> Follower]
        /\ currentEpoch       = [s \in Server |-> 0]
        /\ leaderEpoch        = [s \in Server |-> 0]
        /\ leaderOracle       = [s \in Server |-> NullPoint]
        /\ history            = [s \in Server |-> << >>]
        /\ msgs               = [i \in Server |-> [j \in Server |-> << >>]]
        /\ cepochRecv         = [s \in Server |-> {}]
        /\ ackeRecv           = [s \in Server |-> {}]
        /\ ackldRecv          = [s \in Server |-> {}]
        /\ ackIndex           = [i \in Server |-> [j \in Server |-> 0]]
        /\ currentCounter     = [s \in Server |-> 0]
        /\ sendCounter        = [s \in Server |-> 0]
        /\ commitIndex        = [s \in Server |-> 0]
        /\ committedIndex     = [s \in Server |-> 0]
        /\ initialHistory     = [s \in Server |-> << >>]
        /\ cepochSent         = [s \in Server |-> FALSE]
        /\ tempMaxEpoch       = [s \in Server |-> 0]
        /\ tempMaxLastEpoch   = [s \in Server |-> 0]
        /\ tempInitialHistory = [s \in Server |-> << >>]

----------------------------------------------------------------------------
\* A server becomes pleader and a quorum servers knows that.
Election(i, Q) ==
        /\ i \in Q
        /\ state'              = [s \in Server |-> IF s = i THEN ProspectiveLeader
                                                            ELSE IF s \in Q THEN Follower
                                                                            ELSE state[s]]
        /\ cepochRecv'         = [cepochRecv EXCEPT ![i] = {i}]
        /\ ackeRecv'           = [ackeRecv   EXCEPT ![i] = {i}]
        /\ ackldRecv'          = [ackldRecv  EXCEPT ![i] = {i}]
        /\ ackIndex'           = [ii \in Server |-> [ij \in Server |->
                                                    IF ii = i THEN 0
                                                              ELSE ackIndex[ii][ij]]]
        /\ committedIndex'     = [committedIndex     EXCEPT ![i] = 0]
        /\ initialHistory'     = [initialHistory     EXCEPT ![i] = << >>]
        /\ tempMaxEpoch'       = [tempMaxEpoch       EXCEPT ![i] = currentEpoch[i]]
        /\ tempMaxLastEpoch'   = [tempMaxLastEpoch   EXCEPT ![i] = currentEpoch[i]]
        /\ tempInitialHistory' = [tempInitialHistory EXCEPT ![i] = history[i]]
        /\ leaderOracle'       = [s \in Server |-> IF s \in Q THEN i
                                                              ELSE leaderOracle[s]]
        /\ leaderEpoch'        = [s \in Server |-> IF s \in Q THEN currentEpoch[s]
                                                              ELSE leaderEpoch[s]]
        /\ cepochSent'         = [s \in Server |-> IF s \in Q THEN FALSE
                                                              ELSE cepochSent[s]]
        /\ msgs'               = [ii \in Server |-> [ij \in Server |-> 
                                                     IF ii \in Q /\ ij \in Q THEN << >>
                                                                             ELSE msgs[ii][ij]]]
        /\ UNCHANGED <<currentEpoch, history, commitIndex, currentCounter, sendCounter>>

Restart(i) ==
        /\ state' = [state EXCEPT ![i] = Follower]
        /\ leaderOracle' = [leaderOracle EXCEPT ![i] = NullPoint]
        /\ cepochSent' = [cepochSent EXCEPT ![i] = FALSE]
        /\ UNCHANGED <<currentEpoch, leaderEpoch, history, commitIndex, leaderVars, tempVars, msgs>>
        
----------------------------------------------------------------------------
\* In phase f11, follower sends f.p to pleader via CEPOCH.
FollowerDiscovery1(i) ==
        /\ state[i] = Follower
        /\ leaderOracle[i] /= NullPoint
        /\ \lnot cepochSent[i]
        /\ LET leader == leaderOracle[i]
           IN Send(i, leader, [mtype  |-> CEPOCH,
                               mepoch |-> currentEpoch[i]])
        /\ cepochSent' = [cepochSent EXCEPT ![i] = TRUE]
        /\ UNCHANGED <<serverVars, leaderVars, tempVars>>

\* In phase l11, pleader receives CEPOCH from a quorum, and choose a new epoch e'
\* as its own l.p and sends NEWEPOCH to followers.                 
LeaderHandleCEPOCH(i, j) ==
        /\ state[i] = ProspectiveLeader
        /\ msgs[j][i] /= << >>
        /\ msgs[j][i][1].mtype = CEPOCH
        /\ \/ \* redundant message - just discard
              /\ j \in cepochRecv[i]
              /\ UNCHANGED <<tempMaxEpoch, cepochRecv>>
           \/ \* new message - modify tempMaxEpoch and cepochRecv
              /\ j \notin cepochRecv[i]
              /\ LET newEpoch == Maximum({tempMaxEpoch[i],msgs[j][i][1].mepoch})
                 IN tempMaxEpoch' = [tempMaxEpoch EXCEPT ![i] = newEpoch]
              /\ cepochRecv' = [cepochRecv EXCEPT ![i] = cepochRecv[i] \union {j}]
        /\ Discard(j, i)
        /\ UNCHANGED <<serverVars, ackeRecv, ackldRecv, ackIndex, currentCounter, sendCounter, 
                       initialHistory, committedIndex, cepochSent, tempMaxLastEpoch, tempInitialHistory>>

\* Here I decide to change leader's epoch in l12&l21, otherwise there may exist an old leader and
\* a new leader who share the same expoch. So here I just change leaderEpoch, and use it in handling ACK-E.
LeaderDiscovery1(i) ==
        /\ state[i] = ProspectiveLeader
        /\ cepochRecv[i] \in Quorums
        /\ leaderEpoch' = [leaderEpoch EXCEPT ![i] = tempMaxEpoch[i] + 1]
        /\ cepochRecv'  = [cepochRecv  EXCEPT ![i] = {}]
        /\ Broadcast(i,[mtype  |-> NEWEPOCH,
                        mepoch |-> leaderEpoch'[i]])
        /\ UNCHANGED <<state, currentEpoch, leaderOracle, history, ackeRecv, ackldRecv, ackIndex, 
                       currentCounter, sendCounter, initialHistory, commitIndex, committedIndex, cepochSent, tempVars>>

\* In phase f12, follower receives NEWEPOCH. If e' > f.p then sends back ACKE,
\* and ACKE contains f.a and hf to help pleader choose a newer history.
FollowerDiscovery2(i, j) ==
        /\ state[i] = Follower
        /\ msgs[j][i] /= << >>
        /\ msgs[j][i][1].mtype = NEWEPOCH
        /\ LET msg == msgs[j][i][1]
           IN \/ \* new NEWEPOCH - accept and reply
                 /\ currentEpoch[i] <= msg.mepoch \* Here use <=, because one follower may send CEPOCH more then once.
                 /\ currentEpoch' = [currentEpoch EXCEPT ![i] = msg.mepoch]
                 /\ leaderOracle' = [leaderOracle EXCEPT ![i] = j]
                 /\ Reply(i, j, [mtype      |-> ACKE,
                                 mepoch     |-> msg.mepoch,
                                 mlastEpoch |-> leaderEpoch[i],
                                 mhf        |-> history[i]])
              \/ \* stale NEWEPOCH - diacard
                 /\ currentEpoch[i] > msg.mepoch
                 /\ Discard(j, i)
                 /\ UNCHANGED <<currentEpoch, leaderOracle>>
        /\ UNCHANGED<<state, leaderEpoch, history, leaderVars, commitIndex, cepochSent, tempVars>>

\* In phase l12, pleader receives ACKE from a quorum, 
\* and select the history of one most up-to-date follower to be the initial history.          
LeaderHandleACKE(i, j) ==
        /\ state[i] = ProspectiveLeader
        /\ msgs[j][i] /= << >>
        /\ msgs[j][i][1].mtype = ACKE
        /\ LET msg    == msgs[j][i][1]
               infoOk == \/ msg.mlastEpoch > tempMaxLastEpoch[i]
                         \/ /\ msg.mlastEpoch = tempMaxLastEpoch[i]
                            /\ \/ LastZxid(msg.mhf)[1] > LastZxid(tempInitialHistory[i])[1]
                               \/ /\ LastZxid(msg.mhf)[1] = LastZxid(tempInitialHistory[i])[1]
                                  /\ LastZxid(msg.mhf)[2] >= LastZxid(tempInitialHistory[i])[2]
           IN \/ /\ leaderEpoch[i] = msg.mepoch
                 /\ \/ /\ infoOk
                       /\ tempMaxLastEpoch'   = [tempMaxLastEpoch   EXCEPT ![i] = msg.mlastEpoch]
                       /\ tempInitialHistory' = [tempInitialHistory EXCEPT ![i] = msg.mhf]
                    \/ /\ ~infoOk
                       /\ UNCHANGED <<tempMaxLastEpoch, tempInitialHistory>>
                 /\ ackeRecv' = [ackeRecv EXCEPT ![i] = IF j \notin ackeRecv[i] THEN ackeRecv[i] \union {j}
                                                                       ELSE ackeRecv[i]]
              \/ /\ leaderEpoch[i] /= msg.mepoch
                 /\ UNCHANGED<<tempMaxLastEpoch, tempInitialHistory, ackeRecv>>
        /\ Discard(j, i)
        /\ UNCHANGED <<serverVars, cepochRecv, ackldRecv, ackIndex, currentCounter, 
                       sendCounter, initialHistory, committedIndex, cepochSent, tempMaxEpoch>>

LeaderDiscovery2Sync1(i) ==
        /\ state[i] = ProspectiveLeader
        /\ ackeRecv[i] \in Quorums
        /\ currentEpoch'   = [currentEpoch   EXCEPT ![i] = leaderEpoch[i]]
        /\ history'        = [history        EXCEPT ![i] = tempInitialHistory[i]]
        /\ initialHistory' = [initialHistory EXCEPT ![i] = tempInitialHistory[i]]
        /\ commitIndex'    = [commitIndex    EXCEPT ![i] = 0]
        /\ ackeRecv'       = [ackeRecv       EXCEPT ![i] = {}]
        /\ ackIndex'       = [ackIndex       EXCEPT ![i] = Len(tempInitialHistory[i])]
        \* until now, phase1(Discovery) ends
        /\ Broadcast(i, [mtype           |-> NEWLEADER,
                         mepoch          |-> currentEpoch[i],
                         minitialHistory |-> history'[i]])
        /\ UNCHANGED <<state, leaderEpoch, leaderOracle, cepochRecv,ackldRecv, 
                       currentCounter, sendCounter, committedIndex, cepochSent, tempVars>> 
                       
----------------------------------------------------------------------------
\* In phase f21, follower receives NEWLEADER. The follower updates its epoch and history,
\* and sends back ACK-LD to pleader.
FollowerSync1(i, j) ==
        /\ state[i] = Follower
        /\ msgs[j][i] /= << >>
        /\ msgs[j][i][1].mtype = NEWLEADER
        /\ LET msg == msgs[j][i][1]
           IN \/ \* new NEWLEADER - accept and reply
                 /\ currentEpoch[i] <= msg.mepoch
                 /\ currentEpoch' = [currentEpoch EXCEPT ![i] = msg.mepoch]
                 /\ leaderEpoch'  = [leaderEpoch  EXCEPT ![i] = msg.mepoch]
                 /\ leaderOracle' = [leaderOracle EXCEPT ![i] = j]
                 /\ history'      = [history      EXCEPT ![i] = msg.minitialHistory]
                 /\ commitIndex'  = [commitIndex  EXCEPT ![i] = 0]
                 /\ Reply(i, j, [mtype    |-> ACKLD,
                                 mepoch   |-> msg.mepoch,
                                 mhistory |-> msg.minitialHistory])
              \/ \* stale NEWLEADER - discard
                 /\ currentEpoch[i] > msg.mepoch
                 /\ Discard(j, i)
                 /\ UNCHANGED <<currentEpoch, leaderEpoch, leaderOracle, history, commitIndex>>
        /\ UNCHANGED <<state, leaderVars, tempVars, cepochSent>>
                 
\* In phase l22, pleader receives ACK-LD from a quorum of followers, and sends COMMIT-LD to followers.
LeaderHandleACKLD(i, j) ==
        /\ state[i] = ProspectiveLeader
        /\ msgs[j][i] /= << >>
        /\ msgs[j][i][1].mtype = ACKLD
        /\ LET msg == msgs[j][i][1] 
           IN \/ \* new ACK-LD - accept
                 /\ currentEpoch[i] = msg.mepoch
                 /\ ackIndex'  = [ackIndex  EXCEPT ![i][j] = Len(initialHistory[i])]
                 /\ ackldRecv' = [ackldRecv EXCEPT ![i] = IF j \notin ackldRecv[i] THEN ackldRecv[i] \union {j}
                                                                                   ELSE ackldRecv[i]]
              \/ \* stale ACK-LD - impossible
                 /\ currentEpoch[i] /= msg.mepoch
                 /\ UNCHANGED <<ackldRecv, ackIndex>>
        /\ Discard(j, i)
        /\ UNCHANGED <<serverVars, cepochRecv, ackeRecv, currentCounter, 
                       sendCounter, initialHistory, committedIndex, tempVars, cepochSent>>

LeaderSync2(i) == 
        /\ state[i] = ProspectiveLeader
        /\ ackldRecv[i] \in Quorums
        /\ commitIndex'    = [commitIndex    EXCEPT ![i] = Len(history[i])]
        /\ committedIndex' = [committedIndex EXCEPT ![i] = Len(history[i])]
        /\ state'          = [state          EXCEPT ![i] = Leader]
        /\ currentCounter' = [currentCounter EXCEPT ![i] = 0]
        /\ sendCounter'    = [sendCounter    EXCEPT ![i] = 0]
        /\ ackldRecv'      = [ackldRecv      EXCEPT ![i] = {}]
        /\ Broadcast(i, [mtype  |-> COMMITLD,
                         mepoch |-> currentEpoch[i]])
        /\ UNCHANGED <<currentEpoch, leaderEpoch, leaderOracle, history, cepochRecv, 
                       ackeRecv, ackIndex, initialHistory, tempVars, cepochSent>>

\* In phase f22, follower receives COMMIT-LD and submits all unprocessed transaction.
FollowerSync2(i, j) ==
        /\ state[i] = Follower
        /\ msgs[j][i] /= << >>
        /\ msgs[j][i][1].mtype = COMMITLD
        /\ LET msg == msgs[j][i][1]
           IN \/ \* new COMMIT-LD - commit all transactions in initial history
                 /\ currentEpoch[i] = msg.mepoch
                 /\ commitIndex' = [commitIndex EXCEPT ![i] = Len(history[i])]
                 /\ leaderOracle' = [leaderOracle EXCEPT ![i] = j]
              \/ \* stale COMMIT-LD - discard
                 /\ currentEpoch[i] /= msg.mepoch
                 /\ UNCHANGED <<commitIndex, leaderOracle>>
        /\ Discard(j, i)
        /\ UNCHANGED <<state, currentEpoch, leaderOracle, history, leaderVars, tempVars, cepochSent>>

----------------------------------------------------------------------------
\* In phase l31, leader receives client request and broadcasts PROPOSE.
ClientRequest(i, v) ==
        /\ state[i] = Leader
        /\ currentCounter' = [currentCounter EXCEPT ![i] = currentCounter[i] + 1]
        /\ LET newTransaction == [epoch   |-> currentEpoch[i],
                                  counter |-> currentCounter'[i],
                                  value   |-> v]
           IN /\ history'  = [history  EXCEPT ![i] = Append(history[i], newTransaction)]
              /\ ackIndex' = [ackIndex EXCEPT ![i] = Len(history'[i])]
        /\ UNCHANGED <<msgs, state, currentEpoch, leaderEpoch, leaderOracle, commitIndex, cepochRecv,
                       ackeRecv, ackldRecv, sendCounter, initialHistory, committedIndex, tempVars, cepochSent>>

LeaderBroadcast1(i) ==
        /\ state[i] = Leader
        /\ sendCounter[i] < currentCounter[i]
        /\ LET toBeSentCounter == sendCounter[i] + 1
               toBeSentIndex   == Len(initialHistory[i]) + toBeSentCounter
               toBeSentEntry   == history[i][toBeSentIndex]
           IN /\ Broadcast(i, [mtype     |-> PROPOSE,
                               mepoch    |-> currentEpoch[i],
                               mproposal |-> toBeSentEntry])
              /\ sendCounter' = [sendCounter EXCEPT ![i] = toBeSentCounter]
        /\ UNCHANGED <<serverVars,cepochRecv, ackeRecv, ackldRecv, ackIndex, 
                       currentCounter, initialHistory, committedIndex, tempVars, cepochSent>>

\* In phase f31, follower accepts proposal and append it to history.
FollowerBroadcast1(i, j) ==
        /\ state[i] = Follower
        /\ msgs[j][i] /= << >>
        /\ msgs[j][i][1].mtype = PROPOSE
        /\ LET msg == msgs[j][i][1]
           IN \/ \* It should be that msg.mproposal.counter = 1 \/ msg.mrpoposal.counter = history[Len(history)].counter + 1
                 /\ currentEpoch[i] = msg.mepoch
                 /\ history' = [history EXCEPT ![i] = Append(history[i], msg.mproposal)]
                 /\ leaderOracle' = [leaderOracle EXCEPT ![i] = j]
                 /\ Reply(i, j, [mtype  |-> ACK,
                                 mepoch |-> currentEpoch[i],
                                 mindex |-> Len(history'[i])])
              \/ \* If happens, /= must be >, namely a stale leader sends it.
                 /\ currentEpoch[i] /= msg.mepoch
                 /\ Discard(j, i)
                 /\ UNCHANGED <<history, leaderOracle>>
        /\ UNCHANGED <<state, currentEpoch, leaderEpoch, commitIndex, leaderVars, tempVars, cepochSent>>

\* In phase l32, leader receives ack from a quorum of followers to a certain proposal,
\* and commits the proposal.
LeaderHandleACK(i, j) ==
        /\ state[i] = Leader
        /\ msgs[j][i] /= << >>
        /\ msgs[j][i][1].mtype = ACK
        /\ LET msg == msgs[j][i][1]
           IN \/ \* There should be ackIndex[i][j] + 1 == msg.mindex
                 /\ currentEpoch[i] = msg.mepoch
                 /\ ackIndex' = [ackIndex EXCEPT ![i][j] = Maximum({ackIndex[i][j], msg.mindex})]
              \/ \* If happens, /= must be >, namely a stale follower sends it.
                 /\ currentEpoch[i] /= msg.mepoch
                 /\ UNCHANGED ackIndex
        /\ Discard(j ,i)
        /\ UNCHANGED <<serverVars, cepochRecv, ackeRecv, ackldRecv,currentCounter, 
                       sendCounter, initialHistory, committedIndex, tempVars, cepochSent>>

LeaderAdvanceCommit(i) ==
        /\ state[i] = Leader
        /\ commitIndex[i] < Len(history[i])
        /\ LET Agree(index)   == {i} \cup {k \in Server: ackIndex[i][k] >= index}
               agreeIndexes   == {index \in (commitIndex[i] + 1)..Len(history[i]): Agree(index) \in Quorums}
               newCommitIndex == IF agreeIndexes /= {} THEN Maximum(agreeIndexes)
                                                       ELSE commitIndex[i]
           IN commitIndex' = [commitIndex EXCEPT ![i] = newCommitIndex]
        /\ UNCHANGED <<state, currentEpoch, leaderEpoch, leaderOracle, history,
                       msgs, leaderVars, tempVars, cepochSent>>

LeaderBroadcast2(i) ==
        /\ state[i] = Leader
        /\ committedIndex[i] < commitIndex[i]
        /\ LET newCommittedIndex == committedIndex[i] + 1
           IN /\ Broadcast(i, [mtype    |-> COMMIT,
                               mepoch   |-> currentEpoch[i],
                               mindex   |-> newCommittedIndex,
                               mcounter |-> history[newCommittedIndex].counter])
              /\ committedIndex' = [committedIndex EXCEPT ![i] = committedIndex[i] + 1]
        /\ UNCHANGED <<serverVars, cepochRecv, ackeRecv, ackldRecv, ackIndex, currentCounter, 
                       sendCounter, initialHistory, tempVars, cepochSent>>

\* In phase f32, follower receives COMMIT and commits transaction.
FollowerBroadcast2(i, j) ==
        /\ state[i] = Follower
        /\ msgs[j][i] /= << >>
        /\ msgs[j][i][1].mtype = COMMIT
        /\ LET msg == msgs[j][i][1]
           IN \/ \* new COMMIT - commit transaction in history
                 /\ currentEpoch[i] = msg.mepoch
                 /\ commitIndex'  = [commitIndex  EXCEPT ![i] = Maximum({commitIndex[i], msg.mindex})]
                 /\ leaderOracle' = [leaderOracle EXCEPT ![i] = j]
              \/ \* stale COMMIT - discard
                 /\ currentEpoch[i] /= msg.mepoch
                 /\ UNCHANGED <<commitIndex, leaderOracle>>
        /\ Discard(j, i)
        /\ UNCHANGED <<state, currentEpoch, leaderEpoch, history, 
                       leaderVars, tempVars, cepochSent>>

----------------------------------------------------------------------------
\* There may be two ways to make sure all followers as up-to-date as the leader.
\* way1: choose Send not Broadcast when leader is going to send PROPOSE and COMMIT.
\* way2: When one follower receives PROPOSE or COMMIT which misses some entries between
\*       its history and the newest entry, the follower send CEPOCH to catch pace.
\* Here I choose way2, which I need not to rewrite PROPOSE and COMMIT, but need to
\* modify the code when follower receives NEWLEADER and COMMIT.

\* In phase l33, upon receiving CEPOCH, leader l proposes back NEWEPOCH and NEWLEADER.
LeaderHandleCEPOCHinPhase3(i, j) ==
        /\ state[i] = Leader
        /\ msgs[j][i] /= << >>
        /\ msgs[j][i][1].mtype = CEPOCH
        /\ LET msg == msgs[j][i][1]
           IN \/ /\ currentEpoch[i] >= msg.mepoch
                 /\ Reply2(i, j, [mtype  |-> NEWEPOCH,
                                  mepoch |-> currentEpoch[i]],
                                 [mtype           |-> NEWLEADER,
                                  mepoch          |-> currentEpoch[i],
                                  minitialHistory |-> history[i]])
              \/ /\ currentEpoch[i] < msg.mepoch
                 /\ UNCHANGED msgs
        /\ UNCHANGED <<serverVars, leaderVars, tempVars, cepochSent>>
        
\* In phase l34, upon receiving ack from f of the NEWLEADER, it sends a commit message to f.
\* Leader l also makes Q := Q \union {f}.
LeaderHandleACKLDinPhase3(i, j) ==
        /\ state[i] = Leader
        /\ msgs[j][i] /= << >>
        /\ msgs[j][i][1].mtype = ACKLD
        /\ LET msg == msgs[j][i][1]
               aimCommitIndex == Minimum({commitIndex[i], Len(msg.mhistory)})
           IN \/ /\ currentEpoch[i] = msg.mepoch
                 /\ ackIndex' = [ackIndex EXCEPT ![i][j] = Len(msg.mhistory)]
                 /\ Reply(i, j, [mtype    |-> COMMIT,
                                 mepoch   |-> currentEpoch[i],
                                 mindex   |-> aimCommitIndex,
                                 mcounter |-> history[aimCommitIndex].counter])
              \/ /\ currentEpoch[i] /= msg.mepoch
                 /\ Discard(j, i)
                 /\ UNCHANGED <<ackIndex>>
        /\ UNCHANGED <<serverVars, cepochRecv, ackeRecv, ackldRecv, currentCounter, sendCounter, 
                       initialHistory, committedIndex, tempVars, cepochSent>>

\* To ensure any follower can find the correct leader, the follower should modify leaderOracle
\* anytime when it receive messages from leader, because a server may restart and join the cluster Q
\* halfway and receive the first message which is not NEWEPOCH. But we can delete this restriction
\* when we ensure Broadcast function acts on the followers in the cluster not any servers in 
\* the whole system, then one server must has correct leaderOracle before it receives messages.

\* Let me suppose two conditions when one follower sends CEPOCH to leader:
\* 0. Usually, the server becomes follower in election and sends CEPOCH before receiving NEWEPOCH.
\* 1. The follower wants to join the cluster halfway and get the newest history.
\* 2. The follower has received COMMIT, but there exists the gap between its own history and mindex,
\*    which means there are some transactions before mindex miss. Here we choose to send CEPOCH 
\*    again, to receive the newest history from leader.
BecomeFollower(i) ==
        /\ \E j \in Server \ {i}: /\ msgs[j][i] /= << >>   
                                  /\ LET msg == msgs[j][i][1]
                                     IN /\ currentEpoch[i] < msg.mepoch
                                        /\ \/ msg.mtype = NEWEPOCH
                                           \/ msg.mtype = NEWLEADER
                                           \/ msg.mtype = COMMITLD
                                           \/ msg.mtype = PROPOSE
                                           \/ msg.mtype = COMMIT
                                        /\ state'        = [state        EXCEPT ![i] = Follower]
                                        /\ currentEpoch' = [currentEpoch EXCEPT ![i] = msg.mepoch]
                                        /\ leaderOracle' = [leaderOracle EXCEPT ![i] = j]
                                        \* Here we should not use Discard.
        /\ UNCHANGED <<leaderEpoch, history, commitIndex, msgs, leaderVars, tempVars, cepochSent>>
                                        
----------------------------------------------------------------------------
DiscardStaleMessage(i) ==
        /\ \E j \in Server \ {i}: /\ msgs[j][i] /= << >>
                                  /\ LET msg == msgs[j][i][1]
                                     IN \/ /\ state[i] = Follower
                                           /\ \/ msg.mepoch < currentEpoch[i]
                                              \/ msg.mtype = CEPOCH
                                              \/ msg.mtype = ACKE
                                              \/ msg.mtype = ACKLD
                                              \/ msg.mtype = ACK
                                        \/ /\ state[i] = Leader 
                                           /\ msg.mtype /= CEPOCH
                                           /\ \/ msg.mepoch < currentEpoch[i] 
                                              \/ msg.mtype = ACKE \* response of NEWEPOCH
                                        \/ /\ state[i] = ProspectiveLeader
                                           /\ msg.mtype /= CEPOCH
                                           /\ \/ msg.mepoch < currentEpoch[i]
                                              \/ msg.mtype = ACK
                                  /\ Discard(j ,i)
        /\ UNCHANGED <<serverVars, leaderVars, tempVars, cepochSent>>


----------------------------------------------------------------------------
\* Defines how the variables may transition.
Next ==
        \/ \E i \in Server:      Restart(i)
        \/ \E i \in Server, Q \in Quorums: Election(i, Q)
        \/ \E i \in Server:      FollowerDiscovery1(i)
        \/ \E i, j \in Server:   LeaderHandleCEPOCH(i, j)
        \/ \E i \in Server:      LeaderDiscovery1(i)
        \/ \E i, j \in Server:   FollowerDiscovery2(i, j)
        \/ \E i, j \in Server:   LeaderHandleACKE(i, j)
        \/ \E i \in Server:      LeaderDiscovery2Sync1(i)
        \/ \E i, j \in Server:   FollowerSync1(i, j)
        \/ \E i, j \in Server:   LeaderHandleACKLD(i, j)
        \/ \E i \in Server:      LeaderSync2(i)
        \/ \E i, j \in Server:   FollowerSync2(i, j)
        \/ \E i \in Server, v \in Value: ClientRequest(i, v)
        \/ \E i \in Server:      LeaderBroadcast1(i)
        \/ \E i, j \in Server:   FollowerBroadcast1(i, j)
        \/ \E i, j \in Server:   LeaderHandleACK(i, j)
        \/ \E i \in Server:      LeaderAdvanceCommit(i)
        \/ \E i \in Server:      LeaderBroadcast2(i)
        \/ \E i, j \in Server:   FollowerBroadcast2(i, j)
        \/ \E i, j \in Server:   LeaderHandleCEPOCHinPhase3(i, j)
        \/ \E i, j \in Server:   LeaderHandleACKLDinPhase3(i, j)
        \/ \E i \in Server:      DiscardStaleMessage(i)
        \/ \E i \in Server:      BecomeFollower(i)

Spec == Init /\ [][Next]_vars

----------------------------------------------------------------------------
\* Defines some variants, safety propoties, and liveness propoties of zab consensus algorithm.

Consistency == 
        \E i, j \in Server:
                    /\ state[i] = Leader
                    /\ state[j] = Leader
                    /\ currentEpoch[i] = currentEpoch[j]
                    => i = j
(*   
DiscoveryLeader1(i) ==
        /\ state[i] = ProspectiveLeader
        /\ ~\E m \in msgs: /\ m.mtype = NEWEPOCH
                           /\ m.msource = i
                           /\ m.mepoch = currentEpoch[i]
        /\ \E Q \in Quorums:
            LET mset == {m \in msgs: /\ m.mtype = CEPOCH
                                     /\ m.msource \in Q 
                                     /\ m.mdest = i}
                newEpoch == Maximum({m.mepoch: m \in mset}) + 1
            IN /\ \A s \in Q: \E m \in mset: m.msource = s
               /\ currentEpoch' = [currentEpoch EXCEPT ![i] = newEpoch]
               /\ leaderEpoch'  = [leaderEpoch EXCEPT ![i] = newEpoch] 
               /\ Send([mtype   |-> NEWEPOCH,
                        msource |-> i,
                        mdest   |-> Server \ {i},
                        mepoch  |-> newEpoch])
        /\ UNCHANGED <<state, leaderOracle, history>>


DiscoveryFollower1(i) == 
        /\ state[i] = Follower
        /\ leaderOracle[i] /= NullPoint
        /\ LET leader == leaderOracle[i]
           IN /\ ~\E m \in msgs: /\ m.mtype = CEPOCH 
                                 /\ m.msource = i 
                                 /\ m.mdest = leader 
                                 /\ m.mepoch = currentEpoch[i]
              /\ Send([mtype   |-> CEPOCH,
                       msource |-> i,
                       mdest   |-> leader,
                       mepoch  |-> currentEpoch[i]])
        /\ UNCHANGED <<state, currentEpoch, leaderEpoch, leaderOracle, history>>


DiscoveryFollower2(i) == 
        /\ state[i] = Follower
        /\ \E m \in msgs: /\ m.mtype = NEWEPOCH
                          /\ i \in m.mdest
                          /\ currentEpoch[i] < m.mepoch
                          /\ leaderOracle' = [leaderOracle EXCEPT ![i] = m.msource]
                          /\ currentEpoch' = [currentEpoch EXCEPT ![i] = m.mepoch]
                          /\ LET qm == [mtype   |-> NEWEPOCH, 
                                        msource |-> m.msource, 
                                        mdest   |-> m.mdest\{i}, 
                                        mepoch  |-> m.mepoch]
                             IN msgs' = (msgs \ {m}) \union {qm}
                          /\ Send([mtype     |-> ACKE,
                                   msource   |-> i,
                                   mdest     |-> m.msource,
                                   lastEpoch |-> leaderEpoch[i],
                                   hf        |-> history[i]])
        /\ UNCHANGED <<state, leaderEpoch, history>>

              
Integrity == \A l, f \in Server, msg \in msgs:
                /\ state[l] = Leader /\ state[f] = Follower
                /\ msg.type = COMMIT /\ msg \in histroy[f]   
                => msg \in history[l]

Consistency == \E i, j \in Server:
                (state[i] = Leader) /\ (state[j] = Leader)
                => i = j

LivenessProperty1 == \A i, j \in Server, msg \in msgs:
                      (state[i] = Leader) /\ (msg.type = COMMIT)
                      ~> (msg \in history[j]) /\ (state[j] = Follower)
*)

=============================================================================
\* Modification History
\* Last modified Thu Apr 01 20:19:10 CST 2021 by Dell
\* Created Sat Dec 05 13:32:08 CST 2020 by Dell


