-------------------------------- MODULE Zab --------------------------------
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
            [mtype:{ACK_E}, msource:Server, mdest: Server, lastEpoch:Epoches, hf:]
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

\* The set of followers who has successfully sent CEPOCH to pleader in pleader.
VARIABLE cepochRecv

\* The set of followers who has successfully sent ACK-E to pleader in pleader.
VARIABLE ackeRecv

\* The set of followers who has successfully sent ACK-LD to pleader in pleader.
VARIABLE ackldRecv

\* ackIndex[i][j] means leader i has received how many ACK messages from follower j.
\* So ackIndex[i][i] is not used.
VARIABLE ackIndex

\* commitIndex[i] means leader/follower i has committed how many proposals and sent COMMIT messages.
VARIABLE commitIndex

\* Hepler matrix for follower to stop sending CEPOCH to pleader in followers.
\* Because CEPOCH is the sole message which follower actively sends to pleader.
VARIABLE cepochSent

\* the biggest epoch in CEPOCH pleader received from followers.
VARIABLE tempMaxEpoch

\* the biggest leaderEpoch and most up-to-date history in ACKE pleader received from followers.
VARIABLE tempMaxLastEpoch

VARIABLE tempInitialHistory

serverVars == <<state, currentEpoch, leaderEpoch, leaderOracle, history, commitIndex>>
leaderVars == <<cepochRecv, ackeRecv, ackldRecv, ackIndex>>
tempVars   == <<tempMaxEpoch, tempMaxLastEpoch, tempInitialHistory>>

vars == <<serverVars, msgs, leaderVars, cepochSent>>
----------------------------------------------------------------------------
LastZxid(his) == IF Len(his) > 0 THEN <<his[Len(his)].epoch,his[Len(his)].counter>>
                                 ELSE <<-1, -1>>

\* Add a message to msgs - add a message m to msgs[i][j]
(*Send(m) == msgs' = msgs \union {m}*)
Send(i, j, m) == msgs' = [msgs EXCEPT ![i][j] = Append(msgs[i][j], m)]

\* Remove a message from msgs - discard head of msgs[i][j]
(*Discard(m) == msgs' = msgs \ {m}*)
Discard(i, j) == msgs' = IF msgs[i][j] /= << >> THEN [msgs EXCEPT ![i][j] = Tail(msgs[i][j])]
                                                ELSE msgs

\* Leader/Pleader broadcasts a message to all other servers
Broadcast(i, m) == msgs' = [ii \in Server |-> [ij \in Server |-> IF ii = i /\ ij /= i THEN Append(msgs[ii][ij], m)
                                                                                      ELSE msgs[ii][ij]]] 

\* Combination of Send and Discard - discard head of msgs[j][i] and add m into msgs[i][j]
(*Reply(response, request) == msgs' = (msgs \union {response}) \ {request}*)
Reply(i, j, m) == msgs' = [msgs EXCEPT ![j][i] = Tail(msgs[j][i]),
                                       ![i][j] = Append(msgs[i][j], m)]

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
        /\ commitIndex        = [s \in Server |-> 0]
        /\ cepochSent         = [s \in Server |-> FALSE]
        /\ tempMaxEpoch       = [s \in Server |-> 0]
        /\ tempMaxLastEpoch   = [s \in Server |-> 0]
        /\ tempInitialHistory = [s \in Server |-> << >>]

\* A server becomes pleader and a quorum servers knows that.

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
        /\ UNCHANGED <<serverVars, ackeRecv, ackldRecv, ackIndex, cepochSent, tempMaxLastEpoch, tempInitialHistory>>

LeaderDiscovery1(i) ==
        /\ state[i] = ProspectiveLeader
        /\ cepochRecv[i] \in Quorums
        /\ currentEpoch' = [currentEpoch EXCEPT ![i] = tempMaxEpoch[i] + 1]
        /\ cepochRecv'   = [cepochRecv   EXCEPT ![i] = {}]
        /\ Broadcast(i,[mtype  |-> NEWEPOCH,
                        mepoch |-> currentEpoch'[i]])
        /\ UNCHANGED <<state, leaderEpoch, leaderOracle, history, ackeRecv, ackldRecv, ackIndex, commitIndex, cepochSent, tempVars>>

\* In phase f12, follower receives NEWEPOCH. If e' > f.p then sends back ACKE,
\* and ACKE contains f.a and hf to help pleader choose a newer history.
FollowerDiscovery2(i, j) ==
        /\ state[i] = Follower
        /\ msgs[j][i] /= << >>
        /\ msgs[j][i][1].mtype = NEWEPOCH
        /\ LET msg == msgs[j][i][1]
           IN \/ \* new NEWEPOCH - accept and reply
                 /\ currentEpoch[i] < msg.mepoch
                 /\ currentEpoch' = [currentEpoch EXCEPT ![i] = msg.mepoch]
                 /\ leaderOracle' = [leaderOracle EXCEPT ![i] = j]
                 /\ Reply(i, j, [mtype      |-> ACKE,
                                 mepoch     |-> msg.mepoch,
                                 mlastEpoch |-> leaderEpoch[i],
                                 mhf        |-> history[i]])
              \/ \* old NEWEPOCH - diacard
                 /\ currentEpoch[i] >= msg.mepoch
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
           IN \/ /\ currentEpoch[i] = msg.mepoch
                 /\ \/ /\ infoOk
                       /\ tempMaxLastEpoch'   = [tempMaxLastEpoch   EXCEPT ![i] = msg.mlastEpoch]
                       /\ tempInitialHistory' = [tempInitialHistory EXCEPT ![i] = msg.mhf]
                    \/ /\ ~infoOk
                       /\ UNCHANGED <<tempMaxLastEpoch, tempInitialHistory>>
                 /\ ackeRecv' = [ackeRecv EXCEPT ![i] = IF j \notin ackeRecv[i] THEN ackeRecv[i] \union {j}
                                                                       ELSE ackeRecv[i]]
              \/ /\ currentEpoch[i] /= msg.mepoch
                 /\ UNCHANGED<<tempMaxLastEpoch, tempInitialHistory, ackeRecv>>
        /\ Discard(j, i)
        /\ UNCHANGED <<serverVars, cepochRecv, ackldRecv, ackIndex, cepochSent, tempMaxEpoch>>

LeaderDiscovery2Sync1(i) ==
        /\ state[i] = ProspectiveLeader
        /\ ackeRecv[i] \in Quorums
        /\ history'     = [history     EXCEPT ![i] = tempInitialHistory[i]]
        /\ commitIndex' = [commitIndex EXCEPT ![i] = 0]
        /\ ackeRecv'    = [ackeRecv    EXCEPT ![i] = {}]
        \* until now, phase1(Discovery) ends
        /\ Broadcast(i, [mtype           |-> NEWLEADER,
                         mepoch          |-> currentEpoch[i],
                         minitialHistory |-> history'[i]])
        /\ UNCHANGED <<state, currentEpoch, leaderEpoch, leaderOracle, cepochRecv,ackldRecv, ackIndex, cepochSent, tempVars>> 

\* In phase f21, follower receives NEWLEADER. The follower updates its epoch and history,
\* and send back ACK-LD to pleader.
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
                 /\ Reply(i, j, [mtype  |-> ACKLD,
                                 mepoch |-> msg.mepoch])
              \/ \* old NEWLEADER - discard
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
                 /\ ackldRecv' = [ackldRecv EXCEPT ![i] = IF j \notin ackldRecv[i] THEN ackldRecv[i] \union {j}
                                                                                   ELSE ackldRecv[i]]
              \/ \* old ACK-LD - impossible
                 /\ currentEpoch[i] /= msg.mepoch
                 /\ UNCHANGED ackldRecv
        /\ Discard(j, i)
        /\ UNCHANGED <<serverVars, cepochRecv, ackeRecv, ackIndex, tempVars, cepochSent>>

LeaderSync2(i) == 
        /\ state[i] = ProspectiveLeader
        /\ ackldRecv[i] \in Quorums
        /\ commitIndex' = [commitIndex EXCEPT ![i] = Len(history[i])]
        /\ state' = [state EXCEPT ![i] = Leader]
        /\ Broadcast(i, [mtype  |-> COMMITLD,
                         mepoch |-> currentEpoch[i]])
        /\ UNCHANGED <<currentEpoch, leaderEpoch, leaderOracle, history, leaderVars, tempVars, cepochSent>>

FollowerSync2(i, j) ==
        /\ state[i] = Follower 
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
\* Last modified Sun Mar 14 22:35:50 CST 2021 by Dell
\* Created Sat Dec 05 13:32:08 CST 2020 by Dell


