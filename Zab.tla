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
                            /\ \A Q1, Q2 \in Quorums: Q1 \cap Q2 # {}                           

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

\* commitIndex[i] means leader i has committed how many proposals and sent COMMIT messages.
VARIABLE commitIndex

VARIABLE leaderHaveSentNEWEPOCH

\* Hepler matrix for follower to stop sending CEPOCH to pleader in followers.
VARIABLE newepochRecv

serverVars == <<state, currentEpoch, leaderEpoch, leaderOracle, history>>
leaderVars == <<cepochRecv, ackeRecv, ackldRecv, ackIndex, commitIndex>>

vars == <<serverVars, msgs, leaderVars, newepochRecv>>
----------------------------------------------------------------------------
LastZxid(his) == IF Len(his) > 0 THEN <<his[Len(his)].epoch,his[Len(his)].counter>>
                                 ELSE <<-1, -1>>

\* Add a message to msgs
(*Send(m) == msgs' = msgs \union {m}*)
Send(i, j, m) == msgs' = [msgs EXCEPT ![i][j] = Append(msgs[i][j], m)]

\* Remove a message from msgs
(*Discard(m) == msgs' = msgs \ {m}*)
Discard(i, j) == msgs' = [msgs EXCEPT ![i][j] = Tail(msgs[i][j])]

\* Leader/Pleader broadcasts a message to all other servers
Broadcast(i, m) == msgs' = [ii \in Server |-> [ij \in Server |-> IF ii = i THEN Append(msgs[ii][ij], m)
                                                                           ELSE msgs[ii][ij] ]] 

\* Combination of Send and Discard
Reply(response, request) == msgs' = (msgs \union {response}) \ {request}

(*
TypeOK == /\ state \in [Server -> {Follower, Leader, ProspectiveLeader}]
          /\ currentEpoch \in [Server -> Epoches]
          /\ leaderEpoch \in [Server -> Epoches]
          /\ leaderOracle \in [Server -> Server]
*)
----------------------------------------------------------------------------
\* Define initial values for all variables
Init == /\ state        = [s \in Server |-> Follower]
        /\ currentEpoch = [s \in Server |-> 0]
        /\ leaderEpoch  = [s \in Server |-> 0]
        /\ leaderOracle = [s \in Server |-> NullPoint]
        /\ history      = [s \in Server |-> << >>]
        \* /\ msgs      = {}
        /\ msgs         = [i \in Server |-> [j \in Server |-> << >>]]
        /\ cepochRecv   = [s \in Server |-> {}]
        /\ ackeRecv     = [s \in Server |-> {}]
        /\ ackldRecv    = [s \in Server |-> {}]
        /\ ackIndex     = [i \in Server |-> [j \in Server |-> 0]]
        /\ commitIndex  = [i \in Server |-> 0]
        /\ newepochRecv = [i \in Server |-> FALSE]

\* A server becomes pleader and a quorum servers knows that.

\* In phase f11, follower sends f.p to pleader via CEPOCH.
(*
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
*)
DiscoveryFollower1(i) ==
        /\ state[i] = Follower
        /\ leaderOracle[i] /= NullPoint
        /\ \lnot newepochRecv[i]
        /\ LET leader == leaderOracle[i]
           IN Send(i, leader, [mtype  |-> CEPOCH,
                               mepoch |-> currentEpoch[i]])
        /\ UNCHANGED <<serverVars, leaderVars, newepochRecv>>

\* In phase l11, pleader receives CEPOCH from a quorum, and choose a new epoch e'
\* as its own l.p and sends NEWEPOCH to followers.                 
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
*)
HandleCEPOCH(i, j) ==
        /\ state[i] = ProspectiveLeader
        /\ msgs[j][i] /= << >>
        /\ msgs[j][i][1].mtype = CEPOCH
        /\ \/ \* redundant message - just delete
              /\ j \in cepochRecv[i]
              /\ UNCHANGED <<currentEpoch, cepochRecv>>
           \/ \* new message - modify currentEpoch and cepochRecv
              /\ j \notin cepochRecv[i]
              /\ LET newEpoch == Maximum({currentEpoch[i],msgs[j][i][1].mepoch})
                 IN currentEpoch' = [currentEpoch EXCEPT ![i] = newEpoch]
              /\ cepochRecv' = [cepochRecv EXCEPT ![i] = cepochRecv[i] \union {j}]
        /\ Discard(j, i)
        /\ UNCHANGED <<state, leaderEpoch, leaderOracle, history, newepochRecv, ackeRecv, ackldRecv, ackIndex, commitIndex>>

DiscoveryLeader1(i) ==
        /\ state[i] = ProspectiveLeader
        /\ cepochRecv[i] \in Quorums
        /\ currentEpoch' = [currentEpoch EXCEPT ![i] = currentEpoch[i] + 1]
        /\ Broadcast(i,[mtype  |-> NEWEPOCH,
                        mepoch |-> currentEpoch[i]])
        /\ UNCHANGED <<state, leaderEpoch, leaderOracle, history, 

\* In phase f12, follower receives NEWEPOCH. If e' > f.p then sends back ACKE,
\* and ACKE contains f.a and hf to help pleader choose a newer history.
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
                      
DiscoveryLeader2plus(i) == /\ state[i] = ProspectiveLeader   

(*msgs' = [ii \in Server |-> [ij \in Server |-> IF ii = i THEN Append(msgs[ii][ij], m)
                                                        ELSE msgs[ii][ij] ]]              
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




e' == CHOOSE x \in Nat:
        \A e \in Q: x > e
        

LET f == CHOOSE fq \in Q:
            \A fp \in Q: \/ fp.a < fq.a
                         \/ fp.a = fq.a /\ fp.zxid <= fq.zxid
IN Ie' == hf*)

=============================================================================
\* Modification History
\* Last modified Fri Mar 12 22:41:00 CST 2021 by Dell
\* Created Sat Dec 05 13:32:08 CST 2020 by Dell


