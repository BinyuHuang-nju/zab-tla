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

(*Here need to be added about Messages
Messages == [mtype:{CEPOCH}, msource:Server, mdest:Server, mepoch:Epoches]
            \union
            [mtype:{NEWEPOCH}, msource:Server, mdest:SUBSET Server, mepoch:Epoches]
            \union
            [mtype:{ACK_E}, msource:Server, mdest: Server, lastEpoch:Epoches, hf:]*)

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
VARIABLE msgs

\* The set of followers who has successfully sent CEPOCH to pleader.
VARIABLE cepochReceived

\* The set of followers who has successfully sent ACK-E to pleader.
VARIABLE ackeReceived

\* The set of followers who has successfully sent ACK-LD to pleader.
VARIABLE ackldReceived

\* ackIndex[i][j] means leader i has received how many ACK messages from follower j.
\* So ackIndex[i][i] is not used.
VARIABLE ackIndex

\* commitIndex[i] means leader i has committed how many proposals and sent COMMIT messages.
VARIABLE commitIndex

vars == <<state, currentEpoch, leaderEpoch, leaderOracle, history, msgs>>
----------------------------------------------------------------------------
LastZxid(his) == IF Len(his) > 0 THEN <<his[Len(his)].epoch,his[Len(his)].counter>>
                                 ELSE <<-1, -1>>

\* Add a message to msgs
Send(m) == msgs' = msgs \union {m}

\* Remove a message from msgs
Discard(m) == msgs' = msgs \ {m}

\* Combination of Send and Discard
Reply(response, request) == msgs' = (msgs \union {response}) \ {request}

(*TypeOK == /\ msgs \in [Server -> [Server ->]]*)
TypeOK == /\ state \in [Server -> {Follower, Leader, ProspectiveLeader}]
          /\ currentEpoch \in [Server -> Epoches]
          /\ leaderEpoch \in [Server -> Epoches]
          /\ leaderOracle \in [Server -> Server]
          \*/\ msgs \subseteq Messages
----------------------------------------------------------------------------
\* Define initial values for all variables
Init == /\ state        = [s \in Server |-> Follower]
        /\ currentEpoch = [s \in Server |-> 0]
        /\ leaderEpoch  = [s \in Server |-> 0]
        /\ leaderOracle = [s \in Server |-> NullPoint]
        /\ history      = [s \in Server |-> << >>]
        /\ msgs         = {}

\* A server becomes pleader and a quorum servers knows that.

\* In phase f11, follower sends f.p to pleader via CEPOCH.
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

\* In phase l11, pleader receives CEPOCH from a quorum, and choose a new epoch e'
\* as its own l.p and sends NEWEPOCH to followers.                 
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
(*Integrity == \A l, f \in Server, msg \in msgs:
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
\* Last modified Thu Mar 11 22:59:45 CST 2021 by Dell
\* Created Sat Dec 05 13:32:08 CST 2020 by Dell


