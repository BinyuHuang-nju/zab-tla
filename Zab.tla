-------------------------------- MODULE Zab --------------------------------
EXTENDS Integers, FiniteSets, Sequences, Naturals, TLC

\* The set of server identifiers
CONSTANT Server

\* The set of requests that can go into history
CONSTANT Value

\* Server states
CONSTANTS Follower, Leader, ProspectiveLeader

\* Message types
CONSTANTS CEPOCH, NEWEPOCH, ACK_E, NEWLEADER, ACK_LD, COMMIT_LD, PROPOSE, ACK, COMMIT

\* the maximum round of epoch (initially {0,1,2})
CONSTANT Epoches
----------------------------------------------------------------------------
Maximum(S) == IF S = {} THEN -1
                        ELSE CHOOSE n \in S: \A m \in S: n >= m

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
\* The server's state(Follower,Leader,ProspectiveLeader)
VARIABLE state

\* The leader's epoch or the last new epoch proposal the follower acknowledged(f.p in paper)
VARIABLE currentEpoch

\* The last new leader proposal the follower acknowledged(f.a in paper)
VARIABLE leaderEpoch

\* The identifier of the leader for followers
VARIABLE leaderOracle

\* The history of servers as the sequence of transactions
VARIABLE history

\* The messages repersenting requests and responses sent from one server to another
VARIABLE msgs

vars == <<state, currentEpoch, leaderEpoch, leaderOracle, history, msgs>>
----------------------------------------------------------------------------
LastZxid(his) == IF Len(his) > 0 THEN <<his[Len(his)].epoch,his[Len(his)].counter>>
                                 ELSE <<-1, -1>>

Send(m) == msgs' = msgs \union {m}

(*TypeOK == /\ msgs \in [Server -> [Server ->]]*)
TypeOK == /\ state \in [Server -> {Follower, Leader, ProspectiveLeader}]
          /\ currentEpoch \in [Server -> Epoches]
          /\ leaderEpoch \in [Server -> Epoches]
          /\ leaderOracle \in [Server -> Server]
          \*/\ msgs \subseteq Messages
----------------------------------------------------------------------------
Init == /\ state = [s \in Server |-> Follower]
        /\ currentEpoch = [s \in Server |-> 0]
        /\ leaderEpoch = [s \in Server |-> 0]
        /\ leaderOracle = [s \in Server |-> NullPoint]
        /\ history = [s \in Server |-> << >>]
        /\ msgs = {}

PhaseFollower11(i) == /\ state[i] = Follower
                      /\ leaderOracle[i] # NullPoint
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
                  
PhaseLeader11(i) == /\ state[i] = ProspectiveLeader
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
                           /\ leaderEpoch' = [leaderEpoch EXCEPT ![i] = newEpoch]
                           /\ Send([mtype   |-> NEWEPOCH,
                                    msource |-> i,
                                    mdest   |-> Server \ {i},
                                    mepoch  |-> newEpoch])
                    /\ UNCHANGED <<state, leaderOracle, history>>

PhaseFollower12(i) == /\ state[i] = Follower
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
                                        /\ Send([mtype     |-> ACK_E,
                                                 msource   |-> i,
                                                 mdest     |-> m.msource,
                                                 lastEpoch |-> leaderEpoch[i],
                                                 hf        |-> history[i]])
                      /\ UNCHANGED <<state, leaderEpoch, history>>
                      
PhaseLeader12and21(i) == /\ state[i] = ProspectiveLeader                 
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
\* Last modified Wed Mar 10 15:03:37 CST 2021 by Dell
\* Created Sat Dec 05 13:32:08 CST 2020 by Dell


