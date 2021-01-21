-------------------------------- MODULE Zab --------------------------------
EXTENDS Integers, FiniteSets, Sequences, Naturals, TLC

\* The set of server IDs
CONSTANT Server

\* The set of requests that can go into history
CONSTANT Value

\* Server states
CONSTANTS Follower, Leader, ProspectiveLeader

\* Message types
CONSTANTS CEPOCH, NEWEPOCH, ACK_E, NEWLEADER, ACK_LD, COMMIT_LD, PROPOSE, ACK, COMMIT

Maximum(S) == IF S = {} THEN -1
                        ELSE CHOOSE n \in S: \A m \in S: n >= m

Quorums == {Q \in SUBSET Server: Cardinality(Q)*2 > Cardinality(Server)}

(*Here need to be added about Messages*)

None == CHOOSE v: v \notin Value

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
\* Last modified Thu Jan 21 22:55:25 CST 2021 by Dell
\* Created Sat Dec 05 13:32:08 CST 2020 by Dell


