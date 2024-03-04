----------------- MODULE TLCVDFConsensusSimulation -----------------

EXTENDS Integers, FiniteSets, TLC

\* CONSTANTS
\*     p1, p2, p3, p4, p5
\* P == {p1,p2,p3,p4,p5}
\* B == {p4,p5}
\* tAdv == 1
\* tWB == 1

\* CONSTANTS
\*     p1, p2, p3, p4, p5
\* P == {p1,p2,p3,p4,p5}
\* B == {p4,p5}
\* \* in this case, 3/4 is only interesting if we can get to round 3 (otherwise there's no real adversarial advantage compared to 1/1)
\* tAdv == 3
\* tWB == 4

CONSTANTS
    p1, p2, p3
P == {p1,p2,p3}
B == {p1}
tAdv == 2
tWB == 3

\* CONSTANTS
\*     p1, p2, p3
\* P == {p1,p2,p3}
\* B == {p1}
\* tAdv == 1
\* tWB == 1

Sym == Permutations(P \ B)\cup Permutations(B)

VARIABLES messages, pendingMessage, tick, phase, donePhase, pc, messageCount
    
INSTANCE VDFConsensusSimulation

\* Debugging canaries:

Canary1 == \neg (
    tick = 2 /\ phase = "end"
)

M == {[id |-> <<p1, 1>>, round |-> 0, coffer |-> {}], [id |-> <<p1, 2>>, round |-> 1, coffer |-> {<<p1, 1>>}], [id |-> <<p1, 3>>, round |-> 1, coffer |-> {<<p1, 1>>, <<p2, 1>>}], [id |-> <<p1, 4>>, round |-> 2, coffer |-> {<<p1, 2>>, <<p1, 3>>, <<p2, 2>>, <<p3, 2>>}], [id |-> <<p1, 5>>, round |-> 3, coffer |-> {<<p1, 4>>}], [id |-> <<p1, 6>>, round |-> 3, coffer |-> {<<p1, 4>>}], [id |-> <<p2, 1>>, round |-> 0, coffer |-> {}], [id |-> <<p2, 2>>, round |-> 1, coffer |-> {<<p1, 1>>, <<p2, 1>>, <<p3, 1>>}], [id |-> <<p2, 3>>, round |-> 2, coffer |-> {<<p2, 2>>, <<p3, 2>>}], [id |-> <<p2, 4>>, round |-> 3, coffer |-> {<<p2, 3>>, <<p3, 3>>}], [id |-> <<p3, 1>>, round |-> 0, coffer |-> {}], [id |-> <<p3, 2>>, round |-> 1, coffer |-> {<<p1, 1>>, <<p2, 1>>, <<p3, 1>>}], [id |-> <<p3, 3>>, round |-> 2, coffer |-> {<<p2, 2>>, <<p3, 2>>}], [id |-> <<p3, 4>>, round |-> 3, coffer |-> {<<p2, 3>>, <<p3, 3>>}]}

Test ==
    \* ConsistentHistory({[id |-> <<p2, 3>>, round |-> 2, coffer |-> {<<p2, 2>>, <<p3, 2>>}], [id |-> <<p3, 3>>, round |-> 2, coffer |-> {<<p2, 2>>, <<p3, 2>>}]}, M)
    \* ConsistentHistory({[id |-> <<p2, 2>>, round |-> 1, coffer |-> {<<p1,1>>, <<p2, 1>>, <<p3, 1>>}], [id |-> <<p3, 2>>, round |-> 1, coffer |-> {<<p1,1>>, <<p2, 1>>, <<p3, 1>>}]}, M)
    \* ConsistentHistory({[id |-> <<p2, 1>>, round |-> 0, coffer |-> {}], [id |-> <<p3, 1>>, round |-> 0, coffer |-> {}]}, M)
    \* ConsistentHistory({[id |-> <<p2, 4>>, round |-> 3, coffer |-> {<<p2, 3>>, <<p3, 3>>}], [id |-> <<p3, 4>>, round |-> 3, coffer |-> {<<p2, 3>>, <<p3, 3>>}]}, M)
    ConsistentHistory({[id |-> <<p1, 5>>, round |-> 3, coffer |-> {<<p1, 4>>}], [id |-> <<p1, 6>>, round |-> 3, coffer |-> {<<p1, 4>>}]}, M)

Test2 ==
    IDs(CHOOSE S \in MaximalSets(ConsistentHistories({[id |-> <<p1, 5>>, round |-> 3, coffer |-> {<<p1, 4>>}], [id |-> <<p1, 6>>, round |-> 3, coffer |-> {<<p1, 4>>}]}, M)) : TRUE)
    \* IDs(CHOOSE S \in MaximalSets(ConsistentHistories({[id |-> <<p2, 4>>, round |-> 3, coffer |-> {<<p2, 3>>, <<p3, 3>>}], [id |-> <<p3, 4>>, round |-> 3, coffer |-> {<<p2, 3>>, <<p3, 3>>}]}, M)) : TRUE)
    
Test3 ==
    Cardinality(MaxCardinalitySets(ConsistentHistories({[id |-> <<p1, 5>>, round |-> 3, coffer |-> {<<p1, 4>>}], [id |-> <<p1, 6>>, round |-> 3, coffer |-> {<<p1, 4>>}]}, M)))
        \* Cardinality(MaxCardinalitySets(ConsistentHistories({[id |-> <<p2, 4>>, round |-> 3, coffer |-> {<<p2, 3>>, <<p3, 3>>}], [id |-> <<p3, 4>>, round |-> 3, coffer |-> {<<p2, 3>>, <<p3, 3>>}]}, M)))
    
\* Test4 == 
\*     LET 
\*         H1 == MaxConsistentHistory({[id |-> <<p1, 5>>, round |-> 3, coffer |-> {<<p1, 4>>}], [id |-> <<p1, 6>>, round |-> 3, coffer |-> {<<p1, 4>>}]},M)
\*         H2 == MaxConsistentHistory({[id |-> <<p2, 4>>, round |-> 3, coffer |-> {<<p2, 3>>, <<p3, 3>>}], [id |-> <<p3, 4>>, round |-> 3, coffer |-> {<<p2, 3>>, <<p3, 3>>}]},M)
\*     IN  GT(H1,H2)

=========================================================