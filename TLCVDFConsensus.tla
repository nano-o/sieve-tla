----------------- MODULE TLCVDFConsensus -----------------

EXTENDS Integers, FiniteSets, TLC

CONSTANTS
    \* p1, p2, p3
    p1, p2, p3, p4, p5

MaxTick == 18

\* P == {p1,p2,p3}
\* B == {p1}
\* tAdv == 2
\* tWB == 3

\* with SCC rule, violation at tick 9 (depth 74):
\* P == {p1,p2,p3}
\* B == {p1}
\* tAdv == 2
\* tWB == 3

\* with SCC rule, violation at tick 9 (depth 74):
\* P == {p1,p2,p3}
\* B == {p1}
\* tAdv == 2
\* tWB == 3

P == {p1,p2,p3,p4,p5}
B == {p4,p5}
tAdv == 3
tWB == 4

Sym == Permutations(P \ B)\cup Permutations(B) 

VARIABLES messages, pendingMessage, tick, phase, donePhase, pc, messageCount

TickConstraint == tick <= MaxTick

INSTANCE VDFConsensus

Canary1 == \neg (
    tick = 2 /\ phase = "end"
)

\* Check that the adversary can indeed outpace the round number of well-behaved nodes:
Canary2 == \neg (
    tick = 5 /\ \E m \in messages : m.sender = p1 /\ m.round = 2
)

\* With this constraint we let the adversary build an initial "thin" chain of length 3:
AdvConstraint == \A m1,m2 \in messages :
    /\  sender(m1) \in B
    /\  sender(m2) \in B
    /\  m1.round <= 2
    /\  m2.round <= 2
    /\  m1.round = m2.round
    => m1 = m2

\* defeats MinSCCs (p4 and p5 malicious); coffer {<<p3,2>>} possible at round 2:
M1 == {
    [round |-> 0, id |-> <<p1, 1>>, coffer |-> {}],
    [round |-> 0, id |-> <<p2, 1>>, coffer |-> {}], 
    [round |-> 0, id |-> <<p3, 1>>, coffer |-> {}], 
    [round |-> 0, id |-> <<p4, 1>>, coffer |-> {}], 
    [round |-> 0, id |-> <<p5, 1>>, coffer |-> {}], 
    [round |-> 1, id |-> <<p1, 2>>, coffer |-> {<<p1, 1>>, <<p2, 1>>, <<p3, 1>>}], 
    [round |-> 1, id |-> <<p2, 2>>, coffer |-> {<<p1, 1>>, <<p2, 1>>, <<p3, 1>>}], 
    [round |-> 1, id |-> <<p3, 2>>, coffer |-> {<<p1, 1>>, <<p2, 1>>, <<p3, 1>>, <<p4, 1>>, <<p5, 1>>}],
    [round |-> 1, id |-> <<p4, 2>>, coffer |-> {<<p4, 1>>}], 
    [round |-> 1, id |-> <<p5, 2>>, coffer |-> {<<p5, 1>>}]
}

==========================================================