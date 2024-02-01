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

\* Problematic sets of messages (p1 is the malicious node):

\* \* defeats def using SCCs (empty coffer possible at round 3):
\* M1 == {
\*     [round |-> 0, id |-> <<p1, 1>>, coffer |-> {}],
\*     [round |-> 0, id |-> <<p1, 2>>, coffer |-> {}],
\*     [round |-> 0, id |-> <<p2, 1>>, coffer |-> {}],
\*     [round |-> 0, id |-> <<p3, 1>>, coffer |-> {}],
\*     [round |-> 1, id |-> <<p1, 3>>, coffer |-> {<<p1, 1>>, <<p1, 2>>, <<p2, 1>>, <<p3, 1>>}],
\*     [round |-> 1, id |-> <<p2, 2>>, coffer |-> {<<p2, 1>>, <<p3, 1>>}],
\*     [round |-> 1, id |-> <<p3, 2>>, coffer |-> {<<p2, 1>>, <<p3, 1>>}],
\*     [round |-> 2, id |-> <<p1, 4>>, coffer |-> {<<p1, 3>>}],
\*     [round |-> 2, id |-> <<p2, 3>>, coffer |-> {<<p2, 2>>, <<p3, 2>>}],
\*     [round |-> 2, id |-> <<p3, 3>>, coffer |-> {<<p2, 2>>, <<p3, 2>>}]
\* }

\* \* ASSUME AcceptedMessages(M1, 3) = {}
\* ASSUME StronglyConsistentChains(M1, 2) =
\* {
\*     {
\*         [round |-> 0, id |-> <<p1, 1>>, coffer |-> {}], 
\*         [round |-> 0, id |-> <<p1, 2>>, coffer |-> {}],
\*         [round |-> 0, id |-> <<p2, 1>>, coffer |-> {}],
\*         [round |-> 1, id |-> <<p1, 3>>, coffer |-> {<<p1, 1>>, <<p1, 2>>, <<p2, 1>>, <<p3, 1>>}],
\*         [round |-> 2, id |-> <<p1, 4>>, coffer |-> {<<p1, 3>>}]
\*     },
\*     {
\*         [round |-> 0, id |-> <<p1, 1>>, coffer |-> {}], 
\*         [round |-> 0, id |-> <<p1, 2>>, coffer |-> {}], 
\*         [round |-> 0, id |-> <<p3, 1>>, coffer |-> {}], 
\*         [round |-> 1, id |-> <<p1, 3>>, coffer |-> {<<p1, 1>>, <<p1, 2>>, <<p2, 1>>, <<p3, 1>>}], 
\*         [round |-> 2, id |-> <<p1, 4>>, coffer |-> {<<p1, 3>>}]
\*     },
\*     {
\*         [round |-> 0, id |-> <<p1, 1>>, coffer |-> {}],
\*         [round |-> 0, id |-> <<p2, 1>>, coffer |-> {}], 
\*         [round |-> 0, id |-> <<p3, 1>>, coffer |-> {}], 
\*         [round |-> 1, id |-> <<p1, 3>>, coffer |-> {<<p1, 1>>, <<p1, 2>>, <<p2, 1>>, <<p3, 1>>}], 
\*         [round |-> 2, id |-> <<p1, 4>>, coffer |-> {<<p1, 3>>}]
\*     },
\*     {
\*         [round |-> 0, id |-> <<p1, 2>>, coffer |-> {}],
\*         [round |-> 0, id |-> <<p2, 1>>, coffer |-> {}], 
\*         [round |-> 0, id |-> <<p3, 1>>, coffer |-> {}], 
\*         [round |-> 1, id |-> <<p1, 3>>, coffer |-> {<<p1, 1>>, <<p1, 2>>, <<p2, 1>>, <<p3, 1>>}], 
\*         [round |-> 2, id |-> <<p1, 4>>, coffer |-> {<<p1, 3>>}]
\*     },
\*     {
\*         [round |-> 0, id |-> <<p2, 1>>, coffer |-> {}], 
\*         [round |-> 0, id |-> <<p3, 1>>, coffer |-> {}], 
\*         [round |-> 1, id |-> <<p2, 2>>, coffer |-> {<<p2, 1>>, <<p3, 1>>}], 
\*         [round |-> 1, id |-> <<p3, 2>>, coffer |-> {<<p2, 1>>, <<p3, 1>>}], 
\*         [round |-> 2, id |-> <<p2, 3>>, coffer |-> {<<p2, 2>>, <<p3, 2>>}]
\*     }, 
\*     {
\*         [round |-> 0, id |-> <<p2, 1>>, coffer |-> {}], 
\*         [round |-> 0, id |-> <<p3, 1>>, coffer |-> {}], 
\*         [round |-> 1, id |-> <<p2, 2>>, coffer |-> {<<p2, 1>>, <<p3, 1>>}], 
\*         [round |-> 1, id |-> <<p3, 2>>, coffer |-> {<<p2, 1>>, <<p3, 1>>}], 
\*         [round |-> 2, id |-> <<p3, 3>>, coffer |-> {<<p2, 2>>, <<p3, 2>>}]
\*     }, 
\*     {
\*         [round |-> 0, id |-> <<p1, 1>>, coffer |-> {}], 
\*         [round |-> 0, id |-> <<p1, 2>>, coffer |-> {}], 
\*         [round |-> 0, id |-> <<p2, 1>>, coffer |-> {}], 
\*         [round |-> 0, id |-> <<p3, 1>>, coffer |-> {}], 
\*         [round |-> 1, id |-> <<p1, 3>>, coffer |-> {<<p1, 1>>, <<p1, 2>>, <<p2, 1>>, <<p3, 1>>}], 
\*         [round |-> 2, id |-> <<p1, 4>>, coffer |-> {<<p1, 3>>}]},
\*     {
\*         [round |-> 0, id |-> <<p2, 1>>, coffer |-> {}],
\*         [round |-> 0, id |-> <<p3, 1>>, coffer |-> {}], 
\*         [round |-> 1, id |-> <<p2, 2>>, coffer |-> {<<p2, 1>>, <<p3, 1>>}], 
\*         [round |-> 1, id |-> <<p3, 2>>, coffer |-> {<<p2, 1>>, <<p3, 1>>}], 
\*         [round |-> 2, id |-> <<p2, 3>>, coffer |-> {<<p2, 2>>, <<p3, 2>>}], 
\*         [round |-> 2, id |-> <<p3, 3>>, coffer |-> {<<p2, 2>>, <<p3, 2>>}]
\*     }
\* }

\* \* defeats def using CCs (empty coffer possible at round 3):
\* M2 == {
\*     [round |-> 0, id |-> <<p1, 1>>, coffer |-> {}],
\*     [round |-> 0, id |-> <<p2, 1>>, coffer |-> {}],
\*     [round |-> 0, id |-> <<p3, 1>>, coffer |-> {}],
\*     [round |-> 1, id |-> <<p1, 2>>, coffer |-> {<<p1, 1>>}],
\*     [round |-> 1, id |-> <<p1, 3>>, coffer |-> {<<p1, 1>>}],
\*     [round |-> 1, id |-> <<p2, 2>>, coffer |-> {<<p2, 1>>, <<p3, 1>>}],
\*     [round |-> 1, id |-> <<p3, 2>>, coffer |-> {<<p2, 1>>, <<p3, 1>>}],
\*     [round |-> 2, id |-> <<p1, 4>>, coffer |-> {<<p1, 3>>}],
\*     [round |-> 2, id |-> <<p2, 3>>, coffer |-> {<<p2, 2>>, <<p3, 2>>}],
\*     [round |-> 2, id |-> <<p3, 3>>, coffer |-> {<<p2, 2>>, <<p3, 2>>}]
\* }

\* Expr2 == AcceptedMessages(M2, 3)
\* \* ASSUME Expr2 = {}

\* \* defeats def using HSCCs (coffer {<<p1,3>>} possible at round 2):
\* M3 == {
\*     [round |-> 0, id |-> <<p1, 1>>, coffer |-> {}],
\*     [round |-> 0, id |-> <<p1, 2>>, coffer |-> {}],
\*     [round |-> 0, id |-> <<p2, 1>>, coffer |-> {}],
\*     [round |-> 0, id |-> <<p3, 1>>, coffer |-> {}],
\*     [round |-> 1, id |-> <<p1, 3>>, coffer |-> {<<p1, 1>>, <<p1, 2>>, <<p2, 1>>, <<p3, 1>>}],
\*     [round |-> 1, id |-> <<p2, 2>>, coffer |-> {<<p2, 1>>, <<p3, 1>>}],
\*     [round |-> 1, id |-> <<p3, 2>>, coffer |-> {<<p2, 1>>, <<p3, 1>>}]
\* }

\* Expr3 == HeaviestStronglyConsistentChains(M3, 1)
\* ASSUME Expr3 = {
\*     {
\*         [round |-> 0, id |-> <<p1, 1>>, coffer |-> {}],
\*         [round |-> 0, id |-> <<p1, 2>>, coffer |-> {}],
\*         [round |-> 0, id |-> <<p2, 1>>, coffer |-> {}],
\*         [round |-> 0, id |-> <<p3, 1>>, coffer |-> {}],
\*         [round |-> 1, id |-> <<p1, 3>>, coffer |-> {<<p1, 1>>, <<p1, 2>>, <<p2, 1>>, <<p3, 1>>}]
\*     }
\* }

\* \* defeats def using HCCs (coffer {<<p1, 2>>, <<p1, 3>>, <<p2, 2>>, <<p3, 2>>} possible at round 2):
\* M4 == {
\*     [round |-> 0, id |-> <<p1, 1>>, coffer |-> {}],
\*     [round |-> 0, id |-> <<p2, 1>>, coffer |-> {}],
\*     [round |-> 0, id |-> <<p3, 1>>, coffer |-> {}],
\*     [round |-> 1, id |-> <<p1, 2>>, coffer |-> {<<p1, 1>>}],
\*     [round |-> 1, id |-> <<p1, 3>>, coffer |-> {<<p2, 1>>}],
\*     [round |-> 1, id |-> <<p2, 2>>, coffer |-> {<<p2, 1>>, <<p3, 1>>}],
\*     [round |-> 1, id |-> <<p3, 2>>, coffer |-> {<<p2, 1>>, <<p3, 1>>}]
\* }

\* Expr4 == HeaviestConsistentChains(M4, 1)
\* ASSUME Expr4 = {
\*     {
\*         [round |-> 0, id |-> <<p1, 1>>, coffer |-> {}],
\*         [round |-> 0, id |-> <<p2, 1>>, coffer |-> {}], 
\*         [round |-> 0, id |-> <<p3, 1>>, coffer |-> {}], 
\*         [round |-> 1, id |-> <<p1, 2>>, coffer |-> {<<p1, 1>>}], 
\*         [round |-> 1, id |-> <<p1, 3>>, coffer |-> {<<p2, 1>>}], 
\*         [round |-> 1, id |-> <<p2, 2>>, coffer |-> {<<p2, 1>>, <<p3, 1>>}], 
\*         [round |-> 1, id |-> <<p3, 2>>, coffer |-> {<<p2, 1>>, <<p3, 1>>}]
\*     }
\* }

\* \* violation (coffer {<<p3, 2>>, <<p5, 3>>} possible at round 2)
\* \* took 50 minutes
\* \* But expected since we had tWB=3 and tAdv=2 with p4 and p5 malicious...
\* M5 == {
\*     [round |-> 0, id |-> <<p1, 1>>, coffer |-> {}], 
\*     [round |-> 0, id |-> <<p2, 1>>, coffer |-> {}], 
\*     [round |-> 0, id |-> <<p3, 1>>, coffer |-> {}], 
\*     [round |-> 0, id |-> <<p4, 1>>, coffer |-> {}], 
\*     [round |-> 0, id |-> <<p4, 2>>, coffer |-> {}], 
\*     [round |-> 0, id |-> <<p5, 1>>, coffer |-> {}], 
\*     [round |-> 1, id |-> <<p1, 2>>, coffer |-> {<<p1, 1>>, <<p2, 1>>, <<p3, 1>>}], 
\*     [round |-> 1, id |-> <<p2, 2>>, coffer |-> {<<p1, 1>>, <<p2, 1>>, <<p3, 1>>}], 
\*     [round |-> 1, id |-> <<p3, 2>>, coffer |-> {<<p1, 1>>, <<p2, 1>>, <<p3, 1>>, <<p4, 1>>}], 
\*     [round |-> 1, id |-> <<p4, 3>>, coffer |-> {<<p4, 2>>}], 
\*     [round |-> 1, id |-> <<p5, 2>>, coffer |-> {<<p4, 1>>, <<p5, 1>>}], 
\*     [round |-> 1, id |-> <<p5, 3>>, coffer |-> {<<p1, 1>>, <<p2, 1>>, <<p4, 1>>, <<p4, 2>>}]
\* }
\* Expr5 == MinimalStronglyConsistentChains(M5, 1)
\* \* ASSUME AcceptedMessages(M5, 2) = {[round |-> 1, id |-> <<p3, 2>>, coffer |-> {<<p1, 1>>, <<p2, 1>>, <<p3, 1>>, <<p4, 1>>}], [round |-> 1, id |-> <<p5, 3>>, coffer |-> {<<p1, 1>>, <<p2, 1>>, <<p4, 1>>, <<p4, 2>>}]} \* Takes forever...

==========================================================