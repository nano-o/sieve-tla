----------------- MODULE TLCVDFConsensus -----------------

EXTENDS Integers, FiniteSets, TLC

CONSTANTS
    p1, p2, p3, p4 \*, p5

P == {p1,p2,p3}
B == {p1}
tAdv == 2
tWB == 3

\* 50 minutes, depth 104, to finish tick 12:
\* P == {p1,p2,p3}
\* B == {p1}
\* tAdv == 3
\* tWB == 4

\* 5m40s to get to tick 4 with this config:
\* P == {p1,p2,p3}
\* B == {p1}
\* tAdv == 1
\* tWB == 1

\* We use the following definition to bound the state-space for the model-checker
MaxTick == 18
\* MCTick == 0..MaxTick
\* MaxRound == MaxTick \div tAdv
\* MCRound == 0..MaxRound

VARIABLES messages, pendingMessage, tick, phase, donePhase, pc, messageCount

INSTANCE VDFConsensus

Sym == Permutations(P \ B)\cup Permutations(B) 

TickConstraint == tick <= MaxTick
\* With this constraint we let the adversary build an initial "thin" chain of length 3:
AdvConstraint == \A m1,m2 \in messages :
    /\  sender(m1) \in B
    /\  sender(m2) \in B
    /\  m1.round <= 2
    /\  m2.round <= 2
    /\  m1.round = m2.round
    => m1 = m2

Canary1 == \neg (
    tick = 12
)

\* Check that the adversary can indeed outpace the round number of well-behaved nodes:
Canary2 == \neg (
    tick = 5 /\ \E m \in messages : m.sender = p1 /\ m.round = 2
)

\* Examples of components of (strongly) consistent chains:

\* M == {
\*     [round |-> 0, id |-> <<p1, 1>>, coffer |-> {}],
\*     [round |-> 0, id |-> <<p2, 1>>, coffer |-> {}],
\*     [round |-> 0, id |-> <<p3, 1>>, coffer |-> {}],
\*     [round |-> 1, id |-> <<p1, 2>>, coffer |-> {<<p1, 1>>}],
\*     [round |-> 1, id |-> <<p1, 3>>, coffer |-> {<<p1, 1>>}],
\*     [round |-> 1, id |-> <<p2, 2>>, coffer |-> {<<p2, 1>>, <<p3, 1>>}],
\*     [round |-> 1, id |-> <<p3, 2>>, coffer |-> {<<p2, 1>>, <<p3, 1>>}] }

\* ASSUME Components(StronglyConsistentChains(M)) = 
\*     {
\*         {
\*             [round |-> 0, id |-> <<p1, 1>>, coffer |-> {}],
\*             [round |-> 1, id |-> <<p1, 2>>, coffer |-> {<<p1, 1>>}],
\*             [round |-> 1, id |-> <<p1, 3>>, coffer |-> {<<p1, 1>>}]
\*         },
\*         {
\*             [round |-> 0, id |-> <<p2, 1>>, coffer |-> {}],
\*             [round |-> 0, id |-> <<p3, 1>>, coffer |-> {}],
\*             [round |-> 1, id |-> <<p2, 2>>, coffer |-> {<<p2, 1>>, <<p3, 1>>}],
\*             [round |-> 1, id |-> <<p3, 2>>, coffer |-> {<<p2, 1>>, <<p3, 1>>}]
\*         }
\*     }


\* ASSUME Components(ConsistentChains(M)) = {
\*     {
\*         [round |-> 0, id |-> <<p1, 1>>, coffer |-> {}],
\*         [round |-> 0, id |-> <<p2, 1>>, coffer |-> {}],
\*         [round |-> 0, id |-> <<p3, 1>>, coffer |-> {}],
\*         [round |-> 1, id |-> <<p1, 2>>, coffer |-> {<<p1, 1>>}],
\*         [round |-> 1, id |-> <<p1, 3>>, coffer |-> {<<p1, 1>>}]},
\*     {
\*         [round |-> 0, id |-> <<p1, 1>>, coffer |-> {}],
\*         [round |-> 0, id |-> <<p2, 1>>, coffer |-> {}],
\*         [round |-> 0, id |-> <<p3, 1>>, coffer |-> {}],
\*         [round |-> 1, id |-> <<p2, 2>>, coffer |-> {<<p2, 1>>, <<p3, 1>>}],
\*         [round |-> 1, id |-> <<p3, 2>>, coffer |-> {<<p2, 1>>, <<p3, 1>>}]
\*     }
\* }

\* M2 == 
\*     {
\*         [round |-> 0, id |-> <<p1, 1>>, coffer |-> {}],
\*         [round |-> 0, id |-> <<p1, 2>>, coffer |-> {}],
\*         [round |-> 0, id |-> <<p2, 1>>, coffer |-> {}],
\*         [round |-> 0, id |-> <<p3, 1>>, coffer |-> {}],
\*         [round |-> 1, id |-> <<p1, 3>>, coffer |-> {<<p1, 1>>, <<p1, 2>>, <<p2, 1>>}],
\*         [round |-> 1, id |-> <<p2, 2>>, coffer |-> {<<p2, 1>>, <<p3, 1>>}],
\*         [round |-> 1, id |-> <<p3, 2>>, coffer |-> {<<p2, 1>>, <<p3, 1>>}]
\*     }

\* ASSUME Components(StronglyConsistentChains(M2)) = 
\*     {
\*         {
\*             [round |-> 0, id |-> <<p1, 1>>, coffer |-> {}],
\*             [round |-> 0, id |-> <<p1, 2>>, coffer |-> {}],
\*             [round |-> 0, id |-> <<p2, 1>>, coffer |-> {}],
\*             [round |-> 1, id |-> <<p1, 3>>, coffer |-> {<<p1, 1>>, <<p1, 2>>, <<p2, 1>>}]
\*         },
\*         {
\*             [round |-> 0, id |-> <<p2, 1>>, coffer |-> {}],
\*             [round |-> 0, id |-> <<p3, 1>>, coffer |-> {}],
\*             [round |-> 1, id |-> <<p2, 2>>, coffer |-> {<<p2, 1>>, <<p3, 1>>}],
\*             [round |-> 1, id |-> <<p3, 2>>, coffer |-> {<<p2, 1>>, <<p3, 1>>}]
\*         }
\*     }
    
==========================================================