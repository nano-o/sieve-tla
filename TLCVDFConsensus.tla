----------------- MODULE TLCVDFConsensus -----------------

EXTENDS Integers, FiniteSets, TLC

CONSTANTS
    p1, p2, p3, p4 \*, p5

P == {p1,p2,p3}
B == {p1}
tAdv == 2
tWB == 3

\* We use the following definition to bound the state-space for the model-checker
MaxTick == 8
MCTick == 0..MaxTick
MCRound == 0..(MaxTick \div tAdv)
MCMessageID == 0..(MCRound*Cardinality(P))


VARIABLES messages, messageCount, pendingMessage, tick, phase, donePhase, pc

INSTANCE VDFConsensus

\* TODO: using model values for message IDs could allow using symmetry on them
Sym == Permutations(P \ B) \cup Permutations(B)

TickConstraint == tick <= 8

\* Check that the adversary can indeed outpace the round number of well-behaved nodes:
Canary2 == \neg (
    tick = 5 /\ \E m \in messages : m.sender = p1 /\ m.round = 2
)

\* The TLC model-checker confirms all the assumptions below.

ASSUME Intersection({{1,2},{2,3}}) = {2}
ASSUME Intersection({}) = {}
ASSUME Intersection({{1,2},{3,4}}) = {}

m1 == [id |-> 1, round |-> 0, coffer|-> {}] \* well-behaved message
m2 == [id |-> 2, round |-> 0, coffer|-> {}] \* well-behaved message
m3 == [id |-> 3, round |-> 0, coffer|-> {}] \* malicious message
m4 == [id |-> 4, round |-> 1, coffer|-> {1,2}] \* well-behaved message
m5 == [id |-> 5, round |-> 1, coffer|-> {1,2,3}] \* well-behaved message
m6 == [id |-> 6, round |-> 1, coffer|-> {1,3}] \* malicious message

ASSUME \neg ConsistentSet({m1,m2,m3})
ASSUME ConsistentSet({m4,m5})
ASSUME \neg ConsistentSet({m4,m5,m6})

ASSUME ConsistentChain({m1,m2,m3})
ASSUME ConsistentChain({m1,m2,m4,m5})
ASSUME \neg ConsistentChain({m1,m2,m3,m4,m5}) \* m3 is not a predecessor of m4
ASSUME \neg ConsistentChain({m1,m2,m3,m4,m5,m6}) \* {m4,m5,m6} is not even consistent

ASSUME HeaviestConsistentChain({m1,m2,m3}) = {m1,m2,m3}

(*********************************************************************************)
(* Now we have a problem: the heaviest consistent chain in {m1,m2,m3,m4,m5} does *)
(* not have all the well-behaved messages. That's because both {m1,m2,m3,m5} and *)
(* {m1,m2,m4,m5} are consistent chains, and we break ties arbitrarily. Should we *)
(* make more recent messages heavier?                                            *)
(*********************************************************************************)

ASSUME HeaviestConsistentChain({m1,m2,m3,m4,m5}) = {m1,m2,m3,m5} \* oops

m1a == [sender |-> p1, round |-> 0, id |-> 3, coffer |-> {}]
m2a == [sender |-> p1, round |-> 0, id |-> 4, coffer |-> {}]
m3a == [sender |-> p1, round |-> 0, id |-> 7, coffer |-> {}]
m4a == [sender |-> p1, round |-> 0, id |-> 10, coffer |-> {}]
m5a == [sender |-> p2, round |-> 0, id |-> 1, coffer |-> {}]
m6a == [sender |-> p2, round |-> 1, id |-> 5, coffer |-> {1, 2}]
m7a == [sender |-> p3, round |-> 0, id |-> 2, coffer |-> {}]
m8a == [sender |-> p3, round |-> 1, id |-> 6, coffer |-> {1, 2}]
m9a ==  [sender |-> p3, round |-> 2, id |-> 9, coffer |-> {}]


\* {[sender |-> p1, round |-> 0, id |-> 3, coffer |-> {}], 
\*     [sender |-> p1, round |-> 0, id |-> 4, coffer |-> {}],
\*  [sender |-> p1, round |-> 0, id |-> 7, coffer |-> {}],
\*      [sender |-> p2, round |-> 0, id |-> 1, coffer |-> {}],
\*      [sender |-> p2, round |-> 1, id |-> 5, coffer |-> {1, 2}],
\*      [sender |-> p3, round |-> 0, id |-> 2, coffer |-> {}],
\*      [sender |-> p3, round |-> 1, id |-> 6, coffer |-> {1, 2}]}

M == {m5a,m6a,m7a,m8a,m1a,m2a,m3a}
\* Expr == Max({m.round : m \in M}, <=)
\* Expr == {C \in SUBSET M : (\E m \in C : m.round = 1) /\ ConsistentChain(C)}
Expr == (0..2) \ {1}

BreakPoint1 == 
    IF \E p \in P \ B : LET m == pendingMessage[p] IN
        m # <<>> /\ m.round > 0 /\ m.coffer = {}
    THEN TRUE
    ELSE TRUE

WatchExpr1 ==
    {<<msgs, {m \in HeaviestConsistentChain(msgs) : m.round = 1}>> : msgs \in receivedMsgsSets}
        
==========================================================