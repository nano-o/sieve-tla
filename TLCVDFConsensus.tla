----------------- MODULE TLCVDFConsensus -----------------

EXTENDS Integers, FiniteSets, TLC

CONSTANTS
    p1, p2, p3, p4 \*, p5

P == {p1,p2,p3}
B == {p1}
\* TODO: should be 6 - 5 no?
tAdv == 3
tWB == 4

\* We use the following definition to bound the state-space for the model-checker
MaxTick == 12
MCTick == 0..MaxTick
MCRound == 0..(MaxTick \div tAdv)
MCMessageID == 0..(MCRound*Cardinality(P))


VARIABLES messages, messageCount, pendingMessage, tick, phase, donePhase, pc

INSTANCE VDFConsensus

\* TODO: using model values for message IDs could allow using symmetry on them
Sym == Permutations(P \ B) \cup Permutations(B)

TickConstraint == tick <= MaxTick

\* Check that the adversary can indeed outpace the round number of well-behaved nodes:
Canary2 == \neg (
    tick = 5 /\ \E m \in messages : m.sender = p1 /\ m.round = 2
)
        
==========================================================