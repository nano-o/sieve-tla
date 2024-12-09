------------ MODULE Sieve ----------------

EXTENDS FiniteSets, Integers, Utils, TLC

CONSTANTS
    P \* the set of processes
,   B \* the set of malicious processes
,   tAdv \* the time it takes for a malicious process to produce a message
,   tWB \* the time it takes for a well-behaved process to produce a message

ASSUME B \subseteq P \* malicious processes are a subset of all processes
W == P \ B \* the set of well-behaved processes

Tick == Nat \* a tick is a real-time clock tick
Step == Nat \* step number

(*********************************************************************************)
(* The message-production rate of well-behaved processes is of 1 message per tWB *)
(* ticks, and that of malicious processes is of 1 message per tAdv ticks. We     *)
(* require that, collectively and in any interval of at least tWB, well-behaved  *)
(* processes produce strictly more than twice the number of messages produced by *)
(* malicious processes.                                                          *)
(*********************************************************************************)
ASSUME Cardinality(W)*tAdv > 2*Cardinality(B)*tWB

SuperMajority(S1, S2) ==
    /\  S1 \subseteq S2
    /\  3*Cardinality(S1) > 2*Cardinality(S2)


(********************************************************************************)
(* A message identifier consists of a process identifier and a sequence number. *)
(********************************************************************************)
MessageID == P\times Nat

(********************************************************************************************)
(* A message consists of an identifier, a step number, and a coffer of message identifiers. *)
(********************************************************************************************)
Message == [id : MessageID, step: Step, coffer : SUBSET MessageID]
sender(m) == m.id[1]
Ids(M) == {m.id : m \in M}
FilterStep(M, s) == {m \in M : m.step = s}

(****************************)
(* Now on to BootstrapSieve *)
(****************************)

ConsistentSuccessor(M, m) ==
    SuperMajority(Ids(M), m.coffer)

RECURSIVE ConsistentDAG(_)
ConsistentDAG(M) == IF M = {} THEN TRUE ELSE
    LET maxStep == MaxInteger({m.step : m \in M})
        tip == FilterStep(M, maxStep)
    IN  IF \A m \in M : m.step = maxStep THEN TRUE
        ELSE LET prevTip == FilterStep(M, maxStep-1) IN
            /\  \A m \in tip : ConsistentSuccessor(prevTip, m)
            /\  ConsistentDAG(M \ tip)

RECURSIVE BootstrapSieve(_, _)
BootstrapSieve(M, s) ==  IF M = {} THEN M ELSE
    LET maxStep == MaxInteger({m.step : m \in M})
    IN  IF s > maxStep THEN M
        ELSE
            LET consistentDAGs == {D \in SUBSET M : ConsistentDAG(D)}
                M2 == {m \in M :
                    \/  m.step > s
                    \/  /\  m.step = s
                        /\  \E D \in consistentDAGs : m \in D
                        /\  LET CA == PickFrom(MaxCardinalitySets({D \in consistentDAGs : m \in D})) IN
                            \A CB \in consistentDAGs : CA \cap CB = {} => Cardinality(CB) < Cardinality(CA)}
            IN  BootstrapSieve(M2, s+1)

============================================================
