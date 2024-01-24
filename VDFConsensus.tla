------------ MODULE VDFConsensus ----------------

EXTENDS FiniteSets, Naturals

CONSTANTS
    P \* the set of processes
,   B \* the set of malicious processes
,   tAdv \* the time it takes for a malicious process to produce a message
,   tWB \* the time it takes for a well-behaved process to produce a message

ASSUME B \subseteq P \* malicious processes are a subset of all processes
W == P \ B \* the set of well-behaved processes

Tick == Nat \* a tick is a real-time clock tick
Round == Nat \* a round is just a tag on a message

(***********************************************************************************)
(* Processes build a DAG of messages. The message-production rate of well-behaved  *)
(* processes is of 1 message per tWB ticks, and that of malicious processes is of  *)
(* 1 message per tAdv ticks. We require that, collectively, well-behaved processes *)
(* produce messages at a rate strictly higher than that of malicious processes.    *)
(***********************************************************************************)
ASSUME Cardinality(W)*tAdv > Cardinality(B)*tWB

MessageID == Nat
\* A message consists of a unique ID, a round number, and a pointer to a set of previous messages:
Message == [id : MessageID, round : Round, pred : SUBSET MessageID]

\* We will need the intersection of a set of sets:
RECURSIVE Intersection(_)
Intersection(Ss) ==
    CASE
        Ss = {} -> {}
    []  \E S \in Ss : Ss = {S} -> CHOOSE S \in Ss : Ss = {S}
    []  OTHER ->
            LET S == (CHOOSE S \in Ss : TRUE)
            IN  S \cap Intersection(Ss \ {S})

(*********************************************************************************)
(* A set of messages is consistent when the intersection of the sets of          *)
(* predecessors of each message is a strict majority of the predecessors of each *)
(* message.                                                                      *)
(*********************************************************************************)
ConsistentSet(M) ==
    LET I == Intersection({m.pred : m \in M})
    IN \A m \in M : 2*Cardinality(I) > Cardinality(m.pred)

(***********************************************************************************)
(* A consistent chain is a subset of the messages in the DAG that potentially has  *)
(* some dangling pointers (i.e. messages that have predecessors not in the chain)  *)
(* and that satisfies the following recursive predicate:                           *)
(*                                                                                 *)
(*     * Any set of messages which all have a round of 0 is a consistent chain.    *)
(*                                                                                 *)
(*     * A set of messages C with some non-zero rounds and maximal round r is a    *)
(*     consistent chain when, with Tip being the set of messages in the chain that *)
(*     have round r and Pred being the set of messages in the chain with round     *)
(*     r-1, Pred is a strict majority of the set of predecessors of each message   *)
(*     in Tip and C \ Tip is a consistent chain. (Note that this implies that Tip  *)
(*     is a consistent set)                                                        *)
(***********************************************************************************)
Max(X, Leq(_,_)) ==
    CHOOSE m \in X : \A x \in X : Leq(x,m)

RECURSIVE ConsistentChain(_)
ConsistentChain(M) ==
    IF M = {}
    THEN FALSE
    ELSE LET r == Max({m.round : m \in M}, <=) IN
        \/  r = 0
        \/  LET Tip == { m \in M : m.round = r }
                Pred == { m \in M : m.round = r-1 }
            IN  /\  \A m \in Tip : 
                    /\  Pred \subseteq m.pred
                    /\  2*Cardinality(Pred) > Cardinality(m.pred)
                /\  ConsistentChain(M \ Tip)

(***********************************************************************************)
(* Given a message DAG, the heaviest consistent chain is a consistent chain in the *)
(* DAG that has a maximal number of messages.                                      *)
(***********************************************************************************)
HeaviestConsistentChain(M) == 
    LET r == Max({m.round : m \in M}, <=)
        Cs == {C \in SUBSET M : ConsistentChain(C)}
    IN  
        IF Cs = {} THEN {}
        ELSE Max(Cs, LAMBDA C1,C2 : Cardinality(C1) <= Cardinality(C2))

=================================================
