------------ MODULE VDFConsensus ----------------

EXTENDS FiniteSets, Integers, Utils

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

\* A message consists of a unique ID, a round number, and a coffer containing the IDs of a set of predecessor messages:
MessageID == P\times Nat
Message == [id : MessageID, round : Round, coffer : SUBSET MessageID]
sender(m) == m.id[1]

(**********************************************************************************)
(* A strongly consistent chain is a subset of the messages in the DAG that        *)
(* potentially has some dangling pointers (i.e. messages that have predecessors   *)
(* not in the chain) and that satisfies the following recursive predicate:        *)
(*                                                                                *)
(*     * Any set of messages which all have a round of 0 is a strongly consistent *)
(*     chain.                                                                     *)
(*                                                                                *)
(*     * A set of messages C with some non-zero rounds and maximal round r is a   *)
(*     strongly consistent chain when, with Tip being the set of messages in the  *)
(*     chain that have round r and Pred being the set of messages in the chain    *)
(*     with round r-1, Pred is a strict majority of the set of predecessors of    *)
(*     each message in Tip and C \ Tip is a consistent chain.                     *)
(**********************************************************************************)

\* The max round of a set of messages is the maximal round of its messages:
MaxRound(M) == MaxInteger({m.round : m \in M})

StronglyConsistentChain(M) ==
    /\  M # {}
    /\  \/  MaxRound(M) = 0
        \/  \A r \in 1..MaxRound(M) :
            LET Tip == { m \in M : m.round = r }
                Pred == { m \in M : m.round = r-1 }
            IN  /\  Tip # {}
                /\  \A m \in Tip :
                    /\  {m2.id : m2 \in Pred} \subseteq m.coffer
                    /\  2*Cardinality(Pred) > Cardinality(m.coffer)

\* A weaker version of the above:
ConsistentChain(M) ==
    /\  M # {}
    /\  \/  MaxRound(M) = 0
        \/  \A r \in 1..MaxRound(M) :
            LET Tip == { m \in M : m.round = r }
                Pred == { m \in M : m.round = r-1 }
            IN  /\  Tip # {}
                /\  \A m \in Tip : \E Maj \in SUBSET Pred :
                    /\ {m2.id : m2 \in Maj} \subseteq m.coffer
                    /\  2*Cardinality(Maj) > Cardinality(m.coffer)


RECURSIVE Chains(_,_)
Chains(M,r) ==
    LET MM == {m \in M : m.round = r} IN
        IF r = 0
        THEN {M1 : M1 \in (SUBSET MM) \ {}}
        ELSE {M1 \cup M2 : M1 \in (SUBSET MM) \ {}, M2 \in Chains(M \ MM, r-1)}
    
\* The set of all consistent chains that can be found in M:
ConsistentChains(M, r) ==
    {C \in Chains(M, r) : ConsistentChain(C)}

\* The set of all strongly consistent chains that can be found in M:
StronglyConsistentChains(M, r) ==
    {C \in Chains(M, r) : StronglyConsistentChain(C)}
        
(*****************************************************************************)
(* We can rank the chains by wheight, i.e. just their cardinality, or we can *)
(* consider the maximal or minimal one in the subset order:                  *)
(*****************************************************************************)
HeaviestConsistentChains(M, r) == MaxCardinalitySets(ConsistentChains(M, r))
HeaviestStronglyConsistentChains(M, r) == MaxCardinalitySets(StronglyConsistentChains(M, r))
MinimalStronglyConsistentChains(M, r) == MinimalSets(StronglyConsistentChains(M, r))
MaximalStronglyConsistentChains(M, r) == MaximalSets(StronglyConsistentChains(M, r))

(*********************************************************************************)
(* Two chains are disjoint when there is a round smaller than their max round in *)
(* which they have no messages in common.                                        *)
(*********************************************************************************)
DisjointChains(C1,C2) ==
    LET rmax == MaxRound(C1 \cup C2)
    IN  \E r \in 0..(rmax-1) :
            {m \in C1 : m.round = r} \cap {m \in C2 : m.round = r} = {}

(*******************)
(* Acceptance rule *)
(*******************)
AcceptedMessages(M,r) == {m \in M :
    /\  m.round = r-1
    /\  LET CCs == MaximalStronglyConsistentChains(M,r-1) IN \* This looks promising!
        /\  \E C \in CCs : m \in C
        /\  \A C1,C2 \in CCs :
                /\  m \in C1
                /\  m \notin C2
                /\  DisjointChains(C1,C2)
                => Cardinality(C2) <= Cardinality(C1)}

\* M does not have dangling edges:
Closed(M) == \A m \in M : \A i \in m.coffer : \E m2 \in M : m2.id = i

(********************************)
(* Now we specify the algorithm *)
(********************************)

(*--algorithm Algo {
    variables
        messages = {};
        tick = 0;
        phase = "start"; \* each tick has two phases: "start" and "end"
        donePhase = [p \in P |-> "end"];
        pendingMessage = [p \in P |-> <<>>]; \* message we're computing the VDF on
        messageCount = [p \in P |-> 0]; \* used to generate unique message IDs
    define {
        currentRound == tick \div tWB \* round of well-behaved processes
        wellBehavedMessages == {m \in messages : sender(m) \in P \ B}
        \* possible sets of messages received by a well-behaved process:
        receivedMsgsSets == 
            \* ignore messages from future rounds:
            LET msgs == {m \in messages : m.round < currentRound} IN
            {M \in SUBSET msgs :
                \* don't use a set of messages that has dangling edges (messages in coffers that are missing):
                /\  Closed(M)
                /\  wellBehavedMessages \subseteq  M}
    }
    macro sendMessage(m) {
        messages := messages \cup {m}
    }
    process (clock \in {"clock"}) {
tick:   while (TRUE) {
            await \A p \in P : donePhase[p] = phase;
            if (phase = "start")
                phase := "end"
            else {
                phase := "start";
                tick := tick+1
            }
        }
    }
    process (proc \in P \ B) \* a well-behaved process
    {
l1:     while (TRUE) {
            await phase = "start";
            if (tick % tWB = 0) {
                \* Start the VDF computation for the next message:
                with (msgs \in receivedMsgsSets)
                with (predMsgs = AcceptedMessages(msgs, currentRound)) {
                    pendingMessage[self] := [
                        id |-> <<self,messageCount[self]+1>>,
                        round |-> currentRound,
                        coffer |-> {m.id : m \in predMsgs}];
                    messageCount[self] := messageCount[self]+1
                }
            };
            donePhase[self] := "start";
l2:         await phase = "end";
            if (tick % tWB = tWB - 1)
                \* it's the end of the tWB period, the VDF has been computed
                sendMessage(pendingMessage[self]);
            donePhase[self] := "end";
        }
    }
    process (byz \in B) \* a malicious process
    {
lb1:    while (TRUE) {
            await phase = "start";
            if (tick % tAdv = 0) {
                \* Start the VDF computation for the next message:
                with (maxRound = Max({m.round : m \in messages} \cup {0}, <=))
                with (rnd \in {maxRound, maxRound+1})
                with (predMsgs \in SUBSET {m \in messages : m.round = rnd-1}) {
                    when rnd > 0 => predMsgs # {};
                    pendingMessage[self] := [
                        id |-> <<self,messageCount[self]+1>>,
                        round |-> rnd,
                        coffer |-> {m.id : m \in predMsgs}];
                    messageCount[self] := messageCount[self]+1
                }
            };
            donePhase[self] := "start";
lb2:        await phase = "end";
            if (tick % tAdv = tAdv - 1)
                sendMessage(pendingMessage[self]);
            donePhase[self] := "end";
        };
    }
}
*)

\* Invariant describing the type of the variables:
TypeOK == 
    /\  messages \in SUBSET Message
    /\  pendingMessage \in [P -> Message \cup {<<>>}]
    /\  tick \in Tick
    /\  phase \in {"start", "end"}
    /\  donePhase \in [P -> {"start", "end"}]
    /\  messageCount \in [P -> Nat]

(**********************************************************************************)
(* The main property we want to establish is that, each round, for each message m *)
(* of a well-behaved process, the messages of well-behaved processes from the     *)
(* previous round are all in m's coffer and consist of a strict majority of m's   *)
(* coffer.                                                                        *)
(**********************************************************************************)
Safety == \A p \in P \ B : LET m == pendingMessage[p] IN
    /\  m # <<>>
    /\  m.round > 0
    =>
    /\  \A m2 \in wellBehavedMessages : m2.round = m.round-1 => m2.id \in m.coffer
    /\  LET M == {m2 \in wellBehavedMessages : m2.round = m.round-1}
        IN  2*Cardinality(M) > Cardinality(m.coffer)

\* helper definition:
messageWithID(id) == CHOOSE m \in messages : m.id = id

\* Basic well-formedness properties:    
Inv1 == \A m \in messages : 
    /\  \A m2 \in messages : m # m2 => m.id # m2.id
    /\  \A id \in m.coffer :
        /\  \E m2 \in messages : m2.id = id
        /\  messageWithID(id).round = m.round-1
    
=================================================
