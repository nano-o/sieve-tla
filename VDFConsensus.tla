------------ MODULE VDFConsensus ----------------

EXTENDS FiniteSets, Integers, Utils, TLC

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

\* The max round appearing in a set of messages:
MaxRound(M) == MaxInteger({m.round : m \in M})
MinRound(M) == MinInteger({m.round : m \in M})

(***********************************************************************************)
(* A strongly consistent chain C is a subset of the DAG of messages such that, for *)
(* each round r between 0 and the predecessor of the maximal round appearing in C, *)
(* the subset Cr of the messages in C that have round r is a strict majority of    *)
(* the coffer of each message in in C that has round r.                            *)
(***********************************************************************************)
StronglyConsistentChain(C) ==
    /\  C # {}
    /\  \/  MaxRound(C) = 0
        \/  \A r \in 1..MaxRound(C) :
            LET Tip == { m \in C : m.round = r }
                Pred == { m \in C : m.round = r-1 }
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

(**********************************************************************************)
(* The sets of messages with rounds at most r and containing at least one message *)
(* from each round between 0 and r:                                               *)
(**********************************************************************************)
Chains(M,r) == {C \in SUBSET M :
    /\  \A m \in C : m.round <= r
    /\  \A r2 \in 0..r : \E m \in C : m.round = r2}

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
(* which they share less than a strict majority of their messages.               *)
(*********************************************************************************)
DisjointChains(C1,C2) ==
    LET rmax == MaxRound(C1 \cup C2)
    IN  \E r \in 0..(rmax-1) :
        LET I == {m \in C1 : m.round = r} \cap {m \in C2 : m.round = r}
        IN  \/  2*Cardinality(I) < Cardinality(C1)
            \/  2*Cardinality(I) < Cardinality(C2)

StronglyDisjointChains(C1,C2) ==
    LET rmax == MaxRound(C1 \cup C2)
    IN  \E r \in 0..(rmax-1) :
        {m \in C1 : m.round = r} \cap {m \in C2 : m.round = r} = {}

(*******************)
(* Acceptance rule *)
(*******************)
AcceptedMessages(M,r) == {m \in M :
    /\  m.round = r-1
    /\  LET CCs == MaximalStronglyConsistentChains(M,r-1) IN
        /\  \E C \in CCs : m \in C
        /\  \A C1,C2 \in CCs :
                /\  m \in C1
                /\  m \notin C2
                /\  StronglyDisjointChains(C1,C2)
                => Cardinality(C2) <= Cardinality(C1)}

(****************************)
(* Youer's acceptance rule. *)
(****************************)

StronglyConsistentSuccessors(S, M) == {m \in M :
    /\  {m2.id : m2 \in S} \subseteq m.coffer
    /\  2*Cardinality(S) > Cardinality(m.coffer)}

ConsistentSuccessors(S, M) == {m \in M : \E Maj \in SUBSET S :
    /\  {m2.id : m2 \in Maj} \subseteq m.coffer
    /\  2*Cardinality(Maj) > Cardinality(m.coffer)}
    
RECURSIVE ConsistentSetOfRec(_,_)
ConsistentSetOfRec(S, M) ==
    IF S = {} THEN {}
    ELSE LET T == ConsistentSuccessors(S, M) IN \* TODO: Why not strongly?
        S \cup ConsistentSetOfRec(T, M)

ConsistentSetOf(S, M) ==
    LET T == StronglyConsistentSuccessors(S, M)
    IN S \cup ConsistentSetOfRec(T, M)

MaxRootOf(M, m) ==
    LET MM == {m2 \in M : m2.round = MinRound(M)}
        CSs == [S \in SUBSET MM |-> IF m \in ConsistentSetOf(S, M) THEN ConsistentSetOf(S, M) ELSE {}]
    IN CHOOSE S \in DOMAIN CSs : \A S2 \in DOMAIN CSs : 
        Cardinality(CSs[S2]) <= Cardinality(CSs[S])

Valid(M, m) == LET MM == {m2 \in M : m2.round = MinRound(M)} IN
    \A S \in (SUBSET MM) \ {{}}:
        S \cap MaxRootOf(M,m) = {} =>
            LET C1 == ConsistentSetOf(MaxRootOf(M,m), M)
                C2 == ConsistentSetOf(S, M)
            IN  m \notin C2 => Cardinality(C2) <= Cardinality(C1)

RECURSIVE AcceptedMessages2Rec(_)
AcceptedMessages2Rec(M) ==
    IF MinRound(M) = MaxRound(M)
    THEN M
    ELSE LET V == {m \in M : Valid(M,m)} IN 
        AcceptedMessages2Rec({m \in V : m.round > MinRound(M)})

AcceptedMessages2(M) == 
    IF M = {}
    THEN {}
    ELSE AcceptedMessages2Rec(M)

\* Another try:

\* This only looks at r and r-1:
ConsistentSets(M, r) ==
    LET M0 == {m \in M : m.round = r-1}
    IN  {S \cup StronglyConsistentSuccessors(S, M) : S \in SUBSET M0}

MaxConsistentSet(M, m) ==
    LET r == m.round
        Cs == {C \in ConsistentSets(M,r) : m \in C}
    IN
        \* Cs can be empty because M might not have m's coffer
        Max(Cs \cup {{}}, LAMBDA C1,C2 : Cardinality(C1) <= Cardinality(C2))

Valid2(M, m) ==
    LET r == m.round
        C == MaxConsistentSet(M, m)
    IN  \A C2 \in ConsistentSets(M,r) :
            m \notin C2 /\ C \cap C2 = {} => Cardinality(C2) <= Cardinality(C)

RECURSIVE AcceptedMessages3Rec(_)
AcceptedMessages3Rec(M) ==
    IF M = {} \/ MinRound(M) = MaxRound(M)
    THEN M
    ELSE LET V == {m \in M : m.round = MinRound(M)+1 /\ Valid2(M,m)} IN 
        AcceptedMessages3Rec(V \cup {m \in M : m.round > MinRound(M)+1})

AcceptedMessages3(M) == 
    IF M = {}
    THEN {}
    ELSE AcceptedMessages3Rec(M)

(********************************)
(* The DAG is acyclic and closed *)
(********************************)

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
                /\  Closed(M) \* TODO: is this important?
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
                with (predMsgs = AcceptedMessages2(msgs)) {
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
            \* when currentRound < 2; \* TODO temporary hack
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
\* BEGIN TRANSLATION (chksum(pcal) = "f12bbc99" /\ chksum(tla) = "33306de7")
\* Label tick of process clock at line 231 col 9 changed to tick_
VARIABLES messages, tick, phase, donePhase, pendingMessage, messageCount, pc

(* define statement *)
currentRound == tick \div tWB
wellBehavedMessages == {m \in messages : sender(m) \in P \ B}

receivedMsgsSets ==

    LET msgs == {m \in messages : m.round < currentRound} IN
    {M \in SUBSET msgs :

        /\  Closed(M)
        /\  wellBehavedMessages \subseteq  M}


vars == << messages, tick, phase, donePhase, pendingMessage, messageCount, pc
        >>

ProcSet == ({"clock"}) \cup (P \ B) \cup (B)

Init == (* Global variables *)
        /\ messages = {}
        /\ tick = 0
        /\ phase = "start"
        /\ donePhase = [p \in P |-> "end"]
        /\ pendingMessage = [p \in P |-> <<>>]
        /\ messageCount = [p \in P |-> 0]
        /\ pc = [self \in ProcSet |-> CASE self \in {"clock"} -> "tick_"
                                        [] self \in P \ B -> "l1"
                                        [] self \in B -> "lb1"]

tick_(self) == /\ pc[self] = "tick_"
               /\ \A p \in P : donePhase[p] = phase
               /\ IF phase = "start"
                     THEN /\ phase' = "end"
                          /\ tick' = tick
                     ELSE /\ phase' = "start"
                          /\ tick' = tick+1
               /\ pc' = [pc EXCEPT ![self] = "tick_"]
               /\ UNCHANGED << messages, donePhase, pendingMessage, 
                               messageCount >>

clock(self) == tick_(self)

l1(self) == /\ pc[self] = "l1"
            /\ phase = "start"
            /\ IF tick % tWB = 0
                  THEN /\ \E msgs \in receivedMsgsSets:
                            LET predMsgs == AcceptedMessages2(msgs) IN
                              /\ pendingMessage' = [pendingMessage EXCEPT ![self] =                     [
                                                                                    id |-> <<self,messageCount[self]+1>>,
                                                                                    round |-> currentRound,
                                                                                    coffer |-> {m.id : m \in predMsgs}]]
                              /\ messageCount' = [messageCount EXCEPT ![self] = messageCount[self]+1]
                  ELSE /\ TRUE
                       /\ UNCHANGED << pendingMessage, messageCount >>
            /\ donePhase' = [donePhase EXCEPT ![self] = "start"]
            /\ pc' = [pc EXCEPT ![self] = "l2"]
            /\ UNCHANGED << messages, tick, phase >>

l2(self) == /\ pc[self] = "l2"
            /\ phase = "end"
            /\ IF tick % tWB = tWB - 1
                  THEN /\ messages' = (messages \cup {(pendingMessage[self])})
                  ELSE /\ TRUE
                       /\ UNCHANGED messages
            /\ donePhase' = [donePhase EXCEPT ![self] = "end"]
            /\ pc' = [pc EXCEPT ![self] = "l1"]
            /\ UNCHANGED << tick, phase, pendingMessage, messageCount >>

proc(self) == l1(self) \/ l2(self)

lb1(self) == /\ pc[self] = "lb1"
             /\ phase = "start"
             /\ IF tick % tAdv = 0
                   THEN /\ LET maxRound == Max({m.round : m \in messages} \cup {0}, <=) IN
                             \E rnd \in {maxRound, maxRound+1}:
                               \E predMsgs \in SUBSET {m \in messages : m.round = rnd-1}:
                                 /\ rnd > 0 => predMsgs # {}
                                 /\ pendingMessage' = [pendingMessage EXCEPT ![self] =                     [
                                                                                       id |-> <<self,messageCount[self]+1>>,
                                                                                       round |-> rnd,
                                                                                       coffer |-> {m.id : m \in predMsgs}]]
                                 /\ messageCount' = [messageCount EXCEPT ![self] = messageCount[self]+1]
                   ELSE /\ TRUE
                        /\ UNCHANGED << pendingMessage, messageCount >>
             /\ donePhase' = [donePhase EXCEPT ![self] = "start"]
             /\ pc' = [pc EXCEPT ![self] = "lb2"]
             /\ UNCHANGED << messages, tick, phase >>

lb2(self) == /\ pc[self] = "lb2"
             /\ phase = "end"
             /\ IF tick % tAdv = tAdv - 1
                   THEN /\ messages' = (messages \cup {(pendingMessage[self])})
                   ELSE /\ TRUE
                        /\ UNCHANGED messages
             /\ donePhase' = [donePhase EXCEPT ![self] = "end"]
             /\ pc' = [pc EXCEPT ![self] = "lb1"]
             /\ UNCHANGED << tick, phase, pendingMessage, messageCount >>

byz(self) == lb1(self) \/ lb2(self)

Next == (\E self \in {"clock"}: clock(self))
           \/ (\E self \in P \ B: proc(self))
           \/ (\E self \in B: byz(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 

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
Inv1 == \A m \in messages \cup ({pendingMessage[p] : p \in P} \ {<<>>}): 
    /\  \A m2 \in messages : m # m2 => m.id # m2.id
    /\  \A id \in m.coffer :
        /\  \E m2 \in messages : m2.id = id
        /\  messageWithID(id).round = m.round-1
    
=================================================
