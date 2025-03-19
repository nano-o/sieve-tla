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
Step == Nat \* a step consists of a fixed number of ticks

(***********************************************************************************)
(* The message-production rate of well-behaved processes is of 1 message per tWB   *)
(* ticks, and that of malicious processes is of 1 message per tAdv ticks.          *)
(*                                                                                 *)
(* We require that, collectively and in any interval of at least tWB, well-behaved *)
(* processes produce a number of messages strictly greater than the number of      *)
(* messages produced by malicious processes.                                       *)
(***********************************************************************************)
ASSUME Cardinality(W)*tAdv > Cardinality(B)*tWB

(********************************************************************************)
(* A message identifier consists of a process identifier and a sequence number. *)
(********************************************************************************)
MessageID == P\times Nat

(**************************************************************************************)
(* A message consists of an identifier, a step number, and a coffer of message        *)
(* identifiers.                                                                       *)
(*                                                                                    *)
(* We usually use M for sets of messages, which we sometimes interpret as DAGs.       *)
(**************************************************************************************)

Message == [id : MessageID, step: Step, coffer : SUBSET MessageID]
Sender(m) == m.id[1]

\* Whether a set of messages M forms a graph (i.e. there are no dangling edges):
IsGraph(M) == \A m \in M : \A i \in m.coffer : \E m2 \in M : m2.id = i

(**************************************************************************************)
(* If M is a message DAG, Height(m, M) is the height of message m in the DAG.         *)
(**************************************************************************************)
RECURSIVE Height(_,_)
Height(m, M) == IF m.coffer = {} THEN 0 ELSE
    LET cofferMsgs == {m2 \in M : m2.id \in m.coffer} IN
        1 + MaxInteger({Height(m2, M) : m2 \in cofferMsgs})

\* TODO not used anymore
RECURSIVE RecursiveMatryoska(_, _)
RecursiveMatryoska(m, M) ==
    IF m.coffer = {} /\ m.step = 0
    THEN TRUE
    ELSE LET cofferMsgs == {m2 \in M : m2.id \in m.coffer} IN
        \A m2 \in cofferMsgs :
        /\  m2.step = m.step-1
        /\  RecursiveMatryoska(m2, M)

(**************************************************************************************)
(* Now on to BootstrapSieve                                                           *)
(**************************************************************************************)

SuperMajorityOf(S1, S2) ==
    /\  S1 \subseteq S2
    /\  2*Cardinality(S1) > Cardinality(S2)

ConsistentSuccessor(M, m) ==
    SuperMajorityOf({msg.id : msg \in M}, m.coffer)

RECURSIVE ConsistentDAG(_)
\* Whether the DAG M is consistent DAG
\* The seed is {m \in M : m.step = MinInteger({msg.step : msg \in M})}
ConsistentDAG(M) == IF M = {} THEN TRUE ELSE
    LET maxStep == MaxInteger({m.step : m \in M})
    IN  IF \A m \in M : m.step = maxStep
        THEN TRUE
        ELSE
            LET tip == {m \in M : m.step = maxStep}
                tipPreds == {m \in M : m.step = maxStep-1}
            IN  /\  \A m \in tip : ConsistentSuccessor(tipPreds, m)
                /\  ConsistentDAG(M \ tip)


(**************************************************************************************)
(* We now define BootstrapSieve recursively.                                          *)
(* For example, if messages in M span steps 0 to 3 (included), we have:               *)
(*                                                                                    *)
(*     BootstrapSieve(M) = FilterAntique(FilterAntique(FilterAntique(M,1),2),3)       *)
(**************************************************************************************)

(**************************************************************************************)
(* RECURSIVE BootstrapSieveRec(_, _)                                                  *)
(* BootstrapSieve(M) == IF M = {} THEN {} ELSE                                        *)
(*     LET maxStep == MaxInteger({m.step : m \in M})                                  *)
(*     IN  BootstrapSieveRec(M, maxStep)                                              *)
(*                                                                                    *)
(* \* Filter step-s messages deemed antique:                                          *)
(* FilterAntique(M, s) == \* assumes all messages in M have a step number >= s-1      *)
(*     LET consistentDAGs ==                                                          *)
(*             {D \in SUBSET M : ConsistentDAG(D) /\ \E m \in D : m.step = s-1}       *)
(*     IN  {m \in M : \* messages we keep (i.e. not antique and step >= s)            *)
(*         \/  m.step > s                                                             *)
(*         \/  /\  m.step = s                                                         *)
(*             /\  \E D \in consistentDAGs : m \in D                                  *)
(*             /\  LET CA == PickOne( \* pick a max-cardinality consistent DAG containing m *)
(*                         MaxCardinalitySets({D \in consistentDAGs : m \in D}))      *)
(*                 IN  \A CB \in consistentDAGs : \* all disjoint consistent DAGs are of lower cardinality *)
(*                         CA \cap CB = {} => Cardinality(CB) < Cardinality(CA)}      *)
(*                                                                                    *)
(* BootstrapSieveRec(M, s) == IF M = {} \/ s = 0 THEN M ELSE                          *)
(*     FilterAntique(BootstrapSieveRec(M, s-1), s)                                    *)
(**************************************************************************************)

RECURSIVE BootstrapSieveRec(_, _)
BootstrapSieve(M) ==
    IF \A m \in M : m.step = 0
    THEN M
    ELSE BootstrapSieveRec(M, 1)

\* Filter out step-s messages deemed antique (assuming all messages in M have a step number >= s-1):
FilterAntique(M, s) ==
    LET consistentDAGs ==
            {D \in SUBSET M : ConsistentDAG(D) /\ \E m \in D : m.step = s-1}
    IN  {m \in M : \* messages we keep (i.e. not antique and step >= s)
        \/  m.step > s
        \/  /\  m.step = s
            /\  \E D \in consistentDAGs : m \in D
            /\  LET CA == PickOne( \* pick a max-cardinality consistent DAG containing m
                        MaxCardinalitySets({D \in consistentDAGs : m \in D}))
                IN  \A CB \in consistentDAGs : \* all disjoint consistent DAGs are of lower cardinality
                        CA \cap CB = {} => Cardinality(CB) < Cardinality(CA)}

BootstrapSieveRec(M, s) ==
    \* We filter out step-s antique messages then call BootstrapSieveRec(_, s+1)
    LET nonAntiqueStepS == FilterAntique(M, s)
    IN  IF \E m \in M : m.step > s
        THEN BootstrapSieveRec(nonAntiqueStepS, s+1)
        ELSE nonAntiqueStepS

(*--algorithm BootstrapSieve {
    variables
        messages = {}; \* messages sent
        tick = 0; \* current tick (this is a synchronous system)
        phase = "start"; \* each tick has two phases: "start" and "end"
        \* for each process, which phase of the current tick the processes has completed:
        donePhase = [p \in P |-> "end"];
        pendingMessage = [p \in P |-> <<>>]; \* for each process, the message the process is working on
        messageCount = [p \in P |-> 0]; \* auxiliary variable used to generate unique message IDs
    define {
        step == tick \div tWB \* the current step
        \* the set of messages sent by correct processes:
        correctMessages == {m \in messages : Sender(m) \in P \ B}
    }
    macro sendMessage(m) {
        messages := messages \cup {m}
    }
(**************************************************************************************)
(*     We use a global scheduler process to move the system clock:                    *)
(**************************************************************************************)
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
                with (msgs = {m \in messages : m.step < step})
                with (predMsgs = BootstrapSieve(msgs)) {
                    pendingMessage[self] := [
                        id |-> <<self,messageCount[self]+1>>,
                        step |-> step,
                        coffer |-> {m.id : m \in predMsgs}];
                    messageCount[self] := messageCount[self]+1
                }
            };
            donePhase[self] := "start";
l2:         await phase = "end";
            if (tick % tWB = tWB - 1)
                \* it's the end of the step, the VDF has been computed
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
                with (maxStep = MaxInteger({m.step : m \in messages} \cup {0}))
                with (stp \in {maxStep, maxStep+1}) \* trying to limit state explosion a bit
                with (predMsgs \in SUBSET {m \in messages : m.step = stp-1}) {
                    when stp > 0 => predMsgs # {};
                    pendingMessage[self] := [
                        id |-> <<self,messageCount[self]+1>>,
                        step |-> stp,
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
\* BEGIN TRANSLATION (chksum(pcal) = "d746a597" /\ chksum(tla) = "3e69a08c")
\* Label tick of process clock at line 165 col 9 changed to tick_
VARIABLES pc, messages, tick, phase, donePhase, pendingMessage, messageCount

(* define statement *)
step == tick \div tWB

correctMessages == {m \in messages : Sender(m) \in P \ B}


vars == << pc, messages, tick, phase, donePhase, pendingMessage, messageCount
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
                  THEN /\ LET msgs == {m \in messages : m.step < step} IN
                            LET predMsgs == BootstrapSieve(msgs) IN
                              /\ pendingMessage' = [pendingMessage EXCEPT ![self] =                     [
                                                                                    id |-> <<self,messageCount[self]+1>>,
                                                                                    step |-> step,
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
                   THEN /\ LET maxStep == MaxInteger({m.step : m \in messages} \cup {0}) IN
                             \E stp \in {maxStep, maxStep+1}:
                               \E predMsgs \in SUBSET {m \in messages : m.step = stp-1}:
                                 /\ stp > 0 => predMsgs # {}
                                 /\ pendingMessage' = [pendingMessage EXCEPT ![self] =                     [
                                                                                       id |-> <<self,messageCount[self]+1>>,
                                                                                       step |-> stp,
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
    /\  m.step > 0
    =>
    /\  \A m2 \in correctMessages : m2.step = m.step-1 => m2.id \in m.coffer
    /\  LET M == {m2 \in correctMessages : m2.step = m.step-1}
        IN  ConsistentSuccessor(M, m)

============================================================
