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

(***********************************************************************************)
(* The message-production rate of well-behaved processes is of 1 message per tWB   *)
(* ticks, and that of malicious processes is of 1 message per tAdv ticks.          *)
(*                                                                                 *)
(* We require that, collectively and in any interval of at least tWB, well-behaved *)
(* processes produce a number of messages strictly greater than the number of      *)
(* messages produced by malicious processes.                                       *)
(***********************************************************************************)
ASSUME Cardinality(W)*tAdv > Cardinality(B)*tWB

SuperMajority(S1, S2) ==
    /\  S1 \subseteq S2
    /\  2*Cardinality(S1) > Cardinality(S2)

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
IsGraph(M) == \A m \in M : \A i \in m.coffer : \E m2 \in M : m2.id = i
PickFrom(S) == CHOOSE x \in S : TRUE \* pick an arbitrary element from a set

(**************************************************************************)
(* If M is a message DAG, Height(m, M) is the height of message m in DAG. *)
(**************************************************************************)
RECURSIVE Height(_,_)
Height(m, M) == IF m.coffer = {} THEN 0 ELSE
    LET cofferMsgs == {m2 \in M : m2.id \in m.coffer} IN
        1 + MaxInteger({Height(m2, M) : m2 \in cofferMsgs})

RECURSIVE RecursiveMatryoska(_, _)
RecursiveMatryoska(m, M) ==
    IF m.coffer = {} /\ m.step = 0
    THEN TRUE
    ELSE LET cofferMsgs == {m2 \in M : m2.id \in m.coffer} IN
        \A m2 \in cofferMsgs :
        /\  m2.step = m.step-1
        /\  RecursiveMatryoska(m2, M)

(****************************)
(* Now on to BootstrapSieve *)
(****************************)

ConsistentSuccessor(M, m) ==
    SuperMajority(Ids(M), m.coffer)

RECURSIVE ConsistentDAG(_)
ConsistentDAG(M) == IF M = {} THEN TRUE ELSE
    LET maxStep == MaxInteger({m.step : m \in M})
    IN  IF \A m \in M : m.step = maxStep
        THEN TRUE
        ELSE
            LET tip == FilterStep(M, maxStep)
                prevTip == FilterStep(M, maxStep-1)
            IN  /\  \A m \in tip : ConsistentSuccessor(prevTip, m)
                /\  ConsistentDAG(M \ tip)

RECURSIVE BootstrapSieveRec(_, _)
BootstrapSieve(M) == BootstrapSieveRec(M, 1)
FilterAntique(M, s) == \* assumes all messages in M have a step number >= s-1
    LET consistentDAGs == 
            {D \in SUBSET M : ConsistentDAG(D) /\ \E m \in D : m.step = s-1}
    IN  {m \in M : \* messages we keep (i.e. not antique and step >= s)
        \/  m.step > s
        \/  /\  m.step = s \* could we use m.step >= s instead?
            /\  \E D \in consistentDAGs : m \in D
            /\  LET CA == PickFrom( \* pick a max-cardinality consistent DAG containing m
                        MaxCardinalitySets({D \in consistentDAGs : m \in D}))
                IN  \A CB \in consistentDAGs : \* all disjoint consistent DAGs are of lower cardinality
                        CA \cap CB = {} => Cardinality(CB) < Cardinality(CA)}
BootstrapSieveRec(M, s) == 
    IF M = {}
    THEN M
    ELSE
        LET maxStep == MaxInteger({m.step : m \in M})
        IN  IF s > maxStep
            THEN M
            ELSE BootstrapSieveRec(FilterAntique(M,s), s+1)


(*--algorithm BootstrapSieve {
    variables
        messages = {};
        tick = 0;
        phase = "start"; \* each tick has two phases: "start" and "end"
        donePhase = [p \in P |-> "end"];
        pendingMessage = [p \in P |-> <<>>]; \* message we're computing the VDF on
        messageCount = [p \in P |-> 0]; \* used to generate unique message IDs
    define {
        step == tick \div tWB
        correctMessages == {m \in messages : sender(m) \in P \ B}
        \* possible sets of messages received by a well-behaved process:
        recursiveMatryoskaMsgs ==
            LET msgs == {m \in messages : m.step < step /\ RecursiveMatryoska(m, messages)}
            IN {M \in SUBSET msgs : IsGraph(M) /\ correctMessages \subseteq  M}
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
                with (msgs \in recursiveMatryoskaMsgs)
                with (predMsgs = BootstrapSieve(msgs)) {
                    pendingMessage[self] := [
                        id |-> <<self,messageCount[self]+1>>,
                        step |-> step,
                        coffer |-> Ids(predMsgs)];
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
                with (stp \in {maxStep, maxStep+1}) \* TODO why?
                with (predMsgs \in SUBSET {m \in messages : m.step = stp-1}) {
                    when stp > 0 => predMsgs # {};
                    pendingMessage[self] := [
                        id |-> <<self,messageCount[self]+1>>,
                        step |-> stp,
                        coffer |-> Ids(predMsgs)];
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
\* BEGIN TRANSLATION (chksum(pcal) = "4aaf2129" /\ chksum(tla) = "a5a57505")
\* Label tick of process clock at line 124 col 9 changed to tick_
VARIABLES pc, messages, tick, phase, donePhase, pendingMessage, messageCount

(* define statement *)
step == tick \div tWB
correctMessages == {m \in messages : sender(m) \in P \ B}

recursiveMatryoskaMsgs ==
    LET msgs == {m \in messages : m.step < step /\ RecursiveMatryoska(m, messages)}
    IN {M \in SUBSET msgs : IsGraph(M) /\ correctMessages \subseteq  M}


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
                  THEN /\ \E msgs \in recursiveMatryoskaMsgs:
                            LET predMsgs == BootstrapSieve(msgs) IN
                              /\ pendingMessage' = [pendingMessage EXCEPT ![self] =                     [
                                                                                    id |-> <<self,messageCount[self]+1>>,
                                                                                    step |-> step,
                                                                                    coffer |-> Ids(predMsgs)]]
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
                                                                                       coffer |-> Ids(predMsgs)]]
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
