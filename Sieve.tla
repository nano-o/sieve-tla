------------ MODULE Sieve ----------------

(**************************************************************************************)
(* TODO: add online-sieve! Perhaps non-deterministically pick online or bootstrap     *)
(* sieve when possible                                                                *)
(**************************************************************************************)

(**************************************************************************************)
(* `^PlusCal/TLA+^' specification of `^Sieve.^'                                       *)
(*                                                                                    *)
(* We specify the algorithm and its environment at a high level. This means that      *)
(* we abstract over certain details and make some simplifying assumptions. For        *)
(* example, we do not model message weight; instead, we implicitely assume that       *)
(* all mesages have weight 1 and we just count messages. Nevertheless, this           *)
(* specification should clearly convey the main algorithmic ideas behind              *)
(* `^Sieve.^'                                                                         *)
(**************************************************************************************)

EXTENDS FiniteSets, Integers, Utils, TLC

(**************************************************************************************)
(* We start by declaring constant parameters: the sets of processes P, among which    *)
(* B is the set of `^Byzantine^' nodes, and two integer constants tAdv and tWB.       *)
(*                                                                                    *)
(* Time evolves in discrete ticks that are grouped into steps, and a step is an       *)
(* intervale of tWB ticks.                                                            *)
(*                                                                                    *)
(* All processes are always active, and processes nevertheless always use             *)
(* BootstrapSieve (so, this specification does not cover OnlineSieve).                *)
(*                                                                                    *)
(* As we will see, we do not model proofs of work explicitely. Instead, processes     *)
(* just produce messages at a given fixed rate: Well-behaved processes produce 1      *)
(* message per tWB ticks; malicious processes produce 1 message per tAdv              *)
(* ticks. We require that, collectively and in any interval of steps, well-behaved    *)
(* processes produce a number of messages strictly greater than the number of         *)
(* messages produced by malicious processes.                                          *)
(*                                                                                    *)
(* `^Byzantine^' processes always produce well-formed messages, but they are          *)
(* free to populate their message's coffers arbitrarily.                              *)
(**************************************************************************************)

CONSTANTS
    P \* the set of processes
,   B \* the set of `^Byzantine^', malicious processes
,   tAdv \* the time it takes for a malicious process to produce a message
,   tWB \* the time it takes for a well-behaved process to produce a message

ASSUME B \subseteq P \* malicious processes are a subset of all processes
W == P \ B \* the set of well-behaved (also called correct) processes

ASSUME Cardinality(W)*tAdv > Cardinality(B)*tWB
Tick == Nat
Step == Nat
StepOf(tick) == tick \div tWB \* this is an integer

(********************************************************************************)
(* A message identifier consists of a process identifier and a sequence number. *)
(********************************************************************************)
MessageID == P\times Nat
(**************************************************************************************)
(* A message consists of an identifier, a step number, and a coffer of message        *)
(* identifiers. We usually use M for sets of messages, which we sometimes             *)
(* interpret as DAGs.                                                                 *)
(**************************************************************************************)
Message == [id : MessageID, step: Step, coffer : SUBSET MessageID]
Sender(m) == m.id[1]

\* Whether S1 consists of a supermajority of S2:
SuperMajorityOf(S1, S2) ==
    /\  S1 \subseteq S2
    /\  2*Cardinality(S1) > Cardinality(S2)

(**************************************************************************************)
(* First we specify OnlineSieve. OnlineSieve at step s fiters a set of newly          *)
(* received messages M given the set L of non-antique messages computed               *)
(* previously.                                                                        *)
(**************************************************************************************)
OnlineSieve(s, M, L) ==
    IF s <= 1 THEN M
    ELSE LET LIDs == {m.id : m \in L} IN
        {m \in M :
            /\  m.step = s-1
            /\  2*Cardinality(LIDs \cap m.coffer) > Cardinality(LIDs)}

(**************************************************************************************)
(* Next we specify BootstrapSieve                                                     *)
(**************************************************************************************)

ConsistentSuccessor(M, m) ==
    SuperMajorityOf({msg.id : msg \in M}, m.coffer)

RECURSIVE ConsistentDAG(_)
\* Whether the DAG M is consistent DAG
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
(*                                                                                    *)
(* For example, if messages in M span                                                 *)
(* steps 0 to 3 (included), when unfolding the recursion we get:                      *)
(*                                                                                    *)
(*     BootstrapSieve(M) = FilterAntique(FilterAntique(FilterAntique(M,1),2),3)       *)
(*                                                                                    *)
(* The interesting part is the FilterAntique operator.                                *)
(**************************************************************************************)

RECURSIVE BootstrapSieveRec(_, _)
BootstrapSieve(M) ==
    IF \A m \in M : m.step = 0
    THEN M
    ELSE BootstrapSieveRec(M, 1)

(**************************************************************************************)
(* Filter out step-s messages deemed antique, assuming all messages in M have a       *)
(* step number >= s-1 and step-(s-1) messages in M satisfy the Sieve invariant:       *)
(**************************************************************************************)
FilterAntique(M, s) ==
    LET consistentSets ==
            {D \in SUBSET M : ConsistentDAG(D) /\ \E m \in D : m.step = s-1}
    IN  {m \in M : \* messages we keep (i.e. not antique and step >= s)
        \/  m.step > s
        \/  /\  m.step = s
            /\  \E D \in consistentSets : m \in D
            /\  LET CA == PickOne( \* pick a max-cardinality consistent DAG containing m
                        MaxCardinalitySets({D \in consistentSets : m \in D}))
                IN  \A CB \in consistentSets : \* all disjoint consistent DAGs are of lower cardinality
                        CA \cap CB = {} => Cardinality(CB) < Cardinality(CA)}

BootstrapSieveRec(M, s) ==
    \* We filter out step-s antique messages then call BootstrapSieveRec for step s+1
    LET nonAntiqueStepS == FilterAntique(M, s)
    IN  IF \E m \in M : m.step > s
        THEN BootstrapSieveRec(nonAntiqueStepS, s+1)
        ELSE nonAntiqueStepS

(**************************************************************************************)
(* We are now ready to specify Sieve                                                  *)
(**************************************************************************************)
(*--algorithm Sieve {
    variables
        messages = {}, \* messages sent
        tick = 0, \* current tick (this is a synchronous system)
        phase = "start", \* each tick has two phases: "start" and "end"
        \* for each process, which phase of the current tick the processes has completed:
        donePhase = [p \in P |-> "end"],
        pendingMessage = [p \in P |-> <<>>], \* for each process, the message the process is working on
        messageCount = [p \in P |-> 0], \* auxiliary variable used to generate unique message IDs
        L = [p \in P |-> {}]; \* non-antique messages computed in the previous step
    macro sendMessage(m) {
        messages := messages \cup {m}
    }
(**************************************************************************************)
(*     The system clock:                                                              *)
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
(**************************************************************************************)
(* Next we specify the behavior of correct processes:                                 *)
(**************************************************************************************)
    process (proc \in P \ B) \* a well-behaved process
    {
l1:     while (TRUE) {
            await phase = "start";
            if (tick % tWB = 0) {
                \* Start the proof-of-work computation for the next message:
                with (msgs = {m \in messages : m.step < StepOf(tick)})
                \* If L is non-empty, non-deterministically use either BootstrapSieve or OnlineSieve
                \* That way we excercise both without having to explicitely model processes being offline/online
                with (coffer \in
                        IF L[self] = {}
                        THEN {BootstrapSieve(msgs)}
                        ELSE {BootstrapSieve(msgs),OnlineSieve(StepOf(tick), msgs, L[self])}) {
                    pendingMessage[self] := [
                        id |-> <<self,messageCount[self]+1>>, \* new, unique ID
                        step |-> StepOf(tick),
                        coffer |-> {m.id : m \in coffer}];
                    messageCount[self] := messageCount[self]+1;
                    L[self] := coffer
                }
            };
            donePhase[self] := "start";
l2:         await phase = "end";
            if (tick % tWB = tWB - 1)
                \* it's the end of the step, the proof-of-work has been computed
                sendMessage(pendingMessage[self]);
            donePhase[self] := "end";
        }
    }
(**************************************************************************************)
(* Finally, for the purpose of model-checking, we specify the allowed behavior of     *)
(* `^Byzantine^' nodes:                                                               *)
(**************************************************************************************)
    process (byz \in B)
    {
lb1:    while (TRUE) {
            await phase = "start";
            if (tick % tAdv = 0) {
                \* Start the proof-of-work computation for the next message:
                with (maxStep = MaxInteger({m.step : m \in messages} \cup {0}))
                \* we restrict Byzantine nodes a bit to limit combinatorial explosion
                with (stp \in {maxStep, maxStep+1}) 
                with (coffer \in SUBSET {m \in messages : m.step = stp-1}) {
                    when stp > 0 => coffer # {};
                    pendingMessage[self] := [
                        id |-> <<self,messageCount[self]+1>>,
                        step |-> stp,
                        coffer |-> {m.id : m \in coffer}];
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
\* BEGIN TRANSLATION (chksum(pcal) = "78f02d63" /\ chksum(tla) = "8d57a6b4")
\* Label tick of process clock at line 164 col 9 changed to tick_
VARIABLES pc, messages, tick, phase, donePhase, pendingMessage, messageCount, 
          L

vars == << pc, messages, tick, phase, donePhase, pendingMessage, messageCount, 
           L >>

ProcSet == ({"clock"}) \cup (P \ B) \cup (B)

Init == (* Global variables *)
        /\ messages = {}
        /\ tick = 0
        /\ phase = "start"
        /\ donePhase = [p \in P |-> "end"]
        /\ pendingMessage = [p \in P |-> <<>>]
        /\ messageCount = [p \in P |-> 0]
        /\ L = [p \in P |-> {}]
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
                               messageCount, L >>

clock(self) == tick_(self)

l1(self) == /\ pc[self] = "l1"
            /\ phase = "start"
            /\ IF tick % tWB = 0
                  THEN /\ LET msgs == {m \in messages : m.step < StepOf(tick)} IN
                            \E coffer \in IF L[self] = {}
                                          THEN {BootstrapSieve(msgs)}
                                          ELSE {BootstrapSieve(msgs),OnlineSieve(StepOf(tick), msgs, L[self])}:
                              /\ pendingMessage' = [pendingMessage EXCEPT ![self] =                     [
                                                                                    id |-> <<self,messageCount[self]+1>>,
                                                                                    step |-> StepOf(tick),
                                                                                    coffer |-> {m.id : m \in coffer}]]
                              /\ messageCount' = [messageCount EXCEPT ![self] = messageCount[self]+1]
                              /\ L' = [L EXCEPT ![self] = coffer]
                  ELSE /\ TRUE
                       /\ UNCHANGED << pendingMessage, messageCount, L >>
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
            /\ UNCHANGED << tick, phase, pendingMessage, messageCount, L >>

proc(self) == l1(self) \/ l2(self)

lb1(self) == /\ pc[self] = "lb1"
             /\ phase = "start"
             /\ IF tick % tAdv = 0
                   THEN /\ LET maxStep == MaxInteger({m.step : m \in messages} \cup {0}) IN
                             \E stp \in {maxStep, maxStep+1}:
                               \E coffer \in SUBSET {m \in messages : m.step = stp-1}:
                                 /\ stp > 0 => coffer # {}
                                 /\ pendingMessage' = [pendingMessage EXCEPT ![self] =                     [
                                                                                       id |-> <<self,messageCount[self]+1>>,
                                                                                       step |-> stp,
                                                                                       coffer |-> {m.id : m \in coffer}]]
                                 /\ messageCount' = [messageCount EXCEPT ![self] = messageCount[self]+1]
                   ELSE /\ TRUE
                        /\ UNCHANGED << pendingMessage, messageCount >>
             /\ donePhase' = [donePhase EXCEPT ![self] = "start"]
             /\ pc' = [pc EXCEPT ![self] = "lb2"]
             /\ UNCHANGED << messages, tick, phase, L >>

lb2(self) == /\ pc[self] = "lb2"
             /\ phase = "end"
             /\ IF tick % tAdv = tAdv - 1
                   THEN /\ messages' = (messages \cup {(pendingMessage[self])})
                   ELSE /\ TRUE
                        /\ UNCHANGED messages
             /\ donePhase' = [donePhase EXCEPT ![self] = "end"]
             /\ pc' = [pc EXCEPT ![self] = "lb1"]
             /\ UNCHANGED << tick, phase, pendingMessage, messageCount, L >>

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
Safety == \A p \in P \ B :
    LET pending == pendingMessage[p]
        correctMessages == {m \in messages : Sender(m) \in P \ B}
    IN  \/  pending = <<>>
        \/  pending.step = 0
        \/  /\  \A m \in correctMessages :
                    m.step = pending.step-1 => m.id \in pending.coffer
            /\  LET prevCorrect ==
                        {m \in correctMessages : m.step = pending.step-1}
                IN  ConsistentSuccessor(prevCorrect, pending)

============================================================
