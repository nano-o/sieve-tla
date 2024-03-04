------------ MODULE VDFConsensusSimulation ----------------

EXTENDS FiniteSets, Integers, Utils, UndirectedGraphs, TLC

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

Consistent(m1,m2) ==
    LET I == m1.coffer \cap m2.coffer IN
        /\  2*Cardinality(I) > Cardinality(m1.coffer)
        /\  2*Cardinality(I) > Cardinality(m2.coffer)

ConsistentSet(M) ==
    LET I == Intersection({m.coffer : m \in M}) IN
        \A m \in M : 2*Cardinality(I) > Cardinality(m.coffer)

\* The set of messages M does not have dangling edges:
Closed(M) == \A m \in M : \A i \in m.coffer : \E m2 \in M : m2.id = i

messageWithID(id, M) == CHOOSE m \in M : m.id = id

RECURSIVE Reachable(_,_)
Reachable(m,M) ==
    {m} \cup (UNION {Reachable(messageWithID(m2,M), M) : m2 \in m.coffer})

ReachableSet(S,M) == UNION {Reachable(m,M) : m \in S}

Accepted1(M, r) == 
    IF r = 1 THEN M
    ELSE {m \in M : \A m2 \in M :
        (\neg Consistent(m,m2)) => Cardinality(Reachable(m, M)) >= Cardinality(Reachable(m2, M))}

Accepted2(M, r) == 
    IF r = 1 THEN M
    ELSE
        LET Mr == {m \in M : m.round = r-1}
            Size(S) == Cardinality(S \cup (UNION {Reachable(m,M) : m \in S})) 
            Leq(S1,S2) == Size(S1) <= Size(S2)
            ConsistentSets == {S \in SUBSET Mr : ConsistentSet(S)}
        IN  CHOOSE S \in MaximalElements(ConsistentSets, Leq) : TRUE

Accepted3(M, r) == IF r <= 1 THEN M ELSE
    LET Mr == {m \in M : m.round = r-1}
        Graph == [
            node |-> Mr,
            edge |-> {{e[1],e[2]} : e \in {e \in Mr \times Mr : Consistent(e[1],e[2])}} ]
        C == CHOOSE C \in MaxCardinalitySets({ReachableSet(S,M) : S \in ConnectedComponents(Graph)}) : TRUE
    IN  {m \in C : m.round = r-1}

Accepted4(M, r) == IF r <= 1 THEN M ELSE
    LET Mr == {m \in M : m.round = r-1}
        Graph == [
            node |-> Mr,
            edge |-> {{e[1],e[2]} : e \in {e \in Mr \times Mr : Consistent(e[1],e[2])}} ]
        C == CHOOSE C \in MaxCardinalitySets(ConnectedComponents(Graph)) : TRUE
    IN  {m \in C : m.round = r-1}

Accepted5(M, r) == IF r <= 1 THEN M ELSE
    LET Mr == {m \in M : m.round = r-1}
        Graph == [
            node |-> Mr,
            edge |-> {{e[1],e[2]} : e \in {e \in Mr \times Mr : Consistent(e[1],e[2])}} ]
        MaxCs1 == MaxCardinalitySets(ConnectedComponents(Graph))
        MaxCs2 == MaxCardinalitySets({ReachableSet(S,M) : S \in MaxCs1})
        C == CHOOSE C \in MaxCs2 : TRUE
    IN {m \in C : m.round = r-1}

RECURSIVE ConsistentHistory(_,_)
\* Whether S, a set of round-r messages, has a consistent history
ConsistentHistory(S, M) ==
    \/  \A m \in S : m.round = 0
    \/  LET I == Intersection({m.coffer : m \in S})
        IN  \E I2 \in SUBSET I :
            /\  \A m \in S : 2*Cardinality(I2) > Cardinality(m.coffer)
            /\  LET S2 == {messageWithID(id,M) : id \in I2}
                IN
                    ConsistentHistory(S2, M)

Messages(I, M) == {messageWithID(id, M) : id \in I}
IDs(M) == {m.id : m \in M}

RECURSIVE ConsistentHistories(_,_)
\* The set of all consistent histories of S
ConsistentHistories(S, M) == IF S = {} THEN {} ELSE
    IF \A m \in S : m.round = 0 THEN {S}
    ELSE
        LET I == Intersection({m.coffer : m \in S})
            Ps == {Messages(I2, M) : I2 \in \* possible set of predecessors
                {I2 \in SUBSET I : \A m \in S : 2*Cardinality(I2) > Cardinality(m.coffer)}}
        IN  UNION {{S \cup H : H \in ConsistentHistories(Pred, M)} : Pred \in Ps}

MaxConsistentHistory(S, M) ==
    LET CHs == ConsistentHistories(S, M)
    IN  IF CHs = {} THEN {}
        ELSE CHOOSE H \in MaximalSets(ConsistentHistories(S, M)) : TRUE

RECURSIVE HistGTRec(_,_,_)
HistGTRec(H1, H2, r) ==
    LET H1r == {m \in H1 : m.round = r}
        H2r == {m \in H2 : m.round = r}
    IN  IF  /\  H1r \cap H2r = {}
            /\  Cardinality(H1r) > Cardinality(H2r)
        THEN
            TRUE
        ELSE
            /\  \E m \in H1 : r < m.round \* r is not the max round
            /\  HistGTRec(H1, H2, r+1)

\* A history is greater than another if it has more messages in a round r
\* and at least as many messages in all previous rounds:
HistGT(H1, H2) == HistGTRec(H1, H2, 0)

GT(S1,S2,M) ==
    \E H1 \in ConsistentHistories(S1,M) :
        \E H2 \in MaximalSets(ConsistentHistories(S2,M)) : \* NOTE needs to be maximal
            HistGT(H1, H2)

Candidate(S, M, r) ==
    LET Mr == {m \in M : m.round = r-1}
        Srs == {S2 \in SUBSET Mr : ConsistentHistory(S2,M)}
    IN  \A S2 \in Srs :
            (\neg S2 \subseteq S) => \neg GT(S2,S,M)

Accepted6(M, r) == IF r <= 1 THEN M ELSE
    LET Mr == {m \in M : m.round = r-1}
        Srs == {S \in SUBSET Mr : ConsistentHistory(S,M)}
    IN  UNION MaximalSets({S \in Srs : Candidate(S, M, r)})

Accepted(M,r) == Accepted6(M,r) \* This seems to work!

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
            \* ignore messages tagged for future rounds:
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
                with (predMsgs = Accepted(msgs, currentRound)) {
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
                    \* the following makes sure that a message tagged for round n has height n-1:
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
\* BEGIN TRANSLATION (chksum(pcal) = "806ed55f" /\ chksum(tla) = "8d31d47f")
\* Label tick of process clock at line 176 col 9 changed to tick_
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
                            LET predMsgs == Accepted(msgs, currentRound) IN
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

\* Basic well-formedness properties:    
Inv1 == \A m \in messages \cup ({pendingMessage[p] : p \in P} \ {<<>>}): 
    /\  \A m2 \in messages : m # m2 => m.id # m2.id
    /\  \A id \in m.coffer :
        /\  \E m2 \in messages : m2.id = id
        /\  messageWithID(id, messages).round = m.round-1
    
=================================================
