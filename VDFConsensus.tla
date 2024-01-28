------------ MODULE VDFConsensus ----------------

EXTENDS FiniteSets, Integers, TLC

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
\* A message consists of a unique ID, a round number, and a coffer containing the IDs of a set of predecessor messages:
Message == [sender : P, id : MessageID, round : Round, coffer : SUBSET MessageID]

\* We will need the intersection of a set of sets:
RECURSIVE Intersection(_)
Intersection(Ss) ==
    CASE
        Ss = {} -> {}
    []  \E S \in Ss : Ss = {S} -> CHOOSE S \in Ss : Ss = {S}
    []  OTHER ->
            LET S == (CHOOSE S \in Ss : TRUE)
            IN  S \cap Intersection(Ss \ {S})

(********************************************************************************)
(* A set of messages is consistent when the intersection of the coffers of each *)
(* message is a strict majority of the coffer of each message.                  *)
(********************************************************************************)
ConsistentSet(M) ==
    LET I == Intersection({m.coffer : m \in M})
    IN \A m \in M : 2*Cardinality(I) > Cardinality(m.coffer)

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
                    /\ \A m2 \in Pred : m2.id \in m.coffer
                    /\  2*Cardinality(Pred) > Cardinality(m.coffer)
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

(********************************)
(* Now we specify the algorithm *)
(********************************)

(*--algorithm Algo {
    variables
        messages = {};
        tick = 0;
        pendingMessage = [p \in P |-> <<>>];
        doneTick = [p \in P |-> -1];
        messageCount = 0; \* used to generate unique message IDs
    define {
        currentRound(t) == tick \div t
        wellBehavedMessages == {m \in messages : m.sender \in P \ B}
        \* possible sets of messages received by a well-behaved process:
        receivedMsgsSets == LET msgs == {m \in messages : m.round < tick} IN
            {wellBehavedMessages \cup byzMsgs :
                byzMsgs \in SUBSET (msgs \ wellBehavedMessages)}
    }
    macro sendMessage(m) {
        messages := messages \cup {m}
    }
    process (clock \in {"clock"}) {
tick:   while (TRUE) {
            \* wait for all processes to take their step before incrementing the tick
            await \A p \in P : doneTick[p] = tick;
            tick := tick+1;
        }
    }
    process (proc \in P \ B) \* a well-behaved process
    {
l1:     while (TRUE) {
            await tick > doneTick[self];
            if (tick % tWB = 0) {
                \* Start the VDF computation for the next message:
                with (msgs \in receivedMsgsSets)
                with (hCC = HeaviestConsistentChain(msgs))
                with (predMsgs = {m \in hCC : m.round = currentRound(tWB)-1}) {
                    \* TODO: filter messages
                    pendingMessage[self] := [
                        sender |-> self,
                        id |-> messageCount+1,
                        round |-> currentRound(tWB),
                        coffer |-> {m.id : m \in predMsgs}];
                    messageCount := messageCount+1;
                }
            }
            else
            if (tick % tWB = tWB -1) 
                \* it's tWB-1 because we want the message to be received by tick tWB
                sendMessage(pendingMessage[self]);
            else skip; \* busy computing the VDF
            doneTick[self] := tick;
        }
    }
    process (byz \in B) \* a malicious process
    {
lb1:    while (TRUE) {
            await tick > doneTick[self];
            await \A p \in P \ B : doneTick[p] = tick; \* otherwise well-behaved processes may receive Byzantine messages from this tick in this tick
            if (tick % tAdv = 0) {
                \* Start the VDF computation for the next message:
                with (msgs \in receivedMsgsSets)
                with (rnd \in 0..currentRound(tAdv)) \* can forge messages from any previous round
                with (predMsgs = {m \in msgs : m.round = rnd-1}) {
                    pendingMessage[self] := [
                        sender |-> self,
                        id |-> messageCount+1,
                        round |-> rnd,
                        coffer |-> {m.id : m \in predMsgs}];
                    messageCount := messageCount+1;
                }
            }
            else
            if (tick % tAdv = tAdv -1)
                sendMessage(pendingMessage[self]);
            else skip; \* busy computing the VDF
            doneTick[self] := tick;
        };
    }
}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "6359dab8" /\ chksum(tla) = "a23f447a")
\* Label tick of process clock at line 111 col 9 changed to tick_
VARIABLES messages, tick, pendingMessage, doneTick, messageCount

(* define statement *)
currentRound(t) == tick \div t
wellBehavedMessages == {m \in messages : m.sender \in P \ B}

receivedMsgsSets == LET msgs == {m \in messages : m.round < tick} IN
    {wellBehavedMessages \cup byzMsgs :
        byzMsgs \in SUBSET (msgs \ wellBehavedMessages)}


vars == << messages, tick, pendingMessage, doneTick, messageCount >>

ProcSet == ({"clock"}) \cup (P \ B) \cup (B)

Init == (* Global variables *)
        /\ messages = {}
        /\ tick = 0
        /\ pendingMessage = [p \in P |-> <<>>]
        /\ doneTick = [p \in P |-> -1]
        /\ messageCount = 0

clock(self) == /\ \A p \in P : doneTick[p] = tick
               /\ tick' = tick+1
               /\ UNCHANGED << messages, pendingMessage, doneTick, 
                               messageCount >>

proc(self) == /\ tick > doneTick[self]
              /\ IF tick % tWB = 0
                    THEN /\ \E msgs \in receivedMsgsSets:
                              LET hCC == HeaviestConsistentChain(msgs) IN
                                LET predMsgs == {m \in hCC : m.round = currentRound(tWB)-1} IN
                                  /\ pendingMessage' = [pendingMessage EXCEPT ![self] =                     [
                                                                                        sender |-> self,
                                                                                        id |-> messageCount+1,
                                                                                        round |-> currentRound(tWB),
                                                                                        coffer |-> {m.id : m \in predMsgs}]]
                                  /\ messageCount' = messageCount+1
                         /\ UNCHANGED messages
                    ELSE /\ IF tick % tWB = tWB -1
                               THEN /\ messages' = (messages \cup {(pendingMessage[self])})
                               ELSE /\ TRUE
                                    /\ UNCHANGED messages
                         /\ UNCHANGED << pendingMessage, messageCount >>
              /\ doneTick' = [doneTick EXCEPT ![self] = tick]
              /\ tick' = tick

byz(self) == /\ tick > doneTick[self]
             /\ \A p \in P \ B : doneTick[p] = tick
             /\ IF tick % tAdv = 0
                   THEN /\ \E msgs \in receivedMsgsSets:
                             \E rnd \in 0..currentRound(tAdv):
                               LET predMsgs == {m \in msgs : m.round = rnd-1} IN
                                 /\ pendingMessage' = [pendingMessage EXCEPT ![self] =                     [
                                                                                       sender |-> self,
                                                                                       id |-> messageCount+1,
                                                                                       round |-> rnd,
                                                                                       coffer |-> {m.id : m \in predMsgs}]]
                                 /\ messageCount' = messageCount+1
                        /\ UNCHANGED messages
                   ELSE /\ IF tick % tAdv = tAdv -1
                              THEN /\ messages' = (messages \cup {(pendingMessage[self])})
                              ELSE /\ TRUE
                                   /\ UNCHANGED messages
                        /\ UNCHANGED << pendingMessage, messageCount >>
             /\ doneTick' = [doneTick EXCEPT ![self] = tick]
             /\ tick' = tick

Next == (\E self \in {"clock"}: clock(self))
           \/ (\E self \in P \ B: proc(self))
           \/ (\E self \in B: byz(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 

TypeOK == 
    /\  messages \in SUBSET Message
    /\  pendingMessage \in [P -> Message \cup {<<>>}]
    /\  tick \in Tick
    /\  doneTick \in [P -> Tick \cup {-1}]

messageWithID(id) == CHOOSE m \in messages : m.id = id

(**********************************************************************************)
(* The main property we want to establish is that, each round, for each message m *)
(* of a well-behaved process, the messages of well-behaved processes from the     *)
(* previous round are all in m's coffer and consist of a strict majority of m's   *)
(* coffer.                                                                        *)
(**********************************************************************************)
Safety == \A m \in messages : m.round > 0 /\ m.sender \notin B =>
    /\  \A m2 \in wellBehavedMessages : m2.round = m.round-1 => m2.id \in m.coffer
    /\  LET M == {m2 \in wellBehavedMessages : m2.round = m.round-1}
        IN  2*Cardinality(M) > Cardinality(m.coffer)

\* A basic well-formedness property:    
Inv1 == \A m \in messages : \A id \in m.coffer :
    /\  \E m2 \in messages : m2.id = id
    /\  messageWithID(id).round = m.round-1
    
=================================================
