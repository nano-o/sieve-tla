----------- MODULE MMR ------------------

EXTENDS Integers, FiniteSets, Sequences, TLC

Prefix(l1, l2) ==
    /\  Len(l1) <= Len(l2)
    /\  Len(l2) > 0 => l1 = SubSeq(l2, 1, Len(l1))

Compatible(l1, l2) == Prefix(l1, l2) \/ Prefix(l2, l1)

Maximal(ls) == {l \in ls : \A l2 \in ls : Compatible(l, l2) => Prefix(l2, l)}

CONSTANTS
    P \* the set of processes
,   FailProneSets
,   V \* the set of values appearing in logs
,   None \* default, null value

(*--algorithm MMR {
    variables
        round = 1;
        delivered = [p \in P |-> <<>>];
        vote = [p \in P |-> <<>>];
        proposal = [p \in P |-> None];
        received_votes = [p \in P |-> [q \in P |-> None]];
        done = [p \in P |-> 0];
        byz \in FailProneSets;
    define {
        Agreement == \A p,q \in P : Compatible(delivered[p], delivered[q])
        HeardOf(p) == {q \in P : received_votes[p][q] # None}
        TwoThirds(p,l) == \E Q \in SUBSET HeardOf(p) :
            /\ 3*Cardinality(Q) > 2*Cardinality(HeardOf(p))
            /\ \A q \in Q : Prefix(l, received_votes[p][q])
        MaxTwoThirds(p) ==
            Maximal({l \in Seq(V) : TwoThirds(p, l)})
        OneThird(p,l)  == \E Q \in SUBSET HeardOf(p) :
            /\ 3*Cardinality(Q) > Cardinality(HeardOf(p))
            /\ \A q \in Q : Prefix(l, received_votes[p][q])
        MaxOneThird(p) ==
            Maximal({l \in Seq(V) : OneThird(p, l)})
    }
    process (proc \in P) {
        \* round 1
        \* we start with a leader-proposal round where everybody implicitely votes for the empty log <<>>
l0:     when self \notin byz;
        with (b \in V)
            proposal[self] := <<b>>;
        done[self] := 1; \* round 1 done
l1:     while (TRUE) {
            \* round 2k
            await round = (done[self]+1) % 2;
            with (l \in MaxTwoThirds(self)) \* deliver the longest log supported by more than 2/3 of the processes
                delivered[self] := l;
            assert Cardinality(MaxOneThird(self)) = 1;
            with (leader \in HeardOf(self)) \* pick a leader
            with (l \in MaxOneThird(self)) \* if the leader's proposal extends the longest log supported by more than 1/3 of the processes, vote for it
            if (Prefix(l, proposal[leader]))
                vote[self] := proposal[leader]
            else \* else vote for the longest log supported by more than 1/3 of the processes
                vote[self] := l;
            done[self] := round;
            \* round 2k+1:
l2:         await round = done[self]+1;
            with (l \in MaxTwoThirds(self))  \* vote for the longest log supported by more than 2/3 of the processes
                vote[self] := l;
            with (l \in MaxOneThird(self)) \* propose to extend a longest log supported by more than 1/3 of the processes (there might be two; just pick one randomly)
            with (b \in V)
                proposal[self] := l \o <<b>>;
            done[self] := round;
        }
    }
    process (scheduler \in {"scheduler"}) {
        \* TODO: a scheduler that simulates dynamic participation
tick:   while (TRUE) {
            await \A p \in P \ byz : done[p] = round;
            with (byzVotes \in [P \ byz -> [byz -> Seq(V) \cup {None}]])
            received_votes := [p \in P \ byz |-> [q \in P |->
                IF q \notin byz
                THEN vote[q]
                ELSE byzVotes[p][q]]];
            with (byzProposal \in [byz -> Seq(V)])
            proposal := [p \in P |-> IF p \notin byz THEN proposal[p] ELSE byzProposal[p]];
            round := (round+1) % 2;
        }
    }
}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "b215e9f8" /\ chksum(tla) = "80547391")
VARIABLES pc, round, delivered, vote, proposal, received_votes, done, byz

(* define statement *)
Agreement == \A p,q \in P : Compatible(delivered[p], delivered[q])
HeardOf(p) == {q \in P : received_votes[p][q] # None}
TwoThirds(p,l) == \E Q \in SUBSET HeardOf(p) :
    /\ 3*Cardinality(Q) > 2*Cardinality(HeardOf(p))
    /\ \A q \in Q : Prefix(l, received_votes[p][q])
MaxTwoThirds(p) ==
    Maximal({l \in Seq(V) : TwoThirds(p, l)})
OneThird(p,l)  == \E Q \in SUBSET HeardOf(p) :
    /\ 3*Cardinality(Q) > Cardinality(HeardOf(p))
    /\ \A q \in Q : Prefix(l, received_votes[p][q])
MaxOneThird(p) ==
    Maximal({l \in Seq(V) : OneThird(p, l)})


vars == << pc, round, delivered, vote, proposal, received_votes, done, byz >>

ProcSet == (P) \cup ({"scheduler"})

Init == (* Global variables *)
        /\ round = 1
        /\ delivered = [p \in P |-> <<>>]
        /\ vote = [p \in P |-> <<>>]
        /\ proposal = [p \in P |-> None]
        /\ received_votes = [p \in P |-> [q \in P |-> None]]
        /\ done = [p \in P |-> 0]
        /\ byz \in FailProneSets
        /\ pc = [self \in ProcSet |-> CASE self \in P -> "l0"
                                        [] self \in {"scheduler"} -> "tick"]

l0(self) == /\ pc[self] = "l0"
            /\ self \notin byz
            /\ \E b \in V:
                 proposal' = [proposal EXCEPT ![self] = <<b>>]
            /\ done' = [done EXCEPT ![self] = 1]
            /\ pc' = [pc EXCEPT ![self] = "l1"]
            /\ UNCHANGED << round, delivered, vote, received_votes, byz >>

l1(self) == /\ pc[self] = "l1"
            /\ round = (done[self]+1) % 2
            /\ \E l \in MaxTwoThirds(self):
                 delivered' = [delivered EXCEPT ![self] = l]
            /\ Assert(Cardinality(MaxOneThird(self)) = 1, 
                      "Failure of assertion at line 54, column 13.")
            /\ \E leader \in HeardOf(self):
                 \E l \in MaxOneThird(self):
                   IF Prefix(l, proposal[leader])
                      THEN /\ vote' = [vote EXCEPT ![self] = proposal[leader]]
                      ELSE /\ vote' = [vote EXCEPT ![self] = l]
            /\ done' = [done EXCEPT ![self] = round]
            /\ pc' = [pc EXCEPT ![self] = "l2"]
            /\ UNCHANGED << round, proposal, received_votes, byz >>

l2(self) == /\ pc[self] = "l2"
            /\ round = done[self]+1
            /\ \E l \in MaxTwoThirds(self):
                 vote' = [vote EXCEPT ![self] = l]
            /\ \E l \in MaxOneThird(self):
                 \E b \in V:
                   proposal' = [proposal EXCEPT ![self] = l \o <<b>>]
            /\ done' = [done EXCEPT ![self] = round]
            /\ pc' = [pc EXCEPT ![self] = "l1"]
            /\ UNCHANGED << round, delivered, received_votes, byz >>

proc(self) == l0(self) \/ l1(self) \/ l2(self)

tick(self) == /\ pc[self] = "tick"
              /\ \A p \in P \ byz : done[p] = round
              /\ \E byzVotes \in [P \ byz -> [byz -> Seq(V) \cup {None}]]:
                   received_votes' =               [p \in P \ byz |-> [q \in P |->
                                     IF q \notin byz
                                     THEN vote[q]
                                     ELSE byzVotes[p][q]]]
              /\ \E byzProposal \in [byz -> Seq(V)]:
                   proposal' = [p \in P |-> IF p \notin byz THEN proposal[p] ELSE byzProposal[p]]
              /\ round' = (round+1) % 2
              /\ pc' = [pc EXCEPT ![self] = "tick"]
              /\ UNCHANGED << delivered, vote, done, byz >>

scheduler(self) == tick(self)

Next == (\E self \in P: proc(self))
           \/ (\E self \in {"scheduler"}: scheduler(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 
=========================================
