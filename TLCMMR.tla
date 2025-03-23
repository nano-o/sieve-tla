----------------- MODULE TLCMMR -----------------

EXTENDS MMR, TLC

CONSTANTS p1, p2, p3, p4, v1, v2
P_MC == {p1,p2,p3,p4}
FailProneSets_MC == {{p1},{p2},{p3},{p4}}
V_MC == {v1,v2}
Sym == Permutations(V_MC) \cup Permutations(P_MC)
MaxSeqLen == 2
BoundedSeq(S) == (UNION {[1..n -> S] : n \in 1..MaxSeqLen}) \cup {<<>>}

Canary1 == round < 4
Canary2 == \A p \in P : Len(vote[p]) < 2
Canary3 == \A p \in P : proposal[p] = None \/ Len(proposal[p]) < 2
Canary4 == \E p \in P : vote[p] = <<>>
Canary5 == \A p \in P : Len(delivered[p]) < 2

Constraint1 ==
    /\ \A p \in P : vote[p] \in BoundedSeq(V_MC)
    /\ round < 7
    
MaxTwoThirdsFun == [p \in P |-> MaxTwoThirds(p)]
\* TODO: error in watch expression with this:
\* TwoThidrsFun == [p \in P |-> {l \in Seq(V) : TwoThirds(p,l)}]
TwoThirdsFun == [p \in P |-> [l \in Seq(V) |->  TwoThirds(p,l)]]
HeardOfFun == [p \in P |-> HeardOf(p)]
MaxOneThirdFun == [p \in P |-> MaxOneThird(p)]

=================================================