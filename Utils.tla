------------ MODULE Utils -----------------

EXTENDS Integers, FiniteSets

\* The intersection of a set of sets:
Intersection(Ss) == {x \in UNION Ss : \A S \in Ss : x \in S}

Max(X, Leq(_,_)) ==
    CHOOSE m \in X : \A x \in X : Leq(x,m)

Maximal(X, Leq(_,_)) ==
    CHOOSE m \in X : \A x \in X : \neg (Leq(m,x) /\ \neg Leq(x,m))

MaximalElements(X, Leq(_,_)) ==
    {m \in X : \A x \in X : \neg (Leq(m,x) /\ \neg Leq(x,m))}

MaxInteger(I) == Max(I, <=)
MaxCardinalitySets(S) == MaximalElements(S, LAMBDA C1,C2 : Cardinality(C1) <= Cardinality(C2))

===========================================