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
MinimalElements(X, Leq(_,_)) ==
    {m \in X : \A x \in X : \neg (Leq(x,m) /\ \neg Leq(m,x))}

ASSUME MinimalElements({{1},{0,2},{0,2,3},{3}}, \subseteq) = {{0,2},{1},{3}}

MaxInteger(I) == Max(I, <=)
MinInteger(I) == Max(I, >=)
MaxCardinalitySets(S) == MaximalElements(S, LAMBDA C1,C2 : Cardinality(C1) <= Cardinality(C2))
MinCardinalitySets(S) == MinimalElements(S, LAMBDA C1,C2 : Cardinality(C1) <= Cardinality(C2))
MaximalSets(S) == MaximalElements(S, \subseteq)
MinimalSets(S) == MinimalElements(S, \subseteq)


ASSUME MinCardinalitySets({{1},{0,2},{0,2,3},{3}}) = {{1},{3}}

===========================================