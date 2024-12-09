----------- MODULE TLCSieve ----------------


EXTENDS Integers, FiniteSets, TLC

\* CONSTANTS
\*     p1, p2, p3, p4, p5
\* P == {p1,p2,p3,p4,p5}
\* B == {p4,p5}
\* tAdv == 1
\* tWB == 1

\* CONSTANTS
\*     p1, p2, p3, p4, p5
\* P == {p1,p2,p3,p4,p5}
\* B == {p4,p5}
\* tAdv == 3
\* tWB == 4

CONSTANTS
    p1, p2, p3
P == {p1,p2,p3}
B == {p1}
tAdv == 2
tWB == 3

Sym == Permutations(P \ B)\cup Permutations(B)

INSTANCE Sieve

m1 == [id |-> <<p1, 1>>, step |-> 0, coffer |-> {}]
m2 == [id |-> <<p2, 1>>, step |-> 0, coffer |-> {}]
m3 == [id |-> <<p1, 2>>, step |-> 1, coffer |-> {<<p1,1>>,<<p2,1>>}]
m4 == [id |-> <<p2, 2>>, step |-> 2, coffer |-> {<<p1,2>>}]

ASSUME ConsistentSuccessor({m1,m2}, m3)
ASSUME ConsistentDAG({m1,m2,m3})
ASSUME ConsistentDAG({m1,m2,m3,m4})
ASSUME ConsistentDAG({m3,m4})

ASSUME BootstrapSieve({m1,m2,m3,m4}, 1) = {m4}


=============================================================================