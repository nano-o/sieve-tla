This repository contains formal specifications of Sieve and of the MMR algorithm.
The specification are written in PlusCal/TLA+.

For model-checking, you must first transpile the PlusCal algorithm blocks to TLA+.
To do this, run `make trans TLA_SPEC=Sieve.tla` and `make trans TLA_SPEC=Sieve.tla`.

Next, to run the TLC model-checker, run `make run-tlc TLA_SPEC=TLCMMR.tla` or `make run-tlc TLA_SPEC=TLCSieve.tla`.
The specification `TLCSieve.tla` replaces the arbitrary constants of `Sieve.tla` by small finite values, and `TLCSieve.cfg` defines what to check.
`TLCMMR.tla` and `TLCMMR.cfg` play a similar role.

You can also typeset a specification to produce a PDF file, e.g. with `make Sieve.pdf`.
