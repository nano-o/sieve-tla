This repository contains formal specifications of Sieve and of the MMR algorithm.
The specification are written in PlusCal/TLA+.

For model-checking, the PlusCal algorithm blocks must first be transpiled to TLA+.
Run e.g. `make trans TLA_SPEC=Sieve.tla` to do this.
Next, to run the TLC model-checker, run e.g. `make run-tlc TLA_SPEC=TLCSieve.tla`.
The specification `TLCSieve.tla` replaces the arbitrary constants of `Sieve.tla` by small finite values.
`TLCSieve.cfg` defines what to check.
`TLCMMR.tla` and `TLCMMR.cfg` play a similar role.

You can also typeset a specification to produce a PDF file, e.g. with `make Sieve.pdf`.
