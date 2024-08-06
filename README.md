# lambda-delim-cont

A formalization in Agda of the lambda calculus with each of grab/delimit, send/run, and effect handlers.
Contains proofs of the soundness and other properties of the calculus.

The proof is based on the [PLFA](https://plfa.inf.ed.ac.uk/22.08/), specifically the chapter on [intrinsically-typed de Bruijn representation](https://plfa.inf.ed.ac.uk/22.08/DeBruijn/#debruijn-intrinsically-typed-de-bruijn-representation).

Tested with agda 2.6.4 and agda-stdlib 2.0.
