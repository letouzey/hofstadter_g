
Investigation of Hofstadter's G function, tree, and mirror
==========================================================

A Coq development by Pierre Letouzey, started in summer 2015.

http://www.pps.univ-paris-diderot.fr/~letouzey/hofstadter_g

The technical report is now on HAL: http://hal.inria.fr/hal-01195587

Usage
-----

To be compiled with Coq 8.12 or newer. With other versions your mileage may
vary. With older Coq, you may try older git branches coq8.4 and coq8.9.

Use "make" to compile the Coq files.
Use "make gallinahtml" to generate the short html documentation.
Use "pdflatex report" to generate the pdf of the technical report.

Some recent files depend on Coq 8.16 and external libraries Coquelicot >= 3.3.0
and QuantumLib. I advise to fetch them via opam :

```
opam install coq
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-coquelicot coq-quantumlib
```

Summary of files:
----------------

- DeltaList: lists of natural numbers with constrained differences
- Fib: Fibonacci sequence and decomposition
- FunG: Hofstadter's G function and tree
- FunG_prog: Alternative definition of Hofstadter's G function
- Phi: Hofstadter G function and the golden ratio
- FlipG: Hofstadter's flipped G tree

TODO: update this summary

References:
----------

- Hofstadter's book: Goedel, Escher, Bach, page 137.
- For G : http://oeis.org/A005206
- For flipped-G : http://oeis.org/A123070

License
-------

The documents in all subdirectories (especially reports/ talk/ talk2/
talk3/ poster/) are released under the CC-BY 4.0 license,
see http://creativecommons.org/licenses/by/4.0/.

The Coq files of this development are released in the Public Domain,
see the LICENSE file in the current directory.
