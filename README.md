
Investigation of Hofstadter's G function, tree, and mirror
==========================================================

A Coq development by Pierre Letouzey, started in summer 2015.
It now extends to a whole family of functions generalizing G,
and it also considers related infinite morphic words extending
the Fibonacci word.

Documentation:
--------------

- Hofstadter's problem for curious readers. Pierre Letouzey.
  Technical Report, 2015. http://hal.science/hal-01195587

- Pointwise order of generalized Hofstadter functions G, H and beyond.
  Pierre Letouzey, Shuo Li, Wolfgang Steiner. Preprint, 2024.
  https://hal.science/hal-04715451

- Generalized Hofstadter functions G, H and beyond: numeration systems
  and discrepancy. Pierre Letouzey. Preprint, 2025.
  https://hal.science/hal-04948022

- A general poster presenting this work: [poster/poster.pdf](poster/poster.pdf?raw=true)

- Slides of talks: [PPS'24](talks/4/expose.pdf?raw=true).
  Older ones, in French: [PPS'18](talks/1/expose.pdf?raw=true) [Formath'23](talks/2/expose.pdf?raw=true) [FSMP'23](talks/3/expose.pdf?raw=true)


Usage
-----

- Use `make` to compile the Coq files.
- Use `make gallinahtml` to generate the short html documentation.
- Use `cd reports/g && pdflatex report` to generate the pdf of the technical report.

Some recent files depend on Coq >= 8.16 and < 8.20 as well as external libraries
Coquelicot >= 3.4.0 and QuantumLib >= 1.5.1. I advise to fetch them via opam.
For instance:

```
opam pin add coq 8.19.2
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-coquelicot
opam pin add coq-quantumlib 1.5.1
```

Summary of files:
----------------

1. Auxiliary
  - More*.v : additions to the various libraries used.
  - [Approx.v](Approx.v): lightweight interval arithmetic for bounding reals by Q 
  - [DeltaList.v](DeltaList.v): lists of natural numbers with constrained differences
2. Old files specialized to function G
  - [Fib.v](Fib.v): Fibonacci sequence and decomposition
  - [FunG.v](FunG.v): Hofstadter's G function and tree
  - [FunG_prog.v](FunG_prog.v): Alternative definition of Hofstadter's G function
  - [FlipG.v](FlipG.v): Hofstadter's flipped G tree
  - [Phi.v](Phi.v): Hofstadter G function and the golden ratio
3. New, generalized versions of G with more nested recursive calls
  - [GenFib.v](GenFib.v): Fibonacci-like sequences `A q` and decomposition
  - [GenG.v](GenG.v): Hofstadter's G-like functions `f q`
  - [GenFlip.v](GenFlip.v): Mirror of the G-like trees
  - [GenAdd.v](GenAdd.v): Study of the quasi-additivity of G-like functions
  - [Shift.v](Shift.v): quasi-reciprocal of the G-like functions
4. Some infinite morphic words related to functions `f q`
  - [Words.v](Words.v): morphic words `kseq k`, first properties, link with `f q`.
  - [WordGrowth.v](WordGrowth.v): compare some letter frequencies, `f q <= f (q+1)`
  - [WordSuffix.v](WordSuffix.v): enumerate and count the `kword` suffixes
  - [WordFactor.v](WordFactor.v): factors of `kseq k` (i.e. finite sub-words)
  - [Special.v](Special.v): unique left special factor for `kseq q`, complexity
5. Hoftadter G-like functions and real numbers
  - [ThePoly.v](ThePoly.v): start studying polynomial `X^(q+1)-X^q-1`
  - [Mu.v](Mu.v): real roots of this polynomial
  - [SecondRoot.v](SecondRoot.v): a second root of this polynomial has modulus>1 for q>=5
  - [Freq.v](Freq.v): frequencies of letters in `qseq q`, limit of `(f q n)/n`.
  - [LimCase2.v](LimCase2.v): Hofstadter H (i.e. `f 2`) at dist <1 of `n*τ_2`
  - [LimCase3.v](LimCase3.v): `f 3` at dist <2 of `n*τ_3`
  - [LimCase4.v](LimCase4.v): `f 4` at unbounded dist of `n*τ_4`
6. Two companion Coq files for two forthcoming articles
  - [Article1.v](Article1.v)
  - [Article2.v](Article2.v)

References:
----------

- Hofstadter's book: Goedel, Escher, Bach, page 137.
- For G : http://oeis.org/A005206
- For flipped-G : http://oeis.org/A123070

License
-------

The documents in all subdirectories (especially reports/ talks/ poster/) are released under the CC-BY 4.0 license,
see http://creativecommons.org/licenses/by/4.0/.

The Coq files of this development are released in the Public Domain,
see the LICENSE file in the current directory.
