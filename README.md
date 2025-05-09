
Investigation of Hofstadter's G function, tree, and mirror
==========================================================

A Coq/Rocq development by Pierre Letouzey, started in summer 2015.
It now extends to a whole family of functions generalizing G,
and it also considers related infinite morphic words extending
the Fibonacci word.

Documentation:
--------------

- Pointwise order of generalized Hofstadter functions G, H and beyond.
  Pierre Letouzey, Shuo Li, Wolfgang Steiner. Preprint, 2024.
  https://hal.science/hal-04715451

- Generalized Hofstadter functions G, H and beyond: numeration systems
  and discrepancy. Pierre Letouzey. Preprint, 2025.
  https://hal.science/hal-04948022

- Slides of talks: [OWCW](talks/owcw/talk.pdf?raw=true) (March 11, 2025).
  Older ones: [PPS'24](talks/4/expose.pdf?raw=true) and in French: [PPS'18](talks/1/expose.pdf?raw=true) [Formath'23](talks/2/expose.pdf?raw=true) [FSMP'23](talks/3/expose.pdf?raw=true)

- A general poster presenting this work: [poster/poster.pdf](poster/poster.pdf?raw=true)

- Hofstadter's problem for curious readers. Pierre Letouzey.
  Technical Report, 2015. http://hal.science/hal-01195587


Usage
-----

- Use `make` to compile the Coq files.

This development depends on Coq >= 8.16 and <= 9.0 as well as the external library
Coquelicot >= 3.4.0. I advise to fetch them via opam. For instance:

```
opam pin add coq 8.19.2
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-coquelicot
```

NB: the library QuantumLib is not an external dependency anymore,
instead the needed portion of QuantumLib 1.6 is now incorporated here
in the local subdirectory HalfQuantum/ (with minor patches).

Summary of files:
----------------

1. Library complements
  - [MoreLib/More*.v](MoreLib): additions to the various libraries used.
  - [MoreLib/DeltaList.v](MoreLib/DeltaList.v): lists of natural numbers with constrained differences
  - [MoreLib/Approx.v](MoreLib/Approx.v): lightweight interval arithmetic for bounding reals by Q
  - [MoreLib/FlexArray.v](MoreLib/FlexArray.v): flexible persistent array-like data-structure
2. Old files specialized to function G
  - [Fib.v](Fib.v): Fibonacci sequence and decomposition
  - [FunG.v](FunG.v): Hofstadter's G function and tree
  - [FunG_prog.v](FunG_prog.v): Alternative definition of Hofstadter's G function
  - [FlipG.v](FlipG.v): Hofstadter's flipped G tree
  - [Phi.v](Phi.v): Hofstadter G function and the golden ratio
3. New, generalized versions of G with more nested recursive calls
  - [GenFib.v](GenFib.v): Fibonacci-like sequences `A k` and decomposition
  - [GenG.v](GenG.v): Hofstadter's G-like functions `f k`
  - [Fast.v](Fast.v): More efficient implementation of `A k` and `f k`
  - [GenFlip.v](GenFlip.v): Mirror of the G-like trees
  - [GenAdd.v](GenAdd.v): Study of the quasi-additivity of G-like functions
  - [Shift.v](Shift.v): quasi-reciprocal of the G-like functions
4. Some infinite morphic words related to functions `f k`
  - [Words.v](Words.v): morphic words `kseq k`, first properties, link with `f k`.
  - [WordGrowth.v](WordGrowth.v): compare some letter frequencies, `f k <= f (k+1)`
  - [WordSuffix.v](WordSuffix.v): enumerate and count the `kword` suffixes
  - [WordFactor.v](WordFactor.v): factors of `kseq k` (i.e. finite sub-words)
  - [Special.v](Special.v): unique left special factor for `kseq k`, complexity
5. Hoftadter G-like functions and real numbers
  - [ThePoly.v](ThePoly.v): start studying polynomial `X^k-X^(k-1)-1`
  - [Mu.v](Mu.v): real roots of this polynomial
  - [SecondRoot.v](SecondRoot.v): a second root of this polynomial has modulus>1 for k>=6
  - [RootEquiv.v](RootEquiv.v): the positive root `μ_k` behaves as`1+ln(k)/k` when `k` grows
  - [Freq.v](Freq.v): frequencies of letters in `kseq k`, limit of `(f k n)/n`.
  - [Discrepancy.v](Discrepancy.v): general study of discrepancy `f n - n * τ_n`
  - [F3.v](F3.v): Hofstadter H (i.e. `f 3`) at dist <1 of `n*τ_3`
  - [F4.v](F4.v): `f 4` at dist <2 of `n*τ_4`
  - [F5.v](F5.v): `f 5` at unbounded dist of `n*τ_5`
  - [Equidistrib.v](Equidistrib.v): equidistribution theorem (irrational multiples mod 1)
  - [F3bis.v](F3bis.v): mean discrepancy for Hofstadter H (i.e `f 3`)
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

The documents in the subdirectories poster/ reports/ talks/ are released under the CC-BY 4.0 license,
see http://creativecommons.org/licenses/by/4.0/.

The Coq files of this development are released in the Public Domain,
see the LICENSE file in the current directory, with the exception of
the files of the subdirectory HalfQuantum which have a MIT license,
see HalfQuantum/LICENSE.
