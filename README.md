
Some contributions to the QuantumLib library
============================================

Author: Pierre Letouzey

During my work on some Hofstadter's functions (G and beyond), I use the QuantumLib library since 2023. Here are some contributions in direct relation with QuantumLib that might (or might not) interest other QuantumLib users.

This development is hosted at https://github.com/letouzey/hofstadter_g . Consider either the branch `main` for the full development about Hofstadter functions or the branch `contribution_to_QuantumLib_1.5.1` for the current trimmed-down version with just the contributions to QuantumLib.

Usage
-----

Needs Coq >= 8.16 and < 8.20 and QuantumLib >= 1.5.1. Then a simple `make`
should do.

Summary of files:
----------------

- `MoreComplex.v` : integrate some improvements already contributed to Coquelicot >= 3.3 and in particular a better `ring` and `field` declaration (handling Z constants and power). Some other lemmas not yet in Coquelicot nor QuantumLib.

- `MorePoly.v` : various extra stuff about polynomials, in particular that a polynomial without common roots with its derivative has only simple roots. So thanks to FTA we obtain in this case a list of distinct roots whose length is the polynomial degree.

- `MoreMatrix.v` : various extra stuff about matrices, especially the definition of Vandermonde matrices and the expression of their determinants.

- `Leibniz.v` : Leibniz formula of the determinant of a matrix, summing on all permutations.

- Auxiliary files : `MoreList.v` and `MorePermut.v` contains extra lemmas used in particular in `Leibniz.v`, especially an enumaration of all n-permutations for the Leibniz formula.


License
-------

These Coq files are released in the Public Domain,
see the LICENSE file in the current directory.
