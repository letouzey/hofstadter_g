
## Existence des limites fk(n)/n

Passage par les mots infinis engendrés par substitution `k->[k;0] | n->[n+1]` et mot initial `[k]`.

Alors `fk(n)/n` est 1 moins la fréquence de la lettre 0 dans ce mot (les 0 sont les "plats",
les autres "lettres" sont les +1).

Puis cf article : On the Frequency of Letters in Morphic Sequences", Kalle Saari.

Lemme clé :

Lemma 4. Let G ≥ 1 be an integer. We deﬁne Mj = max(a∈Σ)|μ^j(a)| . The
following holds for any letter a ∈ Σ and integer n ≥ 1: If w is a preﬁx of μ^n(a),
then w has a factorization of the form  w = μ^n1(u1) μ^n2(u2) · · · μ^nr(ur) z,
where r ≥ 0, n > n1 > n2 > · · · > nr ≥ G, ui ∈ Σ∗ and |ui | ≤ M1 for
i = 1, . . . , r, and z ∈ Σ∗ , |z| ≤ MG .

Puis Théorème 2 assure ici que toutes les lettres ont bien une fréquence.
(la preuve peut grandement se simplifier dans le cas présent).

En gros, soit ε. Prendre G tel que rapport des Fibo soit proches de
racine ϕ à ε près. Décomposition précedente, puis
|w|_0/|w| vaut environ ϕ+ε + MG/|w| qui tend vers ϕ+ε quand |w|->∞.
Puis on diminue ε.


## Quasi-additivité

#### Fekete's Subadditive Lemma:

For every subadditive sequence `(a_n)` the limit `lim_{n →_∞} (a_n/n)` exists and is equal to the infimum `inf(a_n/n)` (The limit may be `−∞`).

Ici a priori on a (même si ça reste à prouver)

`fk(n+m) <= fk(n) + fk(m) + C`

donc en considérant `f'(n) = fk(n)+C`

`f'(n+m) = fk(n+m)+C <= fk(n)+fk(m)+C+C = f'(n)+f'(m)`

donc `f'(n)/n` a une limite quand `n->\infty`
donc `fk(n)/n = f'(n)/n - C/n` aussi
et ça ne peut être que la racine du polynôme etc etc

Si on a `fk(n)+fk(m)-C <= fk(n+m) <= fk(n)+fk(m)+C`, alors on peut même montrer `n*lim-C <= fk(n) <= n*lim+C`

#### Reference:

https://en.wikipedia.org/wiki/Subadditivity

https://math.stackexchange.com/questions/57455/existence-of-a-limit-associated-to-an-almost-subadditive-sequence/57493#57493

Funny: alternative definition of reals by quasi-additive functions:
https://people.math.ethz.ch/~salamon/PREPRINTS/acampo-real.pdf

https://theorylunch.wordpress.com/2018/03/01/a-crash-course-in-subadditivity-part-1

Rauzy fractals:
https://im.icerm.brown.edu/portfolio/visualizing-rauzy-fractals-via-finite-directed-graphs/
https://tilings.math.uni-bielefeld.de/substitution/a-ab--b-c--c-a/

