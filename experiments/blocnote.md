
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

Pour certains k, on a `∃C, ∀nm, fk(n+m) <= fk(n) + fk(m) + C`.
Cf. `FunG.g_add_bound` (C=1), ou bien l'étude de H "à la Rauzy" (C=2).
Attention, ça n'est sans doute pas général, mais sans doute spécifique
à k <= 4.

Pour ces k presque sous-additifs, on considère `f'(n) = fk(n)+C`
Alors `f'(n+m) = fk(n+m)+C <= fk(n)+fk(m)+C+C = f'(n)+f'(m)`

Par le thm de Fekete, `f'(n)/n` a une limite quand `n->\infty`
donc `fk(n)/n = f'(n)/n - C/n` aussi
et ça ne peut être que la racine du polynôme etc etc.
De plus, `lim = inf (f'(n)/n)` donc `lim <= f'(n)/n = (fk(n)+C)/n`
donc `fk(n) >= n*lim-C`.

Si on a quasi-additivité `fk(n)+fk(m)-C <= fk(n+m) <= fk(n)+fk(m)+C`,
alors on a les deux côtés : `n*lim-C <= fk(n) <= n*lim+C`

Réciproquement, s'il existe C tq `∀n,|fk(n)-n*lim|<=C`
alors fk quasi-additive (avec borne 3C).

#### G <= H

On peut profiter des encadrements ci-dessus (Fekete):
`G(n) <= n*tau+1` et `n*tau2-2 <= H(n)`.
Les courbes se croisent pour `n = 3/(tau2-tau) = 46.6`.
Et on peut vérifier que `G(n) <= H(n)` pour `n=0..46`.

Mieux: On a aussi `G(n)=floor((n+1)*tau)` et `H=floor(n*tau2)+{0,1}`.
On a `(n+1)*tau <= n*tau2` dès que `n >= tau/(tau2-tau) = 9.6`.
Là encore, vérifications par calculs pour `n=0..9`.

Mieux:
```
Lemma g_add_8 n : 4 + g n <= g (8+n) <= 5 + g n.
Lemma h_add_8 n : 5 + h n <= h (8+n) <= 6 + h n.
```
Puis vérification par calculs pour `n=0..8` et ensuite récurrence de 8 en 8.

Comment généraliser tout ça à fk <= f(k+1) pour tout k ?

#### Reference:

https://en.wikipedia.org/wiki/Subadditivity

https://math.stackexchange.com/questions/57455/existence-of-a-limit-associated-to-an-almost-subadditive-sequence/57493#57493

Funny: alternative definition of reals by quasi-additive functions:
https://people.math.ethz.ch/~salamon/PREPRINTS/acampo-real.pdf

https://theorylunch.wordpress.com/2018/03/01/a-crash-course-in-subadditivity-part-1

Rauzy fractals:
https://im.icerm.brown.edu/portfolio/visualizing-rauzy-fractals-via-finite-directed-graphs/
https://tilings.math.uni-bielefeld.de/substitution/a-ab--b-c--c-a/

## Bilan

k=1 : G(n) = floor((n+1)*tau) avec tau=0.618. Quasi-add avec C=1
k=2 : H. Etude "à la Rauzy" donne Quasi-add avec C=2
    et H(n)=floor(n*tau2)+{0,1}
    avec tau2 = root(x^3+x-1) = 1/root(x^3-x^2-1) (inverse du Pisot P3 = 1.4655)
k=3 : Etude à faire. Poly x^4-x^3-1 donne nombre de Pisot Q2 = 1.3802
    donc a priori on a quasi-additivité et proximité de f3 avec floor(n*tau3)
k=4 : Etude à faire. x^5-x^4-1 = (x^2-x+1)(x^3-x-1)
     ou encore x^5+x-1 = (x^2-x+1)(x^3+x^2-1) sur le poly dual.
     Nombre de Pisot minimal (plastic = 1.3247), mais aussi des racines j et conj(j)
     en plus. Sans doute *pas* quasi-additivité et divergence lente de
     f4-floor(n*tau4) (en log(n)) 
k>=5 : des racines secondaires de norme > 1, donc sans doute pas
     de quasi-additivité ni de borne finie sur fk(n)-n*tauk.
     Ces racines secondaires ont normes croissantes juqu'à k=12 (norme=1.0768)
     puis décroissance tout en restant >1. P.ex k=200 norme=1.017.

Conjecture: fk(n)-n*tauk ~ K.n^expo avec 0<expo<1 

    En considérant u(n) = sigma(A k ((k+1)*i),i=0..n) : 
    u(n) ~ K*sigma(primroot^((k+1)*i,i=0..n) ~ K*(primroot^(k+1))^n

    delta(u(n)) = sigma(B^((k+1)*i).z,i=0..n)
     ~ K*sigma(|sndroot|^((k+1)*i,i=0..n)
     ~ K*(|sndroot|^((k+1)*n)
     
    log (delta(u(n)) ~ (k+1)*n*log |sndroot|
    log (u(n)) ~ (k+1)*n*log primroot
    
    log (delta(u(n))) ~ (log |sndroot| / log primroot)* log(u(n))
    
    expo = log |sndroot| / log primroot
     
    delta(u(n)) ~ K*(u(n))^expo
    
    Pour k=6 expo=0.128 donc grosso modo une racine huitième
    Pour k=7 expo=0.221                      racine quatre-et-demi
    Ca monte ensuite assez vite 0.6 0.7 0.8 convergence vers 1

