
Polynome : Pk(x) = x^k - x^(k-1) -1  pour k>1
=============================================

## Allure générale

Pk(0) = -1
Pk(1) = -1
Pk(2) = 2^k - 2^(k-1) -1 = 2^(k-1) -1 > 0
Pk(-1) = 1 - (-1)-1 = 1 si k pair
Pk(-1) = -1 -1 -1 = -3 si k impair

Dérivée : k*x^(k-1)-(k-1)*x^(k-2) = x^(k-2)*(kx-(k-1)).
S'annule en 0 (si k>2) et (k-1)/k = 1-1/k.
Positif sur 1..oo en tout cas.
Si k pair, Pk decroissant avant 1-1/k et croissant après,
 deux racines réelles, une dans ]-1..0[ l'autre dans ]1..2[.
Si k impair, Pk croissant avant 0 (atteint -1) puis décroit,
puis croit de nouveau après 1-1/k. Une unique racine réelle,
dans ]1..2[.

Ces racines réelles positives sont décroissantes quand k augmente.

k=2  P2(x)=x^2-x-1  racine=phi=1.618   (et -0.618)
k=3  P3(x)=x^3-x^2-1 racine=1.4655
k=4  P4(x)=x^4-x^3-1 racine=1.3802     (et -0.82)
k=5  P5(x)=x^5-x^4-1 racine=1.3247 (nombre plastique, racine de x^3-x-1) 
k=6  P6(x)=x^6-x^5-1 racine=1.28       (et -0.88)

## Factorisable quand k = 5 mod 6

Si on a une racine de norme 1 :
 comme |x^(k-1)|.|x-1| = 1 alors |x-1|=1
 donc cela ne peut être que j=e^(iπ/3) ou conj(j)
 Ce qui se produit uniquement pour: j^(k-1).(j-1) = 1
 Sauf que j-1 = e^(2iπ/3)
 Donc e^((k+1)iπ/3) = 1
 (k+1) = 0 mod 6
 k = 5 mod 6

Pour k=5 mod 6, Pk divisible par (x-j)(x-conj(j)) = x^2-x+1

Restes : 
 k = 5    x^3-x-1
 k = 11   x^9-x^7-x^6+x^4+x^3-x-1
 k = 17   x^15-x^13-x^12+x^10+x^9-x^7-x^6+x^4+x^3-x-1

Ces restes sont-ils toujours irréductibles ??


(x^p+a_(p-1).x^(p-1)+...a_0)(x^q+b_(q-1).x^(q-1)+...b_0)
= x^(p+q) +
  [a_(p-1).1 + 1.b_(q-1)]*x^(p+q-1) +
  [a_(p-2).1 + a_(p-1).b_(q-1) + 1.b_(q-2)]*x^(p+q-2)

  
  + a_0*b_0
  
  
Donc a_0*b_0 = -1 donc les deux sont +/-1 (et opposés)
et a_(p-1) = - b_(q-1)

a_(p-2) + b_(q-2)



#### Détails des polynomes restes

Notons k = 5+6p
 Alors Pk(x) = (x^2-x+1)*Rp(x)
 avec R0(x) = x^3-x-1
  et pour p<>0 :  Rp(x) = R_{p-1}(x) + x^(6p-2)*(x^5-x^3-x^2+1)

Démonstration : ok pour (x^2-x+1)(x^3-x-1) = x^5-x^4-1
et ensuite soit p<>0 tel que (x^2-x+1)*R_{p-1}(x) = P(6p-1)
alors (x^2-x+1)(R_{p-1}(x)+x^(6p-2)*(x^5-x^3-x^2+1))
    = P(6p-1) + x^(6p-2)*[x^7 - x^6 -x + 1 ]
    = P(6p+5)

Nb: Pour p<>0 : 
 Rp(x) = x^3-x-1 + x^4*(x^5-x^3-x^2+1)*Qp(x^6)
 où  Qp(x) = x^(p-1) + x^(p-2) + ... + 1 = (x^p-1)/(x-1)
 
 Rp(x) = x^3-x-1 + x^4*(x^5-x^3-x^2+1)*(x^(6*p)-1)/(x^6-1)

Nb: x^5-x^3-x^2+1 = (x-1)^2*(x+1)*(x^2+x+1)

## Irreductibilité sur Q (ou Z) sinon ?

Nb: factorisation dans Z <-> factorisation dans Q.

Si on n'est pas dans le cas k=5 mod 6, alors toutes les racines ont
normes != 1.

On a au moins la racine réelle positive qui est de norme > 1.
Le produit des racines vaut (-1)^(k-1) donc une racine au moins de
norme < 1.

Pour k>5, la racine réelle positive est inférieure au nombre plastique
1.3247... qui est le plus petit nombre de Pisot (racine de x^3-x-1).
Conséquence : Pk a alors au moins une autre racine de norme > 1 (sinon
on aurait trouvé un Pisot < nb plasique). En fait, on a même au final trois
racines de norme > 1 : la racine réelle positive, et deux complexes conjugées.


#### Facteur de degré 1

Factorisation sur Q, donc on aurait alors une racine rationnelle. 

Théorème des racines rationnelles : cette racine ne pourrait être
que +/-1 ce qui n'est pas.

#### Facteur de degré 2

Si un facteur de degré 2 : P = Q.R avec Q degré 2.
Prenons Q et R polynomes à coefs entiers, et unitaires (sinon
developpement ne pourrait donner x^k+...).
Donc Q = x^2+ax+b

P(0) = -1 = Q(0).R(0) donc Q(0) = b = +/- 1
P(1) = -1 = Q(1).R(1) donc Q(1) = 1+a+b = +/- 1

 donc 4 cas possibles : 
 Q = x^2-3x+1 ==> racines (3+/-sqrt(5))/2, racine positive > 2 : impossible

 Q = x^2-x+1 ==> racines j et conj(j), ok ssi k=5 mod 6, cf avant

 Q = x^2-x-1 ==> racines (1+/-sqrt(5))/2 c'est P quand k=2 mais
   ensuite la racine réelle positive est trop grande.
   
 Q = x^2+x-1 ==> racines (-1+/-sqrt(5))/2, racine positive 0< <1 : impossible

Bref, pas de facteur strict de degré 2 hormis parfois (x^2-x+1).


### Facteur de degré 3

Si un facteur de degré 3
 P = Q.R avec Q degré 3
     Q = x^3+ax^2+bx+c

P(0) = -1 = Q(0).R(0) donc Q(0) = c = +/- 1
P(1) = -1 = Q(1).R(1) donc Q(1) = 1+a+b+c = +/- 1
P(-1) =
 si k pair:  1-(-1)-1 = 1 = Q(-1).R(-1) donc Q(-1) = -1+a-b+c = +/- 1
 si k impair: (-1)-1-1 = -3 = Q(-1).R(-1) donc Q(-1) = -1+a-b+c = +/-1 ou +/-3

 donc 16 cas possibles:
 c=1, a+b= -1,-3   a-b=-1,1,-3,3
   donc (a,b)=
        (-1,0) racine réelle -0.75 impossible (pour k=2 c'est -0.618, puis <= -0.81 pour k>=4)
        (0,-1) racine réelle -1.32 KO
        (-2,1) racine réelle -0.46 KO
        (1,-2) racine réelle -2.14 KO
        (-2,-1) racine réelle 2.24 KO
        (1,-4) racine réelle -2.65 KO
        (-3,0) racine réelle 2.87 KO
        (0,-3) racine réelle -1.87 KO
 
 c=-1, a+b= -1,1   a-b=1,3,-1,5
   donc (a,b)=
        (0,-1) possible ssi k=5 (x^3-x-1, cf nb plastique)
        (1,-2) racine réelle -1.8 KO
        (-1,0) c'est k=3, racine réelle 1.4655 impossible ensuite
        (2,-3) ............. -2.91
        (1,0)  ............. 0.75
        (2,-1) ............. -2.24
        (0,1)  ............. 0.6823
        (3,-2) ............. -3.49

Bref, facteur strict de degré 3 possible seulement pour k=5

### Et ensuite ??

Pk irreductible pour k<8 (hormis k=5) car sinon il y aura au
moins un facteur de degré 3. Ensuite ?

Pour P8 on peut vérifier qu'il n'y a pas deux facteurs
de degré 4, à coefs entiers, unitaires tq. P8=Q*R.
Méthode de Kronecker:
P8(0) = -1 = Q(0)*R(0) donc l'un a coef constant 1, l'autre -1
P8(1) = -1 = Q(1)*R(1) donc Q(1) = +/-1 et R(1)=-Q(1)
P8(-1) = -1 = Q(-1)*R(-1) donc Q(-1) = +/-1 et R(-1)=-Q(-1)
P8(2) = 127 = Q(2)*R(2) donc Q(2)\in{1,-1,127,-127} et R(2)=127/Q(2)
On a donc 16 cas pour (Q(1),Q(-1),Q(2)), ensuite cela donne
à chaque fois des systèmes linéaires donnant les coefs restants de Q,
et de R (ou souvent pas de solutions entières, juste des fractions).
Pour le seul cas où Q et R ont des solutions simultanément, le produit
des polynômes trouvées ne donne pas P8.

Pas de généralisation évidente.
Si Pk = Q*R, on peut juste dire:
 Q(0)*R(0) = -1 donc Q(0)=+/-1
 Q(1)*R(1) = -1 donc Q(1)=+/-1 (i.e. la somme des coefs de Q)
 Q(-1)*R(-1) = -1 ou -3 selon la parité de k.
  donc la somme alternée des coefs de Q est dans 1,-1,3,-3.
Ensuite ?
 En 2 on obtient un 2^(k-1)-1 mais qui n'est que rarement premier.
 
??


### Dual

Polynome dual (chgt par x->1/x) : x^k+x-1
Ca n'a pas l'air gagnant comme changement.

Refs:

https://mathcircle.berkeley.edu/sites/default/files/archivedocs/2009_2010/lectures/0910lecturespdf/claudiu_polynomials.pdf

https://yufeizhao.com/olympiad/intpoly.pdf

https://en.wikipedia.org/wiki/Perron%27s_irreducibility_criterion
https://en.wikipedia.org/wiki/Cohn%27s_irreducibility_criterion
https://en.wikipedia.org/wiki/Eisenstein%27s_criterion

### Nombre de racines de norme >1

Apparemment ça a l'air d'être le nombre de racine k-ieme de l'unité
entre e^-iπ/3 et e^iπ/3.

La plus "grande" racine k-ieme de l'unité qui convient:
 2π*p/k <= π/3
      p <= k/6
      p = int(k/6)

En tout (avec 1 et les negatives) :
 1 + 2*int(k/6) racines de norme >1

k<=5 -> 1
6<=k<=11 -> 3
12<=k<=17 -> 5
18<=k<=23 -> 7
24<=k<=29 -> 9
...

En gros un tiers des racines de norme >1 et deux tiers de norme <1


Comment prouver ça ??

racine alpha = r.e^ia  avec a ∈ 0..π (sinon on considère son conjugué)
Soit beta la racine k-ieme de l'unité associée à alpha : e^2πip/k
avec 2πp/k immédiatement au dessus de a donc p = ceil(ak/2π)

Borne sur |alpha-beta| ?
Apparemment Re(alpha-beta) > 0 ?
Et Im(alpha-beta) <= 0 ?

alpha^k - alpha^(k-1) = 1
beta^k = 1


(alpha-beta)^k
 = alpha^k + Σ(-1)^p*Cpk*alpha^p.beta^(k-p) + (-1)^k.beta^k
 = 1+alpha^(k-1) + ... + (-1)^k.1


Continuité de Qk,q(X) = x^k-q.x^(k-1)-1 pour q ∈ [0;1]
Donne un chemin entre les racines de P et les racines k-ieme de
l'unité ? Apparemment oui, cf

https://fr.wikipedia.org/wiki/Relations_entre_coefficients_et_racines#Continuit%C3%A9_des_racines
http://www.lix.polytechnique.fr/~pilaud/enseignement/agreg/continuiteracines/racines.pdf

x^k-q.x^(k-1)-1 est toujours à racines simples
car dérivée kx^(k-1)-(k-1)qx^(k-2) = x^(k-2)*[kx-(k-1)q]
 a 0 et q(1-1/k) comme racines
 Or 0 n'est pas racine du poly de départ
 et q(1-1/k) ∈ [0,1[ tandis que la racine réelle positive de Qk,q est >=1

La somme des racines vaut q et va donc
de 0 (pour les racines k-ième de l'unité) à 1 (pour Pk)

Le produit des racines vaut toujours (-1)^(k-1)
