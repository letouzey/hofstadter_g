% A propos d'une curieuse famille de fonctions récursives imbriquées dues à Hofstadter
% Pierre Letouzey
% 9 octobre 2023

## Avertissement : la préparation de cet exposé a subi...

La loi d'Hofstadter : il faut toujours plus longtemps que prévu, même en tenant compte de la loi d'Hofstadter.

## Code Coq + cet exposé + ancien rapport technique

<https://github.com/letouzey/hofstadter_g>

(branche: `generalized`)

## La fonction G d'Hofstadter (OEIS A5206)

Douglas Hofstadter, "Gödel,Escher,Bach", chapitre 5 (p.135)

\begin{align*}
G(0) &= 0 \\
G(n) &= n - G(G(n-1)) & \text{pour tout entier}\ n>0
\end{align*}

## Etude préliminaire de G

\ensuremath{G(n) = n - G(G(n-1))}

 - Existence et premier encadrement: $0\leq G(n) \leq n$
 - $G(0)=0$, $G(1)=1$ puis $1\leq G(n)<n$
 - G "monte" par pas de +0 ou +1
 - Jamais deux +0 de suite
 - Jamais trois +1 de suite

\pause

Ici en fait : $G(n)=\lfloor (n+1)/\phi \rfloor$ où
$\phi$ est le nombre d'or

## Etude préliminaire de G

Graphes de $G(n)$ et $(n+1)/\phi$ :

\bigskip

\begin{tikzpicture}
  \begin{axis}[
    xmin=0,xmax=14,ymin=0,ymax=14,samples=15,
    xlabel=$n$,
  ] 
    \addplot+[dashed,mark=.,domain=0:14] {(x+1) * 0.618033988749894903}; 
    \addplot+[domain=0:14] {floor((x+1) * 0.618033988749894903)}; 
  \end{axis}
\end{tikzpicture}

## Généralisons : la fonction H (OEIS A5374)

Comme Hofstadter, varions le nombre d'appels imbriqués:

\begin{align*}
H(0) &= 0 \\
H(n) &= n - H(H(H(n-1)) & \text{pour tout entier}\ n>0
\end{align*}

Mêmes propriétés de base que $G$, sauf que:

 - Au plus trois +1 successifs
 - Pas d'équation simple et exacte à base de $\lfloor ~ \rfloor$
 - Par contre: $H(n) = \lfloor \tau n \rfloor + 0 ~\text{ou}~ 1$
 
   avec $\tau$ racine réelle de $X^3+X-1$ ($\tau = 0.6823$)

## Genéralisons encore : une famille $f_k$ de fonctions

Notons $k+1$ le nombre d'appels récursifs:

\begin{align*}
f_k(0) &= 0 \\
f_k(n) &= n - f_k^{(k+1)}(n-1)) & \text{pour tout entier}\ n>0
\end{align*}

où $f_k^{(p)}$ note $p$ itérations de $f_k$ :
$f_k^{(0)}=id$ et $f_k^{(p+1)}=f_k\circ f_k^{(p)}$

On retrouve en particulier $G = f_1$ et $H = f_2$

NB: ce $k$ est choisi pour éviter le cas "0 appel récursif"
(sans intérêt et non uniforme avec le reste)

## Le cas initial $f_0$ : un seul appel récursif

$f_0(n) = n - f_0(n-1)$

On alterne +0 et +1, c'est en fait une fonction moitié :

$f_0(n) = \lfloor (n+1)/2 \rfloor = \lceil n/2 \rceil$

## Graphes

\begin{tikzpicture}
  \begin{axis}[
    xmin=0,xmax=30,ymin=0,ymax=20,samples=31,
    xlabel=$n$, legend pos=south east
  ] 

    \addplot [mark=.,color=blue] coordinates {
(0, 0) (1, 1) (2, 1) (3, 2) (4, 3) (5, 4) (6, 5) (7, 5) (8, 6)
 (9, 6) (10, 7) (11, 8) (12, 8) (13, 9) (14, 10) (15, 11) (16, 11)
 (17, 12) (18, 13) (19, 14) (20, 15) (21, 15) (22, 16) (23, 17)
 (24, 18) (25, 19) (26, 19) (27, 20) (28, 20) (29, 21) (30, 22)};
 \addlegendentry{$f_3$}
    \addplot [mark=.,color=orange] coordinates {
(0, 0) (1, 1) (2, 1) (3, 2) (4, 3) (5, 4) (6, 4) (7, 5) (8, 5)
 (9, 6) (10, 7) (11, 7) (12, 8) (13, 9) (14, 10) (15, 10) (16, 11)
 (17, 12) (18, 13) (19, 13) (20, 14) (21, 14) (22, 15) (23, 16)
 (24, 17) (25, 17) (26, 18) (27, 18) (28, 19) (29, 20) (30, 20) };
 \addlegendentry{$f_2$}
 \addplot+[mark=.,domain=0:30,color=red]
 {floor((x+1) * 0.618033988749894903)};
 \addlegendentry{$f_1$}
 \addplot+[mark=.,domain=0:30] {ceil(x/2)}; 
 \addlegendentry{$f_0$}
 \end{axis}
\end{tikzpicture}

## Premières propriétés de $f_k$

\ensuremath{f_k(n) = n - f_k^{(k+1)}(n-1))}

 - Existence et premier encadrement: $0\leq f_k(n) \leq n$
 - $f_k(0)=0$, $f_k(1)=1$ puis $1\leq f_k(n)<n$
 - $f_k$ "monte" par pas de +0 ou +1
 - Jamais deux +0 de suite
 - Au plus $k+1$ pas de +1 de suite

NB: Pour k>1, $f_k(n)$ n'a pas d'expression simple via $\lfloor~ \rfloor$.

## Deux équations intéressantes pour $G$ puis $f_k$ 

Surjectivité "explicite"

 - $G(n+G(n))=n$
 - $f_k(n+f_k^{(k)}(n))=n$

\pause
\bigskip

Equation "renversée"

 - $G(n)+G(G(n+1)-1)=n$
 - $f_k(n)+f_k^{(k)}(f_k(n+1)-1)=n$

## Et en Coq ?

TODO

## Conjecture: croissance des $f_k$ point-à-point

Conjecture: $\forall k, \forall n, f_k(n) \le f_{k+1}(n)$

Ici, on comparera toujours les fonctions via l'ordre produit.

Cette conjecture affirme donc que $(f_k)$ est une suite croissante.

 - Facile: $\forall k, f_0 \le f_k$
 - Preuves ad-hoc (et dures) : pour $k\le9$, $f_k \le f_{k+1}$
 - "Petits" $n$ : $\forall k, \forall n \le (k+4)(k+5)/2-3, f_k(n) \le
   f_{k+1}(n)$
 - "Grands" $n$ : $\forall k, \exists N, \forall n\ge N, f_k(n) \le f_{k+1}(n)$

Preuve complète ??

TODO: détailler (les 3 cas, pourquoi dur, etc)


##
\section{Arbres rationnels}

## Un arbre infini rationnel

\bigskip

\begin{tabular}{lclclcl}
G & = & 
\begin{tikzpicture}[grow'=up]
\Tree
     [.$\circ$ G
        [.$\circ$ [.G ]]]
\end{tikzpicture}
\pause
& = &
\begin{tikzpicture}[grow'=up]
\Tree
     [.$\circ$
       [.$\circ$ G
          [.$\circ$ [.G ]]]
       [.$\circ$ [.$\circ$ G
          [.$\circ$ [.G ]]]]]
\end{tikzpicture}
&=& ...
\end{tabular}

## Un arbre infini rationnel

\begin{tikzpicture}[grow'=up]
\Tree
     [.$\circ$
       [.$\circ$ [.$\circ$ [.$\circ$ [.$\circ$ G [.$\circ$ G ]]
                                     [.$\circ$ G ] ]
               [.$\circ$ [.$\circ$ G [.$\circ$ G ]]]]
           [.$\circ$ [.$\circ$ [.$\circ$ G [.$\circ$ G ]]
                                           [.$\circ$ G ]]]]
       [.$\circ$ [.$\circ$ [.$\circ$ [.$\circ$ G [.$\circ$ G ]]
                                     [.$\circ$ G ]]
               [.$\circ$ [.$\circ$ G [.$\circ$ G ]]]]]]
\end{tikzpicture}
\pause
Combien de noeuds par niveau ?

## Numérotons !

Parcours en largeur, de gauche à droite

\bigskip

\begin{tikzpicture}[grow'=up]
\Tree
     [.3
       [.4 [.6 [.9 [.14 22 23 ] [.15 24 ] ]
               [.10 [.16 25 26 ]]]
           [.7 [.11 [.17 27 28 ] [.18 29 ]]]]
       [.5 [.8 [.12 [.19 30 31 ] [.20 32 ]]
               [.13 [.21 33 34 ]]]]]
\end{tikzpicture}
\pause
Départ à 3 ? Pour expliciter les nombres de Fibonacci...

Et ainsi, le noeud $n$ a $G(n)$ comme parent.

## Ajout d'une racine ad-hoc : l'arbre de G

\begin{tikzpicture}[grow'=up]
\Tree
 [.1 [.2 [.3
       [.4 [.6 [.9 [.14 22 23 ] [.15 24 ] ]
               [.10 [.16 25 26 ]]]
           [.7 [.11 [.17 27 28 ] [.18 29 ]]]]
       [.5 [.8 [.12 [.19 30 31 ] [.20 32 ]]
               [.13 [.21 33 34 ]]]]]]]
\end{tikzpicture}

## Aparté : arbre de fonction, fonction d'arbre

Soit un arbre:

 - infini
 - dont les noeuds ont des arités finies non nulles
 - numéroté via un parcours en largeur

Que peut-on dire de sa fonction parent ?

\bigskip
\pause
Recip. que faut-il sur une fonction $\mathbb{N}\to \mathbb{N}$ pour
qu'elle soit la fonction parent d'un et un seul tel arbre ?

## Aparté : arbre de fonction, fonction d'arbre

 - f croissante
 - f(n)<n hormis à la racine
 - f surjective
 - f ne stationne pas (i.e. tend vers $+\infty$)

## A problem for curious readers is:

Suppose you flip diagram G around as if in a mirror,
and label the nodes of the new tree so that they increase
from left to right. Can you find a recursive *algebraic*
definition for this "flip-tree" ?

## Arbre miroir $\overline{G}$

\begin{tikzpicture}[grow'=up]
\Tree
 [.1 [.2 [.3
       [.4 [.6 [.9 [.14 22 23 ] ]
               [.10 [.\fbox{15} 24 ] 
                    [.16 25 26 ]]]]
       [.5 [.\fbox{7} [.11 [.17 27 ] [.18 \fbox{28} 29 ]]]
           [.8 [.12 [.19 30 31 ] ]
               [.13 [.\fbox{20} 32 ]
                    [.21 33 34 ]]]]]]]
\end{tikzpicture}

## Solution ?

\newcommand{\FG}{\ensuremath{\overline{G}}}

- Il y avait une conjecture sur <https://oeis.org/A123070>
- Mais pas de preuve...
- Hofstadter devait probablement avoir au moins cette formule

\begin{align*}
\FG(n) &= n+1 - \FG(\FG(n-1)+1) & (n>3) \\
\FG(n) &= n                     & (n=0,1) \\
\FG(n) &= n-1                   & (n=2,3) \\
\end{align*}

- Preuve papier pénible, multiples cas (vive Coq! cf fichier `FlipG.v`)

## Arbre généralisé

On allonge la branche de droite ($k+1$ segments)
\bigskip
\begin{tabular}{lclclcl}
$f_k$ & = &
\begin{tikzpicture}[grow'=up]
\Tree
     [.$\circ$ $f_k$
        [.$\circ$ [. {\ldots} [.$f_k$ ]]]]
\end{tikzpicture}
\end{tabular}

\pause
\bigskip

Et toujours une racine ad-hoc (1 puis $k+1$ segments)

## Arbre pour $f_2$ (H de Hofstadter)

\begin{tikzpicture}[grow'=up]
\Tree
 [.1 [.2 [.3 [.4
       [.5 [.7 [.10 14 15 ]
               [.11 16 ]]
           [.8 [.12 17 ]]]
       [.6 [.9 [.13 18 19 ]]]]]]]
\end{tikzpicture}

## Arbre pour $f_0$

\begin{tikzpicture}[grow'=up]
\Tree
 [.1 [.2
       [.3
         [.5 9 10 ]
         [.6 11 12 ]]
       [.4
         [.7 13 14 ]
         [.8 15 16 ]]]]
\end{tikzpicture}


## Equation de l'arbre miroir $\overline{f}_k$ ?

Quasiment comme pour $\overline{G}$ :

\begin{align*}
\overline{f}_k(n) &= n+1 - \overline{f}_k^{(k)}(\overline{f}_k(n-1)+1) & (n>k+2) \\
\overline{f}_k(n) &= n                     & (n=0,1) \\
\overline{k}_k(n) &= n-1                   & (2\le n \le k+2) \\
\end{align*}


TODO Différences entre $\overline{f}_k$ et $f_k$ : TODO


##
\section{Fibonacci généralisé et numération}

## Fibonacci 

\begin{align*}
F_0 &= 1 \\
F_1 &= 2 \\
F_{n+2} &= F_n + F_{n+1}
\end{align*}

\pause
\bigskip

NB: indices décalés pour éviter 0 et un double 1

## Théorème de Zeckendorf

\newcommand{\fibrest}{\ensuremath{\Sigma F_i}}

Une décomposition $n = \fibrest$ est *canonique* si elle est :

 (1) sans doublons
 (2) sans termes consécutifs

Décomposition *relachée* : (1) mais pas forcément (2)

\pause
\bigskip

Thm: tout entier naturel a une unique décomposition canonique.

## Zeckendorf, variante

Def: le *rang* d'une décomposition est l'indice du plus petit terme.

\bigskip

Algo: canonisation d'une décomposition relachée de n

 - le nombre de termes décroît ou stagne
 - le rang augmente (par pas de 2) ou stagne

## G et Fibonacci

 - \ensuremath{G(F_i) = F_{i-1}} (avec la convention \ensuremath{F_{0-1}=F_0=1})
\pause
 - Plus généralement: $G(\Sigma F_i) = \Sigma F_{i-1}$
\pause
 - Cela marche même pour des décompositions relachées
 - Preuve selon le rang de la décomposition (0, pair>0, impair).
 - Nombreuses conséquences concernant G et le rang.

## TODO Et en Coq ?

Jusqu'ici, rien que du connu (cf <https://oeis.org/A005206>).
Attention à la littérature (en particulier un article buggé de 1986) !
Preuves Coq "maison", sans trop de soucis:

 - `DeltaList.v`
 - `Fib.v`
 - `FunG.v`
 - `Phi.v`
   
## Au passage, différences entre $\overline{G}$ et $G$

Def: $n$ est de rang 1-impair si sa décomposition canonique
commence par $F_1 + F_{2p+1} + ...$.

\bigskip

Thm: $\overline{G}(n)=1+G(n)$ si $n$ est de rang 1-impair,
sinon $\overline{G}(n)=G(n)$.

\pause
\bigskip

Preuve: encore pire que la précédente, pléthore de cas.

\bigskip

Cor: $\overline{G}$ et $G$ diffèrent pour $7 = F_1+F_3$, puis tous les 5 ou 8 entiers.

## Fibonacci généralisé

Soit $k$ fixé.

\begin{align*}
A^k_0 &= 1 \\
A^k_1 &= 2 \\
... \\
A^k_{k} &= k+1 \\
A^k_{n+1} &= A^k_{n} + A^k_{n-k} & (\text{pour}\ n\ge k)
\end{align*}

## Fibonacci généralisé

- $A^0$ : 1  2  4  8  16  32  64  128  256  512
- $A^1$ : 1  2  3  5  8  13  21  34  55  89
- $A^2$ : 1  2  3  4  6  9  13  19  28  41
- $A^3$ : 1  2  3  4  5  7  10  14  19  26

NB: $A^2$ est nommé Narayana’s Cows, cf. OEIS A930

## Zeckendorf généralisé

\newcommand{\Arest}{\ensuremath{\Sigma A^k_i}}

Soit $k$ fixé.

\bigskip

$k$-décomposition $n = \Arest$ *canonique* : indices distants $\ge (k+1)$

$k$-décomposition *relachée* : indices distants d'au moins $k$

\pause
\bigskip

Thm: tout entier naturel a une unique $k$-décomposition canonique.

Algo: on peut "renormaliser" une $k$-décomposition relachée.

## $f_k$ et Fibonacci généralisé

 - \ensuremath{f_k(A^k_i) = A^k_{i-1}} (avec la convention \ensuremath{A^k_{0-1}=A^k_0=1})
\pause
 - Plus généralement: $f_k(\Sigma A^k_i) = \Sigma A^k_{i-1}$
\pause
 - Cela marche pour des décompositions canoniques ou relachées


##
\section{Lien avec des mots morphiques}


## Comparaison des $f_k$ quand $k$ varie ?

- Conjecture: $f_k(n) \le f_{k+1}(n)$ pour tout $n$ et $k$
- Preuve ???

\pause
\bigskip

Pour établir ces comparaisons au moins pour $n$ assez grand:

- Conjecture: $f_k(n) - n/\alpha_k$ borné quand n varie FAUX!
- Ou au moins $f_k(n) \sim n/\alpha_k$ quand $n\to\infty$ ? OUI!
- Preuve ???

## Entiers de rang 0

Une piste pour la comparaison des $f_k$ :

$f_k$ est "plate" en $n$ lorsque rang$_k$($n$) = 0

Bref lorsque $n$ a un 1 dans sa $k$-décomposition

## Tableau de Wythoff / Zeckendorf (k=1)

Colonne c: les nombres de rang c par ordre croissant

\bigskip

\begin{tabular}{|c|c|c|c|c|c|c|c|}
\hline
1 & 2 & 3 & 5 & 8 & 13 & 21 & \ldots\\
\hline
4 & 7 & 11 & 18 & 29 & 47 & 76 & \ldots \\
\hline
6 & 10 & 16 & 26 & 42 & 68 & 110 & \ldots \\
\hline
9 & 15 & 24 & 39 & 63 & 102 & \ldots & \dots \\
\hline
12 & 20 & 32 & 52 & 84 & \ldots & \ldots & \ldots \\
\hline
14 & 23 & 37 & 60 & 97 &  \ldots & \ldots & \ldots \\
\hline
17 & 28 & 45 & 73 & 118 &  \ldots & \ldots & \ldots \\
\hline
\ldots & \ldots & \ldots & \ldots & \ldots &  \ldots & \ldots & \ldots \\
\hline
\end{tabular}

##
\section{Cas k=2, Pisot, Fractale}


## Surprise

Affichage des points $(\delta(i),\delta(f_2(i))$ avec i=0..10000
et $\delta(n) = f_2(n) - n/\alpha_2$


\includegraphics[width=\linewidth]{fractal.png}

##
\section{Cas k=3, Pisot sans jolie fractale...}

##
\section{Cas k>3, $f_k(n) - n.\tau_k$ diverge}


## TODO Conclusions & Perspectives

- On trouve encore des conjectures "abordables" sur OEIS
- Et aussi parfois des petites choses fausses...
\pause
- Des preuves étonnemment délicates pour de "simples" entiers.
- Merci Coq.
- Preuves papier plus directes ?
- Preuves Coq moins pédestres (quasi 7000 lignes en tout) ?
\pause
- Quid des conjectures ?
- Quid de cette fractale ?
- Longue réponse d'Hofstadter par mail à étudier 


## TODO encore à détailler

- Additivité
- suites linéaires, reels Coq, etc

- factorisation de polynôme ? Position des racines ?
  P.ex. raisonnement à rebours donnant des racines complexes | |>1
  sinon on aurait un Pisot trop petit.
