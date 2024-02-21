% Un problème d'Hofstadter pour ses lecteurs curieux
% Pierre Letouzey (CC-BY)
% 9 novembre 2018

## Avertissement : la préparation de cet exposé a subi...

La loi d'Hofstadter : il faut toujours plus longtemps que prévu, même en tenant compte de la loi d'Hofstadter.

## Code Coq + rapport technique + cet exposé

<https://github.com/letouzey/hofstadter_g>

(branche avec les dernières nouveautés: `generalized`)

## Un arbre infini auto-similaire

Douglas Hofstadter, "Gödel,Escher,Bach", p.135

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

## Un arbre infini auto-similaire

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
Départ à 3 ? Pour expliciter les nombres de Fibonacci

## Ajout d'une racine ad-hoc...

\begin{tikzpicture}[grow'=up]
\Tree
 [.1 [.2 [.3
       [.4 [.6 [.9 [.14 22 23 ] [.15 24 ] ]
               [.10 [.16 25 26 ]]]
           [.7 [.11 [.17 27 28 ] [.18 29 ]]]]
       [.5 [.8 [.12 [.19 30 31 ] [.20 32 ]]
               [.13 [.21 33 34 ]]]]]]]
\end{tikzpicture}


## Et la fonction parent est ...

\begin{align*}
G(n) &= n - G(G(n-1)) & (\text{pour}\ n>0) \\
G(0) &= 0
\end{align*}


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

## Etude de G

\ensuremath{G(n) = n - G(G(n-1))}

 - Existence + encadrement $0\leq G(n) \leq n$
 - $G(0)=0$, $G(1)=1$ puis $1\leq G(n)<n$
 - G "avance" par pas de 0 ou +1
 - Après un pas à 0, forcément un +1
 - Jamais trois +1 de suite 

\pause

On peut en fait montrer que $G(n)=\lfloor (n+1)/\phi \rfloor$

## Etude de G

\ensuremath{G(n) = n - G(G(n-1))}

\bigskip

\begin{tikzpicture}
  \begin{axis}[
    xmin=0,xmax=14,ymin=0,ymax=14,samples=15,
    xlabel=$n$,
    ylabel=$G(n)$
  ] 
    \addplot+[dashed,mark=.,domain=0:14] {(x+1) * 0.618033988749894903}; 
    \addplot+[domain=0:14] {floor((x+1) * 0.618033988749894903)}; 
  \end{axis}
\end{tikzpicture}

## Deux équations cruciales

Surjectivité "explicite"

 - $G(n+G(n))=n$

\pause
\bigskip

Equation "renversée"

 - $G(n)+G(G(n+1)-1)=n$

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

## Et en Coq ?

Jusqu'ici, rien que du connu (cf <https://oeis.org/A005206>).
Attention à la littérature (en particulier un article buggé de 1986) !
Preuves Coq "maison", sans trop de soucis:

 - `DeltaList.v`
 - `Fib.v`
 - `FunG.v`
 - `Phi.v`

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

- Preuve papier pénible, multiples cas (vive Coq!)

## Grandes lignes

 - Une fonction $depth$ donnant l'étage de $n$ dans l'arbre.
 - En fait un inverse de Fibonacci.
 - Aussi calculable en itérant $G$ sur $n$ jusqu'à atteindre 1.

\pause

 - Une fonction $flip$ qui renverse un étage de l'arbre:
   $flip(1+F_k),...,flip(F_{k+1}) = F_{k+1},...,1+F_k$.
 - Def: $flip(n)=if~n\leq 1~then~n~else~1+F(1+depth(n))-n$.

\pause
 
 - Def: $\overline{G}(n)=flip(G(flip(n)))$
 - Et on montre que ce $\overline{G}$ valide la formule
 - En Coq: `FlipG.v`
   
## Autre résultat principal

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


## Dérivées

Def: $\Delta\!G(n) = G(n+1)-G(n)$.

Prop: $\Delta\!G(n+1) = 1 - \Delta\!G(n).\Delta\!G(G(n))$.

\bigskip

Def: $\Delta\!\overline{G}(n) = \overline{G}(n+1)-\overline{G}(n)$.

Prop: $\Delta\!\overline{G}(n+1) = 1 - \Delta\!\overline{G}(n).\Delta\!\overline{G}(\overline{G}(n+1))$
 (pour n>2).
 
## Equation alternative

Anciens essais: pour n>3, $\overline{G}(n-1)+\overline{G}(\overline{G}(n))= n$ 

\bigskip

Mais ceci ne caractérise pas une unique fonction
(sauf à exiger qu'elle soit monotone).

## Généralisation

$(k+1)$ appels récursifs imbriqués au lieu de 2 :

\pause

\begin{align*}
f_k (n) &= n - f_k^{(k+1)}(n-1) & (\text{pour}\ n>0) \\
f_k (0) &= 0
\end{align*}

\pause

 - $f_1 = G$
 - $f_2 = H$ (aussi mentionné par Hofstadter)
 - $f_0(n) = n - f_0(n-1)$ : division par 2

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

## Etude de $f_k$

Les propriétés de $G$ se généralisent plutôt bien à $f_k$:

 - $f_k(n+ f_k^{(k)}(n))=n$
 - $f_k(n)+f_k^{(k)}(f_k(n+1)-1)=n$
 - $f_k(\Sigma A^k_i) = \Sigma A^k_{i-1}$
 - ...

\pause

Preuves Coq toutes fraîches, un peu de sport avec $f_k^{(k)}$

\pause
\bigskip

Par contre:

 - $f_k(n)$ n'est **pas** $\lfloor (n+1)/\alpha_k \rfloor$
   avec $\alpha_k$ racine réelle positive de $X^{k+1}-X^k-1$.


## Etude de $\overline{f}_k$

Prouvé cette semaine, quasiment comme pour $\overline{G}$ :

\begin{align*}
\overline{f}_k(n) &= n+1 - \overline{f}_k^{(k)}(\overline{f}_k(n-1)+1) & (n>k+2) \\
\overline{f}_k(n) &= n                     & (n=0,1) \\
\overline{k}_k(n) &= n-1                   & (2\le n \le k+2) \\
\end{align*}

\pause

Différences entre $\overline{f}_k$ et $f_k$ : TODO

## Comparaison des $f_k$ quand $k$ varie ?

- Conjecture: $f_k(n) \le f_{k+1}(n)$ pour tout $n$ et $k$
- Preuve ???

\pause
\bigskip

Pour établir ces comparaisons au moins pour $n$ assez grand:

- Conjecture: $f_k(n) - n/\alpha_k$ borné quand n varie
- Ou au moins $f_k(n) \sim n/\alpha_k$ quand $n\to\infty$ ?
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


## Surprise

Affichage des points $(\delta(i),\delta(f_2(i))$ avec i=0..10000
et $\delta(n) = f_2(n) - n/\alpha_2$


\includegraphics[width=\linewidth]{fractal.png}




## Conclusions & Perspectives

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
