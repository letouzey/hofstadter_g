% Un problème d'Hofstadter pour ses lecteurs curieux
% Pierre Letouzey
% 10 avril 2018

## Code Coq + rapport technique + cet exposé

<https://github.com/letouzey/hofstadter_g>

## Apéritif : fiboscargot

~~~ocaml
let rec f n l a = match n,l with
 | (0|1), [] -> succ a
 | (0|1), m::l -> f m l (succ a)
 | _ -> f (n-1) (n-2 :: l) a

let fiboscargot n = f n [] 0
~~~

<!--- Variant : List.map (fun k -> 1 lsl k) (n::l)  -->

## Un arbre auto-similaire

Douglas Hofstadter, "Gödel,Escher,Bach", p.135

\bigskip

\begin{tabular}{lclclcl}
G & = & 
\begin{tikzpicture}[grow'=up]
\Tree
     [.$\circ$ G
        [.$\circ$ [.G ]]]
\end{tikzpicture}
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

## Un arbre auto-similaire

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

## Une racine ad-hoc

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
G(n) &= n - G(G(n-1)) \hspace{1cm} (n>0) \\
G(0) &= 0
\end{align*}


## Aparté : arbre de fonction, fonction d'arbre

Soit un arbre:

 - infini
 - dont les noeuds ont des arités finies non nulles
 - numéroté via un parcours en largeur

Que peut-on dire de sa fonction parent ?

\bigskip

Recip. que faut-il sur une fonction $\mathbb{N}\to \mathbb{N}$ pour
qu'elle soit la fonction parent d'un et un seul tel arbre ?

## Aparté : arbre de fonction, fonction d'arbre

 - f croissante
 - f(n)<n hormis à la racine
 - f surjective
 - f ne stationne pas (i.e. tend vers $+\infty$)

## Fibonacci

\begin{align*}
F_0 &= 0 \\
F_1 &= 1 \\
F_{n+2} &= F_n + F_{n+1}
\end{align*}

## Théorème de Zeckendorf

\newcommand{\fibrest}{\ensuremath{\Sigma F_i}}

Décomposition $n = \fibrest$ *canonique*:

 (1) pas de $F_0$ ni $F_1$
 (2) pas de redondance
 (3) pas de nombres de Fibonacci consécutifs

Décomposition *faible* : (1) + (2)

\bigskip

Thm: tout entier naturel a une unique décomposition canonique.

## Zeckendorf, variante

Def: le *rang* d'une décomposition est l'indice du plus petit terme.

\bigskip

Algo: canonisation d'une décomposition faible de n

 - le nombre de termes croît ou stagne
 - le rang augmente (par pas de 2) ou stagne

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

## Etude de G

\ensuremath{G(n) = n - G(G(n-1))}

 - Existence + encadrement $0\leq G(n) \leq n$
 - $G(0)=0$, $G(1)=1$ puis $1\leq G(n)<n$
 - G "avance" par pas de 0 ou +1
 - Après un pas à 0, forcément un +1
 - Jamais trois +1 de suite 

On peut en fait montrer que $G(n)=\lfloor (n+1)/\phi \rfloor$

## Surjectivité

Propriété importante:

 - $G(n+G(n))=n$
 
Conséquence:

 - $G(n)+G(G(n+1)-1)=n$


## G et Fibonacci

 - \ensuremath{G(F_i) = F_{i-1}}
 - Plus généralement: $G(\Sigma F_i) = \Sigma F_{i-1}$,
   en partant d'une décomposition faible
 - Preuve selon le rang de la décomposition
   (2, pair>2, impair).
 - Nombreuses conséquences concernant G et le rang.

## Et en Coq ?

Jusqu'ici, rien que du connu (cf <https://oeis.org/A005206>).
Attention à la littérature (en particulier un article buggé de 1986) !
Preuves Coq "maisons", sans trop de soucis:

 - `DeltaList.v`
 - `Fib.v`
 - `FunG.v`
 - `Phi.v`

## A problem for curious readers is:

Suppose you flip diagram G around as if in a mirror,
and label the nodes of the new tree so that they increase
from left to right. Can you find a recursive *algebraic*
definition for this "flip-tree" ?

## Arbre miroir

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
\FG(n) &= n+1 - \FG(\FG(n-1)+1) \hspace{1cm} (n>3) \\
\FG(n) &= \lceil n/2 \rceil  \hspace{4cm} (n\leq 3) \\
\end{align*}

- Preuve papier pénible, multiples cas (vive Coq!)

## Grandes lignes

 - Une fonction $depth$ donnant l'étage de $n$ dans l'arbre.
 - En fait un inverse de Fibonacci.
 - Aussi calculable en itérant $G$ sur $n$ jusqu'à atteindre 1.

 - Une fonction $flip$ qui renverse un étage de l'arbre:
   $flip(1+F_k),...,flip(F_{k+1}) = F_{k+1},...,1+F_k$.
 - Def: $flip(n)=if~n\leq 1~then~n~else~1+F(3+depth(n))-n$.
 - Def: $\overline{G}(n)=flip(G(flip(n)))$
 - Et on montre que ce $\overline{G}$ valide bien l'équation
   précédente, cf `FlipG.v`
   
## Autre résultat principal

Def: $n$ est de rang 3-impair si sa décomposition canonique
commence par $F_3 + F_{2p+1} + ...$.

\bigskip

Thm: $\overline{G}(n)=1+G(n)$ si $n$ est de rang 3-impair,
sinon $\overline{G}(n)=G(n)$.

\bigskip

Preuve: encore pire actuellement que la précédente, pléthore de cas.

\bigskip

Cor: $\overline{G}$ et $G$ diffèrent pour n=7, puis tous les 5 ou 8 entiers.


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

## Conclusions & Perspectives

- On trouve encore des conjectures "abordables" sur OEIS
- Des preuves étonnemment délicates pour de "simples" entiers.
- Merci Coq.
- Preuves papier plus directes ?
- Preuves Coq moins pédestres (quasi 5000 lignes en tout) ?
- Généralisation à $H(n)=n-H(H(H(n-1))$, etc ?
- Fonctions mutuelles d'Hofstadter ($M$ et $F$) ?
- Autres apparitions de $G$ à étudier
  (jeu de Wythoff...)
