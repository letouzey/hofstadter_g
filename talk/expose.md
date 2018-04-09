% Un problème d'Hofstadter pour ses lecteurs curieux
% Pierre Letouzey
% 10 avril 2018

https://github.com/letouzey/hofstadter_g

## Aparté : Fibo Folie

~~~ocaml
let rec f n l a = match n,l with
 | (0|1), [] -> succ a
 | (0|1), m::l -> f m l (succ a)
 | _ -> f (n-1) (n-2 :: l) a
let fibo n = f n [] 0
~~~

## Un arbre auto-similaire

Douglas Hofstadter, "Gödel,Escher,Bach", p.135

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
       [.$\circ$ [.$\circ$ [.$\circ$ [.$\circ$ G G ] [.$\circ$ G ] ]
               [.$\circ$ [.$\circ$ G G ]]]
           [.$\circ$ [.$\circ$ [.$\circ$ G G ] [.$\circ$ G ]]]]
       [.$\circ$ [.$\circ$ [.$\circ$ [.$\circ$ G G ] [.$\circ$ G ]]
               [.$\circ$ [.$\circ$ G G ]]]]]
\end{tikzpicture}

Combien de noeuds par niveau ?

## Numérotons ! (en largeur, par la gauche)

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


## Aparté (2) : arbre de fonction, fonction d'arbre

Soit un arbre:

 - infini
 - dont les noeuds ont des arités finies non nulles
 - numéroté en parcours en largeur

Que peut-on dire de sa fonction parent ?

\bigskip

Recip. que faut-il sur une fonction $\mathbb{N}\to \mathbb{N}$ pour
qu'elle soit la fonction parent d'un et un seul tel arbre ?

## Aparté (2) : arbre de fonction, fonction d'arbre

 - f croissante
 - f(n)<n hormis à la racine
 - f surjective
 - f ne stationne pas (i.e. tend vers $+\infty$)

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
 - le rang diminue (par pas de 2) ou stagne

## Retour sur G

\ensuremath{G(n) = n - G(G(n-1))}

 - Existence + encadrement $0\leq G(n) \leq n$
 - G "avance" par pas de 0 ou 1
 - Après un pas à 0, forcément un pas de 1
 - $G(0)=0$, $G(1)=1$ puis $1\leq G(n)<n$

## G et Fibonacci

 - \ensuremath{G(F_i) = F_{i-1}}
 - Plus généralement: $G(\Sigma F_i) = \Sigma G(F_{i-1})$


## Et en Coq ?



