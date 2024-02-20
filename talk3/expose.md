% Fonction G de Hofstadter et au-delà: un exemple curieux mêlant calculs et preuves sur ordinateur
% Pierre Letouzey (IRIF, UPC, Inria)
% FSMP, 2 décembre 2023

## Avertissement : la préparation de cet exposé a subi...

La loi d'Hofstadter : il faut toujours plus longtemps que prévu, même en tenant compte de la loi d'Hofstadter.

## Prélude : une première fonction récursive

Que dire de la fonction $d : \mathbb{N}\to\mathbb{N}$ définie ainsi ?
\begin{equation*}
\begin{cases}
d(0) = 0 \\
d(1) = 0 \\
d(n) = 1 + d(n-2) \spa \text{pour}\ n\ge 2 \spa
\end{cases}
\end{equation*}

\pause

\begin{tabular}{c|cccccccc}
$n$    & 0 & 1 & 2 & 3 & 4 & 5 & 6 & \ldots \\
\hline
$d(n)$ & 0 & 0 & 1 & 1 & 2 & 2 & 3 & \ldots
\end{tabular}

\ski

\pause

En fait $d(n) = \lfloor n/2 \rfloor$ (arrondi à l'entier inférieur).

\pause

Justification : par récurrence !

## Plus délicat : soustrayons !

Que dire de la fonction $f_0 : \mathbb{N}\to\mathbb{N}$ définie ainsi ?
\begin{equation*}
\begin{cases}
f_0(0) = 0 \\
f_0(n) = n - f_0(n-1) \spa \text{pour}\ n\ge 1 \spa
\end{cases}
\end{equation*}

\pause

\begin{tabular}{c|cccccccc}
$n$    & 0 & 1 & 2 & 3 & 4 & 5 & 6 & \ldots \\
\hline
$f_0(n)$ & 0 & 1 & 1 & 2 & 2 & 3 & 3 & \ldots
\end{tabular}

\ski

\pause

En fait $f_0(n) = d(n+1) = \lfloor (n+1)/2 \rfloor$.

\pause

Autre écriture possible $f_0(n) = \lceil n/2 \rceil$
(arrondi à l'entier supérieur).

\pause

Justification : si $n-1\ge 1$, on "re-expanse" $f_0(n-1)$ :
$$f_0(n) = n - ((n-1) - f_0(n-2)) = 1+f_0(n-2)$$




## La fonction G d'Hofstadter

Douglas Hofstadter définit au chap. 5 de "Gödel,Escher,Bach" :
\begin{equation*}
\begin{cases}
G(0) = 0 \\
G(n) = n - G(G(n-1)) \spa \text{pour}\ n\ge 1 \spa
\end{cases}
\end{equation*}

\pause

\begin{tabular}{c|ccccccccccccc}
$n$    & 0 & 1 & 2 & 3 & 4 & 5 & 6 & 7 & 8 & 9 & \ldots & 13 & \ldots\\
\hline
$G(n)$ & 0 & 1 & 1 & 2 & 3 & 3 & 4 & 4 & 5 & 6 & \ldots & 8 & \ldots
\end{tabular}

\ski
\pause

Remarque: $G$ semble transformer tout nombre de Fibonacci $F_i >1$
en le précédent (on y reviendra):
$$G(F_i) = F_{i-1}$$


## Quelques premières propriétés de G

 - Existence et premier encadrement: $0\leq G(n) \leq n$.
 - $G(0)=0$, $G(1)=1$ puis $1\leq G(n)<n$.
 - A chaque étape, $G$ "monte" (de +1) ou "stagne" (+0).
 - Jamais deux +0 de suite.
 - Jamais trois +1 de suite.

\ski
\pause

Ici en fait : $G(n)=\lfloor (n+1)/\varphi \rfloor$

où $\varphi = (1+\sqrt 5)/2 \approx 1.618$ est le nombre d'or

et $1/\varphi = \varphi-1 \approx 0.618$.

\pause

Arrondi de droite à pente irrationnelle : voir les \emph{mots sturmiens}.


## Tracés de $G(n)$ et $(n+1)/\varphi$ :

\begin{tikzpicture}[scale=1.2]
  \begin{axis}[
    xmin=0,xmax=14,ymin=0,ymax=10,samples=15,
    xlabel=$n$,
  ] 
    \addplot+[dashed,mark=.,domain=0:14] {(x+1) * 0.618033988749894903}; 
    \addplot+[domain=0:14] {floor((x+1) * 0.618033988749894903)}; 
  \end{axis}
\end{tikzpicture}

## Généralisons : la fonction H

Comme Hofstadter, varions le nombre d'appels imbriqués:
\begin{equation*}
\begin{cases}
H(0) = 0 \\
H(n) = n - H(H(H(n-1)) \spa \text{pour}\ n\ge 1 \spa
\end{cases}
\end{equation*}

\ski
\pause

Mêmes propriétés de base que $G$, sauf que:

 - Au plus trois +1 successifs
 - Pas d'équation simple et exacte à base de $\lfloor ~ \rfloor$
 - Par contre: $H(n) = \lfloor \tau n \rfloor + 0 ~\text{ou}~ 1$
 
   avec $\tau \approx 0.6823$ racine réelle de $X^3+X-1$

## Surprise !

Posons $\delta(n) = H(n) - \tau.n$

Affichage des points $(\delta(i),\delta(H(i))$ avec i=0..10000

\includegraphics[width=\linewidth]{fractal.png}

## Fractale de Rauzy et variantes

 - Fractale précédente déjà connue, mais obtenue différemment.

 - Variante de la fractale de Rauzy, via une autre
   variante de Fibonacci et un autre nombre de Pisot-Vijayaraghavan,
   mais l'étude est similaire.

Références:

 - G. Rauzy, \emph{Nombres algébriques et substitutions}, 1982.
 - N. Pytheas Fogg, \emph{Substitutions in Dynamics, Arithmetics and
 Combinatorics}, 2002


## Généralisons encore : une famille de fonctions $f_k$

Notons $k+1$ le nombre d'appels récursifs souhaités. On définit:
\begin{equation*}
\begin{cases}
f_k(0) = 0 \\
f_k(n) = n - \smash{\underbrace{f(\cdots f}_{k+1}}(n-1)\cdots) \spa \text{pour}\ n\ge 1 \spa\!
\end{cases}
\end{equation*}

\ski
\pause

On retrouve les cas particuliers précédents :

 - $f_0 = \lfloor (n+1)/2 \rfloor$ avec un seul appel récursif
 
 - $f_1 = G$ avec deux appels récursifs
 
 - $f_2 = H$ avec trois appels récursifs

## Tracés

\begin{tikzpicture}[scale=1.2]
  \begin{axis}[
    xmin=0,xmax=30,ymin=0,ymax=20,samples=31,
    xlabel=$n$, legend pos=south east
  ] 
 \addplot+[mark=.,color=black,style=dashed,domain=0:30] {x};
 \addlegendentry{id}
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
 \addlegendentry{$G$}
 \addplot+[mark=.,domain=0:30] {ceil(x/2)}; 
 \addlegendentry{$f_0$}
 \end{axis}
\end{tikzpicture}

## Premières propriétés de $f_k$

 - Existence et premier encadrement: $0\leq f_k(n) \leq n$
 
 - $f_k(0)=0$, $f_k(1)=1$ puis $1\leq f_k(n)<n$
 
 - A chaque étape, $f_k$ "monte" (de +1) ou "stagne" (+0).
 
 - Jamais deux +0 de suite
 
 - Au plus $k+1$ montées +1 de suite

Nota: pour $k\ge 2$, $f_k(n)$ n'a pas d'expression exacte via $\lfloor~ \rfloor$.

## De la science toute récente !

\fcolorbox{blue}{white}{Théorème: pour tous $k$ et $n$, on a $f_k(n) \le f_{k+1}(n)$}

Bref, $f_0$ est partout en dessous de $G$, qui est en dessous de $H$, etc

\pause

 - Conjecturé en 2018.
 
 - Coeur de la preuve par Shuo Li il y a 15 jours !
 
 - Version certifiée sur machine cette semaine (preuve Coq) !

 - Preuve par reformulation en un problème de mots infinis.

##
\section{Partie 2 : Fibonacci généralisé et numération}

## Les nombres de Fibonacci

\begin{equation*}
\begin{cases}
F_0 &= 1 \\
F_1 &= 2 \\
F_{n+2} &= F_n + F_{n+1} \spa\spa\spa
\end{cases}
\end{equation*}

\ski
\pause
 $(F_i)$ :  1  2  3  5  8  13  21  34  55  89 $\ldots$

\ski

NB: définition inhabituelle, pas de 0, un seul 1.

## Théorème de Zeckendorf

\fcolorbox{blue}{white}{
\begin{minipage}{0.9\linewidth}
Théorème (Zeckendorf): tout nombre entier peut s'écrire comme somme
de nombres de Fibonacci tous différents et sans voisins. Cette
décomposition est unique.
\end{minipage}
}

Par exemple: $17 = 13 + 3 + 1 = F_5 + F_2 + F_0$

On écrit alors parfois $17 = {100101}_{F}$

\begin{tabular}{lcr@{\spa}|lcr}
1 & = & ${1}_F$      & 7 & = & ${1010}_F$ \\
2 & = & ${10}_F$     & 8 & = & ${10000}_F$ \\
3 & = & ${100}_F$    & 9 & = & ${10001}_F$ \\
4 & = & ${101}_F$    & 10 & = & ${10010}_F$ \\
5 & = & ${1000}_F$   & 11 & = & ${10100}_F$ \\
6 & = & ${1001}_F$   & 12 & = & ${10101}_F$ \\
\end{tabular}

## G et Fibonacci

 - \ensuremath{G(F_i) = F_{i-1}} (avec la convention \ensuremath{F_{0-1}=F_0=1})
\pause

 - Et même, $G$ décale les décompositions:
 $G(\Sigma F_i) = \Sigma F_{i-1}$
\pause

 - Propriété cruciale, preuve délicate

 - Exemple: $G(17) = G(100101_F) = 10011_F = 11$

 - Voisins possibles dans la décomposition obtenue, on
   peut la \emph{renormaliser} ensuite, p.ex. $10011_F = 10100_F = 11$

 
## Fibonacci généralisé

Soit $k$ un entier naturel. On définit:
\begin{equation*}
\begin{cases}
A^k_n &= n+1 \hfill \text{pour}\ n\le k \spa \\
A^k_{n+1} &= A^k_{n} + A^k_{n-k} \spa \text{pour}\ n\ge k \spa
\end{cases}
\end{equation*}

\ski
\pause

- $A^0$ : \textcolor{red}{1}  2  4  8  16  32  64  128  256  512
  $\ldots$ (Puissances de 2)
  
- $A^1$ : \textcolor{red}{1  2}  3  5  8  13  21  34  55  89 $\ldots$
  (Fibonacci $F_i$)
  
- $A^2$ : \textcolor{red}{1  2  3}  4  6  9  13  19  28  41 $\ldots$
  (Narayana's Cows)
  
- $A^3$ : \textcolor{red}{1  2  3  4}  5  7  10  14  19  26 $\ldots$

## Zeckendorf généralisé

Soit $k$ un entier naturel.

\fcolorbox{blue}{white}{
\begin{minipage}{0.9\linewidth}
Théorème (Zeckendorf): tout nombre entier peut s'écrire comme somme
de nombres $A^k_i$ dont les indices diffèrent tous d'au moins $k+1$.
Cette décomposition est unique.
\end{minipage}
}

\fcolorbox{blue}{white}{
\begin{minipage}{0.9\linewidth}
Théorème: $f_k$ décale cette décomposition :
 $f_k(\Sigma A^k_i) = \Sigma A^k_{i-1}$
(toujours avec la convention $A^k_{0-1} = A^k_0 = 1$)
\end{minipage}
}

Là encore, $f_k$ dénormalise au passage certaines décompositions.

Important: $f_k$ "stagne" en $n$ lorsque $n$ contient $A^k_0=1$ dans
sa décomposition.

##
\section{Partie 3 : Lien avec des mots infinis}

## Une substitution de lettres

Soit k un entier naturel.
On utilise $\mathcal{A}=[0..k]$ comme alphabet et on définit
une \emph{substitution} $\sigma_k : \mathcal{A} \to \mathcal{A}^*$ ainsi:

\begin{equation*}
\begin{cases}
\sigma_k(n) = (n+1) \spa \text{pour}\ n<k \\
\sigma_k(k) = k.0
\end{cases}
\end{equation*}


Ceci engendre un mot infini $m_k$ à partir de la lettre $k$
(on parle de mot \emph{morphique})

Par exemple:

 - $m_1 = 1011010110110...$ (dual du mot de Fibonacci)

 - $m_2 = 20122020120122012202...$

## Vision par blocs de lettres

Si l'on découpe $m_k$ à chaque lettre $k$ et que l'on marque la taille
des blocs entre ces $k$, on réobtient $m_i$.

Exemple: 

\begin{tabular}{ccccccc}
$m_2$ & = & \textcolor{red}{2}01 &
          \textcolor{red}{2} &
          \textcolor{red}{2}0 & 
          \textcolor{red}{2}01 & 
          \textcolor{red}{2}01... \\
    & = & 2 & 0 & 1 & 2 & 2...
\end{tabular}

\pause

A contrario, ceci donne une méthode d'expansion de $m_k$
(c'est en fait la substitution $(\sigma_k)^k$).

## Equation récursive alternative

$m_k$ est la limite de $\sigma_k^n(k)$ quand $n\to\infty$

Mais aussi la limite de préfixes finis $M_{k,n}$ définis ainsi:

- $M_{k,n}=k.0...(n-1)$ pour $n\le k$
- $M_{k,n+1}=M_{k,n}.M_{k,n-k}$ pour $k\le n$

\pause
Remarque : $|M_{k,n}| = A^k_n$

## Lien avec $f_k$

\fcolorbox{blue}{white}{
\begin{minipage}{0.9\linewidth}
Theorème : si l'on projette vers 1 chaque lettre non-nulle de $m_k$,
on obtient le mot infini des montées et des plats de $f_k$
\end{minipage}}

Autrement dit, $f_k$ stagne là il y a des $0$ dans $m_k$.

Et en cumulant: le nombre de 0 dans $m_k$ parmi ses $n$ premières
lettres donne $n-f_k(n)$.

##
\section{Partie 4 : Formalisation sur machine}

## Comment définir $f_k$ en Coq ?

Voir <https://github.com/letouzey/hofstadter_g>

\footnotesize
```coq
Fixpoint recf k p n :=
 match p, n with
 | S p, S n => S n - Nat.iter (S k) (recf k p) n
 | _, _ => 0
 end.

Definition f k n := recf k n n.

Lemma f_k_0 : forall k, f k 0 = 0.
Proof.
 intro. compute. reflexivity.
Qed.

Lemma f_pred : forall k n, f k n = n - Nat.iter (S k) (f k) (n-1).
Proof.
 ...
Qed.
```


## Quelques énoncés prouvés en Coq

Voir <https://github.com/letouzey/hofstadter_g>

\footnotesize
```coq
(* Action de f_k sur la décomposition de n en sommes de k-bonacci *)
Lemma f_decomp : forall k n, f k n = sumA k (map pred (decomp k n)).
Proof.
 ...
Qed.

(* Proximité entre H = f 2 et son approximation linéaire *)
Lemma h_natpart_or :
 forall n, h n = nat_part (tau*n) \/ h n = S (nat_part (tau*n)).
Proof.
 ...
Qed.

(* Monotonie de la famille de fonctions f_k *)
Theorem f_grows : forall k n, f k n <= f (S k) n.
Proof.
 ...
Qed.
```

## Bilan

- Au tout début: une plage, un livre, du papier !

- Il reste encore des territoires à défricher, même d'approche
  élémentaire.

- Le calcul sur machine est essentiel pour affiner ses intuitions

- Des preuves rapidement trop longues/complexes pour être
  totalement fiabilisées par relecture humaine.
  
- Preuve sur machines : ardu, coûteux, mais faisable et gratifiant

##
\section{Questions ?}

##
\section{Partie 5 : G vu comme arbre infini}

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

## Numérotons les noeuds !

Parcours en largeur, de gauche à droite

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
Départ à 3 ? Pour faire apparaître les nombres de Fibonacci...

Théorème: le noeud $n$ a $G(n)$ comme ancêtre.

## Ajout d'un tronc : l'arbre de G

\begin{tikzpicture}[grow'=up]
\Tree
 [.1 [.2 [.3
       [.4 [.6 [.9 [.14 22 23 ] [.15 24 ] ]
               [.10 [.16 25 26 ]]]
           [.7 [.11 [.17 27 28 ] [.18 29 ]]]]
       [.5 [.8 [.12 [.19 30 31 ] [.20 32 ]]
               [.13 [.21 33 34 ]]]]]]]
\end{tikzpicture}

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

Et encore un tronc sur mesure (1 puis $k+1$ segments)

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
