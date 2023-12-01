% Fonction G de Hofstadter et au-delà: un exemple curieux mêlant calculs et preuves sur ordinateur
% Pierre Letouzey
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

Ainsi, le noeud $n$ a $G(n)$ comme parent.

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


## Fibonacci généralisé

Soit $k$ un entier naturel.

\begin{align*}
A^k_0 &= 1 \\
A^k_1 &= 2 \\
... \\
A^k_{k} &= k+1 \\
A^k_{n+1} &= A^k_{n} + A^k_{n-k} & \text{pour}\ n\ge k
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

$k$-décomposition $n = \Arest$ est *canonique* : indices distants $\ge (k+1)$

$k$-décomposition *relachée* : indices distants d'au moins $k$

\pause
\bigskip

Thm: tout entier naturel a une unique $k$-décomposition canonique.

Algo: on peut "renormaliser" une $k$-décomposition relachée.

## Un peu d'arithmétique avec ces décompositions

La décomposition de $n+1$ et $n-1$ peut s'obtenir raisonnablement bien
à partir de celle de $n$. 

Par contre pas d'addition, multiplication, etc.



## $f_k$ et Fibonacci généralisé

 - \ensuremath{f_k(A^k_i) = A^k_{i-1}} (avec la convention \ensuremath{A^k_{0-1}=A^k_0=1})
\pause
 - Plus généralement: $f_k(\Sigma A^k_i) = \Sigma A^k_{i-1}$
\pause
 - Cela marche pour des décompositions canoniques ou relachées
 - Important : $f_k$ "stagne" en $n$ lorsque le rang de $n$ est 0
   (i.e. lorsque $n$ a 1 dans sa décomposition)


##
\section{Lien avec des mots morphiques}

## Une substitution de lettres

Soit k un entier naturel.
On utilise $\mathcal{A}=[0..k]$ comme alphabet.

\begin{align*}
            & \mathcal{A} \to \mathcal{A}^* \\
\sigma_k(n) &= (n+1) & \text{pour}\ n<k \\
\sigma_k(k) &= k.0
\end{align*}

Ceci engendre un mot infini $m_k$ à partir de la lettre $k$
(on parle de mot \emph{morphique})

Par exemple $m_2 = 20122020120122012202...$

## Equation récursive

$m_k$ est la limite de $\sigma_k^n(k)$ quand $n\to\infty$

Mais aussi la limite de préfixes finis $M_{k,n}$ définis ainsi:

- $M_{k,n}=k.0...(n-1)$ pour $n\le k$
- $M_{k,n+1}=M_{k,n}.M_{k,n-k}$ pour $k\le n$

\pause
Remarque : $|M_{k,n}| = A^k_n$

## Lien avec $f_k$

La $n$-ième lettre $(m_k)_n$ du mot infini $m_k$ est le rang de la
$k$-decomposition de $n$ (ou $k$ si ce rang est plus de $k$).

En particulier cette lettre est 0 si $f_k(n)=f_k(n+1)$

En cumulant : le nombre de 0 dans $m_k$ entre 0 et $n$ est $n-f_k(n)$.

Plus généralement, compter les lettres au dessus de $p$ donne
$f_k^{(p)}$. En particulier le nombre de $k$ est $f_k^{(k)}$.

## Fréquences ?

Quelle limite pour $f_k(n)/n$ lorsque $n\to \infty$ ?

 - Si elle existe, facile à déterminer, racine positive de $X^{k+1}+X-1$.
 - Preuve d'existence non triviale
 
Cf. K. Saari, \emph{On the Frequency of Letters in Morphic Sequences}.

En Coq, il fallait déjà parler de racines, et d'équivalent infini de
suites linéaires comme $A^k$.

De fil en aiguille, preuve de la formule de Leibniz du determinant et
determinant des matrices de Vandermonde...

Assure la croissance des $f_k$ pour $n$ suffisemment grand.

##
\section{Cas k=2 (i.e. H)}


## Surprise il y a quelques années

Affichage des points $(\delta(i),\delta(H(i))$ avec i=0..10000
et $\delta(n) = H(n) - n.\tau_2$


\includegraphics[width=\linewidth]{fractal.png}

## Fractale de Rauzy et variante

Apparemment, la factale précédente est nommée Jacobi-Perron, proche de
la fractale de Rauzy.

G. Rauzy, \emph{Nombres algébriques et substitutions}, 1982

- Dans son cas, suites de Tribonacci additionnant les trois derniers
termes
- Ici on additionne dernier et avant-avant-dernier termes

L'étude est très similaire.

## Application ici

On obtient finalement:

- $|H(n) - n.\tau_2|<0.996<1$
- Et donc $H(n) = \lfloor n.\tau_2 \rfloor + 0~\text{ou}~1$
- Et quasi-additivité de $H$ :
  $\forall n m, -2 \le H(n+m)-H(n)-H(m) \le 2$

## Nombres de Pisot

Dixit Wikipédia: En mathématiques, un nombre de Pisot-Vijayaraghavan
 est un entier algébrique réel strictement supérieur à 1, dont tous
 les éléments conjugués ont un module strictement inférieur à 1.

Ici la limite $\tau_2$ de $H(n)/n$ est la racine positive de $X^3+X-1$
mais aussi l'inverse de la racine positive de $X^3-X^2-1$ qui est le
nombre de Pisot $P_3$.



##
\section{Cas k=3, Pisot sans jolie fractale...}

## Résultat principal pour k=3

En suivant le même cheminement (pas encore formalisé en Coq)

- $|f_3(n) - n.\tau_3|<1.998$
- Et donc $-1 \le f_3(n) - \lfloor n.\tau_3 \rfloor \le 2$
- Et quasi-additivité de $f_3$ :
  $\forall n m, -5 \le H(n+m)-H(n)-H(m) \le 5$


##
\section{Cas k>3, $f_k(n) - n.\tau_k$ diverge}


## Et en Coq ?

Cf `FunG.v FunG_prog.v GenG.v` :

- Décroissance non structurelle : pas de `Fixpoint` Coq ainsi
- Spécification via un prédicat inductif
- `recf` : une définition remaniée avec un compteur `p`
- Possibilité d'utiliser `Program Fixpoint` (mais lourd)
- Plus rapide : `fopt` fonctionnant par table




## Conclusions & Perspectives

- On trouve encore des conjectures "abordables" sur OEIS
- Et aussi parfois des petites choses fausses...
\pause
- Des preuves étonnemment délicates pour de "simples" entiers.
- Merci Coq !
- Peut-on éviter ces "détours" via $\mathbb{R}$ et $\mathbb{C}$ ?
- Quid de la conjecture ?
- Des questions restantes concernant l'irréductibilité des polynômes rencontrés


## Code Coq + cet exposé + ancien rapport technique

<https://github.com/letouzey/hofstadter_g>

