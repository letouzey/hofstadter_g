% A family of Hofstadter's recursive functions : more on G and beyond
% Pierre Letouzey
% Journées PPS, 25 juin 2024

## Hofstadter's functions G and H

From Douglas Hofstadter, "Gödel,Escher,Bach", chapter 5 :
\begin{align*}
G &: \mathbb{N} \to \mathbb{N} \\
G(0) &= 0 \\
G(n) &= n - G(G(n-1)) \quad \text{otherwise}
\end{align*}
\begin{align*}
H &: \mathbb{N} \to \mathbb{N} \\
H(0) &= 0 \\
H(n) &= n - H(H(H(n-1))) \quad \text{otherwise}
\end{align*}

In the On-Line Encyclopedia of Integer Sequences (OEIS):

\href{http://oeis.org/A5206}{A5206} and
\href{http://oeis.org/A5374}{A5374}


## Beyond : a family $F_k$ of functions

For any number $k$ of nested recursive calls:
\begin{align*}
F_k &: \mathbb{N} \to \mathbb{N} \\
F_k(0) &= 0 \\
F_k(n) &= n - F_k^{(k)}(n-1) \quad \text{otherwise}
\end{align*}

where $F_k^{(k)}$ is the $k$-th iterate $F_k\circ F_k \circ \cdots \circ F_k$.

In particular, $G = F_2$ and $H = F_3$. 

This is suggested in Hofstadter's text, but does not appear explicitly.

## What about $F_0$ and $F_1$ ?

- $F_0$ is a degenerate, non-recursive situation:

  $F_0(n) = 1$ when $n>0$. 

  Too different from the rest of the $F_k$ family !

  We'll ignore it and \red{only consider $k>0$ from now on}.

\pause

- $F_1$ is simply a division by 2 :

  $F_1(n) = n - F_1(n-1) = 1 + F_1(n-2)$ when $n\ge 2$.

  Actually $F_1(n) = \lfloor (n+1)/2 \rfloor = \lceil n/2 \rceil$.



## Plotting the first $F_k$
\pgfplotsset{width=\linewidth}
\begin{tikzpicture}[scale=1]
  \begin{axis}[
    xmin=0,xmax=30,ymin=0,ymax=25,samples=31,
    xtick = {0,5,...,30},
    ytick = {0,5,...,30},
    %xlabel=$n$,
    legend pos=south east
  ]

 \addplot+[mark=.,color=black,style=dashed,domain=0:30] {x};
% Si on veut mettre les labels directement sur les plot
%\node at (axis cs: 25,24) {$id$};
 \addlegendentry{id \phantom{=G}}
    \addplot [mark=.,color=blue] coordinates {
(0, 0) (1, 1) (2, 1) (3, 2) (4, 3) (5, 4) (6, 5) (7, 6) (8, 6)
 (9, 7) (10, 7) (11, 8) (12, 9) (13, 9) (14, 10) (15, 11) (16, 12)
 (17, 12) (18, 13) (19, 14) (20, 15) (21, 16) (22, 16) (23, 17)
 (24, 18) (25, 19) (26, 20) (27, 21) (28, 21) (29, 22) (30, 23)};
 \addlegendentry{$F_5 \phantom{=G}$}
    \addplot [mark=.,color=purple] coordinates {
(0, 0) (1, 1) (2, 1) (3, 2) (4, 3) (5, 4) (6, 5) (7, 5) (8, 6)
 (9, 6) (10, 7) (11, 8) (12, 8) (13, 9) (14, 10) (15, 11) (16, 11)
 (17, 12) (18, 13) (19, 14) (20, 15) (21, 15) (22, 16) (23, 17)
 (24, 18) (25, 19) (26, 19) (27, 20) (28, 20) (29, 21) (30, 22)};
 \addlegendentry{$F_4 \phantom{=G}$}
    \addplot [mark=.,color=orange] coordinates {
(0, 0) (1, 1) (2, 1) (3, 2) (4, 3) (5, 4) (6, 4) (7, 5) (8, 5)
 (9, 6) (10, 7) (11, 7) (12, 8) (13, 9) (14, 10) (15, 10) (16, 11)
 (17, 12) (18, 13) (19, 13) (20, 14) (21, 14) (22, 15) (23, 16)
 (24, 17) (25, 17) (26, 18) (27, 18) (28, 19) (29, 20) (30, 20) };
 \addlegendentry{$F_3=H$}
 \addplot+[mark=.,color=red,domain=0:30]
 {floor((x+1) * 0.618033988749894903)};
 \addlegendentry{$F_2=G$}
 \addplot+[mark=.,color=black,style=solid,domain=0:30] {ceil(x/2)};
 \addlegendentry{$F_1 \phantom{=G}$}
 \end{axis}
\end{tikzpicture}


## Some early properties of $F_k$

\ensuremath{F_k(n) = n - F_k^{(k)}(n-1)}

 - Well-defined since $0\leq F_k(n) \leq n$
 - $F_k(0)=0$, $F_k(1)=1$ then $n/2 \leq F_k(n)<n$
 - $F_k$ is made of a mix of flats (+0) and steps (+1)
 - Hence each $F_k$ is increasing, onto, but not one-to-one
 - Never two flats in a row
 - At most $k$ steps in a row

## Monotony of the $F_k$ family

Pointwise order for functions : $f\le h \iff \forall n, f(n) \le h(n)$.

\fcolorbox{blue}{white}{Theorem: $\forall k, F_k \le F_{k+1}$}

\pause

 - Conjectured in 2018.
 
 - First proof by Shuo Li (Nov 2023).
 
 - Improved version by Wolfgang Steiner.
 
 - Completely proved in Coq (as most of this talk).

 - Proof ingredient : "detour" via some infinite morphic words.

## More monotony

For $k>0$ and $0\le j \le k$:

\begin{center}
\begin{tikzcd}[ampersand replacement=\&]
  F_{k}^{j} \arrow[r, "\le"]
    \& F_{k+1}^{j} \& \\
  \& F_{k+1}^{j+1}
    \arrow[u, "\ge" {rotate=-90,xshift=0.6em,yshift=0.5em}]
    \arrow[lu, "\ \ge" rotate=-30]
    \arrow[r, "\le"']
    \& F_{k+2}^{j+1} \arrow[lu, "\ \ge"' rotate=-30]
\end{tikzcd}
\end{center}


## More monotony

\begin{center}
\begin{tikzcd}[ampersand replacement=\&]
 \red{F_1=\divi{2}}\rar[red]\dar[leftarrow]
      \& \red{F_2=G}\rar[red]\dar[leftarrow]
      \& \red{F_3=H}\rar[red]\dar[leftarrow]
      \& \red{F_4}\rar[red]\dar[leftarrow]
      \& \red{F_5}\dar[leftarrow] \\
 F_1^2=\divi{4}\rar\dar[leftarrow]
      \& \red{F_2^2=G^2}\rar\dar[leftarrow]
        \ular[red]
      \& F_3^2=H^2\rar\dar[leftarrow]
        \ular
      \& F_4^2\rar\dar[leftarrow]
        \ular
      \& F_5^2 \dar[leftarrow]
        \ular\\
 F_1^3=\divi{8}\rar\dar[leftarrow]
      \& F_2^3=G^3\rar\dar[leftarrow]
        \ular[dotted,"?" description]
      \& \red{F_3^3=H^3}\rar\dar[leftarrow]
        \ular[red]
      \& F_4^3\rar\dar[leftarrow]
        \ular
      \& F_5^3  \dar[leftarrow]
        \ular \\
 F_1^4=\divi{16}\rar\dar[leftarrow]
      \& F_2^4=G^4\rar\dar[leftarrow]
      \& F_3^4=H^4\rar\dar[leftarrow]
        \ular[dotted,"?" description]
      \& \red{F_4^4}\rar\dar[leftarrow]
        \ular[red]
      \& F_5^4  \dar[leftarrow]
        \ular\\
 F_1^5=\divi{32}\rar\dar[white]
      \& F_2^5=G^5\rar\dar[white]
      \& F_3^5=H^5\rar\dar[white]
      \& F_4^5\rar\dar[white]
        \ular[dotted,"?" description]
      \& \red{F_5^5} \dar[white]
        \ular[red] \\[-0.5cm]
    { } \& { } \& { } \& { } \& { }
\end{tikzcd}
\end{center}

## Linear Equivalent

Let $\alpha_k$ be the positive root of $X^{k}+X-1$.

\fcolorbox{blue}{white}{Theorem: 
$\forall k>0$, when $n\to\infty$ we have
$F_k(n) = \alpha_k.n + o(n)$}

## Linear Equivalent

- \ensuremath{F_1(n) = \lfloor (n+1)/2 \rfloor = \lceil n/2 \rceil}

- \ensuremath{G(n) = F_2(n) = \lfloor \alpha_2.(n+1) \rfloor}
  with $\alpha_2 =\phi-1 \approx 0.618...$

No more exact expression based on integral part of affine function.
Instead:

- \ensuremath{H(n) = F_3(n) \in \lfloor \alpha_3.n \rfloor + \{0,1\}}

- \ensuremath{F_4(n) \in \lfloor \alpha_4.n \rfloor + \{-1,0,1,2\}}

- For $k\ge 5$, \ensuremath{F_k(n) -\alpha_k.n} is no longer bounded.

## Rauzy Fractal

Let $\delta(n) = F_3(n) - \alpha_3.n$.
Then plotting $(\delta(i),\delta(F_3(i)))$
 leads to this Rauzy fractal

\includegraphics[width=\linewidth]{fractal.png}

## Quiz !

Let $k>0$. We say that a set of integers $S$ is $k$-sparse if two
distinct elements of $S$ are always separated by at least $k$.
How many $k$-sparse subsets of $\{1..n\}$ could you form ?


## Generalized Fibonacci

For $k>0$:
\begin{equation*}
\begin{cases}
A_{k,n} &= n+1 \hfill \text{when}\ n\le k \spa \\
A_{k,n} &= A_{k,n-1} + A_{k,n-k} \spa \text{when}\ n\ge k \spa
\end{cases}
\end{equation*}

\ski
\pause

- $A_{1,n}$ : \textcolor{red}{1}  2  4  8  16  32  64  128  256  512
  $\ldots$ (Powers of 2)
  
- $A_{2,n}$ : \textcolor{red}{1  2}  3  5  8  13  21  34  55  89 $\ldots$
  (Fibonacci )
  
- $A_{3,n}$ : \textcolor{red}{1  2  3}  4  6  9  13  19  28  41 $\ldots$
  (Narayana's Cows)
  
- $A_{4,n}$ : \textcolor{red}{1  2  3  4}  5  7  10  14  19  26 $\ldots$

## Zeckendorf decomposition

Let $k>0$.

\fcolorbox{blue}{white}{
\begin{minipage}{0.9\linewidth}
Theorem (Zeckendorf): all natural number can be written
as a sum of $A_{k,i}$ numbers.
This decomposition is unique when its indices $i$ form a $k$-sparse set.
\end{minipage}
}

\fcolorbox{blue}{white}{
\begin{minipage}{0.9\linewidth}
Theorem: $F_k$ is a right shift for such a decomposition :
 $F_k(\Sigma A_{k,i}) = \Sigma A_{k,i-1}$
(with the convention $A_{k,0-1} = A_{k,0} = 1$)
\end{minipage}
}

NB: This shifted decomposition might not be $k$-sparse anymore

Key property : $F_k$ is "flat" at $n$ iff the decomposition of $n$ contains $A_{k,0}=1$.

More generally, $F_k^{(j)}$ is "flat" at $n$ iff $j>rank(n)$ where the
rank of $n$ is the smallest index in the decomposition of $n$.


## A letter substitution

Let $k>0$.
We use $\mathcal{A}=[1..k]$ as alphabet.
\begin{align*}
            & \mathcal{A} \to \mathcal{A}^* \\
\tau_k(n) &= (n+1) & \text{pour}\ n<k \\
\tau_k(k) &= k.1
\end{align*}

Starting from letter $k$, this generates an infinite word $x_k$
(this word is said \emph{morphic}).

For instance $x_3 = 3123313123123312331312331312312331312312\cdots$

## Recursive equation on words

$x_k$ is the limit of $\tau_k^n(k)$ when $n\to\infty$

It is also the limit of the following prefixes $M_{k,n}$:

- $M_{k,n}=k.0...(n-1)$ when $n\le k$
- $M_{k,n}=M_{k,n-1}.M_{k,n-k}$ when $k\le n$

\pause
Note: $|M_{k,n}| = A_{k,n}$

## Link with $F_k$

The $n$-th letter lettre $x_k[n]$ of the infinite word $x_k$ is
$\min(1{+}rank(n),k)$.

In particular this letter is 1 iff $F_k(n)=F_k(n+1)$

The count of letter 1 in $x_k$ between 0 and $n-1$ is $n-F_k(n)$.

More generally, counting letters above $p$ gives
$F_k^{(p)}$. In particular the count of letter $k$ is $F_k^{(k-1)}$.

## No time today for:

- $F_k$ admits a right adjoint (Galois connection), and this function
  behave as a left shift on the previous decompositions.

- A variant of $F_k$ is already known to be a more conventional right
  shift on these decompositions (Meek \& van Rees, 1981).

- An algebraic expression for $A_{k,n}$ fully based on the roots
  of $X^k-X^{k-1}-1$.

- ...

## Thank you for your attention


Coq Development : <https://github.com/letouzey/hofstadter_g>
