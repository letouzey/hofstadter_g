
(** utils *)

let extrems tab =
  let mi = ref tab.(0) and ma = ref tab.(0) in
  Array.iter (fun x -> mi := min x !mi; ma := max x !ma) tab;
  !mi, !ma

let rec iter f n = if n=0 then fun x -> x else fun x -> iter f (n-1) (f x)

(** applying and repeating substitution *)

let dosubst f w =
  (* naive code : List.flatten (List.map f w) *)
  let rec loop acc = function
    | [] -> List.rev acc
    | a::w -> loop (List.rev_append (f a) acc) w
  in loop [] w

let itersubst f n init = iter (dosubst f) n init

(* Almost List.for_all2, but ok when different sizes (discard the leftover) *)
let rec myforall2 f u v =
  match u,v with
  | x::u, y::v -> f x y && myforall2 f u v
  | _ -> true

(** the recursive functions [f k], with [k+1] nested calls *)

let rec f k n = if n = 0 then 0 else n - iter (f k) (k+1) (n-1)

let f0 = f 0 (* d *)
let f1 = f 1 (* g, cf http://oeis.org/A005206 *)
let f2 = f 2 (* h, cf http://oeis.org/A005374 *)
let f3 = f 3 (* http://oeis.org/A005375 *)

(** Tabulate : Faster computation of [f k n] via an array
    - First line (k=0) is function d (division by two)
    - Second line (k=1) is function g
    - Third line (k=2) is function h
*)

let tabulate k n =
  let a = Array.make_matrix (k+1) (n+1) 0 in
  for i = 0 to k do
    for j = 1 to n do
      let x = ref (j-1) in
      for p = 0 to i do
        x := a.(i).(!x)
      done;
      a.(i).(j) <- j - !x
    done
  done;
  a

let a = tabulate 10 1000000
let a0 = a.(0)
let a1 = a.(1)
let a2 = a.(2)
let a3 = a.(3)
let a4 = a.(4)
let a5 = a.(5)

(* Increments *)

let delta a =
  let h,w = Array.length a, Array.length a.(0) in
  let d = Array.make_matrix h (w-1) 0 in
  for i = 0 to h-1 do
    for j = 0 to w-2 do
      d.(i).(j) <- a.(i).(j+1)-a.(i).(j)
    done
  done;
  d

let d = delta a
let d0 = d.(0)
let d1 = d.(1)
let d2 = d.(2)
let d3 = d.(3)
let d4 = d.(4)

(* Consecutive [+1] steps bewteen flat [+0] *)

let nbsteps array =
  let l = ref [] in
  let p = ref (-1) in
  for i = 0 to Array.length array -1 do
    if array.(i) = 0 then begin
        l := i - !p - 1 :: !l;
        p := i
      end
  done;
  List.rev !l

let steps1 = nbsteps d1

let subst1 = function 1->[1;2] | 2->[1;2;2] | _ -> []

let _ = itersubst subst1 2 [2]

let _ = myforall2 (=) steps1 (itersubst subst1 15 [1])

let subst1red = function 2->[2;1] | 1->[2] | _ -> []

(* 1->12  2->122

1
12
12122
1212212122122

Cf fibonacci word 0->01 1->0, en jetant le premier 1,
 et en écrivant 0 pour les 2.
 Donc : 2->21 1->2 et lettre initiale 2.
 Croissance plus lente

 2
 21
 212
 21221
 21221212
 2122121221221

Sous cette forme, mot M(n+1) = Mn @ M(n-1)

*)

let steps2 = nbsteps d2

let subst2 = function 1->[1;3] | 2 -> [1;2;3] | 3 -> [1;2;3;3] | _ -> []

let _ = myforall2 (=) steps2 (itersubst subst2 12 [1])

let subst2red = function 3 -> [3;1] | n -> [n+1]

(* 1->13 2->123 3->1233

1
13
131233
1312331312312331233

Cf modified Jacobi-Perron subst (livre Pytheas Fogg p. 254) :
1->12 2->3 3->1

Ici on adapte (par renommage) en:
3->31 1->2 2->3

Donne encore la suite précédente moins premiere lettre

 3
 31
 312
 3123
 312331
 312331312
 3123313123123

Sous cette forme, mot M(n+1) = Mn @ M(n-2)

*)

let _ = List.iter print_int @@ itersubst (function 3->[3;1]|n ->[n+1]) 6 [3]

let steps3 = nbsteps d3

let subst3 = function
  | 1 -> [1;4]
  | 2 -> [1;2;4]
  | 3 -> [1;2;3;4]
  | 4 -> [1;2;3;4;4]
  | _ -> []

let _ = myforall2 (=) steps3 (itersubst subst3 11 [1])

let _ = List.length (itersubst subst3 11 [1])

(* Version réduite : 4->41 1->2 2->3 3->4 *)

let subst3red = function 4 -> [4;1] | n -> [n+1]

let _ = List.map (itersubst subst3red 6) [[1];[2];[3];[4]]


let _ = List.iter print_int @@ itersubst subst3 3 [1]
(* 14123441412412341234412344 *)

let _ = List.iter print_int @@ itersubst subst3red 9 [4]
(*  41234414124123412344123441 *)

let steps4 = nbsteps d4

let subst4 = function
  | 1 -> [1;5]
  | 2 -> [1;2;5]
  | 3 -> [1;2;3;5]
  | 4 -> [1;2;3;4;5]
  | 5 -> [1;2;3;4;5;5]
  | _ -> []

let _ = myforall2 (=) steps4 (itersubst subst4 10 [1])

let steps10 = nbsteps d.(10)

let rec seq a b = if b=0 then [] else a::seq (a+1) (b-1)
let _ = seq 1 10

let subst10 n = seq 1 n @ [11]

let _ = itersubst subst10 8 [1]
let _ = myforall2 (=) steps10 (itersubst subst10 8 [1])

let subst10red = function 11 -> [11;1] | n -> [n+1]

let _ = myforall2 (=) (List.tl steps10) (itersubst subst10red 70 [11])


(* TODO :
   x preuve lien subst/substred ?
   x approche directe substred en lien avec fk ?
     Oui, en regardant =+ vs. =++ vs. =+++ au premier niveau
   - lien avec figure fractale Jacobi-Perron ?
   - proximité avec n*root(X^k...) ?
   x limite fk(n)/n
   - quasi additivité ?
   - croissance des fk avec k
 *)

(**********************************)



(* Potentially interesting upper-bound of g :
   - starts as g for the 8 first values, then shifts by +5 every 8 steps
   - this amonts to putting a unary node more frequently than g
     (or for gg, a double value every 3 instead of every 2 ou 3:
      111 22 333 444 55 666 777 88 999)
*)

(* let rec mino_gg n = if n <= 8 then g(g(n)) else 3+mino_gg (n-8) *)
let rec majo_g n = if n <= 8 then g n else 5+majo_g(n-8)
let rec majo_g_bis n = g (n mod 8) + 5*(n/8)

(* This is indeed an upper bound for g *)
let diff1 = Array.init 100000 @@ fun n -> (majo_g_bis n - a1.(n))
let _ = extrems diff1

(* And also a lower bound for h :-) *)
let diff2 = Array.init 100000 @@ fun n -> (majo_g_bis n - a2.(n))
let _ = extrems diff2

(* More generally,
   g(n+2)>=g(n)+1
   g(n+3)<=g(n)+2
   g(n+5)>=g(n)+3
   g(n+8)<=g(n)+5
   g(n+13)>=g(n)+8
   g(n+21)<=g(n)+13
   ...
*)

let _ = Array.init 30 @@
        fun i ->
        (i,extrems (Array.init 900000 @@ fun n -> a1.(n+i)-a1.(n)-a1.(i)))

(* Proved : g(n+p)-g(n)-g(p) = {-1,0,1}    (proof via g(n) = floor(tau*(n+1)))
   Proved : g(n+p)-g(n)-g(p) = 0 when parity(n)<>parity(p)
                                = {-1,0} when parity(n)=parity(p)=even
                                = {0,1} when parity(n)=parity(p)=odd
    where parity(n) is the parity of lowest F_k in the Zeckendorf decomposition
    of n (convention 1 = F_2, no use of F_1 here)
*)

let _ =
  print_newline();
  for i=0 to 20 do
    for j=0 to 20 do
      let d = a1.(i+j)-a1.(i)-a1.(j) in
      print_string
        (match d with
         | 0 -> "= "
         | 1 -> "+ "
         | -1 -> "- "
         | _ -> assert false)
    done;
    print_newline()
  done

let fib n =
  let rec loop k a b =
    if k = n then a
    else loop (k+1) b (a+b)
  in loop 0 0 1

let _ = fib 16

let rec fib_inv_loop n a b k =
  if n < b then k
  else fib_inv_loop n b (a+b) (k+1)

let fib_inv n = if n = 0 then 0 else fib_inv_loop n 1 2 2

let rec decomp n acc =
 if n = 0 then acc
 else
   let k = fib_inv n in
   decomp (n-fib k) (k::acc)

let _ = decomp 1000 []

let rank n =
  if n = 0 then 0 else List.hd (decomp n [])

let _ = rank 1000

let _ =
  print_newline();
  print_string "  ";
  for j=1 to 20 do
    print_int ((rank j) mod 2); print_string " ";
  done;
  print_newline();
  for i=1 to 20 do
    print_int ((rank i) mod 2); print_string " ";
    for j=1 to 20 do
      let d = a1.(i+j)-a1.(i)-a1.(j) in
      print_string
        (match d with
         | 0 -> "= "
         | 1 -> "+ "
         | -1 -> "- "
         | _ -> assert false)
    done;
    print_newline()
  done



(*
0, =
1, -  F2 rg pair
2, +  F3 rg impair
3, -  F4 rg pair
4, -  1+3 rg pair
5, +  F5 rg impair
6, -  1+5 rg pair
7, +  2+5 rg impair
8, -  F6  rg pair
9, -  1+8 rg pair
10, + 2+8 rg impair
11, - 3+8 rg pair
12, - 1+3+8 rg pair
13, + F7 rg impair
14, - 1+13 rg pair
15, + 2+13
16, - 3+13
17, - 1+3+13
18, + 5+13
19, - 1+5+13
20, + 2+5+13
21, - F8
22, - 1+21
23, + 2+21
24, - 3+21
25, - 1+3+21
26, + 5+21
27, - 1+5+21
28, + 2+5+21
29, - 8+21

*)

(* ================== *)
(* H *)

(* Experimentally, H(n+p)-H(n)-H(p) \in [-2..2],
   and -2 and 2 are rather rare

   First h(i+j)-h(i)-h(j) = -2 : i=18 j=78
   First h(i+j)-h(i)-h(j) = 2 : i=39 j=39
*)

let _ = extrems (Array.init 900000 @@ fun n -> a2.(n+21)-a2.(n)-a2.(21))

let _ = Array.init 30 @@
        fun i ->
        (i,extrems (Array.init 900000 @@ fun n -> a2.(n+i)-a2.(n)-a2.(i)))


(*
For H:
i, extrems
0, (0, 0)
1, (-1, 0)
2, (0, 1)
3, (-1, 1)
4, (-1, 0)
------------- levels in tree H
5, (-1, 0)
6, (-1, 1)
-------------
7, (-1, 1)
8, (0, 1)
9, (-1, 1)
-------------
10, (-1, 1)
11, (0, 1)
12, (-1, 1)
13, (-1, 1)
-------------
14, (-1, 0)
15, (-1, 1)
16, (-1, 1)
17, (-1, 0)
18, (-2, 0) <---------------------- Arggggl
19, (-1, 1)
-------------
20, (-1, 1)
21, (-1, 1)
22, (-1, 1)
23, (-1, 1)
24, (-1, 0)
25, (-1, 1)
26, (-1, 1)
27, (0, 1)
28, (-1, 1)
-------------
29, (-1, 1)

*)

(* Searching for 2 and -2 : *)

let _ =
 for i = 1 to 100 do
   for j = 1 to 1000 do
     let d = a2.(i+j)-a2.(i)-a2.(j) in
     if abs d >= 2 then
       Printf.printf "i=%d j=%d delta=%d\n" i j d
   done
 done

(* Conjecture: forall m exists I={-2..0} ou {-1..1} ou {0..2} such that
                 forall n, H(m+n)-H(m)-H(n) \in I
   Experiment:
 *)

let width (a,b) = b-a

let _ = extrems @@ Array.init 10000 @@
        fun i ->
        (width @@ extrems (Array.init 90000 @@ fun n -> a2.(n+i)-a2.(n)-a2.(i)))

let itvls1 =
  let a =
    Array.init 1000 @@
    fun i ->
    (i, width @@ extrems (Array.init 90000 @@ fun n -> a2.(n+i)-a2.(n)-a2.(i)))
  in
  List.map fst (List.filter (fun (i,j) -> j<2) (Array.to_list a))

let _ =
  let rec diffs = function
    | [] | [_] -> []
    | a::b::l -> b-a :: diffs (b::l)
  in diffs itvls1

let _ = extrems @@ Array.init 10000 @@
        fun i ->
        (fst @@ extrems (Array.init 90000 @@ fun n -> a2.(n+i)-a2.(n)-a2.(i)))

(* Generalized Fibonacci. k is distance between terms to add.
   Starts at 1.
   Hence k=1 is usual Fibonacci, shifted: *)

let gfib k n =
  let a = Array.make n 1 in
  for i = 0 to n-2 do a.(i+1) <- a.(i) + a.(max 0 (i-k)) done;
  a

let gfib1 = gfib 1 10
(* [|1; 2; 3; 5; 8; 13; 21; 34; 55; 89|] *)

let _ = (gfib1 = Array.init 10 (fun n -> fib (n+2)))

(* beware, overflow for gfib 1 (for G) around 90,
                        gfib 2 (for H) around 113,
                        ...
*)

let gfib2 = gfib 2 30

(* conjecture :
   when i is a gfib2 number, forall n, H(n+i)-H(n)-H(i) \in {-1,0,1} *)

let _ = Array.init 30 @@
        fun i ->
        let j=gfib2.(i) in
        (i,j,extrems (Array.init 900000 @@
                        fun n -> a2.(n+j)-a2.(n)-a2.(j)))

(* ================== *)
(* f3 *)

(* All numbers : f3(i+j)-f3(i)-f3(j) \in [-3..3] ?
   i=12 -> itvl [0..2]
   i=13 -> itvl [-1..2]
   i=20 -> itvl [-2..1]
   ...
   i=120, j=127 --> -3
   i=229, j=1150 --> +3
*)

let _ = Array.init 30 @@
        fun i ->
        (i,extrems (Array.init 900000 @@
                      fun n -> a3.(n+i)-a3.(n)-a3.(i)))

let _ =
 for i = 1 to 1000 do
   for j = 1 to 900000 do
     let d = a3.(i+j)-a3.(i)-a3.(j) in
     if abs d >= 4 then
       Printf.printf "i=%d j=%d delta=%d\n" i j d
   done
 done

let _ = Array.init 30 @@
        fun i ->
        (i,extrems (Array.init 900000 @@ fun n -> a3.(n+i)-a3.(n)-a3.(i)))


(* If i is a gfib3 number : f3(n+i)-f3(n)-f3(i) \in {-1,0,1} ? *)

let gfib3 = gfib 3 35

let _ = Array.init 35 @@
        fun i ->
        let j=gfib3.(i) in
        (i,j,extrems (Array.init 900000 @@
                        fun n -> a3.(n+j)-a3.(n)-a3.(j)))

(* ================== *)
(* f4 *)

(* All numbers : f4(n+i)-f4(n)-f4(i) \in [-5..5] ?
   i=928 j=1227 delta=-5
   i=12580 j=14755 delta=5
*)

let _ = Array.init 30 @@
        fun i ->
        (i,extrems (Array.init 900000 @@
                      fun n -> a4.(n+i)-a4.(n)-a4.(i)))

let _ =
 for i = 12580 to 12580 (*1 to 1000*) do
   for j = 1 to 900000 do
     let d = a4.(i+j)-a4.(i)-a4.(j) in
     if d=5 then begin
       Printf.printf "i=%d j=%d delta=%d\n" i j d;
       failwith "Stop"
      end
   done
 done

(* gfib4 numbers : f4(n+i)-f4(n)-f4(i) \in {-1,0,1} ? NOT AT ALL ?!? *)

let gfib4 = gfib 4 40

let _ = Array.init 40 @@
        fun i ->
        let j=gfib4.(i) in
        (i,j,extrems (Array.init 900000 @@
                        fun n -> a4.(n+j)-a4.(n)-a4.(j)))
(* Up to [-5..5] for gfib 4 39 = 90061 *)

(* ================== *)
(* f5 *)

(* All numbers : f5(n+i)-f5(n)-f5(i) \in [-11..11] ?
   i=9852 j=12648 delta=-11
   i=18553 j=42773 delta=11
*)

let _ = Array.init 30 @@
        fun i ->
        (i,extrems (Array.init 900000 @@
                      fun n -> a5.(n+i)-a5.(n)-a5.(i)))

let _ =
 for i = 1 to 20000 do
   for j = 1 to 50000 do
     let d = a5.(i+j)-a5.(i)-a5.(j) in
     if d = 11 then begin
       Printf.printf "i=%d j=%d delta=%d\n" i j d;
       failwith "Stop"
      end
   done
 done

(* gfib5 numbers : f5(n+i)-f5(n)-f5(i) \in {-1,0,1} ? NOT AT ALL ?!? *)

let gfib5 = gfib 5 40

let _ = Array.init 40 @@
        fun i ->
        let j=gfib5.(i) in
        (i,j,extrems (Array.init 900000 @@
                        fun n -> a5.(n+j)-a5.(n)-a5.(j)))
(* Up to [-7..9] for gfib 5 39 = 29548 *)
