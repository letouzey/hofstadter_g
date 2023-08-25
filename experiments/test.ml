
#use "defs.ml";;

let a = tabulate_f 10 10_000_000
let a0 = a.(0)
let a1 = a.(1)
let a2 = a.(2)
let a3 = a.(3)
let a4 = a.(4)
let a5 = a.(5)

let _ = check_col_incr 1000 1000

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

(* All numbers : f4(n+i)-f4(n)-f4(i) \in [-5..5] ? PROBABLY NOT
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

(* All numbers : f5(n+i)-f5(n)-f5(i) \in [-11..11] ? PROBABLY NOT
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


#use "roots.ml";; (* for lims *)

(** FLOAT EXPRESSIONS OR APPROXIMATIONS *)

(**** k=0 ****)

(* f0 is a division by 2, with two possible statements *)

let t0 len = Array.init len @@ fun i -> int ( float (i+1) /. 2.)

let t0' len = Array.init len @@ fun i -> int ( ceil (float i /. 2.))

let _ = a.(0) = t0 1000001
let _ = a.(0) = t0' 1000001

(**** k=1 (G) ****)


let t1 = Array.init 1000 @@ fun i -> int ( float (i+1) /. phi)

let delta_old = Array.init 1000 @@ fun i -> float (i+1) /. phi -. float a1.(i)

let delta = Array.init 10000 @@ fun i -> float a1.(i) -. float i /. phi

(* Two increasing segments : *)
let _ = output_gnuplot_file "/tmp/out1"
      (Array.init 9999 @@ fun i -> delta.(i),delta.(i+1))

(* Two decreasing segments *)
let _ = output_gnuplot_file "/tmp/out1bis"
      (Array.init 1000 @@ fun i -> delta.(i),delta.(a1.(i)))

(* f1 (also named g earlier) is fun n -> floor ((n+1) / phi).
   This implies that for all n, f1(n) is either floor(n/phi)
   or ceil(n/phi), and hence is at most 1 away from the other.
*)

(* Justification:
(n+1)/phi = n/phi + 0.618
hence floor ((n+1)/phi) is either floor(n/phi) or
 floor(n/phi)+1 = ceil(n/phi) (as soon as n<>0, phi being irrational)
 *)

let t1' = Array.init 1000 @@ fun i -> float i /. phi
type fc = F | C
let _ = Array.init 1000 @@
          fun i ->
          if a1.(i) = int (t1'.(i)) then F
          else if a1.(i) = int (ceil (t1'.(i))) then C
          else failwith "BUG"

(*
Remark: never two consecutive "floor" : one "floor", followed by
 one or two "ceil", etc
*)
(*
tau = 0.618 = (sqrt(5)-1)/2 = phi-1 = 1/phi
1-tau = 0.38.. = 2-phi

No "floor" after a "floor" :

If f2(n) = floor(n/phi) then it's also floor((n+1)/phi)
hence frac(n/phi) is in [0;1-tau[ = [0;0.38[
      frac((n+1)/phi) is in [tau;1[ = [0.618;1[
and (n+2)/phi=n/phi+2tau=n/phi+1.2 will be in the next interval
  f2(n+1) = floor((n+2)/phi) = f2(n)+1 = floor((n+1)/phi)+1
                                       = ceil((n+1)/phi)
  hence "ceil" in (n+1)

No more than two consecutive "ceil" :

If f2(n) = ceil(n/phi), it's also floor((n+1)/phi)
hence frac(n/phi) is in [1-tau;1[
hence frac((n+1)/phi) is in [0;tau[ = [0;0.618[
two cases:
 - if frac((n+1)/phi) is in [0;1-tau[ = [0;0.38[
   then f2(n+1) = floor((n+2)/phi) = floor((n+1)/phi)
   hence "floor" in n+1 (and f2(n+1)=f2(n))

 - if frac((n+1)/phi is in [1-tau;tau[ = [0.38;0.618[
   then f2(n+1) = floor((n+2)/phi) = floor((n+1)/phi)+1
                                   = ceil((n+1)/phi
   hence "ceil" in (n+1)
   but then frac((n+2)/phi) is in [0;2*tau-1[ = [0;0.23[
   hence f2(n+2) = floor((n+3)/phi) = floor((n+2)/phi)
   hence "floor" in (n+2)
*)

(**** k=2 (H) ****)

let delta2 = Array.init 100000 @@ fun i -> float a2.(i) -. float i *. lims.(2)

let _ = extrems delta2 (* -0.7..0.85 hence more than 1 of width *)

(* two increasing lines, one partly below the other *)
let _ = output_gnuplot_file "/tmp/out2"
          (Array.init 1000 @@ fun i -> delta2.(i),delta2.(i+1))

(* A Rauzy fractal ?!? *)
let _ = output_gnuplot_file "/tmp/out2bis"
          (Array.init 10000 @@ fun i -> delta2.(i),delta2.(a2.(i)))

(* Or rather the fractal boundary of a Modified Jacobi-Perron substitution
   \sigma_(1,0) : 1->12, 2->3, 3->1
   See Pytheas Fogg, Substitutions in Dynamics Arithmetics and Combinatorics,
    Fig 8.1 page 256 *)
(* See also :
   https://tilings.math.uni-bielefeld.de/substitution/a-ab--b-c--c-a/ *)

(* A version which looks closer to this Jacobi-Perron fractal:
   (h(n)-limh*n, h(h(n))-limh^2*n) is just a 90 degree rotation of it
 *)
let _ = output_gnuplot_file "/tmp/out2bisbis"
          (Array.init 10000 @@ fun i ->
                               float a2.(i) -. float i *. limh,
                               float a2.(a2.(i)) -. float i *. limh ** 2.)

let delta2ter =
  Array.init 10000 @@
    fun i ->
    let k1 = a2.(i) in
    let k2 = a2.(k1) in
    (delta2.(i),lims.(2)*.delta2.(k1)+.delta2.(k2))

let _ = output_gnuplot_file "/tmp/out2ter" delta2ter
(* Two decreasing segments : *)

(* High segment (when f2 grows) :
((-0.535727138340007514, 0.785146282035457332),
 (0.707284644711762667, -1.03657602805559979))

 Low segment (when f2 stagnate):
((-0.853399334533605725, 0.250717513904961442),
 (0.0249568408762570471, -1.03657602805559979))

*)

let delta2qu =
  Array.init 1000 @@
    fun i ->
    let k1 = a2.(i) in
    let k2 = a2.(k1) in
    round (delta2.(k2) +. lims.(2)*.delta2.(k1) +. delta2.(i)/.lims.(2))
(* Always equal to 0 ou -1 *)


(* f2 (H) and float computation *)

let hbis n = int (limh *. float n)
let hter n = int (ceil (limh *. float n))

let _ = Array.init 20 @@ fun n -> (hbis n, h n, hter n)

let _ = Array.init 1000 @@ fun n ->
        if a2.(n) = hbis n then F
        else if a2.(n) = hter n then C
        else failwith "AWAY"

let _ = Array.init 1000 @@ fun n ->
        int (limh *. (float (n+1))) - a2.(n)
 (* majoritairement des 0, mais aussi quelques 1 et -1 *)


(**** k=3 ****)

let _ = lims.(3)

let delta3 =
  Array.init 1000000 @@ fun i -> float a3.(i) -. float i *. lims.(3)

let _ = extrems delta3 (* -1.40..1.46 *)

(* Two segments *)
let _ = output_gnuplot_file "/tmp/out3"
      (Array.init 1000 @@ fun i -> (delta3.(i),delta3.(i+1)))

let delta3bis = Array.init 10000 @@ fun i -> (delta3.(i),delta3.(a3.(i)))

(* No obvious fractal, rather a cloud of points : *)
let _ = output_gnuplot_file "/tmp/out3bis" delta3bis

let _ = output_gnuplot_file "/tmp/out3bisbis"
      (Array.init 50000 @@ fun i ->
                           float a3.(i) -. float i *. lims.(3),
                           float a3.(a3.(i)) -. float i *. lims.(3) ** 2.)

let _ = output_gnuplot_file3 "/tmp/out3bisbis3"
      (Array.init 50000 @@ fun i ->
                           float a3.(i) -. float i *. lims.(3),
                           float a3.(a3.(i)) -. float i *. lims.(3) ** 2.,
                           float a3.(a3.(a3.(i))) -. float i *. lims.(3) ** 3.)

(* Displayed via splot, the 3D cloud of points seems to have at least one axis
   revealing some fractal aspect. *)

(* Two segments *)
let delta3ter =
  Array.init 10000 @@
    fun i ->
    let k1 = a3.(i) in
    let k2 = a3.(k1) in
    let k3 = a3.(k2) in
    (delta3.(i),
     lims.(3)**2.*.delta3.(k1)+.
     lims.(3)*.delta3.(k2)+.
     delta3.(k3))

let _ = extrems delta3ter

let _ = output_gnuplot_file "/tmp/out3ter" delta3ter

(* ligne du haut (lorsque f3 grimpe):
((-1.18651591357775033, 1.63772130094070367),
 (1.40104105672799051, -1.93382554394093065))

ligne du bas (lorsque f3 stagne)
((-1.46202395457657985, 1.01799887003979084),
 (0.676549097755923867, -1.93382554394093065))
*)

let delta3qu =
  Array.init 1000 @@
    fun i ->
    let k1 = a3.(i) in
    let k2 = a3.(k1) in
    let k3 = a3.(k2) in
    round
      (lims.(3)**2.*.delta3.(k1)+.
       lims.(3)*.delta3.(k2)+.
       delta3.(k3) +.
       delta3.(i)/.lims.(3))
(* que des 0 ou 1 *)

(* f3 and float computation *)

let out = Array.init 1000 @@ fun n ->
        a3.(n) - int(float n /. expo3)
let _ = histo out
(* histo : (-1, 4); (0, 504); (1, 482); (2, 10) *)

let out = Array.init 100000 @@ fun n ->
        a3.(n) - int(float n /. expo3)
let _ = histo out
(* histo : (-1, 746); (0, 49930); (1, 47971); (2, 1353) *)


(**** k=4 ****)

let _ = lims.(4)

let out = Array.init 1000 @@ fun n ->
        a4.(n) - int(float n *. lims.(4))
let _ = histo out
(* histo : (-1, 55); (0, 475); (1, 411); (2, 59) *)

let out = Array.init 100000 @@ fun n ->
        a4.(n) - int(float n *. lims.(4))
let _ = histo out
(* histo : (-2, 712); (-1, 15182); (0, 42821); (1, 33705); (2, 7345); (3, 235) *)

let delta4 =
  Array.init 1000000 @@ fun i -> float a4.(i) -. float i *. lims.(4)

let _ = extrems delta4 (* -3..3.2 *)

(* Two segments *)
let _ = output_gnuplot_file "/tmp/out4"
      (Array.init 1000 @@ fun i -> (delta4.(i),delta4.(i+1)))

let delta4bis = Array.init 10000 @@ fun i -> (delta4.(i),delta4.(a4.(i)))

(* Strange figure, globally a cloud but with "detached" agglomeration points *)
let _ = output_gnuplot_file "/tmp/out4bis" delta4bis


(**** k = 5 *****)

let _ = lims.(5)

let delta5 =
  Array.init 10000000 @@ fun i -> float a5.(i) -. float i *. lims.(5)

let _ = extrems delta5 (* 10^5 : -4.66..5.4
                          10^6 : -7.8..7.25
                          10^7 : -10.8..9.46 *)


(** DECOMPOSITION *)

(** Zeckendorf decomposition for k=2 *)

(** The sequence.
    Similar to Fibonacci, but skipping a term in the addition
    See http://oeis.org/A000930 (Narayana)
    Here we start at the last 1 (no 0, no ambiguity over 1)
*)
let rec s2 n = if n<4 then n+1 else s2 (n-1) + s2 (n-3)

(** Ratio converges to expo *)
let _ = Array.init 20 (fun n -> float (s2 (n+2)) /. float (s2 (n+1)))
let _ = Array.init 20 (fun n -> float (s2 (n+2)) /. float (s2 (n+1)) -. expo)

(** Memoized version of the sequence : cf earlier gfib *)

let _ = gfib 2 10 = Array.init 10 s2

let s2opt = gfib 2 101

let _ =
  Array.init 100 @@ fun i -> float s2opt.(i) /.(expo ** float i)

(** s2(n) ~ 1.3134230598523 * expo^n *)

(** The decomposition *)

let rec decomp n =
  let rec loop k =
    if s2opt.(k) > n then k-1
    else loop (k+1)
  in
  if n = 0 then []
  else
    let x = loop 1 in
    x::(decomp (n-s2opt.(x)))

let _ = Array.init 100 @@ fun n -> n, decomp n

let a20942 =
  let l = Array.to_list (Array.init 100 @@ fun n -> n, decomp n) in
  List.filter (fun (x,l) -> List.mem 0 l) l

(* See http://oeis.org/A020942 : numbers containing 1 in
   their 2-decomposition.
   = places where h will stagnate: h 1 = h 2, h 5 = h 6, h 7 = h 8, etc
*)

let _ = List.map (fun (n,_) -> a2.(n+1) - a2.(n)) a20942


(** Zeckendorf decomposition for k=4 *)

let rec s4 n = if n<6 then n+1 else s4 (n-1) + s4 (n-5)

(** Ratio converges to expo *)
let _ = Array.init 20 (fun n -> float (s4 (n+2)) /. float (s4 (n+1)))
let _ = Array.init 20
          (fun n -> float (s4 (n+2)) /. float (s4 (n+1)) -. 1./.lims.(4))

(** Memoized version of the sequence : cf earlier gfib *)

let _ = gfib 4 10 = Array.init 10 s4

let s4opt = gfib 4 151

let _ =
  Array.init 100 @@ fun i -> float s4opt.(i) *. (lims.(4) ** float i)

(** s4(n) ~ 1.5549670321610 * expo^n *)

(** Interesting numbers leading to divergent delta (f4-n*tau4) *)

let rec nb n = if n = 0 then 1 else nb (n-1) + s4opt.(6*n)

(* indirect computation of (f4 (nb n)) : *)
let rec f4nb n = if n = 0 then 1 else f4nb (n-1) + s4opt.(6*n-1)

let _ = List.init 25 nb
let _ = List.init 25 f4nb

(* Check when possible that f4nb is indeed f4(nb) *)
let _ = List.init 25 (fun n ->
            let nb_n = nb n in
            let f4nb_n = f4nb n in
            if nb_n < Array.length a4 then
              Some (f4nb_n - a4.(nb_n))
            else None)

let delta_nb n = float (f4nb n) -. lims.(4) *. float (nb n)

let _ = List.init 25 delta_nb

(* Too bad, not enough precision to compute delta_nb accurately
   after n=20 roughly. Increment of about 0.0378 between two steps.
   Values arbitrarily large can theoretically be reached.
   Cf rauzy4.wxm for values between 1 and 1.3 (sic).
*)


(** Zeckendorf decomposition for k=5 *)

let rec s5 n = if n<7 then n+1 else s5 (n-1) + s5 (n-6)

(** Ratio converges to expo *)
let _ = Array.init 20 (fun n -> float (s5 (n+2)) /. float (s5 (n+1)))
let _ = Array.init 20
          (fun n -> float (s5 (n+2)) /. float (s5 (n+1)) -. 1./.lims.(5))

(** Memoized version of the sequence : cf earlier gfib *)

let _ = gfib 5 10 = Array.init 10 s5

let s5opt = gfib 5 170

let _ =
  Array.init 170 @@ fun i -> float s5opt.(i) *. (lims.(5) ** float i)

(** s5(n) ~ 1.662117470913826 * expo^n *)

(** Interesting numbers leading to divergent delta (f5-n*tau5) *)

(* Check when possible that shifting down s5opt is indeed f5(s5opt) *)

let _ = List.init 169 (fun n ->
            let nb_n = s5opt.(n+1) in
            let f5nb_n = s5opt.(n) in
            if nb_n < Array.length a5 then
              Some (f5nb_n - a5.(nb_n))
            else None)

let delta_nb n = float s5opt.(n) -. lims.(5) *. float s5opt.(n+1)

let _ = List.init 169 delta_nb

(* Seems unbounded, but hard to conclude anything, accuracy ?? *)


(** FLIPPED *)

(** "flipped" functions *)

let rec h' x = if x <= 5 then h x else x+1 - h' (h' (1 + h' (x-1)))

let _ = Array.init 30 (fun i -> i,h' i)

let rec f3' x = if x <= 6 then a3.(x) else x+1 - f3' (f3' (f3' (1 + f3' (x-1))))

let _ = Array.init 30 (fun i -> i,f3' i)
