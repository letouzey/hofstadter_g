
(** utils *)

let float = float_of_int
let int = int_of_float

let round f = float (int (f *. 1e8)) /. 1e8

let extrems tab =
  let mi = ref tab.(0) and ma = ref tab.(0) in
  Array.iter (fun x -> mi := min x !mi; ma := max x !ma) tab;
  !mi, !ma

let histo tab =
  let t = Array.copy tab in
  let () = Array.sort compare t in
  let rec cumul a k i =
    if i >= Array.length t then [(a,k)]
    else if t.(i) = a then cumul a (k+1) (i+1)
    else (a,k)::cumul t.(i) 1 (i+1)
  in cumul t.(0) 1 1

let output_gnuplot_file file tab =
  let c = open_out file in
  Array.iter (fun (a,b) -> Printf.fprintf c "%f %f\n" a b) tab;
  close_out c

(** applying and repeating substitution *)

let dosubst f w =
  (* naive code : List.flatten (List.map f w) *)
  let rec loop acc = function
    | [] -> List.rev acc
    | a::w -> loop (List.rev_append (f a) acc) w
  in loop [] w

(** Generalization : k+1 nested calls *)
let rec iter f n = if n=0 then fun x -> x else fun x -> iter f (n-1) (f x)

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

(* Generalized Fibonacci. k is distance between terms to add.
   Starts at 1.
   Hence k=1 is usual Fibonacci, shifted: *)

let gfib k n =
  let a = Array.make n 1 in
  for i = 0 to n-2 do a.(i+1) <- a.(i) + a.(max 0 (i-k)) done;
  a

(* beware, overflow for gfib 1 (for G) around 90,
                        gfib 2 (for H) around 113,
                        ...
*)

let gfib2 = gfib 2 30

(** LIMITS *)

(* k = 1 (G) *)
let phi = (1.+.sqrt(5.))/.2. (* root of X^2-X-1 *)
let tau = phi-.1.  (* also 1/phi, root of X^2+X-1 *)

(* k = 2 (H) *)
let limh = 0.6823278038280194 (* root of X^3+X-1, cf maxima *)
let expo = 1.465571231876768 (* 1/limh, also root of X^3-X^2-1 *)

(** Little equation solver (via Newton's method.
   newton k find an approximation of the root of X^k+X-1
   in [0;1]
*)

let newton k =
  if k = 0 then 0. else
  let fk = float k in
  let rec loop n x =
    let y = x -. (x** fk +. x -. 1.)/.(fk *.x ** (fk-.1.) +.1.) in
    if x = y || n > 100 then x
    else loop (n+1) y
  in loop 0 1.

(* Beware! for k=18 and 19, we get a two-cycle (issue with approx ?) *)

(* Precision: around 10^-15 (note that epsilon_float = 2e-16 *)

let lims = Array.init 20 (fun n -> newton (n+1))

let _ = lims.(1)-.tau;;
let _ = lims.(2)-.limh;;




let subst = function 1->[1;2] | 2->[3] | _->[1]

let mot = Array.of_list (itersubst subst 25 [1])
let _ = Array.length mot

let cumul letter mot =
  let n = Array.length mot in
  let a = Array.make n 0 in
  for i = 1 to n-1 do
    a.(i) <- a.(i-1) + (if mot.(i-1)=letter then 1 else 0)
  done;
  a

let r1 = cumul 1 mot
let r2 = cumul 2 mot
let r3 = cumul 3 mot

let _ = for i = 0 to Array.length mot -1;
        do assert (r1.(i)+r2.(i)+r3.(i) = i); done

let hbis n = if n=0 then 0 else n - r2.(n)

let _ = for i = 0 to Array.length mot -1; do assert (hbis i = a2.(i)); done

let rauzy_delta1 n = limh*.limh*.float n -. float (r1.(n))
let rauzy_delta2 n = (1.-.limh)*.float n -. float (r2.(n))

let _ = output_gnuplot_file "/tmp/rauzy"
          (Array.init 10000 @@ fun i -> rauzy_delta1 i, rauzy_delta2 i)

let _ = output_gnuplot_file "/tmp/rauzy_my"
          (Array.init 10000 @@ fun i -> rauzy_delta2 i,
                                        -. rauzy_delta1 i -. limh *.rauzy_delta2 i)

let b (x,y) = (-.limh*.limh*.x-.y, limh*.x)

let vect_z = (limh*.limh-.1.,limh**3.)
let vectBz = b vect_z
let vectBBz = b vectBz

let coins =
  let a = 1.21 and b = 0.996 in
  [|a,b;a,-.b;-.a,-.b;-.a,b;a,b|]

let addpair (a,b) (c,d) = (a+.c,b+.d)

let bcoins = Array.map b coins
let b3coins_p_z = Array.map (fun p -> addpair vect_z (b (b (b p)))) coins

let _ = output_gnuplot_file "/tmp/bcoins" bcoins
let _ = output_gnuplot_file "/tmp/b3coins" b3coins_p_z

let _ = output_gnuplot_file "/tmp/rauzyB"
          (Array.init 10000 @@ fun i -> b (rauzy_delta1 i, rauzy_delta2 i))

let _ = output_gnuplot_file "/tmp/rauzyB2"
          (Array.init 10000 @@ fun i -> b (b (rauzy_delta1 i, rauzy_delta2 i)))

let _ = output_gnuplot_file "/tmp/rauzyB3"
          (Array.init 10000 @@ fun i -> b (b (b (rauzy_delta1 i, rauzy_delta2 i))))

let _ = output_gnuplot_file "/tmp/rauzyB4"
          (Array.init 10000 @@ fun i -> b (b (b (b (rauzy_delta1 i, rauzy_delta2 i)))))

let _ = output_gnuplot_file "/tmp/rauzyB5"
          (Array.init 10000 @@ fun i -> b (b (b (b (b (rauzy_delta1 i, rauzy_delta2 i))))))



(** FLOAT EXPRESSIONS OR APPROXIMATIONS *)

(**** k=2 (H) ****)

let delta2 = Array.init 100000 @@ fun i -> float a2.(i) -. float i *. lims.(2)

let _ = extrems delta2 (* -0.7..0.85 hence more than 1 of width *)

(* two increasing lines, one partly below the other *)
let _ = output_gnuplot_file "/tmp/out2"
          (Array.init 1000 @@ fun i -> delta2.(i),delta2.(i+1))

(* A Rauzy fractal ?!? *)
(* My first encounter:
 *)
let _ = output_gnuplot_file "/tmp/out2bis"
          (Array.init 10000 @@ fun i -> delta2.(i),delta2.(a2.(i)))

(* turned:
let _ = output_gnuplot_file "/tmp/out2bis"
          (Array.init 10000 @@ fun i -> delta2.(a2.(i)),-.delta2.(i))
 *)

(* Or rather the fractal boundary of a Modified Jacobi-Perron substitution
   \sigma_(1,0) : 1->12, 2->3, 3->1
   See Pytheas Fogg, Substitutions in Dynamics Arithmetics and Combinatorics,
    Fig 8.1 page 256 *)
(* See also :
   https://tilings.math.uni-bielefeld.de/substitution/a-ab--b-c--c-a/ *)

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

let dosubst f w =
  (* naive code : List.flatten (List.map f w) *)
  let rec loop acc = function
    | [] -> List.rev acc
    | a::w -> loop (List.rev_append (f a) acc) w
  in loop [] w

let itersubst f n init = iter (dosubst f) n init

let subst2 = function 2 -> [2;0] | n -> [n+1]
let subst2b = function 2|3 -> [3;0] | n -> [n+1]

let mot2 = Array.of_list (itersubst subst2 36 [2])
let mot2b = Array.of_list (itersubst subst2b 36 [3])
let _ = Array.length mot2

let h' n =
  let r = ref 0 in
  for i = 0 to n-1 do
    if mot2.(i) <> 0 then incr r
  done;
  !r

let t = Array.init 100000 @@
          fun i ->
          (mot2.(i), float a2.(i) -. float i *. lims.(2))


let t0_delta_next =
  Array.init 50000 @@ fun i ->
                      let (u,v) = t.(i) in
                      if u=0 then v,snd t.(i+1)
                      else 0.,0.

let _ = extrems (Array.map fst t0_delta_next)
  (*  (-0.0221187768729578238, 0.850466788466292201) *)
let _ = extrems (Array.map snd t0_delta_next)
  (*  (-0.704446580701187486, 0.168138984638062539) *)

let _ = output_gnuplot_file "/tmp/h_0" t0_delta_next

let _ = lims.(2)

(* n de rang 0 : une unique ligne croissante (-0.022,-0.70)..(0.85,0.168)
   y = x - 0.68 (h plat)
*)

let t1_delta_next =
  Array.init 50000 @@ fun i ->
                      let (u,v) = t.(i) in
                      if u=1 then v,snd t.(i+1)
                      else -0.5,0.

let _ = extrems (Array.map fst t1_delta_next)
  (* (-0.704446580701187486, -0.102549800049018813) *)
let _ = extrems (Array.map snd t1_delta_next)
  (* (-0.386774384529417148, 0.215122396122751525) *)

let _ = output_gnuplot_file "/tmp/h_1" t1_delta_next

(* n de rang 1 : une unique ligne croissante (-0.70,-0.38)..(-0.10,0.215)
   y = x + 0.317
   car h(n+1)-(n+1).alpha = h(n)-n.alpha + (1-alpha)
*)

let t2_delta_next =
  Array.init 50000 @@ fun i ->
                      let (u,v) = t.(i) in
                      if u=2 then v,snd t.(i+1)
                      else 0.,0.

let _ = extrems (Array.map fst t2_delta_next)
  (* (-0.386774384529417148, 0.532794592294521863) *)
let _ = extrems (Array.map snd t2_delta_next)
  (* (-0.0691021883576468099, 0.850466788466292201) *)

let _ = output_gnuplot_file "/tmp/h_2" t2_delta_next

(* n de rang >=2 : une unique ligne croissante (-0.38,-0.069)..(0.53,0.85) *)


(* rang 0 : next 1 ou 2+ (car renorm (1::...) donc 1 ou 3+)
   rang 1 : next 2+
   rang 2+ : next 0 ou 2+ (car exact 2 donc renorm(3::...) donc 2+
                           mais 3+ donne 0::3 donc 0)

Subdiviser 2+ en 2 et 3+ : cf mot2b

 rang 0 : next 1 ou 3+
 rang 1 : next 2 ou 3+ (car renorm (2::...))
 rang 2 : next 3+
 rang 3+ : next 0

*)

let t2bis_delta_next =
  Array.init 50000 @@ fun i ->
                      if mot2b.(i)=2 then snd t.(i),snd t.(i+1)
                      else 0.,0.

let _ = extrems (Array.map fst t2bis_delta_next)
  (* (-0.386774384529417148, 0.215122396122751525) *)
let _ = extrems (Array.map snd t2bis_delta_next)
  (* (-0.0691021883576468099, 0.532794592294521863) *)

let t3bis_delta_next =
  Array.init 50000 @@ fun i ->
                      if mot2b.(i)=3 then snd t.(i),snd t.(i+1)
                      else 0.,0.

let _ = extrems (Array.map fst t3bis_delta_next)
  (* (-0.339790973044728162, 0.532794592294521863) *)
let _ = extrems (Array.map snd t3bis_delta_next)
  (* (-0.0221187768729578238, 0.850466788466292201) *)

let _ = output_gnuplot_file "/tmp/h_2b" t2bis_delta_next
let _ = output_gnuplot_file "/tmp/h_3b" t3bis_delta_next

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

let rank2_max3 n =
  match List.rev (decomp n) with
  | [] -> 3
  | r::_ -> min r 3

let _ = Array.init 100 rank2_max3

let prefix_max3 = Array.init 20 (fun i -> Array.init s2opt.(i) rank2_max3)

let _ =
  for i = 1 to 16 do
    assert (prefix_max3.(i+3) = Array.append prefix_max3.(i+2) prefix_max3.(i))
  done

let _ =
  for i = 0 to Array.length prefix_max3.(19) - 1 do
    assert (mot2b.(i) = prefix_max3.(19).(i))
  done

(* Seule exception : 3012 n'est pas 301++3 sinon ensuite M(n+1)=Mn++M(n-2)

M0 = 3
M1 = 30
M2 = 301
M3 = 3012
puis
M(n+1) = Mn++M(n-2)

Expression via substitution : 0->1, 1->2, 2->30, 3->30

3
30
301
3012
301230
301230301
3012303013012
3012303013012301230
3012303013012301230301230301

Comparaison avec mot "de base" pour k=3 engendré par 0->1, 1->2, 2->3, 3->30

3
30
301
3012
30123.                        supprimé: 0
30123.30.                     supprimé: 0 1
30123.30.301.                 supprimé: 0 1 2
30123.30.301.3012..           supprimé: 0 1 2 30
30123.30.301.3012..30123....  supprimé: 0 1 2 30 0 301

Proportion de 0 toujours plus faible que pour k=2 ??

Autre vision : par prolongement:

3
30
301
3012
3012 30
301230 301
301230301 3012
3012303013012 301230
3012303013012301230 301230301

Contre:

3
30
301
3012
3012 3   (un 0 de moins)
30123 30  (un 0 de moins, et un 1 final)
3012330 301  ( 0 1 2 )
3012330301 3012 ( 0 1 2 30 )
30123303013012 30123
3012330301301230123 3012330
30123303013012301233012330 3012330301

Des zeros en moins, mais aussi des fins de mots (car on prend un pas en
arriere de plus)



*)




let _ = s2opt

let _ = s2opt.(30)

let _ = Array.init 30 @@
          fun i -> float s2opt.(i) -. float s2opt.(i+1) *. lims.(2)
(* moins de 1/10 après s2opt.(7) *)

let _ = mot2

(* 1; 2; 3; 4; 6; 9; 13; 19; 28; 41; 60; 88; 129; 189; 277; 406; 595; 872 *)

(* avec 0,1,2+ :
2
20
201
201 2
2012 20
201220 201
201220201 2012
2012202012012 201220
 *)

(* avec 0,1,2,3+ :

30123030130123012303012303013012303013012301230301
..... .  .   .     .        .            .


3012303013012301230301230301


*)



(** FLIPPED *)

(** "flipped" functions *)

let rec h' x = if x <= 5 then h x else x+1 - h' (h' (1 + h' (x-1)))

let _ = Array.init 30 (fun i -> i,h' i)

let rec f3' x = if x <= 6 then a3.(x) else x+1 - f3' (f3' (f3' (1 + f3' (x-1))))

let _ = Array.init 30 (fun i -> i,f3' i)
