
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

(** the recursive functions *)

let rec d n = if n = 0 then 0 else n - d(n-1)

(* http://oeis.org/A005206 *)
let rec g n = if n = 0 then 0 else n - g (g (n-1))

(* http://oeis.org/A005374 *)
let rec h n = if n = 0 then 0 else n - h (h (h (n-1)))


(** Generalization : k+1 nested calls *)
let rec iter f n = if n=0 then fun x -> x else fun x -> iter f (n-1) (f x)

let rec f k n = if n = 0 then 0 else n - iter (f k) (k+1) (n-1)

let f0 = f 0 (* d *)
let f1 = f 1 (* g *)
let f2 = f 2 (* h *)
let f3 = f 3

let _ = Array.init 20 @@ fun n -> n,f0 n,d n
let _ = Array.init 20 @@ fun n -> n,f1 n,g n
let _ = Array.init 20 @@ fun n -> n,f2 n,h n

(* nb: f4 is http://oeis.org/A005375 *)

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

(* Check that all columns are increasing : f k n <= f (k+1) n *)

let check k n =
  let a = tabulate k n in
  for i = 0 to k-1 do
    for j = 0 to n do
      if a.(i).(j) > a.(i+1).(j) then Printf.printf "(%d,%d)\n" i j
    done
  done

let _ = check 1000 1000

(* Shift : quasi inverse of f *)

let shift k n = n + iter (f k) k n

let sh1 = Array.init 100 (shift 1)

let phi = (1.+.sqrt(5.))/.2. (* root of X^2-X-1 *)
let _ = Array.init 100 (fun i -> float i *. phi -. float sh.(i))

let sh2 = Array.init 100 (shift 2)

let tabulate_shift a =
  let k = Array.length a -1 in
  let n = Array.length a.(0) -1 in
  let b = Array.make_matrix (k+1) (n+1) 0 in
  for i = 0 to k do
    for j = 1 to n do
      let x = ref j in
      for p = 1 to i do
        x := a.(i).(!x)
      done;
      b.(i).(j) <- j + !x
    done
  done;
  b

let b = tabulate_shift a
let b0 = b.(0)
let b1 = b.(1)
let b2 = b.(2)
let b3 = b.(3)
let _ = for i = 0 to 99 do assert (sh1.(i) = b1.(i)) done
let _ = for i = 0 to 99 do assert (sh2.(i) = b2.(i)) done


(* Quasi-additivité de shift 2 :
   shift2 (n+m)-shift2(n)-shift2(m) semble toujours entre -2 et 2
*)

let _ =
  let m = ref 0 in
  for i = 0 to 10000 do
    for j = 0 to 90000 do
      let d = b2.(i+j)-b2.(i)-b2.(j) in
      m := max !m (abs d)
    done
  done;
  !m

(* des intervalles (-2,1) par exemple pour i=14
               ou  (-1,2) par exemple pour i=31 *)

let _ = Array.init 100 @@
        fun i ->
        (i,extrems (Array.init 900000 @@ fun n -> b2.(n+i)-b2.(n)-b2.(i)))

(*
Lien shift / f pour la quasi-additivité ?

Supposons forall n m, H(n+m) = H(n)+H(m) + {-2..2}


shift(n+m)   shift(n)+shift(m)

surjectivité:
n peut s'ecrire H(n') (et en fait n' = shift n)
m ............. H(m') (et en fait m' = shift m)

shift(n+m) = shift (H(n')+H(m'))
           = shift (H(n'+m')+{-2..2})
           = shift (H(n'+m')) + {-4..4} ?
           = n'+m' + {0,1} + {-4..4}
           = shift(n)+shift(m) + {-4..5}

Reciproquement
Supposons forall n m, shift(n+m) = shift(n)+shift(m) + {-2..2}

H(a+b)

a = shift(a') ou 1+shift(a')   (avec a' = H a)
b = shift(b') ou 1+shift(b')   (avec b' = H b)

donc
H(a+b) = H(shift(a')+shift(b')+{0..2})
       = H(shift(a')+shift(b')) + {0..2}
       = H(shift(a'+b') + {-2..2}) + {0,2}
       = H(shift(a'+b')) + {-2..2} + {0..2}
       = a'+b' +{-1,0} + {-2..2} + {0..2}
       = H(a)+H(b) + {-3..4}

Donc en tout cas une quasi-additivité donne l'autre (et vice-versa)
mais avec des constantes qui seront dures à optimiser
*)


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

(* conjecture :
   when i is a gfib2 number,
   forall n, shift2(n+i)-shift2(n)-shift2(i) \in {-1,0,1} *)

let _ = Array.init 30 @@
        fun i ->
        let j=gfib2.(i) in
        (i,j,extrems (Array.init 900000 @@
                        fun n -> b2.(n+j)-b2.(n)-b2.(j)))


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



(** LIMITS *)

(* k = 1 (G) *)
let phi = (1.+.sqrt(5.))/.2. (* root of X^2-X-1 *)
let tau = phi-.1.  (* also 1/phi, root of X^2+X-1 *)

(* k = 2 (H) *)
let limh = 0.6823278038280194 (* root of X^3+X-1, cf maxima *)
let expo = 1.465571231876768 (* 1/limh, also root of X^3-X^2-1 *)

(* k = 3 *)
let expo3 = 1.380277569097618


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
let _ = lims.(3)-.1./.expo3;;


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

let _ = extrems delta2 (* -0.7..0.85 hence more than 1 of wide *)

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
let rec s2 n = if n<4 then n+1 else s3 (n-1) + s3 (n-3)

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




(** FLIPPED *)

(** "flipped" functions *)

let rec h' x = if x <= 5 then h x else x+1 - h' (h' (1 + h' (x-1)))

let _ = Array.init 30 (fun i -> i,h' i)

let rec f3' x = if x <= 6 then a3.(x) else x+1 - f3' (f3' (f3' (1 + f3' (x-1))))

let _ = Array.init 30 (fun i -> i,f3' i)
