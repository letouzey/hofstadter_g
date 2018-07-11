
let float = float_of_int
let int = int_of_float


let rec d n = if n = 0 then 0 else n - d(n-1);;
let rec g n = if n = 0 then 0 else n - g (g (n-1));;

let rec h n = if n = 0 then 0 else n - h (h (h (n-1)));;

let rec iter f n = if n=1 then f else fun x -> iter f (n-1) (f x);;

let rec f k n = if k=0 then n else if n = 0 then 0 else
            n - iter (f k) k (n-1)

let _ = Array.init 20 @@ fun n -> n, d n
let _ = Array.init 20 @@ fun n -> n,f 6 n
let _ = Array.init 20 @@ f 2
let _ = Array.init 20 h
let _ = Array.init 20 @@ f 3

let _ = Array.init 100 @@ fun n -> g n - d n


(** LIMITS *)

(* k = 2 *)
let phi = (1.+.sqrt(5.))/.2. (* root of X^2-X-1 *)
let tau = phi-.1.  (* also 1/phi, root of X^2+X-1 *)

(* k = 3 *)
let limh = 0.6823278038280194 (* root of X^3+X-1, cf maxima *)
let expo = 1.465571231876768 (* 1/limh, also root of X^3-X^2-1 *)

(* k = 4 *)

let expo4 = 1.380277569097618

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

let lims = Array.init 20 newton

let _ = lims.(2)-.tau;;
let _ = lims.(3)-.limh;;
let _ = lims.(4)-.1./.expo4;;



let tabulate k n =
  let a = Array.make_matrix k n 0 in
  for j = 0 to n-1 do a.(0).(j) <- j done;
  for i = 1 to k-1 do
    for j = 1 to n-1 do
      let x = ref (j-1) in
      for p = 1 to i do
        x := a.(i).(!x)
      done;
      a.(i).(j) <- j - !x
    done
  done;
  a

let a = tabulate 1000 1000

let check k n a =
  for i = 1 to k-2 do
    for j = 0 to n-1 do
      if a.(i).(j) > a.(i+1).(j) then Printf.printf "(%d,%d)\n" i j
    done
  done

let _ = check 1000 1000 a


(** FLOAT EXPRESSIONS OR APPROXIMATIONS *)

(* f1 is a division by 2, with two possible statements *)

let t1 = Array.init 1000 @@ fun i -> int ( float (i+1) /. 2.)

let t1' = Array.init 1000 @@ fun i -> int ( ceil (float i /. 2.))

let _ = t1 = a.(1)
let _ = t1' = a.(1)

(* f2 (named g earlier) is fun n -> floor ((n+1) / phi).
   This implies that for all n, f2(n) is either floor(n/phi)
   or ceil(n/phi), and hence is at most 1 away from the other.
*)

(* Justification:
(n+1)/phi = n/phi + 0.618
donc floor ((n+1)/phi) is either floor(n/phi) or
 floor(n/phi)+1 = ceil(n/phi) (as soon as n<>0, phi being irrational)
 *)

let t2 = Array.init 1000 @@ fun i -> int ( float (i+1) /. phi)

let t2' = Array.init 1000 @@ fun i -> float i /. phi)

let _ = t2 = a.(2)

type fc = F | C
let _ = Array.init 1000 @@
          fun i ->
          if a.(2).(i) = int (t2'.(i)) then F
          else if a.(2).(i) = int (ceil (t2'.(i))) then C
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

(* f3 and float computation *)


let hbis n = int (limh *. float n)
let hter n = int (ceil (limh *. float n))

let _ = Array.init 20 @@ fun n -> (hbis n, h n, hter n)

let _ = Array.init 1000 @@ fun n ->
        if a.(3).(n) = hbis n then F
        else if a.(3).(n) = hter n then C
        else failwith "AWAY"

let _ = Array.init 1000 @@ fun n ->
        int (limh *. (float (n+1))) - a.(3).(n)
 (* majoritairement des 0, mais aussi quelques 1 et -1 *)


(* f4 and float computation *)

let out = Array.init 1000 @@ fun n ->
        a.(4).(n) - int(float n /. expo4)
  (* histo : (-1, 4); (0, 504); (1, 482); (2, 10) *)

let out = Array.init 1000 @@ fun n ->
        a.(5).(n) - int(float n *. lims.(5))
  (* histo : (-1, 55); (0, 475); (1, 411); (2, 59) *)

let histo a =
  let t = Array.copy a in
  let () = Array.sort compare t in
  let rec cumul a k i =
    if i >= Array.length t then [(a,k)]
    else if t.(i) = a then cumul a (k+1) (i+1)
    else (a,k)::cumul t.(i) 1 (i+1)
  in cumul t.(0) 1 1

let _ = histo out



(** DECOMPOSITION *)

(** Zeckendorf decomposition of rank 3 *)

(** The sequence.
    Similar to Fibonacci, but skipping a term in the addition *)
let rec a n = if n<4 then n else a (n-1) + a (n-3)

(** Ratio converges to expo *)
let _ = Array.init 20 (fun n -> float (a (n+2)) /. float (a (n+1)))

(** Memoized version of the sequence *)
let atab = Array.make 100 0

let rec aopt n =
  if n >= 100 then a n
  else
    let x = atab.(n) in
    if x<>0 then x
    else
      if n <4 then (atab.(n) <- n; n)
      else
        let x = aopt (n-1) + aopt (n-3) in
        (atab.(n) <- x; x)

let _ = aopt 70
let _ = atab

let _ = Array.mapi (fun i x -> float x /.(expo ** float i)) atab

(** a(n) ~ 0.89618 * expo^n *)

(** The decomposition *)

let rec decomp n =
  let rec loop k =
    if aopt k > n then k-1
    else loop (k+1)
  in
  if n = 0 then []
  else
    let x = loop 1 in
    x::(decomp (n-aopt x))

let _ = Array.init 100 (fun n -> n, decomp n)

let _ = atab.(0) <- 0

let prevdecomp l = List.map (function 1 -> 1 | n -> n-1) l
let sumdecomp l = List.fold_left (fun acc n -> acc + aopt n) 0 l

let _ = List.map (fun n -> h n, sumdecomp (prevdecomp (decomp n))) test



(** FLIPPED *)

(** "flipped" functions *)

let rec h' x = if x <= 5 then h x else x+1 - h' (h' (1 + h' (x-1)))

let _ = Array.init 30 (fun i -> i,h' i)

let rec f4' x = if x <= 6 then a.(4).(x) else x+1 - f4' (f4' (f4' (1 + f4' (x-1))))

let _ = Array.init 30 (fun i -> i,f4' i)
