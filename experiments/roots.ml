(** ROOTS *)

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
  let fk = float_of_int k in
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

