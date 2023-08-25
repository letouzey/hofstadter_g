
(** See definition of Generalized Fibonacci sequences in defs.ml *)

#use "defs.ml";;
#use "roots.ml";;

let gfib1 = memo_A 1 10
(* [|1; 2; 3; 5; 8; 13; 21; 34; 55; 89; 144|] *)

let gfib2 = memo_A 2 30

(* Reduced A numbers : A k n * lims.(k)^n
   They have a finite nonzero limit when n->\infty
*)

let rA k n =
 Array.mapi (fun i a -> float a*.(lims.(k)**float i)) (memo_A k n)

(* NB: A k i = i+1 when i <= k+1 *)

let _ = memo_A 0 2
let _ = memo_A 1 3
let _ = memo_A 4 6

(* Hence initial rfib k i is (i+1)/lims.(k)^i *)

let _ = rA 0 1 (* [|1.;1.|] *)
let _ = rA 1 2 (* [|1.; 1.23606797749978958; 1.14589803375031529|] *)
let _ = rA 2 3
(* [|1.; 1.36465560765603855; 1.3967136956303039; 1.27068878468792246|] *)
let _ = rA 3 4
(* [|1.; 1.44898391800103132; 1.57466579596921474; 1.52111027639045671;
  1.37754020499742236|] *)
let _ = rA 4 5
(* [|1.; 1.50975533249338545; 1.70952087299415956; 1.72063883600778667;
  1.62358978622372963; 1.47073400251984321|] *)
let _ = rA 5 6
(* [|1.; 1.55617919735720212; 1.8162702707154792; 1.88429467471050849;
  1.83268760904715577; 1.71119419947209561; 1.55337280924979182|] *)
let _ = rA 6 7
(* [|1.; 1.59308870825691429; 1.90344872428176282; 2.02157511293287;
  2.0128428033165946; 1.92398228487591583; 1.7879600975379264;
  1.62764516697234374|] *)
let _ = rA 7 8
let _ = rA 8 9
let _ = rA 9 10
let _ = rA 10 11
let _ = rA 11 12
let _ = rA 19 20

(* Bref, rA k commence par 1. puis croissant jusqu'à un maximum vers k/3
puis décroissant jusqu'à k+1 *)

let _ = rA 0 60 (* 1 tout le temps *)
let _ = rA 1 60 (* converge vers 1.1708203932499 environ *)
let _ = rA 2 80 (* 1.31342305985234 *)
let _ = rA 3 100 (* 1.43970621227693 *)
let _ = rA 4 100 (* 1.55496703216 *)
let _ = rA 5 100 (* 1.66211747 *)
let _ = rA 6 100 (* 1.7629650 *)
let _ = rA 7 100 (* 1.858724 *)
let _ = rA 8 100 (* 1.95025 *)
let _ = rA 9 200 (* 2.03821 *)
let _ = rA 10 200 (* 2.123075 *)
let _ = rA 19 250 (* 2.7933 *)

(* Prouvé en Coq : A k n / root k ** n a une limite réelle
   (cf ThePoly.A_div_pow_mu_limit)
   De plus : root k ** n <= A k n (cf Freq.A_gt_mu_pow)
   Donc la limite en question est >= 1
   Donc A k (n+1) / A k n converge vers root k
*)
