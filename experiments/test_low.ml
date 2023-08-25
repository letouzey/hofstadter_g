(* Where are f_k and f_{k+1} equal ? apart by 1 ? etc *)

#use "defs.ml";;

(* search_near k n p : biggest m <= n such that a.(k+1).(m)-a.(k).(m) <= p *)

let search_near k n p =
  let a = tabulate_f k n in
  let t = Array.make k 0 in
  for i = 0 to k-1 do
    for j = 0 to n do
      if a.(i+1).(j) - a.(i).(j) <= p then t.(i) <- j
    done;
  done;
  t

let diffs = array_diffs (-)

let t = search_near 200 30000 0 (* last equality between f_k and f_(k+1) *)
let dt = diffs t
let _ = dt = Array.init 199 ((+) 5)
 (* dt is (fun k -> k+5)
    hence t is (fun k -> (k+4)(k+5)/2 - 3) *)

let t = search_near 50 30000 1
let dt = diffs t
let d2t = diffs dt
let _ = Array.mapi (fun i n -> n-(i+8)) d2t
 (* d2t is (fun k -> k+8) except in k=0 and k=1
    hence t is some polynom of degree 3 *)

let d2t' = function 0 -> 14 | 1 -> 6 | n -> n+8
let dt' = function 0 -> 15 | 1 -> 29 | n -> 17 + 9*n + ((n-2)*(n-1))/2
let _ = Array.init 50 dt'
let dt' = function 0 -> 15 | 1 -> 29 | n -> 18 + 7*n + (n*(n+1))/2
let _ = Array.init 50 dt'
let t' = function 0 -> 15 | 1 -> 30 | n-> 15+18*n+((n-1)*n*(n+22))/6
let _ = Array.init 50 t'




let t = search_near 49 30000 2
let dt = diffs t
let d2t = diffs dt
let _ = Array.mapi (fun i n -> n-(i+9)) d2t
 (* d2t is (fun k -> k+9) except in k=0 and k=1 *)

let t = search_near 49 30000 3
let dt = diffs t
let d2t = diffs dt
let _ = Array.mapi (fun i n -> n-(i+9)) d2t
 (* d2t is (fun k -> k+9) except in k=0 and k=1 *)

let t = search_near 48 30000 4
let dt = diffs t
let d2t = diffs dt
let _ = Array.mapi (fun i n -> n-(i+10)) d2t
 (* d2t is (fun k -> k+10) except in k=0 *)

let t = search_near 48 30000 5
let dt = diffs t
let d2t = diffs dt
let _ = Array.mapi (fun i n -> n-(i+10)) d2t
 (* d2t is (fun k -> k+10) except for k<=3 *)

let t = search_near 48 30000 6
let dt = diffs t
let d2t = diffs dt
let _ = Array.mapi (fun i n -> n-(i+11)) d2t
 (* d2t is (fun k -> k+11) except for k<=4 *)

let t = search_near 48 30000 7
let dt = diffs t
let d2t = diffs dt
let _ = Array.mapi (fun i n -> n-(i+11)) d2t
 (* d2t is (fun k -> k+11) except for k<=5 *)

let t = search_near 48 30000 8
let dt = diffs t
let d2t = diffs dt
let _ = Array.mapi (fun i n -> n-(i+11)) d2t
 (* d2t is (fun k -> k+11) except for k<=8 *)

let t = search_near 48 30000 9
let dt = diffs t
let d2t = diffs dt
let _ = Array.mapi (fun i n -> n-(i+11)) d2t
 (* d2t is (fun k -> k+11) except for k<=12 *)

let t = search_near 47 30000 10
let dt = diffs t
let d2t = diffs dt
let _ = Array.mapi (fun i n -> n-(i+12)) d2t
 (* d2t is (fun k -> k+12) except for k<=13 *)

let t = search_near 100 1000000 20
let dt = diffs t
let d2t = diffs dt
let _ = Array.mapi (fun i n -> i,n-(i+13)) d2t
 (* d2t is (fun k -> k+13) except for k<=46
    /!\ many +14 between k=23 and k=43 *)

let t = search_near 100 1000000 30
let dt = diffs t
let d2t = diffs dt
let _ = Array.mapi (fun i n -> i,n-(i+15)) d2t
 (* d2t is (fun k -> k+15) except for k<=45 and k=77 and k=78 *)


(* What is the range of a particular delta between f_k and f_{k+1} ? *)

let a = tabulate_f 100 1000000

let fstlast a x =
  let fst = ref None and lst = ref None in
  Array.iteri (fun i y -> if x = y then
                            begin
                              lst := Some i;
                              (if !fst = None then fst := Some i);
                            end) a;
  match !fst, !lst with Some a, Some b -> (a,b) | _ -> 0,0

let d_1_2 = Array.map2 (-) a.(2) a.(1);;

let itvls_1_2 = Array.init 21 (fun i -> i,fstlast d_1_2 i);;
 (* e.g. first delta of 2 between f1 and f2 at n=25, last at n=78 *)
let itvls_2_3 =
  Array.init 21 (fun i -> i,fstlast (Array.map2 (-) a.(3) a.(2)) i);;
