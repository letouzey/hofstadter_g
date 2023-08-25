(* Study of the "triangular" initial zone *)

#use "defs.ml";;

let ff = tabulate_f 100 100_000

(* Tableau des valeurs de f *)

let printtab a x =
  for i = 2 to x do
    Printf.printf "%2d: " i;
    for j = 0 to i-2 do
      Printf.printf "%2d " a.(j).(i)
    done;
    print_newline ()
  done

(* Pas ce que je voulais, mais étonnant !! *)

let ffk = Array.map (fun a -> Array.map (fun j -> j - a.(j)) a) ff

let _ = printtab ffk 40

(* Ce que je voulais *)

let ffdiff = Array.map (Array.mapi (fun j x -> j-x)) ff

let _ = printtab ffdiff 40

(*
Soit k.
Avec n = (k+4)(k+5)/2-{2,1}, on a:
  n - f k n = k+4
  n - f (k+1) n = k+3
*)

let _ = Array.init 100 @@
          fun k ->
          let n = (k+4)*(k+5)/2-2 in
          n-ff.(k).(n)=k+4,
          n-ff.(k+1).(n)=k+3,
          (n+1)-ff.(k).(n+1)=k+4,
          (n+1)-ff.(k+1).(n+1)=k+3

let _ = ffdiff.(10).(2)

let rec steps n =
 if n = 0 then 0
 else 1+steps (n-1-steps (n-1))

let _ = Array.init 40 steps

let _ = printtab ff 40

let printfun f x =
  for i = 2 to x do
    Printf.printf "%2d: " i;
    for j = 0 to i-2 do
      Printf.printf "%2d " (f j i)
    done;
    print_newline ()
  done

(* Comme ffdiff *)
let _ = printfun (fun i j -> j - ff.(i).(j)) 40

(* f^2 *)
let _ = printfun (fun i j -> ff.(i).(ff.(i).(j))) 40

let _ = printfun (fun i j -> j-1-ff.(i).(ff.(i).(j))) 40

(* f^2 va de n/4 à n-2 *)

(* f^3 *)
let _ = printfun (fun i j ->
            j-ff.(i).(ff.(i).(ff.(i).(j)))) 40

(* f^3 va de n/8 à n-3 *)
