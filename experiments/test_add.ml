
(** utils *)

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

(** the recursive function *)

let rec iter f n = if n=0 then fun x -> x else fun x -> iter f (n-1) (f x)

let rec f k n = if n = 0 then 0 else n - iter (f k) (k+1) (n-1)

(** Tabulate : Faster computation of [f k n] via an array
    - First line (k=0) is function d (division by two)
    - Second line (k=1) is function g
    - Third line (k=2) is function h
*)

let tabulate_f k n =
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

let ff = tabulate_f 100 1000000

let tabulate_a k n =
  let a = Array.make_matrix (k+1) (n+1) 0 in
  for i = 0 to k do
    for j = 0 to n do
      a.(i).(j) <- if j <= i+1 then j+1 else a.(i).(j-1)+a.(i).(j-i-1)
    done
  done;
  a

let a = tabulate_a 100 60 (* attention aux overflows *)

let rec invA k n =
  if n = 0 then 0
  else
    let p = invA k (n-1) in
    if a.(k).(p+1) = n+1 then p+1 else p

let invA_up k n = 1+invA k (max 0 (n-2))

let add_bound k p = a.(k).(invA_up k p + 3*k-1)

let all_diffs k p =
  extrems (Array.init (add_bound k p) @@ fun i -> ff.(k).(p+i)-ff.(k).(i))

let search k =
  let rec loop p =
    let a,b = all_diffs k p in
    let c,d = all_diffs (k+1) p in
    if b <= c then (p,(a,b),(c,d)) else loop (p+1)
  in loop 5

(*
# let _ = search 1;;
- : int * (int * int) * (int * int) = (8, (4, 5), (5, 6))
# let _ = search 2;;
- : int * (int * int) * (int * int) = (33, (22, 23), (23, 25))
# let _ = search 3;;
- : int * (int * int) * (int * int) = (73, (51, 54), (54, 57))
# let _ = search 4;;
- : int * (int * int) * (int * int) = (169, (125, 129), (129, 135))
# let _ = search 5;;
- : int * (int * int) * (int * int) = (424, (326, 333), (333, 342))
# let _ = search 6;;
- : int * (int * int) * (int * int) = (843, (666, 677), (677, 692))
# let _ = search 7;;
- : int * (int * int) * (int * int) = (1617, (1304, 1322), (1322, 1345))

Double grosso modo à chaque fois
*)

(* Tableau des valeurs de f *)

let printtab a x =
  for i = 2 to x do
    Printf.printf "%2d: " i;
    for j = 0 to i-2 do
      Printf.printf "%2d " a.(j).(i)
    done;
    print_newline ()
  done

(* Pas ce que je voulais, mais
   étonnant !! *)

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


