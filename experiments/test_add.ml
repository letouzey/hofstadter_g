
#use "defs.ml";;

let ff = tabulate_f 100 1_000_000

let a = tabulate_A 100 200 (* beware of overflows, coded here as -1 *)

let invA_up k n = invA_up_tab a.(k) n

let add_bound k p = a.(k).(invA_up k p + 3*k-1)

let all_diffs k p =
  extrems (Array.init (add_bound k p) @@ fun i -> ff.(k).(p+i)-ff.(k).(i))

(* Helper for Coq proofs that a specific f_k is below f_{k+1}:
   find a interesting shift and bounds on the growth of f_k and f_{k+1}.
   See GenAdd.v. Sadly, these numbers double roughly at each step. *)

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
# let _ = search 8;;
- : int * (int * int) * (int * int) = (2469, (2022, 2049), (2049, 2079))
# let _ = search 9;;
- : int * (int * int) * (int * int) = (5298, (4402, 4446), (4446, 4504))
*)
