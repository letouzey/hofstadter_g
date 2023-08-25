
#use "defs.ml";;

let ff = tabulate_f 10 1_000_000

(** applying and repeating substitution *)

let dosubst f w =
  (* naive code : List.flatten (List.map f w) *)
  let rec loop acc = function
    | [] -> List.rev acc
    | a::w -> loop (List.rev_append (f a) acc) w
  in loop [] w

let itersubst f n init = iter (dosubst f) n init

(* Increments *)

let delta a =
  let h,w = Array.length a, Array.length a.(0) in
  let d = Array.make_matrix h (w-1) 0 in
  for i = 0 to h-1 do
    for j = 0 to w-2 do
      d.(i).(j) <- a.(i).(j+1)-a.(i).(j)
    done
  done;
  d

let d = delta ff
let d0 = d.(0)
let d1 = d.(1)
let d2 = d.(2)
let d3 = d.(3)
let d4 = d.(4)

(* Consecutive [+1] steps bewteen flat [+0] *)

let nbsteps array =
  let l = ref [] in
  let p = ref (-1) in
  for i = 0 to Array.length array -1 do
    if array.(i) = 0 then begin
        l := i - !p - 1 :: !l;
        p := i
      end
  done;
  List.rev !l

let steps1 = nbsteps d1

let subst1 = function 1->[1;2] | 2->[1;2;2] | _ -> []

let _ = itersubst subst1 2 [2]

let _ = all2 (=) steps1 (itersubst subst1 15 [1])

let subst1red = function 2->[2;1] | 1->[2] | _ -> []

(* 1->12  2->122

1
12
12122
1212212122122

Cf fibonacci word 0->01 1->0, en jetant le premier 1,
 et en écrivant 0 pour les 2.
 Donc : 2->21 1->2 et lettre initiale 2.
 Croissance plus lente

 2
 21
 212
 21221
 21221212
 2122121221221

Sous cette forme, mot M(n+1) = Mn @ M(n-1)

*)

let steps2 = nbsteps d2

let subst2 = function 1->[1;3] | 2 -> [1;2;3] | 3 -> [1;2;3;3] | _ -> []

let _ = all2 (=) steps2 (itersubst subst2 12 [1])

let subst2red = function 3 -> [3;1] | n -> [n+1]

(* 1->13 2->123 3->1233

1
13
131233
1312331312312331233

Cf modified Jacobi-Perron subst (livre Pytheas Fogg p. 254) :
1->12 2->3 3->1

Ici on adapte (par renommage) en:
3->31 1->2 2->3

Donne encore la suite précédente moins premiere lettre

 3
 31
 312
 3123
 312331
 312331312
 3123313123123

Sous cette forme, mot M(n+1) = Mn @ M(n-2)

*)

let _ = List.iter print_int @@ itersubst (function 3->[3;1]|n ->[n+1]) 6 [3]

let steps3 = nbsteps d3

let subst3 = function
  | 1 -> [1;4]
  | 2 -> [1;2;4]
  | 3 -> [1;2;3;4]
  | 4 -> [1;2;3;4;4]
  | _ -> []

let _ = all2 (=) steps3 (itersubst subst3 11 [1])

let _ = List.length (itersubst subst3 11 [1])

(* Version réduite : 4->41 1->2 2->3 3->4 *)

let subst3red = function 4 -> [4;1] | n -> [n+1]

let _ = List.map (itersubst subst3red 6) [[1];[2];[3];[4]]


let _ = List.iter print_int @@ itersubst subst3 3 [1]
(* 14123441412412341234412344 *)

let _ = List.iter print_int @@ itersubst subst3red 9 [4]
(*  41234414124123412344123441 *)

let steps4 = nbsteps d4

let subst4 = function
  | 1 -> [1;5]
  | 2 -> [1;2;5]
  | 3 -> [1;2;3;5]
  | 4 -> [1;2;3;4;5]
  | 5 -> [1;2;3;4;5;5]
  | _ -> []

let _ = all2 (=) steps4 (itersubst subst4 10 [1])

let steps10 = nbsteps d.(10)

let rec seq a b = if b=0 then [] else a::seq (a+1) (b-1)
let _ = seq 1 10

let subst10 n = seq 1 n @ [11]

let _ = itersubst subst10 8 [1]
let _ = all2 (=) steps10 (itersubst subst10 8 [1])

let subst10red = function 11 -> [11;1] | n -> [n+1]

let _ = all2 (=) (List.tl steps10) (itersubst subst10red 70 [11])


(* TODO :
   x preuve lien subst/substred ?
   x approche directe substred en lien avec fk ?
     Oui, en regardant =+ vs. =++ vs. =+++ au premier niveau
   - lien avec figure fractale Jacobi-Perron ?
   - proximité avec n*root(X^k...) ?
   x limite fk(n)/n
   - quasi additivité ?
   - croissance des fk avec k
 *)

