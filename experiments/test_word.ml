
#use "defs.ml";;
#use "test_add.ml";;

(* let ff = tabulate_f 100 1_000_000 *)

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

let tabulate k n =
  let a = Array.make (n+1) [k] in
  for i = 1 to n do
    if i <= k then a.(i) <- a.(i-1) @ [i-1]
    else a.(i) <- a.(i-1) @ a.(i-1-k)
  done;
  a

let mkchar n =
  if n < 10 then Char.chr (n+Char.code '0')
  else if n < 10+26 then Char.chr (n-10 + Char.code 'a')
  else failwith "mkchar : too large"

let mkstring n = String.make 1 (mkchar n)

let ofchar c =
  let n = Char.code c in
  if Char.code '0' <= n && n <= Char.code '9' then n - Char.code '0'
  else 10 + n - Char.code 'a'

let string_tabulate k n =
  let a = Array.make (n+1) (mkstring k) in
  for i = 1 to n do
    if i <= k then a.(i) <- a.(i-1) ^ mkstring (i-1)
    else a.(i) <- a.(i-1) ^ a.(i-1-k)
  done;
  a

let w1 = string_tabulate 1 10
let w2 = string_tabulate 2 20
let w3 = string_tabulate 3 20
let w4 = string_tabulate 4 20
let w5 = string_tabulate 5 20
let w6 = string_tabulate 6 20

let psuffix p w =
  let l = String.length w in
  if l < p then ""
  else String.sub w (l-p) p

let array_sort_uniq a =
  a |> Array.to_list |> List.filter ((<>) "")
    |> List.sort_uniq compare |> Array.of_list

let allpsuffix p ws = Array.map (psuffix p) ws |> array_sort_uniq

let _ = List.init 10 (fun p -> allpsuffix p w1)
let _ = List.init 10 (fun p -> allpsuffix p w2)
let _ = List.init 10 (fun p -> allpsuffix p w3)

let a2 = memo_A 2 100
let a3 = memo_A 3 100

let invA2 = invA_up_tab a2
let invA3 = invA_up_tab a3

let _ = List.init 20 invA2
let _ = a3.(21)

(* Suffix of size p of (M 3 n) *)
let rec suffixM3 n p =
  if n <= 3 then psuffix p w3.(n)
  else if a3.(n-4) < p then suffixM3 (n-1) (p - a3.(n-4)) ^ w3.(n-4)
  else suffixM3 (n-4) p

(* number of non-zero letters in all suffixes of size p of (M k) words *)
let nzsuff k p =
  let a = memo_A k 100 in
  let n = invA_up_tab a p in
  Array.init (k+1) (fun i -> ff.(k).(a.(n+i))-ff.(k).(a.(n+i)-p)) |> extrems

let para_nzsuff k p =
  let a = memo_A k 100 in
  let n = invA_up_tab a p in
  let idx = Array.init (k+1) (fun i -> a.(n+i)) in
  let base = Array.map (fun x -> ff.(k).(x)) idx in
  Array.init p (fun p ->
      Array.map2 (fun idx base -> base-ff.(k).(idx-p)) idx base |> extrems)

let s = para_nzsuff 2 2000

let s' = Array.init 2000 (nzsuff 2)
let _ = s = s'
let _ = List.init 20 (nzsuff 3)
let _ = List.init 20 (nzsuff 4)
let _ = List.init 20 (nzsuff 5)
let _ = List.init 20 (nzsuff 6)

(* additivity bounds, new method *)

let diffs k p =
  if p <= 1 then (0,p)
  else
    let su = para_nzsuff k p in
    let t = Array.init (p-1)
              (fun i ->
                let i = i+1 in
                let f = ff.(k).(i) in
                let (mi,ma) = su.(p-i) in
                (mi+f,ma+f))
    in
    (Array.map fst t |> extrems |> fst,
     Array.map snd t |> extrems |> snd)

let extrems_of_extrems p f = (* extrems of (f 0) .. (f (p-1)), p>0 *)
  let rec loop p mi ma =
    if p = 0 then (mi,ma)
    else let (a,b) = f p in loop (p-1) (min mi a) (max ma b)
  in
  let (a,b) = f 0 in
  loop (p-1) a b

let para_diffs k p =
  let su = para_nzsuff k p in
  Array.init p @@
    fun p ->
    if p <= 1 then (0,p)
    else
      extrems_of_extrems (p-1) @@
        fun i ->
        let f = ff.(k).(i+1) in
        let (mi,ma) = su.(p-i-1) in
        (mi+f,ma+f)

(* Et les cycles au debut ? Pas utile ? Apparemment pas ! *)

let d2opt = para_diffs 2 2000

let d2 = Array.init 2000 (diffs 2)
let d3 = Array.init 2000 (diffs 3)
let d4 = Array.init 2000 (diffs 4)
let d5 = Array.init 2000 (diffs 5)
let d6 = Array.init 2000 (diffs 6)

(* additivity bounds, old method, cf test_add.ml *)

let d2' = Array.init 2000 (all_diffs 2)
let _ = d2 = d2'

let d3' = Array.init 2000 (all_diffs 3)
let _ = d3 = d3'

let d4' = Array.init 2000 (all_diffs 4)
let d5' = Array.init 2000 (all_diffs 5)
let d6' = Array.init 2000 (all_diffs 6)


(* Easier(?) overapprox of diffs *)

let over_diffs k p =
  let t = Array.make p (0,0) in
  t.(1) <- (0,1);
  for i = 2 to p-1 do
    t.(i) <-
      extrems_of_extrems (i-1) @@
        fun j ->
        let f = ff.(k).(j+1) in
        let (mi,ma) = t.(i-j-1) in
        (mi+f,ma+f)
  done;
  t

let _ = over_diffs 2 20
let _ = para_diffs 2 20

(* Trop approximé : borne inf c'est p/2, borne sup c'est p.
   Idem même si on utilise la bonne formule pour p <= k *)

(* application à la recherche de preuve de f_k <= f_{k+1} *)

let search k guess =
  let rec loop i s t1 t2 =
    if i < s then
      let a,b = t1.(i) in
      let c,d = t2.(i) in
      if b <= c then (i,(a,b),(c,d)) else loop (i+1) s t1 t2
    else loop i (2*s) (para_diffs k (2*s)) (para_diffs (k+1) (2*s))
  in loop 5 guess (para_diffs k guess) (para_diffs (k+1) guess)


let _ = search 1 10;;
(* (8, (4, 5), (5, 6)) *)
let _ = search 2 40;;
(* (33, (22, 23), (23, 25)) *)
let _ = search 3 80;;
(* (73, (51, 54), (54, 57)) *)
let _ = search 4 200;;
(* (169, (125, 129), (129, 135)) *)
let _ = search 5 500;;
(* (424, (326, 333), (333, 342)) *)
let _ = search 6 900;;
(* (843, (666, 677), (677, 692)) *)
let _ = search 7 1800;;
(* (1617, (1304, 1322), (1322, 1345)) *)
(*
let _ = search 8 2500;;
(* (2469, (2022, 2049), (2049, 2079)) *)
let _ = search 9 6_000;;
(* (5298, (4402, 4446), (4446, 4504)) *)
let _ = search 10 9_000;;
(* (8222, (6909, 6973), (6973, 7053)) *)
let _ = search 11 15_000;;
(* (14164, (12021, 12118), (12118, 12233)) *)
let _ = search 12 30_000;;
(* (29662, (25406, 25585), (25585, 25793)) *)
*)


let psubs p w =
  let l = String.length w in
  if l < p then []
  else List.init (l-p+1) (fun i -> String.sub w i p)

let _ = psubs 3 "1234"

let allpsubs p w = List.sort_uniq compare (psubs p w)

let arraylast a = let n = Array.length a in a.(n-1)

let factors1 = List.init 10 (fun p -> allpsubs (p+1) (arraylast w1))
let factors2 = List.init 10 (fun p -> allpsubs (p+1) (arraylast w2))
let factors3 = List.init 10 (fun p -> allpsubs (p+1) (arraylast w3))
let factors4 = List.init 15 (fun p -> allpsubs (p+1) (arraylast w4))
let _ = List.init 10 (fun p -> allpsubs p (arraylast w4) |> List.length)
let _ = List.init 10 (fun p -> allpsubs p (arraylast w5) |> List.length)
let _ = List.init 10 (fun p -> allpsubs p (arraylast w6) |> List.length)
(* conjecture: complexité (fun p -> k*p+1) *)

let rec count_repet l =
  match l with
  | [] -> []
  | x::l ->
     match count_repet l with
     | [] -> [(x,1)]
     | ((y,n)::rest) as l -> if x = y then (y,n+1)::rest else (x,1)::l

let count_special l = count_repet l |> List.filter (fun (_,n) -> n>1)

let rec rightspecial ll = match ll with
| [] -> []
| l::rest ->
   let p = String.length (List.hd l) - 1 in
   let l' = List.map (fun w -> String.sub w 0 p) l |> List.sort compare in
   count_special l' :: rightspecial rest

let rs2 = rightspecial factors2
let rs3 = rightspecial factors3
let rs4 = rightspecial factors4

let _ = factors4

let rec leftspecial ll = match ll with
| [] -> []
| l::rest ->
   let p = String.length (List.hd l) - 1 in
   let l' = List.map (fun w -> String.sub w 1 p) l |> List.sort compare in
   count_special l' :: leftspecial rest

let ls2 = leftspecial factors2
let ls3 = leftspecial factors3
let ls4 = leftspecial factors4

let bispecial factor =
  let inter rs ls =
    let pr = List.hd ls |> fst in
    if List.exists (fun (r,_) -> r = pr) rs then [pr] else []
  in List.map2 inter (rightspecial factor) (leftspecial factor)

let _ = bispecial factors2
let _ = bispecial factors3
let _ = bispecial factors4

let _ = Array.init 13 (fun i -> (i,w4.(i)))

let left_letter k n =
  if n = k then
    (* before k : any letter 0 .. k may occur *)
    failwith "multiple letters possible"
  else if n = 0 then k else n-1

(* suffixes des M_i avec k en première lettre,
   quel suffixe étendu à gauche ?
   P.ex k=4

1:  4 -> 34  (on colle M_4 devant M_0)
2:  40 -> 440 (on colle M_5 devant M_1)

3:  401 -> 0401 (on colle M_6 devant M_2)
    440 -> 3440 (sous-partie de M_6=M_5.M_1=M_4.M_0.M_1, fin de M_4)

4:  4012 -> 14012 (on colle M_7 devant M_3)

5:  40401 -> 440401
    40123 -> 240123

6:  440401 -> 3
    401234 -> 3

7:  4014012 -> 0

8:  40123440 -> 4

9:  401240123 -> 1
    404014012 -> 4
    440123440 -> 3

10: 4404014012 -> 3

11: 40123401234 -> 2
    40123440401 -> 0

12: 401401240123 -> 0

TODO: Est-ce qu'il y en a pour tout p ??

*)

(*
let _ = Array.map (psuffix 7) w4
      |> Array.to_list |> List.filter (fun w -> w<>"" && w.[1]='4')
      |> List.sort_uniq compare
*)

let invA_up_modk aa k p last =
  let n = invA_up_tab aa p in
  (* choose the right last letter *)
  let rec loop n =
    let nlast = (n+k) mod (k+1) in
    if nlast = last then n
    else loop (n+1)
  in loop n

let rec opt_suffix_tab aa ww k p =
  if p = 1 then List.init (k+1) mkstring
  else
    let su = opt_suffix_tab aa ww k (p-1) in
    List.map
    (fun w -> if w.[0] = mkchar k then
                let n = invA_up_modk aa k p (ofchar w.[p-2]) in
                psuffix p (ww.(n))
              else
                let c = mkstring (left_letter k (ofchar w.[0])) in
                c^w)
    su |> List.sort_uniq compare

let opt_suffix k p =
  opt_suffix_tab (memo_A k 100) (string_tabulate k (max 30 (p+5))) k p

let _ = opt_suffix 4 60

let opt_psubs k p =
  let inits = psubs p (string_tabulate k k).(k) in
  let suf = opt_suffix k (p-1) in
  let pre = arraylast (string_tabulate k (max 30 (p+5))) in
  let ll = List.init (p-1) (fun i -> let i = i+1 in
                   List.map (fun w -> psuffix i w ^
                                      String.sub pre 0 (p-i))
                     suf)
  in (inits @ List.flatten ll) |> List.sort_uniq compare

let _ = opt_psubs 4 50 |> List.length

let reduce_psubs l =
  let p = String.length (List.hd l) in
  List.init p
    (fun i ->
      l |> List.map (fun w -> String.sub w 0 (i+1))
      |> List.sort_uniq compare)

let factors4' = reduce_psubs (opt_psubs 4 50)

let _ = bispecial factors4' |> List.map (List.map String.length);;

let _ = Array.init 13 (fun i -> (i,String.length w4.(i),w4.(i)))

let _ = ()

401234404014012401234
40123440401401240123

(* bispecial : au début des mots M_n entiers, mais pas tous, p.ex 40123 non
   ensuite plus compliqué que ça

M_n.M_{n-k} donc prol à droite possible par k
(et si n <= k alors on étend à g d'abord M_{n+k+1} = M_{n+k}.M_n
 puis M_{n+k+1}.M_{n+1})

Rq: dès qu'on sait que w est dans RS, alors valence 2 (sinon on aurait
 sa dernière lettre dans RS avec valence > 2). Donc avec -k-> et une autre
 on est bon

autre lettre : redescente jusqu'aux règles initiales ?

p.ex k=4   4 -0-> 40 -1-> 401 -2-> 4012 -3-> 40123=M_4

+gal si i<j<=k alors M_j = M_i.(i)...(j-1)

Pour n>=k, M_{n+k+2} = M_{n+k+1}.M_{n+1} = M_{n+k).M_n.M_n.M_{n-k}
Donc M_n.M_n facteur

M_{n-k} préfixe de M_n donc M_n = M_{n-k}.reste

Donc M_n.M_n = M_n.M_{n-k}.reste = M_{n+1}.reste

Pour M_5:  M_4 = M_0.0123 donc M_5 -0-> ..
Pour M_6:  M_5 = M_4.M_0 = M_1.123.M_0 donc M_6 -1-> ..
Pour M_7:  M_6 = M_5.M_1 = M_2.23.M_0.M_1 donc M_7 -2-> ..
Pour M_8:  M_7 = M_6.M_2 = M_3.3.M_0.M_1.M_2 donc M_8 -3-> ..
Pour M_9:  M_8 = M_7.M_3 = M_4.M_0.M_1.M_2.M_3
  donc M_9 -4-> .. mais on le savait déjà !
  Comment dire que rien d'autre n'est possible ?
Pour M_10: M_9 = M_8.M_4 = M_5.M_1.M_2.M_3.M_4
  marche plus, donne juste -k->

M5 = M4M0
...
M8 = M7M3
ensuite *pas* des Mx

M9M0 (de taille 21 alors que M9 de taille 20)
 M9M0 inclus dans M9M9=M9M8M4=M9M4...=M9M0.0123...
      -0->


M10M1
M11M2
M12M3
ensuite ?


*)
