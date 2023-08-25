
type tree =
  | One of int * tree
  | Two of int * tree * tree
  | Nop

let rec mk_ones n t =
  if n = 0 then t else mk_ones (n-1) (One (0,t))

(* Fk, profondeur p *)

let rec mk_tree k p =
 if p <= 0 then Nop
 else
   let g = mk_tree k (p-1) in
   let d =
     if p<k then mk_ones (p-1) Nop
     else mk_ones (k-1) (mk_tree k (p-k))
   in
   Two (0, g, d)

let _ = mk_tree 3 2

let mk_hof k p = mk_ones k (mk_tree k (p-k))

let test = mk_hof 2 5



(* largeur a profondeur p *)
let rec width p t =
  if p = 0 then 1 else
  match t with
  | Nop -> 0
  | One (_,t) -> width (p-1) t
  | Two (_,g,d) -> width (p-1) g + width (p-1) d

let _ = List.init 10 (fun n -> width n test)


let rec etete p t =
  if p = 0 then [t]
  else
    match t with
    | Nop -> []
    | One (_,t) -> etete (p-1) t
    | Two (_,g,d) -> etete (p-1) g @ etete (p-1) d

let _ = etete 4 test

let rec destruct = function
  | [] -> []
  | One (_,t) :: l -> t :: destruct l
  | Two (_,g,d) :: l -> g :: d :: destruct l
  | Nop::_ -> assert false

let rec rebuild n etage next_etage =
  match etage, next_etage with
  | [],_ -> []
  | One(_,_)::l, t::r -> One(n,t)::rebuild (n+1) l r
  | Two(_,_,_)::l, g::d::r -> Two(n,g,d)::rebuild (n+1) l r
  | _ -> assert false

let rec number p n etage =
  if p = 0 then etage
  else
    let next_etage = number (p-1) (n+List.length etage) (destruct etage) in
    rebuild n etage next_etage

let _ = number 5 1 [test]

let t2 = number 8 1 [mk_hof 2 8] |> List.hd

let t3 = number 9 1 [mk_hof 3 9] |> List.hd


let rec mk_fun_aux last = function
  | Nop -> []
  | One(n,t) -> (n,last) :: mk_fun_aux n t
  | Two(n,g,d) -> (n,last) :: mk_fun_aux n g @ mk_fun_aux n d

let mk_fun t = (0,0) :: List.sort compare (mk_fun_aux 1 t)

let truefun listpairs = fun n -> List.assoc n listpairs

let _ = mk_fun t2
let _ = mk_fun t3
let f2 = truefun (mk_fun t2)
let _ = List.init 35 f2
