
#use "defs.ml";;
#use "roots.ml";;

(** k=2 : Study of (f 2) a.k.a H, following Rauzy's paper *)

let ff = memo_f 2 1_000_000

(** applying and repeating substitution *)

let dosubst f w =
  (* naive code : List.flatten (List.map f w) *)
  let rec loop acc = function
    | [] -> List.rev acc
    | a::w -> loop (List.rev_append (f a) acc) w
  in loop [] w

let itersubst f n init = iter (dosubst f) n init

(* subst on letters 1 2 3 *)
let subst = function 1->[1;2] | 2->[3] | _->[1]

let mot = Array.of_list (itersubst subst 25 [1])
let _ = Array.length mot

let cumul letter mot =
  let n = Array.length mot in
  let a = Array.make n 0 in
  for i = 1 to n-1 do
    a.(i) <- a.(i-1) + (if mot.(i-1)=letter then 1 else 0)
  done;
  a

let r1 = cumul 1 mot
let r2 = cumul 2 mot
let r3 = cumul 3 mot

let _ = for i = 0 to Array.length mot -1;
        do assert (r1.(i)+r2.(i)+r3.(i) = i); done

let hbis n = if n=0 then 0 else n - r2.(n)

let _ = for i = 0 to Array.length mot -1; do assert (hbis i = ff.(i)); done

let rauzy_delta1 n = limh*.limh*.float n -. float (r1.(n))
let rauzy_delta2 n = (1.-.limh)*.float n -. float (r2.(n))

let _ = output_gnuplot_file "/tmp/rauzy"
          (Array.init 10000 @@ fun i -> rauzy_delta1 i, rauzy_delta2 i)

let _ = output_gnuplot_file "/tmp/rauzy_my"
          (Array.init 10000 @@ fun i -> rauzy_delta2 i,
                                        -. rauzy_delta1 i -. limh *.rauzy_delta2 i)

let b (x,y) = (-.limh*.limh*.x-.y, limh*.x)

let vect_z = (limh*.limh-.1.,limh**3.)
let vectBz = b vect_z
let vectBBz = b vectBz

let coins =
  let a = 1.21 and b = 0.996 in
  [|a,b;a,-.b;-.a,-.b;-.a,b;a,b|]

let addpair (a,b) (c,d) = (a+.c,b+.d)

let bcoins = Array.map b coins
let b3coins_p_z = Array.map (fun p -> addpair vect_z (b (b (b p)))) coins

let _ = output_gnuplot_file "/tmp/bcoins" bcoins
let _ = output_gnuplot_file "/tmp/b3coins" b3coins_p_z

let _ = output_gnuplot_file "/tmp/rauzyB"
          (Array.init 10000 @@ fun i -> b (rauzy_delta1 i, rauzy_delta2 i))

let _ = output_gnuplot_file "/tmp/rauzyB2"
          (Array.init 10000 @@ fun i -> b (b (rauzy_delta1 i, rauzy_delta2 i)))

let _ = output_gnuplot_file "/tmp/rauzyB3"
          (Array.init 10000 @@ fun i -> b (b (b (rauzy_delta1 i, rauzy_delta2 i))))

let _ = output_gnuplot_file "/tmp/rauzyB4"
          (Array.init 10000 @@ fun i -> b (b (b (b (rauzy_delta1 i, rauzy_delta2 i)))))

let _ = output_gnuplot_file "/tmp/rauzyB5"
          (Array.init 10000 @@ fun i -> b (b (b (b (b (rauzy_delta1 i, rauzy_delta2 i))))))

(* subst2 is subst with different letters : 1->2, 2->0, 3->1 *)

let subst2 = function 2 -> [2;0] | n -> [n+1]

(* subst2 is an alternative subst using 4 letters *)

let subst2b = function 2|3 -> [3;0] | n -> [n+1]

let mot2 = Array.of_list (itersubst subst2 36 [2])
let mot2b = Array.of_list (itersubst subst2b 36 [3])
let _ = Array.length mot2

(* Alt definition for H *)
let h' n =
  let r = ref 0 in
  for i = 0 to n-1 do
    if mot2.(i) <> 0 then incr r
  done;
  !r

let t = Array.init 100000 @@
          fun i ->
          (mot2.(i), float ff.(i) -. float i *. lims.(2))


let t0_delta_next =
  Array.init 50000 @@ fun i ->
                      let (u,v) = t.(i) in
                      if u=0 then v,snd t.(i+1)
                      else 0.,0.

let _ = extrems (Array.map fst t0_delta_next)
  (*  (-0.0221187768729578238, 0.850466788466292201) *)
let _ = extrems (Array.map snd t0_delta_next)
  (*  (-0.704446580701187486, 0.168138984638062539) *)

let _ = output_gnuplot_file "/tmp/h_0" t0_delta_next

let _ = lims.(2)

(* n de rang 0 : une unique ligne croissante (-0.022,-0.70)..(0.85,0.168)
   y = x - 0.68 (h plat)
*)

let t1_delta_next =
  Array.init 50000 @@ fun i ->
                      let (u,v) = t.(i) in
                      if u=1 then v,snd t.(i+1)
                      else -0.5,0.

let _ = extrems (Array.map fst t1_delta_next)
  (* (-0.704446580701187486, -0.102549800049018813) *)
let _ = extrems (Array.map snd t1_delta_next)
  (* (-0.386774384529417148, 0.215122396122751525) *)

let _ = output_gnuplot_file "/tmp/h_1" t1_delta_next

(* n de rang 1 : une unique ligne croissante (-0.70,-0.38)..(-0.10,0.215)
   y = x + 0.317
   car h(n+1)-(n+1).alpha = h(n)-n.alpha + (1-alpha)
*)

let t2_delta_next =
  Array.init 50000 @@ fun i ->
                      let (u,v) = t.(i) in
                      if u=2 then v,snd t.(i+1)
                      else 0.,0.

let _ = extrems (Array.map fst t2_delta_next)
  (* (-0.386774384529417148, 0.532794592294521863) *)
let _ = extrems (Array.map snd t2_delta_next)
  (* (-0.0691021883576468099, 0.850466788466292201) *)

let _ = output_gnuplot_file "/tmp/h_2" t2_delta_next

(* n de rang >=2 : une unique ligne croissante (-0.38,-0.069)..(0.53,0.85) *)


(* rang 0 : next 1 ou 2+ (car renorm (1::...) donc 1 ou 3+)
   rang 1 : next 2+
   rang 2+ : next 0 ou 2+ (car exact 2 donc renorm(3::...) donc 2+
                           mais 3+ donne 0::3 donc 0)

Subdiviser 2+ en 2 et 3+ : cf mot2b

 rang 0 : next 1 ou 3+
 rang 1 : next 2 ou 3+ (car renorm (2::...))
 rang 2 : next 3+
 rang 3+ : next 0

*)

let t2bis_delta_next =
  Array.init 50000 @@ fun i ->
                      if mot2b.(i)=2 then snd t.(i),snd t.(i+1)
                      else 0.,0.

let _ = extrems (Array.map fst t2bis_delta_next)
  (* (-0.386774384529417148, 0.215122396122751525) *)
let _ = extrems (Array.map snd t2bis_delta_next)
  (* (-0.0691021883576468099, 0.532794592294521863) *)

let t3bis_delta_next =
  Array.init 50000 @@ fun i ->
                      if mot2b.(i)=3 then snd t.(i),snd t.(i+1)
                      else 0.,0.

let _ = extrems (Array.map fst t3bis_delta_next)
  (* (-0.339790973044728162, 0.532794592294521863) *)
let _ = extrems (Array.map snd t3bis_delta_next)
  (* (-0.0221187768729578238, 0.850466788466292201) *)

let _ = output_gnuplot_file "/tmp/h_2b" t2bis_delta_next
let _ = output_gnuplot_file "/tmp/h_3b" t3bis_delta_next

(* Zeckendorf decomp for k=2 *)

let a2 = memo_A 2 100

let invA = invA_tab a2

let rec decomp n =
  if n = 0 then []
  else
    let x = invA n in
    x::(decomp (n-a2.(x)))

let rank2_max3 n =
  match List.rev (decomp n) with
  | [] -> 3
  | r::_ -> min r 3

let _ = Array.init 100 rank2_max3

let prefix_max3 = Array.init 20 (fun i -> Array.init a2.(i) rank2_max3)

let _ =
  for i = 1 to 16 do
    assert (prefix_max3.(i+3) = Array.append prefix_max3.(i+2) prefix_max3.(i))
  done

let _ =
  for i = 0 to Array.length prefix_max3.(19) - 1 do
    assert (mot2b.(i) = prefix_max3.(19).(i))
  done

(* Seule exception : 3012 n'est pas 301++3 sinon ensuite M(n+1)=Mn++M(n-2)

M0 = 3
M1 = 30
M2 = 301
M3 = 3012
puis
M(n+1) = Mn++M(n-2)

Expression via substitution : 0->1, 1->2, 2->30, 3->30

3
30
301
3012
301230
301230301
3012303013012
3012303013012301230
3012303013012301230301230301

Comparaison avec mot "de base" pour k=3 engendré par 0->1, 1->2, 2->3, 3->30

3
30
301
3012
30123.                        supprimé: 0
30123.30.                     supprimé: 0 1
30123.30.301.                 supprimé: 0 1 2
30123.30.301.3012..           supprimé: 0 1 2 30
30123.30.301.3012..30123....  supprimé: 0 1 2 30 0 301

Proportion de 0 toujours plus faible que pour k=2 ??

Autre vision : par prolongement:

3
30
301
3012
3012 30
301230 301
301230301 3012
3012303013012 301230
3012303013012301230 301230301

Contre:

3
30
301
3012
3012 3   (un 0 de moins)
30123 30  (un 0 de moins, et un 1 final)
3012330 301  ( 0 1 2 )
3012330301 3012 ( 0 1 2 30 )
30123303013012 30123
3012330301301230123 3012330
30123303013012301233012330 3012330301

Des zeros en moins, mais aussi des fins de mots (car on prend un pas en
arriere de plus)



*)




let _ = a2

let _ = a2.(30)

let _ = Array.init 30 @@
          fun i -> float a2.(i) -. float a2.(i+1) *. lims.(2)
(* moins de 1/10 après n=7 *)

let _ = mot2

(* 1; 2; 3; 4; 6; 9; 13; 19; 28; 41; 60; 88; 129; 189; 277; 406; 595; 872 *)

(* avec 0,1,2+ :
2
20
201
201 2
2012 20
201220 201
201220201 2012
2012202012012 201220
 *)

(* avec 0,1,2,3+ :

30123030130123012303012303013012303013012301230301
..... .  .   .     .        .            .


3012303013012301230301230301


*)
