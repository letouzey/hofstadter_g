
#use "defs.ml";;

let a = tabulate_f 10 1_000_000
let a0 = a.(0)
let a1 = a.(1)
let a2 = a.(2)
let a3 = a.(3)
let a4 = a.(4)
let a5 = a.(5)

(* Shift : quasi inverse of f *)

let shift k n = n + iter (f k) k n

let sh1 = Array.init 100 (shift 1)

let phi = (1.+.sqrt(5.))/.2. (* root of X^2-X-1 *)
let _ = Array.init 100 (fun i -> float i *. phi -. float sh1.(i))

let sh2 = Array.init 50 (shift 2)

let tabulate_shift a =
  let k = Array.length a -1 in
  let n = Array.length a.(0) -1 in
  let b = Array.make_matrix (k+1) (n+1) 0 in
  for i = 0 to k do
    for j = 1 to n do
      let x = ref j in
      for p = 1 to i do
        x := a.(i).(!x)
      done;
      b.(i).(j) <- j + !x
    done
  done;
  b

let b = tabulate_shift a
let b0 = b.(0)
let b1 = b.(1)
let b2 = b.(2)
let b3 = b.(3)
let _ = for i = 0 to 99 do assert (sh1.(i) = b1.(i)) done
let _ = for i = 0 to 49 do assert (sh2.(i) = b2.(i)) done


(* Quasi-additivité de shift 2 :
   shift2 (n+m)-shift2(n)-shift2(m) semble toujours entre -2 et 2
*)

let _ =
  let m = ref 0 in
  for i = 0 to 10000 do
    for j = 0 to 90000 do
      let d = b2.(i+j)-b2.(i)-b2.(j) in
      m := max !m (abs d)
    done
  done;
  !m

(* des intervalles (-2,1) par exemple pour i=14
               ou  (-1,2) par exemple pour i=31 *)

let _ = Array.init 100 @@
        fun i ->
        (i,extrems (Array.init 900000 @@ fun n -> b2.(n+i)-b2.(n)-b2.(i)))

(*
Lien shift / f pour la quasi-additivité ?

Supposons forall n m, H(n+m) = H(n)+H(m) + {-2..2}


shift(n+m)   shift(n)+shift(m)

surjectivité:
n peut s'ecrire H(n') (et en fait n' = shift n)
m ............. H(m') (et en fait m' = shift m)

shift(n+m) = shift (H(n')+H(m'))
           = shift (H(n'+m')+{-2..2})
           = shift (H(n'+m')) + {-4..4} ?
           = n'+m' + {0,1} + {-4..4}
           = shift(n)+shift(m) + {-4..5}

Reciproquement
Supposons forall n m, shift(n+m) = shift(n)+shift(m) + {-2..2}

H(a+b)

a = shift(a') ou 1+shift(a')   (avec a' = H a)
b = shift(b') ou 1+shift(b')   (avec b' = H b)

donc
H(a+b) = H(shift(a')+shift(b')+{0..2})
       = H(shift(a')+shift(b')) + {0..2}
       = H(shift(a'+b') + {-2..2}) + {0,2}
       = H(shift(a'+b')) + {-2..2} + {0..2}
       = a'+b' +{-1,0} + {-2..2} + {0..2}
       = H(a)+H(b) + {-3..4}

Donc en tout cas une quasi-additivité donne l'autre (et vice-versa)
mais avec des constantes qui seront dures à optimiser
*)


let gfib1 = memo_A 1 10
let gfib2 = memo_A 2 30

(* conjecture :
   when i is a gfib2 number,
   forall n, shift2(n+i)-shift2(n)-shift2(i) \in {-1,0,1} *)
