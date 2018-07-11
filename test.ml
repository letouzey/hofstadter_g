
let rec d n = if n = 0 then 0 else n - d(n-1);;
let rec g n = if n = 0 then 0 else n - g (g (n-1));;

let rec h n = if n = 0 then 0 else n - h (h (h (n-1)));;

let rec iter f n = if n=1 then f else fun x -> iter f (n-1) (f x);;

let rec f k n = if k=0 then n else if n = 0 then 0 else
            n - iter (f k) k (n-1)

let test = Array.to_list (Array.init 21 (fun n -> n));;
let test2 = Array.to_list (Array.init 100 (fun n -> n));;


let _ = List.map (fun n -> (n, d n)) test
let _ = List.map (fun n -> n,f 6 n) test
let _ = List.map (f 2) test
let _ = List.map h test
let _ = List.map (f 3) test

let _ = List.map (fun n -> g n - d n) test2




let limh = 0.6823278038280194
let expo = 1.465571231876768

let hbis n = int_of_float (limh *. (float_of_int (n+1)))

let _ = List.map (fun n -> (n,h n, hbis n)) test

let rec a n = if n<4 then n else a (n-1) + a (n-3)

let _ = List.map (fun n -> float_of_int (a (n+1)) /. float_of_int (a (n+2))) test

let atab = Array.make 100 0

let rec aopt n =
  if n >= 100 then a n
  else
    let x = atab.(n) in
    if x<>0 then x
    else
      if n <4 then (atab.(n) <- n; n)
      else
        let x = aopt (n-1) + aopt (n-3) in
        (atab.(n) <- x; x)

let _ = aopt 70
let _ = atab

let _ = Array.mapi (fun i x -> float_of_int x /.(expo ** float_of_int i)) atab

(** a(n) ~ 0.89618 * expo^n *)


let rec fib n =
  if n = 0 then (0,1) else
    let (a,b) = fib (n-1) in
    (b,a+b)

let _ = fib 70

let phi = (1.+.sqrt(5.))/.2.

let _ = phi ** 70. /. sqrt(5.)



let rec decomp n =
  let rec loop k =
    if aopt k > n then k-1
    else loop (k+1)
  in
  if n = 0 then []
  else
    let x = loop 1 in
    x::(decomp (n-aopt x))

let _ = List.map (fun n -> n, decomp n) test2

let _ = atab.(0) <- 0

let prevdecomp l = List.map (function 1 -> 1 | n -> n-1) l
let sumdecomp l = List.fold_left (fun acc n -> acc + aopt n) 0 l

let _ = List.map (fun n -> h n, sumdecomp (prevdecomp (decomp n))) test


let tabulate k n =
  let a = Array.make_matrix k n 0 in
  for j = 0 to n-1 do a.(0).(j) <- j done;
  for i = 1 to k-1 do
    for j = 1 to n-1 do
      let x = ref (j-1) in
      for p = 1 to i do
        x := a.(i).(!x)
      done;
      a.(i).(j) <- j - !x
    done
  done;
  a

let a = tabulate 1000 1000

let check k n a =
  for i = 1 to k-2 do
    for j = 0 to n-1 do
      if a.(i).(j) > a.(i+1).(j) then Printf.printf "(%d,%d)\n" i j
    done
  done

let _ = check 1000 1000 a

let tab = Array.init 1000 (fun i -> int_of_float ( float_of_int (i+1) /. phi))

let tab' = Array.init 1000 (fun i -> int_of_float ( ceil (float_of_int i /. phi)))

let _ = tab.(100)
let _ = tab'.(100)

let _ = Array.mapi (fun i x -> tab'.(i) - x) tab


let tab3 = Array.init 1000 (fun i -> int_of_float ( float_of_int (i+1) /. expo))
let tab3' = Array.init 1000 (fun i -> int_of_float ( float_of_int i /. expo))
let tab3'' = Array.init 1000 (fun i -> int_of_float (ceil( float_of_int i /. expo)))

let _ = Array.mapi (fun i x -> x - a.(3).(i)) tab3  (* que des 0,1 ou -1 *)
let _ = Array.mapi (fun i x -> a.(3).(i) - x) tab3'  (* que des 0 ou 1 *)
let _ = Array.mapi (fun i x -> x - a.(3).(i)) tab3''  (* que des 0 ou 1 *)

let _ = Array.init 1000 (fun i -> float_of_int (a.(3).(i)) -. float_of_int (i+1) /. expo)


let _ = a.(4);;


let expo4 = 1.380277569097618

let tab4 = Array.init 1000 (fun i -> int_of_float ( float_of_int (i+1) /. expo4))
let tab4' = Array.init 1000 (fun i -> int_of_float ( float_of_int i /. expo4))

let _ = Array.mapi (fun i x -> x - a.(4).(i)) tab4  (* que des 0,1 ou -1 *)
let _ = Array.mapi (fun i x -> a.(4).(i) - x) tab4'  (* que des 0 ou 1 *)


let newton k =
  let e = float_of_int k in
  let rec loop n x =
    let y = x -. (x** e +. x -. 1.)/.(e *.x ** (e-.1.) +.1.) in
    if x = y then (n,x)
    else loop (n+1) y
  in loop 1 1.

let x = newton 30

let _ = limh
let x' = (-.1.+.sqrt(5.))/.2.

let _ = x** 2. +. x -.1.



let rec h' x = if x <= 5 then h x else x+1 - h' (h' (1 + h' (x-1)))

let _ = Array.init 30 (fun i -> i,h' i)

let rec f4' x = if x <= 6 then a.(4).(x) else x+1 - f4' (f4' (f4' (1 + f4' (x-1))))

let _ = Array.init 30 (fun i -> i,f4' i)

(* fk o fk *)

let twice k n a =
  let b = Array.make_matrix k n 0 in
  for i = 0 to k-1 do
    for j = 0 to n-1 do
      b.(i).(j) <- a.(i).(a.(i).(j))
    done;
  done;
  b

let b = twice 1000 1000 a

let _ = b.(2);;
let _ = Array.init 1000 (fun i -> a.(6).(i) - b.(5).(i))
