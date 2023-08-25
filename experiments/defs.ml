
(** * The recursive functions *)

(** http://oeis.org/A005206 *)
let rec g n = if n = 0 then 0 else n - g (g (n-1))

(** http://oeis.org/A005374 *)
let rec h n = if n = 0 then 0 else n - h (h (h (n-1)))

(** limit case, just one recursive call. This is integer division by 2 *)
let rec d n = if n = 0 then 0 else n - d(n-1)

(** Generalization : k+1 nested recursive calls *)
let rec iter f n = if n=0 then fun x -> x else fun x -> iter f (n-1) (f x)

let rec f k n = if n = 0 then 0 else n - iter (f k) (k+1) (n-1)

let f0 = f 0 (* d *)
let f1 = f 1 (* g *)
let f2 = f 2 (* h *)
let f3 = f 3 (* http://oeis.org/A005375 *)

(** memo_f : for a fixed k, fast computation of [ [|f k 0; .. ;f k n|] ]
    via memoization *)

let memo_f k n =
  let t = Array.make (n+1) 0 in
  for j = 1 to n do
    let x = ref (j-1) in
    for p = 0 to k do x := t.(!x) done;
    t.(j) <- j - !x
  done;
  t

(** tabulate_f : pre-compute f values in a matrix up to k and n (included)
    - first line (k=0) is function d (division by two)
    - second line (k=1) is function g
    - third line (k=2) is function h
    - etc
*)

let tabulate_f k n = Array.init (k+1) (fun i -> memo_f i n)

(** Check that all columns are increasing : f k n <= f (k+1) n *)

let check_col_incr k n =
  let ff = tabulate_f k n in
  for i = 0 to k-1 do
    for j = 0 to n do
      if ff.(i).(j) > ff.(i+1).(j) then Printf.printf "(%d,%d)\n" i j
    done
  done

(** * A : generalized Fibonacci sequences *)

(** For k>=0, A k 0 = 1 and A k (n+1) = A k n + A k (max 0 (n-k)).
    Said otherwise, k is the distance between previous terms to add.
    Hence k=1 is usual Fibonacci sequence (shifted).
    Nota: k=0 double the last term, leading to powers of two.
*)

let rec slow_A k n =
  if n = 0 then 1
  else slow_A k (n-1) + slow_A k (max 0 (n-1-k))

(** fast A computation via memoizing array.
    (-1) is used in case of overflow (occurs at 62 for k=0,
    89 for k=1, 112 for k=2, etc) *)

let memo_A k n =
  let a = Array.make (n+1) 0 in
  for j = 0 to n do
    a.(j) <- if j <= k+1 then j+1 else a.(j-1) + a.(j-1-k);
    (* overflow detection *)
    (if a.(j) < 0 || (j>0 && a.(j-1) < 0) then a.(j) <- -1)
  done;
  a

let tabulate_A k n = Array.init (k+1) (fun i -> memo_A i n)

(** Given k and n, find the largest index p such that A k p <= n
    Note: we proceed here by looking into an array of A numbers
    (a different method is used in GenFib) *)

let invA_tab a n =
  let rec loop i =
    if i >= Array.length a then failwith "invA : overflow"
    else if n < a.(i) then i-1
    else loop (i+1)
  in loop 0

(** Given k and n, find the first index p such that n <= A k p
    Note: we proceed here by looking into an array of A numbers
    (a different method is used in GenFib) *)

let invA_up_tab a n =
  let rec loop i =
    if i >= Array.length a then failwith "invA_up : overflow"
    else if n <= a.(i) then i
    else loop (i+1)
  in loop 0

(** * Utils *)

let float = float_of_int
let int = int_of_float

let round f = float (int (f *. 1e8)) /. 1e8

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

let array_diffs op tab =
  Array.init (Array.length tab -1) (fun i -> op tab.(i+1) tab.(i))

let output_gnuplot_file file tab =
  let c = open_out file in
  Array.iter (fun (a,b) -> Printf.fprintf c "%f %f\n" a b) tab;
  close_out c

let output_gnuplot_file3 file tab =
  let c = open_out file in
  Array.iter (fun (x,y,z) -> Printf.fprintf c "%f %f %f\n" x y z) tab;
  close_out c

(* Almost List.for_all2, but ok when different sizes (discard the leftover) *)
let rec all2 f u v =
  match u,v with
  | x::u, y::v -> f x y && all2 f u v
  | _ -> true
