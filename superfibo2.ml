
module IntMap = Map.Make(struct type t=int let compare = compare end);;
open IntMap;;

let init = add 0 0 (add 1 1 (add 2 1 (add 3 2 empty)));;

let step n map = 
  try 
    let gpredn = find (n-1) map in 
    let target = n - gpredn in 
    fold (fun k e l -> if e = target then (add n k map) :: l else l) map []
  with Not_found -> [];;
	  
let iter n = 
  let l = ref [init] in 
  for i = 4 to n do 
    l := List.fold_left (fun ll map -> (step i map) @ ll) [] !l
  done;
  !l;;

let print map = 
  print_string "{"; 
  IntMap.iter (fun _ e -> print_int e; print_string "|") map; 
  print_string "}";;
  
