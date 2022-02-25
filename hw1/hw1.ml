exception Not_implemented

type 'a tree = Leaf of 'a | Node of 'a tree * 'a * 'a tree

let rec sum n =
  match n with
    1 -> 1
  | _ -> n + sum (n - 1)
;;

let rec fib n =
  match n with
    0 | 1 -> 1
  | _ -> fib (n - 1) + fib (n - 2)
;;

let rec gcd m n =
  if (m == 0) then n
  else if (n == 0) then m
  else if (m > n) then gcd n (m - (m / n) * n)
  else gcd m (n - (n / m) * m)
;;

let rec combi n k =
  match k with
    0 -> 1
  | _ -> n * combi (n - 1) (k - 1) / k
;;


let rec sum_tree _ = raise Not_implemented
let rec depth _ = raise Not_implemented
let rec bin_search _ _ = raise Not_implemented
let rec inorder _ = raise Not_implemented

let rec max _ = raise Not_implemented
let rec list_add _ _ = raise Not_implemented
let rec insert _ _ = raise Not_implemented
let rec insort _ = raise Not_implemented

let rec compose _ _ = raise Not_implemented
let rec merge _ _ = raise Not_implemented
let rec curry _ _ _ = raise Not_implemented 
let rec uncurry _ _ = raise Not_implemented
let rec multifun _ _ = raise Not_implemented

let rec ltake _ _ = raise Not_implemented
let rec lall _ _ = raise Not_implemented
let rec lmap _ _ = raise Not_implemented
let rec lrev _ = raise Not_implemented
let rec lflat _ = raise Not_implemented
let rec lzip _ _ = raise Not_implemented
let rec split _ = raise Not_implemented
let rec cartprod _ _ = raise Not_implemented

