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


let rec sum_tree tree =
  match tree with
    Leaf n -> n
  | Node (left, n, right) -> sum_tree left + n + sum_tree right
;;

let rec depth tree =
  match tree with
    Leaf _ -> 0
  | Node (left, _, right) ->
      if depth left > depth right then depth left + 1
      else depth right + 1
;;

let rec bin_search tree x =
  match tree with
    Leaf n -> n == x
  | Node (left, n, right) ->
      n == x || bin_search left x || bin_search right x
;;

let rec inorder tree =
  match tree with
    Leaf n -> [n]
  | Node (left, n, right) -> inorder left @ [n] @ inorder right
;;


let rec max list =
  match list with
    [] -> 0
  | first :: rest ->
      if first > max rest then first
      else max rest
;;

let rec list_add list1 list2 =
  match (list1, list2) with
    ([], _) -> list2
  | (_, []) -> list1
  | (first1 :: rest1, first2 :: rest2) ->
      first1 + first2 :: list_add rest1 rest2
;;

let rec insert m list =
  match list with
    [] -> [m]
  | first :: rest ->
      if m < first then m :: list
      else first :: insert m rest
;;

let rec insort l =
  match l with
    [] -> []
  | first :: rest -> insert first (insort rest)
;;


let rec compose f g = fun x -> g (f x)
let rec merge f g = fun (x, y) -> (f x, g y)
let rec curry f x y = f (x, y)
let rec uncurry f (x, y) = f x y
let rec multifun f n =
  fun x -> if n == 1 then f x
           else (multifun f (n-1)) (f x)
;;

let rec ltake _ _ = raise Not_implemented
let rec lall _ _ = raise Not_implemented
let rec lmap _ _ = raise Not_implemented
let rec lrev _ = raise Not_implemented
let rec lflat _ = raise Not_implemented
let rec lzip _ _ = raise Not_implemented
let rec split _ = raise Not_implemented
let rec cartprod _ _ = raise Not_implemented

