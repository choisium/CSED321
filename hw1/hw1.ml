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


(* let rec max list =
  match list with
    [] -> 0
  | first :: rest ->
      if first > max rest then first
      else max rest
;; *)

(* Revised version of max. accept negative lists, e.g. [-10; -100; -20] *)
let rec max list =
  match list with
    [] -> 0
  | first :: rest ->
      let max_rest = max rest in
      if first > max_rest then first
      else if max_rest == 0 then first
      else max_rest
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


let rec ltake l n =
  if n <= 0 then []
  else
    match l with
      [] -> []
    | first :: rest -> first :: (ltake rest (n-1))
;;

let rec lall f l =
  match l with
    [] -> true
  | first :: rest -> f first && lall f rest
;;
(* let rec lall f l = List.fold_left(fun accum elem -> f elem && accum) true l *)

let rec lmap f l =
  match l with
    [] -> []
  | first :: rest -> f first :: lmap f rest
;;
(* let rec lmap f l = List.fold_right(fun elem accum -> f elem :: accum) l [] *)

let rec lrev l =
  match l with
    [] -> []
  | first :: rest -> lrev rest @ [first]
;;
(* let rec lrev l = List.fold_left(fun accum elem -> elem :: accum) [] l *)

let rec lflat l =
  match l with
    [] -> []
  | first :: rest -> first @ lflat rest
;;
(* let rec lflat l = List.fold_right(fun elem accum -> elem @ accum) l [] *)

let rec lzip l1 l2 =
  match (l1, l2) with
    ([], _) -> []
  | (_, []) -> []
  | (first1 :: rest1, first2 :: rest2) -> (first1, first2) :: lzip rest1 rest2
;;

let rec split l =
  match l with
    [] -> ([], [])
  | [x] -> ([x], [])
  | first :: second :: rest ->
      match split rest with (l1, l2) -> (first :: l1, second :: l2)
;;

let rec cartprod l1 l2 =
  match l1 with
    [] -> []
  | first :: rest -> lmap (fun x -> (first, x)) l2 @ cartprod rest l2
;;

