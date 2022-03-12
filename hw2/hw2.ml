exception NotImplemented
	    
type 'a tree = Leaf of 'a | Node of 'a tree * 'a * 'a tree
						      
(** Recursive functions **)

let rec lrevrev l =
  let rec lrev l_sub =
    match l_sub with
      [] -> []
    | head_sub :: tail_sub -> lrev tail_sub @ [head_sub]
  in
  match l with
    [] -> []
  | head :: tail -> lrevrev tail @ [lrev head]
;;

let rec lfoldl f e l =
  match l with
    [] -> e
  | head :: tail -> lfoldl f (f (head, e)) tail
;;
			 
(** Tail recursive functions  **)

let fact n =
  let rec fact_aux i acc =
    match i with
      0 -> acc
    | _ -> fact_aux (i - 1) (acc * i)
  in fact_aux n 1
;;

let fib n =
  let rec fib_aux i fib_i_1 fib_i_2 =
    if (i = n) then fib_i_1 + fib_i_2
    else fib_aux (i + 1) (fib_i_1 + fib_i_2) fib_i_1
  in
    if (n = 0 || n = 1) then 1
    else fib_aux 2 1 1
;;

let alterSum l =
  let rec alterSum_aux is_add l_sub accum =
    match l_sub with
      [] -> accum
    | head :: tail -> alterSum_aux (not is_add) tail
                                   (if is_add then accum + head else accum - head)
  in alterSum_aux true l 0
;;

let ltabulate n f =
  let rec ltabulate_aux i accum =
    match i with
      0 -> accum
    | _ -> ltabulate_aux (i - 1) (f (i - 1) :: accum)
  in ltabulate_aux n []
;;

let lfilter p l =
  let rec lfilter_aux l_sub accum =
    match l_sub with
      [] -> accum
    | head :: tail ->
        if (p head) then lfilter_aux tail (accum @ [head])
        else lfilter_aux tail accum
  in lfilter_aux l []
;;

let rec union s t =
  match (s, t) with
    ([], _) -> t
  | (_, []) -> s
  | (head :: tail, _) -> union tail (head :: (lfilter (fun elem -> elem <> head) t))
;;

let inorder t =
  let rec inorder_aux t_sub post =
    match t_sub with
      Leaf n -> n :: post
    | Node (l, n, r) -> inorder_aux l (inorder_aux (Leaf n) (inorder_aux r post))
  in inorder_aux t []
;;
	   
let postorder t =
  let rec postorder_aux t_sub post =
    match t_sub with
      Leaf n -> n :: post
    | Node (l, n, r) -> postorder_aux l (postorder_aux r (postorder_aux (Leaf n) post))
  in postorder_aux t []
;;

let preorder t =
  let rec preorder_aux t_sub post =
    match t_sub with
      Leaf n -> n :: post
    | Node (l, n, r) -> preorder_aux (Leaf n) (preorder_aux l (preorder_aux r post))
  in preorder_aux t []
;;
		       
(** Sorting in the ascending order **)

let rec quicksort l =
  match l with
    [] -> []
  | head :: tail -> quicksort (lfilter (fun elem -> elem < head) tail)
                              @ [head]
                              @ quicksort (lfilter (fun elem -> elem > head) tail)
;;

let rec mergesort l =
  let merge_sorted left_sorted right_sorted =
    let rec insert_asc elem list =
      match list with
        [] -> [elem]
      | head :: tail -> if (elem < head) then elem :: list
                        else head :: (insert_asc elem tail)
    in lfoldl (fun (elem, accum) -> insert_asc elem accum) left_sorted right_sorted
  in
  let divide list =
    let rec divide_aux is_left l_sub (left, right) =
      match l_sub with
        [] -> (left, right)
      | head :: tail -> divide_aux (not is_left) tail
                                   (if is_left then (head :: left, right)
                                    else (left, head :: right))
    in divide_aux true list ([], [])
  in
  let rec merge (left, right) =
    match (left, right) with
      ([], _) -> right
    | (_, []) -> left
    | _ -> (let left_sorted = merge (divide left) in
            let right_sorted = merge (divide right) in
            merge_sorted left_sorted right_sorted)
  in merge (divide l)
;;
			
(** Structures **)

module type HEAP = 
  sig
    exception InvalidLocation
    type loc
    type 'a heap
    val empty : unit -> 'a heap
    val allocate : 'a heap -> 'a -> 'a heap * loc
    val dereference : 'a heap -> loc -> 'a 
    val update : 'a heap -> loc -> 'a -> 'a heap
  end
    
module type DICT =
  sig
    type key
    type 'a dict
    val empty : unit -> 'a dict
    val lookup : 'a dict -> key -> 'a option
    val delete : 'a dict -> key -> 'a dict
    val insert : 'a dict -> key * 'a -> 'a dict 
  end

module Heap : HEAP =
  struct
    exception InvalidLocation 
		
    type loc = int
    type 'a heap = (loc * 'a) list

    let empty _ = []
    let allocate h v =
      match h with
        [] -> ([(0, v)], 0)
      | (loc, value) :: tail -> ((loc + 1, v) :: h, loc + 1)
    let dereference h l =
      let rec dereference_aux h_sub =
        match h_sub with
          [] -> raise InvalidLocation
        | (loc, value) :: tail -> if (loc == l) then value else dereference_aux tail
      in dereference_aux h
    let update h l v =
      let rec update_aux h_sub =
        match h_sub with
          [] -> raise InvalidLocation
        | (loc, value) :: tail -> if (loc == l) then (loc, v) :: tail else (loc, value) :: (update_aux tail)
      in update_aux h
  end
    
module DictList : DICT with type key = string =
  struct
    type key = string
    type 'a dict = (key * 'a) list
			      
    let empty _ = []
    let lookup d k =
      match (List.filter (fun (key, value) -> key = k) d) with
        [] -> None
      | (_, value) :: _ -> Some value
    ;;
    let delete d k = List.filter (fun (key, value) -> key <> k) d
    let insert d (k, v) = (k, v) :: (delete d k)
  end
    
module DictFun : DICT with type key = string =
  struct
    type key = string
    type 'a dict = key -> 'a option
			     
    let empty _ = fun _ -> None
    let lookup d k = d k
    let delete d k = fun key -> if key = k then None
                                else d key
    let insert d (k, v) = fun key -> if key = k then Some v
                                     else d key
  end
