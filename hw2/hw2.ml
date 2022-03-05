exception NotImplemented
	    
type 'a tree = Leaf of 'a | Node of 'a tree * 'a * 'a tree
						      
(** Recursive functions **)

let rec lrevrev l =
  match l with
    [] -> []
  | head :: tail -> lrevrev tail @ [head]
;;
(* let rec lrevrev l = List.fold_left (fun accum elem -> elem :: accum) [] l *)

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

let rec quicksort _ = raise NotImplemented

let rec mergesort _ = raise NotImplemented
			
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
		
    type loc = unit       (* dummy type, to be chosen by students *) 
    type 'a heap = unit   (* dummy type, to be chosen by students *)

    let empty _ = raise NotImplemented
    let allocate _ _ = raise NotImplemented
    let dereference _ _ = raise NotImplemented
    let update _ _ _ = raise NotImplemented
  end
    
module DictList : DICT with type key = string =
  struct
    type key = string
    type 'a dict = (key * 'a) list
			      
    let empty _ = raise NotImplemented
    let lookup _ _ = raise NotImplemented
    let delete _ _ = raise NotImplemented 
    let insert _ _ = raise NotImplemented
  end
    
module DictFun : DICT with type key = string =
  struct
    type key = string
    type 'a dict = key -> 'a option
			     
    let empty _ = raise NotImplemented
    let lookup _ _ = raise NotImplemented
    let delete _ _ = raise NotImplemented
    let insert _ _ = raise NotImplemented
  end
