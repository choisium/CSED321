open Tml

exception TypeError

(***************************************************** 
 * replace unit by your own type for typing contexts *
 *****************************************************)

(*
 * I choosed Map for type of context
 * This map has "exp" for type of key, and "tp" for type of value.
 *)
module TypeContext = Map.Make(struct type t = exp let compare = compare end)
type context = tp TypeContext.t

(*
 * For each function you introduce, 
 * write its type, specification, and invariant. 
 * -> I did not introduced any new function.
 *)

(* val createEmptyContext: unit -> context *)
let createEmptyContext () = TypeContext.empty

(* val typing : context -> Tml.exp -> Tml.tp *)
let rec typing ctx e = match e with
    Var x -> (
      match (TypeContext.find_opt e ctx) with
        None -> raise TypeError
      | Some t_x -> t_x
    )
  | Lam (x, t, e') -> (
      let ctx_x = TypeContext.add (Var x) t ctx
      in Fun(t, typing ctx_x e')
    )
  | App (e1, e2) -> (
      match (typing ctx e1) with
        Fun (a, b) -> if (typing ctx e2) = a then b else raise TypeError
      | _ -> raise TypeError
    )
  | Pair (e1, e2) -> Prod (typing ctx e1, typing ctx e2)
  | Fst e' -> (
      match (typing ctx e') with
        Prod (a, b) -> a
      | _ -> raise TypeError
    )
  | Snd e' -> (
      match (typing ctx e') with
        Prod (a, b) -> b
      | _ -> raise TypeError
    )
  | Eunit -> Unit
  | Inl (e', t) -> Sum (typing ctx e', t)
  | Inr (e', t) -> Sum (t, typing ctx e')
  | Case (e', x1, e1, x2, e2) -> (
      match (typing ctx e') with
        Sum (a, b) -> (
          let ctx_x1 = TypeContext.add (Var x1) a ctx
          in let c1 = typing ctx_x1 e1 
          in let ctx_x2 = TypeContext.add (Var x2) b ctx
          in let c2 = typing ctx_x2 e2
          in if c1 = c2 then c1 else raise TypeError
        )
      | _ -> raise TypeError
    )
  | Fix (x, t, e') -> (
      let ctx_x = TypeContext.add (Var x) t ctx
      in if (typing ctx_x e') = t then t else raise TypeError
    )
  | True -> Bool
  | False -> Bool
  | Ifthenelse (e', e1, e2) -> (
      if (typing ctx e') = Bool
      then (
        let c1 = typing ctx e1
        in let c2 = typing ctx e2
        in if c1 = c2 then c1 else raise TypeError
      )
      else raise TypeError
    )
  | Num (n) -> Int
  | Plus -> Fun (Prod (Int, Int), Int)
  | Minus -> Fun (Prod (Int, Int), Int)
  | Eq -> Fun (Prod (Int, Int), Bool)

let typeOf e = typing (createEmptyContext ()) e 
let typeOpt e = try Some (typeOf e) 
                with TypeError -> None



