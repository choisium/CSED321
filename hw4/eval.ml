(*
 * Call-by-value reduction   
 *)

exception NotImplemented 
exception Stuck

module SS = Set.Make(String)

let freshVarCounter = ref 0
                          
(*   getFreshVariable : string -> string 
 *   use this function if you need to generate a fresh variable from s. 
 *)
let getFreshVariable s = 
  let _ = freshVarCounter := !freshVarCounter + 1
  in
  s ^ "__" ^ (string_of_int (!freshVarCounter))

(*
 *   implemenet FV(e)
 *)
let rec freeVariables e =
  match e with
    Uml.Var x -> SS.singleton(x)
  | Uml.Lam (x, e1) -> SS.remove x (freeVariables e1)
  | Uml.App (e1, e2) -> SS.union (freeVariables e1) (freeVariables e2)

(*
 *   check if variable x(string) is included in free variables of expression e
 *)
let fvInclude x e = SS.exists (fun y -> x = y) (freeVariables e)

(*
 *   implement [x <-> y]
 *)
let rec swap x y e =
  match e with
    Uml.Var z -> (
      Uml.Var (
        if (z = x) then y
        else if (z = y) then x
        else z
      )
    )
  | Uml.Lam (z, e_) -> (
      Uml.Lam (
        (if (z = x) then y
        else if (z = y) then x
        else z),
        swap x y e_
      )
    )
  | Uml.App (e1, e2) -> Uml.App (swap x y e1, swap x y e2)

(*
 *   get a fresh variable based on variable base
 *   which is not a free variable of e1 and e2
 *)
let rec getFreshVariableWithCheck base e1 e2 =
  let z = getFreshVariable base
  in
    if (fvInclude z e1) || (fvInclude z e1)
    then (getFreshVariableWithCheck base e1 e2)
    else z

(*
 * implement [e1/x] e2
 *)
let rec substitute e1 x e2 =
  match e2 with
    Uml.Var y -> if (y = x) then e1 else Uml.Var y
  | Uml.Lam (y, e3) -> (
      if (y = x) then e2
      else if (fvInclude y e1 = false) then Uml.Lam (y, substitute e1 x e3)
      else (
        let z = getFreshVariableWithCheck y e1 e2
        in Uml.Lam (z, substitute e1 x (swap y z e3))
      )
    )
  | Uml.App (e3, e4) -> Uml.App ((substitute e1 x e3), (substitute e1 x e4))

(*
 * implement a single step with reduction using the call-by-value strategy.
 *)
let rec stepv e =
  match e with
    Uml.Var x -> raise Stuck
  | Uml.Lam (x, e1) -> raise Stuck
  | Uml.App (e1, e2) ->
      match e1 with
        Uml.Lam (x, e3) -> (
          match e2 with
            Uml.Lam _ -> substitute e2 x e3   (* App *)
          | _ -> Uml.App (e1, stepv e2)       (* Arg *)
        )
      | _ -> Uml.App (stepv e1, e2)           (* Lam *)

let stepOpt stepf e = try Some (stepf e) with Stuck -> None

let rec multiStep stepf e = try multiStep stepf (stepf e) with Stuck -> e

let stepStream stepf e =
  let rec steps e = 
    match (stepOpt stepf e) with 
      None -> Stream.from (fun _ -> None)
    | Some e' -> Stream.icons e' (steps e')
  in 
  Stream.icons e (steps e)

