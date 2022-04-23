open Tml
exception NotImplemented 
exception Stuck
exception NotConvertible

type stoval = 
    Computed of value 
  | Delayed of exp * env

 and stack =
   Hole_SK
   | Frame_SK of stack * frame

 and state =
   Anal_ST of (stoval Heap.heap) * stack * exp * env
   | Return_ST of (stoval Heap.heap) * stack * value 

 (* Define your own datatypes *)
 and env = NOT_IMPLEMENT_ENV
 and value = NOT_IMPLEMENT_VALUE
 and frame = NOT_IMPLEMENT_FRAME

(* Define your own empty environment *)
let emptyEnv = NOT_IMPLEMENT_ENV

(* Implement the function value2exp : value -> Tml.exp
 * Warning : If you give wrong implementation of this function,
 *           you wiil receive no credit for the entire third part!  *)
let value2exp _ = raise NotImplemented

(* Problem 1. 
 * texp2exp : Tml.texp -> Tml.exp *)
module NamingContext = Map.Make(struct type t = var let compare = compare end)
type namingctx = index NamingContext.t

let texp2exp te =
  let rec texp2exp' te' ctx base =
    match te' with
      Tvar x -> Ind (base - (NamingContext.find x ctx) - 1)
    | Tlam (x, t, e) ->
        let ctx' = NamingContext.add x base ctx
        in Lam (texp2exp' e ctx' (base + 1))
    | Tapp (e1, e2) -> App (texp2exp' e1 ctx base, texp2exp' e2 ctx base)
    | Tpair (e1, e2) -> Pair (texp2exp' e1 ctx base, texp2exp' e2 ctx base)
    | Tfst e -> Fst (texp2exp' e ctx base)
    | Tsnd e -> Snd (texp2exp' e ctx base)
    | Teunit -> Eunit
    | Tinl (e, t) -> Inl (texp2exp' e ctx base)
    | Tinr (e, t) -> Inr (texp2exp' e ctx base)
    | Tcase (e, x1, e1, x2, e2) ->
        let ctx1 = NamingContext.add x1 base ctx
        in let ctx2 = NamingContext.add x2 base ctx
        in Case (texp2exp' e ctx base, texp2exp' e1 ctx1 (base + 1), texp2exp' e2 ctx2 (base + 1))
    | Tfix (x, t, e) ->
        let ctx' = NamingContext.add x base ctx
        in Fix (texp2exp' e ctx' (base + 1))
    | Ttrue -> True
    | Tfalse -> False
    | Tifthenelse (e, e1, e2) -> Ifthenelse (texp2exp' e ctx base, texp2exp' e1 ctx base, texp2exp' e2 ctx base)
    | Tnum n -> Num n
    | Tplus -> Plus
    | Tminus -> Minus
    | Teq -> Eq
  in texp2exp' te NamingContext.empty 0

(* Problem 2. 
 * step1 : Tml.exp -> Tml.exp *)

let rec shift n i e =
  match e with
  | Ind m ->
      if (m >= i) then Ind (m + n)
      else Ind (m)
  | Lam e' -> Lam (shift n (i+1) e')
  | App (e1, e2) -> App (shift n i e1, shift n i e2)
  | Pair (e1, e2) -> Pair (shift n i e1, shift n i e2)
  | Fst e' -> Fst (shift n i e')
  | Snd e' -> Snd (shift n i e')
  | Inl e' -> Inl (shift n i e')
  | Inr e' -> Inr (shift n i e')
  | Case (e', e1, e2) -> Case (shift n i e', shift n (i+1) e1, shift n (i+1) e2)
  | Fix e' -> Fix (shift n (i+1) e')
  | Ifthenelse (e', e1, e2) -> Ifthenelse (shift n i e', shift n i e1, shift n i e2)
  | e' -> e'

let rec substitute n em en =
  match em with
    Ind m ->
      if (m < n) then Ind m
      else if (m > n) then Ind (m - 1)
      else shift n 0 en
  | App (e1, e2) -> App (substitute n e1 en, substitute n e2 en)
  | Lam e' -> Lam (substitute (n+1) e' en)
  | Pair (e1, e2) -> Pair (substitute n e1 en, substitute n e2 en)
  | Fst e' -> Fst (substitute n e' en)
  | Snd e' -> Snd (substitute n e' en)
  | Inl e' -> Inl (substitute n e' en)
  | Inr e' -> Inr (substitute n e' en)
  | Case (e', e1, e2) -> Case (substitute n e' en, substitute (n+1) e1 en, substitute (n+1) e2 en)
  | Fix e' -> Fix (substitute (n+1) e' en)
  | Ifthenelse (e', e1, e2) -> Ifthenelse (substitute n e' en, substitute n e1 en, substitute n e2 en)
  | e' -> e'

let rec is_value e =
  match e with
    Lam _ -> true
  | Pair (e1, e2) -> (is_value e1) && (is_value e2)
  | True -> true
  | False -> true
  | Eunit -> true
  | Inl (e') -> is_value e'
  | Inr (e') -> is_value e'
  | Num n -> true
  | _ -> false

let rec step1 e =
  match e with
    App (Lam e1, e2) ->
      if is_value e2 then substitute 0 e1 e2
      else App (Lam e1, step1 e2)
  | App (Plus, Pair (Num n1, Num n2)) -> Num (n1 + n2)
  | App (Plus, e2) -> App (Plus, step1 e2)
  | App (Minus, Pair (Num n1, Num n2)) -> Num (if n1 > n2 then n1 - n2 else 0)
  | App (Minus, e2) -> App (Minus, step1 e2)
  | App (Eq, Pair (Num n1, Num n2)) -> if n1 = n2 then True else False
  | App (Eq, e2) -> App (Eq, step1 e2)
  | App (e1, e2) -> App (step1 e1, e2)
  | Pair (e1, e2) ->
      if is_value e1 then Pair (e1, step1 e2)
      else Pair (step1 e1, e2)
  | Fst e' ->
      if (is_value e') then
        match e' with
          Pair (v1, v2) -> v1
        | _ -> raise Stuck
      else Fst (step1 e')
  | Snd e' ->
      if (is_value e') then
        match e' with
          Pair (v1, v2) -> v2
        | _ -> raise Stuck
      else Snd (step1 e')
  | Inl e' -> Inl (step1 e')
  | Inr e' -> Inr (step1 e')
  | Ifthenelse (True, e1, e2) -> e1
  | Ifthenelse (False, e1, e2) -> e2
  | Ifthenelse (e', e1, e2) -> Ifthenelse (step1 e', e1, e2)
  | Case (e', e1, e2) ->
      if (is_value e') then
        match e' with
          Inl v -> substitute 0 e1 v
        | Inr v -> substitute 0 e2 v
        | _ -> raise Stuck
      else Case (step1 e', e1, e2)
  | Fix e' -> substitute 0 e' (Fix e')
  | _ -> raise Stuck

(* Problem 3. 
 * step2 : state -> state *)
let step2 _ = raise NotImplemented
                    
(* exp2string : Tml.exp -> string *)
let rec exp2string exp = 
  match exp with 
    Ind x -> string_of_int x
  | Lam e -> "(lam. " ^ (exp2string e) ^ ")"
  | App (e1, e2) -> "(" ^ (exp2string e1) ^ " " ^ (exp2string e2) ^ ")"
  | Pair (e1, e2) -> "(" ^ (exp2string e1) ^ "," ^ (exp2string e2) ^ ")"
  | Fst e -> "(fst " ^ (exp2string e) ^ ")"
  | Snd e -> "(snd " ^ (exp2string e) ^ ")"
  | Eunit -> "()"
  | Inl e -> "(inl " ^ (exp2string e) ^ ")"
  | Inr e -> "(inr " ^ (exp2string e) ^ ")"
  | Case (e, e1, e2) -> "(case " ^ (exp2string e) ^" of " ^ (exp2string e1) ^
                          " | " ^ (exp2string e2) ^ ")"
  | Fix e -> "fix. "  ^ (exp2string e) ^ ")"
  | Ifthenelse (e, e1, e2) -> 
     "(if " ^ (exp2string e) ^ " then " ^ (exp2string e1) ^ 
       " else " ^ (exp2string e2) ^ ")"
  | True -> "true"  | False -> "false"
  | Num n -> "<" ^ (string_of_int n) ^ ">"
  | Plus -> "+"  | Minus -> "-" | Eq -> "="

(* state2string : state -> string 
 * you may modify this function for debugging your code *)
let state2string st = match st with
    Anal_ST(_,_,exp,_) -> "Analysis : ???"
  | Return_ST(_,_,_) -> "Return : ??? "

(* ------------------------------------------------------------- *)     
let stepOpt1 e = try Some (step1 e) with Stuck -> None
let stepOpt2 st = try Some (step2 st) with Stuck -> None

let rec multiStep1 e = try multiStep1 (step1 e) with Stuck -> e
let rec multiStep2 st = try multiStep2 (step2 st) with Stuck -> st

let stepStream1 e =
  let rec steps e = 
    match (stepOpt1 e) with
      None -> Stream.from (fun _ -> None)
    | Some e' -> Stream.icons e' (steps e')
  in 
  Stream.icons e (steps e)

let stepStream2 st =
  let rec steps st = 
    match (stepOpt2 st) with
      None -> Stream.from (fun _ -> None)
    | Some st' -> Stream.icons st' (steps st')
  in 
  Stream.icons st (steps st)
