open Tml
exception NotImplemented 
exception Stuck
exception NotConvertible

module Environment = Map.Make(struct type t = index let compare = compare end)

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
 (* environment. it is a mapping from de brujin index to (location of heap, number of lambda binders) *)
 and env = Heap.loc Environment.t
 (* closed value *)
 and value =
    Closure_V of env * exp  (* [env, Lam e], [env, Fix e], [env, Pair (e1, e2)] *)
  | Eunit_V
  | Inl_V of exp   (* does inl, inr need environment? *)
  | Inr_V of exp
  | True_V
  | False_V
  | Num_V of int
  | Plus_V
  | Minus_V
  | Eq_V
 (* frame *)
 and frame =
    App_FR of env * exp   (* []_env exp *)
  | Fst_FR        (* fst []_env *)
  | Snd_FR        (* snd []_env *)
  | Case_FR of env * exp * exp          (* Case []_env of inl e1 | inr e2 *)
  | Ifthenelse_FR of env * exp * exp    (* if []_env then e1 else e2 *)
  | Plus_FR    (* Plus [] *)
  | Plus1_FR of env * exp           (* Plus ([], e) *)
  | Plus2_FR of int           (* Plus (n, []) *)
  | Minus_FR        (* Plus (n, []) *)
  | Minus1_FR of env * exp
  | Minus2_FR of int
  | Eq_FR
  | Eq1_FR of env * exp
  | Eq2_FR of int
  | Location_FR of int    (* [l_i] *)


(* Define your own empty environment *)
let emptyEnv = Environment.empty

(* Implement the function value2exp : value -> Tml.exp
 * Warning : If you give wrong implementation of this function,
 *           you wiil receive no credit for the entire third part!  *)
let value2exp v =
  match v with
    Eunit_V -> Eunit
  | True_V -> True
  | False_V -> False
  | Num_V n -> Num n
  | _ -> raise NotConvertible


(* Problem 1. 
 * texp2exp : Tml.texp -> Tml.exp *)

(*
 * module NamingContext: a map with key type of var
 * type namingctx: a map with key type of var and value type of index
 * This namingctx is an implementation of naming context
 *)
module NamingContext = Map.Make(struct type t = var let compare = compare end)
type namingctx = index NamingContext.t

(*
 * var find_free_ctx: Tml.texp -> Tml.var list -> int NamingContext.t -> int -> int NamingContext.t * int
 *
 * te is a TML expression we want to find ctx of free variables
 * bound_vars is list of bound variables
 * free_ctx is a map from free variable to assigned index
 * last is the last index we assigned to free variable
 * this returns (new free_ctx, new last) after processing te
 *
 * usage example - to get free_ctx of a TML expression te
 * let (free_ctx, _) = find_free_ctx te [] NamingContext.empty 0
 *)
let rec find_free_ctx te bound_vars free_ctx last =
  match te with
    Tvar x ->
      if (List.exists (fun elem -> x = elem) bound_vars) then (free_ctx, last)
      else if (NamingContext.exists (fun key elem -> x = key) free_ctx) then (free_ctx, last)
      else
        let free_ctx' = NamingContext.add x last free_ctx
        in (free_ctx', last + 1)
  | Tlam (x, t, e) -> find_free_ctx e (x :: bound_vars) free_ctx last
  | Tapp (e1, e2) ->
      let (free_ctx1, last1) = find_free_ctx e2 bound_vars free_ctx last
      in find_free_ctx e1 bound_vars free_ctx1 last1
  | Tpair (e1, e2) ->
      let (free_ctx1, last1) = find_free_ctx e2 bound_vars free_ctx last
      in find_free_ctx e1 bound_vars free_ctx1 last1
  | Tfst e -> find_free_ctx e bound_vars free_ctx last
  | Tsnd e -> find_free_ctx e bound_vars free_ctx last
  | Tinl (e, _) -> find_free_ctx e bound_vars free_ctx last
  | Tinr (e, _) -> find_free_ctx e bound_vars free_ctx last
  | Tcase (e, x1, e1, x2, e2) ->
      let (free_ctx1, last1) = find_free_ctx e2 (x2 :: bound_vars) free_ctx last
      in let (free_ctx2, last2) = find_free_ctx e1 (x1 :: bound_vars) free_ctx1 last1
      in find_free_ctx e bound_vars free_ctx2 last2
  | Tfix (x, t, e) -> find_free_ctx e (x :: bound_vars) free_ctx last
  | Tifthenelse (e, e1, e2) ->
      let (free_ctx1, last1) = find_free_ctx e2 bound_vars free_ctx last
      in let (free_ctx2, last2) = find_free_ctx e1 bound_vars free_ctx1 last1
      in find_free_ctx e bound_vars free_ctx2 last2
  | _ -> (free_ctx, last)

(* val texp2exp : Tml.texp -> Tml.exp *)
let texp2exp te =
  let (free_ctx, _) = find_free_ctx te [] NamingContext.empty 0
  in let rec texp2exp' te' bound_ctx level =
    match te' with
      Tvar x -> (
        match (NamingContext.find_opt x bound_ctx) with
          Some n -> Ind (level - n - 1)
        | None -> Ind (NamingContext.find x free_ctx + level)
      )
    | Tlam (x, t, e) ->
        let bound_ctx' = NamingContext.add x level bound_ctx
        in Lam (texp2exp' e bound_ctx' (level + 1))
    | Tapp (e1, e2) -> App (texp2exp' e1 bound_ctx level, texp2exp' e2 bound_ctx level)
    | Tpair (e1, e2) -> Pair (texp2exp' e1 bound_ctx level, texp2exp' e2 bound_ctx level)
    | Tfst e -> Fst (texp2exp' e bound_ctx level)
    | Tsnd e -> Snd (texp2exp' e bound_ctx level)
    | Teunit -> Eunit
    | Tinl (e, t) -> Inl (texp2exp' e bound_ctx level)
    | Tinr (e, t) -> Inr (texp2exp' e bound_ctx level)
    | Tcase (e, x1, e1, x2, e2) ->
        let bound_ctx1 = NamingContext.add x1 level bound_ctx
        in let bound_ctx2 = NamingContext.add x2 level bound_ctx
        in Case (texp2exp' e bound_ctx level, texp2exp' e1 bound_ctx1 (level + 1), texp2exp' e2 bound_ctx2 (level + 1))
    | Tfix (x, t, e) ->
        let bound_ctx' = NamingContext.add x level bound_ctx
        in Fix (texp2exp' e bound_ctx' (level + 1))
    | Ttrue -> True
    | Tfalse -> False
    | Tifthenelse (e, e1, e2) -> Ifthenelse (texp2exp' e bound_ctx level, texp2exp' e1 bound_ctx level, texp2exp' e2 bound_ctx level)
    | Tnum n -> Num n
    | Tplus -> Plus
    | Tminus -> Minus
    | Teq -> Eq
  in texp2exp' te NamingContext.empty 0

(* Problem 2. 
 * step1 : Tml.exp -> Tml.exp *)

(*
 * val shift : int -> Tml.index -> Tml.exp -> Tml.exp
 *
 * This is an implementation of shift^n_i (e)
 * Shift all de Brujin indexes in e by n,
 * where a de Brujin index m in N such that m < i does not count as a free variable.
 *)
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

(*
 * val substitute : Tml.index -> Tml.exp -> Tml.exp -> Tml.exp
 *
 * This is an implementation of substitute_n (em, en)
 * Substitute en for the variable bound in em using n as a boundary index
 *)
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

(*
 * val is_value : Tml.exp -> bool
 *
 * Return true only if exp is value
 *)
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

(*
 * val step1 : Tml.exp -> Tml.exp
 *)
let rec step1 e =
  match e with
    App (Lam e1, e2) ->
      if is_value e2 then substitute 0 e1 e2
      else App (Lam e1, step1 e2)
  | App (Plus, Pair (Num n1, Num n2)) -> Num (n1 + n2)
  | App (Plus, e2) -> App (Plus, step1 e2)
  | App (Minus, Pair (Num n1, Num n2)) -> Num (n1 - n2)
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

(*
 * val increase_idx : 'a Environment.t -> 'a Environment.t
 *
 * this increases index by one for all mapping in this environment
 * i.e. mappings of (i, l) -> mappings of (i + 1, l)
 * this is necessary for lambda application and fixed point combinator
 *)
let increase_idx env =
  let env_seq = Environment.to_seq env
  in let env_seq_inc = Seq.map (fun (index, loc) -> (index + 1, loc)) env_seq
  in Environment.of_seq env_seq_inc

(*
 * val step2 : state -> state
 *)
let step2 s =
  match s with
    (* Analyze phase *)
    Anal_ST (heap, stack, Ind n, env) -> (
      match Environment.find_opt n env with
        None -> raise Stuck
      | Some l -> (
          match (Heap.deref heap l) with
            Delayed (exp, env') ->
              Anal_ST (heap, Frame_SK(stack, Location_FR l), exp, env')
          | Computed v ->
              Return_ST (heap, stack, v)
        )
    )
  | Anal_ST (heap, stack, Lam e, env) ->
      Return_ST (heap, stack, Closure_V (env, Lam e))
  | Anal_ST (heap, stack, App (e1, e2), env) ->
      Anal_ST (heap, Frame_SK (stack, App_FR(env, e2)), e1, env)
  | Anal_ST (heap, stack, Pair (e1, e2), env) ->
      Return_ST (heap, stack, Closure_V (env, Pair (e1, e2)))
  | Anal_ST (heap, stack, Fst e, env) ->
      Anal_ST (heap, Frame_SK (stack, Fst_FR), e, env)
  | Anal_ST (heap, stack, Snd e, env) ->
      Anal_ST (heap, Frame_SK (stack, Snd_FR), e, env)
  | Anal_ST (heap, stack, Eunit, env) ->
      Return_ST (heap, stack, Eunit_V)
  | Anal_ST (heap, stack, Inl e, env) ->
      Return_ST (heap, stack, Inl_V e)
  | Anal_ST (heap, stack, Inr e, env) ->
      Return_ST (heap, stack, Inr_V e)
  | Anal_ST (heap, stack, Case (e, e1, e2), env) ->
      Anal_ST (heap, Frame_SK (stack, Case_FR(env, e1, e2)), e, env)
  | Anal_ST (heap, stack, Fix e, env) ->
      Return_ST (heap, stack, Closure_V (env, Fix e))
  | Anal_ST (heap, stack, True, env) ->
      Return_ST (heap, stack, True_V)
  | Anal_ST (heap, stack, False, env) ->
      Return_ST (heap, stack, False_V)
  | Anal_ST (heap, stack, Ifthenelse (e, e1, e2), env) ->
      Anal_ST (heap, Frame_SK (stack, Ifthenelse_FR (env, e1, e2)), e, env)
  | Anal_ST (heap, stack, Num n, env) ->
      Return_ST (heap, stack, Num_V n)
  | Anal_ST (heap, stack, Plus, env) ->
      Return_ST (heap, stack, Plus_V)
  | Anal_ST (heap, stack, Minus, env) ->
      Return_ST (heap, stack, Minus_V)
  | Anal_ST (heap, stack, Eq, env) ->
      Return_ST (heap, stack, Eq_V)

    (* Return phase *)
  | Return_ST (heap, Hole_SK, v) -> raise Stuck
  | Return_ST (heap, Frame_SK(stack, Location_FR l), v) ->
      let heap' = Heap.update heap l (Computed v)
      in Return_ST (heap', stack, v)
    (* Closure - Lambda abstraction *)
  | Return_ST (heap, Frame_SK(stack, App_FR (env_app, exp_app)), Closure_V (env_lam, Lam exp_lam)) ->
      let (heap', l) = Heap.allocate heap (Delayed (exp_app, env_app))
      in let env_lam' = Environment.add 0 l (increase_idx env_lam)
      in Anal_ST (heap', stack, exp_lam, env_lam')
    (* Pair *)
  | Return_ST (heap, Frame_SK(stack, Fst_FR), Closure_V(env, Pair (e1, e2))) ->
      Anal_ST (heap, stack, e1, env)
  | Return_ST (heap, Frame_SK(stack, Snd_FR), Closure_V(env, Pair (e1, e2))) ->
      Anal_ST (heap, stack, e2, env)
  | Return_ST (heap, stack, Eunit_V) -> raise Stuck
    (* Sum type *)
  | Return_ST (heap, Frame_SK(stack, Case_FR (env, e1, e2)), Inl_V e) ->
      let (heap', l) = Heap.allocate heap (Delayed (e, env))
      in let env' = Environment.add 0 l env
      in Anal_ST (heap', stack, e1, env')
  | Return_ST (heap, Frame_SK(stack, Case_FR (env, e1, e2)), Inr_V e) ->
      let (heap', l) = Heap.allocate heap (Delayed (e, env))
      in let env' = Environment.add 0 l env
      in Anal_ST (heap', stack, e2, env')
    (* Closure - Fixed point constructor *)
  | Return_ST (heap, stack, Closure_V (env, Fix e)) ->
      let (heap', l) = Heap.allocate heap (Delayed (Fix e, env))
      in let env' = Environment.add 0 l (increase_idx env)    (* why 1 instead of 1? (fix x -> 0.e) |-> [fix x.e / x] e *)
      in Anal_ST (heap', stack, e, env')
    (* True, False *)
  | Return_ST (heap, Frame_SK(stack, Ifthenelse_FR (env, e1, e2)), True_V) ->
      Anal_ST (heap, stack, e1, env)
  | Return_ST (heap, Frame_SK(stack, Ifthenelse_FR (env, e1, e2)), False_V) ->
      Anal_ST (heap, stack, e2, env)
    (* Plus *)
  | Return_ST (heap, Frame_SK(stack, App_FR (env, e)), Plus_V) ->
      Anal_ST (heap, Frame_SK(stack, Plus_FR), e, env)
  | Return_ST (heap, Frame_SK(stack, Plus_FR), Closure_V(env, Pair (e1, e2))) ->
      Anal_ST (heap, Frame_SK(stack, Plus1_FR (env, e2)), e1, env)
  | Return_ST (heap, Frame_SK(stack, Plus1_FR (env, e)), Num_V n) ->
      Anal_ST (heap, Frame_SK(stack, Plus2_FR n), e, env)
  | Return_ST (heap, Frame_SK(stack, Plus2_FR n1), Num_V n2) ->
      Return_ST (heap, stack, Num_V (n1 + n2))
    (* Minus *)
  | Return_ST (heap, Frame_SK(stack, App_FR (env, e)), Minus_V) ->
      Anal_ST (heap, Frame_SK(stack, Minus_FR), e, env)
  | Return_ST (heap, Frame_SK(stack, Minus_FR), Closure_V(env, Pair (e1, e2))) ->
      Anal_ST (heap, Frame_SK(stack, Minus1_FR (env, e2)), e1, env)
  | Return_ST (heap, Frame_SK(stack, Minus1_FR (env, e)), Num_V n) ->
      Anal_ST (heap, Frame_SK(stack, Minus2_FR n), e, env)
  | Return_ST (heap, Frame_SK(stack, Minus2_FR n1), Num_V n2) ->
      Return_ST (heap, stack, Num_V (n1 - n2))
    (* Equal *)
  | Return_ST (heap, Frame_SK(stack, App_FR (env, e)), Eq_V) ->
      Anal_ST (heap, Frame_SK(stack, Eq_FR), e, env)
  | Return_ST (heap, Frame_SK(stack, Eq_FR), Closure_V(env, Pair (e1, e2))) ->
      Anal_ST (heap, Frame_SK(stack, Eq1_FR (env, e2)), e1, env)
  | Return_ST (heap, Frame_SK(stack, Eq1_FR (env, e)), Num_V n) ->
      Anal_ST (heap, Frame_SK(stack, Eq2_FR n), e, env)
  | Return_ST (heap, Frame_SK(stack, Eq2_FR n1), Num_V n2) ->
      Return_ST (heap, stack, if n1 = n2 then True_V else False_V)
  | _ -> raise Stuck
                    
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

(* val frame2string : frame -> string *)
let rec frame2string f =
  match f with
    App_FR (env, e) -> "[ ]_env " ^ (exp2string e)
  | Fst_FR -> "fst [ ]_env"
  | Snd_FR -> "snd [ ]_env"
  | Case_FR (env, e1, e2) -> "case [ ]_env of inl " ^ (exp2string e1) ^" | inr " ^ (exp2string e2)
  | Ifthenelse_FR (env, e1, e2) -> "if [ ]_env then " ^ (exp2string e1) ^" else " ^ (exp2string e2)
  | Plus_FR -> "+ [ ]"
  | Plus1_FR (env, e) -> "+ ([ ]_env, " ^ (exp2string e) ^ ")"
  | Plus2_FR n -> "+ (" ^ (string_of_int n) ^", [ ])"
  | Minus_FR -> "- [ ]"
  | Minus1_FR (env, e) -> "- ([ ]_env, " ^ (exp2string e) ^ ")"
  | Minus2_FR n -> "- (" ^ (string_of_int n) ^", [ ])"
  | Eq_FR -> "= [ ]"
  | Eq1_FR (env, e) -> "= ([ ]_env, " ^ (exp2string e) ^ ")"
  | Eq2_FR n -> "= (" ^ (string_of_int n) ^", [ ])"
  | Location_FR n -> "[l_" ^ (string_of_int n) ^"]"

(* val val2string : value -> string *)
let rec val2string v =
  match v with
    Closure_V (_, Lam e) -> "[env, (lam. " ^ (exp2string e) ^ ")]"
  | Closure_V (_, Fix e) -> "[env, (fix. " ^ (exp2string e) ^ ")]"
  | Closure_V (_, Pair (e1, e2)) -> "[env, (" ^ (exp2string e1) ^ ", " ^ (exp2string e2) ^ ")]"
  | Closure_V _ -> "Wrong Closure"
  | Eunit_V -> "()"
  | Inl_V e -> "(inl. " ^ (exp2string e) ^ ")"
  | Inr_V e -> "(inr. " ^ (exp2string e) ^ ")"
  | True_V -> "true"
  | False_V -> "false"
  | Num_V n -> "<" ^ (string_of_int n) ^ ">"
  | Plus_V -> "+"
  | Minus_V -> "-"
  | Eq_V -> "="

(* state2string : state -> string 
 * you may modify this function for debugging your code *)
let state2string st = match st with
    Anal_ST(_,Hole_SK,exp,_) -> "Analysis :  [ ] |> " ^ (exp2string exp)
  | Anal_ST(_,Frame_SK(_, f),exp,_) -> "Analysis :  _, " ^ (frame2string f) ^" |> " ^ (exp2string exp)
  | Return_ST(_,Hole_SK,v) -> "Return :  [ ] <| " ^ (val2string v)
  | Return_ST(_,Frame_SK(_, f),v) -> "Return :  _, " ^ (frame2string f) ^" <| " ^ (val2string v)

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
