open Mach
open Mono 

exception NotImplemented

(* location *)
type loc =
    L_INT of int          (* integer constant *)
  | L_BOOL of bool        (* boolean constant *)
  | L_UNIT                (* unit constant *)
  | L_STR of string       (* string constant *)
  | L_ADDR of Mach.addr   (* at the specified address *)
  | L_REG of Mach.reg     (* at the specified register *)
  | L_DREF of loc * int   (* at the specified location with the specified offset *)

type venv = (Mono.avid, loc) Dict.dict  (* variable environment *)
let venv0 : venv = Dict.empty           (* empty variable environment *)

type env = venv * int
let env0 : env = (venv0, 0)

(* val loc2rvalue : loc -> Mach.code * rvalue *)
let rec loc2rvalue l = match l with
    L_INT i -> (Mach.code0, Mach.INT i)
  | L_BOOL b -> (Mach.code0, Mach.BOOL b)
  | L_UNIT -> (Mach.code0, Mach.UNIT)
  | L_STR s -> (Mach.code0, Mach.STR s)
  | L_ADDR a -> (Mach.code0, Mach.ADDR a)
  | L_REG r -> (Mach.code0, Mach.REG r)
  | L_DREF (L_ADDR a, i) -> (Mach.code0, Mach.REFADDR (a, i))
  | L_DREF (L_REG r, i) -> (Mach.code0, Mach.REFREG (r, i))
  | L_DREF (l, i) ->
     let (code, rvalue) = loc2rvalue l in
     (Mach.cpost code [Mach.MOVE (Mach.LREG Mach.tr, rvalue)], Mach.REFREG (Mach.tr, i))

let rec rvalue2loc rv = match rv with
    INT i -> L_INT i
  | BOOL b -> L_BOOL b
  | UNIT -> L_UNIT
  | STR s -> L_STR s
  | ADDR a -> L_ADDR a
  | REG r -> L_REG r
  | REFADDR (a, i) -> L_DREF (L_ADDR a, i)
  | REFREG (r, i) -> L_DREF (L_REG r, i)

(*
 * helper functions for debugging
 *)
(* val loc2str : loc -> string *)
let rec loc2str l = match l with 
    L_INT i -> "INT " ^ (string_of_int i)
  | L_BOOL b -> "BOOL " ^ (string_of_bool b)
  | L_UNIT -> "UNIT"
  | L_STR s -> "STR " ^ s
  | L_ADDR (Mach.CADDR a) -> "ADDR " ^ ("&" ^ a)
  | L_ADDR (Mach.HADDR a) -> "ADDR " ^ ("&Heap_" ^ (string_of_int a))
  | L_ADDR (Mach.SADDR a) -> "ADDR " ^ ("&Stack_" ^ (string_of_int a))
  | L_REG r -> 
     if r = Mach.sp then "REG SP"
     else if r = Mach.bp then "REG BP"
     else if r = Mach.cp then "REG CP"
     else if r = Mach.ax then "REG AX"
     else if r = Mach.bx then "REG BX"
     else if r = Mach.tr then "REG TR"
     else if r = Mach.zr then "REG ZR"
     else "R[" ^ (string_of_int r) ^ "]"
  | L_DREF (l, i) -> "DREF(" ^ (loc2str l) ^ ", " ^ (string_of_int i) ^ ")"

(*
 * Generate code for Abstract Machine MACH 
 *)
(* pat2code : Mach.label -> Mach.label - > loc -> Mono.pat -> Mach.code * venv *)
let rec pat2code saddr faddr l pat = match pat with
    P_INT i ->
      let (code, rvalue) = loc2rvalue l in
      let code' = clist [JMPNEQ (ADDR (CADDR faddr), rvalue, INT i)]
      in
        (cpre [LABEL saddr] (code @@ code'), venv0)
  | P_BOOL false ->
      let (code, rvalue) = loc2rvalue l in
      let code' = clist [JMPTRUE (ADDR (CADDR faddr), rvalue)]
      in
        (cpre [LABEL saddr] (code @@ code'), venv0)
  | P_BOOL true ->
      let (code, rvalue) = loc2rvalue l in
      let truelabel = labelNewLabel saddr "_TRUE" in
      let code' = clist [
        JMPTRUE (ADDR (CADDR truelabel), rvalue);
        JUMP (ADDR (CADDR faddr));
        LABEL truelabel;
      ]
      in
        (cpre [LABEL saddr] (code @@ code'), venv0)

  | _ -> (cpre [LABEL saddr] code0, venv0)

(* patty2code : Mach.label -> Mach.label -> loc -> Mono.patty -> Mach.code * venv *)
and patty2code saddr faddr l patty = match patty with
    PATTY (P_VID (avid, VAR), _) ->
      (cpre [LABEL saddr] code0, Dict.insert (avid, l) venv0)
  | PATTY (pat, _) -> pat2code saddr faddr l pat

(* exp2code : env -> Mach.label -> Mono.exp -> Mach.code * Mach.rvalue *)
and exp2code environ saddr exp = match exp with
    E_INT i -> (cpre [LABEL saddr] code0, INT i)
  | E_BOOL b -> (cpre [LABEL saddr] code0, BOOL b)
  | E_UNIT -> (cpre [LABEL saddr] code0, UNIT)
  | _ -> (cpre [LABEL saddr] code0, INT 0)

(* expty2code : env -> Mach.label -> Mono.expty -> Mach.code * Mach.rvalue *)
and expty2code environ saddr expty = match expty with
    EXPTY (_, T_UNIT) -> (cpre [LABEL saddr] code0, UNIT)   (* Optimization for unit *)
  | EXPTY (E_VID (avid, VAR), _) -> (
      let (venviron, count) = environ in
      match Dict.lookup avid venviron with
        None -> (clist [LABEL saddr; DEBUG (avid ^ " missing")], INT 0)
      | Some l ->
          let (code, rv) = loc2rvalue l in
          (cpre [LABEL saddr] code, rv)
    )
  | EXPTY (E_FUN mlist, _) -> (
      let saddr_fun = labelNewLabel saddr "E_FUN" in
      let (code, faddr) = List.fold_left (fun (code_acc, saddr_acc) mrule ->
        let faddr' = labelNewLabel saddr_fun "" in
        let code_mrule = mrule2code environ saddr_acc faddr' mrule
        in
          (code_acc @@ code_mrule, faddr')
      ) (code0, saddr_fun) mlist
      in
        (cpost code [LABEL faddr; EXCEPTION; LABEL saddr], ADDR (CADDR saddr_fun))
    )
  | EXPTY (E_APP (expty1, expty2), T_FUN _) -> (
      let label1 = labelNewLabel saddr "E_APP1" in
      let label2 = labelNewLabel saddr "E_APP2" in
      let (code1, rvalue1) = expty2code environ label1 expty1 in
      let (code2, rvalue2) = expty2code environ label2 expty2
      in
        match rvalue1 with
          ADDR (CADDR addr_fun) ->
            let label' = labelNewStr "E_APP_NEW"
            in
              (cpost (code1 @@ code2) [LABEL label'; PUSH rvalue2; CALL rvalue1; LABEL saddr], ADDR (CADDR label'))
        | _ -> (clist [LABEL saddr; DEBUG "E_APP's expty1 is not E_FUN"], INT 0)
    )
  | EXPTY (E_APP (expty1, expty2), _) -> (
      let label1 = labelNewLabel saddr "E_APP1" in
      let (code1, rvalue1) = expty2code environ label1 expty1 in
      let (code2, rvalue2) = expty2code environ saddr expty2
      in
        match rvalue1 with
          ADDR (CADDR addr_fun) ->
            (cpost (code1 @@ code2) [PUSH rvalue2; CALL rvalue1], REG ax)
        | _ -> (clist [LABEL saddr; DEBUG "E_APP's expty1 is not E_FUN"], INT 0)
    )
  | EXPTY (E_LET (dec, expty'), _) -> (
      let (code_d, env_d) = dec2code environ saddr dec in
      let (code_et', rvalue_et') = expty2code env_d (labelNewLabel saddr "_LET_EXPTY") expty'
        in (code_d @@ code_et', rvalue_et')
    )
  | EXPTY (exp, _) -> exp2code environ saddr exp

(* dec2code : env -> Mach.label -> Mono.dec -> Mach.code * env *)
and dec2code environ saddr dec = match dec with
    D_VAL (patty, expty) ->
      let (code_et, rvalue_et) = expty2code environ saddr expty in
      let (code_pt, venv_pt) = patty2code
                                      (labelNewLabel saddr "_PATTY_START")
                                      (labelNewLabel saddr "_PATTY_FAIL")
                                      (rvalue2loc rvalue_et)
                                      patty in
      let (venviron, count) = environ
      in
        (cpre [LABEL saddr] (code_et @@ code_pt), (Dict.merge venviron venv_pt, count + 1))
  (* | D_REC (patty, expty) -> *)
  (* | D_DTYPE ->  *)
  | _ -> (cpre [LABEL saddr] code0, env0)

(* mrule2code : env -> Mach.label -> Mach.label -> Mono.mrule -> Mach.code *)
and mrule2code environ saddr faddr (M_RULE (patty, expty)) =
  let (venviron, count) = environ in
  let (code_pt, venv_pt) = patty2code saddr faddr (L_DREF (L_REG bp, -3)) patty in
  let venv' = Dict.merge venviron venv_pt in
  let (code_et, rvalue_et) = expty2code (venv', count + 1) (labelNewLabel saddr "_EXPTY") expty
  in
    cpost (code_pt @@ code_et) [MOVE (LREG ax, rvalue_et); RETURN]

(* program2code : Mono.program -> Mach.code *)
and program2code (dlist, et) =
  let (code_dl, env_dl, _) = List.fold_left (
      fun (code_prev, env_prev, count) dec ->
        let labelStr = "DEC" ^ (string_of_int count) in
        let (code_curr, env_curr) = dec2code env_prev (labelNewStr labelStr) dec
        in
          ([DEBUG labelStr] @@ code_prev @@ code_curr, env_curr, count + 1)
    ) (code0, env0, 0) dlist in
  let (code_et, rvalue_et) = expty2code env_dl (start_label) et
  in
    code_dl @@ [DEBUG "RESULT"] @@ code_et @@ [HALT rvalue_et]
