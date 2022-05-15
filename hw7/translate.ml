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
let fail_label = labelNewStr ""

(* pat2code : Mach.label -> Mach.label - > loc -> Mono.pat -> Mach.code * env *)
let rec pat2code saddr faddr l pat = match pat with
    P_WILD -> (code0, (venv0, 0))
  | P_INT n -> (
      let (code, rvalue) = loc2rvalue l in
      let code' = cpost code [JMPNEQ (ADDR (CADDR faddr), rvalue, INT n)]
      in
        (cpre [LABEL saddr] code', (venv0, 0))
    )
  | P_BOOL true -> (
      let (code, rvalue) = loc2rvalue l in
      let label_true = labelNewLabel saddr "_TRUE" in
      let code' = cpost code [
        JMPTRUE (ADDR (CADDR label_true), rvalue);
        JUMP (ADDR (CADDR faddr));
        LABEL label_true;
      ]
      in
        (cpre [LABEL saddr] (code @@ code'), (venv0, 0))
    )
  | P_BOOL false -> (
      let (code, rvalue) = loc2rvalue l in
      let code' = cpost code [JMPTRUE (ADDR (CADDR faddr), rvalue)]
      in
        (cpre [LABEL saddr] (code @@ code'), (venv0, 0))
    )
  | P_VID (avid, VAR) -> (
      let venv' = Dict.insert (avid, l) venv0
      in
        (code0, (venv', 1))
    )
  | P_VID (avid, CON) -> (
      let (code, rvalue) = loc2rvalue l in
      let venv' = Dict.insert (avid, l) venv0 in
      let code' = cpost code [MOVE (LREG ax, rvalue); JMPNEQSTR (ADDR (CADDR faddr), REFREG (ax, 0), STR avid)]
      in
        (code', (venv', 0))
    )
  | P_VIDP ((avid, CONF), patty) -> (
      let (code, rvalue) = loc2rvalue l in
      let venv' = Dict.insert (avid, l) venv0 in
      let code' = cpost code [MOVE (LREG ax, rvalue); JMPNEQSTR (ADDR (CADDR faddr), REFREG (ax, 0), STR avid); MOVE (LREG ax, REFREG (ax, 1))] in
      let (code'', (venv'', count'')) = patty2code saddr faddr (L_REG ax) patty
      in
        (code' @@ code'', (Dict.merge venv' venv'', count''))
    )
  | P_PAIR (patty1, patty2) -> (
      (* let (code, rvalue) = loc2rvalue l in *)
      let (code1, (venv1, count1)) = patty2code (labelNewLabel saddr "_FST") faddr (L_DREF (l, 0)) patty1 in
      let (code2, (venv2, count2)) = patty2code (labelNewLabel saddr "_SND") faddr (L_DREF (l, 1)) patty2
      in
        (code1 @@ code2, (Dict.merge venv1 venv2, count1 + count2))
    )
  | _ -> (code0, (venv0, 0))

(* patty2code : Mach.label -> Mach.label -> loc -> Mono.patty -> Mach.code * venv *)
and patty2code saddr faddr l patty =
  let PATTY (pat, _) = patty
  in
    pat2code saddr faddr l pat

(* exp2code : env -> Mach.label -> Mono.exp -> Mach.code * Mach.code * Mach.rvalue *)
and exp2code environ saddr exp =
  let (venviron, count) = environ in
  match exp with
      E_INT n -> (code0, code0, INT n)
    | E_BOOL b -> (code0, code0, BOOL b)
    | E_UNIT -> (code0, code0, UNIT)
    | E_VID (avid, VAR) -> (
        match Dict.lookup avid venviron with
          None -> (code0, clist [DEBUG (avid ^ " missing"); EXCEPTION], INT (-1))
        | Some l ->
            let (code, rvalue) = loc2rvalue l
            in
              (code0, code, rvalue)
      )
    | E_VID (avid, CON) -> (code0, clist [MALLOC (LREG ax, INT 1); MOVE (LREFREG (ax, 0), STR avid)], REG ax)
    | E_VID (avid, CONF) -> (
        let fn_code = clist [
          LABEL saddr;
          MALLOC (LREG ax, INT 2);
          MOVE (LREFREG (ax, 0), STR avid);
          MOVE (LREFREG (ax, 1), REFREG (bp, - 3));
          RETURN
        ]
        in
          (fn_code, code0, ADDR (CADDR saddr))
      )
    | E_FUN mlist -> (
        let (fn_code, code, faddr) = List.fold_left (
          fun (fn_code_acc, code_acc, saddr_acc) mrule ->
            let faddr_mrule = labelNewLabel saddr "" in
            let (fn_code_mrule, code_mrule) = mrule2code environ saddr_acc faddr_mrule mrule
            in
              (fn_code_acc @@ fn_code_mrule, code_acc @@ code_mrule, faddr_mrule)
        ) (code0, code0, labelNewLabel saddr "_MLIST") mlist in
        let code' = cpost code [LABEL faddr; EXCEPTION]
        in
          (cpre [LABEL saddr] (code' @@ fn_code), code0, ADDR (CADDR saddr))
      )
    | E_PAIR (expty1, expty2) -> (
        let saddr1 = labelNewLabel saddr "_1" in
        let saddr2 = labelNewLabel saddr "_2" in
        let (fn_code1, code1, rvalue1) = expty2code environ saddr1 expty1 in
        let code1' = cpost code1 [PUSH rvalue1] in
        let (fn_code2, code2, rvalue2) = expty2code environ saddr2 expty2 in
        let code2' = cpost (code1' @@ code2) [
          MALLOC (LREG bx, INT 2);
          MOVE (LREFREG (bx, 0), REFREG (sp, -1));
          POP (LREG tr);
          MOVE (LREFREG (bx, 1), rvalue2);
          MOVE (LREG ax, REG bx)]
        in
          (fn_code1 @@ fn_code2, code2', REG ax)
      )
    | E_LET (dec, expty) -> (
        let saddr1 = labelNewLabel saddr "_1" in
        let saddr2 = labelNewLabel saddr "_2" in
        let (fn_code1, code1, environ') = dec2code environ saddr1 dec in
        let (fn_code2, code2, rvalue) = expty2code environ' saddr2 expty
        in
          (fn_code1 @@ fn_code2, code1 @@ code2, rvalue)
      )
    | _ -> (code0, code0, INT (-1))

(* expty2code : env -> Mach.label -> Mono.expty -> Mach.code * Mach.code * Mach.rvalue *)
and expty2code environ saddr expty =
  let (venviron, count) = environ in
  match expty with
      EXPTY(E_APP (EXPTY (E_PLUS, _), EXPTY (E_PAIR (expty1, expty2), _)), _) -> (
        let saddr1 = labelNewLabel saddr "_1" in
        let saddr2 = labelNewLabel saddr "_2" in
        let (fn_code1, code1, rvalue1) = expty2code environ saddr1 expty1 in
        let code' = cpost code1 [PUSH rvalue1] in
        let (fn_code2, code2, rvalue2) = expty2code environ saddr2 expty2 in
        let code'' = cpost (code' @@ code2) [ADD (LREG ax, REFREG (sp, -1), rvalue2); POP (LREG tr)]
        in
          (fn_code1 @@ fn_code2, code'', REG ax)
      )
    | EXPTY(E_APP (EXPTY (E_MINUS, _), EXPTY (E_PAIR (expty1, expty2), _)), _) -> (
        let saddr1 = labelNewLabel saddr "_1" in
        let saddr2 = labelNewLabel saddr "_2" in
        let (fn_code1, code1, rvalue1) = expty2code environ saddr1 expty1 in
        let code' = cpost code1 [PUSH rvalue1] in
        let (fn_code2, code2, rvalue2) = expty2code environ saddr2 expty2 in
        let code'' = cpost (code' @@ code2) [SUB (LREG ax, REFREG (sp, -1), rvalue2); POP (LREG tr)]
        in
          (fn_code1 @@ fn_code2, code'', REG ax)
      )
    | EXPTY(E_APP (EXPTY (E_MULT, _), EXPTY (E_PAIR (expty1, expty2), _)), _) -> (
        let saddr1 = labelNewLabel saddr "_1" in
        let saddr2 = labelNewLabel saddr "_2" in
        let (fn_code1, code1, rvalue1) = expty2code environ saddr1 expty1 in
        let code' = cpost code1 [PUSH rvalue1] in
        let (fn_code2, code2, rvalue2) = expty2code environ saddr2 expty2 in
        let code'' = cpost (code' @@ code2) [MUL (LREG ax, REFREG (sp, -1), rvalue2); POP (LREG tr)]
        in
          (fn_code1 @@ fn_code2, code'', REG ax)
      )
    | EXPTY(E_APP (EXPTY (E_EQ, _), EXPTY (E_PAIR (expty1, expty2), _)), _) -> (
        let saddr1 = labelNewLabel saddr "_1" in
        let saddr2 = labelNewLabel saddr "_2" in
        let (fn_code1, code1, rvalue1) = expty2code environ saddr1 expty1 in
        let (fn_code2, code2, rvalue2) = expty2code environ saddr2 expty2 in
        let label_neq = labelNewLabel saddr "_NEQ" in
        let label_final = labelNewLabel saddr "_FINAL" in
        let code' = cpost (code1 @@ code2) [
          JMPNEQ (ADDR (CADDR label_neq), rvalue1, rvalue2);
          MOVE (LREG ax, BOOL true);
          JUMP (ADDR (CADDR label_final));
          LABEL label_neq;
          MOVE (LREG ax, BOOL false);
          LABEL label_final
        ]
        in
          (fn_code1 @@ fn_code2, code', REG ax)
      )
    | EXPTY(E_APP (EXPTY (E_NEQ, _), EXPTY (E_PAIR (expty1, expty2), _)), _) -> (
        let saddr1 = labelNewLabel saddr "_1" in
        let saddr2 = labelNewLabel saddr "_2" in
        let (fn_code1, code1, rvalue1) = expty2code environ saddr1 expty1 in
        let (fn_code2, code2, rvalue2) = expty2code environ saddr2 expty2 in
        let label_neq = labelNewLabel saddr "_NEQ" in
        let label_final = labelNewLabel saddr "_FINAL" in
        let code' = cpost (code1 @@ code2) [
          JMPNEQ (ADDR (CADDR label_neq), rvalue1, rvalue2);
          MOVE (LREG ax, BOOL false);
          JUMP (ADDR (CADDR label_final));
          LABEL label_neq;
          MOVE (LREG ax, BOOL true);
          LABEL label_final
        ]
        in
          (fn_code1 @@ fn_code2, code', REG ax)
      )
    | EXPTY(E_APP (expty1, expty2), ty) -> (
        let saddr1 = labelNewLabel saddr "_1" in
        let saddr2 = labelNewLabel saddr "_2" in
        let (fn_code1, code1, rvalue1) = expty2code environ saddr1 expty1 in
        let (fn_code2, code2, rvalue2) = expty2code environ saddr2 expty2 in
        match ty with
            T_FUN _ -> (
              let code' = cpost (code1 @@ code2) [PUSH rvalue2; CALL rvalue1; POP (LREG tr); RETURN]
              in
                (fn_code1 @@ fn_code2 @@ (cpre [LABEL saddr] code'), code0, ADDR (CADDR saddr))
            )
          | _ -> (
              let code' = cpost (code1 @@ code2) [PUSH rvalue2; CALL rvalue1; POP (LREG tr)]
              in
                (fn_code1 @@ fn_code2, cpre [LABEL saddr] code', REG ax)
            )
      )
    | _ -> (
        let EXPTY (exp, ty) = expty
        in
          exp2code environ saddr exp
      )

(* dec2code : env -> Mach.label -> Mono.dec -> Mach.code * Mach.code * env *)
and dec2code environ saddr dec =
  let (venv, count) = environ
  in
    match dec with
      D_VAL (patty, expty) ->
        let (fn_code, code1, rvalue) = expty2code environ (labelNewLabel saddr "DECVALPAT_") expty in
        let (code2, (venv2, count2)) = patty2code (labelNewLabel saddr "DECVALEXP_") fail_label (rvalue2loc rvalue) patty
        in
          (fn_code, code1 @@ code2, (Dict.merge venv venv2 , count + count2))
    | D_REC (patty, expty) ->
        let label_fun = labelNewLabel saddr "DECRECEXP_" in
        let (code1, (venv1, count1)) = patty2code (labelNewLabel saddr "DECRECPAT_") fail_label (L_ADDR (CADDR label_fun)) patty in
        let environ' = (Dict.merge venv venv1, count + count1) in
        let (fn_code, code2, rvalue) = expty2code environ' label_fun expty
        in
          (fn_code, code1 @@ code2, environ')
    | _ -> (code0, code0, env0)

(* mrule2code : env -> Mach.label -> Mach.label -> Mono.mrule -> Mach.code * Mach.code *)
and mrule2code environ saddr faddr (M_RULE (patty, expty)) =
  let (venv, count) = environ in
  let dref = Dict.fold (
    fun acc (k, v) -> match v with
      L_DREF (L_REG bp, n) -> if acc < n then acc else n
    | _ -> acc
  ) 0 venv in
  let saddr2 = labelNewLabel saddr "_EXP" in
  let (code1, (venv1, count1)) = patty2code saddr faddr (L_DREF (L_REG bp, dref - 3)) patty in
  let environ' = (Dict.merge venv venv1, count + count1) in
  let (fn_code, code2, rvalue) = expty2code environ' saddr2 expty in
  let code' = match expty with
    EXPTY (_, T_FUN _) -> cpost (code1 @@ code2) [JUMP rvalue]
  | _ -> cpost (code1 @@ code2) [MOVE (LREG ax, rvalue); RETURN]
  in
    (fn_code, cpre [LABEL saddr] code')

(* program2code : Mono.program -> Mach.code *)
and program2code (dlist, et) =
  let (fn_code1, code1, environ) = List.fold_left (
    fun (fn_code_acc, code_acc, environ_acc) dec ->
      let (fn_code_dec, code_dec, environ_dec) = dec2code environ_acc (labelNewStr "PRDEC_") dec
      in
        (fn_code_acc @@ fn_code_dec, code_acc @@ code_dec, environ_dec)
  ) (code0, code0, env0) dlist in
  let (fn_code2, code2, rvalue) = expty2code environ (labelNewStr "PREXP_") et
  in
    fn_code1 @@ fn_code2 @@ [LABEL start_label] @@ code1 @@ code2 @@ [HALT rvalue; LABEL fail_label; EXCEPTION]
