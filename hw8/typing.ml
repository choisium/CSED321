exception NotImplemented
exception TypingError


let freshTyvarCounter = ref 0
let freshTynameCounter = ref 0
                          
(*   
 * getFreshTyvar, getFreshTyname : unit - int
 * use this function if you need to generate a fresh type variable or type name. 
 *)
let getFreshTyvar () = 
  let _ = freshTyvarCounter := !freshTyvarCounter + 1
  in !freshTyvarCounter

let getFreshTyname () = 
  let _ = freshTynameCounter := !freshTynameCounter + 1
  in !freshTynameCounter

type tvset = Core.tyvar Set_type.set
let tvset0: tvset = Set_type.empty
(* TE *)
type tenv = (Ast.tycon, Core.ty) Dict.dict
let tenv0: tenv = Dict.empty
(* VE *)
type venv = (Ast.vid, ((tvset * Core.ty) * Core.is)) Dict.dict
let venv0: venv = Dict.empty
(* substitution S *)
type tySub = (Core.tyvar, Core.ty) Dict.dict
let tySub0: tySub = Dict.empty

(* Helper functions *)

(* for {Beta set/Alpha set} A in algorithm W(Gamma, x) *)
let substitute tvset t =
  let mapping = Set_type.fold (fun acc e -> Dict.insert (e, getFreshTyvar ()) acc) Dict.empty tvset in
  let rec substitute' t' = (
    match t' with
    | Core.T_PAIR (t1, t2) -> Core.T_PAIR (substitute' t1, substitute' t2)
    | Core.T_FUN (t1, t2) -> Core.T_FUN (substitute' t1, substitute' t2)
    | Core.T_VAR tv -> (
        match Dict.lookup tv mapping with
          Some tv' -> Core.T_VAR tv'
        | None -> Core.T_VAR tv
      )
    | t'' -> t''
  )
  in substitute' t

(* for S A *)
let rec applySubstitution s tvset ty =
  let rec applySubstitution' (s1, s2) tvset ty =
    if Set_type.mem s1 tvset then (
      (tvset, ty)
    )
    else if (Set_type.size tvset) <> 0 then (
      let (_, ty') = applySubstitution s tvset0 ty in
      (tvset, ty')
    )
    else (
      let ty' = match ty with
          Core.T_PAIR (ty1, ty2) -> (
            let (_, ty1') = applySubstitution s tvset0 ty1 in
            let (_, ty2') = applySubstitution s tvset0 ty2 in
            Core.T_PAIR (ty1', ty2')
          )
        | Core.T_FUN (ty1, ty2) -> (
            let (_, ty1') = applySubstitution s tvset0 ty1 in
            let (_, ty2') = applySubstitution s tvset0 ty2 in
            Core.T_FUN (ty1', ty2')
          )
        | Core.T_VAR tv -> (
            if tv = s1 then (
              let (_, s2') = applySubstitution s tvset0 s2
              in s2'
            )
            else ty
          )
        | _ -> ty
      in (tvset0, ty')
    )
  in Dict.fold (fun (tvset', ty') elem ->
    applySubstitution' elem tvset' ty'
  ) (tvset, ty) s

let applySubstitutionTE s te =
  Dict.map (fun ty ->
    let (_, ty') = applySubstitution s tvset0 ty
    in ty'
  ) te

let applySubstitutionVE s ve =
  Dict.map (fun ((tvset, ty), is) -> (applySubstitution s tvset ty, is)) ve

let applySubstitutionCtx s (te, ve) =
  let te' = applySubstitutionTE s te in
  let ve' = applySubstitutionVE s ve
  in
    (te', ve')

let rec applySubstitutionPatty s patty =
  let Core.PATTY (pat, ty) = patty in
  let pat' = match pat with
  | Core.P_VIDP (vid, patty) -> Core.P_VIDP (vid, applySubstitutionPatty s patty)
  | Core.P_PAIR (patty1, patty2) -> Core.P_PAIR (applySubstitutionPatty s patty1, applySubstitutionPatty s patty2)
  | _ -> pat
  in
  let (_, ty') = applySubstitution s tvset0 ty in
  Core.PATTY (pat', ty')

let rec applySubstitutionExpty s expty =
  let Core.EXPTY (exp, ty) = expty in
  let exp' = match exp with
  | Core.E_FUN mlist -> Core.E_FUN (applySubstitutionMlist s mlist)
  | Core.E_APP (expty1, expty2) -> Core.E_APP (applySubstitutionExpty s expty1, applySubstitutionExpty s expty2)
  | Core.E_PAIR (expty1, expty2) -> Core.E_PAIR (applySubstitutionExpty s expty1, applySubstitutionExpty s expty2)
  | Core.E_LET (dec, expty') -> Core.E_LET (applySubstitutionDec s dec, applySubstitutionExpty s expty')
  | _ -> exp
  in
  let (_, ty') = applySubstitution s tvset0 ty in
  Core.EXPTY (exp', ty')

and applySubstitutionDec s dec =
  match dec with
    Core.D_VAL (patty, expty) -> Core.D_VAL (applySubstitutionPatty s patty, applySubstitutionExpty s expty)
  | Core.D_REC (patty, expty) -> Core.D_VAL (applySubstitutionPatty s patty, applySubstitutionExpty s expty)
  | _ -> dec

and applySubstitutionMlist s mlist =
  List.fold_right (fun mrule acc -> (applySubstitutionMrule s mrule) :: acc) mlist []

and applySubstitutionMrule s mrule =
  let Core.M_RULE (patty, expty) = mrule in
  Core.M_RULE (applySubstitutionPatty s patty, applySubstitutionExpty s expty)
  
(* For closure(advanced version of generalize) *)
let rec findFreeTyvarInTy ty =
  match ty with
    Core.T_PAIR (ty1, ty2) -> (
      let acc1 = findFreeTyvarInTy ty1 in
      let acc2 = findFreeTyvarInTy ty2 in
      Set_type.union acc1 acc2
    )
  | Core.T_FUN (ty1, ty2) -> (
      let acc1 = findFreeTyvarInTy ty1 in
      let acc2 = findFreeTyvarInTy ty2 in
      Set_type.union acc1 acc2
    )
  | Core.T_VAR tv -> Set_type.singleton tv
  | _ -> tvset0

let rec findFreeTyvarInVE ve =
  Dict.fold (fun acc (vid, ((tvset, ty), is)) ->
    let tv1 = findFreeTyvarInTy ty in
    let tv2 = Set_type.diff tv1 tvset in
    Set_type.union acc tv2
  ) tvset0 ve

let findClosure ve ve' =
  let tvVE = findFreeTyvarInVE ve in
  Dict.fold (fun acc (vid, ((tvset, ty), is)) -> 
    let tvTy = findFreeTyvarInTy ty in
    let tv = Set_type.diff tvTy tvVE in
    let tv' = Set_type.union tv tvset in
    Dict.insert (vid, ((tv', ty), is)) acc
  ) Dict.empty ve'

(* Unify *)
let unify tyequations' =
  let rec unify' tyequations s = 
    match tyequations with
      [] -> s
    | (Core.T_INT, Core.T_INT) :: rest -> unify' rest s
    | (Core.T_BOOL, Core.T_BOOL) :: rest -> unify' rest s
    | (Core.T_UNIT, Core.T_UNIT) :: rest -> unify' rest s
    | (Core.T_NAME tn1, Core.T_NAME tn2) :: rest -> if tn1 = tn2 then unify' rest s else raise TypingError
    | (Core.T_PAIR (ty1, ty2), Core.T_PAIR (ty1', ty2')) :: rest -> unify' ((ty1, ty1') :: (ty2, ty2') :: rest) s
    | (Core.T_FUN (ty1, ty2), Core.T_FUN (ty1', ty2')) :: rest -> unify' ((ty1, ty1') :: (ty2, ty2') :: rest) s
    | (Core.T_VAR a, ty) :: rest -> (
        let (_, ty') = applySubstitution s tvset0 ty in
        if ty' = Core.T_VAR a then unify' rest s
        else if Set_type.mem a (findFreeTyvarInTy ty') then raise TypingError
        else (
          unify' rest (Dict.insert (a, ty') s)
        )
      )
    | (ty, Core.T_VAR a) :: rest -> (
        let (_, ty') = applySubstitution s tvset0 ty in
        if ty' = Core.T_VAR a then unify' rest s
        else if Set_type.mem a (findFreeTyvarInTy ty') then raise TypingError
        else (
          unify' rest (Dict.insert (a, ty') s)
        )
      )
    | _ -> raise TypingError
  in unify' tyequations' tySub0


(* Convert functions *)

let rec convertTy te ty =
  match ty with
    Ast.T_INT -> Core.T_INT
  | Ast.T_BOOL -> Core.T_BOOL
  | Ast.T_UNIT -> Core.T_UNIT
  | Ast.T_CON tycon -> (
      match Dict.lookup tycon te with
        Some t -> t
      | None -> raise TypingError
    )
  | Ast.T_PAIR (ty1, ty2) -> Core.T_PAIR (convertTy te ty1, convertTy te ty2)
  | Ast.T_FUN (ty1, ty2) -> Core.T_FUN (convertTy te ty1, convertTy te ty2)

let rec convertPat ctx pat =
  let (te, ve) = ctx
  in
    match pat with
      Ast.P_WILD -> (Core.PATTY(Core.P_WILD, Core.T_VAR (getFreshTyvar ())), venv0)
    | Ast.P_INT n -> (Core.PATTY(Core.P_INT n, Core.T_INT), venv0)
    | Ast.P_BOOL b -> (Core.PATTY(Core.P_BOOL b, Core.T_BOOL), venv0)
    | Ast.P_UNIT -> (Core.PATTY(Core.P_UNIT, Core.T_UNIT), venv0)
    | Ast.P_VID vid -> (
        match Dict.lookup vid ve with
          None -> (
            let a = getFreshTyvar () in
            let tsch = (tvset0, Core.T_VAR a) in
            (Core.PATTY(Core.P_VID (vid, Core.VAR), Core.T_VAR a), Dict.insert (vid, (tsch, Core.VAR)) venv0)
          )
        | Some (tsch, Core.VAR) -> (
            let a = getFreshTyvar () in
            let tsch = (tvset0, Core.T_VAR a) in
            (Core.PATTY(Core.P_VID (vid, Core.VAR), Core.T_VAR a), Dict.insert (vid, (tsch, Core.VAR)) venv0)
          )
        | Some ((tvset, t), Core.CON) -> (
            if Set_type.size tvset = 0
            then (Core.PATTY(Core.P_VID (vid, Core.CON), t), venv0)
            else raise TypingError
          )
        | _ -> raise TypingError
      )
    | Ast.P_VIDP (vid, p) -> (
        match Dict.lookup vid ve with
          Some ((tvset, Core.T_FUN(t1, t2)), Core.CONF) -> (
            if Set_type.size tvset = 0
            then (
              let (p', ve') = convertPat ctx p in
              let Core.PATTY(_, t1') = p' in
              let s = unify [(t1, t1')] in
              let p'' = applySubstitutionPatty s p' in
              let (_, t2'') = applySubstitution s tvset0 t2 in
              (Core.PATTY(Core.P_VIDP ((vid, Core.CONF), p''), t2''), applySubstitutionVE s ve')
            )
            else raise TypingError
          )
        | _ -> raise TypingError
      )
    | Ast.P_PAIR (p1, p2) -> (
        let (p1', ve1) = convertPat ctx p1 in
        let Core.PATTY(_, t1') = p1' in
        let (p2', ve2) = convertPat ctx p2 in
        let Core.PATTY(_, t2') = p2' in
        (Core.PATTY(Core.P_PAIR(p1', p2'), Core.T_PAIR(t1', t2')), Dict.merge ve1 ve2)
      )
    | Ast.P_TPAT (p, ty) -> (
        let (p', ve) = convertPat ctx p in
        let Core.PATTY(_, ty1) = p' in
        let ty2 = convertTy te ty in
        let s = unify [(ty1, ty2)] in
        (applySubstitutionPatty s p', applySubstitutionVE s ve)
      )

let rec convertExp ctx exp =
  let (te, ve) = ctx
  (* let (s, t') = typeExp ctx exp
  in let _ = Core_print.ty2str t' *)
  in
    match exp with
      Ast.E_INT n -> (tySub0, Core.EXPTY(Core.E_INT n, Core.T_INT))
    | Ast.E_BOOL b -> (tySub0, Core.EXPTY(Core.E_BOOL b, Core.T_BOOL))
    | Ast.E_UNIT -> (tySub0, Core.EXPTY(Core.E_UNIT, Core.T_UNIT))
    | Ast.E_PLUS -> (tySub0, Core.EXPTY(Core.E_PLUS, Core.T_FUN (Core.T_PAIR(Core.T_INT, Core.T_INT), Core.T_INT)))
    | Ast.E_MINUS -> (tySub0, Core.EXPTY(Core.E_MINUS, Core.T_FUN (Core.T_PAIR(Core.T_INT, Core.T_INT), Core.T_INT)))
    | Ast.E_MULT -> (tySub0, Core.EXPTY(Core.E_MULT, Core.T_FUN (Core.T_PAIR(Core.T_INT, Core.T_INT), Core.T_INT)))
    | Ast.E_EQ -> (tySub0, Core.EXPTY(Core.E_EQ, Core.T_FUN (Core.T_PAIR(Core.T_INT, Core.T_INT), Core.T_BOOL)))
    | Ast.E_NEQ -> (tySub0, Core.EXPTY(Core.E_NEQ, Core.T_FUN (Core.T_PAIR(Core.T_INT, Core.T_INT), Core.T_BOOL)))
    | Ast.E_VID x -> (
        match Dict.lookup x ve with
          Some ((tvset, t), is) -> (
            (tySub0, Core.EXPTY(Core.E_VID (x, is), substitute tvset t))
          )
        | _ -> raise TypingError
      )
    | Ast.E_FUN mlist -> convertMlist ctx mlist
    | Ast.E_APP (e1, e2) -> (
        let (s1, e1') = convertExp ctx e1 in
        let Core.EXPTY (e1'', t1) = e1' in
        let ctx' = applySubstitutionCtx s1 ctx in
        let (s2, e2') = convertExp ctx' e2 in
        let Core.EXPTY (e2'', t2) = e2' in
        let tv = Core.T_VAR (getFreshTyvar ()) in
        let (_, t1') = applySubstitution s2 tvset0 t1 in
        let s3 = unify [(t1', Core.T_FUN(t2, tv))] in
        let e1'' = applySubstitutionExpty s3 e1' in
        let e2'' = applySubstitutionExpty s3 e2' in
        let (_, tv') = applySubstitution s3 tvset0 tv in
        (Dict.merge s3 (Dict.merge s2 s1), Core.EXPTY(Core.E_APP(e1'',e2''), tv'))
      )
    | Ast.E_PAIR (e1, e2) -> (
        let (s1, e1') = convertExp ctx e1 in
        let ctx' = applySubstitutionCtx s1 ctx in
        let (s2, e2') = convertExp ctx' e2 in
        let Core.EXPTY (_, t2) = e2' in
        let e1'' = applySubstitutionExpty s2 e1' in
        let Core.EXPTY (_, t1') = e1'' in
        (Dict.merge s2 s1, Core.EXPTY(Core.E_APP (e1'', e2'), Core.T_PAIR (t1', t2)))
      )
    | Ast.E_LET (d, e) -> (
        let (d', (te', ve')) = convertDec ctx d in
        let (s, e') = convertExp (Dict.merge te te', Dict.merge ve ve') e in
        let Core.EXPTY (_, ty) = e' in
        (s, Core.EXPTY(Core.E_LET (d', e'), ty))
      )
    | Ast.E_TEXP (e, ty) -> (
        let (s, e') = convertExp ctx e in
        let Core.EXPTY (_, t1) = e' in
        let ty' = convertTy te ty in
        let (_, t2) = applySubstitution s tvset0 ty' in
        let s' = unify [(t1, t2)] in
        (s', e')
      )

and convertMrule ctx mrule =
  let (te, ve) = ctx in
  let Ast.M_RULE (pat, exp) = mrule in
  let (pat', ve') = convertPat ctx pat in
  let (s, exp') = convertExp (te, Dict.merge ve ve') exp in
  let Core.EXPTY (_, ty2) = exp' in
  let pat'' = applySubstitutionPatty s pat' in
  let Core.PATTY (_, ty1) = pat'' in
  (s, [Core.M_RULE(pat'', exp')], Core.T_FUN(ty1, ty2))

and convertMlist ctx mlist =
  match mlist with
    [] -> raise TypingError
  | [mrule] -> (
      let (s, mlist', ty) = convertMrule ctx mrule in
      (s, Core.EXPTY(Core.E_FUN mlist', ty))
    )
  | head :: tail -> (
      let (s_mlist, mlist', ty_mlist) = List.fold_left (fun (s_acc, mlist_acc, ty_acc) mrule -> 
        let ctx' = applySubstitutionCtx s_acc ctx in
        let (s_in, mlist_in, ty_in) = convertMrule ctx' mrule in
        let s' = unify [(ty_in, ty_acc)] in
        let (_, ty_next) = applySubstitution s' tvset0 ty_in in
        let mlist_next = applySubstitutionMlist s' (mlist_acc @ mlist_in) in
        (Dict.merge s' (Dict.merge s_in s_acc), mlist_next, ty_next)
      ) (convertMrule ctx head) tail
      in (s_mlist, Core.EXPTY(Core.E_FUN mlist', ty_mlist))
    )

and convertDec ctx dec =
  let (te, ve) = ctx in
  match dec with
    Ast.D_VAL (pat, exp) -> (
      let (p, ve') = convertPat ctx pat in
      let Core.PATTY (p', t1) = p in
      let (s, e) = convertExp ctx exp in
      let Core.EXPTY (e', t2) = e in
      let s' = unify [(t1, t2)] in
      let ctx' = (tenv0, findClosure ve (applySubstitutionVE (Dict.merge s' s) ve')) in
      let p' = applySubstitutionPatty s' p in
      let e' = applySubstitutionExpty s' e
      in
        (Core.D_VAL (p', e'), ctx')
    )
  | Ast.D_REC (pat, exp) -> (
      let (p, ve') = convertPat ctx pat in
      let Core.PATTY (p', t1) = p in
      let (s, e) = convertExp (te, Dict.merge ve ve') exp in
      let Core.EXPTY (e', t2) = e in
      match t2 with
        Core.T_FUN (t1', t2') -> (
          let s' = unify [(t1, t2)] in
          let ctx' = (tenv0, findClosure ve (applySubstitutionVE (Dict.merge s' s) ve')) in
          let p' = applySubstitutionPatty (Dict.merge s' s) p in
          let e' = applySubstitutionExpty (Dict.merge s' s) e
          in
            (Core.D_REC (p', e'), ctx')
        )
      | _ -> raise TypingError
    )
  | Ast.D_DTYPE (tycon, conlist) -> (
      let t = Core.T_NAME (getFreshTyname ()) in
      let te' = Dict.insert (tycon, t) te in
      let ve' = convertConlist te' t conlist in
      (Core.D_DTYPE, (te', ve'))
    )

and convertConlist te tn conlist =
  List.fold_left (fun ve_acc conbind -> Dict.merge ve_acc (convertConbind te tn conbind)) venv0 conlist

and convertConbind te tn conbind =
  match conbind with
    Ast.CB_VID vid -> Dict.insert (vid, ((tvset0, tn), Core.CON)) venv0
  | Ast.CB_TVID (vid, ty) -> (
      let ty' = convertTy te ty in
      Dict.insert (vid, ((tvset0, Core.T_FUN(ty', tn)), Core.CONF)) venv0
    )

(* tprogram : Ast.program -> Core.program *)
let tprogram (dlist, exp) =
  let (dlist', ctx') = List.fold_left (fun (dlist_acc, ctx_acc) dec ->
    let (te_acc, ve_acc) = ctx_acc in
    let (dec_in, ctx_in) = convertDec ctx_acc dec in
    let (te_in, ve_in) = ctx_in in
    (dlist_acc @ [dec_in], (Dict.merge te_acc te_in, Dict.merge ve_acc ve_in))
  ) ([], (tenv0, venv0)) dlist
  in let (s, e)= convertExp ctx' exp
  in (dlist', e)
