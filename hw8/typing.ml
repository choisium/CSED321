exception NotImplemented
exception TypingError


let freshTyvarCounter = ref 0
let freshTynameCounter = ref 0
                          
(*   getFreshVariable : string -> string 
 *   use this function if you need to generate a fresh variable from s. 
 *)
let getFreshTyvar () = 
  let _ = freshTyvarCounter := !freshTyvarCounter + 1
  in !freshTyvarCounter

let getFreshTyname () = 
  let _ = freshTynameCounter := !freshTynameCounter + 1
  in !freshTynameCounter

type tvset = Core.tyvar Set_type.set (* * Core.ty) *)
let tvset0: tvset = Set_type.empty
type tenv = (Ast.tycon, Core.ty) Dict.dict
let tenv0: tenv = Dict.empty
type venv = (Ast.vid, ((tvset * Core.ty) * Core.is)) Dict.dict
let venv0: venv = Dict.empty

type tySub = (Core.tyvar, Core.ty) Dict.dict
let tySub0: tySub = Dict.empty

let ctx2str (te, ve) =
  let te_str = Dict.fold (fun acc (tycon, ty) -> acc ^", "^ tycon ^"->" ^ Core_print.ty2str ty) "" te in
  let ve_str = Dict.fold (fun acc (vid, ((tvset, ty), is)) -> acc ^", "^ vid ^"-> (tvset, "^ Core_print.ty2str ty ^"), is") "" ve in
  "TE: "^te_str ^"\nVE: "^ve_str

(* Helper function *)
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
  in let _ = print_endline "substitute"
  in substitute' t

let tvset2str tvset =
  Set_type.fold (fun acc tv -> acc^", "^(string_of_int tv)) "" tvset

let s2str s =
  Dict.fold (fun acc (tv, ty) -> acc^", "^(string_of_int tv)^"->"^(Core_print.ty2str ty)) "" s

(* s: tyvar -> ty *)
(* let applySubstitution s tvset ty =
  let rec applySubstitution' (s1, s2) tvset ty =
    (* match s1 with
      Core.T_VAR s1' -> ( *)
        (* let _ = print_endline ("applySub tvset: "^tvset2str tvset) in *)
        if Set_type.mem s1 tvset then (
          (* let _ = print_endline ("substitute s1 in tvset") in *)
          (tvset, ty)
        )
        else if (Set_type.size tvset) <> 0 then (
          (* let _ = print_endline ("substitute tvset not empty") in *)
          let (_, ty') = applySubstitution' (s1, s2) tvset0 ty in
          (tvset, ty')
        )
        else (
          let ty' = match ty with
              Core.T_PAIR (ty1, ty2) -> (
                let (_, ty1') = applySubstitution' (s1, s2) tvset0 ty1 in
                let (_, ty2') = applySubstitution' (s1, s2) tvset0 ty2 in
                Core.T_PAIR (ty1', ty2')
              )
            | Core.T_FUN (ty1, ty2) -> (
                let (_, ty1') = applySubstitution' (s1, s2) tvset0 ty1 in
                (* let _ = print_endline ("applySub T_FUN ty1' - " ^ Core_print.ty2str ty1') in *)
                let (_, ty2') = applySubstitution' (s1, s2) tvset0 ty2 in
                (* let _ = print_endline ("applySub T_FUN ty2' - " ^ Core_print.ty2str ty2') in *)
                Core.T_FUN (ty1', ty2')
              )
            | Core.T_VAR tv -> (
                (* let _ = print_endline ("applySub tvar tv: " ^ string_of_int tv ^" / s1: "^string_of_int s1^" / s2: "^Core_print.ty2str s2) in *)
                if tv = s1 then s2
                else ty
              )
            | _ -> ty
          (* in let _ = print_endline ("applySub result - " ^ Core_print.ty2str ty') *)
          in (tvset0, ty')
        )
      (* )
      | _ -> raise TypingError *)
  in Dict.fold (fun (tvset', ty') elem ->
    applySubstitution' elem tvset' ty'
  ) (tvset, ty) s *)


let rec applySubstitution s tvset ty =
  let rec applySubstitution' (s1, s2) tvset ty =
    (* let _ = print_endline ("applySub tvset: "^tvset2str tvset) in *)
    if Set_type.mem s1 tvset then (
      (* let _ = print_endline ("substitute s1 in tvset") in *)
      (tvset, ty)
    )
    else if (Set_type.size tvset) <> 0 then (
      (* let _ = print_endline ("substitute tvset not empty") in *)
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
            (* let _ = print_endline ("applySub T_FUN ty1' - " ^ Core_print.ty2str ty1') in *)
            let (_, ty2') = applySubstitution s tvset0 ty2 in
            (* let _ = print_endline ("applySub T_FUN ty2' - " ^ Core_print.ty2str ty2') in *)
            Core.T_FUN (ty1', ty2')
          )
        | Core.T_VAR tv -> (
            (* let _ = print_endline ("applySub tvar tv: " ^ string_of_int tv ^" / s1: "^string_of_int s1^" / s2: "^Core_print.ty2str s2) in *)
            if tv = s1 then (
              let (_, s2') = applySubstitution s tvset0 s2
              in s2'
            )
            else ty
          )
        | _ -> ty
      (* in let _ = print_endline ("applySub result - " ^ Core_print.ty2str ty') *)
      in (tvset0, ty')
    )
  (* in match s with
    [] -> (tvset, ty)
  | head :: tail -> (
      let (tvset', ty') = applySubstitution' head tvset ty in
      let s' = 
      applySubstitution tail tvset' ty'
    ) *)


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

(* Generalize *)
let findClosure ve ve' =
  let tvVE = findFreeTyvarInVE ve in
  Dict.fold (fun acc (vid, ((tvset, ty), is)) -> 
    let tvTy = findFreeTyvarInTy ty in
    let tv = Set_type.diff tvTy tvVE in
    let tv' = Set_type.union tv tvset in
    Dict.insert (vid, ((tv', ty), is)) acc
  ) Dict.empty ve'


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
                let _ = print_endline ("unify t_var, "^string_of_int a ^" / "^ Core_print.ty2str ty') in

        if ty' = Core.T_VAR a then unify' rest s
        else if Set_type.mem a (findFreeTyvarInTy ty') then raise TypingError
        else (
          (* let (_, ty') = applySubstitution s tvset0 ty in *)
          unify' rest (Dict.insert (a, ty') s)
        )
      )
    | (ty, Core.T_VAR a) :: rest -> (
        let (_, ty') = applySubstitution s tvset0 ty in
                let _ = print_endline ("unify t_var, "^string_of_int a ^" / "^ Core_print.ty2str ty') in

        if ty' = Core.T_VAR a then unify' rest s
        else if Set_type.mem a (findFreeTyvarInTy ty') then raise TypingError
        else (
          (* let (_, ty') = applySubstitution s tvset0 ty in *)
          unify' rest (Dict.insert (a, ty') s)
        )
      )
    | _ -> raise TypingError
  in unify' tyequations' tySub0

(* unify: type equation list -> substitution(Dict of tyvar -> ty) *)


(* Typing function *)

(* let rec typeTy te ty =
  match ty with
    Ast.T_INT -> Core.T_INT
  | Ast.T_BOOL -> Core.T_BOOL
  | Ast.T_UNIT -> Core.T_UNIT
  | Ast.T_CON tycon -> (
      match Dict.lookup tycon te with
        Some t -> t
      | None -> raise TypingError
    )
  | Ast.T_PAIR (ty1, ty2) -> Core.T_PAIR (typeTy te ty1, typeTy te ty2)
  | Ast.T_FUN (ty1, ty2) -> Core.T_FUN (typeTy te ty1, typeTy te ty2)

let rec typePat ctx pat =
  let (te, ve) = ctx
  in
    match pat with
      Ast.P_WILD -> (Core.T_VAR getFreshTyvar, venv0)
    | Ast.P_INT n -> (Core.T_INT, venv0)
    | Ast.P_BOOL b -> (Core.T_BOOL, venv0)
    | Ast.P_UNIT -> (Core.T_UNIT, venv0)
    | Ast.P_VID vid -> (
        match Dict.lookup vid ve with
          None -> (
            let a = getFreshTyvar in
            let tsch = (tvset0, Core.T_VAR a) in
            (Core.T_VAR a, Dict.insert (vid, (tsch, Core.VAR)) venv0)
          )
        | Some (tsch, Core.VAR) -> (
            let _ = print_endline ("typePat") in
            let (tvset, ty) = tsch in
            let _ = print_endline ("typePat ty: "^ Core_print.ty2str ty) in 
            let a = getFreshTyvar in
            let tsch = (tvset0, Core.T_VAR a) in
            (Core.T_VAR a, Dict.insert (vid, (tsch, Core.VAR)) venv0)
          )
        | Some ((tvset, t), Core.CON) -> (
            if Set_type.size tvset = 0 then (t, venv0) else raise TypingError
          )
        | _ -> raise TypingError
      )
    | Ast.P_VIDP (vid, p) -> (
        match Dict.lookup vid ve with
          Some ((tvset, Core.T_FUN(t1, t2)), Core.CONF) -> (
            if Set_type.size tvset = 0
            then (
              let (t1', ve') = typePat ctx p in
              if t1 = t1' then (t2, ve') else raise TypingError     (***** *)
            )
            else raise TypingError
          )
        | _ -> raise TypingError
      )
    | Ast.P_PAIR (p1, p2) -> (
        let (t1, ve1) = typePat ctx p1 in
        let (t2, ve2) = typePat ctx p2 in
        (Core.T_PAIR(t1, t2), Dict.merge ve1 ve2)
      )
    | Ast.P_TPAT (p, ty) -> (
        let (t, ve') = typePat ctx p in
        let t' = typeTy te ty in
        if t = t' then (t, ve') else raise TypingError     (****** *)
      )

let rec typeExp ctx exp =
  let (te, ve) = ctx
  in
    match exp with
      Ast.E_INT n -> (tySub0, Core.T_INT)
    | Ast.E_BOOL b -> (tySub0, Core.T_BOOL)
    | Ast.E_UNIT -> (tySub0, Core.T_UNIT)
    | Ast.E_PLUS -> (tySub0, Core.T_FUN (Core.T_PAIR(Core.T_INT, Core.T_INT), Core.T_INT))
    | Ast.E_MINUS -> (tySub0, Core.T_FUN (Core.T_PAIR(Core.T_INT, Core.T_INT), Core.T_INT))
    | Ast.E_MULT -> (tySub0, Core.T_FUN (Core.T_PAIR(Core.T_INT, Core.T_INT), Core.T_INT))
    | Ast.E_EQ -> (tySub0, Core.T_FUN (Core.T_PAIR(Core.T_INT, Core.T_INT), Core.T_BOOL))
    | Ast.E_NEQ -> (tySub0, Core.T_FUN (Core.T_PAIR(Core.T_INT, Core.T_INT), Core.T_BOOL))
    | Ast.E_VID x -> (
        let _ = print_endline ("E_VID: "^ (Ast_print.exp2str (Ast.E_VID x))) in
        match Dict.lookup x ve with
          Some ((tvset, t), _) -> (
            let _ = print_endline ("E_VID t: "^ Core_print.ty2str t) in
            (tySub0, substitute tvset t)
          )
        | None -> raise TypingError
      )
    | Ast.E_FUN mlist -> typeMlist ctx mlist
    | Ast.E_APP (e1, e2) -> (
        let (s1, t1) = typeExp ctx e1 in
        let _ = print_endline ("E_APP t1: "^(Core_print.ty2str t1)) in
        let ctx' = applySubstitutionCtx s1 ctx in
        let _ = print_endline ("E_APP ctx': "^ (ctx2str ctx')) in
        let (s2, t2) = typeExp ctx' e2 in
        let _ = print_endline ("E_APP t2: "^(Core_print.ty2str t2)) in
        let tv = Core.T_VAR getFreshTyvar in
        let (_, t1') = applySubstitution s2 tvset0 t1 in
        let _ = print_endline ("E_APP t1': "^(Core_print.ty2str t1')) in
        let s3 = unify [(t1', Core.T_FUN(t2, tv))] in
        let (_, tv') = applySubstitution s3 tvset0 tv in
        let _ = print_endline ("E_APP tv': "^(Core_print.ty2str tv')) in
        (Dict.merge s3 (Dict.merge s2 s1), tv')
      )
    | Ast.E_PAIR (e1, e2) -> (
        let _ = print_endline ("E_PAIR: "^(Ast_print.exp2str (Ast.E_PAIR (e1, e2)))) in
        let (s1, t1) = typeExp ctx e1 in
        let _ = print_endline ("E_PAIR t1: "^(Core_print.ty2str t1)) in
        let (s2, t2) = typeExp ctx e2 in
        let _ = print_endline ("E_PAIR t1: "^(Core_print.ty2str t1)) in
        (Dict.merge s2 s1, Core.T_PAIR (t1, t2))
      )
    | Ast.E_LET (d, e) -> (
        let (te', ve') = typeDec ctx d in
        let (s, t) = typeExp (Dict.merge te te', Dict.merge ve ve') e in
        (s, t)
      )
    (* | Ast.E_TEXP (e, t) -> (
        let t1 = typeExp ctx e in
        let t2 = typeTy te t in
        if t1 = t2 then t1 else raise TypingError     (***** *)
      ) *)
    | _ -> raise TypingError

and typeMrule ctx (Ast.M_RULE (pat, exp)) =
  let (te, ve) = ctx in
  let (t1, ve') = typePat ctx pat in
  let (s, t2) = typeExp (te, Dict.merge ve ve') exp in
  let (_, t1') = applySubstitution s tvset0 t1 in
  (s, Core.T_FUN (t1', t2))

and typeMlist ctx mlist =
  match mlist with
    [] -> raise TypingError
  | [mrule] -> typeMrule ctx mrule
  | head :: tail -> List.fold_left (fun (s_acc, t_acc) mrule -> 
      let (s, t) = typeMrule ctx mrule in
      let (_, t1) = (applySubstitution s tvset0 t_acc) in
      let (_, t2) = (applySubstitution s_acc tvset0 t) in
      let s' = unify [t1, t2] in
      let (_, t1') = applySubstitution s' tvset0 t1 in
      (s', t1')
    ) (typeMrule ctx head) tail

and typeDec ctx dec =
  let (te, ve) = ctx in
  match dec with
    Ast.D_VAL (pat, exp) -> (
      let (t1, ve') = typePat ctx pat in
      let _ = print_endline ("typeDec t1: "^(Core_print.ty2str t1)) in
      let _ = print_endline ("typeDec ve': "^(ctx2str (tenv0, ve'))) in
      let (s, t2) = typeExp ctx exp in
      let _ = print_endline ("typeDec t2: "^(Core_print.ty2str t2)) in
      let s' = unify [(t1, t2)] in
      let _ = print_endline "unify done" in
      let _ = print_endline ("typeDec closure: "^(ctx2str (tenv0, findClosure ve ve'))) in
      let _ = print_endline ("typeDec closure: "^(ctx2str (applySubstitutionCtx s' (tenv0, findClosure ve ve')))) in
      (tenv0, findClosure ve (applySubstitutionVE s' (applySubstitutionVE s ve')))
    )
  | Ast.D_REC (pat, exp) -> (
      let (t1, ve') = typePat ctx pat in
      let (s, t2) = typeExp (te, Dict.merge ve ve') exp in
      let s' = unify [(t1, t2)] in
      applySubstitutionCtx s' (applySubstitutionCtx s (tenv0, findClosure ve ve'))
    )
  (* | Ast.D_DTYPE (tycon, conlist) -> (
      let t = getFreshTyname in

    ) *)
  | _ -> raise TypingError *)

(* Convert functions *)

let rec convertPat ctx pat =
  let (te, ve) = ctx
  (* let (t', ve') = typePat ctx pat
  in let _  = print_endline ("convertPat t': " ^ Core_print.ty2str t') *)
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
            let _ = print_endline ("convertPat vid none - "^ vid ^"->"^ string_of_int a) in
            let tsch = (tvset0, Core.T_VAR a) in
            (Core.PATTY(Core.P_VID (vid, Core.VAR), Core.T_VAR a), Dict.insert (vid, (tsch, Core.VAR)) venv0)
          )
        | Some (tsch, Core.VAR) -> (
            let _ = print_endline ("typePat") in
            let (tvset, ty) = tsch in
            let _ = print_endline ("typePat ty: "^ Core_print.ty2str ty) in 
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
              let Core.PATTY(p'', t1') = p' in
              if t1 = t1'
              then (Core.PATTY(Core.P_VIDP ((vid, Core.CONF), p'), t2), ve')
              else raise TypingError     (***** *)
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
    (* | Ast.P_TPAT (p, ty) -> (
        let (p', _) = convertPat ctx p in
        (p', ve')
      ) *)
    | _ -> raise TypingError

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
            let _ = print_endline ("E_VID t: "^ Core_print.ty2str t) in
            (tySub0, Core.EXPTY(Core.E_VID (x, is), substitute tvset t))
          )
        (* | Some ((tvset, t), Core.CON) -> Core.EXPTY(Core.E_VID (x, Core.CON), t')
        | Some ((tvset, t), Core.CONF) -> Core.EXPTY(Core.E_VID (x, Core.CONF), t') *)
        | _ -> raise TypingError
      )
    | Ast.E_FUN mlist -> convertMlist ctx mlist
    | Ast.E_APP (e1, e2) -> (
        let (s1, e1') = convertExp ctx e1 in
        let Core.EXPTY (e1'', t1) = e1' in
        let _ = print_endline ("E_APP t1: "^(Core_print.ty2str t1)) in
        let ctx' = applySubstitutionCtx s1 ctx in
        let _ = print_endline ("E_APP ctx': "^ (ctx2str ctx')) in
        let (s2, e2') = convertExp ctx' e2 in
        let Core.EXPTY (e2'', t2) = e2' in
        let _ = print_endline ("E_APP t2: "^(Core_print.ty2str t2)) in
        let tv = Core.T_VAR (getFreshTyvar ()) in
        let (_, t1') = applySubstitution s2 tvset0 t1 in
        let _ = print_endline ("E_APP t1': "^(Core_print.ty2str t1')) in
        let s3 = unify [(t1', Core.T_FUN(t2, tv))] in
        let _ = print_endline ("E_APP s3: " ^ (s2str s3)) in
        let e1'' = applySubstitutionExpty s3 e1' in
        let e2'' = applySubstitutionExpty s3 e2' in
        let (_, tv') = applySubstitution s3 tvset0 tv in
        let _ = print_endline ("convertExp "^Ast_print.exp2str (Ast.E_APP (e1, e2)) ^" E_APP - "^ Core_print.ty2str tv') in
        (Dict.merge s3 (Dict.merge s2 s1), Core.EXPTY(Core.E_APP(e1'',e2''), tv'))
      )
    | Ast.E_PAIR (e1, e2) -> (
        let _ = print_endline ("E_PAIR: "^(Ast_print.exp2str (Ast.E_PAIR (e1, e2)))) in
        let (s1, e1') = convertExp ctx e1 in
        let Core.EXPTY (e1'', t1) = e1' in
        let _ = print_endline ("E_PAIR t1: "^(Core_print.ty2str t1)) in
        let (s2, e2') = convertExp ctx e2 in
        let Core.EXPTY (e2'', t2) = e2' in
        let _ = print_endline ("E_PAIR t1: "^(Core_print.ty2str t1)) in
        (* (Dict.merge s2 s1, Core.T_PAIR (t1, t2)) *)
        (Dict.merge s2 s1, Core.EXPTY(Core.E_APP (e1', e2'), Core.T_PAIR (t1, t2)))
      )
    | Ast.E_LET (d, e) -> (
        let (d', (te', ve')) = convertDec ctx d in
        let (s, e') = convertExp (Dict.merge te te', Dict.merge ve ve') e in
        let Core.EXPTY (_, ty) = e' in
        (s, Core.EXPTY(Core.E_LET (d', e'), ty))
      )
    (* | Ast.E_TEXP (e, t) -> (convertExp ctx e) *)
    | _ -> raise TypingError

and convertMrule ctx mrule =
  let (te, ve) = ctx in
  let Ast.M_RULE (pat, exp) = mrule in
  let (pat', ve') = convertPat ctx pat in
  let (s, exp') = convertExp (te, Dict.merge ve ve') exp in
  let Core.EXPTY (_, ty2) = exp' in
  let pat'' = applySubstitutionPatty s pat' in
  let Core.PATTY (_, ty1) = pat'' in
  let _ = print_endline ("convertMrule pat'': " ^ Core_print.patty2str pat'') in
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
        let (s_in, mlist_in, ty_in) = convertMrule ctx mrule in
        let mlist_acc' = (applySubstitutionMlist s_in mlist_acc) in
        let (_, ty1) = applySubstitution s_in tvset0 ty_acc in
        let mlist_in' = (applySubstitutionMlist s_acc mlist_in) in
        let (_, ty2) = applySubstitution s_acc tvset0 ty_in in
        let s' = unify [ty1, ty2] in
        let (_, ty_next) = applySubstitution s' tvset0 ty1 in
        let mlist_next = applySubstitutionMlist s' (mlist_acc' @ mlist_in') in
        (Dict.merge s' (Dict.merge s_in s_acc), mlist_next, ty_next)
      ) (convertMrule ctx head) tail
      in (s_mlist, Core.EXPTY(Core.E_FUN mlist', ty_mlist))
    )

and convertDec ctx dec =
  let (te, ve) = ctx in
  (* let ctx' = typeDec ctx dec in
  let _ = print_endline ("convertDec"^ ctx2str ctx') in *)
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
      let s' = unify [(t1, t2)] in
      let _ = print_endline ("convertDec D_REC s- "^ s2str s) in
      let _ = print_endline ("convertDec D_REC s'- "^ s2str s') in
      (* let _ = print_endline ("convertDec D_REC ve'_- "^ ctx2str (tenv0, (applySubstitutionVE s' (applySubstitutionVE s ve')))) in *)
      let ctx' = (tenv0, findClosure ve (applySubstitutionVE (Dict.merge s' s) ve')) in
      let _ = print_endline ("convertDec D_REC' - "^ ctx2str ctx') in
      let p' = applySubstitutionPatty s' p in
      let e' = applySubstitutionExpty s' e
      in
        (Core.D_REC (p', e'), ctx')

      (* let (p, ve') = convertPat ctx' pat in
      let e = convertExp ctx' exp in
      (Core.D_REC (p, e), ctx') *)
    )
  (* | Ast.D_DTYPE (tycon, conlist) -> (
      let t = getFreshTyname in

    ) *)
  | _ -> raise TypingError

(* tprogram : Ast.program -> Core.program *)
let tprogram (dlist, exp) =
  (* let (s, e)= convertExp (tenv0, venv0) exp in
  ([], e) *)
  let (dlist', ctx') = List.fold_left (fun (dlist_acc, ctx_acc) dec ->
    let _ = print_endline (Ast_print.dec2str dec) in
    let _ = print_endline ("tprogram acc "^ctx2str ctx_acc) in
    let (te_acc, ve_acc) = ctx_acc in
    let (dec_in, ctx_in) = convertDec ctx_acc dec in
    let (te_in, ve_in) = ctx_in in
    let _ = print_endline (Core_print.dec2str dec_in) in
    let _ = print_endline ("tprogram in "^ctx2str ctx_in) in
    (dlist_acc @ [dec_in], (Dict.merge te_acc te_in, Dict.merge ve_acc ve_in))
  ) ([], (tenv0, venv0)) dlist
  in let _ = print_endline ("**tprogram last ctx "^ctx2str ctx')
  in let (s, e)= convertExp ctx' exp
  in (dlist', e)
