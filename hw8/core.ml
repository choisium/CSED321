type is =       (* identifier status *)
    VAR         (* VAR : variable *)
  | CON         (* CON : constructor with no argument *)
  | CONF        (* CONF : constructor with an argument *)
      
type avid = Ast.vid  (* = Ast.vid variable or data constructor *)
type vid = avid * is (* variable or data constructor with status *)

type tyvar = int     (* type variable *)
type tyname = int    (* type name *)

type ty =              (* type *)
    T_INT              (* int *)
  | T_BOOL             (* bool *)
  | T_UNIT             (* unit *)
  | T_NAME of tyname   (* datatype *)
  | T_PAIR of ty * ty  (* type pair *)
  | T_FUN of ty * ty   (* function type *)
  | T_VAR of tyvar     (* type variable *)

type pat =                     (* pattern *)
    P_WILD                      (* wild card *)
  | P_INT of int                (* integer constant *)
  | P_BOOL of bool              (* boolean constant *)
  | P_UNIT                      (* unit *)
  | P_VID of vid                (* variable or constructor with CON *)
  | P_VIDP of vid * patty       (* constructor with CONF *)
  | P_PAIR of patty * patty     (* pattern pair *)
 and patty = PATTY of pat * ty  (* pattern with type annotation *)

type exp =                      (* expression *)
    E_INT of int                (* integer constant *)
  | E_BOOL of bool              (* boolean constant *)
  | E_UNIT                      (* unit *)
  | E_PLUS                      (* + for integers *)
  | E_MINUS                     (* - for integers *)
  | E_MULT                      (* * for integers *)
  | E_EQ                        (* = for integers *)
  | E_NEQ                       (* <> for integers *)
  | E_VID of vid                (* variable or constructor *)
  | E_FUN of mrule list         (* function *)
  | E_APP of expty * expty      (* funtion application *)
  | E_PAIR of expty * expty     (* expression pair *)
  | E_LET of dec * expty        (* let .. in .. end *)
 and expty = EXPTY of exp * ty (* expression with type annotation *)

 and mrule =                   (* pattern matching rule *)
   M_RULE of (patty * expty)

 and dec =                       (* declaration *)
   D_VAL of patty * expty        (* value binding *)
   | D_REC of patty * expty      (* recursive value binding *)
   | D_DTYPE                     (* datatype binding *)

type program = dec list * expty (* program with type annotation *)

