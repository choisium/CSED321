open Common

exception NotImplemented

exception IllegalFormat

module Integer : SCALAR with type t = int
=
struct
  type t = int

  exception ScalarIllegal

  let zero = 0
  let one = 1

  let (++) x y = x + y
  let ( ** ) x y = x * y
  let (==) x y = x = y 
end

(* Problem 1-1 *)
(* Scalars *)

module Boolean : SCALAR with type t = bool 
=
struct
  type t = bool

  exception ScalarIllegal

  let zero = false
  let one = true

  let (++) x y =
    match (x, y) with
      (false, false) -> false
    | _ -> true
  ;;
  let ( ** ) x y =
    match (x, y) with
      (true, true) -> true
    | _ -> false
  ;;
  let (==) x y = x = y
end

(* Problem 1-2 *)
(* Vectors *)

module VectorFn (Scal : SCALAR) : VECTOR with type elem = Scal.t
=
struct
  type elem = Scal.t
  type t = elem list

  exception VectorIllegal

  let create l = match l with
    [] -> raise VectorIllegal
  | _ -> l

  let to_list v = v

  let dim v = List.length v

  let nth v n =
    if (dim v <= n || n < 0) then raise VectorIllegal
    else List.nth v n
  ;;

  let (++) x y =
    if (dim x) <> (dim y) then raise VectorIllegal
    else List.map2 (fun e1 e2 -> Scal.(++) e1 e2) x y
  ;;

  let (==) x y =
    if (dim x) <> (dim y) then raise VectorIllegal
    else List.for_all2 (fun e1 e2 -> Scal.(==) e1 e2) x y
  ;;

  let innerp x y =
    if (dim x) <> (dim y) then raise VectorIllegal
    else List.fold_left2 (fun accum e1 e2 -> Scal.(++) accum (Scal.( ** ) e1 e2)) Scal.zero x y
  ;;
end

(* Problem 1-3 *)
(* Matrices *)

module MatrixFn (Scal : SCALAR) : MATRIX with type elem = Scal.t
=
struct
  type elem = Scal.t
  type t = (elem list) list

  exception MatrixIllegal

  let create l =
    match l with
      [] -> raise MatrixIllegal
    | _ -> if List.for_all (fun e -> (List.length e) = (List.length l)) l
           then l
           else raise MatrixIllegal
  ;;

  let identity n =
    let rec ith_row i j =
      match j with
        0 -> []
      | _ -> (if (j = n - i + 1) then Scal.one else Scal.zero) :: (ith_row i (j - 1))
    in
    let rec identity_aux i accum =
      match i with
        0 -> accum
      | _ -> identity_aux (i - 1) ((ith_row i n) :: accum)
    in
      if n <= 0 then raise MatrixIllegal
      else identity_aux n []
  ;;

  let dim m = List.length m

  let transpose m =
    let rec empty_matrix n =
      match n with
        0 -> []
      | _ -> [] :: empty_matrix (n - 1)
    in
    let transpose_aux m_sub accum =
      if (dim m_sub) <> (dim accum) then raise MatrixIllegal
      else List.fold_right2 (fun e1 e2 acc -> (e1 :: e2) :: acc) m_sub accum []
    in
      List.fold_right (fun m_sub accum -> transpose_aux m_sub accum) m (empty_matrix (dim m))
  ;;

  let to_list m = m

  let get m r c =
    if (r >= dim m || c >= dim m || r < 0 || c < 0) then raise MatrixIllegal
    else List.nth (List.nth m r) c
  ;;

  module Vector = VectorFn (Scal)

  let (++) x y =
    if (dim x <> dim y) then raise MatrixIllegal
    else List.map2 (fun e1 e2 -> Vector.to_list (Vector.(++) (Vector.create e1) (Vector.create e2))) x y
  ;;

  let rec ( ** ) x y =
    if (dim x <> dim y) then raise MatrixIllegal
    else
      List.map (fun x_sub ->
        List.map (fun y_sub -> Vector.innerp (Vector.create x_sub) (Vector.create y_sub)) (transpose y)
      ) x
  ;;

  let rec (==) x y =
    if (dim x) <> (dim y) then raise MatrixIllegal
    else List.for_all2 (fun r1 r2 -> List.equal (fun e1 e2 -> Scal.(==) e1 e2) r1 r2) x y
  ;;
end

(* Problem 2-1 *)
(* Closure *)

module ClosureFn (Mat : MATRIX) :
sig
  val closure : Mat.t -> Mat.t
end
=
struct
  let closure m =
    let i_m = Mat.identity (Mat.dim m)
    in
    let rec closure_aux current_c =
      let next_c = Mat.(++) i_m (Mat.( ** ) current_c m)
      in
        if Mat.(==) current_c next_c then current_c
        else closure_aux next_c
    in
      closure_aux m
end

(* Problem 2-2 *)
(* Applications to Graph Problems *)

module BoolMat = MatrixFn (Boolean)
module BoolMatClosure = ClosureFn (BoolMat)

let reach d =
  if List.for_all (fun e -> (List.length e) = (List.length d)) d
  then BoolMat.to_list(BoolMatClosure.closure (BoolMat.create d))
  else raise IllegalFormat
;;

let al = 
  [[true;  false; false; false; false; false];
   [false; true;  true;  true;  false; false];
   [false; true;  true;  false; true;  false];
   [false; true;  false; true;  true;  true];
   [false; false; true;  true;  true;  false];
   [false; false; false; true;  false; true]]

let solution_al' = 
  [[true;  false; false; false; false; false];
   [false; true;  true;  true;  true;  true];
   [false; true;  true;  true;  true;  true];
   [false; true;  true;  true;  true;  true];
   [false; true;  true;  true;  true;  true];
   [false; true;  true;  true;  true;  true]]

module Distance : SCALAR with type t = int
=
struct
  type t = int

  exception ScalarIllegal

  let zero = 999999              (* Dummy value : Rewrite it! *)
  let one = 999999               (* Dummy value : Rewrite it! *)

  let (++) _ _ = raise NotImplemented
  let ( ** ) _ _ = raise NotImplemented
  let (==) _ _ = raise NotImplemented
end

(* .. Write some code here .. *)

let distance _ = raise NotImplemented

let dl =
  [[  0;  -1;  -1;  -1;  -1;  -1 ];
   [ -1; 0  ; 35 ; 200; -1 ; -1  ];
   [ -1; 50 ; 0  ; -1 ; 150; -1  ];
   [ -1; 75;  -1 ; 0  ; 100; 25  ];
   [ -1; -1 ; 50 ; 65 ; 0  ; -1  ];
   [ -1; -1 ; -1 ; -1 ; -1 ; 0   ]]

let solution_dl' =
  [[0;  -1;  -1;  -1;  -1;  -1  ];
   [-1; 0;   35;  200; 185; 225 ];
   [-1; 50;  0;   215; 150; 240 ];
   [-1; 75;  110; 0;   100; 25  ];
   [-1; 100; 50;  65;  0;   90  ];
   [-1; -1;  -1;  -1;  -1;  0   ]]

module Weight : SCALAR with type t = int
=
struct
  type t = int

  exception ScalarIllegal

  let zero = 999999              (* Dummy value : Rewrite it! *)
  let one = 999999               (* Dummy value : Rewrite it! *)
 
  let (++) _ _ = raise NotImplemented
  let ( ** ) _ _ = raise NotImplemented
  let (==) _ _ = raise NotImplemented
end

(* .. Write some code here .. *)

let weight _ = raise NotImplemented

let ml =
  [[-1; 0  ; 0  ; 0  ; 0  ; 0   ];
   [0 ; -1 ; 10 ; 100; 0  ; 0   ];
   [0 ; 50 ; -1 ; 0  ; 150; 0   ];
   [0 ; 75 ; 0  ; -1 ; 125; 40 ];
   [0 ; 0  ; 25 ; -1 ; -1 ; 0   ];
   [0 ; 0  ; 0  ; 0  ; 0  ; -1  ]]

let solution_ml' =
  [[-1; 0;  0;   0;   0;   0  ];
   [0;  -1; 25;  100; 100; 40 ];
   [0;  75; -1;  150; 150; 40 ];
   [0;  75; 25;  -1;  125; 40 ];
   [0;  75; 25;  -1;  -1;  40 ];
   [0;  0;  0;   0;   0;   -1 ]]

let _ =
  try 
  if reach al = solution_al' && distance dl = solution_dl' && weight ml = solution_ml' then
    print_endline "\nYour program seems fine (but no guarantee)!"
  else
    print_endline "\nYour program might have bugs!"
  with _ -> print_endline "\nYour program is not complete yet!" 

