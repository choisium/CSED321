module V = VectorFn (Integer)
module I = MatrixFn (Integer)
module C = ClosureFn(I)
exception MatrixIllegal = I.MatrixIllegal
exception VectorIllegal = V.VectorIllegal
let lm0 = [[1]]
let lm1 = [[1;2;3];[4;5;6];[7;8;9]]
let lm1t = [[1;4;7];[2;5;8];[3;6;9]]
let lm2 = [[1;4;7];[0;5;8];[8;6;9]]
let lm3 = [[2;6;10]; [4;10;14]; [15;14;18]]
let lm4 = [[0;1;1];[0;0;1];[0;0;0]]
let lm5 = [[1;1;2]; [0;1;1]; [0;0;1]]
let m0 = I.create lm0
let m1 = I.create lm1
let m2 = I.create lm2
let m3 = I.create lm3

let m4 = I.create lm4
let m5 = I.create lm5

let lv1 = [1]
let lv2 = [2;4]
let lv3 = [1;4]
let lv4 = [3;8]
let v1 = V.create lv1
let v2 = V.create lv2
let v3 = V.create lv3
let v4 = V.create lv4


let rfalse _ = false
(* vector *)
(* create test *)

let test9 = try rfalse(V.create[]) with VectorIllegal -> true
| _ -> false
let test9 = test9 && ((V.nth v1 0) = 1)

let test10 = try rfalse(V.nth v1 (-1)) with VectorIllegal -> true
| _ -> false
let test10 = test10 && try rfalse (V.nth v1 1) with VectorIllegal -> true
| _ -> false
let test10 = test10 && (V.nth v1 0) = 1

(* ++ *)
let test11 = try rfalse (V.(++) v1 v2) with VectorIllegal -> true
| _ -> false
let tmp = V.(++) v2 v3
let test11 = test11 && ((V.nth tmp 0) = 3)
let test11 = test11 && ((V.nth tmp 1) = 8)
(* innerp *)


let test12 = try rfalse(V.innerp v1 v2) with VectorIllegal -> true
| _ -> false
let test12 = test12 && ((V.innerp v3 v2) = 18)
let test12 = test12 && ((V.innerp v2 v3) = 18)
(* == *)
let test13 = try rfalse(V.(==) v1 v2) with VectorIllegal -> true
| _ -> false
let test13 = try test13 && rfalse(V.(==) v1 v3) with VectorIllegal -> true
| _ -> false
let test13 = test13 && (if V.(==) v2 v3 then false else true)
let test13 = test13 && (V.(==) (V.(++) v2 v3) v4)

(* Matrix *)
(* create test *)
let test6 = try rfalse(I.create [[]]) with MatrixIllegal -> true
| _ -> false
let test6' = try rfalse(I.create [[1];[2]]) with MatrixIllegal -> true
| _ -> false
let test6'' = try rfalse(I.create [[1;2;3];[1;2];[1;2;3]]) with MatrixIllegal
->
true
| _ -> false
let test6 = test6 && test6' && test6''
let tmp = I.create lm1
let test6 = test6 && ( (I.get tmp 0 0) = 1)
let test6 = test6 && ( (I.get tmp 0 1) = 2)
let test6 = test6 && (( I.get tmp 0 2) = 3 )
let test6 = test6 && ((I.get tmp 1 0) = 4 )
let test6 = test6 && ( (I.get tmp 1 1) = 5 )
let test6 = test6 && ((I.get tmp 1 2) = 6 )
let test6 = test6 && ((I.get tmp 2 0) = 7 )
let test6 = test6 && ((I.get tmp 2 1) = 8 )
let test6 = test6 && (( I.get tmp 2 2) = 9 )
(* identify *)
(* dim *)
(* get *)

(* get *)
let test7 = try rfalse(I.get m1 (-1) 0) with MatrixIllegal -> true
| _ -> false
let test7' = try rfalse(I.get m1 0 (-1)) with MatrixIllegal -> true
| _ -> false
let test7'' = try rfalse(I.get m1 3 0) with MatrixIllegal -> true
| _ -> false
let test7''' = try rfalse(I.get m1 0 3) with MatrixIllegal -> true
| _ -> false
let test7'''' = try I.get m1 2 1 = 8 with MatrixIllegal -> true
| _ -> false
let test7 = test7 && test7' && test7'' && test7''' && test7''''

(* transpose test *)
let m = I.create lm1
let mt = I.create lm1t
let test1 = (I.(==) (I.transpose m) mt)

(* toList test *)
let m = I.create lm1
let test2 = (I.to_list m = lm1)
let m = I.create lm0
let test2 = test2 && (I.to_list m = lm0)
(* ++ test *)
let test3 = try rfalse (I.(++) m0 m1) with MatrixIllegal -> true
| _ -> false

let plus = I.(++) m1 m2
let test3 = test3 && ((I.get plus 0 0) = 2)
let test3 = test3 && ((I.get plus 0 1) = 6)
let test3 = test3 && ((I.get plus 0 2) = 10)
let test3 = test3 && ((I.get plus 1 0) = 4 )
let test3 = test3 && ((I.get plus 1 1) = 10)

let test3 = test3 && ((I.get plus 1 2) = 14)
let test3 = test3 && ((I.get plus 2 0) = 15)
let test3 = test3 && ((I.get plus 2 1) = 14)
let test3 = test3 && ((I.get plus 2 2) = 18)
(* ** test *)
let test4 = try rfalse (I.( ** ) m0 m1) with MatrixIllegal -> true
| _ -> false
let plus = I.( ** ) m1 m2
let test4 = test4 && ((I.get plus 0 0) = 25 )
let test4 = test4 && ((I.get plus 0 1) = 32 )
let test4 = test4 && ((I.get plus 0 2) = 50 )
let test4 = test4 && ((I.get plus 1 0) = 52 )
let test4 = test4 && ((I.get plus 1 1) = 77 )
let test4 = test4 && ((I.get plus 1 2) = 122 )
let test4 = test4 && ((I.get plus 2 0) = 79 )
let test4 = test4 && ((I.get plus 2 1) = 122)
let test4 = test4 && ((I.get plus 2 2) = 194)

(* == test *)
let test5 = try rfalse (I.(==) m0 m1) with MatrixIllegal -> true
| _ -> false
let test5 = test5 && (I.(==) (I.(++) m1 m2) m3)
(* closure test *)
let test8 = I.(==) (C.closure m4) m5

let d1 = [[0; 15; 10; -1; -1]; [5; 0; -1; 20; -1]; [20; -1; 0; 2; -1]; [-1;
10; 15; 0; -1]; [-1; -1; -1; -1; 0]]

let d2 = [[0; -1; 10; -1; -1; 5]; [-1; 0; -1; -1; 3; 10]; [15; -1; 0; -1; -1;
-1]; [-1; -1; -1; 0; 2; 3]; [-1; 8; -1; 9; 0; -1]; [20; 9; -1; 7; -1; 0]]

let d3 = [[0; -1; 1; -1]; [-1; 0; -1; -1]; [7; -1; 0; 5]; [-1; -1; 4; 0]]

let d4 = [[0; 7; 8; 3; -1]; [9; 0; -1; -1; 9]; [6; -1; 0; 5; -1]; [2; -1; 4;
0; 6]; [-1; 3; -1; 1; 0]]

let d5 = [[0; 15; 10; -1; -1]; [4; 0; -1; 3; 7]]

let d6 = [[]]

let sold1 = [[0; 15; 10; 12; -1]; [5; 0; 15; 17; -1]; [17; 12; 0; 2; -1];
[15; 10; 15; 0; -1]; [-1; -1;-1; -1; 0]]

let sold2 = [[0; 14; 10; 12; 14; 5]; [30; 0; 40; 12; 3; 10]; [15; 29; 0; 27;
29; 20]; [23; 10; 33; 0; 2; 3]; [32; 8; 42; 9; 0; 12]; [20; 9; 30; 7; 9; 0]]

let sold3 = [[0; -1; 1; 6]; [-1; 0; -1; -1]; [7; -1; 0; 5]; [11; -1; 4; 0]]

let sold4 = [[0; 7; 7; 3; 9]; [9; 0; 14; 10; 9]; [6; 13; 0; 5; 11]; [2; 9; 4;
0; 6]; [3; 3; 5; 1; 0]]

let sold5 = [[]]

let sold6 = [[]]


let r1 = [[true; true; true; false; false]; [true; true; false; true; false];
[true; false; true; true; false]; [false; true; true; true; false]; [false;
false; false; false; true]]

let r2 = [[true; true; true; false]; [true; true; false; true]; [true; false;
true; false]; [false; true; false; true]]

let r3 = [[true; true; true; true; false]; [true; true; true; false; false];
[true; true; true; false; true]; [true; false; false; true; true]; [false;
false; true; true; true]]

let r4 = [[true; true; false; false; true]; [true; true; false; false; true];
[false; false; true; false; false]; [false; false; false; true; true]; [true;
true; false; true; true]]

let r5 = [[true; true; false; false]; [false; true; true; false]]

let r6 = [[]]




let solr1 = [[true; true; true; true; false]; [true; true; true; true;
false]; [true; true; true; true; false]; [true; true; true; true; false];
[false; false; false; false; true]]

let solr2 = [[true; true; true; true]; [true; true; true; true]; [true; true;
true; true]; [true; true; true; true]]

let solr3 = [[true; true; true; true; true]; [true; true; true; true; true];
[true; true; true; true; true]; [true; true; true; true; true]; [true; true;
true; true; true]]

let solr4 = [[true; true; false; true; true]; [true; true; false; true;
true]; [false; false; true; false; false]; [true; true; false; true; true];
[true; true; false; true; true]]

let solr5 = [[]]
let solr6 = [[]]


let w1 = [[-1; 10; -1; 0]; [20; -1; 0; 12]; [15; 0; -1; 0]; [0; 21; 0; -1]]

let w2 = [[-1; -1; -1; 18; 0]; [15; -1; 16; 0; 0]; [20; 25; -1; 0; 17]; [21;
0; 0; -1; -1]; [0; 0; 20; 25; -1]]

let w3 = [[-1; 17; 0; -1; 0; 0]; [25; -1; 0; 0; 0; 18]; [0; 0; -1; 0; 28;
-1]; [30; 0; 0; -1; 17; 0]; [0; 0; 20; 25; -1; 0]; [0; 21; 19; 0; 0; -1]]

let w4 = [[-1; -1; 3]; [1; -1; 3]; [2; 3]]

let w5 = [[]]


let solw1 = [[-1; 10; -1; 10]; [20; -1; 20; 12]; [15; 10; -1; 10]; [20; 21;
20; -1]]

let solw2 = [[-1; -1; -1; 18; 18]; [16; -1; 16; 16; 16]; [20; 25; -1; 18;
18]; [21; 21; 21; -1; -1]; [21; 21; 21; 25; -1]]

let solw3 = [[-1; 17; 17; -1; 17; 17]; [25; -1; 18; 25; 18; 18]; [25; 21; -1;
25; 28; -1]; [30; 17; 17; -1; 17; 17]; [25; 20; 20; 25; -1; 20]; [21; 21; 19;
21; 19; -1]]

let solw4 = [[]]

let solw5 = [[]]


(* print of matrix and vecror result *)
let _ = if test7 then print_endline "matrix get OK\n" else print_endline
"matrix get fail\n"
let _ = if test6 then print_endline "matrix create OK\n" else print_endline
"matrix create fail\n"
let _ = if test1 then print_endline "matrix transpose OK\n" else
print_endline "matrix transpose fail\n"
let _ = if test2 then print_endline "matrix toList OK\n" else print_endline
"matrix toList fail"
let _ = if test3 then print_endline "matrix ++ OK\n" else print_endline
"matrix ++ fail\n"
let _ = if test4 then print_endline "matrix ** OK\n" else print_endline
"matrix ** fail\n"
let _ = if test5 then print_endline "matrix == OK\n" else print_endline
"matrix == fail\n"
let _ = if test8 then print_endline "matrix closure OK\n" else print_endline
"matrix closure fail\n"
let _ = if test9 then print_endline "vector create OK\n" else print_endline
"vector create fail\n"
let _ = if test10 then print_endline "vector nth OK\n" else print_endline
"vector nth fail\n"
let _ = if test11 then print_endline "vector ++ OK\n" else print_endline
"vector nth fail\n"

let _ = if test12 then print_endline "vector innerpOK\n" else print_endline
"vector innerp fail\n"
let _ = if test13 then print_endline "vector == OK\n" else print_endline
"vector == fail\n"
let _ = if test1 && test2 && test3 && test4 &&
test5 && test6 && test7 && test8 &&
test9 && test10 && test11 && test12 &&
test13
then print_endline "\n********** All tests Passed! **********\n\n"
else print_endline "\n********** Fail **********\n\n"


let _ = print_endline "\n************distance Test***************\n\n"

let test1 = try (distance d1 = sold1) with _ -> false
let test2 = try (distance d2 = sold2) with _ -> false
let test3 = try (distance d3 = sold3) with _ -> false
let test4 = try (distance d4 = sold4) with _ -> false
let test5 = try (distance d5 = sold5) with IllegalFormat -> true | _ -> false
let test6 = try (distance d6 = sold6) with IllegalFormat -> true | _ -> false

let _ = if (test1 && test2 && test3 && test4 && test5 && test6)
then print_endline "\nSuccess all the distance Example!!\n"
else print_endline "\nFail on some tests\n"


let _ = print_endline "\n************reach Test***************\n\n"

let test7 = try (reach r1 = solr1) with _ -> false
let test8 = try (reach r2 = solr2) with _ -> false
let test9 = try (reach r3 = solr3) with _ -> false
let test10 = try (reach r4 = solr4) with _ -> false
let test11 = try (reach r5 = solr5) with IllegalFormat -> true | _ -> false
let test12 = try (reach r6 = solr6) with IllegalFormat -> true | _ -> false

let _ = if test7 && test8 && test9 && test10 && test11 &&
test12
then print_endline "\nSuccess all the reach Example!!\n"
else print_endline "\nFail on some tests\n"

let _ = print_endline "\n************weight Test****************\n\n"

let test13 = try (weight w1 = solw1) with _ -> false
let test14 = try(weight w2 = solw2) with _ -> false
let test15 = try(weight w3 = solw3) with _ -> false
let test16 = try(weight w4 = solw4) with IllegalFormat -> true | _ -> false
let test17 = try(weight w5 = solw5) with IllegalFormat -> true | _ -> false

let _ = if test13 && test14 && test15 && test16 && test17
then print_endline "\nSuccess all the weight Example!!\n"
else print_endline "\nFail on some tests\n"


let _ = print_endline "\nRefer to PL2013 30, Thanks to hesedjds\n\n"
let _ = print_endline "\nRefer to PL2012 98, Thanks to jh2ekd\n\n"