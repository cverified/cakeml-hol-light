(* ======================================================== *)
(*  mlrat: ported from HOL4's
    basis/pure/mlratScript.sml
    A definition theory, with 6 definitions, 1 datatype and 21
    theorems.  Needed by RatProg.ml.  *)
(* ======================================================== *)

(*
  Pure functions for the Rat module.
*)

needs "basis/pure/mlint.ml";;
needs "basis/pure/mlstring.ml";;
needs "lib/rat.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "mlrat"
  ["mlint"; "mlstring"];;

let _ = do_list hide_constant ["ABS"; "Num"];;
(* HOL4 ancestors outside the port: gcd *)

(* representation type *)

let rational_INDUCT,rational_RECURSION = define_datatype
  "rational =
     RatPair int num";;

let rational_of_num_def = new_definition
  `rational_of_num (n:num) = RatPair (&n) 1`;;

let rational_of_int_def = new_definition
  `rational_of_int (n:int) = RatPair n 1`;;

(* connection between real and rat *)

let real_of_rat_def = new_definition
  `(real_of_rat (r:rat):real) =
     real_of_int (RATN r) / real_of_num (RATD r)`;;

let real_of_rat_int = prove
 (`real_of_rat (&x) = &x`,
  CHEAT_TAC);;

let real_of_rat_le = prove
 (`!r1 r2. real_of_rat r1 <= real_of_rat r2 <=> r1 <= r2`,
  CHEAT_TAC);;
add_simp real_of_rat_le;;

let real_of_rat_eq = prove
 (`!r1 r2. real_of_rat r1 = real_of_rat r2 <=> r1 = r2`,
  CHEAT_TAC);;
add_simp real_of_rat_eq;;

let real_of_rat_lt = prove
 (`!r1 r2. real_of_rat r1 < real_of_rat r2 <=> r1 < r2`,
  CHEAT_TAC);;

let real_of_rat_add = prove
 (`!r1 r2. real_of_rat (r1 + r2) = real_of_rat r1 + real_of_rat r2`,
  CHEAT_TAC);;

let real_of_rat_mul = prove
 (`!r1 r2. real_of_rat (r1 * r2) = real_of_rat r1 * real_of_rat r2`,
  CHEAT_TAC);;

let real_of_rat_ainv = prove
 (`!r. real_of_rat (--r) = --(real_of_rat r)`,
  CHEAT_TAC);;

let real_of_rat_sub = prove
 (`!r1 r2. real_of_rat (r1 - r2) = real_of_rat r1 - real_of_rat r2`,
  CHEAT_TAC);;

(* [local] *)
let inv_div = prove
 (`~(x = (&0:real)) /\ ~(y = 0) ==> (inv (x / y) = y / x)`,
  CHEAT_TAC);;

let real_of_int_eq_num = prove
 (`((real_of_int i = &n) <=> (i = &n)) /\
   ((&n = real_of_int i) <=> (i = &n))`,
  CHEAT_TAC);;
add_simp real_of_int_eq_num;;

let rat_of_int_eq_num = prove
 (`((rat_of_int i = &n) <=> (i = &n)) /\
   ((&n = rat_of_int i) <=> (i = &n))`,
  CHEAT_TAC);;
add_simp rat_of_int_eq_num;;

let real_of_rat_inv = prove
 (`!r. ~(r = 0) ==> real_of_rat (rat_minv r) = inv (real_of_rat r)`,
  CHEAT_TAC);;

let real_of_rat_div = prove
 (`~(x = 0) ==> real_of_rat (x' / x) = real_of_rat x' / real_of_rat x`,
  CHEAT_TAC);;

let real_of_int_of_rat = prove
 (`real_of_int i = real_of_rat (rat_of_int i)`,
  CHEAT_TAC);;

let rat_of_int_eq = prove
 (`hol4_gcd (num_of_int (abs n1)) d1 = 1 /\ ~(d1 = 0) /\
   hol4_gcd (num_of_int (abs n2)) d2 = 1 /\ ~(d2 = 0) /\
   rat_of_int n1 / &d1 = rat_of_int n2 / &d2 ==>
   n1 = n2 /\ d1 = d2`,
  CHEAT_TAC);;

let mlrat_toString_def = new_definition
  `mlrat_toString (RatPair i n) =
     if n = 1 then mlint_toString i else mlstring_concat [mlint_toString
       i; implode "/"; mlint_toString (&n)]`;;

let real_to_rational_def = new_definition
  `real_to_rational (r:real) =
     let (n,d) = (@x. ?n d. x = (n,d) /\
                            r = real_of_int n / &d /\
                            hol4_gcd (num_of_int (abs n)) d = 1 /\ ~(d = 0))
                              in
       RatPair n d`;;

let real_to_str_def = new_definition
  `real_to_str r = mlrat_toString (real_to_rational r)`;;

let real_of_int_div_eq = prove
 (`!n d n' d'.
     hol4_gcd (num_of_int (abs n')) d' = 1 /\ ~(d' = 0) /\
     hol4_gcd (num_of_int (abs n)) d = 1 /\ ~(d = 0) ==>
     (real_of_int n / &d = real_of_int n' / &d' <=> n = n' /\ d = d')`,
  CHEAT_TAC);;

(* [compute] *)
let real_to_str_num = prove
 (`real_to_str (&n) = mlrat_toString (RatPair (&n) 1)`,
  CHEAT_TAC);;

(* [compute] *)
let real_to_str_neg_num = prove
 (`real_to_str (--(&n)) = mlrat_toString (RatPair (--(&n)) 1)`,
  CHEAT_TAC);;

(* [compute] *)
let real_to_str_rat = prove
 (`real_to_str (&n / &d) =
   mlrat_toString (if d = 0 then real_to_rational (&n / &d)
             else let k = hol4_gcd n d in RatPair (&(n DIV k)) (d DIV k))`,
  CHEAT_TAC);;

(* [compute] *)
let real_to_str_neg_rat = prove
 (`real_to_str (--(&n) / &d) =
   mlrat_toString (if d = 0 then real_to_rational (--(&n) / &d)
             else let k = hol4_gcd n d in RatPair (--(&(n DIV k))) (d DIV
               k))`,
  CHEAT_TAC);;

let INT_FLOOR_real_of_int = prove
 (`INT_FLOOR (real_of_int i) = i`,
  CHEAT_TAC);;

(* and the names it reads as variables are constants again *)
let _ = do_list unhide_constant
  ["ABS";
   "Num"];;

(* and the interface *)
let _ = unhide_overloads ();;
