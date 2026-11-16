(* ======================================================== *)
(*  cv_type: ported from HOL4's
    src/num/theories/cv_compute/automation/cv_typeScript.sml
    A HOL4 library theory, of which the port has the definitions
    that CakeML needs.  Needed by cv_std.ml, fmap_cv.ml and
    unify_cv.ml.  *)
(* ======================================================== *)

needs "lib/rat.ml";;
needs "lib/sum.ml";;
needs "lib/term.ml";;

(* of no theory of the port: what it registers is in the scope of every file *)
let _ = cake_library ();;
(* HOL4 ancestors outside the port: cv one option list pair words integer *)

(* HOL4 cv_typeScript.sml:9: the overload c2n, which the port expands *)
(* HOL4 cv_typeScript.sml:10: the overload c2b, which the port expands *)
(* HOL4 cv_typeScript.sml:11: the overload Num, which the port expands *)
(* HOL4 cv_typeScript.sml:12: the overload Pair, which the port expands *)

let from_to_def = new_definition
  `from_to (f:'a->cv) (t:cv->'a) = (!x. t (f x) = x)`;;

let from_char_def = new_definition
  `from_char (c:char) = Num (ORD c)`;;

let to_char_def = new_definition
  `to_char x = CHR (c2n x)`;;

let from_option_def = define_cases
  `(from_option f NONE = Num (&0)) /\
   (from_option f (SOME x) = Pair (Num (&1)) (f x))`;;

let from_pair_def = new_definition
  `from_pair f1 f2 (x,y) = Pair (f1 x) (f2 y)`;;

let to_pair_def = new_definition
  `to_pair t1 t2 x3 =
   match x3 with
     Pair x y -> (t1 x,t2 y)
   | _ -> ARB`;;

let from_list_def,from_list_ind = define_guess
  `(from_list f [] = Num (&0)) /\
   (from_list f (CONS x xs) = Pair (f x) (from_list f xs))`;;

let to_list_def,to_list_ind = define_guess
  `(to_list f (Num n) = []) /\
   (to_list f (Pair x y) = CONS (f x) (to_list f y))`;;
