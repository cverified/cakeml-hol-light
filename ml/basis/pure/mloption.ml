(* ======================================================== *)
(*  mloption: ported from HOL4's
    basis/pure/mloptionScript.sml
    A definition theory, with 6 definitions and no theorems.  Needed
    by presLang.ml.  *)
(* ======================================================== *)

(*
  Pure functions for the Option module.
*)

needs "lib/ternaryComparisons.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "mloption" [];;

let getOpt_def = assume_definition
  "termination (CHEAT_TAC)"
  [`getOpt (SOME v) a = v`;
   `getOpt NONE a = a`];;

let filter_def = new_definition
  `mloption_filter f a = (if f a then SOME (a) else NONE)`;;

let mloption_mapPartial_def = new_definition
  `mloption_mapPartial f opt = OPTION_BIND opt f`;;

let compose_def = new_definition
  `compose f g a = (match g a with
     (SOME v) -> SOME (f v) | NONE -> NONE)`;;

let composePartial_def = new_definition
  `composePartial f g a = (match g a with
     (SOME v) -> f v | NONE -> NONE)`;;

let mloption_compare_def = new_definition
  `mloption_compare f x y =
     (match x with NONE -> (match y with NONE -> EQUAL | _1 ->
       LESS) | SOME vx -> (match y with NONE -> GREATER | SOME vy ->
       f vx vy))`;;

(* and the interface *)
let _ = unhide_overloads ();;
