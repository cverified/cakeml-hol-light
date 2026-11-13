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

(* the theories whose names the Ancestors blocks of the source
   bring, which are the ones that its statements read: the
   overloads of every other theory come out of the interface
   while this file loads *)
let _ = hol4_ancestors "mloption" [];;

let getOpt_def = assume_definition
  "termination (CHEAT_TAC)"
  [`getOpt (SOME v) a = v`;
   `getOpt NONE a = a`];;

let filter_def = new_definition
  `mloption_filter f a = (if f a then SOME (a) else NONE)`;;
hol4_overload "filter" "mloption_filter";;

let mloption_mapPartial_def = new_definition
  `mloption_mapPartial f opt = OPTION_BIND opt f`;;
hol4_overload "mapPartial" "mloption_mapPartial";;

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
hol4_overload "compare" "mloption_compare";;

(* and the overloads that this file cannot see are back in the
   interface *)
let _ = unhide_overloads ();;
