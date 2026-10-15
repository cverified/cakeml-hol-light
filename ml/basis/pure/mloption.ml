(* ======================================================== *)
(*  mloption: ported from HOL4's
    basis/pure/mloptionScript.sml  *)
(* ======================================================== *)

(*
  Pure functions for the Option module.
*)

needs "lib/ternaryComparisons.ml";;

let getOpt_def = cake_define
  `(getOpt (SOME v) a = v) /\
   (getOpt NONE a = a)`;;

let filter_def = cake_define
  `mloption_filter f a = (if f a then SOME (a) else NONE)`;;
hol4_overload "filter" "mloption_filter";;

let mapPartial_def = cake_define
  `mloption_mapPartial f opt = OPTION_BIND opt f`;;
hol4_overload "mapPartial" "mloption_mapPartial";;

let compose_def = cake_define
  `compose f g a = (match g a with
     (SOME v) -> SOME (f v) | NONE -> NONE)`;;

let composePartial_def = cake_define
  `composePartial f g a = (match g a with
     (SOME v) -> f v | NONE -> NONE)`;;

let compare_def = cake_define
  `mloption_compare f x y =
     (match x with NONE -> (match y with NONE -> EQUAL | _1 ->
       LESS) | SOME vx -> (match y with NONE -> GREATER | SOME vy ->
       f vx vy))`;;
hol4_overload "compare" "mloption_compare";;
