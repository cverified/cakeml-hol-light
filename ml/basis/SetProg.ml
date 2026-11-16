(* ======================================================== *)
(*  SetProg: ported from HOL4's
    basis/SetProgScript.sml
    A definition theory, with no definitions and 3 theorems.  Needed
    by HashtableProg.ml.  *)
(* ======================================================== *)

(*
  This module contains CakeML code implementing a functional set type
  using a self-balancing binary tree.
*)

needs "basis/MapProg.ml";;
needs "basis/pure/mlset.ml";;
needs "lib/balanced_map.ml";;
needs "translator/ml_translator.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "SetProg"
  ["MapProg"; "ml_prog"; "ml_translator"; "mlset"];;

(* HOL4 SetProgScript.sml:11: ML code, not ported *)

(* HOL4 SetProgScript.sml:13: ML code, not ported *)

(* HOL4 SetProgScript.sml:15-17: ML code, not ported *)

(* HOL4 SetProgScript.sml:19-21: ML code, not ported *)

(* Helpers *)

(* HOL4 SetProgScript.sml:25-30: ML code, not ported *)

(* deleteFindmax_side_thm[local] *)
let SetProg_deleteFindmax_side_thm = prove
 (`!m. ~(m = Tip) ==> deletefindmax_side m`,
  CHEAT_TAC);;
(* HOL4 SetProgScript.sml:42: ML code, not ported *)

(* HOL4 SetProgScript.sml:44: ML code, not ported *)

(* deleteFindmin_side_thm[local] *)
let SetProg_deleteFindmin_side_thm = prove
 (`!m. ~(m = Tip) ==> deletefindmin_side m`,
  CHEAT_TAC);;
(* HOL4 SetProgScript.sml:56: ML code, not ported *)

(* HOL4 SetProgScript.sml:58: ML code, not ported *)

(* glue_side_thm[local] *)
let SetProg_glue_side_thm = prove
 (`!m n. glue_side m n`,
  CHEAT_TAC);;
(* HOL4 SetProgScript.sml:67: ML code, not ported *)

(* HOL4 SetProgScript.sml:69-88: ML code, not ported *)

(* Exported functions *)
(* HOL4 SetProgScript.sml:91-109: ML code, not ported *)

(* HOL4 SetProgScript.sml:111: ML code, not ported *)

(* HOL4 SetProgScript.sml:113: ML code, not ported *)

(* provides the Set.set name for the set type *)
(* HOL4 SetProgScript.sml:116-117: ML code, not ported *)

(* HOL4 SetProgScript.sml:119-154: ML code, not ported *)

(* HOL4 SetProgScript.sml:156: ML code, not ported *)

(* HOL4 SetProgScript.sml:158-159: ML code, not ported *)

(* HOL4 SetProgScript.sml:161: ML code, not ported *)

(* Remove all overloads introduced by loading mlset: *)

(* and the interface *)
let _ = unhide_overloads ();;
