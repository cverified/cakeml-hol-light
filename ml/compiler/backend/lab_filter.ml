(* ======================================================== *)
(*  lab_filter: ported from HOL4's
    compiler/backend/lab_filterScript.sml
    A definition theory, with 2 definitions and 1 theorem.  Needed
    by backend_passes.ml, lab_filterProof.ml, lab_to_target.ml and
    lab_to_targetProof.ml.  *)
(* ======================================================== *)

(*
  This compiler phase removes all Skip instructions (generated from
  Tick in stackLang).
*)

needs "compiler/backend/labLang.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "lab_filter"
  ["labLang"];;

let not_skip_def = new_definition
  `not_skip l = (match l with labLang_Asm (Asmi (asm_Inst asm_Skip))
  _1 _2 -> F | _3 -> T)`;;

let _ = size_thms "sec";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let filter_skip_def,filter_skip_ind = define_wf
  `MEASURE (\x0. list_size (sec_size (\x. 0)) x0)`
  [`filter_skip [] = []`;
   `filter_skip (CONS (Section n xs) rest) = CONS (Section n
    (FILTER not_skip xs)) (filter_skip rest)`];;

let filter_skip_MAP = prove
 (`!ls. filter_skip ls = MAP (\x. match x with Section n xs -> Section
  n (FILTER not_skip xs)) ls`,
  CHEAT_TAC);;
