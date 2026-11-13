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

(* the theories whose names the Ancestors blocks of the source
   bring, which are the ones that its statements read: the
   overloads of every other theory come out of the interface
   while this file loads *)
let _ = hol4_ancestors "lab_filter"
  ["labLang"];;

let not_skip_def = cake_define
  `not_skip l = (match l with labLang_Asm (Asmi (asm_Inst asm_Skip))
  _1 _2 -> F | _3 -> T)`;;

let filter_skip_def = cake_define_list
  [`filter_skip [] = []`;
   `filter_skip (Section n xs :: rest) =
         Section n (FILTER not_skip xs) :: filter_skip rest`];;

let filter_skip_MAP = prove
 (`!ls. filter_skip ls = MAP (\x. match x with Section n xs -> Section
  n (FILTER not_skip xs)) ls`,
  CHEAT_TAC);;

(* and the overloads that this file cannot see are back in the
   interface *)
let _ = unhide_overloads ();;
