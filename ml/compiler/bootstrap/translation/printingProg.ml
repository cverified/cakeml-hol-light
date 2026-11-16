(* ======================================================== *)
(*  printingProg: ported from HOL4's
    compiler/bootstrap/translation/printingProgScript.sml
    A definition theory, with no definitions and 3 theorems.  Needed
    by to_word64Prog.ml.  *)
(* ======================================================== *)

(*
  Translate the pretty printing functions for the REPL
*)

needs "compiler/bootstrap/translation/basis_defProg.ml";;
needs "compiler/inference/infer.ml";;
needs "compiler/printing/printTweaks.ml";;
needs "misc/misc.ml";;
needs "translator/ml_translator.ml";;
needs "translator/std_prelude.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "printingProg"
  ["basis_defProg"; "infer"; "misc"; "ml_translator"; "printTweaks";
   "std_prelude"];;

(* HOL4 printingProgScript.sml:11-12: ML code, not ported *)

(* HOL4 printingProgScript.sml:14-15: ML code, not ported *)

(* HOL4 printingProgScript.sml:17: ML code, not ported *)

(* HOL4 printingProgScript.sml:19: ML code, not ported *)

(* HOL4 printingProgScript.sml:21: ML code, not ported *)

(* NOT_NIL_AND_LEMMA[local] *)
let printingProg_NOT_NIL_AND_LEMMA = prove
 (`(~(b = []) /\ x) = if b = [] then F else x`,
  CHEAT_TAC);;

(* HOL4 printingProgScript.sml:29: ML code, not ported *)

(* HOL4 printingProgScript.sml:31: ML code, not ported *)

(* HOL4 printingProgScript.sml:33-44: ML code, not ported *)

(* HOL4 printingProgScript.sml:46-47: ML code, not ported *)
                (* TODO: This ss messes up defs containing if-then-else
                with constant branches
                |> SIMP_RULE bool_ss [IN_INSERT,NOT_IN_EMPTY]*)
(* HOL4 printingProgScript.sml:51-52: ML code, not ported *)

(* HOL4 printingProgScript.sml:54: ML code, not ported *)

(* HOL4 printingProgScript.sml:56: ML code, not ported *)

(* HOL4 printingProgScript.sml:58-59: ML code, not ported *)

(* [local] *)
let OPT_MAP_I = prove
 (`!g ls. OPT_MMAP I (MAP g ls) = OPT_MMAP g ls`,
  CHEAT_TAC);;

(* HOL4 printingProgScript.sml:67-69: ML code, not ported *)

(* HOL4 printingProgScript.sml:71: ML code, not ported *)

(* HOL4 printingProgScript.sml:73: ML code, not ported *)

(* HOL4 printingProgScript.sml:75-77: ML code, not ported *)

(* handle many preconditions to do with inference st invariants t_wfs *)

(* HOL4 printingProgScript.sml:81-83: a theorem that HOL4 states as the
   value of an ML expression: t_wfs_inv *)

(* HOL4 printingProgScript.sml:85-89: a theorem that HOL4 states as the
   value of an ML expression: lemma1 *)

(* HOL4 printingProgScript.sml:91-100: a theorem that HOL4 states as the
   value of an ML expression: lemma2 *)

(* HOL4 printingProgScript.sml:102-114: a theorem that HOL4 states as the
   value of an ML expression: lemma3 *)

(* HOL4 printingProgScript.sml:116-122: a theorem that HOL4 states as the
   value of an ML expression: lemma4 *)

(* HOL4 printingProgScript.sml:124: ML code, not ported *)

(* HOL4 printingProgScript.sml:126-131: a theorem that HOL4 states as the
   value of an ML expression: lemma5 *)
(* HOL4 printingProgScript.sml:126-131: the ML values that the definitions
   below antiquote *)


(* HOL4 printingProgScript.sml:135: ML code, not ported *)

(* HOL4 printingProgScript.sml:137: ML code, not ported *)

(* and the interface *)
let _ = unhide_overloads ();;
