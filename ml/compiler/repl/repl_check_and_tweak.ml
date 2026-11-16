(* ======================================================== *)
(*  repl_check_and_tweak: ported from HOL4's
    compiler/repl/repl_check_and_tweakScript.sml
    A definition theory, with 2 definitions and 1 theorem.  Needed
    by replProof.ml, repl_init_types.ml and repl_types.ml.  *)
(* ======================================================== *)

(*
  The REPL type checks and modifies the decs given as input. This file
  defines the function that implements this and proves that the
  function will only produce type checked and allowed declarations.
*)

needs "basis/pure/mlstring.ml";;
needs "compiler/compiler.ml";;
needs "compiler/inference/infer.ml";;
needs "compiler/printing/printTweaks.ml";;
needs "compiler/repl/repl_decs_allowed.ml";;
needs "semantics/ast.ml";;
needs "semantics/evaluate.ml";;
needs "semantics/proofs/semanticsProps.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "translator/monadic/monad_base/ml_monadBase.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "repl_check_and_tweak"
  ["compiler"; "evaluate"; "infer"; "printTweaks"; "repl_decs_allowed";
   "semanticPrimitives"; "semanticsProps"];;

let _ = do_list hide_constant ["types"];;

let check_and_tweak_def = new_definition
  `check_and_tweak (decs,types',input_str) =
     match add_print_then_read types' decs with M_success
       (new_decs,new_types) ->
         if decs_allowed new_decs then INR (new_decs,new_types)
         else INL (implode (APPEND
           "ERROR: input contains reserved constructor/FFI nam" "es"))
     | M_failure (loc,msg) ->
         INL (mlstring_concat [(implode "ERROR: "); msg; (implode " at ");
                      locs_to_string input_str loc])`;;

(* main correctness result *)

let check_and_tweak = prove
 (`// used in replProof
   check_and_tweak (decs,types,input_str) = INR (safe_decs,new_types) ==>
   infertype_prog_inc (SND types) safe_decs = M_success (SND new_types) /\
   decs_allowed safe_decs`,
  CHEAT_TAC);;

(* used in repl-function in compiler64Prog *)

let roll_back_def = new_definition
  `repl_check_and_tweak_roll_back
  (((old_tn:addPrintVals_type_names),(old_ienv:inf_env),(old_next_id:num)),
  (new_tn:addPrintVals_type_names),(new_ienv:inf_env),(new_next_id:num)) =
     (old_tn,old_ienv,new_next_id)`;;

(* and the names it reads as variables are constants again *)
let _ = do_list unhide_constant
  ["types"];;

(* and the interface *)
let _ = unhide_overloads ();;
