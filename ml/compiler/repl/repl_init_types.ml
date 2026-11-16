(* ======================================================== *)
(*  repl_init_types: ported from HOL4's
    compiler/repl/repl_init_typesScript.sml
    A definition theory, with 3 definitions and 6 theorems.  Needed
    by replProof.ml and repl_init.ml.  *)
(* ======================================================== *)

(*
  This file runs the type inferencer on the declarations of the basis,
  Candle kernel and REPL module, i.e. everything in the user-visible
  initial environment of the read-eval-print loop.
*)

needs "basis/pure/mlstring.ml";;
needs "compiler/inference/infer.ml";;
needs "compiler/inference/infer_cv.ml";;
needs "compiler/printing/addPrintVals.ml";;
needs "compiler/repl/repl_check_and_tweak.ml";;
needs "compiler/repl/repl_moduleProg.ml";;
needs "lib/location.ml";;
needs "semantics/ast.ml";;
needs "semantics/namespace.ml";;
needs "translator/ml_prog.ml";;
needs "translator/monadic/monad_base/ml_monadBase.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "repl_init_types"
  ["infer_cv"; "repl_check_and_tweak"; "repl_moduleProg"];;

(* HOL4 repl_init_typesScript.sml:12: ML code, not ported *)

(* HOL4 repl_init_typesScript.sml:14: ML code, not ported *)

(* HOL4 repl_init_typesScript.sml:16-17: the ML values that the definitions
   below antiquote *)

(* HOL4 repl_init_typesScript.sml:19-36: the ML values that the definitions
   below antiquote *)
let repl_prog_types_def = new_definition
  `repl_prog_types = result_tm`;;
(* HOL4 repl_init_typesScript.sml:40-41: ML code, not ported *)

(* HOL4 repl_init_typesScript.sml:43: a theorem that HOL4 states as the
   value of an ML expression: repl_prog_types_thm *)

let repl_init_types_def = new_definition
  `repl_init_types = (init_type_names (FST repl_prog_types),repl_prog_types)`;;

(* HOL4 repl_init_typesScript.sml:49-51: a theorem that HOL4 states as the
   value of an ML expression: repl_init_types_eq *)

(* HOL4 repl_init_typesScript.sml:53: ML code, not ported *)

let repl_prog_env_def = new_definition
  `repl_init_types_repl_prog_env = merge_env env init_env`;;

(* HOL4 repl_init_typesScript.sml:59: ML code, not ported *)

(* HOL4 repl_init_typesScript.sml:61-69: a theorem that HOL4 states as the
   value of an ML expression: CommandLine_arguments_lemma *)

let infertype_prog_inc_CommandLine_arguments = prove
 (`infertype_prog_inc repl_prog_types
     [Dlet unknown_loc ast_Pany
       (ast_App ast_Opapp
         [ast_Var (Long (implode "CommandLine") (Short (implode
           "arguments")));
          ast_Con NONE []])] = M_success repl_prog_types`,
  CHEAT_TAC);;

(* HOL4 repl_init_typesScript.sml:81-89: a theorem that HOL4 states as the
   value of an ML expression: Repl_charsFrom_lemma *)

let infertype_prog_inc_Repl_charsFrom = prove
 (`infertype_prog_inc repl_prog_types
     [Dlet unknown_loc ast_Pany
       (ast_App ast_Opapp
         [ast_Var (Long (implode "Repl") (Short (implode "charsFrom")));
          ast_Lit (ast_StrLit (implode "config_enc_str.txt"))])] =
            M_success repl_prog_types`,
  CHEAT_TAC);;

(* and the interface *)
let _ = unhide_overloads ();;
