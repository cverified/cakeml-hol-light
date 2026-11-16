(* ======================================================== *)
(*  decProg: ported from HOL4's
    compiler/bootstrap/translation/decProgScript.sml
    A definition theory, with no definitions, 1 datatype and 4
    theorems.  Needed by to_flatProg.ml.  *)
(* ======================================================== *)

(*
  Translation of CakeML source AST
*)

needs "candle/prover/ast_extras.ml";;
needs "compiler/repl/repl_init_envProg.ml";;
needs "semantics/ast.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "translator/ml_pmatch.ml";;
needs "translator/ml_translator.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "decProg"
  ["ast"; "ast_extras"; "ml_pmatch"; "ml_prog"; "ml_translator";
   "repl_init_envProg"; "semanticPrimitives"];;

(* HOL4 decProgScript.sml:11-13: ML code, not ported *)

(* HOL4 decProgScript.sml:15: ML code, not ported *)

(* this is a hack to make the translator avoid these names *)
let decProg_dummy_INDUCT,decProg_dummy_RECURSION = define_datatype
  "decProg_dummy =
     decProg_Tyvar
   | decProg_Tyapp
   | decProg_Var
   | decProg_Const
   | decProg_Abs
   | decProg_Comb
   | decProg_Sequent";;
(* HOL4 decProgScript.sml:21: ML code, not ported *)
(* end of hack *)

(* HOL4 decProgScript.sml:24-37: ML code, not ported *)

(* HOL4 decProgScript.sml:39: a theorem that HOL4 states as the value of an
   ML expression: IsTypeRep_LIST_v *)

let IsTypeRep_AST_DEC_v = prove
 (`IsTypeRep AST_DEC_v AST_DEC_TYPE`,
  CHEAT_TAC);;

(* HOL4 decProgScript.sml:58-59: a theorem that HOL4 states as the value of
   an ML expression: EqualityType_AST_DEC_TYPE *)

(* HOL4 decProgScript.sml:61-62: a theorem that HOL4 states as the value of
   an ML expression: EqualityType_LIST_TYPE_AST_DEC_TYPE *)

(* HOL4 decProgScript.sml:64-69: ML code, not ported *)

(* and the interface *)
let _ = unhide_overloads ();;
