(* ======================================================== *)
(*  repl_init_envProg: ported from HOL4's
    compiler/repl/repl_init_envProgScript.sml
    A definition theory, with no definitions and 1 theorem.  Needed
    by decProg.ml and repl_init.ml.  *)
(* ======================================================== *)

(*
  This file partially instantiates the eval_state and inserts a Denv declaration.
*)

needs "compiler/repl/repl_moduleProg.ml";;
needs "translator/ml_translator.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "repl_init_envProg"
  ["ml_prog"; "ml_translator"; "repl_moduleProg"];;

(* HOL4 repl_init_envProgScript.sml:10: ML code, not ported *)

(* we set the env_id_counter field of the eval_state *)

(* HOL4 repl_init_envProgScript.sml:14-15: ML code, not ported *)

(* we declare a Denv *)

(* HOL4 repl_init_envProgScript.sml:19-20: ML code, not ported *)

(* HOL4 repl_init_envProgScript.sml:22-28: a theorem whose statement the
   port cannot state yet: declare_env_thm *)

(* HOL4 repl_init_envProgScript.sml:30: ML code, not ported *)

(* and the interface *)
let _ = unhide_overloads ();;
