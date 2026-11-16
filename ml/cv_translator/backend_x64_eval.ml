(* ======================================================== *)
(*  backend_x64_eval: ported from HOL4's
    cv_translator/backend_x64_evalScript.sml
    A definition theory, with 1 definition and no theorems.  No file
    of the port needs it.  *)
(* ======================================================== *)

needs "semantics/ast.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "backend_x64_eval" [];;

(*
  Experiments with evaluating the compiler using cv_compute
*)

let backend_x64_eval_prog_def = new_definition
  `backend_x64_eval_prog = ([]:dec list)`;;

(* HOL4 backend_x64_evalScript.sml:12: ML code, not ported *)

(* and the interface *)
let _ = unhide_overloads ();;
