(* ======================================================== *)
(*  arm8Bootstrap: ported from HOL4's
    compiler/bootstrap/compilation/arm8/64/arm8BootstrapScript.sml
    A definition theory, with no definitions and 1 theorem.  Needed
    by arm8BootstrapProof.ml.  *)
(* ======================================================== *)

(*
  Evaluation of the 64-bit version of the compiler into arm8 machine code.
*)

needs "compiler/bootstrap/translation/compiler64Prog.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "arm8Bootstrap"
  ["compiler64Prog"];;

(* HOL4 arm8BootstrapScript.sml:10-11: a theorem that HOL4 states as the
   value of an ML expression: compiler64_compiled *)

(* and the interface *)
let _ = unhide_overloads ();;
