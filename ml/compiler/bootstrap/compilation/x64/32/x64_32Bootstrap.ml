(* ======================================================== *)
(*  x64_32Bootstrap: ported from HOL4's
    compiler/bootstrap/compilation/x64/32/x64_32BootstrapScript.sml
    A definition theory, with no definitions and 1 theorem.  Needed
    by x64_32BootstrapProof.ml.  *)
(* ======================================================== *)

(*
  Evaluation of the 32-bit version of the compiler into x64 machine code.
*)

needs "compiler/bootstrap/translation/compiler32Prog.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "x64_32Bootstrap"
  ["compiler32Prog"];;

(* HOL4 x64_32BootstrapScript.sml:10-11: a theorem that HOL4 states as the
   value of an ML expression: compiler32_compiled *)

(* and the interface *)
let _ = unhide_overloads ();;
