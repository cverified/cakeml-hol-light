(* ======================================================== *)
(*  ag32Bootstrap: ported from HOL4's
    compiler/bootstrap/compilation/ag32/32/ag32BootstrapScript.sml
    A definition theory, with no definitions and 1 theorem.  Needed
    by ag32BootstrapProof.ml.  *)
(* ======================================================== *)

(*
  Evaluate the final part of the 32-bit version of the compiler
  into machine code for ag32, i.e. the Silver ISA.
*)

needs "compiler/bootstrap/translation/compiler32Prog.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "ag32Bootstrap"
  ["compiler32Prog"];;

(* HOL4 ag32BootstrapScript.sml:11-12: a theorem that HOL4 states as the
   value of an ML expression: compiler32_compiled *)

(* and the interface *)
let _ = unhide_overloads ();;
