(* ======================================================== *)
(*  sexprBootstrap32: ported from HOL4's
    compiler/bootstrap/compilation/x64/64/sexprBootstrap32Script.sml
    A definition theory, with no definitions and no theorems.  No
    file of the port needs it.  *)
(* ======================================================== *)

(*
  Produces an sexp print-out of the bootstrap translated compiler
  definition for the 32-bit version of the compiler.
*)

needs "compiler/bootstrap/translation/compiler32Prog.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "sexprBootstrap32"
  ["compiler32Prog"];;

(* HOL4 sexprBootstrap32Script.sml:11: ML code, not ported *)

(* HOL4 sexprBootstrap32Script.sml:13-17: ML code, not ported *)

(* and the interface *)
let _ = unhide_overloads ();;
