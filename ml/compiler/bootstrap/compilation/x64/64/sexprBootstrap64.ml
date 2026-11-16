(* ======================================================== *)
(*  sexprBootstrap64: ported from HOL4's
    compiler/bootstrap/compilation/x64/64/sexprBootstrap64Script.sml
    A definition theory, with no definitions and no theorems.  No
    file of the port needs it.  *)
(* ======================================================== *)

(*
  Produces an sexp print-out of the bootstrap translated compiler
  definition for the 64-bit version of the compiler.
*)

needs "compiler/bootstrap/translation/compiler64Prog.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "sexprBootstrap64"
  ["compiler64Prog"];;

(* HOL4 sexprBootstrap64Script.sml:11: ML code, not ported *)

(* HOL4 sexprBootstrap64Script.sml:13-17: ML code, not ported *)

(* HOL4 sexprBootstrap64Script.sml:19-111: code that the source has in a
   comment *)

(* and the interface *)
let _ = unhide_overloads ();;
