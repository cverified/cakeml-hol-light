(* ======================================================== *)
(*  CommandLineProg: ported from HOL4's
    basis/CommandLineProgScript.sml
    A definition theory, with no definitions and no theorems.
    Needed by CommandLineProof.ml, DoubleProg.ml and TextIOProg.ml.  *)
(* ======================================================== *)

(*
  A module about command-line arguments for the CakeML standard basis
  library.
*)

needs "basis/HashtableProg.ml";;
needs "translator/ml_translator.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "CommandLineProg"
  ["HashtableProg"; "ml_prog"; "ml_translator"];;

(* HOL4 CommandLineProgScript.sml:11: ML code, not ported *)

(* HOL4 CommandLineProgScript.sml:15: ML code, not ported *)

(* HOL4 CommandLineProgScript.sml:17: ML code, not ported *)

(* HOL4 CommandLineProgScript.sml:19-25: ML code, not ported *)

(* HOL4 CommandLineProgScript.sml:27-31: ML code, not ported *)

(* HOL4 CommandLineProgScript.sml:33-46: ML code, not ported *)

(* HOL4 CommandLineProgScript.sml:48: ML code, not ported *)

(* HOL4 CommandLineProgScript.sml:50-58: ML code, not ported *)

(* HOL4 CommandLineProgScript.sml:60-62: ML code, not ported *)

(* HOL4 CommandLineProgScript.sml:64-66: ML code, not ported *)

(* HOL4 CommandLineProgScript.sml:68: ML code, not ported *)

(* HOL4 CommandLineProgScript.sml:70: ML code, not ported *)

(* and the interface *)
let _ = unhide_overloads ();;
