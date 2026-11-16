(* ======================================================== *)
(*  basisProg: ported from HOL4's
    basis/basisProgScript.sml
    A definition theory, with 1 definition and 5 theorems.  Needed
    by candle_prover_semantics.ml, compiler.ml and
    ml_hol_kernel_funsProg.ml.  *)
(* ======================================================== *)

(*
  Contains the code for the entire CakeML basis library in basis_def.
*)

needs "basis/CommandLineProof.ml";;
needs "basis/PrettyPrinterProg.ml";;
needs "basis/RuntimeProof.ml";;
needs "basis/SexpProg.ml";;
needs "basis/TextIOProof.ml";;
needs "translator/std_prelude.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "basisProg"
  ["CommandLineProof"; "PrettyPrinterProg"; "RuntimeProof"; "SexpProg";
   "TextIOProof"; "cf"; "ml_prog"; "ml_translator"; "std_prelude"];;

(* HOL4 basisProgScript.sml:11: ML code, not ported *)

(* HOL4 basisProgScript.sml:13-25: the ML values that the definitions below
   antiquote *)

(* HOL4 basisProgScript.sml:27: ML code, not ported *)

(* HOL4 basisProgScript.sml:29-35: ML code, not ported *)

(* HOL4 basisProgScript.sml:37-43: ML code, not ported *)

(* HOL4 basisProgScript.sml:45: ML code, not ported *)

(* HOL4 basisProgScript.sml:47-49: ML code, not ported *)

(* HOL4 basisProgScript.sml:51: ML code, not ported *)

(* HOL4 basisProgScript.sml:53-82: a theorem whose statement the port cannot
   state yet: print_app_list_aux_spec *)

(* HOL4 basisProgScript.sml:84-94: a theorem whose statement the port cannot
   state yet: print_app_list_spec *)

(* HOL4 basisProgScript.sml:96-98: ML code, not ported *)

(* HOL4 basisProgScript.sml:100-109: a theorem whose statement the port
   cannot state yet: print_int_spec *)

(* HOL4 basisProgScript.sml:111-113: ML code, not ported *)

(* HOL4 basisProgScript.sml:115-125: a theorem whose statement the port
   cannot state yet: print_pp_spec *)

(* HOL4 basisProgScript.sml:127: ML code, not ported *)

(* HOL4 basisProgScript.sml:129: ML code, not ported *)

let basis_def = assume_definition
  "declared (no value)"
  `basis = basis_prog`;;

(* HOL4 basisProgScript.sml:135-137: a theorem that HOL4 states as the value
   of an ML expression: basis_Decls_thm *)

(* and the interface *)
let _ = unhide_overloads ();;
