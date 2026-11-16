(* ======================================================== *)
(*  RuntimeProg: ported from HOL4's
    basis/RuntimeProgScript.sml
    A definition theory, with 3 definitions and no theorems.  Needed
    by OptionProg.ml, RuntimeProof.ml, backend_asm.ml and
    pan_passes.ml.  *)
(* ======================================================== *)

(*
  Module that contains a few special functions, e.g. a function for
  forcing a full GC to run, a function for producing debug output.
*)

needs "basis/pure/mloption.ml";;
needs "basis/pure/mlstring.ml";;
needs "characteristic/cfDiv.ml";;
needs "translator/ml_translator.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "RuntimeProg"
  ["cfDiv"; "ml_prog"; "ml_translator"; "mloption"];;

(* HOL4 RuntimeProgScript.sml:11: ML code, not ported *)

(* HOL4 RuntimeProgScript.sml:13: ML code, not ported *)

let fullGC_def = new_definition
  `fullGC (u:1) = force_unit_type u (force_gc_to_run 0 0)`;;

(* HOL4 RuntimeProgScript.sml:19-20: ML code, not ported *)

let fail_def = new_definition
  `NONE (u:1) = force_unit_type u (force_out_of_memory_error u)`;;

(* HOL4 RuntimeProgScript.sml:26-27: ML code, not ported *)

let debugMsg_def = new_definition
  `debugMsg s = empty_ffi s`;;

(* HOL4 RuntimeProgScript.sml:33-34: ML code, not ported *)

(* HOL4 RuntimeProgScript.sml:36-42: the ML values that the definitions
   below antiquote *)

(* HOL4 RuntimeProgScript.sml:44: ML code, not ported *)

(* HOL4 RuntimeProgScript.sml:46-48: ML code, not ported *)

(* HOL4 RuntimeProgScript.sml:50-56: ML code, not ported *)

(* HOL4 RuntimeProgScript.sml:58-60: ML code, not ported *)

(* HOL4 RuntimeProgScript.sml:62: ML code, not ported *)

(* and the interface *)
let _ = unhide_overloads ();;
