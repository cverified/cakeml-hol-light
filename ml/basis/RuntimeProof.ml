(* ======================================================== *)
(*  RuntimeProof: ported from HOL4's
    basis/RuntimeProofScript.sml
    A proof theory, with 1 definition and 4 theorems.  Needed by
    basisProg.ml and basis_ffi.ml.  *)
(* ======================================================== *)

(*
  Proof about the exit function in the Runtime module.
*)

needs "basis/RuntimeProg.ml";;
needs "basis/pure/mlstring.ml";;
needs "basis/runtimeFFI.ml";;
needs "characteristic/cfHeapsBase.ml";;
needs "characteristic/cfLetAuto.ml";;
needs "characteristic/cfMain.ml";;
needs "translator/ml_translator.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "RuntimeProof"
  ["RuntimeProg"; "cf"; "cfLetAuto"; "cfMain"; "ml_prog"; "ml_translator";
   "mlstring"; "runtimeFFI"];;

let _ = do_list hide_constant ["abort"];;

(* heap predicate for the (trivial) runtime state *)

let RUNTIME_def = new_definition
  `RUNTIME =
     IOx runtime_ffi_part one`;;

let RUNTIME_FFI_part_hprop = prove
 (`FFI_part_hprop RUNTIME`,
  CHEAT_TAC);;

(* HOL4 RuntimeProofScript.sml:30: ML code, not ported *)

(* HOL4 RuntimeProofScript.sml:32-76: a theorem whose statement the port
   cannot state yet: Runtime_exit_spec *)

(* HOL4 RuntimeProofScript.sml:78-90: a theorem whose statement the port
   cannot state yet: Runtime_abort_spec *)

(* [hprop_inj] *)
let RUNTIME_HPROP_INJ = prove
 (`!cl1 cl2. HPROP_INJ (RUNTIME) (RUNTIME) (T)`,
  CHEAT_TAC);;

(* and the names it reads as variables are constants again *)
let _ = do_list unhide_constant
  ["abort"];;

(* and the interface *)
let _ = unhide_overloads ();;
