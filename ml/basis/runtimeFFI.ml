(* ======================================================== *)
(*  runtimeFFI: ported from HOL4's
    basis/runtimeFFIScript.sml
    A definition theory, with 4 definitions and 3 theorems.  Needed
    by RuntimeProof.ml and basis_ffi.ml.  *)
(* ======================================================== *)

(*
  Logical model of the Runtime module's exit function calls.
*)

needs "basis/pure/mlstring.ml";;
needs "characteristic/cfFFIType.ml";;
needs "characteristic/cfHeapsBase.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "runtimeFFI"
  ["cfHeapsBase"];;

let ffi_exit_def = new_definition
  `ffi_exit (conf:word8 list) (bytes:word8 list) one = SOME (FFIdiverge:1
  cfHeapsBase_ffi_result)`;;

let ffi_exit_length = prove
 (`ffi_exit (conf:word8 list) (bytes:word8 list) u = SOME (FFIreturn bytes'
  args') ==> LENGTH bytes' = LENGTH bytes`,
  CHEAT_TAC);;

(* FFI part for the runtime *)

let runtimeFFI_encode_def = new_definition
  `runtimeFFI_encode = (K (cfFFIType_List []):1->ffi)`;;

let decode_def = new_definition
  `decode = ((K (SOME one)):ffi->1 option)`;;

(* encode_11[local] *)
let runtimeFFI_encode_11 = prove
 (`!x y. runtimeFFI_encode x = runtimeFFI_encode y <=> x = y`,
  CHEAT_TAC);;

let decode_encode = prove
 (`decode (runtimeFFI_encode cls) = SOME cls`,
  CHEAT_TAC);;

let runtime_ffi_part_def = new_definition
  `runtime_ffi_part = (runtimeFFI_encode,decode,
     [((implode "exit"),ffi_exit)])`;;

(* and the interface *)
let _ = unhide_overloads ();;
