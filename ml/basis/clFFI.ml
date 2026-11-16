(* ======================================================== *)
(*  clFFI: ported from HOL4's
    basis/clFFIScript.sml
    A definition theory, with 6 definitions and 5 theorems.  Needed
    by CommandLineProof.ml, ag32_basis_ffiProof.ml and basis_ffi.ml.  *)
(* ======================================================== *)

(*
  Logical model of the commandline state: simply a list of mlstrings
*)

needs "basis/pure/mlstring.ml";;
needs "characteristic/cfHeapsBase.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "clFFI"
  ["cfHeapsBase"; "mlstring"];;

let _ = do_list hide_constant ["decode"];;

(* a valid argument has a length that fits 16 bits and no null bytes *)

let validArg_def = new_definition
  `validArg s <=> strlen s < 256 * 256 /\ ~(MEM (CHR 0) (explode s))`;;

(* there are 3 FFI functions over the commandline state: *)

let ffi_get_arg_count_def = new_definition
  `ffi_get_arg_count (conf:word8 list) (bytes:word8 list) args =
     if LENGTH bytes = 2 /\ LENGTH args < 256 * 256 then
       SOME (FFIreturn [n2w (LENGTH args);
              n2w (LENGTH args DIV 256)] args)
     else NONE`;;

let ffi_get_arg_length_def = new_definition
  `ffi_get_arg_length (conf:word8 list) (bytes:word8 list) args =
     if LENGTH bytes = 2 /\ LENGTH args < 256 * 256 then
       (let index = w2n (EL 1 bytes) * 256 + w2n (EL 0 bytes) in
          if index < LENGTH args then
            SOME (FFIreturn [n2w (strlen (EL index args));
                   n2w (strlen (EL index args) DIV 256)] args)
          else NONE)
     else NONE`;;

let ffi_get_arg_def = new_definition
  `ffi_get_arg (conf:word8 list) (bytes:word8 list) args =
     if 2 <= LENGTH bytes then
       (let index = w2n (EL 1 bytes) * 256 + w2n (EL 0 bytes) in
        let arg = EL index args in
          if index < LENGTH args /\ strlen (EL index args) <= LENGTH bytes
            then
            SOME (FFIreturn (APPEND (MAP (n2w o ORD) (explode arg)) (DROP
              (strlen arg) bytes)) args)
          else NONE)
       else NONE`;;

(* lengths *)

let ffi_get_arg_count_length = prove
 (`ffi_get_arg_count conf bytes args = SOME (FFIreturn bytes' args') ==>
    LENGTH bytes' = LENGTH bytes`,
  CHEAT_TAC);;

let ffi_get_arg_length_length = prove
 (`ffi_get_arg_length conf bytes args = SOME (FFIreturn bytes' args') ==>
    LENGTH bytes' = LENGTH bytes`,
  CHEAT_TAC);;

let ffi_get_arg_length = prove
 (`ffi_get_arg conf bytes args = SOME (FFIreturn bytes' args') ==>
    LENGTH bytes' = LENGTH bytes`,
  CHEAT_TAC);;

(* FFI part for the commandline *)

let encode_def = new_definition
  `clFFI_encode = encode_list cfFFIType_Str`;;

(* [local] *)
let encode_11 = prove
 (`!x y. clFFI_encode x = clFFI_encode y <=> x = y`,
  CHEAT_TAC);;

(* [local] *)
let encode_decode_exists = prove
 (`?decode'. !cls. decode' (clFFI_encode cls) = SOME cls`,
  CHEAT_TAC);;

(* HOL4 clFFIScript.sml:90-95: ML code, not ported *)

let cl_ffi_part_def = new_definition
  `cl_ffi_part = (clFFI_encode,decode,
     [((implode "get_arg_count"),ffi_get_arg_count);
      ((implode "get_arg_length"),ffi_get_arg_length);
      ((implode "get_arg"),ffi_get_arg)])`;;

(* and the names it reads as variables are constants again *)
let _ = do_list unhide_constant
  ["decode"];;

(* and the interface *)
let _ = unhide_overloads ();;
