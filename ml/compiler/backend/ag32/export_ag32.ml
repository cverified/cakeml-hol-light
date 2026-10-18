(* ======================================================== *)
(*  export_ag32: ported from HOL4's
    compiler/backend/ag32/export_ag32Script.sml
    A definition theory, with 1 definition and no theorems.  Needed
    by compiler.ml.  *)
(* ======================================================== *)

(*
  Define the format of the compiler-generated output file for ag32
*)

needs "basis/pure/mlstring.ml";;
needs "compiler/backend/export.ml";;
needs "misc/misc.ml";;

let ag32_export_def = cake_define
  `ag32_export (ffi_names':mlstring list) bytes (data:word32 list)
  (syms:(mlstring#num#num) list) exp ret pk =
     SmartAppend
      (split16 (words_line (implode ".data_word ") word_to_string)
        data)
      (split16 (words_line (implode ".code_byte ") byte_to_string)
        bytes)`;;
