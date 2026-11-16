(* ======================================================== *)
(*  CharProg: ported from HOL4's
    basis/CharProgScript.sml
    A definition theory, with 2 definitions and 2 theorems.  Needed
    by Word64Prog.ml.  *)
(* ======================================================== *)

(*
  A module about the char type for the CakeML standard basis library.
*)

needs "basis/RatProg.ml";;
needs "lib/regexp_compiler.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "CharProg"
  ["RatProg"; "ml_prog"; "ml_translator"];;

(* HOL4 CharProgScript.sml:10: ML code, not ported *)

(* Char module -- translated *)

(* HOL4 CharProgScript.sml:14: ML code, not ported *)

(* HOL4 CharProgScript.sml:16: ML code, not ported *)

(* HOL4 CharProgScript.sml:18-19: ML code, not ported *)

(* HOL4 CharProgScript.sml:21-27: the ML values that the definitions below
   antiquote *)

(* HOL4 CharProgScript.sml:29-40: ML code, not ported *)

(* HOL4 CharProgScript.sml:42: the ML values that the definitions below
   antiquote *)

let some_chars_vector_def = new_definition
  `some_chars_vector = Vector (list_of_seq (\n. SOME (CHR n)) 256)`;;

let some_char_def = new_definition
  `some_char c = regexp_compiler_sub some_chars_vector (ORD c)`;;

let some_char_thm = prove
 (`some_char c = SOME c`,
  CHEAT_TAC);;

(* HOL4 CharProgScript.sml:62: ML code, not ported *)

(* HOL4 CharProgScript.sml:64: the ML values that the definitions below
   antiquote *)

(* HOL4 CharProgScript.sml:66: ML code, not ported *)

(* HOL4 CharProgScript.sml:68-69: ML code, not ported *)

(* [local] *)
let some_char_side_thm = prove
 (`some_char_side v = T`,
  CHEAT_TAC);;

(* HOL4 CharProgScript.sml:77: ML code, not ported *)

(* HOL4 CharProgScript.sml:79: ML code, not ported *)

(* HOL4 CharProgScript.sml:81: ML code, not ported *)

(* and the interface *)
let _ = unhide_overloads ();;
