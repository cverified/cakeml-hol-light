(* ======================================================== *)
(*  Word8ArrayProg: ported from HOL4's
    basis/Word8ArrayProgScript.sml
    A definition theory, with no definitions and no theorems.
    Needed by ArrayProg.ml and Word8ArrayProof.ml.  *)
(* ======================================================== *)

(*
  Module about the built-in byte-array type.
*)

needs "basis/Word8Prog.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "Word8ArrayProg"
  ["Word8Prog"; "ml_prog"; "ml_translator"];;

(* HOL4 Word8ArrayProgScript.sml:10: ML code, not ported *)

(* HOL4 Word8ArrayProgScript.sml:12-13: ML code, not ported *)

(* HOL4 Word8ArrayProgScript.sml:15: ML code, not ported *)

(* HOL4 Word8ArrayProgScript.sml:17-33: ML code, not ported *)

(* HOL4 Word8ArrayProgScript.sml:35: ML code, not ported *)

(* HOL4 Word8ArrayProgScript.sml:37-44: ML code, not ported *)

(* HOL4 Word8ArrayProgScript.sml:46: ML code, not ported *)

(* HOL4 Word8ArrayProgScript.sml:48-51: ML code, not ported *)

(* HOL4 Word8ArrayProgScript.sml:53: ML code, not ported *)

(* HOL4 Word8ArrayProgScript.sml:55: ML code, not ported *)

(* and the interface *)
let _ = unhide_overloads ();;
