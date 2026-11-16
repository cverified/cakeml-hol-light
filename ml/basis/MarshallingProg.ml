(* ======================================================== *)
(*  MarshallingProg: ported from HOL4's
    basis/MarshallingProgScript.sml
    A definition theory, with no definitions and 6 theorems.  Needed
    by TextIOProg.ml and TextIOProof.ml.  *)
(* ======================================================== *)

(*
  Module with functions that aid converting to and from the byte
  arrays that CakeML foreign-function interface (FFI) uses.
*)

needs "basis/DoubleProg.ml";;
needs "basis/Marshalling.ml";;
needs "basis/Word8ArrayProof.ml";;
needs "translator/ml_translator.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "MarshallingProg"
  ["DoubleProg"; "Marshalling"; "Word8ArrayProof"; "cf"; "ml_prog";
   "ml_translator"];;

(* HOL4 MarshallingProgScript.sml:11: ML code, not ported *)

(* Word8 module -- translated *)

(* HOL4 MarshallingProgScript.sml:15: ML code, not ported *)

(* HOL4 MarshallingProgScript.sml:17-22: ML code, not ported *)

(* HOL4 MarshallingProgScript.sml:24-29: ML code, not ported *)

(* HOL4 MarshallingProgScript.sml:31: ML code, not ported *)

(* if any more theorems get added here, probably should create Word8ProofTheory *)

(* [xlet_auto_match] *)
let n2w2_UNICITY_R = prove
 (`!n1 n2. n1 < 256 EXP 2 ==> ((n2w2 n1 = n2w2 n2 /\ n2 < 256 EXP 2) <=> n1 =
  n2)`,
  CHEAT_TAC);;

(* [xlet_auto_match] *)
let WORD_n2w2_UNICITY_L = prove
 (`!n1 n2 f. n1 < 256 EXP 2 /\ LIST_TYPE WORD (n2w2 n1) f ==>
    (LIST_TYPE WORD (n2w2 n2) f /\ n2 < 256 EXP 2 <=> n1 = n2)`,
  CHEAT_TAC);;

(* needed? *)
(* [xlet_auto_match] *)
let n2w8_UNICITY_R = prove
 (`!n1 n2. n1 < 256 EXP 8 ==> ((n2w8 n1 = n2w8 n2 /\ n2 < 256 EXP 8) <=> n1 =
  n2)`,
  CHEAT_TAC);;

(* [xlet_auto_match] *)
let WORD_n2w8_UNICITY_L = prove
 (`!n1 n2 f. n1 < 256 EXP 8 /\ LIST_TYPE WORD (n2w8 n1) f ==>
    (LIST_TYPE WORD (n2w8 n2) f /\ n2 < 256 EXP 8 <=> n1 = n2)`,
  CHEAT_TAC);;

(* HOL4 MarshallingProgScript.sml:94-107: a theorem whose statement the port
   cannot state yet: n2w2_spec *)

(* HOL4 MarshallingProgScript.sml:109-119: a theorem whose statement the
   port cannot state yet: w22n_spec *)

(* and the interface *)
let _ = unhide_overloads ();;
