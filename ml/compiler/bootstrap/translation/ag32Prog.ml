(* ======================================================== *)
(*  ag32Prog: ported from HOL4's
    compiler/bootstrap/translation/ag32ProgScript.sml
    A definition theory, with 1 definition and 7 theorems.  Needed
    by compiler32Prog.ml.  *)
(* ======================================================== *)

(*
  Translate the ag32 instruction encoder and ag32-specific config.
*)

needs "compiler/bootstrap/translation/arm7Prog.ml";;
needs "lib/bitstring.ml";;
needs "semantics/evaluate.ml";;
needs "translator/ml_translator.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "ag32Prog"
  ["arm7Prog"; "evaluate"; "ml_translator"];;
(* HOL4 ancestors outside the port: ag32_target ag32 *)

(* HOL4 ag32ProgScript.sml:10-14: ML code, not ported *)

(* HOL4 ag32ProgScript.sml:18-19: ML code, not ported *)

(* [local] *)
let ri2bits_eq = prove
 (`ri2bits ri = match ri with ag32_Imm v -> ((n2w 64):word7) | ag32_Reg i ->
  w2w i`,
  CHEAT_TAC);;

(* HOL4 ag32ProgScript.sml:27-29: ML code, not ported *)

(* [local] *)
let enc_eq = prove
 (`enc (func,w,a,b,opc') =
       (w2w (ri2bits w) << 25 ||
        w2w (ri2bits a) << 17 ||
        w2w (ri2bits b) << 10 ||
        w2w ((n2w (funcT2num func)):word4) << 6 ||
        w2w opc')`,
  CHEAT_TAC);;

(* HOL4 ag32ProgScript.sml:42: ML code, not ported *)

(* [local] *)
let encShift_eq = prove
 (`encShift (sh,w,a,b,opc') =
       (w2w (ri2bits w) << 25 ||
        w2w (ri2bits a) << 17 ||
        w2w (ri2bits b) << 10 ||
        w2w ((n2w (shiftT2num sh)):word4) << 6 ||
        w2w opc')`,
  CHEAT_TAC);;

(* HOL4 ag32ProgScript.sml:55: ML code, not ported *)

(* v2w_sing[local] *)
let ag32Prog_v2w_sing = prove
 (`v2w [b] = if b then (n2w 1) else (n2w 0):word1`,
  CHEAT_TAC);;

(* HOL4 ag32ProgScript.sml:63-65: ML code, not ported *)

(* HOL4 ag32ProgScript.sml:67: ML code, not ported *)

(* HOL4 ag32ProgScript.sml:69-71: ML code, not ported *)

(* HOL4 ag32ProgScript.sml:73: ML code, not ported *)

(* [local] *)
let ag32_encode_eq = prove
 (`ag32_encode [] = [] /\
   ag32_encode (CONS x xs) = APPEND (ag32_encode1 x) (ag32_encode xs)`,
  CHEAT_TAC);;

(* HOL4 ag32ProgScript.sml:82: ML code, not ported *)

(* [local] *)
let word_msb_word_bit = prove
 (`word_msb w = word_bit (dimindex (:'a) - 1) (w:'a word)`,
  CHEAT_TAC);;

(* word_neg[local] *)
let ag32Prog_word_neg = prove
 (`--w = (n2w 0) - w`,
  CHEAT_TAC);;

(* HOL4 ag32ProgScript.sml:95-97: ML code, not ported *)

(* HOL4 ag32ProgScript.sml:99-107: ML code, not ported *)

(* HOL4 ag32ProgScript.sml:109: ML code, not ported *)

(* HOL4 ag32ProgScript.sml:111: ML code, not ported *)

(* HOL4 ag32ProgScript.sml:113-123: ML code, not ported *)

let ag32_enc_Const_def = new_definition
  `ag32_enc_Const n c = ag32_enc (word_Inst (asm_Const n c))`;;

(* HOL4 ag32ProgScript.sml:164: ML code, not ported *)

(* HOL4 ag32ProgScript.sml:166: ML code, not ported *)

(* HOL4 ag32ProgScript.sml:168: ML code, not ported *)

(* HOL4 ag32ProgScript.sml:170: ML code, not ported *)


(* HOL4 ag32ProgScript.sml:173: ML code, not ported *)

(* and the interface *)
let _ = unhide_overloads ();;
