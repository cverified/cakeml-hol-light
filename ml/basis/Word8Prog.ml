(* ======================================================== *)
(*  Word8Prog: ported from HOL4's
    basis/Word8ProgScript.sml
    A definition theory, with 4 definitions and 11 theorems.  Needed
    by TextIOProof.ml and Word8ArrayProg.ml.  *)
(* ======================================================== *)

(*
  Module about the built-in word8 type.
*)

needs "basis/Word64Prog.ml";;
needs "translator/ml_translator.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "Word8Prog"
  ["Word64Prog"; "ml_prog"; "ml_translator"];;

let _ = do_list hide_constant ["fv"];;

(* HOL4 Word8ProgScript.sml:10: ML code, not ported *)

(* Word8 module -- translated *)

(* HOL4 Word8ProgScript.sml:14-15: ML code, not ported *)

(* HOL4 Word8ProgScript.sml:17: ML code, not ported *)

(* HOL4 Word8ProgScript.sml:19: ML code, not ported *)

(* HOL4 Word8ProgScript.sml:21-22: ML code, not ported *)

(* to/from int/char *)
(* HOL4 Word8ProgScript.sml:25-28: the ML values that the definitions below
   antiquote *)

(* bitwise operations *)
(* HOL4 Word8ProgScript.sml:31-33: the ML values that the definitions below
   antiquote *)

(* word_1comp_eq[local] *)
let Word8Prog_word_1comp_eq = prove
 (`word_1comp w = (word_xor w (n2w 0xFF):word8)`,
  CHEAT_TAC);;

(* HOL4 Word8ProgScript.sml:41-42: ML code, not ported *)

(* arithmetic *)
(* HOL4 Word8ProgScript.sml:45-51: the ML values that the definitions below
   antiquote *)

(* shifts *)

let Word8Prog_var_word_lsl_def = new_definition
  `Word8Prog_var_word_lsl (w:word8) (n:num) =
     if n < 8 then
     if n < 4 then
       if n < 2 then if n < 1 then w else w << 1
       else if n < 3 then w << 2
       else w << 3
     else if n < 6 then if n < 5 then w << 4 else w << 5
     else if n < 7 then w << 6
     else w << 7 else (n2w 0)`;;

(* var_word_lsl_thm *)
let Word8Prog_var_word_lsl_thm = prove
 (`Word8Prog_var_word_lsl w n = word_lsl w n`,
  CHEAT_TAC);;
add_simp Word8Prog_var_word_lsl_thm;;

let Word8Prog_var_word_lsr_def = new_definition
  `Word8Prog_var_word_lsr (w:word8) (n:num) =
     if n < 8 then
     if n < 4 then
       if n < 2 then if n < 1 then w else w >>> 1
       else if n < 3 then w >>> 2
       else w >>> 3
     else if n < 6 then if n < 5 then w >>> 4 else w >>> 5
     else if n < 7 then w >>> 6
     else w >>> 7 else (n2w 0)`;;

(* var_word_lsr_thm *)
let Word8Prog_var_word_lsr_thm = prove
 (`Word8Prog_var_word_lsr w n = word_lsr w n`,
  CHEAT_TAC);;
add_simp Word8Prog_var_word_lsr_thm;;

let Word8Prog_var_word_asr_def = new_definition
  `Word8Prog_var_word_asr (w:word8) (n:num) =
     if n < 8 then
     if n < 4 then
       if n < 2 then if n < 1 then w else w >> 1
       else if n < 3 then w >> 2
       else w >> 3
     else if n < 6 then if n < 5 then w >> 4 else w >> 5
     else if n < 7 then w >> 6
     else w >> 7 else w >> 8`;;

(* var_word_asr_thm *)
let Word8Prog_var_word_asr_thm = prove
 (`Word8Prog_var_word_asr w n = word_asr w n`,
  CHEAT_TAC);;
add_simp Word8Prog_var_word_asr_thm;;

(* word_ror_eq_word_shifts *)
let Word8Prog_word_ror_eq_word_shifts = prove
 (`!(w:'a word) n.
     word_ror w n =
     word_or (word_lsl w (dimindex (:'a) - (n MOD (dimindex (:'a)))))
             (word_lsr w (n MOD (dimindex (:'a))))`,
  CHEAT_TAC);;

let Word8Prog_var_word_ror_def = new_definition
  `Word8Prog_var_word_ror (w:word8) n =
     word_or (Word8Prog_var_word_lsl w (8 - (n MOD 8)))
             (Word8Prog_var_word_lsr w (n MOD 8))`;;

(* var_word_ror_thm *)
let Word8Prog_var_word_ror_thm = prove
 (`Word8Prog_var_word_ror w n = word_ror w n`,
  CHEAT_TAC);;
add_simp Word8Prog_var_word_ror_thm;;

(* HOL4 Word8ProgScript.sml:148-149: ML code, not ported *)

(* HOL4 Word8ProgScript.sml:151-152: ML code, not ported *)

(* HOL4 Word8ProgScript.sml:154-155: ML code, not ported *)

(* HOL4 Word8ProgScript.sml:157-158: ML code, not ported *)

(* var_word_ror_side[local] *)
let Word8Prog_var_word_ror_side = prove
 (`!w n. var_word_ror_side w n = T`,
  CHEAT_TAC);;

(* HOL4 Word8ProgScript.sml:167: ML code, not ported *)

(* HOL4 Word8ProgScript.sml:169-170: ML code, not ported *)

(* HOL4 Word8ProgScript.sml:172: ML code, not ported *)

(* if any more theorems get added here, probably should create Word8ProofTheory *)

(* [xlet_auto_match] *)
let WORD_UNICITY_R = prove
 (`!f fv' fv'. WORD (f:word8) fv' ==> (WORD f fv' <=> fv' = fv')`,
  CHEAT_TAC);;

(* [xlet_auto_match] *)
let WORD_UNICITY_L = prove
 (`!f f' fv'. WORD (f:word8) fv' ==> (WORD f' fv' <=> f = f')`,
  CHEAT_TAC);;

(* [xlet_auto_match] *)
let n2w_UNICITY = prove
 (`!n1 n2. n1 <= 255 ==> (((n2w n1:word8) = n2w n2 /\ n2 <= 255) <=> n1 = n2)`,
  CHEAT_TAC);;

(* [xlet_auto_match] *)
let WORD_n2w_UNICITY_L = prove
 (`!n1 n2 f. n1 <= 255 /\ WORD (n2w n1:word8) f ==>
    (WORD (n2w n2:word8) f /\ n2 <= 255 <=> n1 = n2)`,
  CHEAT_TAC);;

(* HOL4 Word8ProgScript.sml:202: the overload WORD8, which the port expands *)

(* and the names it reads as variables are constants again *)
let _ = do_list unhide_constant
  ["fv"];;

(* and the interface *)
let _ = unhide_overloads ();;
