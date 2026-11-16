(* ======================================================== *)
(*  Word64Prog: ported from HOL4's
    basis/Word64ProgScript.sml
    A definition theory, with 5 definitions and 7 theorems.  Needed
    by Word8Prog.ml.  *)
(* ======================================================== *)

(*
  Module about the built-in word64 type.
*)

needs "basis/CharProg.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "Word64Prog"
  ["CharProg"; "ml_prog"; "ml_translator"];;

(* HOL4 Word64ProgScript.sml:10: ML code, not ported *)

(* Word64 module -- translated *)

(* HOL4 Word64ProgScript.sml:14: ML code, not ported *)

(* HOL4 Word64ProgScript.sml:16: ML code, not ported *)

(* HOL4 Word64ProgScript.sml:18-19: ML code, not ported *)

(* to/from int *)
(* HOL4 Word64ProgScript.sml:22-24: the ML values that the definitions below
   antiquote *)

(* bitwise operations *)
(* HOL4 Word64ProgScript.sml:27-29: the ML values that the definitions below
   antiquote *)

(* [local] *)
let word_1comp_eq = prove
 (`word_1comp w = (word_xor w (n2w 0xFFFFFFFFFFFFFFFF):word64)`,
  CHEAT_TAC);;

(* HOL4 Word64ProgScript.sml:37-38: ML code, not ported *)

(* arithmetic *)
(* HOL4 Word64ProgScript.sml:41-47: the ML values that the definitions below
   antiquote *)

(* shifts *)

let var_word_lsl_def,var_word_lsl_ind = define_guess
  `Word64Prog_var_word_lsl (w:word64) (n:num) = if 64 < n then (n2w 0)
     else if n < 8 then
     if n < 4 then
       if n < 2 then if n < 1 then w else w << 1
       else if n < 3 then w << 2
       else w << 3
     else if n < 6 then if n < 5 then w << 4 else w << 5
     else if n < 7 then w << 6
     else w << 7 else Word64Prog_var_word_lsl (w << 8) (n - 8)`;;

let var_word_lsl_thm = prove
 (`Word64Prog_var_word_lsl w n = word_lsl w n`,
  CHEAT_TAC);;
add_simp var_word_lsl_thm;;

let var_word_lsr_def,var_word_lsr_ind = define_guess
  `Word64Prog_var_word_lsr (w:word64) (n:num) = if 64 < n then (n2w 0)
     else if n < 8 then
     if n < 4 then
       if n < 2 then if n < 1 then w else w >>> 1
       else if n < 3 then w >>> 2
       else w >>> 3
     else if n < 6 then if n < 5 then w >>> 4 else w >>> 5
     else if n < 7 then w >>> 6
     else w >>> 7 else Word64Prog_var_word_lsr (w >>> 8) (n - 8)`;;

let var_word_lsr_thm = prove
 (`Word64Prog_var_word_lsr w n = word_lsr w n`,
  CHEAT_TAC);;
add_simp var_word_lsr_thm;;

let var_word_asr_def,var_word_asr_ind = define_guess
  `Word64Prog_var_word_asr (w:word64) (n:num) = if 64 < n then w >> 64
     else if n < 8 then
     if n < 4 then
       if n < 2 then if n < 1 then w else w >> 1
       else if n < 3 then w >> 2
       else w >> 3
     else if n < 6 then if n < 5 then w >> 4 else w >> 5
     else if n < 7 then w >> 6
     else w >> 7 else Word64Prog_var_word_asr (w >> 8) (n - 8)`;;

let var_word_asr_thm = prove
 (`Word64Prog_var_word_asr w n = word_asr w n`,
  CHEAT_TAC);;
add_simp var_word_asr_thm;;

let word_ror_eq_word_shifts = prove
 (`!(w:'a word) n.
     word_ror w n =
     word_or (word_lsl w (dimindex (:'a) - (n MOD (dimindex (:'a)))))
             (word_lsr w (n MOD (dimindex (:'a))))`,
  CHEAT_TAC);;

let var_word_ror_def = new_definition
  `Word64Prog_var_word_ror (w:word64) n =
     word_or (Word64Prog_var_word_lsl w (64 - (n MOD 64)))
             (Word64Prog_var_word_lsr w (n MOD 64))`;;

let var_word_ror_thm = prove
 (`Word64Prog_var_word_ror w n = word_ror w n`,
  CHEAT_TAC);;
add_simp var_word_ror_thm;;

(* HOL4 Word64ProgScript.sml:144-145: ML code, not ported *)

(* HOL4 Word64ProgScript.sml:147-148: ML code, not ported *)

(* HOL4 Word64ProgScript.sml:150-151: ML code, not ported *)

(* HOL4 Word64ProgScript.sml:153-154: ML code, not ported *)

(* [local] *)
let var_word_ror_side = prove
 (`!w n. var_word_ror_side w n = T`,
  CHEAT_TAC);;

(* HOL4 Word64ProgScript.sml:163: ML code, not ported *)

let concat_all_def = new_definition
  `concat_all (a:word8) b c d e f g h =
     (concat_word_list [a; b; c; d; e; f; g; h]:64 word)`;;

(* HOL4 Word64ProgScript.sml:170-171: ML code, not ported *)

(* HOL4 Word64ProgScript.sml:173-174: ML code, not ported *)

(* HOL4 Word64ProgScript.sml:176-177: ML code, not ported *)

(* HOL4 Word64ProgScript.sml:179: ML code, not ported *)

(* and the interface *)
let _ = unhide_overloads ();;
