(* ======================================================== *)
(*  to_word32Prog: ported from HOL4's
    compiler/bootstrap/translation/to_word32ProgScript.sml
    A definition theory, with 6 definitions and 16 theorems.  Needed
    by to_target32Prog.ml.  *)
(* ======================================================== *)

(*
  Translate the data_to_word part of the 32-bit compiler.
*)

needs "basis/pure/mlstring.ml";;
needs "compiler/backend/backend.ml";;
needs "compiler/backend/data_to_word.ml";;
needs "compiler/backend/word_alloc.ml";;
needs "compiler/backend/word_inst.ml";;
needs "compiler/backend/word_simp.ml";;
needs "compiler/bootstrap/translation/basis_defProg.ml";;
needs "lib/integer_word.ml";;
needs "translator/ml_translator.ml";;
needs "translator/std_prelude.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "to_word32Prog"
  ["backend"; "basis_defProg"; "data_to_word"; "ml_translator";
   "std_prelude"; "word_alloc"; "word_inst"; "word_simp"];;

(* HOL4 to_word32ProgScript.sml:11-12: ML code, not ported *)

(* HOL4 to_word32ProgScript.sml:16: ML code, not ported *)

(* HOL4 to_word32ProgScript.sml:18-19: ML code, not ported *)

(* HOL4 to_word32ProgScript.sml:21: ML code, not ported *)

(* HOL4 to_word32ProgScript.sml:23: ML code, not ported *)

(* NOT_NIL_AND_LEMMA[local] *)
let to_word32Prog_NOT_NIL_AND_LEMMA = prove
 (`(~(b = []) /\ x) = if b = [] then F else x`,
  CHEAT_TAC);;

(* HOL4 to_word32ProgScript.sml:31: ML code, not ported *)

(* HOL4 to_word32ProgScript.sml:33: ML code, not ported *)

(* HOL4 to_word32ProgScript.sml:35-46: ML code, not ported *)

(* HOL4 to_word32ProgScript.sml:48: ML code, not ported *)

(* HOL4 to_word32ProgScript.sml:50-52: ML code, not ported *)
                (* TODO: This ss messes up defs containing if-then-else
                with constant branches
                |> SIMP_RULE bool_ss [IN_INSERT,NOT_IN_EMPTY]*)
(* HOL4 to_word32ProgScript.sml:56-57: ML code, not ported *)

(* HOL4 to_word32ProgScript.sml:59: ML code, not ported *)

(* HOL4 to_word32ProgScript.sml:61: ML code, not ported *)

(* HOL4 to_word32ProgScript.sml:63: ML code, not ported *)

(* HOL4 to_word32ProgScript.sml:65: ML code, not ported *)

(* HOL4 to_word32ProgScript.sml:67: ML code, not ported *)

(* HOL4 to_word32ProgScript.sml:69: ML code, not ported *)

(* HOL4 to_word32ProgScript.sml:71: ML code, not ported *)

(* HOL4 to_word32ProgScript.sml:73: ML code, not ported *)

(* HOL4 to_word32ProgScript.sml:75: ML code, not ported *)

(* HOL4 to_word32ProgScript.sml:77: ML code, not ported *)

(* HOL4 to_word32ProgScript.sml:79: ML code, not ported *)

(* HOL4 to_word32ProgScript.sml:81: ML code, not ported *)

(* HOL4 to_word32ProgScript.sml:83: ML code, not ported *)

(* HOL4 to_word32ProgScript.sml:85-86: ML code, not ported *)

(* [local] *)
let i2w_eq_n2w_lemma = prove
 (`i2w (&(k * n)) = n2w (k * n)`,
  CHEAT_TAC);;

(* HOL4 to_word32ProgScript.sml:94-96: a theorem that HOL4 states as the
   value of an ML expression: lemma2 *)

(* HOL4 to_word32ProgScript.sml:98-100: ML code, not ported *)

(* HOL4 to_word32ProgScript.sml:102: ML code, not ported *)

(* HOL4 to_word32ProgScript.sml:104: ML code, not ported *)

(* Manual inlines : shift_def, bytes_in_word because of 'a arg *)
(* HOL4 to_word32ProgScript.sml:107-108: ML code, not ported *)

(* HOL4 to_word32ProgScript.sml:110: ML code, not ported *)

(* check 32 prog is known to be an EqualityType *)
(* HOL4 to_word32ProgScript.sml:113: ML code, not ported *)

(* HOL4 to_word32ProgScript.sml:115: ML code, not ported *)

(* HOL4 to_word32ProgScript.sml:117: ML code, not ported *)

(* HOL4 to_word32ProgScript.sml:119: ML code, not ported *)

(* HOL4 to_word32ProgScript.sml:121: ML code, not ported *)

(* HOL4 to_word32ProgScript.sml:123: ML code, not ported *)

(* HOL4 to_word32ProgScript.sml:125-127: ML code, not ported *)

(* HOL4 to_word32ProgScript.sml:129: the ML values that the definitions
   below antiquote *)

(* [local] *)
let assign_rw = prove
 (`(i < 0 ==> n2w ((decProg_Tyapp (implode "num") []) (4 * (0 - i))) = n2w
  ((decProg_Tyapp (implode "num") []) (abs (4 * (0 - i))))) /\
   (~(i < 0) ==> n2w ((decProg_Tyapp (implode "num") []) (4 * i)) = n2w
     ((decProg_Tyapp (implode "num") []) (abs (4 * i))))`,
  CHEAT_TAC);;

(* TODO: word_mul should maybe target a real op ?
   TODO: econv might be going too far with case simplification
*)

(* HOL4 to_word32ProgScript.sml:148-150: ML code, not ported *)

(* HOL4 to_word32ProgScript.sml:152-154: ML code, not ported *)

(* Smallnum_alt[local] *)
let smallnum_alt = prove
 (`Smallnum i =
   if i < (&0) then (n2w 0) - n2w ((decProg_Tyapp (implode "num") []) (abs
     ((&4) * ((&0) - i))))
            else n2w ((decProg_Tyapp (implode "num") []) (abs ((&4) * i)))`,
  CHEAT_TAC);;

(* HOL4 to_word32ProgScript.sml:164-165: ML code, not ported *)

(* HOL4 to_word32ProgScript.sml:167-176: a theorem that HOL4 states as the
   value of an ML expression: n2mw_ind *)

(* HOL4 to_word32ProgScript.sml:178: ML code, not ported *)

(* HOL4 to_word32ProgScript.sml:180: ML code, not ported *)

(* HOL4 to_word32ProgScript.sml:182-188: ML code, not ported *)

let my_lsl_shift_def = new_definition
  `to_word32Prog_my_lsl_shift w n = (w << n)`;;

(* HOL4 to_word32ProgScript.sml:194-198: the ML values that the definitions
   below antiquote *)

(* HOL4 to_word32ProgScript.sml:200: ML code, not ported *)

(* PORT FAILED: Definition int_to_words_def: expected ')' but found '|>' at
   72 *)
(* HOL4 to_word32ProgScript.sml:202-206: the definition *)

(* PORT FAILED: Definition con_to_words_def: expected ')' but found '|>' at
   77 *)
(* HOL4 to_word32ProgScript.sml:208-212: the definition *)

(* PORT FAILED: Definition w64_to_words_def: expected ')' but found '|>' at
   72 *)
(* HOL4 to_word32ProgScript.sml:214-218: the definition *)

(* PORT FAILED: Definition str_to_words_def: expected ')' but found '|>' at
   72 *)
(* HOL4 to_word32ProgScript.sml:220-224: the definition *)

let to_word32Prog_part_to_words_def =
  REWRITE_RULE [GSYM int_to_words_def; GSYM con_to_words_def; GSYM
  w64_to_words_def; GSYM str_to_words_def] part_to_words_def;;

let word_extract_lemma = prove
 (`(((63 >< 32) (w:word64)):word32) = w2w (w >> 32) /\
   (((31 >< 0) (w:word64)):word32) = w2w w`,
  CHEAT_TAC);;

let bytes_of_string_def = new_definition
  `to_word32Prog_bytes_of_string cs = MAP (\c. n2w (ORD c):word8) (explode
  cs)`;;

(* HOL4 to_word32ProgScript.sml:244: ML code, not ported *)

(* HOL4 to_word32ProgScript.sml:246-250: ML code, not ported *)

(* HOL4 to_word32ProgScript.sml:252-256: ML code, not ported *)

(* HOL4 to_word32ProgScript.sml:258-262: ML code, not ported *)

(* HOL4 to_word32ProgScript.sml:264-271: ML code, not ported *)

(* HOL4 to_word32ProgScript.sml:273: ML code, not ported *)

(* HOL4 to_word32ProgScript.sml:275-277: ML code, not ported *)

(* HOL4 to_word32ProgScript.sml:279-280: ML code, not ported *)

(* HOL4 to_word32ProgScript.sml:282-285: ML code, not ported *)

(* HOL4 to_word32ProgScript.sml:287-290: ML code, not ported *)

(* HOL4 to_word32ProgScript.sml:292-296: ML code, not ported *)

(* HOL4 to_word32ProgScript.sml:298-299: ML code, not ported *)

(* lemma[local] *)
let to_word32Prog_lemma = prove
 (`!A B. A = B ==> ~(B = A) ==> F`,
  CHEAT_TAC);;

(* HOL4 to_word32ProgScript.sml:307-320: code that the source has in a
   comment *)

(* HOL4 to_word32ProgScript.sml:322-323: ML code, not ported *)

(* HOL4 to_word32ProgScript.sml:325-326: a theorem that HOL4 states as the
   value of an ML expression: comp_ind *)
(* Inlines the let k = 8 manually *)
(* HOL4 to_word32ProgScript.sml:328: ML code, not ported *)

(* HOL4 to_word32ProgScript.sml:330: ML code, not ported *)

(* HOL4 to_word32ProgScript.sml:332: the ML values that the definitions
   below antiquote *)

(* HOL4 to_word32ProgScript.sml:334: ML code, not ported *)

(* HOL4 to_word32ProgScript.sml:336-338: ML code, not ported *)

(* HOL4 to_word32ProgScript.sml:340-341: ML code, not ported *)

(* [local] *)
let word_cse_ind = prove
 (`word_cse_word_cse_ind`,
  CHEAT_TAC);;
(* HOL4 to_word32ProgScript.sml:354: ML code, not ported *)

(* HOL4 to_word32ProgScript.sml:356: ML code, not ported *)

(* HOL4 to_word32ProgScript.sml:358: ML code, not ported *)

(* HOL4 to_word32ProgScript.sml:360: ML code, not ported *)

(* [local] *)
let misc_anub_ind = prove
 (`misc_anub_ind (:'a) (:'b)`,
  CHEAT_TAC);;

(* HOL4 to_word32ProgScript.sml:375: ML code, not ported *)

(* HOL4 to_word32ProgScript.sml:377: ML code, not ported *)

(* HOL4 to_word32ProgScript.sml:379: ML code, not ported *)

(* [local] *)
let rws = prove
 (`((+) = (\x y. x + y)) /\
   ((&&) = (\x y. x && y)) /\
   ((||) = (\x y. x || y)) /\
   ((??) = (\x y. x ?? y))`,
  CHEAT_TAC);;

(* HOL4 to_word32ProgScript.sml:390: ML code, not ported *)

(* [local] *)
let word_msb_rw = prove
 (`word_msb (a:word32) <=> ~((a >>> 31) = (n2w 0))`,
  CHEAT_TAC);;

(* HOL4 to_word32ProgScript.sml:401: ML code, not ported *)

(* HOL4 to_word32ProgScript.sml:403-406: a theorem that HOL4 states as the
   value of an ML expression: arith_shift_right_ind *)

(* HOL4 to_word32ProgScript.sml:408-411: ML code, not ported *)

(* HOL4 to_word32ProgScript.sml:413-416: ML code, not ported *)

(* HOL4 to_word32ProgScript.sml:418: ML code, not ported *)

(* TODO: remove when pmatch is fixed *)
(* HOL4 to_word32ProgScript.sml:421: ML code, not ported *)

(* HOL4 to_word32ProgScript.sml:423-428: ML code, not ported *)

(* HOL4 to_word32ProgScript.sml:430: ML code, not ported *)

(* HOL4 to_word32ProgScript.sml:432-433: ML code, not ported *)

(* HOL4 to_word32ProgScript.sml:435: ML code, not ported *)

(* HOL4 to_word32ProgScript.sml:437-439: ML code, not ported *)

(* [local] *)
let inst_select_exp_ind = prove
 (`word_inst_inst_select_exp_ind`,
  CHEAT_TAC);;

(* HOL4 to_word32ProgScript.sml:467: ML code, not ported *)

(* HOL4 to_word32ProgScript.sml:469: ML code, not ported *)

(* HOL4 to_word32ProgScript.sml:471: ML code, not ported *)

(* HOL4 to_word32ProgScript.sml:473: ML code, not ported *)

(* HOL4 to_word32ProgScript.sml:475-481: a theorem that HOL4 states as the
   value of an ML expression: word_inst_pull_exp_side *)

(* HOL4 to_word32ProgScript.sml:483: ML code, not ported *)

(* HOL4 to_word32ProgScript.sml:485-486: ML code, not ported *)

(* HOL4 to_word32ProgScript.sml:488-489: ML code, not ported *)

(* HOL4 to_word32ProgScript.sml:491-492: ML code, not ported *)

(* HOL4 to_word32ProgScript.sml:494-496: ML code, not ported *)

(* [local] *)
let lem = prove
 (`dimindex (:64) = 64 /\
   dimindex (:32) = 32`,
  CHEAT_TAC);;

(* HOL4 to_word32ProgScript.sml:505-506: ML code, not ported *)

(* HOL4 to_word32ProgScript.sml:508-511: ML code, not ported *)

(* HOL4 to_word32ProgScript.sml:513-551: code that the source has in a
   comment *)

(* HOL4 to_word32ProgScript.sml:553-554: ML code, not ported *)

(* HOL4 to_word32ProgScript.sml:556-596: code that the source has in a
   comment *)

(* HOL4 to_word32ProgScript.sml:598-599: ML code, not ported *)

(* HOL4 to_word32ProgScript.sml:601-630: code that the source has in a
   comment *)

(* HOL4 to_word32ProgScript.sml:632-651: code that the source has in a
   comment *)

(* HOL4 to_word32ProgScript.sml:653-657: code that the source has in a
   comment *)

(* HOL4 to_word32ProgScript.sml:659-679: ML code, not ported *)

(* HOL4 to_word32ProgScript.sml:681-683: ML code, not ported *)

(* HOL4 to_word32ProgScript.sml:685-689: ML code, not ported *)

(* HOL4 to_word32ProgScript.sml:691-692: ML code, not ported *)

(* HOL4 to_word32ProgScript.sml:694-695: ML code, not ported *)

(* HOL4 to_word32ProgScript.sml:697-698: ML code, not ported *)

(* HOL4 to_word32ProgScript.sml:700: ML code, not ported *)

(* HOL4 to_word32ProgScript.sml:702-708: ML code, not ported *)

(* explorer specific functions *)

(* HOL4 to_word32ProgScript.sml:712-724: ML code, not ported *)

(* HOL4 to_word32ProgScript.sml:726-729: ML code, not ported *)

(* HOL4 to_word32ProgScript.sml:731: ML code, not ported *)


(* HOL4 to_word32ProgScript.sml:734: ML code, not ported *)

(* HOL4 to_word32ProgScript.sml:736: ML code, not ported *)

(* and the interface *)
let _ = unhide_overloads ();;
