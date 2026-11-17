(* ======================================================== *)
(*  to_word64Prog: ported from HOL4's
    compiler/bootstrap/translation/to_word64ProgScript.sml
    A definition theory, with 6 definitions and 15 theorems.  Needed
    by to_target64Prog.ml.  *)
(* ======================================================== *)

(*
  Translate the data_to_word part of the 64-bit compiler.
*)

needs "basis/pure/mlstring.ml";;
needs "candle/standard/monadic/holKernel.ml";;
needs "compiler/backend/backend.ml";;
needs "compiler/backend/data_to_word.ml";;
needs "compiler/backend/word_alloc.ml";;
needs "compiler/backend/word_inst.ml";;
needs "compiler/backend/word_simp.ml";;
needs "compiler/bootstrap/translation/printingProg.ml";;
needs "lib/integer_word.ml";;
needs "semantics/typeSystem.ml";;
needs "translator/ml_translator.ml";;
needs "translator/std_prelude.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "to_word64Prog"
  ["backend"; "data_to_word"; "ml_translator"; "printingProg"; "std_prelude";
   "word_alloc"; "word_inst"; "word_simp"];;

(* HOL4 to_word64ProgScript.sml:11-12: ML code, not ported *)

(* HOL4 to_word64ProgScript.sml:16: ML code, not ported *)

(* HOL4 to_word64ProgScript.sml:18-19: ML code, not ported *)

(* HOL4 to_word64ProgScript.sml:21: ML code, not ported *)

(* HOL4 to_word64ProgScript.sml:23: ML code, not ported *)

(* NOT_NIL_AND_LEMMA[local] *)
let to_word64Prog_NOT_NIL_AND_LEMMA = prove
 (`(~(b = []) /\ x) = if b = [] then F else x`,
  CHEAT_TAC);;

(* HOL4 to_word64ProgScript.sml:31: ML code, not ported *)

(* HOL4 to_word64ProgScript.sml:33: ML code, not ported *)

(* HOL4 to_word64ProgScript.sml:35-46: ML code, not ported *)

(* HOL4 to_word64ProgScript.sml:48: ML code, not ported *)

(* HOL4 to_word64ProgScript.sml:50-52: ML code, not ported *)
                (* TODO: This ss messes up defs containing if-then-else
                with constant branches
                |> SIMP_RULE bool_ss [IN_INSERT,NOT_IN_EMPTY]*)
(* HOL4 to_word64ProgScript.sml:56-57: ML code, not ported *)

(* HOL4 to_word64ProgScript.sml:59: ML code, not ported *)

(* HOL4 to_word64ProgScript.sml:61: ML code, not ported *)

(* HOL4 to_word64ProgScript.sml:63: ML code, not ported *)

(* HOL4 to_word64ProgScript.sml:65: ML code, not ported *)

(* HOL4 to_word64ProgScript.sml:67: ML code, not ported *)

(* HOL4 to_word64ProgScript.sml:69: ML code, not ported *)

(* HOL4 to_word64ProgScript.sml:71: ML code, not ported *)

(* HOL4 to_word64ProgScript.sml:73: ML code, not ported *)

(* HOL4 to_word64ProgScript.sml:75: ML code, not ported *)

(* HOL4 to_word64ProgScript.sml:77: ML code, not ported *)

(* HOL4 to_word64ProgScript.sml:79: ML code, not ported *)

(* HOL4 to_word64ProgScript.sml:81: ML code, not ported *)

(* HOL4 to_word64ProgScript.sml:83: ML code, not ported *)

(* HOL4 to_word64ProgScript.sml:85-86: ML code, not ported *)

(* i2w_eq_n2w_lemma[local] *)
let to_word64Prog_i2w_eq_n2w_lemma = prove
 (`i2w (&(k * n)) = n2w (k * n)`,
  CHEAT_TAC);;

(* HOL4 to_word64ProgScript.sml:94-96: a theorem that HOL4 states as the
   value of an ML expression: lemma2 *)

(* HOL4 to_word64ProgScript.sml:98-100: ML code, not ported *)

(* HOL4 to_word64ProgScript.sml:102: ML code, not ported *)

(* HOL4 to_word64ProgScript.sml:104: ML code, not ported *)

(* Manual inlines : shift_def, bytes_in_word because of 'a arg *)
(* HOL4 to_word64ProgScript.sml:107-108: ML code, not ported *)

(* HOL4 to_word64ProgScript.sml:110: ML code, not ported *)

(* check 64 prog is known to be an EqualityType *)
(* HOL4 to_word64ProgScript.sml:113: ML code, not ported *)

(* HOL4 to_word64ProgScript.sml:115: ML code, not ported *)

(* HOL4 to_word64ProgScript.sml:117: ML code, not ported *)

(* HOL4 to_word64ProgScript.sml:119: ML code, not ported *)

(* HOL4 to_word64ProgScript.sml:121: ML code, not ported *)

(* HOL4 to_word64ProgScript.sml:123: ML code, not ported *)

(* HOL4 to_word64ProgScript.sml:125-127: ML code, not ported *)

(* HOL4 to_word64ProgScript.sml:129: the ML values that the definitions
   below antiquote *)

(* assign_rw[local] *)
let to_word64Prog_assign_rw = prove
 (`(i < 0 ==> n2w ((decProg_Tyapp (implode "num") []) (4 * (0 - i))) = n2w
  ((decProg_Tyapp (implode "num") []) (abs (4 * (0 - i))))) /\
   (~(i < 0) ==> n2w ((decProg_Tyapp (implode "num") []) (4 * i)) = n2w
     ((decProg_Tyapp (implode "num") []) (abs (4 * i))))`,
  CHEAT_TAC);;

(* TODO: word_mul should maybe target a real op ?
   TODO: econv might be going too far with case simplification
*)

(* HOL4 to_word64ProgScript.sml:148-151: ML code, not ported *)

(* Smallnum_alt[local] *)
let to_word64Prog_Smallnum_alt = prove
 (`Smallnum i =
   if i < (&0) then (n2w 0) - n2w ((decProg_Tyapp (implode "num") []) (abs
     ((&4) * ((&0) - i))))
            else n2w ((decProg_Tyapp (implode "num") []) (abs ((&4) * i)))`,
  CHEAT_TAC);;

(* HOL4 to_word64ProgScript.sml:161-162: ML code, not ported *)

(* HOL4 to_word64ProgScript.sml:164-173: a theorem that HOL4 states as the
   value of an ML expression: n2mw_ind *)

(* HOL4 to_word64ProgScript.sml:175: ML code, not ported *)

(* HOL4 to_word64ProgScript.sml:177: ML code, not ported *)

(* HOL4 to_word64ProgScript.sml:179-185: ML code, not ported *)

let to_word64Prog_my_lsl_shift_def = new_definition
  `to_word64Prog_my_lsl_shift w n = (w << n)`;;

(* HOL4 to_word64ProgScript.sml:191-195: the ML values that the definitions
   below antiquote *)

(* HOL4 to_word64ProgScript.sml:197: ML code, not ported *)

(* the right hand side is the one that the ML of the source
   computes, computed the same way *)
let to_word64Prog_int_to_words_def = new_definition
  (mk_eq(`to_word64Prog_int_to_words c i offset`,
   rand (concl (SPEC_ALL (el 0 (CONJUNCTS part_to_words_def))))));;


(* the right hand side is the one that the ML of the source
   computes, computed the same way *)
let to_word64Prog_con_to_words_def = new_definition
  (mk_eq(`to_word64Prog_con_to_words c m t ns offset`,
   rand (concl (SPEC_ALL (el 1 (CONJUNCTS part_to_words_def))))));;


(* the right hand side is the one that the ML of the source
   computes, computed the same way *)
let to_word64Prog_w64_to_words_def = new_definition
  (mk_eq(`to_word64Prog_w64_to_words c w offset`,
   rand (concl (SPEC_ALL (el 2 (CONJUNCTS part_to_words_def))))));;


(* the right hand side is the one that the ML of the source
   computes, computed the same way *)
let to_word64Prog_str_to_words_def = new_definition
  (mk_eq(`to_word64Prog_str_to_words c s offset`,
   rand (concl (SPEC_ALL (el 3 (CONJUNCTS part_to_words_def))))));;


let to_word64Prog_part_to_words_def =
  REWRITE_RULE [GSYM to_word64Prog_int_to_words_def; GSYM
  to_word64Prog_con_to_words_def; GSYM to_word64Prog_w64_to_words_def; GSYM
  to_word64Prog_str_to_words_def] part_to_words_def;;

let to_word64Prog_bytes_of_string_def = new_definition
  `to_word64Prog_bytes_of_string cs = MAP (\c. n2w (ORD c):word8) (explode
  cs)`;;

(* HOL4 to_word64ProgScript.sml:234: ML code, not ported *)

(* HOL4 to_word64ProgScript.sml:236-240: ML code, not ported *)

(* HOL4 to_word64ProgScript.sml:242-246: ML code, not ported *)

(* HOL4 to_word64ProgScript.sml:248-252: ML code, not ported *)

(* HOL4 to_word64ProgScript.sml:254-261: ML code, not ported *)

(* HOL4 to_word64ProgScript.sml:263: ML code, not ported *)

(* HOL4 to_word64ProgScript.sml:265-267: ML code, not ported *)

(* HOL4 to_word64ProgScript.sml:269-270: ML code, not ported *)

(* HOL4 to_word64ProgScript.sml:272-275: ML code, not ported *)

(* HOL4 to_word64ProgScript.sml:277-280: ML code, not ported *)

(* HOL4 to_word64ProgScript.sml:282-286: ML code, not ported *)

(* HOL4 to_word64ProgScript.sml:288-289: ML code, not ported *)

(* lemma[local] *)
let to_word64Prog_lemma = prove
 (`!A B. A = B ==> ~(B = A) ==> F`,
  CHEAT_TAC);;

(* HOL4 to_word64ProgScript.sml:297-310: code that the source has in a
   comment *)

(* HOL4 to_word64ProgScript.sml:312-313: ML code, not ported *)

(* HOL4 to_word64ProgScript.sml:315-316: a theorem that HOL4 states as the
   value of an ML expression: comp_ind *)
(* Inlines the let k = 8 manually *)
(* HOL4 to_word64ProgScript.sml:318: ML code, not ported *)

(* HOL4 to_word64ProgScript.sml:320: ML code, not ported *)

(* HOL4 to_word64ProgScript.sml:322-323: the ML values that the definitions
   below antiquote *)

(* HOL4 to_word64ProgScript.sml:325: ML code, not ported *)

(* HOL4 to_word64ProgScript.sml:327-329: ML code, not ported *)

(* HOL4 to_word64ProgScript.sml:331-332: ML code, not ported *)

(* word_cse_ind[local] *)
let to_word64Prog_word_cse_ind = prove
 (`word_cse_word_cse_ind`,
  CHEAT_TAC);;
(* HOL4 to_word64ProgScript.sml:345: ML code, not ported *)

(* HOL4 to_word64ProgScript.sml:347: ML code, not ported *)

(* HOL4 to_word64ProgScript.sml:349: ML code, not ported *)

(* HOL4 to_word64ProgScript.sml:351: ML code, not ported *)

(* misc_anub_ind[local] *)
let to_word64Prog_misc_anub_ind = prove
 (`misc_anub_ind (:'a) (:'b)`,
  CHEAT_TAC);;

(* HOL4 to_word64ProgScript.sml:366: ML code, not ported *)

(* HOL4 to_word64ProgScript.sml:368: ML code, not ported *)

(* HOL4 to_word64ProgScript.sml:370: ML code, not ported *)

(* rws[local] *)
let to_word64Prog_rws = prove
 (`((+) = (\x y. x + y)) /\
   ((&&) = (\x y. x && y)) /\
   ((||) = (\x y. x || y)) /\
   ((??) = (\x y. x ?? y))`,
  CHEAT_TAC);;

(* HOL4 to_word64ProgScript.sml:381: ML code, not ported *)

(* word_msb_rw[local] *)
let to_word64Prog_word_msb_rw = prove
 (`word_msb (a:word64) <=> ~((a >>> 63) = (n2w 0))`,
  CHEAT_TAC);;

(* HOL4 to_word64ProgScript.sml:392: ML code, not ported *)

(* HOL4 to_word64ProgScript.sml:394-397: a theorem that HOL4 states as the
   value of an ML expression: arith_shift_right_ind *)

(* HOL4 to_word64ProgScript.sml:399-402: ML code, not ported *)

(* HOL4 to_word64ProgScript.sml:404: ML code, not ported *)

(* HOL4 to_word64ProgScript.sml:406-409: ML code, not ported *)

(* HOL4 to_word64ProgScript.sml:411: ML code, not ported *)

(* TODO: remove when pmatch is fixed *)
(* HOL4 to_word64ProgScript.sml:414: ML code, not ported *)

(* HOL4 to_word64ProgScript.sml:416-421: ML code, not ported *)

(* HOL4 to_word64ProgScript.sml:423: ML code, not ported *)

(* HOL4 to_word64ProgScript.sml:425-426: ML code, not ported *)

(* HOL4 to_word64ProgScript.sml:428: ML code, not ported *)

(* HOL4 to_word64ProgScript.sml:430-432: ML code, not ported *)

(* inst_select_exp_ind[local] *)
let to_word64Prog_inst_select_exp_ind = prove
 (`word_inst_inst_select_exp_ind`,
  CHEAT_TAC);;

(* HOL4 to_word64ProgScript.sml:460: ML code, not ported *)

(* HOL4 to_word64ProgScript.sml:462: ML code, not ported *)

(* HOL4 to_word64ProgScript.sml:464: ML code, not ported *)

(* HOL4 to_word64ProgScript.sml:466: ML code, not ported *)

(* HOL4 to_word64ProgScript.sml:468-474: a theorem that HOL4 states as the
   value of an ML expression: word_inst_pull_exp_side *)

(* HOL4 to_word64ProgScript.sml:476: ML code, not ported *)

(* HOL4 to_word64ProgScript.sml:478-479: ML code, not ported *)

(* HOL4 to_word64ProgScript.sml:481-482: ML code, not ported *)

(* HOL4 to_word64ProgScript.sml:484-485: ML code, not ported *)

(* HOL4 to_word64ProgScript.sml:487-489: ML code, not ported *)

(* lem[local] *)
let to_word64Prog_lem = prove
 (`dimindex (:64) = 64 /\
   dimindex (:32) = 32`,
  CHEAT_TAC);;

(* HOL4 to_word64ProgScript.sml:498-499: ML code, not ported *)

(* HOL4 to_word64ProgScript.sml:501-504: ML code, not ported *)

(* HOL4 to_word64ProgScript.sml:506-543: code that the source has in a
   comment *)

(* HOL4 to_word64ProgScript.sml:545-546: ML code, not ported *)

(* HOL4 to_word64ProgScript.sml:548-588: code that the source has in a
   comment *)

(* HOL4 to_word64ProgScript.sml:590-591: ML code, not ported *)

(* HOL4 to_word64ProgScript.sml:593-622: code that the source has in a
   comment *)

(* HOL4 to_word64ProgScript.sml:624-643: code that the source has in a
   comment *)

(* HOL4 to_word64ProgScript.sml:645-649: code that the source has in a
   comment *)

(* HOL4 to_word64ProgScript.sml:651-671: ML code, not ported *)

(* HOL4 to_word64ProgScript.sml:673-675: ML code, not ported *)

(* HOL4 to_word64ProgScript.sml:677-681: ML code, not ported *)

(* HOL4 to_word64ProgScript.sml:683-684: ML code, not ported *)

(* HOL4 to_word64ProgScript.sml:686-687: ML code, not ported *)


(* HOL4 to_word64ProgScript.sml:690-691: ML code, not ported *)

(* HOL4 to_word64ProgScript.sml:693: ML code, not ported *)

(* HOL4 to_word64ProgScript.sml:695-701: ML code, not ported *)


(* explorer specific functions *)

(* HOL4 to_word64ProgScript.sml:706-718: ML code, not ported *)

(* HOL4 to_word64ProgScript.sml:720-723: ML code, not ported *)

(* HOL4 to_word64ProgScript.sml:725: ML code, not ported *)


(* HOL4 to_word64ProgScript.sml:728: ML code, not ported *)

(* HOL4 to_word64ProgScript.sml:730: ML code, not ported *)

(* and the interface *)
let _ = unhide_overloads ();;
