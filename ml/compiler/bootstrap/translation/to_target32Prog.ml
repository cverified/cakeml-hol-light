(* ======================================================== *)
(*  to_target32Prog: ported from HOL4's
    compiler/bootstrap/translation/to_target32ProgScript.sml
    A definition theory, with 1 definition and 7 theorems.  Needed
    by arm7Prog.ml and from_pancake32Prog.ml.  *)
(* ======================================================== *)

(*
  Translate the final part of the compiler backend for 32-bit targets.
*)

needs "compiler/backend/lab_filter.ml";;
needs "compiler/backend/lab_to_target.ml";;
needs "compiler/backend/stack_alloc.ml";;
needs "compiler/backend/stack_names.ml";;
needs "compiler/backend/stack_remove.ml";;
needs "compiler/backend/stack_to_lab.ml";;
needs "compiler/backend/word_to_stack.ml";;
needs "compiler/bootstrap/translation/to_word32Prog.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "compiler/encoders/monadic_enc/monadic_enc.ml";;
needs "compiler/encoders/monadic_enc/monadic_enc32.ml";;
needs "semantics/evaluate.ml";;
needs "translator/ml_translator.ml";;
needs "translator/std_prelude.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "to_target32Prog"
  ["asm"; "evaluate"; "lab_filter"; "lab_to_target"; "ml_monad_translator";
   "ml_translator"; "monadic_enc"; "monadic_enc32"; "stack_alloc";
   "stack_names"; "stack_remove"; "stack_to_lab"; "std_prelude";
   "to_word32Prog"; "word_to_stack"];;

(* HOL4 to_target32ProgScript.sml:12-15: ML code, not ported *)

(* HOL4 to_target32ProgScript.sml:19-20: ML code, not ported *)

(* HOL4 to_target32ProgScript.sml:24: ML code, not ported *)

(* HOL4 to_target32ProgScript.sml:26: ML code, not ported *)

(* HOL4 to_target32ProgScript.sml:28: ML code, not ported *)

(* NOT_NIL_AND_LEMMA[local] *)
let to_target32Prog_NOT_NIL_AND_LEMMA = prove
 (`(~(b = []) /\ x) = if b = [] then F else x`,
  CHEAT_TAC);;

(* HOL4 to_target32ProgScript.sml:36: ML code, not ported *)

(* HOL4 to_target32ProgScript.sml:38-39: ML code, not ported *)

(* HOL4 to_target32ProgScript.sml:41-52: ML code, not ported *)

(* HOL4 to_target32ProgScript.sml:54: ML code, not ported *)

(* HOL4 to_target32ProgScript.sml:56-58: ML code, not ported *)
                (* TODO: This ss messes up defs containing if-then-else
                with constant branches
                |> SIMP_RULE bool_ss [IN_INSERT,NOT_IN_EMPTY]*)
(* HOL4 to_target32ProgScript.sml:62-63: ML code, not ported *)

(* HOL4 to_target32ProgScript.sml:65: ML code, not ported *)

(* HOL4 to_target32ProgScript.sml:67: ML code, not ported *)

(* HOL4 to_target32ProgScript.sml:69: ML code, not ported *)

(* HOL4 to_target32ProgScript.sml:71: ML code, not ported *)

(* HOL4 to_target32ProgScript.sml:73: ML code, not ported *)

(* HOL4 to_target32ProgScript.sml:75: ML code, not ported *)

(* HOL4 to_target32ProgScript.sml:77: ML code, not ported *)

(* HOL4 to_target32ProgScript.sml:79: the ML values that the definitions
   below antiquote *)

(* HOL4 to_target32ProgScript.sml:81: ML code, not ported *)

(* HOL4 to_target32ProgScript.sml:83: ML code, not ported *)

(* HOL4 to_target32ProgScript.sml:85-86: ML code, not ported *)
(* HOL4 to_target32ProgScript.sml:87-88: a theorem that HOL4 states as the
   value of an ML expression: const_words_to_bitmap_ind *)

(* HOL4 to_target32ProgScript.sml:90: ML code, not ported *)

(* TODO: The paired let trips up the translator's single line def mechanism, unable to find a smaller failing example yet *)
(* HOL4 to_target32ProgScript.sml:93: ML code, not ported *)

(* TODO: the name is messed up (pair_) *)
(* HOL4 to_target32ProgScript.sml:96: ML code, not ported *)

(* HOL4 to_target32ProgScript.sml:98: ML code, not ported *)

(* HOL4 to_target32ProgScript.sml:100-102: a theorem that HOL4 states as the
   value of an ML expression: parmove_fstep_side *)

(* HOL4 to_target32ProgScript.sml:104: ML code, not ported *)

(* HOL4 to_target32ProgScript.sml:106: ML code, not ported *)

(* HOL4 to_target32ProgScript.sml:108: ML code, not ported *)

(* HOL4 to_target32ProgScript.sml:110-111: ML code, not ported *)

(* HOL4 to_target32ProgScript.sml:113: ML code, not ported *)

(* HOL4 to_target32ProgScript.sml:115: ML code, not ported *)

(* HOL4 to_target32ProgScript.sml:117: ML code, not ported *)

(* stack_rawcall *)

(* HOL4 to_target32ProgScript.sml:121-127: ML code, not ported *)

(* HOL4 to_target32ProgScript.sml:129: ML code, not ported *)

(* HOL4 to_target32ProgScript.sml:131-136: ML code, not ported *)

(* HOL4 to_target32ProgScript.sml:138-142: ML code, not ported *)

(* HOL4 to_target32ProgScript.sml:144-160: ML code, not ported *)

(* HOL4 to_target32ProgScript.sml:162: ML code, not ported *)

(* HOL4 to_target32ProgScript.sml:164: ML code, not ported *)

(* HOL4 to_target32ProgScript.sml:166: ML code, not ported *)

(* HOL4 to_target32ProgScript.sml:168-189: code that the source has in a
   comment *)

(* HOL4 to_target32ProgScript.sml:191: ML code, not ported *)

(* HOL4 to_target32ProgScript.sml:193-197: ML code, not ported *)

(* HOL4 to_target32ProgScript.sml:199-200: ML code, not ported *)

(* Might be better to inline this *)
(* HOL4 to_target32ProgScript.sml:203-204: ML code, not ported *)

(* HOL4 to_target32ProgScript.sml:206: ML code, not ported *)

(* HOL4 to_target32ProgScript.sml:208: ML code, not ported *)

(* HOL4 to_target32ProgScript.sml:210-212: ML code, not ported *)

(* HOL4 to_target32ProgScript.sml:214: ML code, not ported *)

(* HOL4 to_target32ProgScript.sml:216: ML code, not ported *)

(* HOL4 to_target32ProgScript.sml:218-220: ML code, not ported *)

(* HOL4 to_target32ProgScript.sml:222: ML code, not ported *)

(* HOL4 to_target32ProgScript.sml:224-227: the ML values that the
   definitions below antiquote *)

(* HOL4 to_target32ProgScript.sml:229: ML code, not ported *)

(* HOL4 to_target32ProgScript.sml:231: ML code, not ported *)

(* HOL4 to_target32ProgScript.sml:233: ML code, not ported *)

(* HOL4 to_target32ProgScript.sml:235: ML code, not ported *)

(* HOL4 to_target32ProgScript.sml:237-238: ML code, not ported *)

(* The record types used for the monadic state and exceptions *)
(* HOL4 to_target32ProgScript.sml:241-244: ML code, not ported *)

(* HOL4 to_target32ProgScript.sml:246-251: ML code, not ported *)

(* HOL4 to_target32ProgScript.sml:253-254: ML code, not ported *)

(* HOL4 to_target32ProgScript.sml:256-259: ML code, not ported *)

(* HOL4 to_target32ProgScript.sml:261-269: ML code, not ported *)

(* Initialization *)

(* HOL4 to_target32ProgScript.sml:273-282: ML code, not ported *)

(* HOL4 to_target32ProgScript.sml:284-290: ML code, not ported *)

(* HOL4 to_target32ProgScript.sml:292: ML code, not ported *)

(* HOL4 to_target32ProgScript.sml:294: ML code, not ported *)

(* [local] *)
let monadic_enc32_enc_line_hash_32_ls_side_def = prove
 (`!a b c d e. ~(d = 0) ==>
   monadic_enc32_enc_line_hash_32_ls_side a b c d e <=> T`,
  CHEAT_TAC);;

(* [local] *)
let monadic_enc32_enc_sec_hash_32_ls_side_def = prove
 (`!a b c d e. ~(d = 0) ==>
   monadic_enc32_enc_sec_hash_32_ls_side a b c d e <=> T`,
  CHEAT_TAC);;

(* HOL4 to_target32ProgScript.sml:316-321: a theorem that HOL4 states as the
   value of an ML expression: monadic_enc32_enc_secs_32_side_def *)

(* HOL4 to_target32ProgScript.sml:323: ML code, not ported *)

(* HOL4 to_target32ProgScript.sml:325: ML code, not ported *)

(* [local] *)
let word_2compl_eq = prove
 (`!(w:'a word). --w = (n2w 0) - w`,
  CHEAT_TAC);;

(* HOL4 to_target32ProgScript.sml:333-334: ML code, not ported *)

(* HOL4 to_target32ProgScript.sml:336: ML code, not ported *)

(* HOL4 to_target32ProgScript.sml:338-339: ML code, not ported *)

(* TODO: there may be a better rewrite for aligned (in to_word32Prog's translation of offset_ok) *)

(* HOL4 to_target32ProgScript.sml:343: ML code, not ported *)

(* HOL4 to_target32ProgScript.sml:345-349: ML code, not ported *)

(* Add in hidden argument to compile_lab *)
let remove_labels_hash_def = new_definition
  `to_target32Prog_remove_labels_hash init_clock c pos labs ffis hash_size
  sec_list =
     remove_labels_loop init_clock c pos labs ffis (enc_secs_32
       (asm_config_encode c) hash_size sec_list)`;;

(* [local] *)
let remove_labels_hash_correct = prove
 (`to_target32Prog_remove_labels_hash (lab_to_target_config_init_clock c) ac
  (lab_to_target_config_pos c) (lab_to_target_config_labels c) ffis
  (lab_to_target_config_hash_size c) sec_list =
   remove_labels (lab_to_target_config_init_clock c) ac
     (lab_to_target_config_pos c) (lab_to_target_config_labels c) ffis
     sec_list`,
  CHEAT_TAC);;

(* HOL4 to_target32ProgScript.sml:365: ML code, not ported *)

(* HOL4 to_target32ProgScript.sml:367-368: ML code, not ported *)

(* HOL4 to_target32ProgScript.sml:370-371: ML code, not ported *)

(* HOL4 to_target32ProgScript.sml:373-374: ML code, not ported *)

(* explorer specific functions *)

(* HOL4 to_target32ProgScript.sml:378-386: ML code, not ported *)


(* HOL4 to_target32ProgScript.sml:389: ML code, not ported *)

(* HOL4 to_target32ProgScript.sml:391: ML code, not ported *)

(* and the interface *)
let _ = unhide_overloads ();;
