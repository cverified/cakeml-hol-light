(* ======================================================== *)
(*  backend_32_cv: ported from HOL4's
    cv_translator/backend_32_cvScript.sml
    A definition theory, with no definitions and 30 theorems.
    Needed by backend_ag32_cv.ml.  *)
(* ======================================================== *)

(*
  Translate arch-size-specific functions to cv equations.
*)

(* The following line is (and shall remain) the only difference between
   the 32-bit and 64-bit versions of this file. *)

needs "characteristic/cfFFIType.ml";;
needs "compiler/backend/backend.ml";;
needs "compiler/backend/lab_to_target.ml";;
needs "cv_translator/backend_cv.ml";;
needs "cv_translator/to_data_cv.ml";;
needs "lib/cv_std.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "backend_32_cv"
  ["backend"; "backend_cv"; "to_data_cv"];;

let _ = do_list hide_constant ["ABS"; "Num"];;

(* HOL4 backend_32_cvScript.sml:13: ML code, not ported *)

(* HOL4 backend_32_cvScript.sml:15-16: ML code, not ported *)

(* HOL4 backend_32_cvScript.sml:18: ML code, not ported *)

(* HOL4 backend_32_cvScript.sml:20: the overload Num, which the port expands *)
(* HOL4 backend_32_cvScript.sml:21: the overload Pair, which the port
   expands *)

(* HOL4 backend_32_cvScript.sml:23-28: ML code, not ported *)

(* HOL4 backend_32_cvScript.sml:30: ML code, not ported *)
(* [cv_pre] *)
let lab_to_target_upd_lab_len_pre = prove
 (`!pos v. lab_to_target_upd_lab_len_pre pos v`,
  CHEAT_TAC);;

(* HOL4 backend_32_cvScript.sml:37: ML code, not ported *)

(* HOL4 backend_32_cvScript.sml:39: ML code, not ported *)
(* [cv_pre,local] *)
let lab_to_target_pad_section_pre = prove
 (`!nop v aux. lab_to_target_pad_section_pre nop v aux`,
  CHEAT_TAC);;

(* HOL4 backend_32_cvScript.sml:46: ML code, not ported *)

(* [local] *)
let to_shmem_info_num = prove
 (`mk_shmem_info_num ep nb ar ao r ex = shmem_info_num ep nb ar ao r ex`,
  CHEAT_TAC);;

(* HOL4 backend_32_cvScript.sml:60-61: ML code, not ported *)

(* [cv_pre] *)
let lab_to_target_get_shmem_info_pre = prove
 (`!v pos ffi_names' shmem_info.
     lab_to_target_get_shmem_info_pre v pos ffi_names' shmem_info`,
  CHEAT_TAC);;

(* HOL4 backend_32_cvScript.sml:71-72: a theorem that HOL4 states as the
   value of an ML expression: bytes_in_word_def *)

(* HOL4 backend_32_cvScript.sml:74-75: a theorem that HOL4 states as the
   value of an ML expression: shift_def *)

(* HOL4 backend_32_cvScript.sml:77-79: ML code, not ported *)

(* HOL4 backend_32_cvScript.sml:81-82: ML code, not ported *)

(* HOL4 backend_32_cvScript.sml:84: ML code, not ported *)
(* [cv_pre,local] *)
let stack_to_lab_flatten_pre = prove
 (`!t p n m cs bs. stack_to_lab_flatten_pre t p n m cs bs`,
  CHEAT_TAC);;

(* HOL4 backend_32_cvScript.sml:91-122: a proof *)

(* HOL4 backend_32_cvScript.sml:124-152: ML code, not ported *)

(* HOL4 backend_32_cvScript.sml:154: ML code, not ported *)
(* [cv_pre,local] *)
let stack_alloc_comp_pre = prove
 (`!n m p. stack_alloc_comp_pre n m p`,
  CHEAT_TAC);;

(* HOL4 backend_32_cvScript.sml:161-163: ML code, not ported *)

(* HOL4 backend_32_cvScript.sml:165-182: ML code, not ported *)

(* [local] *)
let cv_DROP_lemma = prove
 (`!n cv_xs. cv_size (cv_DROP (Num n) cv_xs) <= cv_size cv_xs`,
  CHEAT_TAC);;

(* HOL4 backend_32_cvScript.sml:193-199: a proof *)

(* HOL4 backend_32_cvScript.sml:201-220: ML code, not ported *)

(* [cv_rep] *)
let cv_rep_if_lt = prove
 (`cv_rep p1a c1a Num m /\
   cv_rep p1b c1b Num n /\
   cv_rep p2 c2 f t /\
   cv_rep p3 c3 f e ==>
   cv_rep (p1a /\ p1b /\ (m < n ==> p2) /\ (~(m < n) ==> p3))
          (cv_if (cv_sub c1b c1a) c2 c3) f (if m < n then t else e)`,
  CHEAT_TAC);;

(* HOL4 backend_32_cvScript.sml:234-236: a proof *)

(* HOL4 backend_32_cvScript.sml:238: ML code, not ported *)

(* HOL4 backend_32_cvScript.sml:240: ML code, not ported *)
(* [cv_pre] *)
let wordLang_max_var_exp_pre = prove
 (`(!v. wordLang_max_var_exp_pre v) /\
   (!v. backend_cv_max_var_exp_list_pre v)`,
  CHEAT_TAC);;

(* HOL4 backend_32_cvScript.sml:248: ML code, not ported *)

(* HOL4 backend_32_cvScript.sml:250: ML code, not ported *)
(* [cv_pre] *)
let backend_cv_every_stack_var'_pre = prove
 (`!v m. backend_cv_every_stack_var'_pre m v`,
  CHEAT_TAC);;

(* HOL4 backend_32_cvScript.sml:259-260: ML code, not ported *)

(* HOL4 backend_32_cvScript.sml:262: ML code, not ported *)
(* [cv_pre] *)
let backend_cv_apply_colour_exp'_pre = prove
 (`(!v colour. backend_cv_apply_colour_exp'_pre colour v) /\
   (!v colour. backend_cv_apply_colour_exp'_list_pre colour v)`,
  CHEAT_TAC);;

(* HOL4 backend_32_cvScript.sml:270: ML code, not ported *)
(* [cv_pre] *)
let apply_colour'_pre = prove
 (`!v colour. backend_cv_apply_colour'_pre colour v`,
  CHEAT_TAC);;

(* HOL4 backend_32_cvScript.sml:279: ML code, not ported *)

(* HOL4 backend_32_cvScript.sml:281: ML code, not ported *)
(* [cv_pre] *)
let word_alloc_get_reads_exp_pre = prove
 (`(!v. word_alloc_get_reads_exp_pre v) /\
   (!v. backend_cv_get_reads_exp_list_pre v)`,
  CHEAT_TAC);;

(* HOL4 backend_32_cvScript.sml:289-291: ML code, not ported *)

(* HOL4 backend_32_cvScript.sml:293: ML code, not ported *)
(* [cv_pre] *)
let word_alloc_remove_dead_pre = prove
 (`!v live nlive lt. word_alloc_remove_dead_pre v live nlive lt`,
  CHEAT_TAC);;

(* HOL4 backend_32_cvScript.sml:300: ML code, not ported *)

(* HOL4 backend_32_cvScript.sml:302: ML code, not ported *)

(* HOL4 backend_32_cvScript.sml:304: ML code, not ported *)

(* HOL4 backend_32_cvScript.sml:306: ML code, not ported *)

(* HOL4 backend_32_cvScript.sml:308: ML code, not ported *)
let optimize_consts_pre = prove
 (`!op ls. ~(op = word_bignum_Sub) ==> word_inst_optimize_consts_pre op ls`,
  CHEAT_TAC);;

(* HOL4 backend_32_cvScript.sml:319: ML code, not ported *)

(* HOL4 backend_32_cvScript.sml:321: ML code, not ported *)
(* [cv_pre] *)
let word_inst_pull_exp_pre = prove
 (`(!v. word_inst_pull_exp_pre v) /\
   (!v. backend_cv_pull_exp_list_pre v)`,
  CHEAT_TAC);;

(* HOL4 backend_32_cvScript.sml:331: ML code, not ported *)
(* [cv_pre] *)
let word_inst_flatten_exp_pre = prove
 (`(!v. word_inst_flatten_exp_pre v) /\
   (!v. backend_cv_flatten_exp_list_pre v)`,
  CHEAT_TAC);;

(* HOL4 backend_32_cvScript.sml:344: ML code, not ported *)

(* HOL4 backend_32_cvScript.sml:346: ML code, not ported *)

(* HOL4 backend_32_cvScript.sml:348-359: ML code, not ported *)

(* HOL4 backend_32_cvScript.sml:361-363: ML code, not ported *)

(* HOL4 backend_32_cvScript.sml:365: ML code, not ported *)
(* [cv_pre,local] *)
let word_alloc_ssa_cc_trans_exp_pre = prove
 (`(!v t. word_alloc_ssa_cc_trans_exp_pre t v) /\
   (!v t. backend_cv_ssa_cc_trans_exp_list_pre t v)`,
  CHEAT_TAC);;

(* HOL4 backend_32_cvScript.sml:373: ML code, not ported *)
(* [cv_pre] *)
let word_alloc_ssa_cc_trans_pre = prove
 (`!v ssa na lt. word_alloc_ssa_cc_trans_pre v ssa na lt`,
  CHEAT_TAC);;

(* HOL4 backend_32_cvScript.sml:380: ML code, not ported *)

(* HOL4 backend_32_cvScript.sml:382-387: ML code, not ported *)

(* HOL4 backend_32_cvScript.sml:389: ML code, not ported *)
(* [cv_pre,local] *)
let word_simp_const_fp_exp_pre = prove
 (`(!t v. word_simp_const_fp_exp_pre t v) /\
   (!t v. backend_cv_const_fp_exp_list_pre t v)`,
  CHEAT_TAC);;

(* HOL4 backend_32_cvScript.sml:397: ML code, not ported *)
(* [cv_pre,local] *)
let word_simp_const_fp_loop_pre = prove
 (`!v cs. word_simp_const_fp_loop_pre v cs`,
  CHEAT_TAC);;

(* HOL4 backend_32_cvScript.sml:404-411: ML code, not ported *)

(* HOL4 backend_32_cvScript.sml:413-453: ML code, not ported *)

(* HOL4 backend_32_cvScript.sml:455-456: ML code, not ported *)

(* HOL4 backend_32_cvScript.sml:458-460: ML code, not ported *)

(* HOL4 backend_32_cvScript.sml:462-465: a proof *)
(* [cv_pre] *)
let multiword_2mw_pre = prove
 (`!n. multiword_n2mw_pre n`,
  CHEAT_TAC);;

(* lemma[local] *)
let backend_32_cv_lemma = prove
 (`!i. Num (abs i) = Num i`,
  CHEAT_TAC);;

(* HOL4 backend_32_cvScript.sml:479: ML code, not ported *)

(* HOL4 backend_32_cvScript.sml:481-493: ML code, not ported *)

(* [local] *)
let cv_getWords_lemma = prove
 (`!g acc. cv_size (cv_snd (cv_data_to_word_getWords g acc)) <= cv_size g`,
  CHEAT_TAC);;

(* HOL4 backend_32_cvScript.sml:506-513: a proof *)

(* [cv_pre] *)
let data_to_word_StoreAnyConsts_pre = prove
 (`!r1 r2 r3 v v0. data_to_word_StoreAnyConsts_pre r1 r2 r3 v v0`,
  CHEAT_TAC);;

(* HOL4 backend_32_cvScript.sml:521-523: ML code, not ported *)

(* HOL4 backend_32_cvScript.sml:525-527: ML code, not ported *)

(* HOL4 backend_32_cvScript.sml:529-535: a theorem that HOL4 states as the
   value of an ML expression: inline *)

(* HOL4 backend_32_cvScript.sml:537-539: ML code, not ported *)

(* HOL4 backend_32_cvScript.sml:541-545: ML code, not ported *)

(* HOL4 backend_32_cvScript.sml:547: ML code, not ported *)

(* HOL4 backend_32_cvScript.sml:549-553: ML code, not ported *)

(* HOL4 backend_32_cvScript.sml:555: ML code, not ported *)

(* HOL4 backend_32_cvScript.sml:557: ML code, not ported *)
(* [cv_pre,local] *)
let data_to_word_comp_pre = prove
 (`!c secn l p. data_to_word_comp_pre c secn l p`,
  CHEAT_TAC);;

(* HOL4 backend_32_cvScript.sml:565-566: ML code, not ported *)

(* HOL4 backend_32_cvScript.sml:568-569: ML code, not ported *)

(* HOL4 backend_32_cvScript.sml:571-577: ML code, not ported *)

(* HOL4 backend_32_cvScript.sml:579: ML code, not ported *)
(* [cv_pre] *)
let word_alloc_get_heu_pre = prove
 (`!fc v0 v. word_alloc_get_heu_pre fc v0 v`,
  CHEAT_TAC);;

(* HOL4 backend_32_cvScript.sml:587: ML code, not ported *)

(* and the names it reads as variables are constants again *)
let _ = do_list unhide_constant
  ["ABS";
   "Num"];;

(* and the interface *)
let _ = unhide_overloads ();;
