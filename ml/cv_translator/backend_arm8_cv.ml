(* ======================================================== *)
(*  backend_arm8_cv: ported from HOL4's
    cv_translator/backend_arm8_cvScript.sml
    A definition theory, with 3 definitions and 23 theorems.  No
    file of the port needs it.  *)
(* ======================================================== *)

(*
  Translate arm8-specialised functions to cv equations.
*)

needs "compiler/backend/arm8/arm8_config.ml";;
needs "compiler/backend/arm8/export_arm8.ml";;
needs "compiler/backend/cv_compute/backend_arm8.ml";;
needs "cv_translator/backend_64_cv.ml";;
needs "cv_translator/backend_cv.ml";;
needs "cv_translator/to_data_cv.ml";;
needs "lib/cv_std.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "backend_arm8_cv"
  ["arm8_config"; "backend_64_cv"; "backend_arm8"; "backend_cv";
   "export_arm8"; "to_data_cv"];;
(* HOL4 ancestors outside the port: arm8 arm8_target *)

(*---------------------------------------------------------------------------*
  Translation of instruction encoder
 *---------------------------------------------------------------------------*)

(* [cv_inline,local] *)
let backend_arm8_cv_IN_INSERT = backend_ag32_cv_IN_INSERT;;
(* [cv_inline,local] *)
let backend_arm8_cv_NOT_IN_EMPTY = backend_ag32_cv_NOT_IN_EMPTY;;

(* HOL4 backend_arm8_cvScript.sml:18: a theorem that HOL4 states as the
   value of an ML expression: word_len *)
(* [cv_inline,local] *)
let backend_arm8_cv_v2w_sing = v2w_sing;;

(* HOL4 backend_arm8_cvScript.sml:21-24: ML code, not ported *)

(* [cv_pre] *)
let e_load_store_pre = prove
 (`!i. e_load_store_pre i`,
  CHEAT_TAC);;

(* HOL4 backend_arm8_cvScript.sml:32-35: ML code, not ported *)

(* HOL4 backend_arm8_cvScript.sml:37-39: a theorem that HOL4 states as the
   value of an ML expression: e_sf_word32_F *)

(* HOL4 backend_arm8_cvScript.sml:41-43: a theorem that HOL4 states as the
   value of an ML expression: e_sf_word64_T *)

(* HOL4 backend_arm8_cvScript.sml:45-47: ML code, not ported *)

(* [cv_pre,local] *)
let HighestSetBit_pre = prove
 (`!w. HighestSetBit_pre w`,
  CHEAT_TAC);;

(* HOL4 backend_arm8_cvScript.sml:55: a theorem that HOL4 states as the
   value of an ML expression: cv_inline_v2w_Ones *)

(* HOL4 backend_arm8_cvScript.sml:57-63: ML code, not ported *)

let CountTrailing_T_def,CountTrailing_T_ind = define_guess
  `CountTrailing_T w =
     if w = (n2w 0) then 0
     else if word_bit 0 w then 0
     else 1 + CountTrailing_T (w >>> 1)`;;

(* the termination relation that HOL4 gives is
     MEASURE w2n
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 backend_arm8_cvScript.sml:76-80: the tactic that proves the
   termination *)
let CountTrailing_F_def,CountTrailing_F_ind = define_guess
  `CountTrailing_F w =
     if ~(word_bit 0 w) then 0
     else 1 + CountTrailing_F (w >>> 1)`;;

(* HOL4 backend_arm8_cvScript.sml:82-86: a proof *)

(* HOL4 backend_arm8_cvScript.sml:88-95: ML code, not ported *)

(* [cv_inline,local] *)
let cv_inline_CountTrailing_T = prove
 (`!w. CountTrailing (T,w) = CountTrailing_T w`,
  CHEAT_TAC);;

(* [cv_inline,local] *)
let cv_inline_CountTrailing_F = prove
 (`!w. CountTrailing (F,w) = if w = --(n2w 1) then 0 else CountTrailing_F w`,
  CHEAT_TAC);;

(* HOL4 backend_arm8_cvScript.sml:123-133: ML code, not ported *)

(* HOL4 backend_arm8_cvScript.sml:135-145: ML code, not ported *)

(* [cv_pre] *)
let arm8_ast_pre = prove
 (`!v. arm8_ast_pre v`,
  CHEAT_TAC);;

(* HOL4 backend_arm8_cvScript.sml:153-154: ML code, not ported *)

(*---------------------------------------------------------------------------*
  Remaining arm8-specific functions
 *---------------------------------------------------------------------------*)

(* HOL4 backend_arm8_cvScript.sml:160: ML code, not ported *)

(* [cv_pre,local] *)
let comp_arm8_pre = prove
 (`!perf v bs kf. comp_arm8_pre perf v bs kf`,
  CHEAT_TAC);;

(* HOL4 backend_arm8_cvScript.sml:173: ML code, not ported *)

(* HOL4 backend_arm8_cvScript.sml:175: ML code, not ported *)

(* [cv_pre] *)
let compile_word_to_stack_arm8_pre = prove
 (`!perf k v bitmaps. compile_word_to_stack_arm8_pre perf k v bitmaps`,
  CHEAT_TAC);;

(* HOL4 backend_arm8_cvScript.sml:184: a theorem that HOL4 states as the
   value of an ML expression: fp_reg_ok_arm8_def *)

(* HOL4 backend_arm8_cvScript.sml:186-189: ML code, not ported *)

(* HOL4 backend_arm8_cvScript.sml:191: ML code, not ported *)

(* [cv_pre,local] *)
let enc_lines_again_arm8_pre = prove
 (`!labs ffis pos v0 v. enc_lines_again_arm8_pre labs ffis pos v0 v`,
  CHEAT_TAC);;

(* HOL4 backend_arm8_cvScript.sml:199: ML code, not ported *)

(* [cv_pre,local] *)
let enc_secs_again_arm8_pre = prove
 (`!pos labs ffis v. enc_secs_again_arm8_pre pos labs ffis v`,
  CHEAT_TAC);;

(* HOL4 backend_arm8_cvScript.sml:207: ML code, not ported *)

(* [cv_pre] *)
let remove_labels_loop_arm8_pre = prove
 (`!clock pos init_labs ffis sec_list.
     remove_labels_loop_arm8_pre clock pos init_labs ffis sec_list`,
  CHEAT_TAC);;

(* HOL4 backend_arm8_cvScript.sml:216-222: ML code, not ported *)

(* HOL4 backend_arm8_cvScript.sml:224-225: ML code, not ported *)

(* HOL4 backend_arm8_cvScript.sml:227: ML code, not ported *)

(* HOL4 backend_arm8_cvScript.sml:229: ML code, not ported *)
(* [cv_pre,local] *)
let get_forced_arm8_pre = prove
 (`!v acc. get_forced_arm8_pre v acc`,
  CHEAT_TAC);;

(* HOL4 backend_arm8_cvScript.sml:240: ML code, not ported *)

(* HOL4 backend_arm8_cvScript.sml:242: ML code, not ported *)
(* [cv_pre] *)
let inst_select_exp_arm8_pre = prove
 (`!v tar temp. inst_select_exp_arm8_pre tar temp v`,
  CHEAT_TAC);;

(* HOL4 backend_arm8_cvScript.sml:254: ML code, not ported *)
(* [cv_pre,local] *)
let inst_select_arm8_pre = prove
 (`!v temp. inst_select_arm8_pre temp v`,
  CHEAT_TAC);;

(* HOL4 backend_arm8_cvScript.sml:264: ML code, not ported *)
(* [cv_pre,local] *)
let each_inlogic_arm8_pre = prove
 (`!v. each_inlogic_arm8_pre v`,
  CHEAT_TAC);;

(* HOL4 backend_arm8_cvScript.sml:271-272: ML code, not ported *)

(* HOL4 backend_arm8_cvScript.sml:274-277: ML code, not ported *)

(* HOL4 backend_arm8_cvScript.sml:279-280: ML code, not ported *)

(* export *)


let export_funcs_alt_def,export_funcs_alt_ind = define_guess
  `(backend_arm8_cv_export_funcs_alt [] e = e) /\
   (backend_arm8_cv_export_funcs_alt (CONS x xs) e =
    backend_arm8_cv_export_funcs_alt xs (export_arm8_export_func e x))`;;

let export_funcs_alt_thm = prove
 (`!xs e. backend_arm8_cv_export_funcs_alt xs e = FOLDL
  export_arm8_export_func e xs`,
  CHEAT_TAC);;

(* HOL4 backend_arm8_cvScript.sml:296: ML code, not ported *)

(* HOL4 backend_arm8_cvScript.sml:298-301: ML code, not ported *)

(* HOL4 backend_arm8_cvScript.sml:303-307: ML code, not ported *)

(* main translations below *)

(* HOL4 backend_arm8_cvScript.sml:311-313: ML code, not ported *)

(* and the interface *)
let _ = unhide_overloads ();;
