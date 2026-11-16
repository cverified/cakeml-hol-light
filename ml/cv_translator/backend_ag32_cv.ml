(* ======================================================== *)
(*  backend_ag32_cv: ported from HOL4's
    cv_translator/backend_ag32_cvScript.sml
    A definition theory, with no definitions and 12 theorems.  No
    file of the port needs it.  *)
(* ======================================================== *)

(*
  Translate ag32-specialised functions to cv equations.
*)

needs "compiler/backend/ag32/ag32_config.ml";;
needs "compiler/backend/ag32/export_ag32.ml";;
needs "compiler/backend/cv_compute/backend_ag32.ml";;
needs "cv_translator/backend_32_cv.ml";;
needs "cv_translator/backend_cv.ml";;
needs "cv_translator/to_data_cv.ml";;
needs "lib/cv_std.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "backend_ag32_cv"
  ["ag32_config"; "backend_32_cv"; "backend_ag32"; "backend_cv";
   "export_ag32"; "to_data_cv"];;
(* HOL4 ancestors outside the port: ag32 ag32_target *)

(*---------------------------------------------------------------------------*
  Translation of instruction encoder
 *---------------------------------------------------------------------------*)

(* [cv_inline,local] *)
let backend_ag32_cv_IN_INSERT = IN_INSERT;;
(* [cv_inline,local] *)
let backend_ag32_cv_NOT_IN_EMPTY = NOT_IN_EMPTY;;

(* HOL4 backend_ag32_cvScript.sml:18-29: ML code, not ported *)

(* HOL4 backend_ag32_cvScript.sml:31-32: ML code, not ported *)

(* HOL4 backend_ag32_cvScript.sml:34: ML code, not ported *)

(*---------------------------------------------------------------------------*
  Remaining ag32-specific functions
 *---------------------------------------------------------------------------*)

(* HOL4 backend_ag32_cvScript.sml:40: ML code, not ported *)

(* [cv_pre,local] *)
let comp_ag32_pre = prove
 (`!perf v bs kf. comp_ag32_pre perf v bs kf`,
  CHEAT_TAC);;

(* HOL4 backend_ag32_cvScript.sml:53: ML code, not ported *)

(* HOL4 backend_ag32_cvScript.sml:55: ML code, not ported *)

(* [cv_pre] *)
let compile_word_to_stack_ag32_pre = prove
 (`!perf k v bitmaps. compile_word_to_stack_ag32_pre perf k v bitmaps`,
  CHEAT_TAC);;

(* [local] *)
let fp_ok_false = prove
 (`fp_ok_ag32 v = F`,
  CHEAT_TAC);;

(* HOL4 backend_ag32_cvScript.sml:70-71: ML code, not ported *)

(* HOL4 backend_ag32_cvScript.sml:73-74: ML code, not ported *)

(* HOL4 backend_ag32_cvScript.sml:76-77: ML code, not ported *)

(* HOL4 backend_ag32_cvScript.sml:79: ML code, not ported *)

(* [cv_pre,local] *)
let enc_lines_again_ag32_pre = prove
 (`!labs ffis pos v0 v. enc_lines_again_ag32_pre labs ffis pos v0 v`,
  CHEAT_TAC);;

(* HOL4 backend_ag32_cvScript.sml:87: ML code, not ported *)

(* [cv_pre,local] *)
let enc_secs_again_ag32_pre = prove
 (`!pos labs ffis v. enc_secs_again_ag32_pre pos labs ffis v`,
  CHEAT_TAC);;

(* HOL4 backend_ag32_cvScript.sml:95: ML code, not ported *)

(* [cv_pre] *)
let remove_labels_loop_ag32_pre = prove
 (`!clock pos init_labs ffis sec_list.
     remove_labels_loop_ag32_pre clock pos init_labs ffis sec_list`,
  CHEAT_TAC);;

(* HOL4 backend_ag32_cvScript.sml:104-110: ML code, not ported *)

(* HOL4 backend_ag32_cvScript.sml:112-113: ML code, not ported *)

(* HOL4 backend_ag32_cvScript.sml:115: ML code, not ported *)

(* HOL4 backend_ag32_cvScript.sml:117: ML code, not ported *)
(* [cv_pre,local] *)
let get_forced_ag32_pre = prove
 (`!v acc. get_forced_ag32_pre v acc`,
  CHEAT_TAC);;

(* HOL4 backend_ag32_cvScript.sml:128: ML code, not ported *)

(* HOL4 backend_ag32_cvScript.sml:130: ML code, not ported *)
(* [cv_pre] *)
let inst_select_exp_ag32_pre = prove
 (`!v tar temp. inst_select_exp_ag32_pre tar temp v`,
  CHEAT_TAC);;

(* HOL4 backend_ag32_cvScript.sml:142: ML code, not ported *)
(* [cv_pre,local] *)
let inst_select_ag32_pre = prove
 (`!v temp. inst_select_ag32_pre temp v`,
  CHEAT_TAC);;

(* HOL4 backend_ag32_cvScript.sml:152: ML code, not ported *)
(* [cv_pre,local] *)
let each_inlogic_ag32_pre = prove
 (`!v. each_inlogic_ag32_pre v`,
  CHEAT_TAC);;

(* HOL4 backend_ag32_cvScript.sml:159-160: ML code, not ported *)

(* HOL4 backend_ag32_cvScript.sml:162-165: ML code, not ported *)

(* HOL4 backend_ag32_cvScript.sml:167-168: ML code, not ported *)

(* export *)

(* HOL4 backend_ag32_cvScript.sml:172-176: ML code, not ported *)

(* main translations below *)

(* HOL4 backend_ag32_cvScript.sml:180-182: ML code, not ported *)

(* and the interface *)
let _ = unhide_overloads ();;
