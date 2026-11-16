(* ======================================================== *)
(*  backend_x64_cv: ported from HOL4's
    cv_translator/backend_x64_cvScript.sml
    A definition theory, with 2 definitions and 18 theorems.  No
    file of the port needs it.  *)
(* ======================================================== *)

(*
  Translate x64-specialised functions to cv equations.
*)

needs "compiler/backend/cv_compute/backend_x64.ml";;
needs "compiler/backend/x64/export_x64.ml";;
needs "compiler/backend/x64/x64_config.ml";;
needs "cv_translator/backend_64_cv.ml";;
needs "cv_translator/backend_cv.ml";;
needs "cv_translator/to_data_cv.ml";;
needs "lib/cv_std.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "backend_x64_cv"
  ["backend_64_cv"; "backend_cv"; "backend_x64"; "export_x64"; "to_data_cv";
   "x64_config"];;
(* HOL4 ancestors outside the port: x64 x64_target *)

(*---------------------------------------------------------------------------*
  Translation of instruction encoder
 *---------------------------------------------------------------------------*)

(* [cv_inline,local] *)
let backend_x64_cv_IN_INSERT = IN_INSERT;;
(* [cv_inline,local] *)
let backend_x64_cv_NOT_IN_EMPTY = NOT_IN_EMPTY;;

(* HOL4 backend_x64_cvScript.sml:18: ML code, not ported *)

(* [local] *)
let total_num2Zreg = prove
 (`total_num2Zreg n =
       if n = 1 then RCX else if n = 2 then RDX else if n = 3 then RBX
         else if n = 4 then RSP else if n = 5 then RBP else if n = 6 then RSI
         else if n = 7 then RDI else if n = 8 then zR8 else if n = 9 then zR9
         else if n = 10 then zR10 else if n = 11 then zR11 else if n = 12
         then zR12 else if n = 13 then zR13 else if n = 14 then zR14 else if
         n = 15 then zR15 else RAX`,
  CHEAT_TAC);;

(* [cv_inline] *)
let num2Zreg_w2n = prove
 (`num2Zreg (w2n r) = total_num2Zreg (w2n (r:word4))`,
  CHEAT_TAC);;

(* [cv_inline] *)
let num2Zreg_w2n_w3 = prove
 (`num2Zreg (w2n r) = total_num2Zreg (w2n (r:word3))`,
  CHEAT_TAC);;

(* HOL4 backend_x64_cvScript.sml:54-58: ML code, not ported *)

(* HOL4 backend_x64_cvScript.sml:60-65: ML code, not ported *)

(* [local] *)
let fix_num_case = prove
 (`(match (n:num) with 0 -> x | 1 -> y | v -> z) =
   if n = 0 then x else if n = 1 then y else z`,
  CHEAT_TAC);;

(* HOL4 backend_x64_cvScript.sml:74-94: ML code, not ported *)

let znop_def = new_definition
  `znop (n:num) =
     if n = 1 then [(n2w 144)] else if n = 2 then [(n2w 102); (n2w 144)]
       else if n = 3 then [(n2w 15); (n2w 31); (n2w 0)] else if n = 4 then
       [(n2w 15); (n2w 31); (n2w 64); (n2w 0)] else if n = 5 then [(n2w 15);
       (n2w 31); (n2w 68); (n2w 0); (n2w 0)] else if n = 6 then [(n2w 102);
       (n2w 15); (n2w 31); (n2w 68); (n2w 0); (n2w 0)] else if n = 7 then
       [(n2w 15); (n2w 31); (n2w 128); (n2w 0); (n2w 0); (n2w 0); (n2w 0)]
       else if n = 8 then [(n2w 15); (n2w 31); (n2w 132); (n2w 0); (n2w 0);
       (n2w 0); (n2w 0); (n2w 0)] else if n = 9 then [(n2w 102); (n2w 15);
       (n2w 31); (n2w 132); (n2w 0); (n2w 0); (n2w 0); (n2w 0); (n2w 0)]
       else []:word8 list`;;

(* HOL4 backend_x64_cvScript.sml:109: ML code, not ported *)

(* [local] *)
let to_znop = prove
 (`(match n with 1 -> [(n2w 144)]
    | 2 -> [(n2w 102); (n2w 144)]
    | 3 -> [(n2w 15); (n2w 31); (n2w 0)]
    | 4 -> [(n2w 15); (n2w 31); (n2w 64); (n2w 0)]
    | 5 -> [(n2w 15); (n2w 31); (n2w 68); (n2w 0); (n2w 0)]
    | 6 -> [(n2w 102); (n2w 15); (n2w 31); (n2w 68); (n2w 0); (n2w 0)]
    | 7 -> [(n2w 15); (n2w 31); (n2w 128); (n2w 0); (n2w 0); (n2w 0); (n2w
      0)]
    | 8 -> [(n2w 15); (n2w 31); (n2w 132); (n2w 0); (n2w 0); (n2w 0); (n2w
      0); (n2w 0)]
    | 9 -> [(n2w 102); (n2w 15); (n2w 31); (n2w 132); (n2w 0); (n2w 0); (n2w
      0); (n2w 0); (n2w 0)]
    | _ -> []) = znop n`,
  CHEAT_TAC);;

(* HOL4 backend_x64_cvScript.sml:127-128: ML code, not ported *)

(* HOL4 backend_x64_cvScript.sml:130-131: ML code, not ported *)

(*---------------------------------------------------------------------------*
  Remaining x64-specific functions
 *---------------------------------------------------------------------------*)

(* HOL4 backend_x64_cvScript.sml:137: ML code, not ported *)

(* [cv_pre,local] *)
let comp_x64_pre = prove
 (`!perf v bs kf. comp_x64_pre perf v bs kf`,
  CHEAT_TAC);;

(* HOL4 backend_x64_cvScript.sml:150: ML code, not ported *)

(* HOL4 backend_x64_cvScript.sml:152: ML code, not ported *)

(* [cv_pre] *)
let compile_word_to_stack_x64_pre = prove
 (`!perf k v bitmaps. compile_word_to_stack_x64_pre perf k v bitmaps`,
  CHEAT_TAC);;

(* HOL4 backend_x64_cvScript.sml:161: a theorem that HOL4 states as the
   value of an ML expression: fp_reg_ok_x64_def *)

(* HOL4 backend_x64_cvScript.sml:163-166: ML code, not ported *)

(* HOL4 backend_x64_cvScript.sml:168: ML code, not ported *)

(* [cv_pre,local] *)
let enc_lines_again_x64_pre = prove
 (`!labs ffis pos v0 v. enc_lines_again_x64_pre labs ffis pos v0 v`,
  CHEAT_TAC);;

(* HOL4 backend_x64_cvScript.sml:176: ML code, not ported *)

(* [cv_pre,local] *)
let enc_secs_again_x64_pre = prove
 (`!pos labs ffis v. enc_secs_again_x64_pre pos labs ffis v`,
  CHEAT_TAC);;

(* HOL4 backend_x64_cvScript.sml:184: ML code, not ported *)

(* [cv_pre] *)
let remove_labels_loop_x64_pre = prove
 (`!clock pos init_labs ffis sec_list.
     remove_labels_loop_x64_pre clock pos init_labs ffis sec_list`,
  CHEAT_TAC);;

(* HOL4 backend_x64_cvScript.sml:193-199: ML code, not ported *)

(* HOL4 backend_x64_cvScript.sml:201-202: ML code, not ported *)

(* HOL4 backend_x64_cvScript.sml:204: ML code, not ported *)

(* HOL4 backend_x64_cvScript.sml:206: ML code, not ported *)
(* [cv_pre,local] *)
let get_forced_x64_pre = prove
 (`!v acc. get_forced_x64_pre v acc`,
  CHEAT_TAC);;

(* HOL4 backend_x64_cvScript.sml:217: ML code, not ported *)

(* HOL4 backend_x64_cvScript.sml:219: ML code, not ported *)
(* [cv_pre] *)
let inst_select_exp_x64_pre = prove
 (`!v tar temp. inst_select_exp_x64_pre tar temp v`,
  CHEAT_TAC);;

(* HOL4 backend_x64_cvScript.sml:231: ML code, not ported *)
(* [cv_pre,local] *)
let inst_select_x64_pre = prove
 (`!v temp. inst_select_x64_pre temp v`,
  CHEAT_TAC);;

(* HOL4 backend_x64_cvScript.sml:241: ML code, not ported *)
(* [cv_pre,local] *)
let each_inlogic_x64_pre = prove
 (`!v. each_inlogic_x64_pre v`,
  CHEAT_TAC);;

(* HOL4 backend_x64_cvScript.sml:248-249: ML code, not ported *)

(* HOL4 backend_x64_cvScript.sml:251-254: ML code, not ported *)

(* HOL4 backend_x64_cvScript.sml:256-257: ML code, not ported *)

(* HOL4 backend_x64_cvScript.sml:259-265: ML code, not ported *)

(* export *)

let backend_x64_cv_export_funcs_alt_def,backend_x64_cv_export_funcs_alt_ind =
  define_guess
  `(backend_x64_cv_export_funcs_alt [] e = e) /\
   (backend_x64_cv_export_funcs_alt (CONS x xs) e =
    backend_x64_cv_export_funcs_alt xs (export_x64_export_func e x))`;;

(* export_funcs_alt_thm *)
let backend_x64_cv_export_funcs_alt_thm = prove
 (`!xs e. backend_x64_cv_export_funcs_alt xs e = FOLDL export_x64_export_func
  e xs`,
  CHEAT_TAC);;

(* HOL4 backend_x64_cvScript.sml:280: ML code, not ported *)

(* HOL4 backend_x64_cvScript.sml:282-285: ML code, not ported *)

(* HOL4 backend_x64_cvScript.sml:287-291: ML code, not ported *)

(* main translations below *)

(* HOL4 backend_x64_cvScript.sml:295-297: ML code, not ported *)

(* and the interface *)
let _ = unhide_overloads ();;
