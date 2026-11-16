(* ======================================================== *)
(*  basis_cv: ported from HOL4's
    basis/pure/basis_cvScript.sml
    A definition theory, with no definitions and 5 theorems.  Needed
    by backend_cv.ml, infer_cv.ml, source_cv.ml, to_data_cv.ml and
    unify_cv.ml.  *)
(* ======================================================== *)

(*
  Translation of basis types and functions for use with cv_compute.
*)

needs "basis/pure/mlsexp.ml";;
needs "basis/pure/mlstring.ml";;
needs "lib/cv_std.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "basis_cv"
  ["mlsexp"];;

let _ = do_list hide_constant ["ABS"; "Num"];;

(* HOL4 basis_cvScript.sml:10: ML code, not ported *)

(* [local,cv_inline] *)
let list_mem = MEM;;

(* HOL4 basis_cvScript.sml:14-18: ML code, not ported *)

(* HOL4 basis_cvScript.sml:20-23: ML code, not ported *)

(* HOL4 basis_cvScript.sml:25: ML code, not ported *)

(* [cv_pre] *)
let strsub_pre = prove
 (`!v n. strsub_pre v n <=> n < strlen v`,
  CHEAT_TAC);;

(* HOL4 basis_cvScript.sml:33-34: ML code, not ported *)

(* HOL4 basis_cvScript.sml:36-37: ML code, not ported *)

let IMP_toChar_pre = prove
 (`n < 16 ==> mlint_toChar_pre n`,
  CHEAT_TAC);;

(* [cv_pre,local] *)
let num_to_chars_pre = prove
 (`!a0 a1 a2 a3. mlint_num_to_chars_pre a0 a1 a2 a3`,
  CHEAT_TAC);;

(* [local] *)
let Num_ABS = prove
 (`num_of_int (abs i) = num_of_int i`,
  CHEAT_TAC);;

(* HOL4 basis_cvScript.sml:60-61: ML code, not ported *)

(* HOL4 basis_cvScript.sml:63-65: ML code, not ported *)

(* and the names it reads as variables are constants again *)
let _ = do_list unhide_constant
  ["ABS";
   "Num"];;

(* and the interface *)
let _ = unhide_overloads ();;
