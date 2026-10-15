(* ======================================================== *)
(*  labProps: ported from HOL4's
    compiler/backend/semantics/labPropsScript.sml  *)
(* ======================================================== *)

(*
  Properties about labLang and its semantics
*)

needs "compiler/backend/labLang.ml";;
needs "compiler/backend/lab_to_target.ml";;
needs "compiler/backend/pattern_matching/pattern_semantics.ml";;
needs "compiler/backend/semantics/labSem.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/backend/stackLang.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "lib/alignment.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/proofs/semanticsProps.ml";;

let extract_labels_def = cake_define
  `labProps_extract_labels x1 =
        match x1 with
          [] -> []
        | ((Label l1 l2 _1) :: xs) -> (l1,l2) ::
          labProps_extract_labels xs
        | (x :: xs) -> labProps_extract_labels xs`;;
hol4_overload "extract_labels" "labProps_extract_labels";;

(* HOL4 ML code, not ported:
val extract_labels_ind = theorem"extract_labels_ind";
*)

let labs_of_def = cake_define
  `labs_of x1 =
      match x1 with
        labLang_LocValue _2 (Lab n1 n2) -> {(n1,n2)}
      | (Jump (Lab n1 n2)) -> {(n1,n2)}
      | (JumpCmp _3 _4 _5 (Lab n1 n2)) -> {(n1,n2)}
      | _6 -> {}`;;

let line_get_labels_def = cake_define
  `line_get_labels x1 =
      match x1 with
        LabAsm a _7 _8 _9 -> labs_of a
      | _10 -> {}`;;

let sec_get_labels_def = cake_define
  `sec_get_labels (Section _11 lines) =
     BIGUNION (IMAGE line_get_labels (set_of_list lines))`;;

let get_labels_def = cake_define
  `labProps_get_labels code = BIGUNION (IMAGE sec_get_labels
  (set_of_list code))`;;
hol4_overload "get_labels" "labProps_get_labels";;

let line_get_code_labels_def = cake_define
  `line_get_code_labels x1 =
      match x1 with
        Label _12 l _13 -> {l}
      | _14 -> {}`;;

let sec_get_code_labels_def = cake_define
  `sec_get_code_labels (Section n1 lines) =
     (n1,0) INSERT
     IMAGE (\n2. (n1,n2)) (BIGUNION (IMAGE line_get_code_labels
       (set_of_list lines)))`;;

let get_code_labels_def = cake_define
  `labProps_get_code_labels code = BIGUNION (IMAGE
  sec_get_code_labels (set_of_list code))`;;
hol4_overload "get_code_labels" "labProps_get_code_labels";;

let sec_ends_with_label_def = cake_define
  `sec_ends_with_label (Section _15 ls) <=>
     ~NULL ls /\ is_Label (LAST ls)`;;

let line_length_def = cake_define_list
  [`line_length (Label k1 k2 l) = (if l = 0 then 0 else 1)`;
   `line_length (Asm b bytes l) = LENGTH bytes`;
   `line_length (LabAsm a w bytes l) = LENGTH bytes`];;

let align_dm_def = cake_define
  `align_dm (s:('a,'c,'ffi)labSem_state) =
     (?_mem_domain_fupd (K (?_mem_domain s INTER byte_aligned)) s)`;;

(** align_sdm **)

let align_sdm_def = cake_define
  `align_sdm (s:('a,'c,'ffi)labSem_state) =
     (labSem_state_shared_mem_domain_fupd (K
       (labSem_state_shared_mem_domain s INTER byte_aligned)) s)`;;


(* asm_ok checks coming into lab_to_target *)
let line_ok_pre_def = cake_define
  `line_ok_pre c x2 =
        match (c,x2) with
          ((c:'a asm_config),Asm b bytes l) -> asm_ok (cbw_to_asm b)
            c
        | (c,_16) -> T`;;

let sec_ok_pre_def = cake_define
  `sec_ok_pre c (Section k ls) <=>
     EVERY (line_ok_pre c) ls`;;

(* HOL4 overload (expanded in the port):
     all_enc_ok_pre = λc ls. EVERY (sec_ok_pre c) ls *)

(* invariant: labels have correct section number and are non-zero *)

let sec_label_ok_def = cake_define
  `sec_label_ok k x2 =
        match x2 with
          Label l1 l2 len -> l1 = k /\ ~(l2 = 0)
        | _17 -> T`;;

let sec_labels_ok_def = cake_define
  `sec_labels_ok (Section k ls) <=> EVERY (sec_label_ok k) ls`;;

let no_install_def = cake_define
  `labProps_no_install code <=>
   (!p w bytes l. ~(
     asm_fetch_aux p code =
       SOME (LabAsm Install w bytes l)))`;;
hol4_overload "no_install" "labProps_no_install";;

let no_share_mem_inst_def = cake_define
  `no_share_mem_inst code <=>
   (!p op re a inst' len. ~(
     asm_fetch_aux p code =
       SOME (Asm (ShareMem op re a) inst' len)))`;;
