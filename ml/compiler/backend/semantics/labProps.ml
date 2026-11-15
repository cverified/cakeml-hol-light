(* ======================================================== *)
(*  labProps: ported from HOL4's
    compiler/backend/semantics/labPropsScript.sml
    A proof theory, with 18 definitions and 91 theorems.  Needed by
    backendProof.ml, lab_filterProof.ml, lab_to_targetProof.ml,
    stack_rawcallProof.ml and stack_to_labProof.ml.  *)
(* ======================================================== *)

(*
  Properties about labLang and its semantics
*)

needs "compiler/backend/labLang.ml";;
needs "compiler/backend/lab_to_target.ml";;
needs "compiler/backend/semantics/labSem.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "lib/alignment.ml";;
needs "misc/misc.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/proofs/semanticsProps.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "labProps"
  ["ffi"; "labSem"; "lab_to_target"; "semanticsProps"; "wordSem"];;

(* this file reads the name of a record field as a variable and
   needs the accessors of that field as well, so only these
   pairs come out of the interface *)
let _ = hide_overloads
  ["code_buffer","code_buffer";
   "failed","pegexec_failed"];;

let _ = do_list hide_constant ["mem"];;

make_size "line";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let labProps_extract_labels_def,labProps_extract_labels_ind = define_wf
  `MEASURE (\x0. list_size (line_size (\x. 0)) x0)`
  `labProps_extract_labels x1 =
     match x1 with
       [] -> []
     | CONS (lab_Label l1 l2 _) xs -> CONS (l1,l2) (labProps_extract_labels
       xs)
     | CONS x xs -> labProps_extract_labels xs`;;
add_simp labProps_extract_labels_def;;

(* HOL4 labPropsScript.sml:18: ML code, not ported *)

let extract_labels_append = prove
 (`!A B.
   labProps_extract_labels (APPEND A B) = APPEND (labProps_extract_labels
     A) (labProps_extract_labels B)`,
  CHEAT_TAC);;

let labs_of_def = new_definition
  `labs_of x1' =
   match x1' with
     lab_LocValue _ (lab_Lab n1 n2) -> {(n1,n2)}
   | lab_Jump (lab_Lab n1 n2) -> {(n1,n2)}
   | lab_JumpCmp _ _ _ (lab_Lab n1 n2) -> {(n1,n2)}
   | _ -> {}`;;
add_simp labs_of_def;;

let line_get_labels_def = new_definition
  `line_get_labels x1'' =
   match x1'' with
     lab_LabAsm a _ _ _ -> labs_of a
   | _ -> {}`;;

let sec_get_labels_def = define_general
  `sec_get_labels (Section _ lines) =
     UNIONS (IMAGE line_get_labels (set_of_list lines))`;;

let labProps_get_labels_def = new_definition
  `labProps_get_labels code = UNIONS (IMAGE sec_get_labels (set_of_list
  code))`;;

let get_labels_cons = prove
 (`labProps_get_labels (CONS x xs) = sec_get_labels x UNION
  labProps_get_labels xs`,
  CHEAT_TAC);;

let line_get_code_labels_def = new_definition
  `line_get_code_labels x1''' =
   match x1''' with
     lab_Label _ l _ -> {l}
   | _ -> {}`;;
add_simp line_get_code_labels_def;;

let sec_get_code_labels_def = define_general
  `sec_get_code_labels (Section n1 lines) =
     (n1,0) INSERT
     IMAGE (\n2. (n1,n2)) (UNIONS (IMAGE line_get_code_labels
       (set_of_list lines)))`;;

let labProps_get_code_labels_def = new_definition
  `labProps_get_code_labels code = UNIONS (IMAGE sec_get_code_labels
  (set_of_list code))`;;

let get_code_labels_nil = prove
 (`labProps_get_code_labels [] = {}`,
  CHEAT_TAC);;
add_simp get_code_labels_nil;;

let get_code_labels_cons = prove
 (`labProps_get_code_labels (CONS s secs) = sec_get_code_labels s UNION
  labProps_get_code_labels secs`,
  CHEAT_TAC);;

let sec_ends_with_label_def = define_general
  `sec_ends_with_label (Section _ ls) <=>
     ~(NULL ls) /\ is_Label (LAST ls)`;;

let reg_imm_with_clock = prove
 (`labSem_reg_imm r (labSem_state_clock_fupd (K z) s) = labSem_reg_imm r s`,
  CHEAT_TAC);;
add_simp reg_imm_with_clock;;

let asm_inst_with_clock = prove
 (`asm_inst i (labSem_state_clock_fupd (K z) s) = labSem_state_clock_fupd (K
  z) (asm_inst i s)`,
  CHEAT_TAC);;
add_simp asm_inst_with_clock;;

let read_reg_inc_pc = prove
 (`labSem_state_regs (inc_pc s) r = labSem_state_regs s r`,
  CHEAT_TAC);;
add_simp read_reg_inc_pc;;

(* with_same_clock *)
let labProps_with_same_clock = prove
 (`(labSem_state_clock_fupd (K (labSem_state_clock s)) s) = s`,
  CHEAT_TAC);;
add_simp labProps_with_same_clock;;

let inc_pc_dec_clock = prove
 (`inc_pc (labSem_dec_clock x) = labSem_dec_clock (inc_pc x)`,
  CHEAT_TAC);;

let update_simps = prove
 (`(labSem_state_ffi (labSem_upd_pc x s) = labSem_state_ffi s) /\
    (labSem_state_ffi (labSem_dec_clock s) = labSem_state_ffi s) /\
    (labSem_state_pc (labSem_upd_pc x s) = x) /\
    (labSem_state_pc (labSem_dec_clock s) = labSem_state_pc s) /\
    (labSem_state_clock (labSem_upd_pc x s) = labSem_state_clock s) /\
    (labSem_state_ffi (labSem_upd_pc x s) = labSem_state_ffi s) /\
    (labSem_state_clock (labSem_dec_clock s) = labSem_state_clock s - 1) /\
    (labSem_state_len_reg (labSem_dec_clock s) = labSem_state_len_reg s) /\
    (labSem_state_len2_reg (labSem_dec_clock s) = labSem_state_len2_reg s)
      /\
    (labSem_state_link_reg (labSem_dec_clock s) = labSem_state_link_reg s)
      /\
    (labSem_state_code (labSem_dec_clock s) = labSem_state_code s) /\
    (labSem_state_ptr_reg (labSem_dec_clock s) = labSem_state_ptr_reg s) /\
    (labSem_state_ptr2_reg (labSem_dec_clock s) = labSem_state_ptr2_reg s)
      /\
    (labSem_state_ffi (labSem_dec_clock s) = labSem_state_ffi s) /\
    (labSem_state_len_reg (labSem_upd_pc x s) = labSem_state_len_reg s) /\
    (labSem_state_len2_reg (labSem_upd_pc x s) = labSem_state_len2_reg s) /\
    (labSem_state_link_reg (labSem_upd_pc x s) = labSem_state_link_reg s) /\
    (labSem_state_code (labSem_upd_pc x s) = labSem_state_code s) /\
    (labSem_state_ptr_reg (labSem_upd_pc x s) = labSem_state_ptr_reg s) /\
    (labSem_state_ptr2_reg (labSem_upd_pc x s) = labSem_state_ptr2_reg s) /\
    (labSem_state_mem_domain (labSem_upd_pc x s) = labSem_state_mem_domain
      s) /\
    (labSem_state_shared_mem_domain (labSem_upd_pc x s) =
      labSem_state_shared_mem_domain s) /\
    (labSem_state_failed (labSem_upd_pc x s) = labSem_state_failed s) /\
    (labSem_state_be (labSem_upd_pc x s) = labSem_state_be s) /\
    (labSem_state_mem (labSem_upd_pc x s) = labSem_state_mem s) /\
    (labSem_state_regs (labSem_upd_pc x s) = labSem_state_regs s) /\
    (labSem_state_fp_regs (labSem_upd_pc x s) = labSem_state_fp_regs s) /\
    (labSem_state_ffi (labSem_upd_pc x s) = labSem_state_ffi s) /\
    (labSem_state_ptr_reg (inc_pc s) = labSem_state_ptr_reg s) /\
    (labSem_state_ptr2_reg (inc_pc s) = labSem_state_ptr2_reg s) /\
    (labSem_state_len_reg (inc_pc s) = labSem_state_len_reg s) /\
    (labSem_state_len2_reg (inc_pc s) = labSem_state_len2_reg s) /\
    (labSem_state_link_reg (inc_pc s) = labSem_state_link_reg s) /\
    (labSem_state_code (inc_pc s) = labSem_state_code s) /\
    (labSem_state_be (inc_pc s) = labSem_state_be s) /\
    (labSem_state_failed (inc_pc s) = labSem_state_failed s) /\
    (labSem_state_mem_domain (inc_pc s) = labSem_state_mem_domain s) /\
    (labSem_state_shared_mem_domain (inc_pc s) =
      labSem_state_shared_mem_domain s) /\
    (labSem_state_io_regs (inc_pc s) = labSem_state_io_regs s) /\
    (labSem_state_io_fp_regs (inc_pc s) = labSem_state_io_fp_regs s) /\
    (labSem_state_cc_regs (inc_pc s) = labSem_state_cc_regs s) /\
    (labSem_state_cc_fp_regs (inc_pc s) = labSem_state_cc_fp_regs s) /\
    (labSem_state_compile (inc_pc s) = labSem_state_compile s) /\
    (labSem_state_compile_oracle (inc_pc s) = labSem_state_compile_oracle s)
      /\
    (labSem_state_code_buffer (inc_pc s) = labSem_state_code_buffer s) /\
    (labSem_state_mem (inc_pc s) = labSem_state_mem s) /\
    (labSem_state_regs (inc_pc s) = labSem_state_regs s) /\
    (labSem_state_fp_regs (inc_pc s) = labSem_state_fp_regs s) /\
    (labSem_state_pc (inc_pc s) = labSem_state_pc s + 1) /\
    (labSem_state_ffi (inc_pc s) = labSem_state_ffi s)`,
  CHEAT_TAC);;
add_simp update_simps;;

(* binop_upd_consts *)
let labProps_binop_upd_consts = prove
 (`labSem_state_mem_domain
      (labSem_binop_upd a b c d x) = labSem_state_mem_domain x
        /\ labSem_state_shared_mem_domain
      (labSem_binop_upd a b c d x) = labSem_state_shared_mem_domain x
        /\ labSem_state_ptr_reg
      (labSem_binop_upd a b c d x) = labSem_state_ptr_reg x
        /\ labSem_state_ptr2_reg
      (labSem_binop_upd a b c d x) = labSem_state_ptr2_reg x
        /\ labSem_state_len_reg
      (labSem_binop_upd a b c d x) = labSem_state_len_reg x
        /\ labSem_state_len2_reg
      (labSem_binop_upd a b c d x) = labSem_state_len2_reg x
        /\ labSem_state_link_reg
      (labSem_binop_upd a b c d x) = labSem_state_link_reg x
        /\ labSem_state_code
      (labSem_binop_upd a b c d x) = labSem_state_code x /\ labSem_state_be
      (labSem_binop_upd a b c d x) = labSem_state_be x /\ labSem_state_mem
      (labSem_binop_upd a b c d x) = labSem_state_mem x
        /\ labSem_state_io_regs
      (labSem_binop_upd a b c d x) = labSem_state_io_regs x
        /\ labSem_state_io_fp_regs
      (labSem_binop_upd a b c d x) = labSem_state_io_fp_regs x
        /\ labSem_state_cc_regs
      (labSem_binop_upd a b c d x) = labSem_state_cc_regs x
        /\ labSem_state_cc_fp_regs
      (labSem_binop_upd a b c d x) = labSem_state_cc_fp_regs x
        /\ labSem_state_compile
      (labSem_binop_upd a b c d x) = labSem_state_compile x
        /\ labSem_state_compile_oracle
      (labSem_binop_upd a b c d x) = labSem_state_compile_oracle x
        /\ labSem_state_code_buffer
      (labSem_binop_upd a b c d x) = labSem_state_code_buffer x
        /\ labSem_state_pc
      (labSem_binop_upd a b c d x) = labSem_state_pc x /\ labSem_state_ffi
      (labSem_binop_upd a b c d x) = labSem_state_ffi x`,
  CHEAT_TAC);;
add_simp labProps_binop_upd_consts;;

(* arith_upd_consts *)
let labProps_arith_upd_consts = prove
 (`labSem_state_mem_domain
      (labSem_arith_upd a x) = labSem_state_mem_domain x
        /\ labSem_state_shared_mem_domain
      (labSem_arith_upd a x) = labSem_state_shared_mem_domain x
        /\ labSem_state_ptr_reg
      (labSem_arith_upd a x) = labSem_state_ptr_reg x
        /\ labSem_state_ptr2_reg
      (labSem_arith_upd a x) = labSem_state_ptr2_reg x
        /\ labSem_state_len_reg
      (labSem_arith_upd a x) = labSem_state_len_reg x
        /\ labSem_state_len2_reg
      (labSem_arith_upd a x) = labSem_state_len2_reg x
        /\ labSem_state_link_reg
      (labSem_arith_upd a x) = labSem_state_link_reg x /\ labSem_state_code
      (labSem_arith_upd a x) = labSem_state_code x /\ labSem_state_be
      (labSem_arith_upd a x) = labSem_state_be x /\ labSem_state_mem
      (labSem_arith_upd a x) = labSem_state_mem x /\ labSem_state_io_regs
      (labSem_arith_upd a x) = labSem_state_io_regs x
        /\ labSem_state_io_fp_regs
      (labSem_arith_upd a x) = labSem_state_io_fp_regs x
        /\ labSem_state_cc_regs
      (labSem_arith_upd a x) = labSem_state_cc_regs x
        /\ labSem_state_cc_fp_regs
      (labSem_arith_upd a x) = labSem_state_cc_fp_regs x
        /\ labSem_state_compile
      (labSem_arith_upd a x) = labSem_state_compile x
        /\ labSem_state_compile_oracle
      (labSem_arith_upd a x) = labSem_state_compile_oracle x
        /\ labSem_state_code_buffer
      (labSem_arith_upd a x) = labSem_state_code_buffer x /\ labSem_state_pc
      (labSem_arith_upd a x) = labSem_state_pc x /\ labSem_state_ffi
      (labSem_arith_upd a x) = labSem_state_ffi x`,
  CHEAT_TAC);;
add_simp labProps_arith_upd_consts;;

(* fp_upd_consts *)
let labProps_fp_upd_consts = prove
 (`labSem_state_mem_domain
      (labSem_fp_upd f x) = labSem_state_mem_domain x
        /\ labSem_state_shared_mem_domain
      (labSem_fp_upd f x) = labSem_state_shared_mem_domain x
        /\ labSem_state_ptr_reg
      (labSem_fp_upd f x) = labSem_state_ptr_reg x /\ labSem_state_len_reg
      (labSem_fp_upd f x) = labSem_state_len_reg x /\ labSem_state_ptr2_reg
      (labSem_fp_upd f x) = labSem_state_ptr2_reg x /\ labSem_state_len2_reg
      (labSem_fp_upd f x) = labSem_state_len2_reg x /\ labSem_state_link_reg
      (labSem_fp_upd f x) = labSem_state_link_reg x /\ labSem_state_code
      (labSem_fp_upd f x) = labSem_state_code x /\ labSem_state_cc_regs
      (labSem_fp_upd f x) = labSem_state_cc_regs x
        /\ labSem_state_cc_fp_regs
      (labSem_fp_upd f x) = labSem_state_cc_fp_regs x
        /\ labSem_state_code_buffer
      (labSem_fp_upd f x) = labSem_state_code_buffer x
        /\ labSem_state_compile
      (labSem_fp_upd f x) = labSem_state_compile x
        /\ labSem_state_compile_oracle
      (labSem_fp_upd f x) = labSem_state_compile_oracle x /\ labSem_state_be
      (labSem_fp_upd f x) = labSem_state_be x /\ labSem_state_mem
      (labSem_fp_upd f x) = labSem_state_mem x /\ labSem_state_io_regs
      (labSem_fp_upd f x) = labSem_state_io_regs x
        /\ labSem_state_io_fp_regs
      (labSem_fp_upd f x) = labSem_state_io_fp_regs x /\ labSem_state_pc
      (labSem_fp_upd f x) = labSem_state_pc x /\ labSem_state_ffi
      (labSem_fp_upd f x) = labSem_state_ffi x`,
  CHEAT_TAC);;
add_simp labProps_fp_upd_consts;;

let line_length_def = define_cases
  `(line_length (lab_Label k1 k2 l) = if l = 0 then 0 else 1) /\
   (line_length (lab_Asm b bytes l) = LENGTH bytes) /\
   (line_length (lab_LabAsm a w bytes l) = LENGTH bytes)`;;

let LENGTH_line_bytes = prove
 (`!x2. ~(is_Label x2) ==> (LENGTH (line_bytes x2) = line_length x2)`,
  CHEAT_TAC);;
add_simp LENGTH_line_bytes;;

(* HOL4 labPropsScript.sml:271-277: a theorem that HOL4 states as the value
   of an ML expression: case_eq_thms *)

(* evaluate_io_events_mono *)
let labProps_evaluate_io_events_mono = prove
 (`!s1 r s2. labSem_evaluate s1 = (r,s2) ==> ffi_state_io_events
  (labSem_state_ffi s1) <<= ffi_state_io_events (labSem_state_ffi s2)`,
  CHEAT_TAC);;

let evaluate_ADD_clock = prove
 (`!s res r k.
      labSem_evaluate s = (res,r) /\ ~(res = wordSem_TimeOut) ==>
      labSem_evaluate (labSem_state_clock_fupd (K (labSem_state_clock s +
        k)) s) = (res,labSem_state_clock_fupd (K (labSem_state_clock r + k))
        r)`,
  CHEAT_TAC);;

let addr_add_clock_eq = prove
 (`labSem_addr a (labSem_state_clock_fupd (K (extra + labSem_state_clock s))
  s) = labSem_addr a s`,
  CHEAT_TAC);;

let share_mem_op_add_clock_same = prove
 (`(~(labSem_state_clock s = 0) /\ share_mem_op m n a s = NONE ==>
    share_mem_op m n a (labSem_state_clock_fupd (K (extra +
      labSem_state_clock s)) s) = NONE) /\
   (~(labSem_state_clock s = 0) /\ share_mem_op m n a s = SOME (FFI_return f
     l',r) ==>
    share_mem_op m n a (labSem_state_clock_fupd (K (extra +
      labSem_state_clock s)) s) =
      SOME (FFI_return f l',labSem_state_clock_fupd (K (extra +
        labSem_state_clock r)) r)) /\
   (~(labSem_state_clock s = 0) /\ share_mem_op m n a s = SOME (FFI_final
     f2,r2) ==>
    share_mem_op m n a (labSem_state_clock_fupd (K (extra +
      labSem_state_clock s)) s) =
      SOME (FFI_final f2,(labSem_state_clock_fupd (K (extra +
        labSem_state_clock r2)) r2)))`,
  CHEAT_TAC);;

(* evaluate_add_clock_io_events_mono *)
let labProps_evaluate_add_clock_io_events_mono = prove
 (`!s. ffi_state_io_events (labSem_state_ffi
   (SND (labSem_evaluate s))) <<= ffi_state_io_events (labSem_state_ffi
   (SND (labSem_evaluate (labSem_state_clock_fupd (K (labSem_state_clock s
     + extra)) s))))`,
  CHEAT_TAC);;

let align_dm_def = new_definition
  `align_dm (s:('a,'c,'ffi)labSem_state) =
     (labSem_state_mem_domain_fupd (K (labSem_state_mem_domain s INTER
       byte_aligned)) s)`;;

let align_dm_const = prove
 (`labSem_state_clock
      (align_dm s) = labSem_state_clock s /\ labSem_state_pc
      (align_dm s) = labSem_state_pc s /\ labSem_state_code
      (align_dm s) = labSem_state_code s /\ labSem_state_mem
      (align_dm s) = labSem_state_mem s /\ labSem_state_shared_mem_domain
      (align_dm s) = labSem_state_shared_mem_domain s /\ labSem_state_be
      (align_dm s) = labSem_state_be s /\ labSem_state_len_reg
      (align_dm s) = labSem_state_len_reg s /\ labSem_state_link_reg
      (align_dm s) = labSem_state_link_reg s /\ labSem_state_ptr_reg
      (align_dm s) = labSem_state_ptr_reg s /\ labSem_state_ptr2_reg
      (align_dm s) = labSem_state_ptr2_reg s /\ labSem_state_len2_reg
      (align_dm s) = labSem_state_len2_reg s /\ labSem_state_io_regs
      (align_dm s) = labSem_state_io_regs s /\ labSem_state_io_fp_regs
      (align_dm s) = labSem_state_io_fp_regs s /\ labSem_state_code_buffer
      (align_dm s) = labSem_state_code_buffer s /\ labSem_state_compile
      (align_dm s) = labSem_state_compile s /\ labSem_state_compile_oracle
      (align_dm s) = labSem_state_compile_oracle s /\ labSem_state_ffi
      (align_dm s) = labSem_state_ffi s /\ labSem_state_failed
      (align_dm s) = labSem_state_failed s`,
  CHEAT_TAC);;
add_simp align_dm_const;;

let align_dm_with_clock = prove
 (`align_dm (labSem_state_clock_fupd (K k) s) = labSem_state_clock_fupd (K k)
  (align_dm s)`,
  CHEAT_TAC);;

let asm_fetch_align_dm = prove
 (`asm_fetch (align_dm s) = asm_fetch s`,
  CHEAT_TAC);;
add_simp asm_fetch_align_dm;;

let read_reg_align_dm = prove
 (`labSem_state_regs (align_dm s) n = labSem_state_regs s n`,
  CHEAT_TAC);;
add_simp read_reg_align_dm;;

let upd_reg_align_dm = prove
 (`labSem_upd_reg x y (align_dm s) = align_dm (labSem_upd_reg x y s)`,
  CHEAT_TAC);;
add_simp upd_reg_align_dm;;

let upd_mem_align_dm = prove
 (`labSem_upd_mem x y (align_dm s) = align_dm (labSem_upd_mem x y s)`,
  CHEAT_TAC);;
add_simp upd_mem_align_dm;;

let binop_upd_align_dm = prove
 (`labSem_binop_upd x y z w (align_dm s) = align_dm (labSem_binop_upd x y z w
  s)`,
  CHEAT_TAC);;
add_simp binop_upd_align_dm;;

let reg_imm_align_dm = prove
 (`labSem_reg_imm r (align_dm s) = labSem_reg_imm r s`,
  CHEAT_TAC);;
add_simp reg_imm_align_dm;;

let assert_align_dm = prove
 (`labSem_assert b (align_dm s) = align_dm (labSem_assert b s)`,
  CHEAT_TAC);;
add_simp assert_align_dm;;

let arith_upd_align_dm = prove
 (`labSem_arith_upd x (align_dm s) = align_dm (labSem_arith_upd x s)`,
  CHEAT_TAC);;
add_simp arith_upd_align_dm;;

let fp_upd_align_dm = prove
 (`labSem_fp_upd f (align_dm s) = align_dm (labSem_fp_upd f s)`,
  CHEAT_TAC);;
add_simp fp_upd_align_dm;;

let addr_align_dm = prove
 (`labSem_addr a (align_dm s) = labSem_addr a s`,
  CHEAT_TAC);;
add_simp addr_align_dm;;

let mem_load_align_dm = prove
 (`good_dimindex (:'a) ==>
   labSem_mem_load n (a:'a asm_addr) (align_dm s) = align_dm
     (labSem_mem_load n a s)`,
  CHEAT_TAC);;

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let mem_load_32_align_dm = prove
 (cake_as_vars (fun () ->
    `mem_load_32 (labSem_state_mem s) (labSem_state_mem_domain s) be x = SOME y
  ==>
     mem_load_32 (labSem_state_mem s) (labSem_state_mem_domain (align_dm
       s)) be x = SOME y`),
  CHEAT_TAC);;

let mem_load32_align_dm = prove
 (`good_dimindex (:'a) ==>
   mem_load32 n (a:'a asm_addr) (align_dm s) = align_dm (mem_load32 n a s)`,
  CHEAT_TAC);;

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let mem_load_byte_aux_align_dm = prove
 (cake_as_vars (fun () ->
    `mem_load_byte_aux (labSem_state_mem s) (labSem_state_mem_domain s) be x =
  SOME y ==>
     mem_load_byte_aux (labSem_state_mem s) (labSem_state_mem_domain
       (align_dm s)) be x = SOME y`),
  CHEAT_TAC);;

let mem_load_byte_align_dm = prove
 (`good_dimindex (:'a) ==>
   mem_load_byte n (a:'a asm_addr) (align_dm s) = align_dm (mem_load_byte
     n a s)`,
  CHEAT_TAC);;

let mem_store_align_dm = prove
 (`good_dimindex (:'a) ==>
   labSem_mem_store n (a:'a asm_addr) (align_dm s) = align_dm
     (labSem_mem_store n a s)`,
  CHEAT_TAC);;

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let mem_store_32_align_dm = prove
 (cake_as_vars (fun () ->
    `mem_store_32 mem (labSem_state_mem_domain s) be x c = SOME y ==>
     mem_store_32 mem (labSem_state_mem_domain (align_dm s)) be x c =
       SOME y`),
  CHEAT_TAC);;

let mem_store32_align_dm = prove
 (`good_dimindex (:'a) ==>
   mem_store32 n (a:'a asm_addr) (align_dm s) = align_dm (mem_store32 n a
     s)`,
  CHEAT_TAC);;

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let mem_store_byte_aux_align_dm = prove
 (cake_as_vars (fun () ->
    `mem_store_byte_aux mem (labSem_state_mem_domain s) be x c = SOME y ==>
     mem_store_byte_aux mem (labSem_state_mem_domain (align_dm s)) be x
       c = SOME y`),
  CHEAT_TAC);;

let mem_store_byte_align_dm = prove
 (`good_dimindex (:'a) ==>
   mem_store_byte n (a:'a asm_addr) (align_dm s) = align_dm
     (mem_store_byte n a s)`,
  CHEAT_TAC);;

let mem_op_align_dm = prove
 (`good_dimindex (:'a) ==>
   labSem_mem_op m n (a:'a asm_addr) (align_dm s) = align_dm
     (labSem_mem_op m n a s)`,
  CHEAT_TAC);;

let asm_inst_align_dm = prove
 (`good_dimindex (:'a) ==>
   asm_inst (i:'a asm_inst) (align_dm s) = align_dm (asm_inst i s)`,
  CHEAT_TAC);;

let dec_clock_align_dm = prove
 (`labSem_dec_clock (align_dm s) = align_dm (labSem_dec_clock s)`,
  CHEAT_TAC);;
add_simp dec_clock_align_dm;;

let inc_pc_align_dm = prove
 (`inc_pc (align_dm s) = align_dm (inc_pc s)`,
  CHEAT_TAC);;
add_simp inc_pc_align_dm;;

let upd_pc_align_dm = prove
 (`labSem_upd_pc p (align_dm s) = align_dm (labSem_upd_pc p s)`,
  CHEAT_TAC);;
add_simp upd_pc_align_dm;;

let get_pc_value_align_dm = prove
 (`get_pc_value x (align_dm s) = get_pc_value x s`,
  CHEAT_TAC);;
add_simp get_pc_value_align_dm;;

let get_ret_Loc_align_dm = prove
 (`get_ret_Loc (align_dm s) = get_ret_Loc s`,
  CHEAT_TAC);;
add_simp get_ret_Loc_align_dm;;

let read_bytearray_mem_load_byte_aux_align_dm = prove
 (`!y x.
    read_bytearray x y (mem_load_byte_aux (labSem_state_mem s)
      (labSem_state_mem_domain (align_dm s)) (labSem_state_be s)) =
   read_bytearray x y (mem_load_byte_aux (labSem_state_mem s)
     (labSem_state_mem_domain s) (labSem_state_be s))`,
  CHEAT_TAC);;
add_simp read_bytearray_mem_load_byte_aux_align_dm;;

let write_bytearray_align_dm = prove
 (`!y x. write_bytearray x y (labSem_state_mem s) (labSem_state_mem_domain
  (align_dm s)) (labSem_state_be s) =
   write_bytearray x y (labSem_state_mem s) (labSem_state_mem_domain s)
     (labSem_state_be s)`,
  CHEAT_TAC);;
add_simp write_bytearray_align_dm;;

let share_mem_op_align_dm_simp = prove
 (`(share_mem_op m r a s = NONE ==> share_mem_op m r a (align_dm s) = NONE) /\
   (share_mem_op m r a s = SOME (FFI_final f,s') ==>
   share_mem_op m r a (align_dm s) = SOME (FFI_final f,align_dm s')) /\
   (share_mem_op m r a s = SOME (FFI_return fs l,s') ==>
   share_mem_op m r a (align_dm s) = SOME (FFI_return fs l,align_dm s'))`,
  CHEAT_TAC);;
add_simp share_mem_op_align_dm_simp;;

let evaluate_align_dm = prove
 (`good_dimindex (:'a) ==>
   (!(s:('a,'c,'ffi)labSem_state).
      labSem_evaluate (align_dm s) =
      (let (r,s') = labSem_evaluate s in (r,align_dm s')))`,
  CHEAT_TAC);;

let implements_align_dm = prove
 (`good_dimindex (:'a) ==>
   implements' T {labSem_semantics (s:('a,'c,'ffi)labSem_state)}
     {labSem_semantics (align_dm s)}`,
  CHEAT_TAC);;

(** align_sdm **)

let align_sdm_def = new_definition
  `align_sdm (s:('a,'c,'ffi)labSem_state) =
     (labSem_state_shared_mem_domain_fupd (K
       (labSem_state_shared_mem_domain s INTER byte_aligned)) s)`;;

let align_sdm_const = prove
 (`labSem_state_clock
      (align_sdm s) = labSem_state_clock s /\ labSem_state_pc
      (align_sdm s) = labSem_state_pc s /\ labSem_state_code
      (align_sdm s) = labSem_state_code s /\ labSem_state_mem
      (align_sdm s) = labSem_state_mem s /\ labSem_state_mem_domain
      (align_sdm s) = labSem_state_mem_domain s /\ labSem_state_be
      (align_sdm s) = labSem_state_be s /\ labSem_state_len_reg
      (align_sdm s) = labSem_state_len_reg s /\ labSem_state_link_reg
      (align_sdm s) = labSem_state_link_reg s /\ labSem_state_ptr_reg
      (align_sdm s) = labSem_state_ptr_reg s /\ labSem_state_ptr2_reg
      (align_sdm s) = labSem_state_ptr2_reg s /\ labSem_state_len2_reg
      (align_sdm s) = labSem_state_len2_reg s /\ labSem_state_io_regs
      (align_sdm s) = labSem_state_io_regs s /\ labSem_state_io_fp_regs
      (align_sdm s) = labSem_state_io_fp_regs s /\ labSem_state_code_buffer
      (align_sdm s) = labSem_state_code_buffer s /\ labSem_state_compile
      (align_sdm s) = labSem_state_compile s /\ labSem_state_compile_oracle
      (align_sdm s) = labSem_state_compile_oracle s /\ labSem_state_ffi
      (align_sdm s) = labSem_state_ffi s /\ labSem_state_failed
      (align_sdm s) = labSem_state_failed s`,
  CHEAT_TAC);;
add_simp align_sdm_const;;

let align_sdm_with_clock = prove
 (`align_sdm (labSem_state_clock_fupd (K k) s) = labSem_state_clock_fupd (K
  k) (align_sdm s)`,
  CHEAT_TAC);;

let asm_fetch_align_sdm = prove
 (`asm_fetch (align_sdm s) = asm_fetch s`,
  CHEAT_TAC);;
add_simp asm_fetch_align_sdm;;

let read_reg_align_sdm = prove
 (`labSem_state_regs (align_sdm s) n = labSem_state_regs s n`,
  CHEAT_TAC);;
add_simp read_reg_align_sdm;;

let upd_reg_align_sdm = prove
 (`labSem_upd_reg x y (align_sdm s) = align_sdm (labSem_upd_reg x y s)`,
  CHEAT_TAC);;
add_simp upd_reg_align_sdm;;

let upd_mem_align_sdm = prove
 (`labSem_upd_mem x y (align_sdm s) = align_sdm (labSem_upd_mem x y s)`,
  CHEAT_TAC);;
add_simp upd_mem_align_sdm;;

let binop_upd_align_sdm = prove
 (`labSem_binop_upd x y z w (align_sdm s) = align_sdm (labSem_binop_upd x y z
  w s)`,
  CHEAT_TAC);;
add_simp binop_upd_align_sdm;;

let reg_imm_align_sdm = prove
 (`labSem_reg_imm r (align_sdm s) = labSem_reg_imm r s`,
  CHEAT_TAC);;
add_simp reg_imm_align_sdm;;

let assert_align_sdm = prove
 (`labSem_assert b (align_sdm s) = align_sdm (labSem_assert b s)`,
  CHEAT_TAC);;
add_simp assert_align_sdm;;

let arith_upd_align_sdm = prove
 (`labSem_arith_upd x (align_sdm s) = align_sdm (labSem_arith_upd x s)`,
  CHEAT_TAC);;
add_simp arith_upd_align_sdm;;

let fp_upd_align_sdm = prove
 (`labSem_fp_upd f (align_sdm s) = align_sdm (labSem_fp_upd f s)`,
  CHEAT_TAC);;
add_simp fp_upd_align_sdm;;

let addr_align_sdm = prove
 (`labSem_addr a (align_sdm s) = labSem_addr a s`,
  CHEAT_TAC);;
add_simp addr_align_sdm;;

let mem_load_align_sdm = prove
 (`labSem_mem_load n (a:'a asm_addr) (align_sdm s) = align_sdm
  (labSem_mem_load n a s)`,
  CHEAT_TAC);;

let mem_load32_align_sdm = prove
 (`mem_load32 n (a:'a asm_addr) (align_sdm s) = align_sdm (mem_load32 n a s)`,
  CHEAT_TAC);;

let mem_load_byte_align_sdm = prove
 (`mem_load_byte n (a:'a asm_addr) (align_sdm s) = align_sdm (mem_load_byte n
  a s)`,
  CHEAT_TAC);;

let mem_store_align_sdm = prove
 (`labSem_mem_store n (a:'a asm_addr) (align_sdm s) = align_sdm
  (labSem_mem_store n a s)`,
  CHEAT_TAC);;

let mem_store32_align_sdm = prove
 (`mem_store32 n (a:'a asm_addr) (align_sdm s) = align_sdm (mem_store32 n a
  s)`,
  CHEAT_TAC);;

let mem_store_byte_align_sdm = prove
 (`mem_store_byte n (a:'a asm_addr) (align_sdm s) = align_sdm (mem_store_byte
  n a s)`,
  CHEAT_TAC);;

let mem_op_align_sdm = prove
 (`labSem_mem_op m n (a:'a asm_addr) (align_sdm s) = align_sdm (labSem_mem_op
  m n a s)`,
  CHEAT_TAC);;

let asm_inst_align_sdm = prove
 (`asm_inst (i:'a asm_inst) (align_sdm s) = align_sdm (asm_inst i s)`,
  CHEAT_TAC);;

let dec_clock_align_sdm = prove
 (`labSem_dec_clock (align_sdm s) = align_sdm (labSem_dec_clock s)`,
  CHEAT_TAC);;
add_simp dec_clock_align_sdm;;

let inc_pc_align_sdm = prove
 (`inc_pc (align_sdm s) = align_sdm (inc_pc s)`,
  CHEAT_TAC);;
add_simp inc_pc_align_sdm;;

let upd_pc_align_sdm = prove
 (`labSem_upd_pc p (align_sdm s) = align_sdm (labSem_upd_pc p s)`,
  CHEAT_TAC);;
add_simp upd_pc_align_sdm;;

let get_pc_value_align_sdm = prove
 (`get_pc_value x (align_sdm s) = get_pc_value x s`,
  CHEAT_TAC);;
add_simp get_pc_value_align_sdm;;

let get_ret_Loc_align_sdm = prove
 (`get_ret_Loc (align_sdm s) = get_ret_Loc s`,
  CHEAT_TAC);;
add_simp get_ret_Loc_align_sdm;;

let read_bytearray_mem_load_byte_aux_align_sdm = prove
 (`!y x.
    read_bytearray x y (mem_load_byte_aux (labSem_state_mem s)
      (labSem_state_mem_domain (align_sdm s)) (labSem_state_be s)) =
   read_bytearray x y (mem_load_byte_aux (labSem_state_mem s)
     (labSem_state_mem_domain s) (labSem_state_be s))`,
  CHEAT_TAC);;
add_simp read_bytearray_mem_load_byte_aux_align_sdm;;

let write_bytearray_align_sdm = prove
 (`!y x. write_bytearray x y (labSem_state_mem s) (labSem_state_mem_domain
  (align_sdm s)) (labSem_state_be s) =
   write_bytearray x y (labSem_state_mem s) (labSem_state_mem_domain s)
     (labSem_state_be s)`,
  CHEAT_TAC);;
add_simp write_bytearray_align_sdm;;

let align_sdm_aligned = prove
 (`good_dimindex (:'a) ==>
   (((x:'a word) IN labSem_state_shared_mem_domain s /\ w2n x MOD (dimindex
     (:'a) DIV 8) = 0) <=>
     x IN labSem_state_shared_mem_domain (align_sdm s))`,
  CHEAT_TAC);;

let share_mem_load_align_sdm = prove
 (`good_dimindex (:'a) ==>
   (share_mem_load r (ad:'a asm_addr) (align_sdm s) n = NONE <=>
      share_mem_load r ad s n = NONE) /\
   (share_mem_load r ad s n = SOME (res,s') ==>
    share_mem_load r ad (align_sdm s) n = SOME (res,align_sdm s'))`,
  CHEAT_TAC);;

let share_mem_store_align_sdm = prove
 (`good_dimindex (:'a) ==>
   (share_mem_store r (ad:'a asm_addr) (align_sdm s) n = NONE <=>
      share_mem_store r ad s n = NONE) /\
   (share_mem_store r ad s n = SOME (res,s') ==>
    share_mem_store r ad (align_sdm s) n = SOME (res,align_sdm s'))`,
  CHEAT_TAC);;

let share_mem_op_align_sdm_simp = prove
 (`good_dimindex (:'a) ==>
   (share_mem_op m r (a:'a asm_addr) s = NONE <=> share_mem_op m r a
     (align_sdm s) = NONE) /\
   (share_mem_op m r a s = SOME (res,s') ==>
   share_mem_op m r a (align_sdm s) = SOME (res,align_sdm s'))`,
  CHEAT_TAC);;
add_simp share_mem_op_align_sdm_simp;;

let evaluate_align_sdm = prove
 (`good_dimindex (:'a) ==>
   (!(s:('a,'c,'ffi)labSem_state).
      labSem_evaluate (align_sdm s) =
      (let (r,s') = labSem_evaluate s in (r,align_sdm s')))`,
  CHEAT_TAC);;

let implements_align_sdm = prove
 (`good_dimindex (:'a) ==>
   implements' T {labSem_semantics (s:('a,'c,'ffi)labSem_state)}
     {labSem_semantics (align_sdm s)}`,
  CHEAT_TAC);;


(* asm_ok checks coming into lab_to_target *)
let line_ok_pre_def = new_definition
  `line_ok_pre c x2 =
     match (c,x2) with
       ((c:'a asm_config),lab_Asm b bytes l) -> asm_ok (cbw_to_asm b) c
     | (c,_) -> T`;;

let sec_ok_pre_def = define_general
  `sec_ok_pre c (Section k ls) <=>
     ALL (line_ok_pre c) ls`;;
add_simp sec_ok_pre_def;;

(* HOL4 labPropsScript.sml:1257: the overload all_enc_ok_pre, which the port
   expands *)

(* invariant: labels have correct section number and are non-zero *)

let sec_label_ok_def = new_definition
  `sec_label_ok k x2' =
     match x2' with
       lab_Label l1 l2 len -> l1 = k /\ ~(l2 = 0)
     | _ -> T`;;
add_simp sec_label_ok_def;;

let sec_labels_ok_def = define_general
  `sec_labels_ok (Section k ls) <=> ALL (sec_label_ok k) ls`;;
add_simp sec_labels_ok_def;;

let sec_label_ok_extract_labels = prove
 (`ALL (sec_label_ok n1) lines /\
   MEM (n1',n2) (labProps_extract_labels lines) ==>
   n1' = n1 /\ ~(n2 = 0)`,
  CHEAT_TAC);;

let EVERY_sec_label_ok = prove
 (`ALL (\(l1,l2). l1 = n /\ ~(l2 = 0)) (labProps_extract_labels l) <=>
    // ∧
    // ALL_DISTINCT (extract_labels l)
    ALL (sec_label_ok n) l`,
  CHEAT_TAC);;

let line_get_code_labels_extract_labels = prove
 (`!l.
   UNIONS (IMAGE line_get_code_labels (set_of_list l)) =
   IMAGE SND (set_of_list (labProps_extract_labels l))`,
  CHEAT_TAC);;

let get_code_labels_extract_labels = prove
 (`!code.
   ALL sec_labels_ok code ==>
   labProps_get_code_labels code =
   IMAGE (\s. (Section_num s,0)) (set_of_list code) UNION
   set_of_list (FLAT (MAP (labProps_extract_labels o Section_lines) code))`,
  CHEAT_TAC);;

let no_install_def = new_definition
  `labProps_no_install code <=>
   (!p w bytes l. ~(asm_fetch_aux p code =
       SOME (lab_LabAsm lab_Install w bytes l)))`;;

let no_share_mem_inst_def = new_definition
  `no_share_mem_inst code <=>
   (!p op re a inst' len. ~(asm_fetch_aux p code =
       SOME (lab_Asm (ShareMem op re a) inst' len)))`;;

(* and the names it reads as variables are constants again *)
let _ = do_list unhide_constant
  ["mem"];;

(* and the interface *)
let _ = unhide_overloads ();;
