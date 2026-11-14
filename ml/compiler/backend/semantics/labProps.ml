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
needs "lib/pegexec.ml";;
needs "misc/misc.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/proofs/semanticsProps.ml";;

(* the theories whose names the Ancestors blocks of the source
   bring, which are the ones that its statements read: the
   overloads of every other theory come out of the interface
   while this file loads *)
let _ = hol4_ancestors "labProps"
  ["ffi"; "labSem"; "lab_to_target"; "semanticsProps"; "wordSem"];;

(* this file reads the name of a record field as a variable and
   needs the accessors of that field as well, so only these
   pairs come out of the interface *)
let _ = hide_overloads
  ["code_buffer","code_buffer";
   "failed","pegexec_failed"];;

let _ = do_list hide_constant ["mem"];;

let _ = size_thms "line";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let labProps_extract_labels_def,labProps_extract_labels_ind = define_wf
  `MEASURE (\x0. list_size (line_size (\x. 0)) x0)`
  [`labProps_extract_labels x1 =
        match x1 with
          [] -> []
        | CONS (labLang_Label l1 l2 _2) xs -> CONS (l1,l2)
          (labProps_extract_labels xs)
        | (CONS x xs) -> labProps_extract_labels xs`];;

(* HOL4 labPropsScript.sml:18: ML code, not ported *)

let extract_labels_append = prove
 (`!A B.
   labProps_extract_labels (APPEND A B) = APPEND
     (labProps_extract_labels A) (labProps_extract_labels B)`,
  CHEAT_TAC);;

let labs_of_def = new_definition
  `labs_of x1 =
      match x1 with
        labLang_LocValue _4 (labLang_Lab n1 n2) -> {(n1,n2)}
      | (labLang_Jump (labLang_Lab n1 n2)) -> {(n1,n2)}
      | (labLang_JumpCmp _5 _6 _7 (labLang_Lab n1 n2)) -> {(n1,n2)}
      | _8 -> {}`;;

let line_get_labels_def = new_definition
  `line_get_labels x1 =
      match x1 with
        labLang_LabAsm a _9 _10 _11 -> labs_of a
      | _12 -> {}`;;

let sec_get_labels_def = define_general
  [`sec_get_labels (Section _13 lines) =
     UNIONS (IMAGE line_get_labels (set_of_list lines))`];;

let labProps_get_labels_def = new_definition
  `labProps_get_labels code = UNIONS (IMAGE sec_get_labels
  (set_of_list code))`;;

let get_labels_cons = prove
 (`labProps_get_labels (CONS x xs) = sec_get_labels x UNION
  labProps_get_labels xs`,
  CHEAT_TAC);;

let line_get_code_labels_def = new_definition
  `line_get_code_labels x1 =
      match x1 with
        labLang_Label _16 l _17 -> {l}
      | _18 -> {}`;;

let sec_get_code_labels_def = define_general
  [`sec_get_code_labels (Section n1 lines) =
     (n1,0) INSERT
     IMAGE (\n2. (n1,n2)) (UNIONS (IMAGE line_get_code_labels
       (set_of_list lines)))`];;

let labProps_get_code_labels_def = new_definition
  `labProps_get_code_labels code = UNIONS (IMAGE sec_get_code_labels
  (set_of_list code))`;;

(* [simp] *)
let get_code_labels_nil = prove
 (`labProps_get_code_labels [] = {}`,
  CHEAT_TAC);;

let get_code_labels_cons = prove
 (`labProps_get_code_labels (CONS s secs) = sec_get_code_labels s
  UNION labProps_get_code_labels secs`,
  CHEAT_TAC);;

let sec_ends_with_label_def = define_general
  [`sec_ends_with_label (Section _19 ls) <=>
     ~(NULL ls) /\ is_Label (LAST ls)`];;

(* [simp] *)
let reg_imm_with_clock = prove
 (`labSem_reg_imm r (state_clock_fupd (K z) s) = labSem_reg_imm r s`,
  CHEAT_TAC);;

(* [simp] *)
let asm_inst_with_clock = prove
 (`asm_inst i (state_clock_fupd (K z) s) = state_clock_fupd (K z)
  (asm_inst i s)`,
  CHEAT_TAC);;

(* [simp] *)
let read_reg_inc_pc = prove
 (`regs (inc_pc s) r = regs s r`,
  CHEAT_TAC);;

(* with_same_clock[simp] *)
let labProps_with_same_clock = prove
 (`(state_clock_fupd (K (state_clock s)) s) = s`,
  CHEAT_TAC);;

let inc_pc_dec_clock = prove
 (`inc_pc (labSem_dec_clock x) = labSem_dec_clock (inc_pc x)`,
  CHEAT_TAC);;

(* [simp] *)
let update_simps = prove
 (`(state_ffi (labSem_upd_pc x s) = state_ffi s) /\
    (state_ffi (labSem_dec_clock s) = state_ffi s) /\
    (pc (labSem_upd_pc x s) = x) /\
    (pc (labSem_dec_clock s) = pc s) /\
    (state_clock (labSem_upd_pc x s) = state_clock s) /\
    (state_ffi (labSem_upd_pc x s) = state_ffi s) /\
    (state_clock (labSem_dec_clock s) = state_clock s - 1) /\
    (len_reg (labSem_dec_clock s) = len_reg s) /\
    (len2_reg (labSem_dec_clock s) = len2_reg s) /\
    (link_reg (labSem_dec_clock s) = link_reg s) /\
    (state_code (labSem_dec_clock s) = state_code s) /\
    (ptr_reg (labSem_dec_clock s) = ptr_reg s) /\
    (ptr2_reg (labSem_dec_clock s) = ptr2_reg s) /\
    (state_ffi (labSem_dec_clock s) = state_ffi s) /\
    (len_reg (labSem_upd_pc x s) = len_reg s) /\
    (len2_reg (labSem_upd_pc x s) = len2_reg s) /\
    (link_reg (labSem_upd_pc x s) = link_reg s) /\
    (state_code (labSem_upd_pc x s) = state_code s) /\
    (ptr_reg (labSem_upd_pc x s) = ptr_reg s) /\
    (ptr2_reg (labSem_upd_pc x s) = ptr2_reg s) /\
    (labSem_state_mem_domain (labSem_upd_pc x s) =
      labSem_state_mem_domain s) /\
    (labSem_state_shared_mem_domain (labSem_upd_pc x s) =
      labSem_state_shared_mem_domain s) /\
    (failed (labSem_upd_pc x s) = failed s) /\
    (be (labSem_upd_pc x s) = be s) /\
    (labSem_state_mem (labSem_upd_pc x s) = labSem_state_mem s) /\
    (regs (labSem_upd_pc x s) = regs s) /\
    (fp_regs (labSem_upd_pc x s) = fp_regs s) /\
    (state_ffi (labSem_upd_pc x s) = state_ffi s) /\
    (ptr_reg (inc_pc s) = ptr_reg s) /\
    (ptr2_reg (inc_pc s) = ptr2_reg s) /\
    (len_reg (inc_pc s) = len_reg s) /\
    (len2_reg (inc_pc s) = len2_reg s) /\
    (link_reg (inc_pc s) = link_reg s) /\
    (state_code (inc_pc s) = state_code s) /\
    (be (inc_pc s) = be s) /\
    (failed (inc_pc s) = failed s) /\
    (labSem_state_mem_domain (inc_pc s) = labSem_state_mem_domain s)
      /\
    (labSem_state_shared_mem_domain (inc_pc s) =
      labSem_state_shared_mem_domain s) /\
    (labSem_state_io_regs (inc_pc s) = labSem_state_io_regs s) /\
    (labSem_state_io_fp_regs (inc_pc s) = labSem_state_io_fp_regs s)
      /\
    (labSem_state_cc_regs (inc_pc s) = labSem_state_cc_regs s) /\
    (labSem_state_cc_fp_regs (inc_pc s) = labSem_state_cc_fp_regs s)
      /\
    (compile (inc_pc s) = compile s) /\
    (compile_oracle (inc_pc s) = compile_oracle s) /\
    (state_code_buffer (inc_pc s) = state_code_buffer s) /\
    (labSem_state_mem (inc_pc s) = labSem_state_mem s) /\
    (regs (inc_pc s) = regs s) /\
    (fp_regs (inc_pc s) = fp_regs s) /\
    (pc (inc_pc s) = pc s + 1) /\
    (state_ffi (inc_pc s) = state_ffi s)`,
  CHEAT_TAC);;

(* binop_upd_consts[simp] *)
let labProps_binop_upd_consts = prove
 (`labSem_state_mem_domain
      (labSem_binop_upd a b c d x) = labSem_state_mem_domain x /\
        labSem_state_shared_mem_domain
      (labSem_binop_upd a b c d x) = labSem_state_shared_mem_domain x
        /\ ptr_reg
      (labSem_binop_upd a b c d x) = ptr_reg x /\ ptr2_reg
      (labSem_binop_upd a b c d x) = ptr2_reg x /\ len_reg
      (labSem_binop_upd a b c d x) = len_reg x /\ len2_reg
      (labSem_binop_upd a b c d x) = len2_reg x /\ link_reg
      (labSem_binop_upd a b c d x) = link_reg x /\ state_code
      (labSem_binop_upd a b c d x) = state_code x /\ be
      (labSem_binop_upd a b c d x) = be x /\ labSem_state_mem
      (labSem_binop_upd a b c d x) = labSem_state_mem x /\
        labSem_state_io_regs
      (labSem_binop_upd a b c d x) = labSem_state_io_regs x /\
        labSem_state_io_fp_regs
      (labSem_binop_upd a b c d x) = labSem_state_io_fp_regs x /\
        labSem_state_cc_regs
      (labSem_binop_upd a b c d x) = labSem_state_cc_regs x /\
        labSem_state_cc_fp_regs
      (labSem_binop_upd a b c d x) = labSem_state_cc_fp_regs x /\
        compile
      (labSem_binop_upd a b c d x) = compile x /\ compile_oracle
      (labSem_binop_upd a b c d x) = compile_oracle x /\
        state_code_buffer
      (labSem_binop_upd a b c d x) = state_code_buffer x /\ pc
      (labSem_binop_upd a b c d x) = pc x /\ state_ffi
      (labSem_binop_upd a b c d x) = state_ffi x`,
  CHEAT_TAC);;

(* arith_upd_consts[simp] *)
let labProps_arith_upd_consts = prove
 (`labSem_state_mem_domain
      (labSem_arith_upd a x) = labSem_state_mem_domain x /\
        labSem_state_shared_mem_domain
      (labSem_arith_upd a x) = labSem_state_shared_mem_domain x /\
        ptr_reg
      (labSem_arith_upd a x) = ptr_reg x /\ ptr2_reg
      (labSem_arith_upd a x) = ptr2_reg x /\ len_reg
      (labSem_arith_upd a x) = len_reg x /\ len2_reg
      (labSem_arith_upd a x) = len2_reg x /\ link_reg
      (labSem_arith_upd a x) = link_reg x /\ state_code
      (labSem_arith_upd a x) = state_code x /\ be
      (labSem_arith_upd a x) = be x /\ labSem_state_mem
      (labSem_arith_upd a x) = labSem_state_mem x /\
        labSem_state_io_regs
      (labSem_arith_upd a x) = labSem_state_io_regs x /\
        labSem_state_io_fp_regs
      (labSem_arith_upd a x) = labSem_state_io_fp_regs x /\
        labSem_state_cc_regs
      (labSem_arith_upd a x) = labSem_state_cc_regs x /\
        labSem_state_cc_fp_regs
      (labSem_arith_upd a x) = labSem_state_cc_fp_regs x /\ compile
      (labSem_arith_upd a x) = compile x /\ compile_oracle
      (labSem_arith_upd a x) = compile_oracle x /\ state_code_buffer
      (labSem_arith_upd a x) = state_code_buffer x /\ pc
      (labSem_arith_upd a x) = pc x /\ state_ffi
      (labSem_arith_upd a x) = state_ffi x`,
  CHEAT_TAC);;

(* fp_upd_consts[simp] *)
let labProps_fp_upd_consts = prove
 (`labSem_state_mem_domain
      (labSem_fp_upd f x) = labSem_state_mem_domain x /\
        labSem_state_shared_mem_domain
      (labSem_fp_upd f x) = labSem_state_shared_mem_domain x /\
        ptr_reg
      (labSem_fp_upd f x) = ptr_reg x /\ len_reg
      (labSem_fp_upd f x) = len_reg x /\ ptr2_reg
      (labSem_fp_upd f x) = ptr2_reg x /\ len2_reg
      (labSem_fp_upd f x) = len2_reg x /\ link_reg
      (labSem_fp_upd f x) = link_reg x /\ state_code
      (labSem_fp_upd f x) = state_code x /\ labSem_state_cc_regs
      (labSem_fp_upd f x) = labSem_state_cc_regs x /\
        labSem_state_cc_fp_regs
      (labSem_fp_upd f x) = labSem_state_cc_fp_regs x /\
        state_code_buffer
      (labSem_fp_upd f x) = state_code_buffer x /\ compile
      (labSem_fp_upd f x) = compile x /\ compile_oracle
      (labSem_fp_upd f x) = compile_oracle x /\ be
      (labSem_fp_upd f x) = be x /\ labSem_state_mem
      (labSem_fp_upd f x) = labSem_state_mem x /\
        labSem_state_io_regs
      (labSem_fp_upd f x) = labSem_state_io_regs x /\
        labSem_state_io_fp_regs
      (labSem_fp_upd f x) = labSem_state_io_fp_regs x /\ pc
      (labSem_fp_upd f x) = pc x /\ state_ffi
      (labSem_fp_upd f x) = state_ffi x`,
  CHEAT_TAC);;

let line_length_def = define_cases
  [`line_length (labLang_Label k1 k2 l) = (if l = 0 then 0 else 1)`;
   `line_length (labLang_Asm b bytes l) = LENGTH bytes`;
   `line_length (labLang_LabAsm a w bytes l) = LENGTH bytes`];;

(* [simp] *)
let LENGTH_line_bytes = prove
 (`!x2. ~(is_Label x2) ==> (LENGTH (line_bytes x2) = line_length x2)`,
  CHEAT_TAC);;

(* HOL4 labPropsScript.sml:271-277: a theorem that HOL4 states as the
   value of an ML expression: case_eq_thms *)

(* HOL4 labPropsScript.sml:279-310: a theorem whose statement HOL
   Light does not read (tools/unstated.py): evaluate_io_events_mono *)

(* HOL4 labPropsScript.sml:312-334: a theorem whose statement HOL
   Light does not read (tools/unstated.py): evaluate_ADD_clock *)

(* HOL4 labPropsScript.sml:336-340: a theorem whose statement HOL
   Light does not read (tools/unstated.py): addr_add_clock_eq *)

let share_mem_op_add_clock_same = prove
 (`(~(state_clock s = 0) /\ share_mem_op m n a s = NONE ==>
    share_mem_op m n a (state_clock_fupd (K (extra + state_clock s))
      s) = NONE) /\
   (~(state_clock s = 0) /\ share_mem_op m n a s = SOME (FFI_return f
     l',r) ==>
    share_mem_op m n a (state_clock_fupd (K (extra + state_clock s))
      s) =
      SOME (FFI_return f l',state_clock_fupd (K (extra + state_clock
        r)) r)) /\
   (~(state_clock s = 0) /\ share_mem_op m n a s = SOME (FFI_final
     f2,r2) ==>
    share_mem_op m n a (state_clock_fupd (K (extra + state_clock s))
      s) =
      SOME (FFI_final f2,(state_clock_fupd (K (extra + state_clock
        r2)) r2)))`,
  CHEAT_TAC);;

(* HOL4 labPropsScript.sml:358-439: a theorem whose statement HOL
   Light does not read (tools/unstated.py):
   evaluate_add_clock_io_events_mono *)

let align_dm_def = new_definition
  `align_dm (s:('a,'c,'ffi)labSem_state) =
     (labSem_state_mem_domain_fupd (K (labSem_state_mem_domain s
       INTER byte_aligned)) s)`;;

(* [simp] *)
let align_dm_const = prove
 (`state_clock
      (align_dm s) = state_clock s /\ pc
      (align_dm s) = pc s /\ state_code
      (align_dm s) = state_code s /\ labSem_state_mem
      (align_dm s) = labSem_state_mem s /\
        labSem_state_shared_mem_domain
      (align_dm s) = labSem_state_shared_mem_domain s /\ be
      (align_dm s) = be s /\ len_reg
      (align_dm s) = len_reg s /\ link_reg
      (align_dm s) = link_reg s /\ ptr_reg
      (align_dm s) = ptr_reg s /\ ptr2_reg
      (align_dm s) = ptr2_reg s /\ len2_reg
      (align_dm s) = len2_reg s /\ labSem_state_io_regs
      (align_dm s) = labSem_state_io_regs s /\
        labSem_state_io_fp_regs
      (align_dm s) = labSem_state_io_fp_regs s /\ state_code_buffer
      (align_dm s) = state_code_buffer s /\ compile
      (align_dm s) = compile s /\ compile_oracle
      (align_dm s) = compile_oracle s /\ state_ffi
      (align_dm s) = state_ffi s /\ failed
      (align_dm s) = failed s`,
  CHEAT_TAC);;

let align_dm_with_clock = prove
 (`align_dm (state_clock_fupd (K k) s) = state_clock_fupd (K k)
  (align_dm s)`,
  CHEAT_TAC);;

(* [simp] *)
let asm_fetch_align_dm = prove
 (`asm_fetch (align_dm s) = asm_fetch s`,
  CHEAT_TAC);;

(* [simp] *)
let read_reg_align_dm = prove
 (`regs (align_dm s) n = regs s n`,
  CHEAT_TAC);;

(* [simp] *)
let upd_reg_align_dm = prove
 (`labSem_upd_reg x y (align_dm s) = align_dm (labSem_upd_reg x y s)`,
  CHEAT_TAC);;

(* [simp] *)
let upd_mem_align_dm = prove
 (`labSem_upd_mem x y (align_dm s) = align_dm (labSem_upd_mem x y s)`,
  CHEAT_TAC);;

(* [simp] *)
let binop_upd_align_dm = prove
 (`labSem_binop_upd x y z w (align_dm s) = align_dm (labSem_binop_upd
  x y z w s)`,
  CHEAT_TAC);;

(* [simp] *)
let reg_imm_align_dm = prove
 (`labSem_reg_imm r (align_dm s) = labSem_reg_imm r s`,
  CHEAT_TAC);;

(* [simp] *)
let assert_align_dm = prove
 (`labSem_assert b (align_dm s) = align_dm (labSem_assert b s)`,
  CHEAT_TAC);;

(* HOL4 labPropsScript.sml:517-522: a theorem whose statement HOL
   Light does not read (tools/unstated.py): arith_upd_align_dm *)

(* HOL4 labPropsScript.sml:524-529: a theorem whose statement HOL
   Light does not read (tools/unstated.py): fp_upd_align_dm *)

(* HOL4 labPropsScript.sml:531-535: a theorem whose statement HOL
   Light does not read (tools/unstated.py): addr_align_dm *)

(* HOL4 labPropsScript.sml:537-570: a theorem whose statement HOL
   Light does not read (tools/unstated.py): mem_load_align_dm *)

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let mem_load_32_align_dm = prove
 (cake_as_vars (fun () ->
    `mem_load_32 (labSem_state_mem s) (labSem_state_mem_domain s) be x =
  SOME y ==>
     mem_load_32 (labSem_state_mem s) (labSem_state_mem_domain
       (align_dm s)) be x = SOME y`),
  CHEAT_TAC);;

let mem_load32_align_dm = prove
 (`good_dimindex (:'a) ==>
   mem_load32 n (a:'a asm_addr) (align_dm s) = align_dm (mem_load32
     n a s)`,
  CHEAT_TAC);;

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let mem_load_byte_aux_align_dm = prove
 (cake_as_vars (fun () ->
    `mem_load_byte_aux (labSem_state_mem s) (labSem_state_mem_domain s)
  be x = SOME y ==>
     mem_load_byte_aux (labSem_state_mem s)
       (labSem_state_mem_domain (align_dm s)) be x = SOME y`),
  CHEAT_TAC);;

let mem_load_byte_align_dm = prove
 (`good_dimindex (:'a) ==>
   mem_load_byte n (a:'a asm_addr) (align_dm s) = align_dm
     (mem_load_byte n a s)`,
  CHEAT_TAC);;

(* HOL4 labPropsScript.sml:624-657: a theorem whose statement HOL
   Light does not read (tools/unstated.py): mem_store_align_dm *)

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let mem_store_32_align_dm = prove
 (cake_as_vars (fun () ->
    `mem_store_32 mem (labSem_state_mem_domain s) be x c = SOME y ==>
     mem_store_32 mem (labSem_state_mem_domain (align_dm s)) be x
       c = SOME y`),
  CHEAT_TAC);;

let mem_store32_align_dm = prove
 (`good_dimindex (:'a) ==>
   mem_store32 n (a:'a asm_addr) (align_dm s) = align_dm
     (mem_store32 n a s)`,
  CHEAT_TAC);;

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let mem_store_byte_aux_align_dm = prove
 (cake_as_vars (fun () ->
    `mem_store_byte_aux mem (labSem_state_mem_domain s) be x c = SOME y
  ==>
     mem_store_byte_aux mem (labSem_state_mem_domain (align_dm
       s)) be x c = SOME y`),
  CHEAT_TAC);;

let mem_store_byte_align_dm = prove
 (`good_dimindex (:'a) ==>
   mem_store_byte n (a:'a asm_addr) (align_dm s) = align_dm
     (mem_store_byte n a s)`,
  CHEAT_TAC);;

(* HOL4 labPropsScript.sml:711-719: a theorem whose statement HOL
   Light does not read (tools/unstated.py): mem_op_align_dm *)

let asm_inst_align_dm = prove
 (`good_dimindex (:'a) ==>
   asm_inst (i:'a asm_inst) (align_dm s) = align_dm (asm_inst i s)`,
  CHEAT_TAC);;

(* HOL4 labPropsScript.sml:728-732: a theorem whose statement HOL
   Light does not read (tools/unstated.py): dec_clock_align_dm *)

(* [simp] *)
let inc_pc_align_dm = prove
 (`inc_pc (align_dm s) = align_dm (inc_pc s)`,
  CHEAT_TAC);;

(* [simp] *)
let upd_pc_align_dm = prove
 (`labSem_upd_pc p (align_dm s) = align_dm (labSem_upd_pc p s)`,
  CHEAT_TAC);;

(* [simp] *)
let get_pc_value_align_dm = prove
 (`get_pc_value x (align_dm s) = get_pc_value x s`,
  CHEAT_TAC);;

(* [simp] *)
let get_ret_Loc_align_dm = prove
 (`get_ret_Loc (align_dm s) = get_ret_Loc s`,
  CHEAT_TAC);;

(* [simp] *)
let read_bytearray_mem_load_byte_aux_align_dm = prove
 (`!y x.
    read_bytearray x y (mem_load_byte_aux (labSem_state_mem s)
      (labSem_state_mem_domain (align_dm s)) (be s)) =
   read_bytearray x y (mem_load_byte_aux (labSem_state_mem s)
     (labSem_state_mem_domain s) (be s))`,
  CHEAT_TAC);;

(* [simp] *)
let write_bytearray_align_dm = prove
 (`!y x. write_bytearray x y (labSem_state_mem s)
  (labSem_state_mem_domain (align_dm s)) (be s) =
   write_bytearray x y (labSem_state_mem s)
     (labSem_state_mem_domain s) (be s)`,
  CHEAT_TAC);;

(* [simp] *)
let share_mem_op_align_dm_simp = prove
 (`(share_mem_op m r a s = NONE ==> share_mem_op m r a (align_dm s) =
  NONE) /\
   (share_mem_op m r a s = SOME (FFI_final f,s') ==>
   share_mem_op m r a (align_dm s) = SOME (FFI_final f,align_dm s'))
     /\
   (share_mem_op m r a s = SOME (FFI_return fs l,s') ==>
   share_mem_op m r a (align_dm s) = SOME (FFI_return fs l,align_dm
     s'))`,
  CHEAT_TAC);;

(* HOL4 labPropsScript.sml:803-849: a theorem whose statement HOL
   Light does not read (tools/unstated.py): evaluate_align_dm *)

(* HOL4 labPropsScript.sml:851-866: a theorem whose statement HOL
   Light does not read (tools/unstated.py): implements_align_dm *)

(** align_sdm **)

let align_sdm_def = new_definition
  `align_sdm (s:('a,'c,'ffi)labSem_state) =
     (labSem_state_shared_mem_domain_fupd (K
       (labSem_state_shared_mem_domain s INTER byte_aligned)) s)`;;

(* [simp] *)
let align_sdm_const = prove
 (`state_clock
      (align_sdm s) = state_clock s /\ pc
      (align_sdm s) = pc s /\ state_code
      (align_sdm s) = state_code s /\ labSem_state_mem
      (align_sdm s) = labSem_state_mem s /\ labSem_state_mem_domain
      (align_sdm s) = labSem_state_mem_domain s /\ be
      (align_sdm s) = be s /\ len_reg
      (align_sdm s) = len_reg s /\ link_reg
      (align_sdm s) = link_reg s /\ ptr_reg
      (align_sdm s) = ptr_reg s /\ ptr2_reg
      (align_sdm s) = ptr2_reg s /\ len2_reg
      (align_sdm s) = len2_reg s /\ labSem_state_io_regs
      (align_sdm s) = labSem_state_io_regs s /\
        labSem_state_io_fp_regs
      (align_sdm s) = labSem_state_io_fp_regs s /\ state_code_buffer
      (align_sdm s) = state_code_buffer s /\ compile
      (align_sdm s) = compile s /\ compile_oracle
      (align_sdm s) = compile_oracle s /\ state_ffi
      (align_sdm s) = state_ffi s /\ failed
      (align_sdm s) = failed s`,
  CHEAT_TAC);;

let align_sdm_with_clock = prove
 (`align_sdm (state_clock_fupd (K k) s) = state_clock_fupd (K k)
  (align_sdm s)`,
  CHEAT_TAC);;

(* [simp] *)
let asm_fetch_align_sdm = prove
 (`asm_fetch (align_sdm s) = asm_fetch s`,
  CHEAT_TAC);;

(* [simp] *)
let read_reg_align_sdm = prove
 (`regs (align_sdm s) n = regs s n`,
  CHEAT_TAC);;

(* [simp] *)
let upd_reg_align_sdm = prove
 (`labSem_upd_reg x y (align_sdm s) = align_sdm (labSem_upd_reg x y s)`,
  CHEAT_TAC);;

(* [simp] *)
let upd_mem_align_sdm = prove
 (`labSem_upd_mem x y (align_sdm s) = align_sdm (labSem_upd_mem x y s)`,
  CHEAT_TAC);;

(* [simp] *)
let binop_upd_align_sdm = prove
 (`labSem_binop_upd x y z w (align_sdm s) = align_sdm
  (labSem_binop_upd x y z w s)`,
  CHEAT_TAC);;

(* [simp] *)
let reg_imm_align_sdm = prove
 (`labSem_reg_imm r (align_sdm s) = labSem_reg_imm r s`,
  CHEAT_TAC);;

(* [simp] *)
let assert_align_sdm = prove
 (`labSem_assert b (align_sdm s) = align_sdm (labSem_assert b s)`,
  CHEAT_TAC);;

(* HOL4 labPropsScript.sml:946-951: a theorem whose statement HOL
   Light does not read (tools/unstated.py): arith_upd_align_sdm *)

(* HOL4 labPropsScript.sml:953-958: a theorem whose statement HOL
   Light does not read (tools/unstated.py): fp_upd_align_sdm *)

(* HOL4 labPropsScript.sml:960-964: a theorem whose statement HOL
   Light does not read (tools/unstated.py): addr_align_sdm *)

(* HOL4 labPropsScript.sml:966-971: a theorem whose statement HOL
   Light does not read (tools/unstated.py): mem_load_align_sdm *)

let mem_load32_align_sdm = prove
 (`mem_load32 n (a:'a asm_addr) (align_sdm s) = align_sdm (mem_load32
  n a s)`,
  CHEAT_TAC);;

let mem_load_byte_align_sdm = prove
 (`mem_load_byte n (a:'a asm_addr) (align_sdm s) = align_sdm
  (mem_load_byte n a s)`,
  CHEAT_TAC);;

(* HOL4 labPropsScript.sml:987-992: a theorem whose statement HOL
   Light does not read (tools/unstated.py): mem_store_align_sdm *)

let mem_store32_align_sdm = prove
 (`mem_store32 n (a:'a asm_addr) (align_sdm s) = align_sdm
  (mem_store32 n a s)`,
  CHEAT_TAC);;

let mem_store_byte_align_sdm = prove
 (`mem_store_byte n (a:'a asm_addr) (align_sdm s) = align_sdm
  (mem_store_byte n a s)`,
  CHEAT_TAC);;

(* HOL4 labPropsScript.sml:1008-1015: a theorem whose statement HOL
   Light does not read (tools/unstated.py): mem_op_align_sdm *)

let asm_inst_align_sdm = prove
 (`asm_inst (i:'a asm_inst) (align_sdm s) = align_sdm (asm_inst i s)`,
  CHEAT_TAC);;

(* HOL4 labPropsScript.sml:1023-1027: a theorem whose statement HOL
   Light does not read (tools/unstated.py): dec_clock_align_sdm *)

(* [simp] *)
let inc_pc_align_sdm = prove
 (`inc_pc (align_sdm s) = align_sdm (inc_pc s)`,
  CHEAT_TAC);;

(* [simp] *)
let upd_pc_align_sdm = prove
 (`labSem_upd_pc p (align_sdm s) = align_sdm (labSem_upd_pc p s)`,
  CHEAT_TAC);;

(* [simp] *)
let get_pc_value_align_sdm = prove
 (`get_pc_value x (align_sdm s) = get_pc_value x s`,
  CHEAT_TAC);;

(* [simp] *)
let get_ret_Loc_align_sdm = prove
 (`get_ret_Loc (align_sdm s) = get_ret_Loc s`,
  CHEAT_TAC);;

(* [simp] *)
let read_bytearray_mem_load_byte_aux_align_sdm = prove
 (`!y x.
    read_bytearray x y (mem_load_byte_aux (labSem_state_mem s)
      (labSem_state_mem_domain (align_sdm s)) (be s)) =
   read_bytearray x y (mem_load_byte_aux (labSem_state_mem s)
     (labSem_state_mem_domain s) (be s))`,
  CHEAT_TAC);;

(* [simp] *)
let write_bytearray_align_sdm = prove
 (`!y x. write_bytearray x y (labSem_state_mem s)
  (labSem_state_mem_domain (align_sdm s)) (be s) =
   write_bytearray x y (labSem_state_mem s)
     (labSem_state_mem_domain s) (be s)`,
  CHEAT_TAC);;

let align_sdm_aligned = prove
 (`good_dimindex (:'a) ==>
   (((x:'a word) IN labSem_state_shared_mem_domain s /\ w2n x MOD
     (dimindex (:'a) DIV 8) = 0) <=>
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

(* [simp] *)
let share_mem_op_align_sdm_simp = prove
 (`good_dimindex (:'a) ==>
   (share_mem_op m r (a:'a asm_addr) s = NONE <=> share_mem_op m r a
     (align_sdm s) = NONE) /\
   (share_mem_op m r a s = SOME (res,s') ==>
   share_mem_op m r a (align_sdm s) = SOME (res,align_sdm s'))`,
  CHEAT_TAC);;

(* HOL4 labPropsScript.sml:1174-1226: a theorem whose statement HOL
   Light does not read (tools/unstated.py): evaluate_align_sdm *)

(* HOL4 labPropsScript.sml:1228-1243: a theorem whose statement HOL
   Light does not read (tools/unstated.py): implements_align_sdm *)


(* asm_ok checks coming into lab_to_target *)
let line_ok_pre_def = new_definition
  `line_ok_pre c x2 =
        match (c,x2) with
          ((c:'a asm_config),labLang_Asm b bytes l) -> asm_ok
            (cbw_to_asm b) c
        | (c,_20) -> T`;;

let sec_ok_pre_def = define_general
  [`sec_ok_pre c (Section k ls) <=>
     ALL (line_ok_pre c) ls`];;

(* HOL4 labPropsScript.sml:1257: the overload all_enc_ok_pre, which
   the port expands *)

(* invariant: labels have correct section number and are non-zero *)

let sec_label_ok_def = new_definition
  `sec_label_ok k x2 =
        match x2 with
          labLang_Label l1 l2 len -> l1 = k /\ ~(l2 = 0)
        | _21 -> T`;;

let sec_labels_ok_def = define_general
  [`sec_labels_ok (Section k ls) <=> ALL (sec_label_ok k) ls`];;

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
   set_of_list (FLAT (MAP (labProps_extract_labels o Section_lines)
     code))`,
  CHEAT_TAC);;

let no_install_def = new_definition
  `labProps_no_install code <=>
   (!p w bytes l. ~(asm_fetch_aux p code =
       SOME (labLang_LabAsm labLang_Install w bytes l)))`;;

let no_share_mem_inst_def = new_definition
  `no_share_mem_inst code <=>
   (!p op re a inst' len. ~(asm_fetch_aux p code =
       SOME (labLang_Asm (ShareMem op re a) inst' len)))`;;

(* and the names that this file reads as variables are constants again *)
let _ = do_list unhide_constant
  ["mem"];;

(* and the overloads that this file cannot see are back in the
   interface *)
let _ = unhide_overloads ();;
