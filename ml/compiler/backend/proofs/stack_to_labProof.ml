(* ======================================================== *)
(*  stack_to_labProof: ported from HOL4's
    compiler/backend/proofs/stack_to_labProofScript.sml
    A proof theory about stack_to_lab.ml, with 17 definitions, 1
    datatype and 169 theorems.  Needed by backendProof.ml.  *)
(* ======================================================== *)

(*
  Correctness proof for stack_to_lab
*)

needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/bvl_to_bvi.ml";;
needs "compiler/backend/data_live.ml";;
needs "compiler/backend/data_to_word.ml";;
needs "compiler/backend/labLang.ml";;
needs "compiler/backend/proofs/data_to_word_gcProof.ml";;
needs "compiler/backend/proofs/stack_allocProof.ml";;
needs "compiler/backend/proofs/stack_namesProof.ml";;
needs "compiler/backend/proofs/stack_rawcallProof.ml";;
needs "compiler/backend/proofs/stack_removeProof.ml";;
needs "compiler/backend/proofs/word_to_stackProof.ml";;
needs "compiler/backend/semantics/backendProps.ml";;
needs "compiler/backend/semantics/labProps.ml";;
needs "compiler/backend/semantics/labSem.ml";;
needs "compiler/backend/semantics/stackProps.ml";;
needs "compiler/backend/semantics/stackSem.ml";;
needs "compiler/backend/semantics/wordConvs.ml";;
needs "compiler/backend/semantics/wordProps.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/backend/stackLang.ml";;
needs "compiler/backend/stack_alloc.ml";;
needs "compiler/backend/stack_rawcall.ml";;
needs "compiler/backend/stack_remove.ml";;
needs "compiler/backend/stack_to_lab.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/backend/word_to_stack.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "lib/alignment.ml";;
needs "lib/byte.ml";;
needs "lib/set_sep.ml";;
needs "lib/sptree.ml";;
needs "misc/misc.ml";;
needs "semantics/proofs/semanticsProps.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "stack_to_labProof"
  ["data_to_word_gcProof"; "labProps"; "labSem"; "semanticsProps";
   "stackProps"; "stackSem"; "stack_alloc"; "stack_allocProof";
   "stack_namesProof"; "stack_rawcallProof"; "stack_removeProof";
   "stack_to_lab"; "wordProps"; "wordSem"; "word_to_stackProof"];;

(* this file reads the name of a record field as a variable and
   needs the accessors of that field as well, so only these
   pairs come out of the interface *)
let _ = hide_overloads
  ["code_buffer","code_buffer";
   "data_buffer","data_buffer";
   "failed","pegexec_failed"];;

(* HOL4 stack_to_labProofScript.sml:23-24: ML code, not ported *)

(* HOL4 stack_to_labProofScript.sml:26: code that the source has in a
   comment *)

(* HOL4 stack_to_labProofScript.sml:28: the overload Loc, which the
   port expands *)

(* TODO: move *)

let word_sh_word_shift = prove
 (`word_sh a (b:'a word) c = SOME z ==> c < dimindex (:'a) /\ z =
  backend_common_word_shift a b c`,
  CHEAT_TAC);;

let assert_T = prove
 (`labSem_assert T s = s`,
  CHEAT_TAC);;
add_simp assert_T;;

let asm_fetch_aux_no_label = prove
 (`!pc' code.
   asm_fetch_aux pc' code = SOME (labLang_Label l1 l2 x) ==> F`,
  CHEAT_TAC);;

let dest_to_loc_def = new_definition
  `dest_to_loc regs' dest =
     (match dest with INL p -> p | INR r -> (match FAPPLY regs' r
       with wordLang_Loc loc _1 -> loc))`;;

let dest_to_loc'_def = new_definition
  `dest_to_loc' regs' dest =
     (match dest with INL p -> p | INR r -> (match regs' r with
       wordLang_Loc loc _2 -> loc))`;;

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let find_code_lookup = prove
 (cake_as_vars (fun () ->
    `stackSem_find_code dest regs code = SOME p ==>
      sptree_lookup (dest_to_loc regs dest) code = SOME p /\
      (!r. dest = INR r ==> r IN FDOM regs)`),
  CHEAT_TAC);;

let not_is_Label_compile_jump = prove
 (`is_Label (compile_jump dest) <=> F`,
  CHEAT_TAC);;
add_simp not_is_Label_compile_jump;;

let word_cmp_not_NONE = prove
 (`~(wordSem_word_cmp cmp (wordLang_Word w1) (wordLang_Word w2) =
  NONE)`,
  CHEAT_TAC);;
add_simp word_cmp_not_NONE;;

let word_cmp_negate_alt = prove
 (`asm_word_cmp (negate cmp) w1 w2 <=> ~(wordSem_word_cmp cmp w1 w2)`,
  CHEAT_TAC);;
add_simp word_cmp_negate_alt;;

let word_cmp_negate = prove
 (`wordSem_word_cmp (negate cmp) w1 w2 =
   OPTION_MAP (~) (wordSem_word_cmp cmp (w1) (w2))`,
  CHEAT_TAC);;
add_simp word_cmp_negate;;

(* -- Lemmas about code_installed, loc_to_pc and asm_fetch_aux -- *)

let stack_to_labProof_code_installed_def,
    stack_to_labProof_code_installed_ind =
  define_rec
  [`stack_to_labProof_code_installed n [] code = T`;
   `stack_to_labProof_code_installed n (CONS x xs) code <=>
       (if is_Label x then
         (match x with labLang_Label l1 l2 _4 -> loc_to_pc l1 l2
             code = SOME n) /\
         stack_to_labProof_code_installed n xs code else
         asm_fetch_aux n code = SOME x /\
         stack_to_labProof_code_installed (n + 1) xs code)`];;

let code_installed_append_imp = prove
 (`!l1 pc' l2 code. stack_to_labProof_code_installed pc' (APPEND l1 l2)
  code ==>
   stack_to_labProof_code_installed pc' l1 code /\
   stack_to_labProof_code_installed (pc' + LENGTH (FILTER ((~) o
     is_Label) l1)) l2 code`,
  CHEAT_TAC);;

(* [local] *)
let code_installed_get_labels_IMP = prove
 (`!top e n q cs bs pc'.
       stack_to_labProof_code_installed pc' (append (FST
         (stack_to_lab_flatten top e n q cs bs))) c /\
       (l1,l2) IN labProps_get_labels e ==>
       (?v. loc_to_pc l1 l2 c = SOME v)`,
  CHEAT_TAC);;

(* TODO: these may already be proved in lab_filter or lab_to_target,
         they ought to move into labProps
*)
(* [local] *)
let asm_fetch_aux_SOME_append = prove
 (`!pc' code l code2.
   asm_fetch_aux pc' code = SOME l ==>
   asm_fetch_aux pc' (APPEND code code2) = SOME l`,
  CHEAT_TAC);;

(* [local] *)
let asm_fetch_aux_SOME_isPREFIX = prove
 (`!pc' code l code2.
   asm_fetch_aux pc' code = SOME l /\
   code <<= code2 ==>
   asm_fetch_aux pc' code2 = SOME l`,
  CHEAT_TAC);;

let loc_to_pc_APPEND = prove
 (`!n m code pc' code2.
   loc_to_pc n m code = SOME pc' ==>
   loc_to_pc n m (APPEND code code2) = SOME pc'`,
  CHEAT_TAC);;

let code_installed_APPEND = prove
 (`!ls pc' code code2.
   stack_to_labProof_code_installed pc' ls code ==>
   stack_to_labProof_code_installed pc' ls (APPEND code code2)`,
  CHEAT_TAC);;

let code_installed_isPREFIX = prove
 (`!ls pc' code code2.
   stack_to_labProof_code_installed pc' ls code /\
   code <<= code2 ==>
   stack_to_labProof_code_installed pc' ls code2`,
  CHEAT_TAC);;

let loc_to_pc_isPREFIX = prove
 (`!n m code pc' code2.
   loc_to_pc n m code = SOME pc' /\
   code <<= code2 ==>
   loc_to_pc n m code2 = SOME pc'`,
  CHEAT_TAC);;

(* [local] *)
let MAP_prog_to_section_FST = prove
 (`MAP (\s. match s with Section n v -> n) (MAP prog_to_section prog) =
   MAP FST prog`,
  CHEAT_TAC);;

let MAP_prog_to_section_Section_num = prove
 (`MAP Section_num (MAP prog_to_section prog) =
   MAP FST prog`,
  CHEAT_TAC);;

(* Appending on the other side *)
let asm_fetch_aux_SOME_append2 = prove
 (`!pc' code l code2.
   asm_fetch_aux pc' code2 = SOME l ==>
   asm_fetch_aux
   (LENGTH (FLAT (MAP (FILTER ((~) o is_Label) o Section_lines)
     code)) + pc') (APPEND code code2) = SOME l`,
  CHEAT_TAC);;

(* loc_to_pc on the other side *)
let loc_to_pc_append2 = prove
 (`!k ll code code2 pc'.
   ~(MEM k (MAP Section_num code)) /\
   ALL sec_labels_ok code /\
   loc_to_pc k ll code2 = SOME pc' ==>
   loc_to_pc k ll (APPEND code code2) =
   SOME (pc' + (LENGTH (FLAT (MAP (FILTER ((~) o is_Label) o
     Section_lines) code))))`,
  CHEAT_TAC);;

let code_installed_append2 = prove
 (`!lines pc' c1 c2 k.
   ~(MEM k (MAP Section_num c1)) /\
   ALL sec_labels_ok c1 /\
   ALL (sec_label_ok k) lines /\
   stack_to_labProof_code_installed pc' lines c2 ==>
   stack_to_labProof_code_installed
   (LENGTH (FLAT (MAP (FILTER ((~) o is_Label) o Section_lines) c1))
     + pc')
   lines (APPEND c1 c2)`,
  CHEAT_TAC);;

let ALOOKUP_PARTITION = prove
 (`!ls n v.
   ALOOKUP ls n = SOME v ==>
   (?ls1 ls2.
   ls = APPEND (APPEND ls1 [(n,v)]) ls2 /\
   ~(MEM n (MAP FST ls1)))`,
  CHEAT_TAC);;

let code_installed'_def,code_installed'_ind = define_rec
  [`code_installed' n [] code <=> T`;
   `code_installed' n (CONS x xs) code <=>
         (if is_Label x then code_installed' n xs code else
             asm_fetch_aux n code = SOME x /\ code_installed' (n +
             1) xs code)`];;

let code_installed'_cons_label = prove
 (`!lines pos.
      is_Label h ==>
      code_installed' pos lines (CONS (Section n (CONS h xs)) other)
        =
      code_installed' pos lines (CONS (Section n xs) other)`,
  CHEAT_TAC);;

(* HOL4 stack_to_labProofScript.sml:342-349: a theorem that HOL4
   states as the value of an ML expression:
   code_installed'_cons_non_label *)

let code_installed'_simp = prove
 (`!lines. code_installed' 0 lines (CONS (Section n (APPEND lines
  rest)) other)`,
  CHEAT_TAC);;

let loc_to_pc_skip_section = prove
 (`!lines. ~(n = p) ==>
      loc_to_pc n 0 (CONS (Section p lines) xs) =
      (match loc_to_pc n 0 xs with NONE -> NONE | SOME k -> SOME (k
        + LENGTH (FILTER (\x. ~(is_Label x)) lines)))`,
  CHEAT_TAC);;

let asm_fetch_aux_add = prove
 (`!ys pc' rest.
      asm_fetch_aux (pc' + LENGTH (FILTER (\x. ~(is_Label x)) ys))
        (CONS (Section pos ys) rest) = asm_fetch_aux pc' rest`,
  CHEAT_TAC);;

let labs_correct_def,labs_correct_ind = define_rec
  [`labs_correct n [] code <=> T`;
   `labs_correct n (CONS x xs) code <=>
         (if is_Label x then labs_correct n xs code /\
           (match x with labLang_Label l1 l2 v2 -> loc_to_pc l1
               l2 code = SOME n | _6 -> T) else labs_correct (n +
               1) xs code)`];;

(* HOL4 stack_to_labProofScript.sml:391: ML code, not ported *)

let code_installed_eq = prove
 (`!pc' xs code.
      stack_to_labProof_code_installed pc' xs code <=>
      code_installed' pc' xs code /\ labs_correct pc' xs code`,
  CHEAT_TAC);;

(* code_installed_cons *)
let stack_to_labProof_code_installed_cons = prove
 (`!xs ys pos pc'.
      code_installed' pc' xs rest ==>
      code_installed' (pc' + LENGTH (FILTER (\x. ~(is_Label x)) ys))
        xs
        (CONS (Section pos ys) rest)`,
  CHEAT_TAC);;

(* [local] *)
let code_installed_prog_to_section_lemma = prove
 (`!prog4 n prog3.
       ALOOKUP prog4 n = SOME prog3 ==>
       (?pc'.
         code_installed' pc' (append (FST (stack_to_lab_flatten T
           prog3 n (next_lab prog3 2) [] [])))
           (MAP prog_to_section prog4) /\
         loc_to_pc n 0 (MAP prog_to_section prog4) = SOME pc')`,
  CHEAT_TAC);;

(* HOL4 stack_to_labProofScript.sml:434-435: ML code, not ported *)

let labs_correct_hd = prove
 (`!extra l.
   ALL_DISTINCT (stackProps_extract_labels (APPEND extra l)) /\
   ALL (\(l1,l2). l1 = n /\ ~(l2 = 0)) (stackProps_extract_labels
     (APPEND extra l)) ==>
   labs_correct (LENGTH (FILTER (\x. ~(is_Label x)) extra)) l (CONS
     (Section n (APPEND extra l)) code)`,
  CHEAT_TAC);;

let labels_ok_def = new_definition
  `labels_ok code <=>
   // Section names are distinct
   ALL_DISTINCT (MAP (\s. match s with Section n _7 -> n) code) /\
   ALL (\s. match s with Section n lines ->
     (let labs = stackProps_extract_labels lines in
     ALL (\(l1,l2). l1 = n /\ ~(l2 = 0)) labs /\
     ALL_DISTINCT labs)) code`;;

let labels_ok_imp = prove
 (`!code.
   labels_ok code ==>
   ALL sec_labels_ok code /\
   ALL_DISTINCT (MAP Section_num code) /\
   ALL (ALL_DISTINCT o stackProps_extract_labels o Section_lines)
     code`,
  CHEAT_TAC);;

let labels_ok_labs_correct = prove
 (`!code.
   labels_ok code ==>
   ALL (\s. match s with Section n lines ->
     (match loc_to_pc n 0 code with
      SOME pc' -> labs_correct pc' lines code | _8 -> T)) code`,
  CHEAT_TAC);;

let labs_correct_append = prove
 (`!ls pc'.
   labs_correct pc' (APPEND ls rest) code ==>
   labs_correct pc' ls code`,
  CHEAT_TAC);;

let code_installed_prog_to_section = prove
 (`!prog4 n prog3.
      labels_ok (MAP prog_to_section prog4) /\
      ALOOKUP prog4 n = SOME prog3 ==>
      (?pc'.
        stack_to_labProof_code_installed pc' (append (FST
          (stack_to_lab_flatten T prog3 n (next_lab prog3 2) [] [])))
          (MAP prog_to_section prog4) /\
        loc_to_pc n 0 (MAP prog_to_section prog4) = SOME pc')`,
  CHEAT_TAC);;

(* -- End code_installed lemmas  -- *)

let stack_to_labProof_state_rel_def = new_definition
  `stack_to_labProof_state_rel (s:('a,'c,'ffi)stackSem_state)
  (t:('a,'c,'ffi)labSem_state) <=>
     (!n v. FLOOKUP (stackSem_state_regs s) n = SOME v ==>
       labSem_state_regs t n = v) /\
     (!n v. FLOOKUP (stackSem_state_fp_regs s) n = SOME v ==>
       labSem_state_fp_regs t n = v) /\ labSem_state_mem
     t = stackSem_state_memory s /\ labSem_state_mem_domain
     t = stackSem_state_mdomain s /\ labSem_state_shared_mem_domain
     t = stackSem_state_sh_mdomain s /\ labSem_state_be
     t = stackSem_state_be s /\ labSem_state_ffi
     t = stackSem_state_ffi s /\ labSem_state_clock
     t = stackSem_state_clock s /\
     (!n prog. sptree_lookup n (stackSem_state_code s) = SOME prog
       ==>
       call_args prog (labSem_state_ptr_reg t) (labSem_state_len_reg
         t) (labSem_state_ptr2_reg t) (labSem_state_len2_reg t)
         (labSem_state_link_reg t) /\
       (?pc'. stack_to_labProof_code_installed pc'
              (append (FST (stack_to_lab_flatten T prog n (next_lab
                prog 2) [] []))) (labSem_state_code t) /\
            loc_to_pc n 0 (labSem_state_code t) = SOME pc')) /\
     // These two conjuncts are needed for Install
     domain (stackSem_state_code s) = set_of_list (MAP Section_num
       (labSem_state_code t)) /\
     ALL sec_labels_ok (labSem_state_code t) /\
     ~(labSem_state_failed t) /\ ~(labSem_state_link_reg
     t = labSem_state_len_reg t) /\ ~(labSem_state_link_reg t =
       labSem_state_ptr_reg t) /\ ~(labSem_state_link_reg
     t = labSem_state_len2_reg t) /\ ~(labSem_state_link_reg t =
       labSem_state_ptr2_reg t) /\
     ~(labSem_state_link_reg t IN stackSem_state_ffi_save_regs s) /\
     (!k i n. k IN stackSem_state_ffi_save_regs s ==>
       labSem_state_io_regs t n i k = NONE) /\
     (
      // might need to be cc_save_regs
      !k n. k IN stackSem_state_ffi_save_regs s ==>
        labSem_state_cc_regs t n k = NONE) /\
     (!x. x IN stackSem_state_mdomain s ==> w2n x MOD (dimindex (:'a)
       DIV 8) = 0) /\
     (!x. x IN stackSem_state_sh_mdomain s ==> w2n x MOD (dimindex
       (:'a) DIV 8) = 0) /\ stackSem_state_code_buffer
     s = labSem_state_code_buffer t /\ stackSem_state_compile
     s = (\c p. labSem_state_compile t c (MAP prog_to_section p)) /\
     (labSem_state_compile_oracle t = (\n. let (c,p,_9) =
       stackSem_state_compile_oracle s n in
                            (c,MAP prog_to_section p))) /\
     (!k. let (c,ps,_10) = stackSem_state_compile_oracle s k in
       ALL (\(n,p).
         call_args p (labSem_state_ptr_reg t) (labSem_state_len_reg
           t) (labSem_state_ptr2_reg t) (labSem_state_len2_reg t)
           (labSem_state_link_reg t) /\
         ALL (\(l1,l2). l1 = n /\ ~(l2 = 0) /\ ~(l2 = 1))
           (stackProps_extract_labels p) /\
         ALL_DISTINCT (stackProps_extract_labels p)) ps /\
         // This last conjunct might not be necessary
         ALL_DISTINCT (MAP FST ps)) /\
     ~(stackSem_state_use_stack s) /\
     ~(stackSem_state_use_store s) /\
     ~(stackSem_state_use_alloc s) /\
     good_dimindex (:'a)`;;

let loc_check_IMP_loc_to_pc = prove
 (`loc_check (stackSem_state_code s) (l1,l2) /\
  stack_to_labProof_state_rel s t1 ==>
    (?v. loc_to_pc l1 l2 (labSem_state_code t1) = SOME v)`,
  CHEAT_TAC);;

(* HOL4 stack_to_labProofScript.sml:655-660: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   state_rel_dec_clock *)

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let state_rel_with_pc = prove
 (cake_as_vars (fun () ->
    `stack_to_labProof_state_rel s t ==> stack_to_labProof_state_rel s
  (labSem_upd_pc pc t)`),
  CHEAT_TAC);;

(* state_rel_with_clock *)
let stack_to_labProof_state_rel_with_clock = prove
 (`stack_to_labProof_state_rel s t ==> stack_to_labProof_state_rel
  (stackSem_state_clock_fupd (K k) s) (labSem_state_clock_fupd (K k)
  t)`,
  CHEAT_TAC);;

let set_var_upd_reg = prove
 (`stack_to_labProof_state_rel s t ==>
   stack_to_labProof_state_rel (stackSem_set_var a b s)
     (labSem_upd_reg a b t)`,
  CHEAT_TAC);;

let set_var_Word_upd_reg = prove
 (`stack_to_labProof_state_rel s t ==>
   stack_to_labProof_state_rel (stackSem_set_var a (wordLang_Word
     b) s) (labSem_upd_reg a (wordLang_Word b) t)`,
  CHEAT_TAC);;
add_simp set_var_Word_upd_reg;;

(* HOL4 stack_to_labProofScript.sml:690-696: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   set_fp_var_upd_fp_reg *)

let mem_store_upd_mem = prove
 (`stack_to_labProof_state_rel s t /\ stackSem_mem_store x y s = SOME s1
  ==>
   stack_to_labProof_state_rel s1 (labSem_upd_mem x y t)`,
  CHEAT_TAC);;

let state_rel_read_reg_FLOOKUP_regs = prove
 (`stack_to_labProof_state_rel s t /\
   FLOOKUP (stackSem_state_regs s) x = SOME y ==>
   y = labSem_state_regs t x`,
  CHEAT_TAC);;

(* HOL4 stack_to_labProofScript.sml:719-726: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   state_rel_read_fp_reg_FLOOKUP_fp_regs *)

let state_rel_get_var_imm = prove
 (`stack_to_labProof_state_rel s t /\
   stackSem_get_var_imm r s = SOME x ==>
   labSem_reg_imm r t = x`,
  CHEAT_TAC);;

(* inst_correct *)
(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let stack_to_labProof_inst_correct = prove
 (cake_as_vars (fun () ->
    `stackSem_inst i s1 = SOME s2 /\
     stack_to_labProof_state_rel s1 t1 ==>
     stack_to_labProof_state_rel s2 (asm_inst i t1)`),
  CHEAT_TAC);;

let flatten_leq = prove
 (`!t x y z cs bs. z <= SND (SND (stack_to_lab_flatten t x y z cs bs))`,
  CHEAT_TAC);;

(* [local] *)
let NOT_bad_fun_return_IMP_SOME = prove
 (`~(stackSem_bad_fun_return q) ==> (?n. q = SOME n)`,
  CHEAT_TAC);;

let no_ret_correct = prove
 (`!t p y z cs bs. FST (SND (stack_to_lab_flatten t p y z cs bs)) ==>
  (!s. IS_SOME (FST (stackSem_evaluate (p,s))))`,
  CHEAT_TAC);;

(* HOL4 stack_to_labProofScript.sml:926: the ML values that the
   definitions below antiquote *)

(* HOL4 stack_to_labProofScript.sml:928-939: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   compile_jump_correct *)

let result_view_INDUCT,result_view_RECURSION = define_datatype
  "result_view =
     Vloc num num
   | Vcont num num
   | Vtimeout
   | Verr";;

let result_view_def = new_definition
  `result_view x1 l cs bs =
        match x1 with
          stackSem_Result (wordLang_Loc n1 n2) -> Vloc n1 n2
        | (stackSem_Exception (wordLang_Loc n1 n2)) -> Vloc n1 n2
        | targetSem_TimeOut -> Vtimeout
        | (word_bignum_Continue n) -> Vcont l (find_lab n cs)
        | (stackSem_Break n) -> Vloc l (find_lab n bs)
        | _11 -> Verr`;;
add_simp result_view_def;;

let halt_word_view_def = new_definition
  `halt_word_view x1 =
        match x1 with
          wordLang_Word (n2w 0) -> targetSem_Halt ffi_Success
        | (wordLang_Word _12) -> targetSem_Halt
          ffi_Resource_limit_hit
        | _13 -> targetSem_Error`;;
add_simp halt_word_view_def;;

let halt_view_def = new_definition
  `halt_view x1 =
        match x1 with
          SOME (stackSem_Halt w) -> SOME (halt_word_view w)
        | (SOME (stackSem_FinalFFI outcome)) -> SOME (stackSem_Halt
          (ffi_FFI_outcome outcome))
        | _14 -> NONE`;;
add_simp halt_view_def;;

(* HOL4 stack_to_labProofScript.sml:966-1017: a proof *)

(* Proving that stack_to_lab generates labels_ok *)
(* HOL4 stack_to_labProofScript.sml:1020: ML code, not ported *)

let next_lab_non_zero = prove
 (`!p. 2 <= next_lab p 2`,
  CHEAT_TAC);;

let stack_to_lab_lab_pres = prove
 (`!t p n nl cs bs.
     ALL (\(l1,l2). l1 = n /\ ~(l2 = 0) /\ ~(l2 = 1))
       (stackProps_extract_labels p) /\
     ALL_DISTINCT (stackProps_extract_labels p) /\ ~t /\
     next_lab p 2 <= nl ==>
     (let (cp,nr,nl') = stack_to_lab_flatten t p n nl cs bs in
       ALL (\(l1,l2). l1 = n /\ ~(l2 = 0) /\ ~(l2 = 1))
         (stackProps_extract_labels (append cp)) /\
       ALL_DISTINCT (stackProps_extract_labels (append cp)) /\
       (!lab. MEM lab (stackProps_extract_labels (append cp)) ==> MEM
         lab (stackProps_extract_labels p) \/
                              (nl <= SND lab /\ SND lab < nl')) /\
       nl <= nl')`,
  CHEAT_TAC);;

let stack_to_lab_lab_pres_T = prove
 (`!t p n nl cs bs.
   ALL (\(l1,l2). l1 = n /\ ~(l2 = 0) /\ ~(l2 = 1))
     (stackProps_extract_labels p) /\
   ALL_DISTINCT (stackProps_extract_labels p) /\ t /\
   next_lab p 2 <= nl ==>
   (let (cp,nr,nl') = stack_to_lab_flatten t p n nl cs bs in
   ALL (\(l1,l2). l1 = n /\ ~(l2 = 0)) (stackProps_extract_labels
     (append cp)) /\
   ALL_DISTINCT (stackProps_extract_labels (append cp)) /\
   (!lab. MEM lab (stackProps_extract_labels (append cp)) ==>
        MEM lab (stackProps_extract_labels p) \/ SND lab < nl') /\
   nl <= nl')`,
  CHEAT_TAC);;

let flatten_T_F = prove
 (`~(is_Seq p_2) ==>
   stack_to_lab_flatten T p_2 p_1 m cs bs = stack_to_lab_flatten F
     p_2 p_1 m cs bs`,
  CHEAT_TAC);;

let prog_to_section_labels_ok = prove
 (`ALL (\(n,p).
            let labs = stackProps_extract_labels p in
              ALL (\(l1,l2). l1 = n /\ ~(l2 = 0) /\ ~(l2 = 1)) labs
                /\
              ALL_DISTINCT labs) prog /\
   ALL_DISTINCT (MAP FST prog) ==>
   labels_ok (MAP prog_to_section prog)`,
  CHEAT_TAC);;

let NOT_MEM_find_lab_IMP = prove
 (`!bs n. ~(MEM (find_lab n bs) bs) ==> find_lab n bs = 0`,
  CHEAT_TAC);;

let is_some_loc_to_pc_prefix = prove
 (`IS_SOME (loc_to_pc n k c1) /\ c1 <<= c2 ==>
   IS_SOME (loc_to_pc n k c2)`,
  CHEAT_TAC);;

let every_is_some_loc_to_pc_prefix = prove
 (`ALL (\k. IS_SOME (loc_to_pc n k c1)) cs /\ c1 <<= c2 ==>
   ALL (\k. IS_SOME (loc_to_pc n k c2)) cs`,
  CHEAT_TAC);;

(* HOL4 stack_to_labProofScript.sml:1207-2739: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   flatten_correct *)

(* HOL4 stack_to_labProofScript.sml:2741-2825: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   flatten_call_correct *)

let halt_assum_def = new_definition
  `halt_assum (:'ffi#'c) code <=>
    (!(s:('a,'c,'ffi)stackSem_state).
      subspt code (stackSem_state_code s) /\ ~(stackSem_state_clock s
        = 0) ==>
      (?t. stackSem_evaluate (labLang_Call NONE (INL 1) NONE,s) =
        (SOME (targetSem_Halt (wordLang_Word (n2w 0))),t) /\
        stackSem_state_ffi
          t = stackSem_state_ffi s /\ stackSem_state_clock t =
            stackSem_state_clock s - 1))`;;

(* HOL4 stack_to_labProofScript.sml:2835-3025: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   flatten_semantics *)

let stack_to_labProof_make_init_def = new_definition
  `stack_to_labProof_make_init code coracle regs' save_regs
  (s:('a,'c,'ffi)labSem_state) =
     (mk_stackSem_state (FEMPTY |++ (MAP (\r. r,(\r s.
       labSem_state_regs s r) r s) regs')) FEMPTY ARB ARB ARB
       (labSem_state_mem s) (labSem_state_mem_domain s)
       (labSem_state_shared_mem_domain s) ARB (\c p.
       labSem_state_compile s c (MAP prog_to_section p)) coracle
       (labSem_state_code_buffer s) ARB ARB F F F (labSem_state_clock
       s) code (labSem_state_ffi s) save_regs (labSem_state_be
       s):('a,'c,'ffi)stackSem_state)`;;

(* HOL4 stack_to_labProofScript.sml:3047-3049: ML code, not ported *)

(* HOL4 stack_to_labProofScript.sml:3051: the overload
   stack_to_lab_compile, which the port expands *)
(* HOL4 stack_to_labProofScript.sml:3052: the overload
   stack_names_compile, which the port expands *)
(* HOL4 stack_to_labProofScript.sml:3053: the overload
   stack_alloc_compile, which the port expands *)
(* HOL4 stack_to_labProofScript.sml:3054: the overload
   stack_remove_compile, which the port expands *)

let full_make_init_def = new_definition
  `full_make_init stack_conf data_conf max_heap sp offset bitmaps code
  s4 save_regs data_sp coracle =
   (let ggc = is_gen_gc (data_to_word_config_gc_kind data_conf) in
   let jump = stack_to_lab_config_jump stack_conf in
   let code1 = stack_alloc_compile data_conf (stack_rawcall_compile
     code) in
   let code2 = stack_to_lab_compile jump offset ggc max_heap sp
     InitGlobals_location code1 in
   let code3 = fromAList (stack_to_lab_compile
     (stack_to_lab_config_reg_names stack_conf) code2) in
   let coracle1 = (I ## MAP stack_alloc_prog_comp ## I) o coracle in
   let coracle2 = (I ## MAP (stack_alloc_prog_comp jump offset sp) ##
     I) o coracle1 in
   let coracle3 = (I ## stack_to_lab_compile
     (stack_to_lab_config_reg_names stack_conf) ## I) o coracle2 in
   let s3 = stack_to_labProof_make_init code3 coracle3 (MAP (tlookup
     (stack_to_lab_config_reg_names stack_conf)) [2; 3; 4]) save_regs s4
     in
   let s2 = stack_to_labProof_make_init
     (stack_to_lab_config_reg_names stack_conf) (fromAList code2)
     coracle2 s3 in
   let s1 = make_init_any ggc max_heap bitmaps data_sp coracle1 jump
     offset sp (fromAList code1) s2 in
     (stack_to_labProof_make_init data_conf (fromAList code) coracle
       s1,
      make_init_opt ggc max_heap bitmaps data_sp coracle1 jump
        offset sp (fromAList code1) s2))`;;

let full_make_init_buffer = prove
 (`buffer_buffer (state_code_buffer
       (FST (full_make_init a b c d e f g h i j k))) = [] /\
         buffer_buffer (state_data_buffer
     (FST (full_make_init a b c d e f g h i j k))) = []`,
  CHEAT_TAC);;

let full_make_init_ffi = prove
 (`state_ffi
       (FST (full_make_init a b c d e f g h i j k)) = state_ffi h`,
  CHEAT_TAC);;

let full_make_init_compile = prove
 (`compile
      (FST (full_make_init a b c d e f g h i j k)) =
      (\c. (\p. compile h c (MAP prog_to_section (MAP
        (stack_alloc_prog_comp (stack_to_lab_config_reg_names a)) (MAP
        (stack_alloc_prog_comp (stack_to_lab_config_jump a) e d) p))))
        o MAP stack_alloc_prog_comp)`,
  CHEAT_TAC);;

let memory_assumption_def = new_definition
  `memory_assumption rnames (bitmaps:('a word) list) data_sp t =
     (?ptr2 ptr3 ptr4 bitmap_ptr.
       (\r s. labSem_state_regs s r) (tlookup rnames 2) t =
         wordLang_Word ptr2 /\
       (\r s. labSem_state_regs s r) (tlookup rnames 3) t =
         wordLang_Word ptr3 /\
       (\r s. labSem_state_regs s r) (tlookup rnames 4) t =
         wordLang_Word ptr4 /\ labSem_state_mem
       t ptr2 = wordLang_Word bitmap_ptr /\ labSem_state_mem
       t (ptr2 + bytes_in_word) =
           wordLang_Word (bitmap_ptr + bytes_in_word * n2w (LENGTH
             bitmaps)) /\ labSem_state_mem
       t (ptr2 + (n2w 2) * bytes_in_word) =
           wordLang_Word (bitmap_ptr + bytes_in_word * n2w data_sp +
                 bytes_in_word * n2w (LENGTH bitmaps)) /\
                   labSem_state_mem
       t (ptr2 + (n2w 3) * bytes_in_word) = wordLang_Word
         (buffer_position (labSem_state_code_buffer t)) /\
         labSem_state_mem
       t (ptr2 + (n2w 4) * bytes_in_word) =
           wordLang_Word (buffer_position (labSem_state_code_buffer
             t) + n2w (buffer_space_left (labSem_state_code_buffer t)))
             /\ buffer_buffer (labSem_state_code_buffer
       t) = [] /\
       ptr2 <=+ ptr4 /\ byte_aligned ptr2 /\
       byte_aligned ptr4 /\ byte_aligned bitmap_ptr /\
       (n2w 1024) * bytes_in_word <=+ ptr4 - ptr2 /\
      (word_to_stack_word_list bitmap_ptr (MAP wordLang_Word bitmaps)
        *
       word_list_exists (bitmap_ptr + bytes_in_word * n2w (LENGTH
         bitmaps)) data_sp *
       word_list_exists ptr2
         (w2n (--(n2w 1) * ptr2 + ptr4) DIV w2n (bytes_in_word:'a
           word)))
        (fun2set (labSem_state_mem t,labSem_state_mem_domain t)))`;;

(* [local] *)
let halt_assum_lemma = prove
 (`halt_assum (:'ffi#'c)
      (fromAList (stack_names_compile f
        (stack_to_lab_compile jump off gen max_heap k l code)))`,
  CHEAT_TAC);;

(* [local] *)
let FLOOKUP_regs = prove
 (`!regs' n v f s.
       FLOOKUP (FEMPTY |++ MAP (\r. (r,labSem_state_regs s r))
         regs') n = SOME v ==> labSem_state_regs s n = v`,
  CHEAT_TAC);;

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let state_rel_make_init = prove
 (cake_as_vars (fun () ->
    `stack_to_labProof_state_rel (stack_to_labProof_make_init code
  coracle regs save_regs s) (s:('a,'c,'ffi)labSem_state) <=>
      (!n prog.
       sptree_lookup n code = SOME (prog) ==>
       call_args prog (labSem_state_ptr_reg s)
         (labSem_state_len_reg s) (labSem_state_ptr2_reg s)
         (labSem_state_len2_reg s) (labSem_state_link_reg s) /\
       (?pc'.
         stack_to_labProof_code_installed pc' (append (FST
           (stack_to_lab_flatten T prog n (next_lab prog 2) [] [])))
           (labSem_state_code s) /\
         loc_to_pc n 0 (labSem_state_code s) = SOME pc')) /\
           ~(labSem_state_failed s) /\ labSem_state_compile_oracle
      s = (\n. (\(c,p,_17). (c,MAP prog_to_section p)) (coracle n))
        /\
      (!k.
        (\(c,ps,_18).
           ALL
             (\(n,p).
                call_args p (labSem_state_ptr_reg s)
                  (labSem_state_len_reg s) (labSem_state_ptr2_reg s)
                  (labSem_state_len2_reg s) (labSem_state_link_reg s) /\
                ALL (\(l1,l2). l1 = n /\ ~(l2 = 0) /\ ~(l2 = 1))
                  (stackProps_extract_labels p) /\
                ALL_DISTINCT (stackProps_extract_labels p)) ps /\
           ALL_DISTINCT (MAP FST ps)) (coracle k)) /\
             ~(labSem_state_link_reg
      s = labSem_state_len_reg s) /\ ~(labSem_state_link_reg s =
        labSem_state_ptr_reg s) /\ ~(labSem_state_link_reg
      s = labSem_state_len2_reg s) /\ ~(labSem_state_link_reg s =
        labSem_state_ptr2_reg s) /\ ~(labSem_state_link_reg
      s IN save_regs) /\
      domain code = set_of_list (MAP Section_num (labSem_state_code
        s)) /\
      ALL sec_labels_ok (labSem_state_code s) /\
      (!k i n. k IN save_regs ==> labSem_state_io_regs s n i k =
        NONE) /\
      (!k n. k IN save_regs ==> labSem_state_cc_regs s n k = NONE)
        /\
      (!x. x IN labSem_state_mem_domain s ==> w2n x MOD (dimindex
        (:'a) DIV 8) = 0) /\
      (!x. x IN labSem_state_shared_mem_domain s ==> w2n x MOD
        (dimindex (:'a) DIV 8) = 0) /\
      good_dimindex (:'a)`),
  CHEAT_TAC);;

(* [local] *)
let MAP_FST_compile_compile = prove
 (`MAP FST (stack_to_lab_compile jump off gen max_heap k
  InitGlobals_location
               (stack_alloc_compile c
                  (stack_rawcall_compile code))) = CONS 0 (CONS 1
                    (CONS 2 (CONS gc_stub_location (MAP FST code))))`,
  CHEAT_TAC);;

(* HOL4 stack_to_labProofScript.sml:3209: ML code, not ported *)

(* next_lab_non_zero[allow_rebind] *)
let stack_to_labProof_next_lab_non_zero = prove
 (`!p. 1 <= next_lab p 1 /\
       2 <= next_lab p 2`,
  CHEAT_TAC);;

(* HOL4 stack_to_labProofScript.sml:3218-3270: code that the source
   has in a comment *)

(* MAP_prog_to_section_FST[local] *)
let stack_to_labProof_MAP_prog_to_section_FST = prove
 (`MAP (\s. match s with Section n v -> n) (MAP prog_to_section prog) =
   MAP FST prog`,
  CHEAT_TAC);;

(* [local] *)
let extract_label_store_list_code = prove
 (`!a t ls.
   stackProps_extract_labels (store_list_code a t ls) = []`,
  CHEAT_TAC);;

let stack_to_lab_compile_lab_pres = prove
 (`ALL (\n. ~(n = 0) /\ ~(n = 1) /\ ~(n = 2) /\ ~(n = gc_stub_location))
  (MAP FST prog) /\
   ALL (\(n,p).
            let labs = stackProps_extract_labels p in
              ALL (\(l1,l2). l1 = n /\ ~(l2 = 0) /\ ~(l2 = 1)) labs
                /\
              ALL_DISTINCT labs) prog /\
   ALL_DISTINCT (MAP FST prog) ==>
   labels_ok (stack_to_lab_compile c c2 c3 sp offset prog)`,
  CHEAT_TAC);;

let stack_to_labProof_good_code_def = new_definition
  `stack_to_labProof_good_code sp code <=>
    ALL_DISTINCT (MAP FST code) /\
    ALL (\(k,prog). stack_num_stubs <= k /\ alloc_arg prog) code /\
    ALL (\p. call_args p 1 2 3 4 0) (MAP SND code) /\
    ALL (\p. reg_bound p sp) (MAP SND code) /\
    ALL
    (\(n,p).
       ALL (\(l1,l2). l1 = n /\ ~(l2 = 0) /\ ~(l2 = 1))
         (stackProps_extract_labels p) /\
       ALL_DISTINCT (stackProps_extract_labels p)) code`;;

let contain_def = new_definition
  `contain b = Abbrev b`;;

(* HOL4 stack_to_labProofScript.sml:3365-3615: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   full_make_init_semantics *)

(* HOL4 stack_to_labProofScript.sml:3617-3618: a theorem that HOL4
   states as the value of an ML expression: full_make_init_semantics *)

let EVERY_sec_ends_with_label_MAP_prog_to_section = prove
 (`!prog. ALL sec_ends_with_label (MAP prog_to_section prog)`,
  CHEAT_TAC);;
add_simp EVERY_sec_ends_with_label_MAP_prog_to_section;;

(* HOL4 stack_to_labProofScript.sml:3627: ML code, not ported *)

(* [local] *)
let flatten_line_ok_pre = prove
 (`!t p n m cs bs ls a b c.
   asm_offset_ok 0 (asm_config_byte_offset c) (n2w 0) /\
   stack_asm_ok c p /\
   stack_to_lab_flatten t p n m cs bs = (ls,a,b) ==>
   ALL (line_ok_pre c) (append ls)`,
  CHEAT_TAC);;

let compile_all_enc_ok_pre = prove
 (`asm_offset_ok 0 (asm_config_byte_offset c) (n2w 0) /\
   ALL (\(n,p). stack_asm_ok c p) prog ==>
   (\c ls. ALL (sec_ok_pre c) ls) c (MAP prog_to_section prog)`,
  CHEAT_TAC);;

(* stack_name renames registers to obey non-clashing names
  It should be sufficient that the incoming nregs < reg_count - avoid_regs,
  and that the mapping target for these avoids bad regs
*)

let stack_to_lab_compile_all_enc_ok = prove
 (`ALL (\(n,p). stack_asm_name c p) prog /\
   ALL (\(n,p). stack_asm_remove c p) prog /\
   stack_names_names_ok (stack_to_lab_config_reg_names c1)
     (asm_config_reg_count (c:'a asm_config)) (asm_config_avoid_regs c)
     /\
   fixed_names (stack_to_lab_config_reg_names c1) c /\
   asm_offset_ok 0 (asm_config_addr_offset c) (n2w 0) /\
     good_dimindex (:'a) /\
   asm_offset_ok 0 (asm_config_byte_offset c) (n2w 0) /\
   (!n. n <= max_stack_alloc ==> asm_config_valid_imm
   c (INL word_bignum_Sub) (n2w (n * (dimindex (:'a) DIV 8))) /\
     asm_config_valid_imm
   c (INL word_bignum_Add) (n2w (n * (dimindex (:'a) DIV 8)))) /\
     asm_config_valid_imm
   c (INL word_bignum_Add) (n2w 1) /\ asm_config_valid_imm c (INL
     word_bignum_Sub) (n2w 1) /\ asm_config_valid_imm
   c (INL word_bignum_Add) (n2w 4) /\ asm_config_valid_imm c (INL
     word_bignum_Add) (n2w 8) /\
   (!s. asm_offset_ok 0 (asm_config_addr_offset c) (store_offset s))
     /\ reg_name 10 c /\
   reg_name (sp + 2) c /\ reg_name (sp + 1) c /\ reg_name sp c /\
   conf_ok (:'a) c2 /\ ~(sp = 0) ==>
   (\c ls. ALL (sec_ok_pre c) ls) c (stack_to_lab_compile c1 c2 c3
     sp (asm_config_addr_offset c) prog)`,
  CHEAT_TAC);;

let IMP_init_store_ok = prove
 (`max_heap = 2 * max_heap_limit (:'a) c1 - 1 /\
   (fmis,xxx) = full_make_init stack_conf c1 max_heap sp offset
     (bitmaps:('a word) list) code s save_regs data_sp coracle ==>
    init_store_ok c1
      (state_store fmis \\ Handler) (state_memory
       fmis) (state_mdomain
       fmis) (state_code_buffer
      fmis) (state_data_buffer
      fmis)`,
  CHEAT_TAC);;

let IMP_init_state_ok = prove
 (`4 < kkk /\
   (bitmaps:('a word) list) = CONS (n2w 4) t /\
   good_dimindex (:'a) /\
   (!n.
     (\((bm0,cfg),progs).
      ALL
        (post_alloc_conventions kkk o SND o SND) progs /\
      ALL (flat_exp_conventions o SND o SND) progs /\
      ALL ((\y. ~(raise_stub_location = y)) o FST) progs /\
      ALL ((\y. ~(wordLang_store_consts_stub_location = y)) o FST)
        progs /\
      (n = 0 ==> bm0 = LENGTH bitmaps)) (word_oracle n)) /\
   stack_oracle =
   (\n.
    (\((bm0,cfg),progs).
       (\(progs,fs,bm). (cfg,progs,append (FST bm)))
         (compile_word_to_stack
            ac F kkk progs
            (misc_Nil,bm0))) (word_oracle n)) /\
     (full_make_init scc dc max_heap stk stoff bitmaps p6 lab_st
       save_regs data_sp stack_oracle = (fmis,SOME xxx)) ==>
     init_state_ok ac kkk fmis word_oracle`,
  CHEAT_TAC);;

let full_make_init_has_fp_ops = prove
 (`full_make_init stack_conf (data_to_word_config_has_fp_tern_fupd (K
  b2) (has_fp_ops_fupd (K b1) dconf))
       mheap sp offset bitmaps code s save_regs dsp cor =
     full_make_init stack_conf dconf
       mheap sp offset bitmaps code s save_regs dsp cor`,
  CHEAT_TAC);;
add_simp full_make_init_has_fp_ops;;

let _ = size_thms "stackLang_prog";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let complex_get_code_labels_def,complex_get_code_labels_ind = define_wf
  `MEASURE (\x0. stackLang_prog_size (\x. 0) x0)`
  [`complex_get_code_labels x1 =
        match x1 with
          stackLang_Seq p1 p2 -> complex_get_code_labels p1 UNION
            complex_get_code_labels p2
        | (stackLang_If _19 _20 _21 p1 p2) ->
          complex_get_code_labels p1 UNION complex_get_code_labels p2
        | (stackLang_Call ret dest handler) ->
        (match dest with INL x -> {(x,0)} | _22 -> {}) UNION
        (match ret with NONE -> {} | SOME (r,_23,l1,l2) -> (l1,l2)
          INSERT (complex_get_code_labels r UNION
             (match handler with NONE -> {} | SOME (r,l1,l2) ->
               (l1,l2) INSERT complex_get_code_labels r)))
        | (stackLang_Loop p) -> complex_get_code_labels p
        | (stackLang_LocValue i l1 l2) -> {(l1,l2)}
        | (stackLang_RawCall l) -> {(l,1)}
        | (stackLang_JumpLower n m l) -> {(l,0)}
        | _24 -> {}`];;
add_simp complex_get_code_labels_def;;

(* [local] *)
let complex_flatten_labels = prove
 (`!t p n m cs bs.
   let pp = set_of_list (append (FST (stack_to_lab_flatten t p n m cs
     bs))) in
   UNIONS (IMAGE line_get_labels pp) SUBSET
   (n,0) INSERT
   (n,(if t /\ (?p1 p2. p = reg_alloc_Seq p1 p2) then 1 else 0))
     INSERT (
   set_of_list (MAP (\l. (n,l)) (APPEND cs bs)) UNION
   IMAGE (\n2. (n,n2)) (UNIONS (IMAGE line_get_code_labels pp)) UNION
   complex_get_code_labels p)`,
  CHEAT_TAC);;

(* [local] *)
let flatten_labels = prove
 (`!t m n p cs bs l x y.
     stack_to_lab_flatten t m n p cs bs = (l,x,y) /\
     ALL (sec_label_ok n) (append l) ==>
     UNIONS (IMAGE line_get_labels (set_of_list (append l))) SUBSET
     set_of_list (MAP (\l. (n,l)) (APPEND cs bs)) UNION
     sec_get_code_labels (Section n (append l)) UNION
     stackProps_get_code_labels m`,
  CHEAT_TAC);;

let get_labels_MAP_prog_to_section_SUBSET_code_labels_lemma = prove
 (`!p. ALL sec_labels_ok (MAP prog_to_section p) ==>
    labProps_get_labels (MAP prog_to_section p) SUBSET
    stackProps_get_code_labels (MAP prog_to_section p) UNION
    UNIONS (IMAGE stackProps_get_code_labels (set_of_list (MAP SND
      p)))`,
  CHEAT_TAC);;

(* [local] *)
let prog_to_section_preserves_MAP_FST = prove
 (`!p.
     IMAGE (\n. n,0) (set_of_list (MAP FST p)) SUBSET
     stackProps_get_code_labels (MAP prog_to_section p)`,
  CHEAT_TAC);;

let prog_to_section_labels = prove
 (`prog_to_section (n,p) = pp ==>
   sec_get_labels pp SUBSET
   sec_get_code_labels pp UNION complex_get_code_labels p`,
  CHEAT_TAC);;

let flatten_preserves_handler_labels = prove
 (`!t m n p cs bs l x y.
   stack_to_lab_flatten t m n p cs bs = (l,x,y) ==>
   stack_get_handler_labels n m SUBSET
     sec_get_code_labels (Section n (append l))`,
  CHEAT_TAC);;

let MAP_prog_to_section_preserves_handler_labels = prove
 (`!p.
    UNIONS (set_of_list (MAP (\(n,pp). stack_get_handler_labels n pp)
      p)) SUBSET
    stackProps_get_code_labels (MAP prog_to_section p)`,
  CHEAT_TAC);;

let one_prog_section = prove
 (`IMAGE (\n. (n,1)) (set_of_list (MAP FST p)) SUBSET
   stackProps_get_code_labels (MAP prog_to_section p)`,
  CHEAT_TAC);;

let get_labels_MAP_prog_to_section_SUBSET_code_labels = prove
 (`!p.
     ALL sec_labels_ok (MAP prog_to_section p) /\
      stack_good_code_labels p elabs ==>
      labProps_get_labels (MAP prog_to_section p) SUBSET
      stackProps_get_code_labels (MAP prog_to_section p) UNION
      IMAGE (\n. n,0) elabs UNION
      IMAGE (\n. n,1) elabs`,
  CHEAT_TAC);;

(* TODO: move these when the actual needed theorem is clearer...
  - e.g.: do we need a LIST_REL on the labels before/after each code
    table entry? or just a weaker BIGUNION?
    (I think the latter may be sufficient)
 *)
(* stack_names *)
(* [local] *)
let get_code_labels_comp = prove
 (`!f p. complex_get_code_labels (stack_names_comp f p) =
  complex_get_code_labels p`,
  CHEAT_TAC);;

let stack_names_get_code_labels = prove
 (`ALL2 (\cp p. complex_get_code_labels cp = complex_get_code_labels p)
   (MAP SND (stack_names_compile f prog)) (MAP SND prog)`,
  CHEAT_TAC);;

(* stack_remove *)
(* get_code_labels_comp[local] *)
let stack_to_labProof_get_code_labels_comp = prove
 (`!a b c p. stackProps_get_code_labels (stack_alloc_comp a b c p)
  SUBSET (stack_err_lab,0) INSERT stackProps_get_code_labels p`,
  CHEAT_TAC);;

(* [local] *)
(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let init_stubs_labels = prove
 (cake_as_vars (fun () ->
    `ALL (\p. stackProps_get_code_labels p SUBSET (set_of_list [(1,0);
  (start,0)])) (MAP SND (init_stubs ggc mh k start))`),
  CHEAT_TAC);;

(* ---- stack_names  ----*)
(* [local] *)
let stack_names_get_code_labels_comp = prove
 (`!f p. stackProps_get_code_labels (stack_names_comp f p) =
  stackProps_get_code_labels p`,
  CHEAT_TAC);;

(* [local] *)
let stack_names_stack_get_handler_labels_comp = prove
 (`!f p n.
   stack_get_handler_labels n (stack_names_comp f p) =
   stack_get_handler_labels n p`,
  CHEAT_TAC);;

(* [local] *)
let UNCURRY_PAIR_ETA = prove
 (`UNCURRY f = (\(p1,p2). f p1 p2)`,
  CHEAT_TAC);;

(* TODO: Exported for now -- maybe using in backendProof *)
let stack_names_stack_good_code_labels = prove
 (`!prog f. stack_good_code_labels prog elabs ==>
   stack_good_code_labels (stack_names_compile f prog) elabs`,
  CHEAT_TAC);;

(* ---- stack_remove ---- *)
(* [local] *)
let stack_remove_get_code_labels_comp = prove
 (`!a b c p.
   stackProps_get_code_labels (stack_alloc_comp a b c p) SUBSET
     (stack_err_lab,0) INSERT stackProps_get_code_labels p`,
  CHEAT_TAC);;

(* [local] *)
let stack_remove_stack_get_handler_labels_comp = prove
 (`!a b c p m.
   stack_get_handler_labels m (stack_alloc_comp a b c p) =
   stack_get_handler_labels m p`,
  CHEAT_TAC);;

(* [local] *)
let stack_remove_init_code_labels = prove
 (`x IN stackProps_get_code_labels (stack_remove_init_code ggc mh sp)
  ==> x = (1,0)`,
  CHEAT_TAC);;

let stack_remove_stack_good_code_labels = prove
 (`!prog.
   MEM loc (MAP FST prog) /\
   stack_good_code_labels prog elabs ==>
   stack_good_code_labels (stack_remove_compile jump off ggc mh sp
     loc prog) elabs`,
  CHEAT_TAC);;

(*
  The same theorem, but for the incremental version
  The jump label (2) is now assumed to be in there
*)
let stack_remove_stack_good_code_labels_incr = prove
 (`!prog.
   stack_err_lab IN elabs /\
   stack_good_code_labels prog elabs ==>
   stack_good_code_labels (MAP (stack_alloc_prog_comp jump offset
     sp) prog) elabs`,
  CHEAT_TAC);;

(* --- stack_alloc ---- *)
(* [local] *)
let stack_alloc_get_code_labels_comp = prove
 (`!n m p pp mm.
   stackProps_get_code_labels (FST (stack_alloc_comp n m p)) SUBSET
     (gc_stub_location,0) INSERT stackProps_get_code_labels p`,
  CHEAT_TAC);;

(* [local] *)
let stack_alloc_stack_get_handler_labels_comp = prove
 (`!n m p pp mm.
   stack_get_handler_labels i (FST (stack_alloc_comp n m p)) =
     stack_get_handler_labels i p`,
  CHEAT_TAC);;

(* [local] *)
let stack_alloc_init_code_labels = prove
 (`stackProps_get_code_labels (word_gc_code c) = {}`,
  CHEAT_TAC);;

let stack_alloc_stack_good_code_labels = prove
 (`!prog c.
   stack_good_code_labels prog elabs ==>
   stack_good_code_labels (stack_alloc_compile c prog) elabs`,
  CHEAT_TAC);;

(*
  The same theorem, but for the incremental version
  The jump label (2) is now assumed to be in there
*)
let stack_alloc_stack_good_code_labels_incr = prove
 (`!prog.
   gc_stub_location IN elabs /\
   stack_good_code_labels prog elabs ==>
   stack_good_code_labels (MAP stack_alloc_prog_comp prog) elabs`,
  CHEAT_TAC);;

let IN_get_code_labels_comp_top_lemma = prove
 (`!i q p_1 p_2.
     ((p_1,p_2) IN stackProps_get_code_labels (stack_rawcall_comp i
       q) ==>
      (?k. (p_1,k) IN stackProps_get_code_labels q /\
          (~(p_2 = k) ==> p_2 = 1 /\ k = 0 /\ p_1 IN domain i))) /\
     ((p_1,p_2) IN stackProps_get_code_labels (comp_top i q) ==>
      (?k. (p_1,k) IN stackProps_get_code_labels q /\
          (~(p_2 = k) ==> p_2 = 1 /\ k = 0 /\ p_1 IN domain i)))`,
  CHEAT_TAC);;

let IN_domain_collect_info = prove
 (`!prog f p_1.
     p_1 IN domain (collect_info prog f) ==>
     MEM p_1 (MAP FST prog) \/ p_1 IN domain f`,
  CHEAT_TAC);;

let IN_get_code_labels_comp_top = prove
 (`(p_1,p_2) IN stackProps_get_code_labels (comp_top (collect_info prog
  LN) q) ==>
   (?k. (p_1,k) IN stackProps_get_code_labels q /\
       (~(p_2 = k) ==> p_2 = 1 /\ k = 0 /\ MEM p_1 (MAP FST prog)))`,
  CHEAT_TAC);;

let stack_rawcall_stack_good_code_labels = prove
 (`stack_good_code_labels prog elabs ==>
   stack_good_code_labels (stack_rawcall_compile prog) elabs`,
  CHEAT_TAC);;

(* stack_to_lab *)
let stack_to_lab_stack_good_code_labels = prove
 (`stack_to_lab_compile stack_conf data_conf max_heap sp offset prog =
  prog' /\
   MEM InitGlobals_location (MAP FST prog) /\
   stack_good_code_labels prog elabs /\
   ALL sec_labels_ok prog' ==>
   // TODO: pretty sure this is only ever used with elabs = {}
   labProps_get_labels prog' SUBSET stackProps_get_code_labels
     prog' UNION IMAGE (\n. n,0) elabs UNION IMAGE (\n. n,1) elabs`,
  CHEAT_TAC);;

let stack_to_lab_stack_good_code_labels_incr = prove
 (`stack_err_lab IN elabs /\
   gc_stub_location IN elabs /\
   compile_no_stubs f jump offset sp prog = prog' /\
   stack_good_code_labels prog elabs /\
   ALL sec_labels_ok prog' ==>
   labProps_get_labels prog' SUBSET stackProps_get_code_labels
     prog' UNION IMAGE (\n. n,0) elabs UNION IMAGE (\n. n,1) elabs`,
  CHEAT_TAC);;

(* nonzero restricted code labels *)
let nonzero_get_labels_MAP_prog_to_section_SUBSET_code_labels = prove
 (`!p.
      ALL sec_labels_ok (MAP prog_to_section p) /\
      stack_good_handler_labels p ==>
      restrict_nonzero (labProps_get_labels (MAP prog_to_section p))
        SUBSET
      stackProps_get_code_labels (MAP prog_to_section p)`,
  CHEAT_TAC);;

let stack_names_stack_good_handler_labels = prove
 (`!prog f. stack_good_handler_labels prog ==>
   stack_good_handler_labels (stack_names_compile f prog)`,
  CHEAT_TAC);;

let restrict_nonzero_union = prove
 (`restrict_nonzero (A UNION B) = restrict_nonzero A UNION
  restrict_nonzero B`,
  CHEAT_TAC);;

let restrict_nonzero_IN = prove
 (`x IN restrict_nonzero s <=> x IN s /\ ~(SND x = 0)`,
  CHEAT_TAC);;

let stack_good_handler_labels_append = prove
 (`stack_good_handler_labels xs /\
   stack_good_handler_labels ys ==>
   stack_good_handler_labels (APPEND xs ys)`,
  CHEAT_TAC);;

let stack_remove_stack_good_handler_labels_incr = prove
 (`!prog.
   stack_good_handler_labels prog ==>
   stack_good_handler_labels (MAP (stack_alloc_prog_comp jump
     offset sp) prog)`,
  CHEAT_TAC);;

let stack_remove_stack_good_handler_labels = prove
 (`!prog.
   stack_good_handler_labels prog ==>
   stack_good_handler_labels (stack_remove_compile jump off ggc mh
     sp loc prog)`,
  CHEAT_TAC);;

let stack_alloc_stack_good_handler_labels_incr = prove
 (`!prog.
   stack_good_handler_labels prog ==>
   stack_good_handler_labels (MAP stack_alloc_prog_comp prog)`,
  CHEAT_TAC);;

let stack_alloc_stack_good_handler_labels = prove
 (`!prog c.
   stack_good_handler_labels prog ==>
   stack_good_handler_labels (stack_alloc_compile c prog)`,
  CHEAT_TAC);;

let stack_rawcall_stack_good_handler_labels = prove
 (`stack_good_handler_labels prog ==>
   stack_good_handler_labels (stack_rawcall_compile prog)`,
  CHEAT_TAC);;

let stack_to_lab_stack_good_handler_labels = prove
 (`stack_to_lab_compile stack_conf data_conf max_heap sp offset prog =
  prog' /\
   stack_good_handler_labels prog /\
   ALL sec_labels_ok prog' ==>
   restrict_nonzero (labProps_get_labels prog') SUBSET
     stackProps_get_code_labels prog'`,
  CHEAT_TAC);;

let stack_to_lab_stack_good_handler_labels_incr = prove
 (`compile_no_stubs f jump offset sp prog = prog' /\
   stack_good_handler_labels prog /\
   ALL sec_labels_ok prog' ==>
   restrict_nonzero (labProps_get_labels prog') SUBSET
     stackProps_get_code_labels prog'`,
  CHEAT_TAC);;

(*** no_shmemop ***)

let stack_rawcall_comp_no_shmemop = prove
 (`!i p. no_shmemop p ==> no_shmemop (stack_alloc_comp i p)`,
  CHEAT_TAC);;

let stack_rawcall_comp_top_no_shmemop = prove
 (`!p. no_shmemop p ==> no_shmemop (comp_top i p)`,
  CHEAT_TAC);;

let stack_rawcall_compile_no_shmemop = prove
 (`!prog. ALL (\(a,p). no_shmemop p) prog ==>
       ALL (\(a,p). no_shmemop p) (stack_to_lab_compile prog)`,
  CHEAT_TAC);;

let stack_alloc_comp_no_shmemop = prove
 (`!n m p. no_shmemop p ==> no_shmemop (FST (stack_alloc_comp n m p))`,
  CHEAT_TAC);;

let stack_alloc_prog_comp_no_shmemop = prove
 (`!prog.
   ALL (\(a,p). no_shmemop p) prog ==>
   ALL (\(a,p). no_shmemop p) (MAP stack_alloc_prog_comp prog)`,
  CHEAT_TAC);;

let stack_alloc_compile_no_shmemop = prove
 (`ALL (\(a,p). no_shmemop p) prog ==>
   ALL (\(a,p). no_shmemop p) (stack_alloc_compile data prog)`,
  CHEAT_TAC);;

let upshift_no_shmemop = prove
 (`!k n. no_shmemop (upshift k n)`,
  CHEAT_TAC);;
add_simp upshift_no_shmemop;;

let downshift_no_shmemop = prove
 (`!k n. no_shmemop (downshift k n)`,
  CHEAT_TAC);;
add_simp downshift_no_shmemop;;

let stack_free_no_shmemop = prove
 (`!k n. no_shmemop (word_to_stack_stack_free k n)`,
  CHEAT_TAC);;
add_simp stack_free_no_shmemop;;

let stack_alloc_no_shmemop = prove
 (`!jump k n. no_shmemop (stack_alloc jump k n)`,
  CHEAT_TAC);;
add_simp stack_alloc_no_shmemop;;

let stack_remove_comp_no_shmemop = prove
 (`!jump off k p. no_shmemop p ==> no_shmemop (stack_alloc_comp jump
  off k p)`,
  CHEAT_TAC);;

let stack_remove_prog_comp_no_shmemop = prove
 (`!p. no_shmemop p ==> no_shmemop (SND (stack_alloc_prog_comp jump
  off k (n,p)))`,
  CHEAT_TAC);;

let stack_remove_compile_no_shmemop = prove
 (`ALL (\(a,p). no_shmemop p) prog ==>
   ALL (\(a,p). no_shmemop p) (stack_remove_compile jump offset
     gckind mh sp loc prog)`,
  CHEAT_TAC);;

let stack_names_comp_no_shmemop = prove
 (`!f p. no_shmemop p ==> no_shmemop (stack_names_comp f p)`,
  CHEAT_TAC);;

let stack_names_prog_comp_no_shmemop = prove
 (`!prog.
   ALL (\(a,p). no_shmemop p) prog ==>
   ALL (\(a,p). no_shmemop p) (MAP (stack_alloc_prog_comp f) prog)`,
  CHEAT_TAC);;

let stack_names_compile_no_shmemop = prove
 (`ALL (\(a,p). no_shmemop p) prog ==>
   ALL (\(a,p). no_shmemop p) (stack_names_compile names prog)`,
  CHEAT_TAC);;

let flatten_no_share_mem_inst = prove
 (`!t p n m cs bs.
       no_shmemop p ==>
       ALL (\ln. !op re a inst' len. ~(ln = labLang_Asm (ShareMem op
         re a) inst' len))
             (append (FST (stack_to_lab_flatten t p n m cs bs)))`,
  CHEAT_TAC);;

let asm_fetch_aux_no_share_mem_inst_CONS = prove
 (`!xs.
   ALL (\ln. !op re a inst' len. ~(ln = labLang_Asm (ShareMem op re
     a) inst' len)) xs /\
   no_share_mem_inst ls ==>
   no_share_mem_inst (CONS (Section k xs) ls)`,
  CHEAT_TAC);;

let prog_to_section_no_share_mem_inst = prove
 (`!prog. ALL (\(a,p). no_shmemop p) prog ==>
          no_share_mem_inst (MAP prog_to_section prog)`,
  CHEAT_TAC);;

let compile_no_share_mem_inst = prove
 (`!prog prog'.
   ALL (\(a,p). no_shmemop p) prog /\
   stack_to_lab_compile stack_conf data_conf max_heap sp offset prog
     = prog' ==>
   no_share_mem_inst prog'`,
  CHEAT_TAC);;

let stack_remove_prog_comp_no_shmemop_MAP = prove
 (`ALL (\(a,p). no_shmemop p) prog ==>
   ALL (\(a,p). no_shmemop p) (MAP (stack_alloc_prog_comp jump
     offset sp) prog)`,
  CHEAT_TAC);;

let compile_no_stubs_no_share_mem_inst = prove
 (`ALL (\(a,p). no_shmemop p) prog /\
   compile_no_stubs f jump offset sp prog = prog' ==>
   no_share_mem_inst prog'`,
  CHEAT_TAC);;

(*** no_install ***)

let stack_rawcall_comp_no_install = prove
 (`!i p. stackProps_no_install p ==> stackProps_no_install
  (stack_alloc_comp i p)`,
  CHEAT_TAC);;

let stack_rawcall_comp_top_no_install = prove
 (`!p. stackProps_no_install p ==> stackProps_no_install (comp_top i
  p)`,
  CHEAT_TAC);;

let stack_rawcall_compile_no_install = prove
 (`!prog. ALL (\(a,p). stackProps_no_install p) prog ==>
       ALL (\(a,p). stackProps_no_install p) (stack_to_lab_compile
         prog)`,
  CHEAT_TAC);;

let stack_alloc_comp_no_install = prove
 (`!n m p. stackProps_no_install p ==> stackProps_no_install (FST
  (stack_alloc_comp n m p))`,
  CHEAT_TAC);;

let stack_alloc_prog_comp_no_install = prove
 (`!prog.
   ALL (\(a,p). stackProps_no_install p) prog ==>
   ALL (\(a,p). stackProps_no_install p) (MAP stack_alloc_prog_comp
     prog)`,
  CHEAT_TAC);;

let stack_alloc_compile_no_install = prove
 (`ALL (\(a,p). stackProps_no_install p) prog ==>
   ALL (\(a,p). stackProps_no_install p) (stack_alloc_compile data
     prog)`,
  CHEAT_TAC);;

let upshift_no_install = prove
 (`!k n. stackProps_no_install (upshift k n)`,
  CHEAT_TAC);;
add_simp upshift_no_install;;

let downshift_no_install = prove
 (`!k n. stackProps_no_install (downshift k n)`,
  CHEAT_TAC);;
add_simp downshift_no_install;;

let stack_free_no_install = prove
 (`!k n. stackProps_no_install (word_to_stack_stack_free k n)`,
  CHEAT_TAC);;
add_simp stack_free_no_install;;

let stack_alloc_no_install = prove
 (`!jump k n. stackProps_no_install (stack_alloc jump k n)`,
  CHEAT_TAC);;
add_simp stack_alloc_no_install;;

let stack_remove_comp_no_install = prove
 (`!jump off k p. stackProps_no_install p ==> stackProps_no_install
  (stack_alloc_comp jump off k p)`,
  CHEAT_TAC);;

let stack_remove_prog_comp_no_install = prove
 (`!p. stackProps_no_install p ==> stackProps_no_install (SND
  (stack_alloc_prog_comp jump off k (n,p)))`,
  CHEAT_TAC);;

let stack_remove_compile_no_install = prove
 (`ALL (\(a,p). stackProps_no_install p) prog ==>
   ALL (\(a,p). stackProps_no_install p) (stack_remove_compile jump
     offset gckind mh sp loc prog)`,
  CHEAT_TAC);;

let stack_names_comp_no_install = prove
 (`!f p. stackProps_no_install p ==> stackProps_no_install
  (stack_names_comp f p)`,
  CHEAT_TAC);;

let stack_names_prog_comp_no_install = prove
 (`!prog.
   ALL (\(a,p). stackProps_no_install p) prog ==>
   ALL (\(a,p). stackProps_no_install p) (MAP
     (stack_alloc_prog_comp f) prog)`,
  CHEAT_TAC);;

let stack_names_compile_no_install = prove
 (`ALL (\(a,p). stackProps_no_install p) prog ==>
   ALL (\(a,p). stackProps_no_install p) (stack_names_compile names
     prog)`,
  CHEAT_TAC);;

let flatten_no_install = prove
 (`!t p n m cs bs.
       stackProps_no_install p ==>
       ALL (\ln. !w bytes l. ~(ln = labLang_LabAsm labLang_Install w
         bytes l))
             (append (FST (stack_to_lab_flatten t p n m cs bs)))`,
  CHEAT_TAC);;

let asm_fetch_aux_no_install_CONS = prove
 (`!xs.
   ALL (\ln. !w bytes l. ~(ln = labLang_LabAsm labLang_Install w
     bytes l)) xs /\
   stackProps_no_install ls ==>
   stackProps_no_install (CONS (Section k xs) ls)`,
  CHEAT_TAC);;

let prog_to_section_no_install = prove
 (`!prog. ALL (\(a,p). stackProps_no_install p) prog ==>
          stackProps_no_install (MAP prog_to_section prog)`,
  CHEAT_TAC);;

let stack_to_lab_compile_no_install = prove
 (`!prog prog'.
   ALL (\(a,p). stackProps_no_install p) prog /\
   stack_to_lab_compile stack_conf data_conf max_heap sp offset prog
     = prog' ==>
   labProps_no_install prog'`,
  CHEAT_TAC);;
