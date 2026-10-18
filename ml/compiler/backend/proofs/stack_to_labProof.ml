(* ======================================================== *)
(*  stack_to_labProof: ported from HOL4's
    compiler/backend/proofs/stack_to_labProofScript.sml  *)
(* ======================================================== *)

(*
  Correctness proof for stack_to_lab
*)

needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/bvl_to_bvi.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/data_live.ml";;
needs "compiler/backend/labLang.ml";;
needs "compiler/backend/proofs/data_to_word_gcProof.ml";;
needs "compiler/backend/proofs/stack_allocProof.ml";;
needs "compiler/backend/proofs/stack_namesProof.ml";;
needs "compiler/backend/proofs/stack_rawcallProof.ml";;
needs "compiler/backend/proofs/stack_removeProof.ml";;
needs "compiler/backend/proofs/word_to_stackProof.ml";;
needs "compiler/backend/semantics/labProps.ml";;
needs "compiler/backend/semantics/labSem.ml";;
needs "compiler/backend/semantics/stackProps.ml";;
needs "compiler/backend/semantics/stackSem.ml";;
needs "compiler/backend/semantics/wordConvs.ml";;
needs "compiler/backend/semantics/wordProps.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/backend/stackLang.ml";;
needs "compiler/backend/stack_alloc.ml";;
needs "compiler/backend/stack_to_lab.ml";;
needs "lib/alignment.ml";;
needs "lib/byte.ml";;
needs "lib/set_sep.ml";;
needs "lib/sptree.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "semantics/evaluate.ml";;
needs "semantics/proofs/semanticsProps.ml";;

(* HOL4 stack_to_labProofScript.sml:23-24: ML code, not ported *)

(* HOL4 stack_to_labProofScript.sml:26: code that the source has in a
   comment *)

(* HOL4 stack_to_labProofScript.sml:28: the overload Loc, which the
   port expands *)

(* TODO: move *)

let dest_to_loc_def = cake_define
  `dest_to_loc regs' dest =
     (match dest with INL p -> p | INR r -> (match FAPPLY regs' r
       with wordLang_Loc loc _1 -> loc))`;;

let dest_to_loc'_def = cake_define
  `dest_to_loc' regs' dest =
     (match dest with INL p -> p | INR r -> (match regs' r with
       wordLang_Loc loc _2 -> loc))`;;

(* -- Lemmas about code_installed, loc_to_pc and asm_fetch_aux -- *)

let code_installed_def = cake_define_list
  [`stack_to_labProof_code_installed n [] code = T`;
   `stack_to_labProof_code_installed n (x :: xs) code <=>
       (if is_Label x then
         (match x with Label l1 l2 _4 -> loc_to_pc l1 l2 code = SOME
           n) /\
         stack_to_labProof_code_installed n xs code else
         asm_fetch_aux n code = SOME x /\
         stack_to_labProof_code_installed (n + 1) xs code)`];;
hol4_overload "code_installed" "stack_to_labProof_code_installed";;

(* TODO: these may already be proved in lab_filter or lab_to_target,
         they ought to move into labProps
*)

(* Appending on the other side *)

(* loc_to_pc on the other side *)

let code_installed'_def = cake_define_list
  [`code_installed' n [] code <=> T`;
   `code_installed' n (x :: xs) code <=>
         (if is_Label x then code_installed' n xs code else
           asm_fetch_aux n code = SOME x /\ code_installed' (n + 1)
           xs code)`];;

let labs_correct_def = cake_define_list
  [`labs_correct n [] code <=> T`;
   `labs_correct n (x :: xs) code <=>
         (if is_Label x then labs_correct n xs code /\
           (match x with Label l1 l2 v2 -> loc_to_pc l1 l2 code
             = SOME n | _6 -> T) else labs_correct (n + 1) xs code)`];;

(* HOL4 stack_to_labProofScript.sml:391: ML code, not ported *)

(* HOL4 stack_to_labProofScript.sml:434-435: ML code, not ported *)

let labels_ok_def = cake_define
  `labels_ok code <=>
   ALL_DISTINCT (MAP (\s. match s with Section n _7 -> n) code) /\
   EVERY (\s. match s with Section n lines ->
     (let labs = extract_labels lines in
     EVERY (\(l1,l2). l1 = n /\ ~(l2 = 0)) labs /\
     ALL_DISTINCT labs)) code`;;

(* -- End code_installed lemmas  -- *)

let state_rel_def = cake_define
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
     (!n prog. lookup n (stackSem_state_code s) = SOME prog ==>
       call_args prog (labSem_state_ptr_reg t) (labSem_state_len_reg
         t) (labSem_state_ptr2_reg t) (labSem_state_len2_reg t)
         (labSem_state_link_reg t) /\
       (?pc'. stack_to_labProof_code_installed pc'
              (append (FST (stack_to_lab_flatten T prog n (next_lab
                prog 2) [] []))) (labSem_state_code t) /\
            loc_to_pc n 0 (labSem_state_code t) = SOME pc')) /\
     domain (stackSem_state_code s) = set_of_list (MAP Section_num
       (labSem_state_code t)) /\
     EVERY sec_labels_ok (labSem_state_code t) /\
     ~labSem_state_failed t /\ ~(labSem_state_link_reg
     t = labSem_state_len_reg t) /\ ~(labSem_state_link_reg t =
       labSem_state_ptr_reg t) /\ ~(labSem_state_link_reg
     t = labSem_state_len2_reg t) /\ ~(labSem_state_link_reg t =
       labSem_state_ptr2_reg t) /\
     ~(labSem_state_link_reg t IN stackSem_state_ffi_save_regs s) /\
     (!k i n. k IN stackSem_state_ffi_save_regs s ==>
       labSem_state_io_regs t n i k = NONE) /\
     (!k n. k IN stackSem_state_ffi_save_regs s ==>
       labSem_state_cc_regs t n k = NONE) /\
     (!x. x IN stackSem_state_mdomain s ==> w2n x MOD (dimindex (:'a)
       DIV 8) = 0) /\
     (!x. x IN stackSem_state_sh_mdomain s ==> w2n x MOD (dimindex
       (:'a) DIV 8) = 0) /\ stackSem_state_code_buffer
     s = labSem_state_code_buffer t /\ stackSem_state_compile
     s = (\c p. labSem_state_compile t c (MAP prog_to_section p)) /\
     (labSem_state_compile_oracle t = (\n. let (c,p,_8) =
       stackSem_state_compile_oracle s n in
                            (c,MAP prog_to_section p))) /\
     (!k. let (c,ps,_9) = stackSem_state_compile_oracle s k in
       EVERY (\(n,p).
         call_args p (labSem_state_ptr_reg t) (labSem_state_len_reg
           t) (labSem_state_ptr2_reg t) (labSem_state_len2_reg t)
           (labSem_state_link_reg t) /\
         EVERY (\(l1,l2). l1 = n /\ ~(l2 = 0) /\ ~(l2 = 1))
           (extract_labels p) /\
         ALL_DISTINCT (extract_labels p)) ps /\
         ALL_DISTINCT (MAP FST ps)) /\
     ~stackSem_state_use_stack s /\
     ~stackSem_state_use_store s /\
     ~stackSem_state_use_alloc s /\
     good_dimindex (:'a)`;;
hol4_overload "state_rel" "stack_to_labProof_state_rel";;

(* HOL4 stack_to_labProofScript.sml:926: the ML values that the
   definitions below antiquote *)

let result_view_INDUCT,result_view_RECURSION = define_datatype
  "result_view = Vloc (num) (num) | Vcont (num) (num) | Vtimeout | \
   Verr";;

let result_view_def = cake_define
  `result_view x1 l cs bs =
        match x1 with
          stackSem_Result (wordLang_Loc n1 n2) -> Vloc n1 n2
        | (Exception (wordLang_Loc n1 n2)) -> Vloc n1 n2
        | TimeOut -> Vtimeout
        | (Continue n) -> Vcont l (find_lab n cs)
        | (Break n) -> Vloc l (find_lab n bs)
        | _10 -> Verr`;;

let halt_word_view_def = cake_define
  `halt_word_view x1 =
        match x1 with
          wordLang_Word (n2w 0) -> Halt ffi_Success
        | (wordLang_Word _11) -> Halt ffi_Resource_limit_hit
        | _12 -> Error`;;

let halt_view_def = cake_define
  `halt_view x1 =
        match x1 with
          SOME (Halt w) -> SOME (halt_word_view w)
        | (SOME (FinalFFI outcome)) -> SOME (Halt (ffi_FFI_outcome
          outcome))
        | _13 -> NONE`;;

(* HOL4 stack_to_labProofScript.sml:966-1017: a proof *)

(* Proving that stack_to_lab generates labels_ok *)
(* HOL4 stack_to_labProofScript.sml:1020: ML code, not ported *)

let halt_assum_def = cake_define
  `halt_assum (:'ffi#'c) code <=>
    (!(s:('a,'c,'ffi)stackSem_state).
      subspt code (stackSem_state_code s) /\ ~(stackSem_state_clock s
        = 0) ==>
      (?t. evaluate (Call NONE (INL 1) NONE,s) = (SOME (Halt
        (wordLang_Word (n2w 0))),t) /\ stackSem_state_ffi
          t = stackSem_state_ffi s /\ stackSem_state_clock t =
            stackSem_state_clock s - 1))`;;

let make_init_def = cake_define
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
hol4_overload "make_init" "stack_to_labProof_make_init";;

(* HOL4 stack_to_labProofScript.sml:3047-3049: ML code, not ported *)

(* HOL4 stack_to_labProofScript.sml:3051: the overload
   stack_to_lab_compile, which the port expands *)
(* HOL4 stack_to_labProofScript.sml:3052: the overload
   stack_names_compile, which the port expands *)
(* HOL4 stack_to_labProofScript.sml:3053: the overload
   stack_alloc_compile, which the port expands *)
(* HOL4 stack_to_labProofScript.sml:3054: the overload
   stack_remove_compile, which the port expands *)

let full_make_init_def = cake_define
  `full_make_init stack_conf data_conf max_heap sp offset bitmaps code
  s4 save_regs data_sp coracle =
   (let ggc = is_gen_gc (data_to_word_config_gc_kind data_conf) in
   let jump = stack_to_lab_config_jump stack_conf in
   let code1 = stack_alloc_compile data_conf (stack_rawcall_compile
     code) in
   let code2 = compile jump offset ggc max_heap sp
     InitGlobals_location code1 in
   let code3 = fromAList (compile (stack_to_lab_config_reg_names
     stack_conf) code2) in
   let coracle1 = (I ## MAP prog_comp ## I) o coracle in
   let coracle2 = (I ## MAP (prog_comp jump offset sp) ## I) o
     coracle1 in
   let coracle3 = (I ## compile (stack_to_lab_config_reg_names
     stack_conf) ## I) o coracle2 in
   let s3 = make_init code3 coracle3 (MAP (tlookup
     (stack_to_lab_config_reg_names stack_conf)) [2; 3; 4]) save_regs s4
     in
   let s2 = make_init (stack_to_lab_config_reg_names stack_conf)
     (fromAList code2) coracle2 s3 in
   let s1 = make_init_any ggc max_heap bitmaps data_sp coracle1 jump
     offset sp (fromAList code1) s2 in
     (make_init data_conf (fromAList code) coracle s1,
      make_init_opt ggc max_heap bitmaps data_sp coracle1 jump
        offset sp (fromAList code1) s2))`;;

let memory_assumption_def = cake_define
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
      (word_list bitmap_ptr (MAP wordLang_Word bitmaps) *
       word_list_exists (bitmap_ptr + bytes_in_word * n2w (LENGTH
         bitmaps)) data_sp *
       word_list_exists ptr2
         (w2n (--(n2w 1) * ptr2 + ptr4) DIV w2n (bytes_in_word:'a
           word)))
        (fun2set (labSem_state_mem t,labSem_state_mem_domain t)))`;;

(* HOL4 stack_to_labProofScript.sml:3209: ML code, not ported *)

(* HOL4 stack_to_labProofScript.sml:3218-3270: code that the source
   has in a comment *)

let good_code_def = cake_define
  `stack_to_labProof_good_code sp code <=>
    ALL_DISTINCT (MAP FST code) /\
    EVERY (\(k,prog). stack_num_stubs <= k /\ alloc_arg prog) code /\
    EVERY (\p. call_args p 1 2 3 4 0) (MAP SND code) /\
    EVERY (\p. reg_bound p sp) (MAP SND code) /\
    EVERY
    (\(n,p).
       EVERY (\(l1,l2). l1 = n /\ ~(l2 = 0) /\ ~(l2 = 1))
         (extract_labels p) /\
       ALL_DISTINCT (extract_labels p)) code`;;
hol4_overload "good_code" "stack_to_labProof_good_code";;

let contain_def = cake_define
  `contain b = Abbrev b`;;

(* HOL4 stack_to_labProofScript.sml:3627: ML code, not ported *)

(* stack_name renames registers to obey non-clashing names
  It should be sufficient that the incoming nregs < reg_count -
    avoid_regs,
  and that the mapping target for these avoids bad regs
*)

let complex_get_code_labels_def = cake_define
  `complex_get_code_labels x1 =
        match x1 with
          stackLang_Seq p1 p2 -> complex_get_code_labels p1 UNION
            complex_get_code_labels p2
        | (If _14 _15 _16 p1 p2) -> complex_get_code_labels p1 UNION
          complex_get_code_labels p2
        | (Call ret dest handler) ->
        (match dest with INL x -> {(x,0)} | _17 -> {}) UNION
        (match ret with NONE -> {} | SOME (r,_18,l1,l2) -> (l1,l2)
          INSERT (complex_get_code_labels r UNION
             (match handler with NONE -> {} | SOME (r,l1,l2) ->
               (l1,l2) INSERT complex_get_code_labels r)))
        | (Loop p) -> complex_get_code_labels p
        | (LocValue i l1 l2) -> {(l1,l2)}
        | (stackLang_RawCall l) -> {(l,1)}
        | (stackLang_JumpLower n m l) -> {(l,0)}
        | _19 -> {}`;;

(* TODO: move these when the actual needed theorem is clearer...
  - e.g.: do we need a LIST_REL on the labels before/after each code
    table entry? or just a weaker BIGUNION?
    (I think the latter may be sufficient)
 *)
(* stack_names *)

(* stack_remove *)

(* ---- stack_names  ----*)

(* TODO: Exported for now -- maybe using in backendProof *)

(* ---- stack_remove ---- *)

(*
  The same theorem, but for the incremental version
  The jump label (2) is now assumed to be in there
*)

(* --- stack_alloc ---- *)

(*
  The same theorem, but for the incremental version
  The jump label (2) is now assumed to be in there
*)

(* stack_to_lab *)

(* nonzero restricted code labels *)

(*** no_shmemop ***)

(*** no_install ***)
