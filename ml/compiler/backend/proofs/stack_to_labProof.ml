(* ======================================================== *)
(*  stack_to_labProof: ported from HOL4's
    compiler/backend/proofs/stack_to_labProofScript.sml  *)
(* ======================================================== *)

(*
  Correctness proof for stack_to_lab
*)

needs "basis/pure/mlsexp.ml";;
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
needs "compiler/backend/wordLang.ml";;
needs "lib/alignment.ml";;
needs "lib/byte.ml";;
needs "lib/peg.ml";;
needs "lib/pegexec.ml";;
needs "lib/set_sep.ml";;
needs "lib/sptree.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "semantics/evaluate.ml";;
needs "semantics/proofs/semanticsProps.ml";;

(* HOL4 ML code, not ported:
val get_labels_def = stackSemTheory.get_labels_def;
val get_reg_value_def = targetSemTheory.get_reg_value_def;
*)

(* val _ = set_prover (fn (tm,_) => mk_thm([],tm)); remove *)

(* HOL4 overload (expanded in the port):
     Loc = wordLang$Loc *)

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

(* HOL4 ML code, not ported:
val is_Label_def = labSemTheory.is_Label_def
*)

(* HOL4 ML code, not ported:
val extract_labels_def = labPropsTheory.extract_labels_def
val extract_labels_append = labPropsTheory.extract_labels_append
*)

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
     (!n v. FLOOKUP (regs s) n = SOME v ==> regs t n = v) /\
     (!n v. FLOOKUP (fp_regs s) n = SOME v ==> fp_regs t n = v) /\
       mem
     t = state_memory s /\ mem_domain
     t = state_mdomain s /\ labSem_state_shared_mem_domain
     t = state_sh_mdomain s /\ be
     t = be s /\ state_ffi
     t = state_ffi s /\ state_clock
     t = state_clock s /\
     (!n prog. lookup n (state_code s) = SOME prog ==>
       call_args prog (ptr_reg t) (len_reg t) (ptr2_reg t) (len2_reg
         t) (link_reg t) /\
       (?pc'. stack_to_labProof_code_installed pc'
              (append (FST (flatten T prog n (next_lab prog 2) []
                []))) (state_code t) /\
            loc_to_pc n 0 (state_code t) = SOME pc')) /\
     domain (state_code s) = set_of_list (MAP Section_num (state_code
       t)) /\
     EVERY sec_labels_ok (state_code t) /\
     ~failed t /\ ~(link_reg
     t = len_reg t) /\ ~(link_reg t = ptr_reg t) /\ ~(link_reg
     t = len2_reg t) /\ ~(link_reg t = ptr2_reg t) /\
     ~(link_reg t IN stackSem_state_ffi_save_regs s) /\
     (!k i n. k IN stackSem_state_ffi_save_regs s ==>
       labSem_state_io_regs t n i k = NONE) /\
     (!k n. k IN stackSem_state_ffi_save_regs s ==>
       labSem_state_cc_regs t n k = NONE) /\
     (!x. x IN state_mdomain s ==> w2n x MOD (dimindex (:'a) DIV 8) =
       0) /\
     (!x. x IN state_sh_mdomain s ==> w2n x MOD (dimindex (:'a) DIV
       8) = 0) /\ state_code_buffer
     s = state_code_buffer t /\ compile
     s = (\c p. compile t c (MAP prog_to_section p)) /\
     (compile_oracle t = (\n. let (c,p,_8) = compile_oracle s n in
                            (c,MAP prog_to_section p))) /\
     (!k. let (c,ps,_9) = compile_oracle s k in
       EVERY (\(n,p).
         call_args p (ptr_reg t) (len_reg t) (ptr2_reg t) (len2_reg
           t) (link_reg t) /\
         EVERY (\(l1,l2). l1 = n /\ ~(l2 = 0) /\ ~(l2 = 1))
           (extract_labels p) /\
         ALL_DISTINCT (extract_labels p)) ps /\
         ALL_DISTINCT (MAP FST ps)) /\
     ~stackSem_state_use_stack s /\
     ~stackSem_state_use_store s /\
     ~stackSem_state_use_alloc s /\
     good_dimindex (:'a)`;;
hol4_overload "state_rel" "stack_to_labProof_state_rel";;

(* HOL4 ML code, not ported:
val s = ``s:('a,'c,'ffi) labSem$state``;
*)

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
          backend_passes_Word (n2w 0) -> Halt Success
        | (Word _11) -> Halt ffi_Resource_limit_hit
        | _12 -> Error`;;

let halt_view_def = cake_define
  `halt_view x1 =
        match x1 with
          SOME (Halt w) -> SOME (halt_word_view w)
        | (SOME (FinalFFI outcome)) -> SOME (Halt (ffi_FFI_outcome
          outcome))
        | _13 -> NONE`;;

(* HOL4 ML code, not ported:
val finish_tac =
  rename1`halt_view (SOME z)` \\ Cases_on`z` \\ fs[] >>
  imp_res_tac loc_to_pc_isPREFIX>>
  imp_res_tac code_installed_isPREFIX>>fs[]>>
  TRY(rename1`result_view (_ w)` \\ Cases_on`w` \\ fs[]) >>
  TRY (
    map_every qexists_tac[`ck+ck'+1`,`t2'`] >> simp[] >>
    reverse conj_tac >- metis_tac[IS_PREFIX_TRANS,evaluate_mono] >>
    gen_tac >>
    qpat_abbrev_tac`ss:('a,'c,'ffi)labSem$state = _ _` >>
    first_x_assum(qspec_then`ss`mp_tac) >>
    impl_tac >- (
      simp[Abbr`ss`] >>
      srw_tac[][] >>
        full_simp_tac(srw_ss())[Abbr`regs`,APPLY_UPDATE_THM] >>
      full_simp_tac(srw_ss())[find_code_def,DOMSUB_FLOOKUP_THM] >>
      full_simp_tac(srw_ss())[FLOOKUP_DEF] >>
      full_simp_tac(srw_ss())[state_rel_def,FLOOKUP_DEF] >>
      every_case_tac >> full_simp_tac(srw_ss())[]) >>
    simp[upd_pc_def,dec_clock_def,Abbr`ss`] >>
    strip_tac >>
    last_x_assum(qspec_then`ck1+ck'`mp_tac) >>
    last_x_assum(qspec_then`ck1+ck'`mp_tac) >>
    simp[] >> NO_TAC ) >>
  TRY(rename1 `FFI_outcome` >>
      simp[Once
        labSemTheory.evaluate_def,asm_fetch_def,get_pc_value_def,
          inc_pc_def,dec_clock_def,upd_reg_def,lab_to_loc_def] >>
      qexists_tac `ck + ck' + 1` >> simp[] >>
      qmatch_goalsub_abbrev_tac `evaluate a1` >>
      first_x_assum(qspec_then `a1` mp_tac) >>
      impl_tac >- (
       simp[Abbr`a1`] >>
       srw_tac[][] >>
         full_simp_tac(srw_ss())[Abbr`regs`,APPLY_UPDATE_THM] >>
       full_simp_tac(srw_ss())[find_code_def,DOMSUB_FLOOKUP_THM] >>
       full_simp_tac(srw_ss())[FLOOKUP_DEF] >>
       full_simp_tac(srw_ss())[state_rel_def,FLOOKUP_DEF] >>
       every_case_tac >> full_simp_tac(srw_ss())[]) >>
      simp[upd_pc_def,dec_clock_def,Abbr`a1`] >> NO_TAC) >>
  simp[Once labSemTheory.evaluate_def,asm_fetch_def,get_pc_value_def,
       inc_pc_def,dec_clock_def,upd_reg_def,lab_to_loc_def] >>
  map_every qexists_tac[`ck+ck'+1`,`t2'`] >> simp[] >>
  qpat_abbrev_tac`ss:('a,'c,'ffi)labSem$state = _ _` >>
  first_x_assum(qspec_then`ss`mp_tac) >>
  (impl_tac >- (
     simp[Abbr`ss`] >>
     srw_tac[][] >> full_simp_tac(srw_ss())[Abbr`regs`,APPLY_UPDATE_THM]
       >>
     full_simp_tac(srw_ss())[find_code_def,DOMSUB_FLOOKUP_THM] >>
     full_simp_tac(srw_ss())[FLOOKUP_DEF] >>
     full_simp_tac(srw_ss())[state_rel_def,FLOOKUP_DEF] >>
     every_case_tac >> full_simp_tac(srw_ss())[])) >>
  simp[upd_pc_def,dec_clock_def,Abbr`ss`] >>
  first_x_assum(qspec_then`ck'`mp_tac) \\ simp[] >>
  first_x_assum(qspec_then`ck'`mp_tac) \\ simp[];
*)

(* Proving that stack_to_lab generates labels_ok *)
(* HOL4 ML code, not ported:
val sextract_labels_def = stackPropsTheory.extract_labels_def
*)

let halt_assum_def = cake_define
  `halt_assum (:'ffi#'c) code <=>
    (!(s:('ga,'c,'ffi)stackSem_state).
      subspt code (state_code s) /\ ~(state_clock s = 0) ==>
      (?t. evaluate (Call NONE (INL 1) NONE,s) = (SOME (Halt (Word
        (n2w 0))),t) /\ state_ffi
          t = state_ffi s /\ state_clock t = state_clock s - 1))`;;

let make_init_def = cake_define
  `stack_to_labProof_make_init code coracle regs' save_regs
  (s:('a,'c,'ffi)labSem_state) =
     (mk_stackSem_state (FEMPTY |++ (MAP (\r. r,(\r s. regs s r) r
       s) regs')) FEMPTY ARB ARB ARB (mem s) (mem_domain s)
       (labSem_state_shared_mem_domain s) ARB (\c p. compile s c (MAP
       prog_to_section p)) coracle (state_code_buffer s) ARB ARB F F
       F (state_clock s) code (state_ffi s) save_regs (be
       s):('ga,'c,'ffi)stackSem_state)`;;
hol4_overload "make_init" "stack_to_labProof_make_init";;

(* HOL4 ML code, not ported:
val make_init_semantics = flatten_semantics
  |> Q.INST [`s1`|->`make_init code coracle regs save_regs
    (s:('a,'c,'ffi)labSem$state)`,`s2`|->`s`]
  |> SIMP_RULE std_ss [EVAL ``(make_init code coracle regs save_regs
    s).code``];
*)

(* HOL4 overload (expanded in the port):
     stack_to_lab_compile = stack_to_lab$compile *)
(* HOL4 overload (expanded in the port):
     stack_names_compile = stack_names$compile *)
(* HOL4 overload (expanded in the port):
     stack_alloc_compile = stack_alloc$compile *)
(* HOL4 overload (expanded in the port):
     stack_remove_compile = stack_remove$compile *)

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
       (\r s. regs s r) (tlookup rnames 2) t = Word ptr2 /\
       (\r s. regs s r) (tlookup rnames 3) t = Word ptr3 /\
       (\r s. regs s r) (tlookup rnames 4) t = Word ptr4 /\ mem
       t ptr2 = Word bitmap_ptr /\ mem
       t (ptr2 + bytes_in_word) =
           Word (bitmap_ptr + bytes_in_word * n2w (LENGTH bitmaps))
             /\ mem
       t (ptr2 + (n2w 2) * bytes_in_word) =
           Word (bitmap_ptr + bytes_in_word * n2w data_sp +
                 bytes_in_word * n2w (LENGTH bitmaps)) /\ mem
       t (ptr2 + (n2w 3) * bytes_in_word) = Word (buffer_position
         (state_code_buffer t)) /\ mem
       t (ptr2 + (n2w 4) * bytes_in_word) =
           Word (buffer_position (state_code_buffer t) + n2w
             (buffer_space_left (state_code_buffer t))) /\ buffer_buffer
             (state_code_buffer
       t) = [] /\
       ptr2 <=+ ptr4 /\ byte_aligned ptr2 /\
       byte_aligned ptr4 /\ byte_aligned bitmap_ptr /\
       (n2w 1024) * bytes_in_word <=+ ptr4 - ptr2 /\
      (word_list bitmap_ptr (MAP Word bitmaps) *
       word_list_exists (bitmap_ptr + bytes_in_word * n2w (LENGTH
         bitmaps)) data_sp *
       word_list_exists ptr2
         (w2n (--(n2w 1) * ptr2 + ptr4) DIV w2n (bytes_in_word:'a
           word)))
        (fun2set (mem t,mem_domain t)))`;;

(* HOL4 ML code, not ported:
val sextract_labels_def = stackPropsTheory.extract_labels_def
*)

(*
Theorem stack_to_lab_lab_pres:
    ∀p n nl.
  EVERY (λ(l1,l2). l1 = n ∧ l2 ≠ 0) (extract_labels p) ∧
  ALL_DISTINCT (extract_labels p) ∧
  next_lab p 1 ≤ nl ⇒
  let (cp,nr,nl') = flatten p n nl in
  EVERY (λ(l1,l2). l1 = n ∧ l2 ≠ 0) (extract_labels (append cp)) ∧
  ALL_DISTINCT (extract_labels (append cp)) ∧
  (∀lab. MEM lab (extract_labels (append cp)) ⇒ MEM lab (extract_labels
    p) ∨ (nl ≤ SND lab ∧ SND lab < nl')) ∧
  nl ≤ nl'
Proof
  HO_MATCH_MP_TAC flatten_ind>>Cases_on`p`>>rw[]>>
  once_rewrite_tac
    [flatten_def]>>fs[extract_labels_def,sextract_labels_def]
  >-
    (Cases_on`s`>>BasicProvers.EVERY_CASE_TAC>>fs[]>>rveq>>fs
      [extract_labels_def,sextract_labels_def,compile_jump_def]>>
    rpt(pairarg_tac>>fs[])>>rveq>>fs[extract_labels_def
      ,sextract_labels_def]>>
    qpat_x_assum`A<=nl` mp_tac>>
    simp[Once next_lab_thm]>>
    strip_tac>>
    TRY
      (fs[ALL_DISTINCT_APPEND,extract_labels_append]>>rw[]>>
      CCONTR_TAC>>fs[]>>res_tac>>fs[]>>NO_TAC)
    >>
    `1 ≤ nl` by metis_tac[LESS_EQ_TRANS,next_lab_non_zero]>>
    fs[extract_labels_append,ALL_DISTINCT_APPEND,extract_labels_def]>>
    `next_lab q 1 ≤ m'` by fs[]>>
    fs[]>>rfs[]>>
    `r < nl ∧ r' < nl` by
      fs[MAX_DEF]>>
    rw[]>>
    CCONTR_TAC>>fs[]>>
    res_tac>>fs[]>>
    imp_res_tac extract_labels_next_lab>>fs[]>>
    metis_tac[])
  >>
    (rpt(pairarg_tac>>fs[])>>rveq>>fs[extract_labels_def
      ,sextract_labels_def]>>
    qpat_x_assum`A<=nl` mp_tac>>
    simp[Once next_lab_thm]>>
    strip_tac>>
    `1 ≤ nl` by
      metis_tac[LESS_EQ_TRANS,next_lab_non_zero]>>
    fs[ALL_DISTINCT_APPEND]>>
    qpat_x_assum`A=(cp,_,nl')` mp_tac>>
    BasicProvers.EVERY_CASE_TAC>>strip_tac>>rveq>>fs[extract_labels_def
      ,extract_labels_append,ALL_DISTINCT_APPEND]>>
    TRY
      (rw[]>>
      CCONTR_TAC>>fs[]>>
      res_tac>>fs[]>>
      imp_res_tac extract_labels_next_lab>>fs[])>>
    metis_tac[])
QED
*)

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

(* HOL4 ML code, not ported:
val stack_asm_ok_def = stackPropsTheory.stack_asm_ok_def
*)

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
