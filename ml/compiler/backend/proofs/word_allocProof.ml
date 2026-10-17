(* ======================================================== *)
(*  word_allocProof: ported from HOL4's
    compiler/backend/proofs/word_allocProofScript.sml  *)
(* ======================================================== *)

(*
  Correctness proof for word_alloc
*)

needs "basis/pure/mllist.ml";;
needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/reg_alloc/linear_scan.ml";;
needs "compiler/backend/reg_alloc/proofs/linear_scanProof.ml";;
needs "compiler/backend/reg_alloc/proofs/reg_allocProof.ml";;
needs "compiler/backend/reg_alloc/reg_alloc.ml";;
needs "compiler/backend/semantics/wordConvs.ml";;
needs "compiler/backend/semantics/wordProps.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/backend/stackLang.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/backend/word_alloc.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "lib/sptree.ml";;
needs "semantics/ast.ml";;

(* Ensures we have the correct ML bindings *)
(* HOL4 ML code, not ported:
open reg_allocTheory reg_allocProofTheory linear_scanTheory
     linear_scanProofTheory wordLangTheory wordSemTheory wordPropsTheory
     wordConvsTheory word_allocTheory;
*)

(*TODO: Move?*)
(* TODO: can we have a global for this *)
let hide_def = cake_define
  `word_allocProof_hide x = x`;;
hol4_overload "hide" "word_allocProof_hide";;

(* word_alloc proofs
  1. correctness theorem about colouring_ok
  2. get_clash_sets (TODO: redundant)
  3. connect check_clash_tree to colouring_ok
  4. word_alloc_correct (connect 1 and 3)
  5. ssa_cc_trans correctness proof (including an invariant property),
    followed by full_ssa_cc_trans correctness
  6. ssa syntactic things (pre_alloc_conventions, wf_cutsets)
  7. word_alloc syntactic things
  8. misc
 *)

(* colouring_ok correctness proof *)
let colouring_ok_def = cake_define
  `colouring_ok f prog live lt =
        match prog with
          wordLang_Seq s1 s2 ->
       (let s2_live = get_live s2 live lt in
       let s1_live = get_live s1 s2_live lt in
         INJ f (domain s1_live) UNIV /\
         colouring_ok f s2 live lt /\ colouring_ok f s1 s2_live lt)
        | (If cmp r1 ri e2 e3) ->
       (let e2_live = get_live e2 live lt in
       let e3_live = get_live e3 live lt in
       let union_live = sptree_union e2_live e3_live in
       let merged = (match ri with Reg r2 -> sptree_insert r2 one
         (sptree_insert r1 one union_live) | _1 -> sptree_insert r1 one
         union_live) in
         INJ f (domain merged) UNIV /\
         colouring_ok f e2 live lt /\ colouring_ok f e3 live lt)
        | (Call (SOME (v,cutset,ret_handler,l1,l2)) dest args h) ->
       (let args_set = numset_list_insert args LN in
       let all_names' = sptree_union (SND cutset) (FST cutset) in
       INJ f (domain (sptree_union all_names' args_set)) UNIV /\
       INJ f (domain (numset_list_insert v all_names')) UNIV /\
       colouring_ok f ret_handler live lt /\
       (match h with NONE -> T | SOME (v,prog,l1,l2) ->
           INJ f (domain (sptree_insert v one all_names')) UNIV /\
           colouring_ok f prog live lt))
        | (wordLang_MustTerminate p) ->
       colouring_ok f p live lt
        | (Loop names body exit_names) ->
       (INJ f (domain names) UNIV /\
       INJ f (domain exit_names) UNIV /\
       colouring_ok f body names ((names,exit_names) :: lt))
        | prog ->
       (let lset = get_live prog live lt in
       let iset = sptree_union (get_writes prog) live in
         INJ f (domain lset) UNIV /\ INJ f (domain iset) UNIV)`;;

(*Equivalence on everything except permutation and locals*)
(* should we add local_size here? may be no, as locals are not included
   *)
(*TODO this definition is bad for automation remove it with
t = s with (...)*)
let word_state_eq_rel_def = cake_define
  `word_state_eq_rel (s:('a,'c,'ffi)wordSem_state)
  (t:('a,'c,'ffi)wordSem_state) <=> wordSem_state_fp_regs
   t = wordSem_state_fp_regs s /\ wordSem_state_store
   t = wordSem_state_store s /\ wordSem_state_locals_size
   t = wordSem_state_locals_size s /\ stack
   t = stack s /\ wordSem_state_stack_limit
   t = wordSem_state_stack_limit s /\ wordSem_state_stack_max
   t = wordSem_state_stack_max s /\ wordSem_state_stack_size
   t = wordSem_state_stack_size s /\ wordSem_state_memory
   t = wordSem_state_memory s /\ wordSem_state_mdomain
   t = wordSem_state_mdomain s /\ wordSem_state_sh_mdomain
   t = wordSem_state_sh_mdomain s /\ wordSem_state_gc_fun
   t = wordSem_state_gc_fun s /\ wordSem_state_handler
   t = wordSem_state_handler s /\ state_clock
   t = state_clock s /\ wordSem_state_code
   t = wordSem_state_code s /\ state_ffi
   t = state_ffi s /\ wordSem_state_be
   t = wordSem_state_be s /\ wordSem_state_termdep
   t = wordSem_state_termdep s /\ wordSem_state_compile
   t = wordSem_state_compile s /\ wordSem_state_compile_oracle
   t = wordSem_state_compile_oracle s /\ wordSem_state_code_buffer
   t = wordSem_state_code_buffer s /\ wordSem_state_data_buffer
   t = wordSem_state_data_buffer s`;;


(*tlocs is a supermap of slocs under f for everything in a given
  live set*)

let strong_locals_rel_def = cake_define
  `strong_locals_rel f ls slocs tlocs <=>
   (!n v.
     n IN ls /\ sptree_lookup n slocs = SOME v ==>
     sptree_lookup (f n) tlocs = SOME v)`;;

(* HOL4 ML code, not ported:
val size_tac= (full_simp_tac(srw_ss())[prog_size_def]>>DECIDE_TAC);
*)

(*For any 2 lists that are permutations of each other,
  We can give a list_rearranger that permutes one to the other*)

(* HOL4 ML code, not ported:
val ALL_DISTINCT_FST = ALL_DISTINCT_MAP |> Q.ISPEC `FST`
*)

(*Main theorem for permute oracle usage!
  This shows that we can push locals that are exactly matching using
  any desired permutation
  and we can choose the final permutation to be anything we want
  (In Alloc we choose it to be cst.permute, in Call something
   given by the IH)
*)

(*Proves s_val_eq and some extra conditions on the resulting lists*)

(*TODO: Maybe move to props?
gc doesn't touch other components*)

(* Convenient rewrite for pop_env
  TODO: do we need more on lsz'?
*)

(*Less powerful form*)

(* HOL4 ML code, not ported:
val lookup_alist_insert = sptreeTheory.lookup_alist_insert |> INST_TYPE
  [alpha|->``:'a word_loc``]
*)

(*Main proof of liveness theorem starts here*)
(*
 (* rm later *)
Theorem stack_size_map_excp_const:
  stack_size (StackFrame lsz lmp excp :: st.stack) =
    stack_size (StackFrame lsz lmp' excp' :: st.stack)
Proof
  rw [stack_size_def]
QED
*)

(*Frequently used tactics*)
(* HOL4 ML code, not ported:
val exists_tac = qexists_tac`cst.permute`>>
    full_simp_tac(srw_ss())[evaluate_def,LET_THM,word_state_eq_rel_def
      ,get_live_def,colouring_ok_def];
*)

(* HOL4 ML code, not ported:
val exists_tac_2 =
    Cases_on`word_exp st e`>>full_simp_tac(srw_ss())[]>>
    imp_res_tac apply_colour_exp_lemma>>
    pop_assum (qspecl_then[`f`,`cst`] mp_tac)>>
    impl_tac
    >-
      metis_tac[SUBSET_OF_INSERT,domain_union,SUBSET_UNION
               ,strong_locals_rel_subset];
*)

(* HOL4 ML code, not ported:
val setup_tac = Cases_on`word_exp st expr`>>full_simp_tac(srw_ss())[]>>
      imp_res_tac apply_colour_exp_lemma>>
      pop_assum(qspecl_then[`f`,`cst`]mp_tac)>>unabbrev_all_tac;
*)

(*liveness theorem*)

(* HOL4 ML code, not ported:
Resume evaluate_apply_colour[Skip]:
  full_simp_tac(srw_ss()++LET_ss)[evaluate_def,get_live_def
    ,word_state_eq_rel_def]
QED
*)

(* HOL4 ML code, not ported:
Resume evaluate_apply_colour[Move]:
  gvs[evaluate_def,get_live_def,colouring_ok_def] >>
  full_simp_tac(srw_ss())[MAP_ZIP,get_writes_def,domain_union
    ,domain_numset_list_insert]>>
  Cases_on`ALL_DISTINCT (MAP FST l)`>>full_simp_tac(srw_ss())[]>>
  `ALL_DISTINCT (MAP f (MAP FST l))` by
  (match_mp_tac ALL_DISTINCT_MAP_INJ>>
  srw_tac[][]>>
  FULL_SIMP_TAC bool_ss [INJ_DEF]>>
  first_x_assum(qspecl_then[`x`,`y`] assume_tac)>>
  simp[])>>
  full_simp_tac(srw_ss())[MAP_MAP_o] >>
  Cases_on`get_vars (MAP SND l) st`>>full_simp_tac(srw_ss())[]>>
  `get_vars (MAP f (MAP SND l)) cst = SOME x` by
  (
  drule strong_locals_rel_get_vars>>
  disch_then (qspec_then `(MAP SND l)` mp_tac) >>
  simp[]) >>
  full_simp_tac(srw_ss())[MAP_MAP_o] >>
  fs[word_state_eq_rel_def] >>
  `LENGTH l = LENGTH x` by
  (imp_res_tac get_vars_length_lemma >>
  fs[LENGTH_MAP]) >>
  fs[strong_locals_rel_def,set_vars_def,lookup_alist_insert] >>
  rpt strip_tac >>
  Cases_on`ALOOKUP (ZIP (MAP FST l,x)) n'`>>full_simp_tac(srw_ss())[]
*)
  (*NONE:
  Therefore n is not in l but it is in live and so it is not deleted
  *)
(* HOL4 ML code, not ported:
  >-(
  `n' ∈ domain (FOLDR delete live (MAP FST l))` by
  (full_simp_tac(srw_ss())[domain_FOLDR_delete]>>
  full_simp_tac(srw_ss())[ALOOKUP_NONE]>>rev_full_simp_tac(srw_ss())
    [MAP_ZIP])>>
  EVERY_CASE_TAC>>full_simp_tac(srw_ss())[]>>
  imp_res_tac ALOOKUP_MEM>>
  pop_assum mp_tac>>
  full_simp_tac(srw_ss())[MEM_ZIP]>>strip_tac>>
  rev_full_simp_tac(srw_ss())[EL_MAP,ALOOKUP_NONE]>>
  rev_full_simp_tac(srw_ss())[MAP_ZIP]>>
  `n' = FST (EL n'' l)` by
  (FULL_SIMP_TAC bool_ss [INJ_DEF]>>
  first_assum(qspecl_then[`n'`,`FST (EL n'' l)`] mp_tac)>>
  impl_tac>-
    (srw_tac[][]>>DISJ1_TAC>>
    metis_tac[MEM_MAP,MEM_EL])>>
  metis_tac[])>> fs[] >>
  metis_tac[MEM_EL,MEM_MAP])
  >>
  drule_all_then assume_tac ALOOKUP_MEM >>
  `ALOOKUP (ZIP (MAP (f o FST) l ,x)) (f n') = SOME v` by
  (match_mp_tac ALOOKUP_ALL_DISTINCT_MEM>>
  pop_assum mp_tac>>
  full_simp_tac(srw_ss())[MAP_ZIP,MEM_ZIP
    ,LENGTH_MAP]>>strip_tac>>full_simp_tac(srw_ss())[]>>
  fs[EL_MAP] >> HINT_EXISTS_TAC>>full_simp_tac(srw_ss())[EL_MAP]) >>
  full_simp_tac(srw_ss())[]
QED
*)

(* HOL4 ML code, not ported:
Resume evaluate_apply_colour[Inst]:
  exists_tac>>
  Cases_on`i`>> (TRY (Cases_on`a`))>> (TRY(Cases_on`m`))>>
  full_simp_tac(srw_ss())[get_live_def,get_live_inst_def,inst_def
    ,assign_def,word_add_carry_def]
  >-
  (Cases_on`word_exp st (Const c)`>>
  fs[word_exp_def,set_var_def,domain_union,get_writes_def
    ,get_writes_inst_def]>>
  match_mp_tac strong_locals_rel_insert>>
  metis_tac[INSERT_SING_UNION])
  >-
  (Cases_on`r`>>full_simp_tac(srw_ss())[]>>
  qpat_abbrev_tac `expr = (Op b [Var n0;B])`>>
  setup_tac>>
  (impl_tac
  >-
    (full_simp_tac(srw_ss())[get_live_exp_def,domain_union
      ,big_union_def]>>
    `{n0} ⊆ (n0 INSERT domain live DELETE n)` by
      full_simp_tac(srw_ss())[SUBSET_DEF]>>
    TRY(`{n0} ∪ {n'} ⊆ (n0 INSERT n' INSERT domain live DELETE n)` by
      full_simp_tac(srw_ss())[SUBSET_DEF])>>
    metis_tac[strong_locals_rel_subset])
  >>
  fs[apply_colour_exp_def,word_state_eq_rel_def,set_var_def
    ,get_writes_def
    ,get_writes_inst_def,domain_union]>>
  strip_tac>> match_mp_tac strong_locals_rel_insert>>
  metis_tac[INSERT_SING_UNION,strong_locals_rel_subset
    ,SUBSET_OF_INSERT]))
  >-
  (qpat_abbrev_tac`expr = (Shift s (Var n0) B)`>>
  rename1 ‘Shift _ _ (case r of _ => _ | _ => _)’>>
  setup_tac>>
  impl_tac>-
   (Cases_on ‘r’>>
    irule strong_locals_rel_subset>>
    first_assum $ irule_at (Pos last)>>
    full_simp_tac(srw_ss())[get_live_exp_def,big_union_def
      ,domain_union]) >>
  Cases_on ‘r’>>
  pairarg_tac>>
  fs[word_exp_def,word_state_eq_rel_def,set_var_def]>> strip_tac>>
  match_mp_tac strong_locals_rel_insert>>
  fs[domain_union,get_writes_def,get_writes_inst_def]>>
  metis_tac[INSERT_SING_UNION,strong_locals_rel_subset
    ,SUBSET_OF_INSERT])
  >>
  TRY (
  fs[]>>
  qmatch_goalsub_abbrev_tac `get_vars ls st`>>
  Cases_on`get_vars ls st`>>fs[Abbr`ls`]>>
  imp_res_tac strong_locals_rel_get_vars>>fs[]>>
  pop_assum kall_tac>> pop_assum mp_tac>>
  impl_tac>-
    metis_tac[]>>
  fs[]>>
  qmatch_asmsub_abbrev_tac `INJ f (domain A)`>>
  `!n n'. n ∈ domain A ∧
          n' ∈ domain A ∧ n ≠ n' ⇒ f n ≠ f n'` by
    (fs[get_writes_def,get_writes_inst_def,Abbr`A`]>>
    qpat_x_assum`INJ f A B` mp_tac>>
    rpt (pop_assum kall_tac)>>rw[]>>
    FULL_SIMP_TAC bool_ss
      [INJ_DEF,domain_union,get_writes_def,get_writes_inst_def
      ,domain_insert,IN_UNION]>>
    metis_tac[IN_INSERT])>>
  fs[get_writes_def,get_writes_inst_def,Abbr`A`,domain_union]>>
  every_case_tac>>fs[set_var_def,strong_locals_rel_def,lookup_insert]>>
  rw[]>>
  pop_assum mp_tac>>
  rpt IF_CASES_TAC>>fs[]>>
  metis_tac[])
  >-
  (qpat_abbrev_tac`expr=((Op Add [Var n';A]))`>>
  setup_tac>>
  impl_tac>-
    (full_simp_tac(srw_ss())[get_live_exp_def,big_union_def]>>
    `{n'} ⊆ n' INSERT domain live DELETE n` by
      full_simp_tac(srw_ss())[SUBSET_DEF]>>
    metis_tac[strong_locals_rel_subset])>>
  full_simp_tac(srw_ss())[word_state_eq_rel_def,LET_THM,set_var_def]>>
  Cases_on`x`>>simp[]>>
  fs[mem_load_def]>>
  IF_CASES_TAC>>fs[]>>
  fs[domain_union,get_writes_def,get_writes_inst_def]>>
  metis_tac[INSERT_SING_UNION,strong_locals_rel_subset,SUBSET_OF_INSERT
    ,strong_locals_rel_insert])
  >-
  (qpat_abbrev_tac`expr=((Op Add [Var n';A]))`>>
  setup_tac>>
  impl_tac>-
    (full_simp_tac(srw_ss())[get_live_exp_def,big_union_def]>>
    `{n'} ⊆ n' INSERT domain live DELETE n` by
      full_simp_tac(srw_ss())[SUBSET_DEF]>>
    metis_tac[strong_locals_rel_subset])>>
  full_simp_tac(srw_ss())[word_state_eq_rel_def,LET_THM,set_var_def]>>
  Cases_on`x`>>simp[]>>
  fs[mem_load_byte_aux_def]>>
  Cases_on`st.memory (byte_align c')`>>fs[]>>
  IF_CASES_TAC>>
  fs[domain_union,get_writes_def,get_writes_inst_def]>>
  metis_tac[INSERT_SING_UNION,strong_locals_rel_subset,SUBSET_OF_INSERT
    ,strong_locals_rel_insert])
  >-
  (qpat_abbrev_tac`expr=((Op Add [Var n';A]))`>>
  setup_tac>>
  impl_tac>-
    (full_simp_tac(srw_ss())[get_live_exp_def,big_union_def]>>
    `{n'} ⊆ n' INSERT domain live DELETE n` by
      full_simp_tac(srw_ss())[SUBSET_DEF]>>
    metis_tac[strong_locals_rel_subset])>>
  full_simp_tac(srw_ss())[word_state_eq_rel_def,LET_THM,set_var_def]>>
  Cases_on`x`>>simp[]>>
  fs[mem_load_32_alt]>>
  Cases_on`st.memory (byte_align c')`>>fs[]>>
  ntac 2 (IF_CASES_TAC>>fs[]) >> gvs[] >>
  fs[domain_union,get_writes_def,get_writes_inst_def]>>
  metis_tac[INSERT_SING_UNION,strong_locals_rel_subset,SUBSET_OF_INSERT
    ,strong_locals_rel_insert])
  >-
  (qpat_abbrev_tac`expr=Op Add [Var n';A]`>>
  setup_tac>>
  impl_tac>-
    (full_simp_tac(srw_ss())[get_live_exp_def,big_union_def]>>
    `{n'} ⊆ n' INSERT n INSERT domain live` by
      full_simp_tac(srw_ss())[SUBSET_DEF]>>
    metis_tac[strong_locals_rel_subset])>>
  full_simp_tac(srw_ss())[word_state_eq_rel_def,LET_THM,set_var_def]>>
  Cases_on`x`>>simp[]>>
  srw_tac[][]>>
  Cases_on`get_var n st`>>full_simp_tac(srw_ss())[]>>
  imp_res_tac strong_locals_rel_get_var>>
  Cases_on`mem_store c x' st`>>fs[mem_store_def]>>IF_CASES_TAC>>fs[]>>
  metis_tac[strong_locals_rel_subset,SUBSET_OF_INSERT])
  >-
  (qpat_abbrev_tac`expr=Op Add [Var n';A]`>>
  setup_tac>>
  impl_tac>-
    (full_simp_tac(srw_ss())[get_live_exp_def,big_union_def]>>
    `{n'} ⊆ n' INSERT n INSERT domain live` by
      full_simp_tac(srw_ss())[SUBSET_DEF]>>
    metis_tac[strong_locals_rel_subset])>>
  full_simp_tac(srw_ss())[word_state_eq_rel_def,LET_THM,set_var_def]>>
  Cases_on`x`>>simp[]>>
  srw_tac[][]>>
  Cases_on`get_var n st`>>full_simp_tac(srw_ss())[]>>
  imp_res_tac strong_locals_rel_get_var>>
  fs[]>>
  Cases_on`x`>>fs[]>>
  FULL_CASE_TAC>>fs[strong_locals_rel_def])
  >-
  (qpat_abbrev_tac`expr=Op Add [Var n';A]`>>
  setup_tac>>
  impl_tac>-
    (full_simp_tac(srw_ss())[get_live_exp_def,big_union_def]>>
    `{n'} ⊆ n' INSERT n INSERT domain live` by
      full_simp_tac(srw_ss())[SUBSET_DEF]>>
    metis_tac[strong_locals_rel_subset])>>
  full_simp_tac(srw_ss())[word_state_eq_rel_def,LET_THM,set_var_def]>>
  Cases_on`x`>>simp[]>>
  srw_tac[][]>>
  Cases_on`get_var n st`>>full_simp_tac(srw_ss())[]>>
  imp_res_tac strong_locals_rel_get_var>>
  fs[]>>
  Cases_on`x`>>fs[]>>
  FULL_CASE_TAC>>fs[strong_locals_rel_def])
  >-
*)
  (* All the FP cases *)
(* HOL4 ML code, not ported:
  (Cases_on`f'`>>fs[get_fp_var_def]>>
  every_case_tac>>simp[set_var_def]>>
  imp_res_tac strong_locals_rel_get_var>>
  fs[get_live_inst_def,get_writes_inst_def,get_writes_def
    ,set_fp_var_def]>>
  fs[domain_union]>>
  rw[]>>
  TRY(
    rename1`INJ f ({n0;n} ∪ li) UNIV`>>
    match_mp_tac strong_locals_rel_insert>>
    CONJ_TAC>-
      (drule INJ_SUBSET>>
      disch_then match_mp_tac >>fs[])>>
    match_mp_tac strong_locals_rel_insert>>
    CONJ_TAC>-
      (drule INJ_SUBSET>>
      disch_then match_mp_tac >>fs[SUBSET_DEF]))>>
  metis_tac[strong_locals_rel_insert,SUBSET_OF_INSERT,INSERT_SING_UNION
    ,strong_locals_rel_subset,INJ_SUBSET]
  )
QED
*)

(* HOL4 ML code, not ported:
Resume evaluate_apply_colour[Assign]:
  exists_tac>>exists_tac_2>>  rpt strip_tac >>
  fs[word_state_eq_rel_def,set_var_def]>>
  fs[domain_union,get_writes_def,get_writes_inst_def,GSYM
    INSERT_SING_UNION]>>
  irule strong_locals_rel_insert >> fs[] >>
  metis_tac[INSERT_SING_UNION,strong_locals_rel_subset,SUBSET_OF_INSERT
           ,strong_locals_rel_insert,SUBSET_UNION]
QED
*)

(* HOL4 ML code, not ported:
Resume evaluate_apply_colour[Get]:
  exists_tac>>
  EVERY_CASE_TAC>>
  full_simp_tac(srw_ss())[colouring_ok_def,set_var_def,get_store_def
    ,get_live_def]>>
  gvs[] >> irule strong_locals_rel_insert >> fs[] >>
  fs[domain_union,get_writes_def,get_writes_inst_def,GSYM
    INSERT_SING_UNION]
QED
*)

(* HOL4 ML code, not ported:
Resume evaluate_apply_colour[Set]:
  exists_tac>>exists_tac_2>>
  srw_tac[][]>>
  rev_full_simp_tac(srw_ss())[set_store_def,word_state_eq_rel_def]>>
  metis_tac[SUBSET_OF_INSERT,strong_locals_rel_subset
           ,domain_union,SUBSET_UNION]
QED
*)

(* HOL4 ML code, not ported:
Resume evaluate_apply_colour[Store]:
  exists_tac>>exists_tac_2>>
  srw_tac[][]>>
  rev_full_simp_tac(srw_ss())[set_store_def,word_state_eq_rel_def]>>
  Cases_on`get_var n st`>>full_simp_tac(srw_ss())[]>>
  imp_res_tac strong_locals_rel_get_var>>
  full_simp_tac(srw_ss())[mem_store_def]>>
  EVERY_CASE_TAC>>full_simp_tac(srw_ss())[]>>
  metis_tac[SUBSET_OF_INSERT,strong_locals_rel_subset
           ,domain_union,SUBSET_UNION]
QED
*)

(* HOL4 ML code, not ported:
Resume evaluate_apply_colour[MustTerminate]:
  first_x_assum(qspec_then`p` assume_tac)>>
  full_simp_tac(srw_ss())[colouring_ok_def,evaluate_def,LET_THM
    ,word_state_eq_rel_def]>>
  IF_CASES_TAC>>simp[]>>
  first_x_assum(qspecl_then[
  `st with <|clock:=MustTerminate_limit (:α);termdep:=st.termdep-1|>`,
  `cst with <|clock:=MustTerminate_limit
    (:α);termdep:=st.termdep-1|>`,`f`,`live`,`lt`] mp_tac)>>
  impl_tac>- fs[get_live_def]>>
  strip_tac>>
  qexists_tac`perm'`>>simp[]>>
  pop_assum mp_tac >>
  ntac 2 (pairarg_tac>>full_simp_tac(srw_ss())[])>>
  IF_CASES_TAC >> fs[] >> IF_CASES_TAC >> fs[get_live_def] >>
  metis_tac[]
QED
*)

(* HOL4 ML code, not ported:
Resume evaluate_apply_colour[Call]:
  goalStack.print_tac"Slow evaluate_apply_colour Call proof" >>
  full_simp_tac(srw_ss())[o_UNCURRY_R, C_UNCURRY_L,
    S_UNCURRY_R,LET_FORALL_ELIM',
  o_THM, o_ABS_R, C_ABS_L, C_THM,S_ABS_R,FORALL_UNCURRY]>>
  fs [evaluate_def,LET_THM,colouring_ok_def,get_live_def]>>
  Cases_on`get_vars l st`>>full_simp_tac(srw_ss())[]>>
  Cases_on`bad_dest_args o1 l`>-
    full_simp_tac(srw_ss())[bad_dest_args_def]>>
  `¬bad_dest_args o1 (MAP f l)` by
    full_simp_tac(srw_ss())[bad_dest_args_def]>>
  `get_vars (MAP f l) cst = SOME x` by
  (imp_res_tac strong_locals_rel_get_vars>>
  first_x_assum irule >> simp[oneline get_live_def,
  TypeBase.case_rand_of ``:'a option``,
  TypeBase.case_rand_of ``:'a # 'b``] >>
  simp[domain_numset_list_insert,domain_union] >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  (rpt (TOP_CASE_TAC >> simp[]))) >> simp[] >>
  Cases_on`find_code o1 (add_ret_loc o' x) st.code st.stack_size`>>
  full_simp_tac(srw_ss())[]>>
  PairCases_on`x'`>>full_simp_tac(srw_ss())[]>>
  TOP_CASE_TAC
  >- ( (*Tail call*)
  full_simp_tac(srw_ss())[word_state_eq_rel_def]>>
  Cases_on`o0`>> fs []>>
  qexists_tac`cst.permute`>>full_simp_tac(srw_ss())[]>>
  Cases_on`st.clock=0`>-
    full_simp_tac(srw_ss())[call_env_def,flush_state_def]>>
  full_simp_tac(srw_ss())[]>>
  `call_env x'0 x'2 (dec_clock cst) =
   call_env x'0 x'2 (dec_clock(st with permute:= cst.permute))` by
    rev_full_simp_tac(srw_ss())[call_env_def,
      flush_state_def,dec_clock_def,state_component_equality]>>
  rfs [] >>EVERY_CASE_TAC>>
  fs [])
  >>
*)
  (*Returning calls*)
(* HOL4 ML code, not ported:
  simp[TypeBase.case_eq_of ``:'a # 'b``,PULL_EXISTS] >>
  `?n names ret_handler l1 l2. x' = (n,names,ret_handler,l1,l2)`
   by  (PairCases_on `x'` >> simp[]) >>
  pop_assum SUBST_ALL_TAC >> full_simp_tac(srw_ss())[get_live_def]>>
  qmatch_asmsub_abbrev_tac `add_ret_loc (SOME A)` >>
  qmatch_goalsub_abbrev_tac `add_ret_loc (SOME B)` >>
  `add_ret_loc (SOME B) x  = add_ret_loc (SOME A) x`
  by simp[Abbr`A`,Abbr`B`,add_ret_loc_def] >>
  fs[] >>
  MAP_EVERY Q.UNABBREV_TAC [`A`,`B`] >>
  `cst.code = st.code /\ cst.stack_size = st.stack_size` by
      full_simp_tac(srw_ss())[word_state_eq_rel_def] >>
  fs[] >>
  Cases_on`domain (FST names) = {} ∨ ¬ALL_DISTINCT
    n`>>full_simp_tac(srw_ss())[]>>
  `domain (FST (apply_nummaps_key f names)) <> ∅`
  by (PURE_REWRITE_TAC[nummaps_to_nummap,apply_nummap_key_domain] >>
  simp[]) >>
  `ALL_DISTINCT (MAP f n)` by (
  irule ALL_DISTINCT_MAP_INJ >>
  gvs[colouring_ok_def]>>
  qpat_x_assum`INJ _ _ _` mp_tac>>
  rpt (pop_assum kall_tac)>>
  simp[domain_numset_list_insert,domain_union]>>
  strip_tac>> dxrule INJ_less>>
  disch_then (qspec_then `set n` mp_tac)>>
  simp[INJ_DEF])>>
  simp[] >>
  full_simp_tac(srw_ss())[cut_envs_def] >>
  Cases_on `cut_names (FST names) st.locals` >>
    full_simp_tac(srw_ss())[] >>
  Cases_on `cut_names (SND names) st.locals` >>
    full_simp_tac(srw_ss())[] >>
  imp_res_tac cut_names_lemma >>
  pop_assum kall_tac >>
  pop_assum (qspecl_then [`cst.locals`,`f`] mp_tac)>>
  pop_assum (qspecl_then [`cst.locals`,`f`] mp_tac)>>
  impl_tac >-
  full_simp_tac(srw_ss())[strong_locals_rel_def,domain_union]>>
  impl_tac >-
  (full_simp_tac(srw_ss())[colouring_ok_def,LET_THM,domain_union]>>
  fs[AllCasePreds()] >>
  irule INJ_less >>
  qpat_x_assum `INJ f (domain _) _` kall_tac >>
  qpat_x_assum `INJ f (_ UNION _) _` (irule_at Any) >>
  SET_TAC[]) >>
  strip_tac >>
  impl_tac >-
  full_simp_tac(srw_ss())[strong_locals_rel_def,domain_union]>>
  impl_tac >-
  (full_simp_tac(srw_ss())[colouring_ok_def,LET_THM,domain_union]>>
  fs[AllCasePreds()] >>
  irule INJ_less >>
  qpat_x_assum `INJ f (domain _) _` kall_tac >>
  qpat_x_assum `INJ f (_ UNION _) _` (irule_at Any) >>
  SET_TAC[]) >>
  strip_tac >>
  simp[nummaps_to_nummap,Excl "apply_nummap_key_def"] >>
  `cst.clock = st.clock` by
  full_simp_tac(srw_ss())[word_state_eq_rel_def] >>
  POP_ASSUM SUBST_ALL_TAC >>
  Cases_on `st.clock = 0` >> simp[]
  >- (
  full_simp_tac(srw_ss())[call_env_def,
    flush_state_def,add_ret_loc_def,word_state_eq_rel_def] >>
  Cases_on `o0` >> fs [push_env_def, env_to_list_def, stack_size_def,
    stack_size_frame_def] >>
  PairCases_on `x'''` >> fs [] >>
  fs[push_env_def,env_to_list_def, stack_size_def,
    stack_size_frame_def]) >>
  qpat_abbrev_tac`f_o0=
  case o0 of NONE => NONE
  | SOME (v,prog,l1,l2) => SOME (f v,apply_colour f prog,l1,l2)`>>
  Q.ISPECL_THEN[
  `y'`,`y`,`x'`,`x''`,`dec_clock st`,
  `f`,`dec_clock cst `,`f_o0`,`o0`,`λn. cst.permute (n+1)`]
  mp_tac (GEN_ALL push_env_s_val_eq)  >>
  impl_tac >- (
  full_simp_tac(srw_ss())[word_state_eq_rel_def] >>
  rev_full_simp_tac(srw_ss())[LET_THM,Abbr`f_o0`]>>
  EVERY_CASE_TAC>>full_simp_tac(srw_ss())[])>>
  strip_tac >>
  qmatch_asmsub_abbrev_tac `s_val_eq st'.stack cst'.stack` >>
  qabbrev_tac `st'' = call_env x'0 x'2  st'` >>
  qabbrev_tac `cst'' = call_env x'0 x'2  cst'` >>
  `cst'' = st'' with stack := cst''.stack`
  by (UNABBREV_ALL_TAC >>
  Cases_on `o0` >> TRY (PairCases_on `x'''`) >>
  simp[call_env_def,oneline push_env_def,ELIM_UNCURRY] >>
  simp[state_component_equality,dec_clock_def,stack_size_eq] >>
  fs[word_state_eq_rel_def] >>
  Cases_on `env_to_list y cst.permute` >>
  Cases_on `env_to_list x'' perm` >>
  fs[env_to_list_def]) >>
  pop_assum $ ASSUME_NAMED_TAC "stack_swap" >>
  `s_val_eq st''.stack cst''.stack`
  by simp[Abbr`st''`,Abbr`cst''`] >>
  qrefine `\n. if n = 0 then perm 0 else perm'' (n - 1)` >>
  `!perm''. push_env (x',x'') o0
                 (dec_clock
                    (st with
                     permute :=
                       (λn. if n = 0 then perm 0 else perm'' (n − 1))))
                         =
  st' with permute := perm''`
   by (namedCases_on `o0` ["","HAND"] >> TRY (PairCases_on `HAND`) >>
  simp[oneline push_env_def,Abbr`st'`,env_to_list_def,dec_clock_def,SF
    ETA_ss]) >>
  pop_assum (simp o single) >>
  qho_match_abbrev_tac `?perm''. P (evaluate (x'1,st'' with permute :=
    perm''))`>>
  ho_match_mp_tac permute_swap_lemma4 >>
  Q.UNABBREV_TAC `P` >>
  CONJ_TAC >- simp[] >>
  simp_tac(srw_ss())[] >>
  simp[PAIR_CASE_PAIR_MAP] >>
  namedCases_on `evaluate (x'1,st'')` ["res1 st1"] >>
  namedCases_on `res1` ["","res2"] >>
  TRY (Cases_on `res2`) >>
  asm_simp_tac(srw_ss())[]
*)
  (*Result*)
(* HOL4 ML code, not ported:
  >- (
  Q.SPECL_THEN [`x'1`,`st''`]  mp_tac evaluate_stack_swap >>
  simp[] >> disch_then strip_assume_tac >>
  first_x_assum (qspec_then `cst''.stack` mp_tac) >>
  LABEL_X_ASSUM  "stack_swap" (SUBST_ALL_TAC o GSYM) >>
  simp[] >> disch_then strip_assume_tac >> simp[] >>
  TOP_CASE_TAC >>
  MAP_EVERY Q.UNABBREV_TAC [`cst''`,`st''`,`cst'`,`st'`] >>
  full_simp_tac(srw_ss())[] >>
  `st''' = (st1 with stack := st''').stack` by simp[] >>
  pop_assum (RULE_ASSUM_TAC o SUBS o single) >>
  EVERY_ASSUM (TRY o (mp_then.mp_then (Pos hd) mp_tac
    push_env_pop_env_s_key_eq)) >>
  rw[]>>
  gvs[domain_union,s_val_eq_def,s_key_eq_def,s_frame_val_eq_def2
    ,s_frame_key_eq_def2]>>
  fs[domain_union,AC UNION_COMM UNION_ASSOC] >>
*)
  (*finally using IH*)
(* HOL4 ML code, not ported:
  first_x_assum irule >>
  CONJ_TAC >- (
    full_simp_tac(srw_ss())[word_state_eq_rel_def] >>
    gvs[AllCaseEqs(),pop_env_def])>>
  CONJ_TAC >- (
    drule_at (Pos (el 3)) pop_env_frame>>
    disch_then (drule_at (Pos (el 3)))>>
    impl_tac >- (
      fs[s_val_eq_def,s_frame_val_eq_def2]>>
      metis_tac[s_key_eq_trans,s_key_eq_sym,word_state_eq_rel_def])>>
    simp[word_state_eq_rel_def])>>
  gvs[colouring_ok_def,domain_numset_list_insert,domain_union]>>
  irule strong_locals_rel_set_vars_dom>>
  simp[]>>
  qpat_x_assum`INJ _ (_ ∪ _ ∪ set n) _` (irule_at Any)>>
  CONJ_TAC >-
    simp[SUBSET_DEF]>>
  CONJ_TAC >-(
    fs[domain_union,AC UNION_COMM UNION_ASSOC] >>
    simp[SUBSET_DEF])>>
*)
  (* Strong locals rel *)
(* HOL4 ML code, not ported:
  fs[domain_fromAList]>>
  pairarg_tac>>gvs[]>>
  pairarg_tac>>gvs[]>>
  imp_res_tac s_key_eq_push_env_imp_MAP_FST>>
  rfs[]>>
  ntac 2 (pop_assum kall_tac)>>
  rename1`strong_locals_rel _ _ (union (fromAList ll) _) (union
    (fromAList lll) _)`>>
  `MAP FST lll = MAP f (MAP FST ll)` by
    metis_tac[key_map_implies]>>
  rw[strong_locals_rel_def]>>
  rename1`lookup (f nn) _`>>
  qpat_x_assum` nn ∈ domain _` kall_tac>>
  fs[AC UNION_COMM UNION_ASSOC] >>
  fs[lookup_union,lookup_fromAList]>>
  `ALOOKUP ll nn = ALOOKUP lll (f nn)` by (
    simp[Once (GSYM ZIP_MAP_FST_SND_EQ)]>>
    simp[Once (GSYM ZIP_MAP_FST_SND_EQ), SimpRHS]>>
    irule ALOOKUP_key_remap_INJ>>
    CONJ_TAC >-
      metis_tac[LENGTH_MAP]>>
    irule INJ_less>>
    last_x_assum (irule_at Any)>>
    simp[SUBSET_DEF]>>
    gvs[AllCaseEqs()]>>
    drule ALOOKUP_MEM>>
    metis_tac[MEM_MAP,FST])>>
  fs[AllCaseEqs(),ALOOKUP_toAList]>>
  `~MEM nn (MAP FST ll)` by (
    fs[ALOOKUP_NONE]>>
    metis_tac[MEM_MAP])>>
  fs[strong_locals_rel_def]>>
  first_x_assum irule>>
  metis_tac[domain_lookup])
*)
  (*Exception*)
(* HOL4 ML code, not ported:
  >-(
  Q.SPECL_THEN [`x'1`,`st''`]  mp_tac evaluate_stack_swap >>
  simp[] >> disch_then strip_assume_tac >>
  first_x_assum (qspec_then `cst''.stack` mp_tac) >>
  LABEL_X_ASSUM  "stack_swap" (SUBST_ALL_TAC o GSYM) >>
  simp[] >> disch_then strip_assume_tac >> simp[] >>
  drule_all s_val_eq_LASTN_exists >>
  disch_then strip_assume_tac >> fs[] >>
  Cases_on `o0`
*)
  (*No handler*)
(* HOL4 ML code, not ported:
  >-
    (full_simp_tac(srw_ss())[Abbr`f_o0`]>>
    `e0=e0' /\ ls = ls'` by
    (unabbrev_all_tac>>
    full_simp_tac(srw_ss())[word_state_eq_rel_def,push_env_def
      ,env_to_list_def,LET_THM]>>
    Cases_on`st.handler < LENGTH st.stack` >> full_simp_tac(srw_ss())[]
    >-
      (imp_res_tac LASTN_TL>>
      rev_full_simp_tac(srw_ss())[]>>full_simp_tac(srw_ss())[])
    >>
      `st.handler = LENGTH st.stack` by DECIDE_TAC>>
      rpt (qpat_x_assum `LASTN A B = C` mp_tac)>-
      simp[LASTN_LENGTH_cond])>>
  rev_full_simp_tac(srw_ss())[]>>
  `lss = lss'` by
    (match_mp_tac LIST_EQ_MAP_PAIR>>full_simp_tac(srw_ss())[]>>
    qsuff_tac `e = e'`>-metis_tac[]>>
    unabbrev_all_tac>>
    full_simp_tac(srw_ss())[word_state_eq_rel_def,push_env_def,LET_THM
      ,env_to_list_def]>>
    `st.handler < LENGTH st.stack` by
      (CCONTR_TAC>>
      `st.handler = LENGTH st.stack` by DECIDE_TAC>>
      ntac 2 (qpat_x_assum`LASTN A B = C` mp_tac)>>
      simp[LASTN_LENGTH2])>>
    ntac 2 (qpat_x_assum`LASTN A B = C` mp_tac)>>
    full_simp_tac(srw_ss())[LASTN_TL])>>
  full_simp_tac(srw_ss())[word_state_eq_rel_def] >>
  metis_tac[s_val_and_key_eq,s_key_eq_sym,s_key_eq_trans]) >>
*)
  (*Handler*)
(* HOL4 ML code, not ported:
  `?n' h l1' l2'. x''' = (n',h,l1',l2')`
    by (PairCases_on `x'''` >> simp[]) >>
  POP_ASSUM SUBST_ALL_TAC >>
  full_simp_tac(srw_ss())[Abbr`f_o0`] >>
  IF_CASES_TAC >- simp[] >>
  simp[] >>
  unabbrev_all_tac>>
  full_simp_tac(srw_ss())[word_state_eq_rel_def,push_env_def,LET_THM
    ,env_to_list_def]>>
  rpt (qpat_x_assum `LASTN A B = C` mp_tac)>>
  simp[LASTN_LENGTH_cond]>>
  rpt strip_tac>>
  full_simp_tac(srw_ss())[domain_union,domain_fromAList]>>
  imp_res_tac list_rearrange_keys>>
  `set (MAP FST lss') = domain y` by
    (qpat_x_assum`A=MAP FST lss'` (SUBST1_TAC o SYM)>>
    full_simp_tac(srw_ss())[EXTENSION]>>srw_tac[][EXISTS_PROD]>>
    simp[MEM_MAP,sort_MEM]>>srw_tac[][EQ_IMP_THM]
    >-
      (Cases_on`y''`>>
      full_simp_tac(srw_ss())[MEM_toAList]>>
      imp_res_tac domain_lookup>>
      metis_tac[])
    >>
      full_simp_tac(srw_ss())[EXISTS_PROD,MEM_toAList]>>
      metis_tac[domain_lookup])>>
  `domain (SND names) = set (MAP FST lss)` by
    (qpat_x_assum `A = MAP FST lss` (SUBST1_TAC o SYM)>>
      full_simp_tac(srw_ss())[EXTENSION,MEM_MAP,sort_MEM,MEM_toAList
        ,EXISTS_PROD,domain_lookup])>>
  `set (MAP FST e0) = domain x'` by
    (full_simp_tac(srw_ss())[EXTENSION]>>srw_tac[][EXISTS_PROD]>>
    simp[MEM_MAP,sort_MEM]>>srw_tac[][EQ_IMP_THM]
    >-
      (Cases_on`y''`>>
      full_simp_tac(srw_ss())[MEM_toAList]>>
      imp_res_tac domain_lookup>>
      metis_tac[])
    >>
      full_simp_tac(srw_ss())[EXISTS_PROD,MEM_toAList]>>
      metis_tac[domain_lookup])>>
  `domain (FST names) = set (MAP FST e0)` by
     (full_simp_tac(srw_ss())[EXTENSION,MEM_MAP,sort_MEM,MEM_toAList
        ,EXISTS_PROD,domain_lookup])>>
  `set (MAP FST e0') = IMAGE f (domain x')` by
    (full_simp_tac(srw_ss())[EXTENSION]>>srw_tac[][EXISTS_PROD]>>
    simp[MEM_MAP,sort_MEM]>>srw_tac[][EQ_IMP_THM]
    >-
      (Cases_on`y''`>>
      full_simp_tac(srw_ss())[MEM_toAList]>>
      imp_res_tac domain_lookup>>
      metis_tac[])
    >>
      full_simp_tac(srw_ss())[EXISTS_PROD,MEM_toAList]>>
      metis_tac[domain_lookup])>>
  fs[domain_union,AC UNION_COMM UNION_ASSOC] >>
*)
  (*Use IH*)
(* HOL4 ML code, not ported:
  first_x_assum irule >>
  fs[colouring_ok_def]>>
  CONJ_TAC >-
    metis_tac[s_val_and_key_eq,s_key_eq_sym,s_key_eq_trans]>>
  irule strong_locals_rel_set_var_dom>>
  qpat_assum`INJ _ (_ INSERT _) _` (irule_at Any)>>
  simp[]>>
  CONJ_TAC >-(
    fs[domain_union,AC UNION_COMM UNION_ASSOC,domain_fromAList] >>
    simp[SUBSET_DEF])>>
*)
  (* Strong locals rel *)
(* HOL4 ML code, not ported:
  fs[domain_fromAList]>>
  rename1`strong_locals_rel _ _ (union (fromAList ll) _) (union
    (fromAList lll) _)`>>
  `MAP FST lll = MAP f (MAP FST ll)` by
    metis_tac[key_map_implies]>>
  rw[strong_locals_rel_def]>>
  rename1`lookup (f nn) _`>>
  qpat_x_assum` nn ∈ domain _` kall_tac>>
  fs[AC UNION_COMM UNION_ASSOC] >>
  fs[lookup_union,lookup_fromAList]>>
  `ALOOKUP ll nn = ALOOKUP lll (f nn)` by (
    simp[Once (GSYM ZIP_MAP_FST_SND_EQ)]>>
    simp[Once (GSYM ZIP_MAP_FST_SND_EQ), SimpRHS]>>
    irule ALOOKUP_key_remap_INJ>>
    CONJ_TAC >-
      metis_tac[LENGTH_MAP]>>
    irule INJ_less>>
    qpat_assum`INJ _ (_ INSERT _) _` (irule_at Any)>>
    simp[SUBSET_DEF]>>
    gvs[AllCaseEqs()]>>
    drule ALOOKUP_MEM>>
    simp[domain_union]>>
    metis_tac[MEM_MAP,FST])>>
  fs[AllCaseEqs(),ALOOKUP_toAList]>>
  `~MEM nn (MAP FST ll)` by (
    fs[ALOOKUP_NONE]>>
    metis_tac[MEM_MAP])>>
  fs[strong_locals_rel_def]>>
  first_x_assum irule>>
  metis_tac[domain_lookup])
*)
  (*Remaining Cases*)
(* HOL4 ML code, not ported:
  >>(
  Q.SPECL_THEN [`x'1`,`st''`]  mp_tac evaluate_stack_swap >>
  simp[] >> disch_then strip_assume_tac >>
  first_x_assum (qspec_then `cst''.stack` mp_tac) >>
  LABEL_X_ASSUM  "stack_swap" (SUBST_ALL_TAC o GSYM) >>
  simp[] >> disch_then strip_assume_tac >> simp[] >>
  Q.EXISTS_TAC `st1.permute` >>
  simp[word_state_eq_rel_def])
QED
*)

(* HOL4 ML code, not ported:
Resume evaluate_apply_colour[Seq]:
  srw_tac[][]>>fs[evaluate_def,colouring_ok_def,LET_THM,get_live_def]>>
  last_assum(qspecl_then[`p`,`st`,`cst`,`f`,`get_live p0 live lt`,`lt`]
    mp_tac)>>
  impl_tac>-size_tac>>
  srw_tac[][]>>
  Cases_on`evaluate(p,st with
    permute:=perm')`>>full_simp_tac(srw_ss())[]
  >- (qexists_tac`perm'`>>full_simp_tac(srw_ss())[]) >>
  Cases_on`evaluate(apply_colour f p,cst)`>>full_simp_tac(srw_ss())[]>>
  reverse (Cases_on`q`)>>full_simp_tac(srw_ss())[]
  >-
    (qexists_tac`perm'`>>srw_tac[][])
  >>
  first_assum(qspecl_then[`p0`,`r`,`r'`,`f`,`live`,`lt`] mp_tac)>>
  impl_tac>- size_tac>>
  srw_tac[][]>>
  Q.ISPECL_THEN[`p`,`st with permute:=perm'`,`perm''`]
    assume_tac permute_swap_lemma>>
  rev_full_simp_tac(srw_ss())[LET_THM]>>
  qexists_tac`perm'''`>>srw_tac[][]>>full_simp_tac(srw_ss())[]
QED
*)

(* HOL4 ML code, not ported:
Resume evaluate_apply_colour[If]:
  full_simp_tac(srw_ss())[evaluate_def,colouring_ok_def,LET_THM
    ,get_live_def]>>
  Cases_on`get_var n st`>>full_simp_tac(srw_ss())[]>>imp_res_tac
    strong_locals_rel_get_var>>
  pop_assum kall_tac>>pop_assum mp_tac>>impl_tac >-
    (FULL_CASE_TAC>>full_simp_tac(srw_ss())[])
  >>
  srw_tac[][]>>
  Cases_on`x`>>full_simp_tac(srw_ss())[]>>
  full_simp_tac(srw_ss())[]>>
  Cases_on`get_var_imm r st`>>full_simp_tac(srw_ss())[]>>
  imp_res_tac strong_locals_rel_get_var_imm>>
  pop_assum kall_tac>>pop_assum mp_tac>>impl_tac>-
    (Cases_on`r`>>full_simp_tac(srw_ss())[])>>
  Cases_on`x`>>srw_tac[][]>>full_simp_tac(srw_ss())[]
  >- (
    qmatch_goalsub_abbrev_tac `evaluate (w,st with permute := _)` >>
    first_assum(qspecl_then[`w`,`st`,`cst`,`f`,`live`,`lt`] mp_tac)>>
    impl_tac>- size_tac>>
    impl_tac>-
      (Cases_on`r`>>
      full_simp_tac(srw_ss())[domain_insert,domain_union]>>
      metis_tac[SUBSET_OF_INSERT,SUBSET_UNION
        ,strong_locals_rel_subset])>>
    srw_tac[][])
  >- (
    qmatch_goalsub_abbrev_tac `evaluate (w,st with permute := _)` >>
    first_assum(qspecl_then[`w`,`st`,`cst`,`f`,`live`,`lt`] mp_tac)>>
    impl_tac>- size_tac>>
    impl_tac>-
      (Cases_on`r`>>
      full_simp_tac(srw_ss())[domain_insert,domain_union]>>
      metis_tac[SUBSET_OF_INSERT,SUBSET_UNION
        ,strong_locals_rel_subset])>>
    srw_tac[][])
  >- simp [word_cmp_def]
  >- (TOP_CASE_TAC >> gvs [])
  >- (TOP_CASE_TAC >> gvs [])
  >- (
    Cases_on `c` >> simp [word_cmp_def] >>
    rpt (IF_CASES_TAC >> gvs []) >>
    pairarg_tac >> gvs [] >> (
      qmatch_goalsub_abbrev_tac `evaluate (w,_)` >>
      first_assum(qspecl_then[`w`,`st`,`cst`,`f`,`live`,`lt`] mp_tac)>>
      impl_tac>- size_tac>>
      impl_tac>-
        (Cases_on`r`>>
        full_simp_tac(srw_ss())[domain_insert,domain_union]>>
        metis_tac[SUBSET_OF_INSERT,SUBSET_UNION
          ,strong_locals_rel_subset])>>
      srw_tac[][]))
  >- simp [word_cmp_def]
QED
*)

(* HOL4 ML code, not ported:
Resume evaluate_apply_colour[Loop]:
  rename1`Loop names body exit_names`>>
  irule evaluate_apply_colour_Loop_helper>>
  first_assum (irule_at Any)>>
  first_assum (irule_at Any)>>
  first_assum (irule_at Any)>>
  rpt strip_tac>>
  first_x_assum irule>>
  simp[]
QED
*)

(* HOL4 ML code, not ported:
Resume evaluate_apply_colour[Alloc]:
  last_x_assum kall_tac>>
  fs[evaluate_def,colouring_ok_def,get_live_def,get_writes_def]>>
  Cases_on`get_var n st`>>fs[]>>
  drule strong_locals_rel_get_var>>
  disch_then (drule_at Any)>>
  simp[]>> strip_tac>>
  rename1`get_var _ _ = SOME x`>>
  Cases_on`x`>>fs[alloc_def]>>
  rename1`cut_envs p`>>
  Cases_on`cut_envs p st.locals`>>
  fs[]>>
  rename1`cut_envs p _ = SOME x`>>
  PairCases_on`p`>>
  PairCases_on`x`>>
  drule_at (Pos (el 3)) cut_envs_lemma>>
  disch_then (qspecl_then [`cst.locals`, `f`] mp_tac)>>
  impl_tac >- (
    gvs[domain_union]>>
    irule_at Any INJ_less>>
    last_assum (irule_at Any)>>
    irule_at Any INJ_less>>
    last_x_assum (irule_at Any)>>
    irule_at Any strong_locals_rel_subset>>
    last_assum (irule_at Any)>>
    irule_at Any strong_locals_rel_subset>>
    last_x_assum (irule_at Any)>>
    simp[SUBSET_DEF])>>
  rw[]>>simp[]>>
  fs[set_store_def]>>
  qpat_abbrev_tac`non = NONE`>>
  Q.ISPECL_THEN [`y1`,`y2`,`x0`,`x1`,`st with store:= st.store |+
    (AllocSize,Word c)`,
    `f`,`cst with store:= cst.store |+ (AllocSize,Word
      c)`,`non`,`non`,`cst.permute`] mp_tac (GEN_ALL
      push_env_s_val_eq)>>
  impl_tac >- (
    simp[Abbr`non`]>>
    fs[word_state_eq_rel_def])>>
  rw[]>>
  qexists_tac`perm`>>fs[Abbr`non`]>>
  qpat_abbrev_tac `st' = push_env (x0,x1) NONE A`>>
  qpat_abbrev_tac `cst' = push_env (y1,y2) NONE B`>>
  Cases_on`gc st'`>>full_simp_tac(srw_ss())[]>>
  rename1`gc st' = SOME x`>>
  Q.ISPECL_THEN [`st'`,`cst'`,`x`] mp_tac gc_s_val_eq_gen>>
  impl_keep_tac>- (
    unabbrev_all_tac>>
    full_simp_tac(srw_ss())[push_env_def,LET_THM,env_to_list_def
      ,word_state_eq_rel_def, stack_size_def, stack_size_frame_def]>>
    rev_full_simp_tac(srw_ss())[]) >>
  srw_tac[][]>>simp[]>>
  unabbrev_all_tac>>
  imp_res_tac gc_frame>>
  drule push_env_pop_env_s_key_eq>>
  strip_tac>>
  rename1`pop_env ctt = SOME cxx`>>
  simp[]>>
  rename1`pop_env tt`>>
  Cases_on`pop_env tt`>>fs[]>>
  rename1`pop_env tt = SOME xx`>>
  `strong_locals_rel f (domain live) xx.locals cxx.locals ∧
   word_state_eq_rel xx cxx` by (
    imp_res_tac gc_s_key_eq>>
    fs[push_env_def,env_to_list_def]>>
    ntac 2(pop_assum mp_tac>>simp[Once s_key_eq_sym])>>
    ntac 2 strip_tac>>
    rpt (qpat_x_assum `s_key_eq A B` mp_tac)>>
    qpat_abbrev_tac `lsA = list_rearrange (cst.permute 0)
      (sort key_val_compare ( (toAList y2)))`>>
    qpat_abbrev_tac `lsB = list_rearrange (perm 0)
      (sort key_val_compare ( (toAList x1)))`>>
    ntac 4 strip_tac>>
    Q.ISPECL_THEN [`tt.stack`,`cxx`,`ctt`,`NONE:(num#num#num) option`,
       `st.locals_size`, `(toAList y1)`,`lsA`,`cst.stack`] mp_tac
         (GEN_ALL s_key_eq_val_eq_pop_env)>>
    impl_tac
    >- (
      fs[word_state_eq_rel_def]>>
      metis_tac[s_key_eq_sym,s_val_eq_sym])>>
    Q.ISPECL_THEN [`ctt.stack`,`xx`,`tt`,`NONE:(num#num#num) option`
      ,`st.locals_size`,`toAList x0`, `lsB`,`st.stack`] mp_tac (GEN_ALL
        s_key_eq_val_eq_pop_env)>>
    impl_tac
    >- (
      fs[word_state_eq_rel_def]>>
      metis_tac[s_key_eq_sym,s_val_eq_sym])>>
    rw[]
    >-(
*)
      (* Strong locals rel *)
(* HOL4 ML code, not ported:
      fs[strong_locals_rel_def,lookup_union,lookup_fromAList]>>
      rw[]>>
      rename1`nn ∈ domain live`>>
      qpat_x_assum` nn ∈ domain live` kall_tac>>
      `MAP FST l = MAP f (MAP FST lsB)` by
        fs[s_key_eq_def,s_frame_key_eq_def,MAP_EQ_f,MAP_MAP_o,MAP_EQ_f
          ,FORALL_PROD]>>
      `LENGTH (MAP FST lsB) = LENGTH (MAP SND l)` by
        metis_tac[LENGTH_MAP]>>
      `nn ∈ domain (union p0 p1)` by (
        fs[AllCaseEqs()]>>drule ALOOKUP_MEM>>
        simp[MEM_toAList,domain_union]
        >- metis_tac[domain_lookup]>>
        strip_tac>> drule_at Any MEM_ZIP_weak>>
        simp[Abbr`lsB`,MAP_FST_list_rearrange_keys_SORT])>>
      `ALOOKUP (ZIP (MAP FST lsB,MAP SND l)) nn =
        ALOOKUP l (f nn)` by (
        simp[Once (GSYM ZIP_MAP_FST_SND_EQ), SimpRHS]>>
        irule ALOOKUP_key_remap_INJ>>
        simp[Abbr`lsB`,MAP_FST_list_rearrange_keys_SORT]>>
        irule INJ_less>>
        last_x_assum (irule_at Any)>>
        simp[domain_union,SUBSET_DEF])>>
      fs[AllCaseEqs(),ALOOKUP_toAList]>>
      `~MEM nn (MAP FST lsB)` by (
        fs[ALOOKUP_NONE]>>
        metis_tac[MEM_MAP])>>
      pop_assum mp_tac>>
      simp[Abbr`lsB`,MAP_FST_list_rearrange_keys_SORT]>>
      strip_tac>>
      first_x_assum irule>>
      fs[domain_union])>>
    fs[word_state_eq_rel_def,pop_env_def]>>
    rfs[state_component_equality]>>
    metis_tac[s_val_and_key_eq,s_key_eq_sym,s_val_eq_sym
      ,s_key_eq_trans])>>
  pop_assum mp_tac>>
  simp[Once word_state_eq_rel_def]>>
  strip_tac>>
  pairarg_tac>>simp[]>>
  pairarg_tac>>simp[]>>
  pop_assum mp_tac>>
  simp[AllCaseEqs()]>>
  strip_tac>>
  gvs[get_store_def,has_space_def,AllCaseEqs()]>>
  simp[word_state_eq_rel_def,flush_state_def]
QED
*)

(* HOL4 ML code, not ported:
Resume evaluate_apply_colour[StoreConsts]:
  exists_tac>>
  Cases_on`get_var n1 st`>>fs[]>>
  imp_res_tac strong_locals_rel_get_var>>
  simp[]>>
  TOP_CASE_TAC>> simp[]>>
  Cases_on`get_var n2 st`>>fs[]>>
  imp_res_tac strong_locals_rel_get_var>>
  simp[]>>
  TOP_CASE_TAC>> simp[]>>
  rw[]>>simp[set_var_def,unset_var_def]>>
  match_mp_tac strong_locals_rel_insert>>
  CONJ_TAC >-
    (match_mp_tac (GEN_ALL INJ_less)>>
    asm_exists_tac>>simp[domain_union,get_writes_def])>>
  match_mp_tac strong_locals_rel_insert>>
  CONJ_TAC >-
    (match_mp_tac (GEN_ALL INJ_less)>>
    asm_exists_tac>>
    simp[domain_union,get_writes_def]>>
    simp[SUBSET_DEF])>>
  fs[get_writes_def,domain_union]>>
  fs[strong_locals_rel_def]>>
  rw[lookup_delete]
  >- (
    qpat_x_assum `INJ _ _ _` mp_tac>>
    REWRITE_TAC [INJ_DEF]>>
    strip_tac>>
    first_x_assum(qspecl_then[`n`,`n'`] mp_tac)>>
    simp[])
  >>
    qpat_x_assum `INJ _ _ _` mp_tac>>
    REWRITE_TAC [INJ_DEF]>>
    strip_tac>>
    first_x_assum(qspecl_then[`n0`,`n'`] mp_tac)>>
    simp[]
QED
*)

(* HOL4 ML code, not ported:
Resume evaluate_apply_colour[Raise]:
  exists_tac>>
  Cases_on`get_var n st`>> fs[]>>
  imp_res_tac
    strong_locals_rel_get_var>>full_simp_tac(srw_ss())[jump_exc_def]>>
  EVERY_CASE_TAC>>full_simp_tac(srw_ss())[] >> gvs[]
QED
*)

(* HOL4 ML code, not ported:
Resume evaluate_apply_colour[Return]:
  exists_tac>>
  fs[get_writes_def] >>
  Cases_on`get_var n st`>>
  fs[]>>
  Cases_on `x` >> fs[] >>
  Cases_on`get_vars l st`>>
  fs[]>>
  imp_res_tac strong_locals_rel_get_var>>
  full_simp_tac(srw_ss())[call_env_def,flush_state_def]>>
  `get_vars (MAP f l) cst = SOME x` by
   (drule strong_locals_rel_get_vars >>
    disch_then (qspec_then `l` mp_tac) >>
    simp[domain_numset_list_insert]) >>
  full_simp_tac(srw_ss())[]
QED
*)

(* HOL4 ML code, not ported:
Resume evaluate_apply_colour[Break]:
  exists_tac>>
  TOP_CASE_TAC>>
  PairCases_on`x`>>fs[]
QED
*)

(* HOL4 ML code, not ported:
Resume evaluate_apply_colour[Continue]:
  exists_tac>>
  TOP_CASE_TAC>>
  PairCases_on`x`>>fs[]
QED
*)

(* HOL4 ML code, not ported:
Resume evaluate_apply_colour[Tick]:
  exists_tac>>IF_CASES_TAC>>full_simp_tac(srw_ss())[call_env_def,
    flush_state_def,dec_clock_def]
QED
*)

(* HOL4 ML code, not ported:
Resume evaluate_apply_colour[OpCurrHeap]:
  exists_tac>>
  full_simp_tac(srw_ss())[evaluate_def,LET_THM,word_state_eq_rel_def,
    get_live_def,colouring_ok_def,word_exp_def,the_words_def] >>
  Cases_on `get_var n0 st` >> fs[] >>
  imp_res_tac strong_locals_rel_get_var>>
  full_simp_tac(srw_ss())[call_env_def,flush_state_def]>>
  Cases_on `x` >> fs[] >>
  fs[get_store_def] >> fs[GSYM get_store_def] >>
  Cases_on ‘get_store CurrHeap st’ >> fs [] >> Cases_on ‘x’ >> fs []>>
  EVERY_CASE_TAC>>fs [set_var_def]>>
  match_mp_tac strong_locals_rel_insert >>
  fs [get_writes_def,domain_union] >>
  metis_tac[INSERT_SING_UNION,strong_locals_rel_subset,SUBSET_OF_INSERT
           ,strong_locals_rel_insert,SUBSET_UNION]
QED
*)

(* HOL4 ML code, not ported:
Resume evaluate_apply_colour[LocValue]:
  exists_tac>>fs[set_var_def,strong_locals_rel_def]>>rw[]>>
  fs[lookup_insert]>>
  Cases_on`n'=n`>>fs[]>>
  `f n ≠ f n'` by
  (fs[get_writes_def]>>
  FULL_SIMP_TAC bool_ss [INJ_DEF,domain_union,domain_insert]>>
  first_x_assum(qspecl_then[`n`,`n'`] assume_tac)>>
  ntac 4 (pop_assum mp_tac)>>
  rpt (pop_assum kall_tac)>>
  simp[])>>
  fs[]
QED
*)

(* HOL4 ML code, not ported:
Resume evaluate_apply_colour[Install]:
  exists_tac>>
  pairarg_tac>>fs[case_eq_thms]>>
  pop_assum mp_tac>>pairarg_tac>>strip_tac>>
  rfs[case_eq_thms]>>rw[]>>
  drule_at Any cut_env_lemma >>
  disch_then (qspecl_then [`cst.locals`,`f`] mp_tac)>>
  impl_tac >- (
    CONJ_TAC >- (
      irule (GEN_ALL INJ_less)>>
      last_x_assum (irule_at Any)>>
      simp[SUBSET_DEF,domain_list_insert,domain_union])>>
    fs[list_insert_def,strong_locals_rel_def,domain_union]>>
    metis_tac[])>>
  strip_tac>>fs[]>>
  imp_res_tac strong_locals_rel_get_var>>
  fs[list_insert_def]>>
  fs[strong_locals_rel_def,lookup_insert]>>rw[]
  >-
    (qpat_x_assum`INJ _ _ _` kall_tac>>
    qpat_x_assum`INJ _ _ _` mp_tac>>
    simp[get_writes_def,domain_union]>>
    SIMP_TAC bool_ss [INJ_DEF]>>
    strip_tac>>
    first_x_assum(qspecl_then [`n'`,`n`]
      assume_tac)>>full_simp_tac(srw_ss())[])
  >>
    first_x_assum irule>>
    fs[EXTENSION]>>
    metis_tac[domain_lookup]
QED
*)

(* HOL4 ML code, not ported:
Resume evaluate_apply_colour[CodeBufferWrite]:
  exists_tac>>pairarg_tac>>fs[case_eq_thms]>>
  imp_res_tac strong_locals_rel_get_var>>fs[list_insert_def]>>
  rw[]>>fs[]>>
  match_mp_tac (GEN_ALL strong_locals_rel_subset|>SIMP_RULE std_ss[Once
    CONJ_COMM])>>
  asm_exists_tac>>
  fs[SUBSET_DEF]
QED
*)

(* HOL4 ML code, not ported:
Resume evaluate_apply_colour[DataBufferWrite]:
  exists_tac>>pairarg_tac>>fs[case_eq_thms]>>
  imp_res_tac strong_locals_rel_get_var>>fs[list_insert_def]>>
  rw[]>>fs[]>>
  match_mp_tac (GEN_ALL strong_locals_rel_subset|>SIMP_RULE std_ss[Once
    CONJ_COMM])>>
  asm_exists_tac>>
  fs[SUBSET_DEF]
QED
*)

(* HOL4 ML code, not ported:
Resume evaluate_apply_colour[FFI]:
  exists_tac>>
  pairarg_tac>>pop_assum mp_tac>>
  gvs[]>>
  simp[Ntimes case_eq_thms 9]>>rw[]>>
  imp_res_tac strong_locals_rel_get_var>>
  simp[]>>
  drule_at Any cut_env_lemma >>
  disch_then (qspecl_then [`cst.locals`,`f`] mp_tac)>>
  impl_tac >- (
    CONJ_TAC >- (
      irule (GEN_ALL INJ_less)>>
      last_x_assum (irule_at Any)>>
      simp[domain_union,SUBSET_DEF])>>
    fs[strong_locals_rel_def,domain_union]>>
    metis_tac[])>>
  rw[]>>simp[]>>
  gvs[AllCaseEqs()]>>
  fs[strong_locals_rel_def]>>
  rw[]>>simp[call_env_def,flush_state_def]>>
  first_x_assum irule>>
  fs[EXTENSION]>>
  metis_tac[domain_lookup]
QED
*)

(* HOL4 ML code, not ported:
Resume evaluate_apply_colour[ShareInst]:
  exists_tac>>
  pairarg_tac>>
  gvs[AllCaseEqs()]>>
  drule apply_colour_exp_lemma >>
  disch_then $ qspecl_then [`cst`,`f`] mp_tac >>
  rename1`m = Store \/ m = Store8 \/ m = Store16 \/ m = Store32`>>
  qabbrev_tac `mcase = (m = Store \/ m = Store8 \/ m = Store16 \/ m =
    Store32)`>>
  qpat_x_assum `strong_locals_rel _ _ _ _` mp_tac >>
  IF_CASES_TAC >>
  fs[] >>
  disch_then assume_tac >>
  drule strong_locals_rel_get_var >>
  strip_tac >>
  impl_tac
  >- (
  fs[word_state_eq_rel_def] >>
  metis_tac[SUBSET_OF_INSERT,domain_union,SUBSET_UNION
     ,strong_locals_rel_subset])
  >- (
  strip_tac >>
  gvs[oneline share_inst_def,
    oneline sh_mem_store_def,
    oneline sh_mem_store_byte_def,
    oneline sh_mem_store32_def,
    oneline sh_mem_store16_def,
    flush_state_def,
    markerTheory.Abbrev_def,AllCaseEqs()] >>
  Cases_on `get_var n st` >> fs[] >>
  first_x_assum $ drule_at (Pos last) >>
  (impl_tac >- fs[domain_union,SUBSET_UNION]) >>
  gvs[] >>
  strip_tac >>
  EVERY_CASE_TAC >> gvs[] >>
  irule strong_locals_rel_subset >>
  first_assum $ irule_at (Pos last) >>
  simp[domain_union] >>
  metis_tac[SUBSET_OF_INSERT,SUBSET_TRANS,SUBSET_UNION])
  >- (
  fs[word_state_eq_rel_def] >>
  metis_tac[SUBSET_OF_INSERT,domain_union,SUBSET_UNION
     ,strong_locals_rel_subset])
  >- (
  strip_tac >>
  gvs[oneline share_inst_def,
    oneline sh_mem_load_def,
    oneline sh_mem_load_byte_def,
    oneline sh_mem_load32_def,
    oneline sh_mem_load16_def,
    oneline sh_mem_set_var_def,
    flush_state_def,set_var_def,
    markerTheory.Abbrev_def,AllCaseEqs()] >>
  irule strong_locals_rel_insert >>
  fs[domain_union] >>
  (conj_tac >- (
    drule_then irule INJ_SUBSET >>
    simp[get_writes_def])) >>
  drule_at_then (Pos last) irule strong_locals_rel_subset >>
  metis_tac[SUBSET_UNION])
QED
*)

(* HOL4 ML code, not ported:
Finalise evaluate_apply_colour;
*)

(* TODO: get_clash_sets, made redundant by clash tree *)

(*
(*Alternate liveness*)
Definition colouring_ok_alt_def:
  colouring_ok_alt f prog live =
    let (hd,ls) = get_clash_sets prog live in
    EVERY (λs. INJ f (domain s) UNIV) ls ∧
    INJ f (domain hd) UNIV
End

(*hd element is just get_live*)
Theorem get_clash_sets_hd[local]:
  ∀prog live hd ls.
  get_clash_sets prog live = (hd,ls) ⇒
  get_live prog live = hd
Proof
  Induct>>srw_tac[][get_clash_sets_def]>>full_simp_tac(srw_ss())
    [LET_THM]
  >-
    full_simp_tac(srw_ss())[get_live_def]
  >-
    (Cases_on`o'`>>full_simp_tac(srw_ss())[get_clash_sets_def,LET_THM]>>
    PairCases_on`x`>>full_simp_tac(srw_ss())[get_clash_sets_def
      ,get_live_def]>>
    full_simp_tac(srw_ss())[LET_THM,UNCURRY]>>
    EVERY_CASE_TAC>>full_simp_tac(srw_ss())[])
  >-
    (Cases_on`get_clash_sets prog' live`>>full_simp_tac(srw_ss())[]>>
    Cases_on`get_clash_sets prog q`>>full_simp_tac(srw_ss())[]>>
    metis_tac[get_live_def])
  >>
    Cases_on`get_clash_sets prog live`>>
    Cases_on`get_clash_sets prog' live`>>
    full_simp_tac(srw_ss())[get_live_def,LET_THM]>>metis_tac[]
QED

(*The liveset passed in at the back is always satisfied*)
Theorem get_clash_sets_tl[local]:
 ∀prog live f.
  let (hd,ls) = get_clash_sets prog live in
  EVERY (λs. INJ f (domain s) UNIV) ls ⇒
  INJ f (domain live) UNIV
Proof
  completeInduct_on`prog_size (K 0) prog`>>
  full_simp_tac(srw_ss())[PULL_FORALL]>>
  rpt strip_tac>>
  Cases_on`prog`>>
  full_simp_tac(srw_ss())[colouring_ok_alt_def,LET_THM
    ,get_clash_sets_def,get_live_def]>>
  full_simp_tac(srw_ss())[get_writes_def]
  >- metis_tac[INJ_UNION,domain_union,INJ_SUBSET,SUBSET_UNION]
  >- metis_tac[INJ_UNION,domain_union,INJ_SUBSET,SUBSET_UNION]
  >- metis_tac[INJ_UNION,domain_union,INJ_SUBSET,SUBSET_UNION]
  >- metis_tac[INJ_UNION,domain_union,INJ_SUBSET,SUBSET_UNION]
  >-
    (first_x_assum(qspecl_then[`p`,`live`,`f`]mp_tac)>>
    impl_tac>-size_tac>>srw_tac[][])
  >-
    (Cases_on`o'`>>full_simp_tac(srw_ss())[UNCURRY,get_clash_sets_def
      ,LET_THM]
    >- metis_tac[INJ_UNION,domain_union,INJ_SUBSET,SUBSET_UNION]
    >>
    PairCases_on`x`>>full_simp_tac(srw_ss())[]>>
    first_x_assum(qspecl_then[`x2`,`live`,`f`] mp_tac)>>
    impl_tac >- size_tac>>srw_tac[][]>>
    full_simp_tac(srw_ss())[get_clash_sets_def,UNCURRY,LET_THM]>>
    Cases_on`o0`>>TRY (PairCases_on`x`)>>full_simp_tac(srw_ss())[])
  >>
    TRY(first_x_assum(qspecl_then[`p0`,`live`,`f`]mp_tac)>>
    impl_tac>-size_tac>>srw_tac[][]>>
    full_simp_tac(srw_ss())[UNCURRY])
  >> metis_tac[INJ_UNION,domain_union,INJ_SUBSET,SUBSET_UNION]
QED

Theorem colouring_ok_alt_thm:
 ∀f prog live.
  colouring_ok_alt f prog live
  ⇒
  colouring_ok f prog live
Proof
  ho_match_mp_tac (fetch "-" "colouring_ok_ind")>>
  srw_tac[][]>>
  full_simp_tac(srw_ss())[get_clash_sets_def,colouring_ok_alt_def
    ,colouring_ok_def,LET_THM]
  >-
    (Cases_on`get_clash_sets prog' live`>>
    Cases_on`get_clash_sets prog q`>>full_simp_tac(srw_ss())[]>>
    imp_res_tac get_clash_sets_hd>>
    full_simp_tac(srw_ss())[]>>
    Q.ISPECL_THEN [`prog`,`q`,`f`] assume_tac get_clash_sets_tl>>
    rev_full_simp_tac(srw_ss())[LET_THM])
  >-
    (
    Cases_on`get_clash_sets prog live`>>
    Cases_on`get_clash_sets prog' live`>>
    FULL_CASE_TAC>>full_simp_tac(srw_ss())[]>>
    imp_res_tac get_clash_sets_hd>>
    full_simp_tac(srw_ss())[]>>
    metis_tac[INJ_SUBSET,SUBSET_DEF,SUBSET_OF_INSERT,domain_union
      ,SUBSET_UNION])
  >>
    Cases_on`h`>>full_simp_tac(srw_ss())[LET_THM]
    >-
      (Cases_on`get_clash_sets prog live`>>full_simp_tac(srw_ss())[])
    >>
    PairCases_on`x`>>full_simp_tac(srw_ss())[]>>
    Cases_on`get_clash_sets prog live`>>full_simp_tac(srw_ss())[]>>
    Cases_on`get_clash_sets x1 live`>>full_simp_tac(srw_ss())[]>>
    EVERY_CASE_TAC>>
    full_simp_tac(srw_ss())[LET_THM]>>
    Cases_on`get_clash_sets prog live`>>
    full_simp_tac(srw_ss())[UNCURRY]
QED

val fs1 = full_simp_tac(srw_ss())[LET_THM, get_clash_sets_def,
  every_var_def, get_live_def, domain_numset_list_insert,
  domain_union, EVERY_MEM, get_writes_def, every_var_inst_def,
  get_live_inst_def, every_name_def, toAList_domain];
*)

(*
(*Every variable is in some clash set*)
Theorem every_var_in_get_clash_set:
 ∀prog live.
  let (hd,clash_sets) = get_clash_sets prog live in
  let ls = hd::clash_sets in
  (∀x. x ∈ domain live ⇒ in_clash_sets ls x) ∧
  (every_var (in_clash_sets ls) prog)
Proof
  completeInduct_on`prog_size (K 0) prog`>>
  ntac 2 (full_simp_tac(srw_ss())[Once PULL_FORALL])>>
  rpt strip_tac>>
  Cases_on`prog`>>fs1>>
  TRY(rw[list_insert_def,EXISTS_OR_THM,RIGHT_AND_OVER_OR,domain_union]>>
    NO_TAC)
  >-
    (*Move*)
    (qpat_abbrev_tac`s1 = numset_list_insert A B`>>
    qpat_abbrev_tac`s2 = union A live`>>
    srw_tac[][]
    >-
      (qexists_tac`s2`>>full_simp_tac(srw_ss())[Abbr`s2`,domain_union])
    >-
      (qexists_tac`s2`>>full_simp_tac(srw_ss())[Abbr`s2`
        ,domain_numset_list_insert,domain_union])
    >>
      qexists_tac`s1`>>full_simp_tac(srw_ss())[Abbr`s1`
        ,domain_numset_list_insert,domain_union])
  >-
    (Cases_on`i`>>fs1>>full_simp_tac(srw_ss())[get_writes_inst_def]>>
    `∀P A B. P A ∨ P B ⇒ (?y:num_set. (y = A ∨ y = B) ∧ P y)` by
      metis_tac[]
    >-
      (srw_tac[][]>>
      first_x_assum ho_match_mp_tac>>fs[domain_union])
    >-
      (Cases_on`a`>>fs1>>full_simp_tac(srw_ss())[get_writes_inst_def]>>
      EVERY_CASE_TAC>>srw_tac[][]>>
      full_simp_tac(srw_ss())[every_var_imm_def,in_clash_sets_def]>>
      first_x_assum ho_match_mp_tac>> fs[domain_union])
    >-
      (Cases_on`m`>>Cases_on`a`>>fs1>>full_simp_tac(srw_ss())
        [get_writes_inst_def]>>srw_tac[][]>>
      first_x_assum ho_match_mp_tac>> fs[domain_union])
    >-
      (Cases_on`f`>>fs1>>fs[get_writes_inst_def]>>rw[]>>
      first_x_assum ho_match_mp_tac>> fs[domain_union]))
  >-
    (srw_tac[][]>>
    TRY(qexists_tac`union (insert n () LN)
      live`>>full_simp_tac(srw_ss())[domain_union])>>
    Q.ISPEC_THEN `e` assume_tac every_var_exp_get_live_exp>>
    match_mp_tac every_var_exp_mono>>
    HINT_EXISTS_TAC>>srw_tac[][in_clash_sets_def]>>
    Cases_on`x=n`
    >-
      (qexists_tac`union (insert n () LN)
        live`>>full_simp_tac(srw_ss())[domain_union])
    >>
      (qexists_tac`union (get_live_exp e) (delete n live)`>>
      full_simp_tac(srw_ss())[domain_union]))
  >-
    (srw_tac[][]>-(HINT_EXISTS_TAC>>full_simp_tac(srw_ss())[])>>
    Q.ISPEC_THEN `e` assume_tac every_var_exp_get_live_exp>>
    match_mp_tac every_var_exp_mono>>
    HINT_EXISTS_TAC>>srw_tac[][in_clash_sets_def]>>
    qexists_tac`union (get_live_exp e) live`>>
    full_simp_tac(srw_ss())[domain_union])
  >-
    (srw_tac[][]
    >-
      (HINT_EXISTS_TAC>>full_simp_tac(srw_ss())[])
    >-
      (qexists_tac `insert n () (union (get_live_exp e)
        live)`>>full_simp_tac(srw_ss())[])
    >>
    Q.ISPEC_THEN `e` assume_tac every_var_exp_get_live_exp>>
    match_mp_tac every_var_exp_mono>>
    HINT_EXISTS_TAC>>srw_tac[][in_clash_sets_def]>>
    qexists_tac`insert n () (union (get_live_exp e) live)`>>
    full_simp_tac(srw_ss())[domain_union])
  >-
    (first_x_assum(qspecl_then[`p`,`live`] mp_tac)>>impl_tac>-
    size_tac>>
    pairarg_tac>>simp[])
  >-
    (*Call*)
    (Cases_on`o'`>>fs1
    >-
      (srw_tac[][]>-(HINT_EXISTS_TAC>>full_simp_tac(srw_ss())[])>>
      qexists_tac`numset_list_insert l
        LN`>>full_simp_tac(srw_ss())[domain_numset_list_insert])
    >>
      PairCases_on`x`>>Cases_on`o0`>>fs1
      >-
        (first_x_assum(qspecl_then[`x2`,`live`] mp_tac)>>
        impl_tac>-
          (full_simp_tac(srw_ss())[prog_size_def]>>DECIDE_TAC)>>
        Cases_on`get_clash_sets x2 live`>>srw_tac[][]
        >-
          (first_x_assum(qspec_then`x'`assume_tac)>>rev_full_simp_tac
            (srw_ss())[]>>
          HINT_EXISTS_TAC>>full_simp_tac(srw_ss())[])
        >>
        TRY(full_simp_tac(srw_ss())[every_name_def,EVERY_MEM]>>
          full_simp_tac(srw_ss())[toAList_domain])>>
        qpat_abbrev_tac`A = union x1 X`>>
        qpat_abbrev_tac`Z = insert x0 () x1`>>
        TRY(qexists_tac`A`>>
          full_simp_tac(srw_ss())[Abbr`A`,domain_union
            ,domain_numset_list_insert]>>NO_TAC)>>
        TRY(qexists_tac`Z`>>full_simp_tac(srw_ss())[Abbr`Z`]) >>
        match_mp_tac every_var_mono>>
        HINT_EXISTS_TAC>>full_simp_tac(srw_ss())[]>>srw_tac[]
          [in_clash_sets_def]>>
        HINT_EXISTS_TAC>>full_simp_tac(srw_ss())[])
      >>
        PairCases_on`x`>>full_simp_tac(srw_ss())[]>>
        first_assum(qspecl_then[`x2`,`live`] mp_tac)>>
        impl_tac>-
          (full_simp_tac(srw_ss())[prog_size_def]>>DECIDE_TAC)>>
        first_x_assum(qspecl_then[`x1'`,`live`] mp_tac)>>
        impl_tac>-
          (full_simp_tac(srw_ss())[prog_size_def]>>DECIDE_TAC)>>
        Cases_on`get_clash_sets x2 live`>>
        Cases_on`get_clash_sets x1' live`>>srw_tac[][]
        >-
          (first_x_assum(qspec_then`x'`assume_tac)>>rev_full_simp_tac
            (srw_ss())[]>>
          HINT_EXISTS_TAC>>full_simp_tac(srw_ss())[])
        >>
        qpat_abbrev_tac`A = union x1 X`>>
        qpat_abbrev_tac`Z = insert x0 () x1`>>
        qpat_abbrev_tac`D = insert x0' () x1`>>
        TRY(qexists_tac`A`>>
          full_simp_tac(srw_ss())[Abbr`A`,domain_union
            ,domain_numset_list_insert]>>NO_TAC)>>
        TRY(qexists_tac`Z`>>full_simp_tac(srw_ss())[Abbr`Z`]>>NO_TAC) >>
        TRY(qexists_tac`D`>>full_simp_tac(srw_ss())[Abbr`D`]) >>
        match_mp_tac every_var_mono>>
        TRY(HINT_EXISTS_TAC)>>
        TRY(qexists_tac`in_clash_sets (q'::r')`)>>
        full_simp_tac(srw_ss())[]>>srw_tac[][in_clash_sets_def]>>
        HINT_EXISTS_TAC>>full_simp_tac(srw_ss())[])
  >-
    (first_assum(qspecl_then[`p0`,`live`] mp_tac)>>impl_tac
    >-
      (full_simp_tac(srw_ss())[prog_size_def]>>DECIDE_TAC)
    >>
    Cases_on`get_clash_sets p0 live`>>srw_tac[][]>>
    first_x_assum(qspecl_then[`p`,`q`] mp_tac)>>impl_tac
    >-
      (full_simp_tac(srw_ss())[prog_size_def]>>DECIDE_TAC)
    >>
    Cases_on`get_clash_sets p q`>>srw_tac[][]>>
    TRY (metis_tac[every_var_mono])>>
    match_mp_tac every_var_mono>>
    TRY(pop_assum kall_tac>>HINT_EXISTS_TAC)>>
    TRY HINT_EXISTS_TAC>>
    full_simp_tac(srw_ss())[in_clash_sets_def]>>
    metis_tac[])
  >-
    (first_assum(qspecl_then[`p0`,`live`] mp_tac)>>impl_tac
    >-
      (full_simp_tac(srw_ss())[prog_size_def]>>DECIDE_TAC)
    >>
    Cases_on`get_clash_sets p0 live`>>srw_tac[][]>>
    first_assum(qspecl_then[`p`,`live`] mp_tac)>>impl_tac
    >-
      (full_simp_tac(srw_ss())[prog_size_def]>>DECIDE_TAC)
    >>
    Cases_on`get_clash_sets p live`>>srw_tac[][]>>
    Cases_on`r`>>full_simp_tac(srw_ss())[every_var_imm_def]>>
    full_simp_tac(srw_ss())[in_clash_sets_def,domain_union]>>
    TRY(match_mp_tac
      every_var_mono>>full_simp_tac(srw_ss())[in_clash_sets_def]>>
      HINT_EXISTS_TAC>>srw_tac[][]>>full_simp_tac(srw_ss())
        [in_clash_sets_def])>>
    TRY( match_mp_tac
      every_var_mono>>full_simp_tac(srw_ss())[in_clash_sets_def]>>
    full_simp_tac(srw_ss())[CONJ_COMM]>>
    first_assum (match_exists_tac o
      concl)>>srw_tac[][]>>full_simp_tac(srw_ss())[in_clash_sets_def])>>
    res_tac>>
    TRY(qexists_tac`insert n' () (insert n () (union q' q))`>>
        full_simp_tac(srw_ss())[domain_union]>>metis_tac
          [domain_union])>>
    TRY(HINT_EXISTS_TAC>>metis_tac[domain_union])>>
    TRY(qexists_tac`insert n () (union q' q)`>>
        full_simp_tac(srw_ss())[domain_union]>>metis_tac[domain_union]))
QED

        full_simp_tac(srw_ss())[domain_union]>>metis_tac[domain_union]))
  >-
    (srw_tac[][]
    >-
      (HINT_EXISTS_TAC>>full_simp_tac(srw_ss())[])
    >>
      qexists_tac`insert n () s`>>full_simp_tac(srw_ss())[])
  >-
    (srw_tac[][]>-(HINT_EXISTS_TAC>>full_simp_tac(srw_ss())[])>>
    qexists_tac`insert n () live`>>full_simp_tac(srw_ss())[])
  >-
    (srw_tac[][]>-(HINT_EXISTS_TAC>>full_simp_tac(srw_ss())[])>>
    qexists_tac`insert n () (insert n0 ()
      live)`>>full_simp_tac(srw_ss())[])
  >-
    (rw[]>>
    (qexists_tac`union (insert n () LN) live`>>fs[domain_union]))
  >-
    (srw_tac[][]>-(HINT_EXISTS_TAC>>full_simp_tac(srw_ss())[])>>
     qexists_tac `insert n () (insert n0 () (insert n1 () (insert n2 ()
       s0)))` >> fs[])
    );
*)

(* Proofs for check_clash_tree *)

(*TODO: This is true without wf*)

(* HOL4 ML code, not ported:
val start_tac =
  FULL_CASE_TAC>>fs[]>>Cases_on`x`>>
  imp_res_tac check_partial_col_INJ>>
  rfs[numset_list_delete_swap,domain_numset_list_delete,AND_IMP_INTRO]>>
  TRY(pop_assum mp_tac>>
  impl_keep_tac)>>
  fs[domain_numset_list_delete,domain_numset_list_insert,hide_def]>>
  rfs[GSYM
    domain_numset_list_insert_eq_union,wf_numset_list_delete_eq]>>
  fs[domain_numset_list_delete,domain_numset_list_insert
    ,numset_list_delete_def,numset_list_insert_def];
*)

(* HOL4 ML code, not ported:
val subset_tac =
  match_mp_tac (GEN_ALL INJ_less)>>
  HINT_EXISTS_TAC>>fs[domain_numset_list_insert_eq_union,SUBSET_DEF]>>
  simp[domain_union];
*)

(* HOL4 ML code, not ported:
Resume clash_tree_colouring_ok[Loop]:
  fs[wf_cutsets_def]>>
  every_case_tac>>fs[]>>
  imp_res_tac check_col_INJ>>
  rveq>>
  last_x_assum $ drule_at (Pos last)>>
  simp[]>>
  strip_tac>>
  fs[hide_def,colouring_ok_def]
QED
*)

(* HOL4 ML code, not ported:
Resume clash_tree_colouring_ok[Break]:
  every_case_tac>>fs[check_clash_tree_def]>>
  imp_res_tac check_col_INJ>>
  rveq>>
  fs[hide_def,wf_def]>>
  fs[EVERY_EL,LLOOKUP_EQ_EL]>>
  first_x_assum drule>>
  pairarg_tac>>fs[]
QED
*)

(* HOL4 ML code, not ported:
Resume clash_tree_colouring_ok[Continue]:
  every_case_tac>>fs[check_clash_tree_def]>>
  imp_res_tac check_col_INJ>>
  rveq>>
  fs[hide_def,wf_def]>>
  fs[EVERY_EL,LLOOKUP_EQ_EL]>>
  first_x_assum drule>>
  pairarg_tac>>fs[]
QED
*)

(* HOL4 ML code, not ported:
Finalise clash_tree_colouring_ok;
*)

(*Actually, it should probably be exactly 0,2,4,6...*)
let even_starting_locals_def = cake_define
  `even_starting_locals (locs:('a word_loc) spt) <=>
     (!x. x IN domain locs ==> is_phy_var x)`;;

(* HOL4 ML code, not ported:
fun rm_let tm = tm|> SIMP_RULE std_ss [LET_THM];
*)

(*Prove the full correctness theorem for word_alloc*)

(* Dead code removal *)
let live_store_rel_def = cake_define
  `live_store_rel nlive sstore tstore <=>
   (!n. ~(
     n IN set_of_list nlive) ==>
     FLOOKUP sstore n = FLOOKUP tstore n)`;;

let nlive_store_def = cake_define
  `nlive_store nlive x2 =
        match x2 with
          wordLang_Op _3 ls ->
         EVERY (nlive_store nlive) ls
        | (wordLang_Lookup s) -> ~(
       s IN set_of_list nlive)
        | (Load e) ->
       nlive_store nlive e
        | (Shift _4 e1 e2) ->
       nlive_store nlive e1 /\ nlive_store nlive e2
        | _5 -> T`;;

(* HOL4 ML code, not ported:
Resume evaluate_remove_dead[Move]:
  gvs[evaluate_def,remove_dead_def,AllCaseEqs(),set_vars_def]
  >- (* empty filter case *)
    (fs[strong_locals_rel_def]>>
     imp_res_tac get_vars_length_lemma>>
     simp[lookup_alist_insert]>>
     ntac 2 strip_tac>>
     TOP_CASE_TAC>>simp[]>>
     rw[]>>
     `MEM n (MAP FST ls)` by
       (imp_res_tac ALOOKUP_MEM>>
        rfs[MEM_ZIP,MEM_EL]>>
        metis_tac[])>>
     fs[MEM_MAP,FILTER_EQ_NIL,EVERY_MEM]>>
     res_tac>>
     Cases_on`y`>>fs[domain_lookup])
  >> (* normal case *)
  qmatch_goalsub_abbrev_tac`ALL_DISTINCT Z`>>
  `ALL_DISTINCT Z` by
    (qpat_x_assum `ALL_DISTINCT (MAP FST ls)` mp_tac>>
     fs[Abbr`Z`]>>
     rpt (pop_assum kall_tac)>>
     Induct_on`ls`>>fs[FORALL_PROD]>>rw[]>>
     fs[MEM_MAP,FORALL_PROD,MEM_FILTER])>>
  simp[]>>
  qmatch_goalsub_abbrev_tac`get_vars A stt`>>
  imp_res_tac get_vars_exists>>
  `set A ⊆ domain stt.locals` by
    (unabbrev_all_tac>>
     fs[SUBSET_DEF,MEM_MAP,MEM_FILTER,EXISTS_PROD,strong_locals_rel_def
       ,domain_numset_list_insert]>>
     rw[]>>
     fs[domain_lookup]>>
     fs[SUBSET_DEF,domain_lookup]>>
     metis_tac[MEM_MAP,SND])>>
  imp_res_tac get_vars_eq>>fs[]>>
  unabbrev_all_tac>>fs[set_vars_def,state_component_equality]>>
  qpat_x_assum`A=vs` sym_sub_tac>>
  last_x_assum mp_tac>>
  qpat_x_assum`A ⊆ Z` mp_tac>>
  qpat_x_assum`A ⊆ Z` mp_tac>>
  qpat_x_assum`ALL_DISTINCT A` mp_tac>>
  qpat_x_assum`ALL_DISTINCT A` mp_tac>>
  rpt (pop_assum kall_tac)>>
  qid_spec_tac`live`>>
  Induct_on`ls`>>
  fs[numset_list_insert_def,FORALL_PROD,alist_insert_def]>>rw[]>>
  fs[alist_insert_def]
  >-
    (match_mp_tac strong_locals_rel_I_insert_insert>>rw[]
     >-
       (first_x_assum(qspec_then`delete p_1 live` mp_tac)>>
        fs[AND_IMP_INTRO]>>
        qpat_abbrev_tac`A = FILTER P ls`>>
        qpat_abbrev_tac`Z = FILTER P ls`>>
        `A=Z` by
          (fs[Abbr`A`,Abbr`Z`,lookup_delete]>>
           qpat_x_assum`¬(MEM p_1 (MAP FST ls))` mp_tac>>
           rpt (pop_assum kall_tac)>>
           Induct_on`ls`>>fs[FORALL_PROD])>>
        fs[]>>impl_tac>>
        fs[domain_numset_list_insert,domain_FOLDR_delete,DELETE_DEF
          ,strong_locals_rel_def]>>
        rw[]>>
        first_assum match_mp_tac>>fs[MEM_MAP,MEM_FILTER]>>
        Cases_on`y`>>fs[EXISTS_PROD]>>
        metis_tac[])
     >>
       fs[domain_lookup,domain_numset_list_insert,domain_FOLDR_delete
         ,strong_locals_rel_def,numset_list_insert_def]>>
       pop_assum(qspecl_then[`p_2`,`v`] mp_tac)>>fs[])
  >>
    match_mp_tac strong_locals_rel_insert_notin>>
    fs[domain_lookup]
QED
*)

(* HOL4 ML code, not ported:
Resume evaluate_remove_dead[Inst]:
  gvs[evaluate_def,remove_dead_def,AllCaseEqs(),inst_def,
      remove_dead_inst_def,get_live_inst_def,assign_def,
      word_exp_def,set_var_def,word_add_carry_def,PULL_EXISTS]>>
  TRY (match_mp_tac strong_locals_rel_insert_notin>>
       fs[domain_lookup]>>
       match_mp_tac strong_locals_rel_insert_notin>>
       fs[domain_lookup]>>
       NO_TAC) >>
  TRY (irule strong_locals_rel_I_insert_insert >> simp[] >> NO_TAC) >>
  TRY (
   imp_res_tac strong_locals_rel_I_get_var >>
   gvs[get_vars_def,the_words_def,CaseEq"option",CaseEq"word_loc"
     ,PULL_EXISTS] >>
   irule_at Any strong_locals_rel_I_insert_insert >> simp[] >>
   imp_res_tac strong_locals_rel_I_get_var >> gvs[] >>
   irule_at Any strong_locals_rel_subset >>
   first_x_assum (irule_at Any) >>
   simp[SUBSET_DEF] >> gvs[mem_load_def] >>
   goal_assum $ drule_at Any \\ simp[] >>
   qmatch_rename_tac`∃lv. strong_locals_rel I (_ INSERT lv) _ _`
   \\ metis_tac[INSERT_COMM] ) >>
  TRY (
    imp_res_tac strong_locals_rel_I_get_vars' >>
    gvs[get_vars_def, get_var_def, CaseEq"option", CaseEq"word_loc"] >>
    irule_at Any strong_locals_rel_I_insert_insert >> simp[] >>
    irule_at Any strong_locals_rel_I_insert_insert >> simp[] >>
    irule_at Any strong_locals_rel_subset >>
    first_assum (irule_at Any) >>
    simp[SUBSET_DEF] >>
    TRY(first_assum (irule_at Any)) >>
    rw[] >> fsrw_tac[DNF_ss][] >> gvs[] >> NO_TAC) >>
  TRY (
    imp_res_tac strong_locals_rel_I_get_var >>
    TRY pairarg_tac >>
    gvs[get_var_def, the_words_def, CaseEq"option", CaseEq"word_loc",
        mem_store_def] >>
    irule_at Any strong_locals_rel_subset >> simp[] >>
    rpt(first_assum (irule_at Any)) >>
    simp[SUBSET_DEF] >>
    metis_tac[INSERT_COMM] )
QED
*)

(* HOL4 ML code, not ported:
Resume evaluate_remove_dead[Get]:
  gvs[evaluate_def,remove_dead_def,AllCaseEqs(),set_var_def]
  >-
    (match_mp_tac strong_locals_rel_insert_notin>>fs[domain_lookup])
  >>
    fs[PULL_EXISTS,get_store_def]>>
    drule live_store_rel_FLOOKUP_store>>
    disch_then (fn th => DEP_REWRITE_TAC[th])>>
    simp[MEM_FILTER]>>
    CONJ_TAC >- (
      irule strong_locals_rel_I_insert_insert>>
      fs[])>>
    irule live_store_rel_less>>
    first_x_assum (irule_at Any)>>
    simp[SUBSET_DEF,MEM_FILTER]
QED
*)

(* HOL4 ML code, not ported:
Resume evaluate_remove_dead[OpCurrHeap]:
  gvs[evaluate_def,remove_dead_def,AllCaseEqs(),set_var_def]
  >- (
    match_mp_tac strong_locals_rel_insert_notin>>
    fs[domain_lookup])>>
  drule strong_locals_rel_I_word_exp>>
  disch_then (irule_at Any)>>
  first_assum (irule_at Any)>>
  simp[nlive_store_def,MEM_FILTER,get_live_exp_def,big_union_def
    ,domain_union]>>
  qexists_tac`(delete num live)`>>rw[]
  >- (
    irule strong_locals_rel_subset>>
    first_x_assum (irule_at Any)>>
    simp[SUBSET_DEF])
  >- (
    irule strong_locals_rel_I_insert_insert>>
    simp[]>>
    irule strong_locals_rel_subset>>
    first_x_assum (irule_at Any)>>
    simp[SUBSET_DEF])
  >- (
    irule live_store_rel_less>>
    first_x_assum (irule_at Any)>>
    simp[SUBSET_DEF,MEM_FILTER])
QED
*)

(* HOL4 ML code, not ported:
Resume evaluate_remove_dead[LocValue]:
  gvs[evaluate_def,remove_dead_def,AllCaseEqs(),set_var_def]
  >-
    (match_mp_tac strong_locals_rel_insert_notin>>fs[domain_lookup])>>
  fs[strong_locals_rel_def,lookup_insert,domain_union]>>rw[]
QED
*)

(* HOL4 ML code, not ported:
Resume evaluate_remove_dead[Set]:
  gvs[evaluate_def,remove_dead_def,AllCaseEqs(),word_exp_def
    ,set_store_def,flat_exp_conventions_def]
  >- (
    fs[live_store_rel_def,FLOOKUP_UPDATE]>>
    metis_tac[])>>
  drule_all strong_locals_rel_I_get_var>>
  simp[]>>disch_then kall_tac>>
  CONJ_TAC >- (
    irule strong_locals_rel_subset>>
    first_x_assum (irule_at Any)>>
    simp[SUBSET_DEF])>>
  fs[live_store_rel_def,FLOOKUP_UPDATE]
QED
*)

(* HOL4 ML code, not ported:
Resume evaluate_remove_dead[Seq]:
  gvs[evaluate_def,remove_dead_def,AllCaseEqs()]>>
  rpt (pairarg_tac>>fs[])>>
  gvs[]>>
  qpat_x_assum`_ = (res,rst)` mp_tac>>IF_CASES_TAC>>
  strip_tac
  >- (
    first_x_assum drule>>
    disch_then drule>> simp[]>> strip_tac>>
    first_x_assum drule>>
    disch_then drule>> simp[]>> strip_tac>>
    rw[]>>fs[evaluate_def]>>
    every_case_tac>>fs[])
  >>
    gvs[]>>first_x_assum drule>>
    disch_then drule>> simp[]>> strip_tac>>
    rw[]>>fs[evaluate_def]>>
    every_case_tac>>fs[]
QED
*)

(* HOL4 ML code, not ported:
Resume evaluate_remove_dead[MustTerminate]:
  gvs[evaluate_def,remove_dead_def,AllCaseEqs()]>>
  rpt (pairarg_tac>>fs[])>>
  gvs[]>>
  qpat_x_assum`A=(res,rst)` mp_tac>>
  IF_CASES_TAC>>strip_tac>>
  gvs[evaluate_def]>>
  first_x_assum (qspecl_then [`st with <|clock := MustTerminate_limit
    (:'a) ; termdep := st.termdep -1|>` ] mp_tac)>>
  fs[]>>
  disch_then drule_all>>
  rw[]>>fs[]
QED
*)

(* HOL4 ML code, not ported:
Resume evaluate_remove_dead[If]:
  gvs[evaluate_def,remove_dead_def] >>
  rpt (pairarg_tac >> fs[]) >> gvs[] >>
  Cases_on `ri`
*)
  (* Reg: resolve get_var for register operand, then apply IH *)
(* HOL4 ML code, not ported:
  >- (
    gvs[AllCaseEqs(),domain_insert,domain_union,get_var_imm_def] >>
    gvs[Once INSERT_COMM] >>
    imp_res_tac strong_locals_rel_I_get_var >> gvs[] >>
    `get_var n (st with <|locals := t; store := tstore|>) = SOME y` by (
      first_x_assum (qspecl_then [`t`,`r1 INSERT domain e2_live ∪ domain
        e3_live`]
        mp_tac) >>
      impl_tac >- gvs[Once INSERT_COMM] >> simp[]) >>
    first_x_assum (fn ih =>
      qspecl_then [`st`,`t`,`tstore`,`res`,`rst`] mp_tac ih >>
      impl_tac >- (
        simp[] >>
        CONJ_TAC >- (
          irule strong_locals_rel_subset >>
          first_x_assum (irule_at Any) >> simp[SUBSET_DEF]) >>
        irule live_store_rel_less >>
        first_x_assum (irule_at Any) >> gvs[SUBSET_DEF,MEM_FILTER]) >>
      strip_tac >> IF_CASES_TAC >> gvs[evaluate_def,get_var_imm_def] >>
      simp[]))
*)
  (* Imm: apply IH directly *)
(* HOL4 ML code, not ported:
  >- (
    gvs[AllCaseEqs(),domain_insert,domain_union,get_var_imm_def] >>
    gvs[Once INSERT_COMM] >>
    imp_res_tac strong_locals_rel_I_get_var >> gvs[] >>
    first_x_assum (fn ih =>
      qspecl_then [`st`,`t`,`tstore`,`res`,`rst`] mp_tac ih >>
      impl_tac >- (
        simp[] >>
        CONJ_TAC >- (
          irule strong_locals_rel_subset >>
          first_x_assum (irule_at Any) >> simp[SUBSET_DEF]) >>
        irule live_store_rel_less >>
        first_x_assum (irule_at Any) >> gvs[SUBSET_DEF,MEM_FILTER]) >>
      strip_tac >> IF_CASES_TAC >> gvs[evaluate_def,get_var_imm_def] >>
      simp[]))
QED
*)

(* HOL4 ML code, not ported:
Resume evaluate_remove_dead[CallSome]:
  gvs[evaluate_def,remove_dead_def,AllCaseEqs()] >>
  rpt (pairarg_tac >> fs[]) >> gvs[] >>
  rpt strip_tac >>
  `get_vars args (st with locals := t) = SOME xs` by (
    irule (GEN_ALL strong_locals_rel_I_get_vars') >>
    first_x_assum (irule_at Any) >>
    first_x_assum (irule_at Any) >>
    simp[domain_numset_list_insert,domain_union]) >>
  `cut_envs cutsets t = SOME envs` by (
    irule (GEN_ALL strong_locals_rel_I_cut_envs) >>
    first_x_assum (irule_at Any) >>
    irule strong_locals_rel_subset >>
    first_x_assum (irule_at Any) >>
    simp[domain_union,SUBSET_DEF]) >>
  `∀s. push_env envs (case h of NONE => NONE
         | SOME (n,p,a,b) =>
             SOME (n,FST (remove_dead p live nlive lt),a,b)) s =
       push_env envs h s` by
    (Cases_on `h` >> simp[push_env_def] >>
     rename1 `SOME htup` >> PairCases_on `htup` >>
     simp[push_env_def]) >>
  simp[Once evaluate_def, add_ret_loc_def] >>
  gvs[fix_clock_def, add_ret_loc_def] >>
  gvs[flush_state_def, call_env_def, dec_clock_def] >>
  Cases_on `env_to_list (SND envs) st.permute` >> gvs[]
  >- ((*Result*)
    rename1 `remove_dead _ live nlive lt = (ret_handler, ret_live)` >>
    first_x_assum (qspecl_then
      [`FST ret_live`, `SND ret_live`,
       `set_vars prog ys s1`,
       `(set_vars prog ys s1).locals`,
       `(set_vars prog ys s1).store`,
       `res`, `rst`] mp_tac) >>
    impl_tac >- simp[strong_locals_rel_def] >>
    strip_tac >> gvs[state_component_equality])
  >- ((*Exception*)
    rename1 `evaluate (handler, set_var hn _ _) = _` >>
    `push_env envs (SOME (hn,FST (remove_dead handler live nlive
      lt),l1',l2')) st =
     push_env envs (SOME (hn,handler,l1',l2')) st` by
      simp[push_env_def] >>
    gvs[] >>
    qpat_x_assum `∀a b c d e f g h.
      _ ∧ _ ∧ evaluate (handler,_) = _ ∧ _ ∧ _ ⇒ _`
      (qspecl_then
        [`FST (remove_dead handler live nlive lt)`,
         `FST (SND (remove_dead handler live nlive lt))`,
         `SND (SND (remove_dead handler live nlive lt))`,
         `set_var hn y s2`,
         `(set_var hn y s2).locals`,
         `(set_var hn y s2).store`,
         `res`, `rst`] mp_tac) >>
    impl_tac >- simp[strong_locals_rel_def] >>
    strip_tac >> gvs[state_component_equality])
QED
*)

(* HOL4 ML code, not ported:
Resume evaluate_remove_dead[CallNone]:
  gvs[evaluate_def,remove_dead_def,AllCaseEqs(),get_live_def]>>
  simp[PULL_EXISTS]>>
  first_x_assum (irule_at Any)>>
  rename1 `¬bad_dest_args xss yss` >>
  imp_res_tac strong_locals_rel_I_get_vars'>>
  gvs[domain_numset_list_insert]>>
  fs[call_env_def,dec_clock_def]>>
  qexistsl [`rst.store`,`rst.locals`]>>
  simp[state_component_equality]>>
  every_case_tac>>fs[]
QED
*)

(* HOL4 ML code, not ported:
Resume evaluate_remove_dead[Loop]:
  gvs[remove_dead_def]>>
  rpt (pairarg_tac>>fs[])>>gvs[]>>
  qspecl_then
    [`st`,`t`,`st.store`,`live`,`prog`,`exit_names`,`live'`,`nlive`,`lt`
      ,
     `Loop live body' exit_names`,`live`,`[]`,`res`,`rst`]
    mp_tac evaluate_remove_dead_Loop_helper>>
  simp[remove_dead_def,flat_exp_conventions_def]
QED
*)

(* HOL4 ML code, not ported:
Resume evaluate_remove_dead[Break]:
  gvs[evaluate_def,remove_dead_def,get_live_def]>>
  every_case_tac>>fs[]
QED
*)

(* HOL4 ML code, not ported:
Resume evaluate_remove_dead[Continue]:
  gvs[evaluate_def,remove_dead_def,get_live_def]>>
  every_case_tac>>fs[]
QED
*)

(* HOL4 ML code, not ported:
Resume evaluate_remove_dead[Alloc]:
  gvs[evaluate_def,remove_dead_def,AllCaseEqs(),get_live_def]>>
  imp_res_tac strong_locals_rel_I_get_var'>>fs[]>>
  gvs[alloc_def,AllCaseEqs()]>>
  simp[PULL_EXISTS]>>
  rename1 `cut_envs names st.locals = SOME x` >>
  `cut_envs names t = SOME x` by
    (match_mp_tac (GEN_ALL strong_locals_rel_I_cut_envs)>>fs[]>>
    qexists_tac`st`>>fs[]>>
    fs[strong_locals_rel_def,domain_union] >>
    metis_tac[])>>
  simp[]>>
  fs[get_store_def]>>
  first_x_assum (irule_at Any)>>
  simp[]>>
  qexists_tac`rst.locals`>>
  fs[strong_locals_rel_def]
QED
*)

(* HOL4 ML code, not ported:
Resume evaluate_remove_dead[Raise]:
  gvs[evaluate_def,remove_dead_def,AllCaseEqs(),get_live_def]>>
  imp_res_tac strong_locals_rel_I_get_var'>>fs[]>>
  gvs[jump_exc_def,AllCaseEqs()]
QED
*)

(* HOL4 ML code, not ported:
Resume evaluate_remove_dead[Return]:
  gvs[evaluate_def,remove_dead_def,AllCaseEqs(),get_live_def]>>
  imp_res_tac strong_locals_rel_I_get_var'>>fs[]>>
  irule strong_locals_rel_I_get_vars'>>fs[]>>
  first_x_assum (irule_at Any)>>
  simp[domain_numset_list_insert]
QED
*)

(* HOL4 ML code, not ported:
Resume evaluate_remove_dead[Skip]:
  gvs[evaluate_def,remove_dead_def,AllCaseEqs(),get_live_def]
QED
*)

(* HOL4 ML code, not ported:
Resume evaluate_remove_dead[StoreConsts]:
  gvs[evaluate_def,remove_dead_def,AllCaseEqs(),get_live_def]>>
  imp_res_tac strong_locals_rel_I_get_var>>fs[]>>
  gs[Once INSERT_COMM]>>
  first_x_assum drule>>rw[]>>
  simp[set_var_def,unset_var_def]>>
  fs[strong_locals_rel_def]>>rw[lookup_insert,lookup_delete]
QED
*)

(* HOL4 ML code, not ported:
Resume evaluate_remove_dead[Tick]:
  gvs[evaluate_def,remove_dead_def,AllCaseEqs(),get_live_def,
    flush_state_def,dec_clock_def,state_component_equality]
QED
*)

(* HOL4 ML code, not ported:
Resume evaluate_remove_dead[Install]:
  gvs[evaluate_def,remove_dead_def,AllCaseEqs(),get_live_def]>>
  pairarg_tac>>
  gvs[AllCaseEqs()]>>
  fs[list_insert_def]>>
  first_x_assum $ irule_at Any>> simp[]>>
  first_x_assum $ irule_at Any>> simp[]>>
  drule_at Any strong_locals_rel_I_cut_env>>
  disch_then $ irule_at Any>>
  simp[state_component_equality]>>
  CONJ_TAC >- (
    irule_at Any strong_locals_rel_subset>>
    first_x_assum (irule_at Any)>>
    simp[SUBSET_DEF,domain_union])>>
  ntac 4 (CONJ_TAC >- (
    irule strong_locals_rel_I_get_var>>
    simp[]>>
    qexists_tac`{}`>>
    irule_at Any strong_locals_rel_subset>>
    first_x_assum (irule_at Any)>>
    simp[SUBSET_DEF]))>>
  simp[strong_locals_rel_def]
QED
*)

(* HOL4 ML code, not ported:
Resume evaluate_remove_dead[CodeBufferWrite]:
  gvs[evaluate_def,remove_dead_def,AllCaseEqs(),get_live_def]>>
  fs[list_insert_def,PULL_EXISTS]>>
  first_x_assum (irule_at Any)>>
  simp[]>>
  ntac 2 (CONJ_TAC >- (
    irule strong_locals_rel_I_get_var>>
    simp[]>>
    qexists_tac`{}`>>
    irule_at Any strong_locals_rel_subset>>
    first_x_assum (irule_at Any)>>
    simp[SUBSET_DEF]))>>
  irule_at Any strong_locals_rel_subset>>
  first_x_assum (irule_at Any)>>
  simp[SUBSET_DEF]
QED
*)

(* HOL4 ML code, not ported:
Resume evaluate_remove_dead[DataBufferWrite]:
  gvs[evaluate_def,remove_dead_def,AllCaseEqs(),get_live_def]>>
  fs[list_insert_def,PULL_EXISTS]>>
  first_x_assum (irule_at Any)>>
  simp[]>>
  ntac 2 (CONJ_TAC >- (
    irule strong_locals_rel_I_get_var>>
    simp[]>>
    qexists_tac`{}`>>
    irule_at Any strong_locals_rel_subset>>
    first_x_assum (irule_at Any)>>
    simp[SUBSET_DEF]))>>
  irule_at Any strong_locals_rel_subset>>
  first_x_assum (irule_at Any)>>
  simp[SUBSET_DEF]
QED
*)

(* HOL4 ML code, not ported:
Resume evaluate_remove_dead[FFI]:
  gvs[evaluate_def,remove_dead_def,CaseEqs["option","word_loc"]
    ,get_live_def]>>
  simp[PULL_EXISTS]>>
  last_x_assum (irule_at Any)>>
  first_x_assum (irule_at Any)>>
  simp[GSYM PULL_EXISTS]>>
  ntac 4 (
    CONJ_TAC >- (
    irule strong_locals_rel_I_get_var>>
    simp[]>>
    qexists_tac`{}`>>
    irule_at Any strong_locals_rel_subset>>
    first_x_assum (irule_at Any)>>
    simp[SUBSET_DEF]))>>
  drule_at Any strong_locals_rel_I_cut_env>>
  disch_then $ irule_at Any>>
  simp[GSYM PULL_EXISTS]>>
  CONJ_TAC >- (
    irule_at Any strong_locals_rel_subset>>
    first_x_assum (irule_at Any)>>
    simp[SUBSET_DEF,domain_union])>>
  TOP_CASE_TAC>>gvs[]
  >-
    fs[state_component_equality,strong_locals_rel_def]
  >-
    fs[flush_state_def]
QED
*)

(* HOL4 ML code, not ported:
Resume evaluate_remove_dead[ShareInst]:
  gvs[evaluate_def,remove_dead_def,CaseEqs["option","word_loc"]
    ,get_live_def]>>
  gvs[oneline flat_exp_conventions_def,AllCasePreds()]>>
  drule strong_locals_rel_I_word_exp>>
  disch_then (irule_at Any)>>
  first_assum (irule_at Any)>>
  rename1`share_inst aa bb`>>
  fs[nlive_store_def,get_live_exp_def,domain_union,GSYM PULL_EXISTS]>>
  (CONJ_TAC >- (
    irule_at Any strong_locals_rel_subset>>
    first_x_assum (irule_at Any)>>
    qexists_tac`delete bb live`>>
    rw[SUBSET_DEF]>>simp[domain_union]))>>
  gvs[oneline share_inst_def,AllCaseEqs(),
    oneline sh_mem_store_def,
    oneline sh_mem_store_byte_def,
    oneline sh_mem_store16_def,
    oneline sh_mem_store32_def,
    oneline sh_mem_load_def,
    oneline sh_mem_load_byte_def,
    oneline sh_mem_load16_def,
    oneline sh_mem_load32_def,
    oneline sh_mem_set_var_def,
    set_var_def,
    flush_state_def, get_live_def] >>
  TRY(irule_at Any strong_locals_rel_I_insert_insert >>
    fs[strong_locals_rel_def,domain_union])>>
  irule_at Any strong_locals_rel_I_get_var'>>
  gvs[]>>
  fs[strong_locals_rel_def,domain_union]>>
  metis_tac[]
QED
*)

(* HOL4 ML code, not ported:
Finalise evaluate_remove_dead;
*)

(*SSA Proof*)

(* HOL4 ML code, not ported:
val size_tac2 = impl_tac>-
  (full_simp_tac(srw_ss())[prog_size_def]>>DECIDE_TAC)
*)

(*This might not be the optimal invariant.. because it is very
  restrictive on the ssa_mapping*)
let ssa_locals_rel_def = cake_define
  `ssa_locals_rel na ssa st_locs cst_locs =
   ((!x y. sptree_lookup x ssa = SOME y ==> y IN domain cst_locs) /\
   (!x y. sptree_lookup x st_locs = SOME y ==>
     x IN domain ssa /\
     sptree_lookup (THE (sptree_lookup x ssa)) cst_locs = SOME y /\
     (is_alloc_var x ==> x < na)))`;;

(*ssa_map_ok specifies the form of ssa_maps we care about
  1) The remapped keys are ALL_DISTINCT
  2) The remap keyset is bounded, and no phy vars
*)
let ssa_map_ok_def = cake_define
  `ssa_map_ok na ssa =
   (!x y. sptree_lookup x ssa = SOME y ==>
     ~is_phy_var y /\ y < na)`;;

(* HOL4 ML code, not ported:
val exists_tac = qexists_tac`cst.permute`>>
    full_simp_tac(srw_ss())[evaluate_def,LET_THM,word_state_eq_rel_def
      ,ssa_cc_trans_def];
*)

(*Characterize result of merge_moves*)

(*Another frame proof about unchanged lookups*)

(*Don't know a neat way to prove this for both sides at once neatly,
Also, the cases are basically copy pasted... *)

(*Swapping lemma that allows us to swap in ssaL for ssaR
  after we are done fixing them*)

(* HOL4 ML code, not ported:
fun use_ALOOKUP_ALL_DISTINCT_MEM (g as (asl,w)) =
  let
    val tm = find_term(can(match_term(lhs(snd(dest_imp(concl
      ALOOKUP_ALL_DISTINCT_MEM)))))) w
    val (_,[al,k]) = strip_comb tm
  in
    mp_tac(ISPECL [al,k] (Q.GENL[`al`,`k`,`v`]
      ALOOKUP_ALL_DISTINCT_MEM))
  end g;
*)

(* HOL4 ML code, not ported:
val is_phy_var_tac =
    full_simp_tac(srw_ss())[is_phy_var_def]>>
    `0<2:num` by DECIDE_TAC>>
    `∀k.(2:num)*k=k*2` by DECIDE_TAC>>
    metis_tac[arithmeticTheory.MOD_EQ_0];
*)

(*ordered such that its easy to drule*)

(*ordered such that its easy to drule*)

(*ordered such that its easy to drule*)

(* HOL4 ML code, not ported:
val exp_tac =
  (LET_ELIM_TAC>>full_simp_tac(srw_ss())[next_var_rename_def]>>
    TRY(DECIDE_TAC)>>
    metis_tac[ssa_map_ok_extend,convention_partitions
      ,is_alloc_var_add]);
*)

(* HOL4 ML code, not ported:
val th =
  (MATCH_MP
    (PROVE[]``((a ⇒ b) ∧ (c ⇒ d)) ⇒ ((a ∨ c) ⇒ b ∨ d)``)
    (CONJ is_stack_var_flip is_alloc_var_flip))
*)

(* HOL4 ML code, not ported:
val swap_imp =PROVE[]``A ==> B ==> C <=> B ==> A ==> C``
*)

(* HOL4 ML code, not ported:
val list_next_var_rename_props_2 =
  list_next_var_rename_props
  |> CONV_RULE(RESORT_FORALL_CONV(sort_vars["na","na'"]))
  |> Q.SPECL[`na+2`] |> SPEC_ALL
  |> UNDISCH
  |> REWRITE_RULE[GSYM AND_IMP_INTRO]
  |> C MATCH_MP (UNDISCH th)
  |> DISCH_ALL
  |> REWRITE_RULE[flip_rw]
  |> ONCE_REWRITE_RULE [swap_imp]
  |> UNDISCH
  |> REWRITE_RULE[AND_IMP_INTRO]
  |> DISCH_ALL
  |> GEN_ALL
  |> CONV_RULE(RESORT_FORALL_CONV(sort_vars["ls","ssa","na"]));
*)

(*ordered such that its easy to drule*)


(*Prove the properties that hold of ssa_cc_trans independent of
   semantics*)

(* HOL4 ML code, not ported:
Resume ssa_cc_trans_props[Loop]:
  strip_tac >>
  LET_ELIM_TAC >>
  fs[loop_setup_def] >>
  pairarg_tac >> fs[] >>
  pairarg_tac >> fs[] >>
  rveq >>
  drule_then assume_tac list_next_var_rename_props >>
  rfs[] >>
  qpat_x_assum `list_next_var_rename_move _ _ _ = _` assume_tac >>
  drule_then assume_tac list_next_var_rename_move_props >>
  rfs[] >>
  unabbrev_all_tac >>
  `ssa_map_ok na_refreshed (inter ssa_refreshed names)` by
    (match_mp_tac ssa_map_ok_inter >> first_x_assum ACCEPT_TAC) >>
  qpat_x_assum `_ ∧ is_alloc_var na_refreshed ⇒ _` mp_tac >>
  impl_tac >- simp[] >>
  strip_tac >>
  rpt conj_tac >>
  TRY (match_mp_tac ssa_map_ok_inter >>
       irule ssa_map_ok_more >>
       qexists_tac `na_refreshed`) >>
  gs[]
QED
*)

(* HOL4 ML code, not ported:
Resume ssa_cc_trans_props[Break]:
  fs[ssa_cc_trans_def]>>every_case_tac>>fs[]>>rveq>>simp[]
QED
*)

(* HOL4 ML code, not ported:
Resume ssa_cc_trans_props[Continue]:
  fs[ssa_cc_trans_def]>>every_case_tac>>fs[]>>rveq>>simp[]
QED
*)

(* HOL4 ML code, not ported:
Finalise ssa_cc_trans_props;
*)

(* HOL4 ML code, not ported:
val exp_tac2 =
    (last_x_assum kall_tac>>
    exists_tac>>
    EVERY_CASE_TAC>>full_simp_tac(srw_ss())[next_var_rename_def]>>
    imp_res_tac ssa_locals_rel_get_var>>
    imp_res_tac
      ssa_cc_trans_exp_correct>>full_simp_tac(srw_ss())
      [word_state_eq_rel_def]>>
    rev_full_simp_tac(srw_ss())[evaluate_def]>>
    fs[set_var_def,get_store_def,set_store_def]>>
    match_mp_tac ssa_locals_rel_set_var>>
    full_simp_tac(srw_ss())[every_var_def]);
*)

(* HOL4 ML code, not ported:
val setup_tac = Cases_on`word_exp st expr`>>full_simp_tac(srw_ss())[]>>
                imp_res_tac ssa_cc_trans_exp_correct>>
                rev_full_simp_tac(srw_ss())[word_state_eq_rel_def]>>
                full_simp_tac(srw_ss())[Abbr`expr`,ssa_cc_trans_exp_def
                  ,option_lookup_def,set_var_def];
*)
(*TODO move*)

let lt_ok_def = cake_define
  `lt_ok lt <=>
     EVERY (\(tgt_ssa,names,exit_names).
       INJ (option_lookup tgt_ssa) (domain names) UNIV /\
       INJ (option_lookup tgt_ssa) (domain exit_names) UNIV) lt`;;

(* Evaluating a chain of fake_move r writes 0 to each register in rs,
   leaves the rest of state untouched. *)

(* Bundles the (extend, fake_init, refresh) Loop-entry setup.
   Establishes
   ssa_locals_rel under ssa_refreshed and INJ on names/exit_names
     domains
   by construction. *)

(* If P evaluates to (NONE, t), Seq P Q evaluates as Q from t. *)

(* fromAList (MAP f (toAList LN)) behaves like LN in cut_env. *)

(* Helper for Loop iter; target is the INNER Loop (not the full
   translation),
   so the clock-IH recursive call lines up with the inner Loop's
     STOP-recursion
   without re-running the outer fake_prog + refresh_mov setup each iter.
     *)

(* HOL4 ML code, not ported:
Resume ssa_cc_trans_correct[Skip]:
    exists_tac
QED
*)

(* HOL4 ML code, not ported:
Resume ssa_cc_trans_correct[Move]:
    last_x_assum kall_tac>>
    exists_tac>>
    EVERY_CASE_TAC>>full_simp_tac(srw_ss())[set_vars_def]>>
    rpt(pairarg_tac>>gvs[])>>
    gvs[evaluate_def]>>
    imp_res_tac list_next_var_rename_lemma_1>>
    imp_res_tac list_next_var_rename_lemma_2>>
    gvs[MAP_ZIP,LENGTH_COUNT_LIST]>>
    imp_res_tac ssa_locals_rel_get_vars>>
    gvs[set_vars_def]>>
    qmatch_goalsub_abbrev_tac`ssa_locals_rel (na + 4 * LENGTH l) _ st1
      st2`>>
*)
    (* The ssa'' map would have been fine to return without
      forcing the renames too *)
(* HOL4 ML code, not ported:
    `ssa_locals_rel (na + 4 * LENGTH l) ssa'' st1 st2` by (
      unabbrev_all_tac>>
      fs[ssa_locals_rel_def]>>
      first_x_assum(qspecl_then[`ssa`,`na`] assume_tac)>>
      gvs[]>>
      imp_res_tac get_vars_length_lemma>>
      CONJ_ASM1_TAC
      >- (
        rw[domain_lookup]>>
        fs[lookup_alist_insert]>>
        EVERY_CASE_TAC>>
        rev_full_simp_tac(srw_ss())[ALOOKUP_NONE,MAP_ZIP]>>
        `¬ (MEM x' (MAP FST l))` by
          (CCONTR_TAC>>
          full_simp_tac(srw_ss())[MEM_MAP]>>
          first_x_assum(qspec_then`x'` assume_tac)>>
          rev_full_simp_tac(srw_ss())[]>>
          metis_tac[])>>
        `x' ∈ domain ssa'' ∧ x' ∈ domain ssa` by
          (CONJ_ASM1_TAC>-
            full_simp_tac(srw_ss())[domain_lookup]
          >>
          full_simp_tac(srw_ss())[EXTENSION]>>metis_tac[])>>
        metis_tac[domain_lookup]) >>
      gvs[strong_locals_rel_def]>>
      rw[]>>
      gvs[lookup_alist_insert]
      >- (
        Cases_on`MEM x' (MAP FST l)`>>
        full_simp_tac(srw_ss())[]>>
        Q.ISPECL_THEN [`MAP FST l`,`x`,`x'`] assume_tac
          ALOOKUP_ZIP_FAIL>>
        rev_full_simp_tac(srw_ss())[]>>full_simp_tac(srw_ss())[])
      >- (
        Cases_on`MEM x' (MAP FST l)`>>
        full_simp_tac(srw_ss())[]
        >- (
          `ALL_DISTINCT (MAP FST (ZIP (MAP FST l,x)))` by
            full_simp_tac(srw_ss())[MAP_ZIP]>>
          full_simp_tac(srw_ss())[MEM_EL]>>
          imp_res_tac ALOOKUP_ALL_DISTINCT_EL>>
          pop_assum(qspec_then `n'` mp_tac)>>
          impl_tac>>
          full_simp_tac(srw_ss())[LENGTH_ZIP]>>srw_tac[][]>>
          rev_full_simp_tac(srw_ss())[EL_ZIP]>>full_simp_tac(srw_ss())
            []>>
          imp_res_tac ALOOKUP_ALL_DISTINCT_REMAP>>
          full_simp_tac(srw_ss())[LENGTH_MAP])
        >>
        Q.ISPECL_THEN [`MAP FST l`,`x`,`x'`] assume_tac
          ALOOKUP_ZIP_FAIL>>
        gvs[ssa_map_ok_def]>>
        ntac 11 (last_x_assum kall_tac)>>
        res_tac>>
        fs[domain_lookup]>>res_tac>>
        qabbrev_tac `ls = MAP (\x. THE (lookup x ssa'')) (MAP FST l)`>>
        qsuff_tac `ALOOKUP (ZIP (ls,x)) v = NONE` >>
        full_simp_tac(srw_ss())[]>>full_simp_tac(srw_ss())
          [ALOOKUP_NONE]>>
        qpat_x_assum`A = ls` (sym_sub_tac)>>
        full_simp_tac(srw_ss())[MAP_ZIP,LENGTH_COUNT_LIST]>>
        full_simp_tac(srw_ss())[MEM_MAP]>>srw_tac[][]>>
        DECIDE_TAC)
      >>
        EVERY_CASE_TAC>>rev_full_simp_tac(srw_ss())[every_var_def]
        >-
          metis_tac[DECIDE``x'<na ⇒ x' < na + 4*LENGTH l``]
        >>
          `MEM x' (MAP FST l)` by
            metis_tac[ALOOKUP_ZIP_MEM,LENGTH_MAP]>>
          full_simp_tac(srw_ss())[EVERY_MEM]>>
          metis_tac[DECIDE``x'<na ⇒ x' < na + 4*LENGTH l``]
      )>>
    drule get_vars_length_lemma>>
    simp[]>>strip_tac>>
*)
    (* but we force some new mappings *)
(* HOL4 ML code, not ported:
    match_mp_tac ssa_locals_rel_force_rename>>
    simp[]>>
    CONJ_TAC >- (
      simp[EVERY_MEM,MEM_FILTER,MEM_ZIP,LENGTH_COUNT_LIST]>>
      rw[]>>
      fs[EL_MAP,LENGTH_COUNT_LIST,EL_COUNT_LIST]>>
      qmatch_goalsub_abbrev_tac`A = B`>>
      rename1`ii < LENGTH l`>>
      `B = SOME (EL ii x)` by (
        unabbrev_all_tac>>
        DEP_REWRITE_TAC[lookup_alist_insert]>>
        simp[LENGTH_COUNT_LIST,AllCaseEqs()]>>
        DISJ2_TAC>>
        match_mp_tac ALL_DISTINCT_MEM_IMP_ALOOKUP_SOME>>
        simp[MAP_ZIP,LENGTH_COUNT_LIST,MEM_ZIP]>>
        qexists_tac`ii`>>simp[EL_MAP,LENGTH_COUNT_LIST,EL_COUNT_LIST])>>
      pop_assum SUBST1_TAC>>
      unabbrev_all_tac>>
      DEP_REWRITE_TAC[lookup_alist_insert]>>
      simp[AllCaseEqs()]>>
      DISJ1_TAC>>
      simp[ALOOKUP_NONE,MAP_ZIP]>>
      imp_res_tac get_vars_exists>>
      imp_res_tac get_vars_eq>>
      gvs[EL_MAP,SUBSET_DEF,MEM_MAP,PULL_EXISTS,domain_lookup,MEM_EL]>>
      first_x_assum(qspec_then`ii` mp_tac)>>simp[]>>
      rw[]>>simp[])
    >- (
      simp[Abbr`st2`,SUBSET_DEF,MEM_MAP,MEM_FILTER,MEM_ZIP
        ,LENGTH_COUNT_LIST,PULL_EXISTS,EL_MAP,EL_COUNT_LIST]>>
      DEP_REWRITE_TAC[domain_alist_insert]>>
      simp[LENGTH_COUNT_LIST,MEM_MAP,MEM_COUNT_LIST]>>
      simp[MEM_COUNT_LIST]>>
      metis_tac[ADD_COMM])
QED
*)

(* HOL4 ML code, not ported:
Resume ssa_cc_trans_correct[Inst]:
    last_x_assum kall_tac>>
    exists_tac>>
    Cases_on`i`>> (TRY (Cases_on`a`))>> (TRY(Cases_on`m`))>>
    fs[next_var_rename_def,ssa_cc_trans_inst_def,inst_def,assign_def
      ,evaluate_def,LET_THM]
    >~[`Const`]
    >- (
      Cases_on`word_exp st (Const c)`>>
      full_simp_tac(srw_ss())[set_var_def,word_exp_def]>>
      match_mp_tac ssa_locals_rel_set_var>>
      full_simp_tac(srw_ss())[every_var_inst_def,every_var_def])
    >~[`Binop`]
    >-(
      Cases_on`r`>>
      fs[evaluate_def,inst_def,assign_def]>>
      qpat_abbrev_tac `expr = (Op b [Var n0;Z])`>>
      setup_tac>>
      match_mp_tac ssa_locals_rel_set_var>>
      full_simp_tac(srw_ss())[every_var_inst_def,every_var_def])
    >~[`Shift`]
    >- (
      rename1`Shift _ n n0 r`>>
      Cases_on`r`>>
      fs[evaluate_def,inst_def,assign_def,get_vars_def]
      >- (
        fs[word_exp_def]>>
        rename1`Reg n'`>>
        Cases_on`get_var n0 st`>>fs[]>>
        rename1`get_var _ _ = SOME x`>>
        Cases_on`x`>>simp[]>>
        Cases_on`get_var n' st`>>fs[]>>
        rename1`get_var _ _ = SOME x`>>
        Cases_on`x`>>simp[]>>
        imp_res_tac ssa_locals_rel_get_var>>
        fs[set_vars_def,get_var_def,lookup_alist_insert]>>
        `option_lookup ssa n0 ≠ 8` by (
          fs[ssa_locals_rel_def]>>
          qpat_x_assum`lookup n' _ = _` kall_tac>>
          first_x_assum drule>>
          rfs[domain_lookup,ssa_map_ok_def]>>
          strip_tac>>
          first_x_assum drule>>
          rw[]>>
          fs[is_phy_var_def,option_lookup_def]>>
          CCONTR_TAC>>
          fs[])>>
        fs[]>>
        every_case_tac>>
        simp[set_var_def,alist_insert_def]>>
        match_mp_tac ssa_locals_rel_set_var>>
        fs[every_var_def,every_var_inst_def]>>
        irule ssa_locals_rel_ignore_insert>>
        simp[is_phy_var_def])
     >- (
        qpat_abbrev_tac`expr = (Shift s (Var n0) Z)`>>
        setup_tac>>
        match_mp_tac ssa_locals_rel_set_var>>
        fs[every_var_inst_def,every_var_def])
    )
    >- ( (*Div*)
      fs[]>>
      Cases_on`get_vars [n1;n0] st`>>fs[get_vars_def]>>
      pop_assum mp_tac>>
      ntac 2 FULL_CASE_TAC >>fs[]>>
      disch_then sym_sub_tac>>fs[]>>
      imp_res_tac ssa_locals_rel_get_var>>
      fs[set_vars_def,get_var_def,lookup_alist_insert]>>
      Cases_on`x'`>>Cases_on`x''`>>
      fs[set_var_def,alist_insert_def]>>
      IF_CASES_TAC>>
      fs[lookup_insert,alist_insert_def,insert_shadow,ssa_locals_rel_def
        ,every_var_def,every_var_inst_def]>>
      CONJ_TAC>-
        (rw[]>>metis_tac[])>>
      ntac 2 strip_tac>>
      IF_CASES_TAC>>fs[]>>
      IF_CASES_TAC>>fs[ssa_map_ok_def]>>
      strip_tac>>
      first_x_assum (qspecl_then[`x`,`y`] assume_tac)>>rfs[]>>
      fs[domain_lookup]>>
      first_x_assum (qspecl_then[`x`,`v'`] assume_tac)>>rfs[]>>
      fs[is_phy_var_def]>>
      rw[]>>fs[])
    >~[`LongMul`]
    >- ( (*LongMul*)
      Cases_on`get_vars [n1;n2] st`>>fs[get_vars_def]>>
      pop_assum mp_tac>>
      ntac 2 FULL_CASE_TAC >>fs[]>>
      disch_then sym_sub_tac>>fs[]>>
      fs[get_vars_def,next_var_rename_def,ssa_cc_trans_inst_def,inst_def
        ,assign_def,evaluate_def,LET_THM]>>
      imp_res_tac ssa_locals_rel_get_var>>
      fs[set_vars_def,get_var_def,lookup_alist_insert]>>
      rename1`lookup (_ n1) cst.locals = SOME xx1`>>
      rename1`lookup (_ n2) cst.locals = SOME xx2`>>
      Cases_on`xx1`>>Cases_on`xx2`>>
      fs[set_var_def,alist_insert_def]
      >- (
*)
        (* is_x64 *)
(* HOL4 ML code, not ported:
        `option_lookup ssa n2 ≠ 0` by (
          fs[ssa_locals_rel_def]>>
          qpat_x_assum`lookup n1 _ = _` kall_tac>>
          first_x_assum drule>>
          rfs[domain_lookup,ssa_map_ok_def]>>
          strip_tac>>
          first_x_assum drule>>
          rw[]>>
          fs[is_phy_var_def,option_lookup_def]>>
          CCONTR_TAC>>
          fs[]>>
          qpat_x_assum`B=0n` SUBST_ALL_TAC>>fs[])>>
        fs[lookup_insert,alist_insert_def,insert_shadow
          ,ssa_locals_rel_def,every_var_def,every_var_inst_def]>>
        CONJ_TAC>-
          (rw[]>>metis_tac[])>>
        ntac 2 strip_tac>>
        IF_CASES_TAC>>fs[]>>
        IF_CASES_TAC>>fs[ssa_map_ok_def]>>
        strip_tac>>
        first_x_assum (qspecl_then[`x`,`y`] assume_tac)>>
        rfs[]>>
        fs[domain_lookup]>>
        first_x_assum (qspecl_then[`x`,`v'`] assume_tac)>>
        rfs[]>>
        IF_CASES_TAC>>fs[is_phy_var_def]>>
        rw[]>>fs[])
*)
      (* Not needed
      >- (
        gvs[every_var_def,every_var_inst_def]>>
        `na + 8 = (na + 4) + 4` by fs[]>>
        pop_assum SUBST_ALL_TAC>>
        match_mp_tac ssa_locals_rel_insert>>
        reverse CONJ_TAC
        >- (
          simp[]>>
          match_mp_tac ssa_map_ok_extend>>
          metis_tac[convention_partitions])>>
        match_mp_tac ssa_locals_rel_insert>>
        simp[]
      ) *)
(* HOL4 ML code, not ported:
    )
    >~[`LongDiv`]
    >- ( (*LongDiv*)
      fs[]>>
      Cases_on`get_vars [n1;n2;n3] st`>>fs[get_vars_def]>>
      pop_assum mp_tac>>
      ntac 3 FULL_CASE_TAC >>fs[]>>
      disch_then sym_sub_tac>>fs[]>>
      imp_res_tac
        ssa_locals_rel_get_var>>fs[set_vars_def,get_var_def
        ,lookup_alist_insert]>>
      `option_lookup ssa n3 ≠ 0 ∧ option_lookup ssa n3 ≠ 6` by
        (fs[ssa_locals_rel_def]>>
        first_x_assum(qspecl_then[`n3`,`x'`]assume_tac)>>
        rfs[domain_lookup,ssa_map_ok_def]>>
        first_x_assum(qspecl_then[`n3`,`v'`] assume_tac)>>
        rfs[]>>
        fs[is_phy_var_def,option_lookup_def]>>
        CCONTR_TAC>>
        fs[]>>
        pop_assum SUBST_ALL_TAC>>fs[])>>
      fs[]>>
      Cases_on`x'`>>Cases_on`x''`>>Cases_on`x'''`>>
      fs[set_var_def,alist_insert_def]>>
      IF_CASES_TAC>>
      fs[lookup_insert,alist_insert_def,insert_shadow,ssa_locals_rel_def
        ,every_var_def,every_var_inst_def]>>
      CONJ_TAC>-
        (rw[]>>metis_tac[])>>
      ntac 2 strip_tac>>
      IF_CASES_TAC>>fs[]>>
      IF_CASES_TAC>>fs[ssa_map_ok_def]>>
      strip_tac>>
      first_x_assum (qspecl_then[`x`,`y`] assume_tac)>>rfs[]>>
      fs[domain_lookup]>>
      first_x_assum (qspecl_then[`x`,`v'`] assume_tac)>>rfs[]>>
      IF_CASES_TAC>>fs[is_phy_var_def]>>
      rw[]>>fs[])
    >~[`AddCarry`]
    >- ( (* AddCarry *)
      fs[]>>
      Cases_on`get_vars [n0;n1;n2] st`>>fs[get_vars_def]>>
      pop_assum mp_tac>>
      ntac 3 FULL_CASE_TAC >>fs[]>>
      disch_then sym_sub_tac>>fs[]>>
      imp_res_tac
        ssa_locals_rel_get_var>>fs[set_vars_def,get_var_def
        ,lookup_alist_insert]>>
      `option_lookup ssa n0 ≠ 0 ∧ option_lookup ssa n1 ≠ 0` by
        (fs[ssa_locals_rel_def]>>
        first_assum (qspecl_then[`n0`,`x'''`] assume_tac)>>
        first_x_assum(qspecl_then[`n1`,`x''`] assume_tac)>>
        rfs[domain_lookup,ssa_map_ok_def]>>
        first_assum(qspecl_then[`n0`,`v''`] assume_tac)>>
        first_x_assum(qspecl_then[`n1`,`v'`] assume_tac)>>
        rfs[]>>
        fs[is_phy_var_def,option_lookup_def]>>
        CCONTR_TAC>>
        fs[]>>
        pop_assum SUBST_ALL_TAC>>fs[])>>
      fs[]>>
      Cases_on`x'`>>Cases_on`x''`>>Cases_on`x'''`>>fs[set_var_def
        ,alist_insert_def,word_add_carry_def]>>
      qpat_abbrev_tac`w1 = if A then B else C`>>
      qpat_abbrev_tac`w2 = n2w A`>>
      fs[ssa_locals_rel_def,lookup_insert,every_var_def
        ,every_var_inst_def,alist_insert_def]>>
      CONJ_TAC>-
        (rw[]>>metis_tac[])>>
      ntac 2 strip_tac>>
      IF_CASES_TAC>>fs[]>>
      IF_CASES_TAC>>fs[ssa_map_ok_def]>>
      strip_tac>>
      first_x_assum (qspecl_then[`x`,`y`] assume_tac)>>rfs[]>>
      fs[domain_lookup]>>
      first_x_assum (qspecl_then[`x`,`v'`] assume_tac)>>rfs[]>>
      IF_CASES_TAC>>fs[is_phy_var_def]>>
      rw[]>>fs[])
    >~[`AddOverflow`]
    >- ( (* AddOverflow*)
      fs[]>>
      Cases_on`get_vars [n0;n1] st`>>fs[get_vars_def]>>
      pop_assum mp_tac>>
      ntac 2 FULL_CASE_TAC >>fs[]>>
      disch_then sym_sub_tac>>fs[]>>
      imp_res_tac
        ssa_locals_rel_get_var>>fs[set_vars_def,get_var_def
        ,lookup_alist_insert]>>
      fs[]>>
      Cases_on`x'`>>Cases_on`x''`>>fs[set_var_def,alist_insert_def]>>
      qpat_abbrev_tac`w1 = if A then B else C`>>
      fs[ssa_locals_rel_def,lookup_insert,every_var_def
        ,every_var_inst_def,alist_insert_def]>>
      CONJ_TAC>-
        (rw[]>>metis_tac[])>>
      ntac 2 strip_tac>>
      IF_CASES_TAC>>fs[]>>
      IF_CASES_TAC>>fs[ssa_map_ok_def]>>
      strip_tac>>
      first_x_assum (qspecl_then[`x`,`y`] assume_tac)>>rfs[]>>
      fs[domain_lookup]>>
      first_x_assum (qspecl_then[`x`,`v'`] assume_tac)>>rfs[]>>
      IF_CASES_TAC>>fs[is_phy_var_def]>>
      rw[]>>fs[])
    >~[`SubOverflow`]
    >- ( (*SubOverflow*)
      fs[]>>
      Cases_on`get_vars [n0;n1] st`>>fs[get_vars_def]>>
      pop_assum mp_tac>>
      ntac 2 FULL_CASE_TAC >>fs[]>>
      disch_then sym_sub_tac>>fs[]>>
      imp_res_tac
        ssa_locals_rel_get_var>>fs[set_vars_def,get_var_def
        ,lookup_alist_insert]>>
      fs[]>>
      Cases_on`x'`>>Cases_on`x''`>>fs[set_var_def,alist_insert_def]>>
      qpat_abbrev_tac`w1 = if A then B else C`>>
      fs[ssa_locals_rel_def,lookup_insert,every_var_def
        ,every_var_inst_def,alist_insert_def]>>
      CONJ_TAC>-
        (rw[]>>metis_tac[])>>
      ntac 2 strip_tac>>
      IF_CASES_TAC>>fs[]>>
      IF_CASES_TAC>>fs[ssa_map_ok_def]>>
      strip_tac>>
      first_x_assum (qspecl_then[`x`,`y`] assume_tac)>>rfs[]>>
      fs[domain_lookup]>>
      first_x_assum (qspecl_then[`x`,`v'`] assume_tac)>>rfs[]>>
      IF_CASES_TAC>>fs[is_phy_var_def]>>
      rw[]>>fs[])
    >~[`Mem Load _ (Addr _ _)`]
    >- (
      qpat_abbrev_tac`expr=((Op Add [Var n';A]))`>>
      setup_tac>>
      Cases_on`x`>>
      full_simp_tac(srw_ss())[mem_load_def]>>
        full_simp_tac(srw_ss())[GSYM mem_load_def]>>
      BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[] >>
      match_mp_tac ssa_locals_rel_set_var>>
      fs[every_var_inst_def,every_var_def])
    >~[`Mem Load8 _ (Addr _ _)`]
    >- (
      qpat_abbrev_tac`expr=((Op Add [Var n';A]))`>>
      setup_tac>>
      Cases_on`x`>>
      full_simp_tac(srw_ss())[mem_load_byte_aux_def]>>
      Cases_on`st.memory (byte_align c')`>>fs[]>>
      IF_CASES_TAC>>fs[]>>
      match_mp_tac ssa_locals_rel_set_var>>
      fs[every_var_inst_def,every_var_def])
    >~[`Mem Load32 _ (Addr _ _)`]
    >- (
      qpat_abbrev_tac`expr=((Op Add [Var n';A]))`>>
      setup_tac>>
      Cases_on`x`>>
      full_simp_tac(srw_ss())[mem_load_32_alt]>>
      Cases_on`st.memory (byte_align c')`>>fs[]>>
      ntac 2 (IF_CASES_TAC>>fs[])>> gvs[] >>
      match_mp_tac ssa_locals_rel_set_var>>
      fs[every_var_inst_def,every_var_def])
    >~[`Mem Store _ (Addr _ _)`]
    >- (
      qpat_abbrev_tac`expr=Op Add [Var n';A]`>>
      full_simp_tac(srw_ss())[]>>
      setup_tac>>
      Cases_on`x`>>fs[]>>
      Cases_on`get_var n st`>>full_simp_tac(srw_ss())[]>>imp_res_tac
        ssa_locals_rel_get_var>>
      fs[option_lookup_def]>>
      Cases_on`mem_store c x' st`>>
      fs[mem_store_def]>>
      IF_CASES_TAC>>fs[])
    >~[`Mem Store8 _ (Addr _ _)`]
    >- (
      qpat_abbrev_tac`expr=Op Add [Var n';A]`>>
      fs[]>>
      setup_tac>>
      Cases_on`x`>>fs[]>>
      Cases_on`get_var n st`>>
      fs[]>>imp_res_tac ssa_locals_rel_get_var>>
      Cases_on`x`>>fs[option_lookup_def]>>
      CASE_TAC>>fs[])
    >~[`Mem Store32 _ (Addr _ _)`]
    >- (
      qpat_abbrev_tac`expr=Op Add [Var n';A]`>>
      fs[]>>
      setup_tac>>
      Cases_on`x`>>fs[]>>
      Cases_on`get_var n st`>>
      fs[]>>imp_res_tac ssa_locals_rel_get_var>>
      Cases_on`x`>>fs[option_lookup_def]>>
      CASE_TAC>>fs[])
    >~[`FP`]
    >- ( (* FP *)
      Cases_on`f`>>
      fs[next_var_rename_def,ssa_cc_trans_inst_def,inst_def,assign_def
        ,evaluate_def,get_fp_var_def,set_var_def,every_var_def
        ,every_var_inst_def,set_fp_var_def]
      >~[ `FPMovFromReg`]
      >- (
        rw[]
        >~[`Move`]
        >- (
*)
          (* Nasty special case for 32-bit FPMovFromReg *)
(* HOL4 ML code, not ported:
          Cases_on`get_var n0 st`>>fs[]>>
          Cases_on`x`>>fs[]>>
          Cases_on`get_var n1 st`>>fs[]>>
          Cases_on`x`>>fs[]>>
          imp_res_tac ssa_locals_rel_get_var>>
          gvs[evaluate_def,domain_lookup,get_vars_def,get_var_def
            ,inst_def,set_vars_def,alist_insert_def,lookup_insert
            ,set_fp_var_def]>>
          gvs[ssa_locals_rel_def,lookup_insert,AllCaseEqs()]>>
          rw[]
          >-  metis_tac[]>>
          first_x_assum drule>>
          rw[domain_lookup]>>
          gvs[ssa_map_ok_def]>>
          first_x_assum drule>>fs[])>>
        fs[next_var_rename_def,ssa_cc_trans_inst_def,inst_def,assign_def
          ,evaluate_def,get_fp_var_def,set_var_def,every_var_def
          ,every_var_inst_def,set_fp_var_def]>>
        every_case_tac>>
        fs[next_var_rename_def,ssa_cc_trans_inst_def,inst_def,assign_def
          ,evaluate_def,get_fp_var_def,set_var_def,every_var_def
          ,every_var_inst_def,set_fp_var_def]>>
        imp_res_tac ssa_locals_rel_get_var>>
        fs[ssa_locals_rel_set_var]>>
        rveq>>fs[state_component_equality])>>
      every_case_tac>>
      fs[next_var_rename_def,ssa_cc_trans_inst_def,inst_def,assign_def
        ,evaluate_def,get_fp_var_def,set_var_def,every_var_def
        ,every_var_inst_def,set_fp_var_def]>>
      imp_res_tac ssa_locals_rel_get_var>>
      fs[ssa_locals_rel_set_var]>>
      rveq>>fs[state_component_equality]>>
*)
      (* Special case for two writes *)
(* HOL4 ML code, not ported:
      fs[ssa_locals_rel_def]>>
      (CONJ_TAC>-
        (simp[lookup_insert]>> rw[]>>metis_tac[])
      >>
      simp[lookup_insert]>>ntac 2 strip_tac>>
      IF_CASES_TAC>>simp[]>>
      IF_CASES_TAC>>simp[]>>
      last_x_assum kall_tac>>
      first_x_assum(qspecl_then [`x'`,`y`] assume_tac)>>rfs[]>>
      strip_tac>>
      res_tac>>fs[domain_lookup,ssa_map_ok_def]>>
      res_tac>>fs[]>>
      rw[]>>fs[]))
QED
*)

(* HOL4 ML code, not ported:
Resume ssa_cc_trans_correct[Assign]:
    exp_tac2
QED
*)

(* HOL4 ML code, not ported:
Resume ssa_cc_trans_correct[Get]:
    exp_tac2
QED
*)

(* HOL4 ML code, not ported:
Resume ssa_cc_trans_correct[Set]:
    exp_tac2
QED
*)

(* HOL4 ML code, not ported:
Resume ssa_cc_trans_correct[Store]:
    exists_tac>>
    full_simp_tac(srw_ss())[]>>
    Cases_on`word_exp st e`>>full_simp_tac(srw_ss())[]>>
    Cases_on`get_var n st`>>full_simp_tac(srw_ss())[]>>
    imp_res_tac ssa_locals_rel_get_var>>
    imp_res_tac ssa_cc_trans_exp_correct>>
    rev_full_simp_tac(srw_ss())[word_state_eq_rel_def]>>
    EVERY_CASE_TAC>>full_simp_tac(srw_ss())[mem_store_def
      ,word_state_eq_rel_def]>>
    rev_full_simp_tac(srw_ss())[]>>
    qpat_x_assum`A=x'''` sym_sub_tac>>
    qpat_x_assum`A=x''` sym_sub_tac>>
    full_simp_tac(srw_ss())[]
QED
*)

(* HOL4 ML code, not ported:
Resume ssa_cc_trans_correct[MustTerminate]:
    rw[ssa_cc_trans_def]>>
    rpt(pairarg_tac>>gvs[])>>
    fs[evaluate_def,word_state_eq_rel_def]>>
    first_x_assum(qspecl_then[
    `p`,`st with <|clock:=MustTerminate_limit
      (:'a);termdep:=st.termdep-1|>`,
    `cst with <|clock:=MustTerminate_limit
      (:'a);termdep:=st.termdep-1|>`,`ssa`,`na`,`lt`] mp_tac)>>
    size_tac2>>
    impl_tac>-
     fs[every_var_def]>>
    strip_tac>>
    qexists_tac`perm'`>>simp[]>>
    IF_CASES_TAC>>fs[]>>
    rpt(pairarg_tac>>gvs[])>>
    gvs[AllCaseEqs()]
QED
*)

(* HOL4 ML code, not ported:
Resume ssa_cc_trans_correct[Call_tail]:
    exists_tac>>
    full_simp_tac(srw_ss())[MAP_ZIP]>>
    qpat_abbrev_tac`ls = GENLIST (λx.2*x) (LENGTH l)`>>
    `ALL_DISTINCT ls` by
      (full_simp_tac(srw_ss())[Abbr`ls`,ALL_DISTINCT_GENLIST]>>
      srw_tac[][]>>DECIDE_TAC)>>
    full_simp_tac(srw_ss())[]>>
    Cases_on`get_vars l st`>>full_simp_tac(srw_ss())[]>>
    imp_res_tac ssa_locals_rel_get_vars>>
    IF_CASES_TAC>>full_simp_tac(srw_ss())[]>>
    `¬bad_dest_args o1 ls` by
      (full_simp_tac(srw_ss())[Abbr`ls`,bad_dest_args_def]>>
      Cases_on`l`>>full_simp_tac(srw_ss())[GENLIST_CONS])>>
    `get_vars ls (set_vars ls x cst) = SOME x` by
      (match_mp_tac get_vars_set_vars_eq>>
      full_simp_tac(srw_ss())[Abbr`ls`,get_vars_length_lemma
        ,LENGTH_MAP]>>
      metis_tac[get_vars_length_lemma])>>
    full_simp_tac(srw_ss())[set_vars_def]>>
    EVERY_CASE_TAC>>
    full_simp_tac(srw_ss())[call_env_def,
      flush_state_def,dec_clock_def]>>
    qpat_x_assum `evaluate (q', st with <|locals := _; locals_size := _;
      stack_max := _; permute := _; clock := _|>) = _` mp_tac>>
    qpat_x_assum `evaluate (q', cst with <|locals := _; locals_size :=
      _; stack_max := _; clock := _|>) = _` mp_tac>>
    qpat_abbrev_tac`cst'=cst with <|locals:=A;locals_size := Ls;
      stack_max := SM; clock:=B|>`>>
    qpat_abbrev_tac`st'=st with <|locals:=A;locals_size := Ls;stack_max
      := SM; permute:=B;clock:=C|>`>>
    `cst' = st'` by
      (unabbrev_all_tac>>full_simp_tac(srw_ss())
        [state_component_equality])>>
    rw [] >> every_case_tac >> gvs [bad_fun_return_def]
QED
*)

(* HOL4 ML code, not ported:
Resume ssa_cc_trans_correct[Call_returning]:
    PairCases_on`x`>> full_simp_tac(srw_ss())[] >>
    Q.PAT_ABBREV_TAC`pp = ssa_cc_trans X Y Z lt` >>
    PairCases_on`pp` >> simp[] >>
    pop_assum(mp_tac o SYM o SIMP_RULE std_ss[markerTheory.Abbrev_def])
      >>
    simp_tac std_ss [ssa_cc_trans_def]>>
    LET_ELIM_TAC>>
    full_simp_tac(srw_ss())[Abbr`all_names`,evaluate_def
      ,add_ret_loc_def]>>
    ntac 7 (TOP_CASE_TAC>>full_simp_tac(srw_ss())[])>>
    drule_then assume_tac cut_envs_domain_SUBSET>>
    `domain (FST stack_set) ≠ {}` by
      full_simp_tac(srw_ss())[Abbr`stack_set`,domain_fromAList
        ,toAList_not_empty,nummaps_to_nummap]>>
    `ALL_DISTINCT regs` by
      fs[Abbr`regs`,ALL_DISTINCT_GENLIST]>>
    `¬bad_dest_args o1 conv_args` by
      (full_simp_tac(srw_ss())[Abbr`conv_args`,Abbr`names`
        ,bad_dest_args_def]>>
      Cases_on`l`>>full_simp_tac(srw_ss())[GENLIST_CONS])>>
    Q.SPECL_THEN [`st`,`ssa`,`na+2`,`ls`,`cst`]
      mp_tac list_next_var_rename_move_preserve>>
    impl_tac>- (
      srw_tac[][]
      >-
        (match_mp_tac ssa_locals_rel_more>>
        full_simp_tac(srw_ss())[]>>DECIDE_TAC)
      >- (
        gvs[Abbr`ls`,toAList_domain,SUBSET_DEF,domain_union]>>
        metis_tac[])
      >-
        full_simp_tac(srw_ss())[Abbr`ls`,ALL_DISTINCT_MAP_FST_toAList]
      >-
        (match_mp_tac ssa_map_ok_more>>
        full_simp_tac(srw_ss())[]>>DECIDE_TAC)) >>
    LET_ELIM_TAC>>full_simp_tac(srw_ss())[]>>
    Q.ISPECL_THEN [`ls`,`ssa`,`na`,`stack_mov`,`ssa'`,`na'`] assume_tac
      list_next_var_rename_move_props_2>>
    Q.ISPECL_THEN [`ls`,`ssa_cut`,`na'`,`ret_mov`,`ssa''`,`na''`]
      assume_tac list_next_var_rename_move_props_2>>
    Q.ISPECL_THEN
      [`x3`,`ssa_2_p`,`na_2_p`,`lt`,`ren_ret_handler`,`ssa_2`,`na_2`]
      assume_tac ssa_cc_trans_props>>
    rev_full_simp_tac(srw_ss())[]>>
    full_simp_tac(srw_ss())[MAP_ZIP]>>
    `ALL_DISTINCT conv_args` by
      (full_simp_tac(srw_ss())[Abbr`conv_args`,ALL_DISTINCT_GENLIST]>>
      srw_tac[][]>>DECIDE_TAC)>>
*)
    (*Establish invariants about ssa_cut to use later*)
(* HOL4 ML code, not ported:
    `domain ssa_cut = domain x1 ∪ domain x2` by (
      full_simp_tac(srw_ss())[EXTENSION,Abbr`ssa_cut`,domain_inter
        ,domain_union]>>
      srw_tac[][EQ_IMP_THM]>>
      gvs[SUBSET_DEF]>>
      first_x_assum drule>>
      fs[ssa_locals_rel_def]>>
      metis_tac[domain_lookup])>>
    `∀x y. lookup x ssa_cut = SOME y ⇒ lookup x ssa' = SOME y` by
      (srw_tac[][]>>full_simp_tac(srw_ss())[Abbr`ssa_cut`
        ,lookup_inter]>>
      EVERY_CASE_TAC>>full_simp_tac(srw_ss())[])>>
    `ssa_map_ok na' ssa_cut` by
      full_simp_tac(srw_ss())[Abbr`ssa_cut`,ssa_map_ok_inter]>>
*)
    (*Probably need to case split here to deal with the 2 cases*)
(* HOL4 ML code, not ported:
    Cases_on`o0`>>full_simp_tac(srw_ss())[]
    >- (
      qpat_x_assum`A=pp0`
        (sym_sub_tac)>>full_simp_tac(srw_ss())[Abbr`prog`]>>
      qpat_x_assum`A=stack_mov`
        (sym_sub_tac)>>full_simp_tac(srw_ss())[]>>
      full_simp_tac(srw_ss())[evaluate_def,LET_THM,Abbr`move_args`]>>
      `LENGTH conv_args = LENGTH names` by
        (unabbrev_all_tac >>full_simp_tac(srw_ss())[])>>
      full_simp_tac(srw_ss())[MAP_ZIP]>>
      imp_res_tac ssa_locals_rel_get_vars>>
      `get_vars names rcst = SOME x` by
        (fs[Abbr`names`]>>
        qpat_assum`get_vars l st = SOME x` mp_tac>>
        qid_spec_tac`x`>>
        qpat_assum`ssa_locals_rel na ssa st.locals cst.locals` mp_tac>>
        qpat_assum`!x y. lookup x st.locals = SOME y ⇒ P` mp_tac>>
        rpt(pop_assum kall_tac)>>
        Induct_on`l`>>rw[get_vars_def,get_var_def]>>
        fs[]>>
        pop_assum mp_tac>>
        ntac 2 (TOP_CASE_TAC>>fs[])>>rw[]>>
        fs[ssa_locals_rel_def]>>res_tac>>fs[domain_lookup
          ,option_lookup_def]>>
        last_x_assum(qspecl_then[`h`,`x'`] assume_tac)>>rfs[])>>
      full_simp_tac(srw_ss())[Abbr`names`]>>
      `LENGTH l = LENGTH x` by
        metis_tac[get_vars_length_lemma]>>
      `get_vars conv_args (set_vars conv_args x rcst) = SOME x` by
        (match_mp_tac get_vars_set_vars_eq>>
        full_simp_tac(srw_ss())[Abbr`ls`,get_vars_length_lemma
          ,LENGTH_MAP])>>
      full_simp_tac(srw_ss())[set_vars_def]>>
      qpat_abbrev_tac `rcst' =
        rcst with locals:= alist_insert conv_args x rcst.locals`>>
*)
      (*Important preservation step*)
(* HOL4 ML code, not ported:
      `ssa_locals_rel na' ssa' st.locals rcst'.locals` by
        (full_simp_tac(srw_ss())[Abbr`rcst'`,Abbr`conv_args`]>>
        match_mp_tac ssa_locals_rel_ignore_list_insert>>
        full_simp_tac(srw_ss())[EVERY_MEM,MEM_GENLIST]>>
        srw_tac[][]>>
        is_phy_var_tac) >>
      full_simp_tac(srw_ss())[word_state_eq_rel_def]>>
      qabbrev_tac`f = option_lookup ssa'`>>
*)
      (*Try to use cut_envs_lemma from word_live*)
(* HOL4 ML code, not ported:
      `INJ f (domain x1 ∪ domain x2) UNIV` by (
        srw_tac[][INJ_DEF]>>
        drule list_next_var_rename_move_distinct>>
        disch_then match_mp_tac>>
        simp[Abbr`ls`,ALL_DISTINCT_MAP_FST_toAList,toAList_domain
          ,domain_union])>>
      rename1`push_env yy NONE _`>>
      PairCases_on`yy`>>
      drule_at Any cut_envs_lemma>>
      disch_then (qspecl_then [`rcst'.locals`,`f`] mp_tac)>>
      impl_tac>- (
        CONJ_TAC >- metis_tac[INJ_UNION]>>
        CONJ_TAC >- metis_tac[INJ_UNION]>>
        rfs[Abbr`f`]>>
        fs[ssa_locals_rel_def,strong_locals_rel_def]>>
        ntac 1 (last_x_assum kall_tac)>>
        srw_tac[][]>>
        full_simp_tac(srw_ss())[option_lookup_def,domain_lookup]>>
        res_tac>>
        full_simp_tac(srw_ss())[]>>
        qpat_x_assum`A=SOME v` SUBST_ALL_TAC>>
        full_simp_tac(srw_ss())[]) >>
      srw_tac[][Abbr`rcst'`]>>full_simp_tac(srw_ss())[add_ret_loc_def]>>
      IF_CASES_TAC  >>
      full_simp_tac(srw_ss())[call_env_def,flush_state_def] >-
        fs [push_env_def, env_to_list_def, stack_size_def,
          stack_size_frame_def,
           state_component_equality] >>
      qpat_abbrev_tac`rcst' = rcst with locals := A`>>
      Q.ISPECL_THEN[
        `y1`,`y2`,
        `yy0`,`yy1:'a word_loc num_map`,`st with clock := st.clock-1`,
        `f`,`rcst' with clock := st.clock-1`,`NONE:(num#'a
          wordLang$prog#num#num)option`,
         `NONE:(num#'a wordLang$prog#num#num)option`,`λn. rcst.permute
           (n+1)`]
        mp_tac (GEN_ALL push_env_s_val_eq)>>
      impl_tac>-
        rev_full_simp_tac(srw_ss())[Abbr`rcst'`]>>
      strip_tac>>
      rev_full_simp_tac(srw_ss())[LET_THM,env_to_list_def
        ,dec_clock_def]>>
      qabbrev_tac `envx = push_env (yy0,yy1)
              (NONE:(num # 'a wordLang$prog #num #num)option)
              (st with <|permute := perm; clock := st.clock − 1|>) with
            <|locals := fromList2 (q) ; locals_size := r' ;
              stack_max := OPTION_MAP2 MAX (push_env (yy0,yy1) NONE
                (st with <|permute := perm; clock := st.clock -
                  1|>)).stack_max
                (OPTION_MAP2 $+(stack_size (push_env (yy0,yy1) NONE
                 (st with <|permute := perm; clock := st.clock -
                   1|>)).stack) r')|>`>>
      qpat_abbrev_tac `envy = (push_env (y1,y2) A B) with <| locals :=
        C; locals_size := lsz; stack_max := SM;
                       clock := _ |>`>>
      mp_tac evaluate_stack_swap>>
      disch_then (qspecl_then [`q'`,`envx`] mp_tac)>>
      ntac 2 FULL_CASE_TAC >- (
        srw_tac[][]>>qexists_tac`perm`>>
        full_simp_tac(srw_ss())[dec_clock_def]) >>
      `envx with stack := envy.stack = envy` by
        (unabbrev_all_tac>>
        full_simp_tac(srw_ss())[push_env_def,state_component_equality]>>
        full_simp_tac(srw_ss())[LET_THM,env_to_list_def,dec_clock_def,
          stack_size_def, stack_size_frame_def]) >>
      `s_val_eq envx.stack envy.stack` by
        (unabbrev_all_tac>> simp[] >> full_simp_tac(srw_ss())[])>>
      FULL_CASE_TAC
      >- (
        strip_tac>>pop_assum(qspec_then`envy.stack` mp_tac)>>
        impl_tac>-
          (unabbrev_all_tac>> simp[])>>
        strip_tac>>full_simp_tac(srw_ss())[]>>
        rev_full_simp_tac(srw_ss())[]>>
*)
        (*Backwards chaining*)
(* HOL4 ML code, not ported:
        IF_CASES_TAC>- (
          qexists_tac`perm`>>
          full_simp_tac(srw_ss())[Abbr`regs`])>>
        qspecl_then [`(y1,y2)`,`NONE:(num#'a
          wordLang$prog#num#num)option`,
          `(rcst' with clock := st.clock-1)`,`r with stack := st'`]
          assume_tac push_env_pop_env_s_key_eq>>
        qspecl_then [`(yy0,yy1)`,`NONE:(num#'a
          wordLang$prog#num#num)option`,
           `(st with <|permute:=perm;clock := st.clock-1|>)`,`r`]
          assume_tac push_env_pop_env_s_key_eq>>
*)
        (*This went missing somewhere..*)
(* HOL4 ML code, not ported:
        `rcst'.clock = st.clock` by
          full_simp_tac(srw_ss())[Abbr`rcst'`]>>
        pop_assum SUBST_ALL_TAC>>
        full_simp_tac(srw_ss())[Abbr`envy`,Abbr`envx`
          ,state_component_equality]>>
        rev_full_simp_tac(srw_ss())[]>>
*)
        (*Now is a good place to establish the invariant
           ssa_locals_rel*)
(* HOL4 ML code, not ported:
        `ssa_locals_rel na' ssa_cut y.locals y'.locals ∧
         word_state_eq_rel y y'` by (
          full_simp_tac(srw_ss())[state_component_equality]>>
          `s_key_eq y.stack y'.stack` by
            metis_tac[s_key_eq_trans,s_key_eq_sym] >>
          Q.ISPECL_THEN [`y'`, `y`,  `st'`, `r`]
            assume_tac (GEN_ALL pop_env_frame) >>
          rev_full_simp_tac(srw_ss())[]>>
          rpt (qpat_x_assum`_ cst = _` kall_tac)>>
          rpt (qpat_x_assum`_ rcst = _` kall_tac)>>
          rpt (qpat_x_assum`_ st = _` kall_tac)>>
          last_x_assum kall_tac>>
          fs[ssa_locals_rel_def,Abbr`ssa_cut`]>>
          CONJ_TAC  >- (
            rpt (qpat_x_assum`A=domain _` mp_tac)>>
            fs[Abbr`f`]>>
            rpt (pop_assum kall_tac)>>
            rw[]>>
            qpat_x_assum`_ ∪ _ = _` kall_tac>>
            qpat_x_assum`_ ∪ _ = _` sym_sub_tac>>
            gvs[lookup_inter,lookup_union,AllCaseEqs()
              ,option_lookup_def]>>
            metis_tac[domain_lookup])>>
          rpt gen_tac>>
          rename1`lookup xx`>>
          strip_tac>>
          `xx ∈ domain (union x1 x2)` by
            metis_tac[domain_lookup,UNION_COMM,domain_union]>>
          `xx ∈ domain ssa'` by metis_tac[ssa_cut_inter_lemma]>>
          rpt CONJ_TAC
          >- gvs[domain_union]
          >- (
            `xx ∈ domain (inter ssa' (union x1 x2))` by
              fs[domain_inter,domain_union]>>
            pop_assum mp_tac>> simp[domain_lookup]>>
            strip_tac>>
            `v = f xx` by
              full_simp_tac(srw_ss())[Abbr`f`,option_lookup_def
              ,lookup_inter,lookup_union,AllCaseEqs()]>>
            rveq>>
            full_simp_tac(srw_ss())[lookup_fromAList,lookup_union]>>
            rename1`ALOOKUP lll xx` >>
            rename1`ALOOKUP flll (f xx)` >>
            full_simp_tac(srw_ss())[push_env_def,LET_THM
              ,env_to_list_def]>>
            full_simp_tac(srw_ss())[s_key_eq_def,s_val_eq_def]>>
            Cases_on`opt`>>Cases_on`opt'`>>
            full_simp_tac(srw_ss())[s_frame_key_eq_def
              ,s_frame_val_eq_def]>>
            full_simp_tac(srw_ss())[lookup_fromAList]>>
            `flll = ZIP (MAP f (MAP FST lll), MAP SND lll)` by (
              imp_res_tac key_map_implies>>
              rev_full_simp_tac(srw_ss())[]>>
              metis_tac[ZIP_MAP_FST_SND_EQ])>>
            Q.ISPECL_THEN [`MAP SND lll`, `xx`, `MAP FST lll`,`f`]
              MP_TAC $  GEN_ALL ALOOKUP_key_remap_INJ >>
            impl_tac >- (
              simp[]>>
              irule INJ_less>>
              last_x_assum (irule_at Any)>>
              fs[domain_union,domain_fromAList,SUBSET_DEF,EXTENSION]>>
              metis_tac[])>>
            strip_tac>>fs[ZIP_MAP_FST_SND_EQ]>>
            TOP_CASE_TAC>> fs[]>>
            qpat_x_assum`strong_locals_rel f (domain x1) yy0 y1`
              mp_tac>>
            simp[strong_locals_rel_def]>>
            fs[ALOOKUP_toAList]>>
            metis_tac[domain_lookup])
          >- (
            strip_tac>>
            `xx < na` by (
               qpat_x_assum `every_var _ _` mp_tac >>
               simp[every_var_def,every_name_def,EVERY_MEM
                 ,set_MAP_FST_toAList_domain] >>
               gvs[domain_union]) >>
            intLib.ARITH_TAC))>>
        full_simp_tac(srw_ss())[AC UNION_COMM UNION_ASSOC]>>
*)
        (*We set the return variables but it is never in the
          locals so the ssa_locals_rel property is preserved*)
(* HOL4 ML code, not ported:
        `ssa_locals_rel na' ssa_cut y.locals
          (alist_insert regs l' y'.locals)` by (
          match_mp_tac ssa_locals_rel_ignore_list_insert>>
          full_simp_tac(srw_ss())[]>>
          rw[EVERY_MEM,Abbr`regs`,MEM_GENLIST]>>
          is_phy_var_tac)>>
        qspecl_then [`y`,`ssa_cut`,`na'+2`,`MAP FST (toAList (union x1
          x2))`
                     ,`(set_vars regs l' y')`] mp_tac
                     list_next_var_rename_move_preserve>>
        impl_tac>- (
          rw[set_vars_def]
          >-
            (match_mp_tac (GEN_ALL ssa_locals_rel_more)>>
            full_simp_tac(srw_ss())[]>>
            qexists_tac`na'`>>full_simp_tac(srw_ss())[]>>
            rev_full_simp_tac(srw_ss())[])
          >- (
            full_simp_tac(srw_ss())[Abbr`ls`,set_MAP_FST_toAList_domain
              ,domain_union,SUBSET_DEF,EXTENSION]>>
            metis_tac[])
          >-
            full_simp_tac(srw_ss())[ALL_DISTINCT_MAP_FST_toAList
              ,Abbr`ls`]
          >-
            (`na' ≤ na'+2`by DECIDE_TAC>>
            metis_tac[ssa_map_ok_more,Abbr`ssa_cut`,ssa_map_ok_inter])
          >>
            full_simp_tac(srw_ss())[word_state_eq_rel_def
              ,set_var_def])>>
        LET_ELIM_TAC>>
        full_simp_tac(srw_ss())[Abbr`mov_ret_handler`,evaluate_def]>>
        `LENGTH ret' = LENGTH regs ∧
          ALL_DISTINCT ret'` by (
          drule list_next_var_rename_lemma_1>>
          rw[Abbr`regs`,LENGTH_COUNT_LIST])>>
        rev_full_simp_tac(srw_ss())[LET_THM,MAP_ZIP,set_vars_def]>>
        `get_vars regs rcst'' = SOME l'` by (
          `¬ is_phy_var (na'+2)` by
            metis_tac[is_stack_var_flip,convention_partitions]>>
          first_x_assum drule>>
          strip_tac>>
          irule get_vars_eq_alist_insert>>
          rw[Abbr`regs`]
          >- (
            qexists_tac`y'.locals`>>
            rw[MEM_GENLIST]>>
            first_x_assum irule>>
            is_phy_var_tac)>>
          rw[ALL_DISTINCT_GENLIST])>>
        full_simp_tac(srw_ss())[set_vars_def,alist_insert_def]>>
        qabbrev_tac`res_st = (set_vars x0 l' y)`>>
        qpat_abbrev_tac`res_rcst = rcst'' with locals:=A`>>
        `ssa_locals_rel na_2_p ssa_2_p res_st.locals res_rcst.locals` by
          (
          unabbrev_all_tac>>
          simp[set_vars_def]>>
          irule ssa_locals_rel_list_next_var_rename>>
          simp[]>>
          first_x_assum (irule_at Any)>>
          simp[]>>
          CONJ_TAC >-
            metis_tac[convention_partitions]>>
          irule EVERY_MONOTONIC>>
          full_simp_tac (srw_ss()) [every_var_def]>>
          first_x_assum (irule_at Any)>>
          simp[])>>
        first_x_assum(qspecl_then[`x3`,`res_st`,`res_rcst`,`ssa_2_p`
          ,`na_2_p`,`lt`] mp_tac)>>
        size_tac2>>
        impl_tac>-(
          full_simp_tac(srw_ss())[word_state_eq_rel_def,Abbr`res_st`
            ,Abbr`res_rcst`,set_var_def]>>
          drule list_next_var_rename_props>>
          impl_tac >- simp[]>>
          simp[]>>
          full_simp_tac(srw_ss())[every_var_def
            ,next_var_rename_def]>>srw_tac[][]>>
          match_mp_tac every_var_mono>>
          HINT_EXISTS_TAC>>full_simp_tac(srw_ss())[]>>
          DECIDE_TAC)>>
        srw_tac[][]>>
        qspecl_then[`q'`,`push_env (yy0,yy1) (NONE:(num#'a
          wordLang$prog#num#num) option)
              (st with <|permute := perm; clock := st.clock − 1|>) with
            <|locals := fromList2 q; locals_size := r' ;
              stack_max := OPTION_MAP2 MAX (push_env (yy0,yy1) NONE
                (st with <|permute := perm; clock := st.clock -
                  1|>)).stack_max
                (OPTION_MAP2 $+ (stack_size (push_env (yy0,yy1) NONE
                  (st with
                 <|permute := perm; clock := st.clock - 1|>)).stack)
                   r')|>` ,`perm'`]
        assume_tac permute_swap_lemma>>
        rev_full_simp_tac(srw_ss())[LET_THM]>>
*)
        (*"Hot-swap" the suffix of perm, maybe move into lemma*)
(* HOL4 ML code, not ported:
        qexists_tac`λn. if n = 0:num then perm 0 else perm'' (n-1)`>>
        qpat_abbrev_tac `env1 = push_env A B C with <|locals := D ;
          locals_size := Ls; stack_max := SM|>`>>
        qpat_x_assum `A = (SOME B,C)` mp_tac>>
        qpat_abbrev_tac `env2 = push_env A B C with
                      <|locals:=D; locals_size := Ls; stack_max := SM ;
                        permute:=E|>`>>
        strip_tac>>
        `env1 = env2` by
          (unabbrev_all_tac>>
          simp[push_env_def,LET_THM,env_to_list_def
            ,state_component_equality,FUN_EQ_THM,
               stack_size_def, stack_size_frame_def])>>
        full_simp_tac(srw_ss())[Abbr`regs`]>>
        rev_full_simp_tac(srw_ss())[set_vars_def,Abbr`res_st`] )
      >- (
*)
        (*Excepting without handler*)
(* HOL4 ML code, not ported:
        full_simp_tac(srw_ss())[]>>strip_tac>>
        imp_res_tac s_val_eq_LASTN_exists>>
        first_x_assum(qspecl_then[`envy.stack`,`e0'`,`e'`,`ls'`]
          assume_tac)>>
        rev_full_simp_tac(srw_ss())[]>>
        qexists_tac`perm`>>
        `ls'''=ls' ∧ e0 = e0''` by
          (unabbrev_all_tac>>
          full_simp_tac(srw_ss())[push_env_def,env_to_list_def
            ,LET_THM]>>
          Cases_on`st.handler < LENGTH st.stack`
          >-
            (imp_res_tac LASTN_TL>>
            rev_full_simp_tac(srw_ss())[]>>full_simp_tac(srw_ss())[])
          >>
            `st.handler = LENGTH st.stack` by DECIDE_TAC>>
            rpt (qpat_x_assum `LASTN A B = C` mp_tac)>-
            simp[LASTN_LENGTH_cond])>>
        full_simp_tac(srw_ss())[]>>
        `lss = lss'` by
          (match_mp_tac LIST_EQ_MAP_PAIR>>full_simp_tac(srw_ss())[]>>
          qsuff_tac `e = e''`>-metis_tac[]>>
          unabbrev_all_tac>>
          full_simp_tac(srw_ss())[push_env_def,LET_THM
            ,env_to_list_def]>>
          `st.handler < LENGTH st.stack` by
            (SPOSE_NOT_THEN assume_tac>>
            `st.handler = LENGTH st.stack` by DECIDE_TAC>>
            ntac 2 (qpat_x_assum`LASTN A B = C` mp_tac)>>
            simp[LASTN_LENGTH2])>>
          ntac 2 (qpat_x_assum`LASTN A B = C` mp_tac)>>
          full_simp_tac(srw_ss())[LASTN_TL])>>
        metis_tac[s_val_and_key_eq,s_key_eq_sym,s_key_eq_trans])
      >>
*)
        (* 4 subgoals *)
(* HOL4 ML code, not ported:
        rw[]>>
        qexists_tac`perm`>>fs[]>>
        pop_assum(qspec_then`envy.stack` mp_tac)>>
        (impl_tac>- (unabbrev_all_tac>>full_simp_tac(srw_ss())[]))>>
        srw_tac[][]>>full_simp_tac(srw_ss())[]
)
    >> (
*)
    (*Handler reasoning*)
(* HOL4 ML code, not ported:
    qpat_x_assum`A=(pp0,pp1,pp2)` mp_tac>>
    PairCases_on`x''`>>full_simp_tac(srw_ss())[]>>
    LET_ELIM_TAC>>
    rev_full_simp_tac(srw_ss())[]>>
    qpat_x_assum`A=pp0`
      (sym_sub_tac)>>full_simp_tac(srw_ss())[Abbr`prog'`]>>
    qpat_x_assum`A=stack_mov` (sym_sub_tac)>>full_simp_tac(srw_ss())[]>>
    full_simp_tac(srw_ss())[evaluate_def,LET_THM,Abbr`move_args`]>>
    `LENGTH conv_args = LENGTH names` by
      (unabbrev_all_tac >>full_simp_tac(srw_ss())[])>>
    full_simp_tac(srw_ss())[MAP_ZIP]>>
    imp_res_tac ssa_locals_rel_get_vars>>
    `get_vars names rcst = SOME x` by
      (fs[Abbr`names`]>>
      qpat_assum`get_vars l st = SOME x` mp_tac>>
      qid_spec_tac`x`>>
      qpat_assum`ssa_locals_rel na ssa st.locals cst.locals` mp_tac>>
      qpat_assum`!x y. lookup x st.locals = SOME y ⇒ P` mp_tac>>
      rpt(pop_assum kall_tac)>>
      Induct_on`l`>>rw[get_vars_def,get_var_def]>>
      fs[]>>
      pop_assum mp_tac>>
      ntac 2 (TOP_CASE_TAC>>fs[])>>rw[]>>
      fs[ssa_locals_rel_def]>>res_tac>>fs[domain_lookup
        ,option_lookup_def]>>
      last_x_assum(qspecl_then[`h`,`x'`] assume_tac)>>rfs[])>>
    full_simp_tac(srw_ss())[Abbr`names`]>>
    `LENGTH l = LENGTH x` by
      metis_tac[get_vars_length_lemma]>>
    `get_vars conv_args (set_vars conv_args x rcst) = SOME x` by
      (match_mp_tac get_vars_set_vars_eq>>
      full_simp_tac(srw_ss())[Abbr`ls`,get_vars_length_lemma
        ,LENGTH_MAP])>>
    full_simp_tac(srw_ss())[set_vars_def]>>
    qpat_abbrev_tac `rcst' =
      rcst with locals:= alist_insert conv_args x rcst.locals`>>
*)
    (*Important preservation lemma*)
(* HOL4 ML code, not ported:
    `ssa_locals_rel na' ssa' st.locals rcst'.locals` by
      (full_simp_tac(srw_ss())[Abbr`rcst'`,Abbr`conv_args`]>>
      match_mp_tac ssa_locals_rel_ignore_list_insert>>
      full_simp_tac(srw_ss())[EVERY_MEM,MEM_GENLIST]>>
      srw_tac[][]>>
      is_phy_var_tac) >>
    full_simp_tac(srw_ss())[word_state_eq_rel_def]>>
    qabbrev_tac`f = option_lookup ssa'`>>
    `INJ f (domain x1 ∪ domain x2) UNIV` by (
      srw_tac[][INJ_DEF]>>
      drule list_next_var_rename_move_distinct>>
      disch_then match_mp_tac>>
      simp[Abbr`ls`,ALL_DISTINCT_MAP_FST_toAList,toAList_domain
        ,domain_union])>>
*)
    (*Try to use cut_env_lemma from word_live*)
(* HOL4 ML code, not ported:
    rename1`push_env yy (SOME _) _`>>
    PairCases_on`yy`>>
    drule_at Any cut_envs_lemma>>
    disch_then (qspecl_then [`rcst'.locals`,`f`] mp_tac)>>
    impl_tac>- (
      CONJ_TAC >- metis_tac[INJ_UNION]>>
      CONJ_TAC >- metis_tac[INJ_UNION]>>
      rfs[Abbr`f`]>>
      fs[ssa_locals_rel_def,strong_locals_rel_def]>>
      ntac 1 (last_x_assum kall_tac)>>
      srw_tac[][]>>
      full_simp_tac(srw_ss())[option_lookup_def,domain_lookup]>>
      res_tac>>
      full_simp_tac(srw_ss())[]>>
      qpat_x_assum`A=SOME v` SUBST_ALL_TAC>>
      full_simp_tac(srw_ss())[])>>
    srw_tac[][Abbr`rcst'`]>>full_simp_tac(srw_ss())[add_ret_loc_def]>>
    IF_CASES_TAC>>full_simp_tac(srw_ss())[call_env_def,flush_state_def]
    >- fs [push_env_def, env_to_list_def, stack_size_def,
      stack_size_frame_def,
         state_component_equality] >>
    qpat_abbrev_tac`rcst' = rcst with locals := A`>>
    Q.ISPECL_THEN[
        `y1`,`y2`,
        `yy0`,`yy1:'a word_loc num_map`,`st with clock := st.clock-1`,
        `f`,`rcst' with clock :=
          st.clock-1`,`SOME(2:num,cons_exc_handler,x''2,x''3)`,
       `SOME (x''0,x''1,x''2,x''3)`,`λn. rcst.permute (n+1)`]
      mp_tac (GEN_ALL push_env_s_val_eq)>>
    impl_tac>-
      rev_full_simp_tac(srw_ss())[Abbr`rcst'`]>>
    strip_tac>>
    rev_full_simp_tac(srw_ss())[LET_THM,env_to_list_def,dec_clock_def]>>
    qabbrev_tac `envx = push_env (yy0,yy1) (SOME (x''0,x''1,x''2,x''3))
            (st with <|permute := perm; clock := st.clock − 1|>) with
           <|locals := fromList2 (q) ; locals_size := r';
             stack_max :=
              OPTION_MAP2 MAX (push_env (yy0,yy1) (SOME
                (x''0,x''1,x''2,x''3))
               (st with <|permute := perm; clock := st.clock -
                 1|>)).stack_max
               (OPTION_MAP2 $+ (stack_size(push_env (yy0,yy1) (SOME
                 (x''0,x''1,x''2,x''3))
               (st with <|permute := perm; clock := st.clock -
                 1|>)).stack) r')|>`>>
    qpat_abbrev_tac `envy = (push_env y A B) with <| locals := C;
      locals_size := lsz; stack_max := SM;
                     clock := _ |>`>>
    mp_tac evaluate_stack_swap>>
    disch_then(qspecl_then [`q'`,`envx`] mp_tac)>>
    ntac 2 FULL_CASE_TAC>-
      (srw_tac[][]>>qexists_tac`perm`>>
       full_simp_tac(srw_ss())[dec_clock_def])>>
    `envx with stack := envy.stack = envy` by
      (unabbrev_all_tac>>
      full_simp_tac(srw_ss())[push_env_def,state_component_equality]>>
      full_simp_tac(srw_ss())[LET_THM,env_to_list_def,dec_clock_def,
        stack_size_def, stack_size_frame_def])>>
    `s_val_eq envx.stack envy.stack` by
      (unabbrev_all_tac>>full_simp_tac(srw_ss())[]>>simp[])>>
*)
    (*More props theorems that will be useful*)
(* HOL4 ML code, not ported:
    `ssa_map_ok na_2_p ssa_2_p ∧ is_alloc_var na_2_p ∧ na'' ≤ na_2_p `
      by (
      drule list_next_var_rename_props>>
      impl_tac >- simp[]>>
      simp[])>>
    full_simp_tac(srw_ss())[]>>
    drule ssa_cc_trans_props>>
    impl_keep_tac>- (
      drule next_var_rename_props>>
      impl_tac >- (
        simp[]>>
        match_mp_tac (GEN_ALL ssa_map_ok_more)>>
        first_x_assum (irule_at (Pos (el 1)))>>
        full_simp_tac(srw_ss())[]>>
        DECIDE_TAC)>>
      simp[])>>
    strip_tac>>
    FULL_CASE_TAC
    >- (
      strip_tac>>pop_assum(qspec_then`envy.stack` mp_tac)>>
      impl_tac>-
        (unabbrev_all_tac>> simp[])>>
      strip_tac>>full_simp_tac(srw_ss())[]>>
      rev_full_simp_tac(srw_ss())[]>>
      IF_CASES_TAC>- (
        qexists_tac`perm`>>
        full_simp_tac(srw_ss())[Abbr`regs`])>>
      qspecl_then [`(y1,y2)`,`SOME (2:num,cons_exc_handler,x''2,x''3)`,
        `(rcst' with clock := st.clock-1)`,`r with stack := st'`]
        assume_tac push_env_pop_env_s_key_eq>>
      qspecl_then [`(yy0,yy1)`,`SOME (x''0,x''1,x''2,x''3)`,
         `(st with <|permute:=perm;clock := st.clock-1|>)`,`r`]
        assume_tac push_env_pop_env_s_key_eq>>
      `rcst'.clock = st.clock` by
        full_simp_tac(srw_ss())[Abbr`rcst'`]>>
      pop_assum SUBST_ALL_TAC>>
      full_simp_tac(srw_ss())[Abbr`envy`,Abbr`envx`
        ,state_component_equality]>>
      rev_full_simp_tac(srw_ss())[]>>
      `ssa_locals_rel na' ssa_cut y.locals y'.locals ∧
       word_state_eq_rel y y'` by (
        full_simp_tac(srw_ss())[state_component_equality]>>
        `s_key_eq y.stack y'.stack` by
          metis_tac[s_key_eq_trans,s_key_eq_sym] >>
        Q.ISPECL_THEN [`y'`, `y`,  `st'`, `r`]
          assume_tac (GEN_ALL pop_env_frame) >>
        rev_full_simp_tac(srw_ss())[]>>
        rpt (qpat_x_assum`_ cst = _` kall_tac)>>
        rpt (qpat_x_assum`_ rcst = _` kall_tac)>>
        rpt (qpat_x_assum`_ st = _` kall_tac)>>
        last_x_assum kall_tac>>
        fs[ssa_locals_rel_def,Abbr`ssa_cut`]>>
        CONJ_TAC  >- (
          rpt (qpat_x_assum`A=domain _` mp_tac)>>
          fs[Abbr`f`]>>
          rpt (pop_assum kall_tac)>>
          rw[]>>
          qpat_x_assum`_ ∪ _ = _` kall_tac>>
          qpat_x_assum`_ ∪ _ = _` sym_sub_tac>>
          gvs[lookup_inter,lookup_union,AllCaseEqs()
            ,option_lookup_def]>>
          metis_tac[domain_lookup])>>
        rpt gen_tac>>
        rename1`lookup xx`>>
        strip_tac>>
        `xx ∈ domain (union x1 x2)` by
          metis_tac[domain_lookup,UNION_COMM,domain_union]>>
        `xx ∈ domain ssa'` by metis_tac[ssa_cut_inter_lemma]>>
        rpt CONJ_TAC
        >- gvs[domain_union]
        >- (
          `xx ∈ domain (inter ssa' (union x1 x2))` by
            fs[domain_inter,domain_union]>>
          pop_assum mp_tac>> simp[domain_lookup]>>
          strip_tac>>
          `v = f xx` by
            full_simp_tac(srw_ss())[Abbr`f`,option_lookup_def
            ,lookup_inter,lookup_union,AllCaseEqs()]>>
          rveq>>
          full_simp_tac(srw_ss())[lookup_fromAList,lookup_union]>>
          rename1`ALOOKUP lll xx` >>
          rename1`ALOOKUP flll (f xx)` >>
          full_simp_tac(srw_ss())[push_env_def,LET_THM
            ,env_to_list_def]>>
          full_simp_tac(srw_ss())[s_key_eq_def,s_val_eq_def]>>
          Cases_on`opt`>>Cases_on`opt'`>>
          full_simp_tac(srw_ss())[s_frame_key_eq_def
            ,s_frame_val_eq_def]>>
          full_simp_tac(srw_ss())[lookup_fromAList]>>
          `flll = ZIP (MAP f (MAP FST lll), MAP SND lll)` by (
            imp_res_tac key_map_implies>>
            rev_full_simp_tac(srw_ss())[]>>
            metis_tac[ZIP_MAP_FST_SND_EQ])>>
          Q.ISPECL_THEN [`MAP SND lll`, `xx`, `MAP FST lll`,`f`]
            MP_TAC $  GEN_ALL ALOOKUP_key_remap_INJ >>
          impl_tac >- (
            simp[]>>
            irule INJ_less>>
            last_x_assum (irule_at Any)>>
            fs[domain_union,domain_fromAList,SUBSET_DEF,EXTENSION]>>
            metis_tac[])>>
          strip_tac>>fs[ZIP_MAP_FST_SND_EQ]>>
          TOP_CASE_TAC>> fs[]>>
          qpat_x_assum`strong_locals_rel f (domain x1) yy0 y1` mp_tac>>
          simp[strong_locals_rel_def]>>
          fs[ALOOKUP_toAList]>>
          metis_tac[domain_lookup])
        >- (
          strip_tac>>
          `xx < na` by (
             qpat_x_assum `every_var _ _` mp_tac >>
             simp[every_var_def,every_name_def,EVERY_MEM
               ,set_MAP_FST_toAList_domain] >>
             gvs[domain_union]) >>
          intLib.ARITH_TAC))>>
      full_simp_tac(srw_ss())[AC UNION_COMM UNION_ASSOC]>>
      `ssa_locals_rel na' ssa_cut y.locals
        (alist_insert regs l' y'.locals)` by (
        match_mp_tac ssa_locals_rel_ignore_list_insert>>
        full_simp_tac(srw_ss())[]>>
        rw[EVERY_MEM,Abbr`regs`,MEM_GENLIST]>>
        is_phy_var_tac)>>
      qspecl_then [`y`,`ssa_cut`,`na'+2`,`MAP FST (toAList (union x1
        x2))`
                   ,`(set_vars regs l' y')`] mp_tac
                   list_next_var_rename_move_preserve>>
      impl_tac>- (
        rw[set_vars_def]
        >-
          (match_mp_tac (GEN_ALL ssa_locals_rel_more)>>
          full_simp_tac(srw_ss())[]>>
          qexists_tac`na'`>>full_simp_tac(srw_ss())[]>>
          rev_full_simp_tac(srw_ss())[])
        >- (
          full_simp_tac(srw_ss())[Abbr`ls`,set_MAP_FST_toAList_domain
            ,domain_union,SUBSET_DEF,EXTENSION]>>
          metis_tac[])
        >-
          full_simp_tac(srw_ss())[ALL_DISTINCT_MAP_FST_toAList,Abbr`ls`]
        >-
          (`na' ≤ na'+2`by DECIDE_TAC>>
          metis_tac[ssa_map_ok_more,Abbr`ssa_cut`,ssa_map_ok_inter])
        >>
          full_simp_tac(srw_ss())[word_state_eq_rel_def,set_var_def])>>
      LET_ELIM_TAC>>
      full_simp_tac(srw_ss())[Abbr`cons_ret_handler`
        ,Abbr`mov_ret_handler`,evaluate_def]>>
      `LENGTH ret' = LENGTH regs ∧
        ALL_DISTINCT ret'` by (
        drule list_next_var_rename_lemma_1>>
        rw[Abbr`regs`,LENGTH_COUNT_LIST])>>
      rev_full_simp_tac(srw_ss())[LET_THM,MAP_ZIP,set_vars_def]>>
      `get_vars regs rcst'' = SOME l'` by (
        `¬ is_phy_var (na'+2)` by
          metis_tac[is_stack_var_flip,convention_partitions]>>
        first_x_assum drule>>
        strip_tac>>
        irule get_vars_eq_alist_insert>>
        rw[Abbr`regs`]
        >- (
          qexists_tac`y'.locals`>>
          rw[MEM_GENLIST]>>
          first_x_assum irule>>
          is_phy_var_tac)>>
        rw[ALL_DISTINCT_GENLIST])>>
      full_simp_tac(srw_ss())[set_vars_def,alist_insert_def]>>
      qabbrev_tac`res_st = (set_vars x0 l' y)`>>
      qpat_abbrev_tac`res_rcst = rcst'' with locals:=A`>>
      `ssa_locals_rel na_2_p ssa_2_p res_st.locals res_rcst.locals` by (
        unabbrev_all_tac>>
        simp[set_vars_def]>>
        irule ssa_locals_rel_list_next_var_rename>>
        simp[]>>
        first_x_assum (irule_at Any)>>
        simp[]>>
        CONJ_TAC >-
          metis_tac[convention_partitions]>>
        irule EVERY_MONOTONIC>>
        full_simp_tac (srw_ss()) [every_var_def]>>
        first_x_assum (irule_at Any)>>
        simp[])>>
      first_x_assum(qspecl_then[`x3`,`res_st`,`res_rcst`,`ssa_2_p`
        ,`na_2_p`,`lt`] mp_tac)>>
      size_tac2>>
      impl_tac>-(
        full_simp_tac(srw_ss())[word_state_eq_rel_def,Abbr`res_st`
          ,Abbr`res_rcst`,set_var_def]>>
        drule list_next_var_rename_props>>
        impl_tac >- simp[]>>
        simp[]>>
        full_simp_tac(srw_ss())[every_var_def
          ,next_var_rename_def]>>srw_tac[][]>>
        qpat_x_assum`every_var _ x3` mp_tac>>
        qspecl_then [`λx. x < na`, `x3`, `λx. x < na_2_p`] mp_tac
          wordConvsTheory.every_var_mono>>
        rw[]>>
        first_x_assum match_mp_tac>>
        rw[]>>
        DECIDE_TAC)>>
      srw_tac[][]>>
      qspecl_then[`q'`,`push_env (yy0,yy1) (SOME (x''0,x''1,x''2,x''3))
                  (st with <|permute := perm; clock := st.clock − 1|>)
                    with
                <|locals := fromList2 q; locals_size := r';
                  stack_max := OPTION_MAP2 MAX (push_env (yy0,yy1) (SOME
                    (x''0,x''1,x''2,x''3))
                    (st with <|permute := perm; clock := st.clock -
                      1|>)).stack_max
                    (OPTION_MAP2 $+ (stack_size (push_env (yy0,yy1)
                      (SOME (x''0,x''1,x''2,x''3))  (st with
                     <|permute := perm; clock := st.clock - 1|>)).stack)
                       r')|>` ,`perm'`]
            assume_tac permute_swap_lemma>>
      rev_full_simp_tac(srw_ss())[LET_THM]>>
      qexists_tac`λn. if n = 0:num then perm 0 else perm'' (n-1)`>>
      qpat_abbrev_tac `env1 = push_env A B C with <|locals := D ;
        locals_size := Ls; stack_max := SM|>`>>
      qpat_x_assum `evaluate _ = (SOME (Result _ _), _ with permute :=
        _)` mp_tac>>
      qpat_abbrev_tac `env2 = push_env A B C with
                    <|locals:=D; locals_size := Ls; stack_max := SM ;
                      permute:=E|>`>>
      strip_tac>>
      `env1 = env2` by
        (unabbrev_all_tac>>
        simp[push_env_def,LET_THM,env_to_list_def
          ,state_component_equality,FUN_EQ_THM,
             stack_size_def, stack_size_frame_def])>>
      full_simp_tac(srw_ss())[Abbr`regs`]>>
      rev_full_simp_tac(srw_ss())[set_vars_def,Abbr`res_st`]>>
      qspecl_then [`na_3`,`ssa_2`,`ssa_3`] mp_tac
        fix_inconsistencies_correctL>>
      impl_tac>- (
        simp[]>>
        `na_2 ≤ na_3` by (
          drule next_var_rename_props>>
          impl_tac >- (rw[]>> metis_tac[ssa_map_ok_more])>>
          rw[])>>
        metis_tac[ssa_map_ok_more])>>
      rev_full_simp_tac(srw_ss())[LET_THM]>>
      strip_tac>>
      Cases_on`evaluate (x3, y with <|locals := alist_insert x0 l'
        (union (fromAList l'') (fromAList (toAList yy0))); permute :=
        perm'|>)`>>fs[]>>
      Cases_on`q''`>>fs[]>>
      Cases_on`evaluate (ren_ret_handler, rcst'' with locals :=
        alist_insert ret' l' rcst''.locals)`>>fs[]>>
      Cases_on`q''`>>fs[]>>
      rfs[Abbr`res_rcst`]>>
      qpat_x_assum`_ (evaluate (ren_ret_handler, rcst'' with locals :=
        alist_insert ret' l' rcst''.locals))` mp_tac>>
      simp[]>>strip_tac>>
      `na_2 ≤ na_3` by (
        `na_2 ≤ na_3_p` by (
          qpat_x_assum`next_var_rename x''0 ssa'' na_2 = _` mp_tac>>
          simp[next_var_rename_def]>>rw[])>>
        `(na_3_p:num) ≤ na_3` by full_simp_tac(srw_ss())[]>>
        DECIDE_TAC)>>
      `ssa_locals_rel na_3 ssa_2 r''.locals r'³'.locals` by (
        match_mp_tac (GEN_ALL ssa_locals_rel_more)>>
        qexists_tac`na_2`>>simp[])>>
      qpat_x_assum`∀stL cstL. ssa_locals_rel na_3 ssa_2 _ _ ⇒ _`
        (qspecl_then[`r''`,`r'³'`] mp_tac)>>
      simp[]>>
      Cases_on`evaluate(ret_cons,r'³')`>>fs[word_state_eq_rel_def]>>
      rw[]>>fs[]
)
    >- (
      full_simp_tac(srw_ss())[]>>strip_tac>>
      imp_res_tac s_val_eq_LASTN_exists>>
      first_x_assum(qspecl_then[`envy.stack`,`e0'`,`e'`,`ls'`]
        assume_tac)>>
      rev_full_simp_tac(srw_ss())[]>>
      unabbrev_all_tac>>
      full_simp_tac(srw_ss())[push_env_def,LET_THM,env_to_list_def]>>
      rpt (qpat_x_assum `LASTN A B = C` mp_tac)>>
      simp[LASTN_LENGTH_cond]>>
      rpt strip_tac>>
      full_simp_tac(srw_ss())[domain_fromAList]>>
      imp_res_tac list_rearrange_keys>>
      `set (MAP FST lss') = domain y2` by (
        qpat_x_assum`A=MAP FST lss'` (SUBST1_TAC o SYM)>>
        qpat_x_assum`set _ = set _` mp_tac>>
        qpat_x_assum`set _ = set _` mp_tac>>
        rpt (pop_assum kall_tac)>>
        simp[EXTENSION,MEM_MAP,sort_MEM,MEM_toAList,EXISTS_PROD
          ,domain_lookup])>>
      `domain yy1 = set (MAP FST lss)` by (
        qpat_x_assum `A = MAP FST lss` (SUBST1_TAC o SYM)>>
        full_simp_tac(srw_ss())[EXTENSION,MEM_MAP,sort_MEM,MEM_toAList
          ,EXISTS_PROD,domain_lookup])>>
      full_simp_tac(srw_ss())[word_state_eq_rel_def]>>
      rev_full_simp_tac(srw_ss())[]>>
      full_simp_tac(srw_ss())[domain_union,domain_fromAList]>>
      IF_CASES_TAC>-
        (qexists_tac`perm`>>full_simp_tac(srw_ss())[])>>
      `set (MAP FST e0'') = domain y1` by
        metis_tac[set_MAP_FST_toAList_domain]>>
      full_simp_tac(srw_ss()) [AC UNION_COMM UNION_ASSOC]>>
      qabbrev_tac`ssa_cut = inter ssa' (union x1 x2)`>>
      qpat_abbrev_tac`cres=r with <|locals:= A;stack :=
        B;handler:=C|>`>>
      `ssa_locals_rel na' ssa_cut r.locals cres.locals ∧
       word_state_eq_rel r cres` by (
        `r.stack = st'` by metis_tac[s_key_eq_trans,s_val_and_key_eq]>>
        full_simp_tac(srw_ss())[Abbr`cres`,LET_THM,ssa_locals_rel_def
          ,state_component_equality,word_state_eq_rel_def]>>
        simp[Abbr`ssa_cut`]>>
        rpt (qpat_x_assum`_ cst = _` kall_tac)>>
        rpt (qpat_x_assum`_ rcst = _` kall_tac)>>
        rpt (qpat_x_assum`_ st = _` kall_tac)>>
        last_x_assum kall_tac>>
        CONJ_TAC  >- (
          rw[]>>
          gvs[lookup_inter,lookup_union,AllCaseEqs(),option_lookup_def
            ,domain_union,domain_fromAList]>>
          metis_tac[domain_lookup])>>
        rpt gen_tac>>
        rename1`lookup xx`>>
        strip_tac>>
        full_simp_tac (srw_ss()) [MAP_FST_keys_SORT]>>
        `domain (fromAList lss) = domain yy1 ∧
          domain (fromAList e0) = domain yy0` by
          metis_tac[domain_fromAList,set_MAP_FST_toAList_domain]>>
        CONJ_ASM1_TAC >- (
          CONJ_ASM2_TAC >- (
            qpat_x_assum `_ ∩ _ = _` mp_tac>>
            fs[EXTENSION,domain_union]>>
            metis_tac[domain_union])>>
          gvs[lookup_union,AllCaseEqs(),domain_union]>>
          metis_tac[domain_lookup])>>
        CONJ_TAC >- (
          `xx ∈ domain (inter ssa' (union x1 x2))` by
            fs[domain_inter]>>
          pop_assum mp_tac>> simp[domain_lookup]>>
          strip_tac>>
          `v = (option_lookup ssa') xx` by
            full_simp_tac(srw_ss())[option_lookup_def,lookup_inter
            ,lookup_union,AllCaseEqs()]>>
          rveq>>
          full_simp_tac(srw_ss())[lookup_fromAList,lookup_union]>>
          rename1`ALOOKUP lll xx` >>
          rename1`ALOOKUP flll (f xx)` >>
          `flll = ZIP (MAP f (MAP FST lll), MAP SND lll)` by (
            imp_res_tac key_map_implies>>
            rev_full_simp_tac(srw_ss())[]>>
            metis_tac[ZIP_MAP_FST_SND_EQ])>>
          Q.ISPECL_THEN [`MAP SND lll`, `xx`, `MAP FST lll`,`f`]
            MP_TAC $  GEN_ALL ALOOKUP_key_remap_INJ >>
          impl_tac >- (
            simp[]>>
            irule INJ_less>>
            last_x_assum (irule_at Any)>>
            fs[domain_union,domain_fromAList,SUBSET_DEF,EXTENSION]>>
            metis_tac[])>>
          strip_tac>>fs[ZIP_MAP_FST_SND_EQ]>>
          TOP_CASE_TAC>> fs[]>>
          qpat_x_assum`strong_locals_rel f (domain x1) yy0 y1` mp_tac>>
          simp[strong_locals_rel_def]>>
          fs[ALOOKUP_toAList]>>
          metis_tac[domain_lookup])>>
        strip_tac>>
        `xx < na` by (
          qpat_x_assum `every_var _ _` mp_tac >>
          fs[every_var_def,every_name_def,EVERY_MEM
            ,set_MAP_FST_toAList_domain,domain_union] >>
          ASM_SET_TAC[]) >>
        qpat_x_assum`_ ≤ na'` mp_tac>>
        pop_assum mp_tac>>
        rpt(pop_assum kall_tac)>>
        intLib.ARITH_TAC
)>>
      `ssa_locals_rel na' ssa_cut r.locals
        (set_var 2 w0 cres).locals` by
        (match_mp_tac ssa_locals_rel_ignore_set_var>>
        full_simp_tac(srw_ss())[]>>srw_tac[][]>> is_phy_var_tac)>>
      Q.SPECL_THEN [`r`,`ssa_cut`,`na'+2`,`(MAP FST (toAList (union x1
        x2)))`
                   ,`(set_var 2 w0 cres)`] mp_tac
                   list_next_var_rename_move_preserve>>
      impl_tac>- (
        srw_tac[][]
        >-
          (match_mp_tac (GEN_ALL ssa_locals_rel_more)>>
          full_simp_tac(srw_ss())[]>>
          qexists_tac`na'`>>full_simp_tac(srw_ss())[]>>
          rev_full_simp_tac(srw_ss())[])
        >-
          full_simp_tac(srw_ss())[domain_fromAList
            ,set_MAP_FST_toAList_domain,domain_union]
        >-
          full_simp_tac(srw_ss())[ALL_DISTINCT_MAP_FST_toAList]
        >-
          (`na' ≤ na'+2`by DECIDE_TAC>>
          metis_tac[ssa_map_ok_more,Abbr`ssa_cut`,ssa_map_ok_inter])
        >>
          full_simp_tac(srw_ss())[word_state_eq_rel_def,set_var_def])>>
      LET_ELIM_TAC>>
      rev_full_simp_tac(srw_ss())[LET_THM,evaluate_def]>>
      `get_vars [2] rcst' = SOME [w0]` by
        (full_simp_tac(srw_ss())[ssa_map_ok_more,DECIDE ``na:num ≤
          na+2``]>>
        `¬ is_phy_var (na'+2)` by
          metis_tac[is_stack_var_flip,convention_partitions]>>
        full_simp_tac(srw_ss())[get_vars_def,get_var_def]>>
        first_x_assum(qspec_then`2` assume_tac)>>
        full_simp_tac(srw_ss())[is_phy_var_def,set_var_def])>>
      full_simp_tac(srw_ss())[set_vars_def,alist_insert_def]>>
      qabbrev_tac`res_st = (set_var x''0 w0 r)`>>
      qpat_abbrev_tac`res_rcst = rcst'' with locals:=A`>>
      `ssa_locals_rel na_3_p ssa_3_p res_st.locals res_rcst.locals` by (
        unabbrev_all_tac>>
        full_simp_tac(srw_ss())[next_var_rename_def,set_var_def]>>
        rpt VAR_EQ_TAC>>
        qpat_x_assum`A=union _ _` sym_sub_tac>>
        match_mp_tac ssa_locals_rel_set_var>>
        `na'' ≤ n'` by DECIDE_TAC>>
        CONJ_TAC >-
          metis_tac[ssa_locals_rel_more] >>
        CONJ_TAC >-
          metis_tac[ssa_map_ok_more] >>
        full_simp_tac(srw_ss())[every_var_def]>>
        DECIDE_TAC)>>
      first_x_assum(qspecl_then[`x''1`,`res_st`,`res_rcst`,`ssa_3_p`
        ,`na_3_p`,`lt`] mp_tac)>>
      size_tac2>>
      impl_tac>-
        (full_simp_tac(srw_ss())[word_state_eq_rel_def,Abbr`res_st`
          ,Abbr`res_rcst`,set_var_def]>>
        full_simp_tac(srw_ss())[every_var_def
          ,next_var_rename_def]>>srw_tac[][]>>
        rev_full_simp_tac(srw_ss())[]>>
        match_mp_tac every_var_mono>>
        HINT_EXISTS_TAC>>full_simp_tac(srw_ss())[]>>
        DECIDE_TAC)>>
      srw_tac[][]>>
      qspecl_then[`q'`,`push_env (yy0,yy1) (SOME (x''0,x''1,x''2,x''3))
            (st with <|permute := perm; clock := st.clock − 1|>) with
          <| locals := fromList2 q; locals_size := r';
             stack_max :=  OPTION_MAP2 MAX (OPTION_MAP2 MAX st.stack_max
          (stack_size (StackFrame st.locals_size (toAList yy0)
            (list_rearrange (perm 0)(sort key_val_compare (toAList
              yy1)))
            (SOME (st.handler,x''2,x''3))::st.stack)))
        (OPTION_MAP2 $+ (stack_size (StackFrame st.locals_size (toAList
          yy0)
         (list_rearrange (perm 0)(sort key_val_compare (toAList yy1)))
      (SOME (st.handler,x''2,x''3))::st.stack)) r')|>`,`perm'`]
        assume_tac permute_swap_lemma>>
      rev_full_simp_tac(srw_ss())[LET_THM,push_env_def
        ,env_to_list_def]>>
*)
      (*"Hot-swap" the suffix of perm, maybe move into lemma*)
(* HOL4 ML code, not ported:
      qexists_tac`λn. if n = 0:num then perm 0 else perm'' (n-1)`>>
      qpat_abbrev_tac `env1 = st with <|locals:= A; locals_size := Ls;
        stack:= B;stack_max := SM;
         permute:= C; handler:=D;clock:=E|>`>>
      qpat_x_assum `A = (SOME B,C)` mp_tac>>
      qpat_abbrev_tac `env2 = st with <|locals:= A; locals_size := Ls;
        stack:= B; stack_max := SM;
        permute:= C; handler:=D;clock:=E|>`>>
      strip_tac>>
      `env1 = env2` by
        (unabbrev_all_tac>>
        rpt(pop_assum kall_tac)>>
        simp[state_component_equality,FUN_EQ_THM, stack_size_def,
          stack_size_frame_def])>>
      full_simp_tac(srw_ss())[]>>
      EVERY_CASE_TAC>>full_simp_tac(srw_ss())[]>>
      Cases_on`evaluate(x''1,res_st with permute:=perm')`>>
      Cases_on`evaluate(ren_exc_handler,res_rcst)`>>full_simp_tac(srw_ss
        ())[]>>
    (
      Cases_on`q'³'`>>fs[]>>
      Cases_on`q''`>>fs[]>>
      rename1`fix_inconsistencies prio _ _`>>
      Q.SPECL_THEN [`na_3`,`ssa_2`,`ssa_3`,`prio`] assume_tac
        fix_inconsistencies_correctR >>
      rev_full_simp_tac(srw_ss())[LET_THM]>>
      pop_assum (qspecl_then[`r''`,`r'³'`] mp_tac)>>
      impl_tac>-
        (metis_tac[ssa_locals_rel_more,ssa_map_ok_more])>>
      Cases_on`evaluate(exc_cons,r'³')`>>fs[word_state_eq_rel_def]
)
)
    >> (
      srw_tac[][]>>qexists_tac`perm`>>full_simp_tac(srw_ss())[]>>
      first_x_assum(qspec_then`envy.stack` mp_tac)>>
      (impl_tac>- (unabbrev_all_tac>>full_simp_tac(srw_ss())[]))>>
      srw_tac[][]>>full_simp_tac(srw_ss())[])
)
QED
*)

(* HOL4 ML code, not ported:
Resume ssa_cc_trans_correct[Seq]:
    srw_tac[][]>>full_simp_tac(srw_ss())[evaluate_def,ssa_cc_trans_def
      ,LET_THM]>>
    last_assum(qspecl_then[`p`,`st`,`cst`,`ssa`,`na`,`lt`] mp_tac)>>
    size_tac2>>
    impl_tac>>full_simp_tac(srw_ss())[every_var_def]>>srw_tac[][]>>
    Cases_on`ssa_cc_trans p ssa na
      lt`>>Cases_on`r`>>full_simp_tac(srw_ss())[]>>
    Cases_on`ssa_cc_trans p0 q' r'
      lt`>>Cases_on`r`>>full_simp_tac(srw_ss())[]>>
    full_simp_tac(srw_ss())[evaluate_def,LET_THM]>>
    Cases_on`evaluate(p,st with
      permute:=perm')`>>full_simp_tac(srw_ss())[]
    >- (qexists_tac`perm'`>>full_simp_tac(srw_ss())[]) >>
    Cases_on`evaluate(q,cst)`>>full_simp_tac(srw_ss())[]>>
    reverse (Cases_on`q'''''`)
    >-
      (qexists_tac`perm'`>>srw_tac[][]>>full_simp_tac(srw_ss())[]>>
       Cases_on`x`>>fs[]>>
       every_case_tac>>fs[]>>
       imp_res_tac ssa_cc_trans_props>>
       metis_tac[ssa_locals_rel_more])
    >>
    full_simp_tac(srw_ss())[]>>
    first_assum(qspecl_then[`p0`,`r`,`r'''`,`q'`,`r'`,`lt`] mp_tac)>>
    size_tac2>>
    impl_tac>-
      (rev_full_simp_tac(srw_ss())[]>>imp_res_tac ssa_cc_trans_props>>
      full_simp_tac(srw_ss())[]>>
      match_mp_tac every_var_mono>>
      HINT_EXISTS_TAC>>
      full_simp_tac(srw_ss())[]>>DECIDE_TAC)>>
    srw_tac[][]>>
    qspecl_then[`p`,`st with permute:=perm'`,`perm''`]
      assume_tac permute_swap_lemma>>
    rev_full_simp_tac(srw_ss())[LET_THM]>>
    qexists_tac`perm'''`>>srw_tac[][]>>full_simp_tac(srw_ss())[]
QED
*)

(* HOL4 ML code, not ported:
Resume ssa_cc_trans_correct[If]:
    qpat_abbrev_tac `A = ssa_cc_trans B C D E` >>
    PairCases_on`A`>>simp[]>>
    pop_assum(mp_tac o SYM o SIMP_RULE std_ss[markerTheory.Abbrev_def])
      >>
    full_simp_tac(srw_ss())[evaluate_def,ssa_cc_trans_def]>>
    LET_ELIM_TAC>>fs[]>>
    qpat_x_assum`B = A0`
      sym_sub_tac>>full_simp_tac(srw_ss())[evaluate_def]>>
    Cases_on `get_var n st` >> gvs [] >>
    Cases_on `get_var_imm r st` >> gvs [] >>
    imp_res_tac ssa_locals_rel_get_var >> gvs [Abbr `r1'`] >>
    `get_var_imm ri' cst = SOME x'` by (
      Cases_on `r` >> gvs [Abbr `ri'`, get_var_imm_def] >>
      metis_tac [ssa_locals_rel_get_var]) >>
    gvs [] >>
    Cases_on `word_cmp c x x'` >> gvs [] >>
    Cases_on `x''` >> gvs []
    >- (
      first_assum(qspecl_then[`p`,`st`,`cst`,`ssa`,`na`,`lt`] mp_tac)>>
      size_tac2>>
      impl_tac>-
        (rev_full_simp_tac(srw_ss())[]>>imp_res_tac ssa_cc_trans_props>>
        full_simp_tac(srw_ss())[every_var_def])>>
      srw_tac[][]>>
      qexists_tac`perm'`>>full_simp_tac(srw_ss())[LET_THM]>>
      Cases_on`evaluate(p,st with permute := perm')`>>
      Cases_on`evaluate(e2',cst)`>>full_simp_tac(srw_ss())[]>>
      gvs[] >>
      Cases_on`q`>>full_simp_tac(srw_ss())[]>>rev_full_simp_tac(srw_ss
        ())[]>>
      Q.SPECL_THEN [`na3`,`ssa2`,`ssa3`] mp_tac
        fix_inconsistencies_correctL>>
      impl_tac>-
        (imp_res_tac ssa_cc_trans_props>>
        metis_tac[ssa_map_ok_more])>>
      rev_full_simp_tac(srw_ss())[LET_THM]>>
      disch_then (qspecl_then[`r'`,`r''`] mp_tac)>>
      impl_tac>-
        (imp_res_tac ssa_cc_trans_props>>
        metis_tac[ssa_locals_rel_more,ssa_map_ok_more])>>
      Cases_on`evaluate(e2_cons,r'')`>>full_simp_tac(srw_ss())
        [word_state_eq_rel_def])
    >>
      first_assum(qspecl_then[`p0`,`st`,`cst`,`ssa`,`na2`,`lt`]
        mp_tac)>>
      size_tac2>>
      impl_tac>-
        (rev_full_simp_tac(srw_ss())[]>>imp_res_tac
          ssa_cc_trans_props>>srw_tac[][]
        >-
          metis_tac[ssa_locals_rel_more]
        >-
          (full_simp_tac(srw_ss())[every_var_def]>>match_mp_tac
            every_var_mono>>
          Q.EXISTS_TAC`λx.x<na`>>full_simp_tac(srw_ss())[] >>
          DECIDE_TAC)
        >>
          metis_tac[ssa_map_ok_more])
      >>
      srw_tac[][]>>
      qexists_tac`perm'`>>full_simp_tac(srw_ss())[LET_THM]>>
      Cases_on`evaluate(p0,st with permute := perm')`>>
      Cases_on`evaluate(e3',cst)`>>full_simp_tac(srw_ss())[]>>
      Cases_on`q'`>>full_simp_tac(srw_ss())[]>>rev_full_simp_tac(srw_ss
        ())[]>>
      rename1`fix_inconsistencies prio _ _`>>
      Q.SPECL_THEN [`na3`,`ssa2`,`ssa3`,`prio`] mp_tac
        fix_inconsistencies_correctR>>
      impl_tac>-
        (imp_res_tac ssa_cc_trans_props>>
        metis_tac[ssa_map_ok_more])>>
      rev_full_simp_tac(srw_ss())[LET_THM]>>srw_tac[][]>>
      pop_assum (qspecl_then[`r'`,`r''`] mp_tac)>>
      impl_tac>-
        (imp_res_tac ssa_cc_trans_props>>
        metis_tac[ssa_locals_rel_more,ssa_map_ok_more])>>
      Cases_on`evaluate(e3_cons,r'')`>>full_simp_tac(srw_ss())
        [word_state_eq_rel_def]
QED
*)

(* HOL4 ML code, not ported:
Resume ssa_cc_trans_correct[Alloc]:
    last_x_assum kall_tac>>
    qabbrev_tac`A = ssa_cc_trans (Alloc n p) ssa na lt`>>
    PairCases_on`A`>>full_simp_tac(srw_ss())[ssa_cc_trans_def]>>
    pop_assum mp_tac>>
    LET_ELIM_TAC>>full_simp_tac(srw_ss())[]>>
    full_simp_tac(srw_ss())[evaluate_def]>>
    FULL_CASE_TAC>>Cases_on`x`>>full_simp_tac(srw_ss())[alloc_def]>>
    FULL_CASE_TAC>>full_simp_tac(srw_ss())[]>>
    Q.SPECL_THEN [`st`,`ssa`,`na+2`,`ls`,`cst`] mp_tac
      list_next_var_rename_move_preserve>>
    impl_keep_tac>-
      (srw_tac[][]
      >-
        (match_mp_tac ssa_locals_rel_more>>
        full_simp_tac(srw_ss())[]>>DECIDE_TAC)
      >-
        (
       full_simp_tac(srw_ss())[cut_envs_def,Abbr`ls`,Abbr`all_names`
         ,AllCaseEqs()] >>
       rveq >>
       full_simp_tac(srw_ss())[set_MAP_FST_toAList_domain,domain_union]
         >>
       full_simp_tac(srw_ss())[cut_names_def])
      >-
        full_simp_tac(srw_ss())[Abbr`ls`,ALL_DISTINCT_MAP_FST_toAList]
      >-
        (match_mp_tac ssa_map_ok_more>>
        full_simp_tac(srw_ss())[]))>>
    LET_ELIM_TAC>>
    qpat_x_assum`A=A0` sym_sub_tac>>
    qpat_x_assum`A=A1` sym_sub_tac>>
    qpat_x_assum`A=A2` sym_sub_tac>>
    full_simp_tac(srw_ss())[Abbr`prog`,evaluate_def]>>
    simp_tac(srw_ss())[Once LET_THM] >>
    rev_full_simp_tac(srw_ss())[Abbr`num'`]>>full_simp_tac(srw_ss())[]>>
    Q.ISPECL_THEN [`ls`,`ssa`,`na+2`,`mov`,`ssa'`,`na'`] assume_tac
      list_next_var_rename_move_props>>
    `is_stack_var (na+2)` by
      full_simp_tac(srw_ss())[is_alloc_var_flip]>>
    rev_full_simp_tac(srw_ss())[]>>full_simp_tac(srw_ss())[]>>
    imp_res_tac ssa_locals_rel_get_var>>
    full_simp_tac(srw_ss())[get_vars_def,get_var_def,set_vars_def
      ,alist_insert_def,Once LET_THM]>>
    qpat_abbrev_tac `rcstlocs = insert 2 A rcst.locals`>>
    full_simp_tac(srw_ss())[alloc_def]>>
    PairCases_on`p`>>
    PairCases_on`x`>>
    `INJ (option_lookup ssa') (domain p0 UNION domain p1 ) 𝕌(:num)` by(
      rw[INJ_DEF] >> (
        drule list_next_var_rename_move_distinct>>
        disch_then match_mp_tac>>
        simp[Abbr`ls`,ALL_DISTINCT_MAP_FST_toAList,toAList_domain
          ,Abbr`all_names`,domain_union])) >>
    drule_at Any cut_envs_lemma>>
    disch_then (qspecl_then [`rcstlocs`,`option_lookup ssa'`] mp_tac)>>
    impl_tac>- (
      gvs[ssa_locals_rel_def,strong_locals_rel_def]>>
      rw[]
      >- (
        drule INJ_UNION >> simp[])
      >- (
        drule INJ_UNION >> simp[])
      >>
        full_simp_tac(srw_ss())[option_lookup_def,domain_lookup
          ,Abbr`rcstlocs`,lookup_insert]>>
        last_x_assum kall_tac>>
        res_tac>>
        full_simp_tac(srw_ss())[ssa_map_ok_def]>>
        first_x_assum(qspecl_then [`n'`,`v'`] mp_tac)>>
        simp[]>>
        qpat_x_assum`A=SOME v'`
          SUBST_ALL_TAC>>full_simp_tac(srw_ss())[]>>
        srw_tac[][is_phy_var_def])>>
    srw_tac[][]>>full_simp_tac(srw_ss())[set_store_def]>>
    qpat_abbrev_tac`non = NONE`>>
    Q.ISPECL_THEN [`y1`,`y2`,`x0`,`x1`,`st with store:= st.store |+
      (AllocSize,Word c)`
    ,`option_lookup ssa'`,`rcst with store:= rcst.store |+
      (AllocSize,Word c)`
    ,`non`,`non`,`rcst.permute`] assume_tac (GEN_ALL
      push_env_s_val_eq)>>
    rev_full_simp_tac(srw_ss())[word_state_eq_rel_def,Abbr`non`]>>
    qexists_tac`perm`>>full_simp_tac(srw_ss())[]>>
    qpat_abbrev_tac `st' = push_env x NONE A`>>
    qpat_abbrev_tac `cst' = push_env y NONE B`>>
    Cases_on`gc st'`>>full_simp_tac(srw_ss())[]>>
    Q.ISPECL_THEN [`st'`,`cst'`,`x`] mp_tac gc_s_val_eq_gen>>
    impl_keep_tac>-
      (unabbrev_all_tac>>
      full_simp_tac(srw_ss())[push_env_def,LET_THM,env_to_list_def
        ,word_state_eq_rel_def,
        stack_size_def, stack_size_frame_def]>>
      rev_full_simp_tac(srw_ss())[])>>
    srw_tac[][]>>simp[]>>
    unabbrev_all_tac>>
    imp_res_tac gc_frame>>
    Cases_on`pop_env x`>>
    rev_full_simp_tac(srw_ss())[]>>full_simp_tac(srw_ss())[]>>
    imp_res_tac push_env_pop_env_s_key_eq>>
    rev_full_simp_tac(srw_ss())[]>>full_simp_tac(srw_ss())[]>>
    imp_res_tac gc_s_key_eq>>
    full_simp_tac(srw_ss())[push_env_def,LET_THM,env_to_list_def]>>
    rpt (qpat_x_assum `s_key_eq A B` mp_tac)>>
    qpat_abbrev_tac `lsA = list_rearrange (rcst.permute 0)
        (sort key_val_compare ( (toAList y2)))`>>
    qpat_abbrev_tac `lsB = list_rearrange (perm 0)
        (sort key_val_compare ( (toAList x1)))`>>
    ntac 4 strip_tac>>
    Q.ISPECL_THEN [`x.stack`,`y`,`t'`,`NONE:(num#num#num) option`,
      `rcst.locals_size`,`toAList y1`,`lsA`,`rcst.stack`]
      mp_tac (GEN_ALL s_key_eq_val_eq_pop_env)>>
    impl_tac
    >-
      (full_simp_tac(srw_ss())[]>>metis_tac[s_key_eq_sym
        ,s_val_eq_sym])>>
    strip_tac>>full_simp_tac(srw_ss())[]>>
    Q.ISPECL_THEN [`t'.stack`,`x'`,`x`,`NONE:(num#num#num) option`,
      `st.locals_size`, `toAList x0`,`lsB`,`st.stack`]
      mp_tac (GEN_ALL s_key_eq_val_eq_pop_env)>>
    impl_tac
    >-
      (full_simp_tac(srw_ss())[]>>
      metis_tac[s_key_eq_sym,s_val_eq_sym])>>
    srw_tac[][]>>
    `LENGTH ls' = LENGTH l ∧ LENGTH lsB = LENGTH l` by
      metis_tac[s_key_eq_def,s_frame_key_eq_def,
                s_val_eq_def,LENGTH_MAP,s_frame_val_eq_def]>>
    `x'.stack = ls /\ y.stack = ls /\ s_key_eq ls st.stack /\ rest = ls
      ` by
       (rpt $ irule_at Any s_val_and_key_eq >>
        rpt $ PRED_ASSUM is_forall (K ALL_TAC) >>
        rpt $ PRED_ASSUM is_imp (K ALL_TAC) >>
        gvs[s_key_eq_def,s_val_eq_def,s_key_eq_refl,s_val_eq_refl] >>
        rpt (qpat_x_assum `s_key_eq _ _` mp_tac) >>
        rpt (qpat_x_assum `s_val_eq _ _` mp_tac) >>
        POP_ASSUM_LIST $ K ALL_TAC >>
        metis_tac[s_key_eq_trans,s_key_eq_sym,s_val_eq_trans
          ,s_val_eq_sym]) >>
    POP_ASSUM SUBST_ALL_TAC >>
    `lsz' = (toAList x0)`
       by fs[s_key_eq_def,s_frame_key_eq_def2] >>
    POP_ASSUM SUBST_ALL_TAC >>
*)
    (*Establish invariants about ssa_cut to use later*)
(* HOL4 ML code, not ported:
    qabbrev_tac `s = union p0 p1`>>
    qabbrev_tac `ssa_cut = inter ssa' s` >>
    `domain ssa_cut = domain x0 ∪ domain x1` by
      (full_simp_tac(srw_ss())[EXTENSION,Abbr`ssa_cut`,domain_inter
        ,Abbr`s`,domain_union]>>
      drule cut_envs_domain_SUBSET>>
      srw_tac[][EQ_IMP_THM]>>
      full_simp_tac(srw_ss())[SUBSET_DEF]>>
      last_x_assum kall_tac >>
      full_simp_tac(srw_ss())[ssa_locals_rel_def]>>
      metis_tac[domain_lookup])>>
    `∀x y. lookup x ssa_cut = SOME y ⇒
      lookup x ssa' = SOME y` by (
      srw_tac[][]>>full_simp_tac(srw_ss())[Abbr`ssa_cut`,lookup_inter]>>
      pop_assum mp_tac>>simp[AllCaseEqs()])>>
    `domain x'.locals = domain x0 ∪ domain x1` by (
      full_simp_tac(srw_ss())[domain_fromAList,MAP_ZIP,domain_union]>>
      full_simp_tac(srw_ss())[EXTENSION,Abbr`lsB`]>>
      full_simp_tac(srw_ss())[MEM_MAP,mem_list_rearrange,sort_MEM]>>
      srw_tac[][]>>
      full_simp_tac(srw_ss())[EXISTS_PROD,MEM_toAList,domain_lookup]>>
      metis_tac[])>>
    `ssa_locals_rel na' ssa_cut x'.locals y.locals ∧
      word_state_eq_rel x' y` by (
      CONJ_TAC
      >- (
        rpt (qpat_x_assum`_ cst = _` kall_tac)>>
        rpt (qpat_x_assum`_ rcst = _` kall_tac)>>
        rpt (qpat_x_assum`_ x = _` kall_tac)>>
        rpt (qpat_x_assum`_ t' = _` kall_tac)>>
        fs[ssa_locals_rel_def,Abbr`ssa_cut`,Abbr`s`]>>
        CONJ_TAC
        >- (
          qpat_x_assum`A=domain _` sym_sub_tac>>
          simp[lookup_inter,AllCaseEqs(),lookup_union,domain_lookup]>>
          simp[option_lookup_def,AllCaseEqs()]>>
          metis_tac[])>>
        rpt gen_tac>>
        rename1`lookup xx`>>
        `set (MAP FST lsB) = domain x1` by
          simp[Abbr`lsB`, MAP_FST_list_rearrange_keys_SORT]>>
        strip_tac >>
        `xx ∈ ((domain x0) UNION (domain x1))`
             by ( imp_res_tac$  GSYM domain_lookup >>
               fs[domain_union,domain_fromAList] >>
               rfs[MAP_ZIP] >> fs[set_MAP_FST_toAList_domain]
                 >>metis_tac[]) >>
        CONJ_TAC >- (ASM_SET_TAC[]) >>
        reverse CONJ_TAC >- (
          disch_tac >>
          `xx < na`
            by (
             qpat_x_assum `every_var _ _` mp_tac >>
             simp[every_var_def,every_name_def,EVERY_MEM
               ,set_MAP_FST_toAList_domain] >>
             ASM_SET_TAC[]) >>
          intLib.ARITH_TAC) >>
        Q.ISPECL_THEN [`MAP SND l`, `xx`, `MAP FST lsB`,`option_lookup
          ssa'`]
          MP_TAC $  GEN_ALL ALOOKUP_key_remap_INJ >>
        impl_tac >-
          (simp[] >>
          irule INJ_SUBSET >>
          Q.EXISTS_TAC `(domain p0 UNION domain p1)` >>
          first_x_assum (irule_at (Pos last)) >>
          simp[] >> ASM_SET_TAC[]) >>
        disch_tac >>
        Q.PAT_X_ASSUM `lookup xx _ = SOME _` mp_tac >>
        simp_tac(srw_ss())[lookup_union,lookup_fromAList] >>
        qmatch_asmsub_abbrev_tac `ALOOKUP  A B = ALOOKUP C D` >>
        disch_tac >>
        qmatch_goalsub_abbrev_tac `ALOOKUP C' D'` >>
        `C = C' /\ D = D'`  by (
          simp[Abbr`C`,Abbr`C'`,Abbr`D`,Abbr`D'`] >>
          simp[SimpRHS,Once $GSYM ZIP_MAP_FST_SND_EQ ] >>
          simp[] >>
          CONJ_TAC >-
            (`MAP FST l = MAP FST (MAP (λ(x,y). (option_lookup ssa'
              x,y)) lsB)`
                by fs[s_key_eq_def,s_frame_key_eq_def2] >>
            POP_ASSUM SUBST_ALL_TAC >>
            simp[MAP_MAP_o,ELIM_UNCURRY,o_DEF]) >>
          qmatch_goalsub_abbrev_tac `_ = THE C`>>
          `?y. C = SOME y`
             by (
               simp[Abbr`C`,Abbr`B`,Abbr`A`,GSYM domain_lookup] >>
               ASM_SET_TAC[domain_union]) >>
          `lookup B ssa' = C`
              by (simp[Abbr`C`] >> METIS_TAC[]) >>
          simp_tac(srw_ss())[option_lookup_def,Abbr`C`] >>
          ASM_REWRITE_TAC[] >>
          simp_tac(srw_ss())[]) >>
        ntac 2 $ POP_ASSUM (SUBST_TAC o single o GSYM) >>
        ntac 2 $ POP_ASSUM $ K ALL_TAC >>
        POP_ASSUM MP_TAC >>
        simp[AllCaseEqs(),DISJ_IMP_THM] >>
        MAP_EVERY Q.UNABBREV_TAC [`A`,`B`,`C`,`D`] >>
        strip_tac >>
        qpat_x_assum `strong_locals_rel (option_lookup ssa') (domain p0)
          x0 y1` mp_tac>>
        simp[strong_locals_rel_def] >>
        disch_then (qspec_then `xx` mp_tac) >>
        full_simp_tac(bool_ss)[ALOOKUP_toAList] >>
        simp_tac(srw_ss())[] >>
        impl_tac >- (
          EVERY_ASSUM (TRY o (mp_then.mp_then (Pos hd) mp_tac (iffLR
            ALOOKUP_NONE))) >>
          simp[MAP_ZIP] >>
          ASM_SET_TAC[]) >>
        simp_tac(srw_ss())[])
      >-
        (full_simp_tac(srw_ss())[word_state_eq_rel_def,pop_env_def]>>
        rev_full_simp_tac(srw_ss())[state_component_equality,
          stack_size_def, stack_size_frame_def]>>
        metis_tac[s_val_and_key_eq,s_key_eq_sym,s_val_eq_sym
          ,s_key_eq_trans]))>>
    ntac 3 (qpat_x_assum `A = (B,C)` mp_tac)>>
    FULL_CASE_TAC>>full_simp_tac(srw_ss())[word_state_eq_rel_def
      ,has_space_def,get_store_def]>>
    Cases_on`x''`>>full_simp_tac(srw_ss())[]>>
    Cases_on`FLOOKUP x'.store NextFree`>>full_simp_tac(srw_ss())[]>>
    Cases_on`x''`>>full_simp_tac(srw_ss())[] >>
    Cases_on`FLOOKUP x'.store TriggerGC`>>full_simp_tac(srw_ss())[]>>
    Cases_on`x''`>>full_simp_tac(srw_ss())[] >>
    IF_CASES_TAC >> full_simp_tac(srw_ss())[] >>
    ntac 2 strip_tac>> rveq >>
      full_simp_tac(srw_ss())[call_env_def,flush_state_def]
    >- (
      Q.SPECL_THEN [`rst`,`ssa_cut`,`na'+2`,`(MAP FST (toAList s))`
                   ,`s1`] mp_tac list_next_var_rename_move_preserve>>
      impl_tac>-(
        srw_tac[][]
        >-
          (rev_full_simp_tac(srw_ss())[]>>
          match_mp_tac (GEN_ALL ssa_locals_rel_more)>>
          full_simp_tac(srw_ss())[]>>
          qpat_x_assum `A = union (fromAList _) _` sym_sub_tac>>
          HINT_EXISTS_TAC>>full_simp_tac(srw_ss())[])
        >-
          (srw_tac[][SUBSET_DEF]>>
          full_simp_tac(srw_ss())[MEM_MAP,Abbr`s`]>>
          Cases_on`y`>>
          full_simp_tac(srw_ss())[MEM_toAList,domain_lookup
            ,lookup_union]>>
          pop_assum mp_tac>>simp[AllCaseEqs()]>>
          metis_tac[])
        >-
          (unabbrev_all_tac>>match_mp_tac ssa_map_ok_inter>>
          match_mp_tac (GEN_ALL ssa_map_ok_more)>>
          HINT_EXISTS_TAC>>
          full_simp_tac(srw_ss())[]>>DECIDE_TAC)
        >>
          full_simp_tac(srw_ss())[word_state_eq_rel_def])>>
      simp[] >>
      srw_tac[][]>>full_simp_tac(srw_ss())[word_state_eq_rel_def]) >>
    full_simp_tac(srw_ss())[word_state_eq_rel_def, stack_size_def,
      stack_size_frame_def] >>
    rw[state_component_equality]
QED
*)

(* HOL4 ML code, not ported:
Resume ssa_cc_trans_correct[StoreConsts]:
    exists_tac>>fs[]>>
    Cases_on`get_var n1 st`>>fs[]>>
    imp_res_tac ssa_locals_rel_get_var>>
    TOP_CASE_TAC>>simp[]>>
    Cases_on`get_var n2 st`>>fs[]>>
    imp_res_tac ssa_locals_rel_get_var>>
    TOP_CASE_TAC>>simp[]>>
    fs[next_var_rename_def,evaluate_def,get_vars_def]>>
    simp[get_var_def,set_vars_def,lookup_alist_insert]>>
    IF_CASES_TAC>>simp[set_var_def,unset_var_def,lookup_insert]>>
    `n1 ∈ domain ssa ∧ n2 ∈ domain ssa ` by
      fs[ssa_locals_rel_def,get_var_def]>>
    fs[domain_lookup,option_lookup_def]>>
    `~(is_phy_var v') ∧ ¬(is_phy_var v'')` by
      (fs[ssa_map_ok_def]>>
      metis_tac[])>>
    `EVERY is_phy_var [0;2;4;6]` by
      fs[is_phy_var_def]>>
    fs[lookup_delete]>>
    rpt(IF_CASES_TAC>>gs[])>>
    simp[lookup_alist_insert]>>
    fs[get_var_def]>>
    simp[alist_insert_def]>>
    fs[every_var_def]>>
    `na+8 = (na+4)+4` by fs[]>>
    pop_assum SUBST_ALL_TAC>>
    drule ssa_map_ok_extend >>
    disch_then(qspec_then`n2` mp_tac)>>
    impl_tac>-
      metis_tac[convention_partitions]>>
    strip_tac>>
    match_mp_tac ssa_locals_rel_insert>> simp[]>>
    metis_tac[
      ssa_locals_rel_insert,
      ssa_locals_rel_delete_left,
      ssa_locals_rel_ignore_insert,
      ssa_locals_rel_delete_right,
      ssa_locals_rel_ignore_insert]
QED
*)

(* HOL4 ML code, not ported:
Resume ssa_cc_trans_correct[Raise]:
    exists_tac>>fs[]>>
    Cases_on`get_var n st`>>imp_res_tac ssa_locals_rel_get_var>>
    full_simp_tac(srw_ss())[get_vars_def,get_var_def,set_vars_def
      ,lookup_alist_insert]>>
    full_simp_tac(srw_ss())[jump_exc_def]>>EVERY_CASE_TAC>>full_simp_tac
      (srw_ss())[]>> gvs[]
QED
*)

(* HOL4 ML code, not ported:
Resume ssa_cc_trans_correct[Return]:
    exists_tac>>fs[]>>
    Cases_on`get_var n st`>> fs[] >>
    Cases_on `x` >> fs[] >>
    Cases_on`get_vars l st`>> fs[] >>
    full_simp_tac(srw_ss())[MAP_ZIP,ALL_DISTINCT_GENLIST] >>
    imp_res_tac ssa_locals_rel_get_vars>>
    full_simp_tac(srw_ss())[]>>
    imp_res_tac ssa_locals_rel_get_var>>
    full_simp_tac(srw_ss())[]>>
    full_simp_tac(srw_ss())[set_vars_def]>>
    imp_res_tac ssa_locals_rel_ignore_list_insert>>
    ntac 4 (pop_assum kall_tac)>>
    pop_assum(qspecl_then [`x`,`(GENLIST (λx. 2 * (x + 1)) (LENGTH l))`]
      mp_tac)>>
    pop_assum kall_tac >>
    impl_tac>- (full_simp_tac(srw_ss())[LENGTH_GENLIST]>>
   imp_res_tac get_vars_length_lemma >> gvs[]) >>
    impl_tac>- full_simp_tac(srw_ss())[EVERY_GENLIST,is_phy_var_def] >>
    srw_tac[][]>>full_simp_tac(srw_ss())[alist_insert_def]>>
    qpat_abbrev_tac`rcst=cst with locals:=A`>>
    rename1 `get_var _ cst = SOME (Loc l1 l2)`>>
    Q.ISPECL_THEN [`Loc l1 l2`,`st`,`ssa`,`na`,`n`,`rcst`] assume_tac
      (GEN_ALL ssa_locals_rel_get_var)>>
    pop_assum mp_tac >>
    impl_tac >- (unabbrev_all_tac>>rfs[])>>
    strip_tac >> full_simp_tac(srw_ss())[] >>
    unabbrev_all_tac >> full_simp_tac (srw_ss())[GSYM set_vars_def] >>
    DEP_REWRITE_TAC[get_vars_set_vars_eq] >>
    fs[ALL_DISTINCT_GENLIST,LENGTH_GENLIST] >>
    CONJ_TAC >-
    (imp_res_tac get_vars_length_lemma >> gvs[]) >>
    fs[flush_state_def]
QED
*)

(* HOL4 ML code, not ported:
Resume ssa_cc_trans_correct[Tick]:
    exists_tac>>
    EVERY_CASE_TAC>>full_simp_tac(srw_ss())[call_env_def,
      flush_state_def,dec_clock_def]
QED
*)

(* HOL4 ML code, not ported:
Resume ssa_cc_trans_correct[OpCurrHeap]:
    last_x_assum kall_tac>>
    exists_tac>>
    EVERY_CASE_TAC>>full_simp_tac(srw_ss())[next_var_rename_def]>>
    imp_res_tac ssa_locals_rel_get_var>>
    imp_res_tac
      ssa_cc_trans_exp_correct>>full_simp_tac(srw_ss())
      [word_state_eq_rel_def]>>
    rev_full_simp_tac(srw_ss())[evaluate_def]>>
    fs[set_var_def,set_store_def,ssa_cc_trans_exp_def]>>
    match_mp_tac ssa_locals_rel_set_var>>
    full_simp_tac(srw_ss())[every_var_def]
QED
*)

(* HOL4 ML code, not ported:
Resume ssa_cc_trans_correct[LocValue]:
    exp_tac2
QED
*)

(* HOL4 ML code, not ported:
Resume ssa_cc_trans_correct[Install]:
    qexists_tac`cst.permute`>>
    fs[evaluate_def,word_state_eq_rel_def,ssa_cc_trans_def]>>
    last_x_assum kall_tac>>
    PairCases_on`p`>>
    pairarg_tac>>fs[case_eq_thms]>>
    pop_assum mp_tac>>pairarg_tac>>fs[]>>
    strip_tac>>
    pop_assum mp_tac >>
    rpt (TOP_CASE_TAC >> gvs []) >>
    qmatch_goalsub_abbrev_tac ‘rstt = rst ⇒ _’ >> rw [] >>
    pairarg_tac>>fs[]>>
    pop_assum mp_tac>>
    pairarg_tac>>fs[]>>
    pairarg_tac>>fs[]>>
    pairarg_tac>>fs[]>>
    qmatch_asmsub_abbrev_tac`MAP FST (toAList s)`>>
    Q.SPECL_THEN [`st`,`ssa`,`na+2`,`MAP FST (toAList s)`,`cst`] mp_tac
      list_next_var_rename_move_preserve>>
    impl_keep_tac>- (
      srw_tac[][word_state_eq_rel_def]
      >-
        (match_mp_tac ssa_locals_rel_more>>
        full_simp_tac(srw_ss())[]>>DECIDE_TAC)
      >- (
        fs[cut_env_def,AllCaseEqs()]>>
        drule cut_envs_domain_SUBSET >>
        simp[Abbr`s`,toAList_domain,SUBSET_DEF,domain_union]>>
        metis_tac[])
      >-
        full_simp_tac(srw_ss())[ALL_DISTINCT_MAP_FST_toAList]
      >-
        (match_mp_tac ssa_map_ok_more>>
        full_simp_tac(srw_ss())[]>>DECIDE_TAC))>>
    rw[]>>fs[]>>
    qpat_x_assum` _ = (stack_mov,_,_)` assume_tac>>
    drule (list_next_var_rename_move_props |> SIMP_RULE std_ss[Once
      CONJ_COMM] |> SIMP_RULE std_ss [ GSYM AND_IMP_INTRO]) >>
    disch_then drule>>
    `is_stack_var (na+2)` by fs[is_alloc_var_flip]>>
    simp[]>>strip_tac>>
    qpat_x_assum`_ (evaluate _)` mp_tac>>
    pairarg_tac>>fs[]>>
    rw[]>>
    simp[evaluate_def,get_vars_def]>>
    drule (GEN_ALL ssa_locals_rel_get_var)>>
    strip_tac>>
    res_tac>>simp[]>>
    qpat_abbrev_tac`rcst_mov = set_vars _ _ rcst`>>
    drule_at Any cut_env_lemma>>
    disch_then (qspecl_then[`rcst_mov.locals`,`option_lookup ssa''`]
      mp_tac)>>
    `domain p0 ∪ domain p1 = domain s` by
      simp[Abbr`s`,domain_union]>>
    simp[]>>
    impl_keep_tac >- (
      fs[ssa_locals_rel_def,strong_locals_rel_def]>>
      rw[INJ_DEF]
      >-
        ((* use property of list_next_var_rename_move *)
        drule list_next_var_rename_move_distinct>>
        disch_then match_mp_tac>>
        simp[ALL_DISTINCT_MAP_FST_toAList,toAList_domain])
      >>
        fs[option_lookup_def,domain_lookup,Abbr`rcst_mov`
          ,lookup_insert]>>
        res_tac>>
        fs[ssa_map_ok_def]>>
        rename1`lookup nn ssa = SOME vv`>>
        first_x_assum(qspecl_then [`nn`,`vv`] mp_tac)>>
        simp[set_vars_def,lookup_alist_insert]>>
        res_tac>>
        fs[is_phy_var_def]>>
        rw[]>>fs[])>>
    strip_tac>>
    `get_var (option_lookup ssa'' n1) rcst_mov = SOME (Word w3) ∧
     get_var (option_lookup ssa'' n2) rcst_mov = SOME (Word w4)` by
       (simp[Abbr`rcst_mov`]>>
       DEP_REWRITE_TAC [get_var_set_vars_notin]>>
       CONJ_TAC>-
         (fs[]>>CCONTR_TAC>>fs[option_lookup_def,case_eq_thms
           ,ssa_map_ok_def]>>
         res_tac>>fs[is_phy_var_def])>>
       fs[ssa_locals_rel_def])>>
    fs[evaluate_def,Abbr`rcst_mov`]>>
    simp[get_var_def,set_vars_def,lookup_alist_insert]>>
    fs[word_state_eq_rel_def]>>
    qmatch_goalsub_abbrev_tac`evaluate (_,rcstt)`>>
    qabbrev_tac`ssa_cut = inter ssa'' s`>>
    `domain ssa_cut = domain env` by (
      fs[Abbr`ssa_cut`,domain_union]>>
      irule SUBSET_INTER2>>
      fs[SUBSET_DEF,toAList_domain,ssa_locals_rel_def]>>
      metis_tac[domain_lookup])>>
    `ssa_locals_rel na''' ssa''' rst.locals rcstt.locals ∧
      word_state_eq_rel rst rcstt` by
      (qpat_x_assum`Abbrev(rst=_)` mp_tac>>
      simp[markerTheory.Abbrev_def]>>
      disch_then (SUBST_ALL_TAC)>>
      fs[next_var_rename_def]>>
      fs[Abbr`rcstt`,ssa_locals_rel_def,word_state_eq_rel_def]>>
      rveq>>fs[]>>
      CONJ_TAC>-
        (simp[lookup_insert,domain_alist_insert,Abbr`ssa_cut`]>>rw[]>>
        DISJ1_TAC>>DISJ2_TAC>>
        fs[lookup_inter,case_eq_thms]>>
        fs[domain_lookup,option_lookup_def]>>
        qexists_tac`x`>>simp[])>>
      simp[lookup_insert]>>
      ntac 2 strip_tac>>
      IF_CASES_TAC
      >-
        (strip_tac>>simp[alist_insert_def]>>
        fs[every_var_def])
      >>
      strip_tac>>simp[]>>
      conj_asm1_tac
      >-
        (fs[Abbr`ssa_cut`,domain_inter]>>
        metis_tac[domain_lookup])>>
      conj_tac>-
        (fs[strong_locals_rel_def,Abbr`ssa_cut`,alist_insert_def]>>
        first_x_assum drule>>
        disch_then drule>>
        `∃vv. lookup x (inter ssa'' s) = SOME vv ∧ vv ≠ na''+2 ∧ vv ≠ 2`
          by
          (fs[lookup_inter,domain_lookup,EXTENSION]>>
          first_x_assum(qspec_then`x` assume_tac)>>rfs[case_eq_thms]>>
          fs[ssa_map_ok_def]>>
          rpt (first_x_assum drule)>>
          fs[]>>rw[]>>
          CCONTR_TAC>>fs[is_phy_var_def])>>
        simp[lookup_insert]>>
        fs[lookup_inter,case_eq_thms,option_lookup_def])
      >>
        fs[every_var_def,every_name_def,EVERY_MEM,toAList_domain]>>
        qpat_x_assum`_ ∪ _ = domain s` sym_sub_tac>>
        fs[]>>
        last_x_assum drule>>
        simp[])>>
    drule list_next_var_rename_move_preserve >>
    disch_then(qspecl_then[`MAP FST (toAList s)`] mp_tac)>>
    simp[]>>
    impl_tac>-
      (fs[Abbr`s`,Abbr `rst`,
        next_var_rename_def,SUBSET_DEF,toAList_domain,domain_union]>>rw
        []>>
      `na''+6 = na''+2+4` by fs[]>>
      pop_assum SUBST1_TAC>>
      match_mp_tac ssa_map_ok_extend>>
      reverse conj_tac>-
        metis_tac[convention_partitions,is_stack_var_flip]>>
      simp[Abbr`ssa_cut`]>>
      match_mp_tac ssa_map_ok_inter>>
      match_mp_tac (GEN_ALL ssa_map_ok_more)>>
      asm_exists_tac>>fs[])>>
    pairarg_tac>>fs[word_state_eq_rel_def]
QED
*)

(* HOL4 ML code, not ported:
Resume ssa_cc_trans_correct[CodeBufferWrite]:
    exp_tac2
QED
*)

(* HOL4 ML code, not ported:
Resume ssa_cc_trans_correct[DataBufferWrite]:
    exp_tac2
QED
*)

(* HOL4 ML code, not ported:
Resume ssa_cc_trans_correct[FFI]:
*)
    (*FFI*)
(* HOL4 ML code, not ported:
    exists_tac>>
    last_x_assum kall_tac>>
    rename1 ‘FFI s n n0 n1 n2 p’>>
    qabbrev_tac`A = ssa_cc_trans (FFI s n n0 n1 n2 p) ssa na lt`>>
    PairCases_on`p`>>
    PairCases_on`A`>>full_simp_tac(srw_ss())[ssa_cc_trans_def]>>
    pop_assum mp_tac>>
    LET_ELIM_TAC>>full_simp_tac(srw_ss())[]>>
    full_simp_tac(srw_ss())[evaluate_def]>>
    Cases_on`get_var n0 st`>>full_simp_tac(srw_ss())[]>>
    Cases_on`x`>>full_simp_tac(srw_ss())[]>>
    Cases_on`get_var n st`>>full_simp_tac(srw_ss())[]>>
    Cases_on`x`>>full_simp_tac(srw_ss())[]>>
    Cases_on`get_var n2 st`>>full_simp_tac(srw_ss())[]>>
    Cases_on`x`>>full_simp_tac(srw_ss())[]>>
    Cases_on`get_var n1 st`>>full_simp_tac(srw_ss())[]>>
    Cases_on`x`>>full_simp_tac(srw_ss())[]>>
    Cases_on`cut_env (p0,p1) st.locals`>>full_simp_tac(srw_ss())[]>>
    FULL_CASE_TAC>>full_simp_tac(srw_ss())[LET_THM]>>
    FULL_CASE_TAC>>fs[LET_THM]>>
    Q.SPECL_THEN [`st`,`ssa`,`na+2`,`ls`,`cst`] mp_tac
      list_next_var_rename_move_preserve>>
    impl_keep_tac>- (
      srw_tac[][word_state_eq_rel_def]
      >-
        (match_mp_tac ssa_locals_rel_more>>
        full_simp_tac(srw_ss())[]>>DECIDE_TAC)
      >- (
        unabbrev_all_tac>>
        fs[cut_env_def,AllCaseEqs()]>>
        drule cut_envs_domain_SUBSET >>
        simp[toAList_domain,SUBSET_DEF,domain_union]>>
        metis_tac[])
      >-
        full_simp_tac(srw_ss())[Abbr`ls`,ALL_DISTINCT_MAP_FST_toAList]
      >-
        (match_mp_tac ssa_map_ok_more>>
        full_simp_tac(srw_ss())[]>>DECIDE_TAC))>>
    LET_ELIM_TAC>>
    qpat_x_assum`A=A0` sym_sub_tac>>
    full_simp_tac(srw_ss())[Abbr`prog`,evaluate_def,LET_THM]>>
    srw_tac[][]>>
    `get_vars [cptr1; clen1; cptr2; clen2] rcst = SOME [Word c';Word
      c;Word c''';Word c'']` by
      (unabbrev_all_tac>>full_simp_tac(srw_ss())[get_vars_def]>>
      imp_res_tac
        ssa_locals_rel_get_var>>full_simp_tac(srw_ss())[get_var_def])>>
    qabbrev_tac`f = option_lookup ssa'`>>
    Q.ISPECL_THEN [`ls`,`ssa`,`na+2`,`mov`,`ssa'`,`na'`] assume_tac
      list_next_var_rename_move_props>>
    `is_stack_var (na+2)` by
      full_simp_tac(srw_ss())[is_alloc_var_flip]>>
    rev_full_simp_tac(srw_ss())[]>>full_simp_tac(srw_ss())[set_vars_def
      ,alist_insert_def]>>
    qpat_abbrev_tac `rcstlocs = insert 2 A (insert 4 B (insert 6 C
      (insert 8 D (rcst.locals))))`>>
    full_simp_tac(srw_ss())[get_var_def]>>
    `lookup 8 rcstlocs = SOME (Word c'') ∧
     lookup 6 rcstlocs = SOME (Word c''') ∧
     lookup 4 rcstlocs = SOME (Word c) ∧
     lookup 2 rcstlocs = SOME (Word c')` by
      full_simp_tac(srw_ss())[Abbr`rcstlocs`,lookup_insert]>>
    full_simp_tac(srw_ss())[]>>
    drule_at Any cut_env_lemma>>
    disch_then (qspecl_then[`rcstlocs`,`f`] mp_tac)>>
    `domain p0 ∪ domain p1 = domain all_names` by
      simp[Abbr`all_names`,domain_union]>>
    simp[]>>
    impl_tac>-
      (rev_full_simp_tac(srw_ss())[Abbr`f`]>>
      full_simp_tac(srw_ss())[ssa_locals_rel_def
        ,strong_locals_rel_def]>>
      srw_tac[][INJ_DEF]>-
        ((* use property of list_next_var_rename_move *)
        drule list_next_var_rename_move_distinct>>
        disch_then match_mp_tac>>
        simp[Abbr`ls`,ALL_DISTINCT_MAP_FST_toAList,toAList_domain])
      >>
        full_simp_tac(srw_ss())[option_lookup_def,domain_lookup
          ,Abbr`rcstlocs`,lookup_insert]>>
        res_tac>>
        full_simp_tac(srw_ss())[ssa_map_ok_def]>>
        first_x_assum(qspecl_then [`n'`,`v'`] mp_tac)>>
        simp[]>>
        qpat_x_assum`A=SOME v'`
          SUBST_ALL_TAC>>full_simp_tac(srw_ss())[]>>
        srw_tac[][is_phy_var_def])>>
    srw_tac[][]>>
    full_simp_tac(srw_ss())[word_state_eq_rel_def]>>
    reverse(Cases_on`call_FFI st.ffi (ExtCall s) x''
      x'`)>>full_simp_tac(srw_ss())[]
    >- fs[call_env_def,flush_state_def] >>
    qpat_abbrev_tac`mem = write_bytearray A B C D E`>>
    qabbrev_tac`rst = st with <|locals :=
      x;fp_regs:=FEMPTY;memory:=mem;ffi:=f'|>`>>
    qpat_abbrev_tac`rcstt = rcst with <|locals :=
      A;fp_regs:=FEMPTY;memory:=B;ffi:=D|>`>>
    `domain ssa_cut = domain x` by (
      fs[Abbr`ssa_cut`,domain_union,cut_env_def,AllCaseEqs()]>>
      drule cut_envs_domain_SUBSET>>
      fs[SUBSET_DEF,toAList_domain,ssa_locals_rel_def,EXTENSION]>>
      metis_tac[domain_lookup])>>
    `∀x y. lookup x ssa_cut = SOME y ⇒ lookup x ssa' = SOME y` by
       (srw_tac[][]>>full_simp_tac(srw_ss())[Abbr`ssa_cut`
         ,lookup_inter]>>
       gvs[AllCaseEqs()])>>
    `domain rst.locals = domain x` by
      full_simp_tac(srw_ss())[Abbr`rst`]>>
    `ssa_locals_rel na' ssa_cut rst.locals rcstt.locals ∧
        word_state_eq_rel rst rcstt` by
       (full_simp_tac(srw_ss())[Abbr`rst`,Abbr`rcstt`
         ,state_component_equality
       ,word_state_eq_rel_def,ssa_locals_rel_def]>>
       srw_tac[][]
       >-
         (qexists_tac`x'''`>>unabbrev_all_tac>>
         full_simp_tac(srw_ss())[option_lookup_def,lookup_inter]>>
         pop_assum mp_tac
           >>EVERY_CASE_TAC>>full_simp_tac(srw_ss())[domain_lookup])
       >-
         metis_tac[domain_lookup]
       >-
         (`THE (lookup x''' ssa_cut) = f x'''` by
           (full_simp_tac(srw_ss())[Abbr`f`,option_lookup_def]>>
           `x''' ∈ domain ssa_cut` by metis_tac[domain_lookup]>>
           full_simp_tac(srw_ss())[domain_lookup]>>res_tac>>
           full_simp_tac(srw_ss())[])>>
         full_simp_tac(srw_ss())[strong_locals_rel_def]>>
         metis_tac[domain_lookup])
       >-
         (`x''' ∈ domain all_names` by metis_tac[domain_lookup]>>
         full_simp_tac(srw_ss())[every_var_def,every_name_def,EVERY_MEM
           ,toAList_domain]>>
         qpat_x_assum`_ ∪ _ = domain all_names` sym_sub_tac>>
         fs[]>>
         res_tac>>
         DECIDE_TAC))>>
     Q.SPECL_THEN [`rst`,`inter ssa' all_names`,`na'+2`,`(MAP FST
       (toAList all_names))`
                    ,`rcstt`] mp_tac
                      list_next_var_rename_move_preserve>>
     impl_tac>- (
       srw_tac[][]
       >-
         (unabbrev_all_tac>>rev_full_simp_tac(srw_ss())[]>>
         match_mp_tac (GEN_ALL ssa_locals_rel_more)>>
         full_simp_tac(srw_ss())[]>>
         HINT_EXISTS_TAC>>full_simp_tac(srw_ss())[])
       >-
         (srw_tac[][SUBSET_DEF,Abbr`ls`]>>
         full_simp_tac(srw_ss())[MEM_MAP]>>Cases_on`y'`>>full_simp_tac
           (srw_ss())[MEM_toAList,domain_lookup])
       >-
         (unabbrev_all_tac>>match_mp_tac ssa_map_ok_inter>>
         match_mp_tac (GEN_ALL ssa_map_ok_more)>>
         HINT_EXISTS_TAC>>
         full_simp_tac(srw_ss())[]>>DECIDE_TAC))>>
     full_simp_tac(srw_ss())[LET_THM]>>
     srw_tac[][]>>
     Cases_on`evaluate(ret_mov,rcstt)`>>unabbrev_all_tac>>full_simp_tac
       (srw_ss())[state_component_equality,word_state_eq_rel_def]
QED
*)

(* HOL4 ML code, not ported:
Resume ssa_cc_trans_correct[ShareInst]:
    exists_tac >>
    pairarg_tac >>
    simp[] >>
    rename1`m = Store \/ m = Store8 \/ m = Store16 \/ m = Store32`>>
    qabbrev_tac `mcase = (m = Store \/ m = Store8 \/ m = Store16 \/ m =
      Store32)`>>
    fs[AllCaseEqs()] >>
    IF_CASES_TAC >>
    gvs[next_var_rename_def,evaluate_def] >>
    drule_then (drule_at $ Pos last) ssa_cc_trans_exp_correct
    >- (
      impl_tac >- simp[word_state_eq_rel_def] >>
      disch_then (fn t => simp[t]) >>
      gvs[oneline share_inst_def,
        oneline sh_mem_store_def,
        oneline sh_mem_store_byte_def,
        oneline sh_mem_store16_def,
        oneline sh_mem_store32_def,
        markerTheory.Abbrev_def,flush_state_def,AllCaseEqs()] >>
      drule_then (drule_then assume_tac) ssa_locals_rel_get_var >>
      simp[]) >>
    impl_tac >- simp[word_state_eq_rel_def] >>
    disch_then (fn t => simp[t]) >>
    gvs[oneline share_inst_def,
      oneline sh_mem_load_def,
      oneline sh_mem_load_byte_def,
      oneline sh_mem_load16_def,
      oneline sh_mem_load32_def,
      oneline sh_mem_set_var_def,
      set_var_def,flush_state_def,AllCaseEqs(),
      markerTheory.Abbrev_def] >>
    irule ssa_locals_rel_set_var >>
    fs[every_var_def]
QED
*)

(* HOL4 ML code, not ported:
Resume ssa_cc_trans_correct[Loop]:
  rename1 `Loop names body exit_names` >>
  qpat_x_assum `every_var _ _` mp_tac >> simp[every_var_def] >>
    strip_tac >>
  simp[ssa_cc_trans_def] >>
  rpt (pairarg_tac >> fs[]) >>
  drule_then drule loop_setup_correct >>
  rpt (disch_then drule) >>
  strip_tac >>
  drule evaluate_seq_collapse >>
  strip_tac >>
  qpat_x_assum `inter ssa_refreshed exit_names = ssa'` (assume_tac o
    GSYM) >>
  qpat_x_assum `na'' = na'` (assume_tac o GSYM) >>
  fs[] >>
  `domain names ⊆ domain ssa_refreshed ∧
   domain exit_names ⊆ domain ssa_refreshed` by (
    qpat_x_assum `domain ssa_refreshed = _` SUBST1_TAC >>
    simp[domain_union, SUBSET_DEF]) >>
  `strong_locals_rel (option_lookup ssa_refreshed) (domain names)
     st.locals rcst'.locals` by (
    rw[strong_locals_rel_def] >>
    `n ∈ domain ssa_refreshed ∧
     lookup (THE (lookup n ssa_refreshed)) rcst'.locals = SOME v` by
      (conj_asm1_tac >- fs[SUBSET_DEF] >>
       fs[ssa_locals_rel_def] >> res_tac >> simp[]) >>
    Cases_on `lookup n ssa_refreshed` >- fs[domain_lookup] >>
    fs[option_lookup_def]) >>
  qspecl_then
    [`st`, `rcst'`, `ssa_refreshed`, `na_refreshed`, `names`, `body`,
     `exit_names`, `lt`, `body'`, `ssa''`, `na''`]
    mp_tac ssa_cc_trans_Loop_helper >>
  impl_tac
  >- (rpt conj_tac >> fs[]
      >- (rpt strip_tac >>
          first_x_assum irule >> fs[SUBSET_DEF])
      >- (irule every_var_mono >>
          qexists_tac `λx. x < na` >> fs[])
      >- (irule MONO_EVERY >>
          qexists_tac `λx. x < na` >> fs[])
      >- (irule MONO_EVERY >>
          qexists_tac `λx. x < na` >> fs[])) >>
  simp[LET_DEF] >>
  disch_then (qspecl_then [`res'`, `rcst`] mp_tac) >>
  impl_tac
  >- (qpat_x_assum `Seq setup_prog _ = prog'` (assume_tac o SYM) >>
      fs[] >>
      qpat_x_assum `∀Q. evaluate (Seq _ _, _) = _` (fn th =>
        once_rewrite_tac [GSYM th]) >>
      first_x_assum ACCEPT_TAC) >>
  simp[]
QED
*)

(* HOL4 ML code, not ported:
Resume ssa_cc_trans_correct[Break]:
  qexists_tac `cst.permute` >>
  simp[evaluate_def, ssa_cc_trans_def] >>
  Cases_on `oEL n lt` >> simp[]
  >- (simp[evaluate_def] >> gvs[word_state_eq_rel_def]) >>
  PairCases_on `x` >> simp[] >>
  `MEM (x0, x1, x2) lt` by (fs[oEL_EQ_EL, MEM_EL] >> metis_tac[]) >>
  `INJ (option_lookup x0) (domain x2) UNIV` by
    (fs[lt_ok_def, EVERY_MEM] >> res_tac >> fs[]) >>
  `∃cst'. evaluate (ssa_reconcile ssa x0 x2, cst) = (NONE, cst') ∧
          word_state_eq_rel cst cst' ∧
          strong_locals_rel (option_lookup x0) (domain x2)
            st.locals cst'.locals`
    by (match_mp_tac evaluate_ssa_reconcile >> simp[]) >>
  IF_CASES_TAC
  >- (gvs[evaluate_def, word_state_eq_rel_def]) >>
  gvs[evaluate_def, word_state_eq_rel_def]
QED
*)

(* HOL4 ML code, not ported:
Resume ssa_cc_trans_correct[Continue]:
  qexists_tac `cst.permute` >>
  simp[evaluate_def, ssa_cc_trans_def] >>
  Cases_on `oEL n lt` >> simp[]
  >- (simp[evaluate_def] >> gvs[word_state_eq_rel_def]) >>
  PairCases_on `x` >> simp[] >>
  `MEM (x0, x1, x2) lt` by (fs[oEL_EQ_EL, MEM_EL] >> metis_tac[]) >>
  `INJ (option_lookup x0) (domain x1) UNIV` by
    (fs[lt_ok_def, EVERY_MEM] >> res_tac >> fs[]) >>
  `∃cst'. evaluate (ssa_reconcile ssa x0 x1, cst) = (NONE, cst') ∧
          word_state_eq_rel cst cst' ∧
          strong_locals_rel (option_lookup x0) (domain x1)
            st.locals cst'.locals`
    by (match_mp_tac evaluate_ssa_reconcile >> simp[]) >>
  IF_CASES_TAC
  >- (gvs[evaluate_def, word_state_eq_rel_def]) >>
  gvs[evaluate_def, word_state_eq_rel_def]
QED
*)

(* HOL4 ML code, not ported:
Finalise ssa_cc_trans_correct ;
*)

(*For starting up*)

(*Full correctness theorem*)

(* Prove that the ssa form sets up pre_alloc_conventions
   and preserves some syntactic conventions
*)

(*Prove that the transform sets up arbitrary programs with
  the appropriate conventions*)

(* HOL4 ML code, not ported:
Resume ssa_cc_trans_pre_alloc_conventions[Loop]:
  fs[ssa_cc_trans_def,UNCURRY_EQ]>>rveq>>
  rpt(pairarg_tac>>fs[])>>rveq>>
  drule loop_setup_pre_alloc_conventions>>strip_tac>>
  drule loop_setup_props_local>>simp[]>>strip_tac>>
  qpat_x_assum `loop_setup _ _ _ _ = _` (assume_tac o GSYM)>>
  last_x_assum drule>>disch_then drule>>strip_tac>>
  qpat_x_assum `∀prog' _ _. _` (qspecl_then [`body'`,`ssa''`,`na'`]
    mp_tac)>>
  impl_tac
  >- (simp[]>>match_mp_tac ssa_map_ok_inter>>simp[])>>
  strip_tac>>
  fs[pre_alloc_conventions_def,every_stack_var_def
    ,call_arg_convention_def]>>
  IF_CASES_TAC>>fs[every_stack_var_def,call_arg_convention_def]>>
  fs[ssa_reconcile_def]>>every_case_tac>>
  fs[every_stack_var_def,call_arg_convention_def]
QED
*)

(* HOL4 ML code, not ported:
Resume ssa_cc_trans_pre_alloc_conventions[Break]:
  fs[ssa_cc_trans_def,ssa_reconcile_def]>>every_case_tac>>fs[]>>rveq>>
  fs[pre_alloc_conventions_def,every_stack_var_def
    ,call_arg_convention_def]
QED
*)

(* HOL4 ML code, not ported:
Resume ssa_cc_trans_pre_alloc_conventions[Continue]:
  fs[ssa_cc_trans_def,ssa_reconcile_def]>>every_case_tac>>fs[]>>rveq>>
  fs[pre_alloc_conventions_def,every_stack_var_def
    ,call_arg_convention_def]
QED
*)

(* HOL4 ML code, not ported:
Finalise ssa_cc_trans_pre_alloc_conventions;
*)

(* HOL4 ML code, not ported:
Resume ssa_cc_trans_distinct_tar_reg[Loop]:
  fs[ssa_cc_trans_def,UNCURRY_EQ,every_var_def]>>rveq>>
  rpt(pairarg_tac>>fs[])>>rveq>>
  drule loop_setup_props_local>>simp[]>>strip_tac>>
  drule loop_setup_every_inst_distinct_tar_reg>>strip_tac>>
  last_x_assum mp_tac>>
  impl_tac
  >- (simp[]>>
      conj_tac
      >- (match_mp_tac every_var_mono>>
          qexists_tac`λx. x < na`>>fs[]>>DECIDE_TAC)>>
      match_mp_tac ssa_map_ok_inter>>simp[])>>
  strip_tac>>
  fs[every_inst_def]>>
  IF_CASES_TAC>>fs[every_inst_def]>>
  fs[ssa_reconcile_def]>>every_case_tac>>
  fs[every_inst_def]
QED
*)

(* HOL4 ML code, not ported:
Resume ssa_cc_trans_distinct_tar_reg[Break]:
  fs[ssa_cc_trans_def,ssa_reconcile_def]>>every_case_tac>>fs[]>>rveq>>
  fs[every_inst_def,distinct_tar_reg_def]
QED
*)

(* HOL4 ML code, not ported:
Resume ssa_cc_trans_distinct_tar_reg[Continue]:
  fs[ssa_cc_trans_def,ssa_reconcile_def]>>every_case_tac>>fs[]>>rveq>>
  fs[every_inst_def,distinct_tar_reg_def]
QED
*)

(* HOL4 ML code, not ported:
Finalise ssa_cc_trans_distinct_tar_reg;
*)

(* HOL4 ML code, not ported:
Resume ssa_cc_trans_full_inst_ok_less[Loop]:
  qpat_x_assum `every_var _ _` mp_tac>>simp[every_var_def]>>strip_tac>>
  drule loop_setup_props_local>>simp[]>>strip_tac>>
  drule loop_setup_full_inst_ok_less>>strip_tac>>
  last_x_assum (qspec_then `c` mp_tac)>>
  impl_tac
  >- (simp[]>>
      conj_tac
      >- (match_mp_tac every_var_mono>>
          qexists_tac`λx. x < na`>>fs[]>>DECIDE_TAC)>>
      match_mp_tac ssa_map_ok_inter>>simp[])>>
  strip_tac>>
  fs[full_inst_ok_less_def]>>
  IF_CASES_TAC>>fs[full_inst_ok_less_def]>>
  fs[ssa_reconcile_def]>>every_case_tac>>
  fs[full_inst_ok_less_def,inst_ok_less_def]
QED
*)

(* HOL4 ML code, not ported:
Resume ssa_cc_trans_full_inst_ok_less[Break]:
  fs[ssa_cc_trans_def,ssa_reconcile_def]>>every_case_tac>>fs[]>>rveq>>
  fs[full_inst_ok_less_def]
QED
*)

(* HOL4 ML code, not ported:
Resume ssa_cc_trans_full_inst_ok_less[Continue]:
  fs[ssa_cc_trans_def,ssa_reconcile_def]>>every_case_tac>>fs[]>>rveq>>
  fs[full_inst_ok_less_def]
QED
*)

(* HOL4 ML code, not ported:
Finalise ssa_cc_trans_full_inst_ok_less;
*)

(* word_alloc syntactic stuff *)

(* HOL4 ML code, not ported:
val is_phy_var_tac =
    full_simp_tac(srw_ss())[is_phy_var_def]>>
    `0<2:num` by DECIDE_TAC>>
    `∀k.(2:num)*k=k*2` by DECIDE_TAC>>
    metis_tac[arithmeticTheory.MOD_EQ_0];
*)

(*Composing with a function using apply_colour*)

(* HOL4 ML code, not ported:
val exp_tac3 =
  assume_tac (Q.SPEC `exp` every_var_exp_get_reads_exp)>>
  ho_match_mp_tac every_var_exp_mono>>
  HINT_EXISTS_TAC>>fs[in_clash_tree_def];
*)

(*word_alloc preserves syntactic conventions*)

(*
Theorem lookup_undir_g_insert_existing[local]:
  lookup x G = SOME v ⇒
  lookup x (undir_g_insert a b G) =
  if x = a then SOME (insert b () v)
  else if x = b then SOME (insert a () v)
  else SOME v
Proof
  rw[undir_g_insert_def,dir_g_insert_def,lookup_insert]>>
  fs[insert_shadow]
QED
*)
