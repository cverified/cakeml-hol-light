(* ======================================================== *)
(*  word_elimProof: ported from HOL4's
    compiler/backend/proofs/word_elimProofScript.sml  *)
(* ======================================================== *)

(*
  Correctness proof for word_elim
*)

needs "basis/pure/mllist.ml";;
needs "compiler/backend/semantics/wordConvs.ml";;
needs "compiler/backend/semantics/wordProps.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/backend/stackLang.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/backend/word_elim.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "lib/spt_closure.ml";;
needs "lib/sptree.ml";;

(**************************** ANALYSIS LEMMAS
   *****************************)


(**************************** DEFINITIONS *****************************)

let dest_word_loc_def = cake_define
  `dest_word_loc x1 =
        match x1 with
          (Loc n _1:semanticPrimitives_v) -> SOME n
        | (_2:'a word_loc) -> NONE`;;

let dest_result_loc_def = cake_define
  `dest_result_loc x1 =
        match x1 with
          SOME (wordSem_Result w ns) ->
       BIGUNION (set_of_list (MAP (\x. match (dest_word_loc x) with
         NONE -> {} | SOME x -> {x}) ns))
        | (SOME (wordSem_Exception w (Loc n n0))) -> {n}
        | _3 -> {}`;;

(* TODO could do alt def using toAList -
    not necessary though, may not be cleaner *)
let get_locals_def = cake_define_list
  [`get_locals (LN:('a word_loc) spt) = LN`;
   `get_locals (LS a) = (match (dest_word_loc a) with SOME n ->
  sptree_insert n one LN | NONE -> LN)`;
   `get_locals (BN t1 t2) = sptree_union (get_locals t1) (get_locals
  t2)`;
   `get_locals (BS t1 a t2) =
            (let t = (sptree_union (get_locals t1) (get_locals t2))
              in
                match (dest_word_loc a) with SOME n ->
                  sptree_insert n one t | NONE -> t)`];;

(*TODO fix conflict with get_store in WordSem*)
let get_store_def = cake_define
  `get_store (st:(store_name,'a word_loc)fmap) =
       (let locSet = SET_TO_LIST (FRANGE st) in
       let locList = MAP THE (FILTER IS_SOME (MAP dest_word_loc
         locSet)) in
       FOLDL (\acc loc. sptree_insert loc one acc) LN locList)`;;

let get_num_wordloc_alist_def = cake_define
  `get_num_wordloc_alist (l:(num#'a word_loc) list) =
       (let locs = MAP THE (FILTER IS_SOME (MAP (dest_word_loc o SND)
         l)) in
       FOLDL (\acc loc. sptree_insert loc one acc) LN locs)`;;

let get_stack_def = cake_define_list
  [`get_stack [] = (LN:1 spt)`;
   `get_stack (StackFrame lsz e0 e _4 :: xs) =
            sptree_union (sptree_union (get_num_wordloc_alist
              e0) (get_num_wordloc_alist e)) (get_stack xs)`];;

(* HOL4 ML code, not ported:
val get_stack_ind = theorem "get_stack_ind";
*)

let get_memory_def = cake_define
  `get_memory (mem':'a word->'a word_loc) (mdom:'a word->bool) =
       (let locSet = SET_TO_LIST (IMAGE mem' mdom) in
       let locList = MAP THE (FILTER IS_SOME (MAP dest_word_loc
         locSet)) in
       FOLDL (\acc loc. sptree_insert loc one acc) LN locList)`;;

let find_loc_state_def = cake_define
  `find_loc_state s =
       (let loc = (get_locals (wordSem_state_locals s)) in
       let sto = (get_store (wordSem_state_store s)) in
       let sta = (get_stack (stack s)) in
       let mem' = (get_memory (wordSem_state_memory s)
         (wordSem_state_mdomain s)) in
       sptree_union (sptree_union loc sto) (sptree_union sta
         mem'))`;;

let code_rel_def = cake_define
  `word_elimProof_code_rel (reachable:1 spt) s_code (t_code:(num#'a
  wordLang_prog) spt) =
       (!n. n IN domain reachable ==>
           sptree_lookup n s_code = sptree_lookup n t_code)`;;
hol4_overload "code_rel" "word_elimProof_code_rel";;

let code_closed_def = cake_define
  `code_closed reachable c1 <=> (?code1. c1 = fromAList code1 /\
       (!n m. n IN domain reachable /\
       is_reachable (analyse_word_code code1) n m ==>
       m IN domain reachable))`;;

let gc_no_new_locs_def = cake_define
  `gc_no_new_locs (g:('a word_loc) list#('a word->'a word_loc)#('a
  word->bool)#(store_name,'a word_loc)fmap->(('a word_loc) list#('a
  word->'a word_loc)#(store_name,'a word_loc)fmap) option) <=> (!sta
  mem' mdom sto wl mem1 sto1 sta1.
       (g (wordSem_enc_stack sta,mem',mdom,sto) = SOME
         (wl,mem1,sto1)) /\
        wordSem_dec_stack wl sta = SOME sta1 ==>
       domain (get_stack sta1) SUBSET domain (get_stack sta) /\
       domain (get_memory mem1 mdom) SUBSET domain (get_memory mem'
         mdom) /\
       domain (get_store sto1) SUBSET domain (get_store sto))`;;

let word_state_rel_def = cake_define
  `word_state_rel (reachable:1 spt) t s <=> wordSem_state_locals
       s = wordSem_state_locals t /\ wordSem_state_fp_regs
       s = wordSem_state_fp_regs t /\ wordSem_state_store
       s = wordSem_state_store t /\ stack
       s = stack t /\ wordSem_state_memory
       s = wordSem_state_memory t /\ wordSem_state_mdomain
       s = wordSem_state_mdomain t /\ wordSem_state_sh_mdomain
       s = wordSem_state_sh_mdomain t /\ wordSem_state_permute
       s = wordSem_state_permute t /\ wordSem_state_compile
       s = wordSem_state_compile t /\ wordSem_state_compile_oracle
       s = wordSem_state_compile_oracle t /\
         wordSem_state_code_buffer
       s = wordSem_state_code_buffer t /\ wordSem_state_data_buffer
       s = wordSem_state_data_buffer t /\ wordSem_state_gc_fun
       s = wordSem_state_gc_fun t /\ wordSem_state_handler
       s = wordSem_state_handler t /\ state_clock
       s = state_clock t /\ wordSem_state_termdep
       s = wordSem_state_termdep t /\ wordSem_state_be
       s = wordSem_state_be t /\ state_ffi
       s = state_ffi t /\ wordSem_state_locals_size
       s = wordSem_state_locals_size t /\ wordSem_state_stack_max
       s = wordSem_state_stack_max t /\ wordSem_state_stack_limit
       s = wordSem_state_stack_limit t /\ wordSem_state_stack_size
       s = wordSem_state_stack_size t /\
       word_elimProof_code_rel reachable (wordSem_state_code s)
         (wordSem_state_code t) /\
       domain (find_loc_state t) SUBSET domain (reachable)`;;


(**************************** OTHER LEMMAS
   *****************************)

(**************************** WORD STATE REL
   ***************************)

(*TODO maybe depreciate?*)

(*TODO add assum to prove it*)

(*This can be strengthened to an equality*)
(*TODO move*)

(**************************** MAIN LEMMAS *****************************)

(* HOL4 ML code, not ported:
Resume word_removal_lemma[Skip]:
  simp[wordSemTheory.evaluate_def] >> rw[] >>
  fs[word_state_rel_def, dest_result_loc_def]
QED
*)

(* HOL4 ML code, not ported:
Resume word_removal_lemma[Install]:
  fs[no_install_def]
QED
*)

(* HOL4 ML code, not ported:
Resume word_removal_lemma[Inst]:
  simp[wordSemTheory.evaluate_def] >>
  `inst i s = NONE ⇔ inst i removed_state = NONE` by
      metis_tac[word_state_rel_inst_NONE] >>
  Cases_on `inst i s` >> fs[] >>
  Cases_on `inst i removed_state` >> fs[] >> rw[]
  >- metis_tac[word_state_rel_inst_SOME]
  >- fs[dest_result_loc_def]
QED
*)

(* HOL4 ML code, not ported:
Resume word_removal_lemma[DataBufferWrite]:
  simp[wordSemTheory.evaluate_def] >>
  rpt (TOP_CASE_TAC >> fs[]) >>
  strip_tac >> rveq >>
  fs[word_state_rel_def] >>
  fs[domain_find_loc_state, dest_result_loc_def]
QED
*)

(* HOL4 ML code, not ported:
Resume word_removal_lemma[CodeBufferWrite]:
  simp[wordSemTheory.evaluate_def] >>
  rpt (TOP_CASE_TAC >> fs[]) >>
  fs[get_var_def, buffer_write_def] >>
  strip_tac >> rveq >>
  fs[word_state_rel_def] >>
  fs[domain_find_loc_state, dest_result_loc_def]
QED
*)

(* HOL4 ML code, not ported:
Resume word_removal_lemma[Tick]:
  simp[wordSemTheory.evaluate_def] >>
  Cases_on `s.clock = 0` >> fs[]
  >- (fs[call_env_def, flush_state_def, fromList2_def] >>
      rw[word_state_rel_def] >>
      rw[find_loc_state_def, domain_union,
          get_locals_def, get_stack_def, get_store_def] >>
      fs[domain_find_loc_state, SUBSET_DEF, dest_result_loc_def])
  >- (rw[] >> fs[dec_clock_def, word_state_rel_def,
    domain_find_loc_state,
      dest_result_loc_def])
QED
*)

(* HOL4 ML code, not ported:
Resume word_removal_lemma[If]:
  `get_var_imm ri removed_state = get_var_imm ri s` by (
      Cases_on `ri` >> fs[get_var_imm_def, get_var_def]) >>
  simp[wordSemTheory.evaluate_def] >>
  rpt (TOP_CASE_TAC >> fs[]) >>
  rw[] >>
  fs[find_word_ref_def, domain_union, no_install_def]
QED
*)

(* HOL4 ML code, not ported:
Resume word_removal_lemma[Alloc]:
  simp[wordSemTheory.evaluate_def] >>
  fs[get_var_def] >>
  Cases_on `lookup n s.locals` >> fs[] >>
  Cases_on `x` >> fs[] >>
  metis_tac[word_state_rel_alloc]
QED
*)

(* HOL4 ML code, not ported:
Resume word_removal_lemma[MustTerminate]:
  simp[wordSemTheory.evaluate_def] >> Cases_on `s.termdep` >> fs[] >>
  Cases_on `evaluate (p, s with <|clock := MustTerminate_limit (:'a);
      termdep := n|>)` >> fs[] >>
  Cases_on `q = SOME TimeOut` >> fs[] >> rw[] >>
  first_x_assum (qspecl_then [`reachable`,
      `removed_state with <|clock := MustTerminate_limit (:'a);
          termdep := n|>`] mp_tac) >>
  impl_tac >> rw[] >>
  fs[no_install_def, word_state_rel_def, find_word_ref_def,
      domain_find_loc_state]
QED
*)

(* HOL4 ML code, not ported:
Resume word_removal_lemma[Seq]:
  simp[wordSemTheory.evaluate_def] >>
  fs[find_word_ref_def, domain_union] >>
  Cases_on `evaluate (c1, s)` >> fs[] >> Cases_on `q` >> fs[] >> rw[] >>
  first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >>
  strip_tac >> rveq >> fs[no_install_def, find_word_ref_def] >> rw[] >>
  fs[] >> rfs[] >>
  first_x_assum (qspecl_then [`reachable`, `s'`] match_mp_tac) >> fs[]
    >>
  `s.code = r.code ∧ removed_state.code = s'.code ∧
  r.code = new_state.code ∧ r.gc_fun = s.gc_fun` by
      metis_tac[no_install_evaluate_const_code, evaluate_consts] >>
  rveq >> fs[]
QED
*)

(* HOL4 ML code, not ported:
Resume word_removal_lemma[LocValue]:
  simp[wordSemTheory.evaluate_def] >> fs[find_word_ref_def] >>
  imp_res_tac code_rel_def >>
  Cases_on `l1 ∈ domain s.code` >> fs[] >>
  `l1 ∈ domain removed_state.code` by fs[domain_lookup] >>
  rw[] >> fs[set_var_def, word_state_rel_def] >>
  fs[domain_find_loc_state] >>
  `domain (get_locals (insert r (Loc l1 0) s.locals)) ⊆
      domain (get_locals s.locals) ∪ {l1}`
  by (metis_tac[get_locals_insert_Loc]) >> fs[SUBSET_DEF] >> rw[] >>
  res_tac >> fs[]
  >> fs[dest_result_loc_def]
QED
*)

(* HOL4 ML code, not ported:
Resume word_removal_lemma[Get]:
  simp[wordSemTheory.evaluate_def] >> fs[] >>
  TOP_CASE_TAC >> fs[] >>
  strip_tac >> rveq >>
  fs[set_var_def,wordSemTheory.get_store_def] >>
  rw[] >>
  fs[word_state_rel_def, domain_find_loc_state, dest_result_loc_def] >>
  fs[get_locals_insert_Loc] >>
  qspecl_then [`v`, `x`, `s.locals`] mp_tac get_locals_insert >>
  Cases_on `x` >> fs[dest_word_loc_def] >- metis_tac[SUBSET_TRANS] >>
  rw[] >>
  `n ∈ domain reachable` by metis_tac[domain_get_store, SUBSET_DEF] >>
  fs[SUBSET_DEF] >> metis_tac[]
QED
*)

(* HOL4 ML code, not ported:
Resume word_removal_lemma[Assign]:
  simp[wordSemTheory.evaluate_def] >> fs[] >>
  Cases_on `word_exp s exp` >> fs[] >>
  fs[set_var_def] >> rw[] >> fs[word_state_rel_def,
    domain_find_loc_state,
      dest_result_loc_def] >>
  qspecl_then [`v`, `x`, `s.locals`] mp_tac get_locals_insert >>
  Cases_on `x` >> fs[dest_word_loc_def] >- metis_tac[SUBSET_TRANS] >>
  rw[] >>
  `n ∈ domain reachable` by (Cases_on `exp` >> fs[word_exp_def]
      >- (fs[get_var_def] >> metis_tac[domain_get_locals_lookup,
        SUBSET_DEF])
      >- (fs[wordSemTheory.get_store_def] >> metis_tac[domain_get_store,
        SUBSET_DEF])
      >- (Cases_on `word_exp s e` >> fs[] >> Cases_on `x` >>
          fs[] >>
          fs[mem_load_def] >> metis_tac[domain_get_memory, SUBSET_DEF])
      >- (Cases_on `the_words (MAP (λa. word_exp s a) l)` >>
          fs[])
      >- (rename1 ‘Shift _ e₁ e₂’>>
          namedCases_on `word_exp s e₁` ["", "x"] >> fs[] >>
          Cases_on `x` >> fs[]>>
          namedCases_on `word_exp s e₂` ["", "x"] >> fs[] >>
          Cases_on `x` >> fs[])) >>
  fs[SUBSET_DEF] >> metis_tac[]
QED
*)

(* HOL4 ML code, not ported:
Resume word_removal_lemma[Set]:
  simp[wordSemTheory.evaluate_def] >>
  Cases_on `v = Handler ∨ v = BitmapBase` >> fs[] >>
  Cases_on `word_exp s exp` >> fs[] >>
  strip_tac >> rveq >>
  fs[set_store_def] >> rw[] >>
  fs[word_state_rel_def, domain_find_loc_state, dest_result_loc_def] >>
  fs[find_word_ref_def] >>
  qspecl_then [`s.store`, `v`, `x`] mp_tac get_store_update >>
  Cases_on `x` >> fs[dest_word_loc_def] >> rw[]
  >- metis_tac[SUBSET_TRANS] >>
  `n ∈ domain reachable` by (Cases_on `exp` >> fs[word_exp_def]
      >- (fs[get_var_def] >> metis_tac[domain_get_locals_lookup,
        SUBSET_DEF])
      >- (fs[wordSemTheory.get_store_def] >> metis_tac[domain_get_store,
        SUBSET_DEF])
      >- (Cases_on `word_exp s e` >> fs[] >>
          Cases_on `x` >> fs[] >>
          fs[mem_load_def] >> metis_tac[domain_get_memory, SUBSET_DEF])
      >- (Cases_on `the_words (MAP (λa. word_exp s a) l)` >>
          fs[])
      >- (rename1 ‘Shift _ e₁ e₂’>>
          namedCases_on `word_exp s e₁` ["", "x"] >> fs[] >>
          Cases_on `x` >> fs[]>>
          namedCases_on `word_exp s e₂` ["", "x"] >> fs[] >>
          Cases_on `x` >> fs[])) >>
  fs[SUBSET_DEF] >> metis_tac[]
QED
*)

(* HOL4 ML code, not ported:
Resume word_removal_lemma[Store]:
  simp[wordSemTheory.evaluate_def] >>
  ntac 3 (TOP_CASE_TAC >> fs[]) >>
  fs[mem_store_def] >>
  Cases_on `c ∈ s.mdomain` >> fs[] >> rw[] >>
  fs[word_state_rel_def, domain_find_loc_state, dest_result_loc_def] >>
  qspecl_then [`c`, `x`, `s.memory`, `s.mdomain`] mp_tac
      get_memory_update >> fs[] >>
  Cases_on `x` >> fs[dest_word_loc_def] >> rw[]
  >- metis_tac[SUBSET_TRANS] >>
  `n ∈ domain reachable` by (
      fs[get_var_def] >>
      imp_res_tac domain_get_locals_lookup >>
      fs[SUBSET_DEF]) >>
  fs[SUBSET_DEF] >> metis_tac[]
QED
*)

(* HOL4 ML code, not ported:
Resume word_removal_lemma[OpCurrHeap]:
  simp[wordSemTheory.evaluate_def,word_exp_def,the_words_def] >>
  rpt (TOP_CASE_TAC >> fs[]) >> fs[AllCaseEqs()] >>
  strip_tac >> rveq >>
  gvs [dest_result_loc_def,set_var_def] >>
  fs[word_state_rel_def, domain_find_loc_state, dest_result_loc_def]
  \\ qspecl_then [`dst`, `Word z`, `s.locals`] mp_tac get_locals_insert
  \\ fs[dest_word_loc_def] \\ metis_tac[SUBSET_TRANS]
QED
*)

(* HOL4 ML code, not ported:
Resume word_removal_lemma[Move]:
  simp[wordSemTheory.evaluate_def] >> EVERY_CASE_TAC >> fs[] >> rw[] >>
  fs[set_vars_def] >>
  fs[word_state_rel_def, domain_find_loc_state] >> fs[alist_insert_def]
    >>
  fs[SUBSET_DEF, domain_get_locals_lookup] >> rw[] >>
  imp_res_tac get_vars_length_lemma >>
  fs[lookup_alist_insert] >>
  Cases_on `ALOOKUP (ZIP (MAP FST moves, x)) k` >> fs[]
  >- metis_tac[]
  >- (qsuff_tac `MEM x'' x`
      >- metis_tac[get_vars_get_locals, domain_get_locals_lookup]
      >> `LENGTH x = LENGTH (MAP FST moves)` by
              metis_tac[LENGTH_MAP] >> rveq >>
         metis_tac[ALOOKUP_ZIP_SUCCESS])
  >> fs[dest_result_loc_def]
QED
*)

(* HOL4 ML code, not ported:
Resume word_removal_lemma[StoreConsts]:
  simp[wordSemTheory.evaluate_def] >>
  fs[get_var_def] >>
  every_case_tac >> fs [set_var_def,unset_var_def] >> rw [] >>
  gvs [word_state_rel_def] >>
  irule SUBSET_TRANS >>
  first_x_assum $ irule_at Any >>
  fs [find_loc_state_def,domain_union,dest_result_loc_def] >> fs
    [SUBSET_DEF] >>
  fs [domain_get_locals_lookup,lookup_insert,AllCaseEqs(),lookup_delete,
      domain_get_memory] >> rw [] >>
  imp_res_tac const_writes_eq_Loc >>
  rw [] >> fs [] >> metis_tac []
QED
*)

(* HOL4 ML code, not ported:
Resume word_removal_lemma[Raise]:
  simp[wordSemTheory.evaluate_def] >>
  TOP_CASE_TAC >> fs[] >>
 `jump_exc s = NONE ⇔ jump_exc removed_state = NONE` by (
      fs[jump_exc_def] >> EVERY_CASE_TAC) >>
  drule word_state_rel_jump_exc >> strip_tac >> Cases_on `jump_exc s` >>
  fs[] >>
  PairCases_on `x'` >> fs[] >> rw[] >> fs[word_state_rel_def]
  >> Cases_on `x` >> fs[dest_result_loc_def] >>
     fs[SUBSET_DEF,get_var_def] >>
      qspecl_then [`n'`, `s.locals`] mp_tac domain_get_locals_lookup >>
      rw[] >>
      fs[domain_find_loc_state] >> res_tac >> fs[]
QED
*)

(* HOL4 ML code, not ported:
Resume word_removal_lemma[Return]:
  simp[wordSemTheory.evaluate_def,flush_state_def] >>
  rpt (TOP_CASE_TAC >> fs[]) >>
  strip_tac >> rveq >>
  simp[dest_result_loc_def] >>
  fs[word_state_rel_def,domain_find_loc_state,get_locals_def] >>
  irule SUBSET_TRANS >>
  qpat_x_assum `domain (get_locals _) ⊆ domain reachable`
  (irule_at (Pos last)) >>
  fs[oneline dest_word_loc_def] >>
  pop_assum mp_tac >>
  rpt (pop_assum kall_tac) >>
  map_every qid_spec_tac $ [`x`,`s`,`ms`] >>
  Induct_on `x` >> rw[] >> fs[]
  >-(Cases_on `ms` >>
     gvs[get_vars_def,AllCaseEqs()] >>
     EVERY_CASE_TAC >>
     fs[get_var_def] >> METIS_TAC[domain_get_locals_lookup])
  >> Cases_on `ms` >> fs[get_vars_def,AllCaseEqs()]
  >> METIS_TAC[]
QED
*)

(* HOL4 ML code, not ported:
Resume word_removal_lemma[ShareInst]:
  fs[wordSemTheory.evaluate_def,oneline share_inst_def] >>
  rpt (TOP_CASE_TAC >> fs[]) >>
   gvs[AllCaseEqs(),
   sh_mem_load_def,sh_mem_load_byte_def,
   sh_mem_load32_def,sh_mem_store32_def,
   sh_mem_load16_def,sh_mem_store16_def,
   sh_mem_store_def,sh_mem_store_byte_def,
   DefnBase.one_line_ify NONE sh_mem_set_var_def] >>
  rw[set_var_def,dest_result_loc_def,flush_state_def] >>
  drule_then assume_tac word_state_rel_word_exp >>
  gvs[word_state_rel_def,domain_find_loc_state] >>
  gvs[domain_find_loc_state,domain_get_locals_lookup,
    SUBSET_DEF] >>
  rpt strip_tac >>
  gvs[domain_lookup,lookup_insert,
    PULL_EXISTS,AllCaseEqs(),get_stack_def,get_var_def,get_store_def] >>
  first_x_assum $ drule_then irule
QED
*)

(* HOL4 ML code, not ported:
Resume word_removal_lemma[FFI]:
  fs[wordSemTheory.evaluate_def,flush_state_def] >>
  rpt (TOP_CASE_TAC >> fs[]) >>
  strip_tac >> rveq >>
  fs[word_state_rel_def] >>
  fs[domain_find_loc_state] >>
  simp[dest_result_loc_def,get_stack_def,get_locals_def,get_store_def]
    >>
  fs[get_memory_write_bytearray_lemma] >>
  gvs[cut_env_def,cut_envs_def,cut_names_def,AllCaseEqs()] >>
  irule SUBSET_TRANS >> irule_at (Pos hd) get_locals_union_subset
  \\ fs[domain_union]
  \\ fs[SUBSET_DEF]
  \\ rw[]
  \\ imp_res_tac domain_get_locals_lookup
  \\ fs[lookup_inter, case_eq_thms]
  \\ fs[domain_lookup]
  \\ imp_res_tac (SIMP_RULE std_ss [domain_lookup, PULL_FORALL]
      domain_get_locals_lookup)
  \\ fs[]
QED
*)

(* HOL4 ML code, not ported:
Resume word_removal_lemma[Call]:
  simp[wordSemTheory.evaluate_def,no_install_def] >>
  ntac 2 (TOP_CASE_TAC >> fs[]) >>
  `get_vars args s = SOME [] ⇒ args = []` by (Cases_on `args` >>
      gvs[bad_dest_args_def,get_vars_def,AllCaseEqs()]) >>
  `find_code dest (add_ret_loc ret x) s.code s.stack_size =
      find_code dest (add_ret_loc ret x) removed_state.code
        s.stack_size`
  by (
   rpt (qpat_x_assum `!x. _` kall_tac) >>
   simp[oneline find_code_def] >>
   TOP_CASE_TAC >> fs[]
   >-(
     fs[bad_dest_args_def] >>
     rename1 `get_vars args s = SOME x` >>
     `x ≠ []`
        by (Cases_on `args` >> gvs[get_vars_def,AllCaseEqs()]) >>
     namedCases_on `add_ret_loc ret x` ["","h t"] >> fs[] >>
     ntac 2 (TOP_CASE_TAC >> fs[]) >>
     `MEM (Loc n 0) x` by
       (Cases_on `ret` >> fs[add_ret_loc_def]
        >- metis_tac[LAST_DEF, MEM_LAST, MEM]
        >- (PairCases_on `x'` >> gvs[add_ret_loc_def,LAST_DEF] >>
            Cases_on `t` >> fs[] >> metis_tac[LAST_DEF, MEM_LAST, MEM]))
              >>
     drule_all_then assume_tac get_vars_get_locals >>
     `n ∈ domain reachable`
          by (fs[domain_find_loc_state] >>
           METIS_TAC[SUBSET_DEF]) >>
     `lookup n s.code = lookup n removed_state.code` by
           metis_tac[code_rel_def] >> fs[])
   >> `x' ∈ domain reachable` by
           fs[find_word_ref_def, SUBSET_DEF, domain_union] >>
      `lookup x' s.code = lookup x' removed_state.code` by
           metis_tac[code_rel_def] >> fs[])
  >> pop_assum (SUBST_ALL_TAC o SYM) >> fs[] >>
  ntac 4 (TOP_CASE_TAC >> fs[])
  >- (
     ntac 2 (TOP_CASE_TAC >> fs[])
     >- (
         strip_tac >> rveq >>
         simp[dest_result_loc_def,word_state_rel_def,flush_state_def] >>
         fs[domain_find_loc_state,get_locals_def,get_stack_def
           ,get_store_def]) >>
     ntac 2 (TOP_CASE_TAC >> fs[]) >>
     strip_tac >> rveq >>
     qmatch_asmsub_abbrev_tac `evaluate (q',A)` >>
     qmatch_goalsub_abbrev_tac `evaluate (q',B)` >>
     first_x_assum (qspecl_then [`reachable`, `B`] mp_tac) >>
     impl_tac >-(
       fs[Abbr `A`,Abbr `B`] >>
       CONJ_TAC >-(
         rename [`word_state_rel _ _ _`] >>
         simp[word_state_rel_def,dec_clock_def] >>
         simp[call_env_def] >>
         fs[domain_find_loc_state] >>
         Cases_on `dest` >>
           gvs[find_code_def,add_ret_loc_def,AllCaseEqs()]
         >-(irule SUBSET_TRANS >>
            qpat_assum `domain (get_locals _) ⊆ _` $ irule_at (Pos last)
              >>
            irule get_locals_fromList2_FRONT >> METIS_TAC[])
         >> irule SUBSET_TRANS >>
         qpat_assum `domain (get_locals _) ⊆ _` $ irule_at (Pos last) >>
         Cases_on `q = []` >- simp[fromList2_def,get_locals_def ] >>
         irule get_locals_fromList2 >> METIS_TAC[]) >>
       CONJ_TAC >-(
         rename [`no_install _`] >>
         imp_res_tac no_install_find_code) >>
       qpat_x_assum `code_closed _ _` assume_tac >>
       fs[code_closed_def,is_reachable_def] >>
       simp[SUBSET_DEF] >> rw[] >>
       first_x_assum irule >>
       irule_at Any RTC_SINGLE >>
       simp[is_adjacent_def] >>
       irule_at (Pos hd) lookup_analyse_word_code >>
       Cases_on `dest` >> gvs[find_code_def,AllCaseEqs()] >>
       fs[lookup_fromAList] >>
       first_assum $ irule_at (Pos hd) >>
       (CONJ_TAC >- fs[domain_lookup])
       >- (
       fs[domain_find_loc_state,add_ret_loc_def] >>
       irule SUBSET_THM >>
       qpat_assum `domain (get_locals _) ⊆ _` $ irule_at (Pos last) >>
       irule get_vars_get_locals >>
       METIS_TAC[MEM_LAST_NOT_NIL ])
       >- (fs[find_word_ref_def])) >>
       strip_tac >> fs[])
  >> qmatch_asmsub_rename_tac`add_ret_loc (SOME l)`
  >>  PairCases_on `l` >> fs[] >>
      Cases_on `domain l1 = {} ∨ ¬ALL_DISTINCT l0` >> fs[] >>
      fs[cut_envs_def,cut_names_def] >>
      Cases_on `domain l1 ⊆ domain s.locals` >>
      fs[] >>
      Cases_on `domain l2 ⊆ domain s.locals` >>
      fs[] >>
      Cases_on `s.clock = 0` >> fs[]
      >- (strip_tac >> rveq >>
         simp[dest_result_loc_def] >>
         simp[flush_state_def,word_state_rel_def,call_env_def] >>
         fs[domain_find_loc_state] >>
         simp[get_locals_def,get_stack_def,get_store_def] >>
         simp[oneline push_env_def,env_to_list_def] >>
         rpt (TOP_CASE_TAC >> fs[])) >>
      fs[add_ret_loc_def] >>
          fs[find_word_ref_def, domain_find_loc_state, domain_union] >>
          `domain (find_word_ref q') ⊆ domain reachable` by (
              rpt (qpat_x_assum `!x. _` kall_tac) >>
              Cases_on `dest` >> fs[find_code_def, code_closed_def]
              >- (
                  fs[AllCaseEqs()] >>
                  rveq >> Cases_on `x` >> rfs[bad_dest_args_def] >>
                  rw[] >>
                  `loc ∈ domain reachable` by (
                      `MEM (Loc loc 0) (h::t)` by
                          metis_tac[MEM, LAST_DEF, MEM_LAST] >>
                      qspecl_then [`args`, `s`, `h::t`, `loc`, `0`]
                        mp_tac
                          get_vars_get_locals >> rw[] >>
                          fs[SUBSET_DEF]) >>
                  rw[SUBSET_DEF] >>
                  qpat_x_assum `∀ n m . n ∈ _ ∧ _ ⇒ _`
                      (qspecl_then [`loc`, `x`] mp_tac) >>
                  reverse(impl_tac) >> fs[] >> fs[is_reachable_def] >>
                  match_mp_tac RTC_SINGLE >> fs[is_adjacent_def] >>
                  fs[domain_lookup, lookup_fromAList] >>
                  irule_at Any lookup_analyse_word_code >>
                  goal_assum (drule_at Any) >>
                  goal_assum drule)
              >- (
                  fs[AllCaseEqs()] >>
                  rveq >> Cases_on `x` >>
                  fs[] >> rw[SUBSET_DEF] >>
                  qpat_x_assum `∀ n m . n ∈ _ ∧ _ ⇒ _`
                      (qspecl_then [`x'`, `x`] mp_tac) >>
                  reverse(impl_tac) >> fs[] >>
                  fs[is_reachable_def] >> match_mp_tac RTC_SINGLE >>
                  fs[is_adjacent_def, domain_lookup] >>
                  goal_assum (drule_at Any) >>
                  irule lookup_analyse_word_code >>
                  metis_tac[lookup_fromAList])
                  ) >>
          `word_state_rel reachable (call_env q r' (push_env
              (inter s.locals l1,inter s.locals l2) handler (dec_clock
                s)))
              (call_env q r' (push_env (inter s.locals l1,inter s.locals
                l2) handler
              (dec_clock removed_state)))` by (
                 rpt (qpat_x_assum `!x. _` kall_tac) >>
                  `∀ e . MEM e q ⇒ (case dest_word_loc e of | NONE => {}
                      | SOME n => {n}) ⊆ domain reachable` by (
                  rw[] >> Cases_on `e` >>
                  fs[dest_word_loc_def, SUBSET_EMPTY] >>
                  Cases_on `dest` >>
                  fs[find_code_def] >>
                  EVERY_CASE_TAC >> fs[] >> rveq >>
                  imp_res_tac MEM_FRONT >> fs[] >>
                  METIS_TAC[get_vars_get_locals,SUBSET_DEF]) >>
                fs[dec_clock_def, call_env_def, flush_state_def] >>
                Cases_on `handler`
                >- (fs[word_state_rel_def, domain_find_loc_state] >>
                    fs[call_env_def,push_env_def,env_to_list_def]
                    >> rw[]
                    >- (rw[SUBSET_DEF] >> fs[domain_get_locals_lookup]
                      >>
                        imp_res_tac fromList2_value >>
                        qpat_x_assum `∀ e . MEM _ _ ⇒ _`
                          (qspec_then `Loc x' n1` mp_tac) >>
                        fs[dest_word_loc_def])
                    >- fs[stack_list_rearrange_lemma])
                >- (PairCases_on `x'` >> fs[] >>
                    fs[push_env_def, env_to_list_def,
                      word_state_rel_def,
                      domain_find_loc_state] >>
                    rw[]
                    >- (rw[SUBSET_DEF] >> fs[domain_get_locals_lookup]
                      >>
                        imp_res_tac fromList2_value >>
                        qpat_x_assum `∀ e . MEM _ _ ⇒ _`
                          (qspec_then `Loc x' n1` mp_tac) >>
                        fs[dest_word_loc_def])
                    >- fs[stack_list_rearrange_lemma])) >>
          Cases_on `evaluate (q', call_env q r' (push_env
              (inter s.locals l1,inter s.locals l2) handler (dec_clock
                s)))` >> fs[] >>
          Cases_on `q'' = SOME Error` >> fs[] >>
          last_x_assum (drule_at (Pos hd)) >>
          impl_tac >- (fs[] >> imp_res_tac no_install_find_code) >>
          strip_tac >> fs[] >>
          Cases_on `q''` >> fs[] >> Cases_on `x'` >> fs[] >>
          TRY (strip_tac >> fs[] >> NO_TAC)
          >- (
              drule_then assume_tac word_state_rel_pop_env_NONE >>
              drule_then assume_tac word_state_rel_pop_env >>
              qpat_assum `word_state_rel _ _ _` mp_tac >>
              SIMP_TAC std_ss [Once word_state_rel_def] >> strip_tac >>
              Cases_on `w = Loc l4 l5 ⇒ LENGTH l ≠ LENGTH l0` >> fs[] >>
              TOP_CASE_TAC >> fs[] >>
              qpat_assum `word_state_rel _ _ _` mp_tac >>
              SIMP_TAC std_ss [Once word_state_rel_def] >> strip_tac >>
              TOP_CASE_TAC >> fs[] >>
              strip_tac >> fs[] >>
              qmatch_asmsub_abbrev_tac `evaluate (l3,A)` >>
              qmatch_goalsub_abbrev_tac `evaluate (l3,B)` >>
              first_x_assum (qspecl_then [`reachable`, `B`] mp_tac) >>
              impl_tac >- (
                fs[Abbr`A`,Abbr`B`] >>
                CONJ_TAC >- (
                qpat_assum `dest_result_loc _ ⊆ _` assume_tac >>
                fs[dest_result_loc_def] >>
                fs[word_state_rel_set_vars])
                 >>
                CONJ_TAC >-
                      (imp_res_tac pop_env_code_gc_fun_clock  >> fs[] >>
                       imp_res_tac evaluate_consts >> fs[]) >>
                CONJ_TAC >- fs[no_install_def]
                >> fs[word_state_rel_def] >>
                (imp_res_tac no_install_find_code >> fs[]) >>
                imp_res_tac no_install_evaluate_const_code >>
                imp_res_tac pop_env_code_gc_fun_clock  >> fs[] >>
                gvs[]) >>
              rw[] >> fs[])
          >- (
              namedCases_on `handler`["","h"] >> fs[]
              >- (rw[] >> fs[]) >>
              PairCases_on `h` >> fs[] >>
              TOP_CASE_TAC >> fs[] >>
              qpat_assum `word_state_rel _ _ _` mp_tac >>
              SIMP_TAC std_ss [Once word_state_rel_def] >> strip_tac >>
              fs[] >>
              TOP_CASE_TAC >> fs[] >>
              strip_tac >> fs[] >>
              qmatch_asmsub_abbrev_tac `evaluate (h1,A)` >>
              qmatch_goalsub_abbrev_tac `evaluate (h1,B)` >>
              first_x_assum (qspecl_then [`reachable`, `B`] mp_tac) >>
              impl_tac >- (
                fs[Abbr`A`,Abbr`B`] >>
                CONJ_TAC >- (
                qpat_x_assum `dest_result_loc _ ⊆ domain _` assume_tac
                  >>
                Cases_on `w0` >> fs[]
                >- (irule word_state_rel_set_var_word >> fs[])
                >> fs[dest_result_loc_def]
                >> fs[word_state_rel_def]
                >> CONJ_TAC >- simp[set_var_def]
                >> fs[domain_find_loc_state,set_var_def]
                >> irule SUBSET_TRANS
                >> irule_at Any get_locals_insert
                >> fs[dest_word_loc_def])
                >>
                CONJ_TAC >-
                      (imp_res_tac evaluate_consts >> fs[]) >>
                CONJ_TAC >- fs[no_install_def]
                >> fs[word_state_rel_def] >>
                (imp_res_tac no_install_find_code >> fs[]) >>
                imp_res_tac no_install_evaluate_const_code >>
                gvs[]) >>
              rw[] >> fs[])
QED
*)

(* HOL4 ML code, not ported:
Resume word_removal_lemma[Loop]:
    simp[wordSemTheory.evaluate_def, find_word_ref_def, no_install_def,
         wordSemTheory.cut_state_def] >>
    TOP_CASE_TAC >> fs[] >>
    pairarg_tac >> fs[] >>
    qpat_x_assum `_ = SOME x` mp_tac >>
    simp[wordSemTheory.cut_env_def, wordSemTheory.cut_envs_def,
         wordSemTheory.cut_names_def, AllCaseEqs()] >>
    strip_tac >> gvs[] >>
    `domain (get_locals (inter s.locals names)) SUBSET domain reachable`
      by (
      simp[SUBSET_DEF, domain_get_locals_lookup, lookup_inter,
        AllCaseEqs()] >>
      rw[] >>
      `x IN domain (find_loc_state s)` suffices_by fs[SUBSET_DEF] >>
      simp[find_loc_state_def, domain_union, domain_get_locals_lookup]
        >>
      disj1_tac >> disj1_tac >> metis_tac[]) >>
    strip_tac >>
    `res <> SOME Error` by (
      strip_tac >> gvs[wordSemTheory.exit_loop_def,
        wordSemTheory.cont_loop_def]) >>
    qpat_x_assum `!v. cut_state _ _ = SOME v ==> _`
      (qspec_then `s with locals := inter s.locals names` mp_tac) >>
    simp[wordSemTheory.cut_state_def, wordSemTheory.cut_env_def,
         wordSemTheory.cut_envs_def, wordSemTheory.cut_names_def] >>
    disch_then (qspecl_then [`reachable`,
        `removed_state with locals := inter s.locals names`] mp_tac) >>
    (impl_tac
     >- fs[word_state_rel_def, domain_find_loc_state, no_install_def,
            find_word_ref_def, find_loc_state_def, domain_union]) >>
    strip_tac >> pairarg_tac >> gvs[]
    >- ( (* timeout: cont_loop, clock = 0 *)
      IF_CASES_TAC >>
      gvs[dest_result_loc_def, flush_state_def, word_state_rel_def,
          domain_find_loc_state, get_locals_def, get_store_def,
            get_stack_def])
    >- ( (* cont_loop iteration: cont_loop, clock <> 0 *)
      IF_CASES_TAC >> gvs[] >>
      last_x_assum (qspecl_then
        [`s with locals := inter s.locals names`, `res`, `s1`] mp_tac)
          >>
      simp[wordSemTheory.cut_state_def, wordSemTheory.cut_env_def,
           wordSemTheory.cut_envs_def, wordSemTheory.cut_names_def,
           STOP_def] >>
      fs[dec_clock_def, word_state_rel_def, domain_find_loc_state,
         find_loc_state_def, domain_union, find_word_ref_def,
           no_install_def] >>
      imp_res_tac evaluate_consts >> gvs[] >>
      imp_res_tac no_install_evaluate_const_code >> gvs[])
    >- ( (* Break 0 *)
      gvs[word_state_rel_def, dest_result_loc_def,
        domain_find_loc_state,
          wordSemTheory.cut_envs_def, wordSemTheory.cut_names_def] >>
      imp_res_tac evaluate_consts >> gvs[] >>
      match_mp_tac SUBSET_TRANS >>
      qexists_tac `domain (get_locals s1.locals)` >>
      fs[get_locals_inter_subset])
    >- ( (* exit_loop *)
      Cases_on `res` >>
      gvs[wordSemTheory.exit_loop_def, dest_result_loc_def] >>
      Cases_on `x` >>
      gvs[wordSemTheory.exit_loop_def, dest_result_loc_def])
QED
*)

(* HOL4 ML code, not ported:
Finalise word_removal_lemma;
*)

(**************************** WORD_REMOVAL_THM
   *****************************)
