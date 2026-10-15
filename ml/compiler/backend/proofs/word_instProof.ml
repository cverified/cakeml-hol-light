(* ======================================================== *)
(*  word_instProof: ported from HOL4's
    compiler/backend/proofs/word_instProofScript.sml  *)
(* ======================================================== *)

(*
  Correctness proof for word_inst
*)

needs "compiler/backend/semantics/wordConvs.ml";;
needs "compiler/backend/semantics/wordProps.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/backend/word_inst.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "semantics/ast.ml";;

(* resolve ambiguity between semanticsPrimitives$result and
   wordSem$result
   in latter's favour
*)
(* HOL4 type abbreviation (expanded in the port):
     result = 'a wordSem$result *)

(* TODO: Move, but some of these are specific instantiations *)

(* Instruction selection and assorted optimisation correctness
0) pull_exp correctness -- this does pull_ops and optimize_consts
1) pull_exp syntax
2) flatten_exp correctness -- makes stuff into binary branching trees
3) flatten_exp syntax -- prove the above property (binary_branch_exp --
  not counted as a "global" syntactic convention since it is only used
  locally here)
4) inst_select_exp and inst_select correctness
5) inst_select syntax -- flat_exp_conventions and full_inst_ok_less
6) three_to_two_reg correctness
7) three_to_two_reg syntax -- two_reg_insts and some preservation ones
*)

(* pull_exp correctness *)

(*In general, any permutation works*)

(*Remove tail recursion to make proof easier...*)
let pull_ops_simp_def = cake_define_list
  [`pull_ops_simp op [] = []`;
   `pull_ops_simp op (x :: xs) =
        (match x with (wordLang_Op op' ls) -> (if op = op' then
          ls ++ (pull_ops_simp op xs) else x :: (pull_ops_simp op
          xs)) | _2 -> x :: (pull_ops_simp op xs))`];;

(* TODO: Maybe move to props, if these are needed elsewhere *)

(* Done with pull_ops, next is optimize_consts *)

(* pull_exp syntax *)

(* HOL4 ML code, not ported:
val pull_ops_every_var_exp = Q.prove(`
  ∀ls acc.
  EVERY (every_var_exp P) acc ∧ EVERY (every_var_exp P) ls ⇒
  EVERY (every_var_exp P) (pull_ops op ls acc)`,
  Induct>>full_simp_tac(srw_ss())[pull_ops_def]>>srw_tac[]
    []>>EVERY_CASE_TAC>>full_simp_tac(srw_ss())[every_var_exp_def]>>
  metis_tac[ETA_AX,EVERY_APPEND,every_var_exp_def]) |>
    REWRITE_RULE[EVERY_MEM];
*)

(* flatten_exp correctness *)

(*All ops are 2 args. Technically, we should probably check that Sub has
   2 args. However, the semantics already checks that and it will get
   removed later*)
let _ = size_thms "exp";;
(* HOL4 termination: \\ REPEAT STRIP_TAC \\ IMP_RES_TAC
   MEM_IMP_exp_size \\ TRY (FIRST_X_ASSUM (ASSUME_TAC o Q.SPEC
   `ARB`)) \\ full_simp_tac(srw_ss())[exp_size_def] \\ TRY
   (DECIDE_TAC) *)
let binary_branch_exp_def = cake_define_wf
  `MEASURE (exp_size ARB)`
  `binary_branch_exp exp =
        match exp with
          wordLang_Op Sub exps -> EVERY (binary_branch_exp) exps
        | (wordLang_Op op xs) -> (LENGTH xs = 2 /\ EVERY
          (binary_branch_exp) xs)
        | (Load exp) -> binary_branch_exp exp
        | (Shift backend_common_word_shift exp nexp) ->
          (binary_branch_exp exp /\ binary_branch_exp nexp)
        | exp -> T`;;

(* flatten_exp syntax *)

(* inst_select correctness
  Main difficulty: Dealing with multiple choice of optimizations,
    depending on whether we are allowed to use them w.r.t. to the asm
    configuration
*)

(*  Main semantics theorem for inst selection:
    The inst-selected program gives same result but
    with possibly more locals used
*)

(* HOL4 ML code, not ported:
Resume inst_select_thm[Assign]:
    full_simp_tac(srw_ss())[evaluate_def]>>last_x_assum
      mp_tac>>FULL_CASE_TAC>>srw_tac[][]>>
    full_simp_tac(srw_ss())[every_var_def]>>
    imp_res_tac pull_exp_every_var_exp>>
    imp_res_tac flatten_exp_every_var_exp>>
    imp_res_tac pull_exp_ok>>
    imp_res_tac flatten_exp_ok>>
    fs[]>>
    assume_tac flatten_exp_binary_branch_exp>>
    pop_assum(qspec_then`pull_exp exp` assume_tac)>>
    imp_res_tac inst_select_exp_thm>>rev_full_simp_tac(srw_ss())[]>>
    first_x_assum(qspecl_then[`c'`,`c`]
      assume_tac)>>full_simp_tac(srw_ss())[]>>
    simp[state_component_equality,set_var_def,locals_rel_def]>>
    srw_tac[][]>>full_simp_tac(srw_ss())[lookup_insert]>>
    IF_CASES_TAC>>fs[]>>
    metis_tac[]
QED
*)

(* HOL4 ML code, not ported:
Resume inst_select_thm[Set]:
    full_simp_tac(srw_ss())[evaluate_def]>>last_x_assum mp_tac>>
    ntac 2 FULL_CASE_TAC>>full_simp_tac(srw_ss())[]>>strip_tac>>
    full_simp_tac(srw_ss())[every_var_def]>>
    imp_res_tac pull_exp_every_var_exp>>
    imp_res_tac flatten_exp_every_var_exp>>
    imp_res_tac pull_exp_ok>>
    imp_res_tac flatten_exp_ok>>
    fs[]>>
    assume_tac flatten_exp_binary_branch_exp>>
    pop_assum(qspec_then`pull_exp exp` assume_tac)>>
    imp_res_tac inst_select_exp_thm>>rev_full_simp_tac(srw_ss())[]>>
    first_x_assum(qspecl_then[`temp`,`c`]
      assume_tac)>>full_simp_tac(srw_ss())[]>>
    full_simp_tac(srw_ss())[LET_THM,evaluate_def,word_exp_def]>>
    first_assum(qspec_then`temp`
      assume_tac)>>full_simp_tac(srw_ss())[set_store_def]>>
    full_simp_tac(srw_ss())[get_var_def,state_component_equality
      ,locals_rel_def]>>
    srw_tac[][]>>`x' ≠ temp` by DECIDE_TAC>>metis_tac[]
QED
*)

(* HOL4 ML code, not ported:
Resume inst_select_thm[Store]:
    full_simp_tac(srw_ss())[evaluate_def]>>last_x_assum mp_tac>>
    ntac 3 FULL_CASE_TAC>>full_simp_tac(srw_ss())[]>>strip_tac>>
    qpat_abbrev_tac`expr = flatten_exp (pull_exp exp)`>>
    Cases_on`∃w exp'. expr = Op Add [exp';Const w]`>>
    full_simp_tac(srw_ss())[LET_THM]
    >-
      (IF_CASES_TAC
      >-
        (full_simp_tac(srw_ss())[Abbr`expr`,every_var_def]>>
        imp_res_tac pull_exp_every_var_exp>>
        imp_res_tac pull_exp_ok>>
        imp_res_tac flatten_exp_ok>>
        rfs[word_exp_def,the_words_def]>>
        Cases_on`word_exp st exp'`>>fs[]>>Cases_on`x'`>>fs[]>>
        imp_res_tac inst_select_exp_thm>>
        pop_assum kall_tac>>
        fs[AND_IMP_INTRO]>>
        pop_assum mp_tac>>impl_tac>-
          (assume_tac flatten_exp_binary_branch_exp>>
          pop_assum(qspec_then`pull_exp exp`
            mp_tac)>>simp[binary_branch_exp_def]>>
          imp_res_tac flatten_exp_every_var_exp>>
          rfs[every_var_exp_def])>>
        srw_tac[][]>>
        full_simp_tac(srw_ss())[evaluate_def,LET_THM]>>first_x_assum
          (qspecl_then [`temp`,`c`] assume_tac)>>
        fs[inst_def,word_exp_def,the_words_def]>>
        `lookup temp loc' = SOME(Word c'')` by metis_tac[]>>
        `get_var var (st with locals := loc') = SOME x` by
          (full_simp_tac(srw_ss())[get_var_def]>>
          `var ≠ temp` by DECIDE_TAC>>metis_tac[])>>
        fs[mem_store_def]>>
        simp[get_var_def] >>
        IF_CASES_TAC>>fs[state_component_equality]>>
        TOP_CASE_TAC>>fs[locals_rel_def]>>
        rw[]>>
        `x' ≠ temp` by DECIDE_TAC>>metis_tac[])
      >>
        qpat_x_assum`expr =A` sym_sub_tac>>
        imp_res_tac pull_exp_ok>>
        imp_res_tac flatten_exp_ok>>
        imp_res_tac inst_select_exp_thm>>
        full_simp_tac(srw_ss())[AND_IMP_INTRO]>>
        ntac 2 (pop_assum kall_tac)>>
        pop_assum mp_tac>>
        impl_tac>-
          (full_simp_tac(srw_ss())[every_var_def,Abbr`expr`]>>
          metis_tac[flatten_exp_every_var_exp
            ,flatten_exp_binary_branch_exp,pull_exp_every_var_exp])>>
        disch_then (qspecl_then [`temp`,`c`] assume_tac)>>
        full_simp_tac(srw_ss())[evaluate_def,LET_THM,inst_def
          ,word_exp_def]>>
        full_simp_tac(srw_ss())[word_op_def,the_words_def,Abbr`expr`]>>
        `lookup temp loc' = SOME (Word c')` by metis_tac[]>>
        `get_var var (st with locals := loc') = SOME x` by
          (full_simp_tac(srw_ss())[get_var_def,every_var_def]>>
          `var ≠ temp` by DECIDE_TAC>>
          metis_tac[])>>
        fs[mem_store_def]>>
        simp[get_var_def] >>
        IF_CASES_TAC>>fs[state_component_equality,locals_rel_def]>>
        TOP_CASE_TAC>>rw[]>>
        `x' ≠ temp` by DECIDE_TAC>>metis_tac[])
    >>
      `inst_select c temp (Store exp var) =
        Seq(inst_select_exp c temp temp expr)
        (Inst (Mem Store var (Addr temp 0w)))` by
        (full_simp_tac(srw_ss())[inst_select_def,LET_THM]>>
        EVERY_CASE_TAC>>full_simp_tac(srw_ss())[])>>
      full_simp_tac(srw_ss())[inst_select_def,LET_THM,Abbr`expr`]>>
      imp_res_tac pull_exp_ok>>
      imp_res_tac flatten_exp_ok>>
      imp_res_tac inst_select_exp_thm>>
      full_simp_tac(srw_ss())[AND_IMP_INTRO]>>
      ntac 2 (pop_assum kall_tac)>>
      pop_assum mp_tac>>
      impl_tac
      >-
        (full_simp_tac(srw_ss())[every_var_def]>>
        metis_tac[pull_exp_every_var_exp,flatten_exp_every_var_exp
          ,flatten_exp_binary_branch_exp])
      >>
      disch_then(qspecl_then [`temp`,`c`] assume_tac)>>
      fs[evaluate_def,inst_def,word_exp_def,the_words_def]>>
      `lookup temp loc' = SOME (Word c')` by metis_tac[]>>
      full_simp_tac(srw_ss())[word_op_def,every_var_def]>>
      `get_var var (st with locals := loc') = SOME x` by
        (full_simp_tac(srw_ss())[get_var_def]>>`var ≠ temp` by
          DECIDE_TAC>>
        metis_tac[])>>
      full_simp_tac(srw_ss())[mem_store_def]>>
      simp[get_var_def] >>
      IF_CASES_TAC>>fs[state_component_equality]>>
      FULL_CASE_TAC>>fs[locals_rel_def]>>rw[]>>
      `x' ≠ temp` by DECIDE_TAC>>metis_tac[]
QED
*)

(* HOL4 ML code, not ported:
Resume inst_select_thm[Seq]:
    full_simp_tac(srw_ss())[evaluate_def,LET_THM]>>Cases_on`evaluate
      (prog,st)`>>
    full_simp_tac(srw_ss())[every_var_def,GSYM AND_IMP_INTRO]>>
    `q ≠ SOME Error` by (strip_tac>>gvs[])>>
    first_assum(fn th => first_x_assum(mp_tac o C MATCH_MP th)) >>
    full_simp_tac(srw_ss())[]>> disch_then (qspec_then`loc`
      assume_tac)>>rev_full_simp_tac(srw_ss())[]>>
    IF_CASES_TAC>>full_simp_tac(srw_ss())[]>>
    metis_tac[]
QED
*)

(* HOL4 ML code, not ported:
Resume inst_select_thm[MustTerminate]:
    full_simp_tac(srw_ss())[evaluate_def,LET_THM,every_var_def]>>
    IF_CASES_TAC>>full_simp_tac(srw_ss())[]>>
    ntac 2 (pairarg_tac>>full_simp_tac(srw_ss())[])>>
    Cases_on`res'' = SOME TimeOut`>>full_simp_tac(srw_ss())[]>>
    rveq>>
    res_tac>>
    last_x_assum kall_tac>>
    ntac 2 (pop_assum kall_tac)>>
    pop_assum(qspec_then`loc` assume_tac)>>rev_full_simp_tac(srw_ss())[]
QED
*)

(* HOL4 ML code, not ported:
Resume inst_select_thm[ShareInst]:
    gvs[evaluate_def,LET_THM,every_var_def,AllCaseEqs()] >>
    qpat_abbrev_tac`expr = flatten_exp (pull_exp exp)`>>
    Cases_on`∃w exp'. expr = Op Add [exp';Const w]` >>
    gvs[]
    >- (
      IF_CASES_TAC
      >- (
        imp_res_tac pull_exp_every_var_exp>>
        imp_res_tac pull_exp_ok>>
        imp_res_tac flatten_exp_ok>>
        imp_res_tac flatten_exp_every_var_exp>>
        qspec_then `pull_exp exp` assume_tac
          flatten_exp_binary_branch_exp >>
        gvs[binary_branch_exp_def] >>
        drule inst_select_exp_thm >>
        gvs[every_var_exp_def] >>
        ntac 2 (disch_then drule) >>
        gvs[word_exp_def,the_words_def,AllCaseEqs()] >>
        disch_then $ qspecl_then [`c`,`temp`] assume_tac >>
        gvs[AllCaseEqs(),evaluate_def,COND_EXPAND_IMP,FORALL_AND_THM] >>
        gvs[AllCaseEqs(),PULL_EXISTS,
          oneline share_inst_def,
          sh_mem_load_def,sh_mem_load_byte_def,sh_mem_store_def
            ,sh_mem_store_byte_def,
          oneline sh_mem_set_var_def, sh_mem_load32_def,
            sh_mem_store32_def,
          sh_mem_load16_def,sh_mem_store16_def,
          set_var_def,locals_rel_def,word_exp_def,the_words_def
            ,word_op_def,
          get_var_def,state_component_equality,lookup_insert
            ,flush_state_def] >>
        metis_tac[lookup_insert]
      ) >>
      imp_res_tac pull_exp_every_var_exp>>
      imp_res_tac pull_exp_ok>>
      imp_res_tac flatten_exp_ok>>
      imp_res_tac flatten_exp_every_var_exp>>
      qspec_then `pull_exp exp` assume_tac flatten_exp_binary_branch_exp
        >>
      drule inst_select_exp_thm >>
      gvs[every_var_exp_def] >>
      ntac 3 (disch_then drule) >>
      disch_then $ qspecl_then [`c`,`temp`] assume_tac >>
      gvs[AllCaseEqs(),evaluate_def,COND_EXPAND_IMP,FORALL_AND_THM] >>
      gvs[AllCaseEqs(),PULL_EXISTS,
        oneline share_inst_def,
        sh_mem_load_def,sh_mem_load_byte_def,sh_mem_store_def
          ,sh_mem_store_byte_def,
        oneline sh_mem_set_var_def, sh_mem_load32_def,
          sh_mem_store32_def,
        sh_mem_load16_def,sh_mem_store16_def,
        set_var_def,locals_rel_def,word_exp_def,the_words_def
          ,word_op_def,
        get_var_def,state_component_equality,lookup_insert
          ,flush_state_def] >>
      metis_tac[lookup_insert]) >>
    imp_res_tac pull_exp_every_var_exp>>
    imp_res_tac pull_exp_ok>>
    imp_res_tac flatten_exp_ok>>
    imp_res_tac flatten_exp_every_var_exp>>
    assume_tac flatten_exp_binary_branch_exp >>
    qmatch_goalsub_abbrev_tac `evaluate prog` >>
    `prog = (Seq (inst_select_exp c temp temp expr) (ShareInst op c'
      (Var temp)),
       st with locals := loc)`
      by (unabbrev_all_tac >> PURE_REWRITE_TAC[inst_select_def, LET_THM]
        >> BETA_TAC >>
          every_case_tac >> simp[] >> metis_tac[]) >>
    qpat_x_assum `Abbrev (prog = _)` kall_tac >>
    first_x_assum $ qspec_then `pull_exp exp` assume_tac >>
    drule inst_select_exp_thm >>
    gvs[every_var_exp_def] >>
    ntac 3 (disch_then drule) >>
    disch_then $ qspecl_then [`c`, `temp`] assume_tac >>
    gvs[AllCaseEqs(),evaluate_def,COND_EXPAND_IMP,FORALL_AND_THM] >>
    gvs[AllCaseEqs(),PULL_EXISTS,
      oneline share_inst_def,
      sh_mem_load_def,sh_mem_load_byte_def,sh_mem_store_def
        ,sh_mem_store_byte_def,
      oneline sh_mem_set_var_def, sh_mem_load32_def, sh_mem_store32_def,
      sh_mem_load16_def,sh_mem_store16_def,
      set_var_def,locals_rel_def,word_exp_def,the_words_def,word_op_def,
      get_var_def,state_component_equality,lookup_insert
        ,flush_state_def] >>
    metis_tac[lookup_insert]
QED
*)

(* HOL4 ML code, not ported:
Resume inst_select_thm[If]:
    gvs[AllCaseEqs(),evaluate_def]>>
    Cases_on`ri`>>
    fs[get_var_imm_def]>>
    imp_res_tac locals_rel_get_var>>
    fs[every_var_def,every_var_imm_def]
QED
*)

(* HOL4 ML code, not ported:
Resume inst_select_thm[Call]:
  gvs [inst_select_def, every_var_def] >>
  Cases_on `ret` >> gvs [add_ret_loc_def]
  >- ( (* ret=NONE: tail call — handler not used *)
    fs [evaluate_def] >>
    DEP_REWRITE_TAC [locals_rel_get_vars_simp] >> fs [] >>
    TOP_CASE_TAC >> gvs [] >>
    TOP_CASE_TAC >> gvs [] >>
    TOP_CASE_TAC >> gvs [] >>
    PairCases_on `x'` >> gvs [] >>
    Cases_on `handler` >>
    gvs [AllCaseEqs(), call_env_def, flush_state_def, dec_clock_def,
         oneline bad_fun_return_def, AllCasePreds()] >>
    simp [state_component_equality] >>
    Cases_on `res` >> gvs [locals_rel_def] >>
    rename1 `SOME xx` >> Cases_on `xx` >> gvs []) >>
*)
  (* ret=SOME: full call *)
(* HOL4 ML code, not ported:
  PairCases_on`x` >> fs[add_ret_loc_def] >>
  drule locals_rel_evaluate_thm >>
  simp[every_var_def] >>
  disch_then drule >> simp[] >>
  disch_then drule >> strip_tac >>
  qhdtm_x_assum`evaluate`mp_tac >>
  simp[evaluate_def] >>
  simp[CaseEq"prod",CaseEq"option",CaseEq"bool",PULL_EXISTS] >>
  rpt gen_tac >> strip_tac >> gvs[]
  >- (
    gvs[add_ret_loc_def] >>
    gvs[flush_state_def, call_env_def, state_component_equality] >>
    Cases_on`handler` >> gvs[] >>
    PairCases_on`x` >> gvs[push_env_def] ) >>
  gvs[add_ret_loc_def, PULL_EXISTS] >>
  qmatch_goalsub_abbrev_tac`call_env args1 ss hhh` >>
  qmatch_asmsub_abbrev_tac`call_env args1 ss hhh1` >>
  `hhh = hhh1` by (
    Cases_on`handler` \\ gvs[Abbr`hhh`,Abbr`hhh1`, push_env_def] >>
    PairCases_on`x` \\ gvs[push_env_def] ) >>
  gvs[Abbr`hhh`] >>
  TOP_CASE_TAC >> gvs[]
  >- (
    gvs[CaseEq"bool",CaseEq"option"] >>
    first_x_assum drule >> gvs[] >>
    gvs[set_vars_def] >>
    qmatch_goalsub_abbrev_tac`s1 with locals := lll` >>
    disch_then(qspec_then`lll`mp_tac) >>
    impl_tac >- rw[locals_rel_def] >>
    strip_tac >> simp[] >>
    CASE_TAC >> gvs[locals_rel_def] >>
    CASE_TAC >> gvs[locals_rel_def] ) >>
  gvs[CaseEq"option",CaseEq"prod",CaseEq"bool"] >>
  first_x_assum drule >> gvs[] >>
  qmatch_goalsub_abbrev_tac`locals_rel _ ll1.locals` >>
  disch_then(qspec_then`ll1.locals`mp_tac) >>
  `ll1 with locals := ll1.locals = ll1` by
    simp[state_component_equality] >>
  impl_tac >- gvs[locals_rel_def] >>
  strip_tac >> gvs[] >>
  CASE_TAC >> gvs[locals_rel_def] >>
  CASE_TAC >> gvs[locals_rel_def]
QED
*)

(* HOL4 ML code, not ported:
Resume inst_select_thm[Loop]:
  gvs [every_var_def, inst_select_def] >>
  irule inst_select_Loop_helper >>
  gvs [every_name_def] >>
  simp[sptreeTheory.toAList_def, sptreeTheory.foldi_def]
QED
*)

(* HOL4 ML code, not ported:
Finalise inst_select_thm;
*)

(* three_to_two_reg semantics *)

(*Semantics preservation*)
