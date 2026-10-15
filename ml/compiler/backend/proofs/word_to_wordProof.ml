(* ======================================================== *)
(*  word_to_wordProof: ported from HOL4's
    compiler/backend/proofs/word_to_wordProofScript.sml  *)
(* ======================================================== *)

(*
  Correctness proof for word_to_word
*)

needs "compiler/backend/proofs/wordConvsProof.ml";;
needs "compiler/backend/proofs/word_allocProof.ml";;
needs "compiler/backend/proofs/word_copyProof.ml";;
needs "compiler/backend/proofs/word_cseProof.ml";;
needs "compiler/backend/proofs/word_elimProof.ml";;
needs "compiler/backend/proofs/word_instProof.ml";;
needs "compiler/backend/proofs/word_removeProof.ml";;
needs "compiler/backend/proofs/word_simpProof.ml";;
needs "compiler/backend/proofs/word_unreachProof.ml";;
needs "compiler/backend/semantics/wordConvs.ml";;
needs "compiler/backend/semantics/wordProps.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/backend/word_elim.ml";;
needs "compiler/backend/word_to_word.ml";;
needs "compiler/backend/word_unreach.ml";;
needs "lib/sptree.ml";;

(* HOL4 ML code, not ported:
val is_phy_var_tac =
    full_simp_tac(srw_ss())[reg_allocTheory.is_phy_var_def]>>
    `0<2:num` by DECIDE_TAC>>
    `∀k.(2:num)*k=k*2` by DECIDE_TAC>>
    metis_tac[arithmeticTheory.MOD_EQ_0];
*)

(*Chains up compile_single theorems*)

(* HOL4 ML code, not ported:
val size_tac=
  (full_simp_tac(srw_ss())[wordLangTheory.prog_size_def]>>DECIDE_TAC);
*)

(* The t k a c parameters don't need to be existentially quantified *)
let code_rel_def = cake_define
  `word_to_wordProof_code_rel stc ttc <=>
   (!n v. lookup n stc = SOME v ==>
          (?col t k a c.
          lookup n ttc = SOME (SND (compile_single t k a c
            ((n,v),col)))))`;;
hol4_overload "code_rel" "word_to_wordProof_code_rel";;

(* HOL4 ML code, not ported:
Resume compile_single_correct[Skip]:
  fs[evaluate_def,state_component_equality]
QED
*)

(* HOL4 ML code, not ported:
Resume compile_single_correct[Move]:
  fs[evaluate_def] >> rpt (TOP_CASE_TAC >> simp[]) >>
  simp[state_component_equality]
QED
*)

(* HOL4 ML code, not ported:
Resume compile_single_correct[Inst]:
  fs[evaluate_def] >> rpt (TOP_CASE_TAC >> simp[]) >>
  old_drule inst_const_full >> simp[state_component_equality]
QED
*)

(* HOL4 ML code, not ported:
Resume compile_single_correct[Assign]:
  fs[evaluate_def] >> rpt (TOP_CASE_TAC >> simp[]) >>
  simp[state_component_equality]
QED
*)

(* HOL4 ML code, not ported:
Resume compile_single_correct[Get]:
  fs[evaluate_def] >> rpt (TOP_CASE_TAC >> simp[]) >>
  simp[state_component_equality]
QED
*)

(* HOL4 ML code, not ported:
Resume compile_single_correct[Set]:
  fs[evaluate_def] >> rpt (TOP_CASE_TAC >> simp[]) >>
  simp[state_component_equality]
QED
*)

(* HOL4 ML code, not ported:
Resume compile_single_correct[Store]:
  fs[evaluate_def] >> rpt (TOP_CASE_TAC >> simp[]) >>
  old_drule mem_store_const >> simp[state_component_equality]
QED
*)

(* HOL4 ML code, not ported:
Resume compile_single_correct[MustTerminate]:
  fs[evaluate_def,AND_IMP_INTRO]>>
  rpt (TOP_CASE_TAC >> fs[]) >>
  last_x_assum(qspecl_then[`st with
    <|clock:=MustTerminate_limit(:'a);termdep:=st.termdep-1|>`,`p`,`l`
    ,`cc`] mp_tac)>>
  impl_tac >-  simp[]>>
  rw[]>>
  qexists_tac`perm'`>>fs[]>>
  pop_assum mp_tac >>
  rpt(pairarg_tac >> fs[])>>
  rw[]>> ntac 5 (pop_assum mp_tac) >>
  IF_CASES_TAC>>full_simp_tac(srw_ss())[]>>
  rw[] >> rw[]>>
  fs[state_component_equality]
QED
*)

(* Call: dispatch with Tail-call branch closing inline (via
   every_case_tac >> gvs[bad_fun_return_def] for cake-while's
   Break/Continue handling), then suspend "non_tail_call" for
   the more involved non-tail-call branch. *)
(* HOL4 ML code, not ported:
Resume compile_single_correct[Call]:
  fs[evaluate_def,AND_IMP_INTRO]>>
  ntac 2 (TOP_CASE_TAC>> fs[]) >>
  Cases_on`find_code o1 (add_ret_loc o' x) st.code st.stack_size`>>
  fs []>>
  Cases_on`o'`>>full_simp_tac(srw_ss())[]>>
  Cases_on`x'`>>simp[]>>
  Cases_on `r` >> simp [] >>
  imp_res_tac find_code_thm>>
  pop_assum(qspec_then`l` mp_tac)>>
  (impl_tac>-
    (fs[code_rel_def]>>
    metis_tac[]))>>
  rw[]>> rfs[]
  >- ( (*Tail calls*)
    ntac 2 (TOP_CASE_TAC >>full_simp_tac(srw_ss())[])
    >- simp[flush_state_def,state_component_equality] >>
    qabbrev_tac`stt = call_env q r' (dec_clock st)`>>
    first_x_assum(qspecl_then[`stt`,`prog'`,`l`,`cc`] mp_tac)>>
    impl_tac>-
      (full_simp_tac(srw_ss())[Abbr`stt`,dec_clock_def]>>
      DECIDE_TAC)>>
    srw_tac[][]>>
    Q.ISPECL_THEN [`n`,`q'`,`LENGTH q`,`stt with permute:=perm'`]
     mp_tac (Q.GEN `name` compile_single_lem)>>
    impl_tac>-
      (full_simp_tac(srw_ss())[Abbr`stt`,call_env_def]>>
      simp[domain_fromList2,word_allocTheory.even_list_def])>>
    qpat_abbrev_tac`A = compile_single t k a c B`>>
    PairCases_on`A`>>srw_tac[][]>>full_simp_tac(srw_ss())[LET_THM]>>
    pop_assum mp_tac>>
    pairarg_tac>>full_simp_tac(srw_ss())[Abbr`stt`] >>
    strip_tac
    >-
      (qexists_tac`perm''`>>full_simp_tac(srw_ss())[dec_clock_def])>>
    Cases_on`res`>>full_simp_tac(srw_ss())[]
    >-
      (qexists_tac`perm''`>>full_simp_tac(srw_ss())[dec_clock_def])>>
    Cases_on`x' = Error`>>full_simp_tac(srw_ss())[]
    >-
      (qexists_tac`perm''`>>full_simp_tac(srw_ss())[dec_clock_def])>>
    ntac 2 (pop_assum mp_tac) >>
    pairarg_tac>>full_simp_tac(srw_ss())[]>>
    rw[]>>
    qpat_x_assum`(λ(x,y). _) _`mp_tac >>
    pairarg_tac>>fs[]>>
    qpat_x_assum`Abbrev( (_,_,_) = _)` (mp_tac o GSYM)>>
    simp[Once markerTheory.Abbrev_def]>>rw[]>>
    rw[]>>fs[dec_clock_def,call_env_def,flush_state_def]>>
    qmatch_asmsub_abbrev_tac`evaluate (q',stt)`>>
    Q.ISPECL_THEN [`q'`,`stt`,`rcst.permute`] mp_tac
      permute_swap_lemma>>
    fs[]>>rw[]>>
    qexists_tac`perm'''`>>
    fs[Abbr`stt`,word_state_eq_rel_def,state_component_equality]>>
    fs[code_rel_def]>>
    every_case_tac >> gvs[wordSemTheory.bad_fun_return_def]) >>
  rename [`find_code _ (add_ret_loc (SOME xx) _)`] >>
  `?xn xnames xrh xl1 xl2. xx = (xn, xnames, xrh, xl1, xl2)`
     by (PairCases_on`xx`>>simp[]) >> rveq >>
       full_simp_tac(srw_ss())[]>>
  ntac 2 (TOP_CASE_TAC>>fs[]) >>
  IF_CASES_TAC>-
    (Cases_on `o0` >> TRY (PairCases_on `x''`) >>
     fs[call_env_def,flush_state_def,state_component_equality,
      stack_size_def, stack_size_frame_def, push_env_def,
        env_to_list_def, LET_THM])>>
  fs[]>>
  qabbrev_tac`stt = call_env q r' (push_env x' o0 (dec_clock st))`>>
  first_assum(qspecl_then[`stt`,`prog'`,`l`,`cc`] mp_tac)>>
  impl_tac>-
    (fs[Abbr`stt`,dec_clock_def]>>
    DECIDE_TAC)>>
  rw[]>>
  Q.ISPECL_THEN [`n`,`q'`,`LENGTH q`,`stt with permute:=perm'`] mp_tac
    (Q.GEN `name` compile_single_lem)>>
  impl_tac>-
    (full_simp_tac(srw_ss())[Abbr`stt`,call_env_def] >>
    simp[domain_fromList2,word_allocTheory.even_list_def])>>
  qpat_abbrev_tac`A = compile_single t k a c B`>>
  PairCases_on`A`>>srw_tac[][]>>full_simp_tac(srw_ss())[LET_THM]>>
  pop_assum mp_tac >>
  pairarg_tac>>full_simp_tac(srw_ss())[Abbr`stt`] >>
  strip_tac
  >-
    (qexists_tac`λn. if n = 0:num then st.permute 0 else perm'' (n-1)`>>
    Cases_on`o0`>>TRY(PairCases_on`x''`)>>
    full_simp_tac(srw_ss())[push_env_def,env_to_list_def,LET_THM
      ,dec_clock_def,call_env_def,flush_state_def,ETA_AX])>>
  Cases_on`res`>>full_simp_tac(srw_ss())[]
  >-
    (qexists_tac`λn. if n = 0:num then st.permute 0 else perm'' (n-1)`>>
    Cases_on`o0`>>TRY(PairCases_on`x''`)>>
    full_simp_tac(srw_ss())[push_env_def,env_to_list_def,LET_THM
      ,dec_clock_def,call_env_def,flush_state_def,ETA_AX])>>
  Cases_on`x''`>>full_simp_tac(srw_ss())[]
  >-
*)
    (*Manual simulation for Result*)
(* HOL4 ML code, not ported:
    (Cases_on`w = Loc xl1 xl2 ⇒ LENGTH l'' ≠ LENGTH
      xn`>>full_simp_tac(srw_ss())[]
    >-
      (qexists_tac`λn. if n = 0:num then st.permute 0 else perm''
        (n-1)`>>
      Cases_on`o0`>>TRY(PairCases_on`x''`)>>
      full_simp_tac(srw_ss())[push_env_def,env_to_list_def,LET_THM
        ,dec_clock_def,call_env_def,flush_state_def,ETA_AX])
    >>
    Cases_on`pop_env rst`>>full_simp_tac(srw_ss())[]
    >-
      (qexists_tac`λn. if n = 0:num then st.permute 0 else perm''
        (n-1)`>>
      Cases_on`o0`>>TRY(PairCases_on`x''`)>>
      full_simp_tac(srw_ss())[push_env_def,env_to_list_def,LET_THM
        ,dec_clock_def,call_env_def,flush_state_def,ETA_AX])
    >>
    Cases_on `domain x''.locals = domain (FST x') ∪ domain (SND
      x')`>>full_simp_tac(srw_ss())[]
    >-
      (qpat_x_assum`(λ(x,y). _) _`mp_tac >>
       pairarg_tac>>full_simp_tac(srw_ss())[]>>
       strip_tac >>
       last_x_assum kall_tac>>
       qpat_x_assum`(λ(x,y). _) _`mp_tac >>
       pairarg_tac>>full_simp_tac(srw_ss())[]>>
       strip_tac >>
       last_x_assum(qspecl_then[`(set_vars xn l'' x'') with
         permute:=rcst.permute`,`xrh`,`rst1.code`,`cc`]mp_tac)>>
       impl_tac>-
         (simp[]>>
         `rst.clock < st.clock` by
           (imp_res_tac evaluate_clock>>
           full_simp_tac(srw_ss())[call_env_def,flush_state_def
             ,dec_clock_def]>>
           DECIDE_TAC)>>
         old_drule pop_env_const >> fs[] >> disch_then kall_tac >>
         old_drule pop_env_termdep>> fs[] >> disch_then kall_tac >>
         old_drule pop_env_code_gc_fun_clock >>
         disch_then (mp_tac o LIST_CONJ o (map SYM) o CONJUNCTS) >>
         fs[] >> disch_then kall_tac >>
         imp_res_tac evaluate_consts >> fs[] >>
         imp_res_tac evaluate_clock >> fs[] >>
         fs[word_allocProofTheory.word_state_eq_rel_def]>>
         metis_tac[])>>
       rw[]>>
       Q.ISPECL_THEN[`q'`,`call_env q r' (push_env x' o0 (dec_clock st))
         with permute:=perm''`,`perm'''`] assume_tac
         permute_swap_lemma>>
       rfs[]>>
       qexists_tac`λn. if n = 0:num then st.permute 0 else perm''''
         (n-1)`>>
       Cases_on`o0`>>TRY(PairCases_on `x'''`)>>
       (fs[call_env_def,flush_state_def,push_env_def,dec_clock_def
         ,env_to_list_def,ETA_AX]>>
       qpat_x_assum`((λ(res',rcst). P) A)` mp_tac>>
       pairarg_tac>>rev_full_simp_tac(srw_ss())[]>>full_simp_tac(srw_ss
         ())[]>>
       `pop_env rst1 =
         SOME (x'' with <|compile:= cc;
                          compile_oracle :=
            (I ## MAP (λp. compile_single tt kk aa co (p,NONE))) ∘
            x''.compile_oracle;
            code:=rst1.code; permute:=rcst.permute|>)` by
         (fs[pop_env_def,word_allocProofTheory.word_state_eq_rel_def]>>
         qpat_x_assum`rst1 = _` SUBST_ALL_TAC>>
         simp[]>>
         EVERY_CASE_TAC>>fs[state_component_equality])>>
       simp[]>>
       TRY (rw[]>>pairarg_tac>>fs[set_var_def]>>NO_TAC)>>
       qpat_x_assum`rst1 = _` SUBST_ALL_TAC>>
       fs[pop_env_def,word_allocProofTheory.word_state_eq_rel_def]>>
       EVERY_CASE_TAC>>fs[state_component_equality]>>
       qpat_x_assum`pop_env rst = _` mp_tac>>
       fs[pop_env_def]>>
       EVERY_CASE_TAC>>fs[state_component_equality]))
    >>
    qexists_tac`λn. if n = 0:num then st.permute 0 else perm'' (n-1)`>>
    Cases_on`o0`>>TRY(PairCases_on`x'''`)>>
    full_simp_tac(srw_ss())[push_env_def,env_to_list_def,LET_THM
      ,dec_clock_def,call_env_def,flush_state_def,ETA_AX])
  >-
*)
    (*Manual simulation for Exceptions*)
(* HOL4 ML code, not ported:
    (Cases_on`o0`>>full_simp_tac(srw_ss())[]
    >-
      (pop_assum mp_tac >> pairarg_tac>>full_simp_tac(srw_ss())[]>>
      strip_tac >>
      qmatch_assum_abbrev_tac `evaluate(q',A) = _`>>
      Q.ISPECL_THEN [`q'`,`A`,`rcst.permute`] mp_tac
        permute_swap_lemma>>
      simp[Abbr`A`]>>
      impl_tac>-
        (qpat_x_assum`B=res'` sym_sub_tac>>full_simp_tac(srw_ss())[])>>
      rw[]>>
      qexists_tac`λn. if n = 0:num then st.permute 0 else perm'''
        (n-1)`>>
      fs[push_env_def,env_to_list_def,dec_clock_def,call_env_def
        ,flush_state_def,ETA_AX]>>
      qpat_x_assum`(λ(x,y). _) _`mp_tac >>
      pairarg_tac>>rfs[]>>fs[]>>
      rw[]>>fs[word_state_eq_rel_def,state_component_equality]>>
      metis_tac[])
    >>
    qmatch_goalsub_rename_tac`push_env _ (SOME p)` >>
    PairCases_on`p`>>full_simp_tac(srw_ss())[]>>
    Cases_on`w ≠ Loc p2 p3`
    >-
      (qexists_tac`λn. if n = 0:num then st.permute 0 else perm''
        (n-1)`>>
      full_simp_tac(srw_ss())[push_env_def,env_to_list_def,LET_THM
        ,dec_clock_def,call_env_def,flush_state_def,ETA_AX])>>
    Cases_on`domain rst.locals ≠ domain (FST x') ∪ domain (SND x')`
    >-
      (qexists_tac`λn. if n = 0:num then st.permute 0 else perm''
        (n-1)`>>
      full_simp_tac(srw_ss())[push_env_def,env_to_list_def,LET_THM
        ,dec_clock_def,call_env_def,flush_state_def,ETA_AX])
    >>
    qpat_x_assum`((λ(res',rcst). P) A)` mp_tac>>
    pairarg_tac>>full_simp_tac(srw_ss())[]>>strip_tac>>
    last_x_assum kall_tac>>
    qpat_x_assum`(λ(x,y). _) _`mp_tac >>
    pairarg_tac>>full_simp_tac(srw_ss())[]>>
    strip_tac >>
    last_x_assum(qspecl_then[`(set_var p0 w0 rst) with
      permute:=rcst.permute`,`p1`,`rst1.code`,`cc`]mp_tac)>>
    impl_tac>-
      (simp[]>>
      imp_res_tac evaluate_clock>> fs[] >>
      imp_res_tac evaluate_consts>>fs[dec_clock_def]>>
      fs[word_state_eq_rel_def]>>
      gs[]) >>
    rw[]>>
    Q.ISPECL_THEN[`q'`,`call_env q r' (push_env x' (SOME (p0,p1,p2,p3))
      (dec_clock st)) with permute:=perm''`,`perm'''`] assume_tac
      permute_swap_lemma>>
    rfs[]>>
    qexists_tac`λn. if n = 0:num then st.permute 0 else perm''''
      (n-1)`>>
    fs[call_env_def,flush_state_def,push_env_def,dec_clock_def
      ,env_to_list_def,ETA_AX]>>
    `domain rst1.locals = domain (FST x') ∪ domain (SND x')` by
      (qpat_x_assum`rst1=_` SUBST_ALL_TAC>>rw[])>>
    simp[]>>
    pairarg_tac>>fs[]>>
    qpat_x_assum`rst1=_` SUBST_ALL_TAC>>fs[]>>
    rpt(pairarg_tac>>fs[])>>
    fs[]>>
    pop_assum mp_tac>>
    qmatch_goalsub_abbrev_tac`_ (evaluate (_,A))`>>
    qmatch_asmsub_abbrev_tac`_ (evaluate (_,B))`>>
    strip_tac>>
    `A = B` by
      (unabbrev_all_tac>>fs[state_component_equality
        ,word_state_eq_rel_def] >>
      simp[set_var_def])>>
    rfs[]>>
    unabbrev_all_tac>>fs[])
  >>
    TRY(
    pop_assum mp_tac >> pairarg_tac>>
    fs[]>>
    Q.ISPECL_THEN [`q'`,`call_env q r' (push_env x' o0 (dec_clock st))
      with permute:=perm''`,`rcst.permute`] mp_tac permute_swap_lemma>>
    fs[]>>rw[]>>
    qexists_tac`λn. if n = 0:num then st.permute 0 else perm''' (n-1)`>>
    Cases_on`o0`>>TRY(PairCases_on`x''`)>>
    fs[push_env_def,env_to_list_def,dec_clock_def,call_env_def
      ,flush_state_def,ETA_AX]>>
    qpat_x_assum`(λ(a,b). _) _`mp_tac >>
    pairarg_tac>>rfs[]>>
    fs[]>>rw[]>>
    fs[word_state_eq_rel_def,state_component_equality]>>
    metis_tac[])
  >>
    qexists_tac`λn. if n = 0:num then st.permute 0 else perm'' (n-1)`>>
    Cases_on`o0`>>TRY(PairCases_on`x''`)>>
    fs[push_env_def,env_to_list_def,dec_clock_def,call_env_def
      ,flush_state_def,ETA_AX]
QED
*)


(* HOL4 ML code, not ported:
Resume compile_single_correct[Seq]:
  fs[evaluate_def,LET_THM,AND_IMP_INTRO]>>
  first_assum(qspecl_then[`p`,`st`,`l`,`cc`] mp_tac)>>
  impl_tac>- size_tac>>
  strip_tac>>
  pop_assum mp_tac >>
  pairarg_tac>>fs[]>>
  strip_tac
  >- (qexists_tac`perm'`>>srw_tac[][]) >>
  pop_assum mp_tac >>
  pairarg_tac>>fs[]>>
  strip_tac >>
  Cases_on`res` >> simp[]
  >- (
*)
    (* NONE case (first w/o reverse) *)
(* HOL4 ML code, not ported:
    full_simp_tac std_ss [GSYM PULL_FORALL]>>
    `rst.clock ≤ st.clock ∧ rst.termdep = st.termdep` by
      (imp_res_tac evaluate_clock>>
      full_simp_tac(srw_ss())[state_component_equality])>>
    Cases_on`rst.clock = st.clock`
    >-
      (first_x_assum(qspecl_then[`p0`,`rst`,`rst1.code`,`cc`] mp_tac)>>
      impl_tac>-(
        imp_res_tac evaluate_consts>>
        fs[]>>
        size_tac)>>
      rw[]>>
      Q.ISPECL_THEN[`p`,`st with permute:=perm'`,`perm''`]
        assume_tac permute_swap_lemma>>
      rfs[]>>
      qexists_tac`perm'''`>>
      rw[]>>fs[]>>
      pairarg_tac>>fs[]>>
      qpat_x_assum`rst1 = _` SUBST_ALL_TAC>>fs[])
    >>
      first_x_assum(qspecl_then[`rst`,`p0`,`rst1.code`,`cc`] mp_tac)>>
      impl_tac>- (
        imp_res_tac evaluate_consts>>
        fs[]>>
        size_tac)>>
      rw[]>>
      Q.ISPECL_THEN[`p`,`st with permute:=perm'`,`perm''`]
        assume_tac permute_swap_lemma>>
      rfs[]>>
      qexists_tac`perm'''`>>
      rw[]>>fs[]>>
      pairarg_tac>>fs[]>>
      qpat_x_assum`rst1 = _` SUBST_ALL_TAC>>fs[]) >>
*)
  (* SOME case *)
(* HOL4 ML code, not ported:
  qexists_tac`perm'`>>fs[]
QED
*)

(* HOL4 ML code, not ported:
Resume compile_single_correct[If]:
  simp[evaluate_def,get_var_def,get_var_imm_def]>>
  ntac 2 (TOP_CASE_TAC>>full_simp_tac(srw_ss())[])>>
  Cases_on`r`>>full_simp_tac(srw_ss())[get_var_imm_def,get_var_def]>>
  rpt(TOP_CASE_TAC>>full_simp_tac(srw_ss())[])>>
  TRY(qpat_abbrev_tac`prog = p`)>>
  TRY(qpat_abbrev_tac`prog = p0`)>>
  first_x_assum(qspecl_then[`prog`,`st`,`l`,`cc`] mp_tac)>>
  (impl_tac>-size_tac>>srw_tac[][])
QED
*)

(* HOL4 ML code, not ported:
Resume compile_single_correct[Loop]:
  rename1 `Loop names body exit_names` >>
  fs[evaluate_def,AND_IMP_INTRO] >>
  TOP_CASE_TAC >> simp[]
  >- (
*)
    (* SOME case: cut_state succeeds *)
(* HOL4 ML code, not ported:
    rename1`cut_state (names,LN) st = SOME stt` >>
    `stt.code = st.code ∧ stt.compile = st.compile ∧
     stt.compile_oracle = st.compile_oracle ∧ stt.gc_fun = st.gc_fun ∧
     stt.clock = st.clock ∧ stt.termdep = st.termdep ∧
     stt.permute = st.permute` by
      (imp_res_tac cut_state_const >> fs[]) >>
    first_assum(qspecl_then[`body`,`stt`,`l`,`cc`] mp_tac) >>
    impl_tac >- (
      fs[] >> size_tac) >>
    strip_tac >>
    pop_assum mp_tac >>
    pairarg_tac >> simp[] >>
    strip_tac
    >- (qexists_tac`perm'`>>simp[]) >>
    pop_assum mp_tac >>
    pairarg_tac >> simp[] >>
    strip_tac >>
    `rst.clock = rst1.clock ∧ rst.termdep = rst1.termdep` by
      (qpat_x_assum `rst1 = _` SUBST1_TAC >> simp[]) >>
    Cases_on `cont_loop res` >> fs[]
    >- (
      Cases_on `rst1.clock = 0` >> fs[]
      >- (
        qexists_tac`perm'` >>
        qpat_x_assum `evaluate (body, stt with permute := perm') = _`
          (fn th => simp[th]) >>
        qpat_x_assum `rst1 = _` SUBST1_TAC >>
        simp[flush_state_def, state_component_equality]) >>
      simp[STOP_def] >>
      `(dec_clock rst).clock < st.clock ∧
       st.termdep = (dec_clock rst).termdep ∧
       code_rel (dec_clock rst).code rst1.code ∧
       domain (dec_clock rst).code = domain rst1.code ∧
       (dec_clock rst).compile =
         (λconf progs. cc conf (MAP (λp. compile_single tt kk aa co
           (p,NONE)) progs)) ∧
       gc_fun_const_ok (dec_clock rst).gc_fun` by (
        imp_res_tac evaluate_clock >>
        imp_res_tac evaluate_consts >>
        fs[dec_clock_def]) >>
      first_x_assum(qspecl_then[`dec_clock rst`,
        `Loop names body exit_names`, `rst1.code`, `cc`] mp_tac) >>
      impl_tac >- simp[] >>
      strip_tac >>
      `res ≠ SOME Error` by (
        Cases_on `res` >> fs[cont_loop_def] >>
        rename1 `cont_loop (SOME xx)` >> Cases_on `xx` >>
          fs[cont_loop_def]) >>
      Q.ISPECL_THEN[`body`, `stt with permute := perm'`, `perm''`]
        mp_tac permute_swap_lemma >>
      simp[] >> strip_tac >>
      rename1 `evaluate (body, stt with permute := perm_swap) = (res,
        rst with permute := _)` >>
      qexists_tac `perm_swap` >>
      qpat_x_assum `evaluate (body, stt with permute := perm_swap) = _`
        (fn th => simp[th]) >>
      `(rst with permute := perm'').clock = rst1.clock ∧
       dec_clock (rst with permute := perm'') = dec_clock rst with
         permute := perm''` by
        simp[dec_clock_def] >>
      simp[STOP_def] >>
      qpat_x_assum `(λ(x,y). _) (evaluate (Loop _ _ _, _))` mp_tac >>
      pairarg_tac >> simp[] >>
      strip_tac
      >- (qpat_x_assum `rst1 = _` SUBST1_TAC >> simp[]) >>
      disj2_tac >>
      qpat_x_assum `(λ(x,y). _) _` mp_tac >>
      pairarg_tac >> simp[] >>
      strip_tac >>
      qpat_x_assum `rst1 = _` SUBST1_TAC >>
      simp[dec_clock_def, state_component_equality] >>
      qpat_x_assum `evaluate (Loop _ _ _, _) = (res1', rst1')` mp_tac >>
      simp[dec_clock_def] >> strip_tac >>
      qpat_x_assum `rst1' = _` SUBST1_TAC >>
      simp[]) >>
    Cases_on `res = SOME (Break 0)` >> fs[]
    >- (
      qexists_tac `perm'` >>
      qpat_x_assum `evaluate (body, stt with permute := perm') = _` (fn
        th => simp[th]) >>
      qpat_x_assum `rst1 = _` SUBST1_TAC >>
      simp[] >>
      Cases_on `cut_state (exit_names, LN) rst` >> simp[] >>
      imp_res_tac cut_state_const >> fs[] >>
      simp[state_component_equality]) >>
    qexists_tac `perm'` >>
    qpat_x_assum `evaluate (body, stt with permute := perm') = _` (fn th
      => simp[th]) >>
    qpat_x_assum `rst1 = _` SUBST1_TAC >>
    Cases_on `res` >> fs[exit_loop_def] >>
    rename1 `SOME xx` >>
    Cases_on `xx` >> fs[exit_loop_def, state_component_equality]) >>
*)
  (* NONE case *)
(* HOL4 ML code, not ported:
  qexists_tac`st.permute`>>simp[rm_perm,state_component_equality]
QED
*)

(* HOL4 ML code, not ported:
Resume compile_single_correct[Alloc]:
  qexists_tac`st.permute`>>fs[rm_perm]>>
  fs[evaluate_def,get_var_def]>>
  ntac 2 (TOP_CASE_TAC>>fs[])>>
  fs[alloc_def]>>
  TOP_CASE_TAC>>fs[]>>
  fs[push_env_def,env_to_list_def,set_store_def,gc_def]>>
  qpat_abbrev_tac`A = st.gc_fun B`>>
  Cases_on`A`>>fs[]>>
  PairCases_on`x'`>>fs[]>>
  qpat_abbrev_tac`A = dec_stack B C`>>
  Cases_on`A`>>fs[pop_env_def]>>
  Cases_on`x'`>>fs[]>>Cases_on`h`>>fs[]>>
  EVERY_CASE_TAC>>fs[has_space_def]>>
  rfs[call_env_def,flush_state_def]
QED
*)

(* HOL4 ML code, not ported:
Resume compile_single_correct[StoreConsts]:
  fs[evaluate_def,state_component_equality] >> every_case_tac >> fs[]
QED
*)

(* HOL4 ML code, not ported:
Resume compile_single_correct[Raise]:
  fs[evaluate_def,jump_exc_def,state_component_equality] >>
    every_case_tac >> fs[]
QED
*)

(* HOL4 ML code, not ported:
Resume compile_single_correct[Return]:
  fs[evaluate_def,flush_state_def,state_component_equality] >>
    every_case_tac >> fs[]
QED
*)

(* HOL4 ML code, not ported:
Resume compile_single_correct[Break]:
  qexists_tac`st.permute`>>fs[rm_perm]>>
  fs[evaluate_def,state_component_equality]
QED
*)

(* HOL4 ML code, not ported:
Resume compile_single_correct[Continue]:
  qexists_tac`st.permute`>>fs[rm_perm]>>
  fs[evaluate_def,state_component_equality]
QED
*)

(* HOL4 ML code, not ported:
Resume compile_single_correct[Tick]:
  fs[evaluate_def,flush_state_def,dec_clock_def
    ,state_component_equality] >> every_case_tac >> fs[]
QED
*)

(* HOL4 ML code, not ported:
Resume compile_single_correct[OpCurrHeap]:
  fs[evaluate_def,state_component_equality] >> every_case_tac >> fs[]
QED
*)

(* HOL4 ML code, not ported:
Resume compile_single_correct[LocValue]:
  fs[evaluate_def,state_component_equality] >> every_case_tac >> fs[]
QED
*)

(* HOL4 ML code, not ported:
Resume compile_single_correct[Install]:
  qexists_tac`st.permute`>>fs[rm_perm]>>
  ntac 3 (last_x_assum kall_tac)>>
  simp[evaluate_def]>>
  ntac 9 (TOP_CASE_TAC>>fs[])>>
  Cases_on`st.compile_oracle 0`>>fs[]>>
  ntac 4 (TOP_CASE_TAC>>fs[])>>
  Cases_on`r`>>fs[]>>
  ntac 3 (TOP_CASE_TAC>>fs[])>>
  PairCases_on`h`>>fs[compile_single_def,shift_seq_def]>>
  TOP_CASE_TAC>>fs[]>>
  conj_tac>-
    (old_drule (GEN_ALL code_rel_union_fromAList)>>
    simp[]>>
    disch_then(qspecl_then[`tt`,`kk`,`co`,`aa`,`(h0,h1,h2)::t`]
      assume_tac)>>
    fs[compile_single_def])>>
  conj_tac>-
    (simp[domain_union]>>AP_TERM_TAC>>
    simp[domain_fromAList]>>AP_TERM_TAC>>
    simp[EXTENSION,MAP_MAP_o,compile_single_def,MEM_MAP,EXISTS_PROD])>>
  simp[state_component_equality,o_DEF]
QED
*)

(* HOL4 ML code, not ported:
Resume compile_single_correct[CodeBufferWrite]:
  fs[evaluate_def,state_component_equality] >> every_case_tac >> fs[]
QED
*)

(* HOL4 ML code, not ported:
Resume compile_single_correct[DataBufferWrite]:
  fs[evaluate_def,state_component_equality] >> every_case_tac >> fs[]
QED
*)

(* HOL4 ML code, not ported:
Resume compile_single_correct[FFI]:
  fs[evaluate_def,flush_state_def,state_component_equality] >>
    every_case_tac >> fs[]
QED
*)

(* HOL4 ML code, not ported:
Resume compile_single_correct[ShareInst]:
  fs[evaluate_def,state_component_equality]>>
  qexists_tac`st.permute`>>
  rpt (TOP_CASE_TAC >> fs[state_component_equality]) >>
  fs[DefnBase.one_line_ify NONE share_inst_def,
    DefnBase.one_line_ify NONE sh_mem_set_var_def,
    sh_mem_load_def,sh_mem_load_byte_def,sh_mem_load32_def,
    sh_mem_load16_def,sh_mem_store16_def,
    sh_mem_store_def,sh_mem_store_byte_def,sh_mem_store32_def] >>
  rpt (TOP_CASE_TAC >>
    fs[state_component_equality,set_var_def,flush_state_def])
QED
*)

(* HOL4 ML code, not ported:
Finalise compile_single_correct;
*)

(* HOL4 ML code, not ported:
val rmt_thms = (remove_must_terminate_conventions|>SIMP_RULE std_ss
  [LET_THM,FORALL_AND_THM])|>CONJUNCTS;
*)

(* HOL4 ML code, not ported:
val rmd_thms = (remove_dead_prog_conventions|>SIMP_RULE std_ss
  [LET_THM,FORALL_AND_THM])|>CONJUNCTS;
*)

(* HOL4 ML code, not ported:
val cond16bit_inst_select_exp = cond16bit_inst_select_exp' |> SIMP_RULE
  std_ss [];
*)

(* syntax going into stackLang *)

(**** more on syntactic form restrictions ****)


(***** compile_single correctness for no_alloc & no_install ******)

(* HOL4 ML code, not ported:
Resume no_install_no_alloc_compile_single_correct[ni_Skip]:
  fs[evaluate_def, state_component_equality]
QED
*)

(* HOL4 ML code, not ported:
Resume no_install_no_alloc_compile_single_correct[ni_Move]:
  fs[evaluate_def] >> rpt (TOP_CASE_TAC >> simp[]) >>
  simp[state_component_equality]
QED
*)

(* HOL4 ML code, not ported:
Resume no_install_no_alloc_compile_single_correct[ni_Inst]:
  fs[evaluate_def] >> rpt (TOP_CASE_TAC >> simp[]) >>
  old_drule inst_const_full >> simp[state_component_equality]
QED
*)

(* HOL4 ML code, not ported:
Resume no_install_no_alloc_compile_single_correct[ni_Assign]:
  fs[evaluate_def] >> rpt (TOP_CASE_TAC >> simp[]) >>
  simp[state_component_equality]
QED
*)

(* HOL4 ML code, not ported:
Resume no_install_no_alloc_compile_single_correct[ni_Get]:
  fs[evaluate_def] >> rpt (TOP_CASE_TAC >> simp[]) >>
  simp[state_component_equality]
QED
*)

(* HOL4 ML code, not ported:
Resume no_install_no_alloc_compile_single_correct[ni_Set]:
  fs[evaluate_def] >> rpt (TOP_CASE_TAC >> simp[]) >>
  simp[state_component_equality]
QED
*)

(* HOL4 ML code, not ported:
Resume no_install_no_alloc_compile_single_correct[ni_Store]:
  fs[evaluate_def] >> rpt (TOP_CASE_TAC >> simp[]) >>
  old_drule mem_store_const >> simp[state_component_equality]
QED
*)

(* HOL4 ML code, not ported:
Resume no_install_no_alloc_compile_single_correct[ni_MustTerminate]:
  fs[evaluate_def, no_install_def, no_alloc_def] >>
  rpt (TOP_CASE_TAC >> fs[]) >>
  last_x_assum(qspecl_then[`st with
    <|clock:=MustTerminate_limit(:'a);termdep:=st.termdep-1|>`,`p`,`l`]
    mp_tac)>>
  impl_tac >- simp[] >>
  disch_tac >> fs[] >>
  qexists_tac`perm'`>>fs[] >>
  rpt (pairarg_tac >> fs[]) >>
  fs[bool_case_eq] >>
  fs[state_component_equality]
QED
*)

(* HOL4 ML code, not ported:
Resume no_install_no_alloc_compile_single_correct[ni_Break]:
  fs[evaluate_def, state_component_equality]
QED
*)

(* HOL4 ML code, not ported:
Resume no_install_no_alloc_compile_single_correct[ni_Continue]:
  fs[evaluate_def, state_component_equality]
QED
*)

(* HOL4 ML code, not ported:
Resume no_install_no_alloc_compile_single_correct[ni_Alloc]:
  fs[no_alloc_def, no_install_def] >>
  fs[evaluate_def, flush_state_def, state_component_equality] >>
  every_case_tac >> fs[]
QED
*)

(* HOL4 ML code, not ported:
Resume no_install_no_alloc_compile_single_correct[ni_StoreConsts]:
  fs[no_alloc_def, no_install_def] >>
  fs[evaluate_def, flush_state_def, state_component_equality] >>
  every_case_tac >> fs[]
QED
*)

(* HOL4 ML code, not ported:
Resume no_install_no_alloc_compile_single_correct[ni_Raise]:
  fs[no_alloc_def, no_install_def] >>
  fs[evaluate_def, jump_exc_def, flush_state_def,
    state_component_equality] >>
  every_case_tac >> fs[]
QED
*)

(* HOL4 ML code, not ported:
Resume no_install_no_alloc_compile_single_correct[ni_Return]:
  fs[no_alloc_def, no_install_def] >>
  fs[evaluate_def, flush_state_def, state_component_equality] >>
  every_case_tac >> fs[]
QED
*)

(* HOL4 ML code, not ported:
Resume no_install_no_alloc_compile_single_correct[ni_Tick]:
  fs[no_alloc_def, no_install_def] >>
  fs[evaluate_def, dec_clock_def, flush_state_def,
    state_component_equality] >>
  every_case_tac >> fs[]
QED
*)

(* HOL4 ML code, not ported:
Resume no_install_no_alloc_compile_single_correct[ni_OpCurrHeap]:
  fs[no_alloc_def, no_install_def] >>
  fs[evaluate_def, state_component_equality] >>
  every_case_tac >> fs[]
QED
*)

(* HOL4 ML code, not ported:
Resume no_install_no_alloc_compile_single_correct[ni_LocValue]:
  fs[no_alloc_def, no_install_def] >>
  fs[evaluate_def, state_component_equality] >>
  every_case_tac >> fs[]
QED
*)

(* HOL4 ML code, not ported:
Resume no_install_no_alloc_compile_single_correct[ni_Install]:
  fs[no_install_def]
QED
*)

(* HOL4 ML code, not ported:
Resume no_install_no_alloc_compile_single_correct[ni_CodeBufferWrite]:
  fs[no_alloc_def, no_install_def] >>
  fs[evaluate_def, state_component_equality] >>
  every_case_tac >> fs[]
QED
*)

(* HOL4 ML code, not ported:
Resume no_install_no_alloc_compile_single_correct[ni_DataBufferWrite]:
  fs[no_alloc_def, no_install_def] >>
  fs[evaluate_def, state_component_equality] >>
  every_case_tac >> fs[]
QED
*)

(* HOL4 ML code, not ported:
Resume no_install_no_alloc_compile_single_correct[ni_FFI]:
  fs[no_alloc_def, no_install_def] >>
  fs[evaluate_def, flush_state_def, state_component_equality] >>
  every_case_tac >> fs[]
QED
*)

(* HOL4 ML code, not ported:
Resume no_install_no_alloc_compile_single_correct[ni_ShareInst]:
  fs[evaluate_def, state_component_equality]>>
  qexists_tac`st.permute`>>
  rpt (TOP_CASE_TAC >> fs[state_component_equality]) >>
  fs[DefnBase.one_line_ify NONE share_inst_def,
    DefnBase.one_line_ify NONE sh_mem_set_var_def,
    sh_mem_load_def,sh_mem_load_byte_def,sh_mem_load32_def,
    sh_mem_load16_def,sh_mem_store16_def,
    sh_mem_store_def,sh_mem_store_byte_def,sh_mem_store32_def] >>
  rpt (TOP_CASE_TAC >>
    fs[state_component_equality,set_var_def,flush_state_def])
QED
*)

(* HOL4 ML code, not ported:
Resume no_install_no_alloc_compile_single_correct[ni_If]:
  simp[evaluate_def,get_var_def,get_var_imm_def]>>
  ntac 2 (TOP_CASE_TAC>>full_simp_tac(srw_ss())[])>>
  Cases_on`r`>>full_simp_tac(srw_ss())[get_var_imm_def,get_var_def]>>
  rpt(TOP_CASE_TAC>>full_simp_tac(srw_ss())[])>>
  TRY(qpat_abbrev_tac`prog = p`)>>
  TRY(qpat_abbrev_tac`prog = p0`)>>
  first_x_assum(qspecl_then[`prog`,`st`,`l`] mp_tac)>>
  gs[no_install_def, no_alloc_def]>>
  TRY (impl_tac>-size_tac>>srw_tac[][])
QED
*)

(* HOL4 ML code, not ported:
Resume no_install_no_alloc_compile_single_correct[ni_Seq]:
  fs[evaluate_def,LET_THM,AND_IMP_INTRO]>>
  gs[no_install_def, no_alloc_def]>>
  first_assum(qspecl_then[`p`,`st`,`l`] mp_tac)>>
  impl_tac>- size_tac>>
  strip_tac>>
  pop_assum mp_tac >>
  pairarg_tac>>fs[]>>
  strip_tac
  >- (qexists_tac`perm'`>>srw_tac[][]) >>
  pop_assum mp_tac >>
  pairarg_tac>>fs[]>>
  strip_tac >>
  Cases_on`res`>>fs[]
  >- (
    full_simp_tac std_ss [GSYM PULL_FORALL]>>
    `rst.clock ≤ st.clock ∧ rst.termdep = st.termdep` by
      (imp_res_tac evaluate_clock>>
       full_simp_tac(srw_ss())[state_component_equality])>>
    Cases_on`rst.clock = st.clock`
    >- (
      gs[no_install_def, no_alloc_def]>>
      first_x_assum(qspecl_then[`p0`,`rst`,`rst1.code`] mp_tac)>>
      impl_tac>-(
        gs[no_install_def, no_alloc_def]>>
        `no_install_code rst.code ∧ no_alloc_code rst.code`
          by (qpat_assum `_ = (_, rst)` assume_tac>>
              old_drule no_install_evaluate_const_code>>
              strip_tac>>gs[]>>
              imp_res_tac wordPropsTheory.evaluate_consts>>fs[])>>
        imp_res_tac wordPropsTheory.evaluate_consts>>
        fs[]>>size_tac)>>
      rw[]>>
      Q.ISPECL_THEN[`p`,`st with permute:=perm'`,`perm''`]
        assume_tac wordPropsTheory.permute_swap_lemma>>
      rfs[]>>
      qexists_tac`perm'''`>>
      rw[]>>fs[]>>
      pairarg_tac>>fs[]>>
      qpat_x_assum`rst1 = _` SUBST_ALL_TAC>>fs[])
    >>
    first_x_assum(qspecl_then[`rst`,`p0`,`rst1.code`] mp_tac)>>
    impl_tac>- (
      imp_res_tac wordPropsTheory.evaluate_consts>>
      fs[]>>
      qpat_assum `_ = (_, rst)` assume_tac>>
      old_drule no_install_evaluate_const_code>>
      strip_tac>>gs[])>>
    rw[]>>
    Q.ISPECL_THEN[`p`,`st with permute:=perm'`,`perm''`]
      assume_tac wordPropsTheory.permute_swap_lemma>>
    rfs[]>>
    qexists_tac`perm'''`>>
    rw[]>>fs[]>>
    pairarg_tac>>fs[]>>
    qpat_x_assum`rst1 = _` SUBST_ALL_TAC>>fs[]) >>
  qexists_tac`perm'`>>fs[]
QED
*)

(* HOL4 ML code, not ported:
Resume no_install_no_alloc_compile_single_correct[ni_Loop]:
  rename1 `Loop names body exit_names` >>
  fs[evaluate_def] >>
  TOP_CASE_TAC >> simp[]
  >- (
    rename1`cut_state (names,LN) st = SOME stt` >>
    `stt.code = st.code ∧ stt.gc_fun = st.gc_fun ∧
     stt.clock = st.clock ∧ stt.termdep = st.termdep ∧
     stt.permute = st.permute ∧ stt.compile = st.compile ∧
     stt.compile_oracle = st.compile_oracle` by
      (imp_res_tac cut_state_const >> fs[]) >>
    `cut_state (names,LN) (st with code := l) = SOME (stt with code :=
      l)` by (
      fs[cut_state_def] >> every_case_tac >>
        fs[state_component_equality]) >>
    simp[] >>
    `no_install body ∧ no_alloc body` by
      (gs[no_install_subprogs_def, no_alloc_subprogs_def,
        not_created_subprogs_def]) >>
    first_assum(qspecl_then[`body`,`stt`,`l`] mp_tac) >>
    impl_tac >- (fs[] >> size_tac) >>
    strip_tac >>
    pop_assum mp_tac >>
    pairarg_tac >> simp[] >>
    strip_tac
    >- (qexists_tac`perm'`>>simp[]) >>
    pop_assum mp_tac >>
    pairarg_tac >> simp[] >>
    strip_tac >>
    `rst.clock = rst1.clock ∧ rst.termdep = rst1.termdep` by
      (qpat_x_assum `rst1 = _` SUBST1_TAC >> simp[]) >>
    Cases_on `cont_loop res` >> fs[]
    >- (
      Cases_on `rst1.clock = 0` >> fs[]
      >- (
        qexists_tac`perm'` >>
        qpat_x_assum `evaluate (body, stt with permute := perm') = _`
          (fn th => simp[th]) >>
        qpat_x_assum `rst1 = _` SUBST1_TAC >>
        simp[flush_state_def, state_component_equality]) >>
      simp[STOP_def] >>
      `no_install_code rst.code ∧ no_alloc_code rst.code` by (
        qpat_x_assum `evaluate (body, stt with permute := perm') = _`
          assume_tac >>
        old_drule no_install_evaluate_const_code >>
        impl_tac >- gs[] >>
        strip_tac >> fs[]) >>
      first_x_assum(qspecl_then[`dec_clock rst`,
        `Loop names body exit_names`, `rst1.code`] mp_tac) >>
      impl_tac >- (
        imp_res_tac evaluate_clock >>
        imp_res_tac evaluate_consts >>
        fs[dec_clock_def] >>
        qpat_x_assum `rst1 = _` SUBST1_TAC >> fs[]) >>
      strip_tac >>
      `res ≠ SOME Error` by (
        Cases_on `res` >> fs[cont_loop_def] >>
        rename1 `cont_loop (SOME xx)` >> Cases_on `xx` >>
          fs[cont_loop_def]) >>
      Q.ISPECL_THEN[`body`, `stt with permute := perm'`, `perm''`]
        mp_tac permute_swap_lemma >>
      simp[] >> strip_tac >>
      rename1 `evaluate (body, stt with permute := perm_swap) = _` >>
      qexists_tac `perm_swap` >>
      qpat_x_assum `evaluate (body, stt with permute := perm_swap) = _`
        (fn th => simp[th]) >>
      `(rst with permute := perm'').clock = rst1.clock ∧
       dec_clock (rst with permute := perm'') = dec_clock rst with
         permute := perm''` by
        simp[dec_clock_def] >>
      simp[STOP_def] >>
      qpat_x_assum `(λ(x,y). _) (evaluate (Loop _ _ _, _))` mp_tac >>
      pairarg_tac >> simp[] >>
      strip_tac
      >- (qpat_x_assum `rst1 = _` SUBST1_TAC >> simp[]) >>
      disj2_tac >>
      qpat_x_assum `(λ(x,y). _) _` mp_tac >>
      pairarg_tac >> simp[] >>
      strip_tac >>
      qpat_x_assum `rst1 = _` SUBST1_TAC >>
      simp[dec_clock_def, state_component_equality] >>
      qpat_x_assum `evaluate (Loop _ _ _, _) = (res1', rst1')` mp_tac >>
      simp[dec_clock_def] >> strip_tac >>
      qpat_x_assum `rst1' = _` SUBST1_TAC >>
      simp[]) >>
    Cases_on `res = SOME (Break 0)` >> fs[]
    >- (
      qexists_tac `perm'` >>
      qpat_x_assum `evaluate (body, stt with permute := perm') = _` (fn
        th => simp[th]) >>
      qpat_x_assum `rst1 = _` SUBST1_TAC >>
      simp[] >>
      Cases_on `cut_state (exit_names, LN) rst` >> simp[] >>
      imp_res_tac cut_state_const >> fs[] >>
      simp[state_component_equality]) >>
    qexists_tac `perm'` >>
    qpat_x_assum `evaluate (body, stt with permute := perm') = _` (fn th
      => simp[th]) >>
    qpat_x_assum `rst1 = _` SUBST1_TAC >>
    Cases_on `res` >> fs[exit_loop_def] >>
    rename1 `SOME xx` >>
    Cases_on `xx` >> fs[exit_loop_def, state_component_equality]) >>
  qexists_tac`st.permute`>>simp[rm_perm,state_component_equality]
QED
*)

(* HOL4 ML code, not ported:
Resume no_install_no_alloc_compile_single_correct[ni_Call]:
  fs[evaluate_def, no_alloc_def, no_install_def] >>
  ntac 2 (TOP_CASE_TAC >> fs[]) >>
  Cases_on`find_code o1 (add_ret_loc o' x) st.code st.stack_size`>>
  fs[] >>
  Cases_on`o'`>>full_simp_tac(srw_ss())[] >>
  Cases_on`x'`>>simp[] >>
  Cases_on`r`>>simp[] >>
  imp_res_tac find_code_thm >>
  pop_assum(qspec_then`l` mp_tac) >>
  (impl_tac>-(fs[code_rel_def]>>metis_tac[])) >>
  rw[]>>rfs[]
  >- ( (* Tail call *)
    ntac 2 (TOP_CASE_TAC >> fs[])
    >- simp[flush_state_def, state_component_equality] >>
    qabbrev_tac`stt = call_env q r' (dec_clock st)` >>
    first_x_assum(qspecl_then[`stt`,`prog'`,`l`] mp_tac) >>
    simp[AND_IMP_INTRO] >>
    impl_tac>-(
      full_simp_tac(srw_ss())[Abbr`stt`,dec_clock_def,call_env_def
        ,flush_state_def] >>
      conj_tac>-DECIDE_TAC >>
      qpat_x_assum `find_code _ _ st.code _ = _` assume_tac >>
      old_drule (GEN_ALL code_rel_no_install) >>
      disch_then old_drule>>gs[] >>
      impl_tac
      >- (drule_all (INST_TYPE [beta|->alpha, gamma|->``:num``]
        no_install_find_code)>>gs[]) >>
      rw[] >>
      old_drule (GEN_ALL code_rel_no_alloc) >>
      disch_then old_drule>>gs[] >>
      impl_tac
      >- (drule_all (INST_TYPE [beta|->alpha, gamma|->``:num``]
        no_alloc_find_code)>>gs[]) >>
      rw[]) >>
    srw_tac[][] >>
    Q.ISPECL_THEN [`n`,`q'`,`LENGTH q`,`stt with permute:=perm'`] mp_tac
      (Q.GEN `name` compile_single_lem) >>
    impl_tac >- (
      full_simp_tac(srw_ss())[Abbr`stt`,call_env_def,flush_state_def] >>
      simp[domain_fromList2,word_allocTheory.even_list_def
        ,dec_clock_def]) >>
    qpat_abbrev_tac`A = compile_single t k a c B` >>
    PairCases_on`A`>>srw_tac[][]>>full_simp_tac(srw_ss())[LET_THM] >>
    pop_assum mp_tac >>
    pairarg_tac>>full_simp_tac(srw_ss())[Abbr`stt`] >>
    strip_tac
    >- (qexists_tac`perm''`>>full_simp_tac(srw_ss())[dec_clock_def]) >>
    Cases_on`res`>>full_simp_tac(srw_ss())[]
    >- (qexists_tac`perm''`>>full_simp_tac(srw_ss())[dec_clock_def]) >>
    Cases_on`x' = Error`>>full_simp_tac(srw_ss())[]
    >- (qexists_tac`perm''`>>full_simp_tac(srw_ss())[dec_clock_def]) >>
    ntac 2 (pop_assum mp_tac) >>
    pairarg_tac>>full_simp_tac(srw_ss())[] >>
    rw[] >>
    qpat_x_assum`(λ(x,y). _) _`mp_tac >>
    pairarg_tac>>fs[] >>
    qpat_x_assum`Abbrev ((_,_,_) = _)` mp_tac >>
    simp[Once markerTheory.Abbrev_def]>>rw[] >>
    rw[]>>fs[dec_clock_def] >>
    qmatch_asmsub_abbrev_tac`evaluate (q',stt)` >>
    Q.ISPECL_THEN [`q'`,`stt`,`rcst.permute`] mp_tac permute_swap_lemma
      >>
    fs[]>>rw[] >>
    qexists_tac`perm'''` >>
    fs[Abbr`stt`,word_allocProofTheory.word_state_eq_rel_def
      ,state_component_equality] >>
    fs[code_rel_def] >>
    every_case_tac >> gvs[wordSemTheory.bad_fun_return_def]) >>
  rename [`find_code _ (add_ret_loc (SOME xx) _)`] >>
  `?xn xnames xrh xl1 xl2. xx = (xn, xnames, xrh, xl1, xl2)`
    by (PairCases_on`xx`>>simp[]) >> rveq >> full_simp_tac(srw_ss())[]>>
  ntac 2 (TOP_CASE_TAC>> fs [])>>
  IF_CASES_TAC>-
   (simp[state_component_equality,flush_state_def] >>
    simp[oneline push_env_def,call_env_def]) >>
  fs[]>>
  qabbrev_tac`stt = call_env q r' (push_env x' o0 (dec_clock st))`>>
  first_assum(qspecl_then[`stt`,`prog'`,`l`] mp_tac)>>
  impl_tac>-
   (
    fs[Abbr`stt`,dec_clock_def] >>
    qpat_x_assum `find_code _ _ st.code _ = _` assume_tac>>
    old_drule (GEN_ALL code_rel_no_install)>>
    disch_then old_drule>>gs[]>>
    impl_tac
    >-(drule_all (INST_TYPE [beta|->alpha, gamma|->``:num``]
                  no_install_find_code)>>gs[])>>
    rw[]>>
    old_drule (GEN_ALL code_rel_no_alloc)>>
    disch_then old_drule>>gs[]>>
    impl_tac
    >-(drule_all (INST_TYPE [beta|->alpha, gamma|->``:num``]
                  no_alloc_find_code)>>gs[])>>
    rw[])>>
  rw[]>>
  Q.ISPECL_THEN [`n`,`q'`,`LENGTH q`,`stt with permute:=perm'`] mp_tac
   (Q.GEN `name` compile_single_lem)>>
  impl_tac>-
   (fs[Abbr`stt`,call_env_def] >>
    simp[domain_fromList2,word_allocTheory.even_list_def]) >>
  qpat_abbrev_tac`A = compile_single t k a c B`>>
  PairCases_on`A`>>srw_tac[][]>>full_simp_tac(srw_ss())[LET_THM]>>
  pop_assum mp_tac >>
  pairarg_tac>>full_simp_tac(srw_ss())[Abbr`stt`] >>
  strip_tac
  >-
   (qexists_tac`λn. if n = 0:num then st.permute 0 else perm'' (n-1)`>>
    Cases_on`o0`>>TRY(PairCases_on`x''`)>>
    full_simp_tac(srw_ss())[push_env_def,env_to_list_def,LET_THM
      ,dec_clock_def,call_env_def,flush_state_def,ETA_AX])>>
  Cases_on`res`>>full_simp_tac(srw_ss())[]
  >-
   (qexists_tac`λn. if n = 0:num then st.permute 0 else perm'' (n-1)`>>
    Cases_on`o0`>>TRY(PairCases_on`x''`)>>
    full_simp_tac(srw_ss())[push_env_def,env_to_list_def,LET_THM
      ,dec_clock_def,call_env_def,
                            flush_state_def,ETA_AX])>>
   `!perm. dec_clock (st with permute := perm) = dec_clock st with
     permute := perm`
        by (EVAL_TAC >> simp[]) >> fs[] >>
   qrefine `λn. if n = 0:num then st.permute 0 else perm''' (n-1)` >>
  `!perm. push_env x' o0 (dec_clock st with permute := λn. if n = 0n
    then st.permute 0 else perm (n − 1)) =
   push_env x' o0 (dec_clock st) with permute := perm`
      by (fs[oneline push_env_def,env_to_list_def,ETA_AX] >>
      rpt (TOP_CASE_TAC >> fs[])) >> fs[] >>
  ntac 2 (pop_assum kall_tac) >>
  Cases_on`x''`>>full_simp_tac(srw_ss())[]
  >-
*)
   (* Manual simulation for Result *)
(* HOL4 ML code, not ported:
   (rename [`evaluate (q', call_env q r' (push_env x' o0 (dec_clock st))
     with permute := perm'') =
    (SOME (Result x ys),rst)`] >>
    Cases_on`x = Loc xl1 xl2 ⇒ LENGTH ys ≠ LENGTH
      xn`>>full_simp_tac(srw_ss())[]
    >- (qexists_tac`perm''`>> fs[]) >>
    Cases_on`pop_env rst`>>full_simp_tac(srw_ss())[]
    >- (qexists_tac`perm''`>> fs[]) >>
    rename [`pop_env rst = SOME x''`] >>
    Cases_on`domain x''.locals = domain (FST x') ∪ domain (SND
      x')`>>full_simp_tac(srw_ss())[]
    >- (
     qpat_x_assum`(λ(x,y). _) _`mp_tac >>
     pairarg_tac>>full_simp_tac(srw_ss())[]>>
     strip_tac >>
     last_x_assum kall_tac>>
     qpat_x_assum`(λ(x,y). _) _`mp_tac >>
     pairarg_tac>>full_simp_tac(srw_ss())[]>>
     strip_tac >>
     last_x_assum(qspecl_then[`(set_vars xn ys x'') with
       permute:=rcst.permute`,`xrh`,`rst1.code`]mp_tac)>>
     impl_tac>-
      (`rst.clock < st.clock` by
         (imp_res_tac evaluate_clock>>
          full_simp_tac(srw_ss())[call_env_def,flush_state_def
            ,dec_clock_def]>>
          DECIDE_TAC)>>
       old_drule pop_env_const >> fs[] >> disch_then kall_tac >>
       old_drule pop_env_termdep>> fs[] >> disch_then kall_tac >>
       old_drule pop_env_code_gc_fun_clock >>
       disch_then (mp_tac o LIST_CONJ o (map SYM) o CONJUNCTS) >>
       fs[] >> disch_then kall_tac >>
       imp_res_tac evaluate_consts >> fs[] >>
       imp_res_tac evaluate_clock >> fs[] >>
       fs[word_allocProofTheory.word_state_eq_rel_def]>>
       gs[]>>
       gvs[] >>
       imp_res_tac no_install_evaluate_const_code >>
       imp_res_tac no_install_find_code >>
       gs []) >>
     rw[]>>
     Q.ISPECL_THEN[`q'`,`call_env q r' (push_env x' o0 (dec_clock st))
       with permute:=perm''`,`perm'''`] assume_tac permute_swap_lemma>>
      rfs[]>>
      qexists_tac `perm''''` >> fs[] >>
      qpat_x_assum`((λ(res',rcst). P) A)` mp_tac>>
      pairarg_tac>>rev_full_simp_tac(srw_ss())[]>>full_simp_tac(srw_ss
        ())[]>>
      `pop_env rst1 =
      SOME (x'' with <| code:=rst1.code; permute:=rcst.permute|>)` by
        (fs[pop_env_def,word_allocProofTheory.word_state_eq_rel_def]>>
         qpat_x_assum`rst1 = _` SUBST_ALL_TAC>>
         simp[]>>
         EVERY_CASE_TAC>>fs[state_component_equality])>>
      simp[]>>
      rw[]>>
      fs[dec_clock_def]) >>
    (qexists_tac`perm''`>> fs[]))
  >-
*)
   (* Manual simulation for Exceptions *)
(* HOL4 ML code, not ported:
   (Cases_on`o0`>> fs[]
    >-
     (pop_assum mp_tac >> pairarg_tac>>full_simp_tac(srw_ss())[]>>
      strip_tac >>
      qmatch_assum_abbrev_tac `evaluate(q',A) = _`>>
      Q.ISPECL_THEN [`q'`,`A`,`rcst.permute`] mp_tac
        permute_swap_lemma>>
      simp[Abbr`A`]>>
      impl_tac>-
       (qpat_x_assum`B=res'` sym_sub_tac>>full_simp_tac(srw_ss())[])>>
      rw[]>>
      qexists_tac`perm'''`>>
      qpat_x_assum`(λ(x,y). _) _`mp_tac >>
      pairarg_tac>>rfs[]>>fs[]>>
      rw[]>>fs[word_allocProofTheory.word_state_eq_rel_def
        ,state_component_equality]>>
      fs[dec_clock_def] >>
      metis_tac[]) >>
    rename [`evaluate (q', call_env q r' (push_env x' (SOME p)
      (dec_clock st)) with
          permute := perm'') = (SOME (Exception w w0),rst)`] >>
    PairCases_on`p`>>full_simp_tac(srw_ss())[]>>
    Cases_on`w ≠ Loc p2 p3`
    >- (qexists_tac`perm''`>> fs[]) >>
    Cases_on`domain rst.locals ≠ domain (FST x') ∪ domain (SND x')`
    >- (qexists_tac`perm''`>> fs[]) >>
    qpat_x_assum`((λ(res',rcst). P) A)` mp_tac>>
    pairarg_tac>>full_simp_tac(srw_ss())[]>>strip_tac>>
    last_x_assum kall_tac>>
    qpat_x_assum`(λ(x,y). _) _`mp_tac >>
    pairarg_tac>>full_simp_tac(srw_ss())[]>>
    strip_tac >>
    last_x_assum(qspecl_then[`(set_var p0 w0 rst) with
      permute:=rcst.permute`,`p1`,`rst1.code`]mp_tac)>>
    impl_tac>-
     (simp[] >>
      imp_res_tac evaluate_consts>>fs[dec_clock_def]>>
      imp_res_tac evaluate_clock>> fs[] >>
      fs[word_allocProofTheory.word_state_eq_rel_def]>>
      gs[]>>
      imp_res_tac no_install_evaluate_const_code >>
      imp_res_tac no_install_find_code >>
      gs []) >>
    rw[]>>
    Q.ISPECL_THEN[`q'`,`call_env q r' (push_env x' (SOME (p0,p1,p2,p3))
      (dec_clock st)) with permute:=perm''`,`perm'''`] assume_tac
      permute_swap_lemma>>
    rfs[]>>
    qexists_tac`perm''''` >>
    fs[dec_clock_def]>>
    `domain rst1.locals = domain (FST x') ∪ domain (SND x')` by
      (qpat_x_assum`rst1=_` SUBST_ALL_TAC>>rw[])>>
    simp[]>>
    pairarg_tac>>fs[]>>
    qpat_x_assum`rst1=_` SUBST_ALL_TAC>>fs[]>>
    rpt(pairarg_tac>>fs[])>>
    fs[]>>
    pop_assum mp_tac>>
    qmatch_goalsub_abbrev_tac`_ (evaluate (_,A))`>>
    qmatch_asmsub_abbrev_tac`_ (evaluate (_,B))`>>
    strip_tac>>
    `A = B` by
      (unabbrev_all_tac>>fs[set_var_def,
     state_component_equality
       ,word_allocProofTheory.word_state_eq_rel_def])>>
    rfs[]>>
    unabbrev_all_tac>>fs[])
  >>
  TRY (
    pop_assum mp_tac >> pairarg_tac>>
    fs[]>>
    Q.ISPECL_THEN [`q'`,`call_env q r' (push_env x' o0 (dec_clock st))
      with permute:=perm''`,`rcst.permute`] mp_tac permute_swap_lemma>>
    fs[]>>rw[]>>
    qexists_tac`perm'''`>>
    fs[dec_clock_def] >>
    qpat_x_assum`(λ(a,b). _) _`mp_tac >>
    pairarg_tac>>rfs[]>>
    fs[word_allocProofTheory.word_state_eq_rel_def
      ,state_component_equality])
  >>
  qexists_tac`perm''`>> fs[dec_clock_def]
QED
*)

(* HOL4 ML code, not ported:
Finalise no_install_no_alloc_compile_single_correct;
*)

(*
  completeInduct_on`((st:('a,'c,'ffi)wordSem$state).termdep)`>>
                   completeInduct_on`((st:('a,'c
                     ,'ffi)wordSem$state).clock)`>>
                   simp_tac(srw_ss())[PULL_FORALL]>>
  completeInduct_on`prog_size (K 0) (prog:'a wordLang$prog)`>>
                   rpt strip_tac>>
  full_simp_tac(srw_ss())[PULL_FORALL,evaluate_def,AND_IMP_INTRO]>>
  Cases_on`prog`
  >- (fs[evaluate_def] >> simp[state_component_equality])
  >- (fs[evaluate_def] >> rpt (TOP_CASE_TAC >> simp[]) >>
      simp[state_component_equality])
  >- (fs[evaluate_def] >> rpt (TOP_CASE_TAC >> simp[]) >>
      old_drule inst_const_full >> simp[state_component_equality])
  >- (fs[evaluate_def] >> rpt (TOP_CASE_TAC >> simp[]) >>
      simp[state_component_equality])
  >- (fs[evaluate_def] >> rpt (TOP_CASE_TAC >> simp[]) >>
      simp[state_component_equality])
  >- (fs[evaluate_def] >> rpt (TOP_CASE_TAC >> simp[]) >>
      simp[state_component_equality])
  >- (fs[evaluate_def] >> rpt (TOP_CASE_TAC >> simp[]) >>
      old_drule mem_store_const >> simp[state_component_equality])
   (* Must_Terminate *)
  >- (fs[evaluate_def,no_install_def,no_alloc_def] >>
     rpt (TOP_CASE_TAC >> simp[]) >>
     last_x_assum(qspecl_then[`st with
       <|clock:=MustTerminate_limit(:'a);termdep:=st.termdep-1|>`,`p`
       ,`l`] mp_tac)>>
     impl_tac >- simp[] >>
     disch_tac >> fs[] >>
     qexists_tac`perm'`>>fs[]>>
     rpt (pairarg_tac >> fs[]) >>
     fs[bool_case_eq] >>
     fs[state_component_equality])
  >- (*Call -- the hard case*)
   (
   fs[evaluate_def,no_alloc_def, no_install_def]>>
   ntac 2 (TOP_CASE_TAC >> fs[]) >>
   Cases_on`find_code o1 (add_ret_loc o' x) st.code st.stack_size`>>
   fs []>>
   Cases_on`o'`>>full_simp_tac(srw_ss())[]>>
   (*    Cases_on`o0`>>full_simp_tac(srw_ss())[]>>*)
   Cases_on`x'`>>simp[]>>
   Cases_on `r` >> simp [] >>
   imp_res_tac find_code_thm>>
   pop_assum(qspec_then`l` mp_tac)>>
   (impl_tac>-
     (fs[code_rel_def]>>
      metis_tac[]))>>
   rw[]>> rfs[]
   >- (*Tail calls*)
     (
     ntac 2 (TOP_CASE_TAC >> fs[])
     >-simp[flush_state_def,
            state_component_equality] >>
     qabbrev_tac`stt = call_env q r' (dec_clock st)`>>
     first_x_assum(qspecl_then[`stt`,`prog'`,`l`] mp_tac)>>
     simp[AND_IMP_INTRO]>>
     impl_tac>-
      (full_simp_tac(srw_ss())
       [Abbr`stt`,dec_clock_def,
        call_env_def,
        flush_state_def]>>
       conj_tac>-DECIDE_TAC>>
       qpat_x_assum ‘find_code _ _ st.code _ = _’ assume_tac>>
       old_drule (GEN_ALL code_rel_no_install)>>
       disch_then old_drule>>gs[]>>
       impl_tac
       >-(drule_all (INST_TYPE [beta|->alpha, gamma|->“:num”]
                     no_install_find_code)>>gs[])>>
       rw[]>>
       old_drule (GEN_ALL code_rel_no_alloc)>>
       disch_then old_drule>>gs[]>>
       impl_tac
       >-(drule_all (INST_TYPE [beta|->alpha, gamma|->“:num”]
                     no_alloc_find_code)>>gs[])>>
       rw[])>>
     srw_tac[][]>>
     Q.ISPECL_THEN [`n`,`q'`,`LENGTH q`,`stt with permute:=perm'`]
      mp_tac (Q.GEN `name` compile_single_lem) >>
     impl_tac >-
      (full_simp_tac(srw_ss())[Abbr`stt`,call_env_def,flush_state_def]
        >>
       simp[domain_fromList2,word_allocTheory.even_list_def
         ,dec_clock_def]) >>
     qpat_abbrev_tac`A = compile_single t k a c B`>>
     PairCases_on`A`>>srw_tac[][]>>full_simp_tac(srw_ss())[LET_THM]>>
     pop_assum mp_tac>>
     pairarg_tac>>full_simp_tac(srw_ss())[Abbr`stt`] >>
     strip_tac
     >-
      (qexists_tac`perm''`>>full_simp_tac(srw_ss())[dec_clock_def])>>
     Cases_on`res`>>full_simp_tac(srw_ss())[]
     >-
      (qexists_tac`perm''`>>full_simp_tac(srw_ss())[dec_clock_def])>>
     Cases_on`x' = Error`>>full_simp_tac(srw_ss())[]
     >-
      (qexists_tac`perm''`>>full_simp_tac(srw_ss())[dec_clock_def])>>
     ntac 2 (pop_assum mp_tac) >>
     pairarg_tac>>full_simp_tac(srw_ss())[]>>
     rw[]>>
     qpat_x_assum`(λ(x,y). _) _`mp_tac >>
     pairarg_tac>>fs[]>>
     qpat_x_assum`Abbrev ((_,_,_) = _)` mp_tac>>
     simp[Once markerTheory.Abbrev_def]>>rw[]>>
     rw[]>>fs[dec_clock_def]>>
     qmatch_asmsub_abbrev_tac`evaluate (q',stt)`>>
                             Q.ISPECL_THEN [`q'`,`stt`,`rcst.permute`]
                               mp_tac
                               wordPropsTheory.permute_swap_lemma>>
     fs[]>>rw[]>>
     qexists_tac`perm'''`>>
                fs[Abbr`stt`,word_allocProofTheory.word_state_eq_rel_def
                  ,state_component_equality]>>
     fs[code_rel_def]>>
     metis_tac[])
   >>
   rename [‘find_code _ (add_ret_loc (SOME xx) _)’] >>
   ‘∃xn xnames xrh xl1 xl2. xx = (xn, xnames, xrh, xl1, xl2)’
     by (PairCases_on`xx`>>simp[]) >> rveq >>
       full_simp_tac(srw_ss())[]>>
   ntac 2 (TOP_CASE_TAC>> fs [])>>
   IF_CASES_TAC>-
    (simp[state_component_equality,flush_state_def] >>
     simp[oneline push_env_def,call_env_def]) >>
   fs[]>>
   rename [`evaluate (_,call_env q r' (push_env x' o0 (dec_clock (st
     with permute := _))))`] >>
   qabbrev_tac`stt = call_env q r' (push_env x' o0 (dec_clock st))`>>
                              first_assum(qspecl_then[`stt`,`prog'`,`l`]
                                mp_tac)>>
   impl_tac>-
    (
     fs[Abbr`stt`,dec_clock_def] >>
     qpat_x_assum ‘find_code _ _ st.code _ = _’ assume_tac>>
     old_drule (GEN_ALL code_rel_no_install)>>
     disch_then old_drule>>gs[]>>
     impl_tac
     >-(drule_all (INST_TYPE [beta|->alpha, gamma|->“:num”]
                   no_install_find_code)>>gs[])>>
     rw[]>>
     old_drule (GEN_ALL code_rel_no_alloc)>>
     disch_then old_drule>>gs[]>>
     impl_tac
     >-(drule_all (INST_TYPE [beta|->alpha, gamma|->“:num”]
                   no_alloc_find_code)>>gs[])>>
     rw[])>>
   rw[]>>
   Q.ISPECL_THEN [`n`,`q'`,`LENGTH q`,`stt with permute:=perm'`] mp_tac
    (Q.GEN `name` compile_single_lem)>>
   impl_tac>-
    (fs[Abbr`stt`,call_env_def] >>
     simp[domain_fromList2,word_allocTheory.even_list_def]) >>
   qpat_abbrev_tac`A = compile_single t k a c B`>>
   PairCases_on`A`>>srw_tac[][]>>full_simp_tac(srw_ss())[LET_THM]>>
   pop_assum mp_tac >>
   pairarg_tac>>full_simp_tac(srw_ss())[Abbr`stt`] >>
   strip_tac
   >-
    (qexists_tac`λn. if n = 0:num then st.permute 0 else perm'' (n-1)`>>
     Cases_on`o0`>>TRY(PairCases_on`x''`)>>
     full_simp_tac(srw_ss())[push_env_def,env_to_list_def,LET_THM
       ,dec_clock_def,call_env_def,flush_state_def,ETA_AX])>>
   Cases_on`res`>>full_simp_tac(srw_ss())[]
   >-
    (qexists_tac`λn. if n = 0:num then st.permute 0 else perm'' (n-1)`>>

      Cases_on`o0`>>TRY(PairCases_on`x''`)>>
     full_simp_tac(srw_ss())[push_env_def,env_to_list_def,LET_THM
       ,dec_clock_def,call_env_def,
                             flush_state_def,ETA_AX])>>
    `!perm. dec_clock (st with permute := perm) = dec_clock st with
      permute := perm`
         by (EVAL_TAC >> simp[]) >> fs[] >>
    qrefine `λn. if n = 0:num then st.permute 0 else perm''' (n-1)` >>
   `!perm. push_env x' o0 (dec_clock st with permute := λn. if n = 0n
     then st.permute 0 else perm (n − 1)) =
    push_env x' o0 (dec_clock st) with permute := perm`
       by (fs[oneline push_env_def,env_to_list_def,ETA_AX] >>
       rpt (TOP_CASE_TAC >> fs[])) >> fs[] >>
   ntac 2 (pop_assum kall_tac) >>
   Cases_on`x''`>>full_simp_tac(srw_ss())[]
   >-
    (*Manual simulation for Result*)
    (
     rename [`evaluate (q', call_env q r' (push_env x' o0 (dec_clock
       st)) with permute := perm'') =
     (SOME (Result x ys),rst)`] >>
     Cases_on`x = Loc xl1 xl2 ⇒ LENGTH ys ≠ LENGTH
       xn`>>full_simp_tac(srw_ss())[]
     >-
      (qexists_tac`perm''`>> fs[])
     >>
     Cases_on`pop_env rst`>>full_simp_tac(srw_ss())[]
     >-
      (qexists_tac`perm''`>> fs[]) >>
     rename [`pop_env rst = SOME x''`]
     >>
     reverse (Cases_on`domain x''.locals = domain (FST x') ∪ domain (SND
       x')`)>>full_simp_tac(srw_ss())[]
     >-
      (qexists_tac`perm''`>> fs[])
     >>
     qpat_x_assum`(λ(x,y). _) _`mp_tac >>
     pairarg_tac>>full_simp_tac(srw_ss())[]>>
     strip_tac >>
     last_x_assum kall_tac>>
     qpat_x_assum`(λ(x,y). _) _`mp_tac >>
     pairarg_tac>>full_simp_tac(srw_ss())[]>>
     strip_tac >>
     last_x_assum(qspecl_then[`(set_vars xn ys x'') with
       permute:=rcst.permute`,`xrh`,`rst1.code`]mp_tac)>>
     impl_tac>-
      ((*TODO this is a mess*)
       (*Monotonicity on 12, and dec_clock*)
       `rst.clock < st.clock` by
         (imp_res_tac evaluate_clock>>
          full_simp_tac(srw_ss())[call_env_def,flush_state_def
            ,dec_clock_def]>>
          DECIDE_TAC)>>
       (*Why are there 3 different lemmas*)
       old_drule pop_env_const >> fs[] >> disch_then kall_tac >>
       old_drule pop_env_termdep>> fs[] >> disch_then kall_tac >>
       old_drule pop_env_code_gc_fun_clock >>
       disch_then (mp_tac o LIST_CONJ o (map SYM) o CONJUNCTS) >>
       fs[] >> disch_then kall_tac >>
       (*Yet another duplication*)
       imp_res_tac evaluate_consts >> fs[] >>
       imp_res_tac evaluate_clock >> fs[] >>
       fs[word_allocProofTheory.word_state_eq_rel_def]>>
       gs[]>>
       gvs[] >>
       imp_res_tac no_install_evaluate_const_code >>
       imp_res_tac no_install_find_code >>
       gs []) >>
     rw[]>>
     Q.ISPECL_THEN[`q'`,`call_env q r' (push_env x' o0 (dec_clock st))
       with permute:=perm''`,`perm'''`] assume_tac
       wordPropsTheory.permute_swap_lemma>>
      rfs[]>>
      qexists_tac `perm''''` >> fs[] >>
      qpat_x_assum`((λ(res',rcst). P) A)` mp_tac>>
      pairarg_tac>>rev_full_simp_tac(srw_ss())[]>>full_simp_tac(srw_ss
        ())[]>>
      `pop_env rst1 =
      SOME (x'' with <| code:=rst1.code; permute:=rcst.permute|>)` by
        (fs[pop_env_def,word_allocProofTheory.word_state_eq_rel_def]>>
         qpat_x_assum`rst1 = _` SUBST_ALL_TAC>>
         simp[]>>
         EVERY_CASE_TAC>>fs[state_component_equality])>>
      simp[]>>
      rw[]>>
      fs[dec_clock_def])
   >-
    (*Manual simulation for Exceptions*)
    (
     Cases_on`o0`>> fs[]
     >-
      (pop_assum mp_tac >> pairarg_tac>>full_simp_tac(srw_ss())[]>>
       strip_tac >>
       qmatch_assum_abbrev_tac `evaluate(q',A) = _`>>
                                                  Q.ISPECL_THEN
                                                    [`q'`,`A`
                                                    ,`rcst.permute`]
                                                    mp_tac

      wordPropsTheory.permute_swap_lemma>>
       simp[Abbr`A`]>>
       impl_tac>-
        (qpat_x_assum`B=res'` sym_sub_tac>>full_simp_tac(srw_ss())[])>>
       rw[]>>
       qexists_tac`perm'''`>>
       qpat_x_assum`(λ(x,y). _) _`mp_tac >>
       pairarg_tac>>rfs[]>>fs[]>>
       rw[]>>fs[word_allocProofTheory.word_state_eq_rel_def
         ,state_component_equality]>>
       fs[dec_clock_def] >>
       metis_tac[])
     >>
     rename [`evaluate (q', call_env q r' (push_env x' (SOME p)
       (dec_clock st)) with
           permute := perm'') = (SOME (Exception w w0),rst)`] >>
     PairCases_on`p`>>full_simp_tac(srw_ss())[]>>
     Cases_on`w ≠ Loc p2 p3`
     >-
      (qexists_tac`perm''`>> fs[])
     >> Cases_on`domain rst.locals ≠ domain (FST x') ∪ domain (SND x')`
     >-
      (qexists_tac`perm''`>> fs[])
     >>
     qpat_x_assum`((λ(res',rcst). P) A)` mp_tac>>
     pairarg_tac>>full_simp_tac(srw_ss())[]>>strip_tac>>
     last_x_assum kall_tac>>
     qpat_x_assum`(λ(x,y). _) _`mp_tac >>
     pairarg_tac>>full_simp_tac(srw_ss())[]>>
     strip_tac >>
     last_x_assum(qspecl_then[`(set_var p0 w0 rst) with
       permute:=rcst.permute`,`p1`,`rst1.code`]mp_tac)>>
     impl_tac>-
      (simp[] >>
       imp_res_tac wordPropsTheory.evaluate_consts>>fs[dec_clock_def]>>
       imp_res_tac evaluate_clock>> fs[] >>
       fs[word_allocProofTheory.word_state_eq_rel_def]>>
       gs[]>>
       imp_res_tac no_install_evaluate_const_code >>
       imp_res_tac no_install_find_code >>
       gs []) >>
     rw[]>>
     Q.ISPECL_THEN[`q'`,`call_env q r' (push_env x' (SOME (p0,p1,p2,p3))
       (dec_clock st)) with permute:=perm''`,`perm'''`] assume_tac
       wordPropsTheory.permute_swap_lemma>>
     rfs[]>>
     qexists_tac`perm''''` >>
     fs[dec_clock_def]>>
     `domain rst1.locals = domain (FST x') ∪ domain (SND x')` by
       (qpat_x_assum`rst1=_` SUBST_ALL_TAC>>rw[])>>
     simp[]>>
     pairarg_tac>>fs[]>>
     qpat_x_assum`rst1=_` SUBST_ALL_TAC>>fs[]>>
     rpt(pairarg_tac>>fs[])>>
     fs[]>>
     pop_assum mp_tac>>
     qmatch_goalsub_abbrev_tac`_ (evaluate (_,A))`>>
                              qmatch_asmsub_abbrev_tac`_ (evaluate
                                (_,B))`>>
                              strip_tac>>
     `A = B` by
       (unabbrev_all_tac>>fs[set_var_def,
      state_component_equality
        ,word_allocProofTheory.word_state_eq_rel_def])>>
     rfs[]>>
     unabbrev_all_tac>>fs[])
   >>
   TRY(
     pop_assum mp_tac >> pairarg_tac>>
     fs[]>>
     Q.ISPECL_THEN [`q'`,`call_env q r' (push_env x' o0 (dec_clock st))
       with permute:=perm''`,`rcst.permute`] mp_tac
       wordPropsTheory.permute_swap_lemma>>
     fs[]>>rw[]>>
     qexists_tac`perm'''`>>
     fs[dec_clock_def] >>
     qpat_x_assum`(λ(a,b). _) _`mp_tac >>
     pairarg_tac>>rfs[]>>
     fs[word_allocProofTheory.word_state_eq_rel_def
       ,state_component_equality]
     )
   >>
   qexists_tac`perm''`>> fs[dec_clock_def])
  >- (*Seq, inductive*)
   (fs[evaluate_def,LET_THM,AND_IMP_INTRO]>>
    gs[no_install_def, no_alloc_def]>>
    first_assum(qspecl_then[`p`,`st`,`l`] mp_tac)>>
    impl_tac>- size_tac>>
    strip_tac>>
    pop_assum mp_tac >>
    pairarg_tac>>fs[]>>
    strip_tac
    >- (qexists_tac`perm'`>>srw_tac[][]) >>
    pop_assum mp_tac >>
    pairarg_tac>>fs[]>>
    strip_tac >>
    reverse (Cases_on`res`)>>fs[]
    >- (qexists_tac`perm'`>>fs[])>>
    full_simp_tac std_ss [GSYM PULL_FORALL]>>
    (*Clock monotonicity*)
    `rst.clock ≤ st.clock ∧ rst.termdep = st.termdep` by
      (imp_res_tac evaluate_clock>>
       full_simp_tac(srw_ss())[state_component_equality])>>
    Cases_on`rst.clock = st.clock`
    >-
     (gs[no_install_def, no_alloc_def]>>
      first_x_assum(qspecl_then[`p0`,`rst`,`rst1.code`] mp_tac)>>
      impl_tac>-(
       gs[no_install_def, no_alloc_def]>>
       ‘no_install_code rst.code ∧ no_alloc_code rst.code’
         by (qpat_assum ‘_ = (_, rst)’ assume_tac>>
             old_drule no_install_evaluate_const_code>>
             strip_tac>>gs[call_env_def,
                           push_env_def]>>
             qpat_x_assum ‘find_code _ _ st.code _ = _’ assume_tac>>
             drule_all (INST_TYPE [beta|->alpha, gamma|->“:num”]
                        no_alloc_find_code)>>gs[]>>
             drule_all (INST_TYPE [beta|->alpha, gamma|->“:num”]
                        no_install_find_code)>>gs[]>>
             ntac 2 strip_tac>>gs[])>>
       imp_res_tac wordPropsTheory.evaluate_consts>>
       fs[]>>size_tac)>>
      rw[]>>
      Q.ISPECL_THEN[`p`,`st with permute:=perm'`,`perm''`]
       assume_tac wordPropsTheory.permute_swap_lemma>>
      rfs[]>>
      qexists_tac`perm'''`>>
                 rw[]>>fs[]>>
      pairarg_tac>>fs[]>>
      qpat_x_assum`rst1 = _` SUBST_ALL_TAC>>fs[])
    >>
    first_x_assum(qspecl_then[`rst`,`p0`,`rst1.code`] mp_tac)>>
    impl_tac>- (
     imp_res_tac wordPropsTheory.evaluate_consts>>
     fs[]>>
     qpat_assum ‘_ = (_, rst)’ assume_tac>>
     old_drule no_install_evaluate_const_code>>
     strip_tac>>gs[call_env_def,
                   push_env_def]>>
     qpat_x_assum ‘find_code _ _ st.code _ = _’ assume_tac>>
     drule_all (INST_TYPE [beta|->alpha, gamma|->“:num”]
                no_alloc_find_code)>>gs[]>>
     drule_all (INST_TYPE [beta|->alpha, gamma|->“:num”]
                no_install_find_code)>>gs[]>>
     ntac 2 strip_tac>>gs[])>>
    rw[]>>
    Q.ISPECL_THEN[`p`,`st with permute:=perm'`,`perm''`]
     assume_tac wordPropsTheory.permute_swap_lemma>>
    rfs[]>>
    qexists_tac`perm'''`>>
               rw[]>>fs[]>>
    pairarg_tac>>fs[]>>
    qpat_x_assum`rst1 = _` SUBST_ALL_TAC>>fs[])
  >- (* If *)
   (simp[evaluate_def,get_var_def,get_var_imm_def]>>
    ntac 2 (TOP_CASE_TAC>>full_simp_tac(srw_ss())[])>>
    Cases_on`r`>>full_simp_tac(srw_ss())[get_var_imm_def,get_var_def]>>
    rpt(TOP_CASE_TAC>>full_simp_tac(srw_ss())[])>>
    TRY(qpat_abbrev_tac`prog = p`)>>
    TRY(qpat_abbrev_tac`prog = p0`)>>
    first_x_assum(qspecl_then[`prog`,`st`,`l`] mp_tac)>>
    gs[no_install_def, no_alloc_def]>>
    (impl_tac>-size_tac>>srw_tac[][]))
  >~ [`ShareInst`]
  >- (fs[evaluate_def,state_component_equality]>>
    qexists_tac`st.permute`>>
    rpt (TOP_CASE_TAC >> fs[state_component_equality]) >>
    fs[DefnBase.one_line_ify NONE share_inst_def,
      DefnBase.one_line_ify NONE sh_mem_set_var_def,
      sh_mem_load_def,sh_mem_load_byte_def,sh_mem_load32_def,
      sh_mem_load16_def,sh_mem_store16_def,
      sh_mem_store_def,sh_mem_store_byte_def,sh_mem_store32_def] >>
    rpt (TOP_CASE_TAC >>
      fs[state_component_equality,set_var_def,flush_state_def]))>>
  gs[no_alloc_def, no_install_def]>> (
  fs[evaluate_def,jump_exc_def,flush_state_def,dec_clock_def
    ,state_component_equality] >>
  every_case_tac >> fs[])
  *)

(******** more on no_mt **********)

(*** code_rel_ext ***)

let code_rel_ext_def = cake_define
  `code_rel_ext code l <=>
   (!n p_1 p_2.
      SOME (p_1,p_2) = lookup n code ==>
      (?t' k' a' c' col.
        SOME
        (SND (full_compile_single t' k' a' c' ((n,p_1,p_2),col))) =
        lookup n l))`;;

(* HOL4 ML code, not ported:
val code_rel_ext_def = definition"code_rel_ext_def";
*)

(**** more on no_share_inst ****)

(***** word_to_word semantics correctness for Pancake *****)
