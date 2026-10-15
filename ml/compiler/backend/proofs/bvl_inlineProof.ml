(* ======================================================== *)
(*  bvl_inlineProof: ported from HOL4's
    compiler/backend/proofs/bvl_inlineProofScript.sml  *)
(* ======================================================== *)

(*
  Correctness proof for bvl_inline
*)

needs "compiler/backend/bvl.ml";;
needs "compiler/backend/bvl_const.ml";;
needs "compiler/backend/bvl_handle.ml";;
needs "compiler/backend/bvl_inline.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/pattern_matching/pattern_semantics.ml";;
needs "compiler/backend/proofs/bvl_handleProof.ml";;
needs "compiler/backend/semantics/backendProps.ml";;
needs "compiler/backend/semantics/bvlProps.ml";;
needs "compiler/backend/semantics/bvlSem.ml";;
needs "lib/sptree.ml";;
needs "semantics/ast.ml";;

(* removal of ticks *)

let state_rel_def = cake_define
  `bvl_inlineProof_state_rel (s:('c,'ffi)bvlSem_state)
  (t:('c,'ffi)bvlSem_state) <=>
     t = compile_oracle_fupd (K ((I ##
       MAP (I ## I ## (\x. HD (remove_ticks [x])))) o compile_oracle
         s)) (compile_fupd (K (compile t)) (code_fupd (K (sptree_map (I
         ## (\x. HD (remove_ticks [x]))) (code s))) s)) /\ compile
     s = (\cfg prog. compile t cfg
                    (MAP (I ## I ## (\x. HD (remove_ticks [x])))
                      prog))`;;

(* HOL4 ML code, not ported:
val state_rel_alt = state_rel_def
*)

(* HOL4 ML code, not ported:
val state_rel_def =
  state_rel_def |> SIMP_RULE (srw_ss()) [state_component_equality,GSYM
    CONJ_ASSOC];
*)

(* HOL4 ML code, not ported:
val evaluate_remove_ticks_thm =
  evaluate_remove_ticks
  |> SIMP_RULE std_ss []
  |> Q.SPEC `[Call 0 (SOME start) []]`
  |> SIMP_RULE std_ss [remove_ticks_def];
*)

let remove_ticks_cc_def = cake_define
  `bvl_inlineProof_remove_ticks_cc cc =
     (\cfg prog'.
          cc cfg (MAP (I ## I ## (\x. HD (bvl_inline_remove_ticks
            [x]))) prog'))`;;

let remove_ticks_co_def = cake_define
  `bvl_inlineProof_remove_ticks_co =
     (I ## MAP (I ## I ## (\x. HD (bvl_inline_remove_ticks [x]))))`;;

(* HOL4 ML code, not ported:
val FST_EQ_LEMMA = prove(
  ``FST x = y <=> ?y1. x = (y,y1)``,
  Cases_on `x` \\ fs []);
*)

(* HOL4 ML code, not ported:
val remove_ticks_CONS = prove(
  ``!xs x. bvl_inline$remove_ticks (x::xs) =
           HD (remove_ticks [x]) :: remove_ticks xs``,
  Cases \\ fs [remove_ticks_def]);
*)

(* correctness of tick_inline *)

let exp_rel = cake_inductive
  `(!cs v. exp_rel (cs:(num#bvl_exp) spt) [bvl_Var v] [bvl_Var v]) /\
   (!cs. exp_rel cs [] []) /\
   (!cs x x1 xs y y1 ys.
      exp_rel cs [x] [y] /\
      exp_rel cs (x1 :: xs) (y1 :: ys) ==>
      exp_rel cs (x :: x1 :: xs) (y :: y1 :: ys)) /\
   (exp_rel cs [x1] [y1] /\
    exp_rel cs [x2] [y2] /\
    exp_rel cs [x3] [y3] ==>
    exp_rel cs [If x1 x2 x3] [If y1 y2 y3]) /\
   (exp_rel cs xs ys /\
    exp_rel cs [x] [y] ==>
    exp_rel cs [Let xs x] [Let ys y]) /\
   (exp_rel cs [x1] [y1] /\
    exp_rel cs [x2] [y2] ==>
    exp_rel cs [Handle x1 x2] [Handle y1 y2]) /\
   (exp_rel cs [x] [y] ==>
    exp_rel cs [Raise x] [Raise y]) /\
   (exp_rel cs [x] [y] ==>
    exp_rel cs [Tick x] [Tick y]) /\
   (exp_rel cs xs ys ==>
    exp_rel cs [Op op xs] [Op op ys]) /\
   (exp_rel cs [Force loc n] [Force loc n]) /\
   (exp_rel cs xs ys ==>
    exp_rel cs [Call ticks dest xs] [Call ticks dest ys]) /\
   (exp_rel cs xs ys /\ sptree_lookup n cs = SOME (arity,x) /\
    exp_rel cs [x] [y] ==>
    exp_rel cs [Call ticks (SOME n) xs]
               [Let ys (mk_tick (SUC ticks) y)])`;;

let in_cc_def = cake_define
  `bvl_inlineProof_in_cc limit cc =
     (\(cs,cfg) prog.
         let (cs1,prog1) = tick_compile_prog limit cs prog in
           match cc cfg prog1 with NONE -> NONE | SOME
             (code,data,cfg1) -> SOME (code,data,(cs1,cfg1)))`;;

let in_state_rel_def = cake_define
  `bvl_inlineProof_in_state_rel limit s t <=> globals
     t = globals s /\ refs
     t = refs s /\ clock
     t = clock s /\ ffi
     t = ffi s /\ compile_oracle
     t = (\n.
       let ((cs,cfg),progs) = compile_oracle s n in
       let (cs1,progs) = tick_compile_prog limit cs progs in
         (cfg,progs)) /\
     subspt (FST (FST (compile_oracle s 0))) (code t) /\ compile
     s = bvl_inlineProof_in_cc limit (compile t) /\
     domain (code t) = domain (code s) /\
     (!k arity exp.
        sptree_lookup k (code s) = SOME (arity,exp) ==>
        (?exp2. sptree_lookup k (code t) = SOME (arity,exp2) /\
               exp_rel (code s) [exp] [exp2]))`;;

(* HOL4 ML code, not ported:
val tick_inline_all_acc = prove(
  ``!limit cs t aux.
      tick_inline_all limit cs t aux =
        let (cs1,xs) = tick_inline_all limit cs t [] in
          (cs1, REVERSE aux ++ xs)``,
  Induct_on `t` \\ fs [tick_inline_all_def] \\ rpt strip_tac
  \\ PairCases_on `h` \\ simp_tac std_ss  [tick_inline_all_def]
  \\ pop_assum (fn th => once_rewrite_tac [th])
  \\ fs [] \\ pairarg_tac \\ fs []);
*)

(* HOL4 ML code, not ported:
val tick_compile_prog_IMP = prove(
  ``tick_compile_prog limit q0 ((k,prog)::t) = (cs1,prog1) ==>
    ?p1 vs. prog1 = (k,p1)::vs /\ MAP FST vs = MAP FST t``,
  Cases_on `prog` \\ strip_tac \\ fs [tick_compile_prog_def]
  \\ imp_res_tac tick_inline_all_names \\ fs []
  \\ Cases_on `prog1` \\ fs []
  \\ Cases_on `h` \\ fs []);
*)

(* HOL4 ML code, not ported:
val subspt_union_lemma = prove(
  ``(!x. lookup x t1 = lookup x t2) ==>
    subspt x (union c t1) ==> subspt x (union c t2)``,
  fs [subspt_def,domain_union,lookup_union,domain_lookup]);
*)

(* HOL4 ML code, not ported:
val tick_inline_all_domain = prove(
  ``!limit cs0 in1 cs1 xs.
      tick_inline_all limit cs0 in1 [] = (cs1,xs) ==>
      domain cs1 SUBSET domain cs0 UNION set (MAP FST xs)``,
  Induct_on `in1`
  \\ fs [tick_inline_all_def,FORALL_PROD] \\ rw []
  \\ pop_assum mp_tac
  \\ once_rewrite_tac [tick_inline_all_acc]
  \\ fs [] \\ pairarg_tac \\ fs [] \\ rw []
  \\ res_tac \\ fs [MAP,SUBSET_DEF] \\ metis_tac []);
*)

(* HOL4 ML code, not ported:
val exp_rel_swap_lemma = prove(
  ``!x1 x2 x3. exp_rel x1 x2 x3 ==>
      !y1. (!k. lookup k x1 = lookup k y1) ==> exp_rel y1 x2 x3``,
  ho_match_mp_tac exp_rel_ind \\ rw []
  \\ once_rewrite_tac [exp_rel_cases] \\ fs []
  \\ res_tac \\ metis_tac []);
*)

(* HOL4 ML code, not ported:
val exp_rel_rw = prove(
  ``exp_rel (union (union src_code (insert p1 (p2,p3) LN)) (fromAList
    in1))
      [exp] [exp2] <=>
    exp_rel (union src_code (fromAList ((p1,p2,p3)::in1))) [exp]
      [exp2]``,
  match_mp_tac exp_rel_swap
  \\ fs
    [lookup_union,lookup_insert,fromAList_def,case_eq_thms,lookup_def]
  \\ Cases_on `lookup k src_code` \\ fs []
  \\ CCONTR_TAC \\ fs []);
*)

let in_co_def = cake_define
  `bvl_inlineProof_in_co limit co = (\n.
       (let
          ((cs,cfg),progs) = co n in let
          (cs1,progs) = tick_compile_prog limit cs progs in
          (cfg,progs)))`;;

(* HOL4 ML code, not ported:
val exp_rel_rw = prove(
  ``~MEM x (MAP FST prog) ==>
    exp_rel (union (insert x y (fromAList prog)) acc) [exp] [exp2] =
    exp_rel (union (fromAList prog) (insert x y acc)) [exp] [exp2]``,
  strip_tac
  \\ match_mp_tac exp_rel_swap
  \\ fs [lookup_union,lookup_insert,lookup_fromAList] \\ strip_tac
  \\ IF_CASES_TAC \\ fs []
  \\ every_case_tac \\ fs []
  \\ imp_res_tac ALOOKUP_MEM
  \\ fs [MEM_MAP,FORALL_PROD] \\ rfs []
  \\ Cases_on `x'` \\ rfs []);
*)

(* HOL4 ML code, not ported:
val lookup_tick_inline_all = prove(
  ``!cs0 prog acc.
      (∀k arity v.
          lookup k cs0 = SOME (arity,v) ⇒
          ∃exp.
            lookup k (union (fromAList prog) acc) = SOME (arity,exp) ∧
            exp_rel (union (fromAList prog) acc) [exp] [v]) /\
      DISJOINT (set (MAP FST prog)) (domain cs0) /\
      DISJOINT (set (MAP FST prog)) (domain acc) /\
      ALL_DISTINCT (MAP FST prog) ==>
      ∀k arity exp.
        lookup k (fromAList prog) = SOME (arity,exp) ⇒
        ∃exp2.
          lookup k (fromAList (SND (tick_inline_all limit cs0 prog [])))
            =
          SOME (arity,exp2) ∧ exp_rel (union (fromAList prog) acc) [exp]
            [exp2]``,
  Induct_on `prog` THEN1 (fs [fromAList_def,lookup_def])
  \\ fs [FORALL_PROD] \\ rw []
  \\ qmatch_goalsub_rename_tac `(p1,p2,p3)::_`
  \\ fs [tick_inline_all_def]
  \\ once_rewrite_tac [tick_inline_all_acc] \\ fs [UNCURRY]
  \\ fs [fromAList_def,lookup_insert]
  \\ IF_CASES_TAC \\ rw []
  THEN1 (match_mp_tac exp_rel_tick_inline
         \\ fs [lookup_insert,lookup_union]
         \\ rw [] \\ fs [GSYM lookup_NONE_domain]
         \\ first_x_assum drule \\ fs [] \\ strip_tac \\ fs [])
  \\ fs [] \\ rveq
  \\ qmatch_goalsub_abbrev_tac `tick_inline_all _ cs1`
  \\ qpat_x_assum `!x cs. _ ==> _` (qspec_then `cs1` mp_tac)
  \\ disch_then (qspec_then `insert p1 (p2,p3) acc` mp_tac)
  \\ fs [PULL_FORALL,AND_IMP_INTRO]
  \\ disch_then (qspec_then `k` mp_tac) \\ fs [GSYM PULL_FORALL]
  \\ simp [exp_rel_rw]
  \\ disch_then match_mp_tac \\ fs []
  THEN1
   (unabbrev_all_tac \\ fs [lookup_insert] \\ rw []
    THEN1
     (fs [lookup_union,lookup_insert,lookup_fromAList]
      \\ reverse CASE_TAC \\ fs []
      THEN1 (Cases_on `x`
        \\ imp_res_tac ALOOKUP_MEM \\ fs [MEM_MAP,FORALL_PROD] \\ rfs
          [])
      \\ match_mp_tac exp_rel_tick_inline
      \\ rw [] \\ first_x_assum drule
      \\ IF_CASES_TAC THEN1 fs [GSYM lookup_NONE_domain]
      \\ fs [case_eq_thms] \\ strip_tac
      \\ fs [lookup_union,lookup_insert,lookup_fromAList]
      \\ rfs [exp_rel_rw])
    \\ rpt strip_tac \\ first_x_assum drule
    \\ fs [lookup_union,lookup_insert]
    \\ fs [GSYM lookup_NONE_domain] \\ fs [exp_rel_rw])
  \\ rpt strip_tac \\ first_x_assum drule
  \\ fs [lookup_union,lookup_insert]
  \\ IF_CASES_TAC \\ fs [GSYM lookup_NONE_domain] \\ fs [exp_rel_rw]);
*)

(* HOL4 ML code, not ported:
val subspt_tick_inline = prove(
  ``!prog cs aux.
      subspt cs (fromAList (REVERSE aux)) /\
      EVERY (\x. ~(FST x IN domain cs)) prog /\
      ALL_DISTINCT (MAP FST prog ++ MAP FST aux) ==>
      subspt (FST (tick_inline_all limit cs prog aux))
             (fromAList (SND (tick_inline_all limit cs prog aux)))``,
  Induct \\ fs [tick_inline_all_def,FORALL_PROD] \\ rw []
  \\ first_x_assum match_mp_tac
  \\ fs [subspt_lookup,lookup_insert] \\ rw []
  \\ fs [ALL_DISTINCT_APPEND]
  \\ res_tac \\ fs []
  \\ fs [lookup_fromAList,ALOOKUP_APPEND]
  \\ fs [case_eq_thms,ALOOKUP_NONE,MAP_REVERSE]
  \\ fs [EVERY_MEM,MEM_MAP] \\ rw [] \\ res_tac \\ metis_tac [])
*)

(* HOL4 ML code, not ported:
val evaluate_initial_state = prove(
  ``evaluate
     ([Call 0 (SOME start) []],env,
      initial_state ffi0 (fromAList prog) co cc k) = (res,s2) ∧
    in_co limit co = co1 /\ in_cc limit cc1 = cc /\
    FST (FST (co 0)) = FST (tick_compile_prog limit LN prog) /\
    ALL_DISTINCT (MAP FST prog) /\
    res ≠ Rerr (Rabort Rtype_error) ⇒
    ∃t2.
      evaluate
        ([Call 0 (SOME start) []],env,
         initial_state ffi0
          (fromAList (SND (tick_compile_prog limit LN prog))) co1 cc1 k)
            =
        (res,t2) ∧ in_state_rel limit s2 t2``,
  strip_tac
  \\ match_mp_tac evaluate_inline
  \\ qexists_tac `[Call 0 (SOME start) []]`
  \\ qexists_tac `initial_state ffi0 (fromAList prog) co cc k`
  \\ fs [exp_rel_refl]
  \\ fs [in_state_rel_def,initial_state_def,GSYM in_co_def]
  \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ fs []
  \\ fs [tick_compile_prog_def,domain_fromAList,MAP_FST_tick_inline_all]
  \\ conj_tac
  THEN1 (match_mp_tac subspt_tick_inline \\ fs [])
  \\ match_mp_tac (lookup_tick_inline_all
       |> Q.SPECL [`LN`,`prog`,`LN`] |> SIMP_RULE (srw_ss())
         [lookup_def])
  \\ fs []) |> GEN_ALL |> SIMP_RULE std_ss [];
*)

(* HOL4 ML code, not ported:
val in_evaluate_Call = prove(
  ``evaluate
     ([Call 0 (SOME start) []],env,
      initial_state ffi0 (fromAList prog) co (in_cc limit cc1) k) =
        (res,s2) ∧
    FST (FST (co 0)) = FST (tick_compile_prog limit LN prog) /\
    ALL_DISTINCT (MAP FST prog) /\
    res ≠ Rerr (Rabort Rtype_error) ⇒
    ∃t2.
      evaluate
        ([Call 0 (SOME start) []],env,
         initial_state ffi0
          (fromAList (SND (tick_compile_prog limit LN prog)))
            (in_co limit co) cc1 k) =
        (res,t2) ∧ s2.ffi = t2.ffi``,
  metis_tac [evaluate_initial_state,in_state_rel_def]);
*)

(* HOL4 ML code, not ported:
val semantics_tick_inline = prove(
  ``FST (FST (co 0)) = FST (tick_compile_prog limit LN prog) /\
    ALL_DISTINCT (MAP FST prog) ==>
    semantics ffi (fromAList prog) co (in_cc limit cc) start <> Fail ==>
    semantics ffi (fromAList (SND (tick_compile_prog limit LN prog)))
                  (in_co limit co) cc start =
    semantics (ffi:'b ffi_state) (fromAList prog) co (in_cc limit cc)
      start``,
  strip_tac
  \\ simp [Once semantics_def]
  \\ simp [Once semantics_def, SimpRHS]
  \\ IF_CASES_TAC \\ fs []
  \\ DEEP_INTRO_TAC some_intro \\ simp []
  \\ conj_tac
  >-
   (gen_tac \\ strip_tac \\ rveq \\ simp []
    \\ simp [semantics_def]
    \\ IF_CASES_TAC \\ fs []
    >-
     (first_assum (subterm (fn tm =>
       Cases_on`^(assert(has_pair_type)tm)`) o concl)
      \\ drule evaluate_add_clock
      \\ disch_then (qspec_then `k` mp_tac)
      \\ impl_tac >- fs []
      \\ strip_tac
      \\ qpat_x_assum `evaluate (_,_,_ _ (_ prog) _ _ _) = _` kall_tac
      \\ last_assum (qspec_then `k'` mp_tac)
      \\ (fn g => subterm (fn tm =>
        Cases_on`^(assert(has_pair_type)tm)`) (#2 g) g )
      \\ rw [] \\ fs [] \\ rveq
      \\ CCONTR_TAC
      \\ drule (GEN_ALL in_evaluate_Call) \\ simp [])
    \\ DEEP_INTRO_TAC some_intro \\ simp []
    \\ conj_tac
    >-
     (gen_tac \\ strip_tac \\ rveq \\ fs []
      \\ qabbrev_tac `opts = (fromAList (SND (tick_compile_prog limit LN
        prog)))`
      \\ qmatch_assum_abbrev_tac `bvlSem$evaluate (opts1,[],sopt1) = _`
      \\ qmatch_assum_abbrev_tac `bvlSem$evaluate (exps1,[],st1) =
        (r,s)`
      \\ qspecl_then [`opts1`,`[]`,`sopt1`] mp_tac
          evaluate_add_to_clock_io_events_mono
      \\ qspecl_then [`exps1`,`[]`,`st1`] mp_tac
          (evaluate_add_to_clock_io_events_mono
           |> INST_TYPE [alpha|->``:(num # bvl$exp) num_map # 'a``])
      \\ simp [inc_clock_def, Abbr`sopt1`, Abbr`st1`]
      \\ ntac 2 strip_tac
      \\ Cases_on `r` \\ fs []
      >-
       (Cases_on `r'` \\ fs []
        >-
         (unabbrev_all_tac
          \\ drule (GEN_ALL in_evaluate_Call) \\ simp []
          \\ strip_tac
          \\ drule evaluate_add_clock
          \\ disch_then (qspec_then `k'` mp_tac)
          \\ impl_tac
          >- (every_case_tac \\ fs [])
          \\ rveq
          \\ simp [inc_clock_def]
          \\ qpat_x_assum `evaluate _ = _` kall_tac
          \\ drule evaluate_add_clock
          \\ disch_then (qspec_then `k` mp_tac)
          \\ impl_tac
          >- (spose_not_then strip_assume_tac \\ fs [evaluate_def])
          \\ simp [inc_clock_def]
          \\ ntac 2 strip_tac \\ rveq \\ fs []
          \\ fs [state_component_equality] \\ rfs [] \\ rfs [])
        \\ qpat_x_assum `∀extra._` mp_tac
        \\ first_x_assum (qspec_then `k'` assume_tac)
        \\ first_assum (subterm
             (fn tm => Cases_on`^(assert has_pair_type tm)`) o concl)
        \\ strip_tac \\ fs []
        \\ unabbrev_all_tac
        \\ drule (GEN_ALL in_evaluate_Call)
        \\ impl_tac
        >- (last_x_assum (qspec_then `k+k'` mp_tac) \\ fs [])
        \\ strip_tac
        \\ qhdtm_x_assum `evaluate` mp_tac
        \\ imp_res_tac evaluate_add_clock
        \\ pop_assum mp_tac
        \\ ntac 2 (pop_assum kall_tac)
        \\ impl_tac
        >- (strip_tac \\ fs [])
        \\ disch_then (qspec_then `k'` mp_tac) \\ simp [inc_clock_def]
        \\ first_x_assum (qspec_then `k` mp_tac) \\ fs []
        \\ ntac 3 strip_tac
        \\ fs [] \\ rveq
        \\ qpat_x_assum `evaluate _ = (Rerr _,_)` assume_tac
        \\ drule evaluate_add_clock
        \\ disch_then (qspec_then `k` mp_tac)
        \\ rpt(PURE_FULL_CASE_TAC >> fs[inc_clock_def]))
      \\ qpat_x_assum `∀extra._` mp_tac
      \\ first_x_assum (qspec_then `k'` assume_tac)
      \\ first_assum (subterm (fn tm =>
            Cases_on`^(assert has_pair_type tm)`) o concl)
      \\ fs []
      \\ unabbrev_all_tac
      \\ strip_tac
      \\ drule (GEN_ALL in_evaluate_Call)
      \\ impl_tac
      >- (last_x_assum (qspec_then `k+k'` mp_tac) \\ fs [])
      \\ strip_tac \\ rveq \\ fs []
      \\ reverse (Cases_on `r'`) \\ fs [] \\ rfs []
      >-
       (qpat_x_assum `evaluate _ = (Rerr e', _)` assume_tac
        \\ drule evaluate_add_clock
        \\ disch_then (qspec_then `k` assume_tac)
        \\ qpat_x_assum `evaluate _ = (Rerr e, _)` assume_tac
        \\ drule evaluate_add_clock
        \\ disch_then (qspec_then `k'` assume_tac)
        \\ rpt(PURE_FULL_CASE_TAC \\ fs[inc_clock_def] \\ rveq)
        \\ fs[])
      \\ qhdtm_x_assum `evaluate` mp_tac
      \\ imp_res_tac evaluate_add_clock
      \\ pop_assum kall_tac
      \\ pop_assum mp_tac
      \\ impl_tac
      >- (strip_tac \\ fs [])
      \\ disch_then (qspec_then `k` mp_tac)
      \\ simp [inc_clock_def]
      \\ rpt strip_tac \\ rveq
      \\ CCONTR_TAC \\ fs []
      \\ rveq \\ fs [] \\ rfs []
      \\ rpt(PURE_FULL_CASE_TAC \\ fs[] \\ rveq)
      \\ qpat_x_assum `evaluate _ = (Rerr _, _)` assume_tac
      \\ drule evaluate_add_clock
      \\ disch_then(qspec_then `k'` mp_tac)
      \\ simp[inc_clock_def])
    \\ qmatch_assum_abbrev_tac `bvlSem$evaluate (exps2,[],st2) = _`
    \\ qspecl_then [`exps2`,`[]`,`st2`] mp_tac
          (evaluate_add_to_clock_io_events_mono
           |> INST_TYPE [alpha|->``:(num # bvl$exp) num_map # 'a``])
    \\ simp [inc_clock_def, Abbr`st2`]
    \\ disch_then (qspec_then `0` strip_assume_tac)
    \\ first_assum (subterm (fn tm =>
      Cases_on`^(assert(has_pair_type)tm)`) o concl)
    \\ unabbrev_all_tac
    \\ drule (GEN_ALL in_evaluate_Call)
    \\ impl_tac
    >- (last_x_assum (qspec_then `k` mp_tac) \\ fs [])
    \\ strip_tac
    \\ asm_exists_tac \\ fs []
    \\ every_case_tac \\ fs [] \\ rveq \\ fs [])
  \\ strip_tac
  \\ simp [semantics_def]
  \\ IF_CASES_TAC \\ fs []
  >-
    (last_x_assum (qspec_then `k` assume_tac) \\ rfs []
    \\ first_assum (qspec_then `e` assume_tac)
    \\ fs [] \\ rfs []
    \\ qmatch_assum_abbrev_tac `FST q ≠ _`
    \\ Cases_on `q` \\ fs [markerTheory.Abbrev_def]
    \\ pop_assum (assume_tac o SYM)
    \\ drule (GEN_ALL in_evaluate_Call)
    \\ simp []
    \\ spose_not_then strip_assume_tac
    \\ qmatch_assum_abbrev_tac `FST q = _`
    \\ Cases_on `q` \\ fs [markerTheory.Abbrev_def]
    \\ pop_assum (assume_tac o SYM))
  \\ DEEP_INTRO_TAC some_intro \\ simp []
  \\ conj_tac
  >-
    (spose_not_then assume_tac \\ rw []
    \\ fsrw_tac [QUANT_INST_ss[pair_default_qp]] []
    \\ last_assum (qspec_then `k` mp_tac)
    \\ (fn g => subterm (fn tm => Cases_on`^(assert (can dest_prod o
      type_of) tm)` g) (#2 g))
    \\ strip_tac
    \\ qmatch_assum_rename_tac `evaluate (_,[],_ k) = (_,rr)`
    \\ drule (GEN_ALL in_evaluate_Call)
    \\ impl_tac >- (last_x_assum (qspec_then `k` mp_tac) \\ fs [])
    \\ strip_tac
    \\ fs[]
    \\ rveq
    \\ rpt(PURE_FULL_CASE_TAC \\ fs[] \\ rveq)
    \\ qmatch_asmsub_abbrev_tac `evaluate _ = (a1,_)`
    \\ first_assum (qspecl_then [`k`,`case a1 of Rerr (Rabort
      (Rffi_error e)) => FFI_outcome e
                                               | _ => Success`] mp_tac)
    \\ strip_tac \\ unabbrev_all_tac
    \\ fs[] \\ rfs[])
  \\ strip_tac
  \\ qmatch_abbrev_tac `build_lprefix_lub l1 = build_lprefix_lub l2`
  \\ `(lprefix_chain l1 ∧ lprefix_chain l2) ∧ equiv_lprefix_chain l1 l2`
     suffices_by metis_tac [build_lprefix_lub_thm,
                            lprefix_lub_new_chain,
                            unique_lprefix_lub]
  \\ conj_asm1_tac
  >-
    (unabbrev_all_tac
    \\ conj_tac
    \\ Ho_Rewrite.ONCE_REWRITE_TAC [GSYM o_DEF]
    \\ REWRITE_TAC [IMAGE_COMPOSE]
    \\ match_mp_tac prefix_chain_lprefix_chain
    \\ simp [prefix_chain_def, PULL_EXISTS]
    \\ qx_genl_tac [`k1`,`k2`]
    \\ qspecl_then [`k1`,`k2`] mp_tac LESS_EQ_CASES
    \\ metis_tac [
         LESS_EQ_EXISTS,
         bvlPropsTheory.initial_state_with_simp,
         bvlPropsTheory.evaluate_add_to_clock_io_events_mono
           |> CONV_RULE(RESORT_FORALL_CONV(sort_vars["s"]))
           |> Q.SPEC`s with clock := k`
           |> SIMP_RULE (srw_ss())[bvlPropsTheory.inc_clock_def]])
  \\ simp [equiv_lprefix_chain_thm]
  \\ unabbrev_all_tac \\ simp [PULL_EXISTS]
  \\ simp [LNTH_fromList, PULL_EXISTS, GSYM FORALL_AND_THM]
  \\ rpt gen_tac
  \\ Cases_on `evaluate
         ([Call 0 (SOME start) []],[],
          initial_state ffi (fromAList prog) co (in_cc limit cc) k)`
  \\ drule (GEN_ALL in_evaluate_Call)
  \\ impl_tac >- (last_x_assum (qspec_then `k` mp_tac) \\ fs [])
  \\ strip_tac \\ fs []
  \\ conj_tac \\ rw []
  \\ qexists_tac `k` \\ fs []);
*)

(* let_op *)

let let_opt_def = cake_define
  `let_opt split_seq cut_size (arity,prog) =
     (arity,compile_any split_seq cut_size arity (let_op_sing
       prog))`;;

let let_state_rel_def = cake_define
  `let_state_rel split_seq cut_size (s:('c,'ffi)bvlSem_state)
  (t:('c,'ffi)bvlSem_state) <=>
     t = compile_oracle_fupd (K ((I ##
       MAP (I ## let_opt split_seq cut_size)) o compile_oracle s))
         (compile_fupd (K (compile t)) (code_fupd (K (sptree_map
         (let_opt split_seq cut_size) (code s))) s)) /\ compile
     s = (\cfg prog. compile t cfg (MAP (I ## let_opt split_seq
       cut_size) prog))`;;

(* HOL4 ML code, not ported:
val let_state_rel_alt = let_state_rel_def
*)

(* HOL4 ML code, not ported:
val let_state_rel_def = let_state_rel_def
  |> SIMP_RULE (srw_ss()) [state_component_equality,GSYM CONJ_ASSOC];
*)

(* HOL4 ML code, not ported:
val let_op_sing_thm = prove(
  ``let_op_sing (x :bvl$exp) = HD (let_op [x])``,
  fs [let_op_sing_def]
  \\ once_rewrite_tac [GSYM HD_let_op] \\ fs []);
*)

(* HOL4 ML code, not ported:
val var_list_IMP_evaluate = prove(
  ``!a2 a1 l (xs :bvl$exp list) (s :('a, 'b) state).
      var_list (LENGTH a1) l xs /\ LENGTH xs = LENGTH a2 ==>
      evaluate (l,a1++a2++env,s) = (Rval a2,s)``,
  Induct THEN1
   (fs [APPEND_NIL,var_list_def]
    \\ Cases_on `l` \\ fs [var_list_def,evaluate_def]
    \\ Cases_on `h` \\ fs [var_list_def,evaluate_def])
  \\ Cases_on `xs` \\ fs [LENGTH]
  \\ Cases_on `l` \\ fs [var_list_def]
  \\ Cases_on `h'` \\ fs [var_list_def]
  \\ once_rewrite_tac [evaluate_CONS]
  \\ fs [evaluate_def,EL_LENGTH_APPEND] \\ rw []
  \\ simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
  \\ first_x_assum (qspec_then `a1 ++ [h']` mp_tac)
  \\ fs [] \\ rw [] \\ res_tac
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
  \\ fs [EL_LENGTH_APPEND]);
*)

(* HOL4 ML code, not ported:
val var_list_IMP_evaluate = prove(
  ``var_list 0 l xs /\ LENGTH (xs:bvl$exp list) = LENGTH a ==>
    evaluate (l,a++env,(s :('a, 'b) state)) = (Rval a,s)``,
  rw []
  \\ match_mp_tac (Q.SPECL [`xs`,`[]`] var_list_IMP_evaluate
       |> SIMP_RULE std_ss [APPEND,LENGTH])
  \\ asm_exists_tac \\ fs []);
*)

let let_op_cc_def = cake_define
  `let_op_cc q4 l4 cc =
      (\cfg prog. cc cfg (MAP (I ## let_opt q4 l4) prog))`;;

(* HOL4 ML code, not ported:
val semantics_let_op = prove(
  ``semantics ffi prog co (let_op_cc q4 l4 cc) start <> Fail ==>
    semantics ffi (map (let_opt q4 l4) prog)
                  ((I ## MAP (I ## let_opt q4 l4)) o co) cc start =
    semantics (ffi:'b ffi_state) prog co (let_op_cc q4 l4 cc) start``,
  simp [Once semantics_def]
  \\ simp [Once semantics_def, SimpRHS]
  \\ IF_CASES_TAC \\ fs []
  \\ DEEP_INTRO_TAC some_intro \\ simp []
  \\ conj_tac
  >-
   (
    gen_tac \\ strip_tac \\ rveq \\ simp []
    \\ simp [semantics_def]
    \\ IF_CASES_TAC \\ fs []
    >-
     (first_assum (subterm (fn tm =>
       Cases_on`^(assert(has_pair_type)tm)`) o concl)
      \\ drule evaluate_add_clock
      \\ `q <> Rerr (Rabort Rtimeout_error)` by (CCONTR_TAC \\ fs []) \\
        fs []
      \\ CCONTR_TAC \\ fs []
      \\ qpat_x_assum `evaluate (_,_,_ _ (_ prog) _ _ _) = _` kall_tac
      \\ last_assum (qspec_then `k'` mp_tac)
      \\ (fn g => subterm (fn tm =>
        Cases_on`^(assert(has_pair_type)tm)`) (#2 g) g )
      \\ rw [] \\ fs [] \\ rveq
      \\ CCONTR_TAC
      \\ drule (GEN_ALL let_evaluate_Call) \\ simp []
      \\ strip_tac
      \\ first_x_assum (qspec_then `0` mp_tac)
      \\ simp [inc_clock_def])
    \\ DEEP_INTRO_TAC some_intro \\ simp []
    \\ conj_tac
    >-
     (gen_tac \\ strip_tac \\ rveq \\ fs []
      \\ qabbrev_tac `opts = (map (I ## let_op_sing) prog)`
      \\ qmatch_assum_abbrev_tac `bvlSem$evaluate (opts1,[],sopt1) = _`
      \\ qmatch_assum_abbrev_tac `bvlSem$evaluate (exps1,[],st1) =
        (r,s)`
      \\ qspecl_then [`opts1`,`[]`,`sopt1`] mp_tac
           evaluate_add_to_clock_io_events_mono
      \\ qspecl_then [`exps1`,`[]`,`st1`] mp_tac
           evaluate_add_to_clock_io_events_mono
      \\ simp [inc_clock_def, Abbr`sopt1`, Abbr`st1`]
      \\ ntac 2 strip_tac
      \\ Cases_on `r` \\ fs []
      >-
       (Cases_on `r'` \\ fs []
        >-
         (unabbrev_all_tac
          \\ drule (GEN_ALL let_evaluate_Call) \\ simp []
          \\ strip_tac
          \\ drule evaluate_add_clock
          \\ disch_then (qspec_then `k'` mp_tac) \\ simp [inc_clock_def]
          \\ qpat_x_assum `evaluate _ = _` kall_tac
          \\ drule evaluate_add_clock
          \\ disch_then (qspec_then `k` mp_tac) \\ simp [inc_clock_def]
          \\ ntac 2 strip_tac \\ rveq \\ fs []
          \\ fs [state_component_equality] \\ rfs [] \\ rfs [])
        \\ qpat_x_assum `∀extra._` mp_tac
        \\ first_x_assum (qspec_then `k'` assume_tac)
        \\ first_assum (subterm
             (fn tm => Cases_on`^(assert has_pair_type tm)`) o concl)
        \\ strip_tac \\ fs []
        \\ unabbrev_all_tac
        \\ drule (GEN_ALL let_evaluate_Call)
        \\ impl_tac
        >- (last_x_assum (qspec_then `k+k'` mp_tac) \\ fs [])
        \\ strip_tac
        \\ qhdtm_x_assum `evaluate` mp_tac
        \\ imp_res_tac evaluate_add_clock
        \\ pop_assum mp_tac
        \\ ntac 2 (pop_assum kall_tac)
        \\ impl_tac
        >- (strip_tac \\ fs [])
        \\ disch_then (qspec_then `k'` mp_tac) \\ simp [inc_clock_def]
        \\ first_x_assum (qspec_then `k` mp_tac) \\ fs []
        \\ ntac 3 strip_tac
        \\ fs [let_state_rel_def] \\ rveq
        \\ qpat_x_assum `evaluate _ = (Rerr _, _)` assume_tac
        \\ drule evaluate_add_clock
        \\ disch_then (qspec_then `k` mp_tac)
        \\ impl_tac >- (CCONTR_TAC \\ fs[])
        \\ simp[inc_clock_def])
      \\ qpat_x_assum `∀extra._` mp_tac
      \\ first_x_assum (qspec_then `k'` assume_tac)
      \\ first_assum (subterm (fn tm =>
            Cases_on`^(assert has_pair_type tm)`) o concl)
      \\ fs []
      \\ unabbrev_all_tac
      \\ strip_tac
      \\ drule (GEN_ALL let_evaluate_Call)
      \\ impl_tac
      >- (last_x_assum (qspec_then `k+k'` mp_tac) \\ fs [])
      \\ strip_tac \\ rveq \\ fs []
      \\ reverse (Cases_on `r'`) \\ fs [] \\ rfs []
      >-
        (first_x_assum (qspec_then `k` mp_tac)
        \\ fs [ADD1]
        \\ strip_tac \\ fs [state_rel_def] \\ rfs []
        \\ qpat_x_assum `evaluate _ = (Rerr e, _)` assume_tac
        \\ drule evaluate_add_clock
        \\ disch_then (qspec_then `k'` mp_tac)
        \\ impl_tac >- (CCONTR_TAC \\ fs[])
        \\ qpat_x_assum `evaluate _ = (Rerr e', _)` assume_tac
        \\ drule evaluate_add_clock
        \\ disch_then (qspec_then `k` mp_tac)
        \\ impl_tac >- (CCONTR_TAC \\ fs[])
        \\ simp[inc_clock_def] \\ rpt strip_tac \\ fs[]
        \\ rpt(PURE_FULL_CASE_TAC \\ fs[] \\ rveq \\ fs[]))
      \\ qhdtm_x_assum `evaluate` mp_tac
      \\ imp_res_tac evaluate_add_clock
      \\ pop_assum kall_tac
      \\ pop_assum mp_tac
      \\ impl_tac
      >- (strip_tac \\ fs [])
      \\ disch_then (qspec_then `k` mp_tac)
      \\ simp [inc_clock_def]
      \\ rpt strip_tac \\ rveq
      \\ qpat_x_assum `evaluate _ = (Rerr e, _)` assume_tac
      \\ drule evaluate_add_clock
      \\ disch_then (qspec_then `k'` mp_tac)
      \\ impl_tac >- (CCONTR_TAC \\ fs[])
      \\ simp[inc_clock_def]
      \\ rpt(PURE_FULL_CASE_TAC \\ fs[]))
    \\ qmatch_assum_abbrev_tac `bvlSem$evaluate (exps2,[],st2) = _`
    \\ qspecl_then [`exps2`,`[]`,`st2`] mp_tac
      evaluate_add_to_clock_io_events_mono
    \\ simp [inc_clock_def, Abbr`st2`]
    \\ disch_then (qspec_then `0` strip_assume_tac)
    \\ first_assum (subterm (fn tm =>
      Cases_on`^(assert(has_pair_type)tm)`) o concl)
    \\ unabbrev_all_tac
    \\ drule (GEN_ALL let_evaluate_Call)
    \\ impl_tac
    >- (last_x_assum (qspec_then `k` mp_tac) \\ fs [])
    \\ strip_tac
    \\ asm_exists_tac \\ fs []
    \\ every_case_tac \\ fs [] \\ rveq \\ fs [])
  \\ strip_tac
  \\ simp [semantics_def]
  \\ IF_CASES_TAC \\ fs []
  >-
    (last_x_assum (qspec_then `k` assume_tac) \\ rfs []
    \\ first_assum (qspec_then `e` assume_tac)
    \\ fs [] \\ rfs []
    \\ qmatch_assum_abbrev_tac `FST q ≠ _`
    \\ Cases_on `q` \\ fs [markerTheory.Abbrev_def]
    \\ pop_assum (assume_tac o SYM)
    \\ drule (GEN_ALL let_evaluate_Call)
    \\ simp []
    \\ spose_not_then strip_assume_tac
    \\ qmatch_assum_abbrev_tac `FST q = _`
    \\ Cases_on `q` \\ fs [markerTheory.Abbrev_def]
    \\ pop_assum (assume_tac o SYM))
  \\ DEEP_INTRO_TAC some_intro \\ simp []
  \\ conj_tac
  >-
    (spose_not_then assume_tac \\ rw []
    \\ fsrw_tac [QUANT_INST_ss[pair_default_qp]] []
    \\ last_assum (qspec_then `k` mp_tac)
    \\ (fn g => subterm (fn tm => Cases_on`^(assert (can dest_prod o
      type_of) tm)` g) (#2 g))
    \\ strip_tac
    \\ qmatch_assum_rename_tac `evaluate (_,[],_ k) = (_,rr)`
    \\ drule (GEN_ALL let_evaluate_Call)
    \\ impl_tac >- (last_x_assum (qspec_then `k` mp_tac) \\ fs [])
    \\ strip_tac
    \\ first_assum (qspecl_then [`k`,`case r of Rerr (Rabort (Rffi_error
      e)) => FFI_outcome e
                                               | _ => Success`] mp_tac)
    \\ strip_tac \\ unabbrev_all_tac
    \\ rpt(PURE_FULL_CASE_TAC \\ fs[] \\ rveq) \\ rfs[])
  \\ strip_tac
  \\ qmatch_abbrev_tac `build_lprefix_lub l1 = build_lprefix_lub l2`
  \\ `(lprefix_chain l1 ∧ lprefix_chain l2) ∧ equiv_lprefix_chain l1 l2`
     suffices_by metis_tac [build_lprefix_lub_thm,
                            lprefix_lub_new_chain,
                            unique_lprefix_lub]
  \\ conj_asm1_tac
  >-
    (unabbrev_all_tac
    \\ conj_tac
    \\ Ho_Rewrite.ONCE_REWRITE_TAC [GSYM o_DEF]
    \\ REWRITE_TAC [IMAGE_COMPOSE]
    \\ match_mp_tac prefix_chain_lprefix_chain
    \\ simp [prefix_chain_def, PULL_EXISTS]
    \\ qx_genl_tac [`k1`,`k2`]
    \\ qspecl_then [`k1`,`k2`] mp_tac LESS_EQ_CASES
    \\ metis_tac [
         LESS_EQ_EXISTS,
         bvlPropsTheory.initial_state_with_simp,
         bvlPropsTheory.evaluate_add_to_clock_io_events_mono
           |> CONV_RULE(RESORT_FORALL_CONV(sort_vars["s"]))
           |> Q.SPEC`s with clock := k`
           |> SIMP_RULE (srw_ss())[bvlPropsTheory.inc_clock_def]])
  \\ simp [equiv_lprefix_chain_thm]
  \\ unabbrev_all_tac \\ simp [PULL_EXISTS]
  \\ simp [LNTH_fromList, PULL_EXISTS, GSYM FORALL_AND_THM]
  \\ rpt gen_tac
  \\ Cases_on `evaluate
         ([Call 0 (SOME start) []],[],
          initial_state ffi prog co (let_op_cc q4 l4 cc) k)`
  \\ drule (GEN_ALL let_evaluate_Call)
  \\ impl_tac >- (last_x_assum (qspec_then `k` mp_tac) \\ fs [])
  \\ strip_tac \\ fs []
  \\ conj_tac \\ rw [] \\ qexists_tac `k` \\ fs []);
*)

(* combined theorems *)

(* HOL4 ML code, not ported:
val remove_ticks_mk_tick = prove(
  ``!n r. remove_ticks [mk_tick n r] = remove_ticks [r]``,
  Induct THEN1 (EVAL_TAC \\ fs [])
  \\ fs [bvlTheory.mk_tick_def,FUNPOW,remove_ticks_def]);
*)

(* HOL4 ML code, not ported:
val is_small_aux_0 = prove(
  ``!n:num xs. is_small_aux 0 xs = 0``,
  recInduct is_small_aux_ind
  \\ rw [] \\ fs [is_small_aux_def]);
*)

(* HOL4 ML code, not ported:
val is_small_aux_CONS = prove(
  ``is_small_aux n (x::xs) =
    if n = 0 then n else
      let n = is_small_aux n [x] in
        if n = 0 then n else is_small_aux n xs``,
  Induct_on `xs` \\ fs [is_small_aux_def] \\ rw []
  \\ Cases_on `x` \\ fs [is_small_aux_def,is_small_aux_0]);
*)

(* HOL4 ML code, not ported:
val is_small_aux_remove_ticks = prove(
  ``!limit d. is_small_aux limit (remove_ticks d) = is_small_aux limit
    d``,
  recInduct is_small_aux_ind \\ rw []
  \\ fs [is_small_aux_def,remove_ticks_def]
  \\ rw [] \\ fs []
  \\ once_rewrite_tac [is_small_aux_CONS] \\ fs []
  \\ simp [Once is_small_aux_CONS] \\ fs []);
*)

(* HOL4 ML code, not ported:
val is_rec_CONS = prove(
  ``is_rec n (x::xs) <=> is_rec n [x] \/ is_rec n xs``,
  Cases_on `xs` \\ fs [is_rec_def]);
*)

(* HOL4 ML code, not ported:
val is_rec_remove_ticks = prove(
  ``!p_1 xs. is_rec p_1 (remove_ticks xs) = is_rec p_1 xs``,
  recInduct is_rec_ind \\ rw []
  \\ fs [remove_ticks_def,is_rec_def]
  \\ simp [Once is_rec_CONS]
  \\ fs [] \\ fs [is_rec_def]
  \\ metis_tac []);
*)

(* HOL4 ML code, not ported:
val must_inline_remove_ticks = prove(
  ``must_inline p_1 limit (HD (remove_ticks (tick_inline cs [p_2]))) =
    must_inline p_1 limit (HD ((tick_inline cs [p_2])))``,
  fs [must_inline_def]
  \\ `?d. tick_inline cs [p_2] = [d]` by
   (`LENGTH (tick_inline cs [p_2]) = LENGTH [p_2]`
       by metis_tac [LENGTH_tick_inline] \\ fs []
    \\ Cases_on `tick_inline cs [p_2]` \\ fs [])
  \\ fs [is_small_def,is_rec_def,is_small_aux_remove_ticks]
  \\ fs [is_rec_remove_ticks]);
*)

let let_opt_remove_def = cake_define
  `let_opt_remove b l (arity,prog) =
     let_opt b l (arity,HD (remove_ticks [prog]))`;;

(* HOL4 ML code, not ported:
val map_fromAList_HASH = prove(
  ``map f (fromAList ls) = fromAList (MAP (I ## f) ls)``,
  fs [map_fromAList]
  \\ rpt (AP_TERM_TAC ORELSE AP_THM_TAC)
  \\ fs [FUN_EQ_THM,FORALL_PROD]);
*)

(* HOL4 ML code, not ported:
val ticks =
  semantics_remove_ticks
  |> Q.INST [`prog`|->`fromAList p`]
  |> SIMP_RULE std_ss [map_fromAList]
*)

(* HOL4 ML code, not ported:
val lets =
  semantics_let_op
  |> Q.INST [`prog`|->`fromAList p`]
  |> SIMP_RULE std_ss [map_fromAList]
*)

(* HOL4 ML code, not ported:
val inline_ticks = prove(
  ``FST (FST (co 0)) = (FST (tick_compile_prog limit LN prog)) ∧
    ALL_DISTINCT (MAP FST prog) ⇒
    semantics ffi (fromAList prog) co
      (in_cc limit (remove_ticks_cc cc)) start ≠ Fail ⇒
    semantics ffi (fromAList (MAP (I ## I ## (λx. HD (remove_ticks
      [x])))
                                (SND (tick_compile_prog limit LN
                                  prog))))
      (remove_ticks_co ∘ in_co limit co) cc start =
    semantics ffi (fromAList prog) co (in_cc limit (remove_ticks_cc cc))
      start``,
  fs [ticks] \\ strip_tac
  \\ match_mp_tac semantics_tick_inline \\ fs []);
*)

(* HOL4 ML code, not ported:
val comp_lemma = prove(
  ``(I ## let_opt q4 l4) o (I ## I ## (λx. HD (remove_ticks [x]))) =
    (I ## let_opt_remove q4 l4)``,
  fs [FUN_EQ_THM,FORALL_PROD,let_opt_remove_def,let_opt_def]);
*)

let bvl_inline_cc_def = cake_define
  `bvl_inline_cc limit q4 l4 cc =
     (bvl_inlineProof_in_cc limit (bvl_inlineProof_remove_ticks_cc
       (let_op_cc q4 l4 cc)))`;;

let bvl_inline_co_def = cake_define
  `bvl_inline_co limit q4 l4 co =
    (\x. (I ## MAP (I ## let_opt q4 l4))
           (bvl_inlineProof_remove_ticks_co (bvl_inlineProof_in_co
             limit co x)))`;;

(* HOL4 ML code, not ported:
val MAP_optimise = prove(
  ``!prog.
      MAP (optimise o1 o2) prog =
      MAP (I ## let_opt o1 o2)
        (MAP (I ## I ## (λx. HD (remove_ticks [x]))) prog)``,
  Induct \\ fs [FORALL_PROD,optimise_def,let_opt_def]);
*)
