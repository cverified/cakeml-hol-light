(* ======================================================== *)
(*  source_evalProof: ported from HOL4's
    compiler/backend/proofs/source_evalProofScript.sml  *)
(* ======================================================== *)

(*
  Proofs that the eval mode of the source semantics can
  be switched to one that includes an oracle.
*)

needs "compiler/backend/pattern_matching/pattern_semantics.ml";;
needs "lib/peg.ml";;
needs "semantics/ast.ml";;
needs "semantics/evaluate.ml";;
needs "semantics/namespace.ml";;
needs "semantics/proofs/evaluateProps.ml";;
needs "semantics/proofs/namespaceProps.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "semantics/semantics.ml";;
(* HOL4 ancestors outside the port: string *)

(* The things the translator is expected to produce from the
   compiler definition etc. *)

let compiler_instance_FIELDS = define_record "compiler_instance"
  ["compiler_fun","(num#num)#'config#dec list->('config#word8 \
   list#word64 list) option";
   "config_v","'config->semanticPrimitives_v";
   "config_dom","'config->bool";
   "decs_v","dec list->semanticPrimitives_v";
   "decs_dom","dec list->bool";
   "init_state","'config"];;

let v_rel_abs = cake_define
  `v_fun_abs fun_dom fun_v v = (some (\x. fun_v x = v /\ x IN
  fun_dom))`;;

let mk_compiler_fun_from_ci_def = cake_define
  `mk_compiler_fun_from_ci ci (env_id,cfg_v,decs) =
     OPTION_BIND (v_fun_abs (compiler_instance_config_dom ci)
       (compiler_instance_config_v ci) cfg_v) (\cfg.
     OPTION_BIND (compiler_instance_compiler_fun ci
       (env_id,cfg,decs)) (\(cfg2,bs,ws).
     SOME (compiler_instance_config_v ci cfg2,bs,ws)))`;;

(* HOL4 overload (expanded in the port):
     ci_comp = mk_compiler_fun_from_ci *)

let mk_init_eval_state_def = cake_define
  `mk_init_eval_state ci = EvalDecs (mk_eval_decs_state
  (mk_compiler_fun_from_ci ci) (compiler_instance_config_v ci
  (compiler_instance_init_state ci)) (0,0,1) (v_fun_abs
  (compiler_instance_decs_dom ci) (compiler_instance_decs_v ci)))`;;

(* an instance of custom_do_eval that behaves as much as possible
   like the no-oracle semantics *)

let v_to_nat_def = cake_define
  `v_to_nat v = (match v with (semanticPrimitives_Litv (ast_IntLit
  i)) -> (if 0 <= i then SOME (num_of_int i) else NONE) | _1 -> NONE)`;;

let v_to_env_id_def = cake_define
  `v_to_env_id v = (match v with semanticPrimitives_Conv NONE
  [gen_id_v; id_v] -> (match (v_to_nat gen_id_v,v_to_nat id_v) with
  (SOME gen_id,SOME id') -> SOME (gen_id,id') | _2 -> NONE) | _3 ->
  NONE)`;;

let do_eval_record_def = cake_define
  `do_eval_record ci vs (orac:num->(num#num)#semanticPrimitives_v#dec
  list) = (match vs with [env_id_v; st_v; decs_v; st_v2; bs_v; ws_v] ->
       (let ((i,_4),st,_5) = orac 0 in
       (match (v_to_env_id env_id_v,v_fun_abs
         (compiler_instance_decs_dom ci) (compiler_instance_decs_v ci)
         decs_v) with (SOME env_id,SOME decs) ->
         (if compiler_agrees (mk_compiler_fun_from_ci ci)
             (env_id,st_v,decs) (st_v2,bs_v,ws_v) /\ st_v = st then
         let orac' = \j. if j = 0 then ((i + 1,0),st_v2,[]) else
           if j = SUC i then (env_id,st,decs) else orac j in SOME
           (env_id,orac',decs) else NONE) | _6 -> NONE)) | _7 ->
           NONE)`;;

(* a somewhat generic env rel *)

let env_rel_def = cake_define
  `source_evalProof_env_rel v_rel' (env:semanticPrimitives_v sem_env)
  env' <=> c
     env = c env' /\ nsDom (v env) = nsDom (v env') /\
     nsDomMod (v env) = nsDomMod (v env') /\
     (!nm x y. nsLookup (v env) nm = SOME x /\ nsLookup (v env') nm =
       SOME y ==>
         v_rel' x y)`;;

(* HOL4 ML code, not ported:
val _ = IndDefLib.add_mono_thm env_rel_mono_rel;
*)

(* HOL4 ML code, not ported:
val _ = bossLib.augment_srw_ss [rewrites (CONJUNCTS env_rel_nsEmpty)];
*)


(* various trivia *)

(* HOL4 ML code, not ported:
val s = mk_var ("s", ``: 'ffi semanticPrimitives$state``);
*)

(* first step. switch over to recording semantics and move envs
   out of Env values and into the state *)

let v_rel = cake_inductive
  `(!env'. v_to_env_id v = SOME id /\ lookup_env es id = SOME env' /\
         source_evalProof_env_rel (v_rel es) env env' ==>
     v_rel es (semanticPrimitives_Env env id) v) /\
   (LIST_REL (v_rel es) xs ys ==>
     v_rel es (semanticPrimitives_Vectorv xs)
       (semanticPrimitives_Vectorv ys)) /\
   (LIST_REL (v_rel es) xs ys ==>
     v_rel es (semanticPrimitives_Conv stmp xs)
       (semanticPrimitives_Conv stmp ys)) /\
   (source_evalProof_env_rel (v_rel es) env env' ==>
     v_rel es (semanticPrimitives_Closure env nm x)
       (semanticPrimitives_Closure env' nm x)) /\
   (source_evalProof_env_rel (v_rel es) env env' ==>
     v_rel es (semanticPrimitives_Recclosure env funs nm)
       (semanticPrimitives_Recclosure env' funs nm)) /\
   (v_rel es (semanticPrimitives_Litv l) (semanticPrimitives_Litv l))
     /\
   (v_rel es (semanticPrimitives_Loc br n) (semanticPrimitives_Loc
     br n))`;;

(* HOL4 ML code, not ported:
val _ = bossLib.augment_srw_ss [rewrites [v_rel_l_simps, v_rel_Boolv]];
*)

let recorded_orac_wf_def = cake_define
  `recorded_orac_wf compiler
  (orac:num->(num#num)#semanticPrimitives_v#dec list) <=>
   (0 < FST (FST (orac 0)) ==>
     (?r. compiler (orac (FST (FST (orac 0)))) = SOME r /\
         FST (SND (orac 0)) = FST r)) /\
   (!j. j < FST (FST (orac 0)) /\ 0 < j ==>
     (?r. compiler (orac j) = SOME r /\ FST (SND (orac (j + 1))) =
       FST r))`;;

let s_rel_def = cake_define
  `s_rel ci s s' <=>
   (?dec_s orac_s' refs'. s' =
     semanticPrimitives_state_eval_state_fupd (K (SOME (EvalOracle
     orac_s'))) (semanticPrimitives_state_refs_fupd (K refs') s) /\
   LIST_REL (sv_rel (v_rel orac_s')) (semanticPrimitives_state_refs
     s) refs' /\ semanticPrimitives_state_eval_state
   s = SOME (EvalDecs dec_s) /\ eval_oracle_state_custom_do_eval
   orac_s' = do_eval_record ci /\ eval_decs_state_compiler_state
   dec_s = (FST (SND (oracle orac_s' 0))) /\
     eval_decs_state_decode_decs
   dec_s = v_fun_abs (compiler_instance_decs_dom ci)
     (compiler_instance_decs_v ci) /\ eval_decs_state_compiler
   dec_s = mk_compiler_fun_from_ci ci /\
   (0 = FST (FST (oracle orac_s' 0)) ==>
     eval_decs_state_compiler_state
     dec_s = compiler_instance_config_v ci
       (compiler_instance_init_state ci)) /\
   (0 < FST (FST (oracle orac_s' 0)) ==>
     FST (SND (oracle orac_s' 1)) = compiler_instance_config_v ci
       (compiler_instance_init_state ci)) /\
       eval_decs_state_env_id_counter
   dec_s = (eval_oracle_state_generation orac_s',
         LENGTH (EL (eval_oracle_state_generation orac_s')
           (eval_oracle_state_envs orac_s')),LENGTH
           (eval_oracle_state_envs orac_s')) /\
           eval_oracle_state_generation
   orac_s' < LENGTH (eval_oracle_state_envs orac_s') /\
   recorded_orac_wf (mk_compiler_fun_from_ci ci) (oracle orac_s'))`;;

let orac_s_def = cake_define
  `orac_s x1 =
      match x1 with
        SOME (EvalOracle es) -> es
      | _8 -> ARB "not EvalOracle"`;;

(* HOL4 ML code, not ported:
val _ = bossLib.augment_srw_ss [rewrites [orac_s_def]];
*)

let es_forward_def = cake_define
  `es_forward es es' <=>
   (LENGTH (eval_oracle_state_envs es) <= LENGTH
     (eval_oracle_state_envs es')) /\
   (!env_id env. lookup_env es env_id = SOME env ==>
     lookup_env es' env_id = SOME env)`;;

(* a stronger notion that applies end-to-end over
   evaluate/evaluate_decs,
   where the generation stack will match at either end and the previous
   generations will be untouched. *)
let es_stack_forward_def = cake_define
  `es_stack_forward es es' <=> eval_oracle_state_generation
   es' = eval_oracle_state_generation es /\
   (!j. j < eval_oracle_state_generation es ==> EL j
     (eval_oracle_state_envs es') = EL j (eval_oracle_state_envs es))`;;

let match_result_rel_def = cake_define
  `source_evalProof_match_result_rel nerr R mr1 mr2 <=> (match mr1
  with No_match -> mr2 = No_match | Match_type_error -> nerr \/ mr2 =
  Match_type_error | Match x -> (?y. mr2 = Match y /\ R x y))`;;

(* HOL4 ML code, not ported:
val ci = mk_var ("ci", ``: 'cfg compiler_instance``);
*)

let abort_def = cake_define
  `source_evalProof_abort r <=> (match r with Rerr (Rabort a) -> T |
  _9 -> F)`;;

(* case splits for evaluate proofs *)
(* HOL4 ML code, not ported:
val eval_cases_tac =
  fs [pair_case_eq, result_case_eq, error_result_case_eq, bool_case_eq,
        option_case_eq, list_case_eq, exp_or_val_case_eq,
          match_result_case_eq]
  \\ rveq \\ fs []
  \\ imp_res_tac evaluate_sing
  \\ rveq \\ fs []
*)

(* take a step of forward-consistency-type reasoning *)
(* HOL4 ML code, not ported:
val forward_tac = MAP_FIRST (drule_then irule)
    (map (REWRITE_RULE [Once CONJ_COMM])
        [es_forward_trans, es_stack_forward_trans] @ IMP_CANON
          forward_rules)
*)

(* quantifier instantiation based on s_rel, v_rel etc *)
(* HOL4 ML code, not ported:
val insts_tac = rpt (FIRST ([
      do_xig_inst `s_rel Ig_ci X_s _`,
      do_xig_inst `env_rel (v_rel Ig_es) X_env _`,
      do_xig_inst `LIST_REL (v_rel Ig_es) X_env _`,
      do_xig_inst `v_rel Ig_es X_v _`,
      CHANGED_TAC (rveq \\ fs [Q.ISPEC `(a, b)` EQ_SYM_EQ,
            es_forward_refl, es_stack_forward_refl]
        \\ rfs []),
      forward_tac,
      first_x_assum (fn t => mp_tac t \\ (impl_tac THENL
            [rpt conj_tac \\ forward_tac, disch_tac])),
      conj_tac THENL [forward_tac, all_tac],
      match_mp_tac abort_imp_intro \\ rw [] \\ fs []
    ]))
*)

(* HOL4 ML code, not ported:
Resume eval_simulation[App]:
  rw []
  \\ reverse (fs [pair_case_eq, result_case_eq] \\ rveq \\ fs [])
  \\ insts_tac
  \\ Cases_on `getOpClass op`
  >- (
    fs [do_eval_res_def, evaluate_def, do_con_check_def]
    \\ fs [option_case_eq, pair_case_eq] \\ rveq \\ fs []
    \\ drule_then (drule_then drule) do_eval_sim
    \\ rw []
    \\ fs []
    \\ drule_then assume_tac s_rel_clock
    \\ fs [bool_case_eq] \\ rveq \\ fs []
    \\ insts_tac
    \\ fs [EVAL ``(dec_clock x).eval_state``]
    \\ eval_cases_tac
    \\ insts_tac
    \\ TRY (drule_then (drule_then (qsubterm_then `declare_env _ _`
      mp_tac))
        declare_env_sim
      \\ impl_tac
      \\ (irule env_rel_extend_dec_env ORELSE disch_tac))
    \\ insts_tac
    \\ first_x_assum drule \\ impl_tac
    \\ rw [] \\ insts_tac
  )
  >- (
    rveq \\ fs []
    \\ imp_res_tac s_rel_clock
    \\ fs [do_opapp_def]
    \\ eval_cases_tac
    \\ fs [listTheory.SWAP_REVERSE_SYM, CaseEq "v"] \\ rveq \\ fs []
    \\ fs [listTheory.SWAP_REVERSE, miscTheory.FST_triple]
    \\ eval_cases_tac
    \\ insts_tac
    \\ rfs [EVAL ``(dec_clock s).eval_state``]
    \\ first_x_assum (qsubterm_then `evaluate _ _ _` mp_tac)
    \\ impl_tac \\ rw [] \\ insts_tac
    \\ irule env_rel_add_nsBind
    \\ insts_tac
    \\ simp [build_rec_env_merge, nsAppend_to_nsBindList]
    \\ irule env_rel_add_nsBindList
    \\ simp [LIST_REL_MAP1, SIMP_RULE (bool_ss ++ ETA_ss) []
      LIST_REL_MAP2]
    \\ simp [ELIM_UNCURRY, EVERY2_refl]
  )
  >~ [`getOpClass op = Force`]
  >- (
    gvs [AllCaseEqs(), dec_clock_def]
    >- (
      gvs [oneline dest_thunk_def, AllCaseEqs(), oneline
        store_lookup_def]
      \\ gvs [s_rel_def, LIST_REL_EL_EQN]
      \\ `∃a. EL n refs'' = Thunk Evaluated a ∧
              v_rel orac_s'' v a` by (
        first_x_assum drule \\ rw []
        \\ Cases_on `EL n refs''` \\ gvs [sv_rel_def]) \\ gvs []
      \\ simp [state_component_equality])
    >- (
      gvs [oneline dest_thunk_def, AllCaseEqs(), oneline
        store_lookup_def]
      \\ simp[PULL_EXISTS]
      \\ gvs [s_rel_def, LIST_REL_EL_EQN]
      \\ `∃a. EL n refs'' = Thunk NotEvaluated a ∧
              v_rel orac_s'' v a` by (
        first_x_assum drule \\ rw []
        \\ Cases_on `EL n refs''` \\ gvs [sv_rel_def]) \\ gvs []
      \\ gvs[do_opapp_cases] \\ irule_at Any EQ_REFL >> simp[])
    >- (
      gvs [oneline dest_thunk_def, AllCaseEqs(), oneline
        store_lookup_def]
      \\ `n < LENGTH t''.refs ∧
          ∃a. EL n t''.refs = Thunk NotEvaluated a ∧
          v_rel (orac_s t''.eval_state) v a` by (
        gvs [s_rel_def, LIST_REL_EL_EQN]
        \\ first_x_assum drule \\ rw []
        \\ Cases_on `EL n refs''` \\ gvs [sv_rel_def]) \\ gvs [] >>
      gvs[do_opapp_cases, PULL_EXISTS]
      >- (
        imp_res_tac s_rel_def >> gvs[] >>
        drule s_rel_clock >> simp[dec_clock_def] >> strip_tac >>
        last_x_assum dxrule >> simp[] >>
        qmatch_goalsub_abbrev_tac ‘evaluate _ new_env’ >>
        disch_then $ qspec_then ‘new_env’ mp_tac >> impl_tac
        >- (unabbrev_all_tac >> irule env_rel_add_nsBind >> simp[]) >>
        strip_tac >> gvs[] >>
        gvs[oneline update_thunk_def, AllCaseEqs()] >>
        gvs[store_assign_def, s_rel_def, state_component_equality] >>
        reverse $ rw[] >> insts_tac
        >- (irule EVERY2_LUPDATE_same >> gvs[])
        >- (
          gvs[LIST_REL_EL_EQN, store_v_same_type_def] >>
          first_x_assum drule >> simp[sv_rel_cases] >>
          strip_tac >> gvs[]
          )
        >- gvs[LIST_REL_EL_EQN] >>
        qpat_x_assum ‘dest_thunk _ _ = _’ mp_tac >> simp[oneline
          dest_thunk_def] >>
        qpat_x_assum ‘v_rel _ _ _’ mp_tac >> simp[Once v_rel_cases] >>
          strip_tac >> gvs[]
        >- gvs[oneline v_to_env_id_def, AllCaseEqs()] >>
        simp[store_lookup_def] >> gvs[LIST_REL_EL_EQN] >>
        IF_CASES_TAC >> gvs[] >>
        first_x_assum drule >> simp[sv_rel_cases] >> strip_tac >> gvs[]
          >>
        TOP_CASE_TAC >> gvs[] >> rw[]
        )
      >- (
        imp_res_tac s_rel_def >> gvs[] >>
        drule s_rel_clock >> simp[dec_clock_def] >> strip_tac >>
        last_x_assum dxrule >> simp[] >>
        qmatch_goalsub_abbrev_tac ‘evaluate _ new_env’ >>
        disch_then $ qspec_then ‘new_env’ mp_tac >> impl_tac
        >- (
          unabbrev_all_tac >> simp[build_rec_env_merge,
            nsAppend_to_nsBindList] >>
          irule env_rel_add_nsBind >> simp[] >>
          irule env_rel_add_nsBindList >>
          simp[LIST_REL_MAP1, SRULE [SF ETA_ss] LIST_REL_MAP2,
            ELIM_UNCURRY] >>
          simp[LIST_REL_EL_EQN]
          ) >>
        strip_tac >> gvs[] >>
        gvs[oneline update_thunk_def, AllCaseEqs()] >>
        gvs[store_assign_def, s_rel_def, state_component_equality] >>
        reverse $ rw[] >> insts_tac
        >- (irule EVERY2_LUPDATE_same >> gvs[])
        >- (
          gvs[LIST_REL_EL_EQN, store_v_same_type_def] >>
          first_x_assum drule >> simp[sv_rel_cases] >>
          strip_tac >> gvs[]
          )
        >- gvs[LIST_REL_EL_EQN] >>
        qpat_x_assum ‘dest_thunk _ _ = _’ mp_tac >> simp[oneline
          dest_thunk_def] >>
        qpat_x_assum ‘v_rel _ _ _’ mp_tac >> simp[Once v_rel_cases] >>
          strip_tac >> gvs[]
        >- gvs[oneline v_to_env_id_def, AllCaseEqs()] >>
        simp[store_lookup_def] >> gvs[LIST_REL_EL_EQN] >>
        IF_CASES_TAC >> gvs[] >>
        first_x_assum drule >> simp[sv_rel_cases] >> strip_tac >> gvs[]
          >>
        TOP_CASE_TAC >> gvs[] >> rw[]
        )
      )
    >- (
      gvs [oneline dest_thunk_def, AllCaseEqs(), oneline
        store_lookup_def]
      \\ `n < LENGTH t''.refs ∧
          ∃a. EL n t''.refs = Thunk NotEvaluated a ∧
          v_rel (orac_s t''.eval_state) v a` by (
        gvs [s_rel_def, LIST_REL_EL_EQN]
        \\ first_x_assum drule \\ rw []
        \\ Cases_on `EL n refs''` \\ gvs [sv_rel_def]) \\ gvs [] >>
      gvs[do_opapp_cases, PULL_EXISTS]
      >- (
        imp_res_tac s_rel_def >> gvs[] >>
        irule_at Any OR_INTRO_THM2 >>
        drule s_rel_clock >> simp[dec_clock_def] >> strip_tac >>
        last_x_assum dxrule >> simp[] >>
        qmatch_goalsub_abbrev_tac ‘evaluate _ new_env’ >>
        disch_then $ qspec_then ‘new_env’ mp_tac >> impl_tac
        >- (unabbrev_all_tac >> irule env_rel_add_nsBind >> simp[]) >>
        strip_tac >> gvs[] >> insts_tac
        )
      >- (
        imp_res_tac s_rel_def >> gvs[] >>
        irule_at Any OR_INTRO_THM2 >>
        drule s_rel_clock >> simp[dec_clock_def] >> strip_tac >>
        last_x_assum dxrule >> simp[] >>
        qmatch_goalsub_abbrev_tac ‘evaluate _ new_env’ >>
        disch_then $ qspec_then ‘new_env’ mp_tac >> impl_tac
        >- (
          unabbrev_all_tac >> simp[build_rec_env_merge,
            nsAppend_to_nsBindList] >>
          irule env_rel_add_nsBind >> simp[] >>
          irule env_rel_add_nsBindList >>
          simp[LIST_REL_MAP1, SRULE [SF ETA_ss] LIST_REL_MAP2,
            ELIM_UNCURRY] >>
          simp[LIST_REL_EL_EQN]
          ) >>
        strip_tac >> gvs[] >> insts_tac
        )
      )
    )
  \\ eval_cases_tac
  \\ drule_then (drule_then assume_tac) do_app_sim
  \\ insts_tac
  \\ fs [s_rel_def] \\ rveq \\ fs []
  \\ simp [state_component_equality]
  \\ rw [] \\ fs []
QED
*)

(* HOL4 ML code, not ported:
Resume eval_simulation[Denv]:
  rw []
  \\ eval_cases_tac
  \\ fs [declare_env_def, s_rel_def]
  \\ rveq \\ fs []
  \\ fs [pair_case_eq]
  \\ rveq \\ fs []
  \\ simp [oEL_THM]
  \\ simp [state_component_equality]
  \\ qmatch_goalsub_abbrev_tac `es_forward cur_es new_es`
  \\ qsuff_tac `es_forward cur_es new_es`
  >- (
    rpt strip_tac \\ insts_tac
    \\ simp [EL_LUPDATE]
    \\ insts_tac
    \\ simp [nsSing_eq_bind]
    \\ fs [markerTheory.Abbrev_def, es_stack_forward_def, EL_LUPDATE]
    \\ irule env_rel_add_nsBind
    \\ simp [v_to_env_id_def, v_to_nat_def, nat_to_v_def]
    \\ fs [markerTheory.Abbrev_def, lookup_env_def,
          oEL_THM, EL_LUPDATE, EL_APPEND_EQN,
          es_stack_forward_def]
    \\ insts_tac
  )
  >- (
    fs [markerTheory.Abbrev_def, es_forward_def, FORALL_PROD]
    \\ simp [lookup_env_def, oEL_THM, option_case_eq]
    \\ simp [EL_LUPDATE]
    \\ rw [EL_APPEND_EQN]
  )
QED
*)

(* HOL4 ML code, not ported:
Resume eval_simulation[Con]:
  rpt disch_tac
  \\ eval_cases_tac
  \\ insts_tac
  \\ imp_res_tac env_rel_def
  \\ fs [do_con_check_def, build_conv_def]
  \\ every_case_tac
  \\ insts_tac
QED
*)

(* HOL4 ML code, not ported:
Resume eval_simulation[Let]:
  rpt disch_tac
  \\ eval_cases_tac
  \\ insts_tac
  \\ first_x_assum (qsubterm_then `evaluate _ _ _` mp_tac)
  \\ simp [namespaceTheory.nsOptBind_def]
  \\ CASE_TAC \\ fs []
  \\ impl_tac
  \\ rw []
  \\ insts_tac
  \\ irule env_rel_add_nsBind
  \\ insts_tac
QED
*)

(* HOL4 ML code, not ported:
Resume eval_simulation[Letrec]:
  rpt disch_tac
  \\ eval_cases_tac
  \\ insts_tac
  \\ fs [miscTheory.FST_triple, MAP_MAP_o]
  \\ fs [GSYM pairarg_to_pair_map, ELIM_UNCURRY, o_DEF, ETA_THM]
  \\ first_x_assum (qsubterm_then `evaluate _ _ _` mp_tac)
  \\ impl_tac \\ rw [] \\ insts_tac
  \\ simp [build_rec_env_merge, nsAppend_to_nsBindList]
  \\ irule env_rel_add_nsBindList
  \\ simp [LIST_REL_MAP1, SIMP_RULE (bool_ss ++ ETA_ss) []
    LIST_REL_MAP2]
  \\ simp [ELIM_UNCURRY]
  \\ simp [GSYM pairarg_to_pair_map, ELIM_UNCURRY, EVERY2_refl]
QED
*)

(* HOL4 ML code, not ported:
Resume eval_simulation[match]:
  rpt disch_tac
  \\ eval_cases_tac
  \\ drule_then (drule_then assume_tac) pmatch_drule_form
  \\ insts_tac
  \\ fs [match_result_rel_def]
  \\ insts_tac
  \\ first_x_assum (qsubterm_then `evaluate _ _ _` mp_tac)
  \\ impl_tac \\ rw [] \\ insts_tac
  \\ simp [nsAppend_to_nsBindList]
  \\ irule env_rel_add_nsBindList
  \\ simp [nsAppend_to_nsBindList]
QED
*)

(* HOL4 ML code, not ported:
Resume eval_simulation[cons_decs]:
  rpt disch_tac
  \\ eval_cases_tac
  \\ insts_tac
  \\ first_x_assum (qsubterm_then `evaluate_decs _ _ _` mp_tac)
  \\ impl_tac \\ rw [] \\ insts_tac
  \\ TRY (irule env_rel_extend_dec_env)
  \\ insts_tac
  \\ TRY strip_tac
  \\ fs [combine_dec_result_def]
  \\ every_case_tac \\ fs []
  \\ rw [] \\ insts_tac
  \\ simp [GSYM (SIMP_RULE (srw_ss ()) [] extend_dec_env_def)]
  \\ TRY (irule env_rel_extend_dec_env)
  \\ insts_tac
QED
*)

(* HOL4 ML code, not ported:
Resume eval_simulation[Dletrec]:
  rpt disch_tac
  \\ eval_cases_tac
  \\ insts_tac
  \\ fs [miscTheory.FST_triple, MAP_MAP_o, o_DEF, ELIM_UNCURRY, ETA_THM]
  \\ imp_res_tac env_rel_imp_c
  \\ simp [build_rec_env_merge, nsAppend_to_nsBindList]
  \\ irule env_rel_add_nsBindList
  \\ simp []
  \\ simp [LIST_REL_MAP1, SIMP_RULE (bool_ss ++ ETA_ss) []
    LIST_REL_MAP2]
  \\ simp [ELIM_UNCURRY]
  \\ simp [EVERY2_refl]
QED
*)

(* HOL4 ML code, not ported:
Resume eval_simulation[Dtype]:
  rpt disch_tac
  \\ eval_cases_tac
  \\ fs [EVERY_MEM, FORALL_PROD, MEM_MAP, EXISTS_PROD, PULL_EXISTS,
      check_dup_ctors_thm]
  \\ fs [s_rel_def, state_component_equality]
  \\ insts_tac
  \\ simp []
QED
*)

(* HOL4 ML code, not ported:
Resume eval_simulation[Dexn]:
  rpt disch_tac
  \\ eval_cases_tac
  \\ fs [s_rel_def, state_component_equality]
  \\ insts_tac
QED
*)

(* HOL4 ML code, not ported:
Resume eval_simulation[Dlocal]:
  rpt disch_tac
  \\ eval_cases_tac
  \\ insts_tac
  \\ first_x_assum (qsubterm_then `evaluate_decs _ _ _` mp_tac)
  \\ impl_tac \\ rw [] \\ insts_tac
  \\ irule env_rel_extend_dec_env
  \\ insts_tac
QED
*)

(* HOL4 ML code, not ported:
Finalise eval_simulation;
*)

(* HOL4 overload (expanded in the port):
     shift_seq = misc$shift_seq *)

let do_eval_oracle_def = cake_define
  `do_eval_oracle (f:(num#num)#semanticPrimitives_v#dec
  list->(semanticPrimitives_v#word8 list#word64 list) option) (g:dec
  list->dec list) vs (orac:num->(num#num)#semanticPrimitives_v#dec list)
  =
   (match vs with [env_id_v; st_v; decs_v; st_v2; bs_v; ws_v] ->
       (let (env_id,st,decs) = orac 0 in
       (match (f (env_id,st,decs),v_to_word8_list bs_v,
             v_to_word64_list ws_v) with (SOME (st_v2,c_bs,c_ws),SOME
               bs,SOME ws) ->
             (if bs = c_bs /\ ws = c_ws /\ st_v2 = (FST (SND (orac
               1))) then SOME (env_id,misc_shift_seq 1 orac,g decs)
               else NONE) | _10 -> NONE)) | _11 -> NONE)`;;

let insert_gen_oracle_def = cake_define
  `insert_gen_oracle ci g shift_f orac es = (match es with SOME
  (EvalOracle s) -> SOME (EvalOracle (oracle_fupd (K (misc_shift_seq
  (shift_f (oracle s 0)) orac))
  (eval_oracle_state_custom_do_eval_fupd (K (do_eval_oracle
  (mk_compiler_fun_from_ci ci) g)) s))) | _12 -> es)`;;

(* HOL4 overload (expanded in the port):
     insert_oracle = \ci. insert_gen_oracle ci I (FST o FST) *)

let orac_agrees_def = cake_define
  `orac_agrees orac es = (match es with SOME (EvalOracle s) ->
       (!j. j < FST (FST (oracle s 0)) ==> orac j = oracle s (j +
         1)) | _13 -> F)`;;

(* the infinite extension of an oracle is still well-formed with
   respect to the compiler function *)
let orac_extended_wf_def = cake_define
  `orac_extended_wf f orac =
   (!i x. f (orac i) = SOME x ==> FST x = FST (SND (orac (SUC
     i))))`;;

let record_forward_def = cake_define
  `record_forward es es' = (match es with SOME (EvalOracle s) -> (?s'.
  es' = SOME (EvalOracle s') /\
         (FST (FST (oracle s 0)) <= FST (FST (oracle s' 0))) /\
         (!j. 0 < j /\ j < FST (FST (oracle s 0)) + 1 ==> oracle
             s' j = oracle s j)) | _14 -> (match es' with SOME
               (EvalOracle _15) -> F | _16 -> T))`;;

let is_record_def = cake_define
  `is_record ci es <=> (match es with SOME (EvalOracle s) ->
  eval_oracle_state_custom_do_eval
         s = do_eval_record ci | _17 -> F)`;;

(* HOL4 ML code, not ported:
val agrees_tac = (drule_then irule orac_agrees_backward)
  \\ rpt (simp_tac bool_ss [record_forward_refl]
    \\ drule_then irule record_forward_trans_sym)
*)

(* HOL4 ML code, not ported:
val agrees_impl_tac = rpt ((qpat_x_assum `orac_agrees _ _ ==> _` mp_tac
    \\ impl_tac)
  >- agrees_tac)
*)

(* HOL4 ML code, not ported:
fun simp_res_tac t = ASSUM_LIST (fn asms => let
    val t2 = SIMP_RULE (srw_ss ()) asms t
  in drule_then simp_res_tac t2
    ORELSE (if is_forall (concl t) then all_tac else strip_assume_tac t)
  end)
*)

(* HOL4 ML code, not ported:
fun imp_res_simp_tac t = IMP_RES_THEN mp_tac t
  \\ simp []
  \\ rpt ((disch_then drule \\ simp []) ORELSE disch_then
      (fn t => if is_forall (concl t) then all_tac else assume_tac t))
*)

(* HOL4 ML code, not ported:
val imp_res_simp_tac = IMP_RES_THEN simp_res_tac
*)

(* HOL4 ML code, not ported:
Resume insert_oracle_correct[App]:
  rw []
  \\ fs [pair_case_eq, result_case_eq] \\ rveq \\ fs []
  \\ fs [bool_case_eq] \\ rveq \\ fs [] \\ Cases_on ‘getOpClass op’ \\
    gs[]
  >- (
*)
    (* Eval *)
(* HOL4 ML code, not ported:
    fs [do_eval_res_def, Q.ISPEC `(a, b)` EQ_SYM_EQ, pair_case_eq]
    \\ rveq \\ fs []
    \\ fs [option_case_eq, pair_case_eq] \\ rveq \\ fs []
    \\ imp_res_simp_tac evaluate_is_record_forward
    \\ drule_then drule insert_do_eval
    \\ disch_then (qspecl_then [`orac`] mp_tac)
    \\ rw []
    \\ fs [bool_case_eq] \\ rveq \\ fs []
    >- (
      agrees_impl_tac
      \\ simp []
    )
    \\ fs [Q.ISPEC `(a, b)` EQ_SYM_EQ, pair_case_eq]
    \\ fs [dec_clock_def]
    \\ fs [result_case_eq, option_case_eq, pair_case_eq] \\ rveq \\ fs
      []
    \\ fs [error_result_case_eq] \\ rveq \\ fs []
    \\ fs [reset_env_generation_orac_eqs]
    \\ imp_res_simp_tac evaluate_is_record_forward
    \\ imp_res_simp_tac insert_declare_env
    \\ agrees_impl_tac
    \\ simp [reset_env_generation_orac_eqs]
  )
  >- (
*)
    (* Opapp *)
(* HOL4 ML code, not ported:
    eval_cases_tac
    \\ fs [Q.ISPEC `(a, b)` EQ_SYM_EQ] \\ rveq \\ fs []
    \\ fs [dec_clock_def]
    \\ imp_res_simp_tac evaluate_is_record_forward
    \\ agrees_impl_tac
    \\ simp []
  )
  >~ [`getOpClass op = Force`] >- (
    gvs [AllCaseEqs(), dec_clock_def]
    \\ eval_cases_tac
    \\ imp_res_simp_tac evaluate_is_record_forward
    \\ imp_res_simp_tac insert_declare_env
    \\ agrees_impl_tac
    \\ simp [])
  \\ eval_cases_tac
  \\ gs[]
QED
*)

(* HOL4 ML code, not ported:
Resume insert_oracle_correct[Denv]:
  rw []
  \\ fs [option_case_eq, pair_case_eq] \\ rveq \\ fs []
  \\ imp_res_simp_tac insert_declare_env
  \\ simp []
QED
*)

(* HOL4 ML code, not ported:
Finalise insert_oracle_correct;
*)

(* Constructs the oracle from an evaluation by using the recorded
   events, padding with null events if necessary. *)
let extract_oracle_def = cake_define
  `extract_oracle s env decs n =
     (match (OLEAST (\k. ?s' res.
       evaluate_evaluate_decs (semanticPrimitives_state_clock_fupd (K
         k) s) env decs = (s',res) /\
         n < FST (FST (oracle (orac_s
           (semanticPrimitives_state_eval_state s')) 0)))) with NONE ->
           NONE | SOME k ->
       (let (s',_18) = evaluate_evaluate_decs
         (semanticPrimitives_state_clock_fupd (K k) s) env decs in
         SOME (oracle (orac_s (semanticPrimitives_state_eval_state
           s')) (n + 1))))`;;

let get_oracle_def = cake_define
  `get_oracle ci s env decs =
     (let es_record = EvalOracle (mk_eval_oracle_state (K
       ((0,0),compiler_instance_config_v ci
       (compiler_instance_init_state ci),[])) (do_eval_record ci) [[]]
       0) in
     extract_oracle (semanticPrimitives_state_eval_state_fupd (K
       (SOME es_record)) s) env decs)`;;

let put_oracle_def = cake_define
  `put_oracle ci orac = ((\ci. insert_gen_oracle ci I (FST o FST)) ci
  orac
     (SOME (EvalOracle (mk_eval_oracle_state (K
       ((0,0),compiler_instance_config_v ci
       (compiler_instance_init_state ci),[])) (do_eval_record ci)
       [[]] 0))))`;;

let precond_eval_state_def = cake_define
  `precond_eval_state orac ci s env decs = (match
  semanticPrimitives_state_eval_state s with NONE -> T | SOME (EvalDecs
  eds) -> EvalDecs eds = mk_init_eval_state ci /\
         (orac_extended_wf (mk_compiler_fun_from_ci ci) orac) /\
         (!i r x. get_oracle ci s env decs i = SOME r /\
           mk_compiler_fun_from_ci ci r = SOME x ==>
             orac i = r) | SOME (EvalOracle _19) -> F)`;;

(* for use in source-to-source phases, a proof that the oracle can be
   adjusted
   by any stateless compiler *)

let adjust_oracle_def = cake_define
  `adjust_oracle ci f es = (match es with
     NONE -> es | SOME (EvalDecs _20) -> es | SOME (EvalOracle o_s)
       -> SOME (EvalOracle
         (eval_oracle_state_custom_do_eval_fupd (K (do_eval_oracle
           (mk_compiler_fun_from_ci ci) f)) o_s)))`;;

(* HOL4 overload (expanded in the port):
     s_adjust_oracle = \ci f s. s with eval_state updated_by
       (adjust_oracle ci f) *)

let is_insert_oracle_def = cake_define
  `is_insert_oracle ci f es = (?es' shift_f orac. es =
  insert_gen_oracle ci f shift_f orac es')`;;
