(* ======================================================== *)
(*  flat_to_closProof: ported from HOL4's
    compiler/backend/proofs/flat_to_closProofScript.sml  *)
(* ======================================================== *)

(*
  Correctness proof for flat_to_clos
*)

needs "basis/pure/mlstring.ml";;
needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/clos_interp.ml";;
needs "compiler/backend/flatLang.ml";;
needs "compiler/backend/flat_to_clos.ml";;
needs "compiler/backend/proofs/bvi_letProof.ml";;
needs "compiler/backend/proofs/clos_interpProof.ml";;
needs "compiler/backend/semantics/backendProps.ml";;
needs "compiler/backend/semantics/closProps.ml";;
needs "compiler/backend/semantics/closSem.ml";;
needs "compiler/backend/semantics/flatProps.ml";;
needs "compiler/backend/semantics/flatSem.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;
needs "semantics/semanticPrimitives.ml";;

let v_rel = cake_inductive
  `(!n b. v_rel (Loc b n) (closSem_RefPtr b n)) /\
   (!i. v_rel (Litv (ast_IntLit i)) (closSem_Number i)) /\
   (!c. v_rel (Litv (ast_Char c)) (closSem_Number (&(ORD c)))) /\
   (!s. v_rel (Litv (ast_StrLit s)) (closSem_ByteVector (MAP (n2w o
     ORD) (explode s)))) /\
   (!b. v_rel (Litv (ast_Word8 b)) (closSem_Number (&(w2n b)))) /\
   (!w. v_rel (Litv (Word64 w)) (Word64 w)) /\
   (!f. v_rel (Litv (ast_Float64 f)) (Word64 f)) /\
   (!vs ws. LIST_REL v_rel vs ws ==> v_rel (Conv NONE vs)
     (closSem_Block 0 ws)) /\
   (!vs ws t r. LIST_REL v_rel vs ws ==> v_rel (Conv (SOME (t,r)) vs)
     (closSem_Block t ws)) /\
   (!vs ws. LIST_REL v_rel vs ws ==> v_rel (Vectorv vs)
     (closSem_Block 0 ws)) /\
   (!env m db.
     (!n x. ALOOKUP (v env) n = SOME x ==>
            indexedLists_findi (SOME n) m < LENGTH db /\
            v_rel x (EL (indexedLists_findi (SOME n) m) db)) ==>
      env_rel env (m:(mlstring option) list) (db:closSem_v list)) /\
   (!env m db n e.
      env_rel env m db /\ no_Mat e ==>
      v_rel (Closure env n e)
            (Closure NONE [] db 1 (HD (flat_to_clos_compile (SOME n
              :: m) [e])))) /\
   (!funs n env m db.
     n < LENGTH funs /\ env_rel env m db /\ ALL_DISTINCT (MAP FST
       funs) /\
     EVERY no_Mat (MAP (SND o SND) funs) ==>
      v_rel (Recclosure env funs (FST (EL n funs)))
       (Recclosure NONE [] db (MAP
             (\(f,v,x). (1,HD (flat_to_clos_compile
                        (SOME v :: (MAP (\n. SOME (FST n)) funs ++
                          m))
                        [x]))) funs) n))`;;

let store_rel_def = cake_define
  `store_rel refs t_refs =
     (!i. if LENGTH refs <= i then FLOOKUP t_refs i = NONE else
           match EL i refs with semanticPrimitives_Refv v -> (?x.
             FLOOKUP t_refs i = SOME (closSem_ValueArray [x]) /\ v_rel v
             x) | Thunk m v -> (?x. FLOOKUP t_refs i = SOME (Thunk m x)
             /\ v_rel v x) | semanticPrimitives_Varray vs -> (?xs.
             FLOOKUP t_refs i = SOME (closSem_ValueArray xs) /\
                              LIST_REL v_rel vs xs) |
                                semanticPrimitives_W8array bs ->
                                FLOOKUP t_refs i = SOME
                                (closSem_ByteArray bs))`;;

let inc_compile_decs'_def = cake_define
  `inc_compile_decs' decs = (flat_to_clos_compile_decs decs ++
     flat_to_clos_compile_decs [Con backend_common_None NONE
       []],[])`;;

let install_config_rel'_def = cake_define
  `install_config_rel' ic co cc = (
     (!i. no_Mat_decs (SND (compile_oracle ic i))) /\
     co = pure_co inc_compile_decs' o compile_oracle ic /\ compile
     ic = pure_cc inc_compile_decs' cc)`;;

let state_rel_def = cake_define
  `flat_to_closProof_state_rel (s:('c,'ffi)flatSem_state)
  (t:('c,'ffi)closSem_state) <=>
     1 <= closSem_state_max_app t /\ ffi
     s = ffi t /\ clock
     s = clock t /\
     store_rel (refs s) (refs t) /\ ~(
     LENGTH (globals t) = 0) /\
     LIST_REL (OPTREL v_rel) (globals s) (TL (globals t)) /\
     install_config_rel' (flatSem_state_eval_config s)
       (compile_oracle t) (compile t)`;;
hol4_overload "state_rel" "flat_to_closProof_state_rel";;

let initial_state'_def = cake_define
  `initial_state' b ffi ma code co cc k =
     mk_closSem_state [SOME (if b then
                            Closure NONE [] [] 1 clos_interpreter
                              else closSem_Unit)] FEMPTY ffi k cc co
                              code ma`;;

(* HOL4 ML code, not ported:
val s = ``s:('c, 'ffi) flatSem$state``;
val t = ``t:('c, 'ffi) closSem$state``;
*)

(* HOL4 ML code, not ported:
val exps_goal =
  ``\env ^s es.
      !m db res1 s1 ^t.
        evaluate env s es = (s1,res1) /\ state_rel s t /\ env_rel env m
          db /\
        EVERY no_Mat es /\ res1 <> Rerr (Rabort Rtype_error) ==>
        ?res2 t1.
          evaluate (compile m es, db, t) = (res2,t1) /\ state_rel s1 t1
            /\
          result_rel (LIST_REL v_rel) v_rel res1 res2``
*)

(* HOL4 ML code, not ported:
val dec_goal =
  ``\^s d. !res1 s1 ^t.
    evaluate_dec s d = (s1,res1) ∧ state_rel s t ∧
    no_Mat_decs [d] /\ res1 ≠ SOME (Rabort Rtype_error) ⇒
    ∃res2 t1.
      evaluate (compile_decs [d],[],t) = (res2,t1) ∧ state_rel s1 t1 /\
      ?v.
        let res1' = (case res1 of NONE => Rval v | SOME e => Rerr e) in
          result_rel (LIST_REL (\x y. T)) v_rel res1' res2``
*)

(* HOL4 ML code, not ported:
Resume compile_correct[nil]:
  fs [evaluate_def,flatSemTheory.evaluate_def,compile_def]
QED
*)

(* HOL4 ML code, not ported:
Resume compile_correct[cons]:
  rpt strip_tac
  \\ fs [evaluate_def,compile_def,flatSemTheory.evaluate_def]
  \\ fs [pair_case_eq] \\ fs []
  \\ first_x_assum drule
  \\ disch_then drule
  \\ impl_tac THEN1 (CCONTR_TAC \\ fs [])
  \\ strip_tac \\ fs [evaluate_APPEND]
  \\ fs [result_case_eq] \\ rveq \\ fs []
  \\ fs [pair_case_eq] \\ fs []
  \\ rveq \\ fs []
  \\ first_x_assum drule
  \\ disch_then drule
  \\ impl_tac THEN1 (CCONTR_TAC \\ fs [])
  \\ strip_tac \\ fs []
  \\ qpat_x_assum `_ = (s1,res1)` mp_tac
  \\ TOP_CASE_TAC \\ fs []
  \\ strip_tac \\ rveq \\ fs []
  \\ imp_res_tac evaluate_sing \\ fs []
QED
*)

(* HOL4 ML code, not ported:
Resume compile_correct[Lit]:
  fs [flatSemTheory.evaluate_def,compile_def]
  \\ Cases_on `l` \\ fs [PULL_EXISTS]
  \\ once_rewrite_tac [CONJUNCT2 v_rel_cases] \\ fs []
  \\ fs
    [compile_lit_def,evaluate_def,do_app_def,do_int_app_def
    ,make_const_def]
QED
*)

(* HOL4 ML code, not ported:
Resume compile_correct[Raise]:
  fs [evaluate_def,flatSemTheory.evaluate_def,compile_def] \\ rw []
  \\ reverse (fs [pair_case_eq,result_case_eq]) \\ rveq \\ fs []
  \\ first_x_assum drule
  \\ disch_then drule \\ strip_tac \\ rveq \\ fs []
  \\ imp_res_tac flatPropsTheory.evaluate_sing \\ fs []
QED
*)

(* HOL4 ML code, not ported:
Resume compile_correct[Handle]:
  rpt strip_tac
  \\ fs [evaluate_def,compile_def,flatSemTheory.evaluate_def]
  \\ fs [pair_case_eq] \\ fs []
  \\ imp_res_tac dest_pat_from_case
  \\ fs []
  \\ fs [dest_pat_thm] \\ rveq \\ fs []
  \\ fs [flatSemTheory.evaluate_def,evaluate_def,
         EVAL ``ALL_DISTINCT (pat_bindings (Pvar x))``,
         EVAL ``pmatch e s' (Pvar x) v []``,pmatch_rows_def]
  \\ fs [pmatch_def, pat_bindings_def]
  \\ first_x_assum drule
  \\ disch_then drule
  \\ impl_tac THEN1 (CCONTR_TAC \\ fs [])
  \\ strip_tac \\ fs []
  \\ fs [result_case_eq] \\ rveq \\ fs []
  \\ rveq \\ fs []
  \\ fs [error_result_case_eq] \\ rveq \\ fs [] \\ rveq \\ fs []
  \\ first_x_assum drule
  \\ rename [`v_rel v1 v2`]
  \\ `env_rel <| v := (nm,v1)::env.v |> (SOME nm::m) (v2::db)` by
    (match_mp_tac env_rel_CONS \\ fs [env_rel_def])
  \\ disch_then drule
  \\ strip_tac \\ fs []
QED
*)

(* HOL4 ML code, not ported:
Resume compile_correct[Let]:
  rpt strip_tac
  \\ fs [evaluate_def,compile_def,flatSemTheory.evaluate_def]
  \\ fs [pair_case_eq] \\ fs []
  \\ first_x_assum drule
  \\ disch_then drule
  \\ impl_tac THEN1 (CCONTR_TAC \\ fs [])
  \\ strip_tac \\ fs []
  \\ fs [result_case_eq] \\ rveq \\ fs []
  \\ rveq \\ fs []
  \\ first_x_assum drule
  \\ imp_res_tac evaluate_sing \\ fs [] \\ rveq \\ fs []
  \\ rename [`v_rel v1 v2`]
  \\ `env_rel (env with v updated_by opt_bind n v1) (n::m) (v2::db)` by
   (fs [env_rel_def]
    \\ Cases_on `n` \\ fs [miscTheory.opt_bind_def,findi_def,GSYM ADD1]
    \\ rw [] \\ fs [])
  \\ disch_then drule
  \\ strip_tac \\ fs []
QED
*)

(* HOL4 ML code, not ported:
Resume compile_correct[Letrec]:
  rpt strip_tac
  \\ fs [evaluate_def,compile_def,flatSemTheory.evaluate_def]
  \\ fs [EVERY_MAP]
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) \\ fs []
  \\ rpt strip_tac \\ `1 <= t.max_app` by fs [state_rel_def] \\ fs []
  \\ fs [bool_case_eq, Q.ISPEC `(a, b)` EQ_SYM_EQ]
  \\ qmatch_goalsub_abbrev_tac `GENLIST recc`
  \\ first_x_assum drule
  \\ disch_then match_mp_tac
  \\ fs [build_rec_env_eq_MAP]
  \\ match_mp_tac env_rel_APPEND \\ fs []
  \\ simp [MAP_MAP_o, MAP_EQ_f, FORALL_PROD]
  \\ fs [MAP_MAP_o,o_DEF]
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) \\ fs []
  \\ match_mp_tac LIST_REL_MAP_GENLIST \\ fs [Abbr`recc`]
  \\ once_rewrite_tac [v_rel_cases] \\ fs []
  \\ rw [MAP_EQ_f, FORALL_PROD]
  \\ qexists_tac `m`
  \\ simp [EVERY_MAP]
QED
*)

(* HOL4 ML code, not ported:
Resume compile_correct[Fun]:
  fs [evaluate_def,flatSemTheory.evaluate_def,PULL_EXISTS,compile_def]
  \\ rpt strip_tac \\ `1 <= t.max_app` by fs [state_rel_def] \\ fs []
  \\ once_rewrite_tac [v_rel_cases] \\ fs []
  \\ metis_tac []
QED
*)

(* HOL4 ML code, not ported:
Resume compile_correct[Con_NONE]:
  rpt strip_tac
  \\ fs
    [evaluate_def,compile_def,flatSemTheory.evaluate_def
    ,evaluate_SmartCons]
  \\ fs [pair_case_eq,CaseEq"bool"] \\ fs []
  \\ first_x_assum drule
  \\ fs [EVERY_REVERSE, Q.ISPEC `no_Mat` ETA_THM]
  \\ (disch_then drule \\ impl_tac THEN1 (CCONTR_TAC \\ fs []))
  \\ strip_tac \\ fs []
  \\ fs [result_case_eq] \\ rveq \\ fs []
  \\ rveq \\ fs [] \\ fs [do_app_def]
  \\ once_rewrite_tac [v_rel_cases] \\ fs []
QED
*)

(* HOL4 ML code, not ported:
Resume compile_correct[Con_SOME]:
  rpt strip_tac
  \\ fs
    [evaluate_def,compile_def,flatSemTheory.evaluate_def
    ,evaluate_SmartCons]
  \\ fs [pair_case_eq,CaseEq"bool"] \\ fs []
  \\ first_x_assum drule
  \\ fs [EVERY_REVERSE, Q.ISPEC `no_Mat` ETA_THM]
  \\ (disch_then drule \\ impl_tac THEN1 (CCONTR_TAC \\ fs []))
  \\ strip_tac \\ fs []
  \\ fs [result_case_eq] \\ rveq \\ fs []
  \\ rveq \\ fs [] \\ fs [do_app_def]
  \\ once_rewrite_tac [v_rel_cases] \\ fs []
  \\ PairCases_on `cn` \\ fs []
QED
*)

(* HOL4 ML code, not ported:
Resume compile_correct[Var_local]:
  fs [evaluate_def,flatSemTheory.evaluate_def,compile_def] \\ rpt
    strip_tac
  \\ pop_assum mp_tac \\ TOP_CASE_TAC \\ fs [env_rel_def]
QED
*)

(* HOL4 ML code, not ported:
Resume compile_correct[If]:
  rpt strip_tac
  \\ fs [evaluate_def,compile_def,flatSemTheory.evaluate_def]
  \\ fs [pair_case_eq] \\ fs []
  \\ first_x_assum drule
  \\ disch_then drule
  \\ impl_tac THEN1 (CCONTR_TAC \\ fs [])
  \\ strip_tac \\ fs []
  \\ fs [result_case_eq] \\ rveq \\ fs []
  \\ imp_res_tac evaluate_sing \\ fs [] \\ rveq \\ fs []
  \\ fs [option_case_eq] \\ fs []
  \\ fs [do_if_def,bool_case_eq] \\ rveq \\ fs []
  \\ first_x_assum drule
  \\ disch_then drule
  \\ strip_tac \\ fs []
  \\ fs [flatSemTheory.Boolv_def]
  \\ qpat_x_assum `v_rel _ _` mp_tac
  \\ once_rewrite_tac [v_rel_cases] \\ fs [Boolv_def]
QED
*)

(* HOL4 ML code, not ported:
Resume compile_correct[Mat]:
  fs [no_Mat_def,dest_pat_thm]
QED
*)

(* HOL4 ML code, not ported:
val op_goal =
  ``do_app s1 op vs = SOME (s2,res2) /\
    state_rel s1 (t1:('c,'ffi) closSem$state) /\
    evaluate (xs,db,t) = (Rval ws,t1) /\
    LIST_REL v_rel vs (REVERSE ws) /\
    LENGTH xs = LENGTH vs /\ op <> Src Opapp /\ op <> Src (ThunkOp
      ForceThunk) ==>
    ∃res2' t1.
      evaluate ([compile_op tt op xs],db,t) = (res2',t1) ∧
      state_rel s2 t1 ∧
      result_rel (LIST_REL v_rel) v_rel (evaluate$list_result res2)
        res2'``;
*)

(* HOL4 ML code, not ported:
Resume compile_correct[App]:
  rpt strip_tac
  \\ fs [evaluate_def,compile_def,flatSemTheory.evaluate_def]
  \\ rfs [pair_case_eq]
  \\ fs [EVERY_REVERSE, Q.ISPEC `no_Mat` ETA_THM]
  \\ first_x_assum drule
  \\ disch_then drule
  \\ impl_tac THEN1 (CCONTR_TAC \\ fs [])
  \\ strip_tac
  \\ Cases_on `op = Src (ThunkOp ForceThunk)` >- (
    gvs [dest_nop_def, compile_op_def, evaluate_def, AllCaseEqs(),
      PULL_EXISTS]
    \\ gvs [oneline flatSemTheory.dest_thunk_def, oneline
      dest_thunk_def,
            AllCaseEqs(), PULL_EXISTS]
    \\ rgs [Once v_rel_cases]
    \\ drule_all lookup_thunk \\ rw [] \\ gvs []
    \\ imp_res_tac state_rel_IMP_clock \\ gvs [PULL_EXISTS]
    \\ imp_res_tac state_rel_dec_clock
    \\ last_x_assum $ drule_then $ qspecl_then [`[SOME «f»]`, `[w]`]
      mp_tac
    \\ (
      impl_tac
      >- gvs [env_rel_def, findi_def, flatSemTheory.AppUnit_def]
      \\ rw [AppUnit_def, flatSemTheory.AppUnit_def, dest_nop_def,
        compile_op_def,
             arg2_def, findi_def, SmartCons_def, compile_def]
      \\ goal_assum drule \\ gvs []
      \\ drule_all rel_update_thunk \\ rw []))
  \\ Cases_on `op = Src Opapp` \\ fs []
  THEN1
   (fs [compile_op_def,dest_nop_def] \\ rveq
    \\ reverse (fs [result_case_eq] \\ rveq \\ fs [] \\ rveq \\ fs [])
    THEN1
     (Cases_on `compile m (REVERSE es)` \\ fs [arg2_def]
      \\ fs [evaluate_def]
      \\ rename [`_ = _::ys`] \\ Cases_on `ys` \\ fs [arg2_def]
      \\ fs [evaluate_def]
      \\ rename [`_ = _::_::ys`] \\ Cases_on `ys` \\ fs [arg2_def]
      \\ fs [evaluate_def] \\ fs [pair_case_eq,result_case_eq])
    \\ fs [option_case_eq,pair_case_eq] \\ rveq \\ fs []
    \\ fs [flatSemTheory.do_opapp_def]
    \\ `?f x. vs = [x;f]` by fs [list_case_eq,SWAP_REVERSE_SYM]
    \\ rveq \\ fs [] \\ rveq \\ fs []
    \\ `?ef ex. es = [ex;ef]` by
      (imp_res_tac evaluate_IMP_LENGTH \\ fs [LENGTH_compile]
       \\ Cases_on `es` \\ fs [] \\ Cases_on `t'` \\ fs [])
    \\ rveq \\ fs [] \\ rveq \\ fs []
    \\ `compile m [ef; ex] = HD (compile m [ef]) :: HD (compile m [ex])
      :: []` by
          fs [compile_def,LENGTH_compile]
    \\ asm_rewrite_tac [arg2_def] \\ fs []
    \\ fs [evaluate_def,LENGTH_compile]
    \\ qpat_x_assum `evaluate _ = _` mp_tac
    \\ once_rewrite_tac [evaluate_CONS] \\ fs []
    \\ fs [pair_case_eq,result_case_eq,PULL_EXISTS]
    \\ rpt strip_tac \\ rveq \\ fs []
    \\ `?vx. v = [vx]` by
        (imp_res_tac evaluate_IMP_LENGTH \\ fs [LENGTH_compile] \\
          Cases_on `v` \\ fs [])
    \\ rveq \\ fs []
    \\ fs [evaluate_def]
    \\ Cases_on `f` \\ fs [] \\ rveq \\ fs []
    \\ qpat_x_assum `v_rel _ _` mp_tac
    \\ once_rewrite_tac [v_rel_cases] \\ fs []
    \\ strip_tac \\ fs []
    \\ rename [`state_rel s1 t1`]
    \\ `1 <= t1.max_app /\ t1.clock = s1.clock` by fs [state_rel_def]
    \\ fs [dest_closure_def,check_loc_def] \\ rveq \\ fs []
    THEN1
     (Cases_on `s1.clock = 0`
      THEN1 (fs [] \\ fs [state_rel_def] \\ rveq \\ fs[])
      \\ fs []
      \\ rename [`compile (SOME vn::m1) [e],vx::db1,dec_clock 1 t1`]
      \\ `state_rel (dec_clock s1) (dec_clock 1 t1)` by
           fs [flatSemTheory.dec_clock_def,dec_clock_def,state_rel_def]
      \\ first_x_assum drule
      \\ `env_rel (e' with v updated_by (λenv. (vn,x)::env))
                (SOME vn::m1) (vx::db1)` by
            (ho_match_mp_tac env_rel_CONS_upd \\ fs [env_rel_def])
      \\ disch_then drule \\ strip_tac \\ fs []
      \\ Cases_on `res1` \\ fs [] \\ rveq \\ fs []
      \\ imp_res_tac evaluate_sing \\ rveq \\ fs [])
    \\ fs [EL_MAP]
    \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) \\ fs []
    \\ Cases_on `s1.clock = 0`
    THEN1 (fs [] \\ fs [state_rel_def] \\ rveq \\ fs[])
    \\ fs [option_case_eq,pair_case_eq] \\ rveq \\ fs []
    \\ `state_rel (dec_clock s1) (dec_clock 1 t1)` by
         fs [flatSemTheory.dec_clock_def,dec_clock_def,state_rel_def]
    \\ first_x_assum drule
    \\ qpat_x_assum `ALL_DISTINCT (MAP FST l0)` assume_tac
    \\ fs [find_recfun_EL]
    \\ qpat_x_assum `SND (EL n l0) = (_,_)` assume_tac
    \\ drule IMP_PAIR \\ strip_tac \\ rveq
    \\ fs []
    \\ qmatch_goalsub_abbrev_tac `evaluate (compile m2 _, db2, _)`
    \\ disch_then (qspecl_then [`m2`,`db2`] mp_tac)
    \\ reverse impl_tac
    THEN1
     (strip_tac \\ fs []
      \\ rpt (goal_assum (first_assum o mp_then Any mp_tac))
      \\ Cases_on `res1` \\ fs []
      \\ rveq \\ fs [] \\ imp_res_tac evaluate_sing \\ fs [])
    \\ unabbrev_all_tac
    \\ reverse conj_tac
    THEN1 (fs [EVERY_EL] \\ fs [EL_MAP])
    \\ fs []
    \\ match_mp_tac env_rel_CONS
    \\ fs [build_rec_env_eq_MAP]
    \\ match_mp_tac env_rel_APPEND \\ fs []
    \\ fs [MAP_MAP_o,o_DEF]
    \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) \\ fs []
    \\ match_mp_tac LIST_REL_MAP_GENLIST \\ fs [] \\ rw []
    \\ once_rewrite_tac [v_rel_cases] \\ fs []
    \\ rename [`env_rel env3 m3 db3`]
    \\ qexists_tac `m3` \\ fs []
    \\ fs [o_DEF])
  \\ Cases_on `op = Src Eval`
  THEN1 (
    simp [compile_op_def, evaluate_def, dest_nop_def]
    \\ fs [case_eq_thms, pair_case_eq] \\ rveq \\ fs []
    \\ drule (Q.INST [`ys` |-> `REVERSE zs`] do_eval_install)
    \\ simp []
    \\ rpt (disch_then drule)
    \\ strip_tac
    \\ drule_then strip_assume_tac state_rel_dec_clock
    \\ fs []
    \\ fs [bool_case_eq] \\ rveq \\ fs []
    \\ fs [Q.ISPEC `(x, y)` EQ_SYM_EQ, pair_case_eq]
    \\ fs []
    \\ last_x_assum drule
    \\ impl_tac >- (CCONTR_TAC \\ fs [])
    \\ rw []
    \\ fs [option_case_eq] \\ rveq \\ fs []
    \\ rveq \\ fs []
    \\ simp [evaluate_append, compile_def, evaluate_def, do_app_def,
             evaluate_SmartCons]
    \\ simp [v_rel_def, Unitv_def]
  )
  \\ Cases_on ‘dest_nop op es’
  THEN1
   (reverse (fs [result_case_eq])
    \\ rveq \\ fs [] \\ rveq \\ fs []
    THEN1 (drule compile_op_evaluates_args \\ fs [])
    \\ fs [option_case_eq,pair_case_eq] \\ rveq \\ fs []
    \\ rename [`state_rel s1 t1`,`LIST_REL v_rel vs ws`,`_ = SOME
      (s2,res2)`]
    \\ qmatch_goalsub_rename_tac `compile_op tt op cexps`
    \\ drule EVERY2_REVERSE
    \\ qmatch_goalsub_rename_tac `LIST_REL _ vvs`
    \\ fs [] \\ rw []
    \\ match_mp_tac (GEN_ALL compile_op_correct)
    \\ rpt (asm_exists_tac \\ fs [])
    \\ imp_res_tac evaluate_IMP_LENGTH
    \\ imp_res_tac LIST_REL_LENGTH \\ fs [])
  \\ gvs [dest_nop_thm,AllCaseEqs(),PULL_EXISTS]
  \\ qpat_x_assum ‘_ = (_,_)’ mp_tac
  \\ simp [Once compile_def,dest_nop_def,compile_op_def]
  \\ fs [arg1_def]
  \\ DEEP_INTRO_TAC compile_single_DEEP_INTRO \\ ntac 2 strip_tac
  \\ last_x_assum mp_tac
  \\ last_x_assum mp_tac
  \\ fs [flatSemTheory.evaluate_def,AllCaseEqs(),PULL_EXISTS]
  \\ fs
    [flatSemTheory.do_app_def,AllCaseEqs(),PULL_EXISTS,check_type_def,
         do_conversion_def,v_to_flat_def,flat_to_v_def]
  \\ fs [evaluate_def,AllCaseEqs(),PULL_EXISTS] \\ rw []
  \\ imp_res_tac closPropsTheory.evaluate_IMP_LENGTH
  \\ gvs [LENGTH_EQ_NUM_compute]
  \\ fs [check_type_def]
  \\ gvs [semanticPrimitivesTheory.check_type_def]
  \\ qpat_x_assum ‘v_rel _ _’ mp_tac
  \\ once_rewrite_tac [v_rel_cases] \\ fs [evaluate_def,AllCaseEqs()]
  \\ rw [] \\ gvs [integer_wordTheory.i2w_pos,ORD_BOUND,evaluate_def]
  \\ fs [v_to_flat_def]
  \\ ‘w2n w < dimword (:8)’ by fs [w2n_lt] \\ fs []
  \\ ‘¬(&w2n w > 255i)’ by intLib.COOPER_TAC \\ fs[]
  \\ rw [] \\ fs [] \\ gvs []
QED
*)

(* HOL4 ML code, not ported:
Resume compile_correct[dec]:
  rw []
  \\ fs [flatSemTheory.evaluate_def, pair_case_eq]
  \\ fs [compile_decs_def]
  \\ first_x_assum (qspecl_then [`[]`, `[]`] drule)
  \\ simp [env_rel_def]
  \\ impl_tac >- (CCONTR_TAC \\ fs [])
  \\ strip_tac
  \\ fs []
  \\ fs [case_eq_thms, bool_case_eq]
  \\ rveq \\ fs []
QED
*)

(* HOL4 ML code, not ported:
Resume compile_correct[decs_nil]:
  rw []
  \\ fs [compile_decs_def, flatSemTheory.evaluate_def, evaluate_def]
  \\ rveq \\ fs []
QED
*)

(* HOL4 ML code, not ported:
Resume compile_correct[decs_cons]:
  rw []
  \\ fs [compile_decs_def, flatSemTheory.evaluate_def, evaluate_def]
  \\ fs [pair_case_eq]
  \\ fs []
  \\ first_x_assum drule
  \\ reverse (fs [option_case_eq])
  >- (
    rveq \\ fs []
    \\ Cases_on `d` \\ fs []
    \\ fs [compile_decs_def, evaluate_append]
    \\ rw []
    \\ fs [evaluate_def]
  )
  \\ Cases_on `d` \\ fs []
  \\ fs [compile_decs_def, evaluate_append]
  \\ rw []
  \\ first_x_assum drule
  \\ rw []
  \\ fs [evaluate_def]
  \\ rveq \\ fs []
  \\ EVERY_CASE_TAC \\ fs []
  \\ metis_tac [LIST_REL_APPEND_suff]
QED
*)

(* HOL4 ML code, not ported:
Finalise compile_correct;
*)

let install_config_rel_def = cake_define
  `install_config_rel ic co cc <=>
     (!i. no_Mat_decs (SND (compile_oracle ic i))) /\
     co = pure_co inc_compile_decs o compile_oracle ic /\ compile
     ic = pure_cc inc_compile_decs cc`;;

(* HOL4 ML code, not ported:
val props_defs = [closPropsTheory.contains_App_SOME_def,
    closPropsTheory.every_Fn_vs_NONE_def,
    closPropsTheory.no_mti_def, Q.ISPEC `no_mti` ETA_THM,
    closPropsTheory.esgc_free_def]
*)
