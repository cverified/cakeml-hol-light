(* ======================================================== *)
(*  bvi_letProof: ported from HOL4's
    compiler/backend/proofs/bvi_letProofScript.sml  *)
(* ======================================================== *)

(*
  Correctness proof for bvi_let
*)

needs "compiler/backend/bvi_let.ml";;
needs "compiler/backend/pattern_matching/pattern_semantics.ml";;
needs "compiler/backend/semantics/bviProps.ml";;
needs "compiler/backend/semantics/bviSem.ml";;

let v_rel_def = cake_define
  `bvi_letProof_v_rel a x y xs ys <=> (\l n. oEL n l) ys a = SOME x`;;
hol4_overload "v_rel" "bvi_letProof_v_rel";;

let env_rel_def = cake_define
  `bvi_letProof_env_rel x1 d e1 e2 =
        match (x1,e1,e2) with
          ([],e1,e2) -> (e1 = DROP d e2)
        | ((a :: rest),(x :: e1),(y :: e2)) ->
        v_rel a x y (x :: e1) (y :: e2) /\ bvi_letProof_env_rel rest
          d e1 e2
        | (_1,_2,_3) -> F`;;
hol4_overload "env_rel" "bvi_letProof_env_rel";;

(* HOL4 ML code, not ported:
Resume evaluate_env_rel[CONS]:
  (fs [compile_def,evaluate_def]
   \\ qpat_x_assum `!x._` mp_tac
   \\ once_rewrite_tac [IMP_COMM] \\ rw [AND_IMP_INTRO]
   \\ gvs [CaseEq"prod"]
   \\ once_rewrite_tac [GSYM compile_HD_SING] \\ fs []
   \\ once_rewrite_tac [evaluate_CONS] \\ fs [compile_HD_SING]
   \\ first_assum $ drule_then drule
   \\ impl_tac >- (CCONTR_TAC \\ gvs [])
   \\ rpt strip_tac \\ gvs []
   \\ gvs [CaseEq"result"]
   \\ imp_res_tac evaluate_SING_IMP \\ gvs []
   \\ gvs [CaseEq"prod"]
   \\ pop_assum kall_tac
   \\ pop_assum $ drule_then drule
   \\ impl_tac >- (CCONTR_TAC \\ gvs [])
   \\ gvs [])
QED
*)

(* HOL4 ML code, not ported:
Resume evaluate_env_rel[Var]:
  (fs [evaluate_def] \\ every_case_tac \\ fs [] \\ rveq \\ fs []
   \\ fs [compile_def,evaluate_def]
   \\ Cases_on `LLOOKUP ax v` \\ fs []
   \\ imp_res_tac env_rel_length
   THEN1 (fs [evaluate_def] \\ metis_tac
     [env_rel_LLOOKUP_NONE,ADD_COMM])
   \\ drule env_rel_LOOKUP_SOME \\ fs [] \\ fs [v_rel_def]
   \\ disch_then drule \\ fs [] \\ rw []
   \\ fs [evaluate_def] \\ fs [LLOOKUP_EQ_EL]
   \\ fs [EL_DROP] \\ rfs [EL_DROP])
QED
*)

(* HOL4 ML code, not ported:
Resume evaluate_env_rel[RaiseTick]:
  (rw [] \\ fs [evaluate_def] \\ every_case_tac \\ fs [] \\ rveq \\ fs
    []
   \\ fs [compile_def,evaluate_def,compile_HD_SING]
   \\ first_x_assum drule \\ fs [] \\ disch_then drule
   \\ rpt (impl_tac THEN1 fs [bviTheory.exp_size_def] \\ strip_tac \\ fs
     [])
   \\ fs [compile_def,evaluate_def,compile_HD_SING])
QED
*)

(* HOL4 ML code, not ported:
Resume evaluate_env_rel[If]:
  (fs [evaluate_def] \\ every_case_tac \\ fs []
   \\ imp_res_tac evaluate_SING_IMP \\ fs [] \\ rveq \\ fs []
   \\ first_assum drule \\ qpat_x_assum `_ = _` mp_tac
   \\ TRY (first_x_assum drule \\ fs [] \\ rw [])
   \\ TRY (qpat_x_assum `!x._` drule)
   \\ TRY (qpat_x_assum `!x._` drule)
   \\ rpt (impl_tac THEN1 fs [bviTheory.exp_size_def] \\ strip_tac \\ fs
     [])
   \\ fs [compile_def,evaluate_def,compile_HD_SING]
   \\ rw [] \\ pop_assum drule
   \\ rpt (impl_tac THEN1 fs [bviTheory.exp_size_def] \\ strip_tac \\ fs
     []))
QED
*)

(* HOL4 ML code, not ported:
Resume evaluate_env_rel[Call]:
  (Cases_on `handler` \\ fs []
   \\ qpat_x_assum `!_ _ _ _ _. bb` mp_tac
   \\ once_rewrite_tac [IMP_COMM] \\ strip_tac
   >- (gvs [compile_def]
       \\ first_x_assum $ qspec_then ‘args’ mp_tac \\ gvs []
       \\ gvs [evaluate_def,CaseEq"prod"]
       \\ disch_then $ drule_then drule
       \\ impl_tac >- (CCONTR_TAC \\ gvs []) \\ gvs [])
   \\ gvs [compile_def]
   \\ first_assum $ qspec_then ‘args’ mp_tac \\ gvs []
   \\ fs [evaluate_def,CaseEq"prod",CaseEq"bool"]
   \\ disch_then $ drule_then drule
   \\ impl_tac >- (CCONTR_TAC \\ gvs []) \\ gvs []
   \\ gvs [CaseEq"result",CaseEq"option",CaseEq"prod",CaseEq"bool"]
   \\ gvs [CaseEq"error_result",CaseEq"exn_or_ret"] \\ rw
     [compile_HD_SING]
*)
   (* the handler now post-processes its result (rejecting an escaping
      Ret);
      split that inner case (the Ret branch is impossible as res <> type
        error),
      then close each surviving handler outcome by the induction
        hypothesis *)
(* HOL4 ML code, not ported:
   \\ gvs [AllCaseEqs()]
   \\ ‘env_rel (0::ax) d (v::env1) (v::env2)’ by fs
     [env_rel_def,v_rel_def,LLOOKUP_def]
   \\ ‘list_size exp_size [x] <
         ts + (exp_size x + (list_size exp_size args + (option_size (λx.
           x) dest + 3)))’
        by simp [list_size_def]
   \\ res_tac \\ gvs [])
QED
*)

(* HOL4 ML code, not ported:
Resume evaluate_env_rel[Op]:
  (rw [] \\ qpat_x_assum `!_ _ _ _ _. bb` mp_tac
   \\ once_rewrite_tac [IMP_COMM] \\ strip_tac
   \\ gvs [compile_def,evaluate_def]
   \\ gvs [evaluate_def,CaseEq"prod"]
   \\ pop_assum $ drule_at $ Pos $ el 2 \\ gvs []
   \\ disch_then drule
   \\ impl_tac >- (CCONTR_TAC \\ gvs []) \\ gvs [])
QED
*)

(* HOL4 ML code, not ported:
Resume evaluate_env_rel[Force]:
  (imp_res_tac env_rel_length \\ gvs []
   \\ gvs [evaluate_def, AllCaseEqs()]
   \\ gvs [compile_def, evaluate_def]
   \\ CASE_TAC \\ gvs []
   >>~- ([‘LLOOKUP ax n = NONE’],
     gvs [evaluate_def] \\ drule_all env_rel_LLOOKUP_NONE \\ rw [])
   \\ (
     drule env_rel_LOOKUP_SOME \\ gvs [v_rel_def]
     \\ disch_then drule \\ gvs [] \\ rw []
     \\ gvs [evaluate_def, LLOOKUP_EQ_EL, EL_DROP]))
QED
*)

(* HOL4 ML code, not ported:
Resume evaluate_env_rel[Return]:
  (rw [] \\ qpat_x_assum `!_ _ _ _ _. bb` mp_tac
   \\ once_rewrite_tac [IMP_COMM] \\ strip_tac
   \\ gvs [compile_def,evaluate_def]
   \\ gvs [evaluate_def,CaseEq"prod"]
   \\ pop_assum $ drule_at $ Pos $ el 2 \\ gvs []
   \\ disch_then drule
   \\ impl_tac >- (CCONTR_TAC \\ gvs []) \\ gvs [])
QED
*)

(* HOL4 ML code, not ported:
Resume evaluate_env_rel[LetCall]:
  (qpat_x_assum `!_ _ _ _ _. bb` mp_tac
   \\ once_rewrite_tac [IMP_COMM] \\ strip_tac
   \\ gvs [compile_def]
   \\ first_assum $ qspec_then ‘args’ mp_tac \\ gvs []
   \\ fs [evaluate_def,CaseEq"prod",CaseEq"bool"]
   \\ disch_then $ drule_then drule
   \\ impl_tac >- (CCONTR_TAC \\ gvs []) \\ gvs []
   \\ gvs [CaseEq"result",CaseEq"option",CaseEq"prod",CaseEq"bool"]
   \\ gvs [CaseEq"error_result",CaseEq"exn_or_ret"] \\ rw
     [compile_HD_SING]
   >- (first_x_assum $ irule \\ gvs []
       \\ first_x_assum $ irule_at Any
       \\ irule env_rel_REPLICATE_0 \\ fs [])
   \\ gvs [])
QED
*)

(* HOL4 ML code, not ported:
Resume evaluate_env_rel[Let]:
  (fs [] \\ rpt (qpat_x_assum `T` kall_tac) \\ rveq \\ fs [evaluate_def]
   \\ pop_assum mp_tac \\ once_rewrite_tac [IMP_COMM] \\ strip_tac
   \\ gvs [CaseEq"prod"]
   \\ gvs [compile_def]
   \\ IF_CASES_TAC \\ gvs [evaluate_def]
   >- (pop_assum $ drule_at $ Pos $ el 2 \\ gvs [])
   \\ IF_CASES_TAC \\ gvs [evaluate_def]
   THEN1
    (imp_res_tac (METIS_PROVE [SNOC_CASES] ``m <> [] ==> ?x y. m = SNOC
      x y``)
     \\ rveq \\ full_simp_tac std_ss
       [FRONT_SNOC,LAST_SNOC,LENGTH_SNOC,ADD1]
     \\ fs [evaluate_SNOC,evaluate_def,bviTheory.exp_size_def]
     \\ fs [SNOC_APPEND,exp_size_APPEND,bviTheory.exp_size_def]
     \\ Cases_on `evaluate (y,env1,s1)` \\ fs []
     \\ first_assum $ drule_at $ Pos $ el 2 \\ gvs []
     \\ disch_then drule
     \\ impl_tac >- (CCONTR_TAC \\ gvs []) \\ gvs [compile_HD_SING]
     \\ Cases_on ‘q’ \\ gvs []
     \\ rpt strip_tac
     \\ gvs [CaseEq"prod"]
     \\ first_x_assum $ irule \\ gvs []
     \\ Cases_on ‘v3’ \\ gvs [CaseEq"bool"]
     \\ qexists_tac ‘env1’ \\ gvs []
     \\ imp_res_tac evaluate_IMP_LENGTH \\ fs []
     \\ imp_res_tac evaluate_SING_IMP \\ fs [] \\ rveq
     \\ full_simp_tac std_ss [APPEND,GSYM APPEND_ASSOC,EL_APPEND2,EL,HD]
     \\ fs [env_rel_def] \\ match_mp_tac env_rel_MAP \\ fs [])
   \\ fs [evaluate_def,compile_HD_SING]
   \\ first_assum $ qspec_then ‘ys’ mp_tac
   \\ gvs [] \\ disch_then $ drule_then drule
   \\ impl_tac >- (CCONTR_TAC \\ gvs []) \\ gvs []
   \\ Cases_on `evaluate (ys,env1,s1)` \\ fs []
   \\ reverse (Cases_on `q`) \\ fs [] \\ rveq \\ gvs []
   \\ rpt (disch_then drule) \\ strip_tac
   THEN1 (drule evaluate_delete_var_Rerr \\ fs [])
   \\ fs [] \\ drule evaluate_delete_var_Rval
   \\ rpt (disch_then drule) \\ strip_tac \\ fs [] \\ fs [AND_IMP_INTRO]
   \\ first_x_assum match_mp_tac \\ fs [bviTheory.exp_size_def]
   \\ asm_exists_tac \\ fs [])
QED
*)

(* HOL4 ML code, not ported:
Finalise evaluate_env_rel;
*)
