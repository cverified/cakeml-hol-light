(* ======================================================== *)
(*  bvi_to_dataProof: ported from HOL4's
    compiler/backend/proofs/bvi_to_dataProofScript.sml  *)
(* ======================================================== *)

(*
  Correctness proof for bvi_to_data
*)

needs "compiler/backend/bvi_to_data.ml";;
needs "compiler/backend/data_live.ml";;
needs "compiler/backend/pattern_matching/pattern_semantics.ml";;
needs "compiler/backend/proofs/data_liveProof.ml";;
needs "compiler/backend/proofs/data_simpProof.ml";;
needs "compiler/backend/proofs/data_spaceProof.ml";;
needs "compiler/backend/semantics/bviProps.ml";;
needs "compiler/backend/semantics/bviSem.ml";;
needs "compiler/backend/semantics/bvlSem.ml";;
needs "compiler/backend/semantics/closSem.ml";;
needs "compiler/backend/semantics/dataProps.ml";;
needs "compiler/backend/semantics/dataSem.ml";;
needs "lib/sptree.ml";;
needs "semantics/ast.ml";;
needs "semantics/semanticPrimitives.ml";;

(* value relation *)

let code_rel_def = cake_define
  `bvi_to_dataProof_code_rel (bvi_code:(num#bvi_exp) spt)
            (data_code:(num#dataLang_prog) spt) <=>
     wf bvi_code /\ wf data_code /\
     (domain bvi_code = domain data_code) /\
     (!n exp arg_count.
       (lookup n bvi_code = SOME (arg_count,exp)) ==>
       (lookup n data_code = SOME (arg_count,compile_exp arg_count
         exp)))`;;
hol4_overload "code_rel" "bvi_to_dataProof_code_rel";;

(* Projection from `dataSem$v` into `bvlSem$v` that basically gets rid
   of
   timestamp information (note this make the function non-injective)
*)

(* TERMINATION: wf_rel_tac `measure v_size`
\\ `∀l. v1_size l = SUM (MAP (λx. v_size x + 1) l)`
   by (Induct >> rw [v_size_def])
\\ rw []
\\ IMP_RES_TAC SUM_MAP_MEM_bound
\\ ho_match_mp_tac LESS_EQ_LESS_TRANS
\\ Q.EXISTS_TAC `SUM (MAP (λx. v_size x + 1) l)`
\\ rw []
\\ ho_match_mp_tac LESS_EQ_TRANS
\\ Q.EXISTS_TAC `v_size a + 1`
\\ rw [] *)
let data_to_bvi_v_def = cake_define
  `data_to_bvi_v (Number i) = bvlSem_Number i /\
   data_to_bvi_v (Word64 w) = bvlSem_Word64 w /\
   data_to_bvi_v (CodePtr p) = bvlSem_CodePtr p /\
   data_to_bvi_v (RefPtr b r) = bvlSem_RefPtr b r /\ data_to_bvi_v
     (Block _1 tag l) = bvlSem_Block tag (MAP data_to_bvi_v l)`;;

(* Projection for Unit constant *)

(* Projection for Boolv constant *)

(* Projection for references, non-injective for value arrays *)
let data_to_bvi_ref_def = cake_define
  `data_to_bvi_ref (ValueArray l) = ValueArray (MAP data_to_bvi_v l) /\
   data_to_bvi_ref (ByteArray b bl) = ByteArray b bl /\
   data_to_bvi_ref (Thunk m v) = Thunk m (data_to_bvi_v v) /\
     data_to_bvi_ref (MutBlock tg fin ls c rs) =
     MutBlock tg fin (MAP data_to_bvi_v ls) (data_to_bvi_v c) (MAP
       data_to_bvi_v rs)`;;

(* State relation *)
let state_rel_def = cake_define
  `bvi_to_dataProof_state_rel (s:('c,'ffi)bviSem_state)
  (t:('c,'ffi)dataSem_state) <=>
     (?_clock s = ?_clock t) /\
     code_rel (?_code s) (?_code t) /\
     (?_compile_oracle t = ((I ## bvi_to_data_compile_prog) o
       ?_compile_oracle s)) /\
     (?_compile s = (\cfg prog. ?_compile t cfg
       (bvi_to_data_compile_prog prog))) /\
     (!n. FLOOKUP (?_refs s) n = lookup n (map data_to_bvi_ref
       (?_refs t))) /\
     (?_ffi s = ?_ffi t) /\
     (?_global s = ?_global t)`;;
hol4_overload "state_rel" "bvi_to_dataProof_state_rel";;

(* semantics lemmas *)

(* HOL4 overload (expanded in the port):
     isException = λx. ∃v. x = Rerr(Rraise (Exn v)) *)
(* HOL4 overload (expanded in the port):
     isReturn = λx. ∃vs. x = Rerr(Rraise (Ret vs)) *)
(* HOL4 overload (expanded in the port):
     isResult = λx. ∃v. x = Rval v *)

(* HOL4 ML code, not ported:
val stack_case_eq_thm = TypeBase.case_eq_of ``:stack``;
*)

(* HOL4 ML code, not ported:
val RW = REWRITE_RULE;
*)

(* Projection for results, injective upto `dataSem$v` *)
let data_to_bvi_result_def = cake_define
  `data_to_bvi_result x1 =
      match x1 with
        Rval vs -> Rval (MAP data_to_bvi_v vs)
      | (Rerr (Rraise v)) -> Rerr (Rraise (Exn (data_to_bvi_v v)))
      | (Rerr (Rabort err)) -> Rerr (Rabort err)`;;

(* All the `dataSem$v` values project to `bvlSem$Boolv b` satisfy
   `isBool` *)

(* Lifting `data_to_bvi_v` projection to work over `bvlSem$v list` *)

(* Special bijection for `data_to_bvi_v` with `dataSem$Number` + `MAP`
   *)

(* Special bijection for `data_to_bvi_v` with `dataSem$Word64` + `MAP`
   *)

(* Bijection of `data_to_bvi_v (Number n)` over multiple maps *)

(* Bijection of `data_to_bvi_v (Word64 n)` over multiple maps *)

(* `data_to_bvi_v_def` is idempotent over `v_to_bytes` *)

(* `data_to_bvi_v_def` is idempotent over `v_to_words` *)

(* isBool simplifications *)

(* HOL4 ML code, not ported:
val [isBool_T_F, isBool_F_T] = zip ["isBool_T_F", "isBool_F_T"]
                                   (CONJUNCTS isBool_simps) |> map
                                     save_thm;
*)

(* A variable correspondece (`var_corr`) over projecte values in `t2`
   implies all values in `a` are projections of values in `t2`
 *)

(* `data_to_bvi_v` preserves `var_corr` *)

(* Construction of the pre-image of `data_to_bvi_v`,
   wich in all cases except `Block` is bijective
 *)
(*flip LHS equalities*)

(* HOL4 ML code, not ported:
val [ data_to_bvi_eq_Number,  data_to_bvi_eq_Word64
    , data_to_bvi_eq_CodePtr, data_to_bvi_eq_RefPtr
    , data_to_bvi_eq_Block] =
      zip [ "data_to_bvi_eq_Number",  "data_to_bvi_eq_Word64"
          , "data_to_bvi_eq_CodePtr", "data_to_bvi_eq_RefPtr"
          , "data_to_bvi_eq_Block"]
          (CONJUNCTS data_to_bvi_v_eq)  |> map save_thm;
*)

(* HOL4 ML code, not ported:
val [data_to_bvi_eq_ByteArray, data_to_bvi_eq_ValueArray,
     data_to_bvi_eq_Thunk, data_to_bvi_eq_MutBlock] =
  zip ["data_to_bvi_eq_ByteArray", "data_to_bvi_eq_ValueArray",
       "data_to_bvi_eq_Thunk", "data_to_bvi_eq_MutBlock"]
      (CONJUNCTS data_to_bvi_ref_eq)  |> map save_thm;
*)

(* Construction of the pre-image of `data_to_bvi_result` *)

(* `data_to_bvi_v` preservers `do_eq` *)

(*
Theorem data_to_bvi_v_list_to_v_EQ_TS:
  ∀vl v ts1 ts2.
   data_to_bvi_v (list_to_v ts1 v vl) = data_to_bvi_v (list_to_v ts2 v
     vl)
Proof
  Induct \\ rw [list_to_v_def,data_to_bvi_v_def]
QED
*)

(* bviSem$finalise_cons is simulated by dataSem$finalise_cons: the extra
   time stamps taken by the dataLang version are invisible to the
     projection *)

(* HOL4 ML code, not ported:
fun cases_on_op q = Cases_on q
  >>> TRY_LT (SELECT_LT_THEN (Q.RENAME_TAC [‘BlockOp b_’]) (Cases_on
    `b_`))
  >>> TRY_LT (SELECT_LT_THEN (Q.RENAME_TAC [‘GlobOp g_’]) (Cases_on
    `g_`))
  >>> TRY_LT (SELECT_LT_THEN (Q.RENAME_TAC [‘MemOp m_’]) (Cases_on
    `m_`));
*)

(* HOL4 ML code, not ported:
fun note_tac s g = (print ("compile_correct: " ^ s ^ "\n"); ALL_TAC g);
*)

(* HOL4 ML code, not ported:
Resume compile_correct[NIL]:
   (note_tac "NIL"
    \\ SRW_TAC [] [var_corr_def,data_to_bvi_v_def]
    \\ CCONTR_TAC \\ FULL_SIMP_TAC std_ss [NOT_LESS]
    \\ RES_TAC \\ FULL_SIMP_TAC std_ss [])
QED
*)

(* HOL4 ML code, not ported:
Resume compile_correct[CONS]:
   (note_tac "CONS"
    \\ `?c1 v1 n1. compile n corr F live [x] = (c1,v1,n1)` by METIS_TAC
      [PAIR]
    \\ `?c2 vs n2. compile n1 corr F (HD v1::live) (y::xs) = (c2,vs,n2)`
      by
      METIS_TAC [PAIR]
    \\ FULL_SIMP_TAC std_ss [LET_DEF,evaluate_def]
    \\ Cases_on `evaluate ([x],env,s)`
    \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) []
    \\ rpt var_eq_tac >> full_simp_tac(srw_ss())[]
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t1`,`n`,`corr`,`F`,`live`])
    \\ FULL_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
    \\ Cases_on `pres` \\ FULL_SIMP_TAC std_ss []
    \\ TRY (qexists_tac `ls` \\ rw [] \\ NO_TAC)
    \\ Cases_on `evaluate (y::xs,env,r)`
    \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) []
    \\ rpt var_eq_tac >> full_simp_tac(srw_ss())[]
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t2`,`n1`,`corr`,`F`,`HD
      v1::live`])
    \\ simp[]
    \\ `EVERY (\n. lookup n t2.locals <> NONE) (HD v1::live)` by
      (IMP_RES_TAC evaluate_SING_IMP \\ FULL_SIMP_TAC (srw_ss()) []
       \\ IMP_RES_TAC compile_SING_IMP
       \\ full_simp_tac(srw_ss())[var_corr_def,get_var_def,lookup_map]
       \\ full_simp_tac(srw_ss())[EVERY_MEM] \\ REPEAT STRIP_TAC \\
         RES_TAC
       \\ Cases_on `lookup n' t1.locals` \\ full_simp_tac(srw_ss())[] \\
         METIS_TAC [])
    \\ full_simp_tac(srw_ss())[] \\ strip_tac
    \\ Cases_on `pres` \\ FULL_SIMP_TAC (srw_ss()) [var_corr_def]
    \\ IMP_RES_TAC evaluate_SING_IMP \\ FULL_SIMP_TAC (srw_ss()) []
    \\ IMP_RES_TAC compile_SING_IMP \\ FULL_SIMP_TAC (srw_ss()) []
    \\ REPEAT STRIP_TAC THEN1 DECIDE_TAC THEN1 DECIDE_TAC
    \\ FULL_SIMP_TAC std_ss [EVERY_MEM]
    \\ FULL_SIMP_TAC std_ss [get_var_def,lookup_map]
    \\ metis_tac [])
QED
*)

(* HOL4 ML code, not ported:
Resume compile_correct[Var]:
   (note_tac "Var"
    \\ Cases_on `tail` \\ FULL_SIMP_TAC std_ss []
    \\ Cases_on `n < LENGTH env`
    \\ fs[any_el_ALT]
    \\ FULL_SIMP_TAC (srw_ss()) [evaluate_def]
    \\ FULL_SIMP_TAC std_ss [var_corr_def]
    \\ FULL_SIMP_TAC std_ss [var_corr_def,LIST_REL_def]
    \\ FULL_SIMP_TAC std_ss [listTheory.LIST_REL_EL_EQN]
    \\ FULL_SIMP_TAC (srw_ss())
      [dataSemTheory.get_vars_def,get_var_def,set_var_def,lookup_insert
      ,lookup_map]
    \\ rfs []
    \\ RES_TAC
    \\ Q.MATCH_ASSUM_RENAME_TAC `k < LENGTH env`
    \\ FULL_SIMP_TAC (srw_ss())
      [dataSemTheory.get_vars_def,state_rel_def,call_env_def
      ,data_to_bvi_result_def,flush_state_def]
    \\ REPEAT STRIP_TAC
    \\ DISJ1_TAC \\ CCONTR_TAC
    \\ `n' ≤ k'` by fs[]
    \\ RES_TAC \\ fs[])
QED
*)

(* HOL4 ML code, not ported:
Resume compile_correct[If]:
   (note_tac "If"
    \\ `?c1 v1 n1. compile n corr F live [x1] = (c1,v1,n1)` by METIS_TAC
      [PAIR]
    \\ `?c2 v2 n2. compile n1 corr tail live [x2] = (c2,v2,n2)` by
      METIS_TAC [PAIR]
    \\ `?c3 v3 n3. compile n2 corr tail live [x3] = (c3,v3,n3)` by
      METIS_TAC [PAIR]
    \\ FULL_SIMP_TAC std_ss [LET_DEF,evaluate_def]
    \\ Cases_on `tail` \\ FULL_SIMP_TAC std_ss []
    \\ SIMP_TAC std_ss [evaluate_def]
    \\ Cases_on `evaluate ([x1],env,s)` \\ FULL_SIMP_TAC (srw_ss()) []
    \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) []
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t1`,`n`,`corr`,`F`,`live`])
    \\ rpt var_eq_tac >> full_simp_tac(srw_ss())[] >> strip_tac
    \\ Cases_on `pres`
    \\ FULL_SIMP_TAC (srw_ss()) []
    \\ IMP_RES_TAC evaluate_SING_IMP \\ FULL_SIMP_TAC (srw_ss()) []
    \\ IMP_RES_TAC compile_SING_IMP \\ FULL_SIMP_TAC (srw_ss()) []
    \\ SRW_TAC [] []
    \\ TRY (qexists_tac `ls` \\ rw [] \\ NO_TAC)
    \\ Q.MATCH_ASSUM_RENAME_TAC `var_corr [w] [n5] (map data_to_bvi_v
      t2.locals)`
    \\ `∃z. get_var n5 t2.locals = SOME z ∧ w = data_to_bvi_v z` by
          FULL_SIMP_TAC (srw_ss()) [var_corr_def,lookup_map,get_var_def]
    \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [LET_DEF]
    \\ CONV_TAC (DEPTH_CONV (DEPTH_CONV PairRules.PBETA_CONV))
    \\ IMP_RES_TAC compile_LESS_EQ
    THEN1
     (`EVERY (\n. lookup n t2.locals <> NONE) live` by
        (full_simp_tac(srw_ss())[EVERY_MEM] \\ REPEAT STRIP_TAC \\
          RES_TAC
         \\ Cases_on `lookup n' t1.locals` \\ full_simp_tac(srw_ss())[]
           \\ METIS_TAC [])
      \\ Cases_on `isBool T z ∨ isBool F z`
      \\ FULL_SIMP_TAC (srw_ss()) []
      \\ FULL_SIMP_TAC (srw_ss()) [GSYM isBool_eq, isBool_simps]
      THEN1
       (Q.PAT_X_ASSUM `(res,s2) = bb` (ASSUME_TAC o GSYM)
        \\ FULL_SIMP_TAC std_ss []
        \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL
          [`t2`,`n1`,`corr`,`T`,`live`])
        \\ FULL_SIMP_TAC std_ss [])
      \\ Q.PAT_X_ASSUM `(res,s2) = bb` (ASSUME_TAC o GSYM)
      \\ FULL_SIMP_TAC std_ss []
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t2`,`n2`,`corr`,`T`,`live`])
      \\ FULL_SIMP_TAC std_ss []
      \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
      THEN1
       (REPEAT STRIP_TAC \\ FIRST_X_ASSUM MATCH_MP_TAC \\ DECIDE_TAC)
      \\ FULL_SIMP_TAC std_ss [])
    \\ `EVERY (\n. lookup n t2.locals <> NONE) live` by
           (full_simp_tac(srw_ss())[EVERY_MEM] \\ REPEAT STRIP_TAC \\
             RES_TAC
            \\ Cases_on `lookup n' t1.locals` \\
              full_simp_tac(srw_ss())[] \\ METIS_TAC [])
    \\ Cases_on `isBool T z ∨ isBool F z`
    \\ FULL_SIMP_TAC (srw_ss()) []
    \\ FULL_SIMP_TAC (srw_ss()) [GSYM isBool_eq, isBool_simps]
    THEN1
     (Q.PAT_X_ASSUM `(res,s2) = bb` (ASSUME_TAC o GSYM)
      \\ FULL_SIMP_TAC std_ss []
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t2`,`n1`,`corr`,`F`,`live`])
      \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC
      \\ FULL_SIMP_TAC std_ss []
      \\ Cases_on `pres` \\ FULL_SIMP_TAC (srw_ss()) []
      \\ Cases_on `res` \\ FULL_SIMP_TAC (srw_ss()) []
      \\ IMP_RES_TAC evaluate_SING_IMP \\ FULL_SIMP_TAC (srw_ss()) []
      \\ SRW_TAC [] []
      \\ Q.MATCH_ASSUM_RENAME_TAC `var_corr [w7] [n7] (_ _ (_ t7))`
      \\ `∃z7. get_var n7 t7.locals = SOME z7 ∧ w7 = data_to_bvi_v z7`
               by FULL_SIMP_TAC (srw_ss())
                 [var_corr_def,lookup_map,get_var_def]
      \\ FULL_SIMP_TAC (srw_ss()) [set_var_def,state_rel_def,
                                   var_corr_def,get_var_def
                                     ,lookup_insert,lookup_map]
      \\ REPEAT STRIP_TAC
      THEN1 DECIDE_TAC
      THEN1 (SRW_TAC [] [] THEN1 DECIDE_TAC
             \\ FIRST_X_ASSUM MATCH_MP_TAC \\ DECIDE_TAC)
      THEN1
       (Cases_on ‘lookup k t7.locals’ \\ gvs [] \\ res_tac \\ gvs [])
      THEN1
       (`∀k. n2 ≤ k ⇒ lookup k (map data_to_bvi_v t7.locals) = NONE`
           by rw [lookup_map]
        \\ FULL_SIMP_TAC std_ss [listTheory.LIST_REL_EL_EQN]
        \\ REPEAT STRIP_TAC
        \\ Q.MATCH_ASSUM_RENAME_TAC `l < LENGTH env`
        \\ sg `EL l corr <> n3` \\ FULL_SIMP_TAC std_ss []
        \\ `n2 <= n3 /\ l < LENGTH corr` by DECIDE_TAC
        \\ `lookup n3 (map data_to_bvi_v t7.locals) = NONE` by METIS_TAC
          []
        \\ RES_TAC \\ CCONTR_TAC \\ FULL_SIMP_TAC std_ss [])
      THEN1 (Cases_on `k = n3` \\ FULL_SIMP_TAC (srw_ss()) []
             \\ RES_TAC \\ DECIDE_TAC)
      THEN1 (Cases_on `k = n3` \\ FULL_SIMP_TAC (srw_ss()) []
             \\ SRW_TAC [] [] \\ `n1 <= k` by DECIDE_TAC
             \\ RES_TAC \\ FULL_SIMP_TAC std_ss [])
      \\ FULL_SIMP_TAC std_ss [jump_exc_NONE,lookup_map]
      \\ qexists_tac `ls` \\ simp [])
    THEN1
     (Q.PAT_X_ASSUM `(res,s3) = bb` (ASSUME_TAC o GSYM)
      \\ FULL_SIMP_TAC std_ss []
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t2`,`n2`,`corr`,`F`,`live`])
      \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
       (FULL_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
        \\ FIRST_X_ASSUM MATCH_MP_TAC \\ DECIDE_TAC)
      \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss []
      \\ Cases_on `pres` \\ FULL_SIMP_TAC (srw_ss()) []
      \\ Cases_on `res` \\ FULL_SIMP_TAC (srw_ss()) []
      \\ IMP_RES_TAC evaluate_SING_IMP \\ FULL_SIMP_TAC (srw_ss()) []
      \\ SRW_TAC [] []
      \\ Q.MATCH_ASSUM_RENAME_TAC `var_corr [w7] [n7] (_ _ (_ t7))`
      \\ `∃z7. get_var n7 t7.locals = SOME z7 ∧ w7 = data_to_bvi_v z7`
            by FULL_SIMP_TAC (srw_ss())
              [var_corr_def,lookup_map,get_var_def]
      \\ FULL_SIMP_TAC (srw_ss()) [set_var_def,state_rel_def,
                                   var_corr_def,get_var_def
                                     ,lookup_insert,lookup_map]
      \\ REPEAT STRIP_TAC
      THEN1 DECIDE_TAC
      THEN1 (SRW_TAC [] [] THEN1 DECIDE_TAC
             \\ FIRST_X_ASSUM MATCH_MP_TAC \\ DECIDE_TAC)
      THEN1
       (Cases_on ‘lookup k t7.locals’ \\ gvs [] \\ res_tac \\ gvs [])
      THEN1
       (FULL_SIMP_TAC std_ss [listTheory.LIST_REL_EL_EQN]
        \\ REPEAT STRIP_TAC
        \\ Q.MATCH_ASSUM_RENAME_TAC `l < LENGTH env`
        \\ sg `EL l corr <> n3` \\ FULL_SIMP_TAC std_ss []
        \\ `n3 <= n3 /\ l < LENGTH corr` by DECIDE_TAC
        \\ `lookup n3 t7.locals = NONE` by METIS_TAC []
        \\ RES_TAC \\ CCONTR_TAC \\ FULL_SIMP_TAC std_ss [])
      THEN1 (Cases_on `k = n3` \\ FULL_SIMP_TAC (srw_ss()) []
             \\ RES_TAC \\ DECIDE_TAC)
      THEN1 (Cases_on `k = n3` \\ FULL_SIMP_TAC (srw_ss()) []
             \\ SRW_TAC [] [] \\ `n1 <= k` by DECIDE_TAC
             \\ RES_TAC \\ FULL_SIMP_TAC std_ss [])
      \\ FULL_SIMP_TAC std_ss [jump_exc_NONE]
      \\ qexists_tac `ls` \\ simp []))
QED
*)

(* HOL4 ML code, not ported:
Resume compile_correct[Let]:
   (note_tac "Let"
    \\ `?c1 vs n1. compile n corr F live xs = (c1,vs,n1)` by METIS_TAC
      [PAIR]
    \\ `?c2 v2 n2. compile n1 (vs ++ corr) tail live [x2] =
       (c2,v2,n2)` by METIS_TAC [PAIR]
    \\ FULL_SIMP_TAC std_ss [LET_DEF,evaluate_def]
    \\ Cases_on `evaluate (xs,env,s)`
    \\ reverse (Cases_on `q`) \\ FULL_SIMP_TAC (srw_ss()) []
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t1`,`n`,`corr`,`F`,`live`])
    \\ rpt var_eq_tac >> full_simp_tac(srw_ss())[] >> strip_tac
    \\ Cases_on `pres`
    \\ FULL_SIMP_TAC (srw_ss()) []
    \\ TRY (qexists_tac `ls` \\ rw [] \\ NO_TAC)
    \\ Q.PAT_X_ASSUM `(res,s2) = bb` (ASSUME_TAC o GSYM)
    \\ FULL_SIMP_TAC std_ss []
    \\ `var_corr (a ++ env) (vs ++ corr) (map data_to_bvi_v t2.locals)`
      by
      (FULL_SIMP_TAC (srw_ss()) [var_corr_def]
       \\ MATCH_MP_TAC (GEN_ALL EVERY2_APPEND_suff)
       \\ FULL_SIMP_TAC std_ss [LIST_REL_REVERSE_EQ])
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t2`,`n1`,`vs ++
      corr`,`tail`,`live`])
    \\ `EVERY (\n. lookup n t2.locals <> NONE) live` by
      (full_simp_tac(srw_ss())[EVERY_MEM] \\ REPEAT STRIP_TAC \\ RES_TAC
       \\ Cases_on `lookup n' t1.locals` \\ full_simp_tac(srw_ss())[] \\
         METIS_TAC [])
    \\ FULL_SIMP_TAC std_ss []
    \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss []
    \\ Cases_on `pres` \\ FULL_SIMP_TAC (srw_ss()) []
    \\ REPEAT STRIP_TAC THEN1 DECIDE_TAC
    \\ FULL_SIMP_TAC std_ss [EVERY_MEM]
    \\ FULL_SIMP_TAC std_ss [var_corr_def]
    \\ IMP_RES_TAC LIST_REL_APPEND_IMP
    \\ IMP_RES_TAC LIST_REL_LENGTH
    \\ FULL_SIMP_TAC (srw_ss()) []
    \\ qexists_tac `ls` \\ rw [] \\ fs [])
QED
*)

(* HOL4 ML code, not ported:
Resume compile_correct[Raise]:
   (note_tac "Raise"
    \\ `?c1 v1 n1. compile n corr F live [x1] = (c1,v1,n1)` by METIS_TAC
      [PAIR]
    \\ FULL_SIMP_TAC std_ss
      [LET_DEF,evaluate_def,call_env_def,flush_state_def]
    \\ Cases_on `evaluate ([x1],env,s)` \\ FULL_SIMP_TAC (srw_ss()) []
    \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) []
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t1`,`n`,`corr`,`F`,`live`])
    \\ rpt var_eq_tac >> full_simp_tac(srw_ss())[] >> strip_tac
    \\ Cases_on `pres`
    \\ FULL_SIMP_TAC (srw_ss()) []
    \\ IMP_RES_TAC evaluate_SING_IMP \\ FULL_SIMP_TAC (srw_ss()) []
    \\ IMP_RES_TAC compile_SING_IMP \\ FULL_SIMP_TAC (srw_ss()) []
    \\ SRW_TAC [] []
    \\ TRY (qexists_tac `ls` \\ rw [] \\ NO_TAC)
    \\ `∃z. get_var t t2.locals = SOME z ∧ w = data_to_bvi_v z`
          by full_simp_tac(srw_ss())[var_corr_def,get_var_def
            ,lookup_map]
         \\ full_simp_tac(srw_ss())[] \\ Cases_on `jump_exc t2` \\
           full_simp_tac(srw_ss())[]
         \\ FULL_SIMP_TAC std_ss [state_rel_def]
         \\ IMP_RES_TAC jump_exc_IMP \\ full_simp_tac(srw_ss())[]
         \\ full_simp_tac(srw_ss())[jump_exc_def,data_to_bvi_result_def]
         \\ qexists_tac `ls` \\ simp [])
QED
*)

(* HOL4 ML code, not ported:
Resume compile_correct[Return]:
   (note_tac "Return"
    \\ `?c1 v1 n1. compile n corr F live xs = (c1,v1,n1)` by METIS_TAC
      [PAIR]
    \\ FULL_SIMP_TAC std_ss [LET_DEF,evaluate_def]
    \\ Cases_on `evaluate (xs,env,s)` \\ FULL_SIMP_TAC (srw_ss()) []
    \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) []
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t1`,`n`,`corr`,`F`,`live`])
    \\ rpt var_eq_tac >> full_simp_tac(srw_ss())[] >> strip_tac
    \\ Cases_on `pres` \\ FULL_SIMP_TAC (srw_ss()) []
    >- (imp_res_tac get_vars_lift_thm
        \\ gvs[flush_state_def,state_rel_def])
    \\ qexists_tac `ls` \\ rw[])
QED
*)

(* HOL4 ML code, not ported:
Resume compile_correct[Op]:
   (note_tac "Op"
    \\ `?c1 vs n1. compile n corr F live xs = (c1,vs,n1)` by METIS_TAC
      [PAIR]
    \\ FULL_SIMP_TAC std_ss [LET_DEF,evaluate_def]
    \\ Cases_on `evaluate (xs,env,s)`
    \\ reverse (Cases_on `q`) \\ FULL_SIMP_TAC (srw_ss()) []
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t1`,`n`,`corr`,`F`,`live`])
    \\ rpt var_eq_tac >> full_simp_tac(srw_ss())[] >> strip_tac
    \\ Cases_on `pres`
    \\ FULL_SIMP_TAC (srw_ss()) []
    THEN1 (SRW_TAC [] [evaluate_def] \\ qexists_tac `ls` \\ simp [])
    \\ `domain (list_to_num_set (REVERSE vs ++ live ++ corr)) SUBSET
        domain (map data_to_bvi_v t2.locals)` by
      (full_simp_tac(srw_ss())[SUBSET_DEF,domain_lookup,
                               lookup_list_to_num_set,EVERY_MEM]
       \\ REPEAT STRIP_TAC \\ RES_TAC
       \\ full_simp_tac(srw_ss())[var_corr_def,get_var_def,lookup_map]
       \\ IMP_RES_TAC LIST_REL_MEM_IMP \\ full_simp_tac(srw_ss())[]
       \\ `lookup x t1.locals <> NONE` by METIS_TAC []
       \\ Cases_on `lookup x t1.locals` \\ full_simp_tac(srw_ss())[]
       \\ METIS_TAC [])
    \\ full_simp_tac(srw_ss())[]
    \\ Q.ABBREV_TAC `env1 = mk_wf (inter t2.locals (list_to_num_set
      (REVERSE vs++live++corr)))`
    \\ Q.ABBREV_TAC `env2 = mk_wf (inter t2.locals (list_insert vs
      (list_to_num_set (REVERSE vs++live++corr))))`
    \\ `var_corr (REVERSE a) (REVERSE vs) (map data_to_bvi_v env1)` by
      (UNABBREV_ALL_TAC
       \\ full_simp_tac(srw_ss())[var_corr_def,get_var_def,state_rel_def
         ,
                                  lookup_inter_EQ,lookup_list_to_num_set
                                    ,lookup_map]
       \\ Q.PAT_X_ASSUM `LIST_REL rrr xs1 xs2` MP_TAC
       \\ ONCE_REWRITE_TAC [LIST_REL_MEM]
       \\ full_simp_tac(srw_ss())[EVERY2_REVERSE] \\ NO_TAC)
    \\ `env2 = env1`
      by (UNABBREV_ALL_TAC \\
      simp[spt_eq_thm,lookup_inter_alt,domain_list_insert2,
       domain_list_to_num_set2,SF DISJ_ss])
    \\ POP_ASSUM $ ASSUME_NAMED_TAC "ENV2=ENV1"
    \\ IMP_RES_TAC get_vars_thm
    \\ IMP_RES_TAC get_vars_lift_thm
    \\ `state_rel r (t2 with <|locals := env1; space := 0|>)` by
      (full_simp_tac(srw_ss())[state_rel_def] \\ NO_TAC)
    \\ `z = REVERSE z'` by
      (rveq \\ UNABBREV_ALL_TAC
       \\ fs [get_vars_mk_wf]
       \\ IMP_RES_TAC get_vars_inter
       \\ IMP_RES_TAC get_vars_reverse
       \\ rveq \\ fs [])
    \\ gvs []
    \\ reverse(Cases_on `do_app op (MAP data_to_bvi_v (REVERSE z')) r`)
      \\ full_simp_tac(srw_ss())[]
    >-
   (imp_res_tac bviPropsTheory.do_app_err >> gvs[]
    \\ `get_vars (REVERSE vs) t2.locals = SOME (REVERSE z')` by
       (unabbrev_all_tac \\ imp_res_tac get_vars_inter \\ fs[])
    \\ `cut_env (list_to_num_set (REVERSE vs ++ live ++ corr)) t2.locals
      = SOME env1` by
       (unabbrev_all_tac \\ fs[cut_env_def])
    \\ `do_app (FFI i) (REVERSE z') (t2 with locals := env1) =
          Rerr (Rabort (Rffi_error x))` by
       (`state_rel r (t2 with locals := env1)` by fs[state_rel_def]
        \\ drule_all state_rel_do_app_FFI_err \\ fs[])
    \\ Cases_on `tail`
    \\ fs[evaluate_def,iAssign_def,dataLangTheory.op_requires_names_def,
          cut_state_opt_def,cut_state_def]
    \\ gvs[data_to_bvi_result_def,flush_state_def,state_rel_def])
    >-
   (PairCases_on `a` \\ full_simp_tac(srw_ss())[] \\ REV_FULL_SIMP_TAC
     std_ss []
    \\ rpt var_eq_tac >> full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[LET_DEF,evaluate_def,iAssign_def]
    \\ (fn (hs,goal) => (reverse (sg `let tail = F in ^goal`))
                        (hs,goal)) THEN1
     (full_simp_tac(srw_ss())[LET_DEF]
      \\ reverse (Cases_on `tail`) THEN1 METIS_TAC []
      \\ full_simp_tac(srw_ss())[evaluate_def,dataSemTheory.get_vars_def
        ,LET_DEF] \\ REV_FULL_SIMP_TAC std_ss []
      \\ Cases_on `pres` \\ full_simp_tac(srw_ss())[]
      \\ `∃z2. get_var n1 t2'.locals = SOME  z2 ∧ a0 = data_to_bvi_v z2`
            by FULL_SIMP_TAC (srw_ss())
              [var_corr_def,lookup_map,get_var_def]
           \\ full_simp_tac(srw_ss())[var_corr_def,call_env_def
             ,flush_state_def,state_rel_def,data_to_bvi_result_def
             ,dataSemTheory.get_vars_def,get_var_def])
    \\ simp[]
    \\ Cases_on`op = Install` >-
  (fs[dataLangTheory.op_requires_names_def,domain_map]
   \\ simp[dataSemTheory.evaluate_def,cut_state_opt_def,cut_state_def
     ,cut_env_def]
   \\ fs[ EVAL ``op_requires_names Install``]
   \\ fs[bviSemTheory.do_app_def,dataSemTheory.do_app_def]
   \\ fs[bviSemTheory.do_install_def,dataSemTheory.do_install_def]
   \\ fs[case_eq_thms,GSYM MAP_REVERSE,bvlSemTheory.case_eq_thms]
   \\ ntac 4 (rfs [MAP_EQ_CONS])
   \\ fs [v_to_words_eq,v_to_bytes_eq,data_to_bvi_v_eq]
   \\ rveq
   \\ fs[bvlPropsTheory.case_eq_thms,case_eq_thms]
   \\ rpt(pairarg_tac \\ fs[])
   \\ fs[Once SWAP_REVERSE_SYM]
   \\ rveq \\ fs[]
   \\ fs[bvlPropsTheory.case_eq_thms,case_eq_thms] \\ rveq
   \\ Cases_on`progs` \\ fs[]
   >- (
     rfs[state_rel_def]
     \\ gvs[compile_prog_def] )
   \\ `r.compile = λcfg prog. t2.compile cfg (compile_prog prog)` by
     fs[state_rel_def]
   \\ `t2.compile_oracle = (I ## compile_prog) o r.compile_oracle` by
     fs[state_rel_def]
   \\ fs[] \\ rveq \\
     fs[shift_seq_def,dataLangTheory.op_requires_names_def]
   \\ Cases_on`h`
   \\ fs[set_var_def,lookup_insert,var_corr_def,state_rel_def,
         o_DEF,get_var_def,lookup_insert,lookup_map]
   \\ simp [SF DNF_ss]
   \\ fs[set_var_def,lookup_insert,var_corr_def,state_rel_def,
         o_DEF,get_var_def,lookup_insert,lookup_map]
*)
   (* single-cut: do_app reads args from full t2.locals (pre-cut);
      recover
      get_vars over t2.locals from the get_vars over the cut env1 *)
(* HOL4 ML code, not ported:
   \\ `get_vars (REVERSE vs) t2.locals =
         SOME [x0; x0'; Number (&LENGTH bytes); Number (&LENGTH data)]`
           by
        (qpat_x_assum `get_vars (REVERSE vs) env1 = _` mp_tac
         \\ simp[Abbr`env1`] \\ strip_tac \\ imp_res_tac get_vars_inter
           \\ fs[])
   \\ fs[]
   \\ qpat_x_assum `REVERSE vs = [_;_;_;_]` (assume_tac o GSYM) \\ fs[]
   \\ qmatch_goalsub_abbrev_tac`fromAList progs1`
   \\ qmatch_goalsub_abbrev_tac`union t2.code (fromAList progs2)`
   \\ qexists_tac `x0` \\ qexists_tac `x0'` \\ fs[]
   \\ conj_tac
   >- (qpat_x_assum `vs = [v; v'; v''; v'³']` (fn th => fs[th] \\
     assume_tac th) \\ fs[])
   \\ conj_tac
   >- (
     rveq \\
     fs[code_rel_def,wf_union,wf_fromAList,domain_union,compile_prog_def
       ,domain_fromAList,
        compile_part_thm,MAP_MAP_o,o_DEF,UNCURRY,ETA_AX] \\
     fs[lookup_union,lookup_fromAList, ALOOKUP_MAP]
     \\ rpt gen_tac
     \\ TOP_CASE_TAC \\ fs[]
     >- (
       TOP_CASE_TAC \\ fs[]
       \\ fs[EXTENSION,domain_lookup]
       \\ metis_tac[NOT_SOME_NONE] )
     \\ rw[] \\ res_tac \\ fs[] )
   \\ rveq \\ fs[] \\ rveq
   \\ conj_tac
   >- ( simp[Abbr`env1`] \\ fs[lookup_inter_alt] )
   \\ conj_tac >- (
     fs[LIST_REL_EL_EQN]
     \\ rw[Abbr`env1`,lookup_inter_EQ,lookup_list_to_num_set]
     >- ( res_tac \\ fs[] )
     \\ METIS_TAC[MEM_EL] )
   \\ conj_tac >- (
     rw[Abbr`env1`,lookup_inter_alt] \\ res_tac \\ fs[] )
   \\ conj_tac >- (
     rw[Abbr`env1`,lookup_inter_alt]
     \\ fs [domain_list_to_num_set])
   \\ reverse conj_tac >- (
     fs[compile_prog_def,compile_part_thm,Abbr`progs1`
       ,data_to_bvi_v_def]
     \\ fs[markerTheory.Abbrev_def] )
   \\ rw[] \\ res_tac
   \\ fs[jump_exc_def]
   \\ TOP_CASE_TAC \\ fs[]
   \\ TOP_CASE_TAC \\ fs[])
    \\ Cases_on `op = IntOp Greater` >-
   (fs [dataLangTheory.op_requires_names_def,
     dataLangTheory.op_space_reset_def]
    \\ fs [dataSemTheory.evaluate_def,cut_state_opt_def]
    \\ fs [cut_state_def,cut_env_def,domain_map]
    \\ fs[domain_list_insert2,domain_list_to_num_set2]
    \\ fs [dataLangTheory.op_requires_names_def]
    \\ imp_res_tac get_vars_reverse \\ fs []
    \\ qpat_x_assum `bviSem$do_app _ _ _ = _` mp_tac
    \\ simp [bviSemTheory.do_app_def,bviSemTheory.do_app_aux_def,
             bvlSemTheory.do_app_def,oneline
               bvlSemTheory.do_int_app_def]
    \\ disch_then (mp_tac o SRULE[AllCaseEqs(),PULL_EXISTS])
    \\ fs [SWAP_REVERSE_SYM,MAP_EQ_CONS]
    \\ strip_tac \\ rveq
    \\ simp[dataSemTheory.do_app_def, dataSemTheory.do_space_def,
            dataSemTheory.do_app_aux_def, dataSemTheory.do_stack_def,
            EVAL ``op_space_reset (IntOp Less)``, EVAL ``op_space_reset
              (IntOp LessEq)``]
    \\ simp[EVAL ``do_int_app Less [Number i'; Number i]``,
            EVAL ``do_int_app LessEq [Number i'; Number i]``]
    \\ simp[EVAL ``op_space_reset (IntOp Less)``, EVAL ``op_space_reset
      (IntOp LessEq)``]
    \\ fs
      [set_var_def,lookup_insert,integerTheory.int_gt
      ,integerTheory.int_ge]
    \\ fs [state_rel_def]
    \\ fs [EVAL ``(bvl_to_bvi (bvi_to_bvl r) r).refs``]
    \\ fs [EVAL ``(bvl_to_bvi (bvi_to_bvl r) r).ffi``]
    \\ fs [EVAL ``(bvl_to_bvi (bvi_to_bvl r) r).global``]
    \\ fs
      [var_corr_def,get_var_def,lookup_insert,bvlSemTheory.Boolv_def,
           backend_commonTheory.bool_to_tag_def,
           backend_commonTheory.true_tag_def,
           backend_commonTheory.false_tag_def]
    \\ rveq \\ fs [] \\ rveq \\ fs []
    \\ unabbrev_all_tac
    \\ fs [lookup_inter_alt,map_insert,lookup_map,
      lookup_insert,data_to_bvi_v_def]
    \\ conj_tac >- ( fs[bvl_to_bvi_def] )
    \\ rpt strip_tac
    THEN1 (full_simp_tac(srw_ss())[LIST_REL_EL_EQN,var_corr_def,
      get_var_def,lookup_insert]
           \\ REPEAT STRIP_TAC
           \\ Q.MATCH_ASSUM_RENAME_TAC `l < LENGTH env`
           \\ IF_CASES_TAC \\ fs []
           \\ res_tac THEN1 (qpat_assum `EL l corr = n1` assume_tac \\
             fs [])
           \\ fs [domain_lookup,lookup_list_to_num_set]
           \\ METIS_TAC [MEM_EL])
    THEN1 (Cases_on `k = n1` \\ full_simp_tac(srw_ss())[] \\
      UNABBREV_ALL_TAC
           \\ full_simp_tac(srw_ss())[lookup_insert,lookup_inter_EQ,
             lookup_list_to_num_set] \\ RES_TAC \\ DECIDE_TAC)
    THEN1
     (`k <> n1` by (REPEAT STRIP_TAC \\ RES_TAC \\
       full_simp_tac(srw_ss())[] \\ NO_TAC)
      \\ full_simp_tac(srw_ss())[] \\ UNABBREV_ALL_TAC
      \\ full_simp_tac(srw_ss())[lookup_insert,lookup_inter_EQ,
        lookup_list_to_num_set]
      \\ CCONTR_TAC \\ full_simp_tac(srw_ss())[]
      \\ fs [lookup_list_to_num_set,domain_lookup])
    THEN1 (POP_ASSUM MP_TAC \\ Cases_on `jump_exc t1` \\
      full_simp_tac(srw_ss())[]
           \\ IMP_RES_TAC jump_exc_IMP
           \\ POP_ASSUM MP_TAC \\ POP_ASSUM MP_TAC
           \\ full_simp_tac(srw_ss())[jump_exc_def]))
    \\ Cases_on `op = IntOp GreaterEq` >-
   (fs [dataLangTheory.op_requires_names_def,
     dataLangTheory.op_space_reset_def]
    \\ fs [dataSemTheory.evaluate_def,cut_state_opt_def]
    \\ fs [cut_state_def,cut_env_def,domain_map]
    \\ fs[domain_list_insert2,domain_list_to_num_set2]
    \\ fs [dataLangTheory.op_requires_names_def]
    \\ imp_res_tac get_vars_reverse \\ fs []
    \\ qpat_x_assum `bviSem$do_app _ _ _ = _` mp_tac
    \\ simp [bviSemTheory.do_app_def,bviSemTheory.do_app_aux_def,
             bvlSemTheory.do_app_def,oneline
               bvlSemTheory.do_int_app_def]
    \\ disch_then (mp_tac o SRULE[AllCaseEqs(),PULL_EXISTS])
    \\ fs [SWAP_REVERSE_SYM,MAP_EQ_CONS]
    \\ strip_tac \\ rveq
    \\ simp[dataSemTheory.do_app_def, dataSemTheory.do_space_def,
            dataSemTheory.do_app_aux_def, dataSemTheory.do_stack_def,
            EVAL ``op_space_reset (IntOp Less)``, EVAL ``op_space_reset
              (IntOp LessEq)``]
    \\ simp[EVAL ``do_int_app Less [Number i'; Number i]``,
            EVAL ``do_int_app LessEq [Number i'; Number i]``]
    \\ simp[EVAL ``op_space_reset (IntOp Less)``, EVAL ``op_space_reset
      (IntOp LessEq)``]
    \\ fs
      [set_var_def,lookup_insert,integerTheory.int_gt
      ,integerTheory.int_ge]
    \\ fs [state_rel_def]
    \\ fs [EVAL ``(bvl_to_bvi (bvi_to_bvl r) r).refs``]
    \\ fs [EVAL ``(bvl_to_bvi (bvi_to_bvl r) r).ffi``]
    \\ fs [EVAL ``(bvl_to_bvi (bvi_to_bvl r) r).global``]
    \\ fs
      [var_corr_def,get_var_def,lookup_insert,bvlSemTheory.Boolv_def,
           backend_commonTheory.bool_to_tag_def,
           backend_commonTheory.true_tag_def,
           backend_commonTheory.false_tag_def]
    \\ rveq \\ fs [] \\ rveq \\ fs []
    \\ unabbrev_all_tac
    \\ fs [lookup_inter_alt,map_insert,lookup_map,
      lookup_insert,data_to_bvi_v_def]
    \\ conj_tac >- ( fs[bvl_to_bvi_def] )
    \\ rpt strip_tac
    THEN1 (full_simp_tac(srw_ss())[LIST_REL_EL_EQN,var_corr_def,
      get_var_def,lookup_insert]
           \\ REPEAT STRIP_TAC
           \\ Q.MATCH_ASSUM_RENAME_TAC `l < LENGTH env`
           \\ IF_CASES_TAC \\ fs []
           \\ res_tac THEN1 (qpat_assum `EL l corr = n1` assume_tac \\
             fs [])
           \\ fs [domain_lookup,lookup_list_to_num_set]
           \\ METIS_TAC [MEM_EL])
    THEN1 (Cases_on `k = n1` \\ full_simp_tac(srw_ss())[] \\
      UNABBREV_ALL_TAC
           \\ full_simp_tac(srw_ss())[lookup_insert,lookup_inter_EQ,
             lookup_list_to_num_set] \\ RES_TAC \\ DECIDE_TAC)
    THEN1
     (`k <> n1` by (REPEAT STRIP_TAC \\ RES_TAC \\
       full_simp_tac(srw_ss())[] \\ NO_TAC)
      \\ full_simp_tac(srw_ss())[] \\ UNABBREV_ALL_TAC
      \\ full_simp_tac(srw_ss())[lookup_insert,lookup_inter_EQ,
        lookup_list_to_num_set]
      \\ CCONTR_TAC \\ full_simp_tac(srw_ss())[]
      \\ fs [lookup_list_to_num_set,domain_lookup])
    THEN1 (POP_ASSUM MP_TAC \\ Cases_on `jump_exc t1` \\
      full_simp_tac(srw_ss())[]
           \\ IMP_RES_TAC jump_exc_IMP
           \\ POP_ASSUM MP_TAC \\ POP_ASSUM MP_TAC
           \\ full_simp_tac(srw_ss())[jump_exc_def]))
    \\ Cases_on `op = WordOp (WordTest W8 (Compare Gt))` >-
   (fs []
    \\ fs [dataLangTheory.op_requires_names_def,
      dataLangTheory.op_space_reset_def,
           data_spaceTheory.op_space_req_def]
    \\ fs [dataSemTheory.evaluate_def,cut_state_opt_def,
           dataLangTheory.op_requires_names_def,
             dataLangTheory.op_space_reset_def]
    \\ fs [cut_state_def,cut_env_def,domain_map,
      dataLangTheory.op_requires_names_def]
    \\ imp_res_tac get_vars_reverse \\ fs []
    \\ qpat_x_assum `bviSem$do_app _ _ _ = _` mp_tac
    \\ simp [bviSemTheory.do_app_def,bviSemTheory.do_app_aux_def,
             oneline
               bvlSemTheory.do_word_app_def,AllCaseEqs(),PULL_EXISTS,
             bvlSemTheory.do_app_def,oneline
               bvlSemTheory.do_int_app_def]
    \\ fs [SWAP_REVERSE_SYM,MAP_EQ_CONS]
    \\ rpt strip_tac \\ rveq
    \\ simp[dataSemTheory.do_app_def, dataSemTheory.do_space_def,
            dataSemTheory.do_app_aux_def, dataSemTheory.do_stack_def,
            EVAL ``op_space_reset (WordOp (WordTest W8 (Compare Lt)))``,
            EVAL ``op_space_reset (WordOp (WordTest W8 (Compare
              Leq)))``,
            EVAL ``op_space_req (WordOp (WordTest W8 (Compare Lt))) 2``,
            EVAL ``op_space_req (WordOp (WordTest W8 (Compare Leq)))
              2``]
    \\ simp[EVAL ``do_word_app (WordTest W8 (Compare Lt)) [Number i';
      Number i]``,
            EVAL ``do_word_app (WordTest W8 (Compare Leq)) [Number i';
              Number i]``]
    \\ fs
      [set_var_def,lookup_insert,integerTheory.int_gt
      ,integerTheory.int_ge]
    \\ fs [state_rel_def]
    \\ fs [EVAL ``(bvl_to_bvi (bvi_to_bvl r) r).refs``]
    \\ fs [EVAL ``(bvl_to_bvi (bvi_to_bvl r) r).ffi``]
    \\ fs [EVAL ``(bvl_to_bvi (bvi_to_bvl r) r).global``]
    \\ fs
      [var_corr_def,get_var_def,lookup_insert,bvlSemTheory.Boolv_def,
           backend_commonTheory.bool_to_tag_def,
           backend_commonTheory.true_tag_def,
           backend_commonTheory.false_tag_def]
    \\ rveq \\ fs [] \\ rveq \\ fs []
    \\ unabbrev_all_tac
    \\ fs [ lookup_inter_alt,map_insert,lookup_map,
      lookup_insert,data_to_bvi_v_def]
    \\ conj_tac >- ( fs[bvl_to_bvi_def] )
    \\ rpt strip_tac
    THEN1 (full_simp_tac(srw_ss())[LIST_REL_EL_EQN,var_corr_def,
      get_var_def,lookup_insert]
           \\ REPEAT STRIP_TAC
           \\ Q.MATCH_ASSUM_RENAME_TAC `l < LENGTH env`
           \\ IF_CASES_TAC \\ fs []
           \\ res_tac THEN1 (qpat_assum `EL l corr = n1` assume_tac \\
             fs [])
           \\ fs [domain_lookup,lookup_list_to_num_set]
           \\ METIS_TAC [MEM_EL])
    THEN1 (Cases_on `k = n1` \\ full_simp_tac(srw_ss())[] \\
      UNABBREV_ALL_TAC
           \\ full_simp_tac(srw_ss())[lookup_insert,lookup_inter_EQ,
             lookup_list_to_num_set] \\ RES_TAC \\ DECIDE_TAC)
    THEN1
     (`k <> n1` by (REPEAT STRIP_TAC \\ RES_TAC \\
       full_simp_tac(srw_ss())[] \\ NO_TAC)
      \\ full_simp_tac(srw_ss())[] \\ UNABBREV_ALL_TAC
      \\ full_simp_tac(srw_ss())[lookup_insert,lookup_inter_EQ,
        lookup_list_to_num_set]
      \\ CCONTR_TAC \\ full_simp_tac(srw_ss())[]
      \\ fs [lookup_list_to_num_set,domain_lookup])
    THEN1 (POP_ASSUM MP_TAC \\ Cases_on `jump_exc t1` \\
      full_simp_tac(srw_ss())[]
           \\ IMP_RES_TAC jump_exc_IMP
           \\ POP_ASSUM MP_TAC \\ POP_ASSUM MP_TAC
           \\ full_simp_tac(srw_ss())[jump_exc_def]))
    \\ Cases_on `op = WordOp (WordTest W8 (Compare Geq))` >-
   (fs []
    \\ fs [dataLangTheory.op_requires_names_def,
      dataLangTheory.op_space_reset_def,
           data_spaceTheory.op_space_req_def]
    \\ fs [dataSemTheory.evaluate_def,cut_state_opt_def,
           dataLangTheory.op_requires_names_def,
             dataLangTheory.op_space_reset_def]
    \\ fs [cut_state_def,cut_env_def,domain_map,
      dataLangTheory.op_requires_names_def]
    \\ imp_res_tac get_vars_reverse \\ fs []
    \\ qpat_x_assum `bviSem$do_app _ _ _ = _` mp_tac
    \\ simp [bviSemTheory.do_app_def,bviSemTheory.do_app_aux_def,
             oneline
               bvlSemTheory.do_word_app_def,AllCaseEqs(),PULL_EXISTS,
             bvlSemTheory.do_app_def,oneline
               bvlSemTheory.do_int_app_def]
    \\ fs [SWAP_REVERSE_SYM,MAP_EQ_CONS]
    \\ rpt strip_tac \\ rveq
    \\ simp[dataSemTheory.do_app_def, dataSemTheory.do_space_def,
            dataSemTheory.do_app_aux_def, dataSemTheory.do_stack_def,
            EVAL ``op_space_reset (WordOp (WordTest W8 (Compare Lt)))``,
            EVAL ``op_space_reset (WordOp (WordTest W8 (Compare
              Leq)))``,
            EVAL ``op_space_req (WordOp (WordTest W8 (Compare Lt))) 2``,
            EVAL ``op_space_req (WordOp (WordTest W8 (Compare Leq)))
              2``]
    \\ simp[EVAL ``do_word_app (WordTest W8 (Compare Lt)) [Number i';
      Number i]``,
            EVAL ``do_word_app (WordTest W8 (Compare Leq)) [Number i';
              Number i]``]
    \\ fs
      [set_var_def,lookup_insert,integerTheory.int_gt
      ,integerTheory.int_ge]
    \\ fs [state_rel_def]
    \\ fs [EVAL ``(bvl_to_bvi (bvi_to_bvl r) r).refs``]
    \\ fs [EVAL ``(bvl_to_bvi (bvi_to_bvl r) r).ffi``]
    \\ fs [EVAL ``(bvl_to_bvi (bvi_to_bvl r) r).global``]
    \\ fs
      [var_corr_def,get_var_def,lookup_insert,bvlSemTheory.Boolv_def,
           backend_commonTheory.bool_to_tag_def,
           backend_commonTheory.true_tag_def,
           backend_commonTheory.false_tag_def]
    \\ rveq \\ fs [] \\ rveq \\ fs []
    \\ unabbrev_all_tac
    \\ fs [ lookup_inter_alt,map_insert,lookup_map,
      lookup_insert,data_to_bvi_v_def]
    \\ conj_tac >- ( fs[bvl_to_bvi_def] )
    \\ rpt strip_tac
    THEN1 (full_simp_tac(srw_ss())[LIST_REL_EL_EQN,var_corr_def,
      get_var_def,lookup_insert]
           \\ REPEAT STRIP_TAC
           \\ Q.MATCH_ASSUM_RENAME_TAC `l < LENGTH env`
           \\ IF_CASES_TAC \\ fs []
           \\ res_tac THEN1 (qpat_assum `EL l corr = n1` assume_tac \\
             fs [])
           \\ fs [domain_lookup,lookup_list_to_num_set]
           \\ METIS_TAC [MEM_EL])
    THEN1 (Cases_on `k = n1` \\ full_simp_tac(srw_ss())[] \\
      UNABBREV_ALL_TAC
           \\ full_simp_tac(srw_ss())[lookup_insert,lookup_inter_EQ,
             lookup_list_to_num_set] \\ RES_TAC \\ DECIDE_TAC)
    THEN1
     (`k <> n1` by (REPEAT STRIP_TAC \\ RES_TAC \\
       full_simp_tac(srw_ss())[] \\ NO_TAC)
      \\ full_simp_tac(srw_ss())[] \\ UNABBREV_ALL_TAC
      \\ full_simp_tac(srw_ss())[lookup_insert,lookup_inter_EQ,
        lookup_list_to_num_set]
      \\ CCONTR_TAC \\ full_simp_tac(srw_ss())[]
      \\ fs [lookup_list_to_num_set,domain_lookup])
    THEN1 (POP_ASSUM MP_TAC \\ Cases_on `jump_exc t1` \\
      full_simp_tac(srw_ss())[]
           \\ IMP_RES_TAC jump_exc_IMP
           \\ POP_ASSUM MP_TAC \\ POP_ASSUM MP_TAC
           \\ full_simp_tac(srw_ss())[jump_exc_def]))
    \\ Cases_on`op = MemOp XorByte` >-
  (
      fs[dataLangTheory.op_requires_names_def]
      \\ qhdtm_x_assum`bviSem$do_app`mp_tac
      \\ simp[bviSemTheory.do_app_def,bviSemTheory.do_app_aux_def
        ,closSemTheory.case_eq_thms]
      \\ strip_tac \\ rveq \\ fs[pair_case_eq,domain_map] \\ rw[]
      \\ simp[dataSemTheory.evaluate_def,cut_state_opt_def,cut_state_def
        ,cut_env_def]
      \\ fs[dataSemTheory.do_app_def,do_space_def
        ,dataLangTheory.op_space_reset_def,
            data_spaceTheory.op_space_req_def
              ,dataSemTheory.do_app_aux_def]
      \\ fs[dataLangTheory.op_requires_names_def]
      \\ fs[state_rel_def,code_rel_def]
      \\ fs [ bvlSemTheory.do_app_def
              , bvlSemTheory.case_eq_thms
              , case_eq_thms
              , pair_case_eq,SWAP_REVERSE_SYM,lookup_map]
      \\ ntac 5 (rfs [MAP_EQ_CONS])
      \\ fs [v_to_words_eq,v_to_bytes_eq,data_to_bvi_v_eq]
      \\ `get_vars (REVERSE vs) t2.locals = SOME (REVERSE z')` by
           (qpat_x_assum `get_vars (REVERSE vs) env1 = _` mp_tac
            \\ simp[Abbr`env1`] \\ strip_tac \\ imp_res_tac
              get_vars_inter \\ fs[])
      \\ fs[]
      \\ fs [v_to_words_eq,v_to_bytes_eq,data_to_bvi_v_eq]
      \\ IMP_RES_TAC data_to_bvi_v_eq \\ rveq
      \\ fs [lookup_map,case_eq_thms]
      \\ IMP_RES_TAC data_to_bvi_eq_ByteArray \\ rveq
      \\ fs [ set_var_def,bvl_to_bvi_id,lookup_insert
              , lookup_map,map_insert]
      \\ fs[bvi_to_bvl_def,bvl_to_bvi_def
            ,bviSemTheory.state_component_equality
            , data_to_bvi_ref_def]
      \\ conj_tac >- rw [FLOOKUP_UPDATE, data_to_bvi_ref_def]
      \\ conj_tac >- ( rw[Abbr`env1`,lookup_inter_EQ] )
      \\ fs [ var_corr_def,data_to_bvi_v_Unit,get_var_def,lookup_insert
              , lookup_map,bvlPropsTheory.case_eq_thms
              , LENGTH_MAP,LIST_REL_LENGTH,lookup_map]
      \\ fs[] \\ rveq
      \\ fs[] \\ rveq
      \\ conj_tac >- (
        fs[LIST_REL_EL_EQN]
        \\ rw[Abbr`env1`,lookup_inter_EQ,lookup_list_to_num_set]
        \\ METIS_TAC[MEM_EL,prim_recTheory.LESS_REFL] )
      \\ conj_tac >- (
        rw[Abbr`env1`,lookup_inter_EQ,lookup_list_to_num_set]
        \\ res_tac \\ fs[] )
      \\ conj_tac >- (
        fs[Abbr`env1`,lookup_inter_EQ,lookup_list_to_num_set]
        \\ METIS_TAC[prim_recTheory.LESS_REFL] )
      \\ rw[] \\ res_tac
      \\ fs[jump_exc_def,dataSemTheory.do_stack_def]
      \\ TOP_CASE_TAC \\ fs[]
      \\ TOP_CASE_TAC \\ fs[])
    \\ Cases_on`∃b cmp. op = MemOp (StringCmp b cmp)` >-
  (
      fs[dataLangTheory.op_requires_names_def]
      \\ qhdtm_x_assum`bviSem$do_app`mp_tac
      \\ simp[bviSemTheory.do_app_def,bviSemTheory.do_app_aux_def
        ,closSemTheory.case_eq_thms]
      \\ strip_tac \\ rveq \\ fs[pair_case_eq,domain_map] \\ rw[]
      \\ simp[dataSemTheory.evaluate_def,cut_state_opt_def,cut_state_def
        ,cut_env_def]
      \\ fs[dataSemTheory.do_app_def,do_space_def
        ,dataLangTheory.op_space_reset_def,
            data_spaceTheory.op_space_req_def
              ,dataSemTheory.do_app_aux_def]
      \\ fs[dataLangTheory.op_requires_names_def]
      \\ fs[state_rel_def,code_rel_def]
      \\ fs [ bvlSemTheory.do_app_def
              , bvlSemTheory.case_eq_thms
              , case_eq_thms
              , pair_case_eq,SWAP_REVERSE_SYM,lookup_map]
      \\ ntac 5 (rfs [MAP_EQ_CONS])
      \\ fs [v_to_words_eq,v_to_bytes_eq,data_to_bvi_v_eq]
      \\ `get_vars (REVERSE vs) t2.locals = SOME (REVERSE z')` by
           (qpat_x_assum `get_vars (REVERSE vs) env1 = _` mp_tac
            \\ simp[Abbr`env1`] \\ strip_tac \\ imp_res_tac
              get_vars_inter \\ fs[])
      \\ fs[]
      \\ fs [v_to_words_eq,v_to_bytes_eq,data_to_bvi_v_eq]
      \\ IMP_RES_TAC data_to_bvi_v_eq \\ rveq
      \\ fs [lookup_map,case_eq_thms]
      \\ IMP_RES_TAC data_to_bvi_eq_ByteArray \\ rveq
      \\ fs [ set_var_def,bvl_to_bvi_id,lookup_insert
              , lookup_map,map_insert]
      \\ fs[bvi_to_bvl_def,bvl_to_bvi_def
            ,bviSemTheory.state_component_equality
            , data_to_bvi_ref_def]
      \\ conj_tac >- ( rw[Abbr`env1`,lookup_inter_EQ] )
      \\ fs [ var_corr_def,get_var_def,lookup_insert,
        lookup_map,data_to_bvi_v_def,
              bvlSemTheory.Boolv_def,bvlPropsTheory.case_eq_thms,
              LENGTH_MAP,LIST_REL_LENGTH]
      \\ fs[] \\ rveq
      \\ fs[] \\ rveq
      \\ conj_tac >- (
        fs[LIST_REL_EL_EQN]
        \\ rw[Abbr`env1`,lookup_inter_EQ,lookup_list_to_num_set]
        \\ METIS_TAC[MEM_EL,prim_recTheory.LESS_REFL] )
      \\ conj_tac >- (
        rw[Abbr`env1`,lookup_inter_EQ,lookup_list_to_num_set]
        \\ res_tac \\ fs[] )
      \\ conj_tac >- (
        fs[Abbr`env1`,lookup_inter_EQ,lookup_list_to_num_set]
        \\ METIS_TAC[prim_recTheory.LESS_REFL] )
      \\ rw[] \\ res_tac
      \\ fs[jump_exc_def,dataSemTheory.do_stack_def]
      \\ TOP_CASE_TAC \\ fs[]
      \\ TOP_CASE_TAC \\ fs[])
    \\ Cases_on`∃b. op = MemOp (CopyByte b)` >-
  (
      fs[dataLangTheory.op_requires_names_def]
      \\ qhdtm_x_assum`bviSem$do_app`mp_tac
      \\ simp[bviSemTheory.do_app_def,bviSemTheory.do_app_aux_def
        ,closSemTheory.case_eq_thms]
      \\ strip_tac \\ rveq \\ fs[pair_case_eq,domain_map] \\ rw[]
      \\ simp[dataSemTheory.evaluate_def,cut_state_opt_def,cut_state_def
        ,cut_env_def]
      \\ fs[dataSemTheory.do_app_def,do_space_def
        ,dataLangTheory.op_space_reset_def,
            data_spaceTheory.op_space_req_def
              ,dataSemTheory.do_app_aux_def]
      \\ fs[dataLangTheory.op_requires_names_def]
      \\ fs[state_rel_def,code_rel_def]
      \\ fs [ bvlSemTheory.do_app_def
              , bvlSemTheory.case_eq_thms
              , case_eq_thms
              , pair_case_eq,SWAP_REVERSE_SYM,lookup_map]
      \\ ntac 5 (rfs [MAP_EQ_CONS])
      \\ fs [v_to_words_eq,v_to_bytes_eq,data_to_bvi_v_eq]
      \\ `get_vars (REVERSE vs) t2.locals = SOME (REVERSE z')` by
           (qpat_x_assum `get_vars (REVERSE vs) env1 = _` mp_tac
            \\ simp[Abbr`env1`] \\ strip_tac \\ imp_res_tac
              get_vars_inter \\ fs[])
      \\ fs[]
      \\ fs [v_to_words_eq,v_to_bytes_eq,data_to_bvi_v_eq]
      \\ IMP_RES_TAC data_to_bvi_v_eq \\ rveq
      \\ fs [lookup_map,case_eq_thms]
      \\ IMP_RES_TAC data_to_bvi_eq_ByteArray \\ rveq
      \\ fs [ set_var_def,bvl_to_bvi_id,lookup_insert
              , lookup_map,map_insert]
      \\ fs[bvi_to_bvl_def,bvl_to_bvi_def
            ,bviSemTheory.state_component_equality
            , data_to_bvi_ref_def]
      \\ conj_tac >- rw [FLOOKUP_UPDATE, data_to_bvi_ref_def]
      \\ conj_tac >- ( rw[Abbr`env1`,lookup_inter_EQ] )
      \\ fs [ var_corr_def,data_to_bvi_v_Unit,get_var_def,lookup_insert
              , lookup_map,bvlPropsTheory.case_eq_thms
              , LENGTH_MAP,LIST_REL_LENGTH,lookup_map]
      \\ fs[] \\ rveq
      \\ fs[] \\ rveq
      \\ conj_tac >- (
        fs[LIST_REL_EL_EQN]
        \\ rw[Abbr`env1`,lookup_inter_EQ,lookup_list_to_num_set]
        \\ METIS_TAC[MEM_EL,prim_recTheory.LESS_REFL] )
      \\ conj_tac >- (
        rw[Abbr`env1`,lookup_inter_EQ,lookup_list_to_num_set]
        \\ res_tac \\ fs[] )
      \\ conj_tac >- (
        fs[Abbr`env1`,lookup_inter_EQ,lookup_list_to_num_set]
        \\ METIS_TAC[prim_recTheory.LESS_REFL] )
      \\ rw[] \\ res_tac
      \\ fs[jump_exc_def,dataSemTheory.do_stack_def]
      \\ TOP_CASE_TAC \\ fs[]
      \\ TOP_CASE_TAC \\ fs[])
    \\ Cases_on `op = ThunkOp ForceThunk` \\ gvs [] >-
  (gvs [bviSemTheory.do_app_def, bvlSemTheory.do_app_def,
           bviSemTheory.do_app_aux_def, AllCaseEqs()])
    \\
     (fs []
    \\ fs[bviSemTheory.state_component_equality] \\ rveq
    \\ Cases_on `op_requires_names op`
    \\ full_simp_tac(srw_ss())[evaluate_def,cut_state_opt_def,
                               cut_state_def,cut_env_def,domain_map]
    \\ full_simp_tac(srw_ss())[dataSemTheory.do_app_def,do_space_def
      ,LET_THM]
    \\ simp[]
    \\ full_simp_tac(srw_ss())[get_var_def,set_var_def]
    \\ full_simp_tac(srw_ss())[call_env_def,flush_state_def]
    \\ full_simp_tac(srw_ss())[state_rel_def]
    \\ IMP_RES_TAC do_app_code \\ full_simp_tac(srw_ss())[]
    \\ IMP_RES_TAC do_app_oracle \\ full_simp_tac(srw_ss())[]
    \\ IMP_RES_TAC compile_LESS_EQ \\
      full_simp_tac(srw_ss())[lookup_insert]
    THEN1
     (`get_vars (REVERSE vs) t2.locals = SOME (REVERSE z')` by
         (qpat_x_assum `get_vars (REVERSE vs) env1 = _` mp_tac
          \\ simp[Abbr`env1`] \\ strip_tac \\ imp_res_tac get_vars_inter
            \\ fs[])
      \\ `op_space_reset op` by
         (rfs [dataLangTheory.op_space_reset_def
               ,dataLangTheory.op_requires_names_def] \\ gvs [])
      \\ fs [do_stack_def,state_fupdcanon]
      \\ qmatch_goalsub_abbrev_tac `do_app_aux op (REVERSE z') st0`
      \\ `state_rel r st0` by (unabbrev_all_tac \\ fs[state_rel_def])
      \\ first_assum (mp_then Any mp_tac data_to_bvi_do_app)
      \\ rpt (disch_then (first_assum o mp_then Any mp_tac))
      \\ rw []
      \\ fs[]
      \\ rfs [dataLangTheory.op_space_reset_def
              ,code_rel_def, do_stack_def
              ,state_rel_def]
      \\ IMP_RES_TAC do_app_aux_const \\ fs [lookup_insert]
      \\ fs[Abbr`st0`]
      \\ REPEAT STRIP_TAC
      THEN1 (
             UNABBREV_ALL_TAC \\
               full_simp_tac(srw_ss())[lookup_inter_EQ,lookup_insert]
             \\ `n1 <= k` by DECIDE_TAC \\ `k <> n1` by DECIDE_TAC \\
             full_simp_tac(srw_ss())[])
      THEN1 (full_simp_tac(srw_ss())[LIST_REL_EL_EQN,var_corr_def,
                                     get_var_def,lookup_insert]
             \\ REPEAT STRIP_TAC
             \\ Q.MATCH_ASSUM_RENAME_TAC `l < LENGTH z''`
             \\ `n1 <= n1 /\ l < LENGTH corr` by DECIDE_TAC
             \\ `lookup n1 t2.locals = NONE` by METIS_TAC []
             \\ `EL l corr <> n1`
               by (RES_TAC \\ CCONTR_TAC \\ fs [lookup_map] \\ fs [])
             \\ RES_TAC \\ CCONTR_TAC \\ full_simp_tac(srw_ss())[]
             \\ UNABBREV_ALL_TAC \\ fs [lookup_map,lookup_insert]
             \\ pop_assum (ASSUME_TAC o Q.SPEC `z`)
             \\ rfs[lookup_inter_EQ,lookup_list_to_num_set]
             \\ full_simp_tac(srw_ss())[] \\ METIS_TAC [MEM_EL])
      THEN1 (
            pop_assum mp_tac \\
            Cases_on `k = n1` \\ full_simp_tac(srw_ss())[] \\
              UNABBREV_ALL_TAC
             \\ rfs[lookup_insert,lookup_inter_EQ,
                    lookup_list_to_num_set]
             \\ simp[SF CONJ_ss]
             \\ DISCH_THEN (CONJUNCTS_THEN ASSUME_TAC)
             \\ RES_TAC \\ DECIDE_TAC)
      THEN1
       (`k <> n1` by (REPEAT STRIP_TAC \\ RES_TAC
                      \\ full_simp_tac(srw_ss())[] \\ NO_TAC)
        \\ full_simp_tac(srw_ss())[] \\ UNABBREV_ALL_TAC
        \\ full_simp_tac(srw_ss())[lookup_insert,lookup_inter_EQ,
                                   lookup_list_to_num_set]
        \\ CCONTR_TAC \\ full_simp_tac(srw_ss())[])
      THEN1 (POP_ASSUM MP_TAC \\ Cases_on `jump_exc t1` \\
        full_simp_tac(srw_ss())[]
             \\ IMP_RES_TAC jump_exc_IMP
             \\ POP_ASSUM MP_TAC \\ POP_ASSUM MP_TAC
             \\ full_simp_tac(srw_ss())[jump_exc_def])
      \\ full_simp_tac(srw_ss())[var_corr_def,get_var_def,lookup_map])
        \\ rveq
    \\ imp_res_tac get_vars_reverse
    \\ imp_res_tac get_vars_IMP_LENGTH \\ full_simp_tac (srw_ss()) []
    \\ Cases_on `op_space_req op (LENGTH vs) = 0`
    \\ full_simp_tac(srw_ss())[evaluate_def
      ,dataLangTheory.op_requires_names_def]
    \\ full_simp_tac(srw_ss())[evaluate_def,cut_state_opt_def,
                               cut_state_def,cut_env_def]
    \\ full_simp_tac(srw_ss())[dataSemTheory.do_app_def,do_space_def
      ,LET_DEF]
    \\ full_simp_tac(srw_ss())[get_var_def,set_var_def]
    \\ full_simp_tac(srw_ss())[call_env_def,flush_state_def]
    \\ full_simp_tac(srw_ss())[state_rel_def] \\ IMP_RES_TAC do_app_code
    \\ full_simp_tac(srw_ss())[]
    \\ IMP_RES_TAC compile_LESS_EQ \\
      full_simp_tac(srw_ss())[lookup_insert]
    THEN1
     (`state_rel r t2` by fs[state_rel_def]
      \\ first_assum (mp_then Any mp_tac data_to_bvi_do_app)
      \\ rpt (disch_then (first_assum o mp_then Any mp_tac))
      \\ rw []
      \\ rfs [dataLangTheory.op_space_reset_def
              ,code_rel_def, do_stack_def
              ,state_rel_def]
      \\ qmatch_goalsub_abbrev_tac `state_stack_max_fupd (K SMX0)
                                   (state_safe_for_space_fupd (K SAFE0)
                                     _)`
      \\ drule_then (qspecl_then [`SMX0`,`SAFE0`,`t2.peak_heap_length`]
        assume_tac)
                    do_app_aux_sm_safe_peak_swap
      \\ IMP_RES_TAC do_app_aux_const \\ fs [lookup_insert]
      \\ REPEAT STRIP_TAC
      THEN1 (full_simp_tac(srw_ss())[LIST_REL_EL_EQN,
                                     var_corr_def,get_var_def
                                       ,lookup_insert]
             \\ REPEAT STRIP_TAC
             \\ rename1 `l1 < LENGTH corr`
             \\ FULL_SIMP_TAC std_ss []
             \\ `n1 <= n1 /\ l1 < LENGTH corr` by DECIDE_TAC
             \\ `lookup n1 t2.locals = NONE` by METIS_TAC []
             \\ `EL l1 corr <> n1`
               by (RES_TAC \\ CCONTR_TAC \\ fs [lookup_map] \\ fs [])
             \\ RES_TAC \\ CCONTR_TAC \\ full_simp_tac(srw_ss())[]
             \\ UNABBREV_ALL_TAC \\ fs [lookup_map,lookup_insert]
             \\ pop_assum (ASSUME_TAC o Q.SPEC `z`)
             \\ rfs[lookup_inter_EQ,lookup_list_to_num_set]
             \\ full_simp_tac(srw_ss())[] \\ METIS_TAC [MEM_EL])
      THEN1 (Cases_on `k = n1` \\ full_simp_tac(srw_ss())[] \\
        UNABBREV_ALL_TAC
             \\ full_simp_tac(srw_ss())[lookup_insert,lookup_inter_EQ,
                                        lookup_list_to_num_set]
             \\ RES_TAC \\ DECIDE_TAC)
      THEN1
       (`k <> n1` by (REPEAT STRIP_TAC \\ RES_TAC
                      \\ full_simp_tac(srw_ss())[] \\ NO_TAC)
        \\ full_simp_tac(srw_ss())[] \\ UNABBREV_ALL_TAC
        \\ full_simp_tac(srw_ss())[lookup_insert,
                                   lookup_inter_EQ
                                     ,lookup_list_to_num_set]
        \\ CCONTR_TAC \\ full_simp_tac(srw_ss())[])
      THEN1 (POP_ASSUM MP_TAC \\ Cases_on `jump_exc t1` \\
        full_simp_tac(srw_ss())[]
             \\ IMP_RES_TAC jump_exc_IMP
             \\ POP_ASSUM MP_TAC \\ POP_ASSUM MP_TAC
             \\ full_simp_tac(srw_ss())[jump_exc_def])
      \\ full_simp_tac(srw_ss())[var_corr_def,get_var_def,lookup_map])
    \\ `(add_space (t2 with locals := env1)
         (op_space_req op (LENGTH vs))).locals = env1` by (EVAL_TAC \\
           fs [])
    \\ fs [] \\ pop_assum kall_tac
    \\ qspecl_then [`t2`,`op_space_req op (LENGTH vs)`,`env1`]
                   (CHOOSE_THEN (CHOOSE_THEN (fn t => fs
                     [t,lookup_map])))
                   (GEN_ALL consume_space_add_space)
    \\ `state_rel r (t2 with <|locals := env1; space := 0;
                               safe_for_space := sf;
                               peak_heap_length := hp |>)`
      by fs[state_rel_def,lookup_map]
    \\ first_assum (mp_then Any mp_tac data_to_bvi_do_app)
    \\ rpt (disch_then (first_assum o mp_then Any mp_tac))
    \\ rw []
    \\ rfs [dataLangTheory.op_space_reset_def
            ,code_rel_def, do_stack_def
            ,state_rel_def]
    \\ qmatch_goalsub_abbrev_tac `state_stack_max_fupd (K SMX0)
                                 (_ (state_safe_for_space_fupd (K SAFE0)
                                   _))`
    \\ drule_then (qspecl_then [`SMX0`,`SAFE0`,`hp`] assume_tac)
                  do_app_aux_sm_safe_peak_swap
    \\ fs [state_fupdcanon]
    \\ IMP_RES_TAC do_app_aux_const \\ fs [lookup_insert,lookup_map]
    \\ REPEAT STRIP_TAC
    THEN1 (UNABBREV_ALL_TAC \\ full_simp_tac(srw_ss())[lookup_inter_EQ]
           \\ `n1 <= k` by DECIDE_TAC \\ full_simp_tac(srw_ss())[])
    THEN1 (full_simp_tac(srw_ss())[LIST_REL_EL_EQN,
                                   var_corr_def,get_var_def
                                     ,lookup_insert]
           \\ REPEAT STRIP_TAC
           \\ rename1 `l1 < LENGTH corr`
           \\ FULL_SIMP_TAC std_ss []
           \\ `n1 <= n1 /\ l1 < LENGTH corr` by DECIDE_TAC
           \\ `lookup n1 t2.locals = NONE` by METIS_TAC []
           \\ `EL l1 corr <> n1`
             by (RES_TAC \\ CCONTR_TAC \\ fs [lookup_map] \\ fs [])
           \\ RES_TAC \\ CCONTR_TAC \\ full_simp_tac(srw_ss())[]
           \\ UNABBREV_ALL_TAC \\ fs [lookup_map,lookup_insert]
           \\ pop_assum (ASSUME_TAC o Q.SPEC `z`)
           \\ rfs[lookup_inter_EQ,lookup_list_to_num_set]
           \\ full_simp_tac(srw_ss())[] \\ METIS_TAC [MEM_EL])
    THEN1 (Cases_on `k = n1` \\ full_simp_tac(srw_ss())[] \\
      UNABBREV_ALL_TAC
           \\ full_simp_tac(srw_ss())[lookup_insert,lookup_inter_EQ
             ,lookup_list_to_num_set]
           \\ RES_TAC \\ DECIDE_TAC)
    THEN1
     (`k <> n1` by (REPEAT STRIP_TAC \\ RES_TAC \\
       full_simp_tac(srw_ss())[] \\ NO_TAC)
      \\ full_simp_tac(srw_ss())[] \\ UNABBREV_ALL_TAC
      \\ full_simp_tac(srw_ss())[lookup_insert,lookup_inter_EQ
        ,lookup_list_to_num_set]
      \\ CCONTR_TAC \\ full_simp_tac(srw_ss())[])
    THEN1 (POP_ASSUM MP_TAC \\ Cases_on `jump_exc t1` \\
      full_simp_tac(srw_ss())[]
           \\ IMP_RES_TAC jump_exc_IMP
           \\ POP_ASSUM MP_TAC \\ POP_ASSUM MP_TAC
           \\ full_simp_tac(srw_ss())[jump_exc_def])
    \\ full_simp_tac(srw_ss())[var_corr_def,get_var_def,lookup_map])))
QED
*)

(* HOL4 ML code, not ported:
Resume compile_correct[Tick]:
   (note_tac "Tick"
    \\ `?c1 v1 n1. compile n corr tail live [x] = (c1,v1,n1)` by
      METIS_TAC [PAIR]
    \\ FULL_SIMP_TAC std_ss [LET_DEF,evaluate_def]
    \\ Cases_on `t1.clock = 0` \\ FULL_SIMP_TAC std_ss []
    THEN1
      (full_simp_tac(srw_ss())[state_rel_def,call_env_def
      ,flush_state_def,data_to_bvi_result_def])
    \\ `s.clock <> 0` by (FULL_SIMP_TAC std_ss [state_rel_def])
    \\ FULL_SIMP_TAC std_ss []
    \\ Q.PAT_X_ASSUM `(res,s2) = bb` (ASSUME_TAC o GSYM)
    \\ FULL_SIMP_TAC std_ss [LENGTH]
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`dec_clock
      t1`,`n`,`corr`,`tail`,`live`])
    \\ FULL_SIMP_TAC std_ss []
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
    \\ FULL_SIMP_TAC (srw_ss())
      [var_corr_def,dataSemTheory.dec_clock_def,
                                 get_var_def,state_rel_def
                                   ,bviSemTheory.dec_clock_def,
                                 jump_exc_NONE])
QED
*)

(* HOL4 ML code, not ported:
Resume compile_correct[Force]:
    gvs [evaluate_def, AllCaseEqs(), PULL_EXISTS]
    >- (
      gvs [any_el_ALT, var_corr_def, LIST_REL_EL_EQN]
      \\ last_assum $ drule_then assume_tac \\ fs []
      \\ fs [get_var_def, lookup_map] \\ gvs []
      \\ drule_all_then assume_tac state_rel_dest_thunk \\ gvs []
      \\ Cases_on `tail` \\ gvs []
      >- gvs [state_rel_def, flush_state_def]
      \\ gvs [cut_env_def]
      \\ `domain (list_to_num_set (live ++ corr)) ⊆ domain t1.locals` by
        (
        gvs [SUBSET_DEF, domain_lookup, lookup_list_to_num_set]
        \\ rw []
        >- (
          gvs [EVERY_EL, MEM_EL]
          \\ first_x_assum drule \\ rw []
          \\ Cases_on `lookup (EL n'' live) t1.locals` \\ gvs [])
        >- (
          gvs [MEM_EL]
          \\ first_x_assum drule \\ rw []
          \\ simp [SF SFY_ss]))
      \\ gvs [set_var_def, state_rel_def, lookup_insert,
        lookup_inter_alt,
              domain_list_to_num_set, lookup_map] \\ rw []
      >- (last_x_assum drule \\ rw [])
      >- gvs [MEM_EL]
      >- (
        gvs [SUBSET_DEF, domain_list_to_num_set]
        \\ rpt (first_x_assum $ qspec_then `k` assume_tac \\ gvs []))
      >- (
        gvs [SUBSET_DEF, domain_list_to_num_set]
        \\ rpt (first_x_assum $ qspec_then `k` assume_tac \\ gvs []))
      >- gvs [MEM_EL]
      >- gvs [MEM_EL]
      >- gvs [jump_exc_def])
    >- (
      gvs [any_el_ALT, var_corr_def, LIST_REL_EL_EQN]
      \\ last_assum $ drule_then assume_tac \\ fs []
      \\ fs [get_var_def, lookup_map] \\ gvs []
      \\ drule_all_then assume_tac state_rel_dest_thunk \\ gvs []
      \\ `t1.clock = s.clock` by gvs [state_rel_def] \\ gvs []
      \\ gvs [find_code_def, dataSemTheory.find_code_def, AllCaseEqs()]
      \\ `lookup force_loc t1.code = SOME (2,compile_exp 2 exp)`
        by gvs [state_rel_def, code_rel_def] \\ gvs []
      \\ Cases_on `tail` \\ gvs []
      >- gvs [state_rel_def]
      \\ gvs [cut_env_def]
      \\ `domain (list_to_num_set (live ++ corr)) ⊆ domain t1.locals` by
        (
        gvs [SUBSET_DEF, domain_lookup, lookup_list_to_num_set]
        \\ rw []
        >- (
          gvs [EVERY_EL, MEM_EL]
          \\ first_x_assum drule \\ rw []
          \\ Cases_on `lookup (EL n'' live) t1.locals` \\ gvs [])
        >- (
          gvs [MEM_EL, state_rel_def]
          \\ first_x_assum drule \\ rw []
          \\ simp [SF SFY_ss]))
      \\ gvs [state_rel_def, call_env_def, push_env_def, dec_clock_def])
    \\ gvs [any_el_ALT, var_corr_def, LIST_REL_EL_EQN]
    \\ first_assum $ drule_then assume_tac \\ fs []
    \\ fs [get_var_def, lookup_map] \\ gvs []
    \\ drule_all_then assume_tac state_rel_dest_thunk \\ gvs []
    \\ `find_code (SOME force_loc) (MAP data_to_bvi_v [z;v']) s.code =
          SOME (args,exp)` by gvs []
    \\ drule_all find_code_lemma \\ rw [] \\ gvs []
    \\ `t1.clock = s.clock` by gvs [state_rel_def] \\ gvs []
    \\ Cases_on `tail` \\ gvs [PULL_EXISTS]
    >- (gvs [compile_exp_def]
    \\ last_x_assum
      $ qspecl_then [`call_env args' ss (dec_clock t1)`, `LENGTH args'`,
                     `COUNT_LIST (LENGTH args')`, `T`, `[]`] mp_tac
    \\ gvs [] \\ impl_tac
    >- (rw []
        \\ gvs [COUNT_LIST_GENLIST, EL_MAP, dec_clock_def, call_env_def,
                lookup_fromList, bviSemTheory.dec_clock_def,
                  state_rel_def])
    \\ rw [] \\ gvs []
    \\ Cases_on `pres` \\ gvs []
    \\ Cases_on `x` \\ gvs [dec_clock_def, data_to_bvi_result_def]
    >- (qspecl_then [`prog`,`call_env args' ss (t1 with clock := s.clock
      - 1)`]
                    assume_tac optimise_correct \\ gvs []
        \\ gvs [state_rel_def, call_env_def])
    \\ Cases_on `e` \\ gvs [data_to_bvi_result_def])
    >- (last_x_assum $ qspecl_then [
      `call_env args' ss (push_env (inter t1.locals
          (list_to_num_set (live ++ corr))) F (dec_clock t1))`,
      `LENGTH args'`, `COUNT_LIST (LENGTH args')`, `T`, `[]`] mp_tac
    \\ gvs [COUNT_LIST_GENLIST, dec_clock_def,
      bviSemTheory.dec_clock_def]
    \\ impl_tac
    >- (rw []
        \\ gvs [call_env_def, push_env_def, lookup_fromList, EL_MAP,
                state_rel_def, jump_exc_def, AllCaseEqs(), LASTN_TL])
    \\ rw [] \\ gvs []
    \\ Cases_on `pres` \\ gvs [PULL_EXISTS]
    \\ `domain (list_to_num_set (live ++ corr)) ⊆ domain t1.locals` by (
      gvs [SUBSET_DEF, domain_lookup, lookup_list_to_num_set]
      \\ rw []
      >- (
        gvs [EVERY_EL, MEM_EL]
        \\ first_x_assum drule \\ rw []
        \\ Cases_on `lookup (EL n'' live) t1.locals` \\ gvs [])
      >- (
        gvs [MEM_EL]
        \\ first_x_assum drule \\ rw []
        \\ simp [SF SFY_ss]))
    \\ gvs [cut_env_def, PULL_EXISTS, compile_exp_def,
      COUNT_LIST_GENLIST]
    \\ qspecl_then [`prog`,
      `call_env args' ss (push_env (inter t1.locals (list_to_num_set
        (live ++ corr)))
                   F (t1 with clock := s.clock − 1))`]
                    assume_tac optimise_correct \\ gvs []
    \\ reverse $ Cases_on `x` \\ gvs []
    >- (Cases_on `e` \\ gvs [data_to_bvi_result_def])
    \\ imp_res_tac bviPropsTheory.evaluate_SING_IMP
    \\ Cases_on `a` \\ gvs []
    \\ `pop_env (t2 with <| locals_size := ls;
                            stack_max := smx;
                            safe_for_space := safe;
                            peak_heap_length := peak |>) =
       SOME (t2 with <| stack := t1.stack;
                        locals := inter t1.locals (list_to_num_set (live
                          ++ corr));
                        locals_size := t1.locals_size;
                        stack_max := smx;
                        safe_for_space := safe;
                        peak_heap_length := peak|>)`
      by (Q.PAT_X_ASSUM `xx = t2.stack` (ASSUME_TAC o GSYM)
          \\ FULL_SIMP_TAC (srw_ss())
            [call_env_def,push_env_def,flush_state_def,
                                       pop_env_def
                                         ,dataSemTheory.dec_clock_def
                                         ,bviSemTheory.dec_clock_def,
                                       FUNPOW_dec_clock_code,LET_DEF])
    \\ gvs [set_var_def, state_rel_def, lookup_insert, lookup_inter_alt,
            lookup_map]
    \\ rw []
    >- (last_x_assum drule \\ rw [])
    >- gvs [domain_list_to_num_set, MEM_EL]
    >- (
      gvs [domain_list_to_num_set]
      \\ rpt (first_x_assum $ qspec_then `k` assume_tac \\ gvs []))
    >- gvs [domain_list_to_num_set]
    >- gvs [domain_list_to_num_set]
    >- gvs [call_env_def, push_env_def]
    >- gvs [jump_exc_def, call_env_def, push_env_def, AllCaseEqs()])
    >- (gvs [compile_exp_def]
    \\ last_x_assum
      $ qspecl_then [`call_env args' ss (dec_clock t1)`, `LENGTH args'`,
                     `COUNT_LIST (LENGTH args')`, `T`, `[]`] mp_tac
    \\ gvs [] \\ impl_tac
    >- (rw []
        \\ gvs [COUNT_LIST_GENLIST, EL_MAP, dec_clock_def, call_env_def,
                lookup_fromList, bviSemTheory.dec_clock_def,
                  state_rel_def,
                jump_exc_def, AllCaseEqs()])
    \\ rw [] \\ gvs []
    \\ Cases_on `pres` \\ gvs []
    \\ gvs [dec_clock_def]
    \\ qspecl_then [`prog`,`call_env args' ss (t1 with clock := s.clock
      - 1)`]
                   assume_tac optimise_correct \\ gvs []
    \\ gvs [state_rel_def, jump_exc_def, call_env_def, AllCaseEqs()]
    \\ qexists `ls` \\ gvs [state_component_equality])
    >- (last_x_assum $ qspecl_then [
      `call_env args' ss (push_env (inter t1.locals
          (list_to_num_set (live ++ corr))) F (dec_clock t1))`,
      `LENGTH args'`, `COUNT_LIST (LENGTH args')`, `T`, `[]`] mp_tac
    \\ gvs [COUNT_LIST_GENLIST, dec_clock_def,
      bviSemTheory.dec_clock_def]
    \\ impl_tac
    >- (rw []
        \\ gvs [call_env_def, push_env_def, lookup_fromList, EL_MAP,
                state_rel_def, jump_exc_def, AllCaseEqs(), LASTN_TL])
    \\ rw [] \\ gvs []
    \\ Cases_on `pres` \\ gvs [PULL_EXISTS]
    \\ `domain (list_to_num_set (live ++ corr)) ⊆ domain t1.locals` by (
      gvs [SUBSET_DEF, domain_lookup, lookup_list_to_num_set]
      \\ rw []
      >- (
        gvs [EVERY_EL, MEM_EL]
        \\ first_x_assum drule \\ rw []
        \\ Cases_on `lookup (EL n'' live) t1.locals` \\ gvs [])
      >- (
        gvs [MEM_EL]
        \\ first_x_assum drule \\ rw []
        \\ simp [SF SFY_ss]))
    \\ gvs [cut_env_def, PULL_EXISTS, compile_exp_def,
      COUNT_LIST_GENLIST]
    \\ qspecl_then [`prog`,
      `call_env args' ss (push_env (inter t1.locals (list_to_num_set
        (live ++ corr)))
                   F (t1 with clock := s.clock − 1))`]
                    assume_tac optimise_correct \\ gvs []
    \\ gvs [state_rel_def, jump_exc_def, call_env_def, push_env_def,
            LASTN_TL, AllCaseEqs()]
    \\ qexists `ls` \\ gvs [state_component_equality])
    >- (gvs [compile_exp_def]
    \\ last_x_assum
      $ qspecl_then [`call_env args' ss (dec_clock t1)`, `LENGTH args'`,
                     `COUNT_LIST (LENGTH args')`, `T`, `[]`] mp_tac
    \\ gvs [] \\ impl_tac
    >- (rw []
        \\ gvs [COUNT_LIST_GENLIST, EL_MAP, dec_clock_def, call_env_def,
                lookup_fromList, bviSemTheory.dec_clock_def,
                  state_rel_def])
    \\ rw [] \\ gvs []
    \\ Cases_on `pres` \\ gvs []
    \\ Cases_on `x` \\ gvs [dec_clock_def, data_to_bvi_result_def]
    \\ Cases_on `e` \\ gvs [data_to_bvi_result_def]
    \\ qspecl_then [`prog`,`call_env args' ss (t1 with clock := s.clock
      - 1)`]
                   assume_tac optimise_correct \\ gvs []
    \\ gvs [state_rel_def, call_env_def, data_to_bvi_result_def])
    >- (last_x_assum $ qspecl_then [
      `call_env args' ss (push_env (inter t1.locals
          (list_to_num_set (live ++ corr))) F (dec_clock t1))`,
      `LENGTH args'`, `COUNT_LIST (LENGTH args')`, `T`, `[]`] mp_tac
    \\ gvs [COUNT_LIST_GENLIST, dec_clock_def,
      bviSemTheory.dec_clock_def]
    \\ impl_tac
    >- (rw []
        \\ gvs [call_env_def, push_env_def, lookup_fromList, EL_MAP,
                state_rel_def, jump_exc_def, AllCaseEqs(), LASTN_TL])
    \\ rw [] \\ gvs []
    \\ Cases_on `pres` \\ gvs [PULL_EXISTS]
    \\ `domain (list_to_num_set (live ++ corr)) ⊆ domain t1.locals` by (
      gvs [SUBSET_DEF, domain_lookup, lookup_list_to_num_set]
      \\ rw []
      >- (
        gvs [EVERY_EL, MEM_EL]
        \\ first_x_assum drule \\ rw []
        \\ Cases_on `lookup (EL n'' live) t1.locals` \\ gvs [])
      >- (
        gvs [MEM_EL]
        \\ first_x_assum drule \\ rw []
        \\ simp [SF SFY_ss]))
    \\ gvs [cut_env_def, PULL_EXISTS, compile_exp_def,
      COUNT_LIST_GENLIST]
    \\ qspecl_then [`prog`,
      `call_env args' ss (push_env (inter t1.locals (list_to_num_set
        (live ++ corr)))
                   F (t1 with clock := s.clock − 1))`]
                    assume_tac optimise_correct \\ gvs []
    \\ Cases_on `x` \\ gvs [data_to_bvi_result_def]
    \\ Cases_on `e` \\ gvs [data_to_bvi_result_def]
    \\ gvs [state_rel_def, call_env_def, push_env_def,
      data_to_bvi_result_def])
QED
*)

(* HOL4 ML code, not ported:
Resume compile_correct[Call]:
   (note_tac "Call"
    \\ Cases_on `handler`
    >- (note_tac "Call without handler"
    \\ `?c1 vs n1. compile n corr F live xs = (c1,vs,n1)` by METIS_TAC
      [PAIR]
    \\ FULL_SIMP_TAC std_ss
      [LET_DEF,evaluate_def,call_env_def,flush_state_def,compile_def,
                             evaluate_mk_ticks,flush_state_def]
    \\ Cases_on `evaluate (xs,env,s1)`
    \\ reverse (Cases_on `q`) \\ FULL_SIMP_TAC (srw_ss()) []
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t1`,`n`,`corr`,`F`,`live`])
    \\ rpt var_eq_tac >> full_simp_tac(srw_ss())[]>> strip_tac
    \\ Cases_on `pres`
    \\ FULL_SIMP_TAC (srw_ss()) []
    \\ TRY (qexists_tac `ls` \\ rw [] \\ NO_TAC)
    \\ Cases_on `find_code dest a r.code` \\ FULL_SIMP_TAC std_ss []
    \\ Cases_on `x` \\ FULL_SIMP_TAC std_ss []
    \\ Q.MATCH_ASSUM_RENAME_TAC `find_code dest a r.code = SOME
      (args,exp)`
    \\ FULL_SIMP_TAC (srw_ss()) []
    \\ `t2.clock = r.clock` by FULL_SIMP_TAC std_ss [state_rel_def]
    \\ first_assum (mp_then Any assume_tac get_vars_thm)
    \\ first_assum (mp_then Any assume_tac get_vars_lift_thm)
    \\ fs [] \\ rveq
    \\ first_assum (mp_then Any assume_tac find_code_lemma)
    \\ first_x_assum (first_assum o (mp_then Any assume_tac))
    \\ fs [] \\ rveq
    \\ FULL_SIMP_TAC (srw_ss()) [] \\ POP_ASSUM (K ALL_TAC)
    \\ `domain (list_to_num_set (live ++ corr)) SUBSET domain t2.locals`
      by
      (full_simp_tac(srw_ss())[SUBSET_DEF,domain_lookup
        ,lookup_list_to_num_set,EVERY_MEM]
       \\ REPEAT STRIP_TAC \\ RES_TAC THEN1
        (`lookup x t1.locals <> NONE` by METIS_TAC []
         \\ Cases_on `lookup x t1.locals` \\ full_simp_tac(srw_ss())[]
           \\ METIS_TAC [])
       \\ full_simp_tac(srw_ss())[var_corr_def,get_var_def,lookup_map]
       \\ IMP_RES_TAC LIST_REL_MEM_IMP \\ full_simp_tac(srw_ss())[])
    \\ full_simp_tac(srw_ss())[] \\ Cases_on `r.clock < ticks + 1`
    \\ full_simp_tac(srw_ss())[] THEN1
     (`r.clock < ticks \/ r.clock = ticks` by decide_tac \\
       full_simp_tac(srw_ss())[]
      \\ full_simp_tac(srw_ss())[state_rel_def,
        funpow_dec_clock_clock,data_to_bvi_result_def]
      \\ Cases_on `tail` \\ full_simp_tac(srw_ss())[state_rel_def,
        funpow_dec_clock_clock]
      \\ full_simp_tac(srw_ss())[cut_env_def,data_to_bvi_result_def
        ,dec_clock_def])
    \\ `~(r.clock < ticks)` by decide_tac \\ full_simp_tac(srw_ss())[]
    \\ `(FUNPOW dec_clock ticks t2).clock ≠ 0` by simp
      [funpow_dec_clock_clock]
    \\ full_simp_tac(srw_ss())[]
    \\ FULL_SIMP_TAC std_ss [compile_exp_def]
    \\ Q.PAT_X_ASSUM `(res,s2) = bb` (ASSUME_TAC o GSYM)
    \\ FULL_SIMP_TAC std_ss []
    \\ Cases_on `tail`
    >- (`evaluate ([exp],MAP data_to_bvi_v args',dec_clock (ticks + 1)
      r) = (res,s2)` by
        (Cases_on `evaluate ([exp],MAP data_to_bvi_v args',dec_clock
          (ticks+1) r)`
         \\ gvs [AllCaseEqs()]) \\ full_simp_tac(srw_ss())[]
      \\ fs [NOT_LESS]
      \\ FIRST_X_ASSUM (qspecl_then
                        [`call_env args' ss (FUNPOW dec_clock (ticks+1)
                          t2)`,
                         `LENGTH args'`,
                         `GENLIST I (LENGTH args')`,`T`,`[]`]mp_tac)
      \\ FULL_SIMP_TAC std_ss []
      \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
       (FULL_SIMP_TAC (srw_ss())
         [state_rel_def,dataSemTheory.dec_clock_def,
                                  bviSemTheory.dec_clock_def
                                    ,var_corr_def,get_var_def
                                    ,LIST_REL_REVERSE_EQ,
                                  LIST_REL_lookup_fromList_MAP
                                    ,lookup_fromList_outside
                                    ,jump_exc_NONE,call_env_def,
                                  funpow_dec_clock_clock,lookup_map
                                    ,flush_state_def,LET_DEF])
      \\ STRIP_TAC \\ full_simp_tac(srw_ss())[LET_DEF]
      \\ MP_TAC (Q.SPECL [`prog`,
                          `call_env args' ss (FUNPOW dec_clock (ticks+1)
                            t2)`] optimise_correct)
      \\ full_simp_tac(srw_ss())[] \\ SIMP_TAC std_ss
        [call_env_def,flush_state_def]
      \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
       (BasicProvers.FULL_CASE_TAC \\
         full_simp_tac(srw_ss())[funpow_dec_clock_clock]
        \\ REPEAT STRIP_TAC \\
          full_simp_tac(srw_ss())[data_to_bvi_result_def])
      \\ REPEAT STRIP_TAC \\
        full_simp_tac(srw_ss())[COUNT_LIST_GENLIST,LET_DEF]
      \\ full_simp_tac(srw_ss())[FUNPOW_dec_clock_code,LET_DEF]
      \\ full_simp_tac(srw_ss())[GSYM ADD1,FUNPOW_SUC]
      \\ Cases_on `pres` \\ full_simp_tac(srw_ss())[] \\ FULL_SIMP_TAC
        std_ss []
      \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
      \\ FULL_SIMP_TAC (srw_ss()) [call_env_def,flush_state_def,
                                   bviSemTheory.dec_clock_def
                                     ,dataSemTheory.dec_clock_def
                                     ,LET_DEF]
      \\ REV_FULL_SIMP_TAC (srw_ss()) [FUNPOW_dec_clock_code,GSYM
        state_rel_peak_safe]
      \\ qexists_tac `ls`
      \\ conj_tac >- fs [state_rel_def]
      \\ conj_tac >- fs []
      \\ strip_tac \\ fs []
      \\ drule_then (qspecl_then [`safe`,`peak`,`ls'`,`smx`] ASSUME_TAC)
        jump_exc_peak_safe
      \\ fs [state_fupdcanon])
    >- (full_simp_tac(srw_ss())[cut_env_def]
    \\ `evaluate ([exp],MAP data_to_bvi_v args',dec_clock (ticks + 1) r)
      = (res,s2)` by
        (Cases_on `evaluate ([exp],MAP data_to_bvi_v args',dec_clock
          (ticks+1) r)`
         \\ gvs [AllCaseEqs()]) \\ full_simp_tac(srw_ss())[]
    \\ Q.ABBREV_TAC `env2 = (inter t2.locals (list_to_num_set (live ++
      corr)))`
    \\ FIRST_X_ASSUM (qspecl_then
                      [`call_env args' ss (push_env env2 F (FUNPOW
                        dec_clock (ticks + 1) t2))`,
                       `LENGTH args'`,
                       `GENLIST I (LENGTH args')`,`T`,`[]`]mp_tac)
    \\ FULL_SIMP_TAC std_ss []
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
     (FULL_SIMP_TAC (srw_ss())
       [state_rel_def,dataSemTheory.dec_clock_def,
                                bviSemTheory.dec_clock_def,var_corr_def
                                  ,get_var_def,LIST_REL_REVERSE_EQ,
                                LIST_REL_lookup_fromList_MAP
                                  ,lookup_fromList_outside,push_env_def,
                                call_env_def,FUNPOW_dec_clock_code
                                  ,lookup_map,flush_state_def,LET_DEF]
      \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss []
      \\ `jump_exc t2 <> NONE` by full_simp_tac(srw_ss())[]
      \\ Cases_on `jump_exc t2` \\ full_simp_tac(srw_ss())[]
      \\ IMP_RES_TAC jump_exc_IMP
      \\ SIMP_TAC (srw_ss()) [jump_exc_def,FUNPOW_dec_clock_code]
      \\ IMP_RES_TAC LASTN_TL \\ full_simp_tac(srw_ss())[]
      \\ DECIDE_TAC)
    \\ STRIP_TAC \\ full_simp_tac(srw_ss())[LET_DEF]
    \\ MP_TAC (Q.SPECL [`prog`,`call_env args' ss
                        (push_env env2 F (FUNPOW dec_clock (ticks + 1)
                          t2))`]
               optimise_correct) \\ full_simp_tac(srw_ss())[]
    \\ SIMP_TAC std_ss [call_env_def,flush_state_def]
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
     (BasicProvers.FULL_CASE_TAC \\ full_simp_tac(srw_ss())[]
      \\ REPEAT STRIP_TAC \\
        full_simp_tac(srw_ss())[data_to_bvi_result_def])
    \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[FUNPOW_dec_clock_code,COUNT_LIST_GENLIST]
    \\ full_simp_tac(srw_ss())[GSYM ADD1,FUNPOW_SUC]
    \\ Cases_on `pres` \\
      full_simp_tac(srw_ss())[call_env_def,flush_state_def,LET_DEF]
    \\ `~(r.clock ≤ ticks)` by DECIDE_TAC \\ full_simp_tac(srw_ss())[]
    \\ reverse (Cases_on `x`) \\ FULL_SIMP_TAC (srw_ss()) []
    \\ rpt var_eq_tac >> full_simp_tac(srw_ss())[data_to_bvi_result_def]
    >- (reverse
      (Cases_on`e`)>>full_simp_tac(srw_ss())[data_to_bvi_result_def]>>
    IMP_RES_TAC jump_exc_IMP >- fs [state_rel_def]
    \\ FULL_SIMP_TAC (srw_ss())
      [call_env_def,flush_state_def,push_env_def,
                                 dataSemTheory.dec_clock_def
                                   ,bviSemTheory.dec_clock_def,LET_DEF]
    \\ SIMP_TAC (srw_ss()) [jump_exc_def]
    \\ full_simp_tac(srw_ss())[FUNPOW_dec_clock_code,GSYM
      state_rel_peak_safe]
    \\ Cases_on `t2.handler = LENGTH t2.stack` THEN1
     (FULL_SIMP_TAC std_ss [Q.SPEC `x::xs` LASTN_LENGTH_ID
                              |> SIMP_RULE std_ss [LENGTH,ADD1]] \\
                                full_simp_tac(srw_ss())[])
    \\ `t2.handler < LENGTH t2.stack` by DECIDE_TAC
    \\ FULL_SIMP_TAC std_ss []
    \\ IMP_RES_TAC LASTN_TL
    \\ FULL_SIMP_TAC (srw_ss()) []
    \\ ONCE_ASM_REWRITE_TAC []
    \\ fs [state_component_equality,state_rel_def])
    >- (`¬isReturn res` by (strip_tac \\ gvs [])
     \\ gvs []
     \\ imp_res_tac bviPropsTheory.evaluate_SING_IMP \\ gvs []
     \\ `pop_env (t2' with <| locals_size := ls';
                             stack_max := smx;
                             safe_for_space := safe;
                             peak_heap_length := peak |>) =
       SOME (t2' with <| stack := t2.stack;
                         locals := env2;
                         locals_size := t2.locals_size;
                         stack_max := smx;
                         safe_for_space := safe;
                         peak_heap_length := peak|>)`
      by (Q.PAT_X_ASSUM `xx = t2'.stack` (ASSUME_TAC o GSYM)
          \\ FULL_SIMP_TAC (srw_ss())
            [call_env_def,push_env_def,flush_state_def,
                                       pop_env_def
                                         ,dataSemTheory.dec_clock_def
                                         ,bviSemTheory.dec_clock_def,
                                       FUNPOW_dec_clock_code,LET_DEF])
    \\ full_simp_tac(srw_ss())[dataSemTheory.set_vars_def,fromAList_def,
                               sptreeTheory.union_insert_LN,set_var_def
                                 ,state_rel_def]
    \\ IMP_RES_TAC compile_LESS_EQ
    >- (REPEAT STRIP_TAC
    THEN1
     (UNABBREV_ALL_TAC
      \\ full_simp_tac(srw_ss())[lookup_insert,lookup_inter]
      \\ SRW_TAC [] [] THEN1 DECIDE_TAC
      \\ sg `lookup k t2.locals = NONE` \\ full_simp_tac(srw_ss())[]
      \\ FIRST_X_ASSUM MATCH_MP_TAC
      \\ DECIDE_TAC)
    THEN1
     (FULL_SIMP_TAC (srw_ss())
       [var_corr_def,get_var_def,lookup_insert,lookup_map]
      \\ FULL_SIMP_TAC std_ss [listTheory.LIST_REL_EL_EQN]
      \\ REPEAT STRIP_TAC
      \\ Q.MATCH_ASSUM_RENAME_TAC `l < LENGTH env`
      \\ sg `EL l corr <> n1` \\ FULL_SIMP_TAC std_ss []
      \\ `n1 <= n1 /\ l < LENGTH corr` by DECIDE_TAC
      \\ `lookup n1 t1.locals = NONE` by METIS_TAC []
      \\ RES_TAC \\ CCONTR_TAC \\ FULL_SIMP_TAC std_ss []
      \\ UNABBREV_ALL_TAC \\ full_simp_tac(srw_ss())[lookup_inter]
      \\ POP_ASSUM MP_TAC \\ full_simp_tac(srw_ss())[]
      \\ `MEM (EL l corr) corr` by METIS_TAC [MEM_EL]
      \\ full_simp_tac(srw_ss())[lookup_list_to_num_set])
    THEN1
     (FULL_SIMP_TAC (srw_ss()) [var_corr_def,get_var_def,lookup_insert]
      \\ Cases_on `k = n1` \\ FULL_SIMP_TAC std_ss []
      \\ CCONTR_TAC \\ `n1 <= k` by DECIDE_TAC
      \\ RES_TAC \\ FULL_SIMP_TAC std_ss []
      \\ UNABBREV_ALL_TAC \\ full_simp_tac(srw_ss())[lookup_inter])
    THEN1
     (`lookup k t2.locals = SOME x` by
        (FIRST_X_ASSUM MATCH_MP_TAC \\ full_simp_tac(srw_ss())[])
      \\ UNABBREV_ALL_TAC \\
        full_simp_tac(srw_ss())[lookup_inter,lookup_insert]
      \\ `lookup k (list_to_num_set (live ++ corr)) = SOME ()` by
        (full_simp_tac(srw_ss())[lookup_list_to_num_set]
         \\ CCONTR_TAC \\ full_simp_tac(srw_ss())[])
      \\ sg `k <> n1` \\ full_simp_tac(srw_ss())[] \\ CCONTR_TAC \\
        full_simp_tac(srw_ss())[]
      \\ RES_TAC \\ FULL_SIMP_TAC std_ss [])
    \\ FULL_SIMP_TAC (srw_ss())
                 [var_corr_def,get_var_def,lookup_insert,lookup_map,
                  call_env_def,push_env_def,dataSemTheory.dec_clock_def,
                  flush_state_def,LET_DEF,bviSemTheory.dec_clock_def]
               \\ FULL_SIMP_TAC (srw_ss()) [jump_exc_def]
               \\ FULL_SIMP_TAC (srw_ss()) [AllCaseEqs()]
               \\ rveq \\ FULL_SIMP_TAC (srw_ss()) []))))
    >- (note_tac "call with handle"
  \\ `?c1 vs n1. compile n corr F live xs = (c1,vs,n1)` by METIS_TAC
    [PAIR]
  \\ `?c2 v n2. compile (n1+1) (n1::corr) F live [x] = (c2,v,n2)` by
    METIS_TAC [PAIR]
  \\ full_simp_tac(srw_ss())[LET_DEF,evaluate_def,evaluate_mk_ticks,
                             call_env_def,compile_def,flush_state_def]
  \\ Cases_on `evaluate (xs,env,s1)`
  \\ Cases_on `dest = NONE` \\ full_simp_tac(srw_ss())[]
  \\ reverse (Cases_on `q`)
  >- (FULL_SIMP_TAC (srw_ss()) []
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t1`,`n`,`corr`,`F`,`live`])
      \\ rpt var_eq_tac >> full_simp_tac(srw_ss())[]>> strip_tac
      \\ Cases_on `pres` \\ FULL_SIMP_TAC (srw_ss()) []
      \\ qexists_tac `ls` \\ rw [])
  \\ FULL_SIMP_TAC (srw_ss()) []
  \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t1`,`n`,`corr`,`F`,`live`])
  \\ rpt var_eq_tac >> full_simp_tac(srw_ss())[]>> strip_tac
  \\ Cases_on `pres`
  \\ FULL_SIMP_TAC (srw_ss()) []
  >- (Cases_on `find_code dest a r.code` \\ FULL_SIMP_TAC std_ss []
  \\ Cases_on `x'` \\ FULL_SIMP_TAC std_ss []
  \\ Q.MATCH_ASSUM_RENAME_TAC `find_code dest a r.code = SOME
    (args,exp)`
  \\ FULL_SIMP_TAC (srw_ss()) []
  \\ `t2.clock = r.clock` by FULL_SIMP_TAC std_ss [state_rel_def]
  \\ `domain (list_to_num_set (live ++ corr)) SUBSET domain t2.locals`
    by
    (full_simp_tac(srw_ss())[SUBSET_DEF,domain_lookup
      ,lookup_list_to_num_set,EVERY_MEM]
     \\ REPEAT STRIP_TAC \\ RES_TAC THEN1
      (Cases_on `lookup x' t1.locals` \\ full_simp_tac(srw_ss())[] \\
        METIS_TAC [])
     \\ full_simp_tac(srw_ss())[var_corr_def,get_var_def]
     \\ IMP_RES_TAC LIST_REL_MEM_IMP \\
       full_simp_tac(srw_ss())[lookup_map] \\ NO_TAC)
  \\ first_assum (mp_then Any assume_tac get_vars_thm)
  \\ first_assum (mp_then Any assume_tac get_vars_lift_thm)
  \\ fs [] \\ rveq
  \\ first_assum (mp_then Any assume_tac find_code_lemma)
  \\ first_x_assum (first_assum o (mp_then Any assume_tac))
  \\ fs [] \\ rveq
  \\ full_simp_tac(srw_ss())[] \\ Cases_on `r.clock < ticks + 1` \\
    full_simp_tac(srw_ss())[] THEN1
   (`r.clock < ticks \/ r.clock = ticks` by decide_tac \\
     full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[state_rel_def,
      funpow_dec_clock_clock,data_to_bvi_result_def]
    \\ Cases_on `tail` \\ full_simp_tac(srw_ss())[state_rel_def,
      funpow_dec_clock_clock]
    \\ full_simp_tac(srw_ss())[cut_env_def,data_to_bvi_result_def
      ,LET_DEF,dec_clock_def])
  \\ `~(r.clock < ticks)` by decide_tac \\ full_simp_tac(srw_ss())[]
  \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [compile_exp_def]
  \\ `~(r.clock < ticks) /\ ~(r.clock ≤ ticks)` by DECIDE_TAC \\
    full_simp_tac(srw_ss())[]
  \\ Q.PAT_X_ASSUM `(res,s2) = bb` (ASSUME_TAC o GSYM)
  \\ FULL_SIMP_TAC std_ss []
  \\ full_simp_tac(srw_ss())[cut_env_def]
  \\ Cases_on `evaluate ([exp],MAP data_to_bvi_v args',dec_clock (ticks
    + 1) r)`
  \\ Q.MATCH_ASSUM_RENAME_TAC
      `evaluate ([exp],MAP data_to_bvi_v args',dec_clock (ticks + 1) r)
        = (res4,r4)`
  \\ Cases_on `isException res4`
  >- (Cases_on `res4` \\ full_simp_tac(srw_ss())[LET_DEF] \\
    full_simp_tac(srw_ss())[]
    \\ Q.ABBREV_TAC `env2 = (inter t2.locals (list_to_num_set (live ++
      corr)))`
    \\ FIRST_X_ASSUM (qspecl_then
                      [`call_env args' ss (push_env env2 T (FUNPOW
                        dec_clock (ticks+1) t2))`,
                       `LENGTH args'`,
                       `GENLIST I (LENGTH args')`,`T`,`[]`] mp_tac)
    \\ FULL_SIMP_TAC std_ss []
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
     (FULL_SIMP_TAC (srw_ss())
       [state_rel_def,dataSemTheory.dec_clock_def,
                                bviSemTheory.dec_clock_def,var_corr_def
                                  ,get_var_def,LIST_REL_REVERSE_EQ
                                  ,lookup_map,
                                LIST_REL_lookup_fromList_MAP
                                  ,lookup_fromList_outside,push_env_def
                                  ,call_env_def,LET_DEF]
      \\ full_simp_tac(srw_ss())[jump_exc_def,LASTN_LENGTH_ID |> Q.SPEC
        `x::xs` |> RW [LENGTH,ADD1]])
    \\ REPEAT STRIP_TAC
    >- (Cases_on `pres` \\ full_simp_tac(srw_ss())[]
    \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[]
    \\ MP_TAC (Q.SPECL [`prog`,`call_env args' ss
                        (push_env env2 T (FUNPOW dec_clock (ticks+1)
                          t2))`]
               optimise_correct) \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[COUNT_LIST_GENLIST]
    \\ SIMP_TAC std_ss [call_env_def,flush_state_def] \\ REPEAT
      STRIP_TAC \\ full_simp_tac(srw_ss())[]
    \\ fs [] \\ rveq
    \\ Cases_on `evaluate (c2,set_var n1 z' t2')` \\
      full_simp_tac(srw_ss())[]
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL
                      [`FST (evaluate ([x],data_to_bvi_v z'::env,r4))`,
                       `SND (evaluate ([x],data_to_bvi_v z'::env,r4))`,
                       `set_var n1 z'
                         t2'`,`n1+1`,`n1::corr`,`F`,`live`]) \\
                         full_simp_tac(srw_ss())[]
    >- (MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
     (full_simp_tac(srw_ss())[var_corr_def,state_rel_def,set_var_def
       ,lookup_insert,get_var_def,lookup_map]
      \\ full_simp_tac(srw_ss())[jump_exc_def,call_env_def
        ,flush_state_def
                                 ,push_env_def
                                   ,dataSemTheory.dec_clock_def
                                 ,LET_DEF]
      \\ full_simp_tac(srw_ss())[jump_exc_def,LASTN_LENGTH_ID |> Q.SPEC
        `x::xs` |> RW [LENGTH,ADD1]]
      \\ full_simp_tac(srw_ss())[dataSemTheory.state_component_equality]
      \\ Q.PAT_X_ASSUM `env2 = t2'.locals` (ASSUME_TAC o GSYM) \\
        full_simp_tac(srw_ss())[]
      \\ Q.UNABBREV_TAC `env2` \\
        full_simp_tac(srw_ss())[lookup_inter_alt]
      \\ full_simp_tac(srw_ss())[domain_lookup,lookup_list_to_num_set]
      \\ REPEAT STRIP_TAC
      THEN1 (Cases_on `evaluate ([x],data_to_bvi_v z'::env,r4)` \\
        gvs[])
      THEN1
       (full_simp_tac(srw_ss())[LIST_REL_EL_EQN] \\ REPEAT STRIP_TAC
        \\ Q.MATCH_ASSUM_RENAME_TAC `n3 < LENGTH env`
        \\ `MEM (EL n3 corr) corr` by METIS_TAC [MEM_EL] \\
          full_simp_tac(srw_ss())[]
        \\ SRW_TAC [] []
        \\ `EL n3 corr <= EL n3 corr` by full_simp_tac(srw_ss())[] \\
          RES_TAC \\ full_simp_tac(srw_ss())[])
      THEN1 (`k <> n1 /\ n1 <= k` by DECIDE_TAC \\
        full_simp_tac(srw_ss())[])
      THEN1 (simp[AllCaseEqs(),SF DISJ_ss])
      THEN1
       (full_simp_tac(srw_ss())[EVERY_MEM] \\ REPEAT STRIP_TAC
        \\ Cases_on `n' = n1` \\ RES_TAC \\ full_simp_tac(srw_ss())[]
        \\ Cases_on `lookup n' t1.locals` \\ full_simp_tac(srw_ss())[]
        \\ RES_TAC \\ full_simp_tac(srw_ss())[] \\ Cases_on `lookup n'
          t2.locals` \\ full_simp_tac(srw_ss())[])
      \\ Cases_on `evaluate ([x],data_to_bvi_v z'::env,r4)` \\ gvs[]
      \\ Cases_on `LASTN (t2'.handler + 1) t2'.stack` \\ gvs[]
      \\ Cases_on `h` \\ gvs[])
    >- (REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[GSYM ADD1,
      FUNPOW_SUC]
    \\ reverse (Cases_on `q`) \\ full_simp_tac(srw_ss())[]
    >- (drule_then (qspecl_then [`smx`,`safe`,`peak`] ASSUME_TAC)
      evaluate_smx_safe_peak_swap
      \\ `set_var n1 z' (t2' with <| locals_size := ls'; stack_max :=
        smx;
                                     safe_for_space := safe;
                                       peak_heap_length := peak |>) =
         set_var n1 z' t2' with <| locals_size := ls'; stack_max := smx;
                                   safe_for_space := safe;
                                     peak_heap_length := peak |>`
        by rw [set_var_def]
      \\ fs []
      \\ qmatch_asmsub_abbrev_tac `evaluate (c2,z0)`
      \\ qmatch_goalsub_abbrev_tac `evaluate (c2,z1)`
      \\ reverse (Cases_on `isException res`)
      >- (drule_then (qspecl_then [`ls'`] ASSUME_TAC)
        evaluate_swap_local_sizes
        \\ fs []
        \\ qmatch_asmsub_abbrev_tac `evaluate (c2,z2)`
        \\ `z1 = z2` by (UNABBREV_ALL_TAC \\ fs
          [state_component_equality])
        \\ fs []
        \\ reverse (Cases_on `isReturn res`)
        >- (Cases_on `evaluate ([x],data_to_bvi_v z'::env,r4)` \\
          gvs[AllCaseEqs()]
    \\ fs [state_rel_def])
        >- (Cases_on `evaluate ([x],data_to_bvi_v z'::env,r4)` \\
          gvs[AllCaseEqs()]))
      >- (fs []
      \\ Cases_on `x'` \\ fs [data_to_bvi_result_def,

      semanticPrimitivesPropsTheory.map_result_def]
      >- (Cases_on `evaluate ([x],data_to_bvi_v z'::env,r4)` \\
        gvs[AllCaseEqs()])
      \\ Cases_on `e` \\ fs [data_to_bvi_result_def]
      >- (qspecl_then [`c2`,`z0`] (assume_tac o RW [])
        evaluate_stack_and_locals_swap
      \\ rfs []
      \\ drule_then (qspec_then `ls'` assume_tac) jump_exc_lss
      \\ rfs [] \\ first_x_assum (qspecl_then [`z0.stack`,`s2'`,`ls'`]
        assume_tac)
      \\ `stack_fupd (K z0.stack) z0 = z0` by fs
        [state_component_equality]
      \\ fs [] \\ pop_assum kall_tac \\ rfs []
      \\ `isException (FST (evaluate ([x],data_to_bvi_v z'::env,r4)))`
            by metis_tac []
      \\ fs []
      \\ qexists_tac `ls''`
      \\ rpt conj_tac
      >- (Cases_on `evaluate ([x],data_to_bvi_v z'::env,r4)` \\ gvs []
    \\ fs [state_rel_def])
      >- (Cases_on `evaluate ([x],data_to_bvi_v z'::env,r4)` \\ gvs [])
      >- (pop_assum kall_tac \\ unabbrev_all_tac \\ fs [] \\ rveq
      \\ `t2'.stack = t2.stack ∧ t2'.handler = t2.handler`
        by fs [jump_exc_def,state_component_equality,set_var_def,
              call_env_def,push_env_def,dataSemTheory.dec_clock_def,
              flush_state_def,LET_DEF,
              LASTN_LENGTH_ID |> Q.SPEC `x::xs` |> RW [LENGTH,ADD1]]
      \\ rfs [set_var_def] \\ rveq \\ fs []
      \\ qpat_x_assum `jump_exc (_ r') = SOME (_ r')` assume_tac
      \\ drule_then (qspecl_then [`sfs`,`phl`,`lss`,`smx''`] ASSUME_TAC)
                    jump_exc_peak_safe
      \\ fs [state_fupdcanon]
      \\ qmatch_asmsub_abbrev_tac `jump_exc z0`
      \\ qmatch_goalsub_abbrev_tac `jump_exc z1`
      \\ `z1 = z0` by (UNABBREV_ALL_TAC \\ fs
        [state_component_equality])
      \\ fs [] \\ UNABBREV_ALL_TAC \\ fs [state_component_equality]))
      >- (Cases_on `evaluate ([x],data_to_bvi_v z'::env,r4)` \\
        gvs[AllCaseEqs()])))
    >- (Cases_on `res` \\ full_simp_tac(srw_ss())[] \\
      full_simp_tac(srw_ss())[]
    >- (imp_res_tac compile_SING_IMP
    \\ fs[var_corr_def,set_var_def]
    \\ `(t2'.stack = t2.stack) /\ (t2'.handler = t2.handler)` by
      (REPEAT STRIP_TAC \\
        full_simp_tac(srw_ss())[set_var_def,jump_exc_def,call_env_def,
                                                   push_env_def

      ,dataSemTheory.dec_clock_def,flush_state_def,LET_DEF]
       \\ full_simp_tac(srw_ss())[jump_exc_def,LASTN_LENGTH_ID |> Q.SPEC
         `x::xs` |> RW [LENGTH,ADD1]]
       \\ full_simp_tac(srw_ss())
         [dataSemTheory.state_component_equality])
    \\ qpat_x_assum `evaluate (c2, _) = (_,r')`
                    (mp_then Any (qspecl_then [`smx`,`safe`,`peak`]
                      ASSUME_TAC) evaluate_smx_safe_peak_swap)
    \\ fs [state_fupdcanon,get_var_def]
    \\ Cases_on `tail` \\
      full_simp_tac(srw_ss())[evaluate_def,dataSemTheory.get_vars_def]
    >- (IMP_RES_TAC compile_LENGTH
    \\ full_simp_tac(srw_ss())[var_corr_def,set_var_def,call_env_def
      ,get_var_def,
                               dataSemTheory.get_vars_def
                                 ,flush_state_def,LET_DEF]
    \\ qmatch_asmsub_abbrev_tac `evaluate (c2,z0)`
    \\ qspecl_then [`c2`,`z0`] assume_tac evaluate_stack_and_locals_swap
    \\ rfs []
    \\ first_x_assum (qspecl_then [`z0.stack`,`ls'`] assume_tac)
    \\ `stack_fupd (K z0.stack) z0 = z0` by fs
      [state_component_equality]
    \\ fs [] \\ pop_assum kall_tac \\ rfs []
    \\ Q.UNABBREV_TAC `z0`
    \\ qmatch_asmsub_abbrev_tac `evaluate (c2,z0)`
    \\ qmatch_goalsub_abbrev_tac `evaluate (c2,z1)`
    \\ `z0 = z1` by (UNABBREV_ALL_TAC \\ fs [state_component_equality])
    \\ namedCases_on `evaluate ([x],data_to_bvi_v z'::env,r4)`
      ["exres exst"]
    \\ Cases_on `exres`
    \\ full_simp_tac(srw_ss())[data_to_bvi_result_def,lookup_map]
    \\ rveq \\ fs [state_rel_def,lookup_map])
    >- (qmatch_asmsub_abbrev_tac `evaluate (c2,z0)`
    \\ qspecl_then [`c2`,`z0`] assume_tac evaluate_stack_and_locals_swap
    \\ rfs []
    \\ first_x_assum (qspecl_then [`z0.stack`,`ls'`] assume_tac)
    \\ `stack_fupd (K z0.stack) z0 = z0` by fs
      [state_component_equality]
    \\ fs [] \\ pop_assum kall_tac \\ rfs []
    \\ Q.UNABBREV_TAC `z0`
    \\ qmatch_asmsub_abbrev_tac `evaluate (c2,z0)`
    \\ qmatch_goalsub_abbrev_tac `evaluate (c2,z1)`
    \\ `z0 = z1` by (UNABBREV_ALL_TAC \\ fs [state_component_equality])
    \\ namedCases_on `evaluate ([x],data_to_bvi_v z'::env,r4)`
      ["exres exst"]
    \\ Cases_on `exres`
    \\ fs [get_var_def,lookup_insert,lookup_map]
    \\ UNABBREV_ALL_TAC \\ rveq \\ fs []
    \\ rpt conj_tac
    >- (fs [state_rel_def])
    >- (qpat_x_assum `LIST_REL (λv x. ∃z. lookup v r'.locals = SOME z ∧
      x = data_to_bvi_v z) corr env` mp_tac
    \\ match_mp_tac LIST_REL_mono
    \\ qx_genl_tac [`cv`,`ev`] \\ strip_tac \\ gvs []
    \\ `cv < n2` by res_tac
    \\ fs [])
    >- (rpt strip_tac \\ Cases_on `k = n2` \\ fs []
    \\ res_tac \\ fs [])
    >- (rpt strip_tac
    \\ `k ≠ n2` by (CCONTR_TAC \\ fs [] \\ `n ≤ n2` by fs [] \\ res_tac
      \\ fs [])
    \\ `k ≠ n1` by (CCONTR_TAC \\ fs [] \\ `n ≤ n1` by fs [] \\ res_tac
      \\ fs [])
    \\ simp []
    \\ first_x_assum match_mp_tac
    \\ reverse conj_tac >- metis_tac []
    \\ simp []
    \\ `lookup k t2.locals = SOME x'` by metis_tac []
    \\ qpat_x_assum `jump_exc (t2' with <|stack := _; handler := _|>) =
      SOME _` mp_tac
    \\ simp
      [jump_exc_def,call_env_def,push_env_def
      ,dataSemTheory.dec_clock_def,
             flush_state_def,LET_DEF,
             LASTN_LENGTH_ID |> Q.SPEC `x::xs` |> RW [LENGTH,ADD1]]
    \\ strip_tac
    \\ fs [dataSemTheory.state_component_equality]
    \\ qpat_x_assum `_ = t2'.locals` (assume_tac o GSYM)
    \\ fs [lookup_inter_alt,domain_lookup,lookup_list_to_num_set]
    \\ metis_tac [])
    >- (fs [jump_exc_def]
    \\ Cases_on `LASTN (t2'.handler + 1) t2'.stack` \\ fs []
    \\ Cases_on `h` \\ fs [])))
    >- (Cases_on `evaluate ([x],data_to_bvi_v z'::env,r4)` \\ gvs
      [AllCaseEqs()]))))))
  >- (`(res4,r4) = (res,s2)`
      by (Cases_on `res4` \\ gvs [AllCaseEqs()])
    \\ Q.ABBREV_TAC `env2 = (inter t2.locals (list_to_num_set (live ++
      corr)))`
    \\ FIRST_X_ASSUM (qspecl_then
                      [`res4`,`r4`,
                       `call_env args' ss (push_env env2 T (FUNPOW
                         dec_clock (ticks+1) t2))`,
                       `LENGTH args'`,
                       `GENLIST I (LENGTH args')`,`T`,`[]`] mp_tac)
    \\ FULL_SIMP_TAC std_ss []
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
     (FULL_SIMP_TAC (srw_ss())
       [state_rel_def,dataSemTheory.dec_clock_def,
                                bviSemTheory.dec_clock_def,var_corr_def
                                  ,get_var_def,LIST_REL_REVERSE_EQ
                                  ,lookup_map,
                                LIST_REL_lookup_fromList_MAP
                                  ,lookup_fromList_outside,push_env_def
                                  ,call_env_def,LET_DEF]
      \\ full_simp_tac(srw_ss())[jump_exc_def,LASTN_LENGTH_ID |> Q.SPEC
        `x::xs` |> RW [LENGTH,ADD1]])
    \\ REPEAT STRIP_TAC
    \\ MP_TAC (Q.SPECL [`prog`,`call_env args' ss
                        (push_env env2 T (FUNPOW dec_clock (ticks+1)
                          t2))`]
               optimise_correct) \\ full_simp_tac(srw_ss())[]
    \\ SIMP_TAC std_ss [call_env_def,flush_state_def]
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
     (BasicProvers.FULL_CASE_TAC \\ full_simp_tac(srw_ss())[]
      \\ REPEAT STRIP_TAC \\
        full_simp_tac(srw_ss())[data_to_bvi_result_def])
    \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[FUNPOW_dec_clock_code,COUNT_LIST_GENLIST]
    \\ full_simp_tac(srw_ss())[GSYM ADD1,FUNPOW_SUC]
    \\ Cases_on `pres` \\
      full_simp_tac(srw_ss())[call_env_def,flush_state_def,LET_DEF]
    \\ Cases_on `x'` \\ full_simp_tac(srw_ss())[] \\ rpt var_eq_tac
    \\ full_simp_tac(srw_ss())[data_to_bvi_result_def]
    >- (`¬isReturn res` by (strip_tac \\ gvs [])
    \\ gvs []
    \\ imp_res_tac bviPropsTheory.evaluate_SING_IMP \\ gvs []
    \\ `pop_env (t2' with <|locals_size := ls; stack_max := smx;
                            safe_for_space := safe; peak_heap_length :=
                              peak|>) =
        SOME (t2' with <|stack := t2.stack; locals := env2; handler :=
          t2.handler;
                         locals_size := t2.locals_size; stack_max :=
                           smx;
                         safe_for_space := safe; peak_heap_length :=
                           peak|>)`
      by (Q.PAT_X_ASSUM `xx = t2'.stack` (ASSUME_TAC o GSYM)
          \\ FULL_SIMP_TAC (srw_ss())
            [call_env_def,push_env_def,flush_state_def,
                                       pop_env_def
                                         ,dataSemTheory.dec_clock_def,
                                       bviSemTheory.dec_clock_def
                                         ,FUNPOW_dec_clock_code
                                         ,LET_DEF])
    \\ Cases_on `tail`
    \\ full_simp_tac(srw_ss())[evaluate_def,dataSemTheory.get_vars_def,
                               dataSemTheory.set_vars_def,fromAList_def,
                               sptreeTheory.union_insert_LN]
    >- (full_simp_tac(srw_ss())[get_var_def,lookup_insert
      ,data_to_bvi_result_def,
                            flush_state_def,state_rel_def])
    >- (IMP_RES_TAC compile_LESS_EQ
    \\ IMP_RES_TAC compile_SING_IMP
    \\ full_simp_tac(srw_ss())[] \\ IMP_RES_TAC compile_RANGE \\
      full_simp_tac(srw_ss())[EVERY_DEF]
    \\ IMP_RES_TAC compile_LESS_EQ
    \\ conj_tac >- full_simp_tac(srw_ss())[state_rel_def]
    \\ REPEAT STRIP_TAC
    THEN1 DECIDE_TAC
    THEN1
     (UNABBREV_ALL_TAC
      \\ full_simp_tac(srw_ss())[lookup_insert,lookup_inter_alt]
      \\ `k ≠ n2` by DECIDE_TAC
      \\ full_simp_tac(srw_ss())[]
      \\ simp[AllCaseEqs()])
    >- (FULL_SIMP_TAC (srw_ss())
      [var_corr_def,get_var_def,lookup_insert,lookup_map]
      \\ FULL_SIMP_TAC std_ss [listTheory.LIST_REL_EL_EQN]
      \\ REPEAT STRIP_TAC
      \\ Q.MATCH_ASSUM_RENAME_TAC `l < LENGTH env`
      \\ RES_TAC
      \\ UNABBREV_ALL_TAC \\ full_simp_tac(srw_ss())[lookup_inter_alt]
      \\ full_simp_tac(srw_ss())[domain_lookup,lookup_list_to_num_set]
      \\ `EL l corr ≠ n2` by
        (CCONTR_TAC>>fs[LIST_REL_EL_EQN]>>
         last_x_assum(qspec_then `l` assume_tac)>>
         last_x_assum(qspec_then `n2` assume_tac)>>rfs[])
      \\ `MEM (EL l corr) corr` by METIS_TAC [MEM_EL] \\
        full_simp_tac(srw_ss())[]
      \\ SRW_TAC [] []
      \\ METIS_TAC [])
    >- (FULL_SIMP_TAC (srw_ss())
      [var_corr_def,get_var_def,lookup_insert]
      \\ Cases_on`k=n2`>>fs[]
      \\ CCONTR_TAC \\ `n2 <= k` by DECIDE_TAC
      \\ RES_TAC \\ FULL_SIMP_TAC std_ss []
      \\ `n1 <= k` by DECIDE_TAC \\ RES_TAC
      \\ UNABBREV_ALL_TAC \\ full_simp_tac(srw_ss())[lookup_inter_alt]
      \\ fs[])
    >- (FULL_SIMP_TAC (srw_ss())
      [var_corr_def,get_var_def,lookup_insert]
      \\ UNABBREV_ALL_TAC \\ full_simp_tac(srw_ss())[lookup_inter_alt]
      \\ full_simp_tac(srw_ss())[domain_lookup,lookup_list_to_num_set]
      \\ `k ≠ n2` by
        (`n ≤ n2` by fs[]>>CCONTR_TAC>>fs[]>>res_tac>>fs[])
      \\ METIS_TAC [])
    >- (full_simp_tac(srw_ss())[] \\
      full_simp_tac(srw_ss())[jump_exc_def] \\
      rev_full_simp_tac(srw_ss())[]
      \\ Cases_on `LASTN (t2.handler + 1) t2.stack` \\
        full_simp_tac(srw_ss())[]
      \\ rename1 `LASTN _ _ = sf::rest` \\ Cases_on `sf` \\
        full_simp_tac(srw_ss())[])
    >- (fs[var_corr_def,get_var_def,lookup_insert,lookup_map])))
    >- (Cases_on `e` \\
      full_simp_tac(srw_ss())[data_to_bvi_result_def,state_rel_def])))))
QED
*)

(* HOL4 ML code, not ported:
Resume compile_correct[LetCall]:
   (note_tac "LetCall"
    \\ `?c1 vs1 n1. compile n corr F live xs = (c1,vs1,n1)` by METIS_TAC
      [PAIR]
    \\ full_simp_tac(srw_ss())[LET_DEF]
    \\ Cases_on `y = Return (GENLIST Var rets)` \\
      full_simp_tac(srw_ss())[]
    >- (FULL_SIMP_TAC std_ss
      [LET_DEF,evaluate_def,call_env_def,flush_state_def,
                          evaluate_mk_ticks,flush_state_def]
    \\ Cases_on `evaluate (xs,env,s1)`
    \\ reverse (Cases_on `q`) \\ FULL_SIMP_TAC (srw_ss()) []
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t1`,`n`,`corr`,`F`,`live`])
    \\ rpt var_eq_tac >> full_simp_tac(srw_ss())[] >> strip_tac
    \\ Cases_on `pres`
    \\ FULL_SIMP_TAC (srw_ss()) []
    >- (qexists_tac `ls` \\ rw [])
    \\ Cases_on `find_code (SOME dest) a r.code` \\ FULL_SIMP_TAC std_ss
      []
    \\ Cases_on `x` \\ FULL_SIMP_TAC std_ss []
    \\ Q.MATCH_ASSUM_RENAME_TAC `find_code (SOME dest) a r.code = SOME
      (args,exp)`
    \\ FULL_SIMP_TAC (srw_ss()) []
    \\ `t2.clock = r.clock` by FULL_SIMP_TAC std_ss [state_rel_def]
    \\ first_assum (mp_then Any assume_tac get_vars_thm)
    \\ first_assum (mp_then Any assume_tac get_vars_lift_thm)
    \\ fs [] \\ rveq
    \\ first_assum (mp_then Any assume_tac find_code_lemma)
    \\ first_x_assum (first_assum o (mp_then Any assume_tac))
    \\ fs [] \\ rveq
    \\ FULL_SIMP_TAC (srw_ss()) [] \\ POP_ASSUM (K ALL_TAC)
    \\ `domain (list_to_num_set (live ++ corr)) SUBSET domain t2.locals`
      by
      (full_simp_tac(srw_ss())[SUBSET_DEF,domain_lookup
        ,lookup_list_to_num_set,EVERY_MEM]
       \\ REPEAT STRIP_TAC \\ RES_TAC THEN1
        (`lookup x t1.locals <> NONE` by METIS_TAC []
         \\ Cases_on `lookup x t1.locals` \\ full_simp_tac(srw_ss())[]
           \\ METIS_TAC [])
       \\ full_simp_tac(srw_ss())[var_corr_def,get_var_def,lookup_map]
       \\ IMP_RES_TAC LIST_REL_MEM_IMP \\ full_simp_tac(srw_ss())[])
    \\ full_simp_tac(srw_ss())[] \\ Cases_on `r.clock < ticks + 1`
    \\ full_simp_tac(srw_ss())[] THEN1
     (`r.clock < ticks \/ r.clock = ticks` by decide_tac \\
       full_simp_tac(srw_ss())[]
      \\ full_simp_tac(srw_ss())[state_rel_def,
        funpow_dec_clock_clock,data_to_bvi_result_def]
      \\ Cases_on `tail` \\ full_simp_tac(srw_ss())[state_rel_def,
        funpow_dec_clock_clock]
      \\ full_simp_tac(srw_ss())[cut_env_def,data_to_bvi_result_def
        ,dec_clock_def])
    \\ `~(r.clock < ticks)` by decide_tac \\ full_simp_tac(srw_ss())[]
    \\ `(FUNPOW dec_clock ticks t2).clock ≠ 0` by simp
      [funpow_dec_clock_clock]
    \\ full_simp_tac(srw_ss())[]
    \\ FULL_SIMP_TAC std_ss [compile_exp_def]
    \\ Q.PAT_X_ASSUM `(res,s2) = bb` (ASSUME_TAC o GSYM)
    \\ FULL_SIMP_TAC std_ss []
    \\ `evaluate ([exp],MAP data_to_bvi_v args',dec_clock (ticks + 1) r)
      = (res,s2)` by
        (Cases_on `evaluate ([exp],MAP data_to_bvi_v args',dec_clock
          (ticks+1) r)`
         \\ gvs [AllCaseEqs(),evaluate_Return_GENLIST_Var]) \\
           full_simp_tac(srw_ss())[]
    \\ fs [NOT_LESS]
    \\ FIRST_X_ASSUM (qspecl_then
                      [`call_env args' ss (FUNPOW dec_clock (ticks+1)
                        t2)`,
                       `LENGTH args'`,
                       `GENLIST I (LENGTH args')`,`T`,`[]`]mp_tac)
    \\ FULL_SIMP_TAC std_ss []
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
     (FULL_SIMP_TAC (srw_ss())
       [state_rel_def,dataSemTheory.dec_clock_def,
                                bviSemTheory.dec_clock_def,var_corr_def
                                  ,get_var_def,LIST_REL_REVERSE_EQ,
                                LIST_REL_lookup_fromList_MAP
                                  ,lookup_fromList_outside,jump_exc_NONE
                                  ,call_env_def,
                                funpow_dec_clock_clock,lookup_map
                                  ,flush_state_def,LET_DEF])
    \\ STRIP_TAC \\ full_simp_tac(srw_ss())[LET_DEF]
    \\ MP_TAC (Q.SPECL [`prog`,
                        `call_env args' ss (FUNPOW dec_clock (ticks+1)
                          t2)`] optimise_correct)
    \\ full_simp_tac(srw_ss())[] \\ SIMP_TAC std_ss
      [call_env_def,flush_state_def]
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
     (BasicProvers.FULL_CASE_TAC \\
       full_simp_tac(srw_ss())[funpow_dec_clock_clock]
      \\ REPEAT STRIP_TAC \\
        full_simp_tac(srw_ss())[data_to_bvi_result_def])
    \\ REPEAT STRIP_TAC \\
      full_simp_tac(srw_ss())[COUNT_LIST_GENLIST,LET_DEF]
    \\ full_simp_tac(srw_ss())[FUNPOW_dec_clock_code,LET_DEF]
    \\ full_simp_tac(srw_ss())[GSYM ADD1,FUNPOW_SUC]
    \\ Cases_on `pres` \\ full_simp_tac(srw_ss())[] \\ FULL_SIMP_TAC
      std_ss []
    \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC (srw_ss()) [call_env_def,flush_state_def,
                                 bviSemTheory.dec_clock_def
                                   ,dataSemTheory.dec_clock_def,LET_DEF]
    \\ REV_FULL_SIMP_TAC (srw_ss()) [FUNPOW_dec_clock_code,GSYM
      state_rel_peak_safe]
    >- (qexists_tac `ls`
    \\ conj_tac >- fs [state_rel_def]
    \\ conj_tac >- fs []
    \\ conj_tac >- (strip_tac \\ gvs [])
    \\ strip_tac \\ fs []
    \\ drule_then (qspecl_then [`safe`,`peak`,`ls'`,`smx`] ASSUME_TAC)
      jump_exc_peak_safe
    \\ fs [state_fupdcanon]))
    >- (`?c2 vy n2. compile (n1 + rets) (GENLIST (λi. n1 + i) rets ++
      corr) tail live [y] =
        (c2,vy,n2)` by METIS_TAC [PAIR]
    \\ full_simp_tac(srw_ss())[LET_DEF]
    \\ FULL_SIMP_TAC std_ss
      [LET_DEF,evaluate_def,call_env_def,flush_state_def,
                             evaluate_mk_ticks,flush_state_def]
    \\ Cases_on `evaluate (xs,env,s1)`
    \\ reverse (Cases_on `q`) \\ FULL_SIMP_TAC (srw_ss()) []
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t1`,`n`,`corr`,`F`,`live`])
    \\ rpt var_eq_tac >> full_simp_tac(srw_ss())[] >> strip_tac
    \\ Cases_on `pres`
    \\ FULL_SIMP_TAC (srw_ss()) []
    >- (qexists_tac `ls` \\ rw [])
    >- (Cases_on `find_code (SOME dest) a r.code` \\ FULL_SIMP_TAC
      std_ss []
    \\ Cases_on `x` \\ FULL_SIMP_TAC std_ss []
    \\ Q.MATCH_ASSUM_RENAME_TAC `find_code (SOME dest) a r.code = SOME
      (args,exp)`
    \\ FULL_SIMP_TAC (srw_ss()) []
    \\ `t2.clock = r.clock` by FULL_SIMP_TAC std_ss [state_rel_def]
    \\ first_assum (mp_then Any assume_tac get_vars_thm)
    \\ first_assum (mp_then Any assume_tac get_vars_lift_thm)
    \\ fs [] \\ rveq
    \\ first_assum (mp_then Any assume_tac find_code_lemma)
    \\ first_x_assum (first_assum o (mp_then Any assume_tac))
    \\ fs [] \\ rveq
    \\ FULL_SIMP_TAC (srw_ss()) [] \\ POP_ASSUM (K ALL_TAC)
    \\ `domain (list_to_num_set (live ++ corr)) SUBSET domain t2.locals`
      by
      (full_simp_tac(srw_ss())[SUBSET_DEF,domain_lookup
        ,lookup_list_to_num_set,EVERY_MEM]
       \\ REPEAT STRIP_TAC \\ RES_TAC THEN1
        (`lookup x t1.locals <> NONE` by METIS_TAC []
         \\ Cases_on `lookup x t1.locals` \\ full_simp_tac(srw_ss())[]
           \\ METIS_TAC [])
       \\ full_simp_tac(srw_ss())[var_corr_def,get_var_def,lookup_map]
       \\ IMP_RES_TAC LIST_REL_MEM_IMP \\ full_simp_tac(srw_ss())[])
    \\ full_simp_tac(srw_ss())[] \\ Cases_on `r.clock < ticks + 1`
    \\ full_simp_tac(srw_ss())[] THEN1
     (`r.clock < ticks \/ r.clock = ticks` by decide_tac \\
       full_simp_tac(srw_ss())[]
      \\ full_simp_tac(srw_ss())[state_rel_def,
        funpow_dec_clock_clock,data_to_bvi_result_def,
           ALL_DISTINCT_GENLIST, cut_env_def]
      \\ full_simp_tac(srw_ss())[funpow_dec_clock_clock,dec_clock_def
        ,LET_DEF])
    \\ `~(r.clock < ticks)` by decide_tac
    \\ `~(r.clock ≤ ticks)` by decide_tac
    \\ full_simp_tac(srw_ss())[ALL_DISTINCT_GENLIST, cut_env_def]
    \\ FULL_SIMP_TAC std_ss [compile_exp_def]
    \\ Cases_on `evaluate ([exp],MAP data_to_bvi_v args',dec_clock
      (ticks + 1) r)`
    \\ Q.MATCH_ASSUM_RENAME_TAC
         `evaluate ([exp],MAP data_to_bvi_v args',dec_clock (ticks + 1)
           r) = (res4,r4)`
    \\ `res4 ≠ Rerr (Rabort Rtype_error)` by (Cases_on `res4` \\
      gvs[AllCaseEqs()])
    \\ Q.ABBREV_TAC `env2 = (inter t2.locals (list_to_num_set (live ++
      corr)))`
    \\ qpat_x_assum `∀res' s2' t1' n' corr' tail' live'. _`
         (qspecl_then [`res4`,`r4`,
            `call_env args' ss (push_env env2 F (FUNPOW dec_clock
              (ticks+1) t2))`,
            `LENGTH args'`,`GENLIST I (LENGTH args')`,`T`,`[]`] mp_tac)
    \\ FULL_SIMP_TAC std_ss []
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
     (FULL_SIMP_TAC (srw_ss())
       [state_rel_def,dataSemTheory.dec_clock_def,
                                bviSemTheory.dec_clock_def,var_corr_def
                                  ,get_var_def,LIST_REL_REVERSE_EQ,
                                LIST_REL_lookup_fromList_MAP
                                  ,lookup_fromList_outside,push_env_def,
                                call_env_def,FUNPOW_dec_clock_code
                                  ,lookup_map,flush_state_def,LET_DEF]
      \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss []
      \\ `jump_exc t2 ≠ NONE` by
           (`isException res` by (Cases_on `res4` \\ gvs[AllCaseEqs()])
             \\ res_tac \\ fs[])
      \\ Cases_on `jump_exc t2` \\ full_simp_tac(srw_ss())[]
      \\ IMP_RES_TAC jump_exc_IMP
      \\ SIMP_TAC (srw_ss()) [jump_exc_def,FUNPOW_dec_clock_code]
      \\ IMP_RES_TAC LASTN_TL \\ full_simp_tac(srw_ss())[]
      \\ DECIDE_TAC)
    >- (REPEAT STRIP_TAC
    \\ MP_TAC (Q.SPECL [`prog`,`call_env args' ss
                        (push_env env2 F (FUNPOW dec_clock (ticks+1)
                          t2))`]
               optimise_correct) \\ full_simp_tac(srw_ss())[]
    \\ SIMP_TAC std_ss [call_env_def,flush_state_def]
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
     (BasicProvers.FULL_CASE_TAC \\ full_simp_tac(srw_ss())[]
      \\ REPEAT STRIP_TAC \\
        full_simp_tac(srw_ss())[data_to_bvi_result_def])
    \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[FUNPOW_dec_clock_code,COUNT_LIST_GENLIST]
    \\ full_simp_tac(srw_ss())[GSYM ADD1,FUNPOW_SUC]
    \\ Cases_on `pres` \\
      full_simp_tac(srw_ss())[call_env_def,flush_state_def,LET_DEF]
    \\ Cases_on `x` \\ full_simp_tac(srw_ss())[] \\ rpt var_eq_tac
    \\ full_simp_tac(srw_ss())[data_to_bvi_result_def]
    >- (`isReturn res4` by (Cases_on `res4` \\ gvs[AllCaseEqs()])
    \\ full_simp_tac(srw_ss())[] \\ rveq \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `LENGTH a = rets` \\ full_simp_tac(srw_ss())[]
    \\ `pop_env (t2' with <|locals_size := ls'; stack_max := smx;
                            safe_for_space := safe; peak_heap_length :=
                              peak|>) =
          SOME (t2' with <|stack := t2.stack; locals := env2; handler :=
            t2.handler;
                           locals_size := t2.locals_size; stack_max :=
                             smx;
                           safe_for_space := safe; peak_heap_length :=
                             peak|>)`
       by (Q.PAT_X_ASSUM `xx = t2'.stack` (ASSUME_TAC o GSYM)
           \\ FULL_SIMP_TAC (srw_ss())
             [call_env_def,push_env_def,flush_state_def,
                                        pop_env_def
                                          ,dataSemTheory.dec_clock_def,
                                        bviSemTheory.dec_clock_def
                                          ,FUNPOW_dec_clock_code
                                          ,LET_DEF])
    \\ full_simp_tac(srw_ss())[]
    \\ qmatch_goalsub_abbrev_tac `evaluate (c2, t1d)`
    \\ first_x_assum (qspecl_then
         [`res`,`s2`,`t1d`,`n1+rets`,`GENLIST (λi. i+n1) rets ++
           corr`,`tail`,`live`] mp_tac)
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
    >- (rpt conj_tac
    >- full_simp_tac(srw_ss())[]
    >- full_simp_tac(srw_ss())[]
    >- (Q.UNABBREV_TAC `t1d`
    \\ simp[var_corr_def, set_vars_def, lookup_map]
    \\ irule EVERY2_APPEND_suff
    \\ conj_tac
    >- (simp[LIST_REL_EL_EQN, EL_MAP, EL_GENLIST, lookup_map,
      get_var_def] \\ rw[]
        \\ DEP_REWRITE_TAC [lookup_union] \\ simp[lookup_fromAList]
        \\ qexists_tac `EL n' a`
        \\ `ALOOKUP (ZIP (GENLIST (λi. i + n1) (LENGTH a),a)) (n' + n1)
          = SOME (EL n' a)` by
             (irule ALOOKUP_ALL_DISTINCT_MEM \\ simp[MAP_ZIP,
               ALL_DISTINCT_GENLIST, MEM_ZIP]
              \\ qexists_tac `n'` \\ simp[EL_GENLIST])
        \\ simp[])
    >- (`!k. MEM k corr ⇒ k < n1` by
      (rpt strip_tac \\ fs[MEM_EL] \\ rveq
       \\ qpat_x_assum `var_corr env corr _` mp_tac
       \\ simp[var_corr_def, LIST_REL_EL_EQN, get_var_def, lookup_map]
       \\ rw[] \\ first_x_assum drule \\ rw[]
       \\ Cases_on `lookup (EL n' corr) t2.locals` \\ fs[] \\ res_tac)
    \\ `!k. k < n1 ⇒ ~MEM k (GENLIST (λi. i + n1) rets)` by
      rw[MEM_GENLIST]
    \\ `!k. MEM k corr ⇒
         lookup k (union (fromAList (ZIP (GENLIST (λi. i + n1) rets,a)))
           env2) =
         lookup k t2.locals` by
       (rpt strip_tac \\ `k < n1` by res_tac \\ `~MEM k (GENLIST (λi. i
         + n1) rets)` by res_tac
        \\ simp[lookup_union]
        \\ `ALOOKUP (ZIP (GENLIST (λi. i + n1) rets,a)) k = NONE` by
             simp[ALOOKUP_NONE, MAP_ZIP, LENGTH_GENLIST]
        \\ simp[] \\ Q.UNABBREV_TAC `env2` \\ simp[lookup_inter_alt]
        \\ simp[lookup_fromAList]
        \\ `k ∈ domain (list_to_num_set (live ++ corr))` by
          simp[domain_list_to_num_set]
        \\ simp[])
    \\ fs[var_corr_def, LIST_REL_EL_EQN] \\ rw[]
    \\ `MEM (EL n' corr) corr` by (simp[MEM_EL] \\ metis_tac[])
    \\ first_x_assum drule \\ rw[get_var_def, lookup_map]
    \\ res_tac \\ fs[]
    \\ qpat_x_assum `∀n. n < LENGTH corr ⇒ get_var _ (map data_to_bvi_v
      t2.locals) = _`
         (qspec_then `n'` mp_tac)
    \\ simp[get_var_def, lookup_map]))
    >- (Q.UNABBREV_TAC `t1d` \\ rpt strip_tac \\ simp[set_vars_def,
      lookup_union]
    \\ `ALOOKUP (ZIP (GENLIST (λi. i + n1) rets,a)) k = NONE` by
         simp[ALOOKUP_NONE, MAP_ZIP, LENGTH_GENLIST, MEM_GENLIST]
    \\ simp[lookup_fromAList] \\ Q.UNABBREV_TAC `env2` \\
      simp[lookup_inter_alt]
    \\ rw[] \\ first_x_assum irule \\ simp[])
    >- (Q.UNABBREV_TAC `t1d` \\ fs[set_vars_def] \\ fs[state_rel_def])
    >- (Q.UNABBREV_TAC `t1d` \\ simp[set_vars_def, EVERY_MEM] \\
      Q.X_GEN_TAC `m` \\ strip_tac
    \\ `m ∈ domain (list_to_num_set (live ++ corr))` by
      simp[domain_list_to_num_set, MEM_APPEND]
    \\ simp[lookup_union, lookup_fromAList]
    \\ Cases_on `ALOOKUP (ZIP (GENLIST (λi. i + n1) rets,a)) m` \\
      simp[]
    \\ Q.UNABBREV_TAC `env2` \\ simp[lookup_inter_alt]
    \\ fs[SUBSET_DEF, domain_lookup] \\ res_tac \\ fs[])
    >- (strip_tac
    \\ `jump_exc t2 ≠ NONE` by metis_tac[]
    \\ `t1d.stack = t2.stack ∧ t1d.handler = t2.handler` by
         (Q.UNABBREV_TAC `t1d` \\ simp[set_vars_def])
    \\ fs[jump_exc_def]
    \\ Cases_on `LASTN (t2.handler + 1) t2.stack` \\ fs[]
    \\ Cases_on `h` \\ fs[]))
    >- (strip_tac
    \\ `t1d.stack = t2.stack ∧ t1d.handler = t2.handler` by
         (Q.UNABBREV_TAC `t1d` \\ simp[set_vars_def])
    \\ gvs[]
    \\ Cases_on `pres` \\ gvs[]
    >- (rpt conj_tac
    >- (qpat_x_assum `var_corr (MAP data_to_bvi_v a ++ env) _ _` mp_tac
        \\ simp[var_corr_def, LENGTH_GENLIST,
          listTheory.LIST_REL_APPEND_EQ])
    >- (rpt strip_tac
        \\ `lookup k t2.locals = SOME x` by metis_tac[]
        \\ `k < n1` by res_tac
        \\ first_x_assum irule \\ simp[]
        \\ Q.UNABBREV_TAC `t1d` \\ simp[set_vars_def, lookup_union,
          lookup_fromAList]
        \\ `~MEM k (GENLIST (λi. i + n1) (LENGTH a))` by rw[MEM_GENLIST]
        \\ `ALOOKUP (ZIP (GENLIST (λi. i + n1) (LENGTH a),a)) k = NONE`
          by
             simp[ALOOKUP_NONE, MAP_ZIP, LENGTH_GENLIST]
        \\ simp[] \\ Q.UNABBREV_TAC `env2` \\ simp[lookup_inter_alt]
        \\ `k ∈ domain (list_to_num_set (live ++ corr))` by
             (simp[domain_list_to_num_set, MEM_APPEND] \\ metis_tac[])
        \\ simp[])
    >- (strip_tac \\ fs[jump_exc_def]
        \\ Cases_on `LASTN (t2''.handler + 1) t2''.stack` \\ fs[] \\
          Cases_on `h` \\ fs[]))
    >- (qexists_tac `ls`
    \\ `t1d.stack = t2.stack ∧ t1d.handler = t2.handler` by
         (Q.UNABBREV_TAC `t1d` \\ simp[set_vars_def])
    \\ conj_tac >- (strip_tac \\ gvs[]) \\ simp[])))
    >- (reverse (Cases_on `e`) >>
      full_simp_tac(srw_ss())[data_to_bvi_result_def] >>
    IMP_RES_TAC jump_exc_IMP >- fs [state_rel_def]
    \\ FULL_SIMP_TAC (srw_ss())
      [call_env_def,flush_state_def,push_env_def,
                                 dataSemTheory.dec_clock_def
                                   ,bviSemTheory.dec_clock_def,LET_DEF]
    \\ SIMP_TAC (srw_ss()) [jump_exc_def]
    \\ full_simp_tac(srw_ss())[FUNPOW_dec_clock_code,GSYM
      state_rel_peak_safe]
    \\ Cases_on `t2.handler = LENGTH t2.stack` THEN1
     (FULL_SIMP_TAC std_ss [Q.SPEC `x::xs` LASTN_LENGTH_ID |> SIMP_RULE
       std_ss [LENGTH,ADD1]]
      \\ full_simp_tac(srw_ss())[])
    \\ `t2.handler < LENGTH t2.stack` by DECIDE_TAC
    \\ FULL_SIMP_TAC std_ss []
    \\ IMP_RES_TAC LASTN_TL
    \\ FULL_SIMP_TAC (srw_ss()) []
    \\ ONCE_ASM_REWRITE_TAC []
    \\ fs [state_component_equality,state_rel_def])))))
QED
*)

(* HOL4 ML code, not ported:
Finalise compile_correct;
*)

(* HOL4 ML code, not ported:
val compile_exp_lemma = compile_correct
  |> Q.SPECL [`[exp]`,`env`,`s1`,`res`,`s2`,`t1`,`n`,`GENLIST I
    n`,`T`,`[]`]
  |> SIMP_RULE std_ss [LENGTH,GSYM compile_exp_def,option_case_NONE_F,
       PULL_EXISTS,EVERY_DEF];
*)

(* observational semantics *)
