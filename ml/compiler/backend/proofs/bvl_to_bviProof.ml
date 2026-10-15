(* ======================================================== *)
(*  bvl_to_bviProof: ported from HOL4's
    compiler/backend/proofs/bvl_to_bviProofScript.sml  *)
(* ======================================================== *)

(*
  Correctness proof for bvl_to_bvi
*)

needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/bvi_inline.ml";;
needs "compiler/backend/bvi_let.ml";;
needs "compiler/backend/bvl_to_bvi.ml";;
needs "compiler/backend/proofs/bvi_inlineProof.ml";;
needs "compiler/backend/proofs/bvi_letProof.ml";;
needs "compiler/backend/proofs/bvi_tailrecProof.ml";;
needs "compiler/backend/proofs/bvi_tmcProof.ml";;
needs "compiler/backend/proofs/bvl_constProof.ml";;
needs "compiler/backend/proofs/bvl_handleProof.ml";;
needs "compiler/backend/proofs/bvl_inlineProof.ml";;
needs "compiler/backend/semantics/backendProps.ml";;
needs "compiler/backend/semantics/bviProps.ml";;
needs "compiler/backend/semantics/bviSem.ml";;
needs "compiler/backend/semantics/bvlProps.ml";;
needs "compiler/backend/semantics/bvlSem.ml";;
needs "compiler/backend/semantics/closSem.ml";;
needs "lib/sptree.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/semanticPrimitives.ml";;

(* HOL4 ML code, not ported:
val handle_ok_def = bvl_handleProofTheory.handle_ok_def;
*)

(* value relation *)
(* HOL4 overload (expanded in the port):
     num_stubs = bvl_num_stubs *)
(* HOL4 overload (expanded in the port):
     nss = bvl_to_bvi_namespaces *)

let adjust_bv_def = cake_define_list
  [`adjust_bv b (Number i:bvlSem_v) = (Number i:bvlSem_v)`;
   `adjust_bv b (Word64 w:bvlSem_v) = (Word64 w:bvlSem_v)`;
   `adjust_bv b (RefPtr l r:bvlSem_v) = (RefPtr l (b r):bvlSem_v)`;
   `adjust_bv b (bvlSem_CodePtr c) = bvlSem_CodePtr (bvl_num_stubs +
  bvl_to_bvi_namespaces * c)`;
   `adjust_bv b (Block tag vs:bvlSem_v) = (Block tag (MAP
  (adjust_bv b) vs):bvlSem_v)`];;

(* HOL4 ML code, not ported:
val adjust_bv_ind = theorem"adjust_bv_ind";
*)

let aux_code_installed_def = cake_define_list
  [`aux_code_installed [] t <=> T`;
   `aux_code_installed ((name,arg_count,body) :: rest) t <=>
         (sptree_lookup name t = SOME (arg_count,body)) /\
         aux_code_installed rest t`];;

(* HOL4 overload (expanded in the port):
     in_ns_0 = λn. n MOD bvl_to_bvi_namespaces = 0 *)
(* HOL4 overload (expanded in the port):
     in_ns_1 = λn. n MOD bvl_to_bvi_namespaces = 1 *)

let names_ok_def = cake_define
  `bvl_to_bviProof_names_ok s_code t_code s_oracle <=>
     (!n k prog. s_oracle n = (k,prog) ==>
                 EVERY (\(name,arity,exp). handle_ok [exp]) prog) /\
     (let next' = FST (FST (s_oracle 0)) in
       (!n. n IN domain t_code /\ bvl_num_stubs <= n ==>
            (if (\n. n MOD bvl_to_bvi_namespaces = 1) n then n <
              bvl_num_stubs + bvl_to_bvi_namespaces * next' else (\n. n
              MOD bvl_to_bvi_namespaces = 0) n /\
                 (n - bvl_num_stubs) DIV bvl_to_bvi_namespaces IN
                   domain s_code)))`;;
hol4_overload "names_ok" "bvl_to_bviProof_names_ok";;

let state_rel_def = cake_define
  `bvl_to_bviProof_state_rel (b:num->num) s (t:('c,'ffi)bviSem_state)
  <=>
     INJ b (FDOM (state_refs s)) (FDOM (state_refs t)) /\
     (!k. match FLOOKUP (state_refs s) k with NONE -> T | SOME
       (ValueArray vs) ->
              (FLOOKUP (state_refs t) (b k) = SOME (ValueArray (MAP
                (adjust_bv b) vs))) | SOME (Thunk m v) ->
              (FLOOKUP (state_refs t) (b k) = SOME (Thunk m
                (adjust_bv b v))) | SOME res -> (FLOOKUP (state_refs t)
                (b k) = SOME res)) /\
     (state_ffi s = state_ffi t) /\
     (!p. bviSem_state_global t = SOME p ==> ~(
            p IN IMAGE b (FDOM (state_refs s))) /\
            (?z. FLOOKUP (state_refs t) p =
                  SOME (ValueArray
                    ((Number (&(SUC (LENGTH (state_globals s))))) ::
                     (MAP (the (Number (&0)) o OPTION_MAP (adjust_bv
                       b)) (state_globals s) ++
                     REPLICATE (z - (SUC (LENGTH (state_globals s))))
                       (Number (&0))))) /\
                SUC (LENGTH (state_globals s)) <= z)) /\
     (state_clock s = state_clock t) /\ compile_oracle
     t = state_co compile_inc (compile_oracle s) /\ compile
     s = state_cc compile_inc (compile t) /\
     (sptree_lookup AllocGlobal_location (state_code t) = SOME
       AllocGlobal_code) /\
     (sptree_lookup CopyGlobals_location (state_code t) = SOME
       CopyGlobals_code) /\
     (sptree_lookup ListLength_location (state_code t) = SOME
       ListLength_code) /\
     (sptree_lookup FromListByte_location (state_code t) = SOME
       FromListByte_code) /\
     (sptree_lookup ToListByte_location (state_code t) = SOME
       ToListByte_code) /\
     (sptree_lookup SumListLength_location (state_code t) = SOME
       SumListLength_code) /\
     (sptree_lookup ConcatByte_location (state_code t) = SOME
       ConcatByte_code) /\
     bvl_to_bviProof_names_ok (state_code s) (state_code t)
       (compile_oracle s) /\
     (!name arity exp.
        (sptree_lookup name (state_code s) = SOME (arity,exp)) ==>
        (?n. let (c1,aux1,n1) = compile_exps n [exp] in
              (sptree_lookup (bvl_num_stubs + bvl_to_bvi_namespaces *
                name) (state_code t) =
                 SOME (arity,bvi_let_compile_exp (HD c1))) /\
              aux_code_installed (append aux1) (state_code t) /\
              handle_ok [exp]))`;;
hol4_overload "state_rel" "bvl_to_bviProof_state_rel";;

let _ = size_thms "v";;
(* HOL4 termination: \\ Induct_on `vs` \\ full_simp_tac(srw_ss())[]
   \\ SRW_TAC [] [v_size_def] \\ RES_TAC \\ FIRST_X_ASSUM (ASSUME_TAC
   o SPEC_ALL) \\ DECIDE_TAC *)
let bv_ok_def = cake_define_wf
  `MEASURE (v_size o SND)`
  `bv_ok refs x2 =
        match (refs,x2) with
          ((refs:(num,bvlSem_v bvlSem_ref)fmap),(RefPtr l
            r:bvlSem_v)) -> r IN FDOM refs
        | (refs,(Block tag vs)) -> EVERY (bv_ok refs) vs
        | (refs,_1) -> T`;;

(* HOL4 ML code, not ported:
val bv_ok_ind = theorem"bv_ok_ind";
*)

let state_ok_def = cake_define
  `bvl_to_bviProof_state_ok (s:('c,'ffi)bvlSem_state) <=>
     EVERY (\x. match x with NONE -> T | SOME v -> bv_ok (state_refs
       s) v) (state_globals s) /\
     (!k. match FLOOKUP (state_refs s) k with SOME (ValueArray vs)
       -> EVERY (bv_ok (state_refs s)) vs | SOME (Thunk _2 v) ->
       bv_ok (state_refs s) v | _3 -> T)`;;
hol4_overload "state_ok" "bvl_to_bviProof_state_ok";;

(* evaluate preserves state_ok *)

(*
  THEN1 (
    rename1`_ () = String _`
    \\ fs[state_ok_def,bv_ok_def,EVERY_MEM,FLOOKUP_UPDATE]
    \\ rw[]
    \\ CASE_TAC \\ fs[]
    \\ TRY CASE_TAC \\ fs[] \\ rw[]
    \\ match_mp_tac bv_ok_SUBSET_IMP
    \\ TRY (first_x_assum(qspec_then`k`mp_tac) \\ rw[])
    \\ res_tac \\ fs[]
    \\ asm_exists_tac \\ fs[]
    \\ fs[SUBSET_DEF] )
*)

(* HOL4 ML code, not ported:
fun cases_on_op q = Cases_on q >|
  map (MAP_EVERY Cases_on) [[], [], [], [], [`b`], [`g`], [`m`], [],
    [`t`]];
*)
(* HOL4 ML code, not ported:
val _ = print "Proved do_app_ok_lemma\n"
*)

(* semantics lemmas *)

(* HOL4 ML code, not ported:
val evaluate_MAP_Var = Q.prove(
  `!l env vs b s.
      EVERY isVar l /\ (get_vars (MAP destVar l) env = SOME vs) ==>
        (evaluate (MAP (Var o destVar) l,MAP (adjust_bv b) env,s) =
          (Rval (MAP (adjust_bv b) vs),s))`,
  Induct THEN1 (EVAL_TAC \\ SRW_TAC [] [])
  \\ Cases \\
    full_simp_tac(srw_ss())[isVar_def,destVar_def,get_vars_def]
  \\ Cases_on `l` \\
    full_simp_tac(srw_ss())[bviSemTheory.evaluate_def,get_vars_def
    ,EL_MAP]
  \\ Cases_on `h` \\ full_simp_tac(srw_ss())[isVar_def,destVar_def]
  \\ REPEAT STRIP_TAC
  \\ Cases_on `n' < LENGTH env` \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `get_vars (MAP destVar t) env` \\
    full_simp_tac(srw_ss())[]
  \\ Q.PAT_X_ASSUM `!xx.bb` (MP_TAC o Q.SPEC `env`) \\
    full_simp_tac(srw_ss())[]
  \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[EL_MAP])
  |> INST_TYPE[beta|->``:'ffi``,alpha|->``:'c``];
*)

(* HOL4 ML code, not ported:
val evaluate_MAP_Var2 = Q.prove(
  `!args.
      bVarBound (LENGTH vs) args /\ EVERY isVar args ==>
      ?ts.
        bviSem$evaluate (MAP (Var o destVar) args,vs ++ env,s) = (Rval
          ts,s) /\
        evaluate (MAP (Var o destVar) args,vs,s) = (Rval ts,s)`,
  Induct \\ full_simp_tac(srw_ss())[MAP,bviSemTheory.evaluate_def] \\
    Cases \\ full_simp_tac(srw_ss())[isVar_def]
  \\ Cases_on `args` \\
    full_simp_tac(srw_ss())[MAP,bviSemTheory.evaluate_def,destVar_def
    ,bVarBound_def]
  \\ REPEAT STRIP_TAC
  \\ `n < LENGTH vs + LENGTH env` by DECIDE_TAC \\
    full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[rich_listTheory.EL_APPEND1]) |> SPEC_ALL
  |> INST_TYPE[beta|->``:'ffi``,alpha|->``:'c``];
*)

(* HOL4 ML code, not ported:
val iEval_def = bviSemTheory.evaluate_def;
*)

(* correctness of stubs *)

(* HOL4 ML code, not ported:
val bEvalOp_def = bvlSemTheory.do_app_def;
val iEvalOp_def = bviSemTheory.do_app_def;
*)
(* HOL4 ML code, not ported:
val evaluate_CopyGlobals_code = Q.GEN `ls` evaluate_CopyGlobals_code;
val _ = print "Proved evaluate_CopyGlobals_code\n";
*)

(* compiler correctness *)

(* HOL4 ML code, not ported:
val bEval_def = bvlSemTheory.evaluate_def;
val iEval_append = bviPropsTheory.evaluate_APPEND;
*)

(* HOL4 ML code, not ported:
val compile_string_thm = Q.prove(
  `∀str s ls vs.
   FLOOKUP s.refs ptr = SOME (ByteArray T ls) ∧ LENGTH vs + LENGTH str =
     LENGTH ls ⇒
   evaluate (MAPi (λn c. Op (MemOp UpdateByte) [Op (IntOp (Const (&ORD
     c))) []; compile_int (&(n + LENGTH vs)); Var 0]) str,
    RefPtr b ptr::env, s) = (Rval (REPLICATE (LENGTH str) Unit),
      s with refs := s.refs |+ (ptr, ByteArray T (TAKE (LENGTH vs) ls ++
        (MAP (n2w o ORD) str))))`,
  Induct \\ rw[evaluate_def,REPLICATE]
  >- (rw[state_component_equality]
      \\ match_mp_tac (GSYM FUPDATE_ELIM) \\ fs[FLOOKUP_DEF])
  \\ rw[Once evaluate_CONS]
  \\ reverse(rw[evaluate_def,do_app_def,do_app_aux_def
    ,backend_commonTheory.small_enough_int_def])
  >- ( qspec_then`h`strip_assume_tac ORD_BOUND \\ fs[] )
  \\ reverse(rw[bvlSemTheory.do_app_def,compile_int_thm
    ,EL_LENGTH_APPEND])
  >- (
    fs[] \\ first_x_assum(qspec_then`n2w (ORD h)`mp_tac)
    \\ simp[w2n_n2w,ORD_BOUND] )
  \\ simp[o_DEF,ADD1]
  \\ simp[bvl_to_bvi_with_refs,bvl_to_bvi_id]
  \\ qpat_abbrev_tac`ss = s with refs := _`
  \\ first_x_assum(qspec_then`ss`mp_tac)
  \\ simp[Abbr`ss`,FLOOKUP_UPDATE]
  \\ disch_then(qspec_then`ARB::vs`mp_tac)
  \\ rw[ADD1,state_component_equality]
  \\ rw[fmap_eq_flookup,FLOOKUP_UPDATE] \\ rw[]
  \\ rw[LIST_EQ_REWRITE]
  \\ Cases_on`x = LENGTH vs` \\
    simp[EL_APPEND1,EL_LUPDATE,EL_APPEND2,EL_TAKE]
  \\ Cases_on`x < LENGTH vs` \\ simp[EL_APPEND1,EL_TAKE,EL_LUPDATE]
  \\ simp[EL_TAKE,EL_APPEND2,o_DEF])
  |> Q.SPECL[`str`,`s`,`ls`,`[]`]
  |> SIMP_RULE(srw_ss())[]
  |> Q.GENL[`str`,`ls`,`ptr`,`s`,`env`]
  |> INST_TYPE[alpha|->``:'c``,beta|->``:'ffi``];
*)

(* HOL4 ML code, not ported:
val sorted_lt_append =
  Q.ISPEC`prim_rec$<`SORTED_APPEND
  |> SIMP_RULE std_ss [transitive_LESS]
*)

let in_ns_def = cake_define
  `in_ns k n <=> n MOD bvl_to_bvi_namespaces = k`;;

(* HOL4 ML code, not ported:
val ODD_num_stubs = EVAL``in_ns 0 num_stubs``;
*)

(* the compiled bvi Call handler post-processes its result, rejecting an
   escaping Ret; a mapped bvl handler result (raised values lifted
     through Exn)
   never raises a Ret, so the post-processing is the identity *)

(* HOL4 ML code, not ported:
fun note_tac s g = (print ("compile_exps_correct: " ^ s ^ "\n"); ALL_TAC
  g);
*)

(* HOL4 ML code, not ported:
val goal = ``
   λ(xs,env,s1).
   !n res s2 (t1:('c,'ffi) bviSem$state) n2 ys aux b1.
     (evaluate (xs,env,s1) = (res,s2)) /\ res <> Rerr(Rabort
       Rtype_error) /\
     (compile_exps n xs = (ys,aux,n2)) /\
     state_rel b1 s1 t1 /\
     state_ok s1 /\ EVERY (bv_ok s1.refs) env /\
     aux_code_installed (append aux) t1.code /\
     handle_ok xs /\ IS_SOME t1.global
     ==>
     ?t2 b2 c.
        (evaluate (ys,MAP (adjust_bv b2) env,inc_clock c t1) =
           (map_result (MAP (adjust_bv b2)) (λv. Exn (adjust_bv b2 v))
             res,t2)) /\
        state_rel b2 s2 t2 /\
        (MAP (adjust_bv b1) env = MAP (adjust_bv b2) env) /\
        (!a. a IN FDOM s1.refs ==> (b1 a = b2 a))``
*)

(* HOL4 ML code, not ported:
Resume compile_exps_correct[Op]:
  note_tac "compile_exps_Op" \\ REPEAT STRIP_TAC
  \\ full_simp_tac(srw_ss())[bEval_def,compile_exps_def,
        iEval_def,bEvery_def,handle_ok_def]
  \\ `?c1 aux1 n1. compile_exps n xs = (c1,aux1,n1)` by METIS_TAC [PAIR]
  \\ full_simp_tac(srw_ss())[LET_DEF] \\ SRW_TAC [] []
  \\ full_simp_tac(srw_ss())[PULL_FORALL]
  \\ `?res5 s5. evaluate (xs,env,s) = (res5,s5)` by METIS_TAC [PAIR]
  \\ full_simp_tac(srw_ss())[]
  \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `n`) \\ full_simp_tac(srw_ss())[]
  \\ reverse (Cases_on `res5`) \\ full_simp_tac(srw_ss())[] \\ SRW_TAC
    [] []
  \\ fs [] \\ first_x_assum old_drule \\ fs []
    THEN1 (
      REPEAT STRIP_TAC \\ IMP_RES_TAC compile_exps_LENGTH
      \\ full_simp_tac(srw_ss())[iEval_def]
      \\ Q.LIST_EXISTS_TAC [`t2`,`b2`] \\ full_simp_tac(srw_ss())[]
      \\ Cases_on`op = Install` THEN1
       (fs[compile_op_def]
        \\ qexists_tac`c` \\ simp[] \\ rw []
        \\ fs [evaluate_def])
      \\ Cases_on `op = ThunkOp ForceThunk`
      >- (
        gvs [compile_op_def]
        \\ qexists `c` \\ gvs []
        \\ gvs [evaluate_def])
      \\ Cases_on`op = MemOp (CopyByte T)`
      >- (note_tac "Op: CopyByte" \\
        fs[compile_op_def]
        \\ qexists_tac`c` \\ simp[]
        \\ rw[evaluate_APPEND,bviSemTheory.evaluate_def] )
      \\ Cases_on`(∃tag i. op = MemOp (MutCons tag i)) ∨
                  op = MemOp UpdateCons ∨ op = MemOp FinaliseCons`
      >- (gvs [compile_op_def]
          \\ qexists_tac `c` \\ gvs [bviSemTheory.evaluate_def])
      \\ fs []
      \\ cases_on_op `op`
      \\ fs[compile_op_def,iEval_def,compile_int_thm,iEval_append]
      \\ qexists_tac`c`>>simp[]>>
         every_case_tac \\
           full_simp_tac(srw_ss())[iEval_def,compile_int_thm]
      \\ imp_res_tac compile_exps_LENGTH
      \\ fs [NULL_EQ,LENGTH_NIL]
      \\ Cases_on `xs` \\ fs [bviSemTheory.evaluate_def])
    \\ Cases_on ‘op = ThunkOp ForceThunk’
    >- gvs [bvlSemTheory.do_app_def, AllCaseEqs()]
    \\ REPEAT STRIP_TAC \\ Cases_on `do_app op (REVERSE a) s5`
    \\ full_simp_tac(srw_ss())[]
    \\ TRY(
      qmatch_asmsub_abbrev_tac `do_app _ _ _ = Rerr _` >>
      srw_tac[][] >>
      CHANGED_TAC(imp_res_tac bvlPropsTheory.do_app_err) >>
      rveq >> fs[] >> fs[bvlSemTheory.do_app_def] >>
      simp[evaluate_def,compile_op_def] >>
      MAP_EVERY qexists_tac [`t2`,`b2`,`c`] >>
      simp[] >>
      fs[do_app_def,do_app_aux_def] >> rpt(PURE_FULL_CASE_TAC >> fs[] >>
        rveq) >>
      fs[bvlSemTheory.do_app_def] >> Cases_on `a` >> fs[] >>
      rpt(PURE_FULL_CASE_TAC >> fs[adjust_bv_def] >> rveq) >>
      fs[GSYM PULL_FORALL] >>
      imp_res_tac state_rel_FLOOKUP_byteArray >>
      fs[] >> rveq >> rfs[state_rel_def])
    \\ full_simp_tac(srw_ss())[GSYM PULL_FORALL]
    \\ Cases_on`a'`>>full_simp_tac(srw_ss())[]\\srw_tac[][]
    \\ Cases_on `op = Install` \\ full_simp_tac(srw_ss())[] THEN1 (
      rveq \\ fs [compile_op_def]
      \\ `LENGTH a = 2` by
       (fs [bvlSemTheory.do_app_def,bvlSemTheory.do_install_def,
            case_eq_thms,UNCURRY] \\ rveq \\ fs [SWAP_REVERSE_SYM])
      \\ imp_res_tac evaluate_IMP_LENGTH \\ fs []
      \\ fs [bvlSemTheory.do_app_def,bvlSemTheory.do_install_def,
             case_eq_thms,UNCURRY] \\ rveq
      \\ fs [SWAP_REVERSE_SYM] \\ rveq \\ fs []
      \\ CONV_TAC SWAP_EXISTS_CONV \\ Q.EXISTS_TAC `b2`
      \\ CONV_TAC SWAP_EXISTS_CONV
      \\ `lookup ListLength_location t2.code = SOME ListLength_code` by
              (fs [state_rel_def] \\ NO_TAC) \\ fs []
      \\ fs [EVAL ``ListLength_code``] \\ fs [GSYM (EVAL ``SND
        ListLength_code``)]
      \\ old_drule (GEN_ALL evaluate_ListLength_code)
      \\ fs [v_to_bytes_def,some_def]
      \\ rfs [MAP_Num_11,o_DEF] \\ rveq
      \\ disch_then (qspec_then `adjust_bv b2 v1` mp_tac) \\ fs []
      \\ simp [v_to_list_adjust]
      \\ disch_then (qspec_then `0` strip_assume_tac)
      \\ old_drule (GEN_ALL evaluate_ListLength_code)
      \\ fs [v_to_words_def,some_def]
      \\ rfs [MAP_Word_11,o_DEF] \\ rveq
      \\ disch_then (qspec_then `adjust_bv b2 v2` mp_tac) \\ fs []
      \\ simp [v_to_list_adjust]
      \\ disch_then (qspec_then `0` strip_assume_tac) \\ fs []
      \\ qexists_tac `c + c' + c'' + 2`
      \\ ntac 2 (pop_assum mp_tac)
      \\ old_drule bviPropsTheory.evaluate_add_clock
      \\ disch_then (qspec_then `c'+c''+2` assume_tac)
      \\ rpt strip_tac
      \\ old_drule bviPropsTheory.evaluate_add_clock
      \\ disch_then (qspec_then `c'+1` assume_tac)
      \\ fs [inc_clock_ADD]
      \\ fs [evaluate_def,EVAL ``bviSem$do_app (IntOp (Const 0)) []
        t2``,
             bvlSemTheory.find_code_def,dec_clock_inc_clock]
      \\ fs [do_install_def,do_app_def]
      \\ imp_res_tac IMP_v_to_bytes \\ fs []
      \\ imp_res_tac IMP_v_to_words \\ fs []
      \\ `t2.compile_oracle = state_co compile_inc s5.compile_oracle ∧
          s5.compile = state_cc compile_inc t2.compile`
              by fs [state_rel_def]
      \\ fs [state_co_def]
      \\ Cases_on `s5.compile_oracle 0` \\ fs []
      \\ PairCases_on `q` \\ fs []
      \\ qabbrev_tac `prog1 = (k,prog)::v7`
      \\ Cases_on `compile_inc q0 prog1` \\ fs [] \\ rveq
      \\ rename1 `compile_inc next1 prog1 = (next2,prog2)`
      \\ fs [state_cc_def,case_eq_thms] \\ rveq \\ fs [PULL_EXISTS]
      \\ simp [adjust_bv_def,shift_seq_def,UNCURRY]
      \\ Cases_on `shift_seq 1 s5.compile_oracle 0` \\ fs [] \\ rveq \\
        fs []
      \\ pop_assum mp_tac
      \\ simp [adjust_bv_def,shift_seq_def,UNCURRY]
      \\ fs [state_rel_def,lookup_union] \\ strip_tac
      \\ simp [GSYM PULL_EXISTS,state_co_def,UNCURRY,case_eq_thms]
      \\ qpat_x_assum `names_ok _ _ _` assume_tac
      \\ conj_tac THEN1
       (fs
         [v_to_bytes_def,v_to_list_adjust,o_DEF,adjust_bv_def,MAP_MAP_o,
            MAP_Num_11])
      \\ conj_asm1_tac THEN1
       (simp [IN_DISJOINT] \\ CCONTR_TAC \\ fs [] \\ fs [names_ok_def]
        \\ rfs [] \\ first_x_assum old_drule
        \\ impl_tac >-  (
          imp_res_tac compile_inc_next_range
          \\ pop_assum mp_tac \\ rw[] )
        \\ IF_CASES_TAC \\ fs []
        \\ imp_res_tac compile_inc_next_range \\ rfs [EVAL ``nss``]
        \\ `DISJOINT (domain s5.code) (set (MAP FST prog1))` by fs
          [Abbr`prog1`]
        \\ pop_assum mp_tac \\ rewrite_tac [IN_DISJOINT]
        \\ strip_tac \\ fs []
        \\ pop_assum (qspec_then `(x - num_stubs) DIV nss`
          strip_assume_tac)
        \\ fs [EVAL ``nss``])
      \\ conj_asm1_tac THEN1
       (rfs [names_ok_def]
        \\ imp_res_tac compile_inc_DISTINCT \\ rfs [Abbr`prog1`])
      \\ conj_tac THEN1
       (fs [compile_inc_def,compile_list_def,Abbr `prog1`]
        \\ PairCases_on `prog` \\ fs [compile_single_def]
        \\ rpt (pairarg_tac \\ fs []) \\ rveq \\ fs [])
      \\ fs [state_cc_def,state_co_def]
      \\ rfs [] \\ fs [FUN_EQ_THM,FORALL_PROD]
      \\ qpat_x_assum `!x. _ = _` (qspec_then `0` mp_tac) \\ fs []
      \\ strip_tac \\ fs []
      \\ conj_tac THEN1
       (fs [names_ok_def,domain_union] \\ rfs [] \\ rveq \\ fs []
        \\ old_drule (GEN_ALL compile_inc_next)
        \\ strip_tac \\ fs []
        \\ rpt strip_tac
        THEN1 (res_tac \\ fs [] \\ rw [] \\ fs [EVAL ``nss``])
        THEN1 (res_tac \\ fs [] \\ rw [] \\ fs [EVAL ``nss``])
        \\ fs [domain_fromAList]
        \\ old_drule (GEN_ALL compile_inc_next_range) \\ fs []
        \\ disch_then old_drule \\ fs []
        \\ rw [] \\ fs [] \\ gvs[Abbr‘prog1’])
      \\ reverse (rpt strip_tac) \\ rveq \\ fs []
      THEN1
       (first_x_assum old_drule \\ strip_tac
        \\ pairarg_tac \\ fs []
        \\ old_drule compile_exps_SING \\ strip_tac \\ fs [] \\ rveq
        \\ rename1 `compile_exps n6 [exp] = _`
        \\ qexists_tac `n6` \\ fs []
        \\ match_mp_tac aux_code_installed_subspt
        \\ asm_exists_tac \\ fs []
        \\ fs [subspt_lookup,lookup_union])
      \\ `lookup (num_stubs + name * nss) t2.code = NONE` by
       (fs [names_ok_def,domain_lookup,PULL_EXISTS]
        \\ Cases_on `lookup (num_stubs + name * nss) t2.code` \\ fs []
        \\ first_x_assum old_drule
        \\ fs [names_nss_DIV_nss,not_in_ns_1]) \\ fs []
      \\ fs [lookup_fromAList,compile_inc_def]
      \\ pairarg_tac \\ fs [] \\ rveq \\ fs []
      \\ old_drule compile_list_imp
      \\ disch_then old_drule \\ strip_tac
      \\ qexists_tac `n0` \\ fs []
      \\ conj_tac THEN1
       (match_mp_tac aux_code_installed_subspt
        \\ qexists_tac `(fromAList (append p1))`
        \\ reverse conj_tac THEN1
         (fs [subspt_lookup,lookup_union] \\ rw [] \\ simp
           [case_eq_thms]
          \\ fs [IN_DISJOINT]
          \\ rename1 `lookup kk _ = _`
          \\ first_x_assum (qspec_then `kk` mp_tac)
          \\ fs [lookup_fromAList] \\ imp_res_tac ALOOKUP_MEM
          \\ fs [domain_lookup]
          \\ Cases_on `lookup kk t2.code` \\ fs []
          \\ fs [MEM_MAP,FORALL_PROD] \\ PairCases_on `y` \\ metis_tac
            [])
        \\ match_mp_tac aux_code_installed_sublist \\ fs [])
      \\ imp_res_tac ALOOKUP_MEM
      \\ fs [names_ok_def]
      \\ qpat_x_assum `!n k. _` (qspec_then `0` mp_tac) \\ fs []
      \\ fs [EVERY_MEM,FORALL_PROD] \\ metis_tac[])
    \\ Cases_on `∃m. op = ThunkOp (AllocThunk m)` >- (
      rw [] \\ gvs []
      \\ gvs [compile_op_def, evaluate_def, AllCaseEqs(), PULL_EXISTS]
      \\ gvs [do_app_def, do_app_aux_def, AllCaseEqs(), PULL_EXISTS]
      \\ qabbrev_tac `b3 = ((LEAST ptr. ptr ∉ FDOM s5.refs) =+
           (LEAST ptr. ptr ∉ FDOM (bvi_to_bvl t2).refs)) b2`
      \\ qexistsl [`b3`, `c`] \\ gvs []
      \\ qabbrev_tac `x = (LEAST ptr. ptr ∉ FDOM s5.refs)`
      \\ qabbrev_tac `y = LEAST ptr. ptr ∉ FDOM (bvi_to_bvl t2).refs`
      \\ gvs []
      \\ `x ∉ FDOM s5.refs` by (
        `∃p. (\ptr. ptr ∉ FDOM s5.refs) p` by
          (rw [] \\ metis_tac [NUM_NOT_IN_FDOM])
        \\ imp_res_tac WhileTheory.LEAST_INTRO \\ gvs [])
      \\ `y ∉ FDOM t2.refs` by (
        `∃p. (\ptr. ptr ∉ FDOM t2.refs) p` by
          (rw [] \\ metis_tac [NUM_NOT_IN_FDOM])
        \\ imp_res_tac WhileTheory.LEAST_INTRO \\ gvs [])
      \\ gvs []
      \\ gvs [bvlSemTheory.do_app_def, AllCaseEqs(), PULL_EXISTS]
      \\ rw [adjust_bv_def]
      \\ `MAP (adjust_bv b3) env = MAP (adjust_bv b2) env` by (
        gvs [MAP_EQ_f] \\ rpt strip_tac
        \\ match_mp_tac (GEN_ALL bv_ok_IMP_adjust_bv_eq)
        \\ qexists_tac `s5.refs`
        \\ gvs [EVERY_MEM] \\ res_tac
        \\ imp_res_tac evaluate_refs_SUBSET
        \\ rpt strip_tac >- metis_tac [bv_ok_SUBSET_IMP]
        \\ qunabbrev_tac `b3` \\ gvs [APPLY_UPDATE_THM]
        \\ rw [] \\ gvs [])
      \\ `adjust_bv b2 v = adjust_bv b3 v` by (
        match_mp_tac (GEN_ALL bv_ok_IMP_adjust_bv_eq)
        \\ qexists `s5.refs`
        \\ imp_res_tac evaluate_ok \\ gvs []
        \\ qunabbrev_tac `b3` \\ gvs [APPLY_UPDATE_THM]
        \\ rw [] \\ gvs [])
      \\ gvs []
      \\ conj_tac >- (
        gvs [bad_thunk_update_def, oneline bvlSemTheory.dest_thunk_def,
             AllCaseEqs(), adjust_bv_def]
        \\ metis_tac [state_rel_FLOOKUP_valueArray,
          state_rel_FLOOKUP_byteArray,
                      state_rel_FLOOKUP_MutBlock])
      \\ conj_tac >- (qunabbrev_tac `b3` \\ rw [])
      \\ reverse conj_tac >- (
        rpt strip_tac \\ unabbrev_all_tac
        \\ gvs [APPLY_UPDATE_THM] \\ rw []
        \\ imp_res_tac evaluate_refs_SUBSET
        \\ gvs [SUBSET_DEF])
      \\ gvs [bvl_to_bvi_def, bvi_to_bvl_def]
      \\ qmatch_goalsub_abbrev_tac `state_rel _ _ tt`
      \\ `tt = t2 with refs := t2.refs |+ (b3 x,Thunk m (adjust_bv b2
        v))` by (
        unabbrev_all_tac \\ gvs [state_component_equality])
      \\ simp [Abbr `tt`, Abbr `b3`]
      \\ irule state_rel_add_thunk \\ gvs []
      \\ imp_res_tac evaluate_ok)
    \\ Cases_on `∃m. op = ThunkOp (UpdateThunk m)` \\ gvs [] >- (
      rw [] \\ gvs []
      \\ gvs [compile_op_def, evaluate_def, AllCaseEqs(), PULL_EXISTS]
      \\ gvs [do_app_def, do_app_aux_def, AllCaseEqs(), PULL_EXISTS]
      \\ goal_assum old_drule
      \\ gvs [bvlSemTheory.do_app_def, AllCaseEqs(), PULL_EXISTS]
      \\ Cases_on `a` \\ gvs [adjust_bv_def]
      \\ drule_all state_rel_FLOOKUP_Thunk \\ rw []
      >- (
        gvs [bad_thunk_update_def, oneline bvlSemTheory.dest_thunk_def,
             AllCaseEqs(), adjust_bv_def]
        \\ metis_tac [state_rel_FLOOKUP_valueArray,
          state_rel_FLOOKUP_byteArray,
                      state_rel_FLOOKUP_MutBlock])
      \\ simp [bvl_to_bvi_def, bvi_to_bvl_def]
      \\ qmatch_goalsub_abbrev_tac `state_rel _ _ tt`
      \\ `tt = t2 with refs := t2.refs |+ (b2 ptr,Thunk m (adjust_bv b2
        h))` by (
        unabbrev_all_tac \\ gvs [state_component_equality])
      \\ qunabbrev_tac `tt` \\ gvs []
      \\ irule state_rel_update_thunk \\ gvs []
      \\ imp_res_tac evaluate_ok \\ gvs [FLOOKUP_DEF])
    \\ `∀thunk_op. op ≠ ThunkOp thunk_op` by (
      qx_gen_tac `t` \\ Cases_on `t` \\ gvs [])
    \\ gvs []
    \\ Cases_on `?i. op = IntOp (Const i)` \\ full_simp_tac(srw_ss())[]
      THEN1
     (note_tac "Op: Const" \\ CONV_TAC SWAP_EXISTS_CONV \\ Q.EXISTS_TAC
       `b2`
      \\ CONV_TAC SWAP_EXISTS_CONV \\ Q.EXISTS_TAC `c`
      \\ full_simp_tac(srw_ss())[] \\
        full_simp_tac(srw_ss())[compile_op_def]
      \\ qpat_x_assum `do_app _ _  _ = _` mp_tac
      \\ disch_then (mp_tac o
        SRULE[AllCaseEqs(),bEvalOp_def,iEval_def,oneline
        do_int_app_def])
      \\ rw[] \\ fs[] \\ Cases_on `c1`
      \\ full_simp_tac(srw_ss())[compile_int_thm,bEvalOp_def,iEval_def]
        \\ rveq
      \\ full_simp_tac(srw_ss())[iEval_def,iEvalOp_def,oneline
        do_int_app_def]
      \\ full_simp_tac(srw_ss())[EVAL ``do_app_aux (IntOp (Const 0)) []
        t2``]
      \\ SRW_TAC [] [adjust_bv_def])
    \\ Cases_on `∃n. op = Label n` THEN1
     (note_tac "Op: Label" \\
      fs[compile_op_def,evaluate_def,case_eq_thms] \\ rveq \\
      fs[do_app_def,do_app_aux_def,bvlSemTheory.do_app_def,
         case_eq_thms,bool_case_eq] \\
      CONV_TAC SWAP_EXISTS_CONV \\ qexists_tac`b2` \\
      CONV_TAC SWAP_EXISTS_CONV \\ qexists_tac`c` \\ simp[] \\ rveq \\
      simp[adjust_bv_def]
      \\ fs[state_rel_def,domain_lookup]
      \\ imp_res_tac evaluate_mono \\ fs [subspt_lookup,domain_lookup]
      \\ res_tac \\ fs []
      \\ Cases_on`v` \\ res_tac
      \\ pairarg_tac \\ fs[])
    \\ Cases_on `?i. op = BlockOp (FromList i)` \\
      full_simp_tac(srw_ss())[] THEN1
     (note_tac "Op: FromList" \\ fs [compile_op_def] \\ rveq
      \\ fs [bvlSemTheory.do_app_def]
      \\ Cases_on `REVERSE a` \\ fs [] \\ Cases_on `t` \\ fs [] \\ rveq
        \\ fs []
      \\ Cases_on `v_to_list h` \\ fs []
      \\ old_drule evaluate_IMP_LENGTH \\ rveq
      \\ Cases_on `c1` \\ fs [LENGTH_NIL]
      \\ strip_tac \\ rveq \\ fs []
      \\ qexists_tac `t2`
      \\ qexists_tac `b2`
      \\ `lookup ListLength_location t2.code = SOME ListLength_code` by
              (fs [state_rel_def] \\ NO_TAC) \\ fs []
      \\ fs [EVAL ``ListLength_code``] \\ fs [GSYM (EVAL ``SND
        ListLength_code``)]
      \\ `v_to_list (adjust_bv b2 h) = SOME (MAP (adjust_bv b2) x)` by
             fs [v_to_list_adjust]
      \\ old_drule evaluate_ListLength_code
      \\ disch_then old_drule \\ fs []
      \\ disch_then (qspec_then `0` strip_assume_tac)
      \\ qexists_tac `c+1+c'`
      \\ fs [bviSemTheory.evaluate_def,EVAL ``bviSem$do_app (IntOp
        (Const 0)) [] t2``]
      \\ qpat_assum `evaluate ([h'],_) = _` assume_tac
      \\ old_drule evaluate_add_clock \\ fs []
      \\ disch_then (qspec_then `1+c'` assume_tac)
      \\ fs [inc_clock_ADD]
      \\ fs [find_code_def]
      \\ `dec_clock 1 (inc_clock (c' + 1) t2) = inc_clock c' t2` by
            (fs [dec_clock_def,inc_clock_def,
                 bviSemTheory.state_component_equality] \\ NO_TAC)
      \\ fs [] \\ fs
        [bviSemTheory.do_app_def,bviSemTheory.do_app_aux_def]
      \\ fs [adjust_bv_def] \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ fs [])
    \\ Cases_on `op = MemOp ToListByte` \\ full_simp_tac(srw_ss())[]
      THEN1
     (note_tac "Op: ToListByte" \\ fs [compile_op_def] \\ rveq
      \\ fs [bvlSemTheory.do_app_def]
      \\ Cases_on `REVERSE a` \\ fs [] \\ Cases_on `t` \\ fs [] \\ rveq
        \\ fs []
      \\ Cases_on `h` \\ fs [option_case_eq] \\ Cases_on `v1` \\ fs []
        \\ rveq \\ fs []
      \\ old_drule evaluate_IMP_LENGTH \\ rveq
      \\ Cases_on `c1` \\ fs [LENGTH_NIL]
      \\ strip_tac \\ rveq \\ fs []
      \\ qexists_tac `t2`
      \\ qexists_tac `b2`
      \\ `lookup ToListByte_location t2.code = SOME (3,SND
        ToListByte_code)` by
              (fs [state_rel_def] \\ EVAL_TAC) \\ fs []
      \\ old_drule (GEN_ALL evaluate_ToListByte_code)
      \\ `FLOOKUP t2.refs (b2 n') = SOME (ByteArray b' l)` by
          (fs [state_rel_def]
          \\ ntac 3 (qpat_x_assum `!x. _` kall_tac)
          \\ first_x_assum (qspec_then `n'` mp_tac) \\ fs [])
      \\ disch_then (qspecl_then [`b'`,`b`,`l`,`[]`,`b2 n'`] mp_tac) \\
        fs [] \\ strip_tac
      \\ fs [adjust_bv_def] \\ pop_assum mp_tac
      \\ old_drule evaluate_add_clock \\ simp []
      \\ disch_then (qspec_then `c'+1` assume_tac) \\ strip_tac
      \\ fs [inc_clock_def]
      \\ qexists_tac `c' + c + 1` \\ fs
        [evaluate_def,do_app_def,find_code_def,
           do_app_aux_def,bvl_to_bvi_def,bvi_to_bvl_def
             ,bvlSemTheory.do_app_def]
      \\ Cases_on `ToListByte_code` \\ fs [] \\ rveq \\ fs
        [dec_clock_def]
      \\ fs [list_to_v_def,EVAL ``nil_tag``]
      \\ `t2 with <|refs := t2.refs; clock := c' + t2.clock; ffi :=
        t2.ffi|> =
          t2 with clock := c' + t2.clock` by fs
            [state_component_equality] \\ fs []
      \\ conj_tac
      THEN1 (qid_spec_tac `l` \\ Induct \\ fs
        [list_to_v_def,adjust_bv_def])
      \\ fs
        [FLOOKUP_EXT,state_component_equality,FLOOKUP_UPDATE,FUN_EQ_THM]
      \\ rw [] \\ fs [])
    \\ Cases_on `op = MemOp Ref` \\ full_simp_tac(srw_ss())[] THEN1
     (note_tac "Op: Ref" \\ rw [] \\
      full_simp_tac(srw_ss())[compile_op_def,iEval_def]
      \\ Q.ABBREV_TAC `b3 = ((LEAST ptr. ptr NOTIN FDOM s5.refs) =+
           (LEAST ptr. ptr NOTIN FDOM (bvi_to_bvl t2).refs)) b2`
      \\ CONV_TAC SWAP_EXISTS_CONV \\ Q.EXISTS_TAC `b3`
      \\ CONV_TAC SWAP_EXISTS_CONV \\ Q.EXISTS_TAC `c`
      \\ full_simp_tac(srw_ss())[do_app_Ref]
      \\ Q.ABBREV_TAC `x = (LEAST ptr. ptr NOTIN FDOM s5.refs)`
      \\ Q.ABBREV_TAC `y = LEAST ptr. ptr NOTIN FDOM (bvi_to_bvl
        t2).refs`
      \\ `~(x IN FDOM s5.refs)` by
       (`?p. (\ptr. ptr NOTIN FDOM s5.refs) p` by
          (SIMP_TAC std_ss [] \\ METIS_TAC [NUM_NOT_IN_FDOM])
        \\ IMP_RES_TAC WhileTheory.LEAST_INTRO \\
          full_simp_tac(srw_ss())[]
        \\ REV_FULL_SIMP_TAC std_ss [])
      \\ `~(y IN FDOM t2.refs)` by
       (`?p. (\ptr. ptr NOTIN FDOM t2.refs) p` by
          (SIMP_TAC std_ss [] \\ METIS_TAC [NUM_NOT_IN_FDOM])
        \\ IMP_RES_TAC WhileTheory.LEAST_INTRO
        \\ full_simp_tac(srw_ss())[bvi_to_bvl_def]
        \\ REV_FULL_SIMP_TAC (srw_ss()) [bvi_to_bvl_def])
      \\ full_simp_tac(srw_ss())[]
      \\ SRW_TAC [] [adjust_bv_def]
      \\ `MAP (adjust_bv b3) env = MAP (adjust_bv b2) env` by
       (full_simp_tac(srw_ss())[MAP_EQ_f] \\ REPEAT STRIP_TAC
        \\ MATCH_MP_TAC (GEN_ALL bv_ok_IMP_adjust_bv_eq)
        \\ qexists_tac `s5.refs`
        \\ full_simp_tac(srw_ss())[EVERY_MEM] \\ RES_TAC
        \\ IMP_RES_TAC evaluate_refs_SUBSET
        \\ REPEAT STRIP_TAC THEN1 METIS_TAC [bv_ok_SUBSET_IMP]
        \\ Q.UNABBREV_TAC `b3` \\
          full_simp_tac(srw_ss())[APPLY_UPDATE_THM]
        \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[]) \\ fs []
      \\ `MAP (adjust_bv b3) a = MAP (adjust_bv b2) a` by
       (full_simp_tac(srw_ss())[MAP_EQ_f] \\ REPEAT STRIP_TAC
        \\ MATCH_MP_TAC (GEN_ALL bv_ok_IMP_adjust_bv_eq)
        \\ qexists_tac `s5.refs`
        \\ IMP_RES_TAC evaluate_ok \\ REV_FULL_SIMP_TAC std_ss [] \\
          full_simp_tac(srw_ss())[]
        \\ full_simp_tac(srw_ss())[EVERY_MEM] \\ RES_TAC
        \\ Q.UNABBREV_TAC `b3` \\
          full_simp_tac(srw_ss())[APPLY_UPDATE_THM]
        \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[])
      \\ `MAP (OPTION_MAP (adjust_bv b2)) s5.globals =
          MAP (OPTION_MAP (adjust_bv b3)) s5.globals` by
       (full_simp_tac(srw_ss())[MAP_EQ_f] \\ REPEAT STRIP_TAC
        \\ Cases_on `e` \\ full_simp_tac(srw_ss())[]
        \\ MATCH_MP_TAC (GEN_ALL bv_ok_IMP_adjust_bv_eq)
        \\ qexists_tac `s5.refs`
        \\ IMP_RES_TAC evaluate_ok \\ REV_FULL_SIMP_TAC std_ss [] \\
          full_simp_tac(srw_ss())[]
        \\ full_simp_tac(srw_ss())[state_ok_def,EVERY_MEM] \\ RES_TAC \\
          full_simp_tac(srw_ss())[]
        \\ Q.UNABBREV_TAC `b3` \\
          full_simp_tac(srw_ss())[APPLY_UPDATE_THM]
        \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[])
      \\ full_simp_tac(srw_ss())[] \\ STRIP_TAC
      THEN1
        (UNABBREV_ALL_TAC \\ full_simp_tac(srw_ss())[APPLY_UPDATE_THM]
         \\ fs [bvlSemTheory.do_app_def] \\ every_case_tac \\ fs []
         \\ rveq \\ fs [adjust_bv_def,APPLY_UPDATE_THM])
      \\ reverse STRIP_TAC THEN1
       (REPEAT STRIP_TAC \\ UNABBREV_ALL_TAC
        \\ full_simp_tac(srw_ss())[APPLY_UPDATE_THM]
        \\ SRW_TAC [] []
        \\ IMP_RES_TAC evaluate_refs_SUBSET
        \\ full_simp_tac(srw_ss())[SUBSET_DEF] \\ RES_TAC)
      \\ simp[bvl_to_bvi_with_refs,bvl_to_bvi_id]
      \\ full_simp_tac(srw_ss())[state_rel_def,bvl_to_bvi_def,
            bvi_to_bvl_def,FLOOKUP_UPDATE]
      \\ STRIP_TAC
      \\ fs [bvl_do_app_Ref] \\ rveq
      THEN1 (Q.UNABBREV_TAC `b3` \\ fs []
             \\ MATCH_MP_TAC INJ_EXTEND \\ full_simp_tac(srw_ss())[])
      \\ srw_tac[][MAP_REVERSE] \\ full_simp_tac(srw_ss())[]
      \\ TRY ( qexists_tac`z`>>simp[]>>
        simp[GSYM MAP_MAP_o] >> srw_tac[][] >>
        simp[Abbr`b3`,APPLY_UPDATE_THM] >> srw_tac[][] >> NO_TAC)
      \\ TRY ( full_simp_tac(srw_ss())[Abbr`b3`,APPLY_UPDATE_THM] \\
        NO_TAC)
      \\ TRY ( simp[Abbr`b3`,APPLY_UPDATE_THM] >> srw_tac[][] >> NO_TAC)
      \\ TRY ( full_simp_tac(srw_ss())[FLOOKUP_DEF] >> NO_TAC)
      \\ fs [FLOOKUP_UPDATE] \\ rw [] \\ fs [MAP_REVERSE]
      \\ Cases_on `FLOOKUP s5.refs k = NONE`
      \\ full_simp_tac(srw_ss())[rich_listTheory.MAP_REVERSE]
      \\ (`b3 k <> y` by
       (full_simp_tac(srw_ss())[] \\ Q.UNABBREV_TAC `b3`
        \\ full_simp_tac(srw_ss())[APPLY_UPDATE_THM,FLOOKUP_DEF]
        \\ full_simp_tac(srw_ss())[INJ_DEF] \\ RES_TAC \\ REPEAT
          STRIP_TAC
        \\ full_simp_tac(srw_ss())[] \\ NO_TAC))
      \\ TRY (Q.UNABBREV_TAC `b3` \\
        full_simp_tac(srw_ss())[APPLY_UPDATE_THM]
           \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[] \\ rfs [] \\
             NO_TAC)
      \\ (`b3 k = b2 k` by
           (Q.UNABBREV_TAC `b3`
            \\ full_simp_tac(srw_ss())[APPLY_UPDATE_THM,FLOOKUP_DEF] \\
              NO_TAC))
      THEN1 ( full_simp_tac(srw_ss())[FLOOKUP_DEF] >> METIS_TAC[INJ_DEF]
        )
      \\ full_simp_tac(srw_ss())[]
      \\ Cases_on `FLOOKUP s5.refs k` \\ full_simp_tac(srw_ss())[]
      \\ ntac 3 (Q.PAT_X_ASSUM `!k. bbb` MP_TAC)
      \\ Q.PAT_X_ASSUM `!k. bbb` (MP_TAC o Q.SPEC `k`) \\
        full_simp_tac(srw_ss())[]
      \\ Cases_on `x'` \\ full_simp_tac(srw_ss())[] \\ REPEAT STRIP_TAC
      \\ full_simp_tac(srw_ss())[MAP_EQ_f] \\ REPEAT STRIP_TAC
      \\ MATCH_MP_TAC (GEN_ALL bv_ok_IMP_adjust_bv_eq)
      \\ qexists_tac `s5.refs`
      \\ IMP_RES_TAC evaluate_ok \\ REV_FULL_SIMP_TAC std_ss []
      \\ full_simp_tac(srw_ss())[]
      \\ full_simp_tac(srw_ss())[state_ok_def]
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `k`) \\
        full_simp_tac(srw_ss())[]
      \\ full_simp_tac(srw_ss())[EVERY_MEM] \\ REPEAT STRIP_TAC
      \\ Q.UNABBREV_TAC `b3` \\
        full_simp_tac(srw_ss())[APPLY_UPDATE_THM]
      \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[])
    \\ Cases_on `op = MemOp RefArray` \\ full_simp_tac(srw_ss())[] THEN1
     (note_tac "Op: RefArray" \\
      full_simp_tac(srw_ss())[compile_op_def,iEval_def]
      \\ Q.ABBREV_TAC `b3 = ((LEAST ptr. ptr NOTIN FDOM s5.refs) =+
           (LEAST ptr. ptr NOTIN FDOM (bvi_to_bvl t2).refs)) b2`
      \\ CONV_TAC SWAP_EXISTS_CONV \\ Q.EXISTS_TAC `b3`
      \\ CONV_TAC SWAP_EXISTS_CONV \\ Q.EXISTS_TAC `c`
      \\ full_simp_tac(srw_ss())[iEvalOp_def,do_app_aux_def,bEvalOp_def
        ,LET_DEF]
      \\ Q.ABBREV_TAC `x = (LEAST ptr. ptr NOTIN FDOM s5.refs)`
      \\ Q.ABBREV_TAC `y = LEAST ptr. ptr NOTIN FDOM (bvi_to_bvl
        t2).refs`
      \\ `~(x IN FDOM s5.refs)` by
       (`?p. (\ptr. ptr NOTIN FDOM s5.refs) p` by
          (SIMP_TAC std_ss [] \\ METIS_TAC [NUM_NOT_IN_FDOM])
        \\ IMP_RES_TAC WhileTheory.LEAST_INTRO \\
          full_simp_tac(srw_ss())[]
        \\ REV_FULL_SIMP_TAC std_ss [])
      \\ `~(y IN FDOM t2.refs)` by
       (`?p. (\ptr. ptr NOTIN FDOM t2.refs) p` by
          (SIMP_TAC std_ss [] \\ METIS_TAC [NUM_NOT_IN_FDOM])
        \\ IMP_RES_TAC WhileTheory.LEAST_INTRO
        \\ full_simp_tac(srw_ss())[bvi_to_bvl_def]
        \\ REV_FULL_SIMP_TAC (srw_ss()) [bvi_to_bvl_def])
      \\ full_simp_tac(srw_ss())[]
      \\ SRW_TAC [] [adjust_bv_def]
      \\ `MAP (adjust_bv b3) env = MAP (adjust_bv b2) env` by
       (full_simp_tac(srw_ss())[MAP_EQ_f] \\ REPEAT STRIP_TAC
        \\ MATCH_MP_TAC (GEN_ALL bv_ok_IMP_adjust_bv_eq) \\ qexists_tac
          `s5.refs`
        \\ full_simp_tac(srw_ss())[EVERY_MEM] \\ RES_TAC
        \\ IMP_RES_TAC evaluate_refs_SUBSET
        \\ REPEAT STRIP_TAC THEN1 METIS_TAC [bv_ok_SUBSET_IMP]
        \\ Q.UNABBREV_TAC `b3` \\
          full_simp_tac(srw_ss())[APPLY_UPDATE_THM]
        \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[])
      \\ `MAP (adjust_bv b3) a = MAP (adjust_bv b2) a` by
       (full_simp_tac(srw_ss())[MAP_EQ_f] \\ REPEAT STRIP_TAC
        \\ MATCH_MP_TAC (GEN_ALL bv_ok_IMP_adjust_bv_eq) \\ qexists_tac
          `s5.refs`
        \\ IMP_RES_TAC evaluate_ok \\ REV_FULL_SIMP_TAC std_ss []
        \\ full_simp_tac(srw_ss())[]
        \\ full_simp_tac(srw_ss())[EVERY_MEM] \\ RES_TAC
        \\ Q.UNABBREV_TAC `b3` \\
          full_simp_tac(srw_ss())[APPLY_UPDATE_THM]
        \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[])
      \\ `MAP (OPTION_MAP (adjust_bv b2)) s5.globals =
          MAP (OPTION_MAP (adjust_bv b3)) s5.globals` by
       (full_simp_tac(srw_ss())[MAP_EQ_f] \\ REPEAT STRIP_TAC
        \\ Cases_on `e` \\ full_simp_tac(srw_ss())[]
        \\ MATCH_MP_TAC (GEN_ALL bv_ok_IMP_adjust_bv_eq) \\ qexists_tac
          `s5.refs`
        \\ IMP_RES_TAC evaluate_ok \\ REV_FULL_SIMP_TAC std_ss [] \\
          full_simp_tac(srw_ss())[]
        \\ full_simp_tac(srw_ss())[state_ok_def,EVERY_MEM] \\ RES_TAC \\
          full_simp_tac(srw_ss())[]
        \\ Q.UNABBREV_TAC `b3` \\
          full_simp_tac(srw_ss())[APPLY_UPDATE_THM]
        \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[])
      \\ full_simp_tac(srw_ss())[]
      \\ Cases_on`REVERSE a`>>full_simp_tac(srw_ss())[]
      \\ Cases_on`t`>>full_simp_tac(srw_ss())[]
      \\ Cases_on`h`>>full_simp_tac(srw_ss())[]
      \\ Cases_on`t'`>>full_simp_tac(srw_ss())[]
      \\ Cases_on`0 ≤ i` >>full_simp_tac(srw_ss())[]
      \\ Cases_on`a`>>full_simp_tac(srw_ss())[adjust_bv_def]
      \\ STRIP_TAC THEN1 (
        rpt var_eq_tac >>
        simp[Abbr`b3`,adjust_bv_def,APPLY_UPDATE_THM] )
      \\ reverse STRIP_TAC THEN1
       (REPEAT STRIP_TAC \\ UNABBREV_ALL_TAC \\
         full_simp_tac(srw_ss())[APPLY_UPDATE_THM]
        \\ SRW_TAC [] []
        \\ IMP_RES_TAC evaluate_refs_SUBSET \\
          full_simp_tac(srw_ss())[SUBSET_DEF] \\ RES_TAC)
      \\ simp[bvl_to_bvi_with_refs,bvl_to_bvi_id]
      \\ full_simp_tac(srw_ss())[state_rel_def,bvl_to_bvi_def
        ,bvi_to_bvl_def,FLOOKUP_UPDATE]
      \\ rpt var_eq_tac \\ simp[]
      \\ STRIP_TAC
      THEN1 (Q.UNABBREV_TAC `b3` \\ MATCH_MP_TAC INJ_EXTEND \\
        full_simp_tac(srw_ss())[])
      \\ simp[FLOOKUP_UPDATE]
      \\ srw_tac[][MAP_REVERSE] \\ full_simp_tac(srw_ss())[]
      \\ TRY ( full_simp_tac(srw_ss())[Abbr`b3`,APPLY_UPDATE_THM] \\
        NO_TAC)
      \\ TRY ( simp[Abbr`b3`,APPLY_UPDATE_THM] >> srw_tac[][] >> NO_TAC)
      \\ TRY ( full_simp_tac(srw_ss())[FLOOKUP_DEF] >> NO_TAC)
      \\ TRY (
        qexists_tac`z`>>simp[]>>
        simp[GSYM MAP_MAP_o] >> srw_tac[][] >>
        simp[Abbr`b3`,APPLY_UPDATE_THM] >> srw_tac[][] >> NO_TAC)
      \\ simp[map_replicate]
      \\ Cases_on `FLOOKUP s5.refs k = NONE` \\
        full_simp_tac(srw_ss())[rich_listTheory.MAP_REVERSE]
      \\ (`b3 k <> y` by
       (full_simp_tac(srw_ss())[] \\ Q.UNABBREV_TAC `b3` \\
         full_simp_tac(srw_ss())[APPLY_UPDATE_THM,FLOOKUP_DEF]
        \\ full_simp_tac(srw_ss())[INJ_DEF] \\ RES_TAC \\ REPEAT
          STRIP_TAC \\ full_simp_tac(srw_ss())[]))
      \\ (`b3 k = b2 k` by (Q.UNABBREV_TAC `b3` \\
        full_simp_tac(srw_ss())[APPLY_UPDATE_THM,FLOOKUP_DEF]))
      THEN1 ( full_simp_tac(srw_ss())[FLOOKUP_DEF] >> METIS_TAC[INJ_DEF]
        )
      \\ full_simp_tac(srw_ss())[] \\ Cases_on `FLOOKUP s5.refs k` \\
        full_simp_tac(srw_ss())[]
      \\ ntac 3 (Q.PAT_X_ASSUM `!k. bbb` MP_TAC)
      \\ Q.PAT_X_ASSUM `!k. bbb` (MP_TAC o Q.SPEC `k`) \\
        full_simp_tac(srw_ss())[]
      \\ Cases_on `x'` \\ full_simp_tac(srw_ss())[] \\ REPEAT STRIP_TAC
      \\ full_simp_tac(srw_ss())[MAP_EQ_f] \\ REPEAT STRIP_TAC
      \\ MATCH_MP_TAC (GEN_ALL bv_ok_IMP_adjust_bv_eq) \\ qexists_tac
        `s5.refs`
      \\ IMP_RES_TAC evaluate_ok \\ REV_FULL_SIMP_TAC std_ss [] \\
        full_simp_tac(srw_ss())[]
      \\ full_simp_tac(srw_ss())[state_ok_def]
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `k`) \\
        full_simp_tac(srw_ss())[]
      \\ full_simp_tac(srw_ss())[EVERY_MEM] \\ REPEAT STRIP_TAC
      \\ Q.UNABBREV_TAC `b3` \\
        full_simp_tac(srw_ss())[APPLY_UPDATE_THM]
      \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[])
    \\ Cases_on`∃flag. op = MemOp (RefByte flag)` \\
      full_simp_tac(srw_ss())[] THEN1
     (note_tac "RefByte" \\
       full_simp_tac(srw_ss())[compile_op_def,iEval_def]
      \\ Q.ABBREV_TAC `b3 = ((LEAST ptr. ptr NOTIN FDOM s5.refs) =+
           (LEAST ptr. ptr NOTIN FDOM (bvi_to_bvl t2).refs)) b2`
      \\ CONV_TAC SWAP_EXISTS_CONV \\ Q.EXISTS_TAC `b3`
      \\ CONV_TAC SWAP_EXISTS_CONV \\ Q.EXISTS_TAC `c`
      \\ full_simp_tac(srw_ss())[iEvalOp_def,do_app_aux_def,bEvalOp_def
        ,LET_DEF]
      \\ Q.ABBREV_TAC `x = (LEAST ptr. ptr NOTIN FDOM s5.refs)`
      \\ Q.ABBREV_TAC `y = LEAST ptr. ptr NOTIN FDOM (bvi_to_bvl
        t2).refs`
      \\ `~(x IN FDOM s5.refs)` by
       (`?p. (\ptr. ptr NOTIN FDOM s5.refs) p` by
          (SIMP_TAC std_ss [] \\ METIS_TAC [NUM_NOT_IN_FDOM])
        \\ IMP_RES_TAC WhileTheory.LEAST_INTRO \\
          full_simp_tac(srw_ss())[]
        \\ REV_FULL_SIMP_TAC std_ss [])
      \\ `~(y IN FDOM t2.refs)` by
       (`?p. (\ptr. ptr NOTIN FDOM t2.refs) p` by
          (SIMP_TAC std_ss [] \\ METIS_TAC [NUM_NOT_IN_FDOM])
        \\ IMP_RES_TAC WhileTheory.LEAST_INTRO
        \\ full_simp_tac(srw_ss())[bvi_to_bvl_def]
        \\ REV_FULL_SIMP_TAC (srw_ss()) [bvi_to_bvl_def])
      \\ full_simp_tac(srw_ss())[]
      \\ SRW_TAC [] [adjust_bv_def]
      \\ `MAP (adjust_bv b3) env = MAP (adjust_bv b2) env` by
       (full_simp_tac(srw_ss())[MAP_EQ_f] \\ REPEAT STRIP_TAC
        \\ MATCH_MP_TAC (GEN_ALL bv_ok_IMP_adjust_bv_eq) \\ qexists_tac
          `s5.refs`
        \\ full_simp_tac(srw_ss())[EVERY_MEM] \\ RES_TAC
        \\ IMP_RES_TAC evaluate_refs_SUBSET
        \\ REPEAT STRIP_TAC THEN1 METIS_TAC [bv_ok_SUBSET_IMP]
        \\ Q.UNABBREV_TAC `b3` \\
          full_simp_tac(srw_ss())[APPLY_UPDATE_THM]
        \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[])
      \\ `MAP (adjust_bv b3) a = MAP (adjust_bv b2) a` by
       (full_simp_tac(srw_ss())[MAP_EQ_f] \\ REPEAT STRIP_TAC
        \\ MATCH_MP_TAC (GEN_ALL bv_ok_IMP_adjust_bv_eq) \\ qexists_tac
          `s5.refs`
        \\ IMP_RES_TAC evaluate_ok \\ REV_FULL_SIMP_TAC std_ss []
        \\ full_simp_tac(srw_ss())[]
        \\ full_simp_tac(srw_ss())[EVERY_MEM] \\ RES_TAC
        \\ Q.UNABBREV_TAC `b3` \\
          full_simp_tac(srw_ss())[APPLY_UPDATE_THM]
        \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[])
      \\ `MAP (OPTION_MAP (adjust_bv b2)) s5.globals =
          MAP (OPTION_MAP (adjust_bv b3)) s5.globals` by
       (full_simp_tac(srw_ss())[MAP_EQ_f] \\ REPEAT STRIP_TAC
        \\ Cases_on `e` \\ full_simp_tac(srw_ss())[]
        \\ MATCH_MP_TAC (GEN_ALL bv_ok_IMP_adjust_bv_eq) \\ qexists_tac
          `s5.refs`
        \\ IMP_RES_TAC evaluate_ok \\ REV_FULL_SIMP_TAC std_ss []
        \\ full_simp_tac(srw_ss())[]
        \\ full_simp_tac(srw_ss())[state_ok_def,EVERY_MEM]
        \\ RES_TAC \\ full_simp_tac(srw_ss())[]
        \\ Q.UNABBREV_TAC `b3` \\
          full_simp_tac(srw_ss())[APPLY_UPDATE_THM]
        \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[])
      \\ full_simp_tac(srw_ss())[]
      \\ Cases_on`REVERSE a`>>full_simp_tac(srw_ss())[]
      \\ Cases_on`t`>>full_simp_tac(srw_ss())[]
      \\ Cases_on`h'`>>full_simp_tac(srw_ss())[]
      \\ Cases_on`h`>>full_simp_tac(srw_ss())[]
      \\ Cases_on`t'`>>full_simp_tac(srw_ss())[]
      \\ qpat_x_assum`X = Rval Y`mp_tac
      \\ IF_CASES_TAC \\ full_simp_tac(srw_ss())[] \\ strip_tac \\ rpt
        var_eq_tac
      \\ Cases_on`a`>>full_simp_tac(srw_ss())[adjust_bv_def]
      \\ IF_CASES_TAC \\ fs[] \\ rveq \\ fs[adjust_bv_def]
      \\ STRIP_TAC THEN1 (
        rpt var_eq_tac >>
        simp[Abbr`b3`,adjust_bv_def,APPLY_UPDATE_THM] )
      \\ reverse STRIP_TAC THEN1
       (REPEAT STRIP_TAC \\ UNABBREV_ALL_TAC \\
         full_simp_tac(srw_ss())[APPLY_UPDATE_THM]
        \\ SRW_TAC [] []
        \\ IMP_RES_TAC evaluate_refs_SUBSET \\
          full_simp_tac(srw_ss())[SUBSET_DEF] \\ RES_TAC)
      \\ simp[bvl_to_bvi_with_refs,bvl_to_bvi_id]
      \\ full_simp_tac(srw_ss())[state_rel_def,bvl_to_bvi_def
        ,bvi_to_bvl_def,FLOOKUP_UPDATE]
      \\ rpt var_eq_tac \\ simp[]
      \\ STRIP_TAC
      THEN1 (Q.UNABBREV_TAC `b3` \\ MATCH_MP_TAC INJ_EXTEND \\
        full_simp_tac(srw_ss())[])
      \\ srw_tac[][MAP_REVERSE] \\ full_simp_tac(srw_ss())[]
      \\ TRY ( full_simp_tac(srw_ss())[Abbr`b3`,APPLY_UPDATE_THM] \\
        NO_TAC)
      \\ TRY ( simp[Abbr`b3`,APPLY_UPDATE_THM] >> srw_tac[][] >> NO_TAC)
      \\ TRY ( full_simp_tac(srw_ss())[FLOOKUP_DEF] >> NO_TAC)
      \\ TRY (
        qexists_tac`z`>>simp[]>>
        simp[GSYM MAP_MAP_o] >> srw_tac[][] >>
        simp[Abbr`b3`,APPLY_UPDATE_THM] >> srw_tac[][] >>
        NO_TAC)
      \\ TRY (
        qmatch_rename_tac`t2.global ≠ SOME p` >>
        full_simp_tac(srw_ss())[FLOOKUP_DEF] >> METIS_TAC[])
      \\ Cases_on `FLOOKUP s5.refs k = NONE` \\
        full_simp_tac(srw_ss())[rich_listTheory.MAP_REVERSE]
      \\ (`b3 k <> y` by
       (full_simp_tac(srw_ss())[] \\ Q.UNABBREV_TAC `b3` \\
         full_simp_tac(srw_ss())[APPLY_UPDATE_THM,FLOOKUP_DEF]
        \\ full_simp_tac(srw_ss())[INJ_DEF] \\ RES_TAC \\ REPEAT
          STRIP_TAC \\ full_simp_tac(srw_ss())[]))
      \\ (`b3 k = b2 k` by (Q.UNABBREV_TAC `b3` \\
        full_simp_tac(srw_ss())[APPLY_UPDATE_THM,FLOOKUP_DEF]))
      THEN1 ( full_simp_tac(srw_ss())[FLOOKUP_DEF] >> METIS_TAC[INJ_DEF]
        )
      \\ full_simp_tac(srw_ss())[] \\ Cases_on `FLOOKUP s5.refs k` \\
        full_simp_tac(srw_ss())[]
      \\ ntac 3 (Q.PAT_X_ASSUM `!k. bbb` MP_TAC)
      \\ Q.PAT_X_ASSUM `!k. bbb` (MP_TAC o Q.SPEC `k`) \\
        full_simp_tac(srw_ss())[]
      \\ Cases_on `x'` \\ full_simp_tac(srw_ss())[] \\ REPEAT STRIP_TAC
      \\ full_simp_tac(srw_ss())[MAP_EQ_f] \\ REPEAT STRIP_TAC
      \\ MATCH_MP_TAC (GEN_ALL bv_ok_IMP_adjust_bv_eq) \\ qexists_tac
        `s5.refs`
      \\ IMP_RES_TAC evaluate_ok \\ REV_FULL_SIMP_TAC std_ss []
      \\ full_simp_tac(srw_ss())[]
      \\ full_simp_tac(srw_ss())[state_ok_def]
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `k`) \\
        full_simp_tac(srw_ss())[]
      \\ full_simp_tac(srw_ss())[EVERY_MEM] \\ REPEAT STRIP_TAC
      \\ Q.UNABBREV_TAC `b3` \\
        full_simp_tac(srw_ss())[APPLY_UPDATE_THM]
      \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[])
    \\ Cases_on`∃n. op = GlobOp (Global n)` \\ full_simp_tac(srw_ss())[]
    >- (
      note_tac "Global" >> simp[compile_op_def] >>
      full_simp_tac(srw_ss())[bEvalOp_def] >>
      Cases_on`REVERSE a`>>full_simp_tac(srw_ss())[]
      >-
      (imp_res_tac evaluate_IMP_LENGTH >>
        full_simp_tac(srw_ss())[LENGTH_NIL] >> gvs [] >>
        simp[iEval_def,compile_int_thm] >>
        Q.LIST_EXISTS_TAC[`t2`,`b2`,`c`] >>
        simp[iEvalOp_def,do_app_aux_def] >>
        BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[] >>
        simp[bEvalOp_def] >>
        full_simp_tac(srw_ss())[closSemTheory.get_global_def] >>
        gvs [AllCaseEqs(),PULL_EXISTS] >>
        imp_res_tac bvlPropsTheory.evaluate_IMP_LENGTH >>
        full_simp_tac(srw_ss())[LENGTH_NIL] >>
        full_simp_tac(srw_ss())[bEval_def] >> rpt var_eq_tac >>
        full_simp_tac(srw_ss())[iEval_def] >> rpt var_eq_tac >>
        last_x_assum mp_tac >>
        simp[Once state_rel_def] >> strip_tac >>
        simp[LENGTH_REPLICATE,ADD1] >>
        simp[EL_CONS,PRE_SUB1,GSYM ADD1] >>
        simp[EL_APPEND1,EL_MAP,miscTheory.the_def,bvl_to_bvi_with_clock
          ,bvl_to_bvi_id] >>
        MATCH_MP_TAC (GEN_ALL bv_ok_IMP_adjust_bv_eq) >>
        qexists_tac`r.refs`>>simp[] >>
        full_simp_tac(srw_ss())[state_ok_def,EVERY_MEM,MEM_EL
          ,PULL_EXISTS] >>
        first_x_assum(fn th => first_x_assum(mp_tac o MATCH_MP th)) >>
        simp[])
      \\ gvs [AllCaseEqs()]
      \\ imp_res_tac evaluate_IMP_LENGTH \\ gvs []
      \\ gvs [LENGTH_EQ_NUM_compute]
      \\ qpat_assum ‘state_rel b2 r t2’ $ irule_at Any
      \\ qpat_x_assum ‘state_rel b2 r t2’ mp_tac
      \\ simp [Once state_rel_def] \\ strip_tac
      \\ qexists_tac ‘c’ \\ fs []
      \\ gvs [iEval_def,EVAL “bviSem$do_app (IntOp (Const 2)) []
        s”,adjust_bv_def]
      \\ gvs [iEval_def,EVAL “bviSem$do_app (IntOp Add) [Number i;
        Number j] s”,adjust_bv_def]
      \\ gvs [iEval_def,EVAL “bviSem$do_app (GlobOp GlobalsPtr) []
        s”,adjust_bv_def]
      \\ Cases_on ‘t2.global’
      >- (fs [] \\ imp_res_tac evaluate_global_mono \\ gvs
        [inc_clock_def])
      \\ gvs []
      \\ gvs [closSemTheory.get_global_def,EVAL “num_added_globals”]
      \\ ‘∃j. i = & j’ by (Cases_on ‘i’ \\ fs []) \\ gvs []
      \\ gvs [bviSemTheory.do_app_def,bviSemTheory.do_app_aux_def]
      \\ gvs [bvlSemTheory.do_app_def,bviSemTheory.do_app_aux_def]
      \\ simp [AllCaseEqs()]
      \\ simp[EL_APPEND1,EL_MAP,miscTheory.the_def,bvl_to_bvi_with_clock
        ,bvl_to_bvi_id]
      \\ ‘&j + 2 = &(j + 2):int’ by intLib.COOPER_TAC \\ fs []
      \\ simp [DECIDE “j+2 = SUC (j+1)”,EL]
      \\ reverse conj_tac
      >- simp [state_component_equality]
      \\ simp [rich_listTheory.EL_APPEND1,EL_MAP,miscTheory.the_def])
    \\ Cases_on`∃n. op = GlobOp (SetGlobal n)` \\
      full_simp_tac(srw_ss())[]
    THEN1 (
         note_tac "Op: SetGlobal" >> simp[compile_op_def] >>
         full_simp_tac(srw_ss())[bEvalOp_def] >>
         Cases_on`REVERSE a`>>full_simp_tac(srw_ss())[] >>
         Cases_on`t`>>full_simp_tac(srw_ss())[] >> srw_tac[][] >>
         imp_res_tac evaluate_IMP_LENGTH >>
         Cases_on`c1`>>full_simp_tac(srw_ss())[LENGTH_NIL] >>
           srw_tac[][] >>
         every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
         simp[iEval_def] >>
         CONV_TAC(RESORT_EXISTS_CONV(List.rev)) >>
         Q.LIST_EXISTS_TAC[`c`,`b2`] >>
         simp[compile_int_thm] >>
         simp[iEvalOp_def,do_app_aux_def] >>
         imp_res_tac evaluate_global_mono >>
         BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[] >>
         simp[bEvalOp_def] >>
         qhdtm_x_assum`state_rel`mp_tac >>
         simp[Once state_rel_def] >> strip_tac >>
         simp[ADD1,LENGTH_REPLICATE] >>
         reverse IF_CASES_TAC >>
         fsrw_tac[ARITH_ss][closSemTheory.get_global_def] >>
         simp[bvl_to_bvi_with_refs,bvl_to_bvi_id,LUPDATE_def,GSYM ADD1]
           >>
         simp[ADD1,LUPDATE_APPEND1] >>
         full_simp_tac(srw_ss())[state_rel_def] >>
         simp[FLOOKUP_UPDATE] >>
         conj_tac >- full_simp_tac(srw_ss())[INJ_DEF] >>
         srw_tac[][] >- ( full_simp_tac(srw_ss())[FLOOKUP_DEF] >>
           srw_tac[][] >> METIS_TAC[] ) >>
         qexists_tac`z` >> simp[ADD1,LUPDATE_MAP] >>
         simp[miscTheory.the_def])
    \\ Cases_on`op = GlobOp AllocGlobal` \\ full_simp_tac(srw_ss())[]
      THEN1
        (note_tac "Op: AllocGlobal" \\ simp[compile_op_def]
         \\ gvs [bvlSemTheory.do_app_def,AllCaseEqs()]
         \\ rename [‘~(ii < 0:int)’]
         \\ ‘∃k. ii = & k’ by (Cases_on ‘ii’ \\ gvs [])
         \\ drule_then assume_tac bvlPropsTheory.evaluate_IMP_LENGTH
         \\ gvs [LENGTH_EQ_NUM_compute]
         \\ drule_then assume_tac compile_exps_LENGTH
         \\ gvs [LENGTH_EQ_NUM_compute,adjust_bv_def]
         \\ gvs [iEvalOp_def,iEval_def]
         \\ `lookup AllocGlobal_location t2.code = SOME(1,SND
           AllocGlobal_code)` by
           (fs [state_rel_def] \\ simp[AllocGlobal_code_def])
         \\ simp [find_code_def]
         \\ qpat_x_assum ‘state_rel b2 s5 t2’ mp_tac
         \\ simp [Once state_rel_def]
         \\ strip_tac
         \\ old_drule evaluate_global_mono
         \\ simp [Once inc_clock_def] \\ strip_tac
         \\ Cases_on ‘t2.global’ \\ fs []
         \\ old_drule evaluate_AllocGlobal_code
         \\ simp []
         \\ impl_tac
         >- EVAL_TAC
         \\ strip_tac
         \\ qpat_x_assum ‘_ = (Rval [Number (&k)],t2)’ assume_tac
         \\ old_drule evaluate_add_clock \\ fs []
         \\ disch_then $ qspec_then ‘c'+1’ assume_tac
         \\ fs [inc_clock_def] \\ full_simp_tac std_ss [ADD_ASSOC]
         \\ simp [AllCaseEqs(),PULL_EXISTS]
         \\ ‘c + c' + t1.clock + 1 = (c + c' + 1) + t1.clock’ by fs []
         \\ full_simp_tac std_ss []
         \\ first_assum $ irule_at $ Pos hd
         \\ simp [dec_clock_def]
         \\ first_assum $ irule_at $ Pos $ el 2
         \\ conj_tac >- EVAL_TAC
         \\ simp [state_rel_def,FLOOKUP_UPDATE]
         \\ full_simp_tac(srw_ss())[iEval_def] >> rpt var_eq_tac >>
         full_simp_tac(srw_ss())[LENGTH_REPLICATE,FLOOKUP_UPDATE] >>
         conj_tac >- full_simp_tac(srw_ss())[INJ_DEF] >>
         conj_tac >- (
           gen_tac >>
           Cases_on`FLOOKUP s5.refs k'`>>simp[]>>
           `x ≠ b2 k'` by (
             full_simp_tac(srw_ss())[INJ_DEF,FLOOKUP_DEF] >>
             METIS_TAC[] ) >>
           `p1 ≠ b2 k'` by (
             full_simp_tac(srw_ss())[INJ_DEF,FLOOKUP_DEF] >>
             METIS_TAC[] ) >>
           simp[] >>
           rpt(first_x_assum(qspec_then`k'`mp_tac)) >>
           simp[])  >>
         conj_tac >- (
           full_simp_tac(srw_ss())[FLOOKUP_DEF] >> metis_tac[INJ_DEF])
             >>
         rewrite_tac [REPLICATE_APPEND,miscTheory.the_def] >>
         irule_at Any (METIS_PROVE [] “k = n ⇒ REPLICATE k x = REPLICATE
           n x”) >>
         fs [ADD1] >>
         qexists_tac ‘extra+z’ >> fs [])
    \\ Cases_on`∃part. op = BlockOp (EqualConst part)` \\ fs[]
    >- (
      note_tac "Op: EqualConst" \\ gvs[compile_op_def,bEvalOp_def]
      \\ Cases_on`REVERSE a` \\ fs[] \\ rw[]
      \\ Cases_on`t` \\ fs[] \\ rw[]
      \\ gvs [AllCaseEqs()]
      \\ imp_res_tac bvlPropsTheory.evaluate_IMP_LENGTH \\ gvs
        [bEval_def]
      \\ imp_res_tac bviPropsTheory.evaluate_IMP_LENGTH \\ gvs
        [iEval_def]
      \\ gvs [LENGTH_EQ_NUM_compute]
      \\ gvs [compile_exps_def,handle_ok_def,aux_code_installed_def]
      \\ CONV_TAC(RESORT_EXISTS_CONV List.rev)
      \\ qexists_tac ‘c’ \\ fs []
      \\ qexists_tac ‘b2’ \\ fs []
      \\ fs
        [bviSemTheory.do_app_def,do_app_aux_def,bvlSemTheory.do_app_def,
             adjust_bv_def]
      \\ fs [state_rel_def,bvl_to_bvi_def,bvi_to_bvl_def]
      \\ ntac 3 (qpat_x_assum ‘∀x._’ mp_tac)
      \\ first_assum (qspec_then ‘p’ assume_tac)
      \\ qpat_x_assum ‘FLOOKUP _ _ = _’ assume_tac \\ fs [])
    \\ Cases_on`∃parts. op = BlockOp (Build parts)` \\ fs[]
    >- (
      note_tac "Op: Build" \\ gvs[compile_op_def,bEvalOp_def]
      \\ Cases_on`REVERSE a` \\ fs[] \\ rw[]
      \\ pairarg_tac \\ gvs []
      \\ gvs [AllCaseEqs()]
      \\ imp_res_tac bvlPropsTheory.evaluate_IMP_LENGTH \\ gvs
        [bEval_def]
      \\ imp_res_tac bviPropsTheory.evaluate_IMP_LENGTH \\ gvs
        [iEval_def]
      \\ gvs [compile_exps_def,handle_ok_def,aux_code_installed_def]
      \\ qpat_x_assum ‘state_rel _ _ t1’ kall_tac
      \\ fs
        [bviSemTheory.do_app_def,do_app_aux_def,bvlSemTheory.do_app_def]
      \\ asm_rewrite_tac [] \\ fs []
      \\ pairarg_tac \\ fs []
      \\ CONV_TAC(RESORT_EXISTS_CONV List.rev)
      \\ qexists_tac ‘c’ \\ fs []
      \\ fs [do_build_const_def]
      \\ rename [‘state_rel b2 s (inc_clock c t)’]
      \\ ‘∃m1 m2 l.
           (∀k. bv_ok s.refs (m1 k)) ∧
           (∀k. m2 k = adjust_bv b2 (m1 k)) ∧
           do_build m1 l parts s.refs = (q,rs) ∧
           do_build m2 l parts t.refs = (v,rs')’ by
       (qexists_tac ‘λx. Number 0’ \\ qexists_tac ‘λx. Number 0’
        \\ fs [adjust_bv_def,bv_ok_def] \\ first_x_assum $ irule_at Any
          \\ fs [])
      \\ rpt (qpat_x_assum ‘do_build _ 0 _ _ = _’ kall_tac)
      \\ rpt strip_tac
      \\ qpat_x_assum ‘state_rel _ _ _’ assume_tac
      \\ rpt $ last_x_assum mp_tac \\ rewrite_tac [AND_IMP_INTRO,GSYM
        CONJ_ASSOC]
      \\ goal_term (fn tm => EVERY (map ID_SPEC_TAC (free_vars tm)))
      \\ Induct_on ‘parts’ \\ fs [do_build_const_def,do_build_def]
      THEN1
       (rw [] \\ qexists_tac ‘b2’ \\ fs []
        \\ fs [state_rel_def,bvi_to_bvl_def,bvl_to_bvi_def])
      \\ strip_tac
      \\ Cases_on ‘(∃i. h = Int i) ∨ (∃w. h = W64 w) ∨
                   (∃n l. h = Con n l)’
      THEN1
       (rw [] \\ fs [do_part_def] \\ rw [] \\ first_x_assum irule \\ fs
         []
        \\ first_x_assum $ irule_at (Pos last)
        \\ first_x_assum $ irule_at (Pos last)
        \\ qexists_tac ‘b2’
        \\ fs [] \\ rw [APPLY_UPDATE_THM,adjust_bv_def]
        \\ fs [MAP_MAP_o,o_DEF,MAP_EQ_f,bv_ok_def,EVERY_MEM,MEM_MAP]
        \\ fs [bv_ok_def] \\ rw [EVERY_MEM,MEM_MAP] \\ fs [])
      \\ ‘∃content. h = Str content’ by (Cases_on ‘h’ \\ fs []) \\ gvs
        []
      \\ fs [do_part_def] \\ rw []
      \\ old_drule (GEN_ALL state_rel_add_bytearray)
      \\ qabbrev_tac ‘new_s = LEAST ptr. ptr ∉ FDOM s.refs’
      \\ qabbrev_tac ‘new_t = LEAST ptr. ptr ∉ FDOM t.refs’
      \\ ‘new_s ∉ FDOM s.refs’ by metis_tac [LEAST_NOTIN_FDOM]
      \\ ‘new_t ∉ FDOM t.refs’ by metis_tac [LEAST_NOTIN_FDOM]
      \\ fs [EVAL “(inc_clock c t).refs”]
      \\ disch_then drule_all
      \\ ‘∀r. (inc_clock c t with refs := r) = inc_clock c (t with refs
        := r)’ by
              (EVAL_TAC \\ fs []) \\ fs []
      \\ disch_then (qspecl_then [‘MAP (n2w ∘ ORD) (mlstring$explode
        content)’,‘T’] mp_tac)
      \\ qmatch_goalsub_abbrev_tac ‘state_rel _ s1 (_ t1)’
      \\ strip_tac
      \\ first_x_assum old_drule
      \\ qunabbrev_tac ‘s1’ \\ fs []
      \\ qunabbrev_tac ‘t1’ \\ fs []
      \\ disch_then old_drule
      \\ disch_then old_drule
      \\ disch_then (qspecl_then [‘b2⦇new_s ↦ new_t⦈’,‘env’] mp_tac)
      \\ impl_tac
      THEN1
       (reverse (rpt strip_tac)
        \\ TRY
         (fs [state_ok_def,FLOOKUP_UPDATE,EVERY_MEM] \\ rw []
          \\ rpt (TOP_CASE_TAC \\ gvs []) \\ rw []
          \\ irule bv_ok_SUBSET_IMP
          \\ qexists_tac ‘s.refs’ \\ fs []
          \\ res_tac \\ gvs []
          \\ first_x_assum (qspec_then ‘k’ mp_tac) \\ gvs [] \\ NO_TAC)
        \\ rw [APPLY_UPDATE_THM,adjust_bv_def,bv_ok_def]
        THEN1 (irule bv_ok_SUBSET_IMP \\ qexists_tac ‘s.refs’ \\ fs [])
        \\ irule bv_ok_IMP_adjust_bv_eq
        \\ qexists_tac ‘s.refs’ \\ fs []
        \\ rw [APPLY_UPDATE_THM]
        \\ metis_tac [LEAST_NOTIN_FDOM])
      \\ strip_tac \\ fs []
      \\ qexists_tac ‘b2'’ \\ fs []
      \\ reverse (rpt strip_tac)
      THEN1
       (gvs [] \\ first_x_assum (qspec_then ‘a’ mp_tac)
        \\ fs [APPLY_UPDATE_THM] \\ rw []
        \\ metis_tac [LEAST_NOTIN_FDOM])
      THEN1
       (qpat_x_assum ‘MAP _ _ = _’ (assume_tac o GSYM) \\ fs [MAP_EQ_f]
        \\ rw []
        \\ irule bv_ok_IMP_adjust_bv_eq
        \\ qexists_tac ‘s.refs’ \\ fs []
        \\ fs [EVERY_MEM] \\ res_tac \\ fs []
        \\ rw [] \\ res_tac
        \\ Cases_on ‘new_s = a’ \\ fs [APPLY_UPDATE_THM])
      \\ qpat_x_assum ‘state_rel _ _ _’ mp_tac
      \\ simp
        [state_rel_def,bvl_to_bvi_def,bvi_to_bvl_def,inc_clock_def])
    \\ Cases_on`∃str. op = MemOp FromListByte` \\ fs[]
    >- (
      note_tac "Op: FromListByte" \\ fs[compile_op_def,bEvalOp_def]
      \\ `∃lv. REVERSE a = [lv]` by (every_case_tac \\ fs[]) \\ fs[]
      \\ qpat_x_assum`_ = Rval _`mp_tac
      \\ DEEP_INTRO_TAC some_intro \\ fs[]
      \\ rpt strip_tac
      \\ imp_res_tac evaluate_IMP_LENGTH
      \\ fs[LENGTH_EQ_NUM_compute] \\ rw[]
      \\ simp[Once iEval_def]
      \\ `lookup ListLength_location t2.code = SOME (2,SND
        ListLength_code)`
      by ( fs[state_rel_def,ListLength_code_def])
      \\ qabbrev_tac`p = (LEAST ptr. ptr ∉ FDOM (bvi_to_bvl t2).refs)`
      \\ qmatch_goalsub_abbrev_tac`_ |+ (ptr,_)`
      \\ qabbrev_tac`b2' = (ptr =+ p) b2`
      \\ `MAP (adjust_bv b2') env = MAP (adjust_bv b2) env` by
       (full_simp_tac(srw_ss())[MAP_EQ_f] \\ REPEAT STRIP_TAC
        \\ MATCH_MP_TAC (bv_ok_IMP_adjust_bv_eq |> GEN_ALL)
        \\ Q.EXISTS_TAC `s5.refs` \\ full_simp_tac(srw_ss())[]
        \\ IMP_RES_TAC evaluate_ok \\ full_simp_tac(srw_ss())[]
        \\ REV_FULL_SIMP_TAC std_ss []
        \\ full_simp_tac(srw_ss())[EVERY_MEM]
        \\ simp[Abbr`b2'`,Abbr`ptr`,APPLY_UPDATE_THM]
        \\ rw[] \\ fs[LEAST_NOTIN_FDOM] \\ NO_TAC)
      \\ `v_to_list (adjust_bv b2 lv) = v_to_list lv`
      by (simp[v_to_list_adjust,MAP_MAP_o,o_DEF,adjust_bv_def])
      \\ rfs[]
      \\ old_drule evaluate_ListLength_code
      \\ disch_then old_drule \\ simp[]
      \\ disch_then(qspec_then`0`(qx_choose_then`cl`strip_assume_tac))
      \\ old_drule (Q.GENL[`p`,`fl`]evaluate_FromListByte_code |> Q.INST
        [‘b’|->‘T’])
      \\ qabbrev_tac`bs = REPLICATE (LENGTH x) (0w:word8)`
      \\ disch_then(qspecl_then[`p`,`T`,`0`,`bs`,`t2 with refs :=
        t2.refs |+ (p,ByteArray T bs)`]mp_tac)
      \\ simp[LENGTH_REPLICATE,Abbr`bs`,FLOOKUP_UPDATE]
      \\ impl_keep_tac >- fs[state_rel_def,FromListByte_code_def]
      \\ disch_then(qx_choose_then`cf`strip_assume_tac)
      \\ CONV_TAC SWAP_EXISTS_CONV \\ Q.EXISTS_TAC `b2'`
      \\ CONV_TAC SWAP_EXISTS_CONV \\ Q.EXISTS_TAC `(cf+1) + (cl+1) + c`
      \\ qspecl_then[`[h]`,`MAP _ env`]old_drule evaluate_add_clock
      \\ simp[GSYM inc_clock_ADD]
      \\ disch_then(qspec_then`cf+1 + cl+1`mp_tac)
      \\ simp[GSYM inc_clock_ADD]
      \\ disch_then kall_tac
      \\ simp[Once iEval_def]
      \\ simp[Once iEval_def]
      \\ simp[Once iEval_def]
      \\ simp[Once iEval_def]
      \\ simp[Once iEval_def]
      \\ simp[Once iEval_def]
      \\ simp[iEvalOp_def,do_app_aux_def
        ,backend_commonTheory.small_enough_int_def]
      \\ simp[Once iEval_def]
      \\ simp[Once iEval_def]
      \\ simp[Once iEval_def]
      \\ simp[Once iEval_def]
      \\ simp[Once
        iEvalOp_def,do_app_aux_def
        ,backend_commonTheory.small_enough_int_def]
      \\ simp[Once iEval_def]
      \\ simp[Once iEval_def]
      \\ simp[Once iEval_def]
      \\ simp[Once iEval_def]
      \\ simp[Once iEval_def]
      \\ simp[Once
        iEvalOp_def,do_app_aux_def
        ,backend_commonTheory.small_enough_int_def]
      \\ simp[find_code_def]
      \\ simp[inc_clock_def,dec_clock_def]
      \\ qspecl_then[`[SND ListLength_code]`]old_drule
        evaluate_add_clock
      \\ simp[]
      \\ disch_then(qspec_then`cf+1`mp_tac)
      \\ simp[inc_clock_def]
      \\ disch_then kall_tac
      \\ simp[iEvalOp_def,do_app_aux_def]
      \\ reverse IF_CASES_TAC \\ fs[]
      >- ( first_x_assum(qspec_then`0w`mp_tac) \\ simp[] )
      \\ Cases_on`w` \\ fs[] \\ rveq \\ fs[]
      \\ fs[inc_clock_def,adjust_bv_def,Abbr`b2'`,APPLY_UPDATE_THM]
      \\ reverse conj_tac
      >- (
        rw[Abbr`ptr`]
        \\ imp_res_tac evaluate_refs_SUBSET
        \\ fs[SUBSET_DEF]
        \\ res_tac \\ fs[LEAST_NOTIN_FDOM] )
      \\ fs[state_rel_def]
      \\ conj_tac
      >- (
        MATCH_MP_TAC INJ_EXTEND
        \\ fs[Abbr`ptr`,LEAST_NOTIN_FDOM,Abbr`p`] )
      \\ fs[v_to_list_adjust] \\ rfs[] \\ rveq
      \\ fs[MAP_MAP_o,o_DEF,adjust_bv_def]
      \\ conj_tac
      >- (
        rw[FLOOKUP_UPDATE,APPLY_UPDATE_THM] \\ fs[]
        >- (
          CASE_TAC \\ fs[]
          \\ fs[INJ_DEF,FLOOKUP_DEF]
          \\ METIS_TAC[LEAST_NOTIN_FDOM] )
        \\ qpat_x_assum`∀k. option_CASE _ _ _`(qspec_then`k`mp_tac)
        \\ CASE_TAC \\ fs[]
        \\ CASE_TAC \\ fs[] \\ rw[]
        \\ imp_res_tac evaluate_ok
        \\ fs[state_ok_def]
        \\ first_x_assum(qspec_then`k`mp_tac) \\ rw[]
        \\ simp[MAP_EQ_f] \\ rw[] \\ fs[EVERY_MEM]
        \\ match_mp_tac (GEN_ALL bv_ok_IMP_adjust_bv_eq) \\ qexists_tac
          `s5.refs`
        \\ simp[APPLY_UPDATE_THM] \\ rw[]
        >- fs[Abbr`a`,LEAST_NOTIN_FDOM]
        >- fs[Abbr`a'`,LEAST_NOTIN_FDOM])
      \\ simp[FLOOKUP_UPDATE,APPLY_UPDATE_THM]
      \\ ntac 2 strip_tac
      \\ first_x_assum old_drule
      \\ rw[]
      >- ( simp[FLOOKUP_DEF,LEAST_NOTIN_FDOM,Abbr`p`] )
      >- ( rw[] )
      >> simp[o_DEF]
      \\ qexists_tac`z` \\ simp[]
      \\ simp[MAP_EQ_f]
      \\ Cases \\ simp[miscTheory.the_def]
      \\ rw[]
      \\ match_mp_tac (GEN_ALL bv_ok_IMP_adjust_bv_eq) \\ qexists_tac
        `s5.refs`
      \\ simp[APPLY_UPDATE_THM]
      \\ imp_res_tac evaluate_ok
      \\ fs[state_ok_def,EVERY_MEM]
      \\ res_tac \\ fs[] \\ rw[]
      \\ fs[Abbr`a`,LEAST_NOTIN_FDOM,Abbr`p`] )
    \\ Cases_on`op = MemOp ConcatByteVec` \\ fs[]
    >- (
      note_tac "Op: ConcatByteVec" \\
      fs[compile_op_def,bEvalOp_def,case_eq_thms]
      \\ imp_res_tac evaluate_IMP_LENGTH
      \\ rw[] \\ fs[NULL_EQ,LENGTH_EQ_NUM_compute]
      \\ qpat_x_assum`_ = SOME _`mp_tac
      \\ DEEP_INTRO_TAC some_intro \\ fs[]
      \\ strip_tac
      \\ `lookup SumListLength_location t2.code = SOME (2,SND
        SumListLength_code)`
      by ( fs[state_rel_def,SumListLength_code_def])
      \\ old_drule evaluate_SumListLength_code
      \\ disch_then(qspec_then`adjust_bv b2 lv`mp_tac)
      \\ simp[v_to_list_adjust,MAP_MAP_o,Once o_DEF,adjust_bv_def]
      \\ `MAP (FLOOKUP t2.refs o b2) ps = MAP (FLOOKUP s5.refs) ps`
      by (
        fs[state_rel_def,MAP_EQ_f,MAP_MAP_o]
        \\ qx_gen_tac`k` \\ rw[]
        \\ fs[LIST_EQ_REWRITE,MEM_EL]
        \\ first_x_assum old_drule
        \\ simp[EL_MAP] \\ strip_tac
        \\ ntac 4 (first_x_assum(qspec_then`k`mp_tac))
        \\ simp[] )
      \\ fs[GSYM MAP_MAP_o] \\ rfs[]
      \\ disch_then(first_assum o mp_then Any mp_tac)
      \\ simp[MAP_MAP_o,o_DEF] \\ rveq
      \\ disch_then(qspec_then`0`(qx_choose_then`c1`strip_assume_tac))
      \\ qabbrev_tac`dst = LEAST ptr. ptr ∉ FDOM t2.refs`
      \\ qabbrev_tac`t3 = t2 with refs := t2.refs |+ (dst, ByteArray T
        (REPLICATE (LENGTH (FLAT wss)) 0w))`
      \\ `lookup SumListLength_location t3.code = SOME (2,SND
        SumListLength_code)`
      by ( fs[state_rel_def,SumListLength_code_def,Abbr`t3`])
      \\ old_drule (evaluate_ConcatByte_code |> Q.INST [‘b’ |-> ‘T’])
      \\ simp[Once(GSYM AND_IMP_INTRO),RIGHT_FORALL_IMP_THM]
      \\ impl_keep_tac >- fs[Abbr`t3`,state_rel_def,ConcatByte_code_def]
      \\ disch_then(qspec_then`adjust_bv b2 lv`mp_tac)
      \\ simp[v_to_list_adjust,MAP_MAP_o,Once o_DEF,adjust_bv_def]
      \\ `¬MEM dst (MAP b2 ps)`
      by (
        strip_tac
        \\ fs[LIST_EQ_REWRITE,MEM_EL,MEM_MAP]
        \\ first_x_assum old_drule
        \\ simp[EL_MAP] \\ strip_tac
        \\ fs[FLOOKUP_DEF,INJ_DEF,state_rel_def]
        \\ METIS_TAC[LEAST_NOTIN_FDOM] )
      \\ `MAP (FLOOKUP t3.refs o b2) ps = MAP (FLOOKUP t2.refs o b2) ps`
      by (
        simp[Abbr`t3`,FLOOKUP_UPDATE,MAP_EQ_f]
        \\ fs[MEM_MAP] \\ rw[]
        \\ METIS_TAC[] )
      \\ fs[GSYM MAP_MAP_o] \\ rfs[]
      \\ disch_then(first_assum o mp_then Any mp_tac)
      \\ simp[MAP_MAP_o,o_DEF] \\ rveq
      \\ simp[Abbr`t3`,FLOOKUP_UPDATE]
      \\ disch_then(qspec_then`[]`mp_tac)
      \\ simp[LENGTH_REPLICATE]
      \\ disch_then(qx_choose_then`c2`strip_assume_tac)
      \\ last_x_assum(mp_then Any mp_tac
            (INST_TYPE[alpha|->``:'c``,beta|->``:'ffi``]
               bviPropsTheory.evaluate_add_clock))
      \\ disch_then(qspec_then`c1+c2+2`mp_tac) \\ rw[inc_clock_ADD]
      \\ CONV_TAC(RESORT_EXISTS_CONV List.rev)
      \\ map_every qexists_tac[`c+c1+c2+2`,
           `((LEAST ptr. ptr ∉ FDOM s5.refs) =+ dst) b2`]
      \\ last_x_assum(mp_then Any mp_tac
            (INST_TYPE[alpha|->``:'c``,beta|->``:'ffi``]
               bviPropsTheory.evaluate_add_clock))
      \\ disch_then(qspec_then`c2+1`mp_tac) \\ rw[inc_clock_ADD]
      \\ simp[LEFT_EXISTS_AND_THM,CONJ_ASSOC]
      \\ reverse conj_asm2_tac
      >- (
        rw[APPLY_UPDATE_THM]
        \\ imp_res_tac evaluate_refs_SUBSET
        \\ fs[SUBSET_DEF]
        \\ METIS_TAC[LEAST_NOTIN_FDOM] )
      \\ reverse conj_asm2_tac
      >- (
        rw[MAP_EQ_f]
        \\ match_mp_tac (GEN_ALL bv_ok_IMP_adjust_bv_eq) \\ qexists_tac
          `s5.refs`
        \\ fs[EVERY_MEM]
        \\ imp_res_tac evaluate_refs_SUBSET
        \\ imp_res_tac bv_ok_SUBSET_IMP
        \\ rw[APPLY_UPDATE_THM]
        \\ METIS_TAC[LEAST_NOTIN_FDOM] )
      \\ pop_assum (assume_tac o SYM)
      \\ rw[iEval_def,find_code_def,iEvalOp_def,do_app_aux_def
        ,backend_commonTheory.small_enough_int_def]
      \\ fs[inc_clock_def,dec_clock_def]
      \\ reverse IF_CASES_TAC
      >- ( `F` by METIS_TAC[EVAL``w2n (0w:word8)``] )
      \\ simp[integer_wordTheory.i2w_def]
      \\ simp[APPLY_UPDATE_THM]
     \\ imp_res_tac evaluate_ok
      \\ imp_res_tac evaluate_refs_SUBSET
      \\ rpt(qhdtm_x_assum`evaluate`kall_tac)
      \\ rpt(qhdtm_x_assum`lookup`kall_tac)
      \\ match_mp_tac state_rel_add_bytearray
      \\ METIS_TAC[LEAST_NOTIN_FDOM])
    \\ Cases_on`op = MemOp XorByte` \\ fs[]
    >- (
      note_tac "Op: XorByte" \\
      CONV_TAC(RESORT_EXISTS_CONV List.rev)
      \\ qabbrev_tac`pp = LEAST ptr. ptr ∉ FDOM s5.refs`
      \\ qabbrev_tac`qq = LEAST ptr. ptr ∉ FDOM t2.refs`
      \\ (`MAP (adjust_bv ((pp =+ qq) b2)) env = MAP (adjust_bv b2) env`
      by (
        rw[MAP_EQ_f]
        \\ match_mp_tac (GEN_ALL bv_ok_IMP_adjust_bv_eq) \\ qexists_tac
          `s5.refs`
        \\ imp_res_tac evaluate_refs_SUBSET
        \\ imp_res_tac bv_ok_SUBSET_IMP
        \\ fs[EVERY_MEM]
        \\ rw[APPLY_UPDATE_THM]
        \\ METIS_TAC[LEAST_NOTIN_FDOM] ))
      \\ qexists_tac`c`
      \\ fs[compile_op_def,bEvalOp_def,case_eq_thms,SWAP_REVERSE_SYM]
      \\ qexists_tac`b2`
      \\ rw[iEval_def,adjust_bv_def,iEvalOp_def,do_app_aux_def
        ,bEvalOp_def]
      \\ fs[case_eq_thms,PULL_EXISTS] \\
        rw[adjust_bv_def,APPLY_UPDATE_THM]
      \\ rename1`FLOOKUP s5.refs src = SOME _`
      \\ (`FLOOKUP t2.refs (b2 src) = FLOOKUP s5.refs src`
      by (
        fs[state_rel_def]
        \\ ntac 4 (first_x_assum(qspec_then`src`mp_tac))
        \\ simp[] \\ NO_TAC) ) \\
          simp[APPLY_UPDATE_THM,bvl_to_bvi_with_refs,bvl_to_bvi_id]
      \\ (`FLOOKUP t2.refs (b2 src') = FLOOKUP s5.refs src'`
      by (
        fs[state_rel_def]
        \\ ntac 4 (first_x_assum(qspec_then`src'`mp_tac))
        \\ simp[] \\ NO_TAC) ) \\
          simp[APPLY_UPDATE_THM,bvl_to_bvi_with_refs,bvl_to_bvi_id]
      \\ fs[state_rel_def,FLOOKUP_UPDATE]
      \\ conj_tac
      >- (
        `src INSERT FDOM s5.refs = FDOM s5.refs ∧
         b2 src INSERT FDOM t2.refs = FDOM t2.refs`
        by (simp[GSYM ABSORPTION]
          \\ fs[FLOOKUP_DEF]
          \\ METIS_TAC[INJ_DEF] ) \\
        simp[] )
      \\ rw[]
      >- (TOP_CASE_TAC \\ fs[FLOOKUP_DEF] \\ METIS_TAC[INJ_DEF])
      >- ( fs[FLOOKUP_DEF] \\ METIS_TAC[] )
      \\ METIS_TAC[] )
    \\ Cases_on`op = MemOp (CopyByte F)` \\ fs[]
    >- (
      note_tac "Op: CopyByte F" \\
      CONV_TAC(RESORT_EXISTS_CONV List.rev)
      \\ qabbrev_tac`pp = LEAST ptr. ptr ∉ FDOM s5.refs`
      \\ qabbrev_tac`qq = LEAST ptr. ptr ∉ FDOM t2.refs`
      \\ (`MAP (adjust_bv ((pp =+ qq) b2)) env = MAP (adjust_bv b2) env`
      by (
        rw[MAP_EQ_f]
        \\ match_mp_tac (GEN_ALL bv_ok_IMP_adjust_bv_eq) \\ qexists_tac
          `s5.refs`
        \\ imp_res_tac evaluate_refs_SUBSET
        \\ imp_res_tac bv_ok_SUBSET_IMP
        \\ fs[EVERY_MEM]
        \\ rw[APPLY_UPDATE_THM]
        \\ METIS_TAC[LEAST_NOTIN_FDOM] ))
      \\ qexists_tac`c`
      \\ fs[compile_op_def,bEvalOp_def,case_eq_thms,SWAP_REVERSE_SYM]
      \\ qexists_tac`b2`
      \\ rw[iEval_def,adjust_bv_def,iEvalOp_def,do_app_aux_def
        ,bEvalOp_def]
      \\ fs[case_eq_thms,PULL_EXISTS] \\
        rw[adjust_bv_def,APPLY_UPDATE_THM]
      \\ rename1`FLOOKUP s5.refs src = SOME _`
      \\ (`FLOOKUP t2.refs (b2 src) = FLOOKUP s5.refs src`
      by (
        fs[state_rel_def]
        \\ ntac 4 (first_x_assum(qspec_then`src`mp_tac))
        \\ simp[] \\ NO_TAC) ) \\
          simp[APPLY_UPDATE_THM,bvl_to_bvi_with_refs,bvl_to_bvi_id]
      \\ `FLOOKUP t2.refs (b2 dst) = FLOOKUP s5.refs dst`
      by (
        fs[state_rel_def]
        \\ ntac 4 (first_x_assum(qspec_then`dst`mp_tac))
        \\ simp[] \\ NO_TAC ) \\
          simp[APPLY_UPDATE_THM,bvl_to_bvi_with_refs,bvl_to_bvi_id]
      \\ fs[state_rel_def,FLOOKUP_UPDATE]
      \\ conj_tac
      >- (
        `dst INSERT FDOM s5.refs = FDOM s5.refs ∧
         b2 dst INSERT FDOM t2.refs = FDOM t2.refs`
        by (simp[GSYM ABSORPTION]
          \\ fs[FLOOKUP_DEF]
          \\ METIS_TAC[INJ_DEF] ) \\
        simp[] )
      \\ rw[]
      >- (TOP_CASE_TAC \\ fs[FLOOKUP_DEF] \\ METIS_TAC[INJ_DEF])
      >- ( fs[FLOOKUP_DEF] \\ METIS_TAC[] )
      \\ METIS_TAC[] )
    \\ Cases_on`op = MemOp (CopyByte T)` \\ fs[]
    >- (
        note_tac "Op: CopyByte T" \\
        CONV_TAC(RESORT_EXISTS_CONV List.rev)
        \\ qexists_tac`c`
        \\ fs[bEvalOp_def,case_eq_thms] \\ rw[]
        \\ fs[SWAP_REVERSE_SYM]
        \\ imp_res_tac evaluate_IMP_LENGTH \\ fs[LENGTH_EQ_NUM_compute]
          \\ rw[]
        \\ simp[compile_op_def]
        \\ fs[semanticPrimitivesTheory.copy_array_def,case_eq_thms]
        \\ qabbrev_tac`pp = LEAST ptr. ptr ∉ FDOM s5.refs`
        \\ qabbrev_tac`qq = LEAST ptr. ptr ∉ FDOM t2.refs`
        \\ qexists_tac`(pp =+ qq) b2` \\
        `MAP (adjust_bv b2) env = MAP (adjust_bv ((pp =+ qq) b2)) env`
          by (
          rw[MAP_EQ_f]
          \\ match_mp_tac (GEN_ALL bv_ok_IMP_adjust_bv_eq) \\
            qexists_tac `s5.refs`
          \\ imp_res_tac evaluate_refs_SUBSET
          \\ imp_res_tac bv_ok_SUBSET_IMP
          \\ fs[EVERY_MEM]
          \\ rw[APPLY_UPDATE_THM]
          \\ METIS_TAC[LEAST_NOTIN_FDOM] )
        \\ qhdtm_x_assum`bviSem$evaluate`mp_tac
        \\ simp[iEval_def,iEvalOp_def,do_app_aux_def,adjust_bv_def
          ,backend_commonTheory.small_enough_int_def]
        \\ fsrw_tac[intLib.INT_ARITH_ss][]
        \\ reverse IF_CASES_TAC
        >- (fs[] \\ first_x_assum(qspec_then`0w`mp_tac) \\ simp[])
        \\ simp[bEvalOp_def,FLOOKUP_UPDATE]
        \\ rename1`qq = b2 src`
        \\ IF_CASES_TAC
        >- (
          fs[state_rel_def]
          \\ ntac 4 (first_x_assum(qspec_then`src`mp_tac))
          \\ simp[]
          \\ fs[FLOOKUP_DEF]
          \\ METIS_TAC[LEAST_NOTIN_FDOM] )
        \\ (`FLOOKUP t2.refs (b2 src) = FLOOKUP s5.refs src`
        by (
          fs[state_rel_def]
          \\ ntac 4 (first_x_assum(qspec_then`src`mp_tac))
          \\ simp[] \\ NO_TAC) )
        \\ simp[semanticPrimitivesTheory.copy_array_def]
        \\ asm_simp_tac(srw_ss()++intLib.INT_ARITH_ss)
          [integerTheory.INT_ABS]
        \\ simp[APPLY_UPDATE_THM,bvl_to_bvi_with_refs,bvl_to_bvi_id]
        \\ strip_tac
        \\ simp[REPLICATE_GENLIST,DROP_LENGTH_NIL_rwt]
        \\ conj_tac
        >- (
          match_mp_tac state_rel_add_bytearray
          \\ imp_res_tac evaluate_ok
          \\ simp[Abbr`pp`,Abbr`qq`,LEAST_NOTIN_FDOM] )
        \\ rw[]
        \\ imp_res_tac evaluate_refs_SUBSET
        \\ METIS_TAC[SUBSET_DEF,LEAST_NOTIN_FDOM] )
    \\ Cases_on`∃b. op = MemOp (CopyByte b)` \\ fs[] >- (Cases_on`b` \\
      fs[])
*)
    (* the ops reserved for bvi_tmc are the remaining ones compile_op
       does not
       leave alone; each is ruled out by bvlSem$do_app being Error on it
         *)
(* HOL4 ML code, not ported:
    \\ `compile_op op c1 = Op op c1` by
      (cases_on_op `op` \\ full_simp_tac(srw_ss())[compile_op_def]
       \\ TRY (gvs [bvlSemTheory.do_app_def] \\ NO_TAC)
       \\ Cases_on `i` \\ fs[]
       \\ NO_TAC)
    \\ full_simp_tac(srw_ss())[iEval_def]
    \\ CONV_TAC SWAP_EXISTS_CONV \\ Q.EXISTS_TAC `b2`
    \\ CONV_TAC SWAP_EXISTS_CONV \\ Q.EXISTS_TAC `c`
    \\ `EVERY (bv_ok s5.refs) (REVERSE a)` by (IMP_RES_TAC evaluate_ok
      \\ full_simp_tac(srw_ss())[rich_listTheory.EVERY_REVERSE])
    \\ old_drule (GEN_ALL do_app_adjust) \\ fs []
    \\ disch_then (qspecl_then [`r`,`q`,`op`,`a`] mp_tac)
    \\ fs [] \\ strip_tac \\ fs [MAP_REVERSE]
QED
*)

(* HOL4 ML code, not ported:
Resume compile_exps_correct[NIL]:
  REPEAT STRIP_TAC
  \\ full_simp_tac(srw_ss())[bEval_def,compile_exps_def,
        iEval_def,bEvery_def,handle_ok_def]
  \\ note_tac "NIL" \\ SRW_TAC [] [iEval_def]
    \\ Q.LIST_EXISTS_TAC [`b1`,`0`] \\
      full_simp_tac(srw_ss())[inc_clock_ZERO]
QED
*)

(* HOL4 ML code, not ported:
Resume compile_exps_correct[CONS]:
  REPEAT STRIP_TAC
  \\ full_simp_tac(srw_ss())[bEval_def,compile_exps_def,
        iEval_def,bEvery_def,handle_ok_def]
  \\ note_tac "CONS" \\
    `?c1 aux1 n1. compile_exps n [x] = (c1,aux1,n1)` by METIS_TAC [PAIR]
    \\ `?c2 aux2 n2. compile_exps n1 (y::xs) = (c2,aux2,n2)` by
      METIS_TAC [PAIR]
    \\ full_simp_tac(srw_ss())[LET_DEF] \\ SRW_TAC [] []
    \\ full_simp_tac(srw_ss())[PULL_FORALL]
    \\ `?res5 s5. evaluate ([x],env,s) = (res5,s5)` by METIS_TAC [PAIR]
    \\ `?res6 s6. evaluate (y::xs,env,s5) = (res6,s6)` by METIS_TAC
      [PAIR]
    \\ IMP_RES_TAC evaluate_ok \\ full_simp_tac(srw_ss())[]
    \\ IMP_RES_TAC aux_code_installed_APPEND \\ SRW_TAC [] []
    \\ full_simp_tac(srw_ss())[] \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `n`)
    \\ full_simp_tac(srw_ss())[]
    \\ reverse (Cases_on `res5`) \\ full_simp_tac(srw_ss())[] \\ REPEAT
      STRIP_TAC
    \\ POP_ASSUM (MP_TAC o Q.SPECL [`t1`,`b1`]) \\
      full_simp_tac(srw_ss())[]
    \\ rpt var_eq_tac
    \\ TRY (impl_tac >- (spose_not_then strip_assume_tac
                         \\ full_simp_tac(srw_ss())[]))
    \\ TRY (REPEAT STRIP_TAC \\ IMP_RES_TAC compile_exps_LENGTH
      \\ `?d. c1 = [d]` by (Cases_on `c1` \\
        full_simp_tac(srw_ss())[LENGTH_NIL])
      \\ SIMP_TAC std_ss [Once bviPropsTheory.evaluate_CONS] \\
        full_simp_tac(srw_ss())[]
      \\ SIMP_TAC std_ss [Once bviPropsTheory.evaluate_CONS] \\
        full_simp_tac(srw_ss())[GSYM PULL_FORALL]
      \\ Q.LIST_EXISTS_TAC [`t2`,`b2`,`c`] \\ full_simp_tac(srw_ss())[]
        \\ NO_TAC)
    \\ REPEAT STRIP_TAC
    \\ Q.PAT_X_ASSUM `!nn mm. bbb` (MP_TAC o Q.SPEC `n1`) \\
      full_simp_tac(srw_ss())[]
    \\ `res6 <> Rerr(Rabort Rtype_error)` by (REPEAT STRIP_TAC \\
      full_simp_tac(srw_ss())[]) \\ full_simp_tac(srw_ss())[]
    \\ REPEAT STRIP_TAC
    \\ IMP_RES_TAC compile_exps_LENGTH
    \\ `?d. c1 = [d]` by (Cases_on `c1`
           \\ full_simp_tac(srw_ss())[LENGTH_NIL]) \\
             full_simp_tac(srw_ss())[]
    \\ `aux_code_installed (append aux2) t2.code` by
     (full_simp_tac(srw_ss())[GSYM PULL_FORALL]
      \\ imp_res_tac evaluate_code_mono \\ fs [inc_clock_def]
      \\ match_mp_tac aux_code_installed_subspt
      \\ asm_exists_tac \\ fs [])
    \\ first_x_assum (qspecl_then [`t2`,`b2`] mp_tac)
    \\ full_simp_tac(srw_ss())[]
    \\ `s2 = s6` by (BasicProvers.EVERY_CASE_TAC \\
      full_simp_tac(srw_ss())[])
    \\ impl_tac >- metis_tac[evaluate_global_mono,inc_clock_global]
    \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[GSYM PULL_FORALL]
    \\ Q.MATCH_ASSUM_RENAME_TAC
        `evaluate (c2,MAP (adjust_bv b3) env,inc_clock c4 t2) =
           (map_result (MAP (adjust_bv b3)) (λv. Exn (adjust_bv b3 v))
             res6,t3)`
    \\ IMP_RES_TAC evaluate_inv_clock
    \\ full_simp_tac(srw_ss())[inc_clock_ADD]
    \\ ONCE_REWRITE_TAC [bviPropsTheory.evaluate_CONS] \\
      full_simp_tac(srw_ss())[]
    \\ REV_FULL_SIMP_TAC std_ss []
    \\ Q.LIST_EXISTS_TAC [`t3`,`b3`,`c4 + c`] \\
      full_simp_tac(srw_ss())[]
    \\ Cases_on `res6` \\ full_simp_tac(srw_ss())[]
    \\ Q.PAT_X_ASSUM `xx = res` (ASSUME_TAC o GSYM) \\
      full_simp_tac(srw_ss())[]
    \\ IMP_RES_TAC evaluate_refs_SUBSET \\
      full_simp_tac(srw_ss())[SUBSET_DEF]
    \\ IMP_RES_TAC bvlPropsTheory.evaluate_SING \\
      full_simp_tac(srw_ss())[]
    \\ MATCH_MP_TAC (GEN_ALL bv_ok_IMP_adjust_bv_eq)
    \\ asm_exists_tac \\ fs []
QED
*)

(* HOL4 ML code, not ported:
Resume compile_exps_correct[Var]:
  REPEAT STRIP_TAC
  \\ full_simp_tac(srw_ss())[bEval_def,compile_exps_def,
        iEval_def,bEvery_def,handle_ok_def]
  \\ note_tac "Var" \\
    Cases_on `n < LENGTH env` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC []
      []
    \\ full_simp_tac(srw_ss())[iEval_def] \\ Q.LIST_EXISTS_TAC
      [`b1`,`0`]
    \\ full_simp_tac(srw_ss())[inc_clock_ZERO,EL_MAP]
QED
*)

(* HOL4 ML code, not ported:
Resume compile_exps_correct[If]:
  REPEAT STRIP_TAC
  \\ full_simp_tac(srw_ss())[bEval_def,compile_exps_def,
        iEval_def,bEvery_def,handle_ok_def]
  \\ note_tac "If" \\
    Q.ABBREV_TAC `n4 = n2` \\ POP_ASSUM (K ALL_TAC)
    \\ `?c1 aux1 n1. compile_exps n [x1] = (c1,aux1,n1)` by METIS_TAC
      [PAIR]
    \\ `?c2 aux2 n2. compile_exps n1 [x2] = (c2,aux2,n2)` by METIS_TAC
      [PAIR]
    \\ `?c3 aux3 n3. compile_exps n2 [x3] = (c3,aux3,n3)` by METIS_TAC
      [PAIR]
    \\ full_simp_tac(srw_ss())[LET_DEF] \\ SRW_TAC [] [] \\
      full_simp_tac(srw_ss())[PULL_FORALL]
    \\ `?res5 s5. evaluate ([x1],env,s) = (res5,s5)` by METIS_TAC [PAIR]
    \\ IMP_RES_TAC evaluate_ok \\ full_simp_tac(srw_ss())[]
    \\ IMP_RES_TAC aux_code_installed_APPEND \\ SRW_TAC [] []
    \\ full_simp_tac(srw_ss())[] \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `n`)
      \\ full_simp_tac(srw_ss())[]
    \\ reverse (Cases_on `res5`) \\ full_simp_tac(srw_ss())[] \\ REPEAT
      STRIP_TAC
    \\ POP_ASSUM (MP_TAC o Q.SPECL [`t1`,`b1`]) \\
      full_simp_tac(srw_ss())[]
    \\ IMP_RES_TAC aux_code_installed_APPEND \\
      full_simp_tac(srw_ss())[GSYM PULL_FORALL]
    \\ TRY (
      impl_tac >- (rpt strip_tac >> full_simp_tac(srw_ss())[])
      \\ REPEAT STRIP_TAC \\ IMP_RES_TAC compile_exps_LENGTH
      \\ `?d. c1 = [d]` by (Cases_on `c1` \\
        full_simp_tac(srw_ss())[LENGTH_NIL])
      \\ SIMP_TAC std_ss [Once iEval_def] \\ full_simp_tac(srw_ss())[]
      \\ Q.LIST_EXISTS_TAC [`t2`,`b2`,`c`] \\ full_simp_tac(srw_ss())[]
      \\ srw_tac[][] \\ NO_TAC)
    \\ REPEAT STRIP_TAC
    \\ IMP_RES_TAC bvlPropsTheory.evaluate_SING \\
      full_simp_tac(srw_ss())[]
    \\ Cases_on `d1 = Boolv T` \\ full_simp_tac(srw_ss())[]
    THEN1
     (IMP_RES_TAC compile_exps_LENGTH
      \\ `?d. c1 = [d]` by (Cases_on `c1` \\
        full_simp_tac(srw_ss())[LENGTH_NIL])
      \\ SIMP_TAC std_ss [Once iEval_def] \\ full_simp_tac(srw_ss())[]
      \\ `?d2. c2 = [d2]` by (Cases_on `c2` \\
        full_simp_tac(srw_ss())[LENGTH_NIL]) \\
        full_simp_tac(srw_ss())[]
      \\ Q.PAT_X_ASSUM `!nn mm. bbb` (MP_TAC o Q.SPEC `n1`) \\
        full_simp_tac(srw_ss())[]
      \\ `aux_code_installed (append aux2) t2.code` by
       (full_simp_tac(srw_ss())[GSYM PULL_FORALL]
        \\ imp_res_tac evaluate_code_mono \\ fs [inc_clock_def]
        \\ match_mp_tac aux_code_installed_subspt
        \\ asm_exists_tac \\ fs [])
      \\ REPEAT STRIP_TAC
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t2`,`b2`]) \\
        full_simp_tac(srw_ss())[]
      \\ impl_tac >- metis_tac[evaluate_global_mono,inc_clock_global]
      \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[GSYM PULL_FORALL]
      \\ IMP_RES_TAC evaluate_inv_clock \\
        full_simp_tac(srw_ss())[inc_clock_ADD]
      \\ REV_FULL_SIMP_TAC std_ss []
      \\ Q.LIST_EXISTS_TAC [`t2'`,`b2'`,`c' + c`] \\
        full_simp_tac(srw_ss())[]
      \\ full_simp_tac(srw_ss())[adjust_bv_def]
      \\ IMP_RES_TAC evaluate_refs_SUBSET \\
        full_simp_tac(srw_ss())[SUBSET_DEF])
    \\ Cases_on `d1 = Boolv F` \\ full_simp_tac(srw_ss())[]
    THEN1
     (IMP_RES_TAC compile_exps_LENGTH
      \\ `?d. c1 = [d]` by (Cases_on `c1` \\
        full_simp_tac(srw_ss())[LENGTH_NIL])
      \\ SIMP_TAC std_ss [Once iEval_def] \\ full_simp_tac(srw_ss())[]
      \\ `?d3. c3 = [d3]` by (Cases_on `c3` \\
        full_simp_tac(srw_ss())[LENGTH_NIL]) \\
        full_simp_tac(srw_ss())[]
      \\ Q.PAT_X_ASSUM `!nn mm. bbb` (MP_TAC o Q.SPEC `n2`) \\
        full_simp_tac(srw_ss())[]
      \\ `aux_code_installed (append aux3) t2.code` by
       (full_simp_tac(srw_ss())[GSYM PULL_FORALL]
        \\ imp_res_tac evaluate_code_mono \\ fs [inc_clock_def]
        \\ match_mp_tac aux_code_installed_subspt
        \\ asm_exists_tac \\ fs [])
      \\ REPEAT STRIP_TAC
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t2`,`b2`]) \\
        full_simp_tac(srw_ss())[]
      \\ impl_tac >- metis_tac[evaluate_global_mono,inc_clock_global]
      \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[GSYM PULL_FORALL]
      \\ IMP_RES_TAC evaluate_inv_clock \\
        full_simp_tac(srw_ss())[inc_clock_ADD]
      \\ REV_FULL_SIMP_TAC std_ss []
      \\ Q.LIST_EXISTS_TAC [`t2'`,`b2'`,`c' + c`] \\
        full_simp_tac(srw_ss())[]
      \\ full_simp_tac(srw_ss())[adjust_bv_def]
      \\ IMP_RES_TAC evaluate_refs_SUBSET \\
        full_simp_tac(srw_ss())[SUBSET_DEF])
QED
*)

(* HOL4 ML code, not ported:
Resume compile_exps_correct[Let]:
  REPEAT STRIP_TAC
  \\ full_simp_tac(srw_ss())[bEval_def,compile_exps_def,
        iEval_def,bEvery_def,handle_ok_def]
  \\ note_tac "Let" \\ reverse (Cases_on `NULL xs`) THEN1
     (`?c1 aux1 n1. compile_exps n xs = (c1,aux1,n1)` by METIS_TAC
       [PAIR]
      \\ `?c2 aux2 n2. compile_exps n1 [x2] = (c2,aux2,n2)` by METIS_TAC
        [PAIR]
      \\ full_simp_tac(srw_ss())[LET_DEF] \\ SRW_TAC [] []
      \\ full_simp_tac(srw_ss())[PULL_FORALL]
      \\ `?res5 s5. evaluate (xs,env,s) = (res5,s5)` by METIS_TAC [PAIR]
      \\ IMP_RES_TAC evaluate_ok \\ full_simp_tac(srw_ss())[]
      \\ IMP_RES_TAC aux_code_installed_APPEND \\ SRW_TAC [] []
      \\ full_simp_tac(srw_ss())[] \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC
        `n`)
      \\ full_simp_tac(srw_ss())[LENGTH_NIL,NULL_EQ]
      \\ reverse (Cases_on `res5`) \\ full_simp_tac(srw_ss())[] \\
        REPEAT STRIP_TAC
      \\ POP_ASSUM (MP_TAC o Q.SPECL [`t1`,`b1`]) \\
        full_simp_tac(srw_ss())[]
      \\ TRY (
        impl_tac >- (rpt strip_tac >> full_simp_tac(srw_ss())[])
        \\ REPEAT STRIP_TAC \\ IMP_RES_TAC compile_exps_LENGTH
        \\ `?d. c2 = [d]` by (Cases_on `c2` \\
          full_simp_tac(srw_ss())[LENGTH_NIL])
        \\ SIMP_TAC std_ss [Once iEval_def] \\ full_simp_tac(srw_ss())[]
        \\ Q.LIST_EXISTS_TAC [`t2`,`b2`,`c`] \\
          full_simp_tac(srw_ss())[]
        \\ srw_tac[][] \\ NO_TAC)
      \\ REPEAT STRIP_TAC
      \\ Q.MATCH_ASSUM_RENAME_TAC `evaluate ([x2],a ++ env,s5) =
        (res6,s6)`
      \\ Q.PAT_X_ASSUM `!nn mm. bbb` (MP_TAC o Q.SPEC `n1`)
      \\ full_simp_tac(srw_ss())[]
      \\ REPEAT STRIP_TAC
      \\ IMP_RES_TAC compile_exps_LENGTH
      \\ `?d. c2 = [d]` by (Cases_on `c2`
           \\ full_simp_tac(srw_ss())[LENGTH_NIL]) \\
             full_simp_tac(srw_ss())[]
      \\ `aux_code_installed (append aux2) t2.code` by
       (full_simp_tac(srw_ss())[GSYM PULL_FORALL]
        \\ imp_res_tac evaluate_code_mono \\ fs [inc_clock_def]
        \\ match_mp_tac aux_code_installed_subspt
        \\ asm_exists_tac \\ fs [])
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t2`,`b2`]) \\
        full_simp_tac(srw_ss())[]
      \\ impl_tac >- metis_tac[evaluate_global_mono,inc_clock_global]
      \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[GSYM PULL_FORALL]
      \\ Q.MATCH_ASSUM_RENAME_TAC
          `evaluate ([d],MAP (adjust_bv b3) a ++
                      MAP (adjust_bv b3) env,inc_clock c4 t2) =
             (map_result (MAP (adjust_bv b3)) (λv. Exn (adjust_bv b3 v))
               res6,t3)`
      \\ IMP_RES_TAC evaluate_inv_clock
      \\ full_simp_tac(srw_ss())[inc_clock_ADD]
      \\ ONCE_REWRITE_TAC [iEval_def] \\ full_simp_tac(srw_ss())[]
      \\ full_simp_tac(srw_ss())[MAP_APPEND_MAP_EQ]
      \\ REV_FULL_SIMP_TAC std_ss []
      \\ Q.LIST_EXISTS_TAC [`t3`,`b3`,`c4 + c`] \\
        full_simp_tac(srw_ss())[]
      \\ IMP_RES_TAC evaluate_refs_SUBSET \\
        full_simp_tac(srw_ss())[SUBSET_DEF])
    \\ fs [LENGTH_NIL,NULL_EQ] \\ rveq \\ fs [bvlSemTheory.evaluate_def]
    \\ Cases_on `x2` \\ fs
      [bvl_handleProofTheory.let_ok_def,destLet_def]
    \\ ntac 2 (pairarg_tac \\ fs []) \\ rveq \\ fs []
    \\ fs [bviSemTheory.evaluate_def,bvlSemTheory.evaluate_def]
    \\ Cases_on `evaluate (l,env,s)` \\ fs []
    \\ first_x_assum (qspec_then `l` (mp_tac o SRULE[GSYM PULL_FORALL]))
    \\ impl_tac >- simp[]
    \\ disch_then old_drule
    \\ `q ≠ Rerr (Rabort Rtype_error)` by (rpt strip_tac \\ fs []) \\ fs
      []
    \\ rpt (disch_then old_drule) \\ fs []
    \\ impl_tac THEN1
     (ntac 3 (IMP_RES_TAC aux_code_installed_APPEND \\ fs[])
      \\ match_mp_tac bvl_handleProofTheory.handle_ok_Var_Const_list \\
        fs []
      \\ fs [EVERY_MEM] \\ rpt strip_tac
      \\ first_x_assum old_drule \\ Cases_on `x` \\ fs [isVar_def])
    \\ strip_tac \\ fs []
    \\ reverse (Cases_on `q`)
    \\ fs [semanticPrimitivesPropsTheory.map_result_def] \\ rveq \\ fs
      []
    THEN1 (Q.LIST_EXISTS_TAC [`t2`,`b2`,`c`] \\ fs [find_code_def])
    \\ ntac 3 (IMP_RES_TAC aux_code_installed_APPEND \\ fs[])
    \\ fs [aux_code_installed_def,compile_aux_def]
    \\ imp_res_tac evaluate_IMP_LENGTH \\ fs []
    \\ imp_res_tac compile_exps_LENGTH \\ fs []
    \\ `r = s` by
     (old_drule (evaluate_Var_list
         |> INST_TYPE [beta|->``:'ffi``,alpha|->``:num # 'c``] |>
           GEN_ALL)
      \\ disch_then (qspecl_then [`s`,`env`] mp_tac) \\ fs []) \\ rveq
    \\ first_x_assum (qspec_then `[e]` (mp_tac o SRULE[GSYM
      PULL_FORALL]))
    \\ impl_tac >- simp[]
    \\ `evaluate ([e],a,r) = (res,s2)` by
     (qpat_x_assum `_ = (res,s2)` (fn th => once_rewrite_tac [GSYM th])
      \\ match_mp_tac (GSYM bEval_bVarBound) \\ fs [] \\ NO_TAC)
    \\ rpt (disch_then old_drule \\ fs [])
    \\ impl_tac
    THEN1
     (rpt strip_tac \\ fs[handle_ok_def]
      \\ imp_res_tac bviPropsTheory.evaluate_code_mono \\ fs
        [inc_clock_def]
      \\ TRY (match_mp_tac aux_code_installed_subspt \\ asm_exists_tac
        \\ fs [])
      \\ imp_res_tac evaluate_global_mono
      \\ fs [inc_clock_def]
      \\ imp_res_tac EVERY_isVar_evaluate_Rval_MEM
      \\ fs [EVERY_MEM] \\ metis_tac [])
    \\ strip_tac
    \\ qpat_x_assum `evaluate (c2,_) = _` mp_tac
    \\ old_drule bviPropsTheory.evaluate_add_clock \\ simp[]
    \\ disch_then (qspec_then `c'+1` mp_tac) \\ strip_tac
    \\ `inc_clock (c'+1) (inc_clock c t1) = inc_clock (c+c'+1) t1` by
          (fs [inc_clock_def] \\ NO_TAC)
    \\ fs [] \\ strip_tac
    \\ Q.LIST_EXISTS_TAC [`t2'`,`b2'`,`c+c'+1`]
    \\ `MAP (adjust_bv b2') env = MAP (adjust_bv b2) env` by
     (full_simp_tac(srw_ss())[MAP_EQ_f] \\ REPEAT STRIP_TAC
      \\ MATCH_MP_TAC (bv_ok_IMP_adjust_bv_eq |> GEN_ALL)
      \\ Q.EXISTS_TAC `r.refs` \\ full_simp_tac(srw_ss())[]
      \\ IMP_RES_TAC evaluate_ok \\ full_simp_tac(srw_ss())[]
      \\ REV_FULL_SIMP_TAC std_ss []
      \\ full_simp_tac(srw_ss())[EVERY_MEM] \\ RES_TAC \\ NO_TAC)
    \\ fs [find_code_def]
    \\ `?d2. c2 = [d2]` by (Cases_on `c2` \\ fs [LENGTH_NIL]) \\ rveq \\
      fs []
    \\ old_drule bvi_letProofTheory.evaluate_compile_exp
    \\ impl_tac THEN1 (Cases_on `res` \\ fs
      [semanticPrimitivesPropsTheory.map_result_def])
    \\ strip_tac \\ fs []
    \\ imp_res_tac evaluate_code_mono \\ fs [subspt_lookup]
    \\ res_tac \\ fs []
    \\ `dec_clock 1 (inc_clock (c' + 1) t2) = inc_clock c' t2` by
           (EVAL_TAC \\ fs [] \\ NO_TAC)
    \\ fs [] \\ Cases_on `res` \\ fs
      [semanticPrimitivesPropsTheory.map_result_def]
    \\ Cases_on `e'` \\ fs
      [semanticPrimitivesPropsTheory.map_error_result_def]
QED
*)

(* HOL4 ML code, not ported:
Resume compile_exps_correct[Raise]:
  REPEAT STRIP_TAC
  \\ full_simp_tac(srw_ss())[bEval_def,compile_exps_def,
        iEval_def,bEvery_def,handle_ok_def]
  \\ note_tac "Raise" \\
    `?c1 aux1 n1. compile_exps n [x1] = (c1,aux1,n1)` by METIS_TAC
      [PAIR]
    \\ full_simp_tac(srw_ss())[LET_DEF] \\ SRW_TAC [] [] \\
      full_simp_tac(srw_ss())[PULL_FORALL]
    \\ IMP_RES_TAC compile_exps_LENGTH
    \\ `?d. c1 = [d]` by (Cases_on `c1` \\
      full_simp_tac(srw_ss())[LENGTH_NIL]) \\ full_simp_tac(srw_ss())[]
    \\ SRW_TAC [] []
    \\ `?res5 s5. evaluate ([x1],env,s) = (res5,s5)` by METIS_TAC [PAIR]
    \\ reverse (Cases_on `res5`) \\ full_simp_tac(srw_ss())[] \\ REPEAT
      STRIP_TAC
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `n`) \\ full_simp_tac(srw_ss())[]
    \\ TRY (SRW_TAC [] [] \\ full_simp_tac(srw_ss())[]
      \\ REPEAT STRIP_TAC \\ RES_TAC
      \\ Q.LIST_EXISTS_TAC [`t2`,`b2`,`c`] \\ full_simp_tac(srw_ss())[]
      \\ SIMP_TAC std_ss [Once bviPropsTheory.evaluate_CONS] \\
        full_simp_tac(srw_ss())[]
      \\ full_simp_tac(srw_ss())[iEval_def] \\ NO_TAC)
    \\ REPEAT STRIP_TAC \\ RES_TAC \\ full_simp_tac(srw_ss())[iEval_def]
    \\ Q.LIST_EXISTS_TAC [`t2`,`b2`,`c`] \\ full_simp_tac(srw_ss())[] \\
      SRW_TAC [] []
    \\ IMP_RES_TAC bvlPropsTheory.evaluate_SING \\ SRW_TAC [] []
QED
*)

(* HOL4 ML code, not ported:
Resume compile_exps_correct[Handle]:
  REPEAT STRIP_TAC
  \\ full_simp_tac(srw_ss())[bEval_def,compile_exps_def,
        iEval_def,bEvery_def,handle_ok_def]
  \\ note_tac "Handle" \\
    Cases_on `x1` \\ full_simp_tac(srw_ss())[handle_ok_def,destLet_def]
    \\ full_simp_tac(srw_ss())[LET_DEF]
    \\ imp_res_tac compile_exps_Var_list
    \\ first_x_assum(qspec_then`n`strip_assume_tac)
    \\ full_simp_tac (srw_ss()) []
    \\ `?c2 aux2 n2. compile_exps n [e] = (c2,aux2,n2)` by METIS_TAC
      [PAIR]
    \\ `?c3 aux3 n3. compile_exps n2' [x2] = (c3,aux3,n3)` by METIS_TAC
      [PAIR]
    \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    \\ full_simp_tac(srw_ss())[bEval_def]
    \\ Q.ISPECL_THEN[`s1`,`l`]mp_tac (Q.GEN`s`evaluate_Var_list)
    \\ full_simp_tac(srw_ss())[]
    \\ STRIP_TAC \\ full_simp_tac(srw_ss())[]
    \\ `evaluate ([e],vs ++ env,s1) = evaluate ([e],vs,s1)` by
      (MATCH_MP_TAC bEval_bVarBound \\ fs[])
    \\ full_simp_tac(srw_ss())[] \\ POP_ASSUM (K ALL_TAC)
    \\ Cases_on `evaluate ([e],vs,s1)` \\ full_simp_tac(srw_ss())[]
    \\ `?d2. c2 = [d2]` by
           (IMP_RES_TAC compile_exps_LENGTH \\ Cases_on `c2`
            \\ full_simp_tac(srw_ss())[LENGTH_NIL])
    \\ `?d3. c3 = [d3]` by
           (IMP_RES_TAC compile_exps_LENGTH \\ Cases_on `c3`
            \\ full_simp_tac(srw_ss())[LENGTH_NIL])
    \\ full_simp_tac(srw_ss())[] \\ NTAC 2 (POP_ASSUM (K ALL_TAC))
    \\ `handle_ok l` by
     (match_mp_tac bvl_handleProofTheory.handle_ok_Var_Const_list \\ fs
       []
      \\ fs [EVERY_MEM] \\ rpt strip_tac
      \\ first_x_assum old_drule \\ Cases_on `x` \\ fs [isVar_def])
    \\ first_x_assum (qspec_then `[e]` (mp_tac o SRULE[GSYM
      PULL_EXISTS]))
    \\ fs [] \\ strip_tac
    \\ `EVERY (bv_ok s1.refs) vs` by
     (imp_res_tac evaluate_IMP_bv_ok
      \\ IMP_RES_TAC evaluate_ok \\ rfs [] \\ NO_TAC)
    \\ (Cases_on `q`) \\ full_simp_tac(srw_ss())[]
    THEN1 (* Result case *)
     (SRW_TAC [] [] \\ FIRST_X_ASSUM (qspecl_then [`vs`,`n`] mp_tac)
      \\ full_simp_tac(srw_ss())[compile_exps_def,compile_exps_Var_list
        ,LET_DEF]
      \\ STRIP_TAC \\ POP_ASSUM (Q.SPECL_THEN [`t1`,`b1`]mp_tac)
      \\ full_simp_tac(srw_ss())[]
      \\ IMP_RES_TAC aux_code_installed_APPEND \\
        full_simp_tac(srw_ss())[]
      \\ IMP_RES_TAC aux_code_installed_APPEND \\
        full_simp_tac(srw_ss())[]
      \\ REPEAT STRIP_TAC
      \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
      \\ full_simp_tac(srw_ss())[aux_code_installed_def,
           iEval_def,find_code_def,compile_aux_def]
      \\ IMP_RES_TAC (GEN_ALL evaluate_MAP_Var) \\
        full_simp_tac(srw_ss())[]
      \\ imp_res_tac bviPropsTheory.evaluate_code_mono \\ fs
        [subspt_lookup]
      \\ `evaluate ([d2],MAP (adjust_bv b2) vs ++ MAP (adjust_bv b2)
        env,
            inc_clock c t1) =
          evaluate ([d2],MAP (adjust_bv b2) vs,inc_clock c t1)` by
       (match_mp_tac iEval_bVarBound_extra \\ fs []
        \\ qexists_tac `[e]` \\ qexists_tac `n` \\ fs [])
      \\ full_simp_tac(srw_ss())[] \\ POP_ASSUM (K ALL_TAC) \\ fs []
      \\ Q.LIST_EXISTS_TAC [`t2`,`b2`,`c + 1`] \\
        full_simp_tac(srw_ss())[]
      \\ `dec_clock 1 (inc_clock (c + 1) t1) = inc_clock c t1` by
        (EVAL_TAC \\
          full_simp_tac(srw_ss())[bviSemTheory.state_component_equality]
         \\ DECIDE_TAC) \\ full_simp_tac(srw_ss())[] \\ fs []
      \\ old_drule bvi_letProofTheory.evaluate_compile_exp \\ fs[] \\ rw
        []
      \\ full_simp_tac(srw_ss())[MAP_EQ_f] \\ REPEAT STRIP_TAC
      \\ MATCH_MP_TAC (bv_ok_IMP_adjust_bv_eq |> GEN_ALL)
      \\ Q.EXISTS_TAC `s1.refs` \\ full_simp_tac(srw_ss())[]
      \\ IMP_RES_TAC evaluate_ok \\ full_simp_tac(srw_ss())[]
      \\ REV_FULL_SIMP_TAC std_ss []
      \\ full_simp_tac(srw_ss())[EVERY_MEM] \\ RES_TAC)
    \\ (Cases_on`e'`) \\ full_simp_tac(srw_ss())[]
    THEN1 (* Raise case *)
     (SRW_TAC [] [] \\ FIRST_X_ASSUM (qspecl_then [`vs`,`n`] mp_tac)
      \\ full_simp_tac(srw_ss())[compile_exps_def,compile_exps_Var_list
        ,LET_DEF]
      \\ STRIP_TAC \\ POP_ASSUM (MP_TAC o Q.SPECL [`t1`,`b1`])
      \\ full_simp_tac(srw_ss())[]
      \\ IMP_RES_TAC aux_code_installed_APPEND \\
        full_simp_tac(srw_ss())[]
      \\ IMP_RES_TAC aux_code_installed_APPEND \\
        full_simp_tac(srw_ss())[]
      \\ REPEAT STRIP_TAC
      \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
      \\ full_simp_tac(srw_ss())[aux_code_installed_def,iEval_def
        ,find_code_def,compile_aux_def]
      \\ IMP_RES_TAC (GEN_ALL evaluate_MAP_Var) \\
        full_simp_tac(srw_ss())[]
      \\ `evaluate ([d2],MAP (adjust_bv b2) vs ++ MAP (adjust_bv b2)
        env,
            inc_clock c t1) =
          evaluate ([d2],MAP (adjust_bv b2) vs,inc_clock c t1)` by
       (match_mp_tac iEval_bVarBound_extra \\ fs []
        \\ qexists_tac `[e]` \\ qexists_tac `n` \\ fs [])
      \\ full_simp_tac(srw_ss())[] \\ POP_ASSUM (K ALL_TAC)
      \\ Q.PAT_X_ASSUM `!nn mm nn1. bbb` (MP_TAC o Q.SPEC `n2'`)
      \\ full_simp_tac(srw_ss())[]
      \\ REPEAT STRIP_TAC \\ fs []
      \\ POP_ASSUM (MP_TAC o Q.SPECL [`t2`,`b2`]) \\
        full_simp_tac(srw_ss())[]
      \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
       (IMP_RES_TAC evaluate_ok \\ full_simp_tac(srw_ss())[]
        \\ REV_FULL_SIMP_TAC std_ss []
        \\ IMP_RES_TAC aux_code_installed_APPEND \\
          full_simp_tac(srw_ss())[]
        \\ IMP_RES_TAC aux_code_installed_APPEND \\
          full_simp_tac(srw_ss())[]
        \\ imp_res_tac evaluate_global_mono
        \\ full_simp_tac(srw_ss())[inc_clock_def]
        \\ sg `EVERY (bv_ok r.refs) env` \\ full_simp_tac(srw_ss())[]
        \\ full_simp_tac(srw_ss())[EVERY_MEM] \\ REPEAT STRIP_TAC \\
          RES_TAC
        \\ IMP_RES_TAC evaluate_refs_SUBSET
        \\ IMP_RES_TAC bv_ok_SUBSET_IMP
        \\ imp_res_tac evaluate_code_mono \\ fs [inc_clock_def]
        \\ match_mp_tac aux_code_installed_subspt
        \\ asm_exists_tac \\ fs [])
      \\ REPEAT STRIP_TAC
      \\ Q.LIST_EXISTS_TAC [`t2'`,`b2'`,`c' + c + 1`] \\
        full_simp_tac(srw_ss())[]
      \\ `dec_clock 1 (inc_clock (c' + c + 1) t1) = inc_clock (c' + c)
        t1` by
        (EVAL_TAC \\
          full_simp_tac(srw_ss())[bviSemTheory.state_component_equality]
         \\ DECIDE_TAC) \\ full_simp_tac(srw_ss())[]
      \\ IMP_RES_TAC evaluate_inv_clock \\
        full_simp_tac(srw_ss())[inc_clock_ADD]
      \\ `MAP (adjust_bv b2) vs = MAP (adjust_bv b2') vs` by
       (full_simp_tac(srw_ss())[MAP_EQ_f] \\ REPEAT STRIP_TAC
        \\ MATCH_MP_TAC (bv_ok_IMP_adjust_bv_eq |> GEN_ALL)
        \\ Q.EXISTS_TAC `r.refs` \\ full_simp_tac(srw_ss())[]
        \\ IMP_RES_TAC evaluate_ok \\ full_simp_tac(srw_ss())[]
        \\ REV_FULL_SIMP_TAC std_ss []
        \\ full_simp_tac(srw_ss())[EVERY_MEM] \\ RES_TAC)
      \\ full_simp_tac(srw_ss())[] \\ IMP_RES_TAC evaluate_refs_SUBSET
      \\ full_simp_tac(srw_ss())[SUBSET_DEF]
      \\ qpat_x_assum `!n. _ = _` (qspec_then `c'` assume_tac) \\ fs []
      \\ old_drule bvi_letProofTheory.evaluate_compile_exp \\ fs[]
      \\ full_simp_tac(srw_ss())[MAP_EQ_f,call_SOME_handler_result] \\
        REPEAT STRIP_TAC
      \\ MATCH_MP_TAC (bv_ok_IMP_adjust_bv_eq |> GEN_ALL)
      \\ Q.EXISTS_TAC `s1.refs` \\ full_simp_tac(srw_ss())[]
      \\ IMP_RES_TAC evaluate_ok \\ full_simp_tac(srw_ss())[]
      \\ REV_FULL_SIMP_TAC std_ss []
      \\ full_simp_tac(srw_ss())[EVERY_MEM] \\ RES_TAC)
    THEN1 (* abort case *)
     (SRW_TAC [] [] \\ FIRST_X_ASSUM (qspecl_then [`vs`,`n`] mp_tac)
      \\ full_simp_tac(srw_ss())[compile_exps_def,compile_exps_Var_list
        ,LET_DEF]
      \\ STRIP_TAC \\ POP_ASSUM (MP_TAC o Q.SPECL [`t1`,`b1`])
      \\ full_simp_tac(srw_ss())[]
      \\ IMP_RES_TAC aux_code_installed_APPEND \\
        full_simp_tac(srw_ss())[]
      \\ IMP_RES_TAC aux_code_installed_APPEND \\
        full_simp_tac(srw_ss())[]
      \\ REPEAT STRIP_TAC
      \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
      \\ full_simp_tac(srw_ss())[aux_code_installed_def,iEval_def,
            find_code_def,compile_aux_def]
      \\ IMP_RES_TAC (GEN_ALL evaluate_MAP_Var) \\
        full_simp_tac(srw_ss())[]
      \\ `evaluate ([d2],MAP (adjust_bv b2) vs ++ MAP (adjust_bv b2)
        env,
            inc_clock c t1) =
          evaluate ([d2],MAP (adjust_bv b2) vs,inc_clock c t1)` by
       (match_mp_tac iEval_bVarBound_extra \\ fs []
        \\ qexists_tac `[e]` \\ qexists_tac `n` \\ fs [])
      \\ full_simp_tac(srw_ss())[] \\ POP_ASSUM (K ALL_TAC) \\ fs []
      \\ Q.LIST_EXISTS_TAC [`t2`,`b2`,`c + 1`] \\
        full_simp_tac(srw_ss())[]
      \\ `dec_clock 1 (inc_clock (c + 1) t1) = inc_clock c t1` by
        (EVAL_TAC \\
          full_simp_tac(srw_ss())[bviSemTheory.state_component_equality]
         \\ DECIDE_TAC) \\ full_simp_tac(srw_ss())[]
      \\ old_drule bvi_letProofTheory.evaluate_compile_exp \\ fs[]
      \\ full_simp_tac(srw_ss())[MAP_EQ_f] \\ REPEAT STRIP_TAC
      \\ MATCH_MP_TAC (bv_ok_IMP_adjust_bv_eq |> GEN_ALL)
      \\ Q.EXISTS_TAC `s1.refs` \\ full_simp_tac(srw_ss())[]
      \\ IMP_RES_TAC evaluate_ok \\ full_simp_tac(srw_ss())[]
      \\ REV_FULL_SIMP_TAC std_ss []
      \\ full_simp_tac(srw_ss())[EVERY_MEM] \\ RES_TAC)
QED
*)

(* HOL4 ML code, not ported:
Resume compile_exps_correct[Force]:
  REPEAT STRIP_TAC
  \\ full_simp_tac(srw_ss())[bEval_def,compile_exps_def,
        iEval_def,bEvery_def,handle_ok_def]
  \\ note_tac "Force"
    \\ gvs [AllCaseEqs()]
    >- (
      last_x_assum kall_tac
      \\ gvs [evaluate_def, EL_MAP, AllCaseEqs(), PULL_EXISTS,
              oneline bvlSemTheory.dest_thunk_def, oneline
                dest_thunk_def,
              adjust_bv_def]
      \\ drule_all state_rel_FLOOKUP_Thunk \\ rw [] \\ gvs []
      \\ goal_assum old_drule \\ gvs [inc_clock_def]
      \\ qexists ‘0’ \\ gvs [state_rel_def])
    >- (
      gvs [evaluate_def, EL_MAP, AllCaseEqs(), PULL_EXISTS,
           oneline bvlSemTheory.dest_thunk_def, oneline dest_thunk_def,
           adjust_bv_def]
      \\ drule_all state_rel_FLOOKUP_Thunk \\ rw [] \\ gvs []
      \\ goal_assum old_drule \\ gvs [inc_clock_def]
      \\ qexistsl [‘t1’, ‘0’] \\ gvs [state_rel_def,
        state_component_equality]
      \\ gvs [find_code_def, AllCaseEqs()]
      \\ first_x_assum old_drule \\ rw [] \\ gvs []
      \\ pairarg_tac \\ gvs [])
    >- (
      gvs [oneline bvlSemTheory.dest_thunk_def, oneline dest_thunk_def,
           AllCaseEqs()]
      \\ ‘state_rel b1 (dec_clock 1 s) (dec_clock 1 t1)’
        by gvs [state_rel_def, dec_clock_def,
          bvlSemTheory.dec_clock_def]
      \\ last_x_assum $ drule_at (Pat ‘state_rel _ _ _’) \\ gvs []
      \\ gvs [find_code_def, AllCaseEqs(), bv_ok_def]
      \\ pop_assum kall_tac
      \\ qpat_x_assum ‘state_rel _ _ _’ mp_tac
      \\ rw [Once state_rel_def]
      \\ first_x_assum old_drule \\ rw []
      \\ pairarg_tac \\ gvs []
      \\ first_x_assum old_drule \\ gvs []
      \\ impl_tac \\ rw []
      >- gvs [state_ok_def, bvlSemTheory.dec_clock_def]
      >- gvs [FLOOKUP_DEF]
      >- (
        qpat_x_assum ‘state_ok _’ mp_tac
        \\ rw [state_ok_def]
        \\ first_x_assum $ qspec_then ‘ptr’ assume_tac \\ gvs [])
      \\ gvs [adjust_bv_def, inc_clock_def, dec_clock_def]
      \\ goal_assum $ drule_at (Pat ‘state_rel _ _ _’) \\ gvs []
      \\ simp [evaluate_def, EL_MAP, adjust_bv_def, dest_thunk_def] \\
        gvs []
      \\ last_x_assum $ qspec_then ‘ptr’ assume_tac
      \\ gvs [find_code_def, AllCaseEqs(), PULL_EXISTS, dec_clock_def]
      \\ imp_res_tac compile_exps_SING \\ gvs []
      \\ imp_res_tac bvi_letProofTheory.evaluate_compile_exp \\ gvs []
      \\ goal_assum $ drule_at (Pat ‘evaluate _ = _’) \\ gvs []
      \\ conj_tac
      >- (Cases_on `res` \\ gvs [] \\ Cases_on `e` \\ gvs [])
      \\ gvs [MAP_EQ_f] \\ rw []
      \\ irule (GEN_ALL bv_ok_IMP_adjust_bv_eq)
      \\ qexists ‘s.refs’ \\ gvs []
      \\ imp_res_tac evaluate_refs_SUBSET \\ gvs [dec_clock_def]
      \\ imp_res_tac bv_ok_SUBSET_IMP \\ gvs [EVERY_MEM])
QED
*)

(* HOL4 ML code, not ported:
Resume compile_exps_correct[Tick]:
  REPEAT STRIP_TAC
  \\ full_simp_tac(srw_ss())[bEval_def,compile_exps_def,
        iEval_def,bEvery_def,handle_ok_def]
  \\ note_tac "Tick" \\
    `?c1 aux1 n1. compile_exps n [x] = (c1,aux1,n1)` by METIS_TAC [PAIR]
    \\ full_simp_tac(srw_ss())[LET_DEF] \\ SRW_TAC [] []
    \\ full_simp_tac(srw_ss())[PULL_FORALL]
    \\ IMP_RES_TAC compile_exps_LENGTH
    \\ `?d. c1 = [d]` by (Cases_on `c1` \\
      full_simp_tac(srw_ss())[LENGTH_NIL]) \\ full_simp_tac(srw_ss())[]
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `n`) \\ full_simp_tac(srw_ss())[]
    \\ SRW_TAC [] [iEval_def]
    \\ Cases_on `s.clock = 0` \\ full_simp_tac(srw_ss())[] THEN1
     (SRW_TAC [] [] \\ Q.LIST_EXISTS_TAC [`t1`,`b1`,`0`]
      \\ full_simp_tac(srw_ss())[inc_clock_ZERO] \\
        full_simp_tac(srw_ss())[state_rel_def]) \\
        full_simp_tac(srw_ss())[]
    \\ `t1.clock <> 0 /\ !c. (inc_clock c t1).clock <> 0` by
      (EVAL_TAC \\ full_simp_tac(srw_ss())[state_rel_def] \\ DECIDE_TAC)
        \\ full_simp_tac(srw_ss())[]
    \\ REV_FULL_SIMP_TAC std_ss [dec_clock_inv_clock1]
    \\ `(dec_clock 1 s).refs = s.refs` by EVAL_TAC \\
      full_simp_tac(srw_ss())[]
    \\ Q.PAT_X_ASSUM `!xx yy. bbb` (MP_TAC o Q.SPECL [`dec_clock 1
      t1`,`b1`])
    \\ REV_FULL_SIMP_TAC std_ss [dec_clock_inv_clock1]
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
    THEN1 (full_simp_tac(srw_ss())[evaluate_ok_lemma]
           \\ full_simp_tac(srw_ss())[state_rel_def,dec_clock_def
             ,bvlSemTheory.dec_clock_def]
           \\ metis_tac[])
    \\ full_simp_tac(srw_ss())[GSYM PULL_FORALL]
QED
*)

(* HOL4 ML code, not ported:
Resume compile_exps_correct[Call]:
  REPEAT STRIP_TAC
  \\ full_simp_tac(srw_ss())[bEval_def,compile_exps_def,
        iEval_def,bEvery_def,handle_ok_def]
  \\ note_tac "Call" \\
    `?c1 aux1 n1. compile_exps n xs = (c1,aux1,n1)` by METIS_TAC [PAIR]
    \\ full_simp_tac(srw_ss())[LET_DEF] \\ SRW_TAC [] []
    \\ full_simp_tac(srw_ss())[PULL_FORALL]
    \\ `?res5 s5. evaluate (xs,env,s1) = (res5,s5)` by METIS_TAC [PAIR]
    \\ full_simp_tac(srw_ss())[] \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `n`)
    \\ full_simp_tac(srw_ss())[]
    \\ reverse (Cases_on `res5`) \\ full_simp_tac(srw_ss())[] \\ SRW_TAC
      [] []
    \\ first_x_assum (MP_TAC o Q.SPECL [`t1`,`b1`]) \\
      full_simp_tac(srw_ss())[]
    \\ TRY (REPEAT STRIP_TAC \\ IMP_RES_TAC compile_exps_LENGTH
      \\ full_simp_tac(srw_ss())[iEval_def]
      \\ Q.LIST_EXISTS_TAC [`t2`,`b2`,`c`] \\ full_simp_tac(srw_ss())[]
        \\ NO_TAC)
    \\ full_simp_tac(srw_ss())[GSYM PULL_FORALL] \\ REPEAT STRIP_TAC
    \\ full_simp_tac(srw_ss())[iEval_def]
    \\ Cases_on `find_code dest a s5.code` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `x` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `s5.clock < ticks + 1` \\ full_simp_tac(srw_ss())[]
      THEN1
     (Q.LIST_EXISTS_TAC [`t2 with clock := 0`,`b2`,`c`] \\
       full_simp_tac(srw_ss())[]
      \\ SRW_TAC [] []
      \\ TRY (full_simp_tac(srw_ss())[state_rel_def]
              \\ qexists_tac`array_size'` \\ simp[])
      \\ `t2.clock < ticks + 1` by
        (full_simp_tac(srw_ss())[state_rel_def]
                                    \\ rev_full_simp_tac(srw_ss())[])
      \\ full_simp_tac(srw_ss())[]
      \\ reverse (Cases_on `dest`)
      \\ full_simp_tac(srw_ss())[bvlSemTheory.find_code_def
        ,find_code_def]
      THEN1
       (Cases_on `lookup x s5.code` \\ full_simp_tac(srw_ss())[]
        \\ Cases_on `x'` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
        \\ full_simp_tac(srw_ss())[state_rel_def] \\ RES_TAC
        \\ `?x1 x2 x3. compile_exps n' [r] = (x1,x2,x3)` by METIS_TAC
          [PAIR]
        \\ full_simp_tac(srw_ss())[LET_DEF])
      \\ `?x1 l1. a = SNOC x1 l1` by METIS_TAC [SNOC_CASES]
      \\ full_simp_tac(srw_ss())[]
      \\ Cases_on `x1` \\ full_simp_tac(srw_ss())[adjust_bv_def]
      \\ Cases_on `lookup n' s5.code` \\ full_simp_tac(srw_ss())[]
      \\ Cases_on `x` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
      \\ full_simp_tac(srw_ss())[state_rel_def] \\ RES_TAC
      \\ `?x1 x2 x3. compile_exps n'' [r] = (x1,x2,x3)` by METIS_TAC
        [PAIR]
      \\ full_simp_tac(srw_ss())[LET_DEF])
    \\ Q.MATCH_ASSUM_RENAME_TAC `find_code dest a s5.code = SOME
      (args,body)`
    \\ `?n7. let (c7,aux7,n8) = compile_exps n7 [body] in
               (find_code (case dest of NONE => NONE
                           | SOME n => SOME (num_stubs + nss * n))
                 (MAP (adjust_bv b2) a) t2.code =
                 SOME (MAP (adjust_bv b2) args,bvi_let$compile_exp (HD
                   c7))) /\
               aux_code_installed (append aux7) t2.code /\
               handle_ok [body]` by
     (reverse (Cases_on `dest`)
      \\ full_simp_tac(srw_ss())[state_rel_def,find_code_def]
      THEN1 (Cases_on `lookup x s5.code` \\ full_simp_tac(srw_ss())[]
             \\ Cases_on `x'` \\ full_simp_tac(srw_ss())[]
        \\ SRW_TAC [] []
        \\ FIRST_X_ASSUM (qspecl_then
             [`x`,`LENGTH a`,`body`]mp_tac) \\ full_simp_tac(srw_ss())[]
        \\ REPEAT STRIP_TAC \\ Q.EXISTS_TAC `n'` \\
          full_simp_tac(srw_ss())[]
        \\ `?c2 aux2 n2. compile_exps n' [body] = (c2,aux2,n2)` by
          METIS_TAC [PAIR]
        \\ full_simp_tac(srw_ss())[LET_DEF])
      \\ `?a1 a2. a = SNOC a1 a2` by METIS_TAC [SNOC_CASES]
      \\ full_simp_tac(srw_ss())[] \\ Cases_on `a1` \\
        full_simp_tac(srw_ss())[]
      \\ FULL_SIMP_TAC std_ss [GSYM SNOC_APPEND,FRONT_SNOC]
      \\ Cases_on `lookup n' s5.code` \\ full_simp_tac(srw_ss())[]
      \\ Cases_on `x` \\ full_simp_tac(srw_ss())[]
      \\ SRW_TAC [] []
      \\ Q.PAT_X_ASSUM `!x1 x2. bbb` (MP_TAC o Q.SPECL [`n'`])
      \\ full_simp_tac(srw_ss())[]
      \\ REPEAT STRIP_TAC \\ Q.EXISTS_TAC `n''`
      \\ `?c2 aux2 n2. compile_exps n'' [body] = (c2,aux2,n2)` by
        METIS_TAC [PAIR]
      \\ full_simp_tac(srw_ss())[LET_DEF,adjust_bv_def])
    \\ `?c7 aux7 n8. compile_exps n7 [body] = (c7,aux7,n8)` by METIS_TAC
      [PAIR]
    \\ full_simp_tac(srw_ss())[LET_DEF]
    \\ `¬(t2.clock < ticks + 1)` by
      (full_simp_tac(srw_ss())[state_rel_def] \\ REV_FULL_SIMP_TAC
      std_ss [])
    \\ full_simp_tac(srw_ss())[] \\ IMP_RES_TAC compile_exps_LENGTH
    \\ `?d. c7 = [d]` by (Cases_on `c7` \\
      full_simp_tac(srw_ss())[LENGTH_NIL]) \\ full_simp_tac(srw_ss())[]
    \\ Q.PAT_X_ASSUM `!nn mm. bbb` (MP_TAC o Q.SPEC `n7`) \\
      full_simp_tac(srw_ss())[]
    \\ STRIP_TAC
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`dec_clock (ticks + 1)
      t2`,`b2`]) \\ full_simp_tac(srw_ss())[]
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
     (`(dec_clock (ticks + 1) t2).code = t2.code` by (EVAL_TAC \\
       full_simp_tac(srw_ss())[])
      \\ `(dec_clock (ticks + 1) t2).refs = t2.refs` by (EVAL_TAC \\
        full_simp_tac(srw_ss())[])
      \\ IMP_RES_TAC evaluate_ok
      \\ full_simp_tac(srw_ss())[evaluate_ok_lemma] \\ REV_FULL_SIMP_TAC
        std_ss []
      \\ STRIP_TAC THEN1
        (full_simp_tac(srw_ss())[state_rel_def,dec_clock_def
          ,bvlSemTheory.dec_clock_def] >>
         METIS_TAC[])
      \\ IMP_RES_TAC find_code_EVERY_IMP
      \\ imp_res_tac evaluate_global_mono
      \\ full_simp_tac(srw_ss())[])
    \\ STRIP_TAC
    \\ Q.LIST_EXISTS_TAC [`t2'`,`b2'`,`c' + c`] \\
      full_simp_tac(srw_ss())[]
    \\ IMP_RES_TAC evaluate_inv_clock
    \\ full_simp_tac(srw_ss())[inc_clock_ADD]
    \\ REV_FULL_SIMP_TAC std_ss []
    \\ `MAP (adjust_bv b2') env = MAP (adjust_bv b2) env` by
     (full_simp_tac(srw_ss())[MAP_EQ_f] \\ REPEAT STRIP_TAC
      \\ MATCH_MP_TAC (bv_ok_IMP_adjust_bv_eq |> GEN_ALL)
      \\ Q.EXISTS_TAC `s5.refs` \\ fs[bvlSemTheory.dec_clock_def]
      \\ IMP_RES_TAC evaluate_refs_SUBSET
      \\ IMP_RES_TAC bv_ok_SUBSET_IMP \\ fs[EVERY_MEM] \\ NO_TAC)
    \\ `(inc_clock c' t2).code = t2.code` by (EVAL_TAC \\
      full_simp_tac(srw_ss())[]) \\ full_simp_tac(srw_ss())[]
    \\ `¬((inc_clock c' t2).clock < ticks + 1)` by
      (full_simp_tac(srw_ss())[inc_clock_def] \\ decide_tac)
    \\ full_simp_tac(srw_ss())[]
    \\ REV_FULL_SIMP_TAC std_ss [dec_clock_inv_clock]
    \\ full_simp_tac(srw_ss())[bvlSemTheory.dec_clock_def]
    \\ IMP_RES_TAC evaluate_refs_SUBSET \\
      full_simp_tac(srw_ss())[SUBSET_DEF]
    \\ Cases_on `res` \\ full_simp_tac(srw_ss())[]
    >-
      (imp_res_tac bvi_letProofTheory.evaluate_compile_exp \\ fs[])
    >>
      (imp_res_tac bvi_letProofTheory.evaluate_compile_exp \\ fs[]
      \\ Cases_on`e` \\ full_simp_tac(srw_ss())[])
QED
*)

(* HOL4 ML code, not ported:
Finalise compile_exps_correct;
*)

(* composed compiler correctness *)

let full_cc_def = cake_define
  `full_cc c cc =
     (let limit' = bvl_to_bvi_config_inline_size_limit c in
     let split = bvl_to_bvi_config_split_main_at_seq c in
     let cut = bvl_to_bvi_config_exp_cut c in
       state_cc (compile_inc limit' split cut) (state_cc compile_inc
         (state_cc (bvi_tailrec_compile_prog
           (bvl_to_bvi_config_do_tailrec c))
           (state_cc (bvi_tmc_compile_prog (bvl_to_bvi_config_do_tmc
             c))
             (state_cc bvi_inline_compile_inc cc)))))`;;

let full_co_def = cake_define
  `full_co c co =
     (let limit' = bvl_to_bvi_config_inline_size_limit c in
     let split = bvl_to_bvi_config_split_main_at_seq c in
     let cut = bvl_to_bvi_config_exp_cut c in
       state_co bvi_inline_compile_inc
         (state_co (bvi_tmc_compile_prog (bvl_to_bvi_config_do_tmc
           c))
           (state_co (bvi_tailrec_compile_prog
             (bvl_to_bvi_config_do_tailrec c))
             (state_co compile_inc
               (state_co (compile_inc limit' split cut) co)))))`;;

(* --- no_mutcons: syntactic absence of MutCons operations ---

   The bvi_tmc pass requires its input to be free of MutCons operations
   (the no_mutcons conjunct of bvi_tmc's input_condition).  This holds
   unconditionally: compile_op compiles out the mem_ops reserved for
   bvi_tmc (bvlSem$do_app is Error on them), so no bvi code produced by
   bvl_to_bvi contains them.  The lemmas below carry the property
   through bvi_let and bvi_tailrec to the two input_condition
   obligations in compile_semantics below. *)

(* no_mutcons preservation: bvi_let *)

(* no_mutcons preservation: bvl_to_bvi compile *)

(* no_mutcons preservation: bvi_tailrec *)

(* A name outside namespace 2 cannot be one of bvi_tailrec's fresh
   names,
   which are all congruent to num_stubs + 2 modulo the namespace count.
     *)
(* NB free_names must be qualified: bvi_tmcProof defines an identically
   printing (and identically stated) constant of the same name. *)

(* The code-label containment for the whole pass boundary, composing all
   four
   stages of [compile]: bvl_inline, compile_prog, bvi_tailrec and
     bvi_inline.
   The last two only ever shrink the label set relative to the names
     they keep,
   so the shape matches compile_prog_get_code_labels above, widened by
     the
   fresh names bvi_tailrec allocates. *)
