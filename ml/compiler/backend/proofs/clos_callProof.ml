(* ======================================================== *)
(*  clos_callProof: ported from HOL4's
    compiler/backend/proofs/clos_callProofScript.sml  *)
(* ======================================================== *)

(*
  Correctness proof for clos_call
*)

needs "compiler/backend/clos_call.ml";;
needs "compiler/backend/db_vars.ml";;
needs "compiler/backend/semantics/backendProps.ml";;
needs "compiler/backend/semantics/closProps.ml";;
needs "compiler/backend/semantics/closSem.ml";;
needs "lib/sptree.ml";;
needs "semantics/ast.ml";;
needs "semantics/semanticPrimitives.ml";;

(* TODO These are the same. Put in closLang? *)

(* TODO: move *)

(* HOL4 ML code, not ported:
val PUSH_EXISTS_IMP = SPEC_ALL RIGHT_EXISTS_IMP_THM;
*)

(* HOL4 ML code, not ported:
val evaluate_add_clock =
  evaluate_add_to_clock
  |> SIMP_RULE (srw_ss()) []
  |> CONJUNCT1 |> GEN_ALL
  |> REWRITE_RULE[GSYM AND_IMP_INTRO]
*)

let is_Recclosure_def = cake_define
  `is_Recclosure x1 =
      match x1 with
        (Recclosure _6 _7 _8 _9 _10:closSem_v) -> T
      | _11 -> F`;;

let every_refv_def = cake_define
  `every_refv P x2 =
        match x2 with
          closSem_ValueArray vs -> EVERY P vs
        | (Thunk m v) -> P v
        | _12 -> T`;;

(* -- *)

(* correctness of free *)

(* value relation *)

let subg_def = cake_define
  `subg g0 g1 <=>
     subspt (FST g0) (FST g1) /\
     (!k v. ALOOKUP (SND g0) k = SOME v ==> ALOOKUP (SND g1) k = SOME
       v) /\
     ALL_DISTINCT (MAP FST (SND g1))`;;

let wfg'_def = cake_define
  `wfg' g <=>
     set_of_list (MAP FST (SND g)) SUBSET IMAGE SUC (domain (FST
       g))`;;

let wfg_def = cake_define
  `wfg g <=>
     set_of_list (MAP FST (SND g)) = IMAGE SUC (domain (FST g)) /\
     ALL_DISTINCT (MAP FST (SND g))`;;

let make_g_def = cake_define
  `make_g d code =
     (if IMAGE SUC (domain d) SUBSET (FDOM code) then
       SOME (d,MAP (\k. (FST k + 1,THE (FLOOKUP code (FST k +
         1)))) (toAList d)) else NONE)`;;

let recclosure_wf_def = cake_define
  `recclosure_wf loc fns <=>
     every_Fn_SOME (MAP SND fns) /\
     every_Fn_vs_NONE (MAP SND fns) /\
     DISJOINT (set_of_list (GENLIST (\i. 2 * i + loc) (LENGTH fns)))
       (set_of_list (code_locs (MAP SND fns))) /\
     ALL_DISTINCT (code_locs (MAP SND fns))`;;

let code_includes_def = cake_define
  `code_includes al code <=>
     (!k v. ALOOKUP al k = SOME v ==> FLOOKUP code k = SOME v)`;;

let recclosure_rel_def = cake_define
  `recclosure_rel g l code loc fns1 fns2 <=> (?g0.
      recclosure_wf loc fns1 /\
      wfg g0 /\
      DISJOINT (IMAGE SUC (set_of_list (code_locs (MAP SND fns1))))
        (set_of_list (MAP FST (SND g0))) /\
      DISJOINT (set_of_list (GENLIST (\i. 2 * i + loc + 1) (LENGTH
        fns1))) (set_of_list (MAP FST (SND g0))) /\
      (let (es,new_g) = calls (MAP SND fns1) (insert_each loc (LENGTH
        fns1) g0) in
      if EVERY2 (\(n,_13) p. !v. has_var v (SND (clos_call_free [p]))
        ==> v < n) fns1 es then
        (?tra n. fns2 = calls_list tra n loc fns1) /\
        subg (code_list loc (ZIP (MAP FST fns1) es) new_g) g /\
        set_of_list (code_locs (MAP SND fns1)) DIFF domain (FST
          new_g) SUBSET l /\
        code_includes (SND (code_list loc (ZIP (MAP FST fns1) es)
          new_g)) code else
        let (es,new_g) = calls (MAP SND fns1) g0 in
        fns2 = ZIP (MAP FST fns1) es /\
        subg new_g g /\
        set_of_list (code_locs (MAP SND fns1)) DIFF domain (FST
          new_g) SUBSET l /\
        set_of_list (GENLIST (\i. 2 * i + loc) (LENGTH fns1)) SUBSET
          l /\
        code_includes (SND new_g) code))`;;

let env_rel_def = cake_define
  `clos_callProof_env_rel R env1 env2 a es <=>
     (if LENGTH env1 = LENGTH env2 then LIST_REL R env1 env2 else
     !x. EXISTS (\(n,p). fv1 (n + a + x) p) es ==>
         x < LENGTH env1 /\ x < LENGTH env2 /\
         R (EL x env1) (EL x env2))`;;
hol4_overload "env_rel" "clos_callProof_env_rel";;

let _ = size_thms "closSem_v";;
(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 termination: >> simp[v_size_def] >> rpt strip_tac >>
   imp_res_tac v_size_lemma >> simp[] *)
let v_rel_def = cake_define_list_try (fun () ->
  `MEASURE (closSem_v_size o FST o SND o SND o SND)`)
  [`clos_callProof_v_rel g l code (closSem_Number i:closSem_v) v <=>
  v = (closSem_Number i:closSem_v)`;
   `clos_callProof_v_rel g l code (Word64 w:closSem_v) v <=> v =
  (Word64 w:closSem_v)`;
   `clos_callProof_v_rel g l code (closSem_Block n vs:closSem_v) v <=>
        (?vs'. v = closSem_Block n vs' /\ LIST_REL
          (clos_callProof_v_rel g l code) vs vs')`;
   `clos_callProof_v_rel g l code (closSem_ByteVector ws) v <=> v =
  closSem_ByteVector ws`;
   `clos_callProof_v_rel g l code (closSem_RefPtr b n:closSem_v) v
  <=> v = (closSem_RefPtr b n:closSem_v)`;
   `clos_callProof_v_rel g l code (Closure loco vs1 env1 n
  bod1:closSem_v) v <=>
         (?loc vs2 env2 bod2.
           recclosure_rel g l code loc [(n,bod1)] [(n,bod2)] /\
           v = Closure (SOME loc) vs2 env2 n bod2 /\ loco = SOME loc
             /\
           LIST_REL (clos_callProof_v_rel g l code) vs1 vs2 /\
           clos_callProof_env_rel (clos_callProof_v_rel g l code)
             env1 env2 0 [(n,bod2)])`;
   `clos_callProof_v_rel g l code (Recclosure loco vs1 env1 fns1
  i:closSem_v) v <=>
         (?loc vs2 env2 fns2.
           recclosure_rel g l code loc fns1 fns2 /\
           v = Recclosure (SOME loc) vs2 env2 fns2 i /\ loco = SOME
             loc /\
           LIST_REL (clos_callProof_v_rel g l code) vs1 vs2 /\
           clos_callProof_env_rel (clos_callProof_v_rel g l
             code) env1 env2 (LENGTH fns2) fns2)`];;
hol4_overload "v_rel" "clos_callProof_v_rel";;

(* HOL4 ML code, not ported:
val v_rel_ind = theorem"v_rel_ind";
*)

let _ = size_thms "closSem_v";;
(* HOL4 termination: >> simp[v_size_def] >> rpt strip_tac >>
   imp_res_tac v_size_lemma >> simp[] *)
let wfv_def = cake_define_wf
  `MEASURE (closSem_v_size o SND o SND o SND)`
  `wfv g l code x4 =
        match x4 with
          (Closure NONE _18 _19 _20 _21:closSem_v) -> F
        | (Recclosure NONE _22 _23 _24 _25) -> F
        | (Closure (SOME loc) vs env n bod) ->
       EVERY (wfv g l code) vs /\ EVERY (wfv g l code) env /\
       (?fns2.
       recclosure_rel g l code loc [(n,bod)] fns2)
        | (Recclosure (SOME loc) vs env fns i) ->
       EVERY (wfv g l code) vs /\ EVERY (wfv g l code) env /\
       (?fns2.
       recclosure_rel g l code loc fns fns2)
        | (closSem_Block _26 vs) -> EVERY (wfv g l code) vs
        | _27 -> T`;;

(* HOL4 ML code, not ported:
val wfv_ind = theorem"wfv_ind";
*)

let wfv_state_def = cake_define
  `wfv_state g l code s <=>
     EVERY (OPTION_ALL (wfv g l code)) (closSem_state_globals s) /\
     FEVERY (every_refv (wfv g l code) o SND) (state_refs s) /\
       closSem_state_code
     s = FEMPTY`;;

new_type_abbrev("calls_state",`: 1 spt#(num#num#closLang_exp) list`);;
new_type_abbrev("abs_calls_state",`: 1 spt`);;

let state_rel_def = cake_define
  `clos_callProof_state_rel g l (s:(1 spt#'c,'ffi)closSem_state)
  (t:('c,'ffi)closSem_state) <=>
     (state_ffi s = state_ffi t) /\
     (state_clock s = state_clock t) /\
     (closSem_state_max_app s = closSem_state_max_app t) /\
     LIST_REL (OPTREL (clos_callProof_v_rel g l (closSem_state_code
       t))) (closSem_state_globals s) (closSem_state_globals t) /\
     fmap_rel (closProps_ref_rel (clos_callProof_v_rel g l
       (closSem_state_code t))) (state_refs s) (state_refs t) /\
       closSem_state_code
     s = FEMPTY`;;
hol4_overload "state_rel" "clos_callProof_state_rel";;

(* syntactic properties of compiler *)

let insert_each'_def = cake_define_list
  [`insert_each' gt p 0 g = g`;
   `insert_each' gt p (SUC n) (g1,g2) =
       insert_each' gt (p + 2) n (sptree_insert p one g1,((p +
         1,THE (ALOOKUP gt (p + 1))) :: g2))`];;

(* HOL4 ML code, not ported:
val insert_each'_ind = theorem"insert_each'_ind";
*)

(* HOL4 ML code, not ported:
fun pairmaparg_tac (g as (asl,w)) =
  (tryfind
    (Lib.partial
      (mk_HOL_ERR"clos_callProofTheory""pairmaparg_tac""not found")
        (bvk_find_term
          (fn (bvs,tm) =>
            is_comb tm andalso
            pairSyntax.is_pair_map (rator tm) andalso
            HOLset.isEmpty
              (HOLset.intersection (FVL bvs empty_tmset,
                                    FVL [rand tm] empty_tmset)) andalso
            not (pairSyntax.is_pair (rand tm)))
          (fn tm => Cases_on [ANTIQUOTE (rand tm)])))
    (w::asl)) g
*)

(* properties of value relation *)

(* semantic functions respect relation *)

let syntax_ok_def = cake_define
  `clos_callProof_syntax_ok x <=> every_Fn_SOME x /\ every_Fn_vs_NONE
  x /\ ALL_DISTINCT (code_locs x)`;;
hol4_overload "syntax_ok" "clos_callProof_syntax_ok";;

let co_ok_def = cake_define
  `co_ok code co full_gs k <=>
     (if k = 0 then T else
       let g = FST (FST (co 0)) in
       let (cfg,exp,aux) = co 0 in
       let (g',exp',aux1) = clos_call_compile_inc g (exp,aux) in
         FST (FST (co 1)) = g' /\
         make_g g code = SOME (full_gs 0) /\
         (!i. subg (full_gs 0) (full_gs i)) /\
         (!x i. MEM x (code_locs exp) /\ ~(x IN domain g') ==> ~(
                x IN domain (FST (FST (co i))))) /\
         DISJOINT (set_of_list (code_locs exp)) (domain g) /\
         DISJOINT (FDOM code) (set_of_list (MAP FST aux1)) /\
         ALL_DISTINCT (MAP FST aux1) /\
         co_ok (code |++ aux1) (misc_shift_seq 1 co)
           (misc_shift_seq 1 full_gs) (k - 1))`;;

let code_inv_def = cake_define
  `code_inv g1_opt l1 (s_code:(num,num#closLang_exp)fmap)
         s_cc s_co t_code t_cc t_co <=>
     s_code = FEMPTY /\
     s_cc = state_cc clos_call_compile_inc t_cc /\
     t_co = state_co clos_call_compile_inc s_co /\
     (?g aux. wfg (g,aux) /\
         FST (FST (s_co 0)) = g /\
         oracle_monotonic (set_of_list o code_locs o FST o SND) (<)
             (domain g UNION l1) s_co /\
         t_code = alist_to_fmap aux /\
         (IS_SOME g1_opt ==> g1_opt = SOME (g,aux))) /\
     (!k. let (cfg,exp,aux) = s_co (k:num) in
         clos_callProof_syntax_ok exp /\ aux = [])`;;

(*
val dummy_code_inv = mk_var("code_inv",
  type_of(#1(strip_comb(lhs(concl(SPEC_ALL code_inv_def))))))
Definition code_inv_def:
  ^dummy_code_inv g1_opt s_code
     s_cc s_co t_code t_cc t_co ⇔ (s_code = FEMPTY)
End
*)

let includes_state_def = cake_define
  `includes_state g1 s_compile_oracle <=>
     (?(k:num). FST (FST (s_compile_oracle k)) = FST g1)`;;

(*
val dummy_includes_state = mk_var("includes_state",
  type_of(#1(strip_comb(lhs(concl(SPEC_ALL includes_state_def))))))
Definition includes_state_def:
  ^dummy_includes_state g1_s compile_oracle ⇔ T
End
*)

(*
Theorem code_inv_g_SUB_UN_locs:
  !i cfg exps aux.
  code_inv g1o s_code s_cc s_co t_code t_cc t_co ==>
  s_co i = (cfg,exps,aux) ==>
  x ∈ domain (FST cfg) ==>
  (x ∈ domain (FST (FST (s_co 0))) \/
    (?j. j < i /\ x ∈ set (code_locs (FST (SND (s_co j))))))
Proof
  Induct \\ rw []
  \\ fs [code_inv_def, is_state_oracle_def]
  \\ rpt (first_x_assum (qspec_then `i` mp_tac))
  \\ rw []
  \\ Cases_on `SND (s_co i)`
  \\ fs [compile_inc_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ rveq \\ fs []
  \\ old_drule calls_domain_locs
  \\ rw [SUBSET_DEF]
  \\ first_x_assum old_drule
  \\ rw []
  \\ fs [prim_recTheory.LESS_THM, PULL_EXISTS]
  \\ metis_tac [FST, SND]
QED

Theorem code_inv_DISJOINT:
  code_inv g1o s_code s_cc s_co t_code t_cc t_co ==>
  s_co i = (cfg,exps,aux) ==>
  DISJOINT (set (code_locs exps)) (domain (FST cfg))
Proof
  rw []
  \\ imp_res_tac code_inv_g_SUB_UN_locs
  \\ fs [code_inv_def, IN_DISJOINT]
  \\ CCONTR_TAC \\ fs []
  \\ first_x_assum old_drule
  \\ rpt strip_tac \\ fs []
  >- (
    old_drule is_state_oracle_0
    \\ rw []
    \\ old_drule oracle_monotonic_init
    \\ disch_then (qspec_then `i` mp_tac)
    \\ CCONTR_TAC \\ fs []
    \\ rfs []
    \\ metis_tac [prim_recTheory.LESS_REFL]
  )
  \\ old_drule oracle_monotonic_step
  \\ disch_then old_drule
  \\ fs []
  \\ metis_tac [prim_recTheory.LESS_REFL]
QED
*)

let mk_code_g_def = cake_define
  `mk_code_g code = (list_to_num_set (MAP PRE (SET_TO_LIST (FDOM
  code))),
     fmap_to_alist code)`;;

(* HOL4 ML code, not ported:
fun asm_exists_pat_conj_tac0 pat = first_assum (part_match_exists_tac
    (hd o filter (can (match_term pat)) o strip_conj) o concl)
val asm_exists_pat_conj_tac = Q_TAC asm_exists_pat_conj_tac0
*)

(* HOL4 ML code, not ported:
val asm_exists_pat_tac = Q_TAC (fn pat => first_assum
  (part_match_exists_tac
    (find_term (can (match_term pat))) o find_term (can (match_term
      pat)) o concl))
*)

(* compiler correctness *)

(* HOL4 ML code, not ported:
val t0 = ``t0:('c,'ffi) closSem$state``;
*)

(*
max_print_depth := 8
max_print_depth := 80
max_print_depth := 800
*)

(* HOL4 ML code, not ported:
fun say0 pfx s g = (print (pfx ^ ": " ^ s ^ "\n"); ALL_TAC g)
val say = say0 "calls_correct";
*)

(* All code_locs come from the original code,
   and therefore, are all even
*)

(* the all distinctness of code_locs is preserved *)

let nth_code_def = cake_define_list
  [`clos_callProof_nth_code code co 0 = code`;
   `clos_callProof_nth_code code co (SUC k) =
      (let (cfg,exp,aux) = co 0 in
      let (g',exp',aux') = clos_call_compile_inc (FST cfg) (exp,aux)
        in
        clos_callProof_nth_code (code |++ aux') (misc_shift_seq
          1 co) k)`];;
hol4_overload "nth_code" "clos_callProof_nth_code";;

(* TODO: move *)

(* Preservation of some label properties
  every_Fn_SOME xs ∧ every_Fn_vs_NONE xs
*)

(*
val tm = ``closLang$Let [Op (IntOp (Const 0)) []; Op (IntOp (Const 0))
  []]
             (App NONE (Fn (SOME 1) NONE 1 (Fn (SOME 2) NONE 1 (Op
               (IntOp (Const 1)) []))) [Op (IntOp (Const 2)) []])``
val res1 = EVAL``evaluate ([^tm],[],<|clock := 1|>)``
val (ctm,ctab) = EVAL``clos_call$compile T ^tm`` |> concl |> rhs |>
  dest_pair
val res2 = EVAL``evaluate ([^ctm],[],<|clock := 2; code :=
  (alist_to_fmap ^ctab)|>)``

val tm2 = ``closLang$Let [Op (IntOp (Const 0)) []; Op (IntOp (Const 0))
  []]
             (Fn (SOME 1) NONE 1 (App NONE (Fn (SOME 2) NONE 1 (Op
               (IntOp (Const 1)) [])) [Op (IntOp (Const 2)) []]))``
val res3 = EVAL``evaluate ([^tm2],[],<|clock := 1|>)``
val (ctm2,ctab2) = EVAL``clos_call$compile T ^tm2`` |> concl |> rhs |>
  dest_pair
val res4 = EVAL``evaluate ([^ctm2],[],<|clock := 2; code :=
  (alist_to_fmap ^ctab2)|>)``
*)

(* obeys_max_app and no_Labels *)

let state_syntax_def = cake_define
  `state_syntax f ((g,xs):1 spt#(num#num#closLang_exp) list) = EVERY
  (\(x1,x2,x3). f x3) xs`;;

(* names *)

(*
Theorem app_call_dests_GENLIST_Var:
   !t i num_args. app_call_dests opt (GENLIST_Var t i num_args) = {}
Proof
  Induct_on `num_args`
  \\ once_rewrite_tac [clos_callTheory.GENLIST_Var_def]
  \\ fs [app_call_dests_append]
QED

Theorem pure_code_locs: (* DUPLCATED! clos_annotate *)
   !xs. pure xs ==> code_locs [xs] = [] /\
                    app_call_dests opt [xs] = {}
Proof
  recInduct closLangTheory.pure_ind
  \\ rw[closLangTheory.pure_def, closPropsTheory.code_locs_def]
  \\ fsrw_tac[ETA_ss][EVERY_MEM]
  \\ Q.ISPEC_THEN`es`mp_tac code_locs_map
  \\ disch_then(qspec_then`I`mp_tac)
  \\ simp[FLAT_EQ_NIL, EVERY_MAP, EVERY_MEM]
  \\ ...
QED

Theorem call_dests_code_list_SUBSET:
   !xs n g.
      call_dests (MAP SND xs) ⊆ set (MAP FST (SND g)) /\
      call_dests (MAP (λx. SND (SND x)) (SND g)) ⊆ set (MAP FST (SND g))
        ==>
      call_dests (MAP (λx. SND (SND x)) (SND (code_list n xs g))) ⊆
      set (MAP FST (SND (code_list n xs g)))
Proof
  Induct \\ fs [FORALL_PROD] THEN1 (EVAL_TAC \\ fs [])
  \\ fs [code_list_def] \\ rw []
  \\ first_x_assum match_mp_tac \\ fs []
  \\ rpt (pop_assum mp_tac)
  \\ once_rewrite_tac [app_call_dests_cons] \\ fs []
  \\ fs [SUBSET_DEF]
QED

Theorem code_locs_MAP_SND_calls_list:
   !t x y fns. code_locs (MAP SND (calls_list t x y fns)) = []
Proof
  Induct_on `fns` \\ fs [calls_list_def,FORALL_PROD]
  \\ once_rewrite_tac [code_locs_cons]
  \\ fs [code_locs_def]
QED

Theorem calls_locs:
   !known_code g call_code g1.
      calls known_code g = (call_code,g1) /\
      call_dests known_code = ∅ /\
      call_dests (MAP (SND ∘ SND) (SND g)) ⊆ set (MAP FST (SND g)) ==>
      set (MAP FST (SND g)) ⊆ set (MAP FST (SND g1)) ∧
      call_dests (MAP (SND ∘ SND) (SND g)) ⊆
      call_dests (MAP (SND ∘ SND) (SND g1)) ∧
      call_dests call_code ⊆ set (MAP FST (SND g1)) ∧
      call_dests (MAP (SND ∘ SND) (SND g1)) ⊆ set (MAP FST (SND g1)) ∧
      app_dests call_code UNION app_dests (MAP (SND ∘ SND) (SND g1))
        ⊆ app_dests known_code UNION app_dests (MAP (SND ∘ SND) (SND g))
          ∧
      set (code_locs call_code) ∪ set (code_locs (MAP (SND ∘ SND) (SND
        g1))) =
      set (code_locs known_code) ∪ set (code_locs (MAP (SND ∘ SND) (SND
        g)))
Proof
  ...
QED

(*

  recInduct calls_ind
  \\ rpt conj_tac

  \\ TRY (

    full_simp_tac std_ss [calls_def,LET_THM,app_call_dests_def,
            every_Fn_SOME_def,MAP,LIST_TO_SET,UNION_EMPTY,
            BIGUNION_INSERT,BIGUNION_EMPTY,
            AC UNION_COMM UNION_ASSOC,SUBSET_REFL,EMPTY_SUBSET]
    \\ rpt gen_tac \\ strip_tac
    \\ rpt gen_tac \\ strip_tac
    \\ rpt (pairarg_tac \\ full_simp_tac std_ss [])
    \\ imp_res_tac calls_sing \\ rveq
    \\ rveq \\ full_simp_tac std_ss [APPEND,bool_case_eq,EMPTY_UNION]
    \\ rveq \\ full_simp_tac std_ss [APPEND,code_locs_def,
                  LET_THM,LIST_TO_SET,LIST_TO_SET_APPEND]
    \\ TRY CASE_TAC \\ full_simp_tac std_ss [APPEND]
    \\ once_rewrite_tac [app_call_dests_cons,code_locs_cons]
    \\ rveq \\ full_simp_tac std_ss
      [app_call_dests_def,UNION_EMPTY,LIST_TO_SET,
         code_locs_def,APPEND_NIL,LIST_TO_SET_APPEND,LET_THM,
         MAP,o_DEF]
    \\ rpt (pop_assum mp_tac)
    \\ once_rewrite_tac [app_call_dests_cons,code_locs_cons]
    \\ rveq \\ full_simp_tac std_ss
      [app_call_dests_def,UNION_EMPTY,LIST_TO_SET,
         code_locs_def,APPEND_NIL,LIST_TO_SET_APPEND]
    \\ rpt (disch_then assume_tac)
    \\ full_simp_tac std_ss [calls_def,LET_THM,
          every_Fn_SOME_def,MAP,LIST_TO_SET,UNION_EMPTY,
          BIGUNION_INSERT,BIGUNION_EMPTY,HD,
          IS_SOME_EXISTS,SND_insert_each,app_call_dests_GENLIST_Var,
          code_locs_GENLIST_Var]
    \\ rev_full_simp_tac std_ss []
    \\ TRY (qpat_x_assum `_ ==> _` mp_tac \\ impl_tac
            THEN1 (match_mp_tac call_dests_code_list_SUBSET
                   \\ imp_res_tac calls_length \\ fs [MAP_ZIP])
            \\ disch_then strip_assume_tac)
    \\ imp_res_tac calls_length \\ fs [MAP_ZIP,calls_list_length]
    \\ imp_res_tac calls_pure_sing
    \\ imp_res_tac pure_code_locs \\ fs []
    \\ full_simp_tac std_ss [AC UNION_ASSOC UNION_COMM,
         code_locs_MAP_SND_calls_list]

    \\ once_rewrite_tac [app_call_dests_cons,code_locs_cons]
    \\ rveq \\ full_simp_tac std_ss
      [app_call_dests_def,UNION_EMPTY,LIST_TO_SET,
         code_locs_def,APPEND_NIL,LIST_TO_SET_APPEND,GSYM ADD1]
    \\ rpt conj_tac
    \\ rveq \\ full_simp_tac std_ss [APPEND]
    \\ TRY CASE_TAC \\ full_simp_tac std_ss [APPEND]
    \\ full_simp_tac std_ss
      [SUBSET_DEF,IN_UNION,IN_INSERT,NOT_IN_EMPTY,IN_IMAGE,
          MAP,LIST_TO_SET,SUBSET_DEF,BIGUNION_INSERT,BIGUNION_EMPTY
            ,EXTENSION]
    \\ metis_tac []

)

  remaining cases:
     App -- almost works (problem with relating FST g with SND g
                          because they can be out-of-sync, i.e.
                          statement above needs updating)
     Letrec -- needs some work

*)

Theorem call_compile_locs:
   clos_call$compile b known_code = (call_code,g,aux) /\
    call_dests known_code = ∅ ==>
    call_dests call_code ∪ call_dests (MAP (SND ∘ SND) aux) ⊆
    set (MAP FST aux) /\
    app_dests call_code ∪ app_dests (MAP (SND ∘ SND) aux) ⊆
    app_dests known_code /\
    set (code_locs call_code) ∪ set (code_locs (MAP (SND ∘ SND) aux)) =
    set (code_locs known_code)
Proof
  reverse (Cases_on `b`) \\ fs [clos_callTheory.compile_def]
  THEN1 (strip_tac \\ rveq \\ fs [closPropsTheory.code_locs_def])
  \\ pairarg_tac \\ fs []
  \\ strip_tac \\ rveq \\ fs []
  \\ old_drule calls_locs \\ fs [EVAL ``(code_locs [])``]
QED
*)
