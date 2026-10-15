(* ======================================================== *)
(*  dataProps: ported from HOL4's
    compiler/backend/semantics/dataPropsScript.sml  *)
(* ======================================================== *)

(*
  Properties about dataLang and its semantics
*)

needs "compiler/backend/closLang.ml";;
needs "compiler/backend/clos_annotate.ml";;
needs "compiler/backend/dataLang.ml";;
needs "compiler/backend/labLang.ml";;
needs "compiler/backend/pattern_matching/pattern_semantics.ml";;
needs "compiler/backend/semantics/backendProps.ml";;
needs "compiler/backend/semantics/bvlSem.ml";;
needs "compiler/backend/semantics/closSem.ml";;
needs "compiler/backend/semantics/dataSem.ml";;
needs "lib/sptree.ml";;
needs "semantics/ast.ml";;
needs "semantics/proofs/semanticsProps.ml";;
needs "semantics/semanticPrimitives.ml";;

let _ = size_thms "list";;
let _ = size_thms "sptree";;
let _ = size_thms "v";;
(* HOL4 termination: \\ rpt strip_tac \\ fs
   [sptreeTheory.size_delete] \\ imp_res_tac miscTheory.lookup_zero
   \\ fs [] *)
let approx_of_def = cake_define_wf
  `(inv_image (MEASURE I LEX MEASURE (list_size v_size))
                             (\(lims,vs,refs). (sptree_size
                               refs,vs)))`
  `approx_of lims x2 refs =
        match x2 with
          [] -> 0
        | (x :: y :: ys) ->
       approx_of lims [x] refs + approx_of lims (y :: ys) refs
        | [Word64 _1] -> 3
        | [Number i] ->
       (if small_num (limits_arch_64_bit lims) i then 0 else
         bignum_size (limits_arch_64_bit lims) i)
        | [CodePtr _2] -> 0
        | [RefPtr _3 r] ->
        (match lookup r refs with NONE -> 0 | SOME (ByteArray _4 bs)
          -> LENGTH bs DIV (arch_size lims DIV 8) + 2 | SOME (ValueArray
          vs) ->
            approx_of lims vs (delete r refs) + LENGTH vs + 1 | SOME
              (Thunk _5 v) ->
            approx_of lims [v] (delete r refs) + 2 | SOME (MutBlock
              tg fin ls c rs) ->
            approx_of lims (ls ++ [c] ++ rs) (delete r refs) +
            LENGTH ls + LENGTH rs + 2)
        | [Block ts tag []] -> 0
        | [Block ts tag vs] ->
       approx_of lims vs refs + LENGTH vs + 1`;;

(* HOL4 ML code, not ported:
val s = ``s:('c,'ffi) dataSem$state``
*)

(* ops that are not allowed_op have stack_consumed = NONE, which has to
   propagate through do_stack's safe_for_space computation *)
(*
Theorem lim_safe_eq[simp]:
  lim_safe (s with locals := x0)            op xs = lim_safe s op xs
∧ lim_safe (s with stack := x1)             op xs = lim_safe s op xs
∧ lim_safe (s with global := x2)            op xs = lim_safe s op xs
∧ lim_safe (s with handler := x3)           op xs = lim_safe s op xs
∧ lim_safe (s with refs := x4)              op xs = lim_safe s op xs
∧ lim_safe (s with compile := x5)           op xs = lim_safe s op xs
∧ lim_safe (s with clock := x6)             op xs = lim_safe s op xs
∧ lim_safe (s with code := x7)              op xs = lim_safe s op xs
∧ lim_safe (s with ffi := x8)               op xs = lim_safe s op xs
∧ lim_safe (s with space := x9)             op xs = lim_safe s op xs
∧ lim_safe (s with tstamps := x10)          op xs = lim_safe s op xs
∧ lim_safe (s with safe_for_space := x11)   op xs = lim_safe s op xs
∧ lim_safe (s with peak_heap_length := x12) op xs = lim_safe s op xs
∧ lim_safe (s with compile_oracle := x13)   op xs = lim_safe s op xs
Proof
  MAP_EVERY (fn t => Q.SPEC_TAC (t,t)) [`xs`,`op`,`s`]
  \\ ho_match_mp_tac lim_safe_ind \\ rw []
QED
*)

let var_corr_def = cake_define
  `var_corr env corr t <=>
     EVERY2 (\v x. get_var v t = SOME x) corr env`;;

(* INFO: only used in bvi_to_dataProof *)

(*fs[] is slower than full_simp_tac(srw_ss())[]*)
(* HOL4 ML code, not ported:
fun cases_on_op_fs q = Cases_on q \\ full_simp_tac(srw_ss()) []
  >>> SELECT_LT_THEN (Q.RENAME_TAC [‘BlockOp b_’]) (Cases_on `b_`)
  >>> SELECT_LT_THEN (Q.RENAME_TAC [‘GlobOp g_’]) (Cases_on `g_`)
  >>> SELECT_LT_THEN (Q.RENAME_TAC [‘MemOp m_’]) (Cases_on `m_`)
  >>> SELECT_LT_THEN (Q.RENAME_TAC [‘ThunkOp t_’]) (Cases_on `t_`);
*)

(*fs[] is slower than full_simp_tac(srw_ss())[]*)

(*fs[] is slower than full_simp_tac(srw_ss())[]*)

(*fs[] is slower than full_simp_tac(srw_ss())[]*)

(*fs[] is slower than full_simp_tac(srw_ss())[]*)

(*fs[] is slower than full_simp_tac(srw_ss())[]*)

(*fs[] is slower than full_simp_tac(srw_ss())[]*)
(* HOL4 ML code, not ported:
val do_app_swap_tac =
   Count.apply (strip_tac
   \\ cases_on_op_fs ‘op’
   \\ TRY (rename [‘EqualConst cc’] \\ Cases_on ‘cc’)
   \\ rw[do_app_def,do_stack_def
              , do_install_def
              , do_app_aux_def
              , with_fresh_ts_def
              , do_space_def
              , op_space_reset_def
              , data_spaceTheory.op_space_req_def
              , consume_space_def
              , stack_consumed_def
              , size_of_heap_with_safe
              , MAX_DEF
              , check_lim_def]
  \\ TRY
    (full_simp_tac(srw_ss())[LET_DEF,UNCURRY_EQ,list_case_eq
    ,option_case_eq,v_case_eq,bool_case_eq,bvlSemTheory.ref_case_eq
        , ffiTheory.ffi_result_case_eq,ffiTheory.oracle_result_case_eq,
          state_component_equality
        , semanticPrimitivesTheory.eq_result_case_eq
          ,astTheory.word_size_case_eq,pair_case_eq
        , limits_component_equality,stack_consumed_def]
          \\ full_simp_tac(srw_ss())
            [data_spaceTheory.op_space_req_def,stack_consumed_def]
          \\ rev_full_simp_tac(srw_ss())
            [data_spaceTheory.op_space_req_def]
          \\ simp [Once CONJ_COMM] \\ NO_TAC)
  \\ rpt(PURE_TOP_CASE_TAC \\ fs[] \\ rveq) \\
    fs[state_component_equality,stack_consumed_def]
  \\ gvs [AllCaseEqs()]);
*)

(* HOL4 ML code, not ported:
val full_fs = fs[ get_var_def, set_var_def
                      , cut_state_opt_def
                      , cut_state_def
                      , get_vars_def
                      , do_install_def
                      , op_space_reset_def
                      , call_env_def
                      , flush_state_def
                      , dec_clock_def
                      , add_space_def
                      , jump_exc_def
                      , MAX_DEF
                      , size_of_heap_with_safe
                      , op_requires_names_def];
*)

(* HOL4 ML code, not ported:
val full_cases = fs [ list_case_eq,option_case_eq
                          , v_case_eq
                          , bool_case_eq
                          , bvlSemTheory.ref_case_eq
                          , ffiTheory.ffi_result_case_eq
                          , ffiTheory.oracle_result_case_eq
                          , semanticPrimitivesTheory.eq_result_case_eq
                          , astTheory.word_size_case_eq
                          , pair_case_eq];
*)

(* HOL4 ML code, not ported:
val basic_tac = fs [evaluate_def]
                      \\ rpt (every_case_tac
                      \\ full_fs
                      \\ fs [state_component_equality]);
*)


(* The field-swap (stack_max/safe_for_space/peak_heap_length) commutes
   through
   the narrow cut in evaluate(Assign), since cut_state_opt only touches
     locals. *)

(* When the swap leaves stack_max at its original value (the fl=F case),
   the merged input update collapses to just
     safe_for_space/peak_heap_length. *)

let same_stack_size_def = cake_define
  `same_stack_size x y <=> size_of_stack_frame x =
  size_of_stack_frame y`;;

let locals_ok_def = cake_define
  `locals_ok l1 l2 =
     (!v x. (sptree_lookup v l1 = SOME x) ==> (sptree_lookup v l2
       = SOME x))`;;

(* Under locals_ok, the narrow cut in evaluate(Assign) succeeds on the
   larger
   locals and yields a state equal up to (and locals_ok on) its locals.
     *)

(*fs[] is slower than full_simp_tac(srw_ss())[]*)

let get_code_labels_def = cake_define
  `dataProps_get_code_labels x1 =
        match x1 with
          (Call r d a h:asm_with_lab) ->
       (match d with SOME x -> {x} | _6 -> {}) UNION
       (match h with SOME (n,p) -> dataProps_get_code_labels p | _7
         -> {})
        | (Force _8 loc _9) -> {loc}
        | (Seq p1 p2) -> dataProps_get_code_labels p1 UNION
          dataProps_get_code_labels p2
        | (If _10 p1 p2) -> dataProps_get_code_labels p1 UNION
          dataProps_get_code_labels p2
        | (Assign _11 op _12 _13) -> assign_get_code_label op
        | _14 -> {}`;;
hol4_overload "get_code_labels" "dataProps_get_code_labels";;

let good_code_labels_def = cake_define
  `dataProps_good_code_labels p elabs <=>
     (BIGUNION (set_of_list (MAP (\(n,m,pp). (get_code_labels pp))
       p))) SUBSET
     (set_of_list (MAP FST p)) UNION elabs`;;
hol4_overload "good_code_labels" "dataProps_good_code_labels";;

(*fs[] is slower than full_simp_tac(srw_ss())[]*)

let zero_limits_def = cake_define
  `zero_limits = (mk_limits 0 0 0 ARB ARB ARB:limits)`;;


(* HOL4 ML code, not ported:
val trivial_tac = qpat_x_assum `evaluate _ = (_,_)` (strip_assume_tac o
                   SIMP_RULE(srw_ss())[evaluate_def,AllCaseEqs()] ) >>
                  rveq >> simp[evaluate_def] >>
                  simp[state_component_equality];
*)

(* The limits-swap commutes through the narrow cut in evaluate(Assign).
   *)

(* Stack frames equal up-to size component*)
let stack_frame_size_rel_def = cake_define
  `stack_frame_size_rel x1 x2 =
        match (x1,x2) with
          (Exc opt spt num,Exc opt' spt' num') ->
       spt = spt' /\ num = num'
        | ((Env opt spt),(Env opt' spt')) ->
       spt = spt'
        | (_15,_16) -> F`;;

(* HOL4 ML code, not ported:
val basics_tac = fs [evaluate_def]
                 \\ every_case_tac
                 \\ full_fs
                 \\ fs [state_component_equality]
                 \\ rfs[];
*)

(* The locals_size/stack/stack_frame_sizes-swap commutes through the
   narrow
   cut in evaluate(Assign), and the cut preserves the stack. *)

let cc_co_only_diff_def = cake_define
  `cc_co_only_diff (s:('a,'ffi)dataSem_state) (t:('b,'ffi)dataSem_state)
  <=> dataSem_state_locals
     s = dataSem_state_locals t /\ dataSem_state_locals_size
     s = dataSem_state_locals_size t /\ ?_stack
     s = ?_stack t /\ dataSem_state_stack_max
     s = dataSem_state_stack_max t /\ dataSem_state_stack_frame_sizes
     s = dataSem_state_stack_frame_sizes t /\ dataSem_state_global
     s = dataSem_state_global t /\ dataSem_state_handler
     s = dataSem_state_handler t /\ ?_refs
     s = ?_refs t /\ ?_clock
     s = ?_clock t /\ ?_code
     s = ?_code t /\ ?_ffi
     s = ?_ffi t /\ dataSem_state_space
     s = dataSem_state_space t /\ dataSem_state_tstamps
     s = dataSem_state_tstamps t /\ dataSem_state_limits
     s = dataSem_state_limits t /\ dataSem_state_safe_for_space
     s = dataSem_state_safe_for_space t /\
       dataSem_state_peak_heap_length
     s = dataSem_state_peak_heap_length t`;;

(*fs[] is slower than full_simp_tac(srw_ss())[]*)

(*fs[] is slower than full_simp_tac(srw_ss())[]*)

(* The narrow cut in evaluate(Assign) only depends on locals (equal
   under
   cc_co_only_diff), so the t-side cut is determined by the s-side cut
     and
   preserves cc_co_only_diff. *)

(* TODO: move *)

(*fs[] is slower than full_simp_tac(srw_ss())[]*)
