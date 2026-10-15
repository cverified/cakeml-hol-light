(* ======================================================== *)
(*  evaluateProps: ported from HOL4's
    semantics/proofs/evaluatePropsScript.sml  *)
(* ======================================================== *)

(*
  Properties of the operational semantics.
*)

needs "compiler/backend/pattern_matching/pattern_semantics.ml";;
needs "semantics/ast.ml";;
needs "semantics/evaluate.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/namespace.ml";;
needs "semantics/proofs/namespaceProps.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;
needs "semantics/semanticPrimitives.ml";;

let call_FFI_rel_def = cake_define
  `call_FFI_rel s1 s2 <=> (?n conf bytes t. call_FFI s1 n conf bytes
  = FFI_return s2 t)`;;

let dest_IO_event_def = cake_define
  `dest_IO_event (IO_event s c b) = (s,c,b)`;;

let io_events_mono_def = cake_define
  `io_events_mono s1 s2 <=> ffi_state_io_events
     s1 <<= ffi_state_io_events s2 /\
     (ffi_state_io_events s2 = ffi_state_io_events s1 ==> s2 = s1)`;;

let is_clock_io_mono_def = cake_define
  `is_clock_io_mono f s = (match f s with (s',r) ->
         io_events_mono (semanticPrimitives_state_ffi s)
           (semanticPrimitives_state_ffi s') /\
         semanticPrimitives_state_clock s' <=
           semanticPrimitives_state_clock s /\
         semanticPrimitives_state_next_type_stamp s <=
           semanticPrimitives_state_next_type_stamp s' /\
         semanticPrimitives_state_next_exn_stamp s <=
           semanticPrimitives_state_next_exn_stamp s' /\
         LENGTH (semanticPrimitives_state_refs s) <= LENGTH
           (semanticPrimitives_state_refs s') /\ (!clk. match f
           (semanticPrimitives_state_clock_fupd (K clk) s) with (s'',r')
           ->
             (
                 ~(r' = Rerr (Rabort Rtimeout_error)) ==>
                 ~(r = Rerr (Rabort Rtimeout_error)) ==>
                     r' = r /\ s'' =
                       (semanticPrimitives_state_clock_fupd (K (clk -
                       (semanticPrimitives_state_clock s -
                       semanticPrimitives_state_clock s'))) s')) /\
             (
                 ~(r = Rerr (Rabort Rtimeout_error)) ==> (
                     clk >= semanticPrimitives_state_clock s -
                       semanticPrimitives_state_clock s' <=> ~(r' = Rerr
                       (Rabort Rtimeout_error)))) /\
             (
                 ~(r' = Rerr (Rabort Rtimeout_error)) ==>
                 clk <= semanticPrimitives_state_clock s ==> ~(r =
                   Rerr (Rabort Rtimeout_error))) /\ (clk <=
                   semanticPrimitives_state_clock s ==>
                   io_events_mono (semanticPrimitives_state_ffi s'')
                   (semanticPrimitives_state_ffi s'))))`;;

let adj_clock_def = cake_define
  `adj_clock inc dec s = (semanticPrimitives_state_clock_fupd (K
  ((semanticPrimitives_state_clock s + inc) - dec)) s)`;;

(* HOL4 ML code, not ported:
val step_tac =
  rpt (FIRST ([strip_tac]
    @ map ho_match_mp_tac [is_clock_io_mono_bind,
      is_clock_io_mono_check]
    @ [CHANGED_TAC (fs [Cong is_clock_io_mono_cong,
                        is_clock_io_mono_return, is_clock_io_mono_err,
                        do_eval_res_def, dec_inc_clock]),
                          TOP_CASE_TAC]));
*)

(* HOL4 ML code, not ported:
fun mk_extra_lemmas mp_rule monad_rule
  = BODY_CONJUNCTS monad_rule
    |> map (BETA_RULE o MATCH_MP mp_rule o Q.GEN `s`)
fun prove_extra mp_rule monad_rule
  = simp_tac bool_ss (mk_extra_lemmas mp_rule monad_rule)
*)

(* HOL4 ML code, not ported:
val evaluate_decs_lemmas
  = BODY_CONJUNCTS is_clock_io_mono_evaluate_decs
    |> map (BETA_RULE o MATCH_MP is_clock_io_mono_extra o Q.GEN `s`)
*)

(* due to Eval this is no longer true
Theorem evaluate_state_unchanged:
  (!(st:'ffi state) env es st' r.
    evaluate st env es = (st', r)
    ⇒
    st'.next_type_stamp = st.next_type_stamp ∧
    st'.next_exn_stamp = st.next_exn_stamp) ∧
  (!(st:'ffi state) env v pes err_v st' r.
    evaluate_match st env v pes err_v = (st', r)
    ⇒
    st'.next_type_stamp = st.next_type_stamp ∧
    st'.next_exn_stamp = st.next_exn_stamp)
Proof
 ho_match_mp_tac evaluate_ind
 >> rw [evaluate_def]
 >> every_case_tac
 >> fs []
 >> rw [dec_clock_def, shift_fp_opts_def]
QED
*)

(* HOL4 ML code, not ported:
val evaluate_set_clock_lemmas
  = (BODY_CONJUNCTS is_clock_io_mono_evaluate
    @ BODY_CONJUNCTS is_clock_io_mono_evaluate_decs)
  |> map (BETA_RULE o MATCH_MP is_clock_io_mono_set_clock);
*)

(* HOL4 ML code, not ported:
val evaluate_minimal_lemmas = BODY_CONJUNCTS is_clock_io_mono_evaluate
  |> map (BETA_RULE o MATCH_MP is_clock_io_mono_minimal);
*)
