(* ======================================================== *)
(*  semanticsProps: ported from HOL4's
    semantics/proofs/semanticsPropsScript.sml  *)
(* ======================================================== *)

(*
  Theorems about the top-level semantics, including totality and
    determinism.
*)

needs "lib/balanced_map.ml";;
needs "lib/lprefix_lub.ml";;
needs "semantics/evaluate.ml";;
needs "semantics/proofs/evaluateProps.ml";;
needs "semantics/proofs/typeSound.ml";;
needs "semantics/proofs/typeSoundInvariants.ml";;
needs "semantics/semantics.ml";;

(* HOL4 ML code, not ported:
val tac1 =
    metis_tac[semanticPrimitivesTheory.result_11
      ,evaluate_decs_ffi_mono_clock,io_events_mono_def,
              semanticPrimitivesTheory.error_result_11,option_nchotomy
                ,LESS_EQ_CASES,
              semanticPrimitivesTheory.abort_distinct,pair_CASES,FST
                ,THE_DEF,
              PAIR_EQ,IS_SOME_EXISTS,SOME_11,NOT_SOME_NONE,SND,PAIR
                ,LESS_OR_EQ]
*)

(* HOL4 ML code, not ported:
val tac2 = every_case_tac >> rfs[] >> first_x_assum (qspec_then `k`
  assume_tac) >> rfs[]
*)

let state_invariant_def = cake_define
  `state_invariant st <=>
   (?ctMap tenvS.
     FRANGE ((SND o SND) o_f ctMap) SUBSET semantics_state_type_ids
       st /\
     type_sound_invariant (semantics_state_sem_st st)
       (semantics_state_sem_env st) ctMap tenvS {}
       (semantics_state_tenv st))`;;

let extend_with_resource_limit_def = cake_define
  `extend_with_resource_limit behaviours =
   behaviours UNION
   {ffi_Terminate ffi_Resource_limit_hit io_list | io_list | ?t l.
     ffi_Terminate t l IN behaviours /\ io_list <<= l} UNION
   {ffi_Terminate ffi_Resource_limit_hit io_list | io_list | ?ll.
     ffi_Diverge ll IN behaviours /\ LPREFIX (fromList io_list) ll}`;;

let extend_with_resource_limit'_def = cake_define
  `extend_with_resource_limit' precise behaviours =
     (if precise then behaviours else
       extend_with_resource_limit behaviours)`;;

let implements_def = cake_define
  `implements x y <=>
     (~(ffi_Fail IN y) ==> x SUBSET extend_with_resource_limit y)`;;

let implements'_def = cake_define
  `implements' precise x y <=> ~(ffi_Fail IN y) ==> x SUBSET
  extend_with_resource_limit' precise y`;;
