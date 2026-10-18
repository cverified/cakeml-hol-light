(* ======================================================== *)
(*  semanticsProps: ported from HOL4's
    semantics/proofs/semanticsPropsScript.sml
    A proof theory about semantics.ml, with 5 definitions and 20
    theorems.  Needed by 12 files of the port.  *)
(* ======================================================== *)

(*
  Theorems about the top-level semantics, including totality and determinism.
*)

needs "lib/lprefix_lub.ml";;
needs "lib/sptree.ml";;
needs "semantics/evaluate.ml";;
needs "semantics/proofs/evaluateProps.ml";;
needs "semantics/proofs/typeSound.ml";;
needs "semantics/proofs/typeSoundInvariants.ml";;
needs "semantics/semantics.ml";;

let evaluate_prog_events_determ =
  cake_theorem "evaluate_prog_events_determ"
  (fun () ->
    `!st env k p k'.
     LENGTH (ffi_state_io_events (FST (evaluate_prog_with_clock st
       env k p))) = LENGTH (ffi_state_io_events (FST
       (evaluate_prog_with_clock st env k' p))) ==>
      ffi_state_io_events
     (FST (evaluate_prog_with_clock st env k p)) =
       ffi_state_io_events (FST (evaluate_prog_with_clock st env k'
       p))`)
  CHEAT_TAC;;

let evaluate_prog_io_events_chain =
  cake_theorem "evaluate_prog_io_events_chain"
  (fun () ->
    `lprefix_chain (IMAGE (\k. fromList (ffi_state_io_events (FST
  (evaluate_prog_with_clock st env k prog)))) UNIV)`)
  CHEAT_TAC;;

let semantics_prog_total = cake_theorem "semantics_prog_total"
  (fun () ->
    `!s e p. ?b. semantics_prog s e p b`)
  CHEAT_TAC;;

let semanticsProps_with_clock_ffi = cake_theorem "with_clock_ffi[local]"
  (fun () ->
    `semanticPrimitives_state_ffi
       (semanticPrimitives_state_clock_fupd (K x) s) =
         semanticPrimitives_state_ffi s`)
  CHEAT_TAC;;

(* HOL4 semanticsPropsScript.sml:76-80: a proof *)

(* HOL4 semanticsPropsScript.sml:82: a proof *)

let semantics_prog_deterministic =
  cake_theorem "semantics_prog_deterministic"
  (fun () ->
    `!s e p b b'.
      semantics_prog s e p b /\
      semantics_prog s e p b' ==>
      b = b'`)
  CHEAT_TAC;;

let semantics_prog_Terminate_not_Fail =
  cake_theorem "semantics_prog_Terminate_not_Fail"
  (fun () ->
    `semantics_prog s e p (ffi_Terminate x y) ==>
      ~semantics_prog s e p ffi_Fail /\
      semantics_prog s e p = {ffi_Terminate x y}`)
  CHEAT_TAC;;

let semantics_prog_Diverge_not_Fail =
  cake_theorem "semantics_prog_Diverge_not_Fail"
  (fun () ->
    `semantics_prog s e p (ffi_Diverge y) ==>
      ~semantics_prog s e p ffi_Fail /\
      semantics_prog s e p = {ffi_Diverge y}`)
  CHEAT_TAC;;

let state_invariant_def = cake_define
  `state_invariant st <=>
   (?ctMap tenvS.
     FRANGE ((SND o SND) o_f ctMap) SUBSET semantics_state_type_ids
       st /\
     type_sound_invariant (semantics_state_sem_st st)
       (semantics_state_sem_env st) ctMap tenvS {}
       (semantics_state_tenv st))`;;

let clock_lemmas = cake_theorem "clock_lemmas[local]"
  (fun () ->
    `(semanticPrimitives_state_clock
  (semanticPrimitives_state_clock_fupd (K c) x) = c) /\
      ((semanticPrimitives_state_clock_fupd (K d)
        (semanticPrimitives_state_clock_fupd (K c) x)) =
        (semanticPrimitives_state_clock_fupd (K d) x)) /\
      (semanticPrimitives_state_clock_fupd (K
        (semanticPrimitives_state_clock x = x)) x)`)
  CHEAT_TAC;;

let semantics_deterministic = cake_theorem "semantics_deterministic"
  (fun () ->
    `state_invariant st ==>
     semantics_semantics st prelude inp = Execute bs ==> (?b. bs
       = {b} /\ ~(b = ffi_Fail))`)
  CHEAT_TAC;;

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

let extend_with_resource_limit_not_fail =
  cake_theorem "extend_with_resource_limit_not_fail"
  (fun () ->
    `x IN extend_with_resource_limit y /\ ~(ffi_Fail IN y) ==> ~(x =
  ffi_Fail)`)
  CHEAT_TAC;;

let implements_intro = cake_theorem "implements_intro"
  (fun () ->
    `(b /\ ~(x = ffi_Fail) ==> y = x) ==> b ==> implements {y} {x}`)
  CHEAT_TAC;;

let implements_trivial_intro = cake_theorem "implements_trivial_intro"
  (fun () ->
    `(y = x) ==> implements {y} {x}`)
  CHEAT_TAC;;

let implements_intro_ext = cake_theorem "implements_intro_ext"
  (fun () ->
    `(b /\ ~(x = ffi_Fail) ==> y IN extend_with_resource_limit {x}) ==>
      b ==> implements {y} {x}`)
  CHEAT_TAC;;

let isPREFIX_IMP_LPREFIX = cake_theorem "isPREFIX_IMP_LPREFIX[local]"
  (fun () ->
    `!xs ys. isPREFIX xs ys ==> LPREFIX (fromList xs) (fromList ys)`)
  CHEAT_TAC;;

let implements_trans = cake_theorem "implements_trans"
  (fun () ->
    `implements y z ==> implements x y ==> implements x z`)
  CHEAT_TAC;;

let implements'_F = cake_theorem "implements'_F"
  (fun () ->
    `implements' F = implements`)
  CHEAT_TAC;;

let implements'_trans = cake_theorem "implements'_trans"
  (fun () ->
    `!x y z b.
       implements' b y z /\
       implements' b x y ==>
       implements' b x z`)
  CHEAT_TAC;;

let implements'_strengthen = cake_theorem "implements'_strengthen"
  (fun () ->
    `!b b' x y. (b' ==> b) /\ implements' b x y ==> implements' b' x y`)
  CHEAT_TAC;;

let implements'_IMP_implements =
  cake_theorem "implements'_IMP_implements"
  (fun () ->
    `implements' b x y ==> implements x y`)
  CHEAT_TAC;;

let extend_with_resource_limit'_SUBSET =
  cake_theorem "extend_with_resource_limit'_SUBSET"
  (fun () ->
    `extend_with_resource_limit' b s SUBSET
     extend_with_resource_limit s`)
  CHEAT_TAC;;
