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

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "semanticsProps"
  ["evaluate"; "evaluateProps"; "semantics"; "typeSound"];;

let evaluate_prog_events_determ = prove
 (`!st env k p k'.
   LENGTH (ffi_state_io_events (FST (evaluate_prog_with_clock st env
     k p))) = LENGTH (ffi_state_io_events (FST (evaluate_prog_with_clock
     st env k' p))) ==>
    ffi_state_io_events
   (FST (evaluate_prog_with_clock st env k p)) =
     ffi_state_io_events (FST (evaluate_prog_with_clock st env k' p))`,
  CHEAT_TAC);;

let evaluate_prog_io_events_chain = prove
 (`lprefix_chain (IMAGE (\k. fromList (ffi_state_io_events (FST
  (evaluate_prog_with_clock st env k prog)))) UNIV)`,
  CHEAT_TAC);;

let semantics_prog_total = prove
 (`!s e p. ?b. semantics_prog s e p b`,
  CHEAT_TAC);;

(* with_clock_ffi[local] *)
let semanticsProps_with_clock_ffi = prove
 (`semanticPrimitives_state_ffi
     (semanticPrimitives_state_clock_fupd (K x) s) =
       semanticPrimitives_state_ffi s`,
  CHEAT_TAC);;

(* HOL4 semanticsPropsScript.sml:76-80: a proof *)

(* HOL4 semanticsPropsScript.sml:82: a proof *)

let semantics_prog_deterministic = prove
 (`!s e p b b'.
    semantics_prog s e p b /\
    semantics_prog s e p b' ==>
    b = b'`,
  CHEAT_TAC);;

let semantics_prog_Terminate_not_Fail = prove
 (`semantics_prog s e p (ffi_Terminate x y) ==>
    ~(semantics_prog s e p ffi_Fail) /\
    semantics_prog s e p = {ffi_Terminate x y}`,
  CHEAT_TAC);;

let semantics_prog_Diverge_not_Fail = prove
 (`semantics_prog s e p (ffi_Diverge y) ==>
    ~(semantics_prog s e p ffi_Fail) /\
    semantics_prog s e p = {ffi_Diverge y}`,
  CHEAT_TAC);;

let state_invariant_def = new_definition
  `state_invariant st <=>
   (?ctMap tenvS.
     FRANGE ((SND o SND) o_f ctMap) SUBSET semantics_state_type_ids
       st /\
     type_sound_invariant (semantics_state_sem_st st)
       (semantics_state_sem_env st) ctMap tenvS {}
       (semantics_state_tenv st))`;;

(* [local] *)
let clock_lemmas = prove
 (`(semanticPrimitives_state_clock (semanticPrimitives_state_clock_fupd
  (K c) x) = c) /\
    ((semanticPrimitives_state_clock_fupd (K d)
      (semanticPrimitives_state_clock_fupd (K c) x)) =
      (semanticPrimitives_state_clock_fupd (K d) x)) /\
    (semanticPrimitives_state_clock_fupd (K
      (semanticPrimitives_state_clock x)) x = x)`,
  CHEAT_TAC);;

let semantics_deterministic = prove
 (`state_invariant st ==>
   semantics_semantics st prelude inp = Execute bs ==> (?b. bs =
     {b} /\ ~(b = ffi_Fail))`,
  CHEAT_TAC);;

let extend_with_resource_limit_def = new_definition
  `extend_with_resource_limit behaviours =
   behaviours UNION
   {ffi_Terminate ffi_Resource_limit_hit io_list | io_list | ?t l.
     ffi_Terminate t l IN behaviours /\ io_list <<= l} UNION
   {ffi_Terminate ffi_Resource_limit_hit io_list | io_list | ?ll.
     ffi_Diverge ll IN behaviours /\ LPREFIX (fromList io_list) ll}`;;

let extend_with_resource_limit'_def = new_definition
  `extend_with_resource_limit' precise behaviours =
     (if precise then behaviours else
       extend_with_resource_limit behaviours)`;;

let implements_def = new_definition
  `implements x y <=>
     (~(ffi_Fail IN y) ==> x SUBSET extend_with_resource_limit y)`;;

let implements'_def = new_definition
  `implements' precise x y <=> ~(ffi_Fail IN y) ==> x SUBSET
  extend_with_resource_limit' precise y`;;

let extend_with_resource_limit_not_fail = prove
 (`x IN extend_with_resource_limit y /\ ~(ffi_Fail IN y) ==> ~(x =
  ffi_Fail)`,
  CHEAT_TAC);;

let implements_intro = prove
 (`(b /\ ~(x = ffi_Fail) ==> y = x) ==> b ==> implements {y} {x}`,
  CHEAT_TAC);;

let implements_trivial_intro = prove
 (`(y = x) ==> implements {y} {x}`,
  CHEAT_TAC);;

let implements_intro_ext = prove
 (`(b /\ ~(x = ffi_Fail) ==> y IN extend_with_resource_limit {x}) ==>
    b ==> implements {y} {x}`,
  CHEAT_TAC);;

(* [local] *)
let isPREFIX_IMP_LPREFIX = prove
 (`!xs ys. isPREFIX xs ys ==> LPREFIX (fromList xs) (fromList ys)`,
  CHEAT_TAC);;

let implements_trans = prove
 (`implements y z ==> implements x y ==> implements x z`,
  CHEAT_TAC);;

let implements'_F = prove
 (`implements' F = implements`,
  CHEAT_TAC);;

let implements'_trans = prove
 (`!x y z b.
     implements' b y z /\
     implements' b x y ==>
     implements' b x z`,
  CHEAT_TAC);;

let implements'_strengthen = prove
 (`!b b' x y. (b' ==> b) /\ implements' b x y ==> implements' b' x y`,
  CHEAT_TAC);;

let implements'_IMP_implements = prove
 (`implements' b x y ==> implements x y`,
  CHEAT_TAC);;

let extend_with_resource_limit'_SUBSET = prove
 (`extend_with_resource_limit' b s SUBSET
   extend_with_resource_limit s`,
  CHEAT_TAC);;
