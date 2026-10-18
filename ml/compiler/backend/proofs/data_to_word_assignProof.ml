(* ======================================================== *)
(*  data_to_word_assignProof: ported from HOL4's
    compiler/backend/proofs/data_to_word_assignProofScript.sml  *)
(* ======================================================== *)

(*
  Part of the correctness proof for data_to_word
*)

needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/bvi_to_data.ml";;
needs "compiler/backend/data_to_word.ml";;
needs "compiler/backend/gc/copying_gc.ml";;
needs "compiler/backend/gc/gc_shared.ml";;
needs "compiler/backend/gc/gen_gc.ml";;
needs "compiler/backend/gc/gen_gc_partial.ml";;
needs "compiler/backend/proofs/data_to_word_bignumProof.ml";;
needs "compiler/backend/proofs/data_to_word_gcProof.ml";;
needs "compiler/backend/proofs/data_to_word_memoryProof.ml";;
needs "compiler/backend/proofs/word_bignumProof.ml";;
needs "compiler/backend/proofs/word_gcFunctions.ml";;
needs "compiler/backend/semantics/backendProps.ml";;
needs "compiler/backend/semantics/dataProps.ml";;
needs "compiler/backend/semantics/dataSem.ml";;
needs "compiler/backend/semantics/wordProps.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/backend/word_bignum.ml";;
needs "lib/alignment.ml";;
needs "lib/byte.ml";;
needs "lib/set_sep.ml";;
needs "semantics/proofs/semanticsProps.ml";;
needs "semantics/semanticPrimitives.ml";;
(* HOL4 ancestors outside the port: (* for word_add_carry *)
   int_bitwise While *)

(* HOL4 data_to_word_assignProofScript.sml:28-29: ML code, not ported *)

(* HOL4 data_to_word_assignProofScript.sml:38: the overload lookup,
   which the port expands *)

(* HOL4 data_to_word_assignProofScript.sml:40-42: ML code, not ported *)

(* HOL4 data_to_word_assignProofScript.sml:44-45: a proof *)

(* HOL4 data_to_word_assignProofScript.sml:47-48: ML code, not ported *)

(* HOL4 data_to_word_assignProofScript.sml:50-53: ML code, not ported *)

(* HOL4 data_to_word_assignProofScript.sml:55-60: a proof *)

(* This list must list all auxiliary definitions used in assign_def *)

(* TODO: should probably replace evaluate_GiveUp directly *)

(* TODO: move to sptreeTheory *)

(* TODO: move to sptreeTheory *)

(*TODO: move to backendProps *)

(* HOL4 data_to_word_assignProofScript.sml:629-631: a proof *)

let is_env_def = cake_define
  `is_env st = (?n vs. st = Env n vs)`;;

(* TODO: copypasta from costPropsScript *)

(* TODO: copypaste from costProps *)

(* HOL4 data_to_word_assignProofScript.sml:1387-1391: ML code, not
   ported *)

(* HOL4 data_to_word_assignProofScript.sml:1765-1778: the ML values
   that the definitions below antiquote *)

(* HOL4 data_to_word_assignProofScript.sml:1780-1781: the ML values
   that the definitions below antiquote *)

let w2w_upper_def = cake_define
  `w2w_upper (w:word64) =
     (if dimindex (:'a) = 32 then ((63 >< 32) w):'a word else w2w
       w)`;;

(* HOL4 data_to_word_assignProofScript.sml:2146-2147: ML code, not
   ported *)

(* HOL4 data_to_word_assignProofScript.sml:2210-2212: ML code, not
   ported *)

(* cut_env is idempotent: cutting the same names twice gives the same
   result. *)

(* Two-stage cut: narrowing an args-augmented cut (list_insert args ns)
   down to
   ns gives the same env as cutting ns directly. *)

(* A join_env pair-list over (l1,l2) is contained in the one over any
   lookup-supermaps (l1',l2') — moves memory_rel pairs between a cut env
   and the full env (with memory_rel_rearrange). *)

(* The three heap-store FLOOKUPs follow directly from state_rel.
   Reusable in any op that needs to inspect
     t.store.{NextFree,CurrHeap,HeapLength}. *)

(* Evaluating a SilentFFI block (the c.call_empty_ffi=T form emitted by
   op_requires_names ops, with var slot 3): if the word state's locals
     can be
   cut by the same names, the FFI call has empty payload and reduces to
     a
   locals-updated state. Reusable in any op whose generated code begins
     or
   resumes with `SilentFFI c 3 (adjust_sets <names>)`. *)

(* size_of_heap monotonicity helpers *)


(* end size_of_heap monotonicity helpers *)

let STOP_def = cake_define
  `data_to_word_assignProof_STOP x = x`;;
hol4_overload "STOP" "data_to_word_assignProof_STOP";;
(* HOL4 data_to_word_assignProofScript.sml:5278-5281: ML code, not
   ported *)
(* HOL4 data_to_word_assignProofScript.sml:5370-5371: ML code, not
   ported *)

(* TODO: declared with [simp] further down *)

(* TODO: move *)

(* ConfigGC: assign-specific helper + body *)

(* Prepending values to the size_of root list never shrinks the heap
   count.
   Basis for the args-aware do_space bridge (replaces the two-stage
     size_of
   narrow/wide reconciliation helpers). *)
(* size_of_LE_append and size_of_heap_LE_args are inherited from
   data_to_word_bignumProof (used there by eval_Call_Arith). *)

(* The single narrow cut state IS cut_locals of the original:
   alloc_lemma's
   size_of_heap (cut_locals ns s) is exactly size_of_heap x. *)

(* ---- helpers used by assign_FromList's NES/Success arms (also reused
   by
   assign_RefByte etc. below); hoisted above assign_FromList so they are
     in
   scope here. ---- *)

(* do_app for FromList sets the result stack_max uniformly
   (stack_consumed is
   the same for the empty and nonempty cases), regardless of tstamps. *)

(* do_app for FromList: the result safe_for_space field, uniform over
   the empty
   and nonempty cases (the empty case lacks the with_fresh_ts/check_lim
     wrapper,
   but its extra `LENGTH ys < 2 ** length_limit` conjunct is trivially
     true). The
   add_space_safe_args / the F terms are dataSem overloads; the
     statement spells
   them out so it parses without the abbreviation. *)

(* do_app for FromList: the result value is a Block of the source list,
   and the
   non-stack/safe/space fields are preserved from the input state
     (tstamps gains
   a fresh stamp for nonempty lists). Used by assign_FromList's success
     arm to
   relate s2 (do_app on x) and s2_inner (do_app on s_pop): both share
     these
   fields because x and s_pop agree on locals/refs/tstamps/.... *)

(* Variant of call_env_push_env_dec_clock_lift that also absorbs a
   `locals
   := insert k v t.locals` field update inside the dec_clock. *)

(* TODO: move to backendProps? *)

(* Helper: do_app on RefByte gives a precise equation s' = s with
   <known-update>
   (args-aware single-cut form). Used to bridge s2_inner field
     equalities in
   assign_RefByte's Success arm. *)

(* Helper: lift inner-with on a dec_clock'd state to outer-with on
   call_env/push_env.
   Used to bridge the post-Call evaluate term to the shape expected by
   evaluate_IMP_domain_union (which has outer-with). *)

(* Binary (two-argument) instance of AllocVar_thm_nary, used by
   assign_RefArray. *)

(* HOL4 data_to_word_assignProofScript.sml:9692-9693: ML code, not
   ported *)

(* HOL4 data_to_word_assignProofScript.sml:9695-9696: ML code, not
   ported *)

(* HOL4 data_to_word_assignProofScript.sml:9698-9699: ML code, not
   ported *)

(* HOL4 data_to_word_assignProofScript.sml:9701-9702: ML code, not
   ported *)

(* HOL4 data_to_word_assignProofScript.sml:9704-9705: ML code, not
   ported *)

(* TODO: move? *)

(* TODO: move to backendProps *)

let sane_locals_size_def = cake_define
  `sane_locals_size t = (state_locals_size t = sptree_lookup
  Equal_location (wordSem_state_stack_size t) \/ state_locals_size
                         t = sptree_lookup Equal1_location
                           (wordSem_state_stack_size t))`;;

(* HOL4 data_to_word_assignProofScript.sml:13152-13154: the ML values
   that the definitions below antiquote *)

(* HOL4 data_to_word_assignProofScript.sml:13734-13736: the ML values
   that the definitions below antiquote *)

(* HOL4 data_to_word_assignProofScript.sml:13990-13992: ML code, not
   ported *)

(* HOL4 data_to_word_assignProofScript.sml:13994-13996: ML code, not
   ported *)

(* HOL4 data_to_word_assignProofScript.sml:13998-14000: ML code, not
   ported *)

(* HOL4 data_to_word_assignProofScript.sml:14002-14004: ML code, not
   ported *)

let memcopy_def = cake_define
  `memcopy k a1 a2 m dm =
     (if k = 0 then SOME m else
       if a1 IN dm /\ a2 IN dm then
         memcopy (k - 1) (a1 + bytes_in_word) (a2 + bytes_in_word)
           ((a2 =+ m a1) m) dm else NONE)`;;


(* HOL4 data_to_word_assignProofScript.sml:16926: ML code, not ported *)
