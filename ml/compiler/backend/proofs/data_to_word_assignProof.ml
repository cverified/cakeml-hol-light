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

(* HOL4 ML code, not ported:
fun drule0 th =
  first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]
    th))
*)

(* HOL4 overload (expanded in the port):
     lookup = sptree$lookup *)

(* HOL4 ML code, not ported:
val assign_def =
  data_to_wordTheory.assign_def
  |> REWRITE_RULE [arg1_def, arg2_def, arg3_def, arg4_def,
    all_assign_defs];
*)

(* HOL4 ML code, not ported:
val clean_tac = rpt var_eq_tac \\ rpt (qpat_x_assum `T` kall_tac);
fun rpt_drule0 th = drule0 (th |> GEN_ALL) \\ rpt (disch_then drule0 \\
  fs []);
*)

(* HOL4 ML code, not ported:
val state_rel_def = data_to_word_gcProofTheory.state_rel_def;
val code_rel_def = data_to_word_gcProofTheory.code_rel_def;
*)

(* HOL4 ML code, not ported:
val do_app = LIST_CONJ [do_app_def,do_app_aux_def,do_space_def,
  data_spaceTheory.op_space_req_def,
  dataLangTheory.op_space_reset_def,
  do_stack_def,stack_consumed_def];
*)

(* HOL4 ML code, not ported:
val eval_tac = fs [wordSemTheory.evaluate_def,
  wordSemTheory.word_exp_def, wordSemTheory.set_var_def, set_var_def,
  wordSemTheory.get_store_def,
  wordSemTheory.get_var_def,
  wordSemTheory.the_words_def, wordSemTheory.mem_load_def,
  wordLangTheory.word_op_def, wordLangTheory.word_sh_def];
*)

(* This list must list all auxiliary definitions used in assign_def *)

(* TODO: should probably replace evaluate_GiveUp directly *)

(* TODO: move to sptreeTheory *)

(* TODO: move to sptreeTheory *)

(*TODO: move to backendProps *)

(* HOL4 ML code, not ported:
fun sort_tac n =
  CONV_TAC(PATH_CONV(String.concat(List.tabulate(n,(K "lr"))))(REWR_CONV
    set_byte_sort)) \\
  simp[good_dimindex_def]
*)

let is_env_def = cake_define
  `is_env st = (?n vs. st = Env n vs)`;;

(* TODO: copypasta from costPropsScript *)

(* TODO: copypaste from costProps *)

(* HOL4 ML code, not ported:
val get_var_get_real_addr_lemma =
    GEN_ALL(CONV_RULE(LAND_CONV(move_conj_left(
                                   same_const``wordSem$get_var`` o #1 o
                                   strip_comb o lhs)))
                     get_real_addr_lemma)
*)

(* HOL4 ML code, not ported:
val assign_thm_goal =
  ``state_rel c l1 l2 s (t:('a,'c,'ffi) wordSem$state) NONE locs ∧
   (op_requires_names op ≠ (names_opt = NONE)) ∧
   cut_state_opt names_opt s = SOME x ∧
   get_vars args s.locals = SOME vals ∧
   t.termdep > 1 ∧
   do_app op vals x = Rval (v,s2) ==>
   ?q r.
     evaluate (FST (assign c n l dest op args names_opt),t) = (q,r) ∧
     (q = SOME NotEnoughSpace ==>
      r.ffi = t.ffi ∧ option_le r.stack_max s2.stack_max ∧
      (c.gc_kind <> None ==> ~s2.safe_for_space)) ∧
     (q <> SOME NotEnoughSpace ==>
      state_rel c l1 l2 (set_var dest v s2) r NONE locs ∧ q = NONE)``;
*)

(* HOL4 ML code, not ported:
val evaluate_Assign =
  SIMP_CONV(srw_ss())[wordSemTheory.evaluate_def]``evaluate (Assign _ _,
    _)``
*)

let w2w_upper_def = cake_define
  `w2w_upper (w:word64) =
     (if dimindex (:'a) = 32 then ((63 >< 32) w):'a word else w2w
       w)`;;

(* HOL4 ML code, not ported:
fun cases_on_op q = Cases_on q >|
  map (MAP_EVERY Cases_on) [[], [], [], [], [`b`], [`g`], [`m`], [],
    [`t`]];
*)

(* HOL4 ML code, not ported:
val mk_wf_inter = MATCH_MP wf_mk_id (SPEC_ALL wf_inter) |> GEN_ALL;
val state_rel_cut_env' =
  state_rel_cut_env |> REWRITE_RULE [GSYM AND_IMP_INTRO];
*)

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
(* HOL4 ML code, not ported:
val evaluate_AppendMainLoop_code_alt = evaluate_AppendMainLoop_code_alt
  |> SPEC_ALL |> Q.INST [`k`|->`0`]
  |> SIMP_RULE std_ss []
  |> GEN_ALL;
*)
(* HOL4 ML code, not ported:
val evaluate_AppendLenLoop_code = evaluate_AppendLenLoop_code
  |> Q.SPEC `0` |> SIMP_RULE std_ss [] |> Q.GEN `refs`;
*)

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

(* HOL4 ML code, not ported:
val eval_Call_Add = Q.SPEC `0` eval_Call_Arith
  |> SIMP_RULE std_ss [int_op_def,Arith_location_def];
*)

(* HOL4 ML code, not ported:
val eval_Call_Sub = Q.SPEC `1` eval_Call_Arith
  |> SIMP_RULE std_ss [int_op_def,Arith_location_def];
*)

(* HOL4 ML code, not ported:
val eval_Call_Mul = Q.SPEC `4` eval_Call_Arith
  |> SIMP_RULE std_ss [int_op_def,Arith_location_def];
*)

(* HOL4 ML code, not ported:
val eval_Call_Div = Q.SPEC `5` eval_Call_Arith
  |> SIMP_RULE std_ss [int_op_def,Arith_location_def];
*)

(* HOL4 ML code, not ported:
val eval_Call_Mod = Q.SPEC `6` eval_Call_Arith
  |> SIMP_RULE std_ss [int_op_def,Arith_location_def];
*)

(* TODO: move? *)

(* TODO: move to backendProps *)

let sane_locals_size_def = cake_define
  `sane_locals_size t = (?_locals_size t = sptree_lookup Equal_location
  (wordSem_state_stack_size t) \/ ?_locals_size
                         t = sptree_lookup Equal1_location
                           (wordSem_state_stack_size t))`;;

(* HOL4 ML code, not ported:
val assign_WordOp64 =
  ``assign c n l dest (WordOp (WordOpw W64 opw)) [e1; e2] names_opt``
  |> SIMP_CONV (srw_ss()) [assign_def]
*)

(* HOL4 ML code, not ported:
val assign_WordShift64 =
  ``assign c n l dest (WordOp (WordShift W64 sh n)) [e1] names_opt``
  |> SIMP_CONV (srw_ss()) [assign_def]
*)

(* HOL4 ML code, not ported:
val assign_FP_cmp = SIMP_CONV (srw_ss()) [assign_def]
  ``((assign (c:data_to_word$config) (secn:num) (l:num) (dest:num)
    (WordOp (FP_cmp fpc))
       (args:num list) (names:num_set option)):'a wordLang$prog #
         num)``;
*)

(* HOL4 ML code, not ported:
val assign_FP_top = SIMP_CONV (srw_ss()) [assign_def]
  ``((assign (c:data_to_word$config) (secn:num) (l:num) (dest:num)
    (WordOp (FP_top fpt))
       (args:num list) (names:num_set option)):'a wordLang$prog #
         num)``;
*)

(* HOL4 ML code, not ported:
val assign_FP_bop = SIMP_CONV (srw_ss()) [assign_def]
  ``((assign (c:data_to_word$config) (secn:num) (l:num) (dest:num)
    (WordOp (FP_bop fpb))
       (args:num list) (names:num_set option)):'a wordLang$prog #
         num)``;
*)

(* HOL4 ML code, not ported:
val assign_FP_uop = SIMP_CONV (srw_ss()) [assign_def]
  ``((assign (c:data_to_word$config) (secn:num) (l:num) (dest:num)
    (WordOp (FP_uop fpu))
       (args:num list) (names:num_set option)):'a wordLang$prog #
         num)``;
*)

let memcopy_def = cake_define
  `memcopy k a1 a2 m dm =
     (if k = 0 then SOME m else
       if a1 IN dm /\ a2 IN dm then
         memcopy (k - 1) (a1 + bytes_in_word) (a2 + bytes_in_word)
           ((a2 =+ m a1) m) dm else NONE)`;;


(* HOL4 ML code, not ported:
fun foldr1 f (x::xs) = foldr f x xs | foldr1 f [] = fail();
*)
