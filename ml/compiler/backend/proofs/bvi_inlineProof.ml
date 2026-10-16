(* ======================================================== *)
(*  bvi_inlineProof: ported from HOL4's
    compiler/backend/proofs/bvi_inlineProofScript.sml  *)
(* ======================================================== *)

(*
  Correctness of the CPR worker-wrapper BVI inliner. The cache [cs] is
  persistent across incremental compilation: a cache hit causes the
  matching call to be inlined, and cache entries are trusted only when
  their bodies and arities agree with the compiled code table.
*)

needs "compiler/backend/bvi_inline.ml";;
needs "compiler/backend/bvl_const.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/semantics/backendProps.ml";;
needs "compiler/backend/semantics/bviProps.ml";;
needs "compiler/backend/semantics/bviSem.ml";;
needs "lib/sptree.ml";;
needs "semantics/ast.ml";;

let cache_code_labels_def = cake_define
  `cache_code_labels (cs:(num#bvi_exp) spt) =
     BIGUNION (set_of_list (MAP (bviProps_get_code_labels o SND)
       (sptree_toList cs)))`;;

(* [exp_rel c] relates a source expression to its image under the
   inlining
   phase, where [c] is the transformed target code table.
   [exp_rel_inline] is the only rule that removes a Call boundary. *)
let exp_rel = cake_inductive
  `((!c n. bvi_inlineProof_exp_rel c (Var n) (Var n))) /\
   ((!c loc n. bvi_inlineProof_exp_rel c (Force loc n) (Force loc
     n))) /\
   ((!c x1 x2 x3 y1 y2 y3.
        bvi_inlineProof_exp_rel c x1 y1 /\ bvi_inlineProof_exp_rel c
          x2 y2 /\ bvi_inlineProof_exp_rel c x3 y3 ==>
        bvi_inlineProof_exp_rel c (If x1 x2 x3) (If y1 y2 y3))) /\
   ((!c xs ys x y.
        LIST_REL (bvi_inlineProof_exp_rel c) xs ys /\
          bvi_inlineProof_exp_rel c x y ==>
        bvi_inlineProof_exp_rel c (Let xs x) (Let ys y))) /\
   ((!c x y. bvi_inlineProof_exp_rel c x y ==>
     bvi_inlineProof_exp_rel c (Raise x) (Raise y))) /\
   ((!c x y. bvi_inlineProof_exp_rel c x y ==>
     bvi_inlineProof_exp_rel c (Tick x) (Tick y))) /\
   ((!c op xs ys. LIST_REL (bvi_inlineProof_exp_rel c) xs ys ==>
        bvi_inlineProof_exp_rel c (Op op xs) (Op op ys))) /\
   ((!c ticks dest xs ys handler handler1.
        LIST_REL (bvi_inlineProof_exp_rel c) xs ys /\ OPTREL
          (bvi_inlineProof_exp_rel c) handler handler1 ==>
        bvi_inlineProof_exp_rel c (bvi_Call ticks dest xs handler)
          (bvi_Call ticks dest ys handler1))) /\
   ((!c rets ticks dest xs ys x y.
        LIST_REL (bvi_inlineProof_exp_rel c) xs ys /\
          bvi_inlineProof_exp_rel c x y ==>
        bvi_inlineProof_exp_rel c (bvi_LetCall rets ticks dest xs x)
          (bvi_LetCall rets ticks dest ys y))) /\
   ((!c xs ys. LIST_REL (bvi_inlineProof_exp_rel c) xs ys ==>
        bvi_inlineProof_exp_rel c (bvi_Return xs) (bvi_Return ys)))
          /\
   ((!c ticks n xs ys arity body.
        LIST_REL (bvi_inlineProof_exp_rel c) xs ys /\ sptree_lookup n
          c = SOME (arity,body) /\
        LENGTH ys = arity ==>
        bvi_inlineProof_exp_rel c (bvi_Call ticks (SOME n) xs NONE)
          (Let ys (bvi_mk_tick (SUC ticks) body))))`;;
hol4_overload "exp_rel" "bvi_inlineProof_exp_rel";;

let in_cc_def = cake_define
  `bvi_inlineProof_in_cc cc =
     (\(cs,cfg) prog.
        let (cs1,prog1) = inline_all cs prog in
          match cc cfg prog1 with NONE -> NONE | SOME
            (code,data,cfg1) -> SOME (code,data,(cs1,cfg1)))`;;
hol4_overload "in_cc" "bvi_inlineProof_in_cc";;

let in_co_def = cake_define
  `bvi_inlineProof_in_co co =
     (\n.
        let ((cs,cfg),prog) = co n in
        let (cs1,prog1) = inline_all cs prog in
          (cfg,prog1))`;;
hol4_overload "in_co" "bvi_inlineProof_in_co";;

let in_state_rel_def = cake_define
  `bvi_inlineProof_in_state_rel s (t:('c,'ffi)bviSem_state) <=>
  state_refs
     t = state_refs s /\ state_clock
     t = state_clock s /\ bviSem_state_global
     t = bviSem_state_global s /\ state_ffi
     t = state_ffi s /\ compile_oracle
     t = bvi_inlineProof_in_co (compile_oracle s) /\
     subspt (FST (FST (compile_oracle s 0))) (state_code t) /\
       compile
     s = bvi_inlineProof_in_cc (compile t) /\
     domain (state_code t) = domain (state_code s) /\
     (!k arity exp.
        sptree_lookup k (state_code s) = SOME (arity,exp) ==>
        (?exp1. sptree_lookup k (state_code t) = SOME (arity,exp1) /\
               bvi_inlineProof_exp_rel (state_code t) exp exp1))`;;
hol4_overload "in_state_rel" "bvi_inlineProof_in_state_rel";;

(* Inversion of [exp_rel] on each source constructor. [~inline] is why
   the
   Call clause has a second disjunct. *)

(* The inlined form of a Call evaluates exactly like the Call it
   replaces:
   the extra environment entries are unreachable, and the two differ on
     a
   [Ret]-raise only, which the side condition excludes. *)

(* HOL4 ML code, not ported:
Resume evaluate_inline[CONS]:
  Cases_on `es1`
  >- gvs []
  >> gvs []
  >> qmatch_asmsub_rename_tac `exp_rel t.code x y1`
  >> qmatch_asmsub_rename_tac `exp_rel t.code y y2`
  >> qmatch_asmsub_rename_tac `LIST_REL (exp_rel t.code) xs ys2`
  >> qpat_x_assum `evaluate (_::_::_,_,_) = _` mp_tac
  >> once_rewrite_tac [evaluate_CONS]
  >> namedCases_on `evaluate ([x],env,s)` ["head_res head_state"]
  >> namedCases_on `head_res` ["head_vals", "head_err"]
  >> gvs []
  >> strip_tac
  >> gvs []
  >> qpat_x_assum `∀t1 es. in_state_rel s t1 ∧ _ ⇒ _`
       (qspecl_then [`t`,`[y1]`] mp_tac)
  >> simp []
  >> strip_tac
  >> gvs []
  >> namedCases_on `evaluate (y::xs,env,head_state)`
       ["tail_res tail_state"]
  >> namedCases_on `tail_res` ["tail_vals", "tail_err"]
  >> gvs []
  >> `exp_rel t1.code y y2 ∧ LIST_REL (exp_rel t1.code) xs ys2` by
       metis_tac [exp_rel_evaluate_mono]
  >> qpat_x_assum `∀t1 es. in_state_rel head_state t1 ∧ _ ⇒ _`
       (qspecl_then [`t1`,`y2::ys2`] mp_tac)
  >> simp []
  >> strip_tac
  >> gvs []
QED
*)


(* HOL4 ML code, not ported:
Resume evaluate_inline[Var]:
  gvs [evaluate_def, AllCaseEqs()]
QED
*)


(* HOL4 ML code, not ported:
Resume evaluate_inline[If]:
  gvs []
  >> qpat_x_assum `evaluate ([If _ _ _],_,_) = _` mp_tac
  >> simp [evaluate_def]
  >> namedCases_on `evaluate ([x1],env,s)` ["cond_res cond_state"]
  >> namedCases_on `cond_res` ["cond_vals", "cond_err"]
  >> gvs []
  >> strip_tac
  >> gvs []
  >> qpat_x_assum `∀t1 es. in_state_rel s t1 ∧ _ ⇒ _`
       (qspecl_then [`t`,`[y1]`] mp_tac)
  >> simp []
  >> strip_tac
  >> gvs []
  >> `exp_rel t1.code x2 y2 ∧ exp_rel t1.code x3 y3` by
       metis_tac [exp_rel_evaluate_mono]
  >> Cases_on `HD cond_vals = Boolv T`
  >> gvs []
  >> Cases_on `HD cond_vals = Boolv F`
  >> gvs []
  >> metis_tac []
QED
*)


(* HOL4 ML code, not ported:
Resume evaluate_inline[Let]:
  gvs []
  >> qpat_x_assum `evaluate ([Let _ _],_,_) = _` mp_tac
  >> simp [evaluate_def]
  >> namedCases_on `evaluate (xs,env,s)` ["binds_res binds_state"]
  >> namedCases_on `binds_res` ["binds_vals", "binds_err"]
  >> gvs []
  >> strip_tac
  >> gvs []
  >> qpat_x_assum `∀t1 es. in_state_rel s t1 ∧ _ ⇒ _`
       (qspecl_then [`t`,`ys`] mp_tac)
  >> simp []
  >> strip_tac
  >> gvs []
  >> `exp_rel t1.code x2 y1` by metis_tac [exp_rel_evaluate_mono]
  >> metis_tac []
QED
*)


(* HOL4 ML code, not ported:
Resume evaluate_inline[Raise]:
  gvs []
  >> qpat_x_assum `evaluate ([Raise _],_,_) = _` mp_tac
  >> simp [evaluate_def]
  >> namedCases_on `evaluate ([x1],env,s)` ["sub_res sub_state"]
  >> namedCases_on `sub_res` ["sub_vals", "sub_err"]
  >> gvs []
  >> strip_tac
  >> gvs []
  >> qpat_x_assum `∀t1 es. in_state_rel s t1 ∧ _ ⇒ _`
       (qspecl_then [`t`,`[y1]`] mp_tac)
  >> simp []
  >> strip_tac
  >> gvs []
QED
*)


(* HOL4 ML code, not ported:
Resume evaluate_inline[Return]:
  gvs []
  >> qpat_x_assum `evaluate ([Return _],_,_) = _` mp_tac
  >> simp [evaluate_def]
  >> namedCases_on `evaluate (xs,env,s)` ["ret_res ret_state"]
  >> namedCases_on `ret_res` ["ret_vals", "ret_err"]
  >> gvs []
  >> strip_tac
  >> gvs []
  >> qpat_x_assum `∀t1 es. in_state_rel s t1 ∧ _ ⇒ _`
       (qspecl_then [`t`,`ys`] mp_tac)
  >> simp []
  >> strip_tac
  >> gvs []
QED
*)


(* HOL4 ML code, not ported:
Resume evaluate_inline[Op]:
  gvs []
  >> qpat_x_assum `evaluate ([Op _ _],_,_) = _` mp_tac
  >> simp [evaluate_def]
  >> namedCases_on `evaluate (xs,env,s)` ["args_res args_state"]
  >> namedCases_on `args_res` ["args_vals", "args_err"]
  >> gvs []
  >> strip_tac
  >> gvs []
  >> qpat_x_assum `∀t1 es. in_state_rel s t1 ∧ _ ⇒ _`
       (qspecl_then [`t`,`ys`] mp_tac)
  >> simp []
  >> strip_tac
  >> gvs [AllCaseEqs()]
  >> drule (Q.GEN `a` in_do_app_lemma)
  >> disch_then (qspecl_then [`op`,`REVERSE args_vals`] mp_tac)
  >> gvs []
  >> strip_tac
  >> gvs []
QED
*)


(* HOL4 ML code, not ported:
Resume evaluate_inline[Tick]:
  gvs []
  >> `s.clock = t.clock` by gvs [in_state_rel_def]
  >> qpat_x_assum `evaluate ([Tick _],_,_) = _` mp_tac
  >> simp [evaluate_def]
  >> IF_CASES_TAC
  >> gvs []
  >> strip_tac
  >> gvs []
  >> `in_state_rel (dec_clock 1 s) (dec_clock 1 t)`
       by gvs [in_state_rel_def, dec_clock_def]
  >> qpat_x_assum `∀t1 es. in_state_rel (dec_clock 1 s) t1 ∧ _ ⇒ _`
       (qspecl_then [`dec_clock 1 t`,`[y1]`] mp_tac)
  >> simp []
QED
*)


(* HOL4 ML code, not ported:
Resume evaluate_inline[Force]:
  gvs []
  >> `s.refs = t.refs ∧ s.clock = t.clock` by gvs [in_state_rel_def]
  >> gvs [AllCaseEqs(), evaluate_def, oneline dest_thunk_def,
    PULL_EXISTS]
  >> drule_all in_state_rel_find_code
  >> strip_tac
  >- gvs [in_state_rel_def]
  >> `in_state_rel (dec_clock 1 s) (dec_clock 1 t)`
       by gvs [in_state_rel_def, dec_clock_def]
  >> qpat_x_assum `∀t1 y. in_state_rel (dec_clock 1 s) t1 ∧ _ ⇒ _`
       (qspecl_then [`dec_clock 1 t`,`exp1`] mp_tac)
  >> gvs [dec_clock_def]
  >> metis_tac []
QED
*)


(* HOL4 ML code, not ported:
Resume evaluate_inline[Call]:
  qsuff_tac
    `∀ys handler1.
       LIST_REL (exp_rel t.code) xs ys ∧
       OPTREL (exp_rel t.code) handler handler1 ⇒
       ∃t1. evaluate ([Call ticks dest ys handler1],env,t) = (res,t1) ∧
            in_state_rel s1' t1`
  >- (strip_tac
      >> gvs []
      >> first_x_assum (qspec_then `ys` mp_tac)
      >> simp []
      >> strip_tac
      >> `FST (evaluate ([Call ticks (SOME n) ys NONE],env,t)) ≠
            Rerr (Rabort Rtype_error)` by simp []
      >> drule_all evaluate_inlined_call
      >> strip_tac
      >> gvs [])
  >> rpt strip_tac
  >> qpat_x_assum `LIST_REL _ [Call _ _ _ _] _` kall_tac
  >> `IS_SOME handler ⇔ IS_SOME handler1` by gvs [OPTREL_def]
  >> qpat_x_assum `evaluate ([Call _ _ _ _],_,_) = _` mp_tac
  >> simp [evaluate_def]
  >> IF_CASES_TAC
  >> gvs []
  >> namedCases_on `evaluate (xs,env,s1)` ["args_res args_state"]
  >> namedCases_on `args_res` ["args_vals", "args_err"]
  >> gvs []
  >> strip_tac
  >> gvs []
  >> qpat_x_assum `∀t1 es. in_state_rel s1 t1 ∧ _ ⇒ _`
       (qspecl_then [`t`,`ys`] mp_tac)
  >> simp []
  >> strip_tac
  >> gvs []
  >> `t1.clock = args_state.clock` by gvs [in_state_rel_def]
  >> namedCases_on `find_code dest args_vals args_state.code`
       ["", "code_entry"]
  >> gvs []
  >> PairCases_on `code_entry`
  >> qmatch_asmsub_rename_tac
       `find_code dest args_vals args_state.code = SOME
         (body_args,body_exp)`
  >> drule_all in_state_rel_find_code
  >> strip_tac
  >> `in_state_rel (args_state with clock := 0) (t1 with clock := 0) ∧
      in_state_rel (dec_clock (ticks + 1) args_state)
        (dec_clock (ticks + 1) t1)`
       by gvs [in_state_rel_def, dec_clock_def]
  >> gvs []
  >> IF_CASES_TAC
  >> gvs []
  >> namedCases_on
       `evaluate ([body_exp],body_args,dec_clock (ticks + 1)
         args_state)`
       ["body_res body_state"]
  >> `body_res ≠ Rerr (Rabort Rtype_error)` by (strip_tac >> gvs [])
  >> qpat_x_assum
       `∀res1 st t' es. in_state_rel (dec_clock (ticks + 1) args_state)
         t' ∧
          _ ⇒ _`
       (qspecl_then
          [`body_res`,`body_state`,`dec_clock (ticks + 1) t1`,`[exp1]`]
            mp_tac)
  >> simp [dec_clock_def]
  >> strip_tac
  >> gvs []
  >> namedCases_on `body_res` ["body_vals", "body_err"]
  >> gvs []
  >> namedCases_on `body_err` ["raised", "abort_kind"]
  >> gvs []
  >> namedCases_on `raised` ["exn_val", "ret_vals"]
  >> gvs []
  >> namedCases_on `handler` ["", "handler_exp"]
  >> gvs [OPTREL_def]
  >> qmatch_asmsub_rename_tac `exp_rel t.code handler_exp handler_exp1`
  >> `subspt t.code t1'.code` by
       (imp_res_tac evaluate_code_mono
        >> gvs []
        >> metis_tac [subspt_trans])
  >> `exp_rel t1'.code handler_exp handler_exp1` by metis_tac
    [exp_rel_mono]
  >> namedCases_on `evaluate ([handler_exp],exn_val::env,body_state)`
       ["h_res h_state"]
  >> `h_res ≠ Rerr (Rabort Rtype_error)` by (strip_tac >> gvs [])
  >> qpat_x_assum `∀res1 st t' es. in_state_rel body_state t' ∧ _ ⇒ _`
       (qspecl_then [`h_res`,`h_state`,`t1'`,`[handler_exp1]`] mp_tac)
  >> simp []
  >> strip_tac
  >> gvs []
  >> namedCases_on `h_res` ["h_vals", "h_err"]
  >> gvs []
  >> namedCases_on `h_err` ["h_raised", "h_abort"]
  >> gvs []
  >> namedCases_on `h_raised` ["h_exn", "h_ret"]
  >> gvs []
QED
*)

(* HOL4 ML code, not ported:
Resume evaluate_inline[LetCall]:
  gvs []
  >> qpat_x_assum `evaluate ([LetCall _ _ _ _ _],_,_) = _` mp_tac
  >> simp [evaluate_def]
  >> namedCases_on `evaluate (xs,env,s1)` ["args_res args_state"]
  >> namedCases_on `args_res` ["args_vals", "args_err"]
  >> gvs []
  >> strip_tac
  >> gvs []
  >> qpat_x_assum `∀t1 es. in_state_rel s1 t1 ∧ _ ⇒ _`
       (qspecl_then [`t`,`ys`] mp_tac)
  >> simp []
  >> strip_tac
  >> gvs []
  >> `t1.clock = args_state.clock` by gvs [in_state_rel_def]
  >> namedCases_on `find_code (SOME dest) args_vals args_state.code`
       ["", "code_entry"]
  >> gvs []
  >> PairCases_on `code_entry`
  >> qmatch_asmsub_rename_tac
       `find_code (SOME dest) args_vals args_state.code =
          SOME (body_args,body_exp)`
  >> drule_all in_state_rel_find_code
  >> strip_tac
  >> `in_state_rel (args_state with clock := 0) (t1 with clock := 0) ∧
      in_state_rel (dec_clock (ticks + 1) args_state)
        (dec_clock (ticks + 1) t1)`
       by gvs [in_state_rel_def, dec_clock_def]
  >> gvs []
  >> IF_CASES_TAC
  >> gvs []
  >> namedCases_on
       `evaluate ([body_exp],body_args,dec_clock (ticks + 1)
         args_state)`
       ["body_res body_state"]
  >> `body_res ≠ Rerr (Rabort Rtype_error)` by (strip_tac >> gvs [])
  >> qpat_x_assum
       `∀res1 st t' es. in_state_rel (dec_clock (ticks + 1) args_state)
         t' ∧
          _ ⇒ _`
       (qspecl_then
          [`body_res`,`body_state`,`dec_clock (ticks + 1) t1`,`[exp1]`]
            mp_tac)
  >> simp [dec_clock_def]
  >> strip_tac
  >> gvs []
  >> namedCases_on `body_res` ["body_vals", "body_err"]
  >> gvs []
  >> namedCases_on `body_err` ["raised", "abort_kind"]
  >> gvs []
  >> namedCases_on `raised` ["exn_val", "ret_vals"]
  >> gvs []
  >> IF_CASES_TAC
  >> gvs []
  >> `subspt t.code t1'.code` by
       (imp_res_tac evaluate_code_mono
        >> gvs []
        >> metis_tac [subspt_trans])
  >> `exp_rel t1'.code y y1` by metis_tac [exp_rel_mono]
  >> qpat_x_assum `∀t' es. in_state_rel body_state t' ∧ _ ⇒ _`
       (qspecl_then [`t1'`,`[y1]`] mp_tac)
  >> simp []
QED
*)


(* HOL4 ML code, not ported:
Finalise evaluate_inline;
*)

let clean_prog_def = cake_define
  `clean_prog prog =
     MAP (\(name,arity,body). (name,arity,remove_ticks_exp body))
       prog`;;

let remove_ticks_cc_def = cake_define
  `bvi_inlineProof_remove_ticks_cc cc = (\cfg prog. cc cfg
  (clean_prog prog))`;;
hol4_overload "remove_ticks_cc" "bvi_inlineProof_remove_ticks_cc";;

let remove_ticks_co_def = cake_define
  `bvi_inlineProof_remove_ticks_co = (I ## clean_prog)`;;
hol4_overload "remove_ticks_co" "bvi_inlineProof_remove_ticks_co";;

let remove_state_rel_def = cake_define
  `remove_state_rel (s:('c,'ffi)bviSem_state) (t:('c,'ffi)bviSem_state)
  <=> state_refs
     t = state_refs s /\ state_clock t = state_clock s /\
       bviSem_state_global t = bviSem_state_global s /\ state_ffi t =
       state_ffi s /\ state_code
     t = sptree_map (I ## remove_ticks_exp) (state_code s) /\
       compile_oracle
     t = bvi_inlineProof_remove_ticks_co o compile_oracle s /\
       compile
     s = bvi_inlineProof_remove_ticks_cc (compile t)`;;

(* HOL4 ML code, not ported:
Resume evaluate_remove_ticks_mutual[Var]:
  gvs [remove_ticks_exp_def, evaluate_def, AllCaseEqs()]
  >> qexists_tac `0`
  >> gvs [remove_state_rel_def]
QED
*)

(* HOL4 ML code, not ported:
Resume evaluate_remove_ticks_mutual[If]:
  gvs [remove_ticks_exp_def, evaluate_def]
  >> namedCases_on `evaluate ([remove_ticks_exp e],env,t)`
       ["cond_res cond_state"]
  >> qpat_x_assum
       `∀env t s res t1. _ ∧ _ ∧ evaluate ([remove_ticks_exp e],_,_) = _
         ⇒ _`
       (qspecl_then [`env`,`t`,`s`,`cond_res`,`cond_state`] mp_tac)
  >> simp []
  >> disch_then (qx_choosel_then [`cond_extra`,`cond_src`]
    strip_assume_tac)
  >> reverse (namedCases_on `cond_res` ["cond_vals", "cond_err"])
  >- (gvs [] >> qexistsl [`cond_extra`,`cond_src`] >> gvs [])
  >> gvs []
  >> reverse (Cases_on `HD cond_vals = Boolv T ∨ HD cond_vals = Boolv
    F`)
  >- (gvs [] >> qexistsl [`cond_extra`,`cond_src`] >> gvs [])
  >> pop_assum strip_assume_tac
  >> gvs []
  >> `cond_state.clock ≤ k` by (imp_res_tac evaluate_clock >> gvs [])
  >> first_x_assum drule_all
  >> disch_then (qx_choosel_then [`extra1`,`src1`] strip_assume_tac)
  >> qspecl_then
       [`[e]`,`env`,`s`,`Rval
         cond_vals`,`cond_src`,`cond_extra`,`extra1`]
       mp_tac evaluate_add_extra_clock
  >> simp []
  >> strip_tac
  >> qexistsl [`cond_extra + extra1`,`src1`]
  >> gvs []
QED
*)

(* HOL4 ML code, not ported:
Resume evaluate_remove_ticks_mutual[Let]:
  gvs [remove_ticks_exp_def, evaluate_def]
  >> namedCases_on `evaluate (remove_ticks_exps es,env,t)`
       ["args_res args_state"]
  >> qpat_x_assum
       `∀env t s res t1. _ ∧ _ ∧ evaluate (remove_ticks_exps es,_,_) = _
         ⇒ _`
       (qspecl_then [`env`,`t`,`s`,`args_res`,`args_state`] mp_tac)
  >> simp []
  >> disch_then (qx_choosel_then [`args_extra`,`args_src`]
    strip_assume_tac)
  >> reverse (namedCases_on `args_res` ["args_vals", "args_err"])
  >- (gvs [] >> qexistsl [`args_extra`,`args_src`] >> gvs [])
  >> gvs []
  >> `args_state.clock ≤ k` by (imp_res_tac evaluate_clock >> gvs [])
  >> first_x_assum drule_all
  >> disch_then (qx_choosel_then [`body_extra`,`body_src`]
    strip_assume_tac)
  >> qspecl_then
       [`es`,`env`,`s`,`Rval
         args_vals`,`args_src`,`args_extra`,`body_extra`]
       mp_tac evaluate_add_extra_clock
  >> simp []
  >> strip_tac
  >> qexistsl [`args_extra + body_extra`,`body_src`]
  >> gvs []
QED
*)

(* HOL4 ML code, not ported:
Resume evaluate_remove_ticks_mutual[Raise]:
  gvs [remove_ticks_exp_def, evaluate_def]
  >> namedCases_on `evaluate ([remove_ticks_exp e],env,t)`
    ["sub_res sub_state"]
  >> qpat_x_assum
       `∀env t s res t1. _ ∧ _ ∧ evaluate ([remove_ticks_exp e],_,_) = _
         ⇒ _`
       (qspecl_then [`env`,`t`,`s`,`sub_res`,`sub_state`] mp_tac)
  >> simp []
  >> disch_then (qx_choosel_then [`sub_extra`,`sub_src`]
    strip_assume_tac)
  >> namedCases_on `sub_res` ["sub_vals", "sub_err"]
  >> gvs []
  >> qexistsl [`sub_extra`,`sub_src`]
  >> gvs []
QED
*)

(* HOL4 ML code, not ported:
Resume evaluate_remove_ticks_mutual[Tick]:
  gvs [remove_ticks_exp_def, evaluate_def]
  >> qpat_x_assum
       `∀env t s res t1. _ ∧ _ ∧ evaluate ([remove_ticks_exp e],_,_) = _
         ⇒ _`
       (qspecl_then [`env`,`t`,`s`,`res`,`t1`] mp_tac)
  >> simp []
  >> disch_then (qx_choosel_then [`sub_extra`,`sub_src`]
    strip_assume_tac)
  >> qexistsl [`SUC sub_extra`,`sub_src`]
  >> gvs [ADD1, dec_clock_def]
QED
*)

(* HOL4 ML code, not ported:
Resume evaluate_remove_ticks_mutual[Call]:
  qpat_x_assum `evaluate _ = _` mp_tac
  >> simp [remove_ticks_exp_def, evaluate_def, IS_SOME_MAP]
  >> IF_CASES_TAC
  >- (strip_tac >> qexists_tac `0` >> gvs [remove_state_rel_def])
  >> qpat_x_assum `¬(_ = NONE ∧ IS_SOME _)` kall_tac
  >> namedCases_on `evaluate (remove_ticks_exps es,env,t)`
       ["args_res args_st"]
  >> qpat_x_assum
       `∀env t s res t1. _ ∧ _ ∧ evaluate (remove_ticks_exps es,_,_) = _
         ⇒ _`
       (qspecl_then [`env`,`t`,`s`,`args_res`,`args_st`] mp_tac)
  >> simp []
  >> disch_then (qx_choosel_then [`args_extra`,`args_src`]
    strip_assume_tac)
  >> imp_res_tac remove_state_rel_find_code_eq
  >> reverse (namedCases_on `args_res` ["arg_vals", "arg_err"])
  >- (strip_tac >> gvs [] >> qexistsl [`args_extra`,`args_src`] >> gvs
    [])
  >> strip_tac
  >> namedCases_on `find_code dest arg_vals args_src.code` ["",
    "callee"]
  >- (gvs [] >> qexistsl [`args_extra`,`args_src`] >> gvs [])
  >> PairCases_on `callee`
  >> `args_src.clock = args_st.clock` by gvs [remove_state_rel_def]
  >> gvs []
  >> Cases_on `args_st.clock = 0`
  >- (gvs []
      >> qexistsl [`args_extra`,`args_src with clock := 0`]
      >> gvs [remove_state_rel_def])
  >> gvs []
  >> namedCases_on
       `evaluate ([remove_ticks_exp callee1],callee0,dec_clock 1
         args_st)`
       ["body_res body_st"]
  >> `args_st.clock - 1 < k`
       by (irule clock_sub_lt >> imp_res_tac evaluate_clock >> gvs [])
  >> qpat_x_assum `∀m. m < k ⇒ _` (qspec_then `args_st.clock - 1`
    mp_tac)
  >> simp []
  >> strip_tac
  >> `remove_state_rel (dec_clock 1 args_src) (dec_clock 1 args_st) ∧
      (dec_clock 1 args_st).clock ≤ args_st.clock - 1`
       by gvs [remove_state_rel_def, dec_clock_def]
  >> first_x_assum drule_all
  >> disch_then (qx_choosel_then [`body_extra`,`body_src`]
    strip_assume_tac)
  >> qspecl_then
       [`es`,`env`,`s`,`Rval arg_vals`,`args_src`,`args_extra`,
        `ticks + body_extra`]
       mp_tac evaluate_add_extra_clock
  >> simp []
  >> strip_tac
  >> reverse (Cases_on `∃exn_val handle_exp.
                body_res = Rerr (Rraise (Exn exn_val)) ∧
                handler = SOME handle_exp`)
  >- (qexistsl [`args_extra + (ticks + body_extra)`,`body_src`]
      >> gvs [dec_clock_def, AllCaseEqs()])
  >> gvs []
  >> namedCases_on `evaluate ([remove_ticks_exp
    handle_exp],exn_val::env,body_st)`
       ["handler_res handler_st"]
  >> `body_st.clock ≤ k` by (imp_res_tac evaluate_clock >> gvs [])
  >> qpat_x_assum
       `∀env t s res t1.
          _ ∧ _ ∧ evaluate ([remove_ticks_exp handle_exp],_,_) = _ ⇒ _`
       (qspecl_then
          [`exn_val::env`,`body_st`,`body_src`,`handler_res`
            ,`handler_st`] mp_tac)
  >> simp []
  >> disch_then
       (qx_choosel_then [`handler_extra`,`handler_src`]
         strip_assume_tac)
  >> qspecl_then
       [`[callee1]`,`callee0`,`dec_clock 1 args_src`,
        `Rerr (Rraise (Exn
          exn_val))`,`body_src`,`body_extra`,`handler_extra`]
       mp_tac evaluate_add_extra_clock
  >> simp []
  >> strip_tac
  >> qspecl_then
       [`es`,`env`,`s`,`Rval arg_vals`,`args_src`,`args_extra`,
        `ticks + body_extra + handler_extra`]
       mp_tac evaluate_add_extra_clock
  >> simp []
  >> strip_tac
  >> qexistsl
       [`args_extra + (ticks + body_extra +
         handler_extra)`,`handler_src`]
  >> gvs [dec_clock_def, AllCaseEqs()]
QED
*)

(* HOL4 ML code, not ported:
Resume evaluate_remove_ticks_mutual[Force]:
  `t.refs = s.refs ∧ t.clock = s.clock` by gvs [remove_state_rel_def]
  >> drule remove_state_rel_find_code_eq
  >> strip_tac
  >> qpat_x_assum `evaluate _ = _` mp_tac
  >> simp [remove_ticks_exp_def, evaluate_def]
  >> strip_tac
  >> reverse (Cases_on `n < LENGTH env ∧
                        ∃thunk_val callee_env callee_body.
                          dest_thunk (EL n env) s.refs =
                            IsThunk NotEvaluated thunk_val ∧
                          find_code (SOME loc) [EL n env; thunk_val]
                            s.code =
                            SOME (callee_env,callee_body)`)
  >- (gvs [AllCaseEqs()] >> qexists_tac `0` >> gvs
    [remove_state_rel_def])
  >> gvs [AllCaseEqs()]
  >- (qexistsl [`0`,`s with clock := 0`] >> gvs [remove_state_rel_def])
  >> `s.clock - 1 < k` by (irule clock_sub_lt >> gvs [])
  >> qpat_x_assum `∀m. m < k ⇒ _` (qspec_then `s.clock - 1` mp_tac)
  >> simp []
  >> strip_tac
  >> `remove_state_rel (dec_clock 1 s) (dec_clock 1 t) ∧
      (dec_clock 1 t).clock ≤ s.clock - 1`
       by gvs [remove_state_rel_def, dec_clock_def]
  >> first_x_assum drule_all
  >> disch_then (qx_choosel_then [`body_extra`,`body_src`]
    strip_assume_tac)
  >> qexistsl [`body_extra`,`body_src`]
  >> gvs [dec_clock_def]
QED
*)

(* HOL4 ML code, not ported:
Resume evaluate_remove_ticks_mutual[Op]:
  gvs [remove_ticks_exp_def, evaluate_def]
  >> namedCases_on `evaluate (remove_ticks_exps es,env,t)`
       ["args_res args_st"]
  >> qpat_x_assum
       `∀env t s res t1. _ ∧ _ ∧ evaluate (remove_ticks_exps es,_,_) = _
         ⇒ _`
       (qspecl_then [`env`,`t`,`s`,`args_res`,`args_st`] mp_tac)
  >> simp []
  >> disch_then (qx_choosel_then [`args_extra`,`args_src`]
    strip_assume_tac)
  >> reverse (namedCases_on `args_res` ["args_vals", "args_err"])
  >- (gvs [] >> qexistsl [`args_extra`,`args_src`] >> gvs [])
  >> gvs []
  >> qspecl_then [`op`,`REVERSE args_vals`,`args_src`,`args_st`]
       mp_tac remove_state_rel_do_app
  >> simp []
  >> namedCases_on `do_app op (REVERSE args_vals) args_src`
       ["app_res", "app_err"]
  >- (PairCases_on `app_res`
      >> gvs []
      >> strip_tac
      >> qexists_tac `args_extra`
      >> gvs [])
  >> gvs []
  >> strip_tac
  >> qexistsl [`args_extra`,`args_src`]
  >> gvs []
QED
*)

(* HOL4 ML code, not ported:
Resume evaluate_remove_ticks_mutual[LetCall]:
  qpat_x_assum `evaluate _ = _` mp_tac
  >> simp [remove_ticks_exp_def, evaluate_def]
  >> namedCases_on `evaluate (remove_ticks_exps es,env,t)`
       ["args_res args_st"]
  >> qpat_x_assum
       `∀env t s res t1. _ ∧ _ ∧ evaluate (remove_ticks_exps es,_,_) = _
         ⇒ _`
       (qspecl_then [`env`,`t`,`s`,`args_res`,`args_st`] mp_tac)
  >> simp []
  >> disch_then (qx_choosel_then [`args_extra`,`args_src`]
    strip_assume_tac)
  >> imp_res_tac remove_state_rel_find_code_eq
  >> reverse (namedCases_on `args_res` ["arg_vals", "arg_err"])
  >- (strip_tac >> gvs [] >> qexistsl [`args_extra`,`args_src`] >> gvs
    [])
  >> strip_tac
  >> namedCases_on `find_code (SOME dest) arg_vals args_src.code` ["",
    "callee"]
  >- (gvs [] >> qexistsl [`args_extra`,`args_src`] >> gvs [])
  >> PairCases_on `callee`
  >> `args_src.clock = args_st.clock` by gvs [remove_state_rel_def]
  >> gvs []
  >> Cases_on `args_st.clock = 0`
  >- (gvs []
      >> qexistsl [`args_extra`,`args_src with clock := 0`]
      >> gvs [remove_state_rel_def])
  >> gvs []
  >> namedCases_on
       `evaluate ([remove_ticks_exp callee1],callee0,dec_clock 1
         args_st)`
       ["body_res body_st"]
  >> `args_st.clock - 1 < k`
       by (irule clock_sub_lt >> imp_res_tac evaluate_clock >> gvs [])
  >> qpat_x_assum `∀m. m < k ⇒ _` (qspec_then `args_st.clock - 1`
    mp_tac)
  >> simp []
  >> strip_tac
  >> `remove_state_rel (dec_clock 1 args_src) (dec_clock 1 args_st) ∧
      (dec_clock 1 args_st).clock ≤ args_st.clock - 1`
       by gvs [remove_state_rel_def, dec_clock_def]
  >> first_x_assum drule_all
  >> disch_then (qx_choosel_then [`body_extra`,`body_src`]
    strip_assume_tac)
  >> qspecl_then
       [`es`,`env`,`s`,`Rval arg_vals`,`args_src`,`args_extra`,
        `ticks + body_extra`]
       mp_tac evaluate_add_extra_clock
  >> simp []
  >> strip_tac
  >> reverse (Cases_on `∃ret_vals.
                body_res = Rerr (Rraise (Ret ret_vals)) ∧
                LENGTH ret_vals = rets`)
  >- (qexistsl [`args_extra + (ticks + body_extra)`,`body_src`]
      >> gvs [dec_clock_def, AllCaseEqs()])
  >> gvs []
  >> namedCases_on `evaluate ([remove_ticks_exp e],ret_vals ++
    env,body_st)`
       ["cont_res cont_st"]
  >> `body_st.clock ≤ k` by (imp_res_tac evaluate_clock >> gvs [])
  >> qpat_x_assum
       `∀env t s res t1. _ ∧ _ ∧ evaluate ([remove_ticks_exp e],_,_) = _
         ⇒ _`
       (qspecl_then
          [`ret_vals ++ env`,`body_st`,`body_src`,`cont_res`,`cont_st`]
            mp_tac)
  >> simp []
  >> disch_then (qx_choosel_then [`cont_extra`,`cont_src`]
    strip_assume_tac)
  >> qspecl_then
       [`[callee1]`,`callee0`,`dec_clock 1 args_src`,
        `Rerr (Rraise (Ret
          ret_vals))`,`body_src`,`body_extra`,`cont_extra`]
       mp_tac evaluate_add_extra_clock
  >> simp []
  >> strip_tac
  >> qspecl_then
       [`es`,`env`,`s`,`Rval arg_vals`,`args_src`,`args_extra`,
        `ticks + body_extra + cont_extra`]
       mp_tac evaluate_add_extra_clock
  >> simp []
  >> strip_tac
  >> qexistsl
       [`args_extra + (ticks + body_extra + cont_extra)`,`cont_src`]
  >> gvs [dec_clock_def, AllCaseEqs()]
QED
*)


(* HOL4 ML code, not ported:
Resume evaluate_remove_ticks_mutual[Return]:
  gvs [remove_ticks_exp_def, evaluate_def]
  >> namedCases_on `evaluate (remove_ticks_exps es,env,t)`
       ["args_res args_st"]
  >> qpat_x_assum
       `∀env t s res t1. _ ∧ _ ∧ evaluate (remove_ticks_exps es,_,_) = _
         ⇒ _`
       (qspecl_then [`env`,`t`,`s`,`args_res`,`args_st`] mp_tac)
  >> simp []
  >> disch_then (qx_choosel_then [`args_extra`,`args_src`]
    strip_assume_tac)
  >> namedCases_on `args_res` ["args_vals", "args_err"]
  >> gvs []
  >> qexistsl [`args_extra`,`args_src`]
  >> gvs []
QED
*)

(* HOL4 ML code, not ported:
Resume evaluate_remove_ticks_mutual[NIL]:
  gvs [remove_ticks_exp_def, evaluate_def]
  >> qexists_tac `0`
  >> gvs [remove_state_rel_def]
QED
*)

(* HOL4 ML code, not ported:
Resume evaluate_remove_ticks_mutual[CONS]:
  qpat_x_assum `evaluate _ = _` mp_tac
  >> simp [remove_ticks_exp_def]
  >> namedCases_on `es` ["", "tail_head tail_rest"]
  >- (strip_tac
      >> qpat_x_assum
           `∀env t s res t1. _ ∧ _ ∧ evaluate ([remove_ticks_exp e],_,_)
             = _ ⇒ _`
           (qspecl_then [`env`,`t`,`s`,`res`,`t1`] mp_tac)
      >> gvs [])
  >> simp [remove_ticks_exp_def, evaluate_def]
  >> namedCases_on `evaluate ([remove_ticks_exp e],env,t)`
    ["head_res head_st"]
  >> qpat_x_assum
       `∀env t s res t1. _ ∧ _ ∧ evaluate ([remove_ticks_exp e],_,_) = _
         ⇒ _`
       (qspecl_then [`env`,`t`,`s`,`head_res`,`head_st`] mp_tac)
  >> simp []
  >> disch_then (qx_choosel_then [`head_extra`,`head_src`]
    strip_assume_tac)
  >> reverse (namedCases_on `head_res` ["head_vals", "head_err"])
  >- (strip_tac >> gvs [] >> qexistsl [`head_extra`,`head_src`] >> gvs
    [])
  >> strip_tac
  >> namedCases_on
       `evaluate (remove_ticks_exps (tail_head::tail_rest),env,head_st)`
       ["tail_res tail_st"]
  >> `head_st.clock ≤ k` by (imp_res_tac evaluate_clock >> gvs [])
  >> qpat_x_assum
       `∀env t s res t1.
          _ ∧ _ ∧ evaluate (remove_ticks_exps
            (tail_head::tail_rest),_,_) = _ ⇒ _`
       (qspecl_then [`env`,`head_st`,`head_src`,`tail_res`,`tail_st`]
         mp_tac)
  >> simp [remove_ticks_exp_def]
  >> disch_then (qx_choosel_then [`tail_extra`,`tail_src`]
    strip_assume_tac)
  >> qspecl_then
       [`[e]`,`env`,`s`,`Rval
         head_vals`,`head_src`,`head_extra`,`tail_extra`]
       mp_tac evaluate_add_extra_clock
  >> simp []
  >> strip_tac
  >> qexistsl [`head_extra + tail_extra`,`tail_src`]
  >> gvs [remove_ticks_exp_def, AllCaseEqs()]
QED
*)


(* HOL4 ML code, not ported:
Finalise evaluate_remove_ticks_mutual;
*)
