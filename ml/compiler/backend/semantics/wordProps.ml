(* ======================================================== *)
(*  wordProps: ported from HOL4's
    compiler/backend/semantics/wordPropsScript.sml  *)
(* ======================================================== *)

(*
  Properties about wordLang and its semantics
*)

needs "basis/pure/mllist.ml";;
needs "compiler/backend/pattern_matching/pattern_semantics.ml";;
needs "compiler/backend/reg_alloc/reg_alloc.ml";;
needs "compiler/backend/semantics/backendProps.ml";;
needs "compiler/backend/semantics/wordConvs.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/backend/stackLang.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "lib/sptree.ml";;

(*
Main lemmas:
0) Clock lemmas (add_clock, dec_clock, IO monotonicity)
1) Code table constancy across eval
2) Swapping stack for one with identical values (but different keys)
3) Thms to handle the permutation oracle
4) Effect of extra locals (locals_rel)
*)

(*TODO remove *)

(*TODO move*)

(* TODO: move *)

(* HOL4 ML code, not ported:
val GENLIST_I =
  GENLIST_EL |> Q.SPECL [`xs`,`\i. EL i xs`,`LENGTH xs`]
    |> SIMP_RULE std_ss []
*)

(* HOL4 ML code, not ported:
val ALL_DISTINCT_EL = ``ALL_DISTINCT xs``
  |> ONCE_REWRITE_CONV [GSYM GENLIST_I]
  |> SIMP_RULE std_ss [ALL_DISTINCT_GENLIST]
*)

(* -- *)
(*drulel takes a list and tries to apply drule
*)
(* HOL4 ML code, not ported:
fun drulel tl = FIRST (map (drule) tl)
*)
(*This is faster than gvs[AllCaseEqs()]*)
(* HOL4 ML code, not ported:
val CASE_ONE = (TOP_CASE_TAC ORELSE pairarg_tac )
*)
(* Clock lemmas *)

(*helps with existence proofs
?l'. (s with locals := l) = (s with locals := l')*)
(*TODO does not work when given a goal like
?k'. (s with <|locals := l; clock := k|>) = (s with <|locals := l, clock
  := k |>)
*)

(*TODO Weaken this simplification
What that is needed to be pulled down is when
f is a record update like (λs. s with clock := k)
*)

(*USEFUL to clean up proofs with the previous lemma*)

(******CONST LEMMAS *****)

(*FIXME dupe*)
(*code and gc_fun are unchanged across eval*)

(*TODO merge*)

(*FIXME dupe*)

(*TODO use PAIRMAP and deal with breakage*)

(* TODO: generated names *)

(* HOL4 ML code, not ported:
val goal = “
  λ(p:'a wordLang$prog,s:('a,'c,'ffi) wordSem$state).
     ∀r s'.
      evaluate (p, s) = (r, s') ⇒
      s'.clock = s.clock”
val ind_thm = evaluate_ind |> ISPEC goal |> CONV_RULE (DEPTH_CONV
  PAIRED_BETA_CONV);
val ind_goals = ind_thm |> concl |> dest_imp |> fst |>
  helperLib.list_dest dest_conj;
*)

(* HOL4 ML code, not ported:
val clock_goal = “
  λ(p:'a wordLang$prog,s:('a,'c,'ffi) wordSem$state).
    ∀k.
      evaluate (p, s with clock := k) = (λ(r,s). (r,s with clock := k))
        (evaluate (p,s))”
val ind_thm2 = evaluate_ind |> ISPEC clock_goal |> CONV_RULE (DEPTH_CONV
  PAIRED_BETA_CONV);
val ind_goals2 = ind_thm2 |> concl |> dest_imp |> fst |>
  helperLib.list_dest dest_conj;
*)

(******CONST LEMMAS END *****)

(*TODO complete for all get set variaents *)

(* Standard add clock lemma for FBS *)

(* HOL4 ML code, not ported:
val tac =
  EVERY_CASE_TAC>>full_simp_tac(srw_ss())[state_component_equality]
val tac2 =
  strip_tac>>rveq>>full_simp_tac(srw_ss())[]>>
  imp_res_tac evaluate_clock>>full_simp_tac(srw_ss())[]>>
  `¬ (s.clock ≤ r.clock)` by DECIDE_TAC>>full_simp_tac(srw_ss())[]>>
  `s.clock -1 -r.clock = s.clock - r.clock-1` by
    DECIDE_TAC>>full_simp_tac(srw_ss())[]
*)

(* This lemma is interesting in wordLang because of the use of
   MustTerminate

   To remove MustTerminate, we need to inject an exact number of clock
     ticks
   corresponding to the ticks used in the MustTerminate block

   The number of clock ticks is fixed for any program, and can be
     characterized by st.clock - rst.clock *)

(* IO and clock monotonicity *)

(*TODO This format of is really weird can this be changed?*)

(* TODO: monotonicity *)

(* -- *)

(**)

(*--Stack Swap Lemma--*)

(*Stacks look the same to the GC except for the keys (e.g. recoloured
   and in order)*)
let s_frame_val_eq_def = cake_define
  `s_frame_val_eq x1 x2 =
        match (x1,x2) with
          (StackFrame n ls1 ls NONE,StackFrame n' ls1' ls' NONE) ->
        MAP SND ls = MAP SND ls' /\ n = n'
        | ((StackFrame n ls1 ls (SOME y)),(StackFrame n' ls1' ls'
          (SOME y'))) ->
        MAP SND ls = MAP SND ls' /\ y = y' /\ n = n'
        | (_1,_2) -> F`;;

let s_val_eq_def = cake_define
  `s_val_eq x1 x2 =
        match (x1,x2) with
          ([],[]) -> T
        | ((x :: xs),(y :: ys)) -> (s_val_eq xs ys /\
                              s_frame_val_eq x y)
        | (_3,_4) -> F`;;

(*Stacks look the same except for the values of the GC-ed cutsets (e.g.
   result of gc)*)
let s_frame_key_eq_def = cake_define
  `s_frame_key_eq x1 x2 =
        match (x1,x2) with
          (StackFrame n ls0 ls NONE,StackFrame n' ls0' ls' NONE) ->
            MAP FST ls = MAP FST ls' /\ ls0 = ls0' /\ n = n'
        | ((StackFrame n ls0 ls (SOME y)),(StackFrame n' ls0' ls'
          (SOME y'))) -> MAP FST ls = MAP FST ls' /\ y = y' /\ ls0 =
          ls0' /\ n = n'
        | (_5,_6) -> F`;;

let s_key_eq_def = cake_define
  `s_key_eq x1 x2 =
        match (x1,x2) with
          ([],[]) -> T
        | ((x :: xs),(y :: ys)) -> (s_key_eq xs ys /\
                              s_frame_key_eq x y)
        | (_7,_8) -> F`;;

(*Reflexive*)

(*transitive*)


(*Symmetric*)

(*gc preserves the stack_key relation*)

(*gc succeeds on all stacks related by stack_val and there are relations
  in the result*)

(*Slightly more general theorem allows the unused locals to be
   differnt*)

(*Most generalised gc_s_val_eq*)

(*pushing and popping maintain the stack_key relation*)

(* Stack swap theorem for evaluate *)

(*--Stack Swap Lemma DONE--*)

(*--Permute Swap Lemma--*)
(*For any target result permute, we can find an initial permute such
   that the
  final permute is equal to the target *)

(* Locals extend lemma *)
let locals_rel_def = cake_define
  `locals_rel temp (s:('a word_loc) spt) t <=> (!x. x < temp ==>
  lookup x s = lookup x t)`;;

(*Extra temporaries not mentioned in program
  do not affect evaluation
  TODO: theorem statement needs to be changed *)

(* HOL4 ML code, not ported:
Resume locals_rel_evaluate_thm[Move]:
  fs[evaluate_def]>>
  DEP_REWRITE_TAC[locals_rel_get_vars_simp] >> fs[] >>
  gvs[AllCaseEqs()] >> fs[set_vars_def] >>
  irule locals_rel_alist_insert >> fs[]
QED
*)

(* HOL4 ML code, not ported:
Resume locals_rel_evaluate_thm[Inst]:
  fs[evaluate_def] >>
  gvs[inst_def,every_var_def,every_var_inst_def,
  assign_def,AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs []) >>
  TRY (DEP_REWRITE_TAC[locals_rel_word_exp_simp] >>
    fs[every_var_exp_def]) >>
  TRY (rename1 `every_var_imm _ R` >> Cases_on `R` >>
  fs[every_var_imm_def,every_var_exp_def]) >>
  TRY (DEP_REWRITE_TAC[locals_rel_get_vars_simp] >> fs[]) >>
  TRY (DEP_REWRITE_TAC[locals_rel_get_var_simp] >> fs[]) >>
  simp[set_var_def] >>
  rpt (irule locals_rel_set_var >> fs[])
  >-(drule_then assume_tac mem_store_const >> gvs[])
QED
*)

(* HOL4 ML code, not ported:
Resume locals_rel_evaluate_thm[Store]:
  fs[evaluate_def]>>
  DEP_REWRITE_TAC[locals_rel_word_exp_simp] >> fs[] >>
  DEP_REWRITE_TAC[locals_rel_get_var_simp] >> fs[] >>
  gvs[AllCaseEqs()] >> simp[set_var_def] >>
  drule mem_store_const >> fs[]
QED
*)

(* HOL4 ML code, not ported:
Resume locals_rel_evaluate_thm[MustTerminate]:
  fs[evaluate_def] >>
  full_simp_tac(srw_ss())[PULL_FORALL,GSYM AND_IMP_INTRO]>>
  qpat_x_assum`A=(res,rst)` mp_tac>>
  IF_CASES_TAC>>simp[]>>
  pairarg_tac>>simp[]>>
  IF_CASES_TAC>>simp[]>>
  first_x_assum(qspec_then`p` mp_tac)>>
  simp[prog_size_def]>>srw_tac[][]>>full_simp_tac(srw_ss())
    [every_var_def]>>
  res_tac>>full_simp_tac(srw_ss())[]>>
  first_x_assum(qspec_then`loc` mp_tac)>>
  pop_assum kall_tac>>
  simp[]>>strip_tac>>
  simp[]
QED
*)

(* HOL4 ML code, not ported:
Resume locals_rel_evaluate_thm[Call]:
  fs[evaluate_def] >>
  DEP_REWRITE_TAC[locals_rel_get_vars_simp] >> fs[] >>
  TOP_CASE_TAC >- gvs[] >>
  TOP_CASE_TAC >- gvs[] >>
  TOP_CASE_TAC >- gvs[] >>
  PairCases_on `x'` >> fs[] >>
  TOP_CASE_TAC
  >-(
    gvs[AllCaseEqs()]
    >- fs[flush_state_def] >>
    gvs[call_env_def,flush_state_def,dec_clock_def,
      oneline bad_fun_return_def, AllCasePreds()]>>
    simp[state_component_equality]>>
    rename1`res = SOME _`>>
    Cases_on`res`>>gvs[locals_rel_def]>>
    Cases_on`x'`>>gvs[]
  )
  >>
    PairCases_on`x'`>>full_simp_tac(srw_ss())[]>>
    IF_CASES_TAC>>full_simp_tac(srw_ss())[]>>
    qmatch_goalsub_rename_tac`cut_envs (x1, x2)` >>
    Cases_on `cut_envs (x1, x2) st.locals` >>
    imp_res_tac locals_rel_cut_envs>>full_simp_tac(srw_ss())[]>>
    IF_CASES_TAC
     >-(gvs[] >> simp[state_component_equality]) >>
    full_simp_tac(srw_ss())[]>>
    fs[dec_clock_def] >> simp[state_component_equality] >>
    TOP_CASE_TAC >> gvs[locals_rel_def] >> every_case_tac
QED
*)

(* HOL4 ML code, not ported:
Resume locals_rel_evaluate_thm[Seq]:
  fs[evaluate_def] >>
  full_simp_tac(srw_ss())[PULL_FORALL,GSYM AND_IMP_INTRO]>>
  Cases_on`evaluate (p,st)`>>full_simp_tac(srw_ss())[]>>
  first_assum(qspec_then`p` mp_tac)>>
  first_x_assum(qspec_then`p0` mp_tac)>>
  `q ≠ SOME Error` by (every_case_tac >> full_simp_tac(srw_ss())[])>>
  simp[prog_size_def]>>srw_tac[][]>>full_simp_tac(srw_ss())
    [every_var_def]>>res_tac>>
  simp[]>>IF_CASES_TAC>>full_simp_tac(srw_ss())
    [state_component_equality]>>
  Cases_on `q` >> gvs[]
QED
*)

(* HOL4 ML code, not ported:
Resume locals_rel_evaluate_thm[If]:
  gvs[evaluate_def] >>
  DEP_REWRITE_TAC[locals_rel_get_var_simp,
  locals_rel_get_var_imm_simp] >> fs[] >>
  gvs[AllCaseEqs(),prog_size_def]
QED
*)

(* HOL4 ML code, not ported:
Resume locals_rel_evaluate_thm[Loop]:
  simp[every_name_def] >>
  `every_name (\x. x < temp) (s0,LN)` by (simp[every_name_def] >>
    EVAL_TAC) >>
  `cut_env (s0,LN) loc = cut_env (s0,LN) st.locals` by (
    qpat_x_assum `evaluate _ = _` mp_tac >>
    simp[evaluate_def,cut_state_def] >>
    Cases_on `cut_env (s0,LN) st.locals` >> fs[] >>
    strip_tac >>
    imp_res_tac locals_rel_cut_env >> fs[]) >>
  `evaluate (Loop s0 p s, st with locals := loc) =
   evaluate (Loop s0 p s, st)` suffices_by (
    disch_then (fn th => rewrite_tac[th]) >> fs[] >>
    qexists_tac `rst.locals` >>
    fs[state_component_equality] >>
    every_case_tac >> simp[locals_rel_def]) >>
  simp[Once evaluate_def, cut_state_def] >>
  qpat_x_assum `evaluate (Loop _ _ _, st) = _` mp_tac >>
  simp[Once evaluate_def, cut_state_def] >>
  Cases_on `cut_env (s0,LN) st.locals` >> simp[]
QED
*)

(* HOL4 ML code, not ported:
Resume locals_rel_evaluate_thm[Alloc]:
  gvs[evaluate_def] >>
  DEP_REWRITE_TAC[locals_rel_get_var_simp] >> fs[] >>
  gvs[AllCaseEqs()] >>
  fs[alloc_def] >> qpat_x_assum`A=(res,rst)` mp_tac>>
  ntac 6 (full_case_tac>>full_simp_tac(srw_ss())[])>>srw_tac[][]>>
  imp_res_tac  locals_rel_cut_envs>> fs[] >> gvs[] >>
  simp[state_component_equality] >>
  simp[locals_rel_def]
QED
*)

(* HOL4 ML code, not ported:
Resume locals_rel_evaluate_thm[StoreConsts]:
  gvs[evaluate_def] >>
  DEP_REWRITE_TAC[locals_rel_get_var_simp] >> fs[] >>
  gvs[AllCaseEqs()] >> simp[set_var_def,unset_var_def] >>
  irule locals_rel_set_var >> fs[] >>
  irule locals_rel_set_var >> fs[] >>
  irule locals_rel_delete >> fs[] >>
  irule locals_rel_delete >> fs[]
QED
*)

(* HOL4 ML code, not ported:
Resume locals_rel_evaluate_thm[Raise]:
  gvs[evaluate_def] >>
  DEP_REWRITE_TAC[locals_rel_get_var_simp] >> fs[] >>
  gvs[AllCaseEqs()] >>
  fs[jump_exc_def] >>
  simp[state_component_equality]
QED
*)

(* HOL4 ML code, not ported:
Resume locals_rel_evaluate_thm[OpCurrHeap]:
  gvs[evaluate_def] >>
  DEP_REWRITE_TAC[locals_rel_word_exp_simp] >> fs[every_var_exp_def] >>
  gvs[AllCaseEqs()] >> fs[set_var_def] >>
  irule locals_rel_set_var >> fs[]
QED
*)

(* HOL4 ML code, not ported:
Resume locals_rel_evaluate_thm[Install]:
  gvs[evaluate_def] >>
  DEP_REWRITE_TAC[locals_rel_get_var_simp] >> fs[] >>
  gvs[AllCaseEqs()] >>
  imp_res_tac locals_rel_cut_env>> fs[] >>
  pairarg_tac >> fs[] >>
  gvs[AllCaseEqs()] >>
  irule locals_rel_set_var >> fs[locals_rel_def]
QED
*)

(* HOL4 ML code, not ported:
Resume locals_rel_evaluate_thm[FFI]:
  gvs[evaluate_def] >>
  DEP_REWRITE_TAC[locals_rel_get_var_simp] >> fs[] >>
  gvs[AllCaseEqs()] >>
  imp_res_tac locals_rel_cut_env>>
  simp[locals_rel_def,state_component_equality]
QED
*)

(* HOL4 ML code, not ported:
Resume locals_rel_evaluate_thm[ShareInst]:
  gvs[evaluate_def,oneline share_inst_def] >>
  DEP_REWRITE_TAC[locals_rel_word_exp_simp] >> fs[] >>
  DEP_REWRITE_TAC[locals_rel_get_var_simp] >> fs[] >>
  gvs[AllCaseEqs()]
  >>~- ([`sh_mem_set_var`],
    fs[oneline sh_mem_set_var_def] >>
    gvs[AllCaseEqs()] >> fs[set_var_def]
    >-(irule locals_rel_set_var >> fs[]) >>
   simp[state_component_equality]) >>
  fs[sh_mem_store_def,sh_mem_store_byte_def,sh_mem_store32_def,
     sh_mem_store16_def] >>
  gvs[AllCaseEqs()] >> simp[state_component_equality]
QED
*)

(* HOL4 ML code, not ported:
Resume locals_rel_evaluate_thm[Break]:
  fs[evaluate_def] >> gvs[]
QED
*)

(* HOL4 ML code, not ported:
Resume locals_rel_evaluate_thm[Continue]:
  fs[evaluate_def] >> gvs[]
QED
*)

(* HOL4 ML code, not ported:
Resume locals_rel_evaluate_thm[Get]:
  gvs[evaluate_def] >>
  gvs[AllCaseEqs()] >> simp[set_var_def] >>
  irule locals_rel_set_var >> fs[]
QED
*)

(* HOL4 ML code, not ported:
Resume locals_rel_evaluate_thm[Set]:
  gvs[evaluate_def] >>
  DEP_REWRITE_TAC[locals_rel_word_exp_simp] >> fs[] >>
  gvs[AllCaseEqs(),state_component_equality]
QED
*)

(* HOL4 ML code, not ported:
Resume locals_rel_evaluate_thm[Tick]:
  gvs[evaluate_def,AllCaseEqs(),dec_clock_def] >>
  simp[state_component_equality,flush_state_def]
QED
*)

(* HOL4 ML code, not ported:
Resume locals_rel_evaluate_thm[Assign]:
  gvs[evaluate_def] >>
  DEP_REWRITE_TAC[locals_rel_word_exp_simp] >> fs[] >>
  gvs[AllCaseEqs()] >> simp[set_var_def] >>
  irule locals_rel_set_var >> fs[]
QED
*)

(* HOL4 ML code, not ported:
Resume locals_rel_evaluate_thm[Return]:
  gvs[evaluate_def] >>
  DEP_REWRITE_TAC[locals_rel_get_var_simp,locals_rel_get_vars_simp] >>
    fs[] >>
  gvs[AllCaseEqs(),flush_state_def,state_component_equality]
QED
*)

(* HOL4 ML code, not ported:
Resume locals_rel_evaluate_thm[LocValue]:
  gvs[evaluate_def,AllCaseEqs()] >> simp[set_var_def] >>
  irule locals_rel_set_var >> fs[]
QED
*)

(* HOL4 ML code, not ported:
Resume locals_rel_evaluate_thm[Skip]:
  gvs[evaluate_def]
QED
*)

(* HOL4 ML code, not ported:
Resume locals_rel_evaluate_thm[CodeBufferWrite]:
  gvs[evaluate_def] >>
  DEP_REWRITE_TAC[locals_rel_get_var_simp] >> fs[] >>
  gvs[AllCaseEqs(),state_component_equality]
QED
*)

(* HOL4 ML code, not ported:
Resume locals_rel_evaluate_thm[DataBufferWrite]:
  gvs[evaluate_def] >>
  DEP_REWRITE_TAC[locals_rel_get_var_simp] >> fs[] >>
  gvs[AllCaseEqs(),state_component_equality]
QED
*)

(* HOL4 ML code, not ported:
Finalise locals_rel_evaluate_thm;
*)

let gc_fun_ok_def = cake_define
  `gc_fun_ok (f:('a word_loc) list#('a word->'a word_loc)#('a
  word->bool)#(store_name,'a word_loc)fmap->(('a word_loc) list#('a
  word->'a word_loc)#(store_name,'a word_loc)fmap) option) =
     (!wl m d s wl1 m1 s1.
       Handler IN FDOM s /\
       (f (wl,m,d,s \\ Handler) = SOME (wl1,m1,s1)) ==>
       (LENGTH wl = LENGTH wl1) /\
       ~(Handler IN FDOM s1) /\
       (f (wl,m,d,s) = SOME (wl1,m1,s1 |+ (Handler,FAPPLY s
         Handler))))`;;

(*I'm pretty sure this is defined somewhere else too
MOVE THIS to backend props.*)

let inc_clock_def = cake_define
  `wordProps_inc_clock n (t:('a,'c,'ffi)wordSem_state) = ?_clock_fupd
  (K (?_clock t + n)) t`;;
hol4_overload "inc_clock" "wordProps_inc_clock";;

let no_alloc_code_def = cake_define
  `no_alloc_code (code:(num#'a wordLang_prog) spt) <=>
   (!k n p. lookup k code = SOME (n,p) ==> no_alloc p)`;;

let no_install_code_def = cake_define
  `no_install_code (code:(num#'a wordLang_prog) spt) <=>
       (!k n p. lookup k code = SOME (n,p) ==> no_install p)`;;

let no_mt_code_def = cake_define
  `no_mt_code (code:(num#'a wordLang_prog) spt) <=>
   (!k n p. lookup k code = SOME (n,p) ==> no_mt p)`;;


(*** permute_swap for no_install & no_alloc ***)

(* HOL4 overload (expanded in the port):
     PERM_STACK = λs1 s2. case (s1,s2) of
                                 (StackFrame ss l env h,StackFrame ss'
                                   l' env' h') =>
                                   ss = ss' ∧ h = h' ∧ l = l'∧  PERM env
                                     env' ∧ ALL_DISTINCT (MAP FST env)
                                     *)

(* HOL4 ML code, not ported:
Resume permute_swap_lemma2[Loop]:
  fs[evaluate_def] >>
  Cases_on `cut_state (names,LN) st` >> fs[] >>
  `cut_state (names,LN) (st with <|permute := perm; stack := stack|>) =
   SOME (x with <|permute := perm; stack := stack|>)` by
    (fs[cut_state_def] >> every_case_tac >> gvs[]) >>
  Cases_on `evaluate(prog,x)` >> fs[STOP_def] >>
  first_x_assum(qspecl_then [`perm`,`stack`] mp_tac) >>
  impl_tac >- (conj_tac >- (strip_tac >> gvs[]) >>
               fs[cut_state_def] >> every_case_tac >> gvs[]) >>
  strip_tac >>
  qpat_x_assum `LIST_REL _ _ r.stack` mp_tac >>
  gvs[AllCaseEqs(),flush_state_def,dec_clock_def,cut_state_def] >>
  strip_tac >>
  simp[state_component_equality] >>
  TRY (first_x_assum(irule_at $ Pos last) >> simp[]) >>
  last_x_assum(qspecl_then [`perm'`,`stack'`] mp_tac) >>
  impl_tac >- (fs[] >> imp_res_tac no_install_evaluate_const_code >>
               gvs[no_alloc_def,no_install_def]) >>
  strip_tac >> gvs[dec_clock_def] >> simp[state_component_equality]
QED
*)

(* HOL4 ML code, not ported:
Finalise permute_swap_lemma2;
*)
