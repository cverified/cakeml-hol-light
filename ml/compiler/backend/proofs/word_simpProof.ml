(* ======================================================== *)
(*  word_simpProof: ported from HOL4's
    compiler/backend/proofs/word_simpProofScript.sml  *)
(* ======================================================== *)

(*
  Correctness proof for word_simp
*)

needs "basis/pure/mllist.ml";;
needs "compiler/backend/pattern_matching/pattern_semantics.ml";;
needs "compiler/backend/semantics/dataSem.ml";;
needs "compiler/backend/semantics/wordProps.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/backend/stackLang.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/backend/word_simp.ml";;
(* HOL4 ancestors outside the port: alist *)

(* HOL4 ML code, not ported:
val s = ``s:('a,'c,'ffi) wordSem$state``
*)

(** verification of Seq_assoc **)

(** verification of const_fp **)

(* gc *)

let is_gc_word_const_def = cake_define_list
  [`is_gc_word_const (wordLang_Loc _1 _2) = T`;
   `is_gc_word_const (wordLang_Word w) = is_gc_const w`];;

let gc_fun_const_ok_def = cake_define
  `gc_fun_const_ok (f:('a word_loc) list#('a word->'a word_loc)#('a
  word->bool)#(store_name,'a word_loc)fmap->(('a word_loc) list#('a
  word->'a word_loc)#(store_name,'a word_loc)fmap) option) =
     (!x y. f x = SOME y ==> EVERY2 (\a b. is_gc_word_const a ==>
       b = a) (FST x) (FST y))`;;


let sf_gc_consts_def = cake_define
  `sf_gc_consts (StackFrame _3 l0 sv h) (StackFrame _4 l0' sw h') =
   (EVERY2 (\(ak,av) (bk,bv). (ak = bk) /\ (is_gc_word_const av
     ==> bv = av)) sv sw /\ l0 = l0' /\ h = h')`;;

(*
Definition sf_gc_consts_def:
  sf_gc_consts (StackFrame lsz sv h) (StackFrame lsz' sw h') =
  (EVERY2 (\(ak, av) (bk, bv). (ak = bk) /\ (is_gc_word_const av ==> bv
    = av)) sv sw /\
   lsz = lsz' /\ h = h')
End
*)

(* Assign *)

(* Move *)

(* TODO: In need of cleanup *)

(* If *)

(* Helpful lemmas about locals *)
(*TODO move*)

(* Lookup thms *)

(* LIST_REL/EVERY2 thms *)

(* Stack thms *)

(*TODO delete*)

(*Theorem call_env_push_env_dec_clock:
   !s s'. s' = (call_env x0 (push_env x1 x2 (dec_clock s))) ==>
     s'.gc_fun = s.gc_fun
Proof
  rw [dec_clock_def, call_env_def] \\ metis_tac [push_env_gc_fun]
QED*)

let get_above_handler_def = cake_define
  `get_above_handler s = (match EL (LENGTH (?_stack s) -
  (wordSem_state_handler s + 1)) (?_stack s) with StackFrame _5 _6 _7
  (SOME (h,_8,_9)) -> h)`;;

(*TODO move*)

(* HOL4 ML code, not ported:
Resume evaluate_sf_gc_consts[Call]:
  rpt gen_tac \\ rpt DISCH_TAC \\ rpt gen_tac \\ DISCH_TAC \\ fs
    [evaluate_def]
  \\ qpat_x_assum `_ = (res,s')` mp_tac
  \\ ntac 3 (TOP_CASE_TAC >- (rw [] \\ rw []))
  \\ PairCases_on `x'` \\ fs [] \\
  TOP_CASE_TAC
    >- (every_case_tac \\ rw [] \\ gvs [call_env_def, flush_state_def,
      dec_clock_def, get_above_handler_def, bad_fun_return_def]) \\
  PairCases_on `x'` \\ fs [] \\
  ntac 3 (TOP_CASE_TAC >- (rw [] \\ rw [])) \\
  TOP_CASE_TAC \\
  TOP_CASE_TAC >- (rw [] \\ rw []) \\
  TOP_CASE_TAC
    >~ [`Result`] >- (
      ntac 2 (TOP_CASE_TAC >- (rw [] \\ rw []))
      \\ reverse TOP_CASE_TAC >- (rw [] \\ rw [])
      \\ fs [call_env_def, flush_state_def, dec_clock_def, set_var_def]
      \\ rfs []
      \\ imp_res_tac evaluate_gc_fun_const_ok
      \\ rfs []
      \\ imp_res_tac pop_env_gc_fun_const_ok
      \\ imp_res_tac LIST_REL_call_Result
      \\ strip_tac
      \\ TOP_CASE_TAC \\ fs [] \\ res_tac \\ fs []
      >- (irule EVERY2_trans \\ rpt conj_tac
         >- ACCEPT_TAC sf_gc_consts_trans
         >- (asm_exists_tac \\ rw []))
      \\ TOP_CASE_TAC \\ fs []
      >- (irule EVERY2_trans \\ rpt conj_tac
         >- ACCEPT_TAC sf_gc_consts_trans
         >- (asm_exists_tac \\ rw []))
      >- (DISCH_TAC
         \\ `s.handler < LENGTH x''.stack` by (imp_res_tac
           LIST_REL_LENGTH \\ fs [])
         \\ `get_above_handler (set_vars $var$(x'0') l x'') =
           get_above_handler s` by
            (irule sf_gc_consts_get_above_handler \\ fs [set_vars_def])
         \\ res_tac \\ fs [set_vars_def]
         \\ irule EVERY2_trans_LASTN_sf_gc_consts
         \\ conj_tac >- rw [] \\ asm_exists_tac \\ rw [])
      \\ ntac 2 (irule EVERY2_trans \\ rpt conj_tac
      >- ACCEPT_TAC sf_gc_consts_trans
      >- (asm_exists_tac \\ rw [])))
    >~ [`set_var`] >- (
  TOP_CASE_TAC
  >- (* NONE, no handler *)
  (rw [] \\ fs [call_env_def, flush_state_def, push_env_def,
    dec_clock_def] \\ pairarg_tac \\ fs []
  \\ DISCH_TAC \\ res_tac \\ `s.handler < SUC (LENGTH s.stack)` by
    DECIDE_TAC \\ fs [] \\ conj_tac
    >- fs [LASTN_CONS]
    >- (rw [get_above_handler_def, ADD1]
       \\ `(LENGTH s.stack - s.handler) = SUC (LENGTH s.stack -
         (s.handler + 1))` by (fs[]) \\ fs []))
  >- (* SOME, has handler *)
  (PairCases_on `x''` \\ fs []
  \\ TOP_CASE_TAC >- (rw [] \\ rw [])
  \\ reverse (TOP_CASE_TAC) >- (rw [] \\ rw [])
  \\ imp_res_tac evaluate_gc_fun_const_ok
  \\ fs [call_env_def, flush_state_def, push_env_def, dec_clock_def,
    set_var_def]
  \\ pairarg_tac \\ fs [] \\ res_tac \\ fs []
  \\ fs [LASTN_LENGTH_CONS]
  \\ DISCH_TAC \\ TOP_CASE_TAC \\ TRY (TOP_CASE_TAC)
  >- ((* NONE *)
      res_tac \\ fs [] \\ rw []
      >- (irule EVERY2_trans
          \\ conj_tac >- ACCEPT_TAC sf_gc_consts_trans
          >- (asm_exists_tac \\ rw []))
      >- (rw [get_above_handler_def] \\ rw [ADD1]))
  >- ((* Result *)
      res_tac \\ fs [] \\ rw []
      >- (irule EVERY2_trans
          \\ conj_tac >- ACCEPT_TAC sf_gc_consts_trans
          >- (asm_exists_tac \\ rw []))
      >- (rw [get_above_handler_def] \\ rw [ADD1]))
  >- ((* Exception *)
      DISCH_TAC \\ res_tac \\ fs [get_above_handler_def, ADD1]
      \\ `r.handler < LENGTH r.stack` by (metis_tac [LIST_REL_LENGTH])
      \\ fs [] \\ conj_tac
      >- (irule EVERY2_trans_LASTN_sf_gc_consts \\ conj_tac >- rw [] \\
        asm_exists_tac \\ rw [])
      >- metis_tac [sf_gc_consts_get_above_handler,
        get_above_handler_def])
  >- ((* Break *)
      res_tac \\ fs [] \\ rw []
      >- (irule EVERY2_trans
          \\ conj_tac >- ACCEPT_TAC sf_gc_consts_trans
          >- (asm_exists_tac \\ rw []))
      >- (rw [get_above_handler_def] \\ rw [ADD1]))
  >- ((* Continue *)
      res_tac \\ fs [] \\ rw []
      >- (irule EVERY2_trans
          \\ conj_tac >- ACCEPT_TAC sf_gc_consts_trans
          >- (asm_exists_tac \\ rw []))
      >- (rw [get_above_handler_def] \\ rw [ADD1])))
)
    \\ (* Other cases: NONE/Break/Continue errors + catch-all *)
    (rw [] \\ rw [])
QED
*)

(* HOL4 ML code, not ported:
Resume evaluate_sf_gc_consts[Loop]:
  rpt gen_tac \\ rpt DISCH_TAC \\ rpt gen_tac
  \\ fs [evaluate_def] \\ TOP_CASE_TAC \\ fs []
  \\ strip_tac \\ gvs []
  \\ pairarg_tac \\ fs []
  \\ qpat_x_assum `cut_state _ _ = _` mp_tac
  \\ simp [cut_state_def, AllCaseEqs()] \\ strip_tac \\ gvs []
  \\ imp_res_tac evaluate_gc_fun_const_ok \\ fs []
  \\ Cases_on `res'` \\ fs [cont_loop_def]
  >- (* NONE cont_loop *)
   (Cases_on `s1.clock = 0` \\ gvs [flush_state_def]
    \\ qpat_x_assum `case _ of NONE => _ | SOME _ => _` mp_tac
    \\ Cases_on `res` \\ fs [] \\ strip_tac
    >- (irule EVERY2_trans \\ conj_tac >- metis_tac [sf_gc_consts_trans]
      \\ qexists_tac `s1.stack` \\ fs [])
    \\ Cases_on `x` \\ fs []
    >~ [`Exception`]
    >- (strip_tac \\ `s.handler < LENGTH s1.stack` by (imp_res_tac
      LIST_REL_LENGTH \\ fs []) \\ fs []
        \\ conj_tac >- (match_mp_tac (SRULE []
          EVERY2_trans_LASTN_sf_gc_consts) \\ qexists_tac `s1.stack` \\
          fs [])
        \\ irule sf_gc_consts_get_above_handler \\ fs [dec_clock_def])
    \\ (* Result / Break / Continue *)
       (irule EVERY2_trans \\ conj_tac >- metis_tac [sf_gc_consts_trans]
         \\ qexists_tac `s1.stack` \\ fs []))
  \\ Cases_on `x` \\ fs [cont_loop_def, exit_loop_def] \\ gvs []
  >~ [`Exception`] >- gvs [get_above_handler_def]
  >~ [`Break`]
  >- (Cases_on `n = 0` \\ gvs [cut_state_def, AllCaseEqs()] \\ rw [])
  >~ [`Continue`]
  >- (Cases_on `n = 0` \\ gvs [flush_state_def]
      \\ Cases_on `s1.clock = 0` \\ gvs [flush_state_def]
      \\ qpat_x_assum `case _ of NONE => _ | SOME _ => _` mp_tac
      \\ Cases_on `res` \\ fs [] \\ strip_tac
      >- (irule EVERY2_trans \\ conj_tac >- metis_tac
        [sf_gc_consts_trans] \\ qexists_tac `s1.stack` \\ fs [])
      \\ Cases_on `x` \\ fs []
      >~ [`Exception`]
      >- (strip_tac \\ `s.handler < LENGTH s1.stack` by (imp_res_tac
        LIST_REL_LENGTH \\ fs []) \\ fs []
          \\ conj_tac >- (match_mp_tac (SRULE []
            EVERY2_trans_LASTN_sf_gc_consts) \\ qexists_tac `s1.stack`
            \\ fs [])
          \\ irule sf_gc_consts_get_above_handler \\ fs [dec_clock_def])
      \\ (* Result / Break / Continue *)
         (irule EVERY2_trans \\ conj_tac >- metis_tac
           [sf_gc_consts_trans] \\ qexists_tac `s1.stack` \\ fs []))
QED
*)

(* HOL4 ML code, not ported:
Finalise evaluate_sf_gc_consts;
*)

(* HOL4 ML code, not ported:
Resume evaluate_const_fp_loop[Loop]:
  rw [const_fp_loop_def] \\ rpt (pairarg_tac \\ fs []) \\ gvs []
  \\ Cases_on `const_fp_loop p LN` \\ gvs []
  \\ `evaluate (Loop names q exit_names, s) = evaluate (Loop names p
    exit_names, s)` suffices_by fs []
  \\ irule evaluate_Loop_body_cong_gc
  \\ qexists_tac `gc_fun_const_ok` \\ rw []
  \\ Cases_on `evaluate (p, v)` \\ res_tac
QED
*)

(* HOL4 ML code, not ported:
Finalise evaluate_const_fp_loop;
*)

(* the duplicate-if pass *)

(* HOL4 ML code, not ported:
fun uncurry_case_rand x = x
                         |> TypeBase.case_rand_of
                         |> ISPEC ``(UNCURRY (A:'uniquea -> 'uniqueb ->
                           'uniquec))``
                         |> GEN ``(A:'uniquea -> 'uniqueb ->
                           'uniquec)``;
*)

(* putting it all together *)
