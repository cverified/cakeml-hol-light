(* ======================================================== *)
(*  clos_interpProof: ported from HOL4's
    compiler/backend/proofs/clos_interpProofScript.sml  *)
(* ======================================================== *)

(*
  Correctness proof for closLang interpreter used by the REPL, i.e.
    Install,
  to avoid spending time compiling simple run-once code in declarations.
*)

needs "compiler/backend/closLang.ml";;
needs "compiler/backend/clos_interp.ml";;
needs "compiler/backend/pattern_matching/pattern_semantics.ml";;
needs "compiler/backend/semantics/backendProps.ml";;
needs "compiler/backend/semantics/closProps.ml";;
needs "compiler/backend/semantics/closSem.ml";;
needs "semantics/ast.ml";;
needs "semantics/semanticPrimitives.ml";;

(* ---------------------------------------------------------------------
   ---- *
   correctness of interpreter
 * ---------------------------------------------------------------------
   ---- *)

let state_rel_def = cake_define
  `clos_interpProof_state_rel (s:('c,'ffi)closSem_state)
  (t:('c,'ffi)closSem_state) <=>
     (!n. SND (SND (closSem_state_compile_oracle s n)) = []) /\
       closSem_state_code
     s = FEMPTY /\ closSem_state_code t = FEMPTY /\
       closSem_state_max_app
     t = closSem_state_max_app s /\ 1 <= closSem_state_max_app s /\
       ?_clock
     t = ?_clock s /\ ?_ffi
     t = ?_ffi s /\ closSem_state_globals
     s = closSem_state_globals t /\ ?_refs
     s = ?_refs t /\ closSem_state_compile
     s = pure_cc (insert_interp ## I) (closSem_state_compile t) /\
       closSem_state_compile_oracle
     t = pure_co (insert_interp ## I) o closSem_state_compile_oracle
       s /\
     oHD (closSem_state_globals s) = SOME (SOME (Closure NONE []
       [] 1 clos_interpreter))`;;

let state_rel_1_def = cake_define
  `state_rel_1 (s:('c,'ffi)closSem_state) (t:('c,'ffi)closSem_state) <=>
     (!n. SND (SND (closSem_state_compile_oracle s n)) = []) /\
       closSem_state_code
     s = FEMPTY /\ closSem_state_code t = FEMPTY /\
       closSem_state_max_app
     t = closSem_state_max_app s /\ 1 <= closSem_state_max_app s /\
       ?_clock
     t = ?_clock s /\ ?_ffi
     t = ?_ffi s /\ closSem_state_globals
     s = closSem_state_globals t /\ ?_refs
     s = ?_refs t /\ closSem_state_compile
     s = pure_cc (insert_interp ## I) (closSem_state_compile t) /\
       closSem_state_compile_oracle
     t = pure_co (insert_interp ## I) o
       closSem_state_compile_oracle s`;;

let interp_assum_def = cake_define
  `interp_assum (:'c) (:'ffi) c <=>
     (!xs s1 env (t1:('c,'ffi)closSem_state) res s2. ?_clock
       s1 <= c /\
       closSem_evaluate (xs,env,s1) = (res,s2) /\ ~(
       res = Rerr (Rabort Rtype_error)) ==>
       clos_interpProof_state_rel s1 t1 ==>
       (?ck t2.
         closSem_evaluate (xs,env,?_clock_fupd (K (ck + ?_clock t1))
           t1) = (res,t2) /\
         clos_interpProof_state_rel s2 t2)) /\
     (!args s1 loc f (t1:('c,'ffi)closSem_state) res s2. ?_clock
       s1 <= c /\
       evaluate_app loc f args s1 = (res,s2) /\ ~(
       res = Rerr (Rabort Rtype_error)) ==>
       clos_interpProof_state_rel s1 t1 ==>
       (?ck t2.
         evaluate_app loc f args (?_clock_fupd (K (ck + ?_clock t1))
           t1) =
         (res,t2) /\ clos_interpProof_state_rel s2 t2))`;;

(* HOL4 ML code, not ported:
val evaluate_If =
  SIMP_CONV std_ss [evaluate_def] “evaluate ([If t x1 x2 x3],env,s)”;
*)

(* HOL4 ML code, not ported:
val evaluate_Var =
  SIMP_CONV std_ss [evaluate_def] “evaluate ([Var t n],env,s)”;
*)

(* HOL4 ML code, not ported:
val evaluate_TagLenEq =
  SIMP_CONV (srw_ss()) [evaluate_def,do_app_def]
    “evaluate ([Op None (BlockOp (TagLenEq t l)) [V 0]],Block t1 xs ::
      env,s)”;
*)

(* HOL4 ML code, not ported:
val init0_tac =
  simp [to_constant_def,make_const_def,Boolv_def,
        evaluate_Var,evaluate_If,evaluate_TagLenEq,
        backend_commonTheory.true_tag_def,
        backend_commonTheory.false_tag_def,clos_interpreter_body_def];
*)

(* HOL4 ML code, not ported:
val init_tac =
  init0_tac
  \\ qpat_x_assum ‘evaluate ([_],env,s4) = (r,s5)’ mp_tac
  \\ simp [Once evaluate_def,CaseEq"prod"] \\ rw [PULL_EXISTS];
*)

(* ---------------------------------------------------------------------
   ---- *
   not has_install ignores compiler oracle
 * ---------------------------------------------------------------------
   ---- *)

let v_ok_def = cake_define_list
  [`v_ok (closSem_Number i) <=> T`;
   `v_ok (Word64 w:closSem_v) <=> T`;
   `v_ok (closSem_Block n vs) <=> EVERY v_ok vs`;
   `v_ok (closSem_ByteVector ws) <=> T`;
   `v_ok (closSem_RefPtr b n) <=> T`;
   `v_ok (Closure loco vs1 env1 n bod1:closSem_v) <=>
        ~has_install bod1 /\ EVERY v_ok env1 /\ EVERY v_ok vs1`;
   `v_ok (Recclosure loco vs1 env1 fns1 i:closSem_v) <=>
        EVERY v_ok env1 /\ EVERY v_ok vs1 /\ i < LENGTH fns1 /\
        EVERY ((~) o has_install o SND) fns1`];;

let res_ok_def = cake_define
  `res_ok x1 =
      match x1 with
        Rerr (Rabort _1) -> T
      | (Rerr (Rraise v)) -> v_ok v
      | (Rval v) -> EVERY v_ok v`;;

let state_rel'_def = cake_define
  `state_rel' (s:('c,'ffi)closSem_state) (t:('c,'ffi)closSem_state) <=>
     (!n. SND (SND (closSem_state_compile_oracle s n)) = []) /\
       closSem_state_code
     s = FEMPTY /\ closSem_state_code t = FEMPTY /\
       closSem_state_max_app
     t = closSem_state_max_app s /\ 1 <= closSem_state_max_app s /\
       ?_clock
     t = ?_clock s /\ ?_ffi
     t = ?_ffi s /\ closSem_state_globals
     s = closSem_state_globals t /\ EVERY (OPTION_ALL v_ok)
       (closSem_state_globals t) /\ ?_refs
     s = ?_refs t /\
     FEVERY (\(k,v). !vs. v = closSem_ValueArray vs ==> EVERY v_ok
       vs) (?_refs t) /\
     FEVERY (\(k,v). !m w. v = Thunk m w ==> v_ok w) (?_refs t) /\
       closSem_state_compile
     s = pure_cc (insert_interp ## I) (closSem_state_compile t) /\
       closSem_state_compile_oracle
     t = pure_co (insert_interp ## I) o
       closSem_state_compile_oracle s`;;

(* ---------------------------------------------------------------------
   ---- *
   preservation of observable semantics
 * ---------------------------------------------------------------------
   ---- *)

(* ---------------------------------------------------------------------
   ---- *
   syntactic lemmas
 * ---------------------------------------------------------------------
   ---- *)
