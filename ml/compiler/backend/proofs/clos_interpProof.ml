(* ======================================================== *)
(*  clos_interpProof: ported from HOL4's
    compiler/backend/proofs/clos_interpProofScript.sml
    A proof theory about clos_interp.ml, with 6 definitions and 35
    theorems.  Needed by flat_to_closProof.ml.  *)
(* ======================================================== *)

(*
  Correctness proof for closLang interpreter used by the REPL, i.e. Install,
  to avoid spending time compiling simple run-once code in declarations.
*)

needs "basis/pure/mlstring.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/clos_interp.ml";;
needs "compiler/backend/clos_to_bvl.ml";;
needs "compiler/backend/semantics/backendProps.ml";;
needs "compiler/backend/semantics/closProps.ml";;
needs "compiler/backend/semantics/closSem.ml";;
needs "misc/misc.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/semanticPrimitives.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "clos_interpProof"
  ["backendProps"; "closLang"; "closProps"; "closSem"; "clos_interp"];;

(* ------------------------------------------------------------------------- *
   correctness of interpreter
 * ------------------------------------------------------------------------- *)

let clos_interpProof_state_rel_def = new_definition
  `clos_interpProof_state_rel (s:('c,'ffi)closSem_state)
  (t:('c,'ffi)closSem_state) <=>
     (!n. SND (SND (closSem_state_compile_oracle s n)) = []) /\
       closSem_state_code
     s = FEMPTY /\ closSem_state_code t = FEMPTY /\
       closSem_state_max_app
     t = closSem_state_max_app s /\ 1 <= closSem_state_max_app s /\
       closSem_state_clock
     t = closSem_state_clock s /\ closSem_state_ffi
     t = closSem_state_ffi s /\ closSem_state_globals
     s = closSem_state_globals t /\ closSem_state_refs
     s = closSem_state_refs t /\ closSem_state_compile
     s = pure_cc (insert_interp ## I) (closSem_state_compile t) /\
       closSem_state_compile_oracle
     t = pure_co (insert_interp ## I) o closSem_state_compile_oracle
       s /\
     oHD (closSem_state_globals s) = SOME (SOME (closSem_Closure
       NONE [] [] 1 clos_interpreter))`;;

let state_rel_1_def = new_definition
  `state_rel_1 (s:('c,'ffi)closSem_state) (t:('c,'ffi)closSem_state) <=>
     (!n. SND (SND (closSem_state_compile_oracle s n)) = []) /\
       closSem_state_code
     s = FEMPTY /\ closSem_state_code t = FEMPTY /\
       closSem_state_max_app
     t = closSem_state_max_app s /\ 1 <= closSem_state_max_app s /\
       closSem_state_clock
     t = closSem_state_clock s /\ closSem_state_ffi
     t = closSem_state_ffi s /\ closSem_state_globals
     s = closSem_state_globals t /\ closSem_state_refs
     s = closSem_state_refs t /\ closSem_state_compile
     s = pure_cc (insert_interp ## I) (closSem_state_compile t) /\
       closSem_state_compile_oracle
     t = pure_co (insert_interp ## I) o
       closSem_state_compile_oracle s`;;

(* [local] *)
let LIST_REL_eq' = prove
 (`!xs ys. ALL2 (\v1 v2. v1 = v2) = (\xs ys. xs = ys)`,
  CHEAT_TAC);;

(* [local] *)
let OPTREL_eq' = prove
 (`(OPTREL (\v1 v2. v1 = v2)) = (\x y. x = y)`,
  CHEAT_TAC);;

let do_app_oHD_globals = prove
 (`closSem_do_app p vs s1 = Rval (v,s2) ==>
   oHD (closSem_state_globals s1) = SOME (SOME x) ==>
   oHD (closSem_state_globals s2) = SOME (SOME x)`,
  CHEAT_TAC);;

let interp_assum_def = new_definition
  `interp_assum (:'c) (:'ffi) c <=>
     (!xs s1 env (t1:('c,'ffi)closSem_state) res s2. state_clock
       s1 <= c /\
       closSem_evaluate (xs,env,s1) = (res,s2) /\ ~(res = Rerr
         (Rabort Rtype_error)) ==>
       clos_interpProof_state_rel s1 t1 ==>
       (?ck t2.
         closSem_evaluate (xs,env,closSem_state_clock_fupd (K (ck +
           closSem_state_clock t1)) t1) = (res,t2) /\
         clos_interpProof_state_rel s2 t2)) /\
     (!args s1 loc f (t1:('c,'ffi)closSem_state) res s2. state_clock
       s1 <= c /\
       evaluate_app loc f args s1 = (res,s2) /\ ~(res = Rerr (Rabort
         Rtype_error)) ==>
       clos_interpProof_state_rel s1 t1 ==>
       (?ck t2.
         evaluate_app loc f args (closSem_state_clock_fupd (K (ck +
           closSem_state_clock t1)) t1) =
         (res,t2) /\ clos_interpProof_state_rel s2 t2))`;;

let interp_assum_leq = prove
 (`interp_assum (:'c) (:'ffi) c /\ d <= c ==> interp_assum (:'c)
  (:'ffi) d`,
  CHEAT_TAC);;

(* [local] *)
let evaluate_Constant = prove
 (`closSem_evaluate ([(closLang_Op t (closLang_BlockOp
  (closLang_Constant c)) []:closLang_exp)],env,s) = (Rval [make_const
  c],s)`,
  CHEAT_TAC);;
add_simp evaluate_Constant;;

let evaluate_Cons_nil = prove
 (`closSem_evaluate ([(closLang_Op t (closLang_BlockOp (closLang_Cons
  n)) []:closLang_exp)],env,s) = (Rval [closSem_Block n []],s)`,
  CHEAT_TAC);;

let evaluate_Global_0 = prove
 (`clos_interpProof_state_rel s t ==>
   closSem_evaluate ([closLang_Op tr (closLang_GlobOp
     (closLang_Global 0)) []],env,state_clock_fupd (K k) t) =
     (Rval [closSem_Closure NONE [] [] 1
       clos_interpreter],state_clock_fupd (K k) t)`,
  CHEAT_TAC);;

let v_to_list_list_to_v = prove
 (`!a. closSem_v_to_list (closSem_list_to_v a) = SOME a`,
  CHEAT_TAC);;

let clos_interp_el_thm = prove
 (`!n env rest cl_env.
     n < LENGTH env /\ 1 <= closSem_state_max_app t4 ==>
     (?c. closSem_evaluate
           ([clos_interp_el],CONS (closSem_list_to_v env) (CONS
             (closSem_Number (&n)) (CONS (closSem_Recclosure NONE []
             cl_env
              [(1,closLang_Fn (implode "") NONE NONE 1
                clos_interp_el)] 0) rest)),state_clock_fupd (K (c +
                state_clock t4))
            t4) = (Rval [EL n env],t4))`,
  CHEAT_TAC);;

let clos_interp_rev_thm = prove
 (`!a env rest cl_env.
     1 <= closSem_state_max_app t4 ==>
     closSem_evaluate
       ([clos_interp_rev],CONS (closSem_list_to_v env) (CONS
         (closSem_list_to_v a) (CONS (closSem_Recclosure NONE [] cl_env
              [(1,closLang_Fn (implode "") NONE NONE 1
                clos_interp_rev)] 0) rest)),state_clock_fupd (K (2 *
                LENGTH a + state_clock t4))
            t4) =
      (Rval [closSem_list_to_v (APPEND (REVERSE a) env)],t4)`,
  CHEAT_TAC);;

(* HOL4 clos_interpProofScript.sml:171-172: the ML values that the
   definitions below antiquote *)

(* HOL4 clos_interpProofScript.sml:174-175: the ML values that the
   definitions below antiquote *)

(* HOL4 clos_interpProofScript.sml:177-179: ML code, not ported *)

(* HOL4 clos_interpProofScript.sml:181-185: a proof *)

(* HOL4 clos_interpProofScript.sml:187-190: a proof *)

(* [local] *)
let evaluate_SING_intro = prove
 (`x = (Rval [v],s) /\ vs = [v] ==> x = (Rval vs,s)`,
  CHEAT_TAC);;

let clos_interpreter_correct = prove
 (`(!e env (s4:('c,'ffi)closSem_state) (t4:('c,'ffi)closSem_state) r s5.
      closSem_evaluate ([e],env,s4) = (r,s5) /\
      can_interpret e /\
      interp_assum (:'c) (:'ffi) (closSem_state_clock s4) /\
      clos_interpProof_state_rel s4 t4 /\ ~(r = Rerr (Rabort
        Rtype_error)) ==>
      (?c t5.
        closSem_evaluate ([clos_interpreter_body],
                  [make_const (to_constant e); closSem_Block 0 [];
                    closSem_list_to_v env],closSem_state_clock_fupd (K
                    (c + closSem_state_clock t4))
                  t4) = (r,t5) /\
        clos_interpProof_state_rel s5 t5)) /\
   (!es env (s4:('c,'ffi)closSem_state) (t4:('c,'ffi)closSem_state) r
     s5.
      closSem_evaluate (es,env,s4) = (r,s5) /\
      can_interpret_list es /\
      interp_assum (:'c) (:'ffi) (closSem_state_clock s4) /\
      clos_interpProof_state_rel s4 t4 /\ ~(r = Rerr (Rabort
        Rtype_error)) ==>
      (?c t5 r5.
        closSem_evaluate ([clos_interpreter_body],
                  [make_const (to_constant_list es); closSem_Block 1
                    []; closSem_list_to_v env],closSem_state_clock_fupd
                    (K (c + closSem_state_clock t4))
                  t4) = (r5,t5) /\
        clos_interpProof_state_rel s5 t5 /\
        (match r with Rval vs -> r5 = Rval [closSem_list_to_v vs] |
          _1 -> r = r5)))`,
  CHEAT_TAC);;

let opt_interp_thm = prove
 (`opt_interp e = SOME x /\
   interp_assum (:'c) (:'ffi) (closSem_state_clock s4) /\
   closSem_evaluate ([e],[],(s4:('c,'ffi)closSem_state)) = (r,s5) /\
   clos_interpProof_state_rel s4 t4 /\ ~(r = Rerr (Rabort
     Rtype_error)) ==>
   (?ck t5.
     closSem_evaluate ([x],[],state_clock_fupd (K (ck + state_clock
       t4)) t4) = (r,t5) /\
     clos_interpProof_state_rel s5 (t5:('c,'ffi)closSem_state))`,
  CHEAT_TAC);;

let opt_interp1_thm' = prove
 (`!l s4 t4 s5 r.
     interp_assum (:'c) (:'ffi) (state_clock s4) /\
     closSem_evaluate ([l],[],s4) = (r,s5) /\
     clos_interpProof_state_rel s4 t4 /\ ~(r = Rerr (Rabort
       Rtype_error)) ==>
     (?ck (t5:('c,'ffi)closSem_state).
       closSem_evaluate ([opt_interp1 l],[],state_clock_fupd (K
         (state_clock t4 + ck)) t4) = (r,t5) /\
       clos_interpProof_state_rel s5 t5)`,
  CHEAT_TAC);;

let opt_interp1_thm = prove
 (`!l s4 t4 s5 r.
     interp_assum (:'c) (:'ffi) (state_clock s4) /\
     closSem_evaluate (l,[],s4) = (r,s5) /\
     clos_interpProof_state_rel s4 t4 /\ ~(r = Rerr (Rabort
       Rtype_error)) ==>
     (?ck (t5:('c,'ffi)closSem_state).
       closSem_evaluate (MAP opt_interp1 l,[],state_clock_fupd (K
         (state_clock t4 + ck)) t4) = (r,t5) /\
       clos_interpProof_state_rel s5 t5)`,
  CHEAT_TAC);;

let evaluate_insert_interp1 = prove
 (`interp_assum (:'c) (:'ffi) (state_clock s4) /\
   closSem_evaluate ([e],[],s4) = (r,s5) /\
     clos_interpProof_state_rel s4 t4 /\ ~(r = Rerr (Rabort
     Rtype_error)) ==>
   (?ck (t5:('c,'ffi)closSem_state).
     closSem_evaluate ([insert_interp1 e],[],state_clock_fupd (K
       (state_clock t4 + ck)) t4) = (r,t5) /\
     clos_interpProof_state_rel s5 t5)`,
  CHEAT_TAC);;

let evaluate_insert_interp = prove
 (`!exps s4 s5 r t4.
     interp_assum (:'c) (:'ffi) (state_clock s4) /\
     closSem_evaluate (exps,[],s4) = (r,s5) /\
       clos_interpProof_state_rel s4 t4 /\ ~(r = Rerr (Rabort
       Rtype_error)) ==>
     (?ck (t5:('c,'ffi)closSem_state).
       closSem_evaluate (insert_interp exps,[],state_clock_fupd (K
         (state_clock t4 + ck)) t4) = (r,t5) /\
       clos_interpProof_state_rel s5 t5)`,
  CHEAT_TAC);;

(* [local] *)
let state_rel_refs_clocks_eqs = prove
 (`clos_interpProof_state_rel s1 s2 ==> state_refs s1 = state_refs s2
  /\ state_clock s1 = state_clock s2`,
  CHEAT_TAC);;

(* state_rel_update_thunk[local] *)
let clos_interpProof_state_rel_update_thunk = prove
 (`clos_interpProof_state_rel s1 s2 ==>
     closSem_update_thunk [closSem_RefPtr v ptr] (state_refs s1) vs =
       SOME refs1 ==>
       (?refs2. closSem_update_thunk [closSem_RefPtr v ptr]
         (state_refs s2) vs = SOME refs2 /\
               clos_interpProof_state_rel (state_refs_fupd (K
                 refs1) s1) (state_refs_fupd (K refs2) s2))`,
  CHEAT_TAC);;

let evaluate_interp_lemma = prove
 (`(!xs (s1:('c,'ffi)closSem_state) env t1 res s2.
      (closSem_evaluate (xs,env,s1) = (res,s2)) /\ ~(res = Rerr
        (Rabort Rtype_error)) ==>
      clos_interpProof_state_rel s1 t1 ==>
      (?ck t2.
        (closSem_evaluate (xs,env,(state_clock_fupd (K (state_clock
          t1 + ck)) t1)) = (res,t2)) /\
        clos_interpProof_state_rel s2 t2)) /\
   (!args (s1:('c,'ffi)closSem_state) loc f t1 res s2.
      evaluate_app loc f args s1 = (res,s2) /\ ~(res = Rerr (Rabort
        Rtype_error)) ==>
      clos_interpProof_state_rel s1 t1 ==>
      (?ck t2.
        (evaluate_app loc f args (state_clock_fupd (K (state_clock t1
          + ck)) t1) = (res,t2)) /\
        clos_interpProof_state_rel s2 t2))`,
  CHEAT_TAC);;

let evaluate_interp_thm = prove
 (`!xs env (s1:('c,'ffi)closSem_state) t1 res s2.
     closSem_evaluate (xs,env,s1) = (res,s2) /\ ~(res = Rerr (Rabort
       Rtype_error)) /\
     clos_interpProof_state_rel s1 t1 ==>
     (?ck t2.
        closSem_evaluate (xs,env,(state_clock_fupd (K (state_clock t1
          + ck)) t1)) = (res,t2) /\
        clos_interpProof_state_rel s2 t2)`,
  CHEAT_TAC);;

(* ------------------------------------------------------------------------- *
   not has_install ignores compiler oracle
 * ------------------------------------------------------------------------- *)

(* the termination relation that HOL4 gives is
     MEASURE closSem_v_size
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 clos_interpProofScript.sml:1097-1099: the tactic that proves
   the termination *)
let v_ok_def,v_ok_ind = define_shaped_rec
  "nested"
  [`v_ok (closSem_Number i:closSem_v) <=> T`;
   `v_ok (closSem_Word64 w:closSem_v) <=> T`;
   `v_ok (closSem_Block n vs:closSem_v) <=> ALL v_ok vs`;
   `v_ok (closSem_ByteVector ws) <=> T`;
   `v_ok (closSem_RefPtr b n:closSem_v) <=> T`;
   `v_ok (closSem_Closure loco vs1 env1 n bod1:closSem_v) <=>
        ~(has_install bod1) /\ ALL v_ok env1 /\ ALL v_ok vs1`;
   `v_ok (closSem_Recclosure loco vs1 env1 fns1 i:closSem_v) <=>
        ALL v_ok env1 /\ ALL v_ok vs1 /\ i < LENGTH fns1 /\
        ALL ((~) o has_install o SND) fns1`];;
add_simp v_ok_def;;

let res_ok_def = new_definition
  `res_ok x1 =
      match x1 with
        Rerr (Rabort _2) -> T
      | (Rerr (Rraise v)) -> v_ok v
      | (Rval v) -> ALL v_ok v`;;
add_simp res_ok_def;;

let state_rel'_def = new_definition
  `state_rel' (s:('c,'ffi)closSem_state) (t:('c,'ffi)closSem_state) <=>
     (!n. SND (SND (closSem_state_compile_oracle s n)) = []) /\
       closSem_state_code
     s = FEMPTY /\ closSem_state_code t = FEMPTY /\
       closSem_state_max_app
     t = closSem_state_max_app s /\ 1 <= closSem_state_max_app s /\
       closSem_state_clock
     t = closSem_state_clock s /\ closSem_state_ffi
     t = closSem_state_ffi s /\ closSem_state_globals
     s = closSem_state_globals t /\ ALL (OPTION_ALL v_ok)
       (closSem_state_globals t) /\ closSem_state_refs
     s = closSem_state_refs t /\
     FEVERY (\(k,v). !vs. v = closSem_ValueArray vs ==> ALL v_ok vs)
       (closSem_state_refs t) /\
     FEVERY (\(k,v). !m w. v = semanticPrimitives_Thunk m w ==> v_ok
       w) (closSem_state_refs t) /\ closSem_state_compile
     s = pure_cc (insert_interp ## I) (closSem_state_compile t) /\
       closSem_state_compile_oracle
     t = pure_co (insert_interp ## I) o
       closSem_state_compile_oracle s`;;

let lookup_vars_ok = prove
 (`!vs env env'. lookup_vars vs env = SOME env' /\ ALL v_ok env ==>
  ALL v_ok env'`,
  CHEAT_TAC);;

(* [local] *)
let state_rel'_clock = prove
 (`state_rel' s t ==> state_clock t = state_clock s`,
  CHEAT_TAC);;

(* [local] *)
let state_rel'_refs = prove
 (`state_rel' s t ==> state_refs t = state_refs s`,
  CHEAT_TAC);;

(* [local] *)
let state_rel'_dec_clock = prove
 (`state_rel' s t ==> state_rel' (closSem_dec_clock 1 s)
  (closSem_dec_clock 1 t)`,
  CHEAT_TAC);;

(* [local] *)
let has_install_list_eq = prove
 (`!xs. has_install_list xs <=> EX has_install xs`,
  CHEAT_TAC);;

let evaluate_change_oracle = prove
 (`(!tmp xs env (s1:('c,'ffi)closSem_state) t1 res s2 n.
     tmp = (xs,env,s1) /\
     (closSem_evaluate (xs,env,s1) = (res,s2)) /\ ~(res = Rerr
       (Rabort Rtype_error)) ==>
     state_rel' s1 t1 /\ ~(has_install_list xs) /\ ALL v_ok env ==>
     (?t2.
        (closSem_evaluate (xs,env,t1) = (res,t2)) /\
        state_rel' s2 t2 /\ res_ok res)) /\
   (!loc f args (s:('c,'ffi)closSem_state) res s2 t1.
       evaluate_app loc f args s = (res,s2) /\ ~(res = Rerr (Rabort
         Rtype_error)) ==>
       state_rel' s t1 /\ ALL v_ok args /\ v_ok f ==>
       (?t2.
          (evaluate_app loc f args t1 = (res,t2)) /\
          state_rel' s2 t2 /\ res_ok res))`,
  CHEAT_TAC);;

(* ------------------------------------------------------------------------- *
   preservation of observable semantics
 * ------------------------------------------------------------------------- *)

(* [local] *)
let init_globals = prove
 (`closSem_state_globals
     (closSem_initial_state ffi max_app f co cc ck) = []`,
  CHEAT_TAC);;

let semantics_attach_interpreter = prove
 (`~(closSem_semantics (ffi:'ffi ffi_state) max_app FEMPTY
        co (pure_cc (insert_interp ## I) cc) (attach_interpreter xs)
          = ffi_Fail) ==>
      (!n. SND (SND (co n)) = []) /\ 0 < max_app ==>
      closSem_semantics (ffi:'ffi ffi_state) max_app FEMPTY
        (pure_co (insert_interp ## I) o co) cc (attach_interpreter
          xs) =
      closSem_semantics (ffi:'ffi ffi_state) max_app FEMPTY
        co (pure_cc (insert_interp ## I) cc) (attach_interpreter
          xs)`,
  CHEAT_TAC);;

(* ------------------------------------------------------------------------- *
   syntactic lemmas
 * ------------------------------------------------------------------------- *)

(* [local] *)
let opt_interp_lemma = prove
 (`opt_interp x = SOME x' ==>
   closProps_set_globals x' = EMPTY_BAG /\
   closProps_set_globals x = EMPTY_BAG /\
   (1 <= max_app ==> ~(contains_App_SOME max_app [x'])) /\
   every_Fn_vs_NONE [x'] /\
   no_mti x' /\
   closProps_esgc_free x /\
   closProps_esgc_free x'`,
  CHEAT_TAC);;

let elist_globals_insert_interp = prove
 (`closProps_elist_globals (insert_interp xs) =
   closProps_elist_globals xs`,
  CHEAT_TAC);;

let contains_App_SOME_insert_interp = prove
 (`~(contains_App_SOME max_app xs) /\ 1 <= max_app ==>
   ~(contains_App_SOME max_app (insert_interp xs))`,
  CHEAT_TAC);;

let every_Fn_vs_NONE_insert_interp = prove
 (`every_Fn_vs_NONE xs ==> every_Fn_vs_NONE (insert_interp xs)`,
  CHEAT_TAC);;

let insert_interp_no_mti = prove
 (`MEM e (insert_interp xs) ==> ALL no_mti xs ==> no_mti e`,
  CHEAT_TAC);;

let insert_interp_esgc_free = prove
 (`ALL closProps_esgc_free (insert_interp xs) = ALL
  closProps_esgc_free xs`,
  CHEAT_TAC);;
