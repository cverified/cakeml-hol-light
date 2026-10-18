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

needs "compiler/backend/closLang.ml";;
needs "compiler/backend/clos_interp.ml";;
needs "compiler/backend/semantics/backendProps.ml";;
needs "compiler/backend/semantics/closProps.ml";;
needs "compiler/backend/semantics/closSem.ml";;
needs "semantics/ast.ml";;
needs "semantics/semanticPrimitives.ml";;

(* ------------------------------------------------------------------------- *
   correctness of interpreter
 * ------------------------------------------------------------------------- *)

let state_rel_def = cake_define
  `clos_interpProof_state_rel (s:('c,'ffi)closSem_state)
  (t:('c,'ffi)closSem_state) <=>
     (!n. SND (SND (closSem_state_compile_oracle s n)) = []) /\
       closSem_state_code
     s = FEMPTY /\ closSem_state_code t = FEMPTY /\
       closSem_state_max_app
     t = closSem_state_max_app s /\ 1 <= closSem_state_max_app s /\
       state_clock
     t = state_clock s /\ state_ffi
     t = state_ffi s /\ closSem_state_globals
     s = closSem_state_globals t /\ state_refs
     s = state_refs t /\ closSem_state_compile
     s = pure_cc (insert_interp ## I) (closSem_state_compile t) /\
       closSem_state_compile_oracle
     t = pure_co (insert_interp ## I) o closSem_state_compile_oracle
       s /\
     oHD (closSem_state_globals s) = SOME (SOME (Closure NONE []
       [] 1 clos_interpreter))`;;
hol4_overload "state_rel" "clos_interpProof_state_rel";;

let state_rel_1_def = cake_define
  `state_rel_1 (s:('c,'ffi)closSem_state) (t:('c,'ffi)closSem_state) <=>
     (!n. SND (SND (closSem_state_compile_oracle s n)) = []) /\
       closSem_state_code
     s = FEMPTY /\ closSem_state_code t = FEMPTY /\
       closSem_state_max_app
     t = closSem_state_max_app s /\ 1 <= closSem_state_max_app s /\
       state_clock
     t = state_clock s /\ state_ffi
     t = state_ffi s /\ closSem_state_globals
     s = closSem_state_globals t /\ state_refs
     s = state_refs t /\ closSem_state_compile
     s = pure_cc (insert_interp ## I) (closSem_state_compile t) /\
       closSem_state_compile_oracle
     t = pure_co (insert_interp ## I) o
       closSem_state_compile_oracle s`;;

let interp_assum_def = cake_define
  `interp_assum (:'c) (:'ffi) c <=>
     (!xs s1 env (t1:('c,'ffi)closSem_state) res s2. state_clock
       s1 <= c /\
       closSem_evaluate (xs,env,s1) = (res,s2) /\ ~(
       res = Rerr (Rabort Rtype_error)) ==>
       clos_interpProof_state_rel s1 t1 ==>
       (?ck t2.
         closSem_evaluate (xs,env,state_clock_fupd (K (ck +
           state_clock t1)) t1) = (res,t2) /\
         clos_interpProof_state_rel s2 t2)) /\
     (!args s1 loc f (t1:('c,'ffi)closSem_state) res s2. state_clock
       s1 <= c /\
       evaluate_app loc f args s1 = (res,s2) /\ ~(
       res = Rerr (Rabort Rtype_error)) ==>
       clos_interpProof_state_rel s1 t1 ==>
       (?ck t2.
         evaluate_app loc f args (state_clock_fupd (K (ck +
           state_clock t1)) t1) =
         (res,t2) /\ clos_interpProof_state_rel s2 t2))`;;

(* HOL4 clos_interpProofScript.sml:171-172: the ML values that the
   definitions below antiquote *)

(* HOL4 clos_interpProofScript.sml:174-175: the ML values that the
   definitions below antiquote *)

(* HOL4 clos_interpProofScript.sml:177-179: ML code, not ported *)

(* HOL4 clos_interpProofScript.sml:181-185: a proof *)

(* HOL4 clos_interpProofScript.sml:187-190: a proof *)

(* ------------------------------------------------------------------------- *
   not has_install ignores compiler oracle
 * ------------------------------------------------------------------------- *)

let _ = size_thms "closSem_v";;
(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 clos_interpProofScript.sml:1097-1099: the tactic that proves
   the termination *)
let v_ok_def = cake_define_list_try (fun () ->
  `MEASURE closSem_v_size`)
  [`v_ok (closSem_Number i:closSem_v) <=> T`;
   `v_ok (Word64 w:closSem_v) <=> T`;
   `v_ok (closSem_Block n vs:closSem_v) <=> EVERY v_ok vs`;
   `v_ok (closSem_ByteVector ws) <=> T`;
   `v_ok (closSem_RefPtr b n:closSem_v) <=> T`;
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
       state_clock
     t = state_clock s /\ state_ffi
     t = state_ffi s /\ closSem_state_globals
     s = closSem_state_globals t /\ EVERY (OPTION_ALL v_ok)
       (closSem_state_globals t) /\ state_refs
     s = state_refs t /\
     FEVERY (\(k,v). !vs. v = closSem_ValueArray vs ==> EVERY v_ok
       vs) (state_refs t) /\
     FEVERY (\(k,v). !m w. v = Thunk m w ==> v_ok w) (state_refs t)
       /\ closSem_state_compile
     s = pure_cc (insert_interp ## I) (closSem_state_compile t) /\
       closSem_state_compile_oracle
     t = pure_co (insert_interp ## I) o
       closSem_state_compile_oracle s`;;

(* ------------------------------------------------------------------------- *
   preservation of observable semantics
 * ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *
   syntactic lemmas
 * ------------------------------------------------------------------------- *)
