(* ======================================================== *)
(*  evaluate_skip: ported from HOL4's
    compiler/repl/evaluate_skipScript.sml
    A definition theory, with 8 definitions and 47 theorems.  Needed
    by evaluate_init.ml and repl_types.ml.  *)
(* ======================================================== *)

(*
  Lemmas used in repl_typesTheory. These lemmas show that a plain
  evaluate run can be replicated in a state with junk refs, extra type
  stamps and unused exception definitions.
*)

needs "basis/pure/mlstring.ml";;
needs "characteristic/cfFFIType.ml";;
needs "semantics/ast.ml";;
needs "semantics/evaluate.ml";;
needs "semantics/namespace.ml";;
needs "semantics/proofs/evaluateProps.ml";;
needs "semantics/proofs/namespaceProps.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "translator/ml_prog.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "evaluate_skip"
  ["evaluate"; "evaluateProps"; "ml_prog"; "namespaceProps";
   "semanticPrimitives"];;

let _ = do_list hide_constant ["id"; "test"];;

let NOT_NIL_CONS = prove
 (`~(xs = []) <=> (?y ys. xs = CONS y ys)`,
  CHEAT_TAC);;

let stamp_rel = cake_inductive
  `(!ft fe n m1 m2.
     FLOOKUP ft m1 = SOME m2 ==>
     stamp_rel ft fe (TypeStamp n m1) (TypeStamp n m2)) /\
   (!ft fe m1 m2.
     FLOOKUP fe m1 = SOME m2 ==>
     stamp_rel ft fe (ExnStamp m1) (ExnStamp m2))`;;

let ctor_rel_def = new_definition
  `ctor_rel ft fe envc1 (envc2:(mlstring,mlstring,num#stamp)namespace) <=>
     nsAll2 (\id. (RPROD (=) (stamp_rel ft fe))) envc1 envc2`;;

let v_rel = cake_inductive
  `(!(fr:(num,num)fmap) (ft:(num,num)fmap) (fe:(num,num)fmap) l.
      evaluate_skip_v_rel fr ft fe (semanticPrimitives_Litv l)
        (semanticPrimitives_Litv l)) /\
   (!fr ft fe t1 t2 xs ys.
      ALL2 (evaluate_skip_v_rel fr ft fe) xs ys /\ OPTREL (stamp_rel ft fe)
        t1 t2 ==>
      evaluate_skip_v_rel fr ft fe (semanticPrimitives_Conv t1 xs)
        (semanticPrimitives_Conv t2 ys)) /\
   (!fr ft fe xs ys.
      ALL2 (evaluate_skip_v_rel fr ft fe) xs ys ==>
      evaluate_skip_v_rel fr ft fe (semanticPrimitives_Vectorv xs)
        (semanticPrimitives_Vectorv ys)) /\
   (!fr ft fe l1 l2 b.
      FLOOKUP fr l1 = SOME l2 ==>
      evaluate_skip_v_rel fr ft fe (semanticPrimitives_Loc b l1)
        (semanticPrimitives_Loc b l2)) /\
   (!fr ft fe env1 env2 n e.
      evaluate_skip_env_rel fr ft fe env1 env2 ==>
        evaluate_skip_v_rel fr ft fe (semanticPrimitives_Closure env1 n e)
          (semanticPrimitives_Closure env2 n e)) /\
   (!fr ft fe env1 env2 fns n.
      evaluate_skip_env_rel fr ft fe env1 env2 ==>
        evaluate_skip_v_rel fr ft fe (semanticPrimitives_Recclosure env1 fns
          n) (semanticPrimitives_Recclosure env2 fns n)) /\
   (!fr ft fe env1 env2 ns.
     evaluate_skip_env_rel fr ft fe env1 env2 ==>
      evaluate_skip_v_rel fr ft fe (semanticPrimitives_Env env1 ns)
        (semanticPrimitives_Env env2 ns)) /\
   (!fr ft fe env1 env2.
      ctor_rel ft fe (sem_env_c env1) (sem_env_c env2) /\
      nsAll2 (\id. evaluate_skip_v_rel fr ft fe) (sem_env_v env1) (sem_env_v
        env2) ==>
      evaluate_skip_env_rel fr ft fe env1 env2)`;;

(* HOL4 evaluate_skipScript.sml:71-87: a theorem that HOL4 states as the
   value of an ML expression: v_rel_def *)

(* HOL4 evaluate_skipScript.sml:89-90: a theorem that HOL4 states as the
   value of an ML expression: env_rel_def *)

let ref_rel_def = new_definition
  `evaluate_skip_ref_rel f x2 x3 =
   match (x2,x3) with
     (semanticPrimitives_Refv v,semanticPrimitives_Refv w) -> f v w
   | (semanticPrimitives_Varray vs,semanticPrimitives_Varray ws) -> ALL2 f
     vs ws
   | (semanticPrimitives_W8array a,semanticPrimitives_W8array b) -> (a = b)
   | (semanticPrimitives_Thunk m1 v1,semanticPrimitives_Thunk m2 v2) -> ((m1
     = m2) /\ f v1 v2)
   | (_,_) -> F`;;

let ref_rel_mono = prove
 (`evaluate_skip_ref_rel P v w /\
   (!v w. P v w ==> Q v w) ==>
     evaluate_skip_ref_rel Q v w`,
  CHEAT_TAC);;

let ref_rel_refl = prove
 (`(!x. P x x) ==>
   evaluate_skip_ref_rel P x x`,
  CHEAT_TAC);;

let state_rel_def = new_definition
  `evaluate_skip_state_rel l fr ft fe (s:'ffi semanticPrimitives_state) (t:'ffi
  semanticPrimitives_state) <=>
     INJ (FAPPLY fr) (FDOM fr) (count (LENGTH (semanticPrimitives_state_refs
       t))) /\
     INJ (FAPPLY ft) (FDOM ft) (count
       (semanticPrimitives_state_next_type_stamp t)) /\
     INJ (FAPPLY fe) (FDOM fe) (count
       (semanticPrimitives_state_next_exn_stamp t)) /\
     FDOM fr = count (LENGTH (semanticPrimitives_state_refs s)) /\
     FDOM ft = count (semanticPrimitives_state_next_type_stamp s) /\
     FDOM fe = count (semanticPrimitives_state_next_exn_stamp s)
       /\ semanticPrimitives_state_clock
     t = semanticPrimitives_state_clock s
       /\ semanticPrimitives_state_eval_state
     s = NONE /\ semanticPrimitives_state_eval_state
     t = NONE /\ semanticPrimitives_state_ffi
     t = semanticPrimitives_state_ffi s /\
     (!n. n < l ==> FLOOKUP fr n = SOME (n:num) /\ n < LENGTH
       (semanticPrimitives_state_refs s)) /\
     FLOOKUP ft bool_type_num = SOME bool_type_num /\
     FLOOKUP ft list_type_num = SOME list_type_num /\
     FLOOKUP fe 0 = SOME 0 /\
     // Bind
     FLOOKUP fe 1 = SOME 1 /\
     // Chr
     FLOOKUP fe 2 = SOME 2 /\
     // Div
     FLOOKUP fe 3 = SOME 3 /\
     (
      // Subscript
      !n. if n < LENGTH (semanticPrimitives_state_refs s) then
            (?m. FLOOKUP fr n = SOME m /\
                 m < LENGTH (semanticPrimitives_state_refs t) /\
                 evaluate_skip_ref_rel (evaluate_skip_v_rel fr ft fe) (EL n
                   (semanticPrimitives_state_refs s)) (EL m
                   (semanticPrimitives_state_refs t)))
          else FLOOKUP fr n = NONE)`;;

let res_rel_def = new_definition
  `res_rel f g x y =
     match (x,y) with
       (Rval e,Rval e1) -> f e e1
     | (Rerr (Rraise e),Rerr (Rraise e1)) -> g e e1
     | (Rerr (Rabort e),Rerr (Rabort e1)) -> e = e1
     | (x,y) -> F`;;
add_simp res_rel_def;;

let res_rel_abort = prove
 (`res_rel R Q (Rerr (Rabort x)) r <=> r = Rerr (Rabort x)`,
  CHEAT_TAC);;
add_simp res_rel_abort;;

let stamp_rel_update = prove
 (`!ft fe x y.
     stamp_rel ft fe x y ==>
       (!ft1 fe1.
         ft SUBMAP ft1 /\ fe SUBMAP fe1 ==>
           stamp_rel ft1 fe1 x y)`,
  CHEAT_TAC);;

let ctor_rel_update = prove
 (`ctor_rel ft fe envc1 envc2 /\
   ft SUBMAP ft1 /\
   fe SUBMAP fe1 ==>
     ctor_rel ft1 fe1 envc1 envc2`,
  CHEAT_TAC);;

let v_rel_update_lemma = prove
 (`(!fr ft fe v w.
     evaluate_skip_v_rel fr ft fe v w ==>
       (!fr1 ft1 fe1.
         fr SUBMAP fr1 /\
         ft SUBMAP ft1 /\
         fe SUBMAP fe1 ==>
           evaluate_skip_v_rel fr1 ft1 fe1 v w)) /\
   (!fr ft fe env1 env2.
    evaluate_skip_env_rel fr ft fe env1 env2 ==>
      (!fr1 ft1 fe1.
        fr SUBMAP fr1 /\
        ft SUBMAP ft1 /\
        fe SUBMAP fe1 ==>
          evaluate_skip_env_rel fr1 ft1 fe1 env1 env2))`,
  CHEAT_TAC);;

let env_rel_update = CONJUNCT2 v_rel_update_lemma;;

let v_rel_update = CONJUNCT1 v_rel_update_lemma;;

let ctor_rel_nsAppend = prove
 (`ctor_rel ft fe (sem_env_c x1) (sem_env_c x2) /\
   ctor_rel ft fe (sem_env_c y1) (sem_env_c y2) ==>
     ctor_rel ft fe (nsAppend (sem_env_c x1) (sem_env_c y1)) (nsAppend
       (sem_env_c x2) (sem_env_c y2))`,
  CHEAT_TAC);;

let env_rel_nsAppend = prove
 (`evaluate_skip_env_rel fr ft fe x1 x2 /\
   evaluate_skip_env_rel fr ft fe y1 y2 ==>
     evaluate_skip_env_rel fr ft fe (mk_sem_env (nsAppend (sem_env_v x1)
       (sem_env_v y1)) (nsAppend (sem_env_c x1) (sem_env_c y1)))
                      (mk_sem_env (nsAppend (sem_env_v x2) (sem_env_v y2))
                        (nsAppend (sem_env_c x2) (sem_env_c y2)))`,
  CHEAT_TAC);;

let env_rel_extend_dec_env = prove
 (`evaluate_skip_env_rel fr ft fe env1 env2 /\
   evaluate_skip_env_rel fr ft fe env1' env2' ==>
     evaluate_skip_env_rel fr ft fe (extend_dec_env env1' env1)
                      (extend_dec_env env2' env2)`,
  CHEAT_TAC);;

let env_rel_nsBind = prove
 (`evaluate_skip_env_rel fr ft fe env1 env2 /\
   evaluate_skip_v_rel fr ft fe v w ==>
     evaluate_skip_env_rel fr ft fe (sem_env_v_fupd (K (nsBind n v
       (sem_env_v env1))) env1)
                      (sem_env_v_fupd (K (nsBind n w (sem_env_v env2)))
                        env2)`,
  CHEAT_TAC);;

(* [local] *)
let fmap_greatest = prove
 (`!m. ?y. !x. x IN FRANGE m ==> x < y`,
  CHEAT_TAC);;

(* --------------------------------------------------------------------------
 *
 * -------------------------------------------------------------------------- *)

let match_res_rel_def = new_definition
  `match_res_rel R x2' x3' =
     match (x2',x3') with
       (Match env1,Match env2) -> R env1 env2
     | (No_match,No_match) -> T
     | (Match_type_error,Match_type_error) -> T
     | (_,_) -> F`;;
add_simp match_res_rel_def;;

let pmatch_update = prove
 (`(!envC s p v ws res.
     semanticPrimitives_pmatch envC s p v ws = res ==>
       (!envC' s' v' ws' res' ns ms.
         ctor_rel ft fe envC envC' /\
         evaluate_skip_v_rel fr ft fe v v' /\
         INJ (FAPPLY ft) (FDOM ft) ns /\
         INJ (FAPPLY fe) (FDOM fe) ms /\
         ALL2 (\(n,v) (m,w). n = m /\ evaluate_skip_v_rel fr ft fe v w) ws
           ws' /\
         semanticPrimitives_pmatch envC' s' p v' ws' = res' /\
         (!n. if n < LENGTH s then
              ?m. FLOOKUP fr n = SOME m /\ m < LENGTH s' /\
                  evaluate_skip_ref_rel (evaluate_skip_v_rel fr ft fe) (EL n
                    s) (EL m s')
            else FLOOKUP fr n = NONE) ==>
           match_res_rel (\env env'.
             ALL2 (\(n,v) (m,w). n = m /\ evaluate_skip_v_rel fr ft fe v w)
                      env env') res res')) /\
   (!envC s ps vs ws res.
     semanticPrimitives_pmatch_list envC s ps vs ws = res ==>
       (!envC' s' vs' ws' res' ns ms.
         INJ (FAPPLY ft) (FDOM ft) ns /\
         INJ (FAPPLY fe) (FDOM fe) ms /\
         ctor_rel ft fe envC envC' /\
         ALL2 (evaluate_skip_v_rel fr ft fe) vs vs' /\
         ALL2 (\(n,v) (m,w). n = m /\ evaluate_skip_v_rel fr ft fe v w) ws
           ws' /\
         semanticPrimitives_pmatch_list envC' s' ps vs' ws' = res' /\
         (!n. if n < LENGTH s then
              ?m. FLOOKUP fr n = SOME m /\ m < LENGTH s' /\
                  evaluate_skip_ref_rel (evaluate_skip_v_rel fr ft fe) (EL n
                    s) (EL m s')
            else FLOOKUP fr n = NONE) ==>
           match_res_rel (\env env'.
             ALL2 (\(n,v) (m,w). n = m /\ evaluate_skip_v_rel fr ft fe v w)
                      env env') res res'))`,
  CHEAT_TAC);;

(* HOL4 evaluate_skipScript.sml:374-417: ML code, not ported *)

(* HOL4 evaluate_skipScript.sml:419-453: a theorem whose statement the port
   cannot state yet: evaluate_update *)

(* HOL4 evaluate_skipScript.sml:455-458: a proof *)

(* HOL4 evaluate_skipScript.sml:460-481: a proof *)

(* HOL4 evaluate_skipScript.sml:483-487: a proof *)

(* HOL4 evaluate_skipScript.sml:489-496: a proof *)

let can_pmatch_all_thm = prove
 (`!ps envc1 s v envc2 t w ms ns.
     ctor_rel ft fe envc1 envc2 /\
     INJ (FAPPLY ft) (FDOM ft) ns /\
     INJ (FAPPLY fe) (FDOM fe) ms /\
     (!n. if n < LENGTH s then
            ?m. FLOOKUP fr n = SOME m /\ m < LENGTH t /\
            evaluate_skip_ref_rel (evaluate_skip_v_rel fr ft fe) (EL n s)
              (EL m t)
          else FLOOKUP fr n = NONE) /\
     evaluate_skip_v_rel fr ft fe v w ==>
     (can_pmatch_all envc1 s ps v <=> can_pmatch_all envc2 t ps w)`,
  CHEAT_TAC);;

(* HOL4 evaluate_skipScript.sml:529-559: a proof *)

let do_con_check_update = prove
 (`evaluate_skip_env_rel fr ft fe env env1 ==>
     do_con_check (sem_env_c env) cn n = do_con_check (sem_env_c env1) cn
       n`,
  CHEAT_TAC);;

(* HOL4 evaluate_skipScript.sml:577-599: a proof *)

(* HOL4 evaluate_skipScript.sml:601-611: a proof *)

(* HOL4 evaluate_skipScript.sml:613-618: a proof *)

(* HOL4 evaluate_skipScript.sml:620-627: a proof *)

(* HOL4 evaluate_skipScript.sml:629-637: a proof *)

let state_rel_store_lookup = prove
 (`evaluate_skip_state_rel l fr ft fe s t /\
   FLOOKUP fr n = SOME m ==>
     OPTREL (evaluate_skip_ref_rel (evaluate_skip_v_rel fr ft fe))
            (store_lookup n (semanticPrimitives_state_refs s))
            (store_lookup m (semanticPrimitives_state_refs t))`,
  CHEAT_TAC);;

let state_rel_store_assign = prove
 (`evaluate_skip_state_rel l fr ft fe s t /\
   FLOOKUP fr n = SOME m /\
   evaluate_skip_ref_rel (evaluate_skip_v_rel fr ft fe) v w ==>
     OPTREL
       (\r1 r2. evaluate_skip_state_rel l fr ft fe
         (semanticPrimitives_state_refs_fupd (K r1) s)
         (semanticPrimitives_state_refs_fupd (K r2) t))
       (store_assign n v (semanticPrimitives_state_refs s))
       (store_assign m w (semanticPrimitives_state_refs t))`,
  CHEAT_TAC);;

let v_rel_v_to_list = prove
 (`!x1 res1 x2 res2.
     evaluate_skip_v_rel fr ft fe x1 x2 /\
     semanticPrimitives_v_to_list x1 = res1 /\
     semanticPrimitives_v_to_list x2 = res2 /\
     INJ (FAPPLY ft) (FDOM ft) (count ns) /\
     FLOOKUP ft list_type_num = SOME list_type_num /\
     list_type_num < ns ==>
       OPTREL (ALL2 (evaluate_skip_v_rel fr ft fe)) res1 res2`,
  CHEAT_TAC);;

let v_rel_vs_to_string = prove
 (`!x1 res1 x2 res2.
     ALL2 (evaluate_skip_v_rel fr ft fe) x1 x2 /\
     semanticPrimitives_vs_to_string x1 = res1 /\
     semanticPrimitives_vs_to_string x2 = res2 /\
     INJ (FAPPLY ft) (FDOM ft) (count ns) /\
     FLOOKUP ft list_type_num = SOME list_type_num /\
     list_type_num < ns ==>
       res1 = res2`,
  CHEAT_TAC);;

let v_rel_list_to_v = prove
 (`!x1 xs1 x2 xs2.
     semanticPrimitives_v_to_list x1 = SOME xs1 /\
     semanticPrimitives_v_to_list x2 = SOME xs2 /\
     ALL2 (evaluate_skip_v_rel fr ft fe) xs1 xs2 /\
     FLOOKUP ft list_type_num = SOME list_type_num ==>
       evaluate_skip_v_rel fr ft fe (semanticPrimitives_list_to_v xs1)
         (semanticPrimitives_list_to_v xs2)`,
  CHEAT_TAC);;

let v_rel_v_to_char_list = prove
 (`!x1 res1 x2 res2.
     evaluate_skip_v_rel fr ft fe x1 x2 /\
     semanticPrimitives_v_to_char_list x1 = res1 /\
     semanticPrimitives_v_to_char_list x2 = res2 /\
     INJ (FAPPLY ft) (FDOM ft) (count ns) /\
     FLOOKUP ft list_type_num = SOME list_type_num /\
     list_type_num < ns ==>
       res1 = res2`,
  CHEAT_TAC);;

let v_to_list_list_to_v = prove
 (`!xs.
     semanticPrimitives_v_to_list (semanticPrimitives_list_to_v xs) = SOME
       xs`,
  CHEAT_TAC);;

let INJ_EQ_11_alt = prove
 (`!f s x y. INJ f s t /\ x IN s /\ y IN s ==> (f x = f y <=> x = y)`,
  CHEAT_TAC);;

let v_rel_do_eq = prove
 (`(!x1 y1 x2 y2.
      evaluate_skip_v_rel fr ft fe x1 x2 /\
      evaluate_skip_v_rel fr ft fe y1 y2 /\
      FLOOKUP ft bool_type_num = SOME bool_type_num /\
      INJ (FAPPLY fr) (FDOM fr) (count rs) /\
      INJ (FAPPLY ft) (FDOM ft) (count ns) /\
      INJ (FAPPLY fe) (FDOM fe) (count ms) ==>
      semanticPrimitives_do_eq x1 y1 = semanticPrimitives_do_eq x2 y2) /\
   (!x1 y1 x2 y2.
      ALL2 (evaluate_skip_v_rel fr ft fe) x1 x2 /\
      ALL2 (evaluate_skip_v_rel fr ft fe) y1 y2 /\
      FLOOKUP ft bool_type_num = SOME bool_type_num /\
      INJ (FAPPLY fr) (FDOM fr) (count rs) /\
      INJ (FAPPLY ft) (FDOM ft) (count ns) /\
      INJ (FAPPLY fe) (FDOM fe) (count ms) ==>
      semanticPrimitives_do_eq_list x1 y1 = semanticPrimitives_do_eq_list
        x2 y2)`,
  CHEAT_TAC);;

(* [local] *)
let v_rel_IMP_check_type_eq = prove
 (`evaluate_skip_state_rel l fr ft fe s t ==>
   evaluate_skip_v_rel fr ft fe v1 w1 ==> (semanticPrimitives_check_type
     ty v1 = semanticPrimitives_check_type ty w1)`,
  CHEAT_TAC);;

(* [local] *)
let v_rel_IMP_dest_Litv_eq = prove
 (`evaluate_skip_v_rel fr ft fe v1 w1 ==> semanticPrimitives_dest_Litv v1 =
  semanticPrimitives_dest_Litv w1`,
  CHEAT_TAC);;

(* [local] *)
let do_test_thm = prove
 (`semanticPrimitives_do_test test ty v1 v2 = res /\
   evaluate_skip_v_rel fr ft fe v1 w1 /\
   evaluate_skip_v_rel fr ft fe v2 w2 /\
   evaluate_skip_state_rel l fr ft fe s t ==>
   semanticPrimitives_do_test test ty w1 w2 = res`,
  CHEAT_TAC);;

let do_arith_update = prove
 (`evaluate_skip_state_rel l fr ft fe s t /\
   ALL2 (evaluate_skip_v_rel fr ft fe) vs ws /\
   ALL (semanticPrimitives_check_type ty) vs ==>
   OPTREL (extend_dec_env (evaluate_skip_v_rel fr ft fe)
     (evaluate_skip_v_rel fr ft fe))
     (semanticPrimitives_do_arith a ty vs) (semanticPrimitives_do_arith a
       ty ws)`,
  CHEAT_TAC);;

let do_app_update = prove
 (`semanticPrimitives_do_app (semanticPrimitives_state_refs
  s,semanticPrimitives_state_ffi s) op vs = res /\
   evaluate_skip_state_rel l fr ft fe s t /\
   ALL2 (evaluate_skip_v_rel fr ft fe) vs ws /\ ~(op = ast_Opapp) /\ ~(op =
     ast_Eval) ==>
     (?fr1 ft1 fe1 res1.
       semanticPrimitives_do_app (semanticPrimitives_state_refs
         t,semanticPrimitives_state_ffi t) op ws = res1 /\
       fr SUBMAP fr1 /\
       ft SUBMAP ft1 /\
       fe SUBMAP fe1 /\
       OPTREL (\((refs1,ffi1),res) ((refs1',ffi1'),res1).
                 ?s1 t1. semanticPrimitives_state_refs
                   s1 = refs1 /\ semanticPrimitives_state_ffi s1 = ffi1
                     /\ semanticPrimitives_state_refs
                   t1 = refs1' /\ semanticPrimitives_state_ffi t1 = ffi1'
                     /\ semanticPrimitives_state_next_exn_stamp
                   s1 = semanticPrimitives_state_next_exn_stamp s
                     /\ semanticPrimitives_state_next_exn_stamp
                   t1 = semanticPrimitives_state_next_exn_stamp t
                     /\ semanticPrimitives_state_next_type_stamp
                   s1 = semanticPrimitives_state_next_type_stamp s
                     /\ semanticPrimitives_state_next_type_stamp
                   t1 = semanticPrimitives_state_next_type_stamp t /\
                   evaluate_skip_state_rel l fr1 ft1 fe1 s1 t1 /\
                   res_rel (evaluate_skip_v_rel fr1 ft1 fe1)
                     (evaluate_skip_v_rel fr1 ft1 fe1) res res1)
               res res1)`,
  CHEAT_TAC);;

(* TODO Move up *)
let res_rel_list_result = prove
 (`res_rel R1 R2 x y ==>
     res_rel (ALL2 R1) R2 (list_result x) (list_result y)`,
  CHEAT_TAC);;

(* TODO Move up *)
let res_rel_mono = prove
 (`res_rel R1 R2 x y /\
   (!x y. R1 x y ==> Q1 x y) /\
   (!x y. R2 x y ==> Q2 x y) ==>
     res_rel Q1 Q2 x y`,
  CHEAT_TAC);;

let thunk_rel_def = new_definition
  `thunk_rel f x2'' x3'' =
   match (x2'',x3'') with
     (semanticPrimitives_BadRef,semanticPrimitives_BadRef) -> T
   | (semanticPrimitives_NotThunk,semanticPrimitives_NotThunk) -> T
   | (semanticPrimitives_IsThunk m1 v1,semanticPrimitives_IsThunk m2 v2) ->
     (m1 = m2 /\ f v1 v2)
   | (_,_) -> F`;;

let state_rel_dest_thunk = prove
 (`evaluate_skip_state_rel l fr ft fe s t /\
   ALL2 (evaluate_skip_v_rel fr ft fe) vs ws /\
   semanticPrimitives_dest_thunk vs (semanticPrimitives_state_refs s) = t1
     ==>
     (?t2. semanticPrimitives_dest_thunk ws (semanticPrimitives_state_refs
       t) = t2 /\ thunk_rel (evaluate_skip_v_rel fr ft fe) t1 t2)`,
  CHEAT_TAC);;

let state_rel_update_thunk_NONE = prove
 (`fr1 SUBMAP fr2 /\
   evaluate_skip_state_rel l fr2 ft2 fe2 s t /\
   ALL2 (evaluate_skip_v_rel fr1 ft1 fe1) vs1 ws1 /\
   ALL2 (evaluate_skip_v_rel fr2 ft2 fe2) vs2 ws2 /\
   semanticPrimitives_update_thunk vs1 (semanticPrimitives_state_refs s) vs2
     = NONE ==>
     semanticPrimitives_update_thunk ws1 (semanticPrimitives_state_refs t)
       ws2 = NONE`,
  CHEAT_TAC);;

let state_rel_update_thunk_SOME = prove
 (`fr1 SUBMAP fr2 /\
   evaluate_skip_state_rel l fr2 ft2 fe2 s t /\
   semanticPrimitives_update_thunk vs1 (semanticPrimitives_state_refs s) vs2
     = SOME refs1 /\
   ALL2 (evaluate_skip_v_rel fr1 ft1 fe1) vs1 a1 /\
   ALL2 (evaluate_skip_v_rel fr2 ft2 fe2) vs2 a2 ==>
     (?refs2.
       (semanticPrimitives_update_thunk a1 (semanticPrimitives_state_refs t)
         a2 = SOME refs2 /\
        evaluate_skip_state_rel l fr2 ft2 fe2
          (semanticPrimitives_state_refs_fupd (K refs1) s)
          (semanticPrimitives_state_refs_fupd (K refs2) t)))`,
  CHEAT_TAC);;

(* HOL4 evaluate_skipScript.sml:1921-2021: a proof *)

let do_opapp_update = prove
 (`semanticPrimitives_do_opapp vs = res1 /\
   ALL2 (evaluate_skip_v_rel fr ft fe) vs ws ==>
     (let res2 = semanticPrimitives_do_opapp ws in
     OPTREL (\(env1,x1) (env2,x2). evaluate_skip_env_rel fr ft fe env1 env2
       /\ x1 = x2)
            res1 res2)`,
  CHEAT_TAC);;

(* HOL4 evaluate_skipScript.sml:2045-2072: a proof *)

let v_rel_Boolv = prove
 (`evaluate_skip_state_rel l fr ft fe s t /\
   evaluate_skip_v_rel fr ft fe v1 v2 ==>
     (!b. v1 = semanticPrimitives_Boolv b <=> v2 =
       semanticPrimitives_Boolv b)`,
  CHEAT_TAC);;

let v_rel_do_log = prove
 (`evaluate_skip_state_rel l fr ft fe s t /\
   evaluate_skip_v_rel fr ft fe v1 v2 /\
   do_log lop v1 x = res ==>
     (match res with
       SOME (semanticPrimitives_Val v) ->
         (?w. do_log lop v2 x = SOME (semanticPrimitives_Val w) /\
             evaluate_skip_v_rel fr ft fe v w)
     | _ -> do_log lop v2 x = res)`,
  CHEAT_TAC);;

(* HOL4 evaluate_skipScript.sml:2100-2117: a proof *)

(* HOL4 evaluate_skipScript.sml:2119-2137: a proof *)

(* HOL4 evaluate_skipScript.sml:2139-2170: a proof *)

(* HOL4 evaluate_skipScript.sml:2172-2192: a proof *)

(* HOL4 evaluate_skipScript.sml:2194-2210: a proof *)

(* HOL4 evaluate_skipScript.sml:2212-2214: a proof *)

(* HOL4 evaluate_skipScript.sml:2216-2218: a proof *)

(* HOL4 evaluate_skipScript.sml:2220-2223: a proof *)

(* HOL4 evaluate_skipScript.sml:2225-2258: a proof *)

(* HOL4 evaluate_skipScript.sml:2260-2264: a proof *)

(* HOL4 evaluate_skipScript.sml:2266-2296: a proof *)

let env_rel_one_con_check = prove
 (`evaluate_skip_env_rel fr ft fe env env1 ==>
   one_con_check (sem_env_c env1) = one_con_check (sem_env_c env)`,
  CHEAT_TAC);;

(* HOL4 evaluate_skipScript.sml:2313-2338: a proof *)

(* HOL4 evaluate_skipScript.sml:2340-2355: a proof *)

let state_rel_with_next_type_stamp = prove
 (`evaluate_skip_state_rel l fr ft fe s t ==>
     evaluate_skip_state_rel l fr
       (FUNION ft (FUN_FMAP (\n. n -
         semanticPrimitives_state_next_type_stamp s +
         semanticPrimitives_state_next_type_stamp t)
                      (IMAGE ((+) (semanticPrimitives_state_next_type_stamp
                        s)) (count extra)))) fe
       (semanticPrimitives_state_next_type_stamp_fupd (K (extra +
         semanticPrimitives_state_next_type_stamp s)) s)
       (semanticPrimitives_state_next_type_stamp_fupd (K (extra +
         semanticPrimitives_state_next_type_stamp t)) t)`,
  CHEAT_TAC);;

let state_rel_with_next_exn_stamp = prove
 (`evaluate_skip_state_rel l fr ft fe s t ==>
     evaluate_skip_state_rel l fr ft
       (FUNION fe (FUN_FMAP (\n. n - semanticPrimitives_state_next_exn_stamp
         s + semanticPrimitives_state_next_exn_stamp t)
                      (IMAGE ((+) (semanticPrimitives_state_next_exn_stamp
                        s)) (count extra))))
       (semanticPrimitives_state_next_exn_stamp_fupd (K (extra +
         semanticPrimitives_state_next_exn_stamp s)) s)
       (semanticPrimitives_state_next_exn_stamp_fupd (K (extra +
         semanticPrimitives_state_next_exn_stamp t)) t)`,
  CHEAT_TAC);;

(* HOL4 evaluate_skipScript.sml:2413-2503: a proof *)

(* HOL4 evaluate_skipScript.sml:2505-2509: a proof *)

(* [local] *)
let state_rel_declare_env = prove
 (`evaluate_skip_state_rel l fr ft fe s t ==>
     (!env. declare_env (semanticPrimitives_state_eval_state s) env = NONE)
       /\
     (!env. declare_env (semanticPrimitives_state_eval_state t) env =
       NONE)`,
  CHEAT_TAC);;

(* HOL4 evaluate_skipScript.sml:2519-2523: a proof *)

(* HOL4 evaluate_skipScript.sml:2525-2534: a proof *)

(* HOL4 evaluate_skipScript.sml:2536-2543: a proof *)

(* HOL4 evaluate_skipScript.sml:2545-2560: a proof *)

(* HOL4 evaluate_skipScript.sml:2562: a proof *)

(* --------------------------------------------------------------------------
 *  top-level theorem
 * -------------------------------------------------------------------------- *)

let evaluate_decs_skip = prove
 (`!s env decs t s1 res fr ft fe env1 l.
     evaluate_evaluate_decs s env decs = (s1,res) /\
     evaluate_skip_state_rel l fr ft fe s t /\ evaluate_skip_env_rel fr ft
       fe env env1 ==>
     (?t1 res1 fr1 ft1 fe1.
       fr SUBMAP fr1 /\ ft SUBMAP ft1 /\ fe SUBMAP fe1 /\
       evaluate_evaluate_decs t env1 decs = (t1,res1) /\
       evaluate_skip_state_rel l fr1 ft1 fe1 s1 t1 /\
       res_rel (\env' env1'. evaluate_skip_env_rel fr1 ft1 fe1
         (extend_dec_env env' env)
                              (extend_dec_env env1' env1))
         (evaluate_skip_v_rel fr1 ft1 fe1) res res1)`,
  CHEAT_TAC);;

(* and the names it reads as variables are constants again *)
let _ = do_list unhide_constant
  ["id";
   "test"];;

(* and the interface *)
let _ = unhide_overloads ();;
