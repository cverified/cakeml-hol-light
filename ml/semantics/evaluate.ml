(* ======================================================== *)
(*  evaluate: ported from HOL4's
    semantics/evaluateScript.sml
    A definition theory, with 6 definitions and 13 theorems.  Needed
    by 31 files of the port.  *)
(* ======================================================== *)

(*
  Functional big-step semantics for evaluation of CakeML programs.
*)

needs "semantics/ast.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/fpSem.ml";;
needs "semantics/namespace.ml";;
needs "semantics/semanticPrimitives.ml";;

(* the theories whose names the Ancestors blocks of the source
   bring, which are the ones that its statements read: the
   overloads of every other theory come out of the interface
   while this file loads *)
let _ = hol4_ancestors "evaluate"
  ["ast"; "ffi"; "fpSem"; "namespace"; "semanticPrimitives"];;

(* The semantics is defined here using fix_clock so that HOL4 generates
 * provable termination conditions. However, after termination is proved, we
 * clean up the definition (in HOL4) to remove occurrences of fix_clock. *)

let fix_clock_def = new_definition
  `evaluate_fix_clock s (s',res) =
     (semanticPrimitives_state_clock_fupd (K (if
       semanticPrimitives_state_clock s' <=
       semanticPrimitives_state_clock s then
       semanticPrimitives_state_clock s' else
       semanticPrimitives_state_clock s)) s',res)`;;
hol4_overload "fix_clock" "evaluate_fix_clock";;

let dec_clock_def = new_definition
  `evaluate_dec_clock s = (semanticPrimitives_state_clock_fupd (K
  (semanticPrimitives_state_clock s - 1)) s)`;;
hol4_overload "dec_clock" "evaluate_dec_clock";;

let do_eval_res_def = new_definition
  `do_eval_res vs s =
     (match semanticPrimitives_do_eval vs
       (semanticPrimitives_state_eval_state s) with NONE -> (s,Rerr
       (Rabort Rtype_error)) | SOME (env1,decs,es1) ->
       (semanticPrimitives_state_eval_state_fupd (K es1) s,Rval
       (env1,decs)))`;;

(* list_result is equivalent to map_result (\v. [v]) I, where map_result is
 * defined in evalPropsTheory *)
let list_result_def = define_cases
  [`list_result (Rval v) = Rval [v]`;
   `list_result (Rerr e) = Rerr e`];;

(* [local] *)
let fix_clock_IMP = prove
 (`evaluate_fix_clock s x = (s1,res) ==>
  semanticPrimitives_state_clock s1 <= semanticPrimitives_state_clock
  s`,
  CHEAT_TAC);;

(* list_size_REVERSE[local] *)
let evaluate_list_size_REVERSE = prove
 (`!xs. list_size f (REVERSE xs) = list_size f xs`,
  CHEAT_TAC);;

let sing_env_def = new_definition
  `sing_env n v =
     (mk_sem_env (nsBind n v nsEmpty) nsEmpty:semanticPrimitives_v
       sem_env)`;;

let _ = size_thms "ast_exp";;
let _ = size_thms "ast_pat";;
let _ = size_thms "dec";;
(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 evaluateScript.sml:268-277: the tactic that proves the
   termination *)
let evaluate_def = define_mutual_wf
  `inv_image ((<) LEX (<))
       (\x. match x with INL (s,_1,es) ->
         (semanticPrimitives_state_clock s,list_size ast_exp_size es) |
         INR (INL (s,_2,_3,pes,_4)) -> (semanticPrimitives_state_clock
         s,list_size (pair_size ast_pat_size ast_exp_size) pes) | INR
         (INR (s,_5,ds)) -> (semanticPrimitives_state_clock s,list_size
         dec_size ds))`
  [`evaluate (st:'ffi semanticPrimitives_state) env [] = ((st:'ffi
  semanticPrimitives_state),Rval [])`;
   `evaluate (st:'ffi semanticPrimitives_state) env (e1 :: e2 :: es) =
      (match evaluate_fix_clock st (evaluate st env [e1]) with
         (st',Rval v1) ->
           (match evaluate st' env (e2 :: es) with
              (st'',Rval vs) -> (st'',Rval (HD v1 :: vs)) |
                (st'',Rerr v8) -> (st'',Rerr v8)) | (st',Rerr v10) ->
                (st',Rerr v10))`;
   `evaluate (st:'ffi semanticPrimitives_state) env [(ast_Lit
  l:ast_exp)] = (st,Rval [semanticPrimitives_Litv l])`;
   `evaluate (st:'ffi semanticPrimitives_state) env [(ast_Raise
  e:ast_exp)] =
      (match evaluate st env [e] with
         (st',Rval v) -> (st',Rerr (Rraise (HD v))) | (st',Rerr
           v8) -> (st',Rerr v8))`;
   `evaluate (st:'ffi semanticPrimitives_state) env [(ast_Handle e
  pes:ast_exp)] =
      (match evaluate_fix_clock st (evaluate st env [e]) with
         (st',Rval v7) -> (st',Rval v7) | (st',Rerr (Rraise v)) ->
         (if can_pmatch_all (sem_env_c env)
           (semanticPrimitives_state_refs st') (MAP FST pes) v then
           evaluate_evaluate_match st' env v pes v else (st',Rerr
             (Rabort Rtype_error))) | (st',Rerr (Rabort v12)) ->
             (st',Rerr (Rabort v12)))`;
   `evaluate (st:'ffi semanticPrimitives_state) env [(ast_Con cn
  es:ast_exp)] =
      (if do_con_check (sem_env_c env) cn (LENGTH es) then
         match evaluate st env (REVERSE es) with
           (st',Rval vs) ->
             (match build_conv (sem_env_c env) cn (REVERSE vs) with
                NONE -> (st',Rerr (Rabort Rtype_error)) | SOME v
                  -> (st',Rval [v])) | (st',Rerr v8) -> (st',Rerr v8)
                  else (st,Rerr (Rabort Rtype_error)))`;
   `evaluate (st:'ffi semanticPrimitives_state) env [(ast_Var
  n:ast_exp)] =
      (match nsLookup (sem_env_v env) n with
         NONE -> (st,Rerr (Rabort Rtype_error)) | SOME v ->
           (st,Rval [v]))`;
   `evaluate (st:'ffi semanticPrimitives_state) env [(ast_Fun x
  e:ast_exp)] = (st,Rval [semanticPrimitives_Closure env x e])`;
   `evaluate (st:'ffi semanticPrimitives_state) env [(ast_App op
  es:ast_exp)] =
     (match evaluate_fix_clock st (evaluate st env (REVERSE es))
       with
      (st',Rval vs) ->
      (match (getOpClass op) with
        ast_FunApp ->
          (match semanticPrimitives_do_opapp (REVERSE vs) with
            SOME (env',e) ->
              (if semanticPrimitives_state_clock st' = 0 then
                (st',Rerr (Rabort Rtimeout_error)) else
                evaluate (evaluate_dec_clock st') env' [e]) | NONE
                  -> (st',Rerr (Rabort Rtype_error))) | ast_Force ->
          (match semanticPrimitives_dest_thunk (REVERSE vs)
            (semanticPrimitives_state_refs st') with
            semanticPrimitives_BadRef -> (st',Rerr (Rabort Rtype_error))
            | semanticPrimitives_NotThunk -> (st',Rerr (Rabort
            Rtype_error)) | semanticPrimitives_IsThunk Evaluated v ->
            (st',Rval [v]) | semanticPrimitives_IsThunk NotEvaluated f
            ->
              (match semanticPrimitives_do_opapp [f;
                semanticPrimitives_Conv NONE []] with SOME (env',e) ->
                   (if semanticPrimitives_state_clock st' = 0 then
                     (st',Rerr (Rabort Rtimeout_error)) else
                     (match evaluate (evaluate_dec_clock st') env'
                       [e] with (st2,Rval vs2) ->
                          (match semanticPrimitives_update_thunk
                            (REVERSE vs) (semanticPrimitives_state_refs
                            st2) vs2 with NONE -> (st2,Rerr (Rabort
                            Rtype_error)) | SOME refs ->
                            (semanticPrimitives_state_refs_fupd (K refs)
                            st2,Rval vs2)) | (st2,Rerr e) -> (st2,Rerr
                            e))) | NONE -> (st',Rerr (Rabort
                            Rtype_error)))) | ast_EvalOp ->
          (match evaluate_fix_clock st' (do_eval_res (REVERSE vs)
            st') with
            (st1,Rval (env1,decs)) ->
              (if semanticPrimitives_state_clock st1 = 0 then
                (st1,Rerr (Rabort Rtimeout_error)) else
                (match evaluate_fix_clock (evaluate_dec_clock st1)
                        (evaluate_evaluate_decs (evaluate_dec_clock
                          st1) env1 decs) with
                  (st2,Rval env2) -> (match declare_env
                    (semanticPrimitives_state_eval_state st2)
                    (extend_dec_env env2 env1) with
                    SOME (x,es2) ->
                      ((semanticPrimitives_state_eval_state_fupd (K
                      (reset_env_generation
                        (semanticPrimitives_state_eval_state st') es2))
                        st2),Rval [x]) | NONE -> (st2,Rerr (Rabort
                        Rtype_error))) | (st2,Rerr (Rabort a)) ->
                        (st2,Rerr (Rabort a)) | (st2,Rerr e) ->
                        ((semanticPrimitives_state_eval_state_fupd (K
                    (reset_env_generation
                      (semanticPrimitives_state_eval_state st')
                      (semanticPrimitives_state_eval_state st2)))
                      st2),Rerr e))) | (st1,Rerr e) -> (st1,Rerr e)) |
                      ast_Simple ->
          (match semanticPrimitives_do_app
            (semanticPrimitives_state_refs
            st',semanticPrimitives_state_ffi st') op (REVERSE vs) with
            NONE -> (st',Rerr (Rabort Rtype_error)) | SOME
              ((refs,ffi),r) ->
              ((semanticPrimitives_state_ffi_fupd (K ffi)
                (semanticPrimitives_state_refs_fupd (K refs)
                st')),list_result r))) | res -> res)`;
   `evaluate (st:'ffi semanticPrimitives_state) env [ast_Log lop e1 e2]
  =
      (match evaluate_fix_clock st (evaluate st env [e1]) with
         (st',Rval v1) ->
           (match do_log lop (HD v1) e2 with
              NONE -> (st',Rerr (Rabort Rtype_error)) | SOME (Exp
                e) -> evaluate st' env [e] | SOME (Val v) ->
                (st',Rval [v])) | (st',Rerr v9) -> (st',Rerr v9))`;
   `evaluate (st:'ffi semanticPrimitives_state) env [(ast_If e1 e2
  e3:ast_exp)] =
      (match evaluate_fix_clock st (evaluate st env [e1]) with
         (st',Rval v) ->
           (match semanticPrimitives_do_if (HD v) e2 e3 with
              NONE -> (st',Rerr (Rabort Rtype_error)) | SOME e ->
                evaluate st' env [e]) | (st',Rerr v8) -> (st',Rerr
                v8))`;
   `evaluate (st:'ffi semanticPrimitives_state) env [(ast_Mat e
  pes:ast_exp)] =
      (match evaluate_fix_clock st (evaluate st env [e]) with
         (st',Rval v) ->
           (if can_pmatch_all (sem_env_c env)
             (semanticPrimitives_state_refs st') (MAP FST pes) (HD v)
             then
             evaluate_evaluate_match st' env (HD v) pes
               semanticPrimitives_bind_exn_v else (st',Rerr (Rabort
               Rtype_error))) | (st',Rerr v8) -> (st',Rerr v8))`;
   `evaluate (st:'ffi semanticPrimitives_state) env [(ast_Let xo e1
  e2:ast_exp)] =
      (match evaluate_fix_clock st (evaluate st env [e1]) with
         (st',Rval v) ->
           evaluate st' (sem_env_v_fupd (K (nsOptBind xo (HD v)
             (sem_env_v env))) env) [e2] | (st',Rerr v8) -> (st',Rerr
             v8))`;
   `evaluate (st:'ffi semanticPrimitives_state) env [(ast_Letrec funs
  e:ast_exp)] =
      (if ALL_DISTINCT (MAP (\(x,y,z). x) funs) then
         evaluate st (sem_env_v_fupd (K
           (semanticPrimitives_build_rec_env funs env (sem_env_v
           env))) env) [e] else (st,Rerr (Rabort Rtype_error)))`;
   `evaluate (st:'ffi semanticPrimitives_state) env [ast_Tannot e t]
  = evaluate st env [e]`;
   `evaluate (st:'ffi semanticPrimitives_state) env [ast_Lannot e l]
  = evaluate st env [e]`;
   `evaluate_evaluate_match (st:'ffi semanticPrimitives_state) env v
  [] err_v = (st,Rerr (Rraise err_v))`;
   `evaluate_evaluate_match (st:'ffi semanticPrimitives_state) env v
  ((p,e) :: pes) err_v =
      (if ALL_DISTINCT (ast_pat_bindings p) then
         match semanticPrimitives_pmatch (sem_env_c env)
           (semanticPrimitives_state_refs st) p v [] with
           No_match -> evaluate_evaluate_match st env v pes err_v |
             Match_type_error -> (st,Rerr (Rabort Rtype_error)) | Match
             env_v' ->
           evaluate st (sem_env_v_fupd (K (nsAppend (alist_to_ns
             env_v') (sem_env_v env))) env) [e] else (st,Rerr (Rabort
             Rtype_error)))`;
   `evaluate_evaluate_decs (st:'ffi semanticPrimitives_state) env []
  = (st,Rval (mk_sem_env nsEmpty nsEmpty))`;
   `evaluate_evaluate_decs (st:'ffi semanticPrimitives_state) env (d1 ::
  d2 :: ds) =
      (match evaluate_fix_clock st (evaluate_evaluate_decs st env
        [d1]) with
         (st1,Rval env1) ->
           (match evaluate_evaluate_decs st1 (extend_dec_env env1
             env) (d2 :: ds) with
              (st2,r) -> (st2,combine_dec_result env1 r)) |
                (st1,Rerr v7) -> (st1,Rerr v7))`;
   `evaluate_evaluate_decs (st:'ffi semanticPrimitives_state) env [Dlet
  locs p e] =
      (if ALL_DISTINCT (ast_pat_bindings p) /\
          every_exp (one_con_check (sem_env_c env)) e then
         match evaluate st env [e] with
           (st',Rval v) ->
             (st',
              (match semanticPrimitives_pmatch (sem_env_c env)
                (semanticPrimitives_state_refs st') p (HD v) [] with
                No_match -> Rerr (Rraise
                  semanticPrimitives_bind_exn_v) | Match_type_error ->
                  Rerr (Rabort Rtype_error) | Match new_vals ->
                Rval (mk_sem_env (alist_to_ns new_vals)
                  nsEmpty))) | (st',Rerr err) -> (st',Rerr err) else
                  (st,Rerr (Rabort Rtype_error)))`;
   `evaluate_evaluate_decs (st:'ffi semanticPrimitives_state) env
  [Dletrec locs funs] =
      (st,
       (if ALL_DISTINCT (MAP (\(x,y,z). x) funs) /\
          EVERY (\(f,n,e). every_exp (one_con_check (sem_env_c env))
            e) funs then
         Rval (mk_sem_env (semanticPrimitives_build_rec_env funs
           env nsEmpty) nsEmpty) else Rerr (Rabort Rtype_error)))`;
   `evaluate_evaluate_decs (st:'ffi semanticPrimitives_state) env [Dtype
  locs tds] =
      (if EVERY check_dup_ctors tds then
         (semanticPrimitives_state_next_type_stamp_fupd (K
           (semanticPrimitives_state_next_type_stamp st + LENGTH tds))
           st,
          Rval (mk_sem_env nsEmpty (build_tdefs
            (semanticPrimitives_state_next_type_stamp st) tds))) else
            (st,Rerr (Rabort Rtype_error)))`;
   `evaluate_evaluate_decs (st:'ffi semanticPrimitives_state) env
  [Dtabbrev locs tvs tn t] =
      (st,Rval (mk_sem_env nsEmpty nsEmpty))`;
   `evaluate_evaluate_decs (st:'ffi semanticPrimitives_state) env [Denv
  n] =
      (match declare_env (semanticPrimitives_state_eval_state st)
        env with
         NONE -> (st,Rerr (Rabort Rtype_error)) | SOME (x,es') ->
         (semanticPrimitives_state_eval_state_fupd (K es')
           st,Rval (mk_sem_env (nsSing n x) nsEmpty)))`;
   `evaluate_evaluate_decs (st:'ffi semanticPrimitives_state) env [Dexn
  locs cn ts] =
      (semanticPrimitives_state_next_exn_stamp_fupd (K
        (semanticPrimitives_state_next_exn_stamp st + 1)) st,
       Rval
         (mk_sem_env nsEmpty (nsSing cn (LENGTH ts,ExnStamp
           (semanticPrimitives_state_next_exn_stamp st)))))`;
   `evaluate_evaluate_decs (st:'ffi semanticPrimitives_state) env [Dmod
  mn ds] =
      (match evaluate_evaluate_decs st env ds with
         (st',r) ->
           (st',
            (match r with
              Rval env' ->
                Rval (mk_sem_env (nsLift mn (sem_env_v env'))
                  (nsLift mn (sem_env_c env'))) | Rerr err -> Rerr
                  err)))`;
   `evaluate_evaluate_decs (st:'ffi semanticPrimitives_state) env
  [Dlocal lds ds] =
      (match evaluate_fix_clock st (evaluate_evaluate_decs st env
        lds) with
        (st1,Rval env1) -> evaluate_evaluate_decs st1
          (extend_dec_env env1 env) ds | (st1,Rerr v7) -> (st1,Rerr
          v7))`];;
hol4_overload "evaluate" "evaluate";;
hol4_overload "evaluate_decs" "evaluate_evaluate_decs";;
hol4_overload "evaluate_match" "evaluate_evaluate_match";;

(* tidy up evalute_def and evaluate_ind *)

let evaluate_clock = prove
 (`(!(s1:'ffi semanticPrimitives_state) env e r s2.
      evaluate s1 env e = (s2,r) ==> semanticPrimitives_state_clock
        s2 <= semanticPrimitives_state_clock s1) /\
   (!(s1:'ffi semanticPrimitives_state) env v p v' r s2.
      evaluate_evaluate_match s1 env v p v' = (s2,r) ==>
        semanticPrimitives_state_clock s2 <=
        semanticPrimitives_state_clock s1) /\
   (!(s1:'ffi semanticPrimitives_state) env ds r s2.
      evaluate_evaluate_decs s1 env ds = (s2,r) ==>
        semanticPrimitives_state_clock s2 <=
        semanticPrimitives_state_clock s1)`,
  CHEAT_TAC);;

let fix_clock_do_eval_res = prove
 (`evaluate_fix_clock s (do_eval_res vs s) = do_eval_res vs s`,
  CHEAT_TAC);;

let fix_clock_evaluate = prove
 (`evaluate_fix_clock s1 (evaluate s1 env e) = evaluate s1 env e /\
   evaluate_fix_clock s1 (evaluate_evaluate_decs s1 env ds) =
     evaluate_evaluate_decs s1 env ds`,
  CHEAT_TAC);;

(* HOL4 evaluateScript.sml:314-315: a theorem that HOL4 states as the
   value of an ML expression: full_evaluate_def *)

(* HOL4 evaluateScript.sml:317-318: a theorem that HOL4 states as the
   value of an ML expression: full_evaluate_ind *)

(* store evaluate_def and evaluate_ind in parts *)

(* HOL4 evaluateScript.sml:322-326: the ML values that the
   definitions below antiquote *)

(* HOL4 evaluateScript.sml:328-332: the ML values that the
   definitions below antiquote *)

(* HOL4 evaluateScript.sml:334-338: the ML values that the
   definitions below antiquote *)

(* HOL4 evaluateScript.sml:340: a theorem that HOL4 states as the
   value of an ML expression: evaluate_def *)

(* HOL4 evaluateScript.sml:342: a theorem that HOL4 states as the
   value of an ML expression: evaluate_match_def *)

(* HOL4 evaluateScript.sml:344: a theorem that HOL4 states as the
   value of an ML expression: evaluate_decs_def *)

(* HOL4 evaluateScript.sml:346-350: a theorem that HOL4 states as the
   value of an ML expression: evaluate_ind *)

(* HOL4 evaluateScript.sml:352-356: a theorem that HOL4 states as the
   value of an ML expression: evaluate_match_ind *)

(* HOL4 evaluateScript.sml:358-362: a theorem that HOL4 states as the
   value of an ML expression: evaluate_decs_ind *)

(* and the overloads that this file cannot see are back in the
   interface *)
let _ = unhide_overloads ();;
