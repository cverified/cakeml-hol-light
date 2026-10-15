(* ======================================================== *)
(*  evaluate: ported from HOL4's
    semantics/evaluateScript.sml  *)
(* ======================================================== *)

(*
  Functional big-step semantics for evaluation of CakeML programs.
*)

needs "semantics/ast.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/fpSem.ml";;
needs "semantics/namespace.ml";;
needs "semantics/semanticPrimitives.ml";;

(* The semantics is defined here using fix_clock so that HOL4 generates
 * provable termination conditions. However, after termination is
   proved, we
 * clean up the definition (in HOL4) to remove occurrences of fix_clock.
   *)

let fix_clock_def = cake_define
  `evaluate_fix_clock s (s',res) =
     (semanticPrimitives_state_clock_fupd (K (if
       semanticPrimitives_state_clock s' <=
       semanticPrimitives_state_clock s then
       semanticPrimitives_state_clock s' else
       semanticPrimitives_state_clock s)) s',res)`;;
hol4_overload "fix_clock" "evaluate_fix_clock";;

let dec_clock_def = cake_define
  `evaluate_dec_clock s = (semanticPrimitives_state_clock_fupd (K
  (semanticPrimitives_state_clock s - 1)) s)`;;
hol4_overload "dec_clock" "evaluate_dec_clock";;

let do_eval_res_def = cake_define
  `do_eval_res vs s =
     (match do_eval vs (semanticPrimitives_state_eval_state s)
       with NONE -> (s,Rerr (Rabort Rtype_error)) | SOME
       (env1,decs,es1) -> (semanticPrimitives_state_eval_state_fupd
       (K es1) s,Rval (env1,decs)))`;;

(* list_result is equivalent to map_result (\v. [v]) I, where map_result
   is
 * defined in evalPropsTheory *)
let list_result_def = cake_define_list
  [`list_result (Rval v:semanticPrimitives_result) = Rval [v]`;
   `list_result (Rerr e:semanticPrimitives_result) = Rerr e`];;

let sing_env_def = cake_define
  `sing_env n v =
     (mk_sem_env (nsBind n v nsEmpty) nsEmpty:semanticPrimitives_v
       sem_env)`;;

let evaluate_def = cake_define_list
  [`evaluate st env [] = ((st:'ffi semanticPrimitives_state),Rval [])`;
   `evaluate st env (e1 :: e2 :: es) =
      (match fix_clock st (evaluate st env [e1]) with
         (st',Rval v1) ->
           (match evaluate st' env (e2 :: es) with
              (st'',Rval vs) -> (st'',Rval (HD v1 :: vs)) |
                (st'',Rerr v8) -> (st'',Rerr v8)) | (st',Rerr v10) ->
                (st',Rerr v10))`;
   `evaluate st env [(Lit l:ast_exp)] = (st,Rval [Litv l])`;
   `evaluate st env [(Raise e:ast_exp)] =
      (match evaluate st env [e] with
         (st',Rval v) -> (st',Rerr (Rraise (HD v))) | (st',Rerr
           v8) -> (st',Rerr v8))`;
   `evaluate st env [(Handle e pes:ast_exp)] =
      (match fix_clock st (evaluate st env [e]) with
         (st',Rval v7) -> (st',Rval v7) | (st',Rerr (Rraise v)) ->
         (if can_pmatch_all (sem_env_c env)
           (semanticPrimitives_state_refs st') (MAP FST pes) v then
           evaluate_evaluate_match st' env v pes v else (st',Rerr
             (Rabort Rtype_error))) | (st',Rerr (Rabort v12)) ->
             (st',Rerr (Rabort v12)))`;
   `evaluate st env [(Con cn es:ast_exp)] =
      (if do_con_check (sem_env_c env) cn (LENGTH es) then
         match evaluate st env (REVERSE es) with
           (st',Rval vs) ->
             (match build_conv (sem_env_c env) cn (REVERSE vs) with
                NONE -> (st',Rerr (Rabort Rtype_error)) | SOME v
                  -> (st',Rval [v])) | (st',Rerr v8) -> (st',Rerr v8)
                  else (st,Rerr (Rabort Rtype_error)))`;
   `evaluate st env [(Var n:ast_exp)] =
      (match nsLookup (sem_env_v env) n with
         NONE -> (st,Rerr (Rabort Rtype_error)) | SOME v ->
           (st,Rval [v]))`;
   `evaluate st env [(Fun x e:ast_exp)] = (st,Rval [Closure env x e])`;
   `evaluate st env [(App op es:ast_exp)] =
     (match fix_clock st (evaluate st env (REVERSE es)) with
      (st',Rval vs) ->
      (match (getOpClass op) with
        FunApp ->
          (match do_opapp (REVERSE vs) with
            SOME (env',e) ->
              (if semanticPrimitives_state_clock st' = 0 then
                (st',Rerr (Rabort Rtimeout_error)) else
                evaluate (dec_clock st') env' [e]) | NONE ->
                  (st',Rerr (Rabort Rtype_error))) | Force ->
          (match dest_thunk (REVERSE vs)
            (semanticPrimitives_state_refs st') with BadRef -> (st',Rerr
            (Rabort Rtype_error)) | NotThunk -> (st',Rerr (Rabort
            Rtype_error)) | IsThunk Evaluated v -> (st',Rval [v]) |
            IsThunk NotEvaluated f ->
              (match do_opapp [f; Conv NONE []] with SOME (env',e)
                ->
                   (if semanticPrimitives_state_clock st' = 0 then
                     (st',Rerr (Rabort Rtimeout_error)) else
                     (match evaluate (dec_clock st') env' [e] with
                       (st2,Rval vs2) ->
                          (match update_thunk (REVERSE vs)
                            (semanticPrimitives_state_refs st2) vs2 with
                            NONE -> (st2,Rerr (Rabort Rtype_error)) |
                            SOME refs ->
                            (semanticPrimitives_state_refs_fupd (K refs)
                            st2,Rval vs2)) | (st2,Rerr e) -> (st2,Rerr
                            e))) | NONE -> (st',Rerr (Rabort
                            Rtype_error)))) | EvalOp ->
          (match fix_clock st' (do_eval_res (REVERSE vs) st') with
            (st1,Rval (env1,decs)) ->
              (if semanticPrimitives_state_clock st1 = 0 then
                (st1,Rerr (Rabort Rtimeout_error)) else
                (match fix_clock (dec_clock st1)
                        (evaluate_evaluate_decs (dec_clock st1) env1
                          decs) with
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
                      Simple ->
          (match do_app (semanticPrimitives_state_refs
            st',semanticPrimitives_state_ffi st') op (REVERSE vs) with
            NONE -> (st',Rerr (Rabort Rtype_error)) | SOME
              ((refs,ffi),r) ->
              ((semanticPrimitives_state_ffi_fupd (K ffi)
                (semanticPrimitives_state_refs_fupd (K refs)
                st')),list_result r))) | res -> res)`;
   `evaluate st env [(Log lop e1 e2:ast_exp)] =
      (match fix_clock st (evaluate st env [e1]) with
         (st',Rval v1) ->
           (match do_log lop (HD v1) e2 with
              NONE -> (st',Rerr (Rabort Rtype_error)) | SOME (Exp
                e) -> evaluate st' env [e] | SOME (Val v) ->
                (st',Rval [v])) | (st',Rerr v9) -> (st',Rerr v9))`;
   `evaluate st env [(If e1 e2 e3:ast_exp)] =
      (match fix_clock st (evaluate st env [e1]) with
         (st',Rval v) ->
           (match do_if (HD v) e2 e3 with
              NONE -> (st',Rerr (Rabort Rtype_error)) | SOME e ->
                evaluate st' env [e]) | (st',Rerr v8) -> (st',Rerr
                v8))`;
   `evaluate st env [(Mat e pes:ast_exp)] =
      (match fix_clock st (evaluate st env [e]) with
         (st',Rval v) ->
           (if can_pmatch_all (sem_env_c env)
             (semanticPrimitives_state_refs st') (MAP FST pes) (HD v)
             then
             evaluate_evaluate_match st' env (HD v) pes
               bind_exn_v else (st',Rerr (Rabort Rtype_error))) |
               (st',Rerr v8) -> (st',Rerr v8))`;
   `evaluate st env [(Let xo e1 e2:ast_exp)] =
      (match fix_clock st (evaluate st env [e1]) with
         (st',Rval v) ->
           evaluate st' (sem_env_v_fupd (K (nsOptBind xo (HD v)
             (sem_env_v env))) env) [e2] | (st',Rerr v8) -> (st',Rerr
             v8))`;
   `evaluate st env [(Letrec funs e:ast_exp)] =
      (if ALL_DISTINCT (MAP (\(x,y,z). x) funs) then
         evaluate st (sem_env_v_fupd (K (build_rec_env funs env
           (sem_env_v env))) env) [e] else (st,Rerr (Rabort
           Rtype_error)))`;
   `evaluate st env [(Tannot e t:ast_exp)] = evaluate st env [e]`;
   `evaluate st env [(Lannot e l:ast_exp)] = evaluate st env [e]`;
   `evaluate_evaluate_match st env v [] err_v = (st,Rerr (Rraise
  err_v))`;
   `evaluate_evaluate_match st env v ((p,e) :: pes) err_v =
      (if ALL_DISTINCT (pat_bindings p) then
         match pmatch (sem_env_c env) (semanticPrimitives_state_refs
           st) p v [] with
           No_match -> evaluate_evaluate_match st env v pes err_v |
             Match_type_error -> (st,Rerr (Rabort Rtype_error)) | Match
             env_v' ->
           evaluate st (sem_env_v_fupd (K (nsAppend (alist_to_ns
             env_v') (sem_env_v env))) env) [e] else (st,Rerr (Rabort
             Rtype_error)))`;
   `evaluate_evaluate_decs st env [] = (st,Rval (mk_sem_env nsEmpty
  nsEmpty))`;
   `evaluate_evaluate_decs st env (d1 :: d2 :: ds) =
      (match fix_clock st (evaluate_evaluate_decs st env [d1]) with
         (st1,Rval env1) ->
           (match evaluate_evaluate_decs st1 (extend_dec_env env1
             env) (d2 :: ds) with
              (st2,r) -> (st2,combine_dec_result env1 r)) |
                (st1,Rerr v7) -> (st1,Rerr v7))`;
   `evaluate_evaluate_decs st env [(Dlet locs p e:dec)] =
      (if ALL_DISTINCT (pat_bindings p) /\
          every_exp (one_con_check (sem_env_c env)) e then
         match evaluate st env [e] with
           (st',Rval v) ->
             (st',
              (match pmatch (sem_env_c env)
                (semanticPrimitives_state_refs st') p (HD v) [] with
                No_match -> Rerr (Rraise bind_exn_v) |
                  Match_type_error -> Rerr (Rabort Rtype_error) | Match
                  new_vals ->
                Rval (mk_sem_env (alist_to_ns new_vals)
                  nsEmpty))) | (st',Rerr err) -> (st',Rerr err) else
                  (st,Rerr (Rabort Rtype_error)))`;
   `evaluate_evaluate_decs st env [(Dletrec locs funs:dec)] =
      (st,
       (if ALL_DISTINCT (MAP (\(x,y,z). x) funs) /\
          EVERY (\(f,n,e). every_exp (one_con_check (sem_env_c env))
            e) funs then
         Rval (mk_sem_env (build_rec_env funs env nsEmpty)
           nsEmpty) else Rerr (Rabort Rtype_error)))`;
   `evaluate_evaluate_decs st env [(Dtype locs tds:dec)] =
      (if EVERY check_dup_ctors tds then
         (semanticPrimitives_state_next_type_stamp_fupd (K
           (semanticPrimitives_state_next_type_stamp st + LENGTH tds))
           st,
          Rval (mk_sem_env nsEmpty (build_tdefs
            (semanticPrimitives_state_next_type_stamp st) tds))) else
            (st,Rerr (Rabort Rtype_error)))`;
   `evaluate_evaluate_decs st env [(Dtabbrev locs tvs tn t:dec)] =
      (st,Rval (mk_sem_env nsEmpty nsEmpty))`;
   `evaluate_evaluate_decs st env [(Denv n:dec)] =
      (match declare_env (semanticPrimitives_state_eval_state st)
        env with
         NONE -> (st,Rerr (Rabort Rtype_error)) | SOME (x,es') ->
         (semanticPrimitives_state_eval_state_fupd (K es')
           st,Rval (mk_sem_env (nsSing n x) nsEmpty)))`;
   `evaluate_evaluate_decs st env [(Dexn locs cn ts:dec)] =
      (semanticPrimitives_state_next_exn_stamp_fupd (K
        (semanticPrimitives_state_next_exn_stamp st + 1)) st,
       Rval
         (mk_sem_env nsEmpty (nsSing cn (LENGTH ts,ExnStamp
           (semanticPrimitives_state_next_exn_stamp st)))))`;
   `evaluate_evaluate_decs st env [(Dmod mn ds:dec)] =
      (match evaluate_evaluate_decs st env ds with
         (st',r) ->
           (st',
            (match r with
              Rval env' ->
                Rval (mk_sem_env (nsLift mn (sem_env_v env'))
                  (nsLift mn (sem_env_c env'))) | Rerr err -> Rerr
                  err)))`;
   `evaluate_evaluate_decs st env [(Dlocal lds ds:dec)] =
      (match fix_clock st (evaluate_evaluate_decs st env lds) with
        (st1,Rval env1) -> evaluate_evaluate_decs st1
          (extend_dec_env env1 env) ds | (st1,Rerr v7) -> (st1,Rerr
          v7))`];;
hol4_overload "evaluate_decs" "evaluate_evaluate_decs";;
hol4_overload "evaluate_match" "evaluate_evaluate_match";;

(* tidy up evalute_def and evaluate_ind *)

(* store evaluate_def and evaluate_ind in parts *)

(* HOL4 ML code, not ported:
val eval_pat = “evaluate$evaluate _ _ _”
val evaluate_conjs =
  CONJUNCTS full_evaluate_def
  |> filter (fn th => (th |> SPEC_ALL |> concl |> dest_eq |> fst
                          |> can (match_term eval_pat)));
*)

(* HOL4 ML code, not ported:
val match_pat = “evaluate$evaluate_match _ _ _ _ _”
val evaluate_match_conjs =
  CONJUNCTS full_evaluate_def
  |> filter (fn th => (th |> SPEC_ALL |> concl |> dest_eq |> fst
                          |> can (match_term match_pat)));
*)

(* HOL4 ML code, not ported:
val decs_pat = “evaluate$evaluate_decs _ _ _”
val evaluate_decs_conjs =
  CONJUNCTS full_evaluate_def
  |> filter (fn th => (th |> SPEC_ALL |> concl |> dest_eq |> fst
                          |> can (match_term decs_pat)));
*)
