(* ======================================================== *)
(*  evaluate_dec: ported from HOL4's
    translator/evaluate_decScript.sml
    A definition theory, with 5 definitions and 13 theorems.  Needed
    by backend_asm.ml, basis_ffi.ml, cfMain.ml, compiler32Prog.ml,
    compiler64Prog.ml and ml_prog.ml.  *)
(* ======================================================== *)

(*
  Defines evaluate_dec_list which is an alternative version of
  evaluate_decs from evaluateTheory.  This alternative version is
  adjusted to make translation faster.
*)

needs "basis/pure/mlstring.ml";;
needs "lib/alist_tree.ml";;
needs "lib/lprefix_lub.ml";;
needs "lib/sptree.ml";;
needs "semantics/ast.ml";;
needs "semantics/evaluate.ml";;
needs "semantics/namespace.ml";;
needs "semantics/proofs/evaluateProps.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;
needs "semantics/semanticPrimitives.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "evaluate_dec"
  ["ast"; "evaluate"; "evaluateProps"; "mlstring"; "namespace";
   "semanticPrimitives"; "semanticPrimitivesProps"];;
(* HOL4 ancestors outside the port: integer *)


(* --- define an alternative to evaluate_decs --- *)

(* Same as evaluate_decs from evaluateTheory but modified to not have
   the cons checks (every_exp one_con_check) *)
(* the termination relation that HOL4 gives is
     MEASURE (list_size dec_size o SND o SND)
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
let evaluate_dec_list_def,evaluate_dec_list_ind = define_guess
  `(evaluate_dec_list st env [] = (st,Rval (mk_sem_env nsEmpty nsEmpty))) /\
   (evaluate_dec_list st env (CONS d1 (CONS d2 ds)) =
      (match evaluate_dec_list st env [d1] with
         (st1,Rval env1) ->
           (match evaluate_dec_list st1 (extend_dec_env env1 env) (CONS d2
               ds) with
              (st2,r) -> (st2,combine_dec_result env1 r))
       | (st1,Rerr v7) -> (st1,Rerr v7))) /\
   (evaluate_dec_list st env [Dlet locs p e] =
      (if ALL_DISTINCT (ast_pat_bindings p) then
         match evaluate st env [e] with
           (st',Rval v) ->
             (st',
              (match semanticPrimitives_pmatch (sem_env_c env)
                  (semanticPrimitives_state_refs st') p (HD v) [] with
                No_match -> Rerr (Rraise semanticPrimitives_bind_exn_v)
              | Match_type_error -> Rerr (Rabort Rtype_error)
              | Match new_vals ->
                Rval (mk_sem_env (alist_to_ns new_vals) nsEmpty)))
         | (st',Rerr err) -> (st',Rerr err)
       else (st,Rerr (Rabort Rtype_error)))) /\
   (evaluate_dec_list st env [Dletrec locs funs] =
      (st,
       (if ALL_DISTINCT (MAP (\(x,y,z). x) funs) then
         Rval (mk_sem_env (semanticPrimitives_build_rec_env funs env
             nsEmpty) nsEmpty)
       else Rerr (Rabort Rtype_error)))) /\
   (evaluate_dec_list st env [Dtype locs tds] =
      (if ALL check_dup_ctors tds then
         (semanticPrimitives_state_next_type_stamp_fupd (K
             (semanticPrimitives_state_next_type_stamp st + LENGTH tds)) st,
          Rval (mk_sem_env nsEmpty (build_tdefs
              (semanticPrimitives_state_next_type_stamp st) tds)))
       else (st,Rerr (Rabort Rtype_error)))) /\
   (evaluate_dec_list st env [Dtabbrev locs tvs tn t] =
      (st,Rval (mk_sem_env nsEmpty nsEmpty))) /\
   (evaluate_dec_list st env [Denv n] =
      (match declare_env (semanticPrimitives_state_eval_state st) env with
         NONE -> (st,Rerr (Rabort Rtype_error))
       | SOME (x,es') ->
         (semanticPrimitives_state_eval_state_fupd (K es') st,Rval
             (mk_sem_env (nsSing n x) nsEmpty)))) /\
   (evaluate_dec_list st env [Dexn locs cn ts] =
      (semanticPrimitives_state_next_exn_stamp_fupd (K
          (semanticPrimitives_state_next_exn_stamp st + 1)) st,
       Rval
         (mk_sem_env nsEmpty (nsSing cn (LENGTH ts,ExnStamp
             (semanticPrimitives_state_next_exn_stamp st)))))) /\
   (evaluate_dec_list st env [Dmod mn ds] =
      (match evaluate_dec_list st env ds with
         (st',r) ->
           (st',
            (match r with
              Rval env' ->
                Rval (mk_sem_env (nsLift mn (sem_env_v env')) (nsLift mn
                    (sem_env_c env')))
            | Rerr err -> Rerr err)))) /\
   (evaluate_dec_list st env [Dlocal lds ds] =
      match evaluate_dec_list st env lds with
        (st1,Rval env1) -> evaluate_dec_list st1 (extend_dec_env env1 env)
            ds
      | (st1,Rerr v7) -> (st1,Rerr v7))`;;

let evaluate_dec_list_with_clock_def = new_definition
  `evaluate_dec_list_with_clock st env k prog =
     (let (st',r) =
       evaluate_dec_list (semanticPrimitives_state_clock_fupd (K k) st)
         env prog in (semanticPrimitives_state_ffi st',r))`;;

let semantics_dec_list_def = define_cases
  `(semantics_dec_list st env prog (ffi_Terminate outcome io_list) <=>
        (
         // there is a clock for which evaluation terminates, either internally or via
         // FFI, and the accumulated io events match the given io_list
         ?k ffi r.
          evaluate_dec_list_with_clock st env k prog = (ffi,r) /\
          (match r with Rerr (Rabort (Rffi_error outcome')) ->
             outcome = ffi_FFI_outcome (outcome')
           | r -> ~(r = Rerr (Rabort Rtimeout_error)) /\ outcome =
               ffi_Success) /\
          (io_list = ffi_state_io_events ffi) /\
          (~(r = Rerr (Rabort Rtype_error))))) /\
   (semantics_dec_list st env prog (ffi_Diverge io_trace) <=>
        (
         // for all clocks, evaluation times out
         !k. ?ffi.
          (evaluate_dec_list_with_clock st env k prog =
              (ffi,Rerr (Rabort Rtimeout_error)))) /\
         // the io_trace is the least upper bound of the set of traces
         // produced for each clock
         lprefix_lub
           (IMAGE
             (\k. fromList (ffi_state_io_events (FST
                 (evaluate_dec_list_with_clock st env k prog))))
             UNIV)
           io_trace) /\
   (semantics_dec_list st env prog ffi_Fail <=>
        // there is a clock for which evaluation produces a runtime type error
        (?k.
          SND (evaluate_dec_list_with_clock st env k prog) = Rerr
              (Rabort Rtype_error)))`;;

(* HOL4 evaluate_decScript.sml:124: the ML values that the definitions below
   antiquote *)

(* --- define a check that implies evaluate_dec_list is same as evalaute_decs --- *)

(* the termination relation that HOL4 gives is
     MEASURE (\x. match x with INL (_,ds) -> list_size dec_size ds
                                   | INR (_,d) -> dec_size d)
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
let check_cons_dec_list_def,check_cons_dec_list_ind = define_guess
  `(check_cons_dec_list (env_c:(mlstring,mlstring,num#stamp)namespace) [] =
    SOME nsEmpty) /\
   (check_cons_dec_list (env_c:(mlstring,mlstring,num#stamp)namespace) (CONS d1
    ds) =
      (match check_cons_dec env_c d1 with NONE -> NONE
       | SOME env_c0 ->
         (match check_cons_dec_list (nsAppend env_c0 env_c) ds with NONE ->
             NONE
         | SOME env_c1 -> SOME (nsAppend env_c1 env_c0)))) /\
   (check_cons_dec (env_c:(mlstring,mlstring,num#stamp)namespace) (Dlet locs p
    e) =
      (if ast_every_exp (one_con_check env_c) e then SOME nsEmpty else
          NONE)) /\
   (check_cons_dec (env_c:(mlstring,mlstring,num#stamp)namespace) (Dletrec locs
    funs) =
      (if ALL (\(f,n,e). ast_every_exp (one_con_check env_c) e) funs
          then SOME nsEmpty else NONE)) /\
   (check_cons_dec (env_c:(mlstring,mlstring,num#stamp)namespace) (Dtype locs
    tds) =
      (SOME (build_tdefs 0 tds))) /\
   (check_cons_dec (env_c:(mlstring,mlstring,num#stamp)namespace) (Dtabbrev
    locs tvs tn t) = SOME nsEmpty) /\
   (check_cons_dec (env_c:(mlstring,mlstring,num#stamp)namespace) (Denv _)
    = SOME nsEmpty) /\
   (check_cons_dec (env_c:(mlstring,mlstring,num#stamp)namespace) (Dexn locs cn
    ts) =
      SOME (nsSing cn (LENGTH ts,ExnStamp 0))) /\
   (check_cons_dec (env_c:(mlstring,mlstring,num#stamp)namespace) (Dmod mn ds)
    =
      (match check_cons_dec_list env_c ds with NONE -> NONE
       | SOME env_c0 -> SOME (nsLift mn env_c0))) /\
   (check_cons_dec (env_c:(mlstring,mlstring,num#stamp)namespace) (Dlocal lds
    ds) =
      match check_cons_dec_list env_c lds with NONE -> NONE
      | SOME env_c0 -> check_cons_dec_list (nsAppend env_c0 env_c) ds)`;;

let check_cons_dec_list_isPREFIX = prove
 (`!env_c xs ys x.
     check_cons_dec_list env_c xs = SOME x /\ isPREFIX ys xs ==>
     (?y. check_cons_dec_list env_c ys = SOME y)`,
  CHEAT_TAC);;

(* [local] *)
let check_cons_dec_list_sing = prove
 (`check_cons_dec_list env_c [d] = check_cons_dec env_c d`,
  CHEAT_TAC);;
add_simp check_cons_dec_list_sing;;

(* --- theorems --- *)

let con_check_eqv_def = new_definition
  `con_check_eqv (x:(mlstring,mlstring,num#stamp)namespace)
  (y:(mlstring,mlstring,num#stamp)namespace) <=>
     (match (x,y) with (Bind xs ys,Bind xs1 ys1) ->
          ALL2 (\(a,x1,_) (b,y1,_). a = b /\ x1 = y1) xs xs1 /\
          ALL2 (\(a,x1) (b,y1). a = b /\ con_check_eqv x1 y1) ys ys1)`;;

(* [local] *)
let con_check_eqv_refl = prove
 (`!x. con_check_eqv x x`,
  CHEAT_TAC);;
add_simp con_check_eqv_refl;;

let con_check_eqv_nsAppend = prove
 (`con_check_eqv x1 y1 /\ con_check_eqv x2 y2 ==>
   con_check_eqv (nsAppend x1 x2) (nsAppend y1 y2)`,
  CHEAT_TAC);;

let con_check_eqv_switch = prove
 (`con_check_eqv env2 env1 ==>
   ast_every_exp (one_con_check env1) e = ast_every_exp (one_con_check
     env2) e`,
  CHEAT_TAC);;

(* [local] *)
let con_check_eqv_build_tdefs = prove
 (`!m n. con_check_eqv (build_tdefs m tds) (build_tdefs n tds)`,
  CHEAT_TAC);;

let evaluate_dec_list_eq_evaluate_decs = prove
 (`!(st:'ffi semanticPrimitives_state) env ds st1 res.
     IS_SOME (check_cons_dec_list (sem_env_c env) ds) ==>
     evaluate_dec_list st env ds = evaluate_evaluate_decs st env ds`,
  CHEAT_TAC);;

let evaluate_dec_list_set_clock = prove
 (`!s env decs s1 res.
     evaluate_dec_list s env decs = (s1,res) /\ ~(res = Rerr (Rabort
       Rtimeout_error)) ==>
     (!ck. ?ck1.
            evaluate_dec_list (semanticPrimitives_state_clock_fupd (K ck1)
              s) env decs =
            (semanticPrimitives_state_clock_fupd (K ck) s1,res))`,
  CHEAT_TAC);;

let evaluate_dec_list_cons = prove
 (`!s env d ds.
     evaluate_dec_list s env (CONS d ds) =
     match evaluate_dec_list s env [d] with (s1,Rval env1) ->
         (match evaluate_dec_list s1 (extend_dec_env env1 env) ds with
            (s2,r) -> (s2,combine_dec_result env1 r))
     | (s1,Rerr v7) -> (s1,Rerr v7)`,
  CHEAT_TAC);;

let evaluate_dec_list_append = prove
 (`!s env xs ds.
     evaluate_dec_list s env (APPEND xs ds) =
     match evaluate_dec_list s env xs with (s1,Rval env1) ->
         (match evaluate_dec_list s1 (extend_dec_env env1 env) ds with
            (s2,r) -> (s2,combine_dec_result env1 r))
     | (s1,Rerr v7) -> (s1,Rerr v7)`,
  CHEAT_TAC);;

let evaluate_dec_list_add_to_clock = prove
 (`!s e p s' r extra.
     evaluate_dec_list s e p = (s',r) /\ ~(r = Rerr (Rabort Rtimeout_error))
       ==>
     evaluate_dec_list (semanticPrimitives_state_clock_fupd (K
       (semanticPrimitives_state_clock s + extra)) s) e p =
     (semanticPrimitives_state_clock_fupd (K
       (semanticPrimitives_state_clock s' + extra)) s',r)`,
  CHEAT_TAC);;

let eval_dec_list_no_eval_simulation = prove
 (`!s env decs s' res.
     evaluate_dec_list s env decs = (s',res)
       /\ semanticPrimitives_state_eval_state s = NONE /\ ~(res = Rerr (Rabort
       Rtype_error)) ==> semanticPrimitives_state_eval_state
     s' = NONE /\
     evaluate_dec_list (semanticPrimitives_state_eval_state_fupd (K es) s)
       env decs =
     (semanticPrimitives_state_eval_state_fupd (K es) s',res)`,
  CHEAT_TAC);;

let evaluate_dec_list_call_FFI_rel_imp = prove
 (`!s e p s' r. evaluate_dec_list s e p = (s',r) ==> RTC call_FFI_rel
  (semanticPrimitives_state_ffi s) (semanticPrimitives_state_ffi s')`,
  CHEAT_TAC);;

(* and the interface *)
let _ = unhide_overloads ();;
