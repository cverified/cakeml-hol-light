(* ======================================================== *)
(*  ml_prog: ported from HOL4's
    translator/ml_progScript.sml
    A definition theory, with 24 definitions and 79 theorems.
    Needed by 24 files of the port.  *)
(* ======================================================== *)

(*
  Definitions and theorems supporting ml_progLib, which constructs a
  CakeML program and its semantic environment.
*)

needs "basis/pure/mlstring.ml";;
needs "lib/alist_tree.ml";;
needs "pancake/panLang.ml";;
needs "semantics/ast.ml";;
needs "semantics/evaluate.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/namespace.ml";;
needs "semantics/primTypes.ml";;
needs "semantics/proofs/evaluateProps.ml";;
needs "semantics/proofs/primSemEnv.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "translator/evaluate_dec.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "ml_prog"
  ["ast"; "evaluate"; "evaluateProps"; "evaluate_dec"; "mlstring";
   "namespace"; "primSemEnv"; "semanticPrimitives";
   "semanticPrimitivesProps"];;

let _ = do_list hide_constant ["Local"; "id"; "prog"];;
(* HOL4 ancestors outside the port: integer *)

(* --- env operators --- *)

(* Functions write, write_cons, write_mod, empty_env, merge_env should
   never be expanded by EVAL and are therefore defined using
   nocompute. These should never be exanded by EVAL because that would
   cause very slow appends. *)

let ml_prog_write_def = new_definition
  `ml_prog_write name v (env:semanticPrimitives_v sem_env) = sem_env_v_fupd
  (K (nsBind name v (sem_env_v env))) env`;;

let write_cons_def = new_definition
  `write_cons n d (env:semanticPrimitives_v sem_env) =
     (sem_env_c_fupd (K (nsAppend (nsSing n d) (sem_env_c env))) env)`;;

let ml_prog_empty_env_def = new_definition
  `(ml_prog_empty_env:semanticPrimitives_v sem_env) = mk_sem_env nsEmpty
  nsEmpty`;;

let write_mod_def = new_definition
  `write_mod mn (env:semanticPrimitives_v sem_env) env2 = sem_env_v_fupd (K
  (nsAppend (nsLift mn (sem_env_v env)) (sem_env_v env2))) (sem_env_c_fupd (K
  (nsAppend (nsLift mn (sem_env_c env)) (sem_env_c env2)))
     env2)`;;

let merge_env_def = new_definition
  `merge_env (env2:semanticPrimitives_v sem_env) env1 =
     mk_sem_env (nsAppend (sem_env_v env2) (sem_env_v env1)) (nsAppend
       (sem_env_c env2) (sem_env_c env1))`;;

(* the components of nsLookup are 'nicer' partial functions *)

let nsLookup_Short_def = new_definition
  `nsLookup_Short ns nm = nsLookup ns (Short nm)`;;

let nsLookup_Mod1_def = new_definition
  `nsLookup_Mod1 ns = (match ns with Bind _ ms -> ALOOKUP ms)`;;

let nsLookup_eq = prove
 (`nsLookup ns (Short nm) = nsLookup_Short ns nm /\
    nsLookup ns (Long mnm id) = (match nsLookup_Mod1 ns mnm with
      NONE -> NONE | SOME ns2 -> nsLookup ns2 id)`,
  CHEAT_TAC);;

(* base facts about the partial functions *)

let option_choice_f_apply = prove
 (`option_choice_f f g x = OPTION_CHOICE (f x) (g x)`,
  CHEAT_TAC);;

let nsLookup_Short_Bind = prove
 (`nsLookup_Short (Bind ss ms) = ALOOKUP ss`,
  CHEAT_TAC);;

let nsLookup_Short_nsAppend = prove
 (`nsLookup_Short (nsAppend ns1 ns2) = option_choice_f (nsLookup_Short ns1)
  (nsLookup_Short ns2)`,
  CHEAT_TAC);;

let nsLookup_Mod1_Bind = prove
 (`nsLookup_Mod1 (Bind ss ms) nm = ALOOKUP ms nm`,
  CHEAT_TAC);;

let nsLookup_Mod1_nsAppend = prove
 (`nsLookup_Mod1 (nsAppend ns1 ns2) = option_choice_f (nsLookup_Mod1 ns1)
  (nsLookup_Mod1 ns2)`,
  CHEAT_TAC);;

let nsLookup_Short_nsLift = prove
 (`nsLookup_Short (nsLift mnm ns) = ALOOKUP []`,
  CHEAT_TAC);;

let nsLookup_Mod1_nsLift = prove
 (`nsLookup_Mod1 (nsLift mnm ns) = ALOOKUP [(mnm,ns)]`,
  CHEAT_TAC);;

let nsLookup_pf_nsBind = prove
 (`nsLookup_Short (nsBind n v ns) = option_choice_f (ALOOKUP [(n,v)])
  (nsLookup_Short ns) /\
   nsLookup_Mod1 (nsBind n v ns) = nsLookup_Mod1 ns`,
  CHEAT_TAC);;

(* equalities on these partial functions for the various env operators *)

let nsLookup_write_eqs = prove
 (`nsLookup_Short (sem_env_c (ml_prog_write n v env)) = nsLookup_Short
  (sem_env_c env) /\
    nsLookup_Mod1 (sem_env_c (ml_prog_write n v env)) = nsLookup_Mod1
      (sem_env_c env) /\
    nsLookup_Mod1 (sem_env_v (ml_prog_write n v env)) = nsLookup_Mod1
      (sem_env_v env) /\
    nsLookup_Short (sem_env_v (ml_prog_write n v env)) = option_choice_f
      (ALOOKUP [(n,v)])
        (nsLookup_Short (sem_env_v env))`,
  CHEAT_TAC);;

let nsLookup_write_cons_eqs = prove
 (`nsLookup_Short (sem_env_v (write_cons n v env)) = nsLookup_Short (sem_env_v
  env) /\
    nsLookup_Mod1 (sem_env_v (write_cons n v env)) = nsLookup_Mod1
      (sem_env_v env) /\
    nsLookup_Mod1 (sem_env_c (write_cons n v env)) = nsLookup_Mod1
      (sem_env_c env) /\
    nsLookup_Short (sem_env_c (write_cons n v env)) = option_choice_f
      (ALOOKUP [(n,v)])
        (nsLookup_Short (sem_env_c env))`,
  CHEAT_TAC);;

let nsLookup_merge_env_eqs = prove
 (`nsLookup_Short (sem_env_v (merge_env env env2)) = option_choice_f
  (nsLookup_Short (sem_env_v env)) (nsLookup_Short (sem_env_v env2)) /\
    nsLookup_Mod1 (sem_env_v (merge_env env env2)) = option_choice_f
      (nsLookup_Mod1 (sem_env_v env)) (nsLookup_Mod1 (sem_env_v env2)) /\
    nsLookup_Short (sem_env_c (merge_env env env2)) = option_choice_f
      (nsLookup_Short (sem_env_c env)) (nsLookup_Short (sem_env_c env2)) /\
    nsLookup_Mod1 (sem_env_c (merge_env env env2)) = option_choice_f
      (nsLookup_Mod1 (sem_env_c env)) (nsLookup_Mod1 (sem_env_c env2))`,
  CHEAT_TAC);;

let nsLookup_write_mod_eqs = prove
 (`nsLookup_Short (sem_env_v (write_mod mnm env env2)) = nsLookup_Short
  (sem_env_v env2) /\
    nsLookup_Mod1 (sem_env_v (write_mod mnm env env2)) = option_choice_f
      (ALOOKUP [(mnm,sem_env_v env)]) (nsLookup_Mod1 (sem_env_v env2)) /\
    nsLookup_Short (sem_env_c (write_mod mnm env env2)) = nsLookup_Short
      (sem_env_c env2) /\
    nsLookup_Mod1 (sem_env_c (write_mod mnm env env2)) = option_choice_f
      (ALOOKUP [(mnm,sem_env_c env)]) (nsLookup_Mod1 (sem_env_c env2))`,
  CHEAT_TAC);;

let nsLookup_empty_eqs = prove
 (`nsLookup_Short (sem_env_v ml_prog_empty_env) = ALOOKUP [] /\
    nsLookup_Mod1 (sem_env_v ml_prog_empty_env) = ALOOKUP [] /\
    nsLookup_Short (sem_env_c ml_prog_empty_env) = ALOOKUP [] /\
    nsLookup_Mod1 (sem_env_c ml_prog_empty_env) = ALOOKUP []`,
  CHEAT_TAC);;

(* nonsense theorem instantiated when env's are defined *)

let nsLookup_eq_format = prove
 (`!(env:semanticPrimitives_v sem_env).
     (nsLookup_Short (sem_env_v env) = nsLookup_Short (sem_env_v env)) /\
     (nsLookup_Short (sem_env_c env) = nsLookup_Short (sem_env_c env)) /\
     (nsLookup_Mod1 (sem_env_v env) = nsLookup_Mod1 (sem_env_v env)) /\
     (nsLookup_Mod1 (sem_env_c env) = nsLookup_Mod1 (sem_env_c env))`,
  CHEAT_TAC);;

(* some shorthands that are allowed to EVAL are below *)

let write_rec_def = new_definition
  `write_rec funs env1 env =
     ITLIST (\f env. ml_prog_write (FST f) (semanticPrimitives_Recclosure
       env1 funs (FST f)) env) funs env`;;

let write_rec_thm = prove
 (`write_rec funs env1 env = sem_env_v_fupd (K
  (semanticPrimitives_build_rec_env funs env1 (sem_env_v env)))
    env`,
  CHEAT_TAC);;

let write_conses_def,write_conses_ind = define_guess
  `(write_conses [] env = env) /\
   (write_conses (CONS (n,y) xs) env =
      write_cons n y (write_conses xs env))`;;

let write_tdefs_def,write_tdefs_ind = define_guess
  `(write_tdefs n [] env = env) /\
   (write_tdefs n (CONS (x,_,condefs) tds) env =
      write_tdefs (n + 1) tds (write_conses (REVERSE (build_constrs n
          condefs)) env))`;;

(* [local] *)
let write_conses_v = prove
 (`!xs env. sem_env_v (write_conses xs env) = sem_env_v env`,
  CHEAT_TAC);;

(* [local] *)
let write_tdefs_lemma = prove
 (`!tds env n.
     write_tdefs n tds env =
     merge_env (mk_sem_env nsEmpty (build_tdefs n tds)) env`,
  CHEAT_TAC);;

let write_tdefs_thm = prove
 (`write_tdefs n tds ml_prog_empty_env =
    mk_sem_env nsEmpty (build_tdefs n tds)`,
  CHEAT_TAC);;

(* [local] *)
let merge_env_write_conses = prove
 (`!xs env. merge_env (write_conses xs env1) env2 =
            write_conses xs (merge_env env1 env2)`,
  CHEAT_TAC);;

(* [local] *)
let merge_env_write_tdefs = prove
 (`!tds n env1 env2.
     merge_env (write_tdefs n tds env1) env2 =
     write_tdefs n tds (merge_env env1 env2)`,
  CHEAT_TAC);;

(* it's not clear if these are still needed, but ml_progComputeLib and
   cfTacticsLib want them to be present. *)

(* [compute] *)
let nsLookup_nsAppend_Short = prove
 (`(nsLookup (nsAppend e1 e2) (Short id) =
   match nsLookup e1 (Short id) with
     NONE ->
       nsLookup e2 (Short id)
   | SOME v -> SOME v)`,
  CHEAT_TAC);;

(* [compute] *)
let write_simp = prove
 (`sem_env_c
      (ml_prog_write n v env) = sem_env_c env /\
       nsLookup (sem_env_v (ml_prog_write n v env)) (Short q) =
         (if n = q then SOME v else nsLookup (sem_env_v env) (Short q))`,
  CHEAT_TAC);;

(* [compute] *)
let write_cons_simp = prove
 (`sem_env_v
      (write_cons n v env) = sem_env_v env /\
       nsLookup (sem_env_c (write_cons n v env)) (Short q) =
         (if n = q then SOME v else nsLookup (sem_env_c env) (Short q))`,
  CHEAT_TAC);;

(* [compute] *)
let write_mod_simp = prove
 (`(nsLookup (sem_env_v (write_mod mn env env2)) (Short q) =
    nsLookup (sem_env_v env2) (Short q)) /\
   (nsLookup (sem_env_c (write_mod mn env env2)) (Short c) =
    nsLookup (sem_env_c env2) (Short c)) /\
   (nsLookup (sem_env_v (write_mod mn env env2)) (Long mn' r) =
    (if mn = mn' then nsLookup (sem_env_v env) r
    else nsLookup (sem_env_v env2) (Long mn' r))) /\
   (nsLookup (sem_env_c (write_mod mn env env2)) (Long mn' s) =
    (if mn = mn' then nsLookup (sem_env_c env) s
    else nsLookup (sem_env_c env2) (Long mn' s)))`,
  CHEAT_TAC);;

(* [compute] *)
let empty_simp = prove
 (`nsLookup (sem_env_v ml_prog_empty_env) q = NONE /\
   nsLookup (sem_env_c ml_prog_empty_env) q = NONE`,
  CHEAT_TAC);;
(* the components of nsLookup are 'nicer' partial functions *)

(* --- declarations --- *)

let decls_def = new_definition
  `Decls env s1 ds env2 s2 <=> semanticPrimitives_state_clock
     s1 = semanticPrimitives_state_clock s2 /\
     (?ck1 ck2. evaluate_dec_list (semanticPrimitives_state_clock_fupd (K
       ck1) s1) env ds =
                              (semanticPrimitives_state_clock_fupd (K
                                ck2) s2,Rval env2))`;;

let prog_def = new_definition
  `Prog env s1 ds env2 s2 <=> semanticPrimitives_state_clock
     s1 = semanticPrimitives_state_clock s2 /\
     (?ck1 ck2. evaluate_evaluate_decs (semanticPrimitives_state_clock_fupd
       (K ck1) s1) env ds =
                             (semanticPrimitives_state_clock_fupd (K ck2)
                               s2,Rval env2))`;;

let Decls_Dtype = prove
 (`!env s tds env2 s2 locs.
      Decls env s [Dtype locs tds] env2 s2 <=>
      ALL check_dup_ctors tds /\
      s2 = semanticPrimitives_state_next_type_stamp_fupd (K
        (semanticPrimitives_state_next_type_stamp s + LENGTH tds)) s /\
      env2 = write_tdefs (semanticPrimitives_state_next_type_stamp s) tds
        ml_prog_empty_env`,
  CHEAT_TAC);;

let Decls_Dexn = prove
 (`!env s n l env2 s2 locs.
      Decls env s [Dexn locs n l] env2 s2 <=>
      s2 = semanticPrimitives_state_next_exn_stamp_fupd (K
        (semanticPrimitives_state_next_exn_stamp s + 1)) s /\
      env2 = write_cons n (LENGTH l,ExnStamp
        (semanticPrimitives_state_next_exn_stamp s)) ml_prog_empty_env`,
  CHEAT_TAC);;

let Decls_Dtabbrev = prove
 (`!env s x y z env2 s2 locs.
      Decls env s [Dtabbrev locs x y z] env2 s2 <=>
      s2 = s /\ env2 = ml_prog_empty_env`,
  CHEAT_TAC);;

let eval_rel_def = new_definition
  `eval_rel s1 env e s2 x <=> semanticPrimitives_state_clock
     s1 = semanticPrimitives_state_clock s2 /\
     (?ck1 ck2.
        evaluate (semanticPrimitives_state_clock_fupd (K ck1) s1) env [e] =
                 (semanticPrimitives_state_clock_fupd (K ck2) s2,Rval
                   [x]))`;;

let eval_rel_alt = prove
 (`eval_rel s1 env e s2 x <=> semanticPrimitives_state_clock
    s2 = semanticPrimitives_state_clock s1 /\
    (?ck. evaluate (semanticPrimitives_state_clock_fupd (K ck) s1) env [e]
      = (s2,Rval [x]))`,
  CHEAT_TAC);;

let eval_list_rel_def = new_definition
  `eval_list_rel s1 env e s2 x <=> semanticPrimitives_state_clock
     s1 = semanticPrimitives_state_clock s2 /\
     (?ck1 ck2.
        evaluate (semanticPrimitives_state_clock_fupd (K ck1) s1) env e =
                 (semanticPrimitives_state_clock_fupd (K ck2) s2,Rval x))`;;

let eval_match_rel_def = new_definition
  `eval_match_rel s1 env v pats err_v s2 x <=> semanticPrimitives_state_clock
     s1 = semanticPrimitives_state_clock s2 /\
     (?ck1 ck2.
        evaluate_evaluate_match
                 (semanticPrimitives_state_clock_fupd (K ck1) s1) env v pats
                   err_v =
                 (semanticPrimitives_state_clock_fupd (K ck2) s2,Rval
                   [x]))`;;

(* Delays the write *)
let Decls_Dlet = prove
 (`!env s1 v e s2 env2 locs.
      Decls env s1 [Dlet locs (ast_Pvar v) e] env2 s2 <=>
      (?x. eval_rel s1 env e s2 x /\ (env2 = ml_prog_write v x
        ml_prog_empty_env))`,
  CHEAT_TAC);;

(* [local] *)
let FOLDR_LEMMA = prove
 (`!xs ys. APPEND (ITLIST (\(x1,x2,x3) x4. CONS (x1,f x1 x2 x3) x4) xs []) ys =
           ITLIST (\(x1,x2,x3) x4. CONS (x1,f x1 x2 x3) x4) xs ys`,
  CHEAT_TAC);;

(* Delays the write in build_rec_env *)
let Decls_Dletrec = prove
 (`!env s1 funs s2 env2 locs.
      Decls env s1 [Dletrec locs funs] env2 s2 <=>
      (s2 = s1) /\
      ALL_DISTINCT (MAP (\(x,y,z). x) funs) /\
      (env2 = write_rec funs env ml_prog_empty_env)`,
  CHEAT_TAC);;

let Decls_Dmod = prove
 (`Decls env1 s1 [Dmod mn ds] env2 s2 <=>
   (?s env.
      Decls env1 s1 ds env s /\ s2 = s /\
      env2 = write_mod mn env ml_prog_empty_env)`,
  CHEAT_TAC);;

let Decls_Dlocal = prove
 (`Decls env st lds env2 st2 ==>
    Decls (merge_env env2 env) st2 ds env3 st3 ==> Decls env st [Dlocal
      lds ds] env3 st3`,
  CHEAT_TAC);;

let Decls_Denv = prove
 (`!env s1 v s2 env2.
     Decls env s1 [Denv v] env2 s2 <=>
     (?env1 es.
       declare_env (semanticPrimitives_state_eval_state s1) env = SOME
         (env1,es) /\
       s2 = semanticPrimitives_state_eval_state_fupd (K es) s1 /\
       env2 = ml_prog_write v env1 ml_prog_empty_env)`,
  CHEAT_TAC);;

let Decls_NIL = prove
 (`!env s n l env2 s2.
      Decls env s [] env2 s2 <=>
      s2 = s /\ env2 = ml_prog_empty_env`,
  CHEAT_TAC);;

let Decls_CONS = prove
 (`!s1 s3 env1 d ds1 ds2 env3.
      Decls env1 s1 (CONS d ds2) env3 s3 =
      (?envA envB s2.
         Decls env1 s1 [d] envA s2 /\
         Decls (merge_env envA env1) s2 ds2 envB s3 /\
         env3 = merge_env envB envA)`,
  CHEAT_TAC);;

let merge_env_empty_env = prove
 (`merge_env env ml_prog_empty_env = env /\
   merge_env ml_prog_empty_env env = env`,
  CHEAT_TAC);;

let merge_env_assoc = prove
 (`merge_env env1 (merge_env env2 env3) = merge_env (merge_env env1 env2)
  env3`,
  CHEAT_TAC);;

let Decls_APPEND = prove
 (`!s1 s3 env1 ds1 ds2 env3.
      Decls env1 s1 (APPEND ds1 ds2) env3 s3 =
      (?envA envB s2.
         Decls env1 s1 ds1 envA s2 /\
         Decls (merge_env envA env1) s2 ds2 envB s3 /\
         env3 = merge_env envB envA)`,
  CHEAT_TAC);;

let Decls_SNOC = prove
 (`!s1 s3 env1 ds1 d env3.
      Decls env1 s1 (SNOC d ds1) env3 s3 =
      (?envA envB s2.
         Decls env1 s1 ds1 envA s2 /\
         Decls (merge_env envA env1) s2 [d] envB s3 /\
         env3 = merge_env envB envA)`,
  CHEAT_TAC);;

(* Decls_set_eval_state *)
let decls_set_eval_state = prove
 (`Decls env1 s1 ds env2 s2 /\ semanticPrimitives_state_eval_state s1 = NONE
  ==>
   (!es.
     Decls env1 (semanticPrimitives_state_eval_state_fupd (K es) s1) ds env2
                (semanticPrimitives_state_eval_state_fupd (K es) s2))`,
  CHEAT_TAC);;

(* The translator and CF tools use the following definition of ML_code
   to build (and verify) an ML program within the logic. The goal is to
   prove 'Decls' of the completed list of declarations. The program is
   constructed one statement at a time, with facts about the resulting
   environment built over time. There is a list of currently open blocks
   (e.g. struct and local constructs) so that the contents of modules and
   local objects can also be built up one statement at a time.
*)

let ML_code_env_def,ML_code_env_ind = define_guess
  `(ML_code_env env [] = env) /\
   (ML_code_env env (CONS (comm,st,decls,res_env) bls) = merge_env res_env
    (ML_code_env env bls))`;;

let ML_code_def,ML_code_ind = define_guess
  `(ML_code env [] res_st <=> T) /\
   (ML_code env (CONS ((comment:mlstring#mlstring),st,decls,res_env) bls)
    res_st <=>
         ML_code env bls st /\
         Decls (ML_code_env env bls) st decls res_env res_st)`;;

(* retreive the Decls from a toplevel ML_code *)
let ML_code_Decls = prove
 (`ML_code env1 [(comm,st1,prog,env2)] st2 ==>
     Decls env1 st1 prog env2 st2`,
  CHEAT_TAC);;

(* an empty program *)
(* HOL4 ml_progScript.sml:622: ML code, not ported *)

(* HOL4 ml_progScript.sml:624-633: the ML values that the definitions below
   antiquote *)
  (* init_env_def should not be unpacked by EVAL. Queries will be handled
     by the nsLookup_conv apparatus, which will use the pfun_eqs thm below. *)
let init_env_def = new_definition
  `init_env = (SND (THE (prim_sem_env (ARB:1 ffi_state))))`;;

let ml_prog_init_state_def = new_definition
  `ml_prog_init_state ffi = (FST (THE (prim_sem_env (ffi:'ffi ffi_state))))`;;
(* HOL4 ml_progScript.sml:643: ML code, not ported *)

let init_state_env_thm = prove
 (`THE (prim_sem_env ffi) = (ml_prog_init_state ffi,init_env)`,
  CHEAT_TAC);;

(* HOL4 ml_progScript.sml:651-657: a theorem that HOL4 states as the value
   of an ML expression: nsLookup_init_env_pfun_eqs *)

(* HOL4 ml_progScript.sml:659: ML code, not ported *)

let ML_code_NIL = prove
 (`ML_code init_env [(((implode "Toplevel"),(implode "")),ml_prog_init_state
  ffi,[],ml_prog_empty_env)]
    (ml_prog_init_state ffi)`,
  CHEAT_TAC);;

(* opening and closing of modules *)

let ML_code_new_block = prove
 (`!comm2. ML_code inp_env (CONS (comm,st,decls,env) bls) st2 ==>
    (let env2 = ML_code_env inp_env (CONS (comm,st,decls,env) bls) in
    ML_code inp_env (
        CONS (comm2,st2,[],ml_prog_empty_env) (CONS (comm,st,decls,env)
          bls)) st2)`,
  CHEAT_TAC);;

let ML_code_close_module = prove
 (`ML_code inp_env (
        CONS (((implode "Module"),mn),m_i_st,m_decls,m_env) (CONS
          (comm,st,decls,env) bls)) st2 ==> (let env2 = write_mod mn m_env env
          in ML_code inp_env (CONS (comm,st,SNOC (Dmod mn m_decls) decls,
            env2) bls) st2)`,
  CHEAT_TAC);;

let ML_code_close_local = prove
 (`ML_code inp_env (
        CONS (((implode "Local"),ln2),l2_i_st,l2_decls,l2_env)
        (CONS (((implode "Local"),ln1),l1_i_st,l1_decls,l1_env) (CONS
          (comm,st,decls,env) bls))) st2 ==> (let env2 = merge_env l2_env env
          in ML_code inp_env (CONS (comm,st,SNOC (Dlocal l1_decls l2_decls)
          decls,
            env2) bls) st2)`,
  CHEAT_TAC);;

(* appending a Dtype *)

let ML_code_Dtype = prove
 (`!tds locs. ML_code inp_env (CONS (comm,s1,prog,env2) bls) s2 ==>
     ALL check_dup_ctors tds ==>
     (let nts = semanticPrimitives_state_next_type_stamp s2 in
     let s3 = (semanticPrimitives_state_next_type_stamp_fupd (K (nts +
       LENGTH tds)) s2) in
     let env3 = write_tdefs nts tds env2 in
     ML_code inp_env (CONS (comm,s1,SNOC (Dtype locs tds) prog,env3) bls)
       s3)`,
  CHEAT_TAC);;

(* appending a Dexn *)

let ML_code_Dexn = prove
 (`!n l locs. ML_code inp_env (CONS (comm,s1,prog,env2) bls) s2 ==>
     (let nes = semanticPrimitives_state_next_exn_stamp s2 in
     let s3 = semanticPrimitives_state_next_exn_stamp_fupd (K (nes + 1)) s2
       in
     let env3 = write_cons n (LENGTH l,ExnStamp nes) env2 in
     ML_code inp_env (CONS (comm,s1,SNOC (Dexn locs n l) prog,env3) bls)
       s3)`,
  CHEAT_TAC);;

(* appending a Dtabbrev *)

let ML_code_Dtabbrev = prove
 (`!x y z locs. ML_code inp_env (CONS (comm,s1,prog,env2) bls) s2 ==>
     ML_code inp_env (CONS (comm,s1,SNOC (Dtabbrev locs x y z) prog,env2)
       bls)
       s2`,
  CHEAT_TAC);;

(* appending a Letrec *)

(* [local] *)
let build_rec_env_APPEND = prove
 (`nsAppend (semanticPrimitives_build_rec_env funs cl_env nsEmpty) add_to_env =
    semanticPrimitives_build_rec_env funs cl_env add_to_env`,
  CHEAT_TAC);;

let ML_code_Dletrec = prove
 (`!fns locs. ML_code env0 (CONS (comm,s1,prog,env2) bls) s2 ==>
      ALL_DISTINCT (MAP (\(x,y,z). x) fns) ==>
      (let code_env = ML_code_env env0 (CONS (comm,s1,prog,env2) bls) in
      let env3 = write_rec fns code_env env2 in
      ML_code env0 (CONS (comm,s1,SNOC (Dletrec locs fns) prog,env3) bls)
        s2)`,
  CHEAT_TAC);;

(* appending a Let *)

let ML_code_Dlet_var = prove
 (`!cenv e s3 x n locs. ML_code env0 (CONS (comm,s1,prog,env1) bls) s2 ==>
     eval_rel s2 cenv e s3 x ==>
     cenv = ML_code_env env0 (CONS (comm,s1,prog,env1) bls) ==>
     (let env2 = ml_prog_write n x env1 in let s3_abbrev = s3 in
     ML_code env0 (
         CONS (comm,s1,SNOC (Dlet locs (ast_Pvar n) e) prog,env2) bls)
           s3_abbrev)`,
  CHEAT_TAC);;

let ML_code_Dlet_var_lit = prove
 (`!loc name l. ML_code env0 (CONS (comm,s1,prog,env1) bls) s2 ==>
     (let env2 = ml_prog_write name (semanticPrimitives_Litv l) env1 in let
       s3_abbrev = s2 in
       ML_code env0 (CONS (comm,s1,SNOC (Dlet loc (ast_Pvar name) (ast_Lit
         l)) prog,env2) bls) s3_abbrev)`,
  CHEAT_TAC);;

let ML_code_Dlet_Fun = prove
 (`!n v e locs. ML_code env0 (CONS (comm,s1,prog,env1) bls) s2 ==>
     (let code_env = ML_code_env env0 (CONS (comm,s1,prog,env1) bls) in
     let v_abbrev = semanticPrimitives_Closure code_env v e in
     let env2 = ml_prog_write n v_abbrev env1 in
     ML_code env0 (CONS (comm,s1,SNOC (Dlet locs (ast_Pvar n) (ast_Fun v e))
       prog,
         env2) bls) s2)`,
  CHEAT_TAC);;

let ML_code_Dlet_Var_Var = prove
 (`!n vname locs. ML_code env0 (CONS (comm,s1,prog,env1) bls) s2 ==>
     (let cenv = ML_code_env env0 (CONS (comm,s1,prog,env1) bls) in
     !x. nsLookup (sem_env_v cenv) vname = SOME x ==>
     (let env2 = ml_prog_write n x env1 in
     ML_code env0 (
         CONS (comm,s1,SNOC (Dlet locs (ast_Pvar n) (ast_Var vname))
           prog,env2) bls) s2))`,
  CHEAT_TAC);;

let ML_code_Dlet_Var_Ref_Var = prove
 (`!n vname locs. ML_code env0 (CONS (comm,s1,prog,env1) bls) s2 ==>
     (let cenv = ML_code_env env0 (CONS (comm,s1,prog,env1) bls) in
     !x. nsLookup (sem_env_v cenv) vname = SOME x ==>
     (let len = LENGTH (semanticPrimitives_state_refs s2) in
     let loc = semanticPrimitives_Loc T len in
     let env2 = ml_prog_write n loc env1 in
     let s2_abbrev = semanticPrimitives_state_refs_fupd (K (APPEND
       (semanticPrimitives_state_refs s2) [semanticPrimitives_Refv x])) s2 in
     ML_code env0 (
         CONS (comm,s1,SNOC (Dlet locs (ast_Pvar n) (ast_App ast_Opref
           [ast_Var vname])) prog,env2) bls) s2_abbrev))`,
  CHEAT_TAC);;

(* appending an environment *)

let declare_env_rel_def = new_definition
  `declare_env_rel s2 env1 s3 envv <=>
   (?es.
     declare_env (semanticPrimitives_state_eval_state s2) env1 = SOME
       (envv,es) /\
     s3 = semanticPrimitives_state_eval_state_fupd (K es) s2)`;;

let ML_code_Denv = prove
 (`!n cenv s3 envv.
     ML_code env0 (CONS (comm,s1,prog,env1) bls) s2 ==>
     declare_env_rel s2 cenv s3 envv ==>
     cenv = ML_code_env env0 (CONS (comm,s1,prog,env1) bls) ==>
     (let
       env2 = ml_prog_write n envv env1 in let
       s3_abbrev = s3 in
     ML_code env0 (CONS (comm,s1,SNOC (Denv n) prog,env2) bls) s3_abbrev)`,
  CHEAT_TAC);;

(* setting the eval_state *)

let ML_code_set_eval_state = prove
 (`// only supported at the top-level for simplicity
   ML_code env0 [(comm,s1,prog,env1)] s2 ==>
     semanticPrimitives_state_eval_state
   s1 = NONE ==>
   (!es. ML_code env0 [(comm,semanticPrimitives_state_eval_state_fupd (K
     (SOME es)) s1,prog,env1)]
                           (semanticPrimitives_state_eval_state_fupd (K
                             (SOME es)) s2))`,
  CHEAT_TAC);;

(* lookup function definitions *)

let ml_prog_lookup_var_def = new_definition
  `ml_prog_lookup_var name (env:semanticPrimitives_v sem_env) = nsLookup
  (sem_env_v env) (Short name)`;;

let lookup_cons_def = new_definition
  `lookup_cons name (env:semanticPrimitives_v sem_env) = nsLookup (sem_env_c
  env) name`;;

(* the old lookup formulation worked via nsLookup/mod_defined,
   and mod_defined is still used in various characteristic scripts
   so we supply an eval theorem that maps to the new approach. *)

let mod_defined_def = new_definition
  `mod_defined env n =
     (?p1 p2 e3. ~(p1 = []) /\ id_to_mods n = APPEND p1 p2 /\
       nsLookupMod env p1 = SOME e3)`;;

(* [compute] *)
let mod_defined_nsLookup_Mod1 = prove
 (`mod_defined env id = (match id with Short _ -> F
        | Long mn _ -> (match nsLookup_Mod1 env mn with NONE -> F | _ ->
          T))`,
  CHEAT_TAC);;

(* theorems about old lookup functions *)
(* FIXME: everything below this line is unlikely to be needed. *)

(* [local] *)
let nsLookupMod_nsBind = prove
 (`~(p = []) ==>
     nsLookupMod (nsBind k v env) p = nsLookupMod env p`,
  CHEAT_TAC);;

let nsLookup_write = prove
 (`(nsLookup (sem_env_v (ml_prog_write n v env)) (Short name) =
       (if n = name then SOME v else nsLookup (sem_env_v env) (Short name)))
         /\
   (nsLookup (sem_env_v (ml_prog_write n v env)) (Long mn lname) =
       nsLookup (sem_env_v env) (Long mn lname)) /\
   (nsLookup (sem_env_c (ml_prog_write n v env)) a = nsLookup (sem_env_c
     env) a) /\
   (mod_defined (sem_env_v (ml_prog_write n v env)) x = mod_defined
     (sem_env_v env) x) /\
   (mod_defined (sem_env_c (ml_prog_write n v env)) x = mod_defined
     (sem_env_c env) x)`,
  CHEAT_TAC);;

let nsLookup_write_cons = prove
 (`(nsLookup (sem_env_v (write_cons n v env)) a = nsLookup (sem_env_v env) a)
  /\
   (nsLookup (sem_env_c (write_cons n d env)) (Short name) =
     (if name = n then SOME d else nsLookup (sem_env_c env) (Short name)))
       /\
   (mod_defined (sem_env_v (write_cons n d env)) x = mod_defined (sem_env_v
     env) x) /\
   (mod_defined (sem_env_c (write_cons n d env)) x = mod_defined (sem_env_c
     env) x) /\
   (nsLookup (sem_env_c (write_cons n d env)) (Long mn lname) =
    nsLookup (sem_env_c env) (Long mn lname))`,
  CHEAT_TAC);;

let nsLookup_empty = prove
 (`(nsLookup (sem_env_v ml_prog_empty_env) a = NONE) /\
   (nsLookup (sem_env_c ml_prog_empty_env) b = NONE) /\
   (mod_defined (sem_env_v ml_prog_empty_env) x = F) /\
   (mod_defined (sem_env_c ml_prog_empty_env) x = F)`,
  CHEAT_TAC);;

let nsLookupMod_nsAppend = prove
 (`nsLookupMod (nsAppend env1 env2) p =
     if p = [] then SOME (nsAppend env1 env2)
     else match nsLookupMod env1 p with
         SOME v -> SOME v
       | NONE ->
         if (?p1 p2 e3. ~(p1 = []) /\ p = APPEND p1 p2 /\ nsLookupMod env1
           p1 = SOME e3) then NONE
         else nsLookupMod env2 p`,
  CHEAT_TAC);;

let nsLookup_write_mod = prove
 (`(nsLookup (sem_env_v (write_mod mn env1 env2)) (Short n) =
    nsLookup (sem_env_v env2) (Short n)) /\
   (nsLookup (sem_env_c (write_mod mn env1 env2)) (Short n) =
    nsLookup (sem_env_c env2) (Short n)) /\
   (mod_defined (sem_env_v (write_mod mn env1 env2)) (Long mn' r) =
     ((mn = mn') \/ mod_defined (sem_env_v env2) (Long mn' r))) /\
   (mod_defined (sem_env_c (write_mod mn env1 env2)) (Long mn' r) =
     (if mn = mn' then T
     else mod_defined (sem_env_c env2) (Long mn' r))) /\
   (nsLookup (sem_env_v (write_mod mn env1 env2)) (Long mn1 ln) =
    (if mn = mn1 then nsLookup (sem_env_v env1) ln else nsLookup (sem_env_v
      env2) (Long mn1 ln))) /\
   (nsLookup (sem_env_c (write_mod mn env1 env2)) (Long mn1 ln) =
    (if mn = mn1 then nsLookup (sem_env_c env1) ln else nsLookup
      (sem_env_c env2) (Long mn1 ln)))`,
  CHEAT_TAC);;

let nsLookup_merge_env = prove
 (`(nsLookup (sem_env_v (merge_env e1 e2)) (Short n) =
      (match nsLookup (sem_env_v e1) (Short n) with NONE -> nsLookup
        (sem_env_v e2) (Short n)
      | SOME x -> SOME x)) /\
   (nsLookup (sem_env_c (merge_env e1 e2)) (Short n) =
      (match nsLookup (sem_env_c e1) (Short n) with NONE -> nsLookup
        (sem_env_c e2) (Short n)
      | SOME x -> SOME x)) /\
   (nsLookup (sem_env_v (merge_env e1 e2)) (Long mn ln) =
      (match nsLookup (sem_env_v e1) (Long mn ln) with NONE -> if
        mod_defined (sem_env_v e1) (Long mn ln) then NONE
                else nsLookup (sem_env_v e2) (Long mn ln)
      | SOME x -> SOME x)) /\
   (nsLookup (sem_env_c (merge_env e1 e2)) (Long mn ln) =
      (match nsLookup (sem_env_c e1) (Long mn ln) with NONE -> if
        mod_defined (sem_env_c e1) (Long mn ln) then NONE
                else nsLookup (sem_env_c e2) (Long mn ln)
      | SOME x -> SOME x)) /\
   (mod_defined (sem_env_v (merge_env e1 e2)) x =
   (mod_defined (sem_env_v e1) x \/ mod_defined (sem_env_v e2) x)) /\
   (mod_defined (sem_env_c (merge_env e1 e2)) x =
   (mod_defined (sem_env_c e1) x \/ mod_defined (sem_env_c e2) x))`,
  CHEAT_TAC);;

(* [compute] *)
let nsLookup_nsBind_compute = prove
 (`(nsLookup (nsBind n v e) (Short n1) =
    (if n = n1 then SOME v else nsLookup e (Short n1))) /\
   (nsLookup (nsBind n v e) (Long l1 l2) = nsLookup e (Long l1 l2))`,
  CHEAT_TAC);;

(* [compute] *)
let nsLookup_nsAppend =
  SIMP_RULE [] (CAKE_INST [`mk_sem_env e1v e1c`,`e1`; `mk_sem_env e2v
  e2c`,`e2`] (SIMP_RULE [merge_env_def] nsLookup_merge_env));;

(* Base case for mod_defined (?) *)
(* [compute] *)
let mod_defined_base = prove
 (`mod_defined (Bind _ []) _ = F`,
  CHEAT_TAC);;


(* --- the rest of this file might be unused junk --- *)

(* misc theorems about lookup functions *)

(* No idea why this is sparated out *)
let lookup_var_write = prove
 (`(ml_prog_lookup_var v (ml_prog_write w x env) = (if v = w then SOME x else
  ml_prog_lookup_var v env)) /\
    (nsLookup (sem_env_v (ml_prog_write w x env)) (Short v) =
       (if v = w then SOME x else nsLookup (sem_env_v env) (Short v))) /\
   (nsLookup (sem_env_v (ml_prog_write w x env)) (Long mn lname) =
       nsLookup (sem_env_v env) (Long mn lname)) /\
    (lookup_cons name (ml_prog_write w x env) = lookup_cons name env)`,
  CHEAT_TAC);;

let lookup_var_write_mod = prove
 (`(ml_prog_lookup_var v (write_mod mn e1 env) = ml_prog_lookup_var v env) /\
   (lookup_cons (Long mn1 (Short name)) (write_mod mn2 e1 env) =
    (if mn1 = mn2 then
      lookup_cons (Short name) e1
    else lookup_cons (Long mn1 (Short name)) env)) /\
   (lookup_cons (Short name) (write_mod mn2 e1 env) =
    lookup_cons (Short name) env)`,
  CHEAT_TAC);;

let lookup_var_write_cons = prove
 (`(ml_prog_lookup_var v (write_cons n d env) = ml_prog_lookup_var v env) /\
   (lookup_cons (Short name) (write_cons n d env) =
     (if name = n then SOME d else lookup_cons (Short name) env)) /\
   (lookup_cons (Long l full_name) (write_cons n d env) =
    lookup_cons (Long l full_name) env) /\
   (nsLookup (sem_env_v (write_cons n d env)) x = nsLookup (sem_env_v env)
     x)`,
  CHEAT_TAC);;

let lookup_var_empty_env = prove
 (`(ml_prog_lookup_var v ml_prog_empty_env = NONE) /\
    (nsLookup (sem_env_v ml_prog_empty_env) (Short k) = NONE) /\
    (nsLookup (sem_env_v ml_prog_empty_env) (Long mn m) = NONE) /\
    (lookup_cons name ml_prog_empty_env = NONE)`,
  CHEAT_TAC);;

(* HOL4 ml_progScript.sml:1181-1200: code that the source has in a comment *)

let prog_syntax_ok_def = new_definition
  `prog_syntax_ok prog = IS_SOME (check_cons_dec_list (sem_env_c init_env)
  prog)`;;

let prog_syntax_ok_isPREFIX = prove
 (`!p1 p2. prog_syntax_ok p1 /\ isPREFIX p2 p1 ==> prog_syntax_ok p2`,
  CHEAT_TAC);;

let Decls_IMP_Prog = prove
 (`Decls init_env s1 ds env2 s2 ==>
   prog_syntax_ok ds ==>
   Prog init_env s1 ds env2 s2`,
  CHEAT_TAC);;

let prog_syntax_ok_semantics = prove
 (`prog_syntax_ok prog ==>
   semantics_dec_list st init_env prog = semantics_prog st init_env prog`,
  CHEAT_TAC);;

(* and the names it reads as variables are constants again *)
let _ = do_list unhide_constant
  ["Local";
   "id";
   "prog"];;

(* and the interface *)
let _ = unhide_overloads ();;
