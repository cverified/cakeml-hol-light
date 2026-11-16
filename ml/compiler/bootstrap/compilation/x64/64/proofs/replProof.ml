(* ======================================================== *)
(*  replProof: ported from HOL4's
    compiler/bootstrap/compilation/x64/64/proofs/replProofScript.sml
    A proof theory, with 1 definition and 25 theorems.  Needed by
    x64BootstrapProof.ml.  *)
(* ======================================================== *)

(*
  Verification of the function (called repl) that implements the REPL
*)

needs "basis/CommandLineProof.ml";;
needs "basis/TextIOProof.ml";;
needs "basis/basis_ffi.ml";;
needs "basis/fsFFIProps.ml";;
needs "basis/pure/mlstring.ml";;
needs "characteristic/cfFFIType.ml";;
needs "compiler/backend/backend.ml";;
needs "compiler/backend/proofs/backendProof.ml";;
needs "compiler/backend/proofs/source_evalProof.ml";;
needs "compiler/backend/serialiser/backend_enc_dec.ml";;
needs "compiler/backend/x64/proofs/x64_configProof.ml";;
needs "compiler/bootstrap/translation/compiler64Prog.ml";;
needs "compiler/inference/infer.ml";;
needs "compiler/repl/repl_check_and_tweak.ml";;
needs "compiler/repl/repl_decs_allowed.ml";;
needs "compiler/repl/repl_init.ml";;
needs "compiler/repl/repl_init_types.ml";;
needs "compiler/repl/repl_moduleProg.ml";;
needs "compiler/repl/repl_types.ml";;
needs "semantics/evaluate.ml";;
needs "semantics/namespace.ml";;
needs "semantics/proofs/semanticsProps.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "semantics/semantics.ml";;
needs "translator/ml_prog.ml";;
needs "translator/ml_translator.ml";;
needs "translator/monadic/monad_base/ml_monadBase.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "replProof"
  ["backendProof"; "compiler64Prog"; "evaluate"; "ml_translator";
   "repl_check_and_tweak"; "repl_init"; "repl_types"; "semanticPrimitives";
   "semanticsProps"; "x64_configProof"];;

(* HOL4 replProofScript.sml:12: ML code, not ported *)

let compiler_inst_def = new_definition
  `compiler_inst c = (\(x,y,z).
                 (OPTION_BIND) (v_fun_abs (UNIV:backend_config->bool)
                   BACKEND_CONFIG_v y) (\cfg. (OPTION_BIND)
                   (compile_inc_progs_for_eval c (x,cfg,z)) (\(cfg2,bs,ws).
                   SOME (BACKEND_CONFIG_v cfg2,bs,ws))))`;;

let no_closures_IMP_concrete_v = prove
 (`(!v. no_closures v ==> concrete_v v) /\
   (!v. ALL no_closures v ==> concrete_v_list v)`,
  CHEAT_TAC);;

(* [local] *)
let EqualityType_concrete_v = prove
 (`a x v /\ EqualityType a ==> concrete_v v`,
  CHEAT_TAC);;

(* HOL4 replProofScript.sml:39-40: ML code, not ported *)

(* HOL4 replProofScript.sml:42-43: ML code, not ported *)

let concrete_v_decs = prove
 (`LIST_TYPE AST_DEC_TYPE decs v ==> concrete_v v`,
  CHEAT_TAC);;

let concrete_v_config = prove
 (`BACKEND_CONFIG_TYPE c v ==> concrete_v v`,
  CHEAT_TAC);;

let LIST_TYPE_AST_DEC_IMP = prove
 (`LIST_TYPE AST_DEC_TYPE decs decs_v ==>
   (!x. LIST_v AST_DEC_v x = decs_v <=> x = decs)`,
  CHEAT_TAC);;

let BACKEND_CONFIG_IMP = prove
 (`BACKEND_CONFIG_TYPE c v ==>
   (!x. BACKEND_CONFIG_v x = v <=> x = c)`,
  CHEAT_TAC);;

let v_fun_abs_BACKEND_CONFIG_v = prove
 (`BACKEND_CONFIG_TYPE s1 s1_v ==>
   v_fun_abs (UNIV:backend_config->bool) BACKEND_CONFIG_v s1_v = SOME s1`,
  CHEAT_TAC);;

let v_to_word64_list_thm = prove
 (`!ws ws_v. LIST_TYPE WORD ws ws_v ==> v_to_word64_list ws_v = SOME ws`,
  CHEAT_TAC);;

let v_to_word8_list_thm = prove
 (`!bs bs_v. LIST_TYPE WORD bs bs_v ==> v_to_word8_list bs_v = SOME bs`,
  CHEAT_TAC);;

let evaluate_Eval = prove
 (`semanticPrimitives_state_eval_state
     (st:'ffi semanticPrimitives_state) = SOME (EvalDecs s) /\
     compile_inc_progs_for_eval x64_config (id1,s1,decs) = SOME (s2,bs,ws)
       /\ eval_decs_state_compiler
     s = compiler_inst x64_config /\ eval_decs_state_compiler_state
     s = s1_v /\ eval_decs_state_decode_decs
     s = v_fun_abs decs_allowed (LIST_v AST_DEC_v) ==>
     LIST_TYPE AST_DEC_TYPE decs decs_v /\
     BACKEND_CONFIG_TYPE s1 s1_v /\
     BACKEND_CONFIG_TYPE s2 s2_v /\
     LIST_TYPE WORD ws ws_v /\
     LIST_TYPE WORD bs bs_v /\
     nsLookup (sem_env_v env) (Short (implode "env")) = SOME (dataSem_Env
       env1 id1) ==>
     nsLookup (sem_env_v env) (Short (implode "decs")) = SOME decs_v ==>
     nsLookup (sem_env_v env) (Short (implode "s1")) = SOME s1_v ==>
     nsLookup (sem_env_v env) (Short (implode "s2")) = SOME s2_v ==>
     nsLookup (sem_env_v env) (Short (implode "bs")) = SOME bs_v ==>
     nsLookup (sem_env_v env) (Short (implode "ws")) = SOME ws_v ==>
     decs_allowed decs ==>
     evaluate st env [compute_syntax_App ast_Eval [panStatic_Var (Short
       (implode "env")); panStatic_Var (Short (implode "s1"));
                              panStatic_Var (Short (implode "decs"));
                                panStatic_Var (Short (implode "s2"));
                              panStatic_Var (Short (implode "bs"));
                                panStatic_Var (Short (implode "ws"))]] =
       (let st = (semanticPrimitives_state_eval_state_fupd (K (SOME
         (EvalDecs
                      (add_decs_generation
                        (eval_decs_state_compiler_state_fupd (K s2_v) s)))))
                        st) in
         if semanticPrimitives_state_clock st = 0 then (st,Rerr (Rabort
           Rtimeout_error)) else match evaluate_evaluate_decs
           (evaluate_dec_clock st) env1 decs with (st2,Rval env2) ->
               (match declare_env (semanticPrimitives_state_eval_state st2)
                 (extend_dec_env env2 env1) with
                  NONE -> (st2,Rerr (Rabort Rtype_error))
                | SOME (x,es2) ->
                  (semanticPrimitives_state_eval_state_fupd (K
                     (reset_env_generation (SOME (EvalDecs s)) es2))
                       st2,Rval [x]))
           | (st2,Rerr (Rraise v7)) ->
               (semanticPrimitives_state_eval_state_fupd (K
                  (reset_env_generation (SOME (EvalDecs s))
                    (semanticPrimitives_state_eval_state st2))) st2,
                Rerr (Rraise v7))
           | (st2,Rerr (Rabort a)) -> (st2,Rerr (Rabort a)))`,
  CHEAT_TAC);;

(* HOL4 replProofScript.sml:178-179: ML code, not ported *)

(* HOL4 replProofScript.sml:181-182: ML code, not ported *)

(* HOL4 replProofScript.sml:184-185: ML code, not ported *)

(* HOL4 replProofScript.sml:187: ML code, not ported *)

(* HOL4 replProofScript.sml:189-190: ML code, not ported *)

let Arrow_IMP = prove
 (`!x v (s:'ffi semanticPrimitives_state).
     (Arrow a b) (f:'a->'b) vv /\ a x v ==>
     (?env exp junk u ck s1 res.
       semanticPrimitives_do_opapp [vv; v] = SOME (env,exp) /\ b (f x) u /\
       evaluate s env [exp] = (s1,res) /\
       (~(res = Rerr (Rabort Rtimeout_error)) ==>
         s1 = semanticPrimitives_state_refs_fupd (K (APPEND
           (semanticPrimitives_state_refs s) junk))
           (semanticPrimitives_state_clock_fupd (K
           (semanticPrimitives_state_clock s - ck)) s) /\
         res = Rval [u]))`,
  CHEAT_TAC);;

(* HOL4 replProofScript.sml:222-224: the overload eval_res_stamp, which the
   port expands *)

let evaluate_eval = prove
 (`!(st:'ffi semanticPrimitives_state). semanticPrimitives_state_eval_state
     st = SOME (EvalDecs s) /\ eval_decs_state_compiler
     s = compiler_inst x64_config /\ eval_decs_state_compiler_state
     s = s1_v /\ eval_decs_state_decode_decs
     s = v_fun_abs decs_allowed (LIST_v AST_DEC_v)
       /\ eval_decs_state_env_id_counter
     s = (cur_gen1,next_id1,next_gen1) /\
     env_v = dataSem_Env env1 (env_id,0) /\ decs_allowed decs /\
     nsLookup (sem_env_v env) (Short eval_str) = SOME eval_v ==>
     nsLookup (sem_env_v env) (Short arg_str) =
     SOME (flatSem_Conv NONE [flatSem_Conv NONE [s1_v; flatSem_Litv
       (ast_IntLit (&next_gen))];
                      flatSem_Conv NONE [env_v; flatSem_Litv (ast_IntLit
                        (&env_id))];
                      decs_v]) /\
     BACKEND_CONFIG_TYPE s1 s1_v /\
     LIST_TYPE AST_DEC_TYPE decs decs_v /\
     (!ck junk st1 res. evaluate_evaluate_decs
       (semanticPrimitives_state_eval_state_fupd (K NONE)
       (semanticPrimitives_state_refs_fupd (K (APPEND
       (semanticPrimitives_state_refs st) junk))
       (semanticPrimitives_state_clock_fupd (K (semanticPrimitives_state_clock
       st - ck)) st))) env1
                              decs = (st1,res) ==> ~(res = Rerr (Rabort
                                Rtype_error))) ==>
     (?res s1 ck msg junk.
       evaluate st env [compute_syntax_App ast_Opapp [panStatic_Var (Short
         eval_str); panStatic_Var (Short arg_str)]] = (s1,res) /\
       (~(res = Rerr (Rabort Rtimeout_error)) ==>
        res = Rval
              [flatSem_Conv (SOME (TypeStamp (implode "Compile_error")
                eval_res_stamp))
                    [flatSem_Litv (ast_StrLit msg)]] /\
        s1 = semanticPrimitives_state_refs_fupd (K (APPEND
          (semanticPrimitives_state_refs st) junk))
          (semanticPrimitives_state_clock_fupd (K
          (semanticPrimitives_state_clock st - ck)) st) \/
        (?f. res = Rerr (Rabort (Rffi_error f))) \/
        (?exn st7 ck1 ck2 s2_v s2.
           evaluate_evaluate_decs (semanticPrimitives_state_eval_state_fupd
             (K NONE) (semanticPrimitives_state_refs_fupd (K (APPEND
             (semanticPrimitives_state_refs st) junk))
             (semanticPrimitives_state_clock_fupd (K
             (semanticPrimitives_state_clock st - ck1)) st))) env1 decs =
             (st7,Rerr (Rraise exn)) /\
           BACKEND_CONFIG_TYPE s2 s2_v /\
           res = Rval [flatSem_Conv (SOME (TypeStamp (implode "Eval_exn")
             eval_res_stamp))
                            [exn; flatSem_Conv NONE [s2_v; flatSem_Litv
                              (ast_IntLit (&next_gen + (&1)))]]] /\
           s1 = semanticPrimitives_state_eval_state_fupd (K (SOME (EvalDecs
                              (eval_decs_state_env_id_counter_fupd (K
                                (cur_gen1,next_id1,next_gen1 + 1))
                                (eval_decs_state_compiler_state_fupd (K s2_v)
                                s))))) (semanticPrimitives_state_clock_fupd (K
                                (semanticPrimitives_state_clock st7 - ck2))
                                st7)) \/
        (?env2 st7 ck1 ck2 s2_v s2.
           evaluate_evaluate_decs (semanticPrimitives_state_eval_state_fupd
             (K NONE) (semanticPrimitives_state_refs_fupd (K (APPEND
             (semanticPrimitives_state_refs st) junk))
             (semanticPrimitives_state_clock_fupd (K
             (semanticPrimitives_state_clock st - ck1)) st))) env1 decs =
             (st7,Rval env2) /\
           BACKEND_CONFIG_TYPE s2 s2_v /\
           res = Rval [flatSem_Conv (SOME (TypeStamp (implode "Eval_result")
             eval_res_stamp))
                            [flatSem_Conv NONE
                              [dataSem_Env (extend_dec_env env2 env1)
                                (next_gen1,0);
                              flatSem_Litv (ast_IntLit (&next_gen))];
                             flatSem_Conv NONE [s2_v; flatSem_Litv
                               (ast_IntLit (&next_gen + (&1)))]]] /\
           s1 = semanticPrimitives_state_eval_state_fupd (K (SOME (EvalDecs
                              (eval_decs_state_env_id_counter_fupd (K
                                (cur_gen1,next_id1,next_gen1 + 1))
                                (eval_decs_state_compiler_state_fupd (K s2_v)
                                s))))) (semanticPrimitives_state_clock_fupd
                                (K (semanticPrimitives_state_clock st7 -
                                ck2)) st7))))`,
  CHEAT_TAC);;

let repl_types_alt = prove
 (`repl_types T (ffi,rs) (types,s,env) /\
   infertype_prog_inc types decs = M_success new_t ==>
     ~(evaluate_evaluate_decs s env decs = (new_s,Rerr (Rabort Rtype_error)))`,
  CHEAT_TAC);;

let repl_types_clock_refs = prove
 (`repl_types T (ffi,rs) (types,semanticPrimitives_state_eval_state_fupd (K
  NONE) st,env1) ==>
   repl_types T (ffi,rs)
     (types,semanticPrimitives_state_eval_state_fupd (K NONE)
       (semanticPrimitives_state_refs_fupd (K (APPEND
       (semanticPrimitives_state_refs st) junk))
       (semanticPrimitives_state_clock_fupd (K
       (semanticPrimitives_state_clock st - ck)) st)),env1)`,
  CHEAT_TAC);;

let repl_types_clock_refs_ffi = prove
 (`repl_types T (ffi,rs) (types,semanticPrimitives_state_eval_state_fupd (K
  NONE) st,env1) ==>
   repl_types T (ffi,rs)
     (types,semanticPrimitives_state_eval_state_fupd (K NONE)
       (semanticPrimitives_state_ffi_fupd (K (semanticPrimitives_state_ffi
       st)) (semanticPrimitives_state_refs_fupd (K (APPEND
       (semanticPrimitives_state_refs st) junk))
       (semanticPrimitives_state_clock_fupd (K
       (semanticPrimitives_state_clock st - ck)) st))),env1)`,
  CHEAT_TAC);;

let evaluate_clock_decs = prove
 (`evaluate_evaluate_decs s env xs = (s1,res) ==>
  semanticPrimitives_state_clock s1 <= semanticPrimitives_state_clock s`,
  CHEAT_TAC);;

let evaluate_decs_with_NONE = prove
 (`evaluate_evaluate_decs s env1 safe_decs = (s1,res)
  /\ semanticPrimitives_state_eval_state s = NONE /\ ~(res = Rerr (Rabort
  Rtype_error)) ==>
   evaluate_evaluate_decs s env1 safe_decs =
     (semanticPrimitives_state_eval_state_fupd (K NONE) s1,res)`,
  CHEAT_TAC);;

(* HOL4 replProofScript.sml:491-492: the overload TYPES_TYPE, which the port
   expands *)

let evaluate_repl = prove
 (`!(st:'ffi semanticPrimitives_state) s repl_str arg_str
    env s1_v types' cur_gen next_id next_gen env1
    parse_v types_v conf_v env_v decs_v input_str_v
    types' decs input_str env_id s1 parse'.
      semanticPrimitives_state_eval_state
      st = SOME (EvalDecs s) /\ eval_decs_state_compiler
      s = compiler_inst x64_config /\ eval_decs_state_compiler_state
      s = s1_v /\ eval_decs_state_decode_decs
      s = v_fun_abs decs_allowed (LIST_v AST_DEC_v)
        /\ eval_decs_state_env_id_counter
      s = (cur_gen,next_id,next_gen) /\
      BACKEND_CONFIG_TYPE s1 (eval_decs_state_compiler_state s) /\
      LIST_TYPE AST_DEC_TYPE decs decs_v /\
      (PAIR_TYPE ADDPRINTVALS_TYPE_NAMES_TYPE (PAIR_TYPE INFER_INF_ENV_TYPE
        NUM)) types' types_v /\
      STRING_TYPE input_str input_str_v /\
      (Arrow STRING_TYPE (SUM_TYPE STRING_TYPE (LIST_TYPE AST_DEC_TYPE)))
        parse' parse_v /\
      env_v = flatSem_Conv NONE [dataSem_Env env1 (env_id,0); flatSem_Litv
        (ast_IntLit (&env_id))] /\
      conf_v = flatSem_Conv NONE [s1_v; flatSem_Litv (ast_IntLit
        (&next_gen))] /\
      repl_types T (ffi,repl_rs) (SND
        types',semanticPrimitives_state_eval_state_fupd (K NONE) st,env1) /\
      nsLookup (sem_env_v env) repl_str = SOME repl_v ==>
      nsLookup (sem_env_v env) arg_str =
        SOME (flatSem_Conv NONE [parse_v; types_v; conf_v; env_v; decs_v;
          input_str_v]) ==>
      (?res s1.
        evaluate st env [compute_syntax_App ast_Opapp [panStatic_Var
          repl_str; panStatic_Var arg_str]] = (s1,res) /\ ~(res = Rerr (Rabort
          Rtype_error)) /\
        (!vs. res = Rval vs ==> vs = [flatSem_Conv NONE []]))`,
  CHEAT_TAC);;

let evaluate_repl_thm =
  SPEC_ALL (SIMP_RULE [STRING_TYPE_def; LIST_TYPE_def] (GEN_ALL (CAKE_INST
  [`0`,`cur_gen`; `1`,`next_id`; `1`,`next_gen`; `0`,`env_id`; `(implode
  "")`,`input_str`; `[]`,`decs`] (SPEC_ALL (SIMP_RULE [] evaluate_repl)))));;

let evaluate_start_repl = prove
 (`semanticPrimitives_state_eval_state
     (st:'ffi semanticPrimitives_state) = SOME (EvalDecs s)
       /\ eval_decs_state_compiler
     s = compiler_inst x64_config /\ eval_decs_state_decode_decs
     s = v_fun_abs decs_allowed (LIST_v AST_DEC_v)
       /\ eval_decs_state_env_id_counter
     s = (0,1,1) /\
     BACKEND_CONFIG_TYPE s1 (eval_decs_state_compiler_state s) /\
     LIST_TYPE STRING_TYPE cl cl_v /\
     repl_types T (ffi,repl_rs)
                  (repl_prog_types,semanticPrimitives_state_eval_state_fupd
                    (K NONE) st,repl_init_env) /\
     nsLookup (sem_env_v env) start_repl_str = SOME start_repl_v ==>
     nsLookup (sem_env_v env) arg_str = SOME (flatSem_Conv NONE [cl_v;
       eval_decs_state_compiler_state s]) ==>
     (?res s1.
       evaluate st env [compute_syntax_App ast_Opapp [panStatic_Var
         start_repl_str; panStatic_Var arg_str]] = (s1,res) /\ ~(res = Rerr
         (Rabort Rtype_error)) /\
       (!vs. res = Rval vs ==> vs = [flatSem_Conv NONE []]))`,
  CHEAT_TAC);;

let BUTLAST_LAST = prove
 (`!xs. ~(NULL xs) ==> xs = APPEND (BUTLAST xs) [LAST xs]`,
  CHEAT_TAC);;

(* [local] *)
let BACKEND_CONFIG_TYPE_v = prove
 (`BACKEND_CONFIG_TYPE conf u ==>
   u = BACKEND_CONFIG_v conf`,
  CHEAT_TAC);;

let repl_prog_isPREFIX = prove
 (`repl_prog <<= BUTLAST compiler64_prog`,
  CHEAT_TAC);;

(* HOL4 replProofScript.sml:1112: the ML values that the definitions below
   antiquote *)

(*
  max_print_depth := 15
*)

let evaluate_decs_compiler64_prog = prove
 (`eval_decs_state_compiler
     s = compiler_inst x64_config /\ eval_decs_state_decode_decs
     s = v_fun_abs decs_allowed (LIST_v AST_DEC_v)
       /\ eval_decs_state_env_id_counter
     s = (0,0,1) /\ prog_syntax_ok compiler64_prog /\
     has_repl_flag (TL cl) /\ wfcl cl /\ wfFS fs /\ STD_streams fs /\ CARD
       (set_of_list (MAP FST (IO_fs_infds fs))) < MIN (IO_fs_maxFD fs) (256 EXP
       8) /\ eval_decs_state_compiler_state
     s = BACKEND_CONFIG_v conf /\
     file_content fs (implode "config_enc_str.txt") = SOME
       (encode_backend_config conf) /\
     evaluate_evaluate_decs (semanticPrimitives_state_eval_state_fupd (K
       (SOME (EvalDecs s))) (semanticPrimitives_state_clock_fupd (K ck)
       (ml_prog_init_state (basis_ffi ext cl fs))))
         init_env compiler64_prog = (s1,res) ==> ~(res = Rerr (Rabort
           Rtype_error))`,
  CHEAT_TAC);;

let semantics_prog_compiler64_prog = prove
 (`eval_decs_state_compiler
     s = compiler_inst x64_config /\ eval_decs_state_decode_decs
     s = v_fun_abs decs_allowed (LIST_v AST_DEC_v)
       /\ eval_decs_state_env_id_counter
     s = (0,0,1) /\ has_repl_flag (TL cl) /\ wfcl cl /\ wfFS fs /\
     STD_streams fs /\ CARD (set_of_list (MAP FST (IO_fs_infds fs))) < MIN
       (IO_fs_maxFD fs) (256 EXP 8) /\ prog_syntax_ok compiler64_prog
       /\ eval_decs_state_compiler_state
     s = BACKEND_CONFIG_v conf /\
     file_content fs (implode "config_enc_str.txt") = SOME
       (encode_backend_config conf) ==> ~(ffi_Fail IN semantics_prog
              (semanticPrimitives_state_eval_state_fupd (K (SOME (EvalDecs
                s))) (ml_prog_init_state (basis_ffi ext cl fs)))
              init_env compiler64_prog)`,
  CHEAT_TAC);;

(* and the interface *)
let _ = unhide_overloads ();;
