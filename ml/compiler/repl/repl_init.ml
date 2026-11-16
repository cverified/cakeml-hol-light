(* ======================================================== *)
(*  repl_init: ported from HOL4's
    compiler/repl/repl_initScript.sml
    A definition theory, with 3 definitions and 13 theorems.  Needed
    by replProof.ml.  *)
(* ======================================================== *)

(*
  Proves repl_types for the initial env and types from which the REPL starts.
*)

needs "basis/basis_ffi.ml";;
needs "basis/pure/mlstring.ml";;
needs "candle/standard/monadic/holKernel.ml";;
needs "characteristic/cfApp.ml";;
needs "characteristic/cfHeapsBase.ml";;
needs "characteristic/cfStore.ml";;
needs "compiler/repl/repl_init_envProg.ml";;
needs "compiler/repl/repl_init_types.ml";;
needs "compiler/repl/repl_moduleProg.ml";;
needs "compiler/repl/repl_types.ml";;
needs "lib/set_sep.ml";;
needs "semantics/evaluate.ml";;
needs "semantics/namespace.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "translator/ml_prog.ml";;
needs "translator/ml_translator.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "repl_init"
  ["basis_ffi"; "ml_prog"; "repl_init_envProg"; "repl_init_types";
   "repl_moduleProg"; "repl_types"];;

let _ = do_list hide_constant ["types"];;

(* HOL4 repl_initScript.sml:13: ML code, not ported *)

(* HOL4 repl_initScript.sml:15-18: ML code, not ported *)

(* HOL4 repl_initScript.sml:20: the overload repl_prog_env, which the port
   expands *)

(* PORT FAILED: Definition repl_prog_st_def: expected ')' but found '|>' at
   34 *)
(* HOL4 repl_initScript.sml:22-24: the definition *)

(* HOL4 repl_initScript.sml:26: ML code, not ported *)

let merge_env_intro = prove
 (`extend_dec_env = merge_env`,
  CHEAT_TAC);;

let the_Loc_def = new_definition
  `the_Loc (semanticPrimitives_Loc _ n) = n`;;

let repl_rs_def = new_definition
  `repl_rs = [(Long (implode "Repl") (Short (implode "isEOF")),(holSyntax_Tyapp
  (implode "bool") []),the_Loc isEOF_loc);
              (Long (implode "Repl") (Short (implode
                "nextString")),repl_types_Str,the_Loc nextString_loc);
              (Long (implode "Repl") (Short (implode
                "errorMessage")),repl_types_Str,the_Loc errorMessage_loc);
              (Long (implode "Repl") (Short (implode
                "exn")),repl_types_Exn,the_Loc exn)]`;;

(* HOL4 repl_initScript.sml:45-47: the overload repl_init_env, which the
   port expands *)

let repl_rs_thm = prove
 (`ALL (check_ref_types (FST repl_prog_types) repl_init_env) repl_rs`,
  CHEAT_TAC);;

let evaluate_decs_append = prove
 (`// TODO: move to evaluateProps
   !xs ys st env.
     evaluate_evaluate_decs st env (APPEND xs ys) =
     match evaluate_evaluate_decs st env xs with (st1,Rerr e) -> (st1,Rerr
       e)
     | (st1,Rval env1) ->
         (match evaluate_evaluate_decs st1 (extend_dec_env env1 env) ys
           with (st2,r) -> (st2,combine_dec_result env1 r))`,
  CHEAT_TAC);;

(* [local] *)
let app_frame = prove
 (`app p f xs P Q ==> (!H. app p f xs (P * H) (STARPOST Q H))`,
  CHEAT_TAC);;

(* [local] *)
let app_frame_POSTv = prove
 (`app p f xs P (POSTv Q) ==> (!H. app p f xs (P * H) (POSTv (?_Q v) v * H))`,
  CHEAT_TAC);;

(* HOL4 repl_initScript.sml:110-121: a theorem that HOL4 states as the value
   of an ML expression: CommandLine_arguments_lemma *)

(* HOL4 repl_initScript.sml:123-138: a theorem that HOL4 states as the value
   of an ML expression: Repl_charsFrom_lemma *)

let repl_types_clock = prove
 (`repl_types T x (types,s,env) ==>
   (!k. repl_types T x (types,semanticPrimitives_state_clock_fupd (K
     (semanticPrimitives_state_clock s - k)) s,env))`,
  CHEAT_TAC);;

let repl_types_refs = prove
 (`repl_types T x (types,s,env) ==>
   (!k. repl_types T x (types,semanticPrimitives_state_refs_fupd (K
     (APPEND (semanticPrimitives_state_refs s) k)) s,env))`,
  CHEAT_TAC);;

let extend_dec_env_empty = prove
 (`extend_dec_env (mk_sem_env nsEmpty nsEmpty) env = env`,
  CHEAT_TAC);;

let parts_ok_basis_ffi = prove
 (`parts_ok (basis_ffi ext cls fs) (basis_proj1,basis_proj2)`,
  CHEAT_TAC);;

let st2heap_basis = prove
 (`wfcl cl /\ wfFS fs /\ STD_streams fs /\ semanticPrimitives_state_refs
   (repl_prog_st ext cl fs) <<= semanticPrimitives_state_refs st
     /\ semanticPrimitives_state_ffi
   (repl_prog_st ext cl fs) = semanticPrimitives_state_ffi st ==>
   (?h_i h_k.
     SPLIT (st2heap (basis_proj1,basis_proj2) st) (h_i,h_k) /\
     (COMMANDLINE cl * STDIO fs) h_i)`,
  CHEAT_TAC);;

let repl_types_repl_prog = prove
 (`Prog init_env
     (semanticPrimitives_state_eval_state_fupd (K (SOME (EvalDecs
       (eval_decs_state_env_id_counter_fupd (K ns) s)))) (ml_prog_init_state
       (basis_ffi ext cl fs))) xs env
     st /\
   evaluate_evaluate_decs
     (semanticPrimitives_state_eval_state_fupd (K (SOME (EvalDecs s)))
       (semanticPrimitives_state_clock_fupd (K ck) (ml_prog_init_state
       (basis_ffi ext cl fs)))) init_env (APPEND xs ys) =
   (s1,res) /\ eval_decs_state_env_id_counter s = ns /\ repl_prog <<= xs /\
   prog_syntax_ok repl_prog /\ semanticPrimitives_state_refs
   (repl_prog_st ext cl fs) <<= semanticPrimitives_state_refs st
     /\ semanticPrimitives_state_next_type_stamp
   (repl_prog_st ext cl fs) <= semanticPrimitives_state_next_type_stamp st
     /\ semanticPrimitives_state_next_exn_stamp
   (repl_prog_st ext cl fs) <= semanticPrimitives_state_next_exn_stamp st
     /\ semanticPrimitives_state_ffi
   st = semanticPrimitives_state_ffi (repl_prog_st ext cl fs) /\ wfcl cl
     /\ wfFS fs /\ STD_streams fs /\ CARD (set_of_list (MAP FST (IO_fs_infds
     fs))) < MIN (IO_fs_maxFD fs) (256 EXP 8) /\ file_content fs (implode
     "config_enc_str.txt") = SOME content ==>
   res = Rerr (Rabort Rtimeout_error) \/
   (?ck1 r1 env_cl e_cl s_cl res_cl.
     evaluate_evaluate_decs (semanticPrimitives_state_clock_fupd (K ck1) st)
       (merge_env env init_env) ys =
     (s1,r1) /\ combine_dec_result env r1 = res /\
     repl_types T (basis_ffi ext cl fs,repl_rs)
       (repl_prog_types,semanticPrimitives_state_clock_fupd (K ck1)
         (semanticPrimitives_state_eval_state_fupd (K NONE) st),
        repl_init_env) /\
     semanticPrimitives_do_opapp [CommandLine_arguments_v;
       semanticPrimitives_Conv NONE []] = SOME (env_cl,e_cl) /\
     evaluate (semanticPrimitives_state_clock_fupd (K (ck1 - 2))
       (semanticPrimitives_state_eval_state_fupd (K NONE) st)) env_cl
       [e_cl] = (s_cl,res_cl) /\
     (~(res_cl = Rerr (Rabort Rtimeout_error)) ==>
      (?cl_v.
        LIST_TYPE STRING_TYPE (TL cl) cl_v /\ res_cl = Rval [cl_v] /\
        (!ck junk. ?env_pr e_pr res_pr s_pr.
          semanticPrimitives_do_opapp [Repl_charsFrom_v;
            semanticPrimitives_Litv (ast_StrLit (implode
            "config_enc_str.txt"))] =
          SOME (env_pr,e_pr) /\
          evaluate
            (semanticPrimitives_state_refs_fupd (K (APPEND
              (semanticPrimitives_state_refs s_cl) junk))
              (semanticPrimitives_state_clock_fupd (K
              (semanticPrimitives_state_clock s_cl - (ck + 3))) s_cl))
            env_pr [e_pr] = (s_pr,res_pr) /\
          (~(res_pr = Rerr (Rabort Rtimeout_error)) ==>
           (?pr_v.
             res_pr = Rval [pr_v] /\ LIST_TYPE CHAR content pr_v /\
             repl_types T (basis_ffi ext cl fs,repl_rs)
               (repl_prog_types,s_pr,repl_init_env)))))))`,
  CHEAT_TAC);;

(* and the names it reads as variables are constants again *)
let _ = do_list unhide_constant
  ["types"];;

(* and the interface *)
let _ = unhide_overloads ();;
