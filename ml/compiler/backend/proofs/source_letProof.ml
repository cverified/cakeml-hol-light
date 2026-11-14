(* ======================================================== *)
(*  source_letProof: ported from HOL4's
    compiler/backend/proofs/source_letProofScript.sml
    A proof theory about source_let.ml, with no definitions and 9
    theorems.  Needed by source_to_sourceProof.ml.  *)
(* ======================================================== *)

(*
  Correctness for the source_let pass.
 *)

needs "compiler/backend/proofs/source_evalProof.ml";;
needs "compiler/backend/source_let.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "semantics/evaluate.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/namespace.ml";;
needs "semantics/proofs/evaluateProps.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "semantics/semantics.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "source_letProof"
  ["ast"; "evaluate"; "evaluateProps"; "misc"; "semanticPrimitives";
   "semanticPrimitivesProps"; "semantics"; "source_evalProof";
   "source_let"];;


(* [local] *)
let env_c_lemma = prove
 (`sem_env_c
     (extend_dec_env (mk_sem_env (semanticPrimitives_build_rec_env
       q env env1) nsEmpty) env) = sem_env_c env`,
  CHEAT_TAC);;

let evaluate_lift_let = prove
 (`evaluate_evaluate_decs s env [d] = (s',res) /\ ~(res = Rerr (Rabort
  Rtype_error)) /\
   lift_let d = SOME (d1,d2) ==>
     evaluate_evaluate_decs s env [Dlocal [d1] [d2]] = (s',res)`,
  CHEAT_TAC);;

let lift_lets_is_prefix = prove
 (`!ds d ds1 ds2.
     lift_lets ds d = SOME (ds1,ds2) ==> REVERSE ds <<= ds1`,
  CHEAT_TAC);;

let evaluate_lift_lets = prove
 (`!ds d s env s1 env1 s2 res ds1 ds2.
     evaluate_evaluate_decs s env (REVERSE ds) = (s1,Rval env1) /\
     evaluate_evaluate_decs s1 (extend_dec_env env1 env) [d] =
       (s2,res) /\ ~(res = Rerr (Rabort Rtype_error)) /\
     lift_lets ds d = SOME (ds1,ds2) ==>
       evaluate_evaluate_decs s env [Dlocal ds1 [ds2]] = (s2,res)`,
  CHEAT_TAC);;

(* [local] *)
let lift_lets_mod_local = prove
 (`(!ds1 ds2. lift_lets [] (Dlocal ds1 ds2) = NONE) /\
   (!mn ds. lift_lets [] (Dmod mn ds) = NONE)`,
  CHEAT_TAC);;
add_simp lift_lets_mod_local;;

(* HOL4 source_letProofScript.sml:105-107: a theorem that HOL4 states
   as the value of an ML expression: evaluate_lift_start *)

let compile_decs_correct = prove
 (`!s env ds s' res.
     evaluate_evaluate_decs s env ds = (s',res) /\ ~(res = Rerr
       (Rabort Rtype_error)) ==>
       evaluate_evaluate_decs s env (source_let_compile_decs ds) =
         (s',res)`,
  CHEAT_TAC);;

(* compile_semantics *)
(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let source_letProof_compile_semantics = prove
 (cake_as_vars (fun () ->
    `~(semantics_prog s env prog ffi_Fail) /\
     semantics_prog s env prog outcome ==>
       semantics_prog s env (source_let_compile_decs prog)
         outcome`),
  CHEAT_TAC);;

let compile_semantics_oracle = prove
 (`!f.
   is_insert_oracle ci f (semanticPrimitives_state_eval_state s) /\
   ~(semantics_prog s env prog ffi_Fail) /\
   semantics_prog s env prog outcome ==>
   semantics_prog (semanticPrimitives_state_eval_state_fupd
             (adjust_oracle ci (source_let_compile_decs o f)) s)
         env prog outcome`,
  CHEAT_TAC);;
