(* ======================================================== *)
(*  infer_eSound: ported from HOL4's
    compiler/inference/proofs/infer_eSoundScript.sml
    A proof theory, with no definitions and 20 theorems.  Needed by
    inferComplete.ml, inferSound.ml and type_eDeterm.ml.  *)
(* ======================================================== *)

(*
  Prove soundness of the type inferencer for the expression-level.
*)

needs "compiler/inference/infer.ml";;
needs "compiler/inference/inferProps.ml";;
needs "compiler/inference/infer_t.ml";;
needs "compiler/inference/proofs/envRel.ml";;
needs "compiler/inference/unify.ml";;
needs "semantics/ast.ml";;
needs "semantics/proofs/namespaceProps.ml";;
needs "semantics/proofs/typeSoundInvariants.ml";;
needs "semantics/proofs/typeSysProps.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "semantics/typeSystem.ml";;
needs "translator/monadic/monad_base/ml_monadBase.ml";;

(* the theories whose names the Ancestors blocks of the source
   bring, which are the ones that its statements read: the
   overloads of every other theory come out of the interface
   while this file loads *)
let _ = hol4_ancestors "infer_eSound"
  ["ast"; "envRel"; "infer"; "inferProps"; "infer_t"; "ml_monadBase";
   "namespaceProps"; "semanticPrimitives"; "typeSoundInvariants";
   "typeSysProps"; "typeSystem"; "unify"];;

(* ---------- sub_completion ---------- *)

(* [local] *)
let sub_completion_unify = prove
 (`!st t1 t2 s1 n ts s2 n.
   (t_unify (infer_st_subst st) t1 t2 = SOME s1) /\
   sub_completion n (infer_st_next_uvar st + 1) s1 ts s2 ==>
   sub_completion n (infer_st_next_uvar st) (infer_st_subst st)
     (CONS (t1,t2) ts) s2`,
  CHEAT_TAC);;

let sub_completion_unify2 = prove
 (`!t1 t2 s1 ts s2 n s3 next_uvar.
    (t_unify s1 t1 t2 = SOME s2) /\
    sub_completion n next_uvar s2 ts s3 ==>
    sub_completion n next_uvar s1 (CONS (t1,t2) ts) s3`,
  CHEAT_TAC);;

(* [local] *)
let sub_completion_infer = prove
 (`!l ienv e st1 t st2 n ts2 s.
   infer_e l ienv e st1 = (M_success t,st2) /\
   sub_completion n (infer_st_next_uvar st2) (infer_st_subst st2) ts2
     s ==>
   (?ts1. sub_completion n (infer_st_next_uvar st1) (infer_st_subst
     st1) (APPEND ts1 ts2) s)`,
  CHEAT_TAC);;

let sub_completion_add_constraints = prove
 (`!s1 ts1 s2 n next_uvar s3 ts2.
    pure_add_constraints s1 ts1 s2 /\
    sub_completion n next_uvar s2 ts2 s3 ==>
    sub_completion n next_uvar s1 (APPEND ts1 ts2) s3`,
  CHEAT_TAC);;

(* [local] *)
let sub_completion_more_vars = prove
 (`!m n1 n2 s1 ts s2.
   sub_completion m (n1 + n2) s1 ts s2 ==> sub_completion m n1 s1
     ts s2`,
  CHEAT_TAC);;

(* [local] *)
let sub_completion_infer_es = prove
 (`!l cenv es st1 t st2 n ts2 s.
   infer_es l cenv es st1 = (M_success t,st2) /\
   sub_completion n (infer_st_next_uvar st2) (infer_st_subst st2) ts2
     s ==>
   (?ts1. sub_completion n (infer_st_next_uvar st1) (infer_st_subst
     st1) (APPEND ts1 ts2) s)`,
  CHEAT_TAC);;

let sub_completion_infer_p = prove
 (`(!l cenv p st t env st' tvs extra_constraints s.
     infer_p l cenv p st = (M_success (t,env),st') /\
     sub_completion tvs (infer_st_next_uvar st') (infer_st_subst st')
       extra_constraints s ==>
     (?ts. sub_completion tvs (infer_st_next_uvar st) (infer_st_subst
       st) (APPEND ts extra_constraints) s)) /\
   (!l cenv ps st ts env st' tvs extra_constraints s.
     infer_ps l cenv ps st = (M_success (ts,env),st') /\
     sub_completion tvs (infer_st_next_uvar st') (infer_st_subst st')
       extra_constraints s ==>
     (?ts. sub_completion tvs (infer_st_next_uvar st)
       (infer_st_subst st) (APPEND ts extra_constraints) s))`,
  CHEAT_TAC);;

(* [local] *)
let sub_completion_infer_pes = prove
 (`!l ienv pes t1 t2 st1 t st2 n ts2 s.
   infer_pes l ienv pes t1 t2 st1 = (M_success one,st2) /\
   sub_completion n (infer_st_next_uvar st2) (infer_st_subst st2) ts2
     s ==>
   (?ts1. sub_completion n (infer_st_next_uvar st1) (infer_st_subst
     st1) (APPEND ts1 ts2) s)`,
  CHEAT_TAC);;

(* [local] *)
let sub_completion_infer_funs = prove
 (`!l ienv funs st1 t st2 n ts2 s.
   infer_funs l ienv funs st1 = (M_success t,st2) /\
   sub_completion n (infer_st_next_uvar st2) (infer_st_subst st2) ts2
     s ==>
   (?ts1. sub_completion n (infer_st_next_uvar st1) (infer_st_subst
     st1) (APPEND ts1 ts2) s)`,
  CHEAT_TAC);;

let sub_completion_apply = prove
 (`!n uvars s1 ts s2 t1 t2.
    t_wfs s1 /\
    (t_walkstar s1 t1 = t_walkstar s1 t2) /\
    sub_completion n uvars s1 ts s2 ==>
    (t_walkstar s2 t1 = t_walkstar s2 t2)`,
  CHEAT_TAC);;

(* [local] *)
let sub_completion_apply_list = prove
 (`!n uvars s1 ts s2 ts1 ts2.
   t_wfs s1 /\
   (MAP (t_walkstar s1) ts1 = MAP (t_walkstar s1) ts2) /\
   sub_completion n uvars s1 ts s2 ==>
   (MAP (t_walkstar s2) ts1 = MAP (t_walkstar s2) ts2)`,
  CHEAT_TAC);;

(* [local] *)
let sub_completion_check = prove
 (`!tvs m s uvar s' extra_constraints.
   sub_completion m (uvar + tvs) s' extra_constraints s ==>
   ALL (\n. check_freevars m [] (convert_t (t_walkstar s
     (Infer_Tuvar (uvar + n))))) (COUNT_LIST tvs)`,
  CHEAT_TAC);;

(* ---------- Soundness ---------- *)

let infer_p_sound = prove
 (`(!l ienv p st t tenv env st' tvs extra_constraints s.
     infer_p l ienv p st = (M_success (t,env),st') /\
     t_wfs (infer_st_subst st) /\
     tenv_ctor_ok (type_env_c tenv) /\ inf_env_inf_c
     ienv = type_env_c tenv /\ inf_env_inf_t
     ienv = type_env_t tenv /\
     tenv_abbrev_ok (type_env_t tenv) /\
     sub_completion tvs (infer_st_next_uvar st') (infer_st_subst st')
       extra_constraints s ==>
     type_p tvs tenv p (convert_t (t_walkstar s t)) (convert_env s
       env)) /\
   (!l ienv ps st ts tenv env st' tvs extra_constraints s.
     infer_ps l ienv ps st = (M_success (ts,env),st') /\
     t_wfs (infer_st_subst st) /\
     tenv_ctor_ok (type_env_c tenv) /\ inf_env_inf_c
     ienv = type_env_c tenv /\ inf_env_inf_t
     ienv = type_env_t tenv /\
     tenv_abbrev_ok (type_env_t tenv) /\
     sub_completion tvs (infer_st_next_uvar st') (infer_st_subst st')
       extra_constraints s ==>
     type_ps tvs tenv ps (MAP (convert_t o t_walkstar s) ts)
       (convert_env s env))`,
  CHEAT_TAC);;

(* [local] *)
let letrec_lemma = prove
 (`!funs funs_ts s st.
   (MAP (\n. convert_t (t_walkstar s (Infer_Tuvar (infer_st_next_uvar
     st + n)))) (COUNT_LIST (LENGTH funs)) =
    MAP (\t. convert_t (t_walkstar s t)) funs_ts) ==>
   (MAP2 (\(f,x,e) t. (f,t)) funs (MAP (\n. convert_t (t_walkstar s
     (Infer_Tuvar (infer_st_next_uvar st + n)))) (COUNT_LIST (LENGTH
     funs))) =
    MAP2 (\(x,y,z) t. (x,convert_t (t_walkstar s t))) funs funs_ts)`,
  CHEAT_TAC);;

(* [local] *)
let map_zip_lem = prove
 (`!funs ts.
   (LENGTH funs = LENGTH ts) ==>
   (
    MAP (\x. FST ((\((x',y,z),t). (x',convert_t (t_walkstar s t)))
      x)) (ZIP funs ts) =
    MAP FST funs)`,
  CHEAT_TAC);;

let word_tc_cases = prove
 (`(word_tc wz = Tword8_num <=> wz = ast_W8) /\
   (word_tc wz = Tword64_num <=> wz = ast_W64)`,
  CHEAT_TAC);;

(* HOL4 infer_eSoundScript.sml:435-450: a proof *)

(* [local] *)
let constrain_op_sub_completion = prove
 (`sub_completion (num_tvs tenv) (infer_st_next_uvar st) (infer_st_subst
  st) extra_constraints s /\
   constrain_op l op ts st' = (M_success t,st) ==>
   (?c. sub_completion (num_tvs tenv) (infer_st_next_uvar st')
     (infer_st_subst st') c s)`,
  CHEAT_TAC);;

(* [local] *)
let constrain_op_sound = prove
 (`t_wfs (infer_st_subst st) /\
   sub_completion (num_tvs tenv) (infer_st_next_uvar st')
     (infer_st_subst st') c s /\
   constrain_op l op ts st = (M_success t,st') ==>
   type_op op (MAP (convert_t o t_walkstar s) ts) (convert_t
     (t_walkstar s t))`,
  CHEAT_TAC);;

let infer_deBruijn_subst_walkstar = prove
 (`!ts t s.
    t_wfs s ==>
    t_walkstar s (infer_deBruijn_subst (MAP (t_walkstar s) ts) t) =
    t_walkstar s (infer_deBruijn_subst ts t)`,
  CHEAT_TAC);;

(* HOL4 infer_eSoundScript.sml:518-560: a proof *)

let infer_e_sound = prove
 (`(!l ienv e st st' tenv tenvE t extra_constraints s.
      infer_e l ienv e st = (M_success t,st') /\
      ienv_ok (count (infer_st_next_uvar st)) ienv /\
      env_rel_sound s ienv tenv tenvE /\
      t_wfs (infer_st_subst st) /\
      sub_completion (num_tvs tenvE) (infer_st_next_uvar st')
        (infer_st_subst st') extra_constraints s ==>
      type_e tenv tenvE e (convert_t (t_walkstar s t))) /\
   (!l ienv es st st' tenv tenvE ts extra_constraints s.
      infer_es l ienv es st = (M_success ts,st') /\
      ienv_ok (count (infer_st_next_uvar st)) ienv /\
      env_rel_sound s ienv tenv tenvE /\
      t_wfs (infer_st_subst st) /\
      sub_completion (num_tvs tenvE) (infer_st_next_uvar st')
        (infer_st_subst st') extra_constraints s ==>
      type_es tenv tenvE es (MAP (convert_t o t_walkstar s) ts)) /\
   (!l ienv pes t1 t2 st st' tenv tenvE extra_constraints s.
      infer_pes l ienv pes t1 t2 st = (M_success one,st') /\
      ienv_ok (count (infer_st_next_uvar st)) ienv /\
      env_rel_sound s ienv tenv tenvE /\
      t_wfs (infer_st_subst st) /\
      sub_completion (num_tvs tenvE) (infer_st_next_uvar st')
        (infer_st_subst st') extra_constraints s ==>
      type_pes (num_tvs tenvE) 0 tenv tenvE pes (convert_t
        (t_walkstar s t1)) (convert_t (t_walkstar s t2))) /\
   (!l ienv funs st st' tenv tenvE extra_constraints s ts.
      infer_funs l ienv funs st = (M_success ts,st') /\
      ienv_ok (count (infer_st_next_uvar st)) ienv /\
      env_rel_sound s ienv tenv tenvE /\
      t_wfs (infer_st_subst st) /\
      sub_completion (num_tvs tenvE) (infer_st_next_uvar st')
        (infer_st_subst st') extra_constraints s /\
      ALL_DISTINCT (MAP FST funs) ==>
      type_funs tenv tenvE funs (MAP2 (\(x,y,z) t. (x,(convert_t o
        t_walkstar s) t)) funs ts))`,
  CHEAT_TAC);;

(* and the overloads that this file cannot see are back in the
   interface *)
let _ = unhide_overloads ();;
