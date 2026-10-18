(* ======================================================== *)
(*  type_eDeterm: ported from HOL4's
    compiler/inference/proofs/type_eDetermScript.sml
    A proof theory, with no definitions and 10 theorems.  Needed by
    inferComplete.ml and inferSound.ml.  *)
(* ======================================================== *)

(*
  Prove determinism lemmas about the type inferencer.
*)

needs "compiler/inference/infer.ml";;
needs "compiler/inference/inferProps.ml";;
needs "compiler/inference/infer_t.ml";;
needs "compiler/inference/proofs/envRel.ml";;
needs "compiler/inference/proofs/infer_eComplete.ml";;
needs "compiler/inference/proofs/infer_eSound.ml";;
needs "compiler/inference/unify.ml";;
needs "semantics/ast.ml";;
needs "semantics/evaluate.ml";;
needs "semantics/namespace.ml";;
needs "semantics/proofs/namespaceProps.ml";;
needs "semantics/proofs/typeSoundInvariants.ml";;
needs "semantics/proofs/typeSysProps.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "semantics/typeSystem.ml";;
needs "translator/monadic/monad_base/ml_monadBase.ml";;

let sub_completion_empty = cake_theorem "sub_completion_empty[local]"
  (fun () ->
    `!m n s s'. sub_completion m n s [] s' <=> count n SUBSET FDOM s'
  /\ (!uv. uv IN FDOM s' ==> check_t m {} (t_walkstar s' (Infer_Tuvar
  uv))) /\ s = s'`)
  CHEAT_TAC;;

let type_p_pat_bindings = cake_theorem "type_p_pat_bindings"
  (fun () ->
    `(!tvs tenv p t new_bindings.
      type_p tvs tenv p t new_bindings ==> MAP FST new_bindings =
        ast_pat_bindings p) /\
     (!tvs tenv ps ts new_bindings.
      type_ps tvs tenv ps ts new_bindings ==> MAP FST
        new_bindings = ast_pats_bindings ps)`)
  CHEAT_TAC;;

let infer_pe_complete = cake_theorem "infer_pe_complete"
  (fun () ->
    `ienv_ok {} ienv /\
      env_rel_complete FEMPTY ienv tenv (bind_tvar tvs
        typeSystem_Empty) /\
      ALL_DISTINCT (ast_pat_bindings p) /\
      type_p tvs tenv p t1 tenv1 /\
      type_e tenv (bind_tvar tvs typeSystem_Empty) e t1 ==>
      (?t t' new_bindings st st' s constrs s'.
        infer_e loc ienv e (init_infer_state ss) = (M_success t,st)
          /\
        infer_p loc ienv p st = (M_success (t',new_bindings),st')
          /\
        t_unify (infer_st_subst st') t t' = SOME s /\
        sub_completion tvs (infer_st_next_uvar st') s constrs s' /\
        FDOM s' = count (infer_st_next_uvar st') /\
        t1 = convert_t (t_walkstar s' t') /\
        t1 = convert_t (t_walkstar s' t) /\
        t_wfs s /\
        EVERY (\(n,t). check_t tvs {} (t_walkstar s' t))
          new_bindings /\
        convert_env s' new_bindings = tenv1)`)
  CHEAT_TAC;;

let unconvert_11 = cake_theorem "unconvert_11[local]"
  (fun () ->
    `!t1 t2. check_freevars 0 [] t1 /\ check_freevars 0 [] t2 ==>
     (unconvert_t t1 = unconvert_t t2 <=> t1 = t2)`)
  CHEAT_TAC;;

let infer_e_type_pe_determ = cake_theorem "infer_e_type_pe_determ"
  (fun () ->
    `!loc ienv p e st st' t t' tenv' s.
      ALL_DISTINCT (MAP FST tenv') /\
      ienv_ok {} ienv /\
      env_rel_complete FEMPTY ienv tenv typeSystem_Empty /\
      infer_e loc ienv e (init_infer_state ss) = (M_success t,st)
        /\
      infer_p loc ienv p st = (M_success (t',tenv'),st') /\
      t_unify (infer_st_subst st') t t' = SOME s /\
      EVERY (\(n,t). check_t 0 {} (t_walkstar s t)) tenv' ==>
      type_pe_determ tenv typeSystem_Empty p e`)
  CHEAT_TAC;;

let t_vars_check_t = cake_theorem "t_vars_check_t"
  (fun () ->
    `(!t.
     ~check_t 0 {} t /\
     check_t 0 s t ==>
     (?n'. n' IN s /\ n' IN t_vars t)) /\
     (!ts.
     !x. MEM x ts ==>
     ~check_t 0 {} x /\
     check_t 0 s x ==>
     (?n'. n' IN s /\ n' IN t_vars x))`)
  CHEAT_TAC;;

let t_walkstar_diff = cake_theorem "t_walkstar_diff"
  (fun () ->
    `t_wfs s1 /\ t_wfs s2 /\
     (~(t_walkstar s1 (Infer_Tuvar n) = t_walkstar s2 (Infer_Tuvar
       n))) ==>
     (!t. (n IN t_vars t) ==> ~(t_walkstar s1 t = t_walkstar s2 t))
       /\
     (!ts.
     !x. MEM x ts ==>
     n IN t_vars x ==> ~(t_walkstar s1 x = t_walkstar s2 x))`)
  CHEAT_TAC;;

(* HOL4 type_eDetermScript.sml:233-239: a theorem that HOL4 states as
   the value of an ML expression *)

let type_pe_determ_infer_e = cake_theorem "type_pe_determ_infer_e"
  (fun () ->
    `!loc ienv p e st st' t t' new_bindings s.
      ALL_DISTINCT (MAP FST new_bindings) /\
      env_rel_sound FEMPTY ienv tenv typeSystem_Empty /\
      ienv_ok {} ienv /\
      infer_e loc ienv e (init_infer_state ss) = (M_success t,st)
        /\
      infer_p loc ienv p st = (M_success (t',new_bindings),st') /\
      t_unify (infer_st_subst st') t t' = SOME s /\
      type_pe_determ tenv typeSystem_Empty p e ==>
      EVERY (\(n,t). check_t 0 {} (t_walkstar s t)) new_bindings`)
  CHEAT_TAC;;

(* HOL4 type_eDetermScript.sml:442-450: code that the source has in a
   comment *)

let infer_funs_complete = cake_theorem "infer_funs_complete"
  (fun () ->
    `ienv_ok {} ienv /\
     tenv_ok tenv /\
     env_rel_complete FEMPTY ienv tenv typeSystem_Empty /\
     type_funs tenv (bind_var_list 0 bindings (bind_tvar tvs
       typeSystem_Empty)) funs bindings ==>
     (?funs_ts st st' constr s.
     infer_funs loc
     (inf_env_inf_v_fupd (K (nsAppend (alist_to_ns (MAP2 (\(f,x,e)
       uvar. (f,0,uvar)) funs (MAP (\n. Infer_Tuvar n)
        (COUNT_LIST (LENGTH funs))))) (inf_env_inf_v ienv))) ienv)
          funs (infer_st_next_uvar_fupd (K (infer_st_next_uvar
          (init_infer_state ss) + LENGTH funs)) (init_infer_state ss)) =
     (M_success funs_ts,st) /\ infer_st_next_uvar
     st = infer_st_next_uvar st' /\ infer_st_next_id
     st = infer_st_next_id st' /\
     pure_add_constraints (infer_st_subst st)
     (ZIP (MAP (\n. Infer_Tuvar (infer_st_next_uvar
       (init_infer_state ss) + n))
               (COUNT_LIST (LENGTH funs))) funs_ts) (infer_st_subst
                 st') /\
     check_s 0 (count (infer_st_next_uvar st')) (infer_st_subst
       st') /\
     sub_completion tvs (infer_st_next_uvar st') (infer_st_subst
       st') constr s /\
     FDOM s = count (infer_st_next_uvar st') /\
     MAP SND bindings = MAP (convert_t o t_walkstar s) funs_ts)`)
  CHEAT_TAC;;
