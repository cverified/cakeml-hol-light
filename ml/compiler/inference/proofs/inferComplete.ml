(* ======================================================== *)
(*  inferComplete: ported from HOL4's
    compiler/inference/proofs/inferCompleteScript.sml
    A proof theory, with no definitions and 11 theorems.  Needed by
    compilerProof.ml.  *)
(* ======================================================== *)

(*
  Proves completeness of the type inferencer, i.e. if there is a type
  for the program, then the type inferencer will find a type (the most
  general type).
*)

needs "compiler/inference/infer.ml";;
needs "compiler/inference/inferProps.ml";;
needs "compiler/inference/infer_t.ml";;
needs "compiler/inference/proofs/envRel.ml";;
needs "compiler/inference/proofs/infer_eComplete.ml";;
needs "compiler/inference/proofs/infer_eSound.ml";;
needs "compiler/inference/proofs/type_dCanon.ml";;
needs "compiler/inference/proofs/type_eDeterm.ml";;
needs "compiler/inference/unify.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "semantics/namespace.ml";;
needs "semantics/proofs/namespaceProps.ml";;
needs "semantics/proofs/typeSysProps.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "semantics/typeSystem.ml";;
needs "translator/monadic/monad_base/ml_monadBase.ml";;

(* the theories whose names the Ancestors blocks of the source
   bring, which are the ones that its statements read: the
   overloads of every other theory come out of the interface
   while this file loads *)
let _ = hol4_ancestors "inferComplete"
  ["ast"; "envRel"; "infer"; "inferProps"; "infer_eComplete";
   "infer_eSound"; "infer_t"; "namespaceProps"; "semanticPrimitives";
   "typeSysProps"; "typeSystem"; "type_dCanon"; "type_eDeterm";
   "unify"];;


(* [local] *)
let generalise_no_uvars = prove
 (`(!t m n s dbvars.
   check_t dbvars {} t ==>
   generalise m n s t = (0,s,t)) /\
   (!ts m n s dbvars.
   ALL (check_t dbvars {}) ts ==>
   generalise_list m n s ts = (0,s,ts))`,
  CHEAT_TAC);;

(* HOL4 inferCompleteScript.sml:39-45: ML code, not ported *)

let env_rel_binding_lemma = prove
 (`!t fvs fvs' subst.
    check_freevars 0 fvs' t /\
    set_of_list fvs' SUBSET set_of_list fvs /\
    ALL_DISTINCT fvs' ==>
    infer_deBruijn_subst subst
      (infer_type_subst (ZIP fvs' (MAP Infer_Tvar_db (COUNT_LIST
        (LENGTH (fvs'))))) t) =
    infer_deBruijn_subst
      (list_of_seq (\n.
           infer_deBruijn_subst subst
             (match find_index (EL n fvs) fvs' 0 with
                NONE -> Infer_Tapp [] arb | SOME t -> Infer_Tvar_db
                  t)) (LENGTH fvs))
      (infer_type_subst (ZIP fvs (list_of_seq (\x. Infer_Tvar_db x)
        (LENGTH fvs))) t)`,
  CHEAT_TAC);;

let env_rel_binding_lemma2 = prove
 (`!t fvs fvs' subst.
    check_freevars 0 fvs' t /\
    set_of_list fvs' SUBSET set_of_list fvs /\
    ALL_DISTINCT fvs' ==>
    infer_deBruijn_subst subst
      (infer_type_subst (ZIP fvs (list_of_seq (\x. Infer_Tvar_db x)
        (LENGTH fvs))) t) =
    infer_deBruijn_subst
      (list_of_seq (\n.
           infer_deBruijn_subst subst
             (match find_index (EL n fvs') fvs 0 with
                NONE -> Infer_Tapp [] TC_int | SOME t ->
                  Infer_Tvar_db t)) (LENGTH fvs'))
      (infer_type_subst (ZIP fvs' (MAP Infer_Tvar_db (COUNT_LIST
        (LENGTH fvs')))) t)`,
  CHEAT_TAC);;

let unconvert_type_subst = prove
 (`(!t subst fvs.
     check_freevars 0 fvs t /\ set_of_list fvs SUBSET set_of_list
       (MAP FST subst) ==>
     unconvert_t (type_subst (alist_to_fmap subst) t) =
     infer_type_subst (MAP (\(x,y). (x,unconvert_t y)) subst) t) /\
   (!ts subst fvs.
     ALL (check_freevars 0 fvs) ts /\ set_of_list fvs SUBSET
       set_of_list (MAP FST subst) ==>
     MAP (unconvert_t o type_subst (alist_to_fmap subst)) ts =
     MAP (infer_type_subst (MAP (\(x,y). (x,unconvert_t y)) subst))
       ts)`,
  CHEAT_TAC);;

let env_rel_binding = prove
 (`!fvs t fvs' name.
   check_freevars 0 fvs' t /\
   set_of_list fvs' SUBSET set_of_list fvs ==>
   envRel_env_rel
     (mk_type_env
        (nsSing name
          (LENGTH fvs,
           type_subst
             (alist_to_fmap (ZIP fvs (MAP Tvar_db (list_of_seq (\x.
               x) (LENGTH fvs)))))
             t)) nsEmpty nsEmpty)
    (mk_inf_env
        (nsSing name
          (LENGTH (nub fvs'),
           infer_type_subst
             (ZIP (nub fvs') (MAP Infer_Tvar_db (COUNT_LIST (LENGTH
               (nub fvs')))))
             t)) nsEmpty nsEmpty)`,
  CHEAT_TAC);;

(* [local] *)
let env_rel_complete_bind = prove
 (`env_rel_complete FEMPTY ienv tenv typeSystem_Empty ==>
   env_rel_complete FEMPTY ienv tenv (bind_tvar tvs
     typeSystem_Empty)`,
  CHEAT_TAC);;

let type_pe_determ_canon_infer_e = prove
 (`!loc ienv p e st st' t t' new_bindings s.
    ALL_DISTINCT (MAP FST new_bindings) /\
    env_rel_sound FEMPTY ienv tenv typeSystem_Empty /\
    ienv_ok {} ienv /\
    start_type_id <= infer_st_next_id ss /\
    inf_set_tids_ienv (count (infer_st_next_id ss)) ienv /\
    infer_e loc ienv e (init_infer_state ss) = (M_success t,st) /\
    infer_p loc ienv p st = (M_success (t',new_bindings),st') /\
    t_unify (infer_st_subst st') t t' = SOME s /\
    type_pe_determ_canon (infer_st_next_id ss) tenv typeSystem_Empty
      p e ==>
    ALL (\(n,t). check_t 0 {} (t_walkstar s t)) new_bindings`,
  CHEAT_TAC);;


(* HOL4 inferCompleteScript.sml:569-570: ML code, not ported *)

(* [local] *)
let ap_lemma = prove
 (`!f. x = y ==> f x = f y`,
  CHEAT_TAC);;

let inf_set_tids_extend_dec_ienv = prove
 (`inf_set_tids_ienv (count n) ienv2 /\
    inf_set_tids_ienv (count m) ienv /\ m <= n ==>
      inf_set_tids_ienv (count n) (extend_dec_ienv ienv2 ienv)`,
  CHEAT_TAC);;

let infer_d_complete_canon = prove
 (`(!d n tenv ids tenv' ienv st1.
    type_d_canon n tenv d ids tenv' /\
    envRel_env_rel tenv ienv /\
    inf_set_tids_ienv (count n) ienv /\ infer_st_next_id
    st1 = n /\ start_type_id <= n ==>
    (?ienv' st2.
      envRel_env_rel tenv' ienv' /\ infer_st_next_id
      st2 = infer_st_next_id st1 + ids /\
      infer_d ienv d st1 = (M_success ienv',st2))) /\
   (!ds n tenv ids tenv' ienv st1.
    type_ds_canon n tenv ds ids tenv' /\
    envRel_env_rel tenv ienv /\
    inf_set_tids_ienv (count n) ienv /\ infer_st_next_id
    st1 = n /\ start_type_id <= n ==>
    (?ienv' st2.
      envRel_env_rel tenv' ienv' /\ infer_st_next_id
      st2 = infer_st_next_id st1 + ids /\
      infer_ds ienv ds st1 = (M_success ienv',st2)))`,
  CHEAT_TAC);;

let infer_ds_complete = prove
 (`type_ds T tenv ds ids tenv' /\
   envRel_env_rel tenv ienv /\
   // do you need both of these?
   inf_set_tids_ienv (count (infer_st_next_id st1)) ienv /\
   set_tids_tenv (count (infer_st_next_id st1)) tenv /\
   DISJOINT ids (count (infer_st_next_id st1)) /\
   start_type_id <= infer_st_next_id st1 ==>
   (?g mapped_tenv' ienv' st2.
     infer_ds ienv ds st1 = (M_success ienv',st2) /\
     // BIJ g (count st1.next_id ∪ count ids) (count (st1.next_id + ids)) ∧
     tenv_equiv (remap_tenv g tenv') mapped_tenv' /\
     envRel_env_rel mapped_tenv' ienv' /\ infer_st_next_id
     st2 = infer_st_next_id st1 + CARD ids)`,
  CHEAT_TAC);;

(* HOL4 inferCompleteScript.sml:1446-1788: code that the source has
   in a comment *)

(* and the overloads that this file cannot see are back in the
   interface *)
let _ = unhide_overloads ();;
