(* ======================================================== *)
(*  weakening: ported from HOL4's
    semantics/proofs/weakeningScript.sml
    A proof theory, with 4 definitions and 31 theorems.  Needed by
    typeSound.ml.  *)
(* ======================================================== *)

(*
  Weakening lemmas used in type soundness
*)

needs "semantics/ast.ml";;
needs "semantics/namespace.ml";;
needs "semantics/proofs/namespaceProps.ml";;
needs "semantics/proofs/typeSoundInvariants.ml";;
needs "semantics/proofs/typeSysProps.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "semantics/typeSystem.ml";;
(* HOL4 ancestors outside the port: option rich_list alist *)

let weak_tenvE_def = cake_define
  `weak_tenvE tenv tenv' =
     (num_tvs tenv >= num_tvs tenv' /\
      (!n inc tvs t.
       (tveLookup n inc tenv' = SOME (tvs,t)) <=>
       (tveLookup n inc tenv = SOME (tvs,t))))`;;

let weakS_def = cake_define
  `weakS tenvS tenvS' <=> tenvS' SUBMAP tenvS`;;

let weak_tenvE_refl = cake_theorem "weak_tenvE_refl"
  (fun () ->
    `!tenvE. weak_tenvE tenvE tenvE`)
  CHEAT_TAC;;

(* HOL4 weakeningScript.sml:29-37: code that the source has in a
   comment *)

let weak_tenv_refl = cake_theorem "weak_tenv_refl"
  (fun () ->
    `!tenv. tenv_val_ok (type_env_v tenv) ==> weak_tenv tenv tenv`)
  CHEAT_TAC;;

let weakS_refl = cake_theorem "weakS_refl"
  (fun () ->
    `!tenvS. weakS tenvS tenvS`)
  CHEAT_TAC;;

let weakS_bind = cake_theorem "weakS_bind"
  (fun () ->
    `!l t tenvS. FLOOKUP tenvS l = NONE ==> weakS (tenvS |+ (l,t))
  tenvS`)
  CHEAT_TAC;;

let weak_tenvE_freevars = cake_theorem "weak_tenvE_freevars[local]"
  (fun () ->
    `!tenv tenv' tvs t.
     weak_tenvE tenv' tenv /\
     check_freevars (num_tvs tenv) tvs t ==>
     check_freevars (num_tvs tenv') tvs t`)
  CHEAT_TAC;;

let weak_tenvE_bind = cake_theorem "weak_tenvE_bind[local]"
  (fun () ->
    `!tenv tenv' n tvs t.
     weak_tenvE tenv' tenv ==>
     weak_tenvE (typeSystem_Bind_name n tvs t tenv')
       (typeSystem_Bind_name n tvs t tenv)`)
  CHEAT_TAC;;

let weak_tenvE_opt_bind = cake_theorem "weak_tenvE_opt_bind[local]"
  (fun () ->
    `!tenv tenv' n tvs t.
     weak_tenvE tenv' tenv ==>
     weak_tenvE (opt_bind_name n tvs t tenv') (opt_bind_name n
       tvs t tenv)`)
  CHEAT_TAC;;

let weak_tenvE_bind_tvar = cake_theorem "weak_tenvE_bind_tvar[local]"
  (fun () ->
    `!tenv tenv' tvs.
     weak_tenvE tenv' tenv ==>
     weak_tenvE (bind_tvar tvs tenv') (bind_tvar tvs tenv)`)
  CHEAT_TAC;;

let weak_tenvE_bind_tvar2 = cake_theorem "weak_tenvE_bind_tvar2[local]"
  (fun () ->
    `!tenv tenv' n tvs t.
     tenv_val_exp_ok tenv /\
     num_tvs tenv = 0 /\
     weak_tenvE tenv' tenv ==>
     weak_tenvE (bind_tvar tvs tenv') (bind_tvar 0 tenv)`)
  CHEAT_TAC;;

let weak_tenvE_bind_var_list =
  cake_theorem "weak_tenvE_bind_var_list[local]"
  (fun () ->
    `!bindings tenvE tenvE' n tvs t.
     weak_tenvE tenvE' tenvE ==>
     weak_tenvE (bind_var_list tvs bindings tenvE')
       (bind_var_list tvs bindings tenvE)`)
  CHEAT_TAC;;

let eLookupC_weak = cake_theorem "eLookupC_weak[local]"
  (fun () ->
    `!cn tenv tenv' tvs ts tn.
       weak_tenv tenv' tenv /\
       nsLookup (type_env_c tenv) cn = SOME (tvs,ts,tn) ==>
       nsLookup (type_env_c tenv') cn = SOME (tvs,ts,tn)`)
  CHEAT_TAC;;

let eLookupV_weak = cake_theorem "eLookupV_weak[local]"
  (fun () ->
    `!n tenv tenv' tvs t.
       weak_tenv tenv' tenv /\
       nsLookup (type_env_v tenv) n = SOME (tvs,t) ==>
       (?tvs' t'. nsLookup (type_env_v tenv') n = SOME (tvs',t')
         /\ tscheme_inst (tvs,t) (tvs',t'))`)
  CHEAT_TAC;;

(* HOL4 weakeningScript.sml:159-201: code that the source has in a
   comment *)

let weak_def = cake_define
  `weak tenv' tenv <=> type_env_t
     tenv' = type_env_t tenv /\ weak_tenv tenv' tenv`;;

let type_p_weakening = cake_theorem "type_p_weakening"
  (fun () ->
    `(!tvs tenv p t bindings. type_p tvs tenv p t bindings ==>
        (!tenv' tvs'. tvs' >= tvs /\ weak tenv' tenv ==> type_p
          tvs' tenv' p t bindings)) /\
     (!tvs tenv ps ts bindings. type_ps tvs tenv ps ts bindings ==>
        (!tenv' tvs'. tvs' >= tvs /\ weak tenv' tenv ==> type_ps
          tvs' tenv' ps ts bindings))`)
  CHEAT_TAC;;

let type_e_weakening_lem = cake_theorem "type_e_weakening_lem[local]"
  (fun () ->
    `(!tenv tenvE e t. type_e tenv tenvE e t ==>
       (!tenv' tenvE'. weak tenv' tenv /\ weak_tenvE tenvE' tenvE
         ==> type_e tenv' tenvE' e t)) /\
     (!tenv tenvE es ts. type_es tenv tenvE es ts ==>
       (!tenv' tenvE'. weak tenv' tenv /\ weak_tenvE tenvE' tenvE
         ==> type_es tenv' tenvE' es ts)) /\
     (!tenv tenvE funs bindings. type_funs tenv tenvE funs bindings
       ==>
       (!tenv' tenvE'. weak tenv' tenv /\ weak_tenvE tenvE' tenvE
         ==> type_funs tenv' tenvE' funs bindings))`)
  CHEAT_TAC;;

let type_e_weakening = cake_theorem "type_e_weakening"
  (fun () ->
    `(!tenv tenvE e t tenv' tenvE'.
       type_e tenv tenvE e t /\ weak tenv' tenv /\ weak_tenvE
         tenvE' tenvE ==> type_e tenv' tenvE' e t) /\
     (!tenv tenvE es ts tenv' tenvE'.
       type_es tenv tenvE es ts /\ weak tenv' tenv /\ weak_tenvE
         tenvE' tenvE ==> type_es tenv' tenvE' es ts) /\
     (!tenv tenvE funs bindings tenv' tenvE'.
       type_funs tenv tenvE funs bindings /\ weak tenv' tenv /\
         weak_tenvE tenvE' tenvE ==> type_funs tenv' tenvE' funs
         bindings)`)
  CHEAT_TAC;;

let gt_0 = cake_theorem "gt_0[local]"
  (fun () ->
    `!(x:num). x >= 0`)
  CHEAT_TAC;;

let weakCT_def = cake_define
  `weakCT cenv_impl cenv_spec <=> cenv_spec SUBMAP cenv_impl`;;

let weak_ctMap_lookup = cake_theorem "weak_ctMap_lookup[local]"
  (fun () ->
    `!ctMap ctMap' tvs ts stamp.
     weakCT ctMap' ctMap /\
     FLOOKUP ctMap stamp = SOME (tvs,ts) ==>
     FLOOKUP ctMap' stamp = SOME (tvs,ts)`)
  CHEAT_TAC;;

let weakCT_refl = cake_theorem "weakCT_refl"
  (fun () ->
    `!ctMap. weakCT ctMap ctMap`)
  CHEAT_TAC;;

let weakCT_trans = cake_theorem "weakCT_trans"
  (fun () ->
    `weakCT C1 C2 /\ weakCT C2 C3 ==> weakCT C1 C3`)
  CHEAT_TAC;;

let disjoint_env_weakCT = cake_theorem "disjoint_env_weakCT"
  (fun () ->
    `!ctMap ctMap'.
      DISJOINT (FDOM ctMap') (FDOM ctMap) ==>
      weakCT (FUNION ctMap' ctMap) ctMap`)
  CHEAT_TAC;;

let weakCT2 = cake_theorem "weakCT2"
  (fun () ->
    `!ctMap ctMap'. weakCT (FUNION ctMap' ctMap) ctMap'`)
  CHEAT_TAC;;

let type_tenv_ctor_weakening = cake_theorem "type_tenv_ctor_weakening"
  (fun () ->
    `!ctMap tenvC envC ctMap'.
      weakCT ctMap' ctMap /\
      nsAll2 (type_ctor ctMap) envC tenvC ==>
      nsAll2 (type_ctor ctMap') envC tenvC`)
  CHEAT_TAC;;

let type_tenv_val_weakening_lemma =
  cake_theorem "type_tenv_val_weakening_lemma[local]"
  (fun () ->
    `!ctMap tenvS tenvV envV ctMap' tenvS'.
     weakCT ctMap' ctMap /\
     weakS tenvS' tenvS /\
     nsAll2 (\i v (tvs,t).
             !tvs' ctMap' tenvS'.
               (tvs = 0 \/ tvs = tvs') /\
               weakCT ctMap' ctMap /\
               weakS tenvS' tenvS ==>
               type_v tvs' ctMap' tenvS' v t)
            envV tenvV ==>
     nsAll2 (\i v (tvs,t). type_v tvs ctMap' tenvS' v t) envV
       tenvV`)
  CHEAT_TAC;;

let weakening_remove_lambda_prod =
  cake_theorem "remove_lambda_prod[local]"
  (fun () ->
    `(\(x,y). P x y) = (\xy. P (FST xy) (SND xy))`)
  CHEAT_TAC;;

let type_v_weakening = cake_theorem "type_v_weakening"
  (fun () ->
    `(!tvs ctMap tenvS v t. type_v tvs ctMap tenvS v t ==>
        (!tvs' ctMap' tenvS'.
          ((tvs = 0) \/ (tvs = tvs')) /\ weakCT ctMap' ctMap /\
            weakS tenvS' tenvS ==>
          type_v tvs' ctMap' tenvS' v t))`)
  CHEAT_TAC;;

let type_all_env_weakening = cake_theorem "type_all_env_weakening"
  (fun () ->
    `!ctMap tenvS tenv env ctMap' tenvS'.
      weakCT ctMap' ctMap /\
      weakS tenvS' tenvS /\
      type_all_env ctMap tenvS env tenv ==>
      type_all_env ctMap' tenvS' env tenv`)
  CHEAT_TAC;;

let type_sv_weakening = cake_theorem "type_sv_weakening"
  (fun () ->
    `!ctMap tenvS st sv ctMap' tenvS'.
      type_sv ctMap tenvS sv st /\
      weakCT ctMap' ctMap /\
      weakS tenvS' tenvS ==>
      type_sv ctMap' tenvS' sv st`)
  CHEAT_TAC;;

let type_s_weakening = cake_theorem "type_s_weakening"
  (fun () ->
    `!ctMap tenvS st ctMap'.
      type_s ctMap tenvS st /\
      weakCT ctMap' ctMap ==>
      type_s ctMap' tenvS st`)
  CHEAT_TAC;;

(* HOL4 weakeningScript.sml:577-648: code that the source has in a
   comment *)

let weak_tenv_extend_dec_tenv = cake_theorem "weak_tenv_extend_dec_tenv"
  (fun () ->
    `!tenv1 tenv2 tenv3.
      tenv_val_ok (type_env_v tenv1) /\
      weak_tenv tenv2 tenv3 ==>
      weak_tenv (extend_dec_tenv tenv1 tenv2) (extend_dec_tenv
        tenv1 tenv3)`)
  CHEAT_TAC;;

let weak_extend_dec_tenv = cake_theorem "weak_extend_dec_tenv"
  (fun () ->
    `tenv_ok tenv1 /\ weak tenv2 tenv3 ==> weak (extend_dec_tenv tenv1
  tenv2) (extend_dec_tenv tenv1 tenv3)`)
  CHEAT_TAC;;

let type_d_weakening = cake_theorem "type_d_weakening"
  (fun () ->
    `(!check tenv d decls tenv'.
      type_d check tenv d decls tenv' ==>
      (!tenv''.
      check = F /\
      tenv_ok tenv'' /\
      weak tenv'' tenv ==>
      type_d check tenv'' d decls tenv')) /\
     (!check tenv d decls tenv'.
      type_ds check tenv d decls tenv' ==>
      (!tenv''.
      check = F /\
      tenv_ok tenv'' /\
      weak tenv'' tenv ==>
      type_ds check tenv'' d decls tenv'))`)
  CHEAT_TAC;;

(* HOL4 weakeningScript.sml:729-877: code that the source has in a
   comment *)

(* HOL4 weakeningScript.sml:879-913: code that the source has in a
   comment *)
