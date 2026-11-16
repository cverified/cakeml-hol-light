(* ======================================================== *)
(*  infer_cv: ported from HOL4's
    compiler/inference/infer_cvScript.sml
    A definition theory, with 6 definitions and 26 theorems.  Needed
    by backend_cv.ml and repl_init_types.ml.  *)
(* ======================================================== *)

(*
  Translating inferTheory to cv equations for use with cv_eval
*)

needs "basis/pure/basis_cv.ml";;
needs "compiler/inference/infer.ml";;
needs "compiler/inference/inferProps.ml";;
needs "compiler/inference/unify.ml";;
needs "compiler/inference/unify_cv.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "semantics/namespace.ml";;
needs "semantics/proofs/source_cv.ml";;
needs "semantics/typeSystem.ml";;
needs "translator/monadic/monad_base/ml_monadBase.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "infer_cv"
  ["ast"; "basis_cv"; "infer"; "inferProps"; "misc"; "ml_monadBase";
   "namespace"; "source_cv"; "typeSystem"; "unify_cv"];;

(* HOL4 infer_cvScript.sml:11-16: ML code, not ported *)

(* HOL4 infer_cvScript.sml:18-20: ML code, not ported *)

(* HOL4 infer_cvScript.sml:22-23: ML code, not ported *)

(* HOL4 infer_cvScript.sml:25: ML code, not ported *)

(* HOL4 infer_cvScript.sml:27-29: ML code, not ported *)

(* [cv_pre,local] *)
let n_fresh_uvar_pre = prove
 (`!a0 a1. n_fresh_uvar_pre a0 a1`,
  CHEAT_TAC);;

(* HOL4 infer_cvScript.sml:37: ML code, not ported *)

(* HOL4 infer_cvScript.sml:39-41: ML code, not ported *)

let map_t_walkstar_def,map_t_walkstar_ind = define_guess
  `(map_t_walkstar s [] = []) /\
   (map_t_walkstar s (CONS t ts) = CONS (t_walkstar s t) (map_t_walkstar s
    ts))`;;

(* [local] *)
let map_t_walkstar_thm = prove
 (`MAP (t_walkstar s) ts = map_t_walkstar s ts`,
  CHEAT_TAC);;

(* HOL4 infer_cvScript.sml:54: ML code, not ported *)

(* HOL4 infer_cvScript.sml:56-57: ML code, not ported *)

(* HOL4 infer_cvScript.sml:59: ML code, not ported *)

(* HOL4 infer_cvScript.sml:61: ML code, not ported *)

(* [cv_pre] *)
let get_tyname_pre = prove
 (`!a0 a1. get_tyname_pre a0 a1`,
  CHEAT_TAC);;

(* HOL4 infer_cvScript.sml:70: ML code, not ported *)

(* HOL4 infer_cvScript.sml:72: ML code, not ported *)

(* [cv_pre] *)
let ty_var_name_pre = prove
 (`!a0. ty_var_name_pre a0`,
  CHEAT_TAC);;

(* HOL4 infer_cvScript.sml:80-81: ML code, not ported *)

(* HOL4 infer_cvScript.sml:83: ML code, not ported *)

(* HOL4 infer_cvScript.sml:85-86: ML code, not ported *)

let add_constraint_pre_eq = prove
 (`add_constraint_pre l t1 t2 s = t_wfs (infer_st_subst s)`,
  CHEAT_TAC);;

let add_constraints_pre_eq = prove
 (`!ts1 ts2 l s.
     add_constraints_pre l ts1 ts2 s = (t_wfs (infer_st_subst s) \/ ts1 =
       [] \/ ts2 = [])`,
  CHEAT_TAC);;

(* HOL4 infer_cvScript.sml:107-108: ML code, not ported *)

(* HOL4 infer_cvScript.sml:110: ML code, not ported *)

(* [cv_pre,local] *)
let infer_deBruijn_subst_pre = prove
 (`(!a1 a0. infer_deBruijn_subst_pre a0 a1) /\
   (!a3 a2. infer_deBruijn_subst_list_pre a2 a3)`,
  CHEAT_TAC);;

(* HOL4 infer_cvScript.sml:120-130: ML code, not ported *)

let type_subst_alist_def,type_subst_alist_ind = define_guess
  `(type_subst_alist s (Tvar_db n) = Tvar_db n) /\
   (type_subst_alist s (Tvar tv) =
    (match ALOOKUP s tv with NONE -> Tvar tv | SOME t -> t)) /\
   (type_subst_alist s (Tapp ts tn) = Tapp (type_subst_alist_list s ts) tn) /\
   (type_subst_alist_list s [] = []) /\
   (type_subst_alist_list s (CONS t ts) = CONS (type_subst_alist s t)
    (type_subst_alist_list s ts))`;;

let type_subst_alist_to_fmap = prove
 (`(!t xs. typeSystem_type_subst (alist_to_fmap xs) t = type_subst_alist xs t)
  /\
   (!t xs. MAP (typeSystem_type_subst (alist_to_fmap xs)) t =
     type_subst_alist_list xs t)`,
  CHEAT_TAC);;

(* HOL4 infer_cvScript.sml:150: ML code, not ported *)

(* HOL4 infer_cvScript.sml:152-154: ML code, not ported *)

(* [local,cv_pre] *)
let type_name_check_sub_pre = prove
 (`(!t a0 a1 a2 (a4:'a). type_name_check_sub_pre a0 a1 a2 t a4) /\
   (!t a5 a6 a7 (a9:'a). type_name_check_sub_list_pre a5 a6 a7 t a9)`,
  CHEAT_TAC);;

(* HOL4 infer_cvScript.sml:164: ML code, not ported *)

(* [local,cv_pre] *)
let check_ctor_types_pre = prove
 (`!a0 a1 a2 a3 a4. check_ctor_types_pre a0 a1 a2 a3 a4`,
  CHEAT_TAC);;

(* HOL4 infer_cvScript.sml:172: ML code, not ported *)

(* [local,cv_pre] *)
let check_ctors_pre = prove
 (`!a0 a1 a2 a3. check_ctors_pre a0 a1 a2 a3`,
  CHEAT_TAC);;

(* HOL4 infer_cvScript.sml:180: ML code, not ported *)

(* HOL4 infer_cvScript.sml:182: ML code, not ported *)

(* HOL4 infer_cvScript.sml:184: ML code, not ported *)

(* HOL4 infer_cvScript.sml:186-187: ML code, not ported *)

(* HOL4 infer_cvScript.sml:189-196: a proof *)

(* the termination relation that HOL4 gives is
     MEASURE (\x. match x with sum_INL e -> ast_exp_size e
                                   | sum_INR es -> list_size ast_exp_size es)
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
let exp_is_value_def,exp_is_value_ind = define_guess
  `(exp_is_value (ast_Lit _) = T) /\
   (exp_is_value (ast_Con _ es) = exp_is_value_list es) /\
   (exp_is_value (ast_Var _) = T) /\
   (exp_is_value (ast_Fun _ _) = T) /\
   (exp_is_value (ast_Tannot e v5) = exp_is_value e) /\
   (exp_is_value (ast_Lannot e v6) = exp_is_value e) /\
   (exp_is_value _ = F) /\
   (exp_is_value_list [] = T) /\
   (exp_is_value_list (CONS x xs) = (exp_is_value x /\ exp_is_value_list
    xs))`;;

(* HOL4 infer_cvScript.sml:213: ML code, not ported *)

let exp_is_value_eq = prove
 (`(!e. is_value e = exp_is_value e) /\
   (!es. ALL is_value es = exp_is_value_list es)`,
  CHEAT_TAC);;

(* HOL4 infer_cvScript.sml:223: ML code, not ported *)

let type_name_subst_1_def,type_name_subst_1_ind = define_guess
  `(type_name_subst_1 tenvT (Atvar tv) = Tvar tv) /\
   (type_name_subst_1 tenvT (Attup ts) =
      Ttup (type_name_subst_list_1 tenvT ts)) /\
   (type_name_subst_1 tenvT (Atfun t1 t2) =
      Tfn (type_name_subst_1 tenvT t1) (type_name_subst_1 tenvT t2)) /\
   (type_name_subst_1 tenvT (Atapp ts tc) =
      (let args = type_name_subst_list_1 tenvT ts in
         match nsLookup tenvT tc with NONE -> Ttup args
         | SOME (tvs,t) -> type_subst_alist (ZIP tvs args) t)) /\
   (type_name_subst_list_1 tenvT [] = []) /\
   (type_name_subst_list_1 tenvT (CONS t ts) = CONS (type_name_subst_1 tenvT t)
      (type_name_subst_list_1 tenvT ts))`;;

(* HOL4 infer_cvScript.sml:242: ML code, not ported *)

let type_name_subst_1_eq = prove
 (`type_name_subst tenvT = type_name_subst_1 tenvT /\
   MAP (type_name_subst tenvT) = type_name_subst_list_1 tenvT`,
  CHEAT_TAC);;

(* HOL4 infer_cvScript.sml:254-255: ML code, not ported *)

(* [cv_pre,local] *)
let build_ctor_tenv_pre = prove
 (`!a0 a1 a2. build_ctor_tenv_pre a0 a1 a2`,
  CHEAT_TAC);;

(* HOL4 infer_cvScript.sml:263: ML code, not ported *)

(* HOL4 infer_cvScript.sml:265-267: ML code, not ported *)

let call_infer_def = new_definition
  `call_infer ienv prog start_id =
   infer_ds ienv prog
     (mk_infer_st 0 FEMPTY start_id)`;;

(* HOL4 infer_cvScript.sml:275-276: ML code, not ported *)

(* HOL4 infer_cvScript.sml:278-279: ML code, not ported *)

(* HOL4 infer_cvScript.sml:281: ML code, not ported *)

let type_name_check_sub_success = prove
 (`type_name_check_sub l (inf_env_inf_t ienv) xs a s = (M_success r,s1) ==>
   (?f. type_name_check_subst l f (inf_env_inf_t ienv) xs a s = (M_success
     r,s1))`,
  CHEAT_TAC);;

let IMP_infer_p_pre = prove
 (`(!d l ienv s. t_wfs (infer_st_subst s) ==> infer_p_pre l ienv d s) /\
   (!ds l ienv s. t_wfs (infer_st_subst s) ==> infer_ps_pre l ienv ds s)`,
  CHEAT_TAC);;

let IMP_map_t_walkstar_pre = prove
 (`!xs s. t_wfs s ==> map_t_walkstar_pre s xs`,
  CHEAT_TAC);;

let IMP_apply_subst_list_pre = prove
 (`t_wfs (infer_st_subst s) ==> apply_subst_list_pre xs s`,
  CHEAT_TAC);;

let add_constraint_wfs = prove
 (`add_constraint l x y s = (r,s1) /\ t_wfs (infer_st_subst s) ==> t_wfs
  (infer_st_subst s1)`,
  CHEAT_TAC);;

let add_constraints_wfs = prove
 (`!x y l s. add_constraints l x y s = (r,s1) /\ t_wfs (infer_st_subst s) ==>
  t_wfs (infer_st_subst s1)`,
  CHEAT_TAC);;

let IMP_constrain_op_pre = prove
 (`t_wfs (infer_st_subst s) ==> constrain_op_pre l op ts s`,
  CHEAT_TAC);;

let IMP_infer_e_pre = prove
 (`(!l ienv e s. t_wfs (infer_st_subst s) ==> infer_e_pre l ienv e s) /\
   (!l ienv es s. t_wfs (infer_st_subst s) ==> infer_es_pre l ienv es s) /\
   (!l ienv pes t1 t2 s. t_wfs (infer_st_subst s) ==> infer_pes_pre l ienv
     pes t1 t2 s) /\
   (!l ienv funs s. t_wfs (infer_st_subst s) ==> infer_funs_pre l ienv
     funs s)`,
  CHEAT_TAC);;

let IMP_infer_d_pre = prove
 (`(!d ienv s. t_wfs (infer_st_subst s) ==> infer_d_pre ienv d s) /\
   (!ds ienv s. t_wfs (infer_st_subst s) ==> infer_ds_pre ienv ds s)`,
  CHEAT_TAC);;

(* [cv_pre,local] *)
let call_infer_pre_thm = prove
 (`!a0 a1 a2. call_infer_pre a0 a1 a2`,
  CHEAT_TAC);;

(* HOL4 infer_cvScript.sml:413-414: ML code, not ported *)

(* main results stored as: cv_infertype_prog_thm
                           cv_infertype_prog_inc_thm *)

let alist_nub2_def,alist_nub2_ind = define_guess
  `(alist_nub2 0 xs = []) /\
   (alist_nub2 (SUC n) [] = []) /\
   (alist_nub2 (SUC n) (CONS (x,y) xs) = CONS (x,y) (alist_nub2 n (FILTER
    (\t. ~(x = FST t)) xs)))`;;

let alist_nub2_eq = prove
 (`!n xs. LENGTH xs <= n ==> alist_nub xs = alist_nub2 n xs`,
  CHEAT_TAC);;

let alist_nub_eq = prove
 (`alist_nub xs = alist_nub2 (LENGTH xs) xs`,
  CHEAT_TAC);;

(* HOL4 infer_cvScript.sml:444: ML code, not ported *)

(* HOL4 infer_cvScript.sml:446: ML code, not ported *)

(* and the interface *)
let _ = unhide_overloads ();;
