(* ======================================================== *)
(*  typeSysProps: ported from HOL4's
    semantics/proofs/typeSysPropsScript.sml
    A proof theory, with 4 definitions and 107 theorems.  Needed by
    11 files of the port.  *)
(* ======================================================== *)

(*
  Theorems about the type system.
*)

needs "semantics/ast.ml";;
needs "semantics/namespace.ml";;
needs "semantics/proofs/namespaceProps.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;
needs "semantics/proofs/typeSoundInvariants.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "semantics/typeSystem.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "typeSysProps"
  ["ast"; "namespace"; "namespaceProps"; "semanticPrimitivesProps";
   "typeSoundInvariants"; "typeSystem"];;

let _ = do_list hide_constant ["id"];;

(* HOL4 typeSysPropsScript.sml:14: ML code, not ported *)
(* HOL4 typeSysPropsScript.sml:15-20: code that the source has in a
   comment *)

(* HOL4 typeSysPropsScript.sml:22-37: ML code, not ported *)

(* ----------- Basic stuff ----------- *)

let unchanged_tenv = prove
 (`!(tenv:type_env).
   mk_type_env (type_env_v tenv) (type_env_c tenv) (type_env_t
     tenv) = tenv`,
  CHEAT_TAC);;
add_simp unchanged_tenv;;

(* HOL4 typeSysPropsScript.sml:48-78: code that the source has in a
   comment *)

let extend_dec_tenv_assoc = prove
 (`!tenv1 tenv2 tenv3.
    extend_dec_tenv tenv1 (extend_dec_tenv tenv2 tenv3) =
    extend_dec_tenv (extend_dec_tenv tenv1 tenv2) tenv3`,
  CHEAT_TAC);;
add_simp extend_dec_tenv_assoc;;

let tenv_val_ok_nsEmpty = prove
 (`tenv_val_ok nsEmpty`,
  CHEAT_TAC);;
add_simp tenv_val_ok_nsEmpty;;

let tenv_ctor_ok_nsEmpty = prove
 (`tenv_ctor_ok nsEmpty`,
  CHEAT_TAC);;
add_simp tenv_ctor_ok_nsEmpty;;

let tenv_abbrev_ok_nsEmpty = prove
 (`tenv_abbrev_ok nsEmpty`,
  CHEAT_TAC);;
add_simp tenv_abbrev_ok_nsEmpty;;

let tenv_ok_empty = prove
 (`tenv_ok (mk_type_env nsEmpty nsEmpty nsEmpty)`,
  CHEAT_TAC);;
add_simp tenv_ok_empty;;

let type_pes_def = new_definition
  `type_pes tvs tvs' tenv tenvE pes t1 t2 <=>
     (RES_FORALL (set_of_list pes) (\(p,e).
       ?bindings.
         ALL_DISTINCT (ast_pat_bindings p) /\
         type_p tvs tenv p t1 bindings /\
         type_e tenv (bind_var_list tvs' bindings tenvE) e t2))`;;

let type_pes_cons = prove
 (`!tvs tvs' tenv tenvE p e pes t1 t2.
    type_pes tvs tvs' tenv tenvE (CONS (p,e) pes) t1 t2 <=>
    (ALL_DISTINCT (ast_pat_bindings p) /\
     (?bindings.
         type_p tvs tenv p t1 bindings /\
         type_e tenv (bind_var_list tvs' bindings tenvE) e t2) /\
     type_pes tvs tvs' tenv tenvE pes t1 t2)`,
  (REWRITE_TAC[type_pes_def; MEM; PAIR_EQ] THEN MESON_TAC[]));;

(* ---------- check_freevars ---------- *)

let check_freevars_add = prove
 (`(!tvs tvs' t. check_freevars tvs tvs' t ==>
    (!tvs''. tvs'' >= tvs ==> check_freevars tvs'' tvs' t))`,
  CHEAT_TAC);;

(* ---------- type_subst ---------- *)

let check_freevars_subst_single = prove
 (`!dbmax tvs t tvs' ts.
    LENGTH tvs = LENGTH ts /\
    check_freevars dbmax tvs t /\
    ALL (check_freevars dbmax tvs') ts ==>
    check_freevars dbmax tvs' (type_subst (alist_to_fmap (ZIP tvs
      ts)) t)`,
  CHEAT_TAC);;

let check_freevars_subst_list = prove
 (`!dbmax tvs tvs' ts ts'.
    (LENGTH tvs = LENGTH ts) /\
    ALL (check_freevars dbmax tvs) ts' /\
    ALL (check_freevars dbmax tvs') ts ==>
    ALL (check_freevars dbmax tvs') (MAP (type_subst (alist_to_fmap
      (ZIP tvs ts))) ts')`,
  CHEAT_TAC);;

(* ---------- deBruijn_inc ---------- *)

let deBruijn_inc0 = prove
 (`(!t sk. deBruijn_inc sk 0 t = t) /\
   (!ts sk. MAP (deBruijn_inc sk 0) ts = ts)`,
  CHEAT_TAC);;

let deBruijn_inc_deBruijn_inc = prove
 (`!sk i2 t i1.
    deBruijn_inc sk i1 (deBruijn_inc sk i2 t) = deBruijn_inc sk (i1
      + i2) t`,
  CHEAT_TAC);;

(* [local] *)
let deBuijn_inc_lem1 = prove
 (`!sk i2 t i1.
   deBruijn_inc sk i1 (deBruijn_inc 0 (sk + i2) t) = deBruijn_inc 0
     (i1 + (sk + i2)) t`,
  CHEAT_TAC);;

(* [local] *)
let type_subst_deBruijn_inc_single = prove
 (`!s t ts tvs inc sk.
   (LENGTH tvs = LENGTH ts) /\
   (s = alist_to_fmap (ZIP tvs ts)) /\
   check_freevars 0 tvs t ==>
   (deBruijn_inc sk inc (type_subst s t) =
    type_subst (alist_to_fmap (ZIP tvs (MAP (\t. deBruijn_inc sk
      inc t) ts))) t)`,
  CHEAT_TAC);;

let type_subst_deBruijn_inc_list = prove
 (`!ts' ts tvs inc sk.
    (LENGTH tvs = LENGTH ts) /\
    ALL (check_freevars 0 tvs) ts' ==>
    (MAP (deBruijn_inc sk inc) (MAP (type_subst (alist_to_fmap (ZIP
      tvs ts))) ts') =
     MAP (type_subst (alist_to_fmap (ZIP tvs (MAP (\t. deBruijn_inc
       sk inc t) ts)))) ts')`,
  CHEAT_TAC);;

(* [local] *)
let check_freevars_deBruijn_inc = prove
 (`!tvs tvs' t. check_freevars tvs tvs' t ==>
   (!n n'. check_freevars (n + tvs) tvs' (deBruijn_inc n' n t))`,
  CHEAT_TAC);;

let nil_deBruijn_inc = prove
 (`!skip tvs t.
    (check_freevars skip [] t \/ check_freevars skip [] (deBruijn_inc
      skip tvs t)) ==>
    (deBruijn_inc skip tvs t = t)`,
  CHEAT_TAC);;

(* ---------- deBruijn_subst ---------- *)

let deBruijn_subst_check_freevars = prove
 (`!tvs tvs' t ts n.
    check_freevars tvs tvs' t /\
    ALL (check_freevars tvs tvs') ts ==>
    check_freevars tvs tvs' (deBruijn_subst 0 ts t)`,
  CHEAT_TAC);;

let deBruijn_subst_check_freevars2 = prove
 (`!tvs tvs' t ts n tvs''.
    check_freevars (LENGTH ts) tvs' t /\
    ALL (check_freevars tvs tvs') ts ==>
    check_freevars tvs tvs' (deBruijn_subst 0 ts t)`,
  CHEAT_TAC);;

let check_freevars_subst_inc = prove
 (`!tvs tvs2 t.
    check_freevars tvs tvs2 t ==>
    (!tvs' targs tvs1.
    tvs = LENGTH targs + tvs' /\
    ALL (check_freevars (tvs1 + tvs') tvs2) targs ==>
    check_freevars (tvs1 + tvs') tvs2
       (deBruijn_subst 0 targs (deBruijn_inc (LENGTH targs) tvs1
         t)))`,
  CHEAT_TAC);;

let check_freevars_subst = prove
 (`!tvs tvs2 t.
    check_freevars tvs tvs2 t ==>
    (!tvs' targs tvs1.
    tvs = LENGTH targs + tvs' /\
    ALL (check_freevars (tvs1 + tvs') tvs2) targs ==>
    check_freevars (tvs1 + tvs') tvs2 (deBruijn_subst 0 targs t))`,
  CHEAT_TAC);;

(* [local] *)
let type_subst_deBruijn_subst_single = prove
 (`!s t tvs tvs' ts ts' inc.
   (LENGTH tvs = LENGTH ts) /\
   check_freevars 0 tvs t /\
   (s = alist_to_fmap (ZIP tvs ts)) ==>
   (deBruijn_subst inc ts' (type_subst (alist_to_fmap (ZIP tvs ts))
     t) =
    type_subst (alist_to_fmap (ZIP tvs (MAP (\t. deBruijn_subst inc
      ts' t) ts))) t)`,
  CHEAT_TAC);;

let type_subst_deBruijn_subst_list = prove
 (`!t tvs tvs' ts ts' ts'' inc.
    (LENGTH tvs = LENGTH ts) /\
    ALL (check_freevars 0 tvs) ts'' ==>
    (MAP (deBruijn_subst inc ts') (MAP (type_subst (alist_to_fmap
      (ZIP tvs ts))) ts'') =
     MAP (type_subst (alist_to_fmap (ZIP tvs (MAP (\t.
       deBruijn_subst inc ts' t) ts)))) ts'')`,
  CHEAT_TAC);;

(* [local] *)
let check_freevars_lem = prove
 (`!l tvs' t.
   check_freevars l tvs' t ==>
   (!targs n1 tvs.
     (l = n1 + (LENGTH targs)) /\
     ALL (check_freevars tvs tvs') targs ==>
      check_freevars (n1 + tvs) tvs'
        (deBruijn_subst n1 (MAP (deBruijn_inc 0 n1) targs) t))`,
  CHEAT_TAC);;

let nil_deBruijn_subst = prove
 (`!skip tvs t. check_freevars skip [] t ==> (deBruijn_subst skip tvs
  t = t)`,
  CHEAT_TAC);;

let deBruijn_subst2 = prove
 (`(!t sk targs targs' tvs'.
    check_freevars (LENGTH targs) [] t ==>
    (deBruijn_subst sk (MAP (deBruijn_inc 0 sk) targs')
      (deBruijn_subst 0 targs t) =
     deBruijn_subst 0 (MAP (deBruijn_subst sk (MAP (deBruijn_inc 0
       sk) targs')) targs) t)) /\
   (!ts sk targs targs' tvs'.
    ALL (check_freevars (LENGTH targs) []) ts ==>
    (MAP (deBruijn_subst sk (MAP (deBruijn_inc 0 sk) targs')) (MAP
      (deBruijn_subst 0 targs) ts) =
    (MAP (deBruijn_subst 0 (MAP (deBruijn_subst sk (MAP
      (deBruijn_inc 0 sk) targs')) targs)) ts)))`,
  CHEAT_TAC);;

let type_e_subst_lem3 = prove
 (`!tvs tvs2 t.
    check_freevars tvs tvs2 t ==>
    (!tvs' targs n.
    (tvs = n + LENGTH targs) /\
    ALL (check_freevars tvs' tvs2) targs ==>
    check_freevars (n + tvs') tvs2
       (deBruijn_subst n (MAP (deBruijn_inc 0 n) targs) t))`,
  CHEAT_TAC);;

(* [local] *)
let type_e_subst_lem5 = prove
 (`(!t n inc n' targs.
    deBruijn_inc n inc (deBruijn_subst (n + n') (MAP (deBruijn_inc 0
      (n + n')) targs) t) =
    deBruijn_subst (n + inc + n') (MAP (deBruijn_inc 0 (n + inc +
      n')) targs)
          (deBruijn_inc n inc t)) /\
   (!ts n inc n' targs.
    MAP (deBruijn_inc n inc) (MAP (deBruijn_subst (n + n') (MAP
      (deBruijn_inc 0 (n + n')) targs)) ts) =
    MAP (deBruijn_subst (n + inc + n') (MAP (deBruijn_inc 0 (n + inc
      + n')) targs))
          (MAP (deBruijn_inc n inc) ts))`,
  CHEAT_TAC);;

let subst_inc_cancel = prove
 (`(!t ts inc.
    deBruijn_subst 0 ts (deBruijn_inc 0 (inc + LENGTH ts) t) =
    deBruijn_inc 0 inc t) /\
   (!ts' ts inc.
    MAP (deBruijn_subst 0 ts) (MAP (deBruijn_inc 0 (inc + LENGTH ts))
      ts') =
    MAP (deBruijn_inc 0 inc) ts')`,
  CHEAT_TAC);;

(* [local] *)
let type_e_subst_lem7 = prove
 (`(!t sk targs targs' tvs' tvs''.
   (deBruijn_subst sk (MAP (deBruijn_inc 0 sk) targs')
     (deBruijn_subst 0 targs t) =
    deBruijn_subst 0 (MAP (deBruijn_subst sk (MAP (deBruijn_inc 0 sk)
      targs')) targs)
      (deBruijn_subst (LENGTH targs + sk) (MAP (deBruijn_inc 0
        (LENGTH targs + sk)) targs') t))) /\
   (!ts sk targs targs' tvs' tvs''.
   (MAP (deBruijn_subst sk (MAP (deBruijn_inc 0 sk) targs')) (MAP
     (deBruijn_subst 0 targs) ts) =
   (MAP (deBruijn_subst 0 (MAP (deBruijn_subst sk (MAP (deBruijn_inc
     0 sk) targs')) targs))
        (MAP (deBruijn_subst (LENGTH targs + sk) (MAP (deBruijn_inc
          0 (LENGTH targs + sk)) targs')) ts))))`,
  CHEAT_TAC);;

let deBruijn_subst_id = prove
 (`(!t n. check_freevars n [] t ==> (deBruijn_subst 0 (MAP Tvar_db
  (COUNT_LIST n)) t = t)) /\
   (!ts n. ALL (check_freevars n []) ts ==> (MAP (deBruijn_subst 0
     (MAP Tvar_db (COUNT_LIST n))) ts = ts))`,
  CHEAT_TAC);;

let deBruijn_subst_freevars = prove
 (`!skip targs t tvs.
    skip = 0 /\
    ALL (check_freevars tvs []) targs /\
    check_freevars (LENGTH targs) [] t ==>
    check_freevars tvs [] (deBruijn_subst skip targs t)`,
  CHEAT_TAC);;

(* ---------- tenv_abbrev stuff ---------- *)

let tenv_abbrev_ok_lookup = prove
 (`!tenvT tn tvs t.
    tenv_abbrev_ok tenvT /\
    nsLookup tenvT tn = SOME (tvs,t) ==>
    check_freevars 0 tvs t`,
  CHEAT_TAC);;

let check_freevars_type_name_subst = prove
 (`!tvs t dbmax tenvT.
    tenv_abbrev_ok tenvT /\
    check_type_names tenvT t /\
    check_freevars_ast tvs t ==>
    check_freevars dbmax tvs (type_name_subst tenvT t)`,
  CHEAT_TAC);;

let tenv_abbrev_ok_merge = prove
 (`!tenvT1 tenvT2.
    tenv_abbrev_ok tenvT1 /\ tenv_abbrev_ok tenvT2 ==>
    tenv_abbrev_ok (nsAppend tenvT1 tenvT2)`,
  CHEAT_TAC);;

(* ---------- tenv_ctor stuff ----------*)

let type_ctor_long = prove
 (`!ctMap mn id'. type_ctor ctMap (Long mn id') = type_ctor ctMap id'`,
  CHEAT_TAC);;

let tenv_ctor_ok_merge = prove
 (`!tenvC1 tenvC2.
    tenv_ctor_ok tenvC1 /\ tenv_ctor_ok tenvC2 ==>
    tenv_ctor_ok (nsAppend tenvC1 tenvC2)`,
  CHEAT_TAC);;
add_simp tenv_ctor_ok_merge;;

let tenv_ctor_ok_lookup = prove
 (`!tenvC cn tvs ts tn.
    tenv_ctor_ok tenvC /\ nsLookup tenvC cn = SOME (tvs,ts,tn) ==>
    ALL (check_freevars 0 tvs) ts`,
  CHEAT_TAC);;

(* ---------- tenv_val_exp stuff ---------- *)

let deBruijn_subst_tenvE_def,deBruijn_subst_tenvE_ind = define_rec
  [`deBruijn_subst_tenvE targs (typeSystem_Empty:tenv_val_exp) =
    (typeSystem_Empty:tenv_val_exp)`;
   `deBruijn_subst_tenvE targs (typeSystem_Bind_tvar tvs env) =
      typeSystem_Bind_tvar tvs (deBruijn_subst_tenvE targs env)`;
   `deBruijn_subst_tenvE targs (typeSystem_Bind_name x tvs t env) =
      typeSystem_Bind_name x tvs (deBruijn_subst (tvs + num_tvs env)
                              (MAP (deBruijn_inc 0 (tvs + num_tvs
                                  env)) targs)
                              t)
           (deBruijn_subst_tenvE targs env)`];;

let db_merge_def,db_merge_ind = define_rec
  [`db_merge (typeSystem_Empty:tenv_val_exp) e = e`;
   `db_merge (typeSystem_Bind_tvar tvs e1) e2 = typeSystem_Bind_tvar
    tvs (db_merge e1 e2)`;
   `db_merge (typeSystem_Bind_name x tvs t e1) e2 =
    typeSystem_Bind_name x tvs t (db_merge e1 e2)`];;

let bind_tvar_rewrites = prove
 (`(!tvs e1 e2. db_merge (bind_tvar tvs e1) e2 = bind_tvar tvs (db_merge
  e1 e2)) /\
   (!tvs e. num_tvs (bind_tvar tvs e) = tvs + num_tvs e) /\
   (!tvs e. num_tvs (typeSystem_Bind_tvar tvs e) = tvs + num_tvs e)
     /\
   (!tvs n t e. num_tvs (typeSystem_Bind_name n tvs t e) = num_tvs e)
     /\
   (!tvs e. num_tvs typeSystem_Empty = 0) /\
   (!n inc tvs e. tveLookup n inc (bind_tvar tvs e) = tveLookup n
     (inc + tvs) e) /\
   (!tvs e. tenv_val_exp_ok (bind_tvar tvs e) <=> tenv_val_exp_ok e)
     /\
   (!targs tvs e.
     deBruijn_subst_tenvE targs (bind_tvar tvs e) =
     bind_tvar tvs (deBruijn_subst_tenvE targs e))`,
  CHEAT_TAC);;
add_simp bind_tvar_rewrites;;

let bind_tvar0 = prove
 (`!x. bind_tvar 0 x = x`,
  CHEAT_TAC);;
add_simp bind_tvar0;;

let tveLookup_subst_none = prove
 (`!n inc e.
   tveLookup n inc (deBruijn_subst_tenvE targs e) = NONE <=>
   tveLookup n inc e = NONE`,
  CHEAT_TAC);;

let tveLookup_db_merge_none = prove
 (`!n inc e1 e2.
    tveLookup n inc (db_merge e1 e2) = NONE <=>
    tveLookup n inc e1 = NONE /\ tveLookup n (num_tvs e1 + inc) e2
      = NONE`,
  CHEAT_TAC);;

let tveLookup_inc_none = prove
 (`!n inc e.
    tveLookup n inc e = NONE <=>
    tveLookup n 0 e = NONE`,
  CHEAT_TAC);;

let tveLookup_freevars = prove
 (`!n tvs tenvE tvs' t.
    tenv_val_exp_ok tenvE /\
    num_tvs tenvE = 0 /\
    tveLookup n tvs tenvE = SOME (tvs',t) ==>
    check_freevars tvs' [] t`,
  CHEAT_TAC);;

let tveLookup_bvl = prove
 (`!x tvs tvs' bindings tenvE.
    tveLookup x tvs (bind_var_list tvs' bindings tenvE) =
    (match ALOOKUP bindings x with SOME t -> SOME
      (tvs',deBruijn_inc tvs' tvs t) | NONE -> tveLookup x tvs tenvE)`,
  CHEAT_TAC);;

let bind_var_list_append = prove
 (`!n te1 te2 te3.
    bind_var_list n (APPEND te1 te2) te3 = bind_var_list n te1
      (bind_var_list n te2 te3)`,
  CHEAT_TAC);;

let num_tvs_bind_var_list = prove
 (`!tvs env tenvE. num_tvs (bind_var_list tvs env tenvE) = num_tvs
  tenvE`,
  CHEAT_TAC);;
add_simp num_tvs_bind_var_list;;

let tenv_val_exp_ok_bvl = prove
 (`!tenvE env.
    tenv_val_exp_ok tenvE /\ ALL (check_freevars (num_tvs tenvE) [])
      (MAP SND env) ==>
    tenv_val_exp_ok (bind_var_list 0 env tenvE)`,
  CHEAT_TAC);;

let tveLookup_subst_some = prove
 (`!n e targs tvs t inc.
    tveLookup n inc e = SOME (tvs,t) ==>
    tveLookup n inc (deBruijn_subst_tenvE targs e) =
      SOME (tvs,deBruijn_subst (tvs + inc + num_tvs e) (MAP
        (deBruijn_inc 0 (tvs + inc + num_tvs e)) targs) t)`,
  CHEAT_TAC);;

let num_tvs_db_merge = prove
 (`!e1 e2. num_tvs (db_merge e1 e2) = num_tvs e1 + num_tvs e2`,
  CHEAT_TAC);;
add_simp num_tvs_db_merge;;

let num_tvs_deBruijn_subst_tenvE = prove
 (`!targs tenvE. num_tvs (deBruijn_subst_tenvE targs tenvE) = num_tvs
  tenvE`,
  CHEAT_TAC);;
add_simp num_tvs_deBruijn_subst_tenvE;;

let tveLookup_inc_some = prove
 (`!n inc e tvs t inc2.
     tveLookup n inc e = SOME (tvs,t) ==>
     (?t'. (t = deBruijn_inc tvs inc t') /\
          (tveLookup n inc2 e = SOME (tvs,deBruijn_inc tvs inc2
            t')))`,
  CHEAT_TAC);;

let tveLookup_add_inc = prove
 (`!x inc tenv tvs t inc2.
    (tveLookup x inc tenv = SOME (tvs,t)) ==>
    (tveLookup x (inc2 + inc) tenv = SOME (tvs,deBruijn_inc tvs
      inc2 t))`,
  CHEAT_TAC);;

let tveLookup_freevars_subst = prove
 (`!tenvE targs n t inc.
    ALL (check_freevars (inc + num_tvs tenvE) []) targs /\
    tveLookup n inc tenvE = SOME (LENGTH targs,t) /\
    tenv_val_exp_ok tenvE ==>
    check_freevars (inc + num_tvs tenvE) [] (deBruijn_subst 0 targs
      t)`,
  CHEAT_TAC);;

let tenv_val_exp_ok_db_merge = prove
 (`!e1 e2. tenv_val_exp_ok (db_merge e1 e2) ==> tenv_val_exp_ok e2`,
  CHEAT_TAC);;

(* tveLookup_freevars[local] *)
let typeSysProps_tveLookup_freevars = prove
 (`!e n inc t tvs.
   tenv_val_exp_ok e /\
   tveLookup n inc e = SOME (tvs,t) ==>
   check_freevars (tvs + inc + num_tvs e) [] t`,
  CHEAT_TAC);;

let tveLookup_no_tvs = prove
 (`!tvs l tenv n t.
    tenv_val_exp_ok tenv /\
    num_tvs tenv = 0 ==>
    (
     tveLookup n tvs tenv = SOME (l,t) <=>
     tveLookup n 0 tenv = SOME (l,t))`,
  CHEAT_TAC);;

let deBruijn_subst_E_bvl = prove
 (`!tenv1 tenv2 tvs.
    deBruijn_subst_tenvE targs (bind_var_list tvs tenv1 tenv2) =
    bind_var_list tvs
            (MAP (\(x,t). (x,deBruijn_subst (tvs + num_tvs tenv2)
              (MAP (deBruijn_inc 0 (tvs + num_tvs tenv2)) targs) t))
              tenv1)
            (deBruijn_subst_tenvE targs tenv2)`,
  CHEAT_TAC);;

let db_merge_bvl = prove
 (`!tenv1 tenv2 tenv3 tvs.
    db_merge (bind_var_list tvs tenv1 tenv2) tenv3 =
    bind_var_list tvs tenv1 (db_merge tenv2 tenv3)`,
  CHEAT_TAC);;

let tveLookup_db_merge_some = prove
 (`!n inc tenvE1 tenvE2 tvs t.
    tveLookup n inc (db_merge tenvE1 tenvE2) = SOME (tvs,t) <=>
    tveLookup n inc tenvE1 = SOME (tvs,t) \/
    (tveLookup n inc tenvE1 = NONE /\
     tveLookup n (num_tvs tenvE1 + inc) tenvE2 = SOME (tvs,t))`,
  CHEAT_TAC);;

(* ---------- type_op ---------- *)

(* HOL4 typeSysPropsScript.sml:909-917: ML code, not ported *)

(* HOL4 typeSysPropsScript.sml:919-923: a theorem that HOL4 states as
   the value of an ML expression: type_op_cases *)

(* ---------- type_p ---------- *)

let type_ps_length = prove
 (`!tvs tenvC ps ts tenv.
    type_ps tvs tenvC ps ts tenv ==> (LENGTH ps = LENGTH ts)`,
  CHEAT_TAC);;

let type_p_freevars = prove
 (`(!tvs tenvC p t env'.
     type_p tvs tenvC p t env' ==>
     check_freevars tvs [] t /\
     ALL (check_freevars tvs []) (MAP SND env')) /\
   (!tvs tenvC ps ts env'.
     type_ps tvs tenvC ps ts env' ==>
     ALL (check_freevars tvs []) ts /\
     ALL (check_freevars tvs []) (MAP SND env'))`,
  CHEAT_TAC);;

let type_p_subst = prove
 (`(!n tenv p t new_bindings. type_p n tenv p t new_bindings ==>
      (!targs' inc tvs targs.
      tenv_abbrev_ok (type_env_t tenv) /\
      tenv_ctor_ok (type_env_c tenv) /\
      (n = inc + LENGTH targs) /\
      ALL (check_freevars tvs []) targs /\
      (targs' = MAP (deBruijn_inc 0 inc) targs) ==>
      type_p (inc + tvs) tenv
             p
             (deBruijn_subst inc targs' t)
             (MAP (\(x,t). (x,deBruijn_subst inc targs' t))
               new_bindings))) /\
   (!n tenv ps ts new_bindings. type_ps n tenv ps ts new_bindings ==>
      (!targs' inc targs tvs.
      tenv_abbrev_ok (type_env_t tenv) /\
      tenv_ctor_ok (type_env_c tenv) /\
      (n = inc + LENGTH targs) /\
      ALL (check_freevars tvs []) targs /\
      (targs' = MAP (deBruijn_inc 0 inc) targs) ==>
      type_ps (inc + tvs) tenv
             ps
             (MAP (deBruijn_subst inc targs') ts)
             (MAP (\(x,t). (x,deBruijn_subst inc targs' t))
               new_bindings)))`,
  CHEAT_TAC);;

let type_p_bvl = prove
 (`(!tvs tenvC p t bindings. type_p tvs tenvC p t bindings ==>
    (!tenv'. tenv_val_exp_ok tenv' ==> tenv_val_exp_ok (bind_var_list
      tvs bindings tenv'))) /\
   (!tvs tenvC ps ts bindings. type_ps tvs tenvC ps ts bindings ==>
    (!tenv'. tenv_val_exp_ok tenv' ==> tenv_val_exp_ok
      (bind_var_list tvs bindings tenv')))`,
  CHEAT_TAC);;

let type_p_tenvV_indep = prove
 (`(!p tvs tenv t bindings tenvV.
    type_p tvs tenv p t bindings = type_p tvs (type_env_v_fupd (K
      tenvV) tenv) p t bindings) /\
   (!ps tvs tenv t bindings tenvV.
    type_ps tvs tenv ps t bindings = type_ps tvs (type_env_v_fupd
      (K tenvV) tenv) ps t bindings)`,
  CHEAT_TAC);;

(* ---------- type_e, type_es, type_funs ---------- *)

let type_es_list_rel = prove
 (`!es ts tenv tenvE. type_es tenv tenvE es ts = ALL2 (type_e tenv
  tenvE) es ts`,
  CHEAT_TAC);;

let type_es_length = prove
 (`!tenv tenvE es ts.
    type_es tenv tenvE es ts ==> (LENGTH es = LENGTH ts)`,
  (REWRITE_TAC[type_es_list_rel] THEN MESON_TAC[LIST_REL_LENGTH]));;

let type_funs_MAP_FST = prove
 (`!funs tenv tenvE env.
    type_funs tenv tenvE funs env ==>
    MAP FST funs = MAP FST env`,
  CHEAT_TAC);;

let tenv_val_exp_ok_bvl_tvs = prove
 (`!funs tenv env tvs bindings tenvE.
    type_funs tenv (bind_var_list 0 bindings (bind_tvar tvs tenvE))
      funs env /\
    tenv_val_exp_ok tenvE ==>
    tenv_val_exp_ok (bind_var_list tvs env tenvE)`,
  CHEAT_TAC);;

let tenv_val_exp_ok_bvl_funs = prove
 (`!funs env tenv bindings tenv_val tenvE.
    type_funs tenv (bind_var_list 0 bindings tenvE) funs env /\
    tenv_val_exp_ok tenvE ==>
    tenv_val_exp_ok (bind_var_list 0 env tenvE)`,
  CHEAT_TAC);;

let type_e_freevars = prove
 (`(!tenv tenvE e t.
     type_e tenv tenvE e t ==>
     tenv_val_exp_ok tenvE /\ tenv_val_ok (type_env_v tenv) ==>
     check_freevars (num_tvs tenvE) [] t) /\
   (!tenv tenvE es ts.
     type_es tenv tenvE es ts ==>
     tenv_val_exp_ok tenvE /\ tenv_val_ok (type_env_v tenv) ==>
     ALL (check_freevars (num_tvs tenvE) []) ts) /\
   (!tenv tenvE funs env.
     type_funs tenv tenvE funs env ==>
     tenv_val_exp_ok tenvE /\ tenv_val_ok (type_env_v tenv) ==>
     ALL (check_freevars (num_tvs tenvE) []) (MAP SND env))`,
  CHEAT_TAC);;

let type_e_subst = prove
 (`(!tenv tenvE e t. type_e tenv tenvE e t ==>
      (!tenvE1 targs tvs targs'.
        num_tvs tenvE2 = 0 /\
        tenv_abbrev_ok (type_env_t tenv) /\
        tenv_ctor_ok (type_env_c tenv) /\
        tenv_val_ok (type_env_v tenv) /\
        tenv_val_exp_ok tenvE /\
        ALL (check_freevars tvs []) targs /\
        tenvE = db_merge tenvE1 (bind_tvar (LENGTH targs) tenvE2) /\
        targs' = MAP (deBruijn_inc 0 (num_tvs tenvE1)) targs ==>
        type_e tenv (db_merge (deBruijn_subst_tenvE targs tenvE1)
          (bind_tvar tvs tenvE2))
                     e
                     (deBruijn_subst (num_tvs tenvE1) targs' t))) /\
   (!tenv tenvE es ts. type_es tenv tenvE es ts ==>
      (!tenvE1 targs tvs targs'.
        num_tvs tenvE2 = 0 /\
        tenv_abbrev_ok (type_env_t tenv) /\
        tenv_ctor_ok (type_env_c tenv) /\
        tenv_val_ok (type_env_v tenv) /\
        tenv_val_exp_ok tenvE /\
        ALL (check_freevars tvs []) targs /\
        tenvE = db_merge tenvE1 (bind_tvar (LENGTH targs) tenvE2) /\
        targs' = MAP (deBruijn_inc 0 (num_tvs tenvE1)) targs ==>
        type_es tenv (db_merge (deBruijn_subst_tenvE targs tenvE1)
          (bind_tvar tvs tenvE2))
                    es
                    (MAP (deBruijn_subst (num_tvs tenvE1) targs')
                      ts))) /\
   (!tenv tenvE funs env. type_funs tenv tenvE funs env ==>
      (!tenvE1 targs tvs targs'.
        num_tvs tenvE2 = 0 /\
        tenv_abbrev_ok (type_env_t tenv) /\
        tenv_ctor_ok (type_env_c tenv) /\
        tenv_val_ok (type_env_v tenv) /\
        tenv_val_exp_ok tenvE /\
        ALL (check_freevars tvs []) targs /\
        tenvE = db_merge tenvE1 (bind_tvar (LENGTH targs) tenvE2) /\
        targs' = MAP (deBruijn_inc 0 (num_tvs tenvE1)) targs ==>
        type_funs tenv (db_merge (deBruijn_subst_tenvE targs tenvE1)
          (bind_tvar tvs tenvE2))
                        funs
                        (MAP (\(x,t). (x,deBruijn_subst (num_tvs
                          tenvE1) targs' t)) env)))`,
  CHEAT_TAC);;

(* Recursive functions have function type *)
let type_funs_Tfn = prove
 (`!tenv tenvE funs bindings tvs t n.
    type_funs tenv tenvE funs bindings /\
    ALOOKUP bindings n = SOME t ==>
    (?t1 t2. (t = Tfn t1 t2) /\ check_freevars (num_tvs tenvE) []
      (Tfn t1 t2))`,
  CHEAT_TAC);;

(* Recursive functions can be looked up in the execution environment. *)
let type_funs_lookup = prove
 (`!fn tenvE funs bindings n e tenv.
    MEM (fn,n,e) funs /\
    type_funs tenv tenvE funs bindings ==>
    (?t. ALOOKUP bindings fn = SOME t)`,
  CHEAT_TAC);;

(* Functions in the type environment can be found *)
let type_funs_find_recfun = prove
 (`!fn env funs bindings e tenv tenvE t.
    ALOOKUP bindings fn = SOME t /\
    type_funs tenv tenvE funs bindings ==>
    (?n e. find_recfun fn funs = SOME (n,e))`,
  CHEAT_TAC);;

let type_recfun_lookup = prove
 (`!fn funs n e tenv tenvE bindings tvs t1 t2.
    find_recfun fn funs = SOME (n,e) /\
    type_funs tenv tenvE funs bindings /\
    ALOOKUP bindings fn = SOME (Tfn t1 t2) ==>
    type_e tenv (typeSystem_Bind_name n 0 t1 tenvE) e t2 /\
    check_freevars (num_tvs tenvE) [] (Tfn t1 t2)`,
  CHEAT_TAC);;

(* No duplicate function definitions in a single let rec *)
let type_funs_distinct = prove
 (`!tenv tenvE funs bindings.
    type_funs tenv tenvE funs bindings ==>
    ALL_DISTINCT (MAP (\(x,y,z). x) funs)`,
  CHEAT_TAC);;

let type_funs_tenv_exp_ok = prove
 (`!funs env tenv tenvE tvs bindings.
    num_tvs tenvE = 0 /\
    type_funs tenv (bind_var_list 0 bindings (bind_tvar tvs tenvE))
      funs env ==>
    tenv_val_exp_ok (bind_var_list tvs env typeSystem_Empty)`,
  CHEAT_TAC);;

(* [local] *)
let type_e_subst_lem = prove
 (`!tenv tenvE e t targs tvs targs'.
   type_e tenv (typeSystem_Bind_name x 0 t1 (bind_tvar (LENGTH targs)
     tenvE)) e t /\
   num_tvs tenvE = 0 /\
   tenv_abbrev_ok (type_env_t tenv) /\
   tenv_ctor_ok (type_env_c tenv) /\
   tenv_val_ok (type_env_v tenv) /\
   tenv_val_exp_ok (bind_tvar (LENGTH targs) tenvE) /\
   ALL (check_freevars tvs []) targs /\
   check_freevars (LENGTH targs) [] t1 ==>
   type_e tenv (typeSystem_Bind_name x 0 (deBruijn_subst 0 targs
     t1) (bind_tvar tvs tenvE)) e (deBruijn_subst 0 targs t)`,
  (REPEAT STRIP_TAC THEN
   MP_TAC(SPECL [`tenv:type_env`;
                 `typeSystem_Bind_name x 0 t1 (bind_tvar (LENGTH
                   (targs:t list)) tenvE)`;
                 `e:ast_exp`; `t:t`] (CONJUNCT1 (INST
                   [`tenvE:tenv_val_exp`,`tenvE2:tenv_val_exp`]
                                             type_e_subst))) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(MP_TAC o SPECL [`typeSystem_Bind_name x 0 t1
     typeSystem_Empty`; `targs:t list`; `tvs:num`;
                              `MAP (deBruijn_inc 0 0) (targs:t
                                list)`]) THEN
   ASM_REWRITE_TAC[db_merge_def; deBruijn_subst_tenvE_def;
     num_tvs_def; ADD_CLAUSES;
                   deBruijn_inc0; tenv_val_exp_ok_def] THEN
   ASM_SIMP_TAC[bind_tvar_rewrites; ADD_CLAUSES]));;


(* HOL4 typeSysPropsScript.sml:1654-1685: code that the source has in
   a comment *)

(* ---------- ctMap stuff ---------- *)


let _ = size_thms "ast_t";;
let _ = size_thms "mlstring";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let type_def_to_ctMap_def,type_def_to_ctMap_ind = define_wf
  `MEASURE (\(x0,x1,x2,x3).      list_size      (pair_size (\x. 0)
  (pair_size (\x. 0) (list_size (pair_size mlstring_size
  ast_t_size1))))      x2)`
  [`type_def_to_ctMap tenvT next_stamp [] [] = []`;
   `type_def_to_ctMap tenvT next_stamp (CONS (tvs,tn,ctors) tds) (CONS
    id' ids) = APPEND (type_def_to_ctMap tenvT (next_stamp + 1) tds ids)
        (REVERSE
          (MAP (\(cn,ts).
            (TypeStamp cn next_stamp,(tvs,MAP (type_name_subst
                tenvT) ts,id')))
            ctors))`];;

let mem_type_def_to_ctMap = prove
 (`!tenvT next' tds ids stamp x.
    MEM (stamp,x) (type_def_to_ctMap tenvT next' tds ids) /\
    LENGTH tds = LENGTH ids ==>
    (?cn i. stamp = TypeStamp cn i /\ next' <= i /\ i < next' +
      LENGTH tds)`,
  CHEAT_TAC);;

(* [local] *)
let o_f_FRANGE2 = prove
 (`(?x. y = f x /\ x IN FRANGE g) ==> y IN FRANGE (f o_f g)`,
  CHEAT_TAC);;

let ctMap_ok_merge_imp = prove
 (`!ctMap1 ctMap2.
    DISJOINT (FRANGE ((SND o SND) o_f ctMap1)) (FRANGE ((SND o SND)
      o_f ctMap2)) /\
    ctMap_ok ctMap1 /\ ctMap_ok ctMap2 ==>
    ctMap_ok (FUNION ctMap1 ctMap2)`,
  CHEAT_TAC);;

let ctMap_ok_lookup = prove
 (`!ctMap cn tvs ts ti tn.
    ctMap_ok ctMap /\ (FLOOKUP ctMap tn = SOME (tvs,ts,ti)) ==>
    ALL (check_freevars 0 tvs) ts`,
  CHEAT_TAC);;

let type_def_to_ctMap_mem = prove
 (`!tenvT next' tds tids.
    ALOOKUP (type_def_to_ctMap tenvT next' tds tids) k = SOME x /\
    LENGTH tds = LENGTH tids ==>
    MEM (SND (SND x)) tids`,
  CHEAT_TAC);;

(* [local] *)
let fupdate2_union = prove
 (`!m a1 a2. m |++ a1 |++ a2 = FUNION (FEMPTY |++ a2) (m |++ a1)`,
  CHEAT_TAC);;

let ctMap_ok_type_defs = prove
 (`!tenvT next' tds tids.
    ALL_DISTINCT tids /\
    DISJOINT (set_of_list tids) (set_of_list prim_type_nums) /\
    LENGTH tds = LENGTH tids /\
    check_ctor_tenv tenvT tds /\
    tenv_abbrev_ok tenvT ==>
    ctMap_ok
      (FEMPTY |++
        REVERSE (type_def_to_ctMap tenvT next' tds tids))`,
  CHEAT_TAC);;


(* HOL4 typeSysPropsScript.sml:1893-1982: code that the source has in
   a comment *)

(* [local] *)
let all_distinct_map_fst_lemma = prove
 (`!l v. ALL_DISTINCT (MAP (\(x,y). x) l) ==> ALL_DISTINCT (MAP
  (\(x,y). (x,v)) l)`,
  CHEAT_TAC);;

(* HOL4 typeSysPropsScript.sml:1997-2054: code that the source has in
   a comment *)

let check_ctor_tenv_change_tenvT = prove
 (`!tenvT1 env tenvT2.
   ALL (\(cn,ts). ALL (check_type_names tenvT1) ts ==>
                    ALL (check_type_names tenvT2) ts)
         (FLAT (MAP (SND o SND) env)) /\
   check_ctor_tenv tenvT1 env ==>
   check_ctor_tenv tenvT2 env`,
  CHEAT_TAC);;

let check_ctor_tenv_EVERY = prove
 (`!tenvT tds.
     check_ctor_tenv tenvT tds <=>
     ALL check_dup_ctors tds /\
     ALL (ALL_DISTINCT o FST) tds /\
     ALL (\(tvs,tn,ctors).
       ALL (\(cn,ts). ALL (check_freevars_ast tvs) ts /\
                        ALL (check_type_names tenvT) ts) ctors) tds
                          /\
    ALL_DISTINCT (MAP (FST o SND) tds)`,
  CHEAT_TAC);;

(* ---------- consistent_decls ---------- *)

(* HOL4 typeSysPropsScript.sml:2088-2130: code that the source has in
   a comment *)

(* ---------- type_v  ---------- *)

let nsLookup_add_tenvE1 = prove
 (`!tenvE tenvV n tvs t tvs2.
    check_freevars tvs2 [] t /\
    tveLookup n tvs tenvE = SOME (tvs2,t) ==>
    nsLookup (add_tenvE tenvE tenvV) (Short n) = SOME (tvs2,t)`,
  CHEAT_TAC);;

let nsLookup_add_tenvE2 = prove
 (`!tenvE tenvV n tvs t tvs2.
    tveLookup n tvs tenvE = NONE /\
    nsLookup tenvV (Short n) = SOME (tvs2,t) ==>
    nsLookup (add_tenvE tenvE tenvV) (Short n) = SOME (tvs2,t)`,
  CHEAT_TAC);;

let nsLookup_add_tenvE3 = prove
 (`!tenvE tenvV n t tvs2 mn.
    nsLookup tenvV (Long mn n) = SOME (tvs2,t) ==>
    nsLookup (add_tenvE tenvE tenvV) (Long mn n) = SOME (tvs2,t)`,
  CHEAT_TAC);;

let tenv_val_ok_add_tenvE = prove
 (`!tenvE tenvV.
    num_tvs tenvE = 0 /\
    tenv_val_exp_ok tenvE /\
    tenv_val_ok tenvV ==>
    tenv_val_ok (add_tenvE tenvE tenvV)`,
  CHEAT_TAC);;

let add_tenvE_nsAppend = prove
 (`!tenvE tenvV. nsAppend (add_tenvE tenvE nsEmpty) tenvV = add_tenvE
  tenvE tenvV`,
  CHEAT_TAC);;

let add_tenvE_bvl = prove
 (`!n bindings tenvE tenvV.
    add_tenvE (bind_var_list n bindings tenvE) tenvV =
    nsBindList (MAP (\(x,t). (x,(n,t))) bindings) (add_tenvE tenvE
      tenvV)`,
  CHEAT_TAC);;

let type_v_freevars = prove
 (`!tvs tenvC tenvS v t. type_v tvs tenvC tenvS v t ==> check_freevars
  tvs [] t`,
  CHEAT_TAC);;

(* [local] *)
let remove_lambda_prod = prove
 (`(\(x,y). P x y) = (\xy. P (FST xy) (SND xy))`,
  CHEAT_TAC);;

(* HOL4 typeSysPropsScript.sml:2254-2259: ML code, not ported *)

(* type_subst *)
let typeSysProps_type_subst = prove
 (`!tvs ctMap tenvS v t.
     type_v tvs ctMap tenvS v t ==>
     tvs = LENGTH targs /\
     ctMap_ok ctMap /\
     ALL (check_freevars tvs' []) targs /\
     check_freevars (LENGTH targs) [] t ==>
     type_v tvs' ctMap tenvS v (deBruijn_subst 0 targs t)`,
  CHEAT_TAC);;

let check_ctor_tenv_ok = prove
 (`!tenvT tds tis.
   LENGTH tds = LENGTH tis /\
   check_ctor_tenv tenvT tds /\
   tenv_abbrev_ok tenvT ==>
   tenv_ctor_ok (build_ctor_tenv tenvT tds tis)`,
  CHEAT_TAC);;

let nsMap_build_ctor_tenv = prove
 (`!ga g h tenvT tds ids.
   LENGTH tds = LENGTH ids /\ (!x. MEM x (MAP SND (FLAT (MAP (SND o
     SND) tds))) ==>
         MAP (type_name_subst tenvT) (ga x) = (g (MAP
           (type_name_subst tenvT) x))) ==>
   nsMap (\(tvs,ts,tid). (tvs,g ts,h tid)) (build_ctor_tenv tenvT tds
     ids) =
   build_ctor_tenv tenvT (MAP (I ## I ## MAP (I ## ga)) tds) (MAP h
     ids)`,
  CHEAT_TAC);;

(* HOL4 typeSysPropsScript.sml:2407-2421: code that the source has in
   a comment *)

(* ---------- type_d ---------- *)

let type_d_check_uniq = prove
 (`(!check tenv d tdecs new_tenv.
    type_d check tenv d tdecs new_tenv ==>
    type_d F tenv d tdecs new_tenv) /\
   (!check tenv d tdecs new_tenv.
    type_ds check tenv d tdecs new_tenv ==>
    type_ds F tenv d tdecs new_tenv)`,
  CHEAT_TAC);;

let extend_dec_tenv_ok = prove
 (`!tenv tenv'. tenv_ok tenv /\ tenv_ok tenv' ==> tenv_ok
  (extend_dec_tenv tenv tenv')`,
  CHEAT_TAC);;

let type_d_tenv_ok_helper = prove
 (`(!check tenv d tdecs tenv'.
    type_d check tenv d tdecs tenv' ==>
    tenv_ok tenv ==>
    tenv_ok tenv') /\
   (!check tenv d tdecs tenv'.
    type_ds check tenv d tdecs tenv' ==>
    tenv_ok tenv ==>
    tenv_ok tenv')`,
  CHEAT_TAC);;

let type_d_tenv_ok = prove
 (`!check tenv d tdecs tenv'.
    type_d check tenv d tdecs tenv' /\
    tenv_ok tenv ==>
    tenv_ok (extend_dec_tenv tenv' tenv)`,
  (MESON_TAC[extend_dec_tenv_ok; type_d_tenv_ok_helper]));;

(* HOL4 typeSysPropsScript.sml:2554-2572: code that the source has in
   a comment *)

(* ---------- type_ds ---------- *)

let type_ds_empty = prove
 (`!check tenv decls r.
   type_ds check tenv [] decls r <=>
   decls = {} /\ r = mk_type_env nsEmpty nsEmpty nsEmpty`,
  CHEAT_TAC);;
add_simp type_ds_empty;;

let type_ds_sing = prove
 (`!check tenv d decls r.
   type_ds check tenv [d] decls r <=> type_d check tenv d decls r`,
  CHEAT_TAC);;
add_simp type_ds_sing;;

(* HOL4 typeSysPropsScript.sml:2595-2617: code that the source has in
   a comment *)

(* HOL4 typeSysPropsScript.sml:2619-2720: code that the source has in
   a comment *)

(* ---------- type_specs ---------- *)

(* HOL4 typeSysPropsScript.sml:2724-2843: code that the source has in
   a comment *)

(* ---------------- type_top, type_prog ---------- *)
(* HOL4 typeSysPropsScript.sml:2846-3039: code that the source has in
   a comment *)
(* HOL4 typeSysPropsScript.sml:3040-3382: code that the source has in
   a comment *)

(* HOL4 typeSysPropsScript.sml:3384-3408: code that the source has in
   a comment *)

(* and the names it reads as variables are constants again *)
let _ = do_list unhide_constant
  ["id"];;
