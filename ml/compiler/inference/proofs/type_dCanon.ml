(* ======================================================== *)
(*  type_dCanon: ported from HOL4's
    compiler/inference/proofs/type_dCanonScript.sml
    A proof theory, with 9 definitions and 61 theorems.  Needed by
    compilerProof.ml and inferComplete.ml.  *)
(* ======================================================== *)

(*
  For any type_d, prove that the canonical type identifier strategy
  succeeds.
*)

needs "compiler/inference/inferProps.ml";;
needs "semantics/ast.ml";;
needs "semantics/namespace.ml";;
needs "semantics/proofs/namespaceProps.ml";;
needs "semantics/proofs/typeSoundInvariants.ml";;
needs "semantics/proofs/typeSysProps.ml";;
needs "semantics/typeSystem.ml";;

(* TODO: move *)

let tenv_equiv_def = cake_define
  `tenv_equiv tenv1 tenv2 <=>
      nsAll2 (\i v1 v2. v1 = v2) (type_env_t tenv1) (type_env_t
        tenv2) /\
      nsAll2 (\i v1 v2. v1 = v2) (type_env_c tenv1) (type_env_c
        tenv2) /\
      nsAll2 (\i v1 v2. v1 = v2) (type_env_v tenv1) (type_env_v
        tenv2)`;;

let tenv_equiv_refl = cake_theorem "tenv_equiv_refl[simp]"
  (fun () ->
    `tenv_equiv tenv tenv`)
  CHEAT_TAC;;

let tenv_equiv_sym = cake_theorem "tenv_equiv_sym"
  (fun () ->
    `tenv_equiv t1 t2 ==> tenv_equiv t2 t1`)
  CHEAT_TAC;;

let tenv_equiv_tenvLift = cake_theorem "tenv_equiv_tenvLift"
  (fun () ->
    `tenv_equiv t1 t2 ==> tenv_equiv (tenvLift m t1) (tenvLift m t2)`)
  CHEAT_TAC;;

let check_type_names_tenv_equiv =
  cake_theorem "check_type_names_tenv_equiv"
  (fun () ->
    `!t1 t t2.
     nsAll2 (\i v1 v2. v1 = v2) t1 t2 /\
     check_type_names t1 t ==>
     check_type_names t2 t`)
  CHEAT_TAC;;

let lookup_var_tenv_equiv = cake_theorem "lookup_var_tenv_equiv"
  (fun () ->
    `tenv_equiv tenv1 tenv2 ==> lookup_var n bvs tenv1 = lookup_var n
  bvs tenv2`)
  CHEAT_TAC;;

let type_name_subst_tenv_equiv =
  cake_theorem "type_name_subst_tenv_equiv"
  (fun () ->
    `!t1 t t2.
      nsAll2 (\i v1 v2. v1 = v2) t1 t2 ==>
      type_name_subst t1 t = type_name_subst t2 t`)
  CHEAT_TAC;;

let type_p_tenv_equiv = cake_theorem "type_p_tenv_equiv"
  (fun () ->
    `(!tvs tenv1 p t bindings.
       type_p tvs tenv1 p t bindings ==>
       (!tenv2. tenv_equiv tenv1 tenv2 ==>
       type_p tvs tenv2 p t bindings)) /\
     (!tvs tenv1 ps ts bindings.
       type_ps tvs tenv1 ps ts bindings ==>
       (!tenv2. tenv_equiv tenv1 tenv2 ==>
       type_ps tvs tenv2 ps ts bindings))`)
  CHEAT_TAC;;

let type_e_tenv_equiv = cake_theorem "type_e_tenv_equiv"
  (fun () ->
    `(!tenv1 bvs e t.
       type_e tenv1 bvs e t ==>
       (!tenv2. tenv_equiv tenv1 tenv2 ==>
       type_e tenv2 bvs e t)) /\
     (!tenv1 bvs es ts.
       type_es tenv1 bvs es ts ==>
       (!tenv2. tenv_equiv tenv1 tenv2 ==>
       type_es tenv2 bvs es ts)) /\
     (!tenv1 bvs funs ts.
       type_funs tenv1 bvs funs ts ==>
       (!tenv2. tenv_equiv tenv1 tenv2 ==>
       type_funs tenv2 bvs funs ts))`)
  CHEAT_TAC;;

let type_pe_determ_tenv_equiv = cake_theorem "type_pe_determ_tenv_equiv"
  (fun () ->
    `type_pe_determ t1 x y z /\
     tenv_equiv t1 t2 ==>
     type_pe_determ t2 x y z`)
  CHEAT_TAC;;

(* -- *)

(* all the tids used in a tenv *)
let set_tids_tenv_def = cake_define
  `set_tids_tenv tids tenv <=>
   nsAll (\i (ls,t). set_tids_subset tids t) (type_env_t tenv) /\
   nsAll (\i (ls,ts,tid). EVERY (\t. set_tids_subset tids t) ts /\
     tid IN tids) (type_env_c tenv) /\
   nsAll (\i (n,t). set_tids_subset tids t) (type_env_v tenv)`;;

let type_pe_determ_canon_def = cake_define
  `type_pe_determ_canon n tenv tenvE p e <=>
   (!t1 tenv1 t2 tenv2.
     type_p 0 tenv p t1 tenv1 /\ type_e tenv tenvE e t1 /\
     EVERY (\(k,t). set_tids_subset (count n) t) tenv1 /\
     type_p 0 tenv p t2 tenv2 /\ type_e tenv tenvE e t2 /\
     EVERY (\(k,t). set_tids_subset (count n) t) tenv2 ==> tenv1 =
       tenv2)`;;

let type_pe_determ_canon_tenv_equiv =
  cake_theorem "type_pe_determ_canon_tenv_equiv"
  (fun () ->
    `type_pe_determ_canon n t1 x y z /\
     tenv_equiv t1 t2 ==>
     type_pe_determ_canon n t2 x y z`)
  CHEAT_TAC;;

(* A "canonical" version of type_d that produces the type identifiers
  in ascending order.
  It also drops the extra_checks argument so it corresponds to type_d T,
  but adds a starting index, and an argument for the number of
  type ids that got produced.
*)

let type_d_canon = cake_inductive
  `(!n tvs tenv p e t bindings locs.
     (is_value e /\
     ALL_DISTINCT (ast_pat_bindings p) /\
     type_p tvs tenv p t bindings /\
     type_e tenv (bind_tvar tvs typeSystem_Empty) e t /\
     (!tvs' bindings' t'.
     (type_p tvs' tenv p t' bindings' /\
     type_e tenv (bind_tvar tvs' typeSystem_Empty) e t' /\
     EVERY (\(k,t). set_tids_subset (count n) t) bindings') ==>
           EVERY2 tscheme_inst (MAP SND (tenv_add_tvs tvs'
             bindings')) (MAP SND (tenv_add_tvs tvs bindings)))) ==>
     type_d_canon n tenv (Dlet locs p e)
       0
       (mk_type_env (alist_to_ns (tenv_add_tvs tvs bindings)) nsEmpty
         nsEmpty)) /\
   (!n tenv p e t bindings locs.
     ((~(is_value e) /\ type_pe_determ_canon n tenv typeSystem_Empty
       p e) /\
     ALL_DISTINCT (ast_pat_bindings p) /\
     type_p ((0:num)) tenv p t bindings /\
     type_e tenv typeSystem_Empty e t) ==>
     type_d_canon n tenv (Dlet locs p e)
       0 (mk_type_env (alist_to_ns (tenv_add_tvs ((0:num)) bindings))
         nsEmpty nsEmpty)) /\
   (!n tenv funs bindings tvs locs.
     (type_funs tenv (bind_var_list ((0:num)) bindings (bind_tvar tvs
       typeSystem_Empty)) funs bindings /\
     (!tvs' bindings'.
         type_funs tenv (bind_var_list ((0:num)) bindings' (bind_tvar
           tvs' typeSystem_Empty)) funs bindings' /\
         EVERY (\(k,t). set_tids_subset (count n) t) bindings' ==>
           EVERY2 tscheme_inst (MAP SND (tenv_add_tvs tvs'
             bindings')) (MAP SND (tenv_add_tvs tvs bindings)))) ==>
     type_d_canon n tenv (Dletrec locs funs)
     0 (mk_type_env (alist_to_ns (tenv_add_tvs tvs bindings)) nsEmpty
       nsEmpty)) /\
   (!n type_identities tenv tdefs tenvT locs.
     (ITLIST MAX (Tlist_num :: (Tbool_num :: prim_type_nums)) 0 < n
       /\
     type_identities = GENLIST (\i. i + n) (LENGTH tdefs) /\
     check_ctor_tenv (nsAppend tenvT (type_env_t tenv)) tdefs /\
     (tenvT = alist_to_ns (MAP2
                           (\(tvs,tn,ctors) i.
                             (tn,(tvs,Tapp (MAP Tvar tvs) i)))
                           tdefs type_identities))) ==>
     type_d_canon n tenv (Dtype locs tdefs)
       (LENGTH tdefs)
       (mk_type_env nsEmpty (build_ctor_tenv (nsAppend tenvT
         (type_env_t tenv)) tdefs type_identities) tenvT)) /\
   (!n tenv tvs tn t locs.
     (check_freevars_ast tvs t /\
     check_type_names (type_env_t tenv) t /\
     ALL_DISTINCT tvs) ==>
     type_d_canon n tenv (Dtabbrev locs tvs tn t)
       0
       (mk_type_env nsEmpty nsEmpty (nsSing tn (tvs,type_name_subst
         (type_env_t tenv) t)))) /\
   (!n tenv cn ts locs.
     (EVERY (check_freevars_ast []) ts /\
     EVERY (check_type_names (type_env_t tenv)) ts) ==>
     type_d_canon n tenv (Dexn locs cn ts)
       0
       (mk_type_env nsEmpty (nsSing cn ([],MAP (type_name_subst
         (type_env_t tenv)) ts,Texn_num)) nsEmpty)) /\
   (!n tenv mn ds decls tenv'.
     (type_ds_canon n tenv ds decls tenv') ==>
     type_d_canon n tenv (Dmod mn ds) decls (tenvLift mn tenv')) /\
   (!n tenv lds ds decls1 decls2 tenv1 tenv2.
     (type_ds_canon n tenv lds decls1 tenv1) /\
     (type_ds_canon (n + decls1) (extend_dec_tenv tenv1 tenv) ds
       decls2 tenv2) ==>
     type_d_canon n tenv (Dlocal lds ds) (decls1 + decls2) tenv2) /\
   (!n tenv.
     T ==>
     type_ds_canon n tenv []
       0
       (mk_type_env nsEmpty nsEmpty nsEmpty)) /\
   (!n tenv d ds tenv1 tenv2 decls1 decls2.
     (type_d_canon n tenv d decls1 tenv1 /\
     type_ds_canon (n + decls1) (extend_dec_tenv tenv1 tenv) ds
       decls2 tenv2) ==>
     type_ds_canon n tenv (d :: ds)
       (decls1 + decls2) (extend_dec_tenv tenv2 tenv1))`;;

(* The remapping must be identity on these numbers *)
let good_remap_def = cake_define
  `good_remap f <=>
   MAP f (Tlist_num :: (Tbool_num :: prim_type_nums)) =
     Tlist_num :: (Tbool_num :: prim_type_nums)`;;

let ts_tid_rename_type_subst =
  cake_theorem "ts_tid_rename_type_subst[local]"
  (fun () ->
    `!s t f.
     ts_tid_rename f (type_subst s t) =
     type_subst (ts_tid_rename f o_f s) (ts_tid_rename f t)`)
  CHEAT_TAC;;

let ts_tid_rename_type_name_subst =
  cake_theorem "ts_tid_rename_type_name_subst[local]"
  (fun () ->
    `!tenvt t f tenv.
     good_remap f /\
     check_type_names tenvt t ==>
     ts_tid_rename f (type_name_subst tenvt t) =
     type_name_subst (nsMap (\(ls,t). (ls,ts_tid_rename f t))
       tenvt) t`)
  CHEAT_TAC;;

let check_type_names_ts_tid_rename =
  cake_theorem "check_type_names_ts_tid_rename[local]"
  (fun () ->
    `!tenvt t.
     check_type_names tenvt t <=>
     check_type_names (nsMap (\(ls,t). (ls,ts_tid_rename f t))
       tenvt) t`)
  CHEAT_TAC;;

let extend_bij_def = cake_define
  `extend_bij (f:num->num) g ids n v =
   (if v IN ids then
     n + g v else
     f v)`;;

(* HOL4 type_dCanonScript.sml:334-344: code that the source has in a
   comment *)

let extend_bij_id = cake_theorem "extend_bij_id[simp]"
  (fun () ->
    `(extend_bij f f s 0 = f) /\
     (extend_bij f g {} n = f)`)
  CHEAT_TAC;;

let extend_bij_compose = cake_theorem "extend_bij_compose"
  (fun () ->
    `extend_bij (extend_bij f g ids n) h jds (n + m) =
     extend_bij f (extend_bij g h jds m) (ids UNION jds) n`)
  CHEAT_TAC;;

(* needs monotonicity of set_tids_tenv *)
let set_tids_tenv_extend_dec_tenv =
  cake_theorem "set_tids_tenv_extend_dec_tenv[local]"
  (fun () ->
    `!s t s' t'.
     set_tids_tenv (s' UNION s) t' /\
     set_tids_tenv (s' UNION s) t ==>
     set_tids_tenv (s' UNION s) (extend_dec_tenv t' t)`)
  CHEAT_TAC;;

let set_tids_tenv_remap = cake_theorem "set_tids_tenv_remap"
  (fun () ->
    `set_tids_tenv tids tenv ==>
     set_tids_tenv (IMAGE f tids) (remap_tenv f tenv)`)
  CHEAT_TAC;;

let good_remap_extend_bij = cake_theorem "good_remap_extend_bij[local]"
  (fun () ->
    `good_remap f /\ prim_tids F ids ==>
     good_remap (extend_bij f g ids n)`)
  CHEAT_TAC;;

(* HOL4 type_dCanonScript.sml:390-404: code that the source has in a
   comment *)

let remap_tenv_extend_dec_tenv =
  cake_theorem "remap_tenv_extend_dec_tenv[local]"
  (fun () ->
    `remap_tenv f (extend_dec_tenv t t') =
     extend_dec_tenv (remap_tenv f t) (remap_tenv f t')`)
  CHEAT_TAC;;

let BIJ_extend_bij = cake_theorem "BIJ_extend_bij"
  (fun () ->
    `DISJOINT tids ids /\
     BIJ f tids (count n) /\
     BIJ g ids (count (CARD ids)) ==>
     BIJ (extend_bij f g ids n) (tids UNION ids) (count (n + CARD
       ids))`)
  CHEAT_TAC;;

(* HOL4 type_dCanonScript.sml:428-460: code that the source has in a
   comment *)

let set_tids_subset_mono = cake_theorem "set_tids_subset_mono"
  (fun () ->
    `!tids t tids'.
     set_tids_subset tids t /\ tids SUBSET tids' ==>
     set_tids_subset tids' t`)
  CHEAT_TAC;;

let set_tids_tenv_mono = cake_theorem "set_tids_tenv_mono[local]"
  (fun () ->
    `set_tids_tenv tids tenv /\ tids SUBSET tids' ==>
     set_tids_tenv tids' tenv`)
  CHEAT_TAC;;

let check_freevars_ts_tid_rename =
  cake_theorem "check_freevars_ts_tid_rename[local]"
  (fun () ->
    `!ts ls t.
     check_freevars ts ls (ts_tid_rename f t) <=>
     check_freevars ts ls t`)
  CHEAT_TAC;;

let sing_renum_def = cake_define
  `sing_renum m n = (\x. if x = m then n else x)`;;

(* HOL4 type_dCanonScript.sml:495-501: ML code, not ported *)

let sing_renum_NOT_tscheme_inst =
  cake_theorem "sing_renum_NOT_tscheme_inst[local]"
  (fun () ->
    `!t.
     m IN set_tids t /\ ~(
     m = n) ==> ~(
     ts_tid_rename (sing_renum m n) t = t) /\
     (!tvs tvs'.
     ~tscheme_inst (tvs,ts_tid_rename (sing_renum m n) t) (tvs',t)
       /\
     ~tscheme_inst (tvs',t) (tvs,ts_tid_rename (sing_renum m n)
       t))`)
  CHEAT_TAC;;

let sing_renum_NOTIN_ID = cake_theorem "sing_renum_NOTIN_ID"
  (fun () ->
    `!t. ~(
     m IN set_tids t) ==>
     ts_tid_rename (sing_renum m n) t = t`)
  CHEAT_TAC;;

let sing_renum_IN_NOT_ID = cake_theorem "sing_renum_IN_NOT_ID"
  (fun () ->
    `!t. m IN set_tids t /\ ~(m = n) ==> ~(ts_tid_rename (sing_renum m
  n) t = t)`)
  CHEAT_TAC;;

(* TODO: this is only true up to equivalence on tenvs *)
let sing_renum_NOTIN_tenv_ID = cake_theorem "sing_renum_NOTIN_tenv_ID"
  (fun () ->
    `set_tids_tenv tids tenv /\ ~(
     m IN tids) ==>
     tenv_equiv (remap_tenv (sing_renum m n) tenv) (tenv)`)
  CHEAT_TAC;;

let type_p_ts_tid_rename = cake_theorem "type_p_ts_tid_rename"
  (fun () ->
    `good_remap f ==>
     (!tvs tenv p t bindings.
     type_p tvs tenv p t bindings ==>
     type_p tvs (remap_tenv f tenv) p (ts_tid_rename f t)
     (MAP (\(n,t). (n,ts_tid_rename f t)) bindings)) /\
     (!tvs tenv ps ts bindings.
     type_ps tvs tenv ps ts bindings ==>
     type_ps tvs (remap_tenv f tenv) ps (MAP (ts_tid_rename f) ts)
     (MAP (\(n,t). (n,ts_tid_rename f t)) bindings))`)
  CHEAT_TAC;;

let type_op_ts_tid_rename = cake_theorem "type_op_ts_tid_rename"
  (fun () ->
    `good_remap f ==>
     (!op ts t.
     type_op op ts t ==>
     type_op op (MAP (ts_tid_rename f) ts) (ts_tid_rename f t))`)
  CHEAT_TAC;;

let remap_tenvE_def = cake_define_list
  [`remap_tenvE f (typeSystem_Empty:tenv_val_exp) =
  (typeSystem_Empty:tenv_val_exp)`;
   `remap_tenvE f (typeSystem_Bind_tvar n e) = typeSystem_Bind_tvar n
  (remap_tenvE f e)`;
   `remap_tenvE f (typeSystem_Bind_name s n t e) =
  typeSystem_Bind_name s n (ts_tid_rename f t) (remap_tenvE f e)`];;

let num_tvs_remap_tenvE = cake_theorem "num_tvs_remap_tenvE[local]"
  (fun () ->
    `!tenvE. num_tvs (remap_tenvE f tenvE) = num_tvs tenvE`)
  CHEAT_TAC;;

let remap_tenvE_bind_var_list =
  cake_theorem "remap_tenvE_bind_var_list[local]"
  (fun () ->
    `!n env tenvE.
     remap_tenvE f (bind_var_list n env tenvE) =
     bind_var_list n (MAP (\(n,t). (n,ts_tid_rename f t)) env)
       (remap_tenvE f tenvE)`)
  CHEAT_TAC;;

let remap_tenvE_bind_tvar = cake_theorem "remap_tenvE_bind_tvar"
  (fun () ->
    `remap_tenvE f (bind_tvar tvs e) = bind_tvar tvs (remap_tenvE f e)`)
  CHEAT_TAC;;

let deBruijn_inc_ts_tid_rename =
  cake_theorem "deBruijn_inc_ts_tid_rename[local]"
  (fun () ->
    `!skip n t.
     ts_tid_rename f (deBruijn_inc skip n t) =
     deBruijn_inc skip n (ts_tid_rename f t)`)
  CHEAT_TAC;;

let lookup_varE_remap_tenvE =
  cake_theorem "lookup_varE_remap_tenvE[local]"
  (fun () ->
    `!n tenvE.
     lookup_varE n (remap_tenvE f tenvE) = OPTION_MAP (\(id',t).
       (id',ts_tid_rename f t)) (lookup_varE n tenvE)`)
  CHEAT_TAC;;

let ts_tid_rename_deBruijn_subst =
  cake_theorem "ts_tid_rename_deBruijn_subst[local]"
  (fun () ->
    `!n targs t.
     ts_tid_rename f (deBruijn_subst n targs t) =
     deBruijn_subst n (MAP (ts_tid_rename f) targs)
       (ts_tid_rename f t)`)
  CHEAT_TAC;;

let type_e_ts_tid_rename = cake_theorem "type_e_ts_tid_rename"
  (fun () ->
    `good_remap f ==>
     (!tenv tenvE e t.
     type_e tenv tenvE e t ==>
     type_e (remap_tenv f tenv) (remap_tenvE f tenvE) e
       (ts_tid_rename f t)) /\
     (!tenv tenvE es ts.
     type_es tenv tenvE es ts ==>
     type_es (remap_tenv f tenv) (remap_tenvE f tenvE) es (MAP
       (ts_tid_rename f) ts)) /\
     (!tenv tenvE funs env.
     type_funs tenv tenvE funs env ==>
     type_funs (remap_tenv f tenv) (remap_tenvE f tenvE) funs
       (MAP (\(n,t). (n,ts_tid_rename f t)) env))`)
  CHEAT_TAC;;

let good_remap_LINV = cake_theorem "good_remap_LINV"
  (fun () ->
    `good_remap f /\ prim_tids T s /\ INJ f s t ==> good_remap (LINV f
  s o f)`)
  CHEAT_TAC;;

let ts_tid_rename_LINV = cake_theorem "ts_tid_rename_LINV"
  (fun () ->
    `!f x. INJ f s t /\ set_tids_subset s x ==> ts_tid_rename (LINV f
  s) (ts_tid_rename f x) = x`)
  CHEAT_TAC;;

let LINVI_def = cake_define
  `LINVI f s y = (match LINV_OPT f s y with SOME x -> x | NONE -> f
  y)`;;

let remap_tenv_LINV = cake_theorem "remap_tenv_LINV"
  (fun () ->
    `BIJ f s t /\ set_tids_tenv s tenv ==>
     tenv_equiv (remap_tenv (LINV f s) (remap_tenv f tenv)) tenv`)
  CHEAT_TAC;;

let good_remap_BIJ = cake_theorem "good_remap_BIJ"
  (fun () ->
    `good_remap f /\ prim_tids T s /\ BIJ f s t ==> good_remap (LINV f
  s)`)
  CHEAT_TAC;;

let good_remap_LINVI = cake_theorem "good_remap_LINVI"
  (fun () ->
    `good_remap f /\ prim_tids T s /\ INJ f s t ==> good_remap (LINVI
  f s)`)
  CHEAT_TAC;;

let INJ_LINVI = cake_theorem "INJ_LINVI"
  (fun () ->
    `INJ f s t /\ x IN s ==> LINVI f s (f x) = x`)
  CHEAT_TAC;;

let LINVI_RINV = cake_theorem "LINVI_RINV"
  (fun () ->
    `INJ f s t /\ (?x. x IN s /\ f x = y) ==>
     f (LINVI f s y) = y`)
  CHEAT_TAC;;

(* HOL4 type_dCanonScript.sml:839-853: code that the source has in a
   comment *)

let ts_tid_rename_LINVI = cake_theorem "ts_tid_rename_LINVI"
  (fun () ->
    `!f x. INJ f s t /\ set_tids_subset s x ==> ts_tid_rename (LINVI f
  s) (ts_tid_rename f x) = x`)
  CHEAT_TAC;;

let remap_tenv_LINVI = cake_theorem "remap_tenv_LINVI"
  (fun () ->
    `INJ f s t /\ set_tids_tenv s tenv ==>
     tenv_equiv (remap_tenv (LINVI f s) (remap_tenv f tenv)) tenv`)
  CHEAT_TAC;;

let ts_tid_rename_compose = cake_theorem "ts_tid_rename_compose"
  (fun () ->
    `!g t f. ts_tid_rename f (ts_tid_rename g t) = ts_tid_rename (f o
  g) t`)
  CHEAT_TAC;;

let remap_tenv_compose = cake_theorem "remap_tenv_compose"
  (fun () ->
    `remap_tenv f (remap_tenv g tenv) = remap_tenv (f o g) tenv`)
  CHEAT_TAC;;

let ts_tid_rename_eq_id = cake_theorem "ts_tid_rename_eq_id"
  (fun () ->
    `!f t. (ts_tid_rename f t = t <=> (!x. x IN set_tids t ==> f x =
  x))`)
  CHEAT_TAC;;

let ts_tid_rename_eq_f = cake_theorem "ts_tid_rename_eq_f"
  (fun () ->
    `!f t g. (ts_tid_rename f t = ts_tid_rename g t <=> (!x. x IN
  set_tids t ==> f x = g x))`)
  CHEAT_TAC;;

let inj_ts_tid_rename_eq = cake_theorem "inj_ts_tid_rename_eq"
  (fun () ->
    `!f t1 t2.
      (!x y.
        x IN set_tids t1 /\ y IN set_tids t2 /\
        f x = f y ==> x = y) /\
      (ts_tid_rename f t1 = ts_tid_rename f t2) ==> t1 = t2`)
  CHEAT_TAC;;

(* HOL4 type_dCanonScript.sml:938-945: code that the source has in a
   comment *)

let type_p_ts_tid_rename_sing_renum =
  cake_theorem "type_p_ts_tid_rename_sing_renum[local]"
  (fun () ->
    `~(
     m IN tids) /\ prim_tids T tids /\
     type_p tvs tenv p t bindings /\
     set_tids_tenv tids tenv ==>
     type_p tvs tenv p (ts_tid_rename (sing_renum m n) t)
     (MAP (\(nn,t). (nn,ts_tid_rename (sing_renum m n) t))
       bindings)`)
  CHEAT_TAC;;

let type_e_ts_tid_rename_sing_renum =
  cake_theorem "type_e_ts_tid_rename_sing_renum[local]"
  (fun () ->
    `~(
     m IN tids) /\ prim_tids T tids /\
     type_e tenv tenvE e t /\
     set_tids_tenv tids tenv ==>
     type_e tenv (remap_tenvE (sing_renum m n) tenvE) e
       (ts_tid_rename (sing_renum m n) t)`)
  CHEAT_TAC;;

let type_funs_ts_tid_rename_sing_renum =
  cake_theorem "type_funs_ts_tid_rename_sing_renum"
  (fun () ->
    `~(
       m IN tids) /\ prim_tids T tids /\
     type_funs tenv tenvE funs res /\
     set_tids_tenv tids tenv ==>
     type_funs tenv (remap_tenvE (sing_renum m n) tenvE) funs
       (MAP (\(z,t). (z,ts_tid_rename (sing_renum m n) t)) res)`)
  CHEAT_TAC;;

let type_pe_bindings_tids = cake_theorem "type_pe_bindings_tids[local]"
  (fun () ->
    `prim_tids T tids /\
     set_tids_tenv tids tenv /\
     type_p tvs tenv p t bindings /\
     type_e tenv (bind_tvar tvs typeSystem_Empty) e t /\
     (!tvs' bindings' t'.
         type_p tvs' tenv p t' bindings' /\
         type_e tenv (bind_tvar tvs' typeSystem_Empty) e t' ==>
         LIST_REL tscheme_inst
           (MAP SND (MAP (\(n,t). (n,tvs',t)) bindings'))
           (MAP SND (MAP (\(n,t). (n,tvs,t)) bindings))) ==>
     (!p_1 p_2. MEM (p_1,p_2) bindings ==> set_tids_subset tids
       p_2)`)
  CHEAT_TAC;;

let type_funs_bindings_tids = cake_theorem "type_funs_bindings_tids"
  (fun () ->
    `type_funs tenv (bind_var_list 0 bindings (bind_tvar tvs
  typeSystem_Empty)) funs bindings /\
     set_tids_tenv tids tenv /\ prim_tids T tids /\
     (!tvs' bindings'.
       type_funs tenv (bind_var_list 0 bindings' (bind_tvar tvs'
         typeSystem_Empty)) funs bindings' ==>
       LIST_REL tscheme_inst (MAP (\x. (tvs',SND x)) bindings')
         (MAP (\x. (tvs,SND x)) bindings)) ==>
     EVERY (set_tids_subset tids o SND) bindings`)
  CHEAT_TAC;;

let type_pe_bindings_tids_0 = cake_theorem "type_pe_bindings_tids_0"
  (fun () ->
    `prim_tids T tids /\
     set_tids_tenv tids tenv /\
     type_p 0 tenv p t bindings /\
     type_e tenv typeSystem_Empty e t /\
     type_pe_determ tenv typeSystem_Empty p e ==>
     (!p_1 p_2. MEM (p_1,p_2) bindings ==> set_tids_subset tids
       p_2)`)
  CHEAT_TAC;;

let type_pe_determ_remap = cake_theorem "type_pe_determ_remap"
  (fun () ->
    `type_pe_determ tenv typeSystem_Empty p e /\
     good_remap f /\
     prim_tids T tids /\
     BIJ f tids (count n) /\
     set_tids_tenv tids tenv ==>
     type_pe_determ_canon n (remap_tenv f tenv) typeSystem_Empty
       p e`)
  CHEAT_TAC;;

let build_ctor_tenv_type_identities =
  cake_theorem "build_ctor_tenv_type_identities"
  (fun () ->
    `!tenvt xs type_identities tids.
     prim_tids T tids /\
     nsAll (\i (ls,t). set_tids_subset (tids UNION set_of_list
       type_identities) t) tenvt /\
     LENGTH xs = LENGTH type_identities ==>
     nsAll ((\i (ls,ts,tid).
     EVERY (\t. set_tids_subset (tids UNION set_of_list
       type_identities) t) ts /\
     (tid IN tids \/ MEM tid type_identities)))
     (build_ctor_tenv tenvt xs type_identities)`)
  CHEAT_TAC;;

(* HOL4 type_dCanonScript.sml:1173-1183: code that the source has in
   a comment *)

let DISJOINT_CARD_UNION = cake_theorem "DISJOINT_CARD_UNION"
  (fun () ->
    `FINITE s /\ FINITE t /\ DISJOINT s t ==> CARD (s UNION t) = CARD
  s + CARD t`)
  CHEAT_TAC;;

(* For any type_d, prove that the canonical type identifier strategy
  succeeds.
  f,g are maps from the identifiers used in type_d into the ones
  used by type_d_canon
  TODO: do we actually need the bijection??
*)
let type_d_type_d_canon = cake_theorem "type_d_type_d_canon"
  (fun () ->
    `(!extra_checks tenv d ids tenv'.
     type_d extra_checks tenv d ids tenv' ==>
     (!tids f n mapped_tenv.
     extra_checks = T /\
     DISJOINT ids tids /\
     set_tids_tenv tids tenv /\
     BIJ f tids (count n) /\
     prim_tids T tids /\ good_remap f /\
     tenv_equiv (remap_tenv f tenv) mapped_tenv ==>
       (?g mapped_tenv'.
         set_tids_tenv (tids UNION ids) tenv' /\ prim_tids F ids /\
           FINITE ids /\
         BIJ g ids (count (CARD ids)) /\
         type_d_canon n mapped_tenv d (CARD ids) mapped_tenv' /\
         tenv_equiv (remap_tenv (extend_bij f g ids n) tenv')
           mapped_tenv'))) /\
     (!extra_checks tenv ds ids tenv'.
     type_ds extra_checks tenv ds ids tenv' ==>
     (!tids f n mapped_tenv.
     extra_checks = T /\
     DISJOINT ids tids /\
     set_tids_tenv tids tenv /\
     BIJ f tids (count n) /\
     prim_tids T tids /\ good_remap f /\
     tenv_equiv (remap_tenv f tenv) mapped_tenv ==>
     (?g mapped_tenv'.
       set_tids_tenv (tids UNION ids) tenv' /\ prim_tids F ids /\
         FINITE ids /\
       BIJ g ids (count (CARD ids)) /\
       type_ds_canon n mapped_tenv ds (CARD ids) mapped_tenv' /\
       tenv_equiv (remap_tenv (extend_bij f g ids n) tenv')
         mapped_tenv')))`)
  CHEAT_TAC;;

(* n.b. proof almost entirely copied from type_d_tenv_ok_helper *)
let type_d_canon_tenv_ok = cake_theorem "type_d_canon_tenv_ok"
  (fun () ->
    `(!check tenv d tdecs tenv'.
      type_d_canon check tenv d tdecs tenv' ==>
      tenv_ok tenv ==>
      tenv_ok tenv') /\
     (!check tenv d tdecs tenv'.
      type_ds_canon check tenv d tdecs tenv' ==>
      tenv_ok tenv ==>
      tenv_ok tenv')`)
  CHEAT_TAC;;
