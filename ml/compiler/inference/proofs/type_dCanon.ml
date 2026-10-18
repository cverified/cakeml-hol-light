(* ======================================================== *)
(*  type_dCanon: ported from HOL4's
    compiler/inference/proofs/type_dCanonScript.sml  *)
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

let extend_bij_def = cake_define
  `extend_bij (f:num->num) g ids n v =
   (if v IN ids then
     n + g v else
     f v)`;;

(* HOL4 type_dCanonScript.sml:334-344: code that the source has in a
   comment *)

(* needs monotonicity of set_tids_tenv *)

(* HOL4 type_dCanonScript.sml:390-404: code that the source has in a
   comment *)

(* HOL4 type_dCanonScript.sml:428-460: code that the source has in a
   comment *)

let sing_renum_def = cake_define
  `sing_renum m n = (\x. if x = m then n else x)`;;

(* HOL4 type_dCanonScript.sml:495-501: ML code, not ported *)

(* TODO: this is only true up to equivalence on tenvs *)

let remap_tenvE_def = cake_define_list
  [`remap_tenvE f (typeSystem_Empty:tenv_val_exp) =
  (typeSystem_Empty:tenv_val_exp)`;
   `remap_tenvE f (typeSystem_Bind_tvar n e) = typeSystem_Bind_tvar n
  (remap_tenvE f e)`;
   `remap_tenvE f (typeSystem_Bind_name s n t e) =
  typeSystem_Bind_name s n (ts_tid_rename f t) (remap_tenvE f e)`];;

let LINVI_def = cake_define
  `LINVI f s y = (match LINV_OPT f s y with SOME x -> x | NONE -> f
  y)`;;

(* HOL4 type_dCanonScript.sml:839-853: code that the source has in a
   comment *)

(* HOL4 type_dCanonScript.sml:938-945: code that the source has in a
   comment *)

(* HOL4 type_dCanonScript.sml:1173-1183: code that the source has in
   a comment *)

(* For any type_d, prove that the canonical type identifier strategy
  succeeds.
  f,g are maps from the identifiers used in type_d into the ones
  used by type_d_canon
  TODO: do we actually need the bijection??
*)

(* n.b. proof almost entirely copied from type_d_tenv_ok_helper *)
