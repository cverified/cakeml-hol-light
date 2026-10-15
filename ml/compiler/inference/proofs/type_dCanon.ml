(* ======================================================== *)
(*  type_dCanon: ported from HOL4's
    compiler/inference/proofs/type_dCanonScript.sml  *)
(* ======================================================== *)

(*
  For any type_d, prove that the canonical type identifier strategy
  succeeds.
*)

needs "compiler/backend/pattern_matching/pattern_semantics.ml";;
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
      nsAll2 (\i v1 v2. v1 = v2) (?_c tenv1) (?_c tenv2) /\
      nsAll2 (\i v1 v2. v1 = v2) (?_v tenv1) (?_v tenv2)`;;

(* -- *)

(* all the tids used in a tenv *)
let set_tids_tenv_def = cake_define
  `set_tids_tenv tids tenv <=>
   nsAll (\i (ls,t). set_tids_subset tids t) (type_env_t tenv) /\
   nsAll (\i (ls,ts,tid). EVERY (\t. set_tids_subset tids t) ts /\
     tid IN tids) (?_c tenv) /\
   nsAll (\i (n,t). set_tids_subset tids t) (?_v tenv)`;;

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
     ALL_DISTINCT (pat_bindings p) /\
     type_p tvs tenv p t bindings /\
     type_e tenv (bind_tvar tvs Empty) e t /\
     (!tvs' bindings' t'.
     (type_p tvs' tenv p t' bindings' /\
     type_e tenv (bind_tvar tvs' Empty) e t' /\
     EVERY (\(k,t). set_tids_subset (count n) t) bindings') ==>
           EVERY2 tscheme_inst (MAP SND (tenv_add_tvs tvs'
             bindings')) (MAP SND (tenv_add_tvs tvs bindings)))) ==>
     type_d_canon n tenv (Dlet locs p e)
       0
       (mk_? (alist_to_ns (tenv_add_tvs tvs bindings)) nsEmpty
         nsEmpty)) /\
   (!n tenv p e t bindings locs.
     ((~(is_value e) /\ type_pe_determ_canon n tenv Empty p e) /\
     ALL_DISTINCT (pat_bindings p) /\
     type_p ((0:num)) tenv p t bindings /\
     type_e tenv Empty e t) ==>
     type_d_canon n tenv (Dlet locs p e)
       0 (mk_? (alist_to_ns (tenv_add_tvs ((0:num)) bindings))
         nsEmpty nsEmpty)) /\
   (!n tenv funs bindings tvs locs.
     (type_funs tenv (bind_var_list ((0:num)) bindings (bind_tvar tvs
       Empty)) funs bindings /\
     (!tvs' bindings'.
         type_funs tenv (bind_var_list ((0:num)) bindings' (bind_tvar
           tvs' Empty)) funs bindings' /\
         EVERY (\(k,t). set_tids_subset (count n) t) bindings' ==>
           EVERY2 tscheme_inst (MAP SND (tenv_add_tvs tvs'
             bindings')) (MAP SND (tenv_add_tvs tvs bindings)))) ==>
     type_d_canon n tenv (Dletrec locs funs)
     0 (mk_? (alist_to_ns (tenv_add_tvs tvs bindings)) nsEmpty
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
       (mk_? nsEmpty (build_ctor_tenv (nsAppend tenvT (type_env_t
         tenv)) tdefs type_identities) tenvT)) /\
   (!n tenv tvs tn t locs.
     (check_freevars_ast tvs t /\
     check_type_names (type_env_t tenv) t /\
     ALL_DISTINCT tvs) ==>
     type_d_canon n tenv (Dtabbrev locs tvs tn t)
       0
       (mk_? nsEmpty nsEmpty (nsSing tn (tvs,type_name_subst
         (type_env_t tenv) t)))) /\
   (!n tenv cn ts locs.
     (EVERY (check_freevars_ast []) ts /\
     EVERY (check_type_names (type_env_t tenv)) ts) ==>
     type_d_canon n tenv (Dexn locs cn ts)
       0
       (mk_? nsEmpty (nsSing cn ([],MAP (type_name_subst (type_env_t
         tenv)) ts,Texn_num)) nsEmpty)) /\
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
       (mk_? nsEmpty nsEmpty nsEmpty)) /\
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

(*
Definition extend_bij_def:
  extend_bij (f:type_ident->type_ident) g tids ids n v =
  if v ∈ tids then
    f v
  else if v ∈ ids then
    n + g v
  else
    v
End
*)

(* needs monotonicity of set_tids_tenv *)

(*
Theorem good_remap_extend_bij[local]:
  good_remap f ∧ prim_tids T tids ⇒
  good_remap (extend_bij f g tids n)
Proof
  rw[good_remap_def, extend_bij_def, prim_tids_def,prim_type_nums_def]
QED

Theorem good_remap_extend_bij[local]:
  good_remap f ∧ prim_tids T tids ⇒
  good_remap (extend_bij f g tids ids n)
Proof
  rw[good_remap_def, extend_bij_def, prim_tids_def,prim_type_nums_def]
QED
*)

(*
Theorem INJ_extend_bij:
    DISJOINT tids ids ∧
  INJ f tids (count n) ∧
  INJ g ids (count (CARD ids)) ⇒
  INJ (extend_bij f g ids n) (tids ∪ ids) (count (n + CARD ids))
Proof
  rewrite_tac[INJ_DEF,extend_bij_def,IN_DISJOINT,IN_COUNT,IN_UNION]
  \\ rpt strip_tac
  \\ res_tac
  \\ rpt (pop_assum mp_tac)
  \\ rewrite_tac[]
  \\ rpt IF_CASES_TAC
  \\ rpt strip_tac
  \\ full_simp_tac bool_ss []
  \\ fs[]
QED

Theorem BIJ_extend_bij:
    DISJOINT tids ids ∧
  BIJ f tids (count n) ∧
  BIJ g ids (count (CARD ids)) ⇒
  BIJ (extend_bij f g tids ids n) (tids ∪ ids) (count (n + CARD ids))
Proof
  rewrite_tac[INJ_DEF,SURJ_DEF,BIJ_DEF,extend_bij_def,IN_DISJOINT]
  \\ strip_tac
  \\ rewrite_tac[IN_UNION, count_add, IN_IMAGE]
  \\ reverse conj_tac >- metis_tac[]
  \\ conj_tac >- metis_tac[]
  \\ rw[]
  \\ rpt (first_x_assum drule)>>fs[]
QED
*)

let sing_renum_def = cake_define
  `sing_renum m n = (\x. if x = m then n else x)`;;

(* HOL4 ML code, not ported:
val ast_t_ind = ast_t_induction
  |> Q.SPECL[`P`,`EVERY P`]
  |> UNDISCH_ALL
  |> CONJUNCT1
  |> DISCH_ALL
  |> SIMP_RULE (srw_ss()) []
  |> Q.GEN`P`;
*)

(* TODO: this is only true up to equivalence on tenvs *)

let remap_tenvE_def = cake_define_list
  [`remap_tenvE f Empty = Empty`;
   `remap_tenvE f (Bind_tvar n e) = Bind_tvar n (remap_tenvE f e)`;
   `remap_tenvE f (Bind_name s n t e) = Bind_name s n (ts_tid_rename
  f t) (remap_tenvE f e)`];;

let LINVI_def = cake_define
  `LINVI f s y = (match LINV_OPT f s y with SOME x -> x | NONE -> f
  y)`;;

(*
Theorem BIJ_LINVI_RINV:
   BIJ f s t ∧ LINVI f s y ∈ s ⇒
   f (LINVI f s y) = y
Proof
  rw[LINVI_def, LINV_OPT_def] \\ fs[]
  ff"bij""inv"
  f"LINV_OPT"
  \\ imp_res_tac
  \\ drule INJ_LINV_OPT
  \\ disch_then(qspec_then`f x`mp_tac o CONV_RULE SWAP_FORALL_CONV)
  \\ CASE_TAC \\ rw[]
  \\ metis_tac[INJ_DEF]
QED
*)

(* probably not be true because of shadows...
Theorem remap_tenv_LINVI
  `INJ f s t ∧ set_tids_tenv s tenv ⇒
   remap_tenv (LINVI f s) (remap_tenv f tenv) = tenv`
  (rw[remap_tenv_def, type_env_component_equality,
     nsMap_compose, o_DEF, UNCURRY, MAP_MAP_o,
     set_tids_tenv_def]
*)

(*
Theorem type_d_canon_tenv_equiv
  `(∀x t d c v. type_d_canon x t d c v ⇒
      ∀v2. tenv_equiv v v2 ⇒ type_d_canon x t d c v2) ∧
   (∀x t d c v. type_ds_canon x t d c v ⇒
      ∀v2. tenv_equiv v v2 ⇒ type_ds_canon x t d c v2)`
  (ho_match_mp_tac type_d_canon_ind
  \\ rw[]
  \\ rw[Once type_d_canon_cases]
  type_d_canon_rules
*)

(* For any type_d, prove that the canonical type identifier strategy
  succeeds.
  f,g are maps from the identifiers used in type_d into the ones
  used by type_d_canon
  TODO: do we actually need the bijection??
*)

(* n.b. proof almost entirely copied from type_d_tenv_ok_helper *)
