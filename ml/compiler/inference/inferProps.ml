(* ======================================================== *)
(*  inferProps: ported from HOL4's
    compiler/inference/inferPropsScript.sml
    A proof theory about infer.ml, with 13 definitions and 158
    theorems.  Needed by 8 files of the port.  *)
(* ======================================================== *)

(*
  Various lemmas that are handy in the soundness and completeness
  proofs of the type inferencer.
*)

needs "compiler/inference/infer.ml";;
needs "compiler/inference/infer_t.ml";;
needs "compiler/inference/unify.ml";;
needs "semantics/ast.ml";;
needs "semantics/namespace.ml";;
needs "semantics/proofs/namespaceProps.ml";;
needs "semantics/proofs/typeSoundInvariants.ml";;
needs "semantics/proofs/typeSysProps.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "semantics/typeSystem.ml";;
needs "translator/monadic/monad_base/ml_monadBase.ml";;

cake_hide ["C"; "id"; "inst"];;

let ienv_unchanged = cake_theorem "ienv_unchanged[simp]"
  (fun () ->
    `(inf_env_inf_v_fupd (K (inf_env_inf_v ienv)) ienv) = ienv /\
     (inf_env_inf_c_fupd (K (inf_env_inf_c ienv)) ienv) = ienv /\
     (inf_env_inf_t_fupd (K (inf_env_inf_t ienv)) ienv) = ienv`)
  CHEAT_TAC;;

let extend_dec_ienv_empty = cake_theorem "extend_dec_ienv_empty"
  (fun () ->
    `!ienv.
      extend_dec_ienv ienv (mk_inf_env nsEmpty nsEmpty nsEmpty) =
        ienv /\
      extend_dec_ienv (mk_inf_env nsEmpty nsEmpty nsEmpty) ienv =
        ienv`)
  CHEAT_TAC;;

(* ---------- Facts about deBruijn increment ---------- *)

let infer_deBruijn_inc0 = cake_theorem "infer_deBruijn_inc0"
  (fun () ->
    `!(n:num) t. infer_deBruijn_inc 0 t = t`)
  CHEAT_TAC;;

let infer_deBruijn_inc0_id = cake_theorem "infer_deBruijn_inc0_id"
  (fun () ->
    `infer_deBruijn_inc 0 = (\x. x)`)
  CHEAT_TAC;;

let t_vars_inc = cake_theorem "t_vars_inc"
  (fun () ->
    `!tvs t. t_vars (infer_deBruijn_inc tvs t) = t_vars t`)
  CHEAT_TAC;;

let inc_wfs = cake_theorem "inc_wfs"
  (fun () ->
    `!tvs s. t_wfs s ==> t_wfs (infer_deBruijn_inc tvs o_f s)`)
  CHEAT_TAC;;

let vwalk_inc = cake_theorem "vwalk_inc"
  (fun () ->
    `!s tvs n.
      t_wfs s ==>
      t_vwalk (infer_deBruijn_inc tvs o_f s) n =
        infer_deBruijn_inc tvs (t_vwalk s n)`)
  CHEAT_TAC;;

let walk_inc = cake_theorem "walk_inc"
  (fun () ->
    `!s tvs t.
      t_wfs s ==>
      t_walk (infer_deBruijn_inc tvs o_f s) (infer_deBruijn_inc
        tvs t) = infer_deBruijn_inc tvs (t_walk s t)`)
  CHEAT_TAC;;

let walkstar_inc = cake_theorem "walkstar_inc"
  (fun () ->
    `!tvs s t.
      t_wfs s ==>
      (t_walkstar (infer_deBruijn_inc tvs o_f s)
        (infer_deBruijn_inc tvs t) =
       infer_deBruijn_inc tvs (t_walkstar s t))`)
  CHEAT_TAC;;

let walkstar_inc2 = cake_theorem "walkstar_inc2"
  (fun () ->
    `!tvs s n.
      t_wfs s ==>
      (t_walkstar (infer_deBruijn_inc tvs o_f s) (Infer_Tuvar n) =
       infer_deBruijn_inc tvs (t_walkstar s (Infer_Tuvar n)))`)
  CHEAT_TAC;;

(* ---------- Type substitution ---------- *)

let subst_infer_subst_swap = cake_theorem "subst_infer_subst_swap"
  (fun () ->
    `(!t tvs s uvar.
      t_wfs s ==>
      (
       t_walkstar s (infer_type_subst (ZIP tvs (MAP (\n.
         Infer_Tuvar (uvar + n)) (COUNT_LIST (LENGTH tvs)))) t) =
       infer_type_subst (ZIP tvs (MAP (\n. t_walkstar s
         (Infer_Tuvar (uvar + n))) (COUNT_LIST (LENGTH tvs)))) t)) /\
     (!ts tvs s uvar.
      t_wfs s ==>
      (
       MAP (t_walkstar s) (MAP (infer_type_subst (ZIP tvs (MAP (\n.
         Infer_Tuvar (uvar + n)) (COUNT_LIST (LENGTH tvs))))) ts) =
       MAP (infer_type_subst (ZIP tvs (MAP (\n. t_walkstar s
         (Infer_Tuvar (uvar + n))) (COUNT_LIST (LENGTH tvs))))) ts))`)
  CHEAT_TAC;;

(* HOL4 inferPropsScript.sml:157: ML code, not ported *)

let infer_subst_FEMPTY = cake_theorem "infer_subst_FEMPTY"
  (fun () ->
    `(!t. infer_subst FEMPTY t = t) /\
     (!ts. MAP (infer_subst FEMPTY) ts = ts)`)
  CHEAT_TAC;;

let infer_subst_submap = cake_theorem "infer_subst_submap"
  (fun () ->
    `(!t s1 s2 m.
        s1 SUBMAP s2 /\
        {uv | uv IN t_vars t /\ m <= uv} SUBSET FDOM s1 /\
        (!uv. uv IN FDOM s2 DIFF FDOM s1 ==> m <= uv) ==>
        (infer_subst s1 t = infer_subst s2 t)) /\
     (!ts s1 s2 m.
        s1 SUBMAP s2 /\
        {uv | ?s. uv IN s /\ MEM s (MAP t_vars ts) /\ m <= uv}
          SUBSET FDOM s1 /\
        (!uv. uv IN FDOM s2 DIFF FDOM s1 ==> m <= uv) ==>
        (MAP (infer_subst s1) ts = MAP (infer_subst s2) ts))`)
  CHEAT_TAC;;

let generalise_list_length = cake_theorem "generalise_list_length"
  (fun () ->
    `!a b c d e f g.
     generalise_list a b c d = (e,f,g) ==> LENGTH g = LENGTH d`)
  CHEAT_TAC;;

let generalise_subst = cake_theorem "generalise_subst"
  (fun () ->
    `(!t m n s tvs s' t'.
      (generalise m n s t = (tvs,s',t')) ==>
      (s SUBMAP s') /\
      (FDOM s' = FDOM s UNION {uv | uv IN t_vars t /\ m <= uv}) /\
      (!uv. uv IN FDOM s' DIFF FDOM s ==> (?tv. (FAPPLY s' uv = tv)
        /\ n <= tv /\ tv < tvs + n)) /\
      (!uv. uv IN t_vars t' ==> uv < m) /\
      (infer_subst s' t = infer_subst s t')) /\
     (!ts m n s tvs s' ts'.
      (generalise_list m n s ts = (tvs,s',ts')) ==>
      (s SUBMAP s') /\
      (FDOM s' = FDOM s UNION {uv | uv IN BIGUNION (set_of_list
        (MAP t_vars ts)) /\ m <= uv}) /\
      (!uv. uv IN FDOM s' DIFF FDOM s ==> (?tv. (FAPPLY s' uv = tv)
        /\ n <= tv /\ tv < tvs + n)) /\
      (!uv. uv IN BIGUNION (set_of_list (MAP t_vars ts')) ==> uv <
        m) /\
      (MAP (infer_subst s') ts = MAP (infer_subst s) ts'))`)
  CHEAT_TAC;;

let generalise_subst_empty = cake_theorem "generalise_subst_empty"
  (fun () ->
    `!n ts tvs s ts'.
      (generalise_list 0 n FEMPTY ts = (tvs,s,ts')) ==>
      (FDOM s = {uv | uv IN BIGUNION (set_of_list (MAP t_vars
        ts))}) /\
      (!uv. uv IN FDOM s ==> (?tv. (FAPPLY s uv = tv) /\ tv < tvs +
        n)) /\
      (BIGUNION (set_of_list (MAP t_vars ts')) = {}) /\
      (ts' = MAP (infer_subst s) ts)`)
  CHEAT_TAC;;

(* ---------- Dealing with the monad ---------- *)

(* TODO: update *)
let infer_st_rewrs = cake_theorem "infer_st_rewrs"
  (fun () ->
    `(!st. (infer_st_next_uvar_fupd (K (infer_st_next_uvar st)) st) =
  st) /\
     (!st. (infer_st_subst_fupd (K (infer_st_subst st)) st) = st)
       /\
     (!st s. infer_st_subst (infer_st_subst_fupd (K s) st) = s) /\
     (!st s. infer_st_next_uvar (infer_st_subst_fupd (K s) st) =
       infer_st_next_uvar st) /\
     (!st uv. infer_st_next_uvar (infer_st_next_uvar_fupd (K uv)
       st) = uv) /\
     (!st uv. infer_st_subst (infer_st_next_uvar_fupd (K uv) st)
       = infer_st_subst st)`)
  CHEAT_TAC;;

let inferProps_st_ex_return_success =
  cake_theorem "st_ex_return_success[local]"
  (fun () ->
    `!v st v' st'.
     (st_ex_return v st = (M_success v',st')) =
     ((v = v') /\ (st = st'))`)
  CHEAT_TAC;;

let inferProps_st_ex_bind_success =
  cake_theorem "st_ex_bind_success[local]"
  (fun () ->
    `!f g st st' v.
     (st_ex_bind f g st = (M_success v,st')) =
     (?v' st''. (f st = (M_success v',st'')) /\ (g v' st'' =
       (M_success v,st')))`)
  CHEAT_TAC;;

let st_ex_ignore_bind_success =
  cake_theorem "st_ex_ignore_bind_success[local]"
  (fun () ->
    `!f g st st' v.
     (st_ex_ignore_bind f g st = (M_success v,st')) =
     (?v' st''. (f st = (M_success v',st'')) /\ (g st'' =
       (M_success v,st')))`)
  CHEAT_TAC;;

let fresh_uvar_success = cake_theorem "fresh_uvar_success[local]"
  (fun () ->
    `!st t st'.
     (fresh_uvar st = (M_success t,st')) =
     ((t = Infer_Tuvar (infer_st_next_uvar st)) /\
      (st' = infer_st_next_uvar_fupd (K (infer_st_next_uvar st +
        1)) st))`)
  CHEAT_TAC;;

let n_fresh_uvar_success = cake_theorem "n_fresh_uvar_success"
  (fun () ->
    `!n st ts st'.
      (n_fresh_uvar n st = (M_success ts,st')) =
      ((ts = MAP (\n. Infer_Tuvar (infer_st_next_uvar st + n))
        (COUNT_LIST n)) /\
       (st' = infer_st_next_uvar_fupd (K (infer_st_next_uvar st +
         n)) st))`)
  CHEAT_TAC;;

let apply_subst_success = cake_theorem "apply_subst_success[local]"
  (fun () ->
    `!t1 st1 t2 st2.
     (apply_subst t1 st1 = (M_success t2,st2)) =
     ((st2 = st1) /\
      (t2 = t_walkstar (infer_st_subst st1) t1))`)
  CHEAT_TAC;;

let add_constraint_success = cake_theorem "add_constraint_success"
  (fun () ->
    `!l t1 t2 st st' x.
      (add_constraint l t1 t2 st = (M_success x,st')) =
      ((x = one) /\ (?s. (t_unify (infer_st_subst st) t1 t2 =
        SOME s) /\ (st' = infer_st_subst_fupd (K s) st)))`)
  CHEAT_TAC;;

let add_constraints_success =
  cake_theorem "add_constraints_success[local]"
  (fun () ->
    `!l ts1 ts2 st st' x.
     (add_constraints l ts1 ts2 st = (M_success x,st')) =
     ((LENGTH ts1 = LENGTH ts2) /\
      ((x = one) /\
      (infer_st_next_uvar st = infer_st_next_uvar st') /\
      (infer_st_next_id st = infer_st_next_id st') /\
      pure_add_constraints (infer_st_subst st) (ZIP ts1 ts2)
        (infer_st_subst st')))`)
  CHEAT_TAC;;

let add_constraints_nil2_success =
  cake_theorem "add_constraints_nil2_success[local]"
  (fun () ->
    `(add_constraints l ts1 [] st = (M_success x,st')) = (ts1 = [] /\
  st = st')`)
  CHEAT_TAC;;

let add_constraints_cons2_success =
  cake_theorem "add_constraints_cons2_success[local]"
  (fun () ->
    `(add_constraints l ts1 (t2 :: ts2) st = (M_success x,st')) = (?t1
  tl1 st''. ts1 = t1 :: tl1 /\
       add_constraint l t1 t2 st = (M_success one,st'') /\
       add_constraints l tl1 ts2 st'' = (M_success x,st'))`)
  CHEAT_TAC;;

let failwith_success = cake_theorem "failwith_success[local]"
  (fun () ->
    `!l m st v st'. (infer_failwith l m st = (M_success v,st')) = F`)
  CHEAT_TAC;;

let lookup_st_ex_success = cake_theorem "lookup_st_ex_success[local]"
  (fun () ->
    `!loc x err l st v st'.
     (lookup_st_ex loc err x l st = (M_success v,st')) =
     ((nsLookup l x = SOME v) /\ (st = st'))`)
  CHEAT_TAC;;

(* HOL4 inferPropsScript.sml:502-507: ML code, not ported *)

(* HOL4 inferPropsScript.sml:509-511: ML code, not ported *)

(* HOL4 inferPropsScript.sml:513-519: ML code, not ported *)

(* HOL4 inferPropsScript.sml:521-523: ML code, not ported *)

let UNCURRY_rator = cake_theorem "UNCURRY_rator"
  (fun () ->
    `UNCURRY f x y = UNCURRY (\a b. f a b y) x`)
  CHEAT_TAC;;

let constrain_op_op_case = cake_theorem "constrain_op_op_case[local]"
  (fun () ->
    `constrain_op l op ts st = (match op with
         ast_Opapp -> (let x = one in constrain_op l op ts st) |
           _1 -> constrain_op l op ts st)`)
  CHEAT_TAC;;

(* HOL4 inferPropsScript.sml:539-550: the ML values that the
   definitions below antiquote *)

(* HOL4 inferPropsScript.sml:552-553: a theorem that HOL4 states as
   the value of an ML expression: constrain_op_success *)

let get_next_uvar_success = cake_theorem "get_next_uvar_success[local]"
  (fun () ->
    `!st v st'.
     (get_next_uvar st = (M_success v,st')) =
     ((v = infer_st_next_uvar st) /\ (st = st'))`)
  CHEAT_TAC;;

(* HOL4 inferPropsScript.sml:565-567: ML code, not ported *)

let guard_success = cake_theorem "guard_success[local]"
  (fun () ->
    `!P l m st v st'.
     (infer_guard P l m st = (M_success v,st')) =
     (P /\ (v = one) /\ (st = st'))`)
  CHEAT_TAC;;

let check_dups_success = cake_theorem "check_dups_success"
  (fun () ->
    `!l f ls s r s'.
      check_dups l f ls s = (M_success r,s') <=>
      s' = s /\ ALL_DISTINCT ls`)
  CHEAT_TAC;;

let type_name_check_subst_success =
  cake_theorem "type_name_check_subst_success"
  (fun () ->
    `(!t l f tenvT tvs r (s:'a) s'.
      type_name_check_subst l f tenvT tvs t s = (M_success r,s')
        <=>
      s = s' /\ r = type_name_subst tenvT t /\
      check_freevars_ast tvs t /\ check_type_names tenvT t) /\
     (!ts l f tenvT tvs r (s:'a) s'.
      type_name_check_subst_list l f tenvT tvs ts s = (M_success
        r,s') <=>
      s = s' /\ r = MAP (type_name_subst tenvT) ts /\
      EVERY (check_freevars_ast tvs) ts /\ EVERY
        (check_type_names tenvT) ts)`)
  CHEAT_TAC;;

let check_ctor_types_success = cake_theorem "check_ctor_types_success"
  (fun () ->
    `!l tenvT tvs ts s s'.
     check_ctor_types l tenvT tvs ts s = (M_success one,s') <=>
     s = s' /\
     EVERY (\(cn,ts). EVERY (check_freevars_ast tvs) ts /\
     EVERY (check_type_names tenvT) ts) ts`)
  CHEAT_TAC;;

let inferProps_check_dup_ctors_thm = cake_theorem "check_dup_ctors_thm"
  (fun () ->
    `check_dup_ctors (tvs,tn,condefs) = ALL_DISTINCT (MAP FST condefs)`)
  CHEAT_TAC;;

let check_ctors_success = cake_theorem "check_ctors_success"
  (fun () ->
    `!l tenvT tds s s'.
      ALL_DISTINCT (MAP (FST o SND) tds) ==>
      (check_ctors l tenvT tds s = (M_success one,s') <=>
       s' = s /\ check_ctor_tenv tenvT tds)`)
  CHEAT_TAC;;

let check_type_definition_success =
  cake_theorem "check_type_definition_success"
  (fun () ->
    `!l tenvT tds s r s'.
      check_type_definition l tenvT tds s = (M_success r,s') <=>
      s' = s /\ check_ctor_tenv tenvT tds`)
  CHEAT_TAC;;

let option_case_eq = cake_theorem "option_case_eq[local]"
  (fun () ->
    `!opt f g v st st'.
     ((match opt with NONE -> f | SOME x -> g x) st = (M_success
       v,st')) =
     (((opt = NONE) /\ (f st = (M_success v,st'))) \/ (?x. (opt =
       SOME x) /\ (g x st = (M_success v,st'))))`)
  CHEAT_TAC;;

(* HOL4 inferPropsScript.sml:724-734: ML code, not ported *)

(* HOL4 inferPropsScript.sml:736-737: a theorem that HOL4 states as
   the value of an ML expression: success_eqns *)

let remove_pair_lem = cake_theorem "remove_pair_lem"
  (fun () ->
    `(!f v. (\(x,y). f x y) v = f (FST v) (SND v)) /\
     (!f v. (\(x,y,z). f x y z) v = f (FST v) (FST (SND v)) (SND
       (SND v)))`)
  CHEAT_TAC;;

(* ---------- Simple structural properties ---------- *)

let infer_funs_length = cake_theorem "infer_funs_length"
  (fun () ->
    `!l ienv funs ts st1 st2.
      (infer_funs l ienv funs st1 = (M_success ts,st2)) ==>
      (LENGTH funs = LENGTH ts)`)
  CHEAT_TAC;;

let type_name_check_subst_state =
  cake_theorem "type_name_check_subst_state"
  (fun () ->
    `(!t l err tenvT fvs (st:'a) r st'. type_name_check_subst l err
  tenvT fvs t st = (r,st') ==> st = st') /\
     (!ts l err tenvT fvs (st:'a) r st'.
       type_name_check_subst_list l err tenvT fvs ts st = (r,st') ==>
       st = st')`)
  CHEAT_TAC;;

let infer_p_bindings = cake_theorem "infer_p_bindings"
  (fun () ->
    `(!l cenv p st t env st'.
        (infer_p l cenv p st = (M_success (t,env),st')) ==>
        (ast_pat_bindings p = MAP FST env)) /\
     (!l cenv ps st ts env st'.
        (infer_ps l cenv ps st = (M_success (ts,env),st')) ==>
        (ast_pats_bindings ps = MAP FST env))`)
  CHEAT_TAC;;

(* ---------- Dealing with the constraint set ---------- *)

let pure_add_constraints_append2 =
  cake_theorem "pure_add_constraints_append2[local]"
  (fun () ->
    `!s1 ts s2 t1 t2.
     t_wfs s1 /\
     pure_add_constraints s1 ts s2 /\
     (t_walkstar s1 t1 = t_walkstar s1 t2) ==>
     (t_walkstar s2 t1 = t_walkstar s2 t2)`)
  CHEAT_TAC;;

let pure_add_constraints_apply =
  cake_theorem "pure_add_constraints_apply"
  (fun () ->
    `!s1 ts s2.
      t_wfs s1 /\
      pure_add_constraints s1 ts s2 ==>
      MAP (t_walkstar s2 o FST) ts = MAP (t_walkstar s2 o SND) ts`)
  CHEAT_TAC;;

let pure_add_constraints_append =
  cake_theorem "pure_add_constraints_append"
  (fun () ->
    `!s1 ts1 s3 ts2.
      pure_add_constraints s1 (ts1 ++ ts2) s3 =
      (?s2. pure_add_constraints s1 ts1 s2 /\
        pure_add_constraints s2 ts2 s3)`)
  CHEAT_TAC;;

let infer_p_constraints = cake_theorem "infer_p_constraints"
  (fun () ->
    `(!l cenv p st t env st'.
        (infer_p l cenv p st = (M_success (t,env),st')) ==>
        (?ts. pure_add_constraints (infer_st_subst st) ts
          (infer_st_subst st'))) /\
     (!l cenv ps st ts env st'.
        (infer_ps l cenv ps st = (M_success (ts,env),st')) ==>
        (?ts'. pure_add_constraints (infer_st_subst st) ts'
          (infer_st_subst st')))`)
  CHEAT_TAC;;

let infer_e_constraints = cake_theorem "infer_e_constraints"
  (fun () ->
    `(!l ienv e st st' t.
        (infer_e l ienv e st = (M_success t,st')) ==>
        (?ts. pure_add_constraints (infer_st_subst st) ts
          (infer_st_subst st'))) /\
     (!l ienv es st st' ts.
        (infer_es l ienv es st = (M_success ts,st')) ==>
        (?ts. pure_add_constraints (infer_st_subst st) ts
          (infer_st_subst st'))) /\
     (!l ienv pes t1 t2 st st'.
        (infer_pes l ienv pes t1 t2 st = (M_success one,st')) ==>
        (?ts. pure_add_constraints (infer_st_subst st) ts
          (infer_st_subst st'))) /\
     (!l ienv funs st st' ts'.
        (infer_funs l ienv funs st = (M_success ts',st')) ==>
        (?ts. pure_add_constraints (infer_st_subst st) ts
          (infer_st_subst st')))`)
  CHEAT_TAC;;

let pure_add_constraints_wfs = cake_theorem "pure_add_constraints_wfs"
  (fun () ->
    `!s1 ts s2.
      pure_add_constraints s1 ts s2 /\
      t_wfs s1 ==>
      t_wfs s2`)
  CHEAT_TAC;;

(* ---------- The next unification variable is monotone non-decreasing ---------- *)

let infer_p_next_uvar_mono = cake_theorem "infer_p_next_uvar_mono"
  (fun () ->
    `(!l cenv p st t env st'.
        (infer_p l cenv p st = (M_success (t,env),st')) ==>
          infer_st_next_uvar
        st <= infer_st_next_uvar st') /\
     (!l cenv ps st ts env st'.
        (infer_ps l cenv ps st = (M_success (ts,env),st')) ==>
          infer_st_next_uvar
        st <= infer_st_next_uvar st')`)
  CHEAT_TAC;;

let infer_e_next_uvar_mono = cake_theorem "infer_e_next_uvar_mono"
  (fun () ->
    `(!l ienv e st st' t.
        (infer_e l ienv e st = (M_success t,st')) ==>
          infer_st_next_uvar
        st <= infer_st_next_uvar st') /\
     (!l ienv es st st' ts.
        (infer_es l ienv es st = (M_success ts,st')) ==>
          infer_st_next_uvar
        st <= infer_st_next_uvar st') /\
     (!l ienv pes t1 t2 st st'.
        (infer_pes l ienv pes t1 t2 st = (M_success one,st')) ==>
          infer_st_next_uvar
        st <= infer_st_next_uvar st') /\
     (!l ienv funs st st' ts.
        (infer_funs l ienv funs st = (M_success ts,st')) ==>
          infer_st_next_uvar
        st <= infer_st_next_uvar st')`)
  CHEAT_TAC;;

(* ---------- The inferencer builds well-formed substitutions ---------- *)

let infer_p_wfs = cake_theorem "infer_p_wfs"
  (fun () ->
    `(!l cenv p st t env st'.
        t_wfs (infer_st_subst st) /\
        (infer_p l cenv p st = (M_success (t,env),st')) ==>
        t_wfs (infer_st_subst st')) /\
     (!l cenv ps st ts env st'.
        t_wfs (infer_st_subst st) /\
        (infer_ps l cenv ps st = (M_success (ts,env),st')) ==>
       t_wfs (infer_st_subst st'))`)
  CHEAT_TAC;;

let infer_e_wfs = cake_theorem "infer_e_wfs"
  (fun () ->
    `(!l ienv e st st' t.
        infer_e l ienv e st = (M_success t,st') /\
        t_wfs (infer_st_subst st) ==>
        t_wfs (infer_st_subst st')) /\
     (!l ienv es st st' ts.
        infer_es l ienv es st = (M_success ts,st') /\
        t_wfs (infer_st_subst st) ==>
        t_wfs (infer_st_subst st')) /\
     (!l ienv pes t1 t2 st st'.
        infer_pes l ienv pes t1 t2 st = (M_success one,st') /\
        t_wfs (infer_st_subst st) ==>
        t_wfs (infer_st_subst st')) /\
     (!l ienv funs st st' ts'.
        infer_funs l ienv funs st = (M_success ts',st') /\
        t_wfs (infer_st_subst st) ==>
        t_wfs (infer_st_subst st'))`)
  CHEAT_TAC;;

(* ---------- The invariants of the inferencer ---------- *)

let check_t_more = cake_theorem "check_t_more"
  (fun () ->
    `(!t tvs. check_t tvs {} t ==> (!uvs. check_t tvs uvs t)) /\
     (!ts tvs. EVERY (check_t tvs {}) ts ==> (!uvs. EVERY
       (check_t tvs uvs) ts))`)
  CHEAT_TAC;;

let check_t_more2 = cake_theorem "check_t_more2"
  (fun () ->
    `(!t tvs uvs. check_t tvs uvs t ==> (!tvs'. check_t (tvs' + tvs) uvs
  t)) /\
     (!ts tvs uvs. EVERY (check_t tvs uvs) ts ==> (!tvs'. EVERY
       (check_t (tvs' + tvs) uvs) ts))`)
  CHEAT_TAC;;

let check_t_more3 = cake_theorem "check_t_more3"
  (fun () ->
    `(!t uvs tvs. check_t tvs (count uvs) t ==> (!uvs'. check_t tvs
  (count (uvs + uvs')) t)) /\
     (!ts uvs tvs. EVERY (check_t tvs (count uvs)) ts ==> (!uvs'.
       EVERY (check_t tvs (count (uvs + uvs'))) ts))`)
  CHEAT_TAC;;

let check_t_more4 = cake_theorem "check_t_more4"
  (fun () ->
    `(!t uvs tvs. check_t tvs (count uvs) t ==> (!uvs'. uvs <= uvs' ==>
  check_t tvs (count uvs') t)) /\
     (!ts uvs tvs. EVERY (check_t tvs (count uvs)) ts ==> (!uvs'.
       uvs <= uvs' ==> EVERY (check_t tvs (count uvs')) ts))`)
  CHEAT_TAC;;

let check_t_more5 = cake_theorem "check_t_more5"
  (fun () ->
    `(!t uvs tvs. check_t tvs uvs t ==> (!uvs'. uvs SUBSET uvs' ==>
  check_t tvs uvs' t)) /\
     (!ts uvs tvs. EVERY (check_t tvs uvs) ts ==> (!uvs'. uvs
       SUBSET uvs' ==> EVERY (check_t tvs uvs') ts))`)
  CHEAT_TAC;;

let check_t_t_vars = cake_theorem "check_t_t_vars"
  (fun () ->
    `!tvs uvs t.
      check_t tvs uvs t ==> t_vars t SUBSET uvs`)
  CHEAT_TAC;;

let check_s_more = cake_theorem "check_s_more[local]"
  (fun () ->
    `!s tvs uvs. check_s tvs (count uvs) s ==> check_s tvs (count (uvs
  + 1)) s`)
  CHEAT_TAC;;

let check_s_more2 = cake_theorem "check_s_more2"
  (fun () ->
    `!s uvs. check_s tvs (count uvs) s ==> (!uvs'. uvs <= uvs' ==>
  check_s tvs (count uvs') s)`)
  CHEAT_TAC;;

let check_s_more3 = cake_theorem "check_s_more3"
  (fun () ->
    `!s uvs. check_s tvs uvs s ==> (!uvs'. uvs SUBSET uvs' ==> check_s
  tvs uvs' s)`)
  CHEAT_TAC;;

let check_s_more5 = cake_theorem "check_s_more5"
  (fun () ->
    `!s uvs tvs uvs'. check_s tvs uvs s /\ uvs SUBSET uvs' ==> check_s
  tvs uvs' s`)
  CHEAT_TAC;;

let check_t_deBruijn_inc2 = cake_theorem "check_t_deBruijn_inc2"
  (fun () ->
    `!inc t s. check_t tvs s t ==> check_t (inc + tvs) s
  (infer_deBruijn_inc inc t)`)
  CHEAT_TAC;;

let check_t_deBruijn_inc = cake_theorem "check_t_deBruijn_inc"
  (fun () ->
    `!inc t. check_t 0 UNIV t ==> (infer_deBruijn_inc inc t = t)`)
  CHEAT_TAC;;

let infer_deBruijn_subst_twice =
  cake_theorem "infer_deBruijn_subst_twice"
  (fun () ->
    `(!t.
      check_t (LENGTH subst2) uvs t ==>
      (infer_deBruijn_subst subst1 (infer_deBruijn_subst subst2 t)
        =
       infer_deBruijn_subst (MAP (infer_deBruijn_subst subst1)
         subst2) t)) /\
     (!ts.
      EVERY (check_t (LENGTH subst2) uvs) ts ==>
      MAP ((infer_deBruijn_subst subst1) o (infer_deBruijn_subst
        subst2)) ts =
      MAP (infer_deBruijn_subst (MAP (infer_deBruijn_subst
        subst1) subst2)) ts)`)
  CHEAT_TAC;;

let check_t_subst = cake_theorem "check_t_subst"
  (fun () ->
    `!tvs (tvs':num->bool) t s.
      t_wfs s /\
      check_t tvs {} t ==>
      (t = (t_walkstar (infer_deBruijn_inc tvs o_f s) t))`)
  CHEAT_TAC;;

let t_vwalk_check = cake_theorem "t_vwalk_check"
  (fun () ->
    `!s. t_wfs s ==>
      (!n tvs uvs t.
        n IN uvs /\
        check_s tvs uvs s ==>
        check_t tvs uvs (t_vwalk s n))`)
  CHEAT_TAC;;

let t_walkstar_check' = cake_theorem "t_walkstar_check'[local]"
  (fun () ->
    `!s. t_wfs s ==>
     (!t tvs uvs.
       check_s tvs (uvs UNION FDOM s) s /\
       check_t tvs (uvs UNION FDOM s) t ==>
       check_t tvs uvs (t_walkstar s t))`)
  CHEAT_TAC;;

let t_walkstar_check = cake_theorem "t_walkstar_check"
  (fun () ->
    `!s t tvs uvs.
        t_wfs s /\
        check_s tvs (uvs UNION FDOM s) s /\
        check_t tvs (uvs UNION FDOM s) t ==>
        check_t tvs uvs (t_walkstar s t)`)
  CHEAT_TAC;;

let t_walkstar_uncheck_lem =
  cake_theorem "t_walkstar_uncheck_lem[local]"
  (fun () ->
    `!s. t_wfs s ==>
       (!t max_tvs uvs.
       check_t max_tvs uvs (t_walkstar s t) ==>
       check_t max_tvs (uvs UNION FDOM s) t)`)
  CHEAT_TAC;;

let t_walkstar_uncheck = cake_theorem "t_walkstar_uncheck"
  (fun () ->
    `!s t max_tvs uvs.
      check_t max_tvs uvs (t_walkstar s t) /\
      t_wfs s ==>
      check_t max_tvs (uvs UNION FDOM s) t`)
  CHEAT_TAC;;

let t_unify_check_s_help = cake_theorem "t_unify_check_s_help[local]"
  (fun () ->
    `(!s t1 t2. t_wfs s ==>
       (!tvs uvs s'.
              check_s tvs uvs s /\
              check_t tvs uvs t1 /\
              check_t tvs uvs t2 /\
              (t_unify s t1 t2 = SOME s') ==>
              check_s tvs uvs s')) /\
     (!s ts1 ts2. t_wfs s ==>
       (!tvs uvs s'.
              check_s tvs uvs s /\
              EVERY (check_t tvs uvs) ts1 /\
              EVERY (check_t tvs uvs) ts2 /\
              (ts_unify s ts1 ts2 = SOME s') ==>
              check_s tvs uvs s'))`)
  CHEAT_TAC;;

let check_t_walkstar = cake_theorem "check_t_walkstar"
  (fun () ->
    `(!t tvs s.
        t_wfs s /\
        check_t tvs (FDOM s) t /\
        (!uv. uv IN FDOM s ==> check_t tvs {} (t_walkstar s
          (Infer_Tuvar uv))) ==>
        check_t tvs {} (t_walkstar s t)) /\
     (!ts tvs s.
        t_wfs s /\
        EVERY (check_t tvs (FDOM s)) ts /\
        (!uv. uv IN FDOM s ==> check_t tvs {} (t_walkstar s
          (Infer_Tuvar uv))) ==>
        EVERY (check_t tvs {} o t_walkstar s) ts)`)
  CHEAT_TAC;;

let t_walkstar_no_vars = cake_theorem "t_walkstar_no_vars[local]"
  (fun () ->
    `!tvs uvs t s.
     t_wfs s /\
     uvs = {} /\
     check_t tvs uvs t ==>
     t_walkstar s t = t`)
  CHEAT_TAC;;

let inferProps_t_walkstar_no_vars = cake_theorem "t_walkstar_no_vars"
  (fun () ->
    `!tvs t s.
      t_wfs s /\
      check_t tvs {} t ==>
      t_walkstar s t = t`)
  CHEAT_TAC;;

let t_unify_check_s = cake_theorem "t_unify_check_s"
  (fun () ->
    `!s1 tvs uvs t1 t2 s2.
      t_unify s1 t1 t2 = SOME s2 /\
      t_wfs s1 /\
      check_s tvs uvs s1 /\
      check_t tvs uvs t1 /\
      check_t tvs uvs t2 ==>
      check_s tvs uvs s2`)
  CHEAT_TAC;;

let pure_add_constraints_check_s =
  cake_theorem "pure_add_constraints_check_s"
  (fun () ->
    `!s1 tvs uvs ts s2.
      pure_add_constraints s1 ts s2 /\
      t_wfs s1 /\
      EVERY (\(t1,t2). check_t tvs (count uvs) t1 /\ check_t tvs
        (count uvs) t2) ts /\
      check_s tvs (count uvs) s1 ==>
      check_s tvs (count uvs) s2`)
  CHEAT_TAC;;

let infer_p_check_t = cake_theorem "infer_p_check_t"
  (fun () ->
    `(!l cenv p st t env st'.
        (infer_p l cenv p st = (M_success (t,env),st')) ==>
        EVERY (\(x,t). check_t 0 (count (infer_st_next_uvar st'))
          t) env /\
        check_t 0 (count (infer_st_next_uvar st')) t) /\
     (!l cenv ps st ts env st'.
        (infer_ps l cenv ps st = (M_success (ts,env),st')) ==>
        EVERY (\(x,t). check_t 0 (count (infer_st_next_uvar st'))
          t) env /\
        EVERY (check_t 0 (count (infer_st_next_uvar st'))) ts)`)
  CHEAT_TAC;;

let check_infer_type_subst =
  cake_theorem "check_infer_type_subst[local]"
  (fun () ->
    `(!t tvs uvs.
     check_freevars 0 tvs t ==>
     check_t 0 (count (LENGTH tvs + uvs)) (infer_type_subst (ZIP
       tvs (MAP (\n. Infer_Tuvar (uvs + n)) (COUNT_LIST (LENGTH tvs))))
       t)) /\
     (!ts tvs uvs.
     EVERY (check_freevars 0 tvs) ts ==>
     EVERY (\t. check_t 0 (count (LENGTH tvs + uvs))
       (infer_type_subst (ZIP tvs (MAP (\n. Infer_Tuvar (uvs + n))
       (COUNT_LIST (LENGTH tvs)))) t)) ts)`)
  CHEAT_TAC;;

(* moved this one around a bit *)
let infer_type_subst_empty_check =
  cake_theorem "infer_type_subst_empty_check"
  (fun () ->
    `(!t.
     check_freevars 0 [] t ==>
     check_t 0 {} (infer_type_subst [] t)) /\
     (!ts.
     EVERY (check_freevars 0 []) ts ==>
     EVERY (check_t 0 {}) (MAP (infer_type_subst []) ts))`)
  CHEAT_TAC;;

let type_name_check_subst_thm = cake_theorem "type_name_check_subst_thm"
  (fun () ->
    `(!t l err tenvT fvs (st:'a) r st'.
       type_name_check_subst l err tenvT fvs t st = (M_success
         r,st') ==>
       check_freevars_ast fvs t /\ check_type_names tenvT t /\
       r = type_name_subst tenvT t) /\
     (!ts l err tenvT fvs (st:'a) rs st'.
       type_name_check_subst_list l err tenvT fvs ts st =
         (M_success rs,st') ==>
       EVERY (check_freevars_ast fvs) ts /\ EVERY (check_type_names
         tenvT) ts /\
       rs = MAP (type_name_subst tenvT) ts)`)
  CHEAT_TAC;;

let type_name_check_subst_comp_thm =
  cake_theorem "type_name_check_subst_comp_thm"
  (fun () ->
    `(!t l err tenvT fvs (st:'a) r.
       check_freevars_ast fvs t /\ check_type_names tenvT t ==>
       type_name_check_subst l err tenvT fvs t st =
         (M_success (type_name_subst tenvT t),st)) /\
     (!ts l err tenvT fvs (st:'a) rs st'.
       EVERY (check_freevars_ast fvs) ts /\ EVERY (check_type_names
         tenvT) ts ==>
       type_name_check_subst_list l err tenvT fvs ts st =
         (M_success (MAP (type_name_subst tenvT) ts),st))`)
  CHEAT_TAC;;

let infer_p_check_s = cake_theorem "infer_p_check_s"
  (fun () ->
    `(!l ienv p st t env st' tvs.
      infer_p l ienv p st = (M_success (t,env),st') /\
      t_wfs (infer_st_subst st) /\
      tenv_ctor_ok (inf_env_inf_c ienv) /\
      tenv_abbrev_ok (inf_env_inf_t ienv) /\
      check_s tvs (count (infer_st_next_uvar st)) (infer_st_subst
        st) ==>
      check_s tvs (count (infer_st_next_uvar st')) (infer_st_subst
        st')) /\
     (!l ienv ps st ts env st' tvs.
      infer_ps l ienv ps st = (M_success (ts,env),st') /\
      t_wfs (infer_st_subst st) /\
      tenv_ctor_ok (inf_env_inf_c ienv) /\
      tenv_abbrev_ok (inf_env_inf_t ienv) /\
      check_s tvs (count (infer_st_next_uvar st)) (infer_st_subst
        st) ==>
      check_s tvs (count (infer_st_next_uvar st'))
        (infer_st_subst st'))`)
  CHEAT_TAC;;

let check_env_more = cake_theorem "check_env_more"
  (fun () ->
    `!uvs e.
      nsAll (\x (tvs,t). check_t tvs (count uvs) t) e ==>
      (!uvs'. uvs <= uvs' ==> nsAll (\x (tvs,t). check_t tvs
        (count uvs') t) e)`)
  CHEAT_TAC;;

let check_env_letrec_lem = cake_theorem "check_env_letrec_lem"
  (fun () ->
    `!uvs funs uvs'.
      ((funs = []) \/ (uvs' + LENGTH funs <= uvs)) ==>
      nsAll (\x (tvs,t). check_t tvs (count uvs) t)
        (alist_to_ns (MAP2 (\(f,x,e) uvar. (f,0,uvar)) funs (MAP
          (\n. Infer_Tuvar (n + uvs')) (COUNT_LIST (LENGTH funs)))))`)
  CHEAT_TAC;;

let check_t_infer_db_subst =
  cake_theorem "check_t_infer_db_subst[local]"
  (fun () ->
    `(!t uvs tvs.
      check_t 0 (count (uvs + tvs)) (infer_deBruijn_subst (MAP (\n.
        Infer_Tuvar (uvs + n)) (COUNT_LIST tvs)) t) =
      check_t tvs (count (uvs + tvs)) t) /\
     (!ts uvs tvs.
      EVERY (check_t 0 (count (uvs + tvs)) o infer_deBruijn_subst
        (MAP (\n. Infer_Tuvar (uvs + n)) (COUNT_LIST tvs))) ts =
      EVERY (check_t tvs (count (uvs + tvs))) ts)`)
  CHEAT_TAC;;

let check_t_infer_db_subst2 = cake_theorem "check_t_infer_db_subst2"
  (fun () ->
    `(!t tvs1 tvs2.
       check_t tvs1 (count tvs2) (infer_deBruijn_subst (MAP (\n.
         Infer_Tuvar n) (COUNT_LIST tvs2)) t) =
       check_t (tvs1 + tvs2) (count tvs2) t) /\
     (!ts tvs1 tvs2.
       EVERY (check_t tvs1 (count tvs2) o infer_deBruijn_subst (MAP
         (\n. Infer_Tuvar n) (COUNT_LIST tvs2))) ts =
       EVERY (check_t (tvs1 + tvs2) (count tvs2)) ts)`)
  CHEAT_TAC;;

let infer_e_check_t = cake_theorem "infer_e_check_t"
  (fun () ->
    `(!l ienv e st st' t.
        infer_e l ienv e st = (M_success t,st') /\
        ienv_val_ok (count (infer_st_next_uvar st)) (inf_env_inf_v
          ienv) ==>
       check_t 0 (count (infer_st_next_uvar st')) t) /\
     (!l ienv es st st' ts.
        infer_es l ienv es st = (M_success ts,st') /\
        ienv_val_ok (count (infer_st_next_uvar st)) (inf_env_inf_v
          ienv) ==>
        EVERY (check_t 0 (count (infer_st_next_uvar st'))) ts) /\
     (!l ienv pes t1 t2 st st'.
        infer_pes l ienv pes t1 t2 st = (M_success one,st') /\
       ienv_val_ok (count (infer_st_next_uvar st)) (inf_env_inf_v
         ienv) ==>
        T) /\
     (!l ienv funs st st' ts'.
        infer_funs l ienv funs st = (M_success ts',st') /\
        ienv_val_ok (count (infer_st_next_uvar st)) (inf_env_inf_v
          ienv) ==>
        EVERY (check_t 0 (count (infer_st_next_uvar st'))) ts')`)
  CHEAT_TAC;;

(* HOL4 inferPropsScript.sml:1836-1837: ML code, not ported *)

(* HOL4 inferPropsScript.sml:1839-1840: ML code, not ported *)

let constrain_op_wfs = cake_theorem "constrain_op_wfs"
  (fun () ->
    `!l tvs op ts t st st'.
      constrain_op l op ts st = (M_success t,st') /\
      t_wfs (infer_st_subst st) ==>
      t_wfs (infer_st_subst st')`)
  CHEAT_TAC;;

let constrain_op_check_t = cake_theorem "constrain_op_check_t"
  (fun () ->
    `!l tvs op ts t st st'.
      constrain_op l op ts st = (M_success t,st') /\
      EVERY (check_t 0 (count (infer_st_next_uvar st))) ts ==>
      check_t 0 (count (infer_st_next_uvar st')) t`)
  CHEAT_TAC;;

let constrain_op_check_s = cake_theorem "constrain_op_check_s"
  (fun () ->
    `!l tvs op ts t st st'.
      constrain_op l op ts st = (M_success t,st') /\
      t_wfs (infer_st_subst st) /\
      EVERY (check_t 0 (count (infer_st_next_uvar st))) ts /\
      check_s tvs (count (infer_st_next_uvar st)) (infer_st_subst
        st) ==>
      check_s tvs (count (infer_st_next_uvar st'))
        (infer_st_subst st')`)
  CHEAT_TAC;;

let ienv_ok_def = cake_define
  `ienv_ok uvars ienv <=>
     ienv_val_ok uvars (inf_env_inf_v ienv) /\
     tenv_ctor_ok (inf_env_inf_c ienv) /\
     tenv_abbrev_ok (inf_env_inf_t ienv)`;;

let ienv_ok_more = cake_theorem "ienv_ok_more"
  (fun () ->
    `!uv uv' ienv. ienv_ok (count uv) ienv /\ uv <= uv' ==> ienv_ok
  (count uv') ienv`)
  CHEAT_TAC;;

let infer_e_check_s = cake_theorem "infer_e_check_s"
  (fun () ->
    `(!l ienv e st st' t tvs.
        infer_e l ienv e st = (M_success t,st') /\
        t_wfs (infer_st_subst st) /\
        ienv_ok (count (infer_st_next_uvar st)) ienv /\
        check_s tvs (count (infer_st_next_uvar st)) (infer_st_subst
          st) ==>
        check_s tvs (count (infer_st_next_uvar st'))
          (infer_st_subst st')) /\
     (!l ienv es st st' ts tvs.
        infer_es l ienv es st = (M_success ts,st') /\
        t_wfs (infer_st_subst st) /\
        ienv_ok (count (infer_st_next_uvar st)) ienv /\
        check_s tvs (count (infer_st_next_uvar st)) (infer_st_subst
          st) ==>
        check_s tvs (count (infer_st_next_uvar st'))
          (infer_st_subst st')) /\
     (!l ienv pes t1 t2 st st' tvs.
        infer_pes l ienv pes t1 t2 st = (M_success one,st') /\
        t_wfs (infer_st_subst st) /\
        ienv_ok (count (infer_st_next_uvar st)) ienv /\
        check_t 0 (count (infer_st_next_uvar st)) t1 /\
        check_t 0 (count (infer_st_next_uvar st)) t2 /\
        check_s tvs (count (infer_st_next_uvar st)) (infer_st_subst
          st) ==>
        check_s tvs (count (infer_st_next_uvar st'))
          (infer_st_subst st')) /\
     (!l ienv funs st st' ts' tvs.
        infer_funs l ienv funs st = (M_success ts',st') /\
        t_wfs (infer_st_subst st) /\
        ienv_ok (count (infer_st_next_uvar st)) ienv /\
        check_s tvs (count (infer_st_next_uvar st)) (infer_st_subst
          st) ==>
        check_s tvs (count (infer_st_next_uvar st'))
          (infer_st_subst st'))`)
  CHEAT_TAC;;

let generalise_complete_lemma =
  cake_theorem "generalise_complete_lemma[local]"
  (fun () ->
    `!tvs ts.
     (!uv. uv IN FDOM (FEMPTY |++ ts) ==> (?tv. FAPPLY (FEMPTY |++
       ts) uv = tv /\ tv < tvs)) ==>
     (!uv. uv IN FDOM (FEMPTY |++ MAP (\(uv,tv).
       (uv,Infer_Tvar_db tv)) ts) ==> (?tv. FAPPLY (FEMPTY |++ MAP
       (\(uv,tv). (uv,Infer_Tvar_db tv)) ts) uv = Infer_Tvar_db tv /\
       tv < tvs))`)
  CHEAT_TAC;;

let generalise_complete_lemma2 =
  cake_theorem "generalise_complete_lemma2[local]"
  (fun () ->
    `!s ts.
     t_wfs s /\
     ALL_DISTINCT (MAP FST ts) /\
     EVERY (\t. t = Infer_Tapp [] TC_unit \/ (?tvs. t =
       Infer_Tvar_db tvs)) (MAP SND ts) /\
     DISJOINT (FDOM s) (FDOM (FEMPTY |++ ts)) ==>
     pure_add_constraints s (MAP (\(uv,t). (Infer_Tuvar uv,t))
       ts) (s |++ ts)`)
  CHEAT_TAC;;

let infer_subst_var_def = cake_define
  `infer_subst_var s t =
        match t with
          Infer_Tuvar n ->
     (match FLOOKUP s n with NONE -> Infer_Tuvar n | SOME tv ->
       Infer_Tvar_db tv)
        | t -> t`;;

let generalise_complete_lemma4 =
  cake_theorem "generalise_complete_lemma4[local]"
  (fun () ->
    `!s. t_wfs s ==>
     (!t s'. t_wfs (s |++ MAP (\(uv,tv). (uv,Infer_Tvar_db tv)) s')
       /\
            ALL_DISTINCT (MAP FST s') /\
            DISJOINT (FDOM s) (FDOM (FEMPTY |++ MAP (\(uv,tv).
              (uv,Infer_Tvar_db tv)) s')) ==>
            infer_subst_var (FEMPTY |++ s') (t_vwalk s t) =
              t_vwalk (s |++ MAP (\(uv,tv). (uv,Infer_Tvar_db tv)) s')
              t)`)
  CHEAT_TAC;;

let generalise_complete_lemma5 =
  cake_theorem "generalise_complete_lemma5[local]"
  (fun () ->
    `!s. t_wfs s ==>
     (!t s'. t_wfs (s |++ MAP (\(uv,tv). (uv,Infer_Tvar_db tv)) s')
       ==>
            ALL_DISTINCT (MAP FST s') /\
            DISJOINT (FDOM s) (FDOM (FEMPTY |++ MAP (\(uv,tv).
              (uv,Infer_Tvar_db tv)) s')) ==>
            infer_subst (FEMPTY |++ s') (t_walkstar s t) =
              t_walkstar (s |++ MAP (\(uv,tv). (uv,Infer_Tvar_db tv))
              s') t)`)
  CHEAT_TAC;;

let inferProps_fst_lem = cake_theorem "fst_lem[local]"
  (fun () ->
    `FST = (\(x,y). x)`)
  CHEAT_TAC;;

(* HOL4 inferPropsScript.sml:2462-2468: a theorem that HOL4 states as
   the value of an ML expression: t_ind *)

(* Rename (type_system) type identifiers with a function *)
let _ = size_thms "t";;
(* HOL4 inferPropsScript.sml:2474-2481: the tactic that proves the
   termination *)
let ts_tid_rename_def = cake_define_wf
  `MEASURE (\(_2,y). t_size y)`
  `ts_tid_rename f t =
        match t with
          Tapp ts tn -> Tapp (MAP (ts_tid_rename f) ts) (f tn)
        | t -> t`;;

(* HOL4 inferPropsScript.sml:2483: ML code, not ported *)

let ts_tid_rename_I = cake_theorem "ts_tid_rename_I[simp]"
  (fun () ->
    `ts_tid_rename I = I`)
  CHEAT_TAC;;

(* All type ids in a type belonging to a set *)
let _ = size_thms "t";;
(* HOL4 inferPropsScript.sml:2497-2504: the tactic that proves the
   termination *)
let set_tids_def = cake_define_wf
  `MEASURE t_size`
  `set_tids x1 =
        match x1 with
          Tapp ts tn -> tn INSERT (BIGUNION (set_of_list (MAP
            set_tids ts)))
        | _3 -> {}`;;

(* HOL4 inferPropsScript.sml:2506: ML code, not ported *)

let set_tids_ts_tid_rename = cake_theorem "set_tids_ts_tid_rename"
  (fun () ->
    `!f t. set_tids (ts_tid_rename f t) = IMAGE f (set_tids t)`)
  CHEAT_TAC;;

let set_tids_subset_def = cake_define
  `set_tids_subset tids t <=> set_tids t SUBSET tids`;;

let set_tids_subset_type_subst =
  cake_theorem "set_tids_subset_type_subst"
  (fun () ->
    `!s t tids.
     FEVERY (set_tids_subset tids o SND) s /\
     set_tids_subset tids t ==>
     set_tids_subset tids (type_subst s t)`)
  CHEAT_TAC;;

let _ = size_thms "t";;
(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 inferPropsScript.sml:2547-2553: the tactic that proves the
   termination *)
let unconvert_t_def = cake_define_list_try (fun () ->
  `MEASURE t_size`)
  [`unconvert_t (Tvar_db n) = Infer_Tvar_db n`;
   `unconvert_t (Tapp ts tc) = Infer_Tapp (MAP unconvert_t ts) tc`;
   `unconvert_t (Tvar v) = Infer_Tuvar ARB`];;

(* HOL4 inferPropsScript.sml:2555: ML code, not ported *)

(* Properties about inferencer type identifiers *)
let _ = size_thms "infer_t";;
(* HOL4 inferPropsScript.sml:2561-2568: the tactic that proves the
   termination *)
let inf_set_tids_def = cake_define_wf
  `MEASURE infer_t_size`
  `inf_set_tids x1 =
        match x1 with
          Infer_Tapp ts tn -> tn INSERT (BIGUNION (set_of_list (MAP
            inf_set_tids ts)))
        | _4 -> {}`;;

let inf_set_tids_subset_def = cake_define
  `inf_set_tids_subset tids t <=> inf_set_tids t SUBSET tids`;;

(* HOL4 inferPropsScript.sml:2574-2575: a theorem that HOL4 states as
   the value of an ML expression: typeSystem_t_ind *)

let inf_set_tids_infer_type_subst_SUBSET =
  cake_theorem "inf_set_tids_infer_type_subst_SUBSET"
  (fun () ->
    `!subst (t:t).
       inf_set_tids (infer_type_subst subst t) SUBSET
       set_tids t UNION BIGUNION (IMAGE inf_set_tids (set_of_list
         (MAP SND subst)))`)
  CHEAT_TAC;;

let inf_set_tids_infer_deBruijn_subst_SUBSET =
  cake_theorem "inf_set_tids_infer_deBruijn_subst_SUBSET"
  (fun () ->
    `!subst t.
       inf_set_tids (infer_deBruijn_subst subst t) SUBSET
       inf_set_tids t UNION BIGUNION (IMAGE inf_set_tids
         (set_of_list subst))`)
  CHEAT_TAC;;

let inf_set_tids_unconvert = cake_theorem "inf_set_tids_unconvert"
  (fun () ->
    `!t. inf_set_tids (unconvert_t t) = set_tids t`)
  CHEAT_TAC;;

(* all the tids used in a tenv *)
let inf_set_tids_ienv_def = cake_define
  `inf_set_tids_ienv tids (ienv:inf_env) <=>
   nsAll (\i (ls,t). inf_set_tids_subset tids (unconvert_t t))
     (inf_env_inf_t ienv) /\
   nsAll (\i (ls,ts,tid). EVERY (\t. inf_set_tids_subset tids
     (unconvert_t t)) ts /\ tid IN tids) (inf_env_inf_c ienv) /\
   nsAll (\i (n,t). inf_set_tids_subset tids t) (inf_env_inf_v
     ienv)`;;

let inf_set_tids_subst_def = cake_define
  `inf_set_tids_subst tids subst <=>
   (!t. t IN FRANGE subst ==> inf_set_tids_subset tids t)`;;

let prim_tids_def = cake_define
  `prim_tids contain' tids <=>
     EVERY (\x. x IN tids <=> contain') (Tlist_num :: Tbool_num ::
       prim_type_nums)`;;

let set_tids_subset_type_name_subst =
  cake_theorem "set_tids_subset_type_name_subst"
  (fun () ->
    `!tenvt t tids.
     prim_tids T tids /\
     nsAll (\i (ls,t). set_tids_subset tids t) tenvt ==>
     set_tids_subset tids (type_name_subst tenvt t)`)
  CHEAT_TAC;;

let generalise_complete = cake_theorem "generalise_complete"
  (fun () ->
    `!n s l tvs s' ts next_uvar.
      generalise_list 0 n FEMPTY (MAP (t_walkstar s) l) =
        (tvs,s',ts) /\
      t_wfs s /\
      check_s 0 (count next_uvar) s /\
      EVERY (\t. check_t 0 (count next_uvar) t) l ==>
      (?ec1 last_sub.
        (ts = MAP (t_walkstar last_sub) l) /\
        t_wfs last_sub /\
        sub_completion (tvs + n) next_uvar s ec1 last_sub /\
        (TC_unit IN tids /\ inf_set_tids_subst tids s ==>
          inf_set_tids_subst tids last_sub))`)
  CHEAT_TAC;;

let init_infer_state_wfs = cake_theorem "init_infer_state_wfs[local]"
  (fun () ->
    `t_wfs (infer_st_subst (init_infer_state st)) /\
      check_s 0 {} (infer_st_subst (init_infer_state st))`)
  CHEAT_TAC;;

let init_infer_state_next_uvar =
  cake_theorem "init_infer_state_next_uvar[simp]"
  (fun () ->
    `infer_st_next_uvar
        (init_infer_state st) = 0`)
  CHEAT_TAC;;

let init_infer_state_subst = cake_theorem "init_infer_state_subst[simp]"
  (fun () ->
    `infer_st_subst
        (init_infer_state st) = FEMPTY`)
  CHEAT_TAC;;

let t_wfs_FEMPTY = cake_theorem "t_wfs_FEMPTY[simp]"
  (fun () ->
    `t_wfs FEMPTY`)
  CHEAT_TAC;;

let t_wfs_init_infer_state = cake_theorem "t_wfs_init_infer_state[simp]"
  (fun () ->
    `t_wfs (infer_st_subst (init_infer_state s))`)
  CHEAT_TAC;;

(* HOL4 inferPropsScript.sml:2902-2940: a proof *)

let eta2_thm = cake_theorem "eta2_thm[local]"
  (fun () ->
    `(\x. f a b x) = f a b`)
  CHEAT_TAC;;

let check_env_letrec_lem2 = cake_theorem "check_env_letrec_lem2[local]"
  (fun () ->
    `!funs.
       nsAll (\x (tvs,t). check_t tvs (count (LENGTH funs)) t)
         (alist_to_ns (MAP2 (\(f,x,e) uvar. (f,0,uvar))
                         funs
                         (MAP (\n. Infer_Tuvar n) (COUNT_LIST
                           (LENGTH funs)))))`)
  CHEAT_TAC;;

let ienv_ok_extend_dec_ienv = cake_theorem "ienv_ok_extend_dec_ienv"
  (fun () ->
    `!e1 e2 n. ienv_ok n e1 /\ ienv_ok n e2 ==> ienv_ok n
  (extend_dec_ienv e1 e2)`)
  CHEAT_TAC;;

let infer_d_check = cake_theorem "infer_d_check"
  (fun () ->
    `(!d ienv st1 st2 ienv'.
      infer_d ienv d st1 = (M_success ienv',st2) /\
      ienv_ok {} ienv ==>
      ienv_ok {} ienv') /\
     (!ds ienv st1 st2 ienv'.
      infer_ds ienv ds st1 = (M_success ienv',st2) /\
      ienv_ok {} ienv ==>
      ienv_ok {} ienv')`)
  CHEAT_TAC;;

let infer_p_next_id_const = cake_theorem "infer_p_next_id_const"
  (fun () ->
    `(!l cenv p st t env st'.
        (infer_p l cenv p st = (M_success (t,env),st')) ==>
          infer_st_next_id
        st = infer_st_next_id st') /\
     (!l cenv ps st ts env st'.
        (infer_ps l cenv ps st = (M_success (ts,env),st')) ==>
          infer_st_next_id
        st = infer_st_next_id st')`)
  CHEAT_TAC;;

let infer_e_next_id_const = cake_theorem "infer_e_next_id_const"
  (fun () ->
    `(!l ienv e st st' t.
        (infer_e l ienv e st = (M_success t,st')) ==>
          infer_st_next_id
        st = infer_st_next_id st') /\
     (!l ienv es st st' ts.
        (infer_es l ienv es st = (M_success ts,st')) ==>
          infer_st_next_id
        st = infer_st_next_id st') /\
     (!l ienv pes t1 t2 st st'.
        (infer_pes l ienv pes t1 t2 st = (M_success one,st')) ==>
          infer_st_next_id
        st = infer_st_next_id st') /\
     (!l ienv funs st st' ts.
        (infer_funs l ienv funs st = (M_success ts,st')) ==>
          infer_st_next_id
        st = infer_st_next_id st')`)
  CHEAT_TAC;;

let infer_d_next_id_mono = cake_theorem "infer_d_next_id_mono"
  (fun () ->
    `(!d ienv st t st'.
      infer_d ienv d st = (M_success t,st') ==> infer_st_next_id
      st <= infer_st_next_id st') /\
     (!ds ienv st ts st'.
      (infer_ds ienv ds st = (M_success ts,st') ==>
        infer_st_next_id
      st <= infer_st_next_id st'))`)
  CHEAT_TAC;;

let count_list_one = cake_theorem "count_list_one[local]"
  (fun () ->
    `COUNT_LIST 1 = [0]`)
  CHEAT_TAC;;

let check_freevars_more_append =
  cake_theorem "check_freevars_more_append[local]"
  (fun () ->
    `(!t x fvs1 fvs2.
     check_freevars x fvs1 t ==>
     check_freevars x (fvs2 ++ fvs1) t /\
     check_freevars x (fvs1 ++ fvs2) t) /\
     (!ts x fvs1 fvs2.
     EVERY (check_freevars x fvs1) ts ==>
     EVERY (check_freevars x (fvs2 ++ fvs1)) ts /\
     EVERY (check_freevars x (fvs1 ++ fvs2)) ts)`)
  CHEAT_TAC;;

let check_freevars_more = cake_theorem "check_freevars_more"
  (fun () ->
    `!a b c. check_freevars a b c ==> (!b'. set_of_list b SUBSET
  set_of_list b' ==> check_freevars a b' c)`)
  CHEAT_TAC;;

let check_t_infer_type_subst_dbs =
  cake_theorem "check_t_infer_type_subst_dbs"
  (fun () ->
    `!m w t n u ls.
      check_freevars m w t /\
      m + LENGTH ls <= n /\
      (ls = [] ==> 0 < m) ==>
      check_t n u (infer_type_subst (ZIP ls (MAP Infer_Tvar_db
        (COUNT_LIST (LENGTH ls)))) t)`)
  CHEAT_TAC;;

let nub_eq_nil = cake_theorem "nub_eq_nil"
  (fun () ->
    `!ls. nub ls = [] <=> ls = []`)
  CHEAT_TAC;;

let ienv_ok_lift = cake_theorem "ienv_ok_lift"
  (fun () ->
    `!mn ienv n. ienv_ok n ienv ==> ienv_ok n (lift_ienv mn ienv)`)
  CHEAT_TAC;;

let sub_completion_wfs = cake_theorem "sub_completion_wfs"
  (fun () ->
    `!n uvars s1 ts s2.
      t_wfs s1 /\
      sub_completion n uvars s1 ts s2 ==>
      t_wfs s2`)
  CHEAT_TAC;;

let infer_deBruijn_subst_id = cake_theorem "infer_deBruijn_subst_id"
  (fun () ->
    `(!t. infer_deBruijn_subst [] t = t) /\
      (!ts. MAP (infer_deBruijn_subst []) ts = ts)`)
  CHEAT_TAC;;

let deBruijn_subst_nothing = cake_theorem "deBruijn_subst_nothing"
  (fun () ->
    `(!t.
     deBruijn_subst 0 [] t = t) /\
     (!ts.
     MAP (deBruijn_subst 0 []) ts = ts)`)
  CHEAT_TAC;;

let infer_deBruijn_subst_id2 = cake_theorem "infer_deBruijn_subst_id2"
  (fun () ->
    `(!t.
     check_t tvs {} t ==>
     infer_deBruijn_subst (GENLIST (Infer_Tvar_db) tvs) t = t) /\
     (!ts.
     EVERY (check_t tvs {}) ts ==>
     MAP (infer_deBruijn_subst (GENLIST (Infer_Tvar_db) tvs)) ts
       = ts)`)
  CHEAT_TAC;;

let check_t_infer_deBruijn_subst =
  cake_theorem "check_t_infer_deBruijn_subst"
  (fun () ->
    `!subst t tvs uvs.
       check_t (tvs + LENGTH subst) uvs t /\
       EVERY (check_t tvs uvs) subst ==>
       check_t tvs uvs (infer_deBruijn_subst subst t)`)
  CHEAT_TAC;;

let infer_deBruijn_subst_uncheck =
  cake_theorem "infer_deBruijn_subst_uncheck"
  (fun () ->
    `!s t max_tvs uvs.
      check_t max_tvs uvs (infer_deBruijn_subst s t) ==>
      check_t (max_tvs + LENGTH s) uvs t`)
  CHEAT_TAC;;

let db_subst_inc_id = cake_theorem "db_subst_inc_id"
  (fun () ->
    `!inst' t.
      infer_deBruijn_subst inst' (infer_deBruijn_inc (LENGTH
        inst') t) = t`)
  CHEAT_TAC;;

let t_walkstar_db_subst = cake_theorem "t_walkstar_db_subst"
  (fun () ->
    `!inst' t s.
      t_wfs s ==>
      t_walkstar s (infer_deBruijn_subst inst' t) =
      infer_deBruijn_subst (MAP (t_walkstar s) inst')
                 (t_walkstar (infer_deBruijn_inc (LENGTH inst')
                   o_f s) t)`)
  CHEAT_TAC;;

let generalise_subst_exist = cake_theorem "generalise_subst_exist"
  (fun () ->
    `(t_wfs s /\
     (!uv. uv IN FDOM s ==> check_t tvs {} (t_walkstar s
       (Infer_Tuvar uv)))) ==>
     (!t subst n smap a b t'.
     LENGTH subst = n /\
     FRANGE smap SUBSET count n /\
     (!x. MEM x subst ==> check_t tvs {} x) /\
     t_vars t SUBSET FDOM s /\
     check_t 0 (FDOM s) t /\
     (!x. x IN FDOM smap ==> EL (FAPPLY smap x) subst = t_walkstar
       s (Infer_Tuvar x)) /\
     generalise 0 n smap t = (a,b,t') ==>
     (?subst'.
     LENGTH subst' = a /\
     (!x. MEM x subst' ==> check_t tvs {} x) /\
     (!x. x IN FDOM b ==> EL (FAPPLY b x) (subst ++ subst') =
       t_walkstar s (Infer_Tuvar x)))) /\
     (!ts subst n smap a b ts'.
     LENGTH subst = n /\
     FRANGE smap SUBSET count n /\
     (!x. MEM x subst ==> check_t tvs {} x) /\
     EVERY (\t. t_vars t SUBSET FDOM s) ts /\
     EVERY (check_t 0 (FDOM s)) ts /\
     (!x. x IN FDOM smap ==> EL (FAPPLY smap x) subst = t_walkstar
       s (Infer_Tuvar x)) /\
     generalise_list 0 n smap ts = (a,b,ts') ==>
     (?subst'.
     LENGTH subst' = a /\
     (!x. MEM x subst' ==> check_t tvs {} x) /\
     (!x. x IN FDOM b ==> EL (FAPPLY b x) (subst ++ subst') =
       t_walkstar s (Infer_Tuvar x))))`)
  CHEAT_TAC;;

let infer_deBruijn_subst_infer_subst_walkstar =
  cake_theorem "infer_deBruijn_subst_infer_subst_walkstar"
  (fun () ->
    `!b subst n m.
     FRANGE b SUBSET count (LENGTH subst) /\
     t_wfs s ==>
     ((!t.
     (!x. x IN t_vars t ==> EL (FAPPLY b x) subst = t_walkstar s
       (Infer_Tuvar x)) /\
     check_t 0 m t /\
     t_vars t SUBSET FDOM b ==>
     infer_deBruijn_subst subst (infer_subst b t) =
     t_walkstar s t) /\
     (!ts.
     EVERY (\t. (!x. x IN t_vars t ==> EL (FAPPLY b x) subst =
       t_walkstar s (Infer_Tuvar x))) ts /\
     EVERY (check_t 0 m) ts /\
     EVERY (\t. t_vars t SUBSET FDOM b) ts ==>
     MAP ((infer_deBruijn_subst subst) o (infer_subst b)) ts =
     MAP (t_walkstar s) ts))`)
  CHEAT_TAC;;

let remap_tenv_def = cake_define
  `remap_tenv f tenv =
   mk_type_env (nsMap (\(n,t). (n,ts_tid_rename f t)) (type_env_v
     tenv)) (nsMap (\(ls,ts,tid). (ls,MAP (ts_tid_rename f) ts,f
     tid)) (type_env_c tenv)) (nsMap (\(ls,t). (ls,ts_tid_rename f
     t)) (type_env_t tenv))`;;

let remap_tenv_I = cake_theorem "remap_tenv_I[simp]"
  (fun () ->
    `remap_tenv I = I`)
  CHEAT_TAC;;

let t_vwalk_set_tids = cake_theorem "t_vwalk_set_tids"
  (fun () ->
    `!s. t_wfs s ==>
     (!v.
     inf_set_tids_subst tids s ==>
     inf_set_tids (t_vwalk s v) SUBSET tids)`)
  CHEAT_TAC;;

let t_walk_set_tids = cake_theorem "t_walk_set_tids"
  (fun () ->
    `!s t t'.
     t_wfs s /\
     inf_set_tids_subst tids s /\
     inf_set_tids_subset tids t /\
     t_walk s t = t' ==>
     inf_set_tids_subset tids t'`)
  CHEAT_TAC;;

let t_walkstar_set_tids = cake_theorem "t_walkstar_set_tids"
  (fun () ->
    `!s t t'.
     t_wfs s /\
     inf_set_tids_subst tids s /\
     inf_set_tids_subset tids t /\
     t_walkstar s t = t' ==>
     inf_set_tids_subset tids t'`)
  CHEAT_TAC;;

let t_unify_set_tids = cake_theorem "t_unify_set_tids"
  (fun () ->
    `(!s t1 t2. t_wfs s ==>
     (!s'.
     inf_set_tids_subst tids s /\
     inf_set_tids_subset tids t1 /\
     inf_set_tids_subset tids t2 /\
     t_unify s t1 t2 = SOME s' ==>
     inf_set_tids_subst tids s')) /\
     (!s ts1 ts2. t_wfs s ==>
     (!s'.
     inf_set_tids_subst tids s /\
     EVERY (inf_set_tids_subset tids) ts1 /\
     EVERY (inf_set_tids_subset tids) ts2 /\
     ts_unify s ts1 ts2 = SOME s' ==>
     inf_set_tids_subst tids s'))`)
  CHEAT_TAC;;

let pure_add_constraints_set_tids =
  cake_theorem "pure_add_constraints_set_tids"
  (fun () ->
    `!s1 ls s2.
     t_wfs s1 /\
     EVERY (inf_set_tids_subset tids) (MAP FST ls) /\
     EVERY (inf_set_tids_subset tids) (MAP SND ls) /\
     inf_set_tids_subst tids s1 /\
     pure_add_constraints s1 ls s2 ==>
     inf_set_tids_subst tids s2`)
  CHEAT_TAC;;

let hide_def = cake_define
  `inferProps_hide x = x`;;
hol4_overload "hide" "inferProps_hide";;

let infer_p_inf_set_tids = cake_theorem "infer_p_inf_set_tids"
  (fun () ->
    `(!l cenv p st t env st'.
     (infer_p l cenv p st = (M_success (t,env),st')) ==>
     prim_tids T tids /\ inf_set_tids_ienv tids cenv /\
     inf_set_tids_subst tids (infer_st_subst st) /\ t_wfs
       (infer_st_subst st) ==>
     inf_set_tids_subset tids t /\
     EVERY (inf_set_tids_subset tids o SND) env /\
     inf_set_tids_subst tids (infer_st_subst st')) /\
     (!l cenv ps st ts env st'.
     (infer_ps l cenv ps st = (M_success (ts,env),st')) ==>
     prim_tids T tids /\ inf_set_tids_ienv tids cenv /\
     inf_set_tids_subst tids (infer_st_subst st) /\ t_wfs
       (infer_st_subst st) ==>
     EVERY (inf_set_tids_subset tids) ts /\
     EVERY (inf_set_tids_subset tids o SND) env /\
     inf_set_tids_subst tids (infer_st_subst st'))`)
  CHEAT_TAC;;

let constrain_op_set_tids = cake_theorem "constrain_op_set_tids"
  (fun () ->
    `constrain_op l op ts st = (M_success t,st') /\
     EVERY (inf_set_tids_subset tids) ts /\
     inf_set_tids_subst tids (infer_st_subst st) /\
     t_wfs (infer_st_subst st) /\ prim_tids T tids ==>
     inf_set_tids_subset tids t /\ inf_set_tids_subst tids
       (infer_st_subst st')`)
  CHEAT_TAC;;

let infer_e_inf_set_tids = cake_theorem "infer_e_inf_set_tids"
  (fun () ->
    `(!l cenv p st t st'.
       (infer_e l cenv p st = (M_success t,st')) ==>
       prim_tids T tids /\ inf_set_tids_ienv tids cenv /\
       inf_set_tids_subst tids (infer_st_subst st) /\ t_wfs
         (infer_st_subst st) ==>
       inf_set_tids_subset tids t /\
       inf_set_tids_subst tids (infer_st_subst st')) /\
     (!l cenv ps st ts st'.
       (infer_es l cenv ps st = (M_success ts,st')) ==>
       prim_tids T tids /\ inf_set_tids_ienv tids cenv /\
       inf_set_tids_subst tids (infer_st_subst st) /\ t_wfs
         (infer_st_subst st) ==>
       EVERY (inf_set_tids_subset tids) ts /\
       inf_set_tids_subst tids (infer_st_subst st')) /\
     (!l cenv ps t1 t2 st st'.
       (infer_pes l cenv ps t1 t2 st = (M_success one,st')) ==>
       prim_tids T tids /\ inf_set_tids_ienv tids cenv /\
       inf_set_tids_subst tids (infer_st_subst st) /\
       inf_set_tids_subset tids t1 /\
       inf_set_tids_subset tids t2 /\ t_wfs (infer_st_subst st) ==>
       inf_set_tids_subst tids (infer_st_subst st')) /\
     (!l cenv funs st ts st'.
       (infer_funs l cenv funs st = (M_success ts,st')) ==>
       prim_tids T tids /\ inf_set_tids_ienv tids cenv /\
       inf_set_tids_subst tids (infer_st_subst st) /\ t_wfs
         (infer_st_subst st) ==>
       EVERY (inf_set_tids_subset tids) ts /\
       inf_set_tids_subst tids (infer_st_subst st'))`)
  CHEAT_TAC;;

let generalise_inf_set_tids = cake_theorem "generalise_inf_set_tids"
  (fun () ->
    `(!d a b c e f g. generalise a b c d = (e,f,g) ==>
                      inf_set_tids g = inf_set_tids d) /\
     (!d a b c e f g. generalise_list a b c d = (e,f,g) ==>
                      EVERY2 (inv_image (=) inf_set_tids) d g)`)
  CHEAT_TAC;;

let start_type_id_prim_tids_count =
  cake_theorem "start_type_id_prim_tids_count"
  (fun () ->
    `start_type_id <= n ==> prim_tids T (count n)`)
  CHEAT_TAC;;

let inf_set_tids_subst_FEMPTY =
  cake_theorem "inf_set_tids_subst_FEMPTY[simp]"
  (fun () ->
    `inf_set_tids_subst tids FEMPTY`)
  CHEAT_TAC;;

let build_ctor_tenv_FOLDR = cake_theorem "build_ctor_tenv_FOLDR"
  (fun () ->
    `!tenvT tds ids.
       LENGTH tds = LENGTH ids ==>
       build_ctor_tenv tenvT tds ids =
         ITLIST (hol4_C nsAppend)
         (MAP (alist_to_ns o REVERSE)
            (MAP2 (\(tvs,tn,ctors) id'. (MAP (\(cn,ts). (cn,tvs,MAP
              (type_name_subst tenvT) ts,id')) ctors))
                tds ids)) (alist_to_ns [])`)
  CHEAT_TAC;;

let build_ctor_tenv_FOLDL = cake_theorem "build_ctor_tenv_FOLDL"
  (fun () ->
    `!tenvT tds ids.
       LENGTH tds = LENGTH ids ==>
       build_ctor_tenv tenvT tds ids =
         FOLDL nsAppend (alist_to_ns [])
         (REVERSE
         (MAP (alist_to_ns o REVERSE)
            (MAP2 (\(tvs,tn,ctors) id'. (MAP (\(cn,ts). (cn,tvs,MAP
              (type_name_subst tenvT) ts,id')) ctors))
                tds ids)))`)
  CHEAT_TAC;;

let nsMap_FOLDL_nsAppend = cake_theorem "nsMap_FOLDL_nsAppend"
  (fun () ->
    `!ls ns. nsMap f (FOLDL nsAppend ns ls) =
     FOLDL nsAppend (nsMap f ns) (MAP (nsMap f) ls)`)
  CHEAT_TAC;;

let nsAll_FOLDL_nsAppend = cake_theorem "nsAll_FOLDL_nsAppend"
  (fun () ->
    `!ls ns.
     nsAll P ns /\ EVERY (nsAll P) ls ==> nsAll P (FOLDL nsAppend
       ns ls)`)
  CHEAT_TAC;;

let infer_d_inf_set_tids = cake_theorem "infer_d_inf_set_tids"
  (fun () ->
    `(!d ienv st ienv' st'.
       infer_d ienv d st = (M_success ienv',st') /\
       start_type_id <= infer_st_next_id st /\
       inf_set_tids_ienv (count (infer_st_next_id st)) ienv ==>
       inf_set_tids_ienv (count (infer_st_next_id st')) ienv') /\
     (!ds ienv st ienv' st'.
       infer_ds ienv ds st = (M_success ienv',st') /\
       start_type_id <= infer_st_next_id st /\
       inf_set_tids_ienv (count (infer_st_next_id st)) ienv ==>
       inf_set_tids_ienv (count (infer_st_next_id st')) ienv')`)
  CHEAT_TAC;;

let infer_d_wfs = cake_theorem "infer_d_wfs"
  (fun () ->
    `(!d ienv st ienv' st'.
       infer_d ienv d st = (M_success ienv',st') /\
       t_wfs (infer_st_subst st) ==>
       t_wfs (infer_st_subst st')) /\
     (!ds ienv st ienv' st'.
       infer_ds ienv ds st = (M_success ienv',st') /\
       t_wfs (infer_st_subst st) ==>
       t_wfs (infer_st_subst st'))`)
  CHEAT_TAC;;

cake_hide [];;
