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

(* ---------- Facts about deBruijn increment ---------- *)

(* ---------- Type substitution ---------- *)

(* HOL4 inferPropsScript.sml:157: ML code, not ported *)

(* ---------- Dealing with the monad ---------- *)

(* TODO: update *)

(* HOL4 inferPropsScript.sml:502-507: the ML values that the
   definitions below antiquote *)

(* HOL4 inferPropsScript.sml:509-511: ML code, not ported *)

(* HOL4 inferPropsScript.sml:513-519: ML code, not ported *)

(* HOL4 inferPropsScript.sml:521-523: ML code, not ported *)

(* HOL4 inferPropsScript.sml:539-550: the ML values that the
   definitions below antiquote *)

(* HOL4 inferPropsScript.sml:565-567: ML code, not ported *)

(* HOL4 inferPropsScript.sml:724-734: ML code, not ported *)

(* ---------- Simple structural properties ---------- *)

(* ---------- Dealing with the constraint set ---------- *)

(* ---------- The next unification variable is monotone non-decreasing ---------- *)

(* ---------- The inferencer builds well-formed substitutions ---------- *)

(* ---------- The invariants of the inferencer ---------- *)

(* moved this one around a bit *)

(* HOL4 inferPropsScript.sml:1836-1837: ML code, not ported *)

(* HOL4 inferPropsScript.sml:1839-1840: ML code, not ported *)

let ienv_ok_def = cake_define
  `ienv_ok uvars ienv <=>
     ienv_val_ok uvars (inf_env_inf_v ienv) /\
     tenv_ctor_ok (inf_env_inf_c ienv) /\
     tenv_abbrev_ok (inf_env_inf_t ienv)`;;

let infer_subst_var_def = cake_define
  `infer_subst_var s t =
        match t with
          Infer_Tuvar n ->
     (match FLOOKUP s n with NONE -> Infer_Tuvar n | SOME tv ->
       Infer_Tvar_db tv)
        | t -> t`;;

(* Rename (type_system) type identifiers with a function *)
let _ = size_thms "t";;
(* HOL4 inferPropsScript.sml:2474-2481: the tactic that proves the
   termination *)
let ts_tid_rename_def = cake_define_wf
  `MEASURE (\(_1,y). t_size y)`
  `ts_tid_rename f t =
        match t with
          Tapp ts tn -> Tapp (MAP (ts_tid_rename f) ts) (f tn)
        | t -> t`;;

(* HOL4 inferPropsScript.sml:2483: ML code, not ported *)

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
        | _2 -> {}`;;

(* HOL4 inferPropsScript.sml:2506: ML code, not ported *)

let set_tids_subset_def = cake_define
  `set_tids_subset tids t <=> set_tids t SUBSET tids`;;

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
        | _3 -> {}`;;

let inf_set_tids_subset_def = cake_define
  `inf_set_tids_subset tids t <=> inf_set_tids t SUBSET tids`;;

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

(* HOL4 inferPropsScript.sml:2902-2940: a proof *)

let remap_tenv_def = cake_define
  `remap_tenv f tenv =
   mk_type_env (nsMap (\(n,t). (n,ts_tid_rename f t)) (type_env_v
     tenv)) (nsMap (\(ls,ts,tid). (ls,MAP (ts_tid_rename f) ts,f
     tid)) (type_env_c tenv)) (nsMap (\(ls,t). (ls,ts_tid_rename f
     t)) (type_env_t tenv))`;;

let hide_def = cake_define
  `inferProps_hide x = x`;;
hol4_overload "hide" "inferProps_hide";;
