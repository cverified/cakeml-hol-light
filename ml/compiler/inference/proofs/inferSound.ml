(* ======================================================== *)
(*  inferSound: ported from HOL4's
    compiler/inference/proofs/inferSoundScript.sml
    A proof theory, with 1 definition and 11 theorems.  Needed by
    compilerProof.ml.  *)
(* ======================================================== *)

(*
  Proves soundness of the type inferencer: any type assignment
  produced by the type inferencer is a valid type for the program.
*)

needs "compiler/inference/infer.ml";;
needs "compiler/inference/inferProps.ml";;
needs "compiler/inference/infer_t.ml";;
needs "compiler/inference/proofs/envRel.ml";;
needs "compiler/inference/proofs/infer_eComplete.ml";;
needs "compiler/inference/proofs/infer_eSound.ml";;
needs "compiler/inference/proofs/type_eDeterm.ml";;
needs "compiler/inference/unify.ml";;
needs "semantics/ast.ml";;
needs "semantics/proofs/namespaceProps.ml";;
needs "semantics/proofs/typeSysProps.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "semantics/typeSystem.ml";;
needs "translator/monadic/monad_base/ml_monadBase.ml";;

(* the theories whose names the Ancestors blocks of the source
   bring, which are the ones that its statements read: the
   overloads of every other theory come out of the interface
   while this file loads *)
let _ = hol4_ancestors "inferSound"
  ["ast"; "envRel"; "infer"; "inferProps"; "infer_eComplete";
   "infer_eSound"; "infer_t"; "namespaceProps"; "semanticPrimitives";
   "typeSysProps"; "typeSystem"; "type_eDeterm"; "unify"];;

(* [local] *)
let letrec_lemma2 = prove
 (`!funs_ts l l' s s'.
   (!t1 t2. t_walkstar s t1 = t_walkstar s t2 ==> t_walkstar s' t1 =
     t_walkstar s' t2) /\
   (LENGTH funs_ts = LENGTH l) /\
   (LENGTH funs_ts = LENGTH l') /\
   MAP (\n. t_walkstar s (Infer_Tuvar n)) l' = MAP (t_walkstar s)
     funs_ts ==>
   (
   MAP2 (\(f,x,e) t. (f,t)) l (MAP (\n. convert_t (t_walkstar s'
     (Infer_Tuvar n))) l') =
   MAP2 (\(x,y,z) t. (x,convert_t (t_walkstar s' t))) l funs_ts)`,
  CHEAT_TAC);;

(* sub_completion_empty[local] *)
let inferSound_sub_completion_empty = prove
 (`!m n s s'. sub_completion m n s [] s' <=> count n SUBSET FDOM s' /\
  (!uv. uv IN FDOM s' ==> check_t m {} (t_walkstar s' (Infer_Tuvar
  uv))) /\ s = s'`,
  CHEAT_TAC);;

(* [local] *)
let generalise_none = prove
 (`(!t s' t' x.
    check_t 0 x t /\
    generalise 0 0 FEMPTY t = (0,s',t') ==>
    s' = FEMPTY /\
    check_t 0 {} t) /\
   (!ts s' ts' x.
    EVERY (check_t 0 x) ts /\
    generalise_list 0 0 FEMPTY ts = (0,s',ts') ==>
    s' = FEMPTY /\
    EVERY (check_t 0 {}) ts)`,
  CHEAT_TAC);;

(* [local] *)
let lookup_var_empty = prove
 (`lookup_var x (bind_tvar tvs typeSystem_Empty) tenv =
   lookup_var x typeSystem_Empty tenv`,
  CHEAT_TAC);;

(* TODO: This should be generalized eventually *)
(* env_rel_complete_bind *)
let inferSound_env_rel_complete_bind = prove
 (`env_rel_complete FEMPTY ienv tenv typeSystem_Empty ==>
   env_rel_complete FEMPTY ienv tenv (bind_tvar tvs
     typeSystem_Empty)`,
  CHEAT_TAC);;

(* TODO: The generated set of type identifiers (tids)
  must be related to st2.next_id in some way
  The current relation might be wrong *)

(* the set of ids n1 .... n2-1 *)
let set_ids_def = new_definition
  `set_ids n1 (n2:num) = {m | n1 <= m /\ m < n2}`;;

(* [local] *)
let set_ids_eq = prove
 (`set_ids n1 n2 =
   set_of_list (GENLIST (\x. x + n1) (n2 - n1))`,
  CHEAT_TAC);;

(* [simp] *)
let set_ids_same = prove
 (`set_ids x x = {}`,
  CHEAT_TAC);;

let set_ids_eq_union = prove
 (`x <= y /\ y <= z ==> set_ids x z = set_ids x y UNION set_ids y z`,
  CHEAT_TAC);;

let set_ids_eq_union_eq = prove
 (`x <= y /\ y <= z /\ s = set_ids y z ==> set_ids x z = set_ids x y
  UNION s`,
  CHEAT_TAC);;

(* HOL4 inferSoundScript.sml:133-134: ML code, not ported *)

let infer_d_sound = prove
 (`(!d tenv ienv st1 st2 ienv'.
    infer_d ienv d st1 = (M_success ienv',st2) /\
    envRel_env_rel tenv ienv /\
    start_type_id <= infer_st_next_id st1 ==>
    type_d T tenv d (set_ids (infer_st_next_id st1) (infer_st_next_id
      st2)) (ienv_to_tenv ienv')) /\
   (!ds tenv ienv st1 st2 ienv'.
    infer_ds ienv ds st1 = (M_success ienv',st2) /\
    envRel_env_rel tenv ienv /\
    start_type_id <= infer_st_next_id st1 ==>
    type_ds T tenv ds (set_ids (infer_st_next_id st1)
      (infer_st_next_id st2)) (ienv_to_tenv ienv'))`,
  CHEAT_TAC);;

let db_subst_infer_subst_swap2 = prove
 (`(!t s tvs uvar n.
    t_wfs s /\
    check_t tvs {} t ==>
    (convert_t
      (t_walkstar s
         (infer_deBruijn_subst
            (MAP (\n. Infer_Tuvar n) (COUNT_LIST tvs))
            t)) =
     deBruijn_subst 0
      (MAP (convert_t o t_walkstar s)
         (MAP (\n. Infer_Tuvar n) (COUNT_LIST tvs)))
      (convert_t t))) /\
   (!ts s tvs uvar n.
    t_wfs s /\
    EVERY (\t. check_t tvs {} t) ts ==>
    (MAP (convert_t o
         t_walkstar s o
         infer_deBruijn_subst (MAP (\n. Infer_Tuvar n) (COUNT_LIST
           tvs)))
        ts =
     MAP (deBruijn_subst 0 (MAP (convert_t o t_walkstar s) (MAP (\n.
       Infer_Tuvar n) (COUNT_LIST tvs))) o
         convert_t)
        ts))`,
  CHEAT_TAC);;

(* HOL4 inferSoundScript.sml:754-1137: code that the source has in a
   comment *)

(* and the overloads that this file cannot see are back in the
   interface *)
let _ = unhide_overloads ();;
