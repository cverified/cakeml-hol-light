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

(* HOL4 weakeningScript.sml:29-37: code that the source has in a
   comment *)

(* HOL4 weakeningScript.sml:159-201: code that the source has in a
   comment *)

let weak_def = cake_define
  `weak tenv' tenv <=> type_env_t
     tenv' = type_env_t tenv /\ weak_tenv tenv' tenv`;;

let weakCT_def = cake_define
  `weakCT cenv_impl cenv_spec <=> cenv_spec SUBMAP cenv_impl`;;

(* HOL4 weakeningScript.sml:577-648: code that the source has in a
   comment *)

(* HOL4 weakeningScript.sml:729-877: code that the source has in a
   comment *)

(* HOL4 weakeningScript.sml:879-913: code that the source has in a
   comment *)
