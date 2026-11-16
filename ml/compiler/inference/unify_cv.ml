(* ======================================================== *)
(*  unify_cv: ported from HOL4's
    compiler/inference/unify_cvScript.sml
    A definition theory, with no definitions and 15 theorems.
    Needed by backend_cv.ml and infer_cv.ml.  *)
(* ======================================================== *)

(*
  Translating unifyTheory to cv equations for use with cv_eval
*)

needs "basis/pure/basis_cv.ml";;
needs "compiler/inference/unify.ml";;
needs "lib/cv_std.ml";;
needs "lib/cv_type.ml";;
needs "lib/fmsp.ml";;
needs "lib/sptree.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "unify_cv"
  ["basis_cv"; "unify"];;

(* HOL4 unify_cvScript.sml:10: ML code, not ported *)

let tcvwalk_pre = prove
 (`!s t. cwfs s ==> tcvwalk_pre s t`,
  CHEAT_TAC);;

(* HOL4 unify_cvScript.sml:24: ML code, not ported *)

let tcwalk_pre = prove
 (`cwfs s ==> tcwalk_pre s t`,
  CHEAT_TAC);;

(* HOL4 unify_cvScript.sml:32: ML code, not ported *)

let tcocwl_pre = prove
 (`!s n wl. cwfs s ==> tcocwl_pre s n wl`,
  CHEAT_TAC);;

(* HOL4 unify_cvScript.sml:46: ML code, not ported *)

let tcwalkstar_p1_pre_thm = prove
 (`cwfs s ==> (tcwalkstar_p1_pre s its ks <=>
               (!v its' ks'. kcwalkstarwl_code s (F,its,ks) =
                            sum_INL (v,its',ks') ==>
                            (v ==> tcwalkstar_p2_pre s its' ks') /\
                            (~v ==> tcwalkstar_p1_pre s its' ks')))`,
  CHEAT_TAC);;

let tcwalkstar_p2_pre_thm = prove
 (`cwfs s ==> (tcwalkstar_p2_pre s its ks <=>
               (!v its' ks'. kcwalkstarwl_code s (T,its,ks) =
                            sum_INL (v,its',ks') ==>
                            (v ==> tcwalkstar_p2_pre s its' ks') /\
                            (~v ==> tcwalkstar_p1_pre s its' ks')))`,
  CHEAT_TAC);;

let tcwalkstar_pre = prove
 (`!s its ks. cwfs s ==>
              tcwalkstar_p1_pre s its ks /\ tcwalkstar_p2_pre s its ks`,
  CHEAT_TAC);;

(* HOL4 unify_cvScript.sml:90: a theorem that HOL4 states as the value of an
   ML expression: tcwalkstar_pre_def *)

(* HOL4 unify_cvScript.sml:92: ML code, not ported *)

let tcunify_pre_thm = prove
 (`cwfs s ==>
   (tcunify_pre s wl <=>
      (!s' wl'. cunify_code (s,wl) = sum_INL (s',wl') ==> tcunify_pre s'
        wl'))`,
  CHEAT_TAC);;

let tcunify_pre = prove
 (`!s wl. cwfs s ==> tcunify_pre s wl`,
  CHEAT_TAC);;

(* HOL4 unify_cvScript.sml:119: ML code, not ported *)

(* [cv_pre] *)
let cunify_pre = prove
 (`cunify_pre s t1 t2 <=> cwfs s`,
  CHEAT_TAC);;

(* HOL4 unify_cvScript.sml:127: the overload from_infer_t, which the port
   expands *)

let from_option_OPTION_MAP = prove
 (`from_option f (OPTION_MAP g x) = from_option (f o g) x`,
  CHEAT_TAC);;

(* [local] *)
let to_encode_infer_t_o_f = prove
 (`sp2fm (sptree_map encode_infer_t (fromAList (fmap_to_alist s))) =
   encode_infer_t o_f s`,
  CHEAT_TAC);;
add_simp to_encode_infer_t_o_f;;

let t_wfs_IMP_cwfs = prove
 (`t_wfs s ==> cwfs (fromAList (fmap_to_alist s))`,
  CHEAT_TAC);;

(* [cv_rep] *)
let cv_rep_t_unify = prove
 (`t_wfs s ==>
   from_option (from_fmap from_infer_t_infer_t_infer_t) (t_unify s t1 t2) =
   cv_cunify (from_fmap from_infer_t_infer_t_infer_t s)
     (from_infer_t_infer_t_infer_t t1) (from_infer_t_infer_t_infer_t t2)`,
  CHEAT_TAC);;

(* [cv_rep] *)
let cv_rep_t_walkstar = prove
 (`t_wfs s ==>
   from_infer_t_infer_t_infer_t (t_walkstar s t) =
   cv_cwalkstar (from_fmap from_infer_t_infer_t_infer_t s)
     (from_infer_t_infer_t_infer_t t)`,
  CHEAT_TAC);;

(* and the interface *)
let _ = unhide_overloads ();;
