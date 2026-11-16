(* ======================================================== *)
(*  MapProg: ported from HOL4's
    basis/MapProgScript.sml
    A definition theory, with 1 definition and 10 theorems.  Needed
    by SetProg.ml.  *)
(* ======================================================== *)

(*
  This module contains CakeML code implementing a functional map type
  using a self-balancing binary tree.
*)

needs "basis/ArrayProg.ml";;
needs "lib/balanced_map.ml";;
needs "lib/toto.ml";;
needs "misc/misc.ml";;
needs "translator/ml_translator.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "MapProg"
  ["ArrayProg"; "ml_prog"; "ml_translator"];;

(* HOL4 MapProgScript.sml:11: ML code, not ported *)

(* HOL4 MapProgScript.sml:13-15: ML code, not ported *)

(* HOL4 MapProgScript.sml:17-19: ML code, not ported *)

(* HOL4 MapProgScript.sml:21: ML code, not ported *)

(* HOL4 MapProgScript.sml:23-25: ML code, not ported *)

(* Helpers *)
(* HOL4 MapProgScript.sml:28-32: ML code, not ported *)

(* [local] *)
let deleteFindmax_side_thm = prove
 (`!m. ~(m = Tip) ==> deletefindmax_side m`,
  CHEAT_TAC);;
(* HOL4 MapProgScript.sml:44: ML code, not ported *)

(* HOL4 MapProgScript.sml:46: ML code, not ported *)

(* [local] *)
let deleteFindmin_side_thm = prove
 (`!m. ~(m = Tip) ==> deletefindmin_side m`,
  CHEAT_TAC);;
(* HOL4 MapProgScript.sml:58: ML code, not ported *)

(* HOL4 MapProgScript.sml:60: ML code, not ported *)

(* [local] *)
let glue_side_thm = prove
 (`!m n. glue_side m n`,
  CHEAT_TAC);;
(* HOL4 MapProgScript.sml:69: ML code, not ported *)

(* HOL4 MapProgScript.sml:71-90: ML code, not ported *)

(* Exported functions *)
(* HOL4 MapProgScript.sml:93-118: ML code, not ported *)

(* HOL4 MapProgScript.sml:120: ML code, not ported *)

(* HOL4 MapProgScript.sml:122: ML code, not ported *)

(* provides the Map.map name for the map type *)
(* HOL4 MapProgScript.sml:125-127: ML code, not ported *)

(* HOL4 MapProgScript.sml:129-174: ML code, not ported *)

(* HOL4 MapProgScript.sml:176: ML code, not ported *)

(* this is here so that the type name is accessible without the full name *)
(* HOL4 MapProgScript.sml:179-181: ML code, not ported *)

(* HOL4 MapProgScript.sml:183: ML code, not ported *)

(*----------------------------------------------------------------------*
   general tooling for adding mlmap support for fmaps
 *----------------------------------------------------------------------*)

let MapProg_FMAP_TYPE_def = new_definition
  `MapProg_FMAP_TYPE cmp a b f v =
     (?m. map_ok m /\ mlmap_to_fmap m = f /\ MAP_TYPE a b m v /\
         cmp_of m = cmp)`;;

(* [local] *)
let MAP_TYPE_empty_IMP_FMAP_TYPE = prove
 (`MAP_TYPE a b (mlmap_empty cmp) v /\ TotOrd cmp ==>
   MapProg_FMAP_TYPE cmp a b FEMPTY v`,
  CHEAT_TAC);;

(* [local] *)
let IMP_FMAP_TYPE_FLOOKUP = prove
 (`(Arrow (MAP_TYPE b a) (Arrow b (OPTION_TYPE a))) mlmap_lookup v ==>
   (Arrow (MapProg_FMAP_TYPE cmp b a) (Arrow b (OPTION_TYPE a))) FLOOKUP v`,
  CHEAT_TAC);;

(* [local] *)
let IMP_FMAP_TYPE_FUPDATE = prove
 (`(Arrow (MAP_TYPE b a) (Arrow (b:'a->semanticPrimitives_v->bool) (Arrow a
  (MAP_TYPE b a)))) mlmap_insert v ==>
   (Arrow (MapProg_FMAP_TYPE cmp b a) (Arrow b (Arrow a (MapProg_FMAP_TYPE
     cmp b a)))) fmap_update v`,
  CHEAT_TAC);;

(* [local] *)
let IMP_FMAP_TYPE_DOMSUB = prove
 (`(Arrow (MAP_TYPE b a) (Arrow (b:'a->semanticPrimitives_v->bool) (MAP_TYPE b
  a))) mlmap_delete v ==>
   (Arrow (MapProg_FMAP_TYPE cmp b a) (Arrow b (MapProg_FMAP_TYPE cmp b
     a))) (\\) v`,
  CHEAT_TAC);;

(* [local] *)
let IMP_FMAP_TYPE_FUNION = prove
 (`(Arrow (MAP_TYPE b a) (Arrow (MAP_TYPE b a) (MAP_TYPE b a))) mlmap_union v
  ==>
   (Arrow (MapProg_FMAP_TYPE cmp b a) (Arrow (MapProg_FMAP_TYPE cmp b a)
     (MapProg_FMAP_TYPE cmp b a))) FUNION v`,
  CHEAT_TAC);;

let IMP_FMAP_TYPE_ops = prove
 (`MAP_TYPE (key:'k->semanticPrimitives_v->bool)
  (a:'a->semanticPrimitives_v->bool) (mlmap_empty cmp) v /\ TotOrd cmp ==>
   MapProg_FMAP_TYPE cmp key a FEMPTY v /\
   ((Arrow (MAP_TYPE key a) (Arrow key (OPTION_TYPE a))) mlmap_lookup v1 ==>
    (Arrow (MapProg_FMAP_TYPE cmp key a) (Arrow key (OPTION_TYPE a)))
      FLOOKUP v1) /\
   ((Arrow (MAP_TYPE key a) (Arrow key (Arrow a (MAP_TYPE key a))))
     mlmap_insert v1 ==>
    (Arrow (MapProg_FMAP_TYPE cmp key a) (Arrow key (Arrow a
      (MapProg_FMAP_TYPE cmp key a)))) fmap_update v1) /\
   ((Arrow (MAP_TYPE key a) (Arrow key (MAP_TYPE key a))) mlmap_delete v1
     ==>
    (Arrow (MapProg_FMAP_TYPE cmp key a) (Arrow key (MapProg_FMAP_TYPE cmp
      key a))) (\\) v1) /\
   ((Arrow (MAP_TYPE key a) (Arrow (MAP_TYPE key a) (MAP_TYPE key a)))
     mlmap_union v1 ==>
    (Arrow (MapProg_FMAP_TYPE cmp key a) (Arrow (MapProg_FMAP_TYPE cmp key
      a) (MapProg_FMAP_TYPE cmp key a))) FUNION v1)`,
  CHEAT_TAC);;

(* HOL4 MapProgScript.sml:285-289: a theorem that HOL4 states as the value
   of an ML expression: mlmap_op_v_thms *)

(* and the interface *)
let _ = unhide_overloads ();;
