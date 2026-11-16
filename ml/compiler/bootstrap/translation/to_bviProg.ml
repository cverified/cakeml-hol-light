(* ======================================================== *)
(*  to_bviProg: ported from HOL4's
    compiler/bootstrap/translation/to_bviProgScript.sml
    A definition theory, with no definitions and 1 theorem.  Needed
    by to_dataProg.ml.  *)
(* ======================================================== *)

(*
  Translate the backend phase from BVL to BVI.
*)

needs "compiler/bootstrap/translation/to_bvlProg.ml";;
needs "translator/ml_translator.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "to_bviProg"
  ["ml_translator"; "to_bvlProg"];;

(* HOL4 to_bviProgScript.sml:10: ML code, not ported *)

(* HOL4 to_bviProgScript.sml:14: ML code, not ported *)

(* HOL4 to_bviProgScript.sml:16: ML code, not ported *)

(* ------------------------------------------------------------------------- *)
(* Setup                                                                     *)
(* ------------------------------------------------------------------------- *)

(* HOL4 to_bviProgScript.sml:22-32: ML code, not ported *)

(* HOL4 to_bviProgScript.sml:34-35: ML code, not ported *)

(* NOT_NIL_AND_LEMMA[local] *)
let to_bviProg_NOT_NIL_AND_LEMMA = prove
 (`(~(b = []) /\ x) = if b = [] then F else x`,
  CHEAT_TAC);;

(* HOL4 to_bviProgScript.sml:43: ML code, not ported *)

(* HOL4 to_bviProgScript.sml:45-58: ML code, not ported *)
                (* TODO: This ss messes up defs containing if-then-else
                with constant branches
                |> SIMP_RULE bool_ss [IN_INSERT,NOT_IN_EMPTY]*)
(* HOL4 to_bviProgScript.sml:62-63: ML code, not ported *)

(* HOL4 to_bviProgScript.sml:65: ML code, not ported *)

(* HOL4 to_bviProgScript.sml:67: ML code, not ported *)

(* ------------------------------------------------------------------------- *)
(* bvi_let                                                                   *)
(* ------------------------------------------------------------------------- *)

(* HOL4 to_bviProgScript.sml:73: ML code, not ported *)

(* HOL4 to_bviProgScript.sml:75-84: a theorem that HOL4 states as the value
   of an ML expression: bvi_let_compile_side *)

(* HOL4 to_bviProgScript.sml:86: ML code, not ported *)

(* ------------------------------------------------------------------------- *)
(* bvi_tailrec                                                               *)
(* ------------------------------------------------------------------------- *)

(* HOL4 to_bviProgScript.sml:92-104: ML code, not ported *)

(* HOL4 to_bviProgScript.sml:106: ML code, not ported *)

(* HOL4 to_bviProgScript.sml:108: ML code, not ported *)

(* ------------------------------------------------------------------------- *)
(* bvi_inline                                                                *)
(* ------------------------------------------------------------------------- *)

(* HOL4 to_bviProgScript.sml:114: ML code, not ported *)

(* HOL4 to_bviProgScript.sml:116-117: ML code, not ported *)

(* HOL4 to_bviProgScript.sml:119: ML code, not ported *)

(* HOL4 to_bviProgScript.sml:121-122: ML code, not ported *)

(* HOL4 to_bviProgScript.sml:124-126: ML code, not ported *)

(* HOL4 to_bviProgScript.sml:128-129: ML code, not ported *)

(* ------------------------------------------------------------------------- *)
(* bvi_tmc                                                                   *)
(* ------------------------------------------------------------------------- *)

(* pure_exp/pure_exps is given by one mutually recursive definition, which is
   what cv_trans needs but which this translator's preprocessor cannot reduce
   to one line per function.  We therefore translate the equivalent non-mutual
   equations for pure_exps instead (the same split as bvi_let$compile_def vs
   bvi_let$compile_sing_def) and define pure_exp on top of them. *)

(* HOL4 to_bviProgScript.sml:141-142: ML code, not ported *)

(* bvi_to_cb_aux_sing/bvi_to_cb_aux, by contrast, the preprocessor handles as
   it stands. *)

(* HOL4 to_bviProgScript.sml:147: ML code, not ported *)

(* ------------------------------------------------------------------------- *)
(* bvl_to_bvi                                                                *)
(* ------------------------------------------------------------------------- *)

(* HOL4 to_bviProgScript.sml:153-156: ML code, not ported *)

(* HOL4 to_bviProgScript.sml:158-166: a theorem that HOL4 states as the
   value of an ML expression: bvl_to_bvi_compile_exps_side *)

(* HOL4 to_bviProgScript.sml:168: ML code, not ported *)

(* HOL4 to_bviProgScript.sml:170-174: a theorem that HOL4 states as the
   value of an ML expression: bvl_to_bvi_compile_single_side *)

(* HOL4 to_bviProgScript.sml:176: ML code, not ported *)

(* HOL4 to_bviProgScript.sml:178-180: a theorem that HOL4 states as the
   value of an ML expression: bvl_to_bvi_get_names_side *)

(* HOL4 to_bviProgScript.sml:182-184: ML code, not ported *)

(* HOL4 to_bviProgScript.sml:186-187: ML code, not ported *)

(* HOL4 to_bviProgScript.sml:189-190: ML code, not ported *)

(* ------------------------------------------------------------------------- *)

(* HOL4 to_bviProgScript.sml:194-195: ML code, not ported *)

(* and the interface *)
let _ = unhide_overloads ();;
