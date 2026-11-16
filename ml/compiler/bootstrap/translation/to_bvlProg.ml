(* ======================================================== *)
(*  to_bvlProg: ported from HOL4's
    compiler/bootstrap/translation/to_bvlProgScript.sml
    A definition theory, with no definitions and 9 theorems.  Needed
    by to_bviProg.ml.  *)
(* ======================================================== *)

(*
  Translate the backend phase from closLang to BVL.
*)

needs "compiler/backend/backend.ml";;
needs "compiler/bootstrap/translation/to_closProg.ml";;
needs "translator/ml_translator.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "to_bvlProg"
  ["backend"; "ml_translator"; "to_closProg"];;

(* HOL4 to_bvlProgScript.sml:10: ML code, not ported *)

(* HOL4 to_bvlProgScript.sml:14: ML code, not ported *)

(* HOL4 to_bvlProgScript.sml:16: ML code, not ported *)

(* ------------------------------------------------------------------------- *)
(* Setup                                                                     *)
(* ------------------------------------------------------------------------- *)

(* HOL4 to_bvlProgScript.sml:22-32: ML code, not ported *)

(* HOL4 to_bvlProgScript.sml:34-35: ML code, not ported *)

(* NOT_NIL_AND_LEMMA[local] *)
let to_bvlProg_NOT_NIL_AND_LEMMA = prove
 (`(~(b = []) /\ x) = if b = [] then F else x`,
  CHEAT_TAC);;

(* HOL4 to_bvlProgScript.sml:43: ML code, not ported *)

(* HOL4 to_bvlProgScript.sml:45-58: ML code, not ported *)
                (* TODO: This ss messes up defs containing if-then-else
                with constant branches
                |> SIMP_RULE bool_ss [IN_INSERT,NOT_IN_EMPTY]*)
(* HOL4 to_bvlProgScript.sml:62-63: ML code, not ported *)

(* HOL4 to_bvlProgScript.sml:65: ML code, not ported *)

(* HOL4 to_bvlProgScript.sml:67: ML code, not ported *)

(* ------------------------------------------------------------------------- *)
(* clos_to_bvl                                                               *)
(* ------------------------------------------------------------------------- *)

(* HOL4 to_bvlProgScript.sml:73-76: ML code, not ported *)

(* HOL4 to_bvlProgScript.sml:78: ML code, not ported *)

(* [local] *)
let bvl_jump_jumplist_ind = prove
 (`bvl_jump_jumplist_ind`,
  CHEAT_TAC);;

(* HOL4 to_bvlProgScript.sml:94: ML code, not ported *)

(* HOL4 to_bvlProgScript.sml:96-111: a theorem that HOL4 states as the value
   of an ML expression: bvl_jump_jumplist_side *)

(* HOL4 to_bvlProgScript.sml:113-114: ML code, not ported *)

(* HOL4 to_bvlProgScript.sml:116-119: ML code, not ported *)

(* HOL4 to_bvlProgScript.sml:121: ML code, not ported *)

(* HOL4 to_bvlProgScript.sml:123-130: a theorem that HOL4 states as the
   value of an ML expression: clos_to_bvl_recc_lets_side *)

(* HOL4 to_bvlProgScript.sml:132-150: a theorem that HOL4 states as the
   value of an ML expression: clos_to_bvl_compile_exps_side *)

(* HOL4 to_bvlProgScript.sml:152: ML code, not ported *)

(* HOL4 to_bvlProgScript.sml:154-155: ML code, not ported *)

(* HOL4 to_bvlProgScript.sml:157: ML code, not ported *)

(* N.B.
 * Do not remove this! prove_EvalPatRel depends on it (though it should be
 * expanded there, not added to the simpset).
 *)
let to_bvlProg_same_type_def = same_type_def;;
add_simp to_bvlProg_same_type_def;;

(* HOL4 to_bvlProgScript.sml:166-170: a theorem that HOL4 states as the
   value of an ML expression: clos_to_bvl_compile_side *)

(* HOL4 to_bvlProgScript.sml:172-173: ML code, not ported *)

(* ------------------------------------------------------------------------- *)
(* bvl_const                                                                 *)
(* ------------------------------------------------------------------------- *)

(* HOL4 to_bvlProgScript.sml:179-182: ML code, not ported *)
(* HOL4 to_bvlProgScript.sml:183: code that the source has in a comment *)
(* HOL4 to_bvlProgScript.sml:184: ML code, not ported *)

let bvl_const_smartop2_size = prove
 (`bvl_const_smartop2_side v = T`,
  CHEAT_TAC);;

(* HOL4 to_bvlProgScript.sml:195: ML code, not ported *)

(* HOL4 to_bvlProgScript.sml:197-201: ML code, not ported *)

(* HOL4 to_bvlProgScript.sml:203-212: a theorem that HOL4 states as the
   value of an ML expression: bvl_const_compile_side *)

(* HOL4 to_bvlProgScript.sml:214: ML code, not ported *)

(* ------------------------------------------------------------------------- *)
(* bvl_handle                                                                *)
(* ------------------------------------------------------------------------- *)

(* HOL4 to_bvlProgScript.sml:220-221: ML code, not ported *)

(* HOL4 to_bvlProgScript.sml:223: ML code, not ported *)

(* HOL4 to_bvlProgScript.sml:225-236: a theorem that HOL4 states as the
   value of an ML expression: bvl_handle_compile_side *)

(* HOL4 to_bvlProgScript.sml:238: ML code, not ported *)

(* HOL4 to_bvlProgScript.sml:240-244: a theorem that HOL4 states as the
   value of an ML expression: bvl_handle_compile_exp_side *)

(* ------------------------------------------------------------------------- *)
(* bvl_inline                                                                *)
(* ------------------------------------------------------------------------- *)

(* HOL4 to_bvlProgScript.sml:250: ML code, not ported *)

(* HOL4 to_bvlProgScript.sml:252-265: a theorem that HOL4 states as the
   value of an ML expression: bvl_inline_tick_inline_side *)

(* HOL4 to_bvlProgScript.sml:267: ML code, not ported *)

(* [local] *)
let bvl_inline_is_small_aux_ind = prove
 (`bvl_inline_is_small_aux_ind`,
  CHEAT_TAC);;

(* HOL4 to_bvlProgScript.sml:282: ML code, not ported *)

(* HOL4 to_bvlProgScript.sml:284: ML code, not ported *)

(* HOL4 to_bvlProgScript.sml:286-296: a theorem that HOL4 states as the
   value of an ML expression: bvl_inline_tick_inline_all_side *)

(* HOL4 to_bvlProgScript.sml:298: ML code, not ported *)

let let_op_SING_NOT_NIL = prove
 (`~(clos_letop_let_op [x] = [])`,
  CHEAT_TAC);;
add_simp let_op_SING_NOT_NIL;;

(* HOL4 to_bvlProgScript.sml:307-311: a theorem that HOL4 states as the
   value of an ML expression: bvl_inline_let_op_side *)

(* HOL4 to_bvlProgScript.sml:313: ML code, not ported *)

(* HOL4 to_bvlProgScript.sml:315-324: a theorem that HOL4 states as the
   value of an ML expression: bvl_inline_remove_ticks_side *)

(* HOL4 to_bvlProgScript.sml:326: ML code, not ported *)

(* HOL4 to_bvlProgScript.sml:328-336: a theorem that HOL4 states as the
   value of an ML expression: bvl_inline_compile_prog_side *)

(* HOL4 to_bvlProgScript.sml:338-346: a theorem that HOL4 states as the
   value of an ML expression: bvl_inline_compile_inc_side *)

(* HOL4 to_bvlProgScript.sml:348: ML code, not ported *)

(* ------------------------------------------------------------------------- *)

(* HOL4 to_bvlProgScript.sml:352-353: ML code, not ported *)

(* and the interface *)
let _ = unhide_overloads ();;
