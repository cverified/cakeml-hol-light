(* ======================================================== *)
(*  std_prelude: ported from HOL4's
    translator/std_preludeScript.sml
    A definition theory, with 1 definition and 6 theorems.  Needed
    by 11 files of the port.  *)
(* ======================================================== *)

(*
  Translations of various useful HOL functions and datatypes, to serve as a
  starting point for further translations.
*)

needs "semantics/ast.ml";;
needs "semantics/evaluate.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "translator/ml_translator.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "std_prelude"
  ["ast"; "evaluate"; "ml_prog"; "ml_translator"; "semanticPrimitives"];;
(* HOL4 ancestors outside the port: While *)


(* type registration *)

(* HOL4 std_preludeScript.sml:14: ML code, not ported *)

(* HOL4 std_preludeScript.sml:16-21: ML code, not ported *)

(* pair *)

(* HOL4 std_preludeScript.sml:25-28: ML code, not ported *)

(* combin *)

(* HOL4 std_preludeScript.sml:32-40: ML code, not ported *)

(* arithmetic *)

let EXP_AUX_def,EXP_AUX_ind = define_guess
  `EXP_AUX m n k = if n = 0 then k else EXP_AUX m (n - (1:num)) (m *
  (k:num))`;;

(* HOL4 std_preludeScript.sml:48-53: a theorem that HOL4 states as the value
   of an ML expression: EXP_AUX_THM *)

(* HOL4 std_preludeScript.sml:55-56: ML code, not ported *)

(* HOL4 std_preludeScript.sml:58-59: ML code, not ported *)

(* HOL4 std_preludeScript.sml:61-65: the ML values that the definitions
   below antiquote *)

(* HOL4 std_preludeScript.sml:67: ML code, not ported *)

(* HOL4 std_preludeScript.sml:69: the ML values that the definitions below
   antiquote *)

(* while, owhile and least *)

(* [local] *)
let IS_SOME_OWHILE_THM = prove
 (`!g f x. (IS_SOME (OWHILE g f x)) =
             (?n. ~(g (ITER n f x)) /\ (!m. m < n ==> g (ITER m f x)))`,
  CHEAT_TAC);;

let WHILE_ind = prove
 (`!P. (!p g x. (p x ==> P p g (g x)) ==> P p g x) ==>
        (!p g x. IS_SOME (OWHILE p g x) ==> P p g x)`,
  CHEAT_TAC);;

let OWHILE_ind = WHILE_ind;;

(* HOL4 std_preludeScript.sml:104: ML code, not ported *)

(* HOL4 std_preludeScript.sml:106-108: ML code, not ported *)

let SUC_LEMMA = prove
 (`SUC = (\x. x + 1)`,
  CHEAT_TAC);;

(* [local] *)
let LEAST_LEMMA = prove
 (`(minimal) P = WHILE (\x. ~(P x)) (\x. x + 1) 0`,
  CHEAT_TAC);;

(* HOL4 std_preludeScript.sml:122: ML code, not ported *)

(* [local] *)
let FUNPOW_LEMMA = prove
 (`!n m. ITER n (\x. x + 1) m = n + m`,
  CHEAT_TAC);;

(* HOL4 std_preludeScript.sml:130-135: a theorem that HOL4 states as the
   value of an ML expression: least_side_thm *)

(* app_list *)

(* HOL4 std_preludeScript.sml:139-141: ML code, not ported *)

(* HOL4 std_preludeScript.sml:143: ML code, not ported *)

(* HOL4 std_preludeScript.sml:145: ML code, not ported *)

(* HOL4 std_preludeScript.sml:147: ML code, not ported *)

(* and the interface *)
let _ = unhide_overloads ();;
