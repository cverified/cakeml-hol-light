(* ======================================================== *)
(*  setModel: ported from HOL4's
    candle/set-theory/setModelScript.sml
    A definition theory, with 2 definitions and 4 theorems.  Needed
    by holLightConsistency.ml and x64BootstrapProof.ml.  *)
(* ======================================================== *)

(*
  An example universe satisfying is_set_theory and (assuming the
  existence of an infinite set) is_model.
*)

needs "candle/set-theory/setSpec.ml";;
needs "lib/numposrep.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "setModel"
  ["setSpec"];;
(* HOL4 ancestors outside the port: bit *)

let is_set_theory_pred_def = new_definition
  `is_set_theory_pred is_v_rep in_rep <=>
    (?x. is_v_rep x) /\
    (!x y. is_v_rep x /\ is_v_rep y ==> ((x = y) <=> (!a. is_v_rep a ==>
      (in_rep a x <=> in_rep a y)))) /\
    (!x P. is_v_rep x ==> (?y. is_v_rep y /\ (!a. is_v_rep a ==> (in_rep a y
      <=> (in_rep a x /\ P a))))) /\
    (!x. is_v_rep x ==> (?y. is_v_rep y /\ (!a. is_v_rep a ==> (in_rep a y
      <=> (!b. is_v_rep b ==> in_rep b a ==> in_rep b x))))) /\
    (!x. is_v_rep x ==> (?y. is_v_rep y /\ (!a. is_v_rep a ==> (in_rep a y
      <=> (?b. is_v_rep b /\ in_rep a b /\ in_rep b x))))) /\
    (!x y. is_v_rep x /\ is_v_rep y ==> (?z. is_v_rep z /\ (!a. is_v_rep a
      ==> (in_rep a z <=> (a = x \/ a = y))))) /\
    (!x. is_v_rep x ==> (?y. is_v_rep y /\ (!a. is_v_rep a /\ in_rep a x
      ==> in_rep y x)))`;;

let l_model_exists = prove
 (`?(P:'a+num->bool) (mem':'a+num->'a+num->bool). is_set_theory_pred P mem'`,
  CHEAT_TAC);;

(* HOL4 setModelScript.sml:168: ML code, not ported *)

(* HOL4 setModelScript.sml:170-174: ML code, not ported *)

(* HOL4 setModelScript.sml:176-177: ML code, not ported *)

let v_mem_def = new_definition
  `V_mem x y = V_mem_rep (dest_V x) (dest_V y)`;;

let is_set_theory_V = prove
 (`is_set_theory V_mem`,
  CHEAT_TAC);;

(* V_choice_exists[local] *)
let v_choice_exists = prove
 (`?ch. is_choice V_mem ch`,
  CHEAT_TAC);;

(* HOL4 setModelScript.sml:239-240: ML code, not ported *)

(* HOL4 setModelScript.sml:242-244: ML code, not ported *)

let is_model_V = prove
 (`(?(I':'a) V. is_infinite V_mem I') ==>
    is_model (V_mem,(V_indset:'a V),V_choice)`,
  CHEAT_TAC);;

(* and the interface *)
let _ = unhide_overloads ();;
