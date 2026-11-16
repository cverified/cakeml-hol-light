(* ======================================================== *)
(*  pan_common: ported from HOL4's
    pancake/pan_commonScript.sml
    A definition theory, with 1 definition and no theorems.  Needed
    by pan_to_crep.ml.  *)
(* ======================================================== *)

(* this file needs nothing of the port *)

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "pan_common" [];;

(*
  Common definitions for Pancake compiler
*)

let distinct_lists_def = new_definition
  `distinct_lists xs ys =
     ALL (\x. ~(MEM x ys)) xs`;;

(* and the interface *)
let _ = unhide_overloads ();;
