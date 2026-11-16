(* ======================================================== *)
(*  OptionProg: ported from HOL4's
    basis/OptionProgScript.sml
    A definition theory, with no definitions and no theorems.
    Needed by ListProg.ml.  *)
(* ======================================================== *)

(*
  Module about the option type.
*)

needs "basis/RuntimeProg.ml";;
needs "basis/pure/mloption.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "OptionProg"
  ["RuntimeProg"; "ml_prog"; "ml_translator"; "mloption"];;

(* HOL4 OptionProgScript.sml:10: ML code, not ported *)

(* HOL4 OptionProgScript.sml:12: ML code, not ported *)

(* HOL4 OptionProgScript.sml:14-15: ML code, not ported *)

(* HOL4 OptionProgScript.sml:17-18: ML code, not ported *)

(* HOL4 OptionProgScript.sml:20-21: ML code, not ported *)

(* HOL4 OptionProgScript.sml:23-29: a theorem that HOL4 states as the value
   of an ML expression: the_side_def *)

(* HOL4 OptionProgScript.sml:31-32: ML code, not ported *)

(* HOL4 OptionProgScript.sml:34-35: ML code, not ported *)

(* HOL4 OptionProgScript.sml:37-38: ML code, not ported *)

(* HOL4 OptionProgScript.sml:40: ML code, not ported *)

(* HOL4 OptionProgScript.sml:42-43: ML code, not ported *)

(* HOL4 OptionProgScript.sml:45-46: ML code, not ported *)

(* HOL4 OptionProgScript.sml:48-49: ML code, not ported *)

(* HOL4 OptionProgScript.sml:51-52: ML code, not ported *)

(* HOL4 OptionProgScript.sml:54: ML code, not ported *)

(* and the interface *)
let _ = unhide_overloads ();;
