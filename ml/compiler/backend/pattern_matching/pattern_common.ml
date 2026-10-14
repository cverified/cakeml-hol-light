(* ======================================================== *)
(*  pattern_common: ported from HOL4's
    compiler/backend/pattern_matching/pattern_commonScript.sml  *)
(* ======================================================== *)

(*
  Types common to some different parts of the pattern match compiler.
*)

(* this file needs nothing of the port *)
(* HOL4 ancestors outside the port: num list arithmetic *)


(*
A position describes a path to a sub-term in a term
*)
let position_INDUCT,position_RECURSION = define_datatype
  "position = EmptyPos | Pos (num) (position)";;

(* Results of a pattern match or a multiple pattern match *)
let pmatchResult_INDUCT,pmatchResult_RECURSION = define_datatype
  "pmatchResult = PMatchSuccess | PMatchFailure | PTypeFailure";;

(*
  Pattern matching can return three results :
    - Success, with the number of the right hand side that succeeded
    - MatchFailure, when no branch has matched the value
    - TypeFailure, when there was a type mismatch between the value
      to be matched and the patterns
*)
let matchResult_INDUCT,matchResult_RECURSION = define_datatype
  "matchResult = MatchSuccess (num) | MatchFailure";;
