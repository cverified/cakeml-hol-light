(* ======================================================== *)
(*  pattern_common: ported from HOL4's
    compiler/backend/pattern_matching/pattern_commonScript.sml
    A definition theory, with no definitions, 3 datatypes and no
    theorems.  Needed by flat_pattern.ml, flat_patternProof.ml,
    pattern_comp.ml, pattern_exh.ml and pattern_semantics.ml.  *)
(* ======================================================== *)

(*
  Types common to some different parts of the pattern match compiler.
*)

(* this file needs nothing of the port *)

(* the theories whose names the Ancestors blocks of the source
   bring, which are the ones that its statements read: the
   overloads of every other theory come out of the interface
   while this file loads *)
let _ = hol4_ancestors "pattern_common" [];;
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

(* and the overloads that this file cannot see are back in the
   interface *)
let _ = unhide_overloads ();;
