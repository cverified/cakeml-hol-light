(* ======================================================== *)
(*  cmlNTProps: ported from HOL4's
    compiler/parsing/proofs/cmlNTPropsScript.sml
    A proof theory, with no definitions and 84 theorems.  Needed by
    pegComplete.ml.  *)
(* ======================================================== *)

(*
  Properties (first sets etc) for non-terminals in the CakeML grammar
*)

needs "lib/NTproperties.ml";;
needs "semantics/gram.ml";;
needs "semantics/proofs/gramProps.ml";;
(* HOL4 cmlNTPropsScript.sml:57-59: ML code, not ported *)
