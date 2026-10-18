(* ======================================================== *)
(*  typeSound: ported from HOL4's
    semantics/proofs/typeSoundScript.sml  *)
(* ======================================================== *)

(*
  Proof of type soundness: a type-correct program does not crash.
*)

needs "semantics/ast.ml";;
needs "semantics/evaluate.ml";;
needs "semantics/fpSem.ml";;
needs "semantics/proofs/evaluateProps.ml";;
needs "semantics/proofs/namespaceProps.ml";;
needs "semantics/proofs/primSemEnv.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;
needs "semantics/proofs/typeSoundInvariants.ml";;
needs "semantics/proofs/typeSysProps.ml";;
needs "semantics/proofs/weakening.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "semantics/semantics.ml";;
needs "semantics/typeSystem.ml";;

(* HOL4 typeSoundScript.sml:17-32: ML code, not ported *)

(* Classifying values of basic types *)

(* HOL4 typeSoundScript.sml:411-420: ML code, not ported *)

let store_type_extension_def = cake_define
  `store_type_extension tenvS1 tenvS2 =
   (?tenvS'. (tenvS2 = FUNION tenvS' tenvS1) /\
            (!l. (FLOOKUP tenvS' l = NONE) \/ (FLOOKUP tenvS1 l =
              NONE)))`;;

(* HOL4 typeSoundScript.sml:618-632: code that the source has in a
   comment *)

(* HOL4 typeSoundScript.sml:1125-1139: ML code, not ported *)

(* TODO: Move *)

(* HOL4 typeSoundScript.sml:1920-1967: ML code, not ported *)
