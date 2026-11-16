(* ======================================================== *)
(*  source_cv: ported from HOL4's
    semantics/proofs/source_cvScript.sml
    A proof theory, with no definitions and no theorems.  Needed by
    infer_cv.ml and to_data_cv.ml.  *)
(* ======================================================== *)

(*
  Translation of the CakeML AST and related types for use with cv_compute.
*)

needs "basis/pure/basis_cv.ml";;
needs "lib/cv_std.ml";;
needs "lib/location.ml";;
needs "semantics/ast.ml";;
needs "semantics/namespace.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "source_cv"
  ["ast"; "basis_cv"; "namespace"];;

(* HOL4 source_cvScript.sml:11-12: ML code, not ported *)

(* HOL4 source_cvScript.sml:14-15: ML code, not ported *)

(* HOL4 source_cvScript.sml:17: ML code, not ported *)

(* and the interface *)
let _ = unhide_overloads ();;
