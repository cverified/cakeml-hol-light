(* ======================================================== *)
(*  source_to_source: ported from HOL4's
    compiler/backend/source_to_sourceScript.sml
    A definition theory, with 1 definition and no theorems.  Needed
    by backend.ml and source_to_sourceProof.ml.  *)
(* ======================================================== *)

(*
  This phase collects all source-to-source transformations.
 *)

needs "compiler/backend/source_let.ml";;
needs "misc/misc.ml";;


let source_to_source_compile_def = cake_define
  `source_to_source_compile = source_let_compile_decs`;;
hol4_overload "compile" "source_to_source_compile";;
