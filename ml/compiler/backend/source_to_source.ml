(* ======================================================== *)
(*  source_to_source: ported from HOL4's
    compiler/backend/source_to_sourceScript.sml  *)
(* ======================================================== *)

(*
  This phase collects all source-to-source transformations.
 *)

needs "compiler/backend/source_let.ml";;
needs "misc/misc.ml";;


let compile_def = cake_define
  `source_to_source_compile = source_let_compile_decs`;;
hol4_overload "compile" "source_to_source_compile";;
