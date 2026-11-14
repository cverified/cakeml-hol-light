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

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "source_to_source"
  ["misc"; "source_let"];;


let source_to_source_compile_def = new_definition
  `source_to_source_compile = source_let_compile_decs`;;

(* and the interface *)
let _ = unhide_overloads ();;
