(* ======================================================== *)
(*  pan_to_word: ported from HOL4's
    pancake/pan_to_wordScript.sml
    A definition theory, with 1 definition and no theorems.  Needed
    by from_pancake32Prog.ml, from_pancake64Prog.ml and
    pan_to_target.ml.  *)
(* ======================================================== *)

(*
  Compiler from pan to word
*)

needs "basis/pure/mlstring.ml";;
needs "pancake/crep_to_loop.ml";;
needs "pancake/loop_to_word.ml";;
needs "pancake/pan_globals.ml";;
needs "pancake/pan_simp.ml";;
needs "pancake/pan_structs.ml";;
needs "pancake/pan_to_crep.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "pan_to_word"
  ["crep_to_loop"; "loop_to_word"; "pan_globals"; "pan_simp"; "pan_structs";
   "pan_to_crep"];;

let pan_to_word_compile_prog_def = new_definition
  `pan_to_word_compile_prog arch prog =
   let prog = pan_simp_compile_prog prog in let
       prog = pan_structs_compile_top prog in let
       prog = pan_globals_compile_top prog (implode "main") in let
       prog = pan_to_crep_compile_prog prog in let
       prog = crep_to_loop_compile_prog arch prog in
     loop_to_word_compile prog`;;

(* and the interface *)
let _ = unhide_overloads ();;
