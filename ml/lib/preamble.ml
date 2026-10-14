(* ========================================================================= *)
(*  The preamble of the CakeML port: the HOL Light libraries it uses and     *)
(*  the HOL4 compatibility layer.                                           *)
(* ========================================================================= *)

let cakeml_dir = "/home/freek/claude/hol-light/cakeml/ml";;

load_path := cakeml_dir :: (!load_path);;

needs "Library/words.ml";;

needs "lib/hol4.ml";;
needs "lib/records.ml";;
needs "lib/define.ml";;
