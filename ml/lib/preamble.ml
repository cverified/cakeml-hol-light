(* ========================================================================= *)
(*  The preamble of the CakeML port: the HOL Light libraries it uses and     *)
(*  the HOL4 compatibility layer.                                           *)
(* ========================================================================= *)

let cakeml_dir = "/home/freek/claude/hol-light/cakeml/ml";;

load_path := cakeml_dir :: (!load_path);;

(* the port has polymorphic definitions all over the place, as the
   CakeML sources do, so the warning about that is turned off *)
type_invention_warning := false;;

needs "Library/words.ml";;

needs "lib/hol4.ml";;
needs "lib/records.ml";;
needs "lib/define.ml";;
