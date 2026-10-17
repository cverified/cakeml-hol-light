(* ================================================================== *)
(*  The preamble of the CakeML port: the HOL Light libraries it uses  *)
(*  and                                                               *)
(*  the HOL4 compatibility layer.                                     *)
(* ================================================================== *)

let cakeml_dir = "/home/freek/claude/hol-light/cakeml/ml";;

load_path := cakeml_dir :: (!load_path);;

needs "Library/words.ml";;

needs "lib/fastdef.ml";;
needs "lib/hol4.ml";;
needs "lib/define.ml";;
needs "lib/records.ml";;
needs "lib/words4.ml";;
needs "lib/finite_map.ml";;
needs "lib/llist.ml";;
needs "lib/relation.ml";;
needs "lib/bag.ml";;
needs "lib/string4.ml";;

(* the port has polymorphic definitions all over the place, as the
   CakeML sources do, so the warning about that is turned off *)
type_invention_warning := false;;

(* Loading a file of the port would print every definition, which is
   slow and unreadable; this prints a theorem as |- ... instead.  Set
   print_thm_full to see them again. *)

let print_thm_full = ref false;;

let print_thm_brief fmt th =
  if !print_thm_full then pp_print_thm fmt th
  else Format.pp_print_string fmt "|- ...";;

#install_printer print_thm_brief;;
