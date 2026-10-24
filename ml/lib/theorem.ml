(* ================================================================== *)
(*  The one thing a statement of a source needs that HOL Light has    *)
(*  no primitive for.                                                 *)
(*                                                                    *)
(*  A theorem of a CakeML source is in the port the way HOL Light     *)
(*  writes one, with the attributes HOL4 gives it in a comment        *)
(*  over it and CHEAT_TAC where phase three has yet to put a proof:   *)
(*                                                                    *)
(*    (* [simp] *)                                                    *)
(*    let foo = prove                                                 *)
(*     (`!x. P x ==> Q x`,                                            *)
(*      CHEAT_TAC);;                                                  *)
(*                                                                    *)
(*  A name that HOL4 reads as a variable because no theory in scope   *)
(*  defines it is hidden with HOL Light's own hide_constant, and a    *)
(*  variable whose name the port overloads with a record accessor     *)
(*  says its type (tools/fieldvars.py).  What is left is the case     *)
(*  where a file needs the accessors of a field and reads the name    *)
(*  of that field as a variable as well: hiding the name would take   *)
(*  the accessors with it, so only those pairs come out of the        *)
(*  interface, which is what these two say.                           *)
(* ================================================================== *)

let the_removed_overloads = ref ([]:(string * string) list);;

let hide_overloads l =
  the_removed_overloads := l;
  the_interface :=
    filter (fun (n,(c,_)) -> not (mem (n,c) l)) (!the_interface);;

let unhide_overloads () =
  the_interface :=
    map (fun (n,c) -> (n,(c,get_const_type c)))
        (!the_removed_overloads) @ (!the_interface);
  the_removed_overloads := [];;
