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
  (* a pair whose constant is not in the interface is not taken
     out of it, so it is not put back either: the port names the
     pairs of a field by the theories that have one, and a theory
     that comes later in the load order has no constant yet.
     What goes is added to what another call took out, so that one
     unhide_overloads at the end of the file puts all of it back *)
  let gone =
    filter (fun (n,c) ->
              exists (fun (n2,(c2,_)) -> n2 = n && c2 = c)
                     (!the_interface))
           l in
  the_removed_overloads := gone @ (!the_removed_overloads);
  the_interface :=
    filter (fun (n,(c,_)) -> not (mem (n,c) l)) (!the_interface);;

(* the whole interface as it stood before a file cut it down to
   its own scope (hol4_ancestors below), which is how it is put
   back: a pair that goes back in front of the one that stood
   before it would decide another name for the file after this,
   because the interface is resolved from the front *)

let the_saved_interface =
  ref (None:(string * (string * hol_type)) list option);;

let unhide_overloads () =
  match !the_saved_interface with
    Some saved ->
      (* the interface the file had, with what the file registered
         itself in front of it and at the back of it, which is
         where those stood while it loaded: a pair that was in the
         interface already and that the file registered again
         (HOL4's bring_to_front_overload) is in front for the
         files after this, as HOL4 keeps it, and the one further
         back goes -- as overload_interface takes it out, and a
         second entry of the pair would be one that no
         override_interface of a later file can take out again *)
      let own =
        map (fun (n,(c,_)) -> (n,c))
            ((!the_file_overloads) @ (!the_file_overloads_last)) in
      the_interface :=
        (!the_file_overloads) @
          filter (fun (n,(c,_)) -> not (mem (n,c) own)) saved @
          (!the_file_overloads_last);
      the_file_overloads := [];
      the_file_overloads_last := [];
      the_saved_interface := None;
      the_removed_overloads := []
  | None ->
      the_interface :=
        map (fun (n,c) -> (n,(c,get_const_type c)))
            (!the_removed_overloads) @ (!the_interface);
      the_removed_overloads := [];;

(* ------------------------------------------------------------------ *)
(*  The theories that a file can see.                                 *)
(*                                                                    *)
(*  HOL4 reads a statement with the names of the theories of the      *)
(*  Ancestors blocks of its source, and of no others: a name of       *)
(*  another theory is not in the grammar of the file at all.  HOL     *)
(*  Light has one interface for the whole port, so every theory's     *)
(*  overload of a name is in it, and where the type of what the name  *)
(*  is applied to does not pin it down it takes the constant that     *)
(*  was registered last -- which is the load order and not the        *)
(*  ancestry.  The statement then says what the load order made of    *)
(*  it: bvlProps' evaluate_CONS was about bviSem's evaluate in a      *)
(*  run, where bviSem loads before bvlProps, and about bvlSem's in    *)
(*  the closure of a single file, where it does not -- so a proof of  *)
(*  bvl_constProof that rewrites with it passed a verify and failed   *)
(*  the run (ISSUES.md "A statement that means another theory's       *)
(*  constant").                                                       *)
(*                                                                    *)
(*  So a file of the port says which theory it is and which ones its  *)
(*  source can see, and the overloads of all the others come out of   *)
(*  the interface while it loads.  tools/port.py writes the line out  *)
(*  of the Ancestors blocks of the source, and the unhide_overloads   *)
(*  at the end of the file puts them back.                            *)
(* ------------------------------------------------------------------ *)

(* the list of every file that has said it, and the scope that it
   makes of one: the theories of the list and the ones of their own
   lists.  An ancestor is loaded before the file that names it, so
   its list is in before the scope of this one is wanted. *)

let the_ancestry = ref ([]:(string * string list) list);;

let the_anc_scope = Hashtbl.create 300;;

let rec anc_scope thy =
  try Hashtbl.find the_anc_scope thy with Not_found ->
  let anc = try assoc thy (!the_ancestry) with Failure _ -> [] in
  let out = itlist (fun t s -> union (t :: anc_scope t) s) anc [] in
  Hashtbl.replace the_anc_scope thy out; out;;

let hol4_ancestors thy anc =
  (* a file that failed before the end of itself left its own
     scope in the interface, so the interface goes back first *)
  if !the_saved_interface <> None then unhide_overloads ();
  the_thy_loading := thy;
  if not (can (assoc thy) (!the_ancestry)) then
    (the_ancestry := (thy,anc) :: (!the_ancestry);
     Hashtbl.reset the_anc_scope);
  if !the_saved_interface = None then
    (the_saved_interface := Some (!the_interface);
     the_file_overloads := [];
     the_file_overloads_last := []);
  let seen = thy :: anc_scope thy in
  (* a pair of no theory is the library layer's own (sptree's
     lookup), which every source of CakeML has through its
     preamble: it stays in the interface.  So does one that any
     theory of the scope has registered. *)
  let gone =
    map fst (filter (fun (_,ts) ->
                       not (exists (fun t -> t = "" || mem t seen) ts))
                    (!the_overload_thy)) in
  the_interface :=
    filter (fun (n,(c,_)) -> not (mem (n,c) gone)) (!the_interface);;
