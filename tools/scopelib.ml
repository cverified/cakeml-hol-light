(* The theories that the source of a file of the port can see, and
   the interface that it reads its statements with: the one of the
   session with the overloads of every other theory taken out, as
   ml/lib/theorem.ml's hol4_ancestors does while the file loads.

   tools/mkscope.py writes the two tables this reads (tmp/scopes.txt
   and tmp/cstthy.txt).  tools/scope.ml (what the cut changes) and
   tools/diag.ml (what a session cannot read) both read statements
   that way; ISSUES.md "A statement that means another theory's
   constant" says why. *)

let slurp_lines f =
  let ic = open_in f in
  let out = ref [] in
  (try while true do out := input_line ic :: !out done
   with End_of_file -> ());
  close_in ic; rev !out;;

let split_tab l = String.split_on_char '\t' l;;

let cake_dir = "/home/freek/claude/hol-light/cakeml/";;

(* the theories that the port has a file of, and the scope of each
   of its files *)

let the_theories = ref ([]:string list);;
let the_scopes = ref ([]:(string * string list) list);;

let read_scopes () =
  do_list (fun l ->
    match split_tab l with
      ["@@@THYS"; ts] ->
        the_theories := String.split_on_char ' ' ts
    | ["@@@SCOPE"; f; ts] ->
        the_scopes := (f, String.split_on_char ' ' ts) :: !the_scopes
    | _ -> ())
    (slurp_lines (cake_dir ^ "tmp/scopes.txt"));;

(* the theory of a constant of the port: the file of ml/ that
   defines it (tmp/cstthy.txt, out of tools/defsites.py).  The name
   of a constant does not say its theory -- backend_common defines
   bvl_to_bvi_namespaces -- and a constant that no file of the port
   defines (one of HOL Light, or of the library layer) has no
   theory and is in the scope of every file. *)

let the_thy_of = Hashtbl.create 6000;;

let read_cstthy () =
  Hashtbl.reset the_thy_of;
  do_list (fun l ->
    match split_tab l with
      [c; t] -> Hashtbl.replace the_thy_of c t
    | _ -> ())
    (slurp_lines (cake_dir ^ "tmp/cstthy.txt"));;

let thy_of_cst c =
  try Hashtbl.find the_thy_of c with Not_found -> "";;

(* the entries of the interface that a file cannot see: a constant
   of a theory that is not in its scope.  The port registers an
   overload of every theory, so the interface of a session is the
   interface of every file at once. *)

let in_scope thys =
  filter (fun (_,(c,_)) ->
            let t = thy_of_cst c in
            t = "" || mem t thys)
         (!the_interface);;

(* the interface of a file, which is the one of the session cut
   down to its scope: it is the same for every statement of the
   file, so it is built once *)

let with_interface itf f =
  let saved = !the_interface in
  the_interface := itf;
  let fin () = the_interface := saved in
  try let x = f () in fin (); x
  with e -> (fin (); raise e);;
