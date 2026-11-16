(* ==================================================================== *)
(*  The resolution round.                                               *)
(*                                                                      *)
(*  HOL4 resolves an overloaded name by the type that makes the term    *)
(*  typecheck, and HOL Light does the same against its interface --     *)
(*  which the port already builds, one scope per file (cake_theory).    *)
(*  So the port does not have to guess: with CAKE_RESOLVE=1 it writes   *)
(*  the name as the source writes it, the typechecker resolves it, and  *)
(*  this file writes down what the typechecker took.                    *)
(*                                                                      *)
(*  Every term of the port goes through parse_term (the quotation       *)
(*  expands to a call of it, which is compiled in the environment of    *)
(*  the phrase, so a binding made here is the one the files after it    *)
(*  use).  cake_at says which block of which theory is being read, and  *)
(*  the constants of each term that could have come from an overloaded  *)
(*  name are logged under it.  tools/mkresolved.py turns the log into   *)
(*  tools/resolved.txt.                                                 *)
(* ==================================================================== *)

(* The port writes every constant under a name of its own
   (bvl_Var, clos_Var), and nothing of a datatype or a definition
   goes into the interface under the name the HOL4 source writes:
   a file names the constant it means and there is nothing to
   resolve while it loads.  A resolution round is the one place
   that wants the other arrangement, so the files of a round
   register each constant under its HOL4 name as they define it,
   which is what HOL4 does, and cake_theory cuts the interface
   down to the scope of each file as before.

   A block that the port could not write leaves its constant
   undefined, so a registration of it is let go. *)

let cake_ovl l =
  do_list (fun (n,c) -> try hol4_overload n c with _ -> ()) l;;

let cake_res_dir =
  try Sys.getenv "CAKE_RESDIR" with Not_found ->
  "/home/freek/claude/hol-light/cakeml/tmp/res/";;

(* the constants that are worth logging: the ones that some theory
   of the port reaches under a name that another theory of its
   scope has as well.  Everything else says nothing about a
   resolution, and the port has 60,000 constants *)

let cake_res_want = Hashtbl.create 20000;;

let cake_res_read_wanted () =
  try
    let ch = open_in (cake_res_dir ^ "consts.txt") in
    (try while true do
           Hashtbl.replace cake_res_want (input_line ch) ()
         done
     with End_of_file -> ());
    close_in ch
  with Sys_error _ -> ();;

cake_res_read_wanted ();;

let cake_res_ch = ref None;;

let cake_res_out () =
  match !cake_res_ch with
    Some ch -> ch
  | None -> let ch = open_out (cake_res_dir ^ "resolve.txt") in
            cake_res_ch := Some ch; ch;;

let cake_res_now = ref ("","");;
let cake_res_seen = Hashtbl.create 1000;;

let cake_at thy nm =
  cake_res_now := (thy,nm);
  Hashtbl.reset cake_res_seen;
  (match !cake_res_ch with Some ch -> flush ch | None -> ());;

let cake_res_note tm =
  let thy,nm = !cake_res_now in
  if nm = "" then () else
  let cs = setify (map (fst o dest_const) (find_terms is_const tm)) in
  do_list
    (fun c ->
       if Hashtbl.mem cake_res_want c && not (Hashtbl.mem cake_res_seen c)
       then (Hashtbl.replace cake_res_seen c ();
             output_string (cake_res_out ())
               (thy ^ "\t" ^ nm ^ "\t" ^ c ^ "\n")))
    cs;;

let cake_res_parse_term = parse_term;;

let parse_term s =
  let tm = cake_res_parse_term s in
  (try cake_res_note tm with _ -> ()); tm;;

print_string "*** the resolution round is logging constants ***\n";;
