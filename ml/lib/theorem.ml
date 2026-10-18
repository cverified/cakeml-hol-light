(* ================================================================== *)
(*  HOL4's Theorem for HOL Light: the theorems of phase two.          *)
(*                                                                    *)
(*  A theorem of a CakeML source is in the port with its name, its    *)
(*  attributes and its statement, and CHEAT_TAC where HOL4 has its    *)
(*  proof (see CLAUDE.md):                                            *)
(*                                                                    *)
(*    let foo = cake_theorem "foo[simp]"                              *)
(*      (fun () ->                                                    *)
(*        `!x. P x ==> Q x`)                                          *)
(*      CHEAT_TAC;;                                                   *)
(*                                                                    *)
(*  Phase three replaces that CHEAT_TAC by a proof, and nothing else  *)
(*  of the file changes.  The statement is a quotation in a function  *)
(*  so that one that does not typecheck is a cheat of its own and     *)
(*  not an error that loses the rest of the file.                     *)
(* ================================================================== *)

(* the theorems of the port, by the name that HOL4 gives them, with
   the attributes that HOL4 gives them ([simp], [compute], [local],
   ...).  The attributes are part of what the source says, but
   nothing of the port acts on them: phase three does not replay
   HOL4's automation. *)

let the_theorems = ref ([]:(string * string list * thm) list);;

let cake_theorems () = rev (!the_theorems);;

(* the theorems whose statement the port cannot state yet: the
   quotation did not parse or did not typecheck.  Nothing is known
   about those at all, and the reports of a run list them. *)

let the_unstated = ref ([]:(string * string) list);;

let cake_unstated () = rev (!the_unstated);;

let cake_split_commas s =
  let rec go i acc cur =
    if i >= String.length s then rev (cur :: acc)
    else if s.[i] = ',' then go (i + 1) (cur :: acc) ""
    else go (i + 1) acc (cur ^ String.make 1 s.[i]) in
  filter (fun x -> x <> "") (map String.trim (go 0 [] ""));;

(* "foo[simp,compute]" is the name foo with the attributes simp and
   compute, which is how HOL4 writes them *)

let cake_split_attrs name =
  try let i = String.index name '[' in
      String.sub name 0 i,
      cake_split_commas
        (String.sub name (i + 1) (String.length name - i - 2))
  with Not_found -> name,[];;

let note_unstated nm what s =
  the_unstated := (nm,s) :: !the_unstated;
  print_string ("\ncake_theorem " ^ nm ^ " " ^ what ^ ": " ^ s ^ "\n");
  flush stdout;;

(* a theorem of a source, with the tactic that the port has for it.
   In phase two that tactic is CHEAT_TAC and the theorem is an
   axiom, which length(axioms()) counts; in phase three it is a
   proof of its own and no axiom is added. *)

let cake_theorem name mkterm tac =
  let nm,attrs = cake_split_attrs name in
  let tm =
    try Some (mkterm ()) with
      Failure s -> (note_unstated nm "NOT STATED" s; None)
    | Invalid_argument s -> (note_unstated nm "NOT STATED" s; None) in
  match tm with
    None -> TRUTH
  | Some tm ->
      let th =
        try prove (tm,tac) with
          Failure s -> (note_unstated nm "NOT PROVED" s;
                        prove (tm,CHEAT_TAC)) in
      the_theorems := (nm,attrs,th) :: !the_theorems;
      th;;
