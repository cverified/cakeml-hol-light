(* ================================================================== *)
(* An abstract: the files are loaded for their side effects only.     *)
(*                                                                    *)
(* Loading the port takes about two hours, and most of that is spent  *)
(* proving things that have been proved before.  A session that only  *)
(* needs the constants, the definitions and the theorems to be there  *)
(* -- to develop the next proof against, or to read a statement --    *)
(* loads it with this file in front of it instead: every definition   *)
(* makes its constant and assumes its equations, every induction      *)
(* theorem is its statement assumed, and every proof is skipped.      *)
(*                                                                    *)
(* What makes this safe to rely on is that the statements are the     *)
(* same terms either way.  An abstract does not have a second copy    *)
(* of what a file says: the induction theorem is computed from the    *)
(* clauses (ml/lib/induction.ml), and a real load computes it the     *)
(* same way and then proves it.  So an abstract cannot drift from     *)
(* the port, only from the question whether the port is true.         *)
(*                                                                    *)
(* NOTHING IS PROVED IN THIS MODE, and length (axioms ()) says        *)
(* nothing about the port while it is on.                             *)
(* ================================================================== *)

let cake_abstract = true;;

(* the constant of a function that is being defined, made if the
   port has not got it yet *)

let fast_constant v =
  let n,ty = dest_var v in
  try let gty = get_const_type n in
      mk_const(n,type_match gty ty [])
  with Failure _ -> (new_constant(n,ty); mk_mconst(n,ty));;

(* the definition is noted as a real load notes it, so that a
   tactic that asks for one by the name of its constant finds
   the assumed equations.  What a real load also notes is what
   a destructor does to the size of its argument, which only a
   termination proof uses and an abstract proves nothing *)

let fast_definition tm =
  let fs = definition_heads tm in
  let sub = map (fun v -> fast_constant v,v) fs in
  (* every clause is closed over its own variables, which is what
     a real load gives (close_clause, ml/lib/define.ml): a source
     that states a theorem as the value of an ML expression
     specializes the equations of a definition, and an assumed
     form without the quantifiers fails in dest_forall *)
  let cls = map (close_clause fs) (conjuncts(snd(strip_forall tm))) in
  let th = mk_thm([],subst (filter (fun (c,v) -> c <> v) sub)
                           (list_mk_conj cls)) in
  cake_note_def th; th;;

let fast_clauses cls = fast_definition (definition_of_clauses cls);;

let fast_one tm = fast_clauses [tm];;

(* ------------------------------------------------------------------ *)
(* The datatypes.                                                     *)
(*                                                                    *)
(* define_datatype proves the induction and the recursion theorem of  *)
(* a datatype, which is 18% of an abstract's processor time over the  *)
(* 249 datatypes of the port and is a proof like any other.  So an    *)
(* abstract makes the type and the constructors through the kernel    *)
(* and assumes those two, exactly as it assumes the equations of a    *)
(* definition.                                                        *)
(*                                                                    *)
(* The two statements are not read off the specification: HOL Light   *)
(* states and proves them together, and a datatype that recurses      *)
(* through a list (CakeML's expressions do) gets a statement about    *)
(* the list as well, which is where a hand written generator would    *)
(* go wrong.  They are recorded from a real construction instead      *)
(* (tools/harvest_datatypes.ml writes ml/lib/datatypes.txt), so what  *)
(* an abstract assumes is the term a run proves, by construction.     *)
(* A datatype the table does not have is built for real.              *)
(* ------------------------------------------------------------------ *)

let cake_dt_table = Hashtbl.create 500;;

(* the key is the specification with its whitespace taken out, so
   that how the port breaks the lines of one is no part of it *)

let cake_dt_key s =
  implode (filter (fun c -> c <> " " && c <> "\n" && c <> "\t")
                  (explode s));;

(* ml/lib/datatypes.txt has one datatype to a line, in five fields
   that a tab separates: the key, the types with their arity, the
   constructors with their type, and the two statements.  A term
   is written with its line breaks taken out, which the parser of
   HOL Light does not mind *)

let cake_dt_split c s =
  let out = ref [] and cur = ref [] in
  do_list (fun ch ->
             if ch = c then (out := implode (rev !cur) :: !out;
                             cur := [])
             else cur := ch :: !cur)
          (explode s);
  rev (implode (rev !cur) :: !out);;

let cake_dt_pairs sep s =
  if s = "" then [] else
  map (fun e -> let p = cake_dt_split ":" e in hd p, hd (tl p))
      (cake_dt_split sep s);;

let cake_dt_line l =
  let f = cake_dt_split "\t" l in
  if length f <> 5 then () else
  let tys = map (fun (n, a) -> n, int_of_string a)
                (cake_dt_pairs "," (el 1 f)) in
  Hashtbl.replace cake_dt_table (hd f)
    (tys, cake_dt_pairs ";" (el 2 f), el 3 f, el 4 f);;

let cake_dt_read file =
  let ic = open_in file in
  (try while true do cake_dt_line (input_line ic) done
   with End_of_file -> ());
  close_in ic;;

(* the type and the constructors are made through the kernel, so
   that everything after the datatype sees what it would see *)

let cake_dt_make (tys, cons, ind, rc) =
  do_list (fun (n, a) ->
             if not (can get_type_arity n) then new_type (n, a)) tys;
  do_list (fun (c, ty) ->
             if not (can get_const_type c) then
               new_constant (c, parse_type ty)) cons;
  let ith = mk_thm ([], parse_term ind) in
  let rth = mk_thm ([], parse_term rc) in
  register_rec_thm rth;
  ith, rth;;

let real_define_datatype = define_datatype;;

let fast_datatype spec =
  try cake_dt_make (Hashtbl.find cake_dt_table (cake_dt_key spec))
  with Not_found -> real_define_datatype spec;;

(* the statement is read off the clauses, and a real load reads it
   the same way; where it cannot be read off, a real load binds
   nothing either (ISSUES.md) *)

let fast_induction th =
  try mk_thm([],induction_statement (concl th))
  with Failure _ -> TRUTH;;

let fast_pair cls =
  let th = fast_clauses cls in th,fast_induction th;;

let fast_pair_one tm = fast_pair [tm];;

(* what the ways are before this file takes their names: an
   abstract is turned back into a session that proves by
   loading ml/lib/real.ml, which gives them back.  The
   template has the hand written files of ml/lib in it, so
   they are all here already *)

let real_new_definition = new_definition;;
let real_define_cases = define_cases;;
let real_define_general = define_general;;
let real_define_general_cheat = define_general_cheat;;
let real_define_shaped = define_shaped;;
let real_assume_definition = assume_definition;;
let real_define_rec = define_rec;;
let real_define_wf = define_wf;;
let real_define_wf_cheat = define_wf_cheat;;
let real_define_wf_tac = define_wf_tac;;
let real_define_guess = define_guess;;
let real_define_guess_cheat = define_guess_cheat;;
let real_define_shaped_rec = define_shaped_rec;;
let real_define_shaped_rec_cheat = define_shaped_rec_cheat;;
let real_define_shaped_rec_tac = define_shaped_rec_tac;;
let real_define_shaped_wf = define_shaped_wf;;
let real_define_shaped_wf_cheat = define_shaped_wf_cheat;;
let real_define_shaped_wf_tac = define_shaped_wf_tac;;
let real_assume_definition_rec = assume_definition_rec;;
let real_define_cases_clauses = define_cases_clauses;;
let real_define_general_clauses = define_general_clauses;;
let real_define_general_cheat_clauses = define_general_cheat_clauses;;
let real_define_shaped_clauses = define_shaped_clauses;;
let real_assume_definition_clauses = assume_definition_clauses;;
let real_define_rec_clauses = define_rec_clauses;;
let real_define_wf_clauses = define_wf_clauses;;
let real_define_wf_cheat_clauses = define_wf_cheat_clauses;;
let real_define_wf_tac_clauses = define_wf_tac_clauses;;
let real_define_guess_clauses = define_guess_clauses;;
let real_define_guess_cheat_clauses = define_guess_cheat_clauses;;
let real_define_shaped_rec_clauses = define_shaped_rec_clauses;;
let real_define_shaped_rec_cheat_clauses = define_shaped_rec_cheat_clauses;;
let real_define_shaped_rec_tac_clauses = define_shaped_rec_tac_clauses;;
let real_define_shaped_wf_clauses = define_shaped_wf_clauses;;
let real_define_shaped_wf_cheat_clauses = define_shaped_wf_cheat_clauses;;
let real_define_shaped_wf_tac_clauses = define_shaped_wf_tac_clauses;;
let real_assume_definition_rec_clauses = assume_definition_rec_clauses;;
let real_prove = prove;;

(* the ways of making a definition, and the proofs: the
   ones that give a pair give the induction theorem too *)

let new_definition tm = fast_definition tm;;

let define_datatype spec = fast_datatype spec;;

let define_cases tm = fast_one tm;;
let define_cases_clauses cls = fast_clauses cls;;

let define_general tm = fast_one tm;;
let define_general_clauses cls = fast_clauses cls;;

let define_general_cheat tm = fast_one tm;;
let define_general_cheat_clauses cls = fast_clauses cls;;

let define_shaped shape tm = fast_one tm;;
let define_shaped_clauses shape cls = fast_clauses cls;;

let assume_definition why tm = fast_one tm;;
let assume_definition_clauses why cls = fast_clauses cls;;

let define_rec tm = fast_pair_one tm;;
let define_rec_clauses cls = fast_pair cls;;

let define_wf rel tm = fast_pair_one tm;;
let define_wf_clauses rel cls = fast_pair cls;;

let define_wf_cheat rel tm = fast_pair_one tm;;
let define_wf_cheat_clauses rel cls = fast_pair cls;;

let define_wf_tac rel tac tm = fast_pair_one tm;;
let define_wf_tac_clauses rel tac cls = fast_pair cls;;

let define_guess tm = fast_pair_one tm;;
let define_guess_clauses cls = fast_pair cls;;

let define_guess_cheat tm = fast_pair_one tm;;
let define_guess_cheat_clauses cls = fast_pair cls;;

let define_shaped_rec shape tm = fast_pair_one tm;;
let define_shaped_rec_clauses shape cls = fast_pair cls;;

let define_shaped_rec_cheat shape tm = fast_pair_one tm;;
let define_shaped_rec_cheat_clauses shape cls = fast_pair cls;;

let define_shaped_rec_tac shape tac tm = fast_pair_one tm;;
let define_shaped_rec_tac_clauses shape tac cls = fast_pair cls;;

let define_shaped_wf shape rel tm = fast_pair_one tm;;
let define_shaped_wf_clauses shape rel cls = fast_pair cls;;

let define_shaped_wf_cheat shape rel tm = fast_pair_one tm;;
let define_shaped_wf_cheat_clauses shape rel cls = fast_pair cls;;

let define_shaped_wf_tac shape rel tac tm = fast_pair_one tm;;
let define_shaped_wf_tac_clauses shape rel tac cls = fast_pair cls;;

let assume_definition_rec why tm = fast_pair_one tm;;
let assume_definition_rec_clauses why cls = fast_pair cls;;

let prove (tm,tac) = mk_thm([],tm);;

(* the datatypes a real construction recorded; without the file
   every datatype is built for real, which is what an abstract did
   before this *)

let _ =
  try cake_dt_read
        "/home/freek/claude/hol-light/cakeml/ml/lib/datatypes.txt"
  with Sys_error _ -> ();;

print_string
  ("\n*** ABSTRACT: nothing below this line is proved ***\n" ^
   "*** " ^ string_of_int (Hashtbl.length cake_dt_table) ^
   " datatypes are assumed and not built ***\n\n");;
