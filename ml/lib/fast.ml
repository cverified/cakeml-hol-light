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

let fast_definition tm =
  let fs = definition_heads tm in
  let sub = map (fun v -> fast_constant v,v) fs in
  mk_thm([],subst (filter (fun (c,v) -> c <> v) sub) tm);;

let fast_clauses cls = fast_definition (definition_of_clauses cls);;

let fast_induction th = mk_thm([],induction_statement (concl th));;

(* the ways of making a definition, and the proofs: the
   ones that give a pair give the induction theorem too *)

let new_definition tm = fast_definition tm;;

let define_cases cls = fast_clauses cls;;

let define_general cls = fast_clauses cls;;

let define_general_cheat cls = fast_clauses cls;;

let define_shaped shape cls = fast_clauses cls;;

let define_mutual_rec cls = fast_clauses cls;;

let define_mutual_guess cls = fast_clauses cls;;

let define_mutual_guess_cheat cls = fast_clauses cls;;

let define_mutual_wf rel cls = fast_clauses cls;;

let define_mutual_wf_cheat rel cls = fast_clauses cls;;

let define_mutual_wf_tac rel tac cls = fast_clauses cls;;

let define_mutual_shaped_rec shape cls = fast_clauses cls;;

let define_mutual_shaped_rec_cheat shape cls = fast_clauses cls;;

let define_mutual_shaped_wf shape rel cls = fast_clauses cls;;

let define_mutual_shaped_wf_cheat shape rel cls = fast_clauses cls;;

let assume_definition why cls = fast_clauses cls;;


let define_rec cls = fast_pair cls;;

let define_wf rel cls = fast_pair cls;;

let define_wf_cheat rel cls = fast_pair cls;;

let define_wf_tac rel tac cls = fast_pair cls;;

let define_guess cls = fast_pair cls;;

let define_guess_cheat cls = fast_pair cls;;

let define_shaped_rec shape cls = fast_pair cls;;

let define_shaped_rec_cheat shape cls = fast_pair cls;;

let define_shaped_rec_tac shape tac cls = fast_pair cls;;

let define_shaped_wf shape rel cls = fast_pair cls;;

let define_shaped_wf_cheat shape rel cls = fast_pair cls;;

let define_shaped_wf_tac shape rel tac cls = fast_pair cls;;

let assume_definition_rec why cls = fast_pair cls;;

let prove (tm,tac) = mk_thm([],tm);;

print_string
  "\n*** ABSTRACT: nothing below this line is proved ***\n\n";;
