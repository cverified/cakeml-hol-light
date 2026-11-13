(* ================================================================== *)
(* Making a definition.                                               *)
(*                                                                    *)
(* A file of the port says how each of its definitions is made, and   *)
(* nothing is searched for while it loads.  A reader tells the ways   *)
(* apart at the call site:                                            *)
(*                                                                    *)
(*   new_definition      HOL Light's own: no recursion, one clause    *)
(*   define_cases        several clauses and no recursion, by the     *)
(*                       recursion theorem of the type matched on     *)
(*   define_general      a definition HOL Light's own machinery for   *)
(*                       patterns makes, and a family that does not   *)
(*                       recurse, which is a definition each          *)
(*   define_rec          structural recursion, by that same theorem   *)
(*   define_wf <rel>     recursion with the relation written out,     *)
(*                       which is what HOL4's Termination gives       *)
(*   define_guess        recursion whose termination argument HOL     *)
(*                       Light finds by itself                        *)
(*   define_shaped <w>   clauses that HOL Light cannot take as they   *)
(*                       stand; the word says which rewriting of      *)
(*                       them the definition goes through             *)
(*   assume_definition   the port cannot make the definition and      *)
(*                       assumes it                                   *)
(*                                                                    *)
(* and four endings say the rest: _mutual for a family of functions   *)
(* that recurse through one another, _cheat where the termination is  *)
(* assumed rather than proved, _tac where the file gives the tactic   *)
(* that discharges it, and _shaped before them all.  Three of the     *)
(* rewritings hand what comes out back to a way of making a           *)
(* definition, and the word says that one too, after a ">":           *)
(* "sing>nested" is "read the clauses as a function of one element,   *)
(* and make what comes out by the nested way".                        *)
(*                                                                    *)
(* Each of the recursive ones gives the induction theorem with the    *)
(* definition, as HOL4 does, so a file writes                         *)
(*                                                                    *)
(*   let foo_def,foo_ind = define_wf `MEASURE FST`                    *)
(*     [`foo ... = ...`; ...];;                                       *)
(*                                                                    *)
(* and the proofs have foo_ind to do induction with.                  *)
(*                                                                    *)
(* The ones whose name says cheat or assume, and those alone, add an  *)
(* axiom; ml/CHEATS.md lists them and length (axioms ()) counts them. *)
(* ================================================================== *)

(* the clauses are written as separate terms because HOL4
   typechecks each of them on its own *)

let definition_of_clauses cls =
  match cls with
    [tm] -> (try cake_conj_list cls with Failure _ -> tm)
  | _ -> cake_conj_list cls;;

(* the name a definition goes by in what it reports *)

let definition_name tm =
  let _,f,_,_ = hd (definition_cases tm) in
  if is_var f then fst(dest_var f) else fst(dest_const f);;

(* the measure of a definition that recurses on the arguments it
   matches on, which the induction theorem of a definition made by
   the recursion theorem of its type needs: computed from the
   clauses, not looked for *)

let structural_measure tm = hd (candidate_measures tm);;

(* ------------------------------------------------------------------ *)
(* The definition itself.                                             *)
(* ------------------------------------------------------------------ *)

(* the shapes and the guess ask HOL Light's machinery for the
   conditions and have no relation to discharge them with, so a
   cheat for those goes through the tactic that define.ml keeps *)

let with_cheat f x =
  let old = !the_cheat_tac in
  the_cheat_tac := Some CHEAT_TAC;
  let r = (try f x with e -> (the_cheat_tac := old; raise e)) in
  the_cheat_tac := old; r;;

let noted ths =
  let th = end_itlist CONJ ths in
  cake_note_def th; note_dest_fact th; th;;

let definition_made wfs tm =
  let fs = definition_heads tm in
  noted (fst (if length fs = 1 then define_single wfs tm
                               else define_mutual wfs tm));;

(* HOL4 writes clauses that HOL Light's recursion machinery does
   not digest: a recursion through a MAP, a pattern inside a
   pattern, a function of one element of a list, a condition that
   is a boolean of the recursive calls.  ml/lib/define.ml has a
   rewriting of the clauses for each of those, and the word says
   which one this definition goes through.

   Three of the rewritings hand what comes out back to a way of
   making a definition, and which way that is is a second choice:
   the word says both, separated by a ">", so that "sing>nested"
   is "read the clauses as a function of one element, and make
   what comes out by the nested way".  Nothing is searched for
   either way. *)

let shape_head shape =
  try let i = String.index shape '>' in
      String.sub shape 0 i,
      String.sub shape (i + 1) (String.length shape - i - 1)
  with Not_found -> shape,"";;

let rec made_by shape wfs tm =
  let head,rest = shape_head shape in
  let plain tm =
    if length (definition_heads tm) = 1 then define_single wfs tm
    else define_mutual wfs tm in
  let inner tm =
    if rest = "" then plain tm else made_by rest wfs tm in
  match head with
    "" | "new_definition" -> [new_definition tm],TRUTH
  | "define_single" | "general" -> plain tm
  | "prim_rec" | "new_recursive_definition" -> define_prim_rec tm
  | "nested" -> define_nested tm
  | "maplist" -> define_maplist inner tm
  | "cond_bool" -> define_cond_bool inner tm
  | "sing" -> define_sing inner tm
  | "cases" -> define_compiled_cases tm
  | "match" -> define_match_clauses tm
  | "lift_if" -> define_lift_if inner tm
  | "measure" | "guess" -> plain tm
  | _ -> failwith ("define_shaped: no shape " ^ head);;

let shaped_made shape wfs tm = noted (fst (made_by shape wfs tm));;

(* ------------------------------------------------------------------ *)
(* The induction theorem.                                             *)
(* ------------------------------------------------------------------ *)

(* where the termination of the definition was assumed, the
   conditions of the induction cannot be proved either, and then it
   is assumed as well -- and counted, like every other assumption.
   One axiom for it, and not one for every condition. *)

let assumed_induction tm why =
  let name = definition_name tm in
  the_cheat_why := (name ^ "_ind",why) :: !the_cheat_why;
  (* the statement is read off the clauses, and there are shapes
     it cannot be read off (a family that recurses through itself,
     ISSUES.md).  Then the file says so and binds nothing, rather
     than failing over it. *)
  try let ind = induction_statement tm in
      the_cheats := (name ^ "_ind") :: !the_cheats;
      print_string ("\n" ^ name ^ "_ind ASSUMED (" ^ why ^ ")\n");
      flush stdout;
      new_axiom ind
  with Failure e ->
    (print_string ("\n" ^ name ^ "_ind NOT STATED (" ^ e ^ ")\n");
     flush stdout; TRUTH);;

(* an induction that will not go through must not hold up a run,
   so it has a budget of its own and is assumed when it runs out *)

let cake_induction_timeout = ref 10;;

let induction_for rel tac th =
  let old = !cake_timeout in
  cake_timeout := !cake_induction_timeout;
  let fin () = cake_timeout := old in
  try let r = with_timeout (prove_induction_wf rel tac) (concl th) in
      fin (); r
  with Failure e ->
         (fin (); assumed_induction (concl th) ("induction: " ^ e))
     | Cake_timeout ->
         (fin (); assumed_induction (concl th) "induction: timeout");;

(* the measure of a definition that states none is computed from
   its clauses, and that can fail where the clauses are of a shape
   candidate_measures does not read.  It is the induction theorem
   that wants it and not the definition, so a failure there costs
   the theorem and not the file. *)

let induction_by_measure tac th tm =
  try induction_for (structural_measure tm) tac th
  with Failure e -> assumed_induction (concl th) ("measure: " ^ e);;

(* ------------------------------------------------------------------ *)
(* The ways.                                                          *)
(* ------------------------------------------------------------------ *)

(* several clauses and no recursion *)

let define_cases cls = noted (fst (define_prim_rec
                                     (definition_of_clauses cls)));;

(* several clauses and no recursion that neither new_definition
   nor the recursion theorem of the type takes: HOL Light's own
   machinery for a definition by cases *)

(* a family that does not recurse is a definition each, which is
   what the chain of strategies did with one and much faster than
   one mutual definition of them all *)

let general_made tm =
  let fs = definition_heads tm in
  if length fs = 1 then noted (fst (define_single [] tm)) else
  let clause_of f =
    filter (fun cl ->
              fst(strip_comb(lhs(snd(strip_forall cl)))) = f)
           (conjuncts(snd(strip_forall tm))) in
  noted (itlist (fun f l ->
                   fst (define_single [] (list_mk_conj
                          (clause_of f))) @ l)
                fs []);;

let define_general cls = general_made (definition_of_clauses cls);;

let define_general_cheat cls =
  with_cheat general_made (definition_of_clauses cls);;

(* structural recursion: the same theorem makes it, and the
   induction goes by the measure of what is matched on *)

let define_rec cls =
  let tm = definition_of_clauses cls in
  let th = noted (fst (define_prim_rec tm)) in
  th,induction_by_measure TERM_TAC th tm;;

(* recursion with the relation written out *)

let define_wf_tac rel tac cls =
  let th = definition_made [(rel,tac)] (definition_of_clauses cls) in
  th,induction_for rel tac th;;

let define_wf rel cls = define_wf_tac rel TERM_TAC cls;;

let define_wf_cheat rel cls =
  let th = definition_made [(rel,CHEAT_TAC)]
             (definition_of_clauses cls) in
  th,assumed_induction (concl th)
       "the termination of the definition is assumed";;

(* recursion whose termination argument HOL Light finds by itself *)

let define_guess cls =
  let tm = definition_of_clauses cls in
  let th = definition_made [] tm in
  th,induction_by_measure TERM_TAC th tm;;

let define_guess_cheat cls =
  let tm = definition_of_clauses cls in
  let th = with_cheat (definition_made []) tm in
  th,assumed_induction (concl th)
       "the termination of the definition is assumed";;

(* clauses of a shape HOL Light cannot take as they stand *)

let define_shaped_wf_tac shape rel tac cls =
  let th = shaped_made shape [(rel,tac)]
             (definition_of_clauses cls) in
  th,induction_for rel tac th;;

let define_shaped_wf shape rel cls =
  define_shaped_wf_tac shape rel TERM_TAC cls;;

let define_shaped_wf_cheat shape rel cls =
  let th = shaped_made shape [(rel,CHEAT_TAC)]
             (definition_of_clauses cls) in
  th,assumed_induction (concl th)
       "the termination of the definition is assumed";;

let define_shaped_rec_tac shape tac cls =
  let tm = definition_of_clauses cls in
  let th = shaped_made shape [] tm in
  th,induction_by_measure tac th tm;;

let define_shaped_rec shape cls =
  define_shaped_rec_tac shape TERM_TAC cls;;

let define_shaped_rec_cheat shape cls =
  let tm = definition_of_clauses cls in
  let th = with_cheat (shaped_made shape []) tm in
  th,assumed_induction (concl th)
       "the termination of the definition is assumed";;

let define_shaped shape cls =
  shaped_made shape [] (definition_of_clauses cls);;

(* a family of functions that recurse through one another.  HOL4
   gives such a definition a mutual induction theorem; the port
   does not make one yet (ISSUES.md), so these give the definition
   alone and claim nothing else. *)

let define_mutual_wf_tac rel tac cls =
  definition_made [(rel,tac)] (definition_of_clauses cls);;

let define_mutual_wf rel cls = define_mutual_wf_tac rel TERM_TAC cls;;

let define_mutual_wf_cheat rel cls =
  define_mutual_wf_tac rel CHEAT_TAC cls;;

let define_mutual_rec cls =
  noted (fst (define_prim_rec (definition_of_clauses cls)));;

let define_mutual_guess cls =
  definition_made [] (definition_of_clauses cls);;

let define_mutual_guess_cheat cls =
  with_cheat (definition_made []) (definition_of_clauses cls);;

(* the definition the port cannot make at all *)

let assume_definition why cls =
  cheat_why := why;
  let th = cake_cheat (definition_of_clauses cls) in
  cake_note_def th; th;;

let assume_definition_rec why cls =
  let th = assume_definition why cls in
  th,assumed_induction (concl th) why;;

(* and a family whose clauses need a rewriting as well *)

let define_mutual_shaped_wf_tac shape rel tac cls =
  shaped_made shape [(rel,tac)] (definition_of_clauses cls);;

let define_mutual_shaped_wf shape rel cls =
  define_mutual_shaped_wf_tac shape rel TERM_TAC cls;;

let define_mutual_shaped_wf_cheat shape rel cls =
  shaped_made shape [(rel,CHEAT_TAC)] (definition_of_clauses cls);;

let define_mutual_shaped_rec shape cls =
  shaped_made shape [] (definition_of_clauses cls);;

let define_mutual_shaped_rec_cheat shape cls =
  with_cheat (shaped_made shape []) (definition_of_clauses cls);;

(* ------------------------------------------------------------------ *)
(* Which way a definition needs.                                      *)
(* ------------------------------------------------------------------ *)

(* A file says how each of its definitions is made, so writing a
   new one means knowing which way it takes.  The chain of
   strategies of ml/lib/define.ml is what finds out, and this runs
   it and says what it found, as the word and the relation that a
   call site would write.

   It makes the definition as a side effect, so it belongs in a
   session of its own and not in a file; no file of the port calls
   it.  tools/bin/strategies harvests the same thing from a whole
   run. *)

let find_definition_way cls =
  cake_begin ();
  let th = cake_define (definition_of_clauses cls) in
  ignore th;
  (if !the_strategy = "" then "assume_definition" else !the_strategy),
  !the_term_cheat,
  (* in the form a file writes it: a redex left in the measure is
     reduced by the proof and not by the term a goal is built
     from, so it is reduced here *)
  (try string_of_term (beta_normalize (parse_term (!the_relation)))
   with Failure _ | Noparse -> !the_relation);;
