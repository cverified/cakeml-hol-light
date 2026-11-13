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

(* the names of the family that is being defined.  A rewriting of
   the clauses has to invent a name for a function it introduces,
   and the one name it may not take is one of these: presLang
   defines flat_to_display and the flat_to_display_list that the
   map of it would be called, and by the time the rewriting gets
   there the clauses of that one have been taken out of the term
   (ml/lib/define.ml, the_defining) *)

let defining tm =
  the_defining := map (fst o dest_var) (definition_heads tm);;

(* HOL Light's own new_definition, noted like every other way.  A
   tactic of ml/lib/tactics.ml is written before the port and
   asks for a definition by the name of its constant, which is
   the one thing a file cannot hand it; the ways that this file
   has all note what they make, and the way that is HOL Light's
   own has to note it too, or the tactic finds nothing *)

let new_definition tm = noted [new_definition tm];;

let definition_made wfs tm =
  defining tm;
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

let shaped_made shape wfs tm =
  defining tm; noted (fst (made_by shape wfs tm));;

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

let define_cases cls =
  let tm = definition_of_clauses cls in
  defining tm; noted (fst (define_prim_rec tm));;

(* several clauses and no recursion that neither new_definition
   nor the recursion theorem of the type takes: HOL Light's own
   machinery for a definition by cases *)

(* a family that does not recurse is a definition each, which is
   what the chain of strategies did with one and much faster than
   one mutual definition of them all *)

let general_made tm =
  defining tm;
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
  defining tm;
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

(* a family of functions that recurse through one another.  The
   way is the same one as for a definition of one function: what
   makes the definition is the same (ml/lib/define.ml makes a
   family one function on the sum of the arguments of its members
   and the members of it by projection), and the induction
   theorem is read off the clauses and proved the same way, with
   a predicate for each member.  The names are here because a
   file that says define_mutual_wf says something a reader wants
   to know, and nothing searches for what kind of definition it
   is at the call site. *)

let define_mutual_wf_tac = define_wf_tac;;

let define_mutual_wf = define_wf;;

let define_mutual_wf_cheat = define_wf_cheat;;

let define_mutual_rec = define_rec;;

let define_mutual_guess = define_guess;;

let define_mutual_guess_cheat = define_guess_cheat;;

(* the definition the port cannot make at all *)

let assume_definition why cls =
  cheat_why := why;
  let th = cake_cheat (definition_of_clauses cls) in
  cake_note_def th; th;;

let assume_definition_rec why cls =
  let th = assume_definition why cls in
  th,assumed_induction (concl th) why;;

(* and a family whose clauses need a rewriting as well *)

let define_mutual_shaped_wf_tac = define_shaped_wf_tac;;

let define_mutual_shaped_wf = define_shaped_wf;;

let define_mutual_shaped_wf_cheat = define_shaped_wf_cheat;;

let define_mutual_shaped_rec_tac = define_shaped_rec_tac;;

let define_mutual_shaped_rec = define_shaped_rec;;

let define_mutual_shaped_rec_cheat = define_shaped_rec_cheat;;

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

(* the same, as the line that a file would write for it, which is
   what there is to copy into one.  The clauses stand for
   themselves. *)

let the_shapes =
  ["nested"; "maplist"; "cond_bool"; "sing"; "cases"; "match";
   "lift_if"];;

let definition_way_call cls =
  let tm = definition_of_clauses cls in
  let name = definition_name tm in
  let fs = definition_functions (definition_cases tm) in
  let recursive = is_recursive tm in
  let mutual = length fs > 1 in
  let way,cheat,rel = find_definition_way cls in
  let head = fst (shape_head way) in
  let shaped = mem head the_shapes in
  let how,args =
    if way = "assume_definition" then
      (if recursive then "assume_definition_rec" else
       "assume_definition"),"\"why\"\n  "
    else if not recursive then
      (if shaped then "define_shaped","\"" ^ way ^ "\"\n  "
       else if head = "new_definition" then "new_definition",""
       else if head = "define_single" || head = "general" then
         ("define_general" ^ (if cheat then "_cheat" else "")),""
       else "define_cases","")
    else
      let kind,args =
        if shaped then
          (if rel = "" then "_rec","\"" ^ way ^ "\"\n  "
           else "_wf","\"" ^ way ^ "\"\n  `" ^ rel ^ "`\n  ")
        else if head = "prim_rec" then "_rec",""
        else if rel <> "" then "_wf","`" ^ rel ^ "`\n  "
        else "_guess","" in
      let suffix =
        if kind = "_rec" && not shaped then ""
        else if cheat then "_cheat" else "" in
      ("define" ^ (if mutual then "_mutual" else "") ^
       (if shaped then "_shaped" else "") ^ kind ^ suffix),args in
  let binding =
    if recursive && how <> "assume_definition"
    then name ^ "_def," ^ name ^ "_ind" else name ^ "_def" in
  "let " ^ binding ^ " = " ^ how ^ "\n  " ^ args ^
  (if how = "new_definition" then "`...`;;" else "[`...`];;");;

let print_definition_way cls =
  print_string ("\n" ^ definition_way_call cls ^ "\n");
  flush stdout;;
