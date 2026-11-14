(* ================================================================== *)
(*  A declared set of simplification rules.                           *)
(*                                                                    *)
(*  HOL Light has the machinery already: `simpset` is a term net with *)
(*  a prover attached (simp.ml), `ss_of_thms` *extends* one, and      *)
(*  SIMPLIFY_CONV runs it.  What it has not got is a set you declare  *)
(*  theorems into as you go, the way Isabelle's [simp] and Lean's     *)
(*  @[simp] work.  `extend_basic_rewrites` is the nearest thing, and  *)
(*  it is the set REWRITE_TAC silently uses everywhere, so adding a   *)
(*  rule to it changes every proof in the session.                    *)
(*                                                                    *)
(*    add_simp th        declare one                                  *)
(*    simps ()           what has been declared                       *)
(*    SIMPS_TAC thl      simplify with the declared set and thl       *)
(*    ASM_SIMPS_TAC thl  and with the assumptions                     *)
(*                                                                    *)
(*  WHY IT SCALES.  The cost of simplifying is a net lookup, which    *)
(*  does not care how big the net is; the cost that does grow is      *)
(*  *building* the net.  SIMP_TAC thl builds one from thl on every    *)
(*  call, so a thousand rules passed as a list would be a thousand    *)
(*  net insertions per call.  Here the net is built once and          *)
(*  `ss_of_thms` adds to it, so declaring a rule costs one insertion  *)
(*  ever and using the set costs nothing.                             *)
(*                                                                    *)
(*  The set is global, as `basic_rewrites` is.  Inside the load of a  *)
(*  development that is deterministic -- the files load in one order  *)
(*  -- but in a session where you have loaded something extra by      *)
(*  hand, a proof sees that too.  `simps ()` is there so a proof can  *)
(*  say what it saw.                                                  *)
(*                                                                    *)
(*  This file is about HOL Light and nothing else.                    *)
(* ================================================================== *)

let add_simp,add_simps,del_simp,simps,simp_ss =
  (* the declared theorems, newest first, and the net built from them *)
  let declared = ref ([]:thm list)
  and the_ss = ref (basic_ss []) in
  let add_simps thl =
    declared := thl @ (!declared);
    the_ss := ss_of_thms thl (!the_ss)
  and rebuild () =
    the_ss := ss_of_thms (rev (!declared)) (basic_ss []) in
  let add_simp th = add_simps [th]
  (* taking one out means building the net again: a net does not
     forget.  It is here for the rule that turned out to loop, not
     for everyday use *)
  and del_simp th =
    declared := filter (fun t -> not (equals_thm t th)) (!declared);
    rebuild ()
  and simps () = rev (!declared)
  and simp_ss () = !the_ss in
  add_simp,add_simps,del_simp,simps,simp_ss;;

let SIMPS_CONV thl = SIMPLIFY_CONV (simp_ss ()) thl;;

let SIMPS_RULE thl = CONV_RULE (SIMPS_CONV thl);;

let SIMPS_TAC thl = CONV_TAC (SIMPS_CONV thl);;

let ASM_SIMPS_TAC = ASM SIMPS_TAC;;

(* the datatype rules that a proof about a datatype always wants:
   the constructors are distinct and injective.  HOL Light proves
   these when the type is made and keeps them in its stores, so
   declaring them is a lookup *)

let add_type_simps ty =
  add_simps ((try [distinctness ty] with Failure _ -> []) @
             (try [injectivity ty] with Failure _ -> []));;
