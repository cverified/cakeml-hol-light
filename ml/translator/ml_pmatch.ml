(* ======================================================== *)
(*  ml_pmatch: ported from HOL4's
    translator/ml_pmatchScript.sml
    A definition theory, with 5 definitions and 10 theorems.  Needed
    by decProg.ml, ml_hol_kernel_funsProg.ml, ml_monad_translator.ml
    and ml_monad_translatorBase.ml.  *)
(* ======================================================== *)

(*
  Theory support for translation of deeply-embedded (PMATCH-based)
  pattern-matches occurring in HOL functions.
*)

needs "characteristic/cfHeapsBase.ml";;
needs "lib/patternMatches.ml";;
needs "semantics/ast.ml";;
needs "semantics/evaluate.ml";;
needs "semantics/namespace.ml";;
needs "semantics/proofs/evaluateProps.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "translator/ml_prog.ml";;
needs "translator/ml_translator.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "ml_pmatch"
  ["ast"; "evaluate"; "evaluateProps"; "ml_prog"; "ml_translator";
   "semanticPrimitives"; "semanticPrimitivesProps"];;

(* this file reads the name of a record field as a variable and
   needs the accessors of that field as well, so only these
   pairs come out of the interface *)
let _ = hide_overloads
  ["vars","vars"];;
(* HOL4 ancestors outside the port: integer *)

(* HOL4 ml_pmatchScript.sml:13: ML code, not ported *)

let EvalPatRel_def = new_definition
  `EvalPatRel env a p pat <=>
     (!x av. a x av ==> (!refs.
       evaluate_evaluate_match (semanticPrimitives_state_refs_fupd (K refs)
         ml_translator_empty_state) env av
         [(p,ast_Con NONE [])] ARB =
         (semanticPrimitives_state_refs_fupd (K refs)
           ml_translator_empty_state,
          (if ?vars'. pat vars' = x then Rval ([semanticPrimitives_Conv
            NONE []]) else Rerr (Rraise ARB)))))`;;

(*
  This is very similar to pmatch_list (see theorems proving connection below).
  It omits some checks, which are unnecessary for the translator but needed in
  the semantics; it thereby makes the translator's automation easier.
*)
let ml_pmatch_Pmatch_def,ml_pmatch_Pmatch_ind = define_guess
  `Pmatch env refs x3 x4 =
     match (x3,x4) with
       ([],[]) -> SOME env
     | (CONS p1 (CONS p2 ps),CONS v1 (CONS v2 vs)) ->
        (match Pmatch env refs [p1] [v1] with NONE -> NONE
        | SOME env' -> Pmatch env' refs (CONS p2 ps) (CONS v2 vs))
     | ([ast_Pany],[v]) -> SOME env
     | ([ast_Pvar x],[v]) -> SOME (ml_prog_write x v env)
     | ([ast_Pas p x],[v]) ->
        Pmatch (ml_prog_write x v env) refs [p] [v]
     | ([ast_Plit l],[semanticPrimitives_Litv l']) ->
        if l = l' then SOME env else NONE
     | ([ast_Pcon (SOME n) ps],[semanticPrimitives_Conv (SOME (t')) vs]) ->
        (match nsLookup (sem_env_c env) n with NONE -> NONE
        | SOME (l,t) ->
          if LENGTH ps = l /\ LENGTH vs = l /\
             same_ctor t t' /\
             same_type t t' then Pmatch env refs ps vs
          else NONE)
     | ([ast_Pcon NONE ps],[semanticPrimitives_Conv NONE vs]) ->
        if LENGTH ps = LENGTH vs then
          Pmatch env refs ps vs
        else NONE
     | ([ast_Pref p],[semanticPrimitives_Loc b lnum]) ->
      (match store_lookup lnum refs with SOME (semanticPrimitives_Refv v) ->
        Pmatch env refs [p] [v]
      | _ -> NONE)
     | ([ast_Ptannot p t],[v]) -> Pmatch env refs [p] [v]
     | (_,_) -> NONE`;;

(* HOL4 ml_pmatchScript.sml:62: ML code, not ported *)

let EvalPatBind_def = new_definition
  `EvalPatBind env a p pat vars' env2 <=>
     (?x av refs.
       a x av /\
       (Pmatch env refs [p] [av] = SOME env2) /\
       (pat vars' = x))`;;

(* Pmatch_cons *)
let pmatch_cons = prove
 (`!ps vs.
      Pmatch env refs (CONS p ps) (CONS v vs) =
      match Pmatch env refs [p] [v] with NONE -> NONE
      | SOME env' -> Pmatch env' refs ps vs`,
  CHEAT_TAC);;

(* HOL4 ml_pmatchScript.sml:83-136: a theorem that HOL4 states as the value
   of an ML expression: pmatch_imp_Pmatch *)

let Pmatch_SOME_const = prove
 (`!env refs ps vs env'.
      Pmatch env refs ps vs = SOME env' ==> sem_env_c
      env' = sem_env_c env`,
  CHEAT_TAC);;

let pmatch_PMATCH_ROW_COND_No_match = prove
 (`EvalPatRel env a p pat /\
    (!vars'. ~(PMATCH_ROW_COND pat (K T) xv vars')) /\
    a xv res ==>
    semanticPrimitives_pmatch (sem_env_c env) refs p res [] = No_match`,
  CHEAT_TAC);;

let pmatch_PMATCH_ROW_COND_Match = prove
 (`EvalPatRel env a p pat /\
    PMATCH_ROW_COND pat (K T) xv vars /\
    a xv res ==> (?env2. semanticPrimitives_pmatch (sem_env_c env) refs p
      res [] = Match env2)`,
  CHEAT_TAC);;

let pmatch_no_type_error_def = new_definition
  `pmatch_no_type_error envC a p <=>
     ALL_DISTINCT (ast_pat_bindings p) /\
     (!x v refs.
        a x v ==> ~(semanticPrimitives_pmatch envC refs p v [] =
          Match_type_error))`;;

let pmatch_all_no_type_error_def = define_cases
  `(pmatch_all_no_type_error envC a [] = T) /\
   (pmatch_all_no_type_error envC a (CONS (p,e) rows) =
      (pmatch_no_type_error envC a p /\
       pmatch_all_no_type_error envC a rows))`;;

let Eval_PMATCH_NIL = prove
 (`!b x xv a.
      ast_Eval env x (a xv) ==>
      pmatch_all_no_type_error (sem_env_c env) a ([]:(ast_pat#ast_exp) list)
        /\
      (CONTAINER F ==>
       ast_Eval env (ast_Mat x []) (b (PMATCH xv [])))`,
  CHEAT_TAC);;

let pmatch_all_no_type_error_IMP_can_pmatch_all = prove
 (`pmatch_all_no_type_error (sem_env_c env) a ys /\ a x v ==>
   can_pmatch_all (sem_env_c env) refs (MAP FST ys) v`,
  CHEAT_TAC);;

let Eval_PMATCH = prove
 (`!b a x xv.
      ALL_DISTINCT (ast_pat_bindings p) ==>
      (!v1 v2. pat v1 = pat v2 ==> v1 = v2) ==>
      ast_Eval env x (a xv) ==>
      (p1 xv ==> ast_Eval env (ast_Mat x ys) (b (PMATCH xv yrs))) ==>
      EvalPatRel env a p pat ==>
      (!env2 vars'.
        EvalPatBind env a p pat vars' env2 /\ p2 vars' ==>
        ast_Eval env2 e (b (res vars'))) ==>
      pmatch_all_no_type_error (sem_env_c env) a ys ==>
      pmatch_all_no_type_error (sem_env_c env) a (CONS (p,e) ys) /\
      ((!vars'. CONTAINER (PMATCH_ROW_COND pat (K T) xv vars') ==> p2 vars')
        /\
       ((!vars'. ~(CONTAINER (PMATCH_ROW_COND pat (K T) xv vars'))) ==> p1
         xv) ==>
       ast_Eval env (ast_Mat x (CONS (p,e) ys)) (b (PMATCH xv (CONS
         (PMATCH_ROW pat (K T) res) yrs))))`,
  CHEAT_TAC);;

let PMATCH_option_case_rwt = prove
 (`((match x with NONE -> NONE
      | SOME (y1,y2) -> P y1 y2) = SOME env2) <=>
    (?y1 y2. (x = SOME (y1,y2)) /\ (P y1 y2 = SOME env2))`,
  CHEAT_TAC);;

let PMATCH_SIMP = prove
 (`((!vars'. ~(CONTAINER (vars' = x))) = F) /\
    ((!vars'. ~(CONTAINER (x = vars'))) = F) /\
    ((!vars'. ~(vars' = x)) = F) /\
    ((!vars'. ~(x = vars')) = F)`,
  CHEAT_TAC);;

(* and the interface *)
let _ = unhide_overloads ();;
