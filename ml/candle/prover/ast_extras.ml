(* ======================================================== *)
(*  ast_extras: ported from HOL4's
    candle/prover/ast_extrasScript.sml
    A definition theory, with 5 definitions and 4 theorems.  Needed
    by 10 files of the port.  *)
(* ======================================================== *)

(*
  Useful predicates on the CakeML ast.
 *)

needs "semantics/ast.ml";;
needs "semantics/namespace.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "ast_extras"
  ["ast"; "semanticPrimitivesProps"];;

(* the termination relation that HOL4 gives is
     MEASURE (ast_exp_size o SND)
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 ast_extrasScript.sml:54-60: the tactic that proves the termination *)
let ast_extras_every_exp_def,ast_extras_every_exp_ind = define_guess
  `ast_extras_every_exp f e =
     match e with
       ast_Raise e ->
        f (ast_Raise e) /\ ast_extras_every_exp f e
     | ast_Handle e pes ->
        f (ast_Handle e pes) /\
        ast_extras_every_exp f e /\
        ALL (ast_extras_every_exp f) (MAP SND pes)
     | ast_Con ts es ->
        f (ast_Con ts es) /\
        ALL (ast_extras_every_exp f) es
     | ast_Fun n e ->
        f (ast_Fun n e) /\
        ast_extras_every_exp f e
     | ast_App op es ->
        f (ast_App op es) /\
        ALL (ast_extras_every_exp f) es
     | ast_Log lop e1 e2 ->
        f (ast_Log lop e1 e2) /\
        ast_extras_every_exp f e1 /\
        ast_extras_every_exp f e2
     | ast_If e1 e2 e3 ->
       f (ast_If e1 e2 e3) /\
       ast_extras_every_exp f e1 /\
       ast_extras_every_exp f e2 /\
       ast_extras_every_exp f e3
     | ast_Mat e pes ->
       f (ast_Mat e pes) /\
       ast_extras_every_exp f e /\
       ALL (ast_extras_every_exp f) (MAP SND pes)
     | ast_Let n x e ->
       f (ast_Let n x e) /\
       ast_extras_every_exp f x /\
       ast_extras_every_exp f e
     | ast_Letrec funs e ->
       f (ast_Letrec funs e) /\
       ast_extras_every_exp f e /\
       ALL (ast_extras_every_exp f) (MAP (SND o SND) funs)
     | ast_Tannot e t ->
       f (ast_Tannot e t) /\
       ast_extras_every_exp f e
     | ast_Lannot e l ->
       f (ast_Lannot e l) /\
       ast_extras_every_exp f e
     | e -> f e`;;
add_simp ast_extras_every_exp_def;;

let every_exp_the = prove
 (`!P e. ast_extras_every_exp P e ==> P e`,
  CHEAT_TAC);;
add_simp every_exp_the;;

let every_exp_mono = prove
 (`!P e P'.
     (!e. P e ==> P' e) ==> ast_extras_every_exp P e ==>
       ast_extras_every_exp P' e`,
  CHEAT_TAC);;

let every_pat_def,every_pat_ind = define_guess
  `every_pat f p =
   match p with
     ast_Pcon opt ps -> (f (ast_Pcon opt ps) /\ ALL (every_pat f) ps)
   | ast_Pref p -> (f (ast_Pref p) /\ every_pat f p)
   | ast_Pas p s -> (f (ast_Pas p s) /\ every_pat f p)
   | ast_Ptannot p t -> (f (ast_Ptannot p t) /\ every_pat f p)
   | p -> f p`;;
add_simp every_pat_def;;

let every_pat_the = prove
 (`!P p. every_pat P p ==> P p`,
  CHEAT_TAC);;
add_simp every_pat_the;;

let every_pat_mono = prove
 (`!P p P'.
     (!p. P p ==> P' p) ==> every_pat P p ==> every_pat P' p`,
  CHEAT_TAC);;

let every_dec_def,every_dec_ind = define_guess
  `every_dec f d =
     match d with
       Dmod n ds ->
        f (Dmod n ds) /\
        ALL (every_dec f) ds
     | Dlocal ds1 ds2 ->
        f (Dlocal ds1 ds2) /\
        ALL (every_dec f) ds1 /\
        ALL (every_dec f) ds2
     | d ->
        f d`;;
add_simp every_dec_def;;

(* the clauses in two quotations: f is ((varN # varN # exp) list),
   (_#_#_)list and (_#_)list; l is lit and locs; n is ((modN , varN) id) and
   varN; pes is ((pat # exp) list) and (_#_)list, which one quotation cannot
   typecheck *)
let freevars_def,freevars_ind = define_guess_clauses
  [`(freevars (ast_Lit l) = {}) /\
    (freevars (ast_Raise e) = freevars e) /\
    (freevars (ast_Handle e pes) =
        (freevars e UNION UNIONS (set_of_list (MAP (\(p,e). freevars e DIFF
                              set_of_list (MAP Short (ast_pat_bindings
                                  p))) pes)))) /\
    (freevars (ast_Con cn es) = UNIONS (set_of_list (MAP freevars es))) /\
    (freevars (ast_Var n) = {n}) /\
    (freevars (ast_App op xs) = UNIONS (set_of_list (MAP freevars xs))) /\
    (freevars (ast_Log lop x y) = (freevars x UNION freevars y)) /\
    (freevars (ast_If x y z) = (freevars x UNION freevars y UNION freevars
    z)) /\
    (freevars (ast_Mat e pes) =
        (freevars e UNION UNIONS (set_of_list (MAP (\(p,e). freevars e DIFF
                              set_of_list (MAP Short (ast_pat_bindings
                                  p))) pes)))) /\
    (freevars (ast_Let opt x y) =
        (freevars x UNION
         (freevars y DIFF (match opt with SOME n -> {Short n} | _ ->
             {})))) /\
    (freevars (ast_Tannot x t) = freevars x)`;
   `(freevars (ast_Fun n e) = freevars e DIFF {Short n}) /\
    (freevars (ast_Letrec f x) =
        (UNIONS (set_of_list (MAP (\(fn,vn,x). freevars x DIFF
                              {Short fn,Short vn}) f)) UNION
         (freevars x DIFF set_of_list (MAP (Short o FST) f)))) /\
    (freevars (ast_Lannot x l) = freevars x)`];;
add_simp freevars_def;;

(* Partial applications of closures.
 *)

let do_partial_app_def = new_definition
  `do_partial_app f v =
     match f with
       semanticPrimitives_Closure env n (ast_Fun n' e) ->
         SOME (semanticPrimitives_Closure (sem_env_v_fupd (K (nsBind n v
           (sem_env_v env))) env) n' e)
     | _ -> NONE`;;

(* and the interface *)
let _ = unhide_overloads ();;
