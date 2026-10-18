(* ======================================================== *)
(*  flatProps: ported from HOL4's
    compiler/backend/semantics/flatPropsScript.sml
    A proof theory, with 16 definitions and 79 theorems.  Needed by
    backendProof.ml, flat_elimProof.ml, flat_patternProof.ml,
    flat_to_closProof.ml and source_to_flatProof.ml.  *)
(* ======================================================== *)

(*
  Properties about flatLang and its semantics
*)

needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/flatLang.ml";;
needs "compiler/backend/semantics/flatSem.ml";;
needs "lib/lprefix_lub.ml";;
needs "semantics/ast.ml";;
needs "semantics/evaluate.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/proofs/evaluateProps.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;
needs "semantics/semanticPrimitives.ml";;

let ctor_same_type_OPTREL = cake_theorem "ctor_same_type_OPTREL"
  (fun () ->
    `!c1 c2. ctor_same_type c1 c2 <=> OPTREL (inv_image (=) SND) c1 c2`)
  CHEAT_TAC;;

let pats_bindings_FLAT_MAP = cake_theorem "pats_bindings_FLAT_MAP"
  (fun () ->
    `!ps. pats_bindings ps = FLAT (REVERSE (MAP (\p. pat_bindings p)
  ps))`)
  CHEAT_TAC;;

(* HOL4 flatPropsScript.sml:31-33: the ML values that the definitions
   below antiquote *)

let pmatch_state = cake_theorem "pmatch_state"
  (fun () ->
    `(!(st:('c,'ffi)flatSem_state) p v l (st':('d,'ffi)flatSem_state)
  res.
       pmatch st p v l = res /\ state_refs
       st = state_refs st' ==> pmatch st' p v l = res) /\
     (!(st:('c,'ffi)flatSem_state) p vs l
       (st':('d,'ffi)flatSem_state) res.
       pmatch_list st p vs l = res /\ state_refs
       st = state_refs st' ==> pmatch_list st' p vs l = res)`)
  CHEAT_TAC;;

let flatProps_pmatch_extend = cake_theorem "pmatch_extend"
  (fun () ->
    `(!(s:('c,'ffi)flatSem_state) p v env env' env''.
      pmatch s p v env = Match env' ==>
      (?env''. env' = env'' ++ env /\ MAP FST env'' = pat_bindings
        p)) /\
     (!(s:('c,'ffi)flatSem_state) ps vs env env' env''.
      pmatch_list s ps vs env = Match env' ==>
      (?env''. env' = env'' ++ env /\ MAP FST env'' =
        pats_bindings ps))`)
  CHEAT_TAC;;

let pmatch_bindings = cake_theorem "pmatch_bindings"
  (fun () ->
    `(!(s:('c,'ffi)flatSem_state) p v env r.
        flatSem_pmatch s p v env = Match r ==>
        MAP FST r = pat_bindings p ++ MAP FST env) /\
     (!(s:('c,'ffi)flatSem_state) ps vs env r.
       flatSem_pmatch_list s ps vs env = Match r ==>
       MAP FST r = pats_bindings ps ++ MAP FST env)`)
  CHEAT_TAC;;

let pmatch_length = cake_theorem "pmatch_length"
  (fun () ->
    `!(s:('c,'ffi)flatSem_state) p v env r.
        flatSem_pmatch s p v env = Match r ==>
        LENGTH r = LENGTH (pat_bindings p) + LENGTH env`)
  CHEAT_TAC;;

let pmatch_any_match = cake_theorem "pmatch_any_match"
  (fun () ->
    `(!(s:('c,'ffi)flatSem_state) p v env env'. pmatch s p v env = Match
  env' ==>
        (!env. ?env'. pmatch s p v env = Match env')) /\
     (!(s:('c,'ffi)flatSem_state) ps vs env env'. pmatch_list s ps
       vs env = Match env' ==>
        (!env. ?env'. pmatch_list s ps vs env = Match env'))`)
  CHEAT_TAC;;

let pmatch_any_no_match = cake_theorem "pmatch_any_no_match"
  (fun () ->
    `(!(s:('c,'ffi)flatSem_state) p v env. pmatch s p v env = No_match
  ==>
         (!env. pmatch s p v env = No_match)) /\
      (!(s:('c,'ffi)flatSem_state) ps vs env. pmatch_list s ps vs
        env = No_match ==>
         (!env. pmatch_list s ps vs env = No_match))`)
  CHEAT_TAC;;

let pmatch_any_match_error = cake_theorem "pmatch_any_match_error"
  (fun () ->
    `(!(s:('c,'ffi)flatSem_state) p v env. pmatch s p v env =
  Match_type_error ==>
         (!env. pmatch s p v env = Match_type_error)) /\
     (!(s:('c,'ffi)flatSem_state) ps vs env. pmatch_list s ps vs
       env = Match_type_error ==>
         (!env. pmatch_list s ps vs env = Match_type_error))`)
  CHEAT_TAC;;

let pmatch_list_pairwise = cake_theorem "pmatch_list_pairwise"
  (fun () ->
    `!ps vs (s:('c,'ffi)flatSem_state) env env'.
        pmatch_list s ps vs env = Match env' ==>
        EVERY2 (\p v. !env. ?env'. pmatch s p v env = Match env')
          ps vs`)
  CHEAT_TAC;;

let pmatch_list_snoc_nil = cake_theorem "pmatch_list_snoc_nil[simp]"
  (fun () ->
    `!p ps v vs (s:('c,'ffi)flatSem_state) env.
         (pmatch_list s [] (SNOC v vs) env = Match_type_error) /\
         (pmatch_list s (SNOC p ps) [] env = Match_type_error)`)
  CHEAT_TAC;;

let flatProps_pmatch_list_append = cake_theorem "pmatch_list_append"
  (fun () ->
    `!ps vs ps' vs' s env. LENGTH ps = LENGTH vs ==>
        pmatch_list s (ps ++ ps') (vs ++ vs') env =
        (match pmatch_list s ps vs env with Match env' ->
          pmatch_list s ps' vs' env' | Match_type_error ->
          Match_type_error | No_match ->
            (match pmatch_list s ps' vs' env with
              Match_type_error -> Match_type_error | _1 -> No_match))`)
  CHEAT_TAC;;

let pmatch_list_snoc = cake_theorem "pmatch_list_snoc"
  (fun () ->
    `!ps vs p v (s:('c,'ffi)flatSem_state) env. LENGTH ps = LENGTH vs
  ==>
        pmatch_list s (SNOC p ps) (SNOC v vs) env =
        (match pmatch_list s ps vs env with Match env' -> pmatch s
          p v env' | Match_type_error -> Match_type_error | No_match ->
            (match pmatch s p v env with Match_type_error ->
              Match_type_error | _2 -> No_match))`)
  CHEAT_TAC;;

let map_match_eq_case = cake_theorem "map_match_eq_case"
  (fun () ->
    `map_match f v = (match v with Match m -> Match (f m) | _3 -> v)`)
  CHEAT_TAC;;

let flatProps_pmatch_append = cake_theorem "pmatch_append"
  (fun () ->
    `(!(s:('c,'ffi)flatSem_state) p v env pred_env.
       map_match (C APPEND tail_env) (pmatch s p v env) =
         pmatch s p v (env ++ tail_env)) /\
     (!(s:('c,'ffi)flatSem_state) ps vs env n.
       map_match (C APPEND tail_env) (pmatch_list s ps vs env) =
        pmatch_list s ps vs (env ++ tail_env))`)
  CHEAT_TAC;;

(* HOL4 flatPropsScript.sml:217-221: a theorem that HOL4 states as
   the value of an ML expression: pmatch_nil *)

let pmatch_ignore_clock = cake_theorem "pmatch_ignore_clock"
  (fun () ->
    `pmatch (state_clock_fupd (K s') s) p v env = pmatch s p v env /\
     pmatch_list (state_clock_fupd (K s') s) ps vs env =
       pmatch_list s ps vs env`)
  CHEAT_TAC;;

let pmatch_rows_ignore_clock =
  cake_theorem "pmatch_rows_ignore_clock[simp]"
  (fun () ->
    `!pes s v c.
       pmatch_rows pes (state_clock_fupd (K c) s) v = pmatch_rows
         pes s v`)
  CHEAT_TAC;;

let pmatch_rows_IMP_pmatch = cake_theorem "pmatch_rows_IMP_pmatch"
  (fun () ->
    `pmatch_rows pes s v = Match (env',p',e') ==>
     pmatch s p' v [] = Match env' /\ MEM (p',e') pes`)
  CHEAT_TAC;;

let flatProps_build_rec_env_help_lem =
  cake_theorem "build_rec_env_help_lem[local]"
  (fun () ->
    `!funs env funs'.
     ITLIST (\(f,x,e) env'. (f,flatSem_Recclosure env funs' f) ::
       env') funs env' =
     MAP (\(fn,n,e). (fn,Recclosure env funs' fn)) funs ++ env'`)
  CHEAT_TAC;;

(* Alternate definition for build_rec_env *)
let flatProps_build_rec_env_merge = cake_theorem "build_rec_env_merge"
  (fun () ->
    `!funs funs' env env'.
      build_rec_env funs env env' =
      MAP (\(fn,n,e). (fn,Recclosure env funs fn)) funs ++ env'`)
  CHEAT_TAC;;

let flatProps_evaluate_length = cake_theorem "evaluate_length"
  (fun () ->
    `(!env (s:('c,'ffi)flatSem_state) ls s' vs.
        evaluate env s ls = (s',Rval vs) ==> LENGTH vs = LENGTH
          ls)`)
  CHEAT_TAC;;

let flatProps_evaluate_cons = cake_theorem "evaluate_cons"
  (fun () ->
    `flatSem_evaluate env s (e :: es) =
     (match evaluate env s [e] with (s,Rval v) ->
        (match evaluate env s es with (s,Rval vs) -> (s,Rval (v
          ++ vs)) | r -> r) | r -> r)`)
  CHEAT_TAC;;

let flatProps_evaluate_sing = cake_theorem "evaluate_sing"
  (fun () ->
    `(evaluate env s [e] = (s',Rval vs) ==> (?y. vs = [y]))`)
  CHEAT_TAC;;

let flatProps_evaluate_append = cake_theorem "evaluate_append"
  (fun () ->
    `evaluate env s (l1 ++ l2) =
     (match evaluate env s l1 with (s,Rval v1) ->
       (match evaluate env s l2 with (s,Rval v2) -> (s,Rval (v1
         ++ v2)) | r -> r) | r -> r)`)
  CHEAT_TAC;;

let do_app_state_unchanged = cake_theorem "do_app_state_unchanged"
  (fun () ->
    `!c s op vs s' r. do_app s op vs = SOME (s',r) ==>
  flatSem_state_eval_config
        s' = flatSem_state_eval_config s`)
  CHEAT_TAC;;

let flatProps_evaluate_decs_append = cake_theorem "evaluate_decs_append"
  (fun () ->
    `!s ds1 s1 s2 r ds2.
       evaluate_decs s (ds1 ++ ds2) =
       (match evaluate_decs s ds1 with (s1,NONE) -> evaluate_decs
         s1 ds2 | (s1,SOME err) -> (s1,SOME err))`)
  CHEAT_TAC;;

let flatProps_do_app_add_to_clock =
  cake_theorem "do_app_add_to_clock[local]"
  (fun () ->
    `do_app (s:('c,'ffi)flatSem_state) op es = SOME (t,r) ==>
      do_app (state_clock_fupd (K (state_clock s + k)) s) op es =
        SOME (state_clock_fupd (K (state_clock t + k)) t,r)`)
  CHEAT_TAC;;

let do_app_add_to_clock_NONE =
  cake_theorem "do_app_add_to_clock_NONE[local]"
  (fun () ->
    `do_app (s:('c,'ffi)flatSem_state) op es = NONE ==>
      do_app (state_clock_fupd (K (state_clock s + k)) s) op es =
        NONE`)
  CHEAT_TAC;;

let flatProps_evaluate_add_to_clock =
  cake_theorem "evaluate_add_to_clock"
  (fun () ->
    `(!env (s:('c,'ffi)flatSem_state) es s' r.
         evaluate env s es = (s',r) /\ ~(r = Rerr (Rabort
           Rtimeout_error)) ==>
         evaluate env (state_clock_fupd (K (state_clock s + extra))
           s) es =
           (state_clock_fupd (K (state_clock s' + extra)) s',r)) /\
     (!(s:('c,'ffi)flatSem_state) d s' r.
         evaluate_dec s d = (s',r) /\ ~(r = SOME (Rabort
           Rtimeout_error)) ==>
         evaluate_dec (state_clock_fupd (K (state_clock s + extra))
           s) d =
           (state_clock_fupd (K (state_clock s' + extra)) s',r)) /\
     (!(s:('c,'ffi)flatSem_state) ds s' r.
         evaluate_decs s ds = (s',r) /\ ~(r = SOME (Rabort
           Rtimeout_error)) ==>
         evaluate_decs (state_clock_fupd (K (state_clock s +
           extra)) s) ds =
           (state_clock_fupd (K (state_clock s' + extra)) s',r))`)
  CHEAT_TAC;;

let flatProps_evaluate_decs_add_to_clock =
  cake_theorem "evaluate_decs_add_to_clock"
  (fun () ->
    `!decs s s' r. ~(r = SOME (Rabort Rtimeout_error)) /\
      evaluate_decs s decs = (s',r) ==>
      evaluate_decs (state_clock_fupd (K (state_clock s + extra))
        s) decs =
      (state_clock_fupd (K (state_clock s' + extra)) s',r)`)
  CHEAT_TAC;;

let flatProps_do_app_io_events_mono =
  cake_theorem "do_app_io_events_mono"
  (fun () ->
    `do_app (s:('c,'ffi)flatSem_state) op vs = SOME (t,r) ==>
  ffi_state_io_events (state_ffi
     s) <<= ffi_state_io_events (state_ffi t)`)
  CHEAT_TAC;;

let flatProps_evaluate_io_events_mono =
  cake_theorem "evaluate_io_events_mono"
  (fun () ->
    `(!env (s:('c,'ffi)flatSem_state) es. ffi_state_io_events (state_ffi
        s) <<= ffi_state_io_events (state_ffi (FST (evaluate env s
          es)))) /\
     (!(s:('c,'ffi)flatSem_state) d. ffi_state_io_events (state_ffi
        s) <<= ffi_state_io_events (state_ffi (FST (evaluate_dec s
          d)))) /\
     (!(s:('c,'ffi)flatSem_state) ds. ffi_state_io_events
       (state_ffi
        s) <<= ffi_state_io_events (state_ffi (FST (evaluate_decs
          s ds))))`)
  CHEAT_TAC;;

let evaluate_io_events_mono_IMP =
  cake_theorem "evaluate_io_events_mono_IMP"
  (fun () ->
    `(evaluate env s es = (s',r) ==> ffi_state_io_events (state_ffi
        s) <<= ffi_state_io_events (state_ffi s')) /\
     (evaluate_dec s d = (s',r') ==> ffi_state_io_events (state_ffi
        s) <<= ffi_state_io_events (state_ffi s')) /\
     (evaluate_decs s ds = (s',r'') ==> ffi_state_io_events
       (state_ffi
        s) <<= ffi_state_io_events (state_ffi s'))`)
  CHEAT_TAC;;

let flatProps_with_clock_ffi = cake_theorem "with_clock_ffi"
  (fun () ->
    `state_ffi
        (state_clock_fupd (K k) s) = state_ffi s`)
  CHEAT_TAC;;

let flatProps_evaluate_add_to_clock_io_events_mono =
  cake_theorem "evaluate_add_to_clock_io_events_mono"
  (fun () ->
    `(!env (s:('c,'ffi)flatSem_state) es. ffi_state_io_events (state_ffi
         (FST (evaluate env s es))) <<= ffi_state_io_events
           (state_ffi
         (FST (evaluate env (state_clock_fupd (K (state_clock s +
           extra)) s) es)))) /\
     (!(s:('c,'ffi)flatSem_state) d. ffi_state_io_events (state_ffi
         (FST (evaluate_dec s d))) <<= ffi_state_io_events
           (state_ffi
         (FST (evaluate_dec (state_clock_fupd (K (state_clock s +
           extra)) s) d)))) /\
     (!(s:('c,'ffi)flatSem_state) ds. ffi_state_io_events
       (state_ffi
         (FST (evaluate_decs s ds))) <<= ffi_state_io_events
           (state_ffi
         (FST (evaluate_decs (state_clock_fupd (K (state_clock s
           + extra)) s) ds))))`)
  CHEAT_TAC;;

let evaluate_dec_io_events_mono =
  cake_theorem "evaluate_dec_io_events_mono"
  (fun () ->
    `!z y. ffi_state_io_events (state_ffi
        y) <<= ffi_state_io_events (state_ffi (FST (evaluate_dec
          y z)))`)
  CHEAT_TAC;;

let evaluate_dec_add_to_clock_io_events_mono =
  cake_theorem "evaluate_dec_add_to_clock_io_events_mono"
  (fun () ->
    `!prog (s:('c,'ffi)flatSem_state) extra. ffi_state_io_events
  (state_ffi
      (FST (evaluate_dec s prog))) <<= ffi_state_io_events
        (state_ffi
      (FST (evaluate_dec (state_clock_fupd (K (state_clock s +
        extra)) s) prog)))`)
  CHEAT_TAC;;

let evaluate_decs_io_events_mono =
  cake_theorem "evaluate_decs_io_events_mono"
  (fun () ->
    `!ds (s:('c,'ffi)flatSem_state) s' y. evaluate_decs s ds = (s',y)
  ==> ffi_state_io_events (state_ffi
      s) <<= ffi_state_io_events (state_ffi s')`)
  CHEAT_TAC;;

let flatProps_evaluate_decs_add_to_clock_io_events_mono =
  cake_theorem "evaluate_decs_add_to_clock_io_events_mono"
  (fun () ->
    `!ds (s:('c,'ffi)flatSem_state) extra. ffi_state_io_events
  (state_ffi
       (FST (evaluate_decs s ds))) <<= ffi_state_io_events
         (state_ffi
       (FST (evaluate_decs (state_clock_fupd (K (state_clock s +
         extra)) s) ds)))`)
  CHEAT_TAC;;

let evaluate_MAP_Var_local = cake_theorem "evaluate_MAP_Var_local"
  (fun () ->
    `MAP (ALOOKUP (flatSem_environment_v env)) xs = MAP SOME vs ==>
     evaluate env s (MAP (flatLang_Var_local t) xs) = (s,Rval vs)`)
  CHEAT_TAC;;

let bind_locals_list_def = cake_define
  `bind_locals_list ts ks = MAP2 (\t x. (flatLang_Var_local t x)) ts
  ks`;;

let evaluate_vars = cake_theorem "evaluate_vars"
  (fun () ->
    `!env s kvs env' ks vs ts.
      ALL_DISTINCT (MAP FST kvs) /\
      DISJOINT (set_of_list (MAP FST kvs)) (set_of_list (MAP FST
        env')) /\ flatSem_environment_v
      env = env' ++ kvs /\ ks = MAP FST kvs /\ vs = MAP SND kvs /\
      LENGTH ts = LENGTH ks ==>
      evaluate env s (bind_locals_list ts ks) = (s,Rval vs)`)
  CHEAT_TAC;;

(* HOL4 flatPropsScript.sml:546-605: code that the source has in a
   comment *)

let pmatch_list_MAP_Pvar = cake_theorem "pmatch_list_MAP_Pvar"
  (fun () ->
    `!xs vs. LENGTH xs = LENGTH vs ==>
     pmatch_list s (MAP Pvar xs) vs [] = Match (REVERSE (ZIP xs
       vs))`)
  CHEAT_TAC;;

let evaluate_decs_add_to_clock_initial_state =
  cake_theorem "evaluate_decs_add_to_clock_initial_state[local]"
  (fun () ->
    `~(r = SOME (Rabort Rtimeout_error)) /\
        evaluate_decs (flatSem_initial_state ffi k ec) decs =
          (s',r) ==>
        evaluate_decs (flatSem_initial_state ffi (ck + k) ec) decs
          =
        (state_clock_fupd (K (state_clock s' + ck)) s',r)`)
  CHEAT_TAC;;

let evaluate_decs_add_to_clock_initial_state_io_events_mono =
  cake_theorem
    "evaluate_decs_add_to_clock_initial_state_io_events_mono[local]"
  (fun () ->
    `evaluate_decs (flatSem_initial_state ffi k ec) prog = (s',r) ==>
  ffi_state_io_events (state_ffi
      s') <<= ffi_state_io_events (state_ffi
      (FST (evaluate_decs (flatSem_initial_state ffi (k + ck) ec)
        prog)))`)
  CHEAT_TAC;;

let flatProps_initial_state_with_clock =
  cake_theorem "initial_state_with_clock[local]"
  (fun () ->
    `(state_clock_fupd (K (state_clock (flatSem_initial_state ffi k ec)
  + ck)) (flatSem_initial_state ffi k ec)) =
      flatSem_initial_state ffi (k + ck) ec`)
  CHEAT_TAC;;

let SND_SND_lemma = cake_theorem "SND_SND_lemma[local]"
  (fun () ->
    `(SND x) = y <=> (?y1. x = (y1,y))`)
  CHEAT_TAC;;

let eval_sim_def = cake_define
  `flatProps_eval_sim ffi ds1 ds2 ec ec2 rel allow_fail =
     (!k res1 s2.
       evaluate_decs (flatSem_initial_state ffi k ec) ds1 =
         (s2,res1) /\
       (allow_fail \/ ~(res1 = SOME (Rabort Rtype_error))) /\
       rel ds1 ds2 ==>
       (?ck res2 t2.
         evaluate_decs (flatSem_initial_state ffi (k + ck) ec2) ds2 =
           (t2,res2) /\ state_ffi
         s2 = state_ffi t2 /\
         (res1 = NONE ==> res2 = NONE) /\
         (!v. res1 = SOME (Rraise v) ==> (?v1. res2 = SOME (Rraise
           v1))) /\
         (!a. res1 = SOME (Rabort a) ==> res2 = SOME (Rabort a))))`;;
hol4_overload "eval_sim" "flatProps_eval_sim";;

let flatProps_IMP_semantics_eq = cake_theorem "IMP_semantics_eq"
  (fun () ->
    `flatProps_eval_sim ffi ds1 ds2 ec ec2 rel F /\ ~(flatSem_semantics
  ec (ffi:'ffi ffi_state) ds1 = ffi_Fail) ==>
     rel ds1 ds2 ==>
     flatSem_semantics ec ffi ds1 =
     flatSem_semantics ec2 ffi ds2`)
  CHEAT_TAC;;

let op_gbag_def = cake_define
  `flatProps_op_gbag x1 =
      match x1 with
        flatLang_GlobalVarInit n -> BAG_INSERT n EMPTY_BAG
      | _4 -> EMPTY_BAG`;;
hol4_overload "op_gbag" "flatProps_op_gbag";;

let _ = size_thms "flatLang_exp";;
(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 flatPropsScript.sml:819-833: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let set_globals_def = cake_define_list_try_tac (fun () ->
  `MEASURE (\a. match a with INL e -> flatLang_exp_size e | INR es ->
     list_size flatLang_exp_size es)`)
  CHEAT_TAC
  [`flatProps_set_globals (Raise t e:flatLang_exp) =
  flatProps_set_globals e`;
   `flatProps_set_globals (Handle t e pes:flatLang_exp) = (BAG_UNION)
  (flatProps_set_globals e) (flatProps_elist_globals (MAP SND pes))`;
   `flatProps_set_globals (Con t id' es:flatLang_exp) =
  flatProps_elist_globals es`;
   `flatProps_set_globals (Fun t v e:flatLang_exp) =
  flatProps_set_globals e`;
   `flatProps_set_globals (App t op es:flatLang_exp) = (BAG_UNION)
  (flatProps_elist_globals es) (flatProps_op_gbag op)`;
   `flatProps_set_globals (If t e1 e2 e3:flatLang_exp) = (BAG_UNION)
  ((BAG_UNION) (flatProps_set_globals e1) (flatProps_set_globals e2))
  (flatProps_set_globals e3)`;
   `flatProps_set_globals (Mat t e pes:flatLang_exp) = (BAG_UNION)
  (flatProps_set_globals e) (flatProps_elist_globals (MAP SND pes))`;
   `flatProps_set_globals (Let t v e1 e2:flatLang_exp) = (BAG_UNION)
  (flatProps_set_globals e1) (flatProps_set_globals e2)`;
   `flatProps_set_globals (Letrec t fs e:flatLang_exp) = (BAG_UNION)
  (flatProps_set_globals e) (flatProps_elist_globals (MAP (SND o SND)
  fs))`;
   `flatProps_set_globals _5 = EMPTY_BAG`;
   `flatProps_elist_globals [] = EMPTY_BAG`;
   `flatProps_elist_globals (e :: es) = (BAG_UNION)
  (flatProps_set_globals e) (flatProps_elist_globals es)`];;
hol4_overload "elist_globals" "flatProps_elist_globals";;
hol4_overload "set_globals" "flatProps_set_globals";;


let _ = size_thms "flatLang_exp";;
(* HOL4 flatPropsScript.sml:850-856: the tactic that proves the
   termination *)
let esgc_free_def = cake_define_wf
  `MEASURE flatLang_exp_size`
  `flatProps_esgc_free x1 =
        match x1 with
          (Raise t e:flatLang_exp) -> flatProps_esgc_free e
        | (Handle t e pes) ->
       flatProps_esgc_free e /\ EVERY flatProps_esgc_free (MAP SND
         pes)
        | (Con t id' es) -> EVERY flatProps_esgc_free es
        | (Fun t v e) -> flatProps_set_globals e = EMPTY_BAG
        | (App t op es) -> EVERY flatProps_esgc_free es
        | (If t e1 e2 e3) ->
       flatProps_esgc_free e1 /\ flatProps_esgc_free e2 /\
         flatProps_esgc_free e3
        | (Mat t e pes) -> flatProps_esgc_free e /\ EVERY
          flatProps_esgc_free (MAP SND pes)
        | (Let t v e1 e2) -> flatProps_esgc_free e1 /\
          flatProps_esgc_free e2
        | (Letrec t fs e) ->
       flatProps_esgc_free e /\ flatProps_elist_globals (MAP (SND o
         SND) fs) = EMPTY_BAG
        | _6 -> T`;;
hol4_overload "esgc_free" "flatProps_esgc_free";;

(* HOL4 flatPropsScript.sml:858-859: a theorem that HOL4 states as
   the value of an ML expression: esgc_free_def *)

let elist_globals_eq_empty = cake_theorem "elist_globals_eq_empty"
  (fun () ->
    `flatProps_elist_globals l = EMPTY_BAG <=> (!e. MEM e l ==>
  flatProps_set_globals e = EMPTY_BAG)`)
  CHEAT_TAC;;

let flatProps_elist_globals_append = cake_theorem "elist_globals_append"
  (fun () ->
    `flatProps_elist_globals (xs ++ ys) = (BAG_UNION)
  (flatProps_elist_globals xs) (flatProps_elist_globals ys)`)
  CHEAT_TAC;;

let flatProps_elist_globals_FOLDR = cake_theorem "elist_globals_FOLDR"
  (fun () ->
    `flatProps_elist_globals es = (BAG_UNION) FOLDR (EMPTY_BAG (MAP
  flatProps_set_globals es))`)
  CHEAT_TAC;;

let elist_globals_REVERSE = cake_theorem "elist_globals_REVERSE"
  (fun () ->
    `flatProps_elist_globals (REVERSE es) = flatProps_elist_globals es`)
  CHEAT_TAC;;

let flatProps_initial_state_clock = cake_theorem "initial_state_clock"
  (fun () ->
    `state_clock
       (flatSem_initial_state ffi k ec) = k /\
       ((state_clock_fupd (K k1) (flatSem_initial_state ffi k
         ec)) = flatSem_initial_state ffi k1 ec)`)
  CHEAT_TAC;;

let build_rec_env_eq_MAP = cake_theorem "build_rec_env_eq_MAP"
  (fun () ->
    `build_rec_env funs cl_env env =
     MAP (\(f,x,e). (f,Recclosure cl_env funs f)) funs ++ env`)
  CHEAT_TAC;;

let evaluate_decs_add_to_clock_io_events_mono_alt =
  cake_theorem "evaluate_decs_add_to_clock_io_events_mono_alt"
  (fun () ->
    `evaluate_decs (s:('c,'ffi)flatSem_state) ds = (s1,res) /\
     evaluate_decs (state_clock_fupd (K (state_clock s + extra)) s)
       ds = (s2,res2) ==> ffi_state_io_events (state_ffi
     s1) <<= ffi_state_io_events (state_ffi s2)`)
  CHEAT_TAC;;

(* generic proof support for most val_rel/state_rel examples *)

let isClosure_def = cake_define
  `isClosure exp = (
     (?vs n x. exp = Closure vs n x) \/
     (?vs fs x. exp = Recclosure vs fs x))`;;

(* HOL4 flatPropsScript.sml:921-923: ML code, not ported *)

(* HOL4 flatPropsScript.sml:925-927: a theorem that HOL4 states as
   the value of an ML expression: isClosure_simps *)

let simple_basic_val_rel_def = cake_define_list
  [`simple_basic_val_rel (Litv l:flatSem_v) v = (v = (Litv
  l:flatSem_v))`;
   `simple_basic_val_rel (Loc b i:flatSem_v) v = (v = (Loc b
  i:flatSem_v))`;
   `simple_basic_val_rel (Conv stmp vs1:flatSem_v) v = (?vs2. v =
  Conv stmp vs2)`;
   `simple_basic_val_rel (Vectorv vs1:flatSem_v) v = (?vs2. v =
  Vectorv vs2)`;
   `simple_basic_val_rel (Closure vs nm exp:flatSem_v) v = F`;
   `simple_basic_val_rel (Recclosure vs exps nm:flatSem_v) v = F`];;

let v_container_xs_def = cake_define_list
  [`v_container_xs (Litv _8:flatSem_v) = []`;
   `v_container_xs (Loc _11 _12:flatSem_v) = []`;
   `v_container_xs (Conv _14 vs:flatSem_v) = vs`;
   `v_container_xs (Vectorv vs:flatSem_v) = vs`;
   `v_container_xs (Closure vs nm exp:flatSem_v) = []`;
   `v_container_xs (Recclosure vs exps nm:flatSem_v) = []`];;

let simple_val_rel_def = cake_define
  `flatProps_simple_val_rel vr = (
     (!v1 v2. (vr v1 v2 ==> isClosure v1 = isClosure v2)) /\ (!v1 v2.
       ~(isClosure v1) ==> vr v1 v2 = (
         simple_basic_val_rel v1 v2 /\ LIST_REL vr (v_container_xs
           v1) (v_container_xs v2))))`;;
hol4_overload "simple_val_rel" "flatProps_simple_val_rel";;

(* HOL4 flatPropsScript.sml:953-954: a theorem that HOL4 states as
   the value of an ML expression: simple_val_rel_rew *)

(* HOL4 flatPropsScript.sml:956-960: a theorem that HOL4 states as
   the value of an ML expression: simple_val_rel_simps *)

let simple_val_rel_isClosure = cake_theorem "simple_val_rel_isClosure"
  (fun () ->
    `flatProps_simple_val_rel vr /\ vr x y ==> (isClosure x =
  isClosure y)`)
  CHEAT_TAC;;

let simple_state_rel_def = cake_define
  `flatProps_simple_state_rel vr sr <=>
     (!s t. sr s t ==> LIST_REL (semanticPrimitivesProps_sv_rel vr)
       (state_refs s) (state_refs t)) /\
     (!s t srefs trefs.
         sr s t /\ LIST_REL (semanticPrimitivesProps_sv_rel vr) srefs
           trefs ==> sr (state_refs_fupd (K srefs) s) (state_refs_fupd
           (K trefs) t)) /\
     (!s t. sr s t ==> LIST_REL (OPTREL vr) (flatSem_state_globals s)
       (flatSem_state_globals t)) /\
     (!s t sglob tglob.
         sr s t /\ LIST_REL (OPTREL vr) sglob tglob ==> sr
           (flatSem_state_globals_fupd (K sglob) s)
           (flatSem_state_globals_fupd (K tglob) t)) /\
     (!s t. sr s t ==> state_ffi s = state_ffi t) /\
     (!s t sffi tffi.
         sr s t /\ sffi = tffi ==> sr (state_ffi_fupd (K sffi) s)
           (state_ffi_fupd (K tffi) t))`;;
hol4_overload "simple_state_rel" "flatProps_simple_state_rel";;

let simple_do_eq_thm_ind = cake_theorem "simple_do_eq_thm_ind"
  (fun () ->
    `(!x1 y1 x2 y2 b.
     flatProps_simple_val_rel vr /\
     do_eq x1 y1 = Eq_val b /\
     vr x1 x2 /\ vr y1 y2 ==>
     do_eq x2 y2 = Eq_val b) /\
     (!x1 y1 x2 y2 b.
     flatProps_simple_val_rel vr /\
     do_eq_list x1 y1 = Eq_val b /\
     LIST_REL vr x1 x2 /\ LIST_REL vr y1 y2 ==>
     do_eq_list x2 y2 = Eq_val b)`)
  CHEAT_TAC;;

(* HOL4 flatPropsScript.sml:1005: a theorem that HOL4 states as the
   value of an ML expression: simple_do_eq_thm *)

let simple_state_rel_store_assign =
  cake_theorem "simple_state_rel_store_assign"
  (fun () ->
    `flatProps_simple_state_rel vr sr /\
     store_assign lnum x (state_refs s) = SOME srefs' /\
     sr s t /\ semanticPrimitivesProps_sv_rel vr x y ==>
     (?trefs'. store_assign lnum y (state_refs t) = SOME trefs' /\
     sr (state_refs_fupd (K srefs') s) (state_refs_fupd (K
       trefs') t))`)
  CHEAT_TAC;;

let simple_state_rel_store_alloc =
  cake_theorem "simple_state_rel_store_alloc"
  (fun () ->
    `flatProps_simple_state_rel vr sr /\
     store_alloc x (state_refs s) = (srefs',lnum) /\
     sr s t /\ semanticPrimitivesProps_sv_rel vr x y ==>
     (?trefs'. store_alloc y (state_refs t) = (trefs',lnum) /\
     sr (state_refs_fupd (K srefs') s) (state_refs_fupd (K
       trefs') t))`)
  CHEAT_TAC;;

let simple_state_rel_store_lookup =
  cake_theorem "simple_state_rel_store_lookup"
  (fun () ->
    `flatProps_simple_state_rel vr sr /\
     store_lookup lnum (state_refs s) = SOME x /\
     sr s t ==>
     (?y. store_lookup lnum (state_refs t) = SOME y /\
       semanticPrimitivesProps_sv_rel vr x y)`)
  CHEAT_TAC;;

let simple_v_to_char_list_v_rel =
  cake_theorem "simple_v_to_char_list_v_rel"
  (fun () ->
    `flatProps_simple_val_rel vr ==>
     (!x y ls. vr x y /\ v_to_char_list x = SOME ls ==>
       v_to_char_list y = SOME ls)`)
  CHEAT_TAC;;

let simple_v_to_list_v_rel = cake_theorem "simple_v_to_list_v_rel"
  (fun () ->
    `flatProps_simple_val_rel vr ==>
     (!x y ls. vr x y /\ v_to_list x = SOME ls ==>
     (?ls'. v_to_list y = SOME ls' /\ LIST_REL vr ls ls'))`)
  CHEAT_TAC;;

let simple_v_rel_list_to_v = cake_theorem "simple_v_rel_list_to_v"
  (fun () ->
    `flatProps_simple_val_rel vr ==>
     (!x y. LIST_REL vr x y ==> vr (list_to_v x) (list_to_v y))`)
  CHEAT_TAC;;

let simple_vs_to_string_v_rel = cake_theorem "simple_vs_to_string_v_rel"
  (fun () ->
    `flatProps_simple_val_rel vr ==>
     (!vs ws str. LIST_REL vr vs ws /\ vs_to_string vs = SOME str
       ==>
     vs_to_string ws = SOME str)`)
  CHEAT_TAC;;

let flatProps_simple_val_rel_v_to_words =
  cake_theorem "simple_val_rel_v_to_words"
  (fun () ->
    `flatProps_simple_val_rel vr ==>
     (!x y ws. vr x y /\ flatSem_v_to_words x = SOME ws ==>
     flatSem_v_to_words y = SOME ws)`)
  CHEAT_TAC;;

let flatProps_simple_val_rel_v_to_bytes =
  cake_theorem "simple_val_rel_v_to_bytes"
  (fun () ->
    `flatProps_simple_val_rel vr ==>
     (!x y ws. vr x y /\ flatSem_v_to_bytes x = SOME ws ==>
     flatSem_v_to_bytes y = SOME ws)`)
  CHEAT_TAC;;

let check_type_LIST_REL_same =
  cake_theorem "check_type_LIST_REL_same[local]"
  (fun () ->
    `LIST_REL vr vs1 vs2 /\
     EVERY (check_type ty) (MAP flat_to_v vs1) /\
     flatProps_simple_val_rel vr ==>
     vs2 = vs1`)
  CHEAT_TAC;;

(* HOL4 flatPropsScript.sml:1157: ML code, not ported *)

let simple_do_app_thm = cake_theorem "simple_do_app_thm"
  (fun () ->
    `flatProps_simple_val_rel vr /\
     flatProps_simple_state_rel vr sr ==>
     (!s1 vs1 t1 r1 s2 vs2.
     do_app s1 op vs1 = SOME (t1,r1) ==>
     sr s1 s2 /\ LIST_REL vr vs1 vs2 ==>
     (?t2 r2. semanticPrimitivesProps_result_rel vr vr r1 r2 /\
     sr t1 t2 /\ do_app s2 op vs2 = SOME (t2,r2)))`)
  CHEAT_TAC;;

let evaluate_match_def = cake_define
  `flatProps_evaluate_match env s v pes err_v =
     (match pmatch_rows pes s v with Match_type_error -> (s,Rerr
       (Rabort Rtype_error)) | No_match -> (s,Rerr (Rraise err_v)) |
       Match (env',p',e') ->
         (if ALL_DISTINCT (pat_bindings p') then evaluate
           (flatSem_environment_v_fupd (K (env' ++
           flatSem_environment_v env)) env) s [e'] else (s,Rerr
           (Rabort Rtype_error))))`;;
hol4_overload "evaluate_match" "flatProps_evaluate_match";;

let evaluate_Mat = cake_theorem "evaluate_Mat"
  (fun () ->
    `evaluate env s [(Mat tra e pes:flatLang_exp)] =
     (match evaluate env s [e] with (s,Rval v) ->
         (if ~(pmatch_rows pes s (HD v) = Match_type_error) then
           evaluate_match env s (HD v) pes bind_exn_v else (s,Rerr
           (Rabort Rtype_error))) | res -> res)`)
  CHEAT_TAC;;

let evaluate_Handle = cake_theorem "evaluate_Handle"
  (fun () ->
    `evaluate env s [(Handle _16 e pes:flatLang_exp)] =
     (match evaluate env s [e] with (s,Rerr (Rraise v)) ->
         (if ~(pmatch_rows pes s v = Match_type_error) then
           evaluate_match env s v pes v else (s,Rerr (Rabort
           Rtype_error))) | res -> res)`)
  CHEAT_TAC;;

let evaluate_match_NIL = cake_theorem "evaluate_match_NIL"
  (fun () ->
    `evaluate_match env s v [] err_v =
       (s,Rerr (Rraise err_v))`)
  CHEAT_TAC;;

let evaluate_match_CONS = cake_theorem "evaluate_match_CONS"
  (fun () ->
    `evaluate_match env s v ((p,e) :: pes) err_v =
       (match pmatch s p v [] with No_match -> evaluate_match env s
         v pes err_v | Match_type_error -> (s,Rerr (Rabort Rtype_error))
         | Match env_v' ->
           (if ALL_DISTINCT (pat_bindings p) /\ ~(pmatch_rows pes
             s v = Match_type_error) then evaluate
             (flatSem_environment_v_fupd (K (env_v' ++
             flatSem_environment_v env)) env) s [e] else (s,Rerr
             (Rabort Rtype_error))))`)
  CHEAT_TAC;;

(* HOL4 flatPropsScript.sml:1432-1446: the ML values that the
   definitions below antiquote *)

(* HOL4 flatPropsScript.sml:1448: a theorem that HOL4 states as the
   value of an ML expression: flat_evaluate_def *)

let store_v_vs_def = cake_define_list
  [`flatProps_store_v_vs (semanticPrimitives_Varray vs) = vs`;
   `flatProps_store_v_vs (semanticPrimitives_Refv v) = [v]`;
   `flatProps_store_v_vs (semanticPrimitives_Thunk m v) = [v]`;
   `flatProps_store_v_vs (semanticPrimitives_W8array xs) = []`];;
hol4_overload "store_v_vs" "flatProps_store_v_vs";;

let result_vs_def = cake_define
  `result_vs x1 =
      match x1 with
        Rval xs -> xs
      | (Rerr (Rraise x)) -> [x]
      | (Rerr (Rabort y)) -> []`;;

(* HOL4 flatPropsScript.sml:1463-1469: a theorem whose statement the
   port cannot state yet: v_size_aux *)

let _ = size_thms "flatLang_exp";;
(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 flatPropsScript.sml:1484-1489: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let no_Mat_def = cake_define_list_try_tac (fun () ->
  `MEASURE (flatLang_exp_size)`)
  CHEAT_TAC
  [`no_Mat (flatLang_Raise t e) <=> no_Mat e`;
   `no_Mat (Lit t l:flatLang_exp) <=> T`;
   `no_Mat (flatLang_Var_local t v) <=> T`;
   `no_Mat (Con t n es:flatLang_exp) <=> EVERY no_Mat es`;
   `no_Mat (App t op es:flatLang_exp) <=> EVERY no_Mat es`;
   `no_Mat (Fun t v e:flatLang_exp) <=> no_Mat e`;
   `no_Mat (If t x1 x2 x3:flatLang_exp) <=> no_Mat x1 /\ no_Mat x2 /\
  no_Mat x3`;
   `no_Mat (Let t vo e1 e2:flatLang_exp) <=> no_Mat e1 /\ no_Mat e2`;
   `no_Mat (Mat t e pes:flatLang_exp) <=> F`;
   `no_Mat (Handle t e pes:flatLang_exp) <=> no_Mat e /\ EVERY no_Mat
  (MAP SND pes) /\
        (match pes with [(Pvar _24,_25)] -> T | _26 -> F)`;
   `no_Mat (Letrec t funs e:flatLang_exp) <=> EVERY no_Mat (MAP
  (SND o SND) funs) /\ no_Mat e`];;

let no_Mat_decs_def = cake_define_list
  [`no_Mat_decs [] = T`;
   `no_Mat_decs (e :: xs) = (no_Mat e /\ no_Mat_decs xs)`];;

let mk_flat_install_conf_def = cake_define
  `flatProps_mk_flat_install_conf cc co =
     (mk_install_config cc co:'c install_config)`;;
hol4_overload "mk_flat_install_conf" "flatProps_mk_flat_install_conf";;
