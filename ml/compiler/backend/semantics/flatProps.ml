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

needs "basis/pure/mlstring.ml";;
needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/flatLang.ml";;
needs "compiler/backend/semantics/flatSem.ml";;
needs "lib/lprefix_lub.ml";;
needs "semantics/ast.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/proofs/evaluateProps.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;
needs "semantics/semanticPrimitives.ml";;

(* the theories whose names the Ancestors blocks of the source
   bring, which are the ones that its statements read: the
   overloads of every other theory come out of the interface
   while this file loads *)
let _ = hol4_ancestors "flatProps"
  ["ast"; "evaluateProps"; "flatLang"; "flatSem";
   "semanticPrimitivesProps"];;

let _ = do_list hide_constant ["C"];;

let ctor_same_type_OPTREL = prove
 (`!c1 c2. flatSem_ctor_same_type c1 c2 <=> OPTREL (inv_image (=) SND)
  c1 c2`,
  CHEAT_TAC);;

let pats_bindings_FLAT_MAP = prove
 (`!ps. flatLang_pats_bindings ps = FLAT (REVERSE (MAP (\p.
  flatLang_pat_bindings p) ps))`,
  CHEAT_TAC);;

(* HOL4 flatPropsScript.sml:31-33: the ML values that the definitions
   below antiquote *)

let pmatch_state = prove
 (`(!(st) p v l (st') res.
     flatSem_pmatch st p v l = res /\ flatSem_state_refs
     st = flatSem_state_refs st' ==> flatSem_pmatch st' p v l = res)
       /\
   (!(st) p vs l (st') res.
     flatSem_pmatch_list st p vs l = res /\ flatSem_state_refs
     st = flatSem_state_refs st' ==> flatSem_pmatch_list st' p vs l
       = res)`,
  CHEAT_TAC);;

(* pmatch_extend *)
let flatProps_pmatch_extend = prove
 (`(!(s:('c,'ffi)flatSem_state) p v env env' env''.
    flatSem_pmatch s p v env = Match env' ==>
    (?env''. env' = APPEND env'' env /\ MAP FST env'' =
      flatLang_pat_bindings p)) /\
   (!(s:('c,'ffi)flatSem_state) ps vs env env' env''.
    flatSem_pmatch_list s ps vs env = Match env' ==>
    (?env''. env' = APPEND env'' env /\ MAP FST env'' =
      flatLang_pats_bindings ps))`,
  CHEAT_TAC);;

let pmatch_bindings = prove
 (`(!(s:('c,'ffi)flatSem_state) p v env r.
      flatSem_pmatch s p v env = Match r ==>
      MAP FST r = APPEND (flatLang_pat_bindings p) (MAP FST env)) /\
   (!(s:('c,'ffi)flatSem_state) ps vs env r.
     flatSem_pmatch_list s ps vs env = Match r ==>
     MAP FST r = APPEND (flatLang_pats_bindings ps) (MAP FST env))`,
  CHEAT_TAC);;

let pmatch_length = prove
 (`!(s:('c,'ffi)flatSem_state) p v env r.
      flatSem_pmatch s p v env = Match r ==>
      LENGTH r = LENGTH (flatLang_pat_bindings p) + LENGTH env`,
  (REPEAT STRIP_TAC THEN
   FIRST_ASSUM(MP_TAC o AP_TERM `LENGTH:(mlstring)list->num` o
               MATCH_MP (CONJUNCT1 pmatch_bindings)) THEN
   REWRITE_TAC[LENGTH_APPEND; LENGTH_MAP]));;

let pmatch_any_match = prove
 (`(!(s:('c,'ffi)flatSem_state) p v env env'. flatSem_pmatch s p v env =
  Match env' ==>
      (!env. ?env'. flatSem_pmatch s p v env = Match env')) /\
   (!(s:('c,'ffi)flatSem_state) ps vs env env'. flatSem_pmatch_list s
     ps vs env = Match env' ==>
      (!env. ?env'. flatSem_pmatch_list s ps vs env = Match env'))`,
  CHEAT_TAC);;

let pmatch_any_no_match = prove
 (`(!(s:('c,'ffi)flatSem_state) p v env. flatSem_pmatch s p v env =
  No_match ==>
       (!env. flatSem_pmatch s p v env = No_match)) /\
    (!(s:('c,'ffi)flatSem_state) ps vs env. flatSem_pmatch_list s ps
      vs env = No_match ==>
       (!env. flatSem_pmatch_list s ps vs env = No_match))`,
  CHEAT_TAC);;

let pmatch_any_match_error = prove
 (`(!(s:('c,'ffi)flatSem_state) p v env. flatSem_pmatch s p v env =
  Match_type_error ==>
       (!env. flatSem_pmatch s p v env = Match_type_error)) /\
   (!(s:('c,'ffi)flatSem_state) ps vs env. flatSem_pmatch_list s ps
     vs env = Match_type_error ==>
       (!env. flatSem_pmatch_list s ps vs env = Match_type_error))`,
  CHEAT_TAC);;

let pmatch_list_pairwise = prove
 (`!ps vs (s:('c,'ffi)flatSem_state) env env'.
      flatSem_pmatch_list s ps vs env = Match env' ==>
      ALL2 (\p v. !env. ?env'. flatSem_pmatch s p v env = Match
        env') ps vs`,
  CHEAT_TAC);;

(* [simp] *)
let pmatch_list_snoc_nil = prove
 (`!p ps v vs (s:('c,'ffi)flatSem_state) env.
       (flatSem_pmatch_list s [] (SNOC v vs) env = Match_type_error)
         /\
       (flatSem_pmatch_list s (SNOC p ps) [] env =
         Match_type_error)`,
  CHEAT_TAC);;

(* pmatch_list_append *)
let flatProps_pmatch_list_append = prove
 (`!ps vs ps' vs' s env. LENGTH ps = LENGTH vs ==>
      flatSem_pmatch_list s (APPEND ps ps') (APPEND vs vs') env =
      (match flatSem_pmatch_list s ps vs env with Match env' ->
        flatSem_pmatch_list s ps' vs' env' | Match_type_error ->
        Match_type_error | No_match ->
          (match flatSem_pmatch_list s ps' vs' env with
            Match_type_error -> Match_type_error | _1 -> No_match))`,
  CHEAT_TAC);;

let pmatch_list_snoc = prove
 (`!ps vs p v (s:('c,'ffi)flatSem_state) env. LENGTH ps = LENGTH vs ==>
      flatSem_pmatch_list s (SNOC p ps) (SNOC v vs) env =
      (match flatSem_pmatch_list s ps vs env with Match env' ->
        flatSem_pmatch s p v env' | Match_type_error -> Match_type_error
        | No_match ->
          (match flatSem_pmatch s p v env with Match_type_error ->
            Match_type_error | _2 -> No_match))`,
  CHEAT_TAC);;

let map_match_eq_case = prove
 (`map_match f v = (match v with Match m -> Match (f m) | _3 -> v)`,
  CHEAT_TAC);;

(* pmatch_append *)
let flatProps_pmatch_append = prove
 (`(!(s:('c,'ffi)flatSem_state) p v env pred_env.
     map_match (hol4_C APPEND tail_env) (flatSem_pmatch s p v env) =
       flatSem_pmatch s p v (APPEND env tail_env)) /\
   (!(s:('c,'ffi)flatSem_state) ps vs env n.
     map_match (hol4_C APPEND tail_env) (flatSem_pmatch_list s ps vs
       env) =
      flatSem_pmatch_list s ps vs (APPEND env tail_env))`,
  CHEAT_TAC);;

(* HOL4 flatPropsScript.sml:217-221: a theorem that HOL4 states as
   the value of an ML expression: pmatch_nil *)

let pmatch_ignore_clock = prove
 (`flatSem_pmatch (state_clock_fupd (K s') s) p v env = flatSem_pmatch s
  p v env /\
   flatSem_pmatch_list (state_clock_fupd (K s') s) ps vs env =
     flatSem_pmatch_list s ps vs env`,
  CHEAT_TAC);;

(* [simp] *)
let pmatch_rows_ignore_clock = prove
 (`!pes s v c.
     pmatch_rows pes (state_clock_fupd (K c) s) v = pmatch_rows pes
       s v`,
  (MATCH_MP_TAC list_INDUCT THEN
   REWRITE_TAC[FORALL_PAIR_THM; pmatch_rows_def; pmatch_ignore_clock]
     THEN
   REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]));;

let pmatch_rows_IMP_pmatch = prove
 (`pmatch_rows pes s v = Match (env',p',e') ==>
   flatSem_pmatch s p' v [] = Match env' /\ MEM (p',e') pes`,
  CHEAT_TAC);;

(* build_rec_env_help_lem[local] *)
let flatProps_build_rec_env_help_lem = prove
 (`!funs env funs'.
   ITLIST (\(f,x,e) env'. CONS (f,flatSem_Recclosure env funs' f)
     env') funs env' = APPEND (MAP (\(fn,n,e). (fn,flatSem_Recclosure
     env funs' fn)) funs) env'`,
  CHEAT_TAC);;

(* Alternate definition for build_rec_env *)
(* build_rec_env_merge *)
let flatProps_build_rec_env_merge = prove
 (`!funs funs' env env'.
    flatSem_build_rec_env funs env env' = APPEND (MAP (\(fn,n,e).
      (fn,flatSem_Recclosure env funs fn)) funs) env'`,
  CHEAT_TAC);;

(* evaluate_length *)
let flatProps_evaluate_length = prove
 (`(!env (s:('c,'ffi)flatSem_state) ls s' vs.
      flatSem_evaluate env s ls = (s',Rval vs) ==> LENGTH vs =
        LENGTH ls)`,
  CHEAT_TAC);;

(* evaluate_cons *)
let flatProps_evaluate_cons = prove
 (`flatSem_evaluate env s (CONS e es) =
   (match flatSem_evaluate env s [e] with (s,Rval v) ->
      (match flatSem_evaluate env s es with (s,Rval vs) -> (s,Rval
        (APPEND v vs)) | r -> r) | r -> r)`,
  CHEAT_TAC);;

(* evaluate_sing *)
let flatProps_evaluate_sing = prove
 (`(flatSem_evaluate env s [e] = (s',Rval vs) ==> (?y. vs = [y]))`,
  CHEAT_TAC);;

(* evaluate_append *)
let flatProps_evaluate_append = prove
 (`flatSem_evaluate env s (APPEND l1 l2) =
   (match flatSem_evaluate env s l1 with (s,Rval v1) ->
     (match flatSem_evaluate env s l2 with (s,Rval v2) -> (s,Rval
       (APPEND v1 v2)) | r -> r) | r -> r)`,
  CHEAT_TAC);;

let do_app_state_unchanged = prove
 (`!c s op vs s' r. flatSem_do_app s op vs = SOME (s',r) ==>
  flatSem_state_eval_config
      s' = flatSem_state_eval_config s`,
  CHEAT_TAC);;

(* evaluate_decs_append *)
let flatProps_evaluate_decs_append = prove
 (`!s ds1 s1 s2 r ds2.
     flatSem_evaluate_decs s (APPEND ds1 ds2) =
     (match flatSem_evaluate_decs s ds1 with (s1,NONE) ->
       flatSem_evaluate_decs s1 ds2 | (s1,SOME err) -> (s1,SOME err))`,
  CHEAT_TAC);;

(* do_app_add_to_clock[local] *)
let flatProps_do_app_add_to_clock = prove
 (`flatSem_do_app (s:('c,'ffi)flatSem_state) op es = SOME (t,r) ==>
    flatSem_do_app (flatSem_state_clock_fupd (K (flatSem_state_clock
      s + k)) s) op es =
      SOME (state_clock_fupd (K (state_clock t + k)) t,r)`,
  CHEAT_TAC);;

(* [local] *)
let do_app_add_to_clock_NONE = prove
 (`flatSem_do_app (s:('c,'ffi)flatSem_state) op es = NONE ==>
    flatSem_do_app (flatSem_state_clock_fupd (K
      (flatSem_state_clock s + k)) s) op es = NONE`,
  CHEAT_TAC);;

(* evaluate_add_to_clock *)
let flatProps_evaluate_add_to_clock = prove
 (`(!env (s:('c,'ffi)flatSem_state) es s' r.
       flatSem_evaluate env s es = (s',r) /\ ~(r = Rerr (Rabort
         Rtimeout_error)) ==>
       flatSem_evaluate env (flatSem_state_clock_fupd (K
         (flatSem_state_clock s + extra)) s) es =
         (state_clock_fupd (K (state_clock s' + extra)) s',r)) /\
   (!(s:('c,'ffi)flatSem_state) d s' r.
       evaluate_dec s d = (s',r) /\ ~(r = SOME (Rabort
         Rtimeout_error)) ==>
       evaluate_dec (flatSem_state_clock_fupd (K (flatSem_state_clock
         s + extra)) s) d =
         (state_clock_fupd (K (state_clock s' + extra)) s',r)) /\
   (!(s:('c,'ffi)flatSem_state) ds s' r.
       flatSem_evaluate_decs s ds = (s',r) /\ ~(r = SOME (Rabort
         Rtimeout_error)) ==>
       flatSem_evaluate_decs (flatSem_state_clock_fupd (K
         (flatSem_state_clock s + extra)) s) ds =
         (state_clock_fupd (K (state_clock s' + extra)) s',r))`,
  CHEAT_TAC);;

(* evaluate_decs_add_to_clock *)
let flatProps_evaluate_decs_add_to_clock = prove
 (`!decs s s' r. ~(r = SOME (Rabort Rtimeout_error)) /\
    flatSem_evaluate_decs s decs = (s',r) ==>
    flatSem_evaluate_decs (state_clock_fupd (K (state_clock s +
      extra)) s) decs =
    (state_clock_fupd (K (state_clock s' + extra)) s',r)`,
  CHEAT_TAC);;

(* do_app_io_events_mono *)
let flatProps_do_app_io_events_mono = prove
 (`flatSem_do_app (s:('c,'ffi)flatSem_state) op vs = SOME (t,r) ==>
  ffi_state_io_events (flatSem_state_ffi
   s) <<= ffi_state_io_events (state_ffi t)`,
  CHEAT_TAC);;

(* evaluate_io_events_mono *)
let flatProps_evaluate_io_events_mono = prove
 (`(!env (s:('c,'ffi)flatSem_state) es. ffi_state_io_events
  (flatSem_state_ffi
      s) <<= ffi_state_io_events (state_ffi (FST (flatSem_evaluate
        env s es)))) /\
   (!(s:('c,'ffi)flatSem_state) d. ffi_state_io_events
     (flatSem_state_ffi
      s) <<= ffi_state_io_events (state_ffi (FST (evaluate_dec s
        d)))) /\
   (!(s:('c,'ffi)flatSem_state) ds. ffi_state_io_events
     (flatSem_state_ffi
      s) <<= ffi_state_io_events (state_ffi (FST
        (flatSem_evaluate_decs s ds))))`,
  CHEAT_TAC);;

let evaluate_io_events_mono_IMP = prove
 (`(flatSem_evaluate env s es = (s',r) ==> ffi_state_io_events
  (state_ffi
      s) <<= ffi_state_io_events (state_ffi s')) /\
   (evaluate_dec s d = (s',r') ==> ffi_state_io_events (state_ffi
      s) <<= ffi_state_io_events (state_ffi s')) /\
   (flatSem_evaluate_decs s ds = (s',r'') ==> ffi_state_io_events
     (state_ffi
      s) <<= ffi_state_io_events (state_ffi s'))`,
  CHEAT_TAC);;

(* with_clock_ffi *)
let flatProps_with_clock_ffi = prove
 (`state_ffi
      (state_clock_fupd (K k) s) = state_ffi s`,
  CHEAT_TAC);;

(* evaluate_add_to_clock_io_events_mono *)
let flatProps_evaluate_add_to_clock_io_events_mono = prove
 (`(!env (s:('c,'ffi)flatSem_state) es. ffi_state_io_events (state_ffi
       (FST (flatSem_evaluate env s es))) <<= ffi_state_io_events
         (state_ffi
       (FST (flatSem_evaluate env (flatSem_state_clock_fupd (K
         (flatSem_state_clock s + extra)) s) es)))) /\
   (!(s:('c,'ffi)flatSem_state) d. ffi_state_io_events (state_ffi
       (FST (evaluate_dec s d))) <<= ffi_state_io_events (state_ffi
       (FST (evaluate_dec (flatSem_state_clock_fupd (K
         (flatSem_state_clock s + extra)) s) d)))) /\
   (!(s:('c,'ffi)flatSem_state) ds. ffi_state_io_events (state_ffi
       (FST (flatSem_evaluate_decs s ds))) <<= ffi_state_io_events
         (state_ffi
       (FST (flatSem_evaluate_decs (flatSem_state_clock_fupd (K
         (flatSem_state_clock s + extra)) s) ds))))`,
  CHEAT_TAC);;

let evaluate_dec_io_events_mono = prove
 (`!z y. ffi_state_io_events (state_ffi
      y) <<= ffi_state_io_events (state_ffi (FST (evaluate_dec y
        z)))`,
  (REWRITE_TAC[flatProps_evaluate_io_events_mono]));;

let evaluate_dec_add_to_clock_io_events_mono = prove
 (`!prog (s:('c,'ffi)flatSem_state) extra. ffi_state_io_events
  (state_ffi
    (FST (evaluate_dec s prog))) <<= ffi_state_io_events (state_ffi
    (FST (evaluate_dec (flatSem_state_clock_fupd (K
      (flatSem_state_clock s + extra)) s) prog)))`,
  (REWRITE_TAC[flatProps_evaluate_add_to_clock_io_events_mono]));;

let evaluate_decs_io_events_mono = prove
 (`!ds (s:('c,'ffi)flatSem_state) s' y. flatSem_evaluate_decs s ds =
  (s',y) ==> ffi_state_io_events (flatSem_state_ffi
    s) <<= ffi_state_io_events (state_ffi s')`,
  (REWRITE_TAC[evaluate_io_events_mono_IMP]));;

(* evaluate_decs_add_to_clock_io_events_mono *)
let flatProps_evaluate_decs_add_to_clock_io_events_mono = prove
 (`!ds (s:('c,'ffi)flatSem_state) extra. ffi_state_io_events (state_ffi
     (FST (flatSem_evaluate_decs s ds))) <<= ffi_state_io_events
       (state_ffi
     (FST (flatSem_evaluate_decs (flatSem_state_clock_fupd (K
       (flatSem_state_clock s + extra)) s) ds)))`,
  CHEAT_TAC);;

let evaluate_MAP_Var_local = prove
 (`MAP (ALOOKUP (flatSem_environment_v env)) xs = MAP SOME vs ==>
   flatSem_evaluate env s (MAP (flatLang_Var_local t) xs) = (s,Rval
     vs)`,
  CHEAT_TAC);;

let bind_locals_list_def = new_definition
  `bind_locals_list ts ks = MAP2 (\t x. (flatLang_Var_local t x)) ts
  ks`;;

let evaluate_vars = prove
 (`!env s kvs env' ks vs ts.
    ALL_DISTINCT (MAP FST kvs) /\
    DISJOINT (set_of_list (MAP FST kvs)) (set_of_list (MAP FST env'))
      /\ flatSem_environment_v
    env = APPEND env' kvs /\ ks = MAP FST kvs /\ vs = MAP SND kvs /\
    LENGTH ts = LENGTH ks ==>
    flatSem_evaluate env s (bind_locals_list ts ks) = (s,Rval vs)`,
  CHEAT_TAC);;

(* HOL4 flatPropsScript.sml:546-605: code that the source has in a
   comment *)

let pmatch_list_MAP_Pvar = prove
 (`!xs vs. LENGTH xs = LENGTH vs ==>
   flatSem_pmatch_list s (MAP flatLang_Pvar xs) vs [] = Match
     (REVERSE (ZIP xs vs))`,
  CHEAT_TAC);;

(* [local] *)
let evaluate_decs_add_to_clock_initial_state = prove
 (`~(r = SOME (Rabort Rtimeout_error)) /\
      flatSem_evaluate_decs (flatSem_initial_state ffi k ec) decs =
        (s',r) ==>
      flatSem_evaluate_decs (flatSem_initial_state ffi (ck + k) ec)
        decs =
      (state_clock_fupd (K (state_clock s' + ck)) s',r)`,
  CHEAT_TAC);;

(* [local] *)
let evaluate_decs_add_to_clock_initial_state_io_events_mono = prove
 (`flatSem_evaluate_decs (flatSem_initial_state ffi k ec) prog = (s',r)
  ==> ffi_state_io_events (state_ffi
    s') <<= ffi_state_io_events (state_ffi
    (FST (flatSem_evaluate_decs (flatSem_initial_state ffi (k + ck)
      ec) prog)))`,
  CHEAT_TAC);;

(* initial_state_with_clock[local] *)
let flatProps_initial_state_with_clock = prove
 (`(state_clock_fupd (K (state_clock (flatSem_initial_state ffi k ec) +
  ck)) (flatSem_initial_state ffi k ec)) =
    flatSem_initial_state ffi (k + ck) ec`,
  CHEAT_TAC);;

(* [local] *)
let SND_SND_lemma = prove
 (`(SND x) = y <=> (?y1. x = (y1,y))`,
  (MESON_TAC[PAIR; FST; SND]));;

let flatProps_eval_sim_def = new_definition
  `flatProps_eval_sim ffi ds1 ds2 ec ec2 rel allow_fail =
     (!k res1 s2.
       flatSem_evaluate_decs (flatSem_initial_state ffi k ec) ds1 =
         (s2,res1) /\
       (allow_fail \/ ~(res1 = SOME (Rabort Rtype_error))) /\
       rel ds1 ds2 ==>
       (?ck res2 t2.
         flatSem_evaluate_decs (flatSem_initial_state ffi (k + ck)
           ec2) ds2 =
           (t2,res2) /\ state_ffi
         s2 = state_ffi t2 /\
         (res1 = NONE ==> res2 = NONE) /\
         (!v. res1 = SOME (Rraise v) ==> (?v1. res2 = SOME (Rraise
           v1))) /\
         (!a. res1 = SOME (Rabort a) ==> res2 = SOME (Rabort a))))`;;

(* IMP_semantics_eq *)
(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let flatProps_IMP_semantics_eq = prove
 (cake_as_vars (fun () ->
    `flatProps_eval_sim ffi ds1 ds2 ec ec2 rel F /\ ~(flatSem_semantics
  ec (ffi:'ffi ffi_state) ds1 = ffi_Fail) ==>
     rel ds1 ds2 ==>
     flatSem_semantics ec ffi ds1 =
     flatSem_semantics ec2 ffi ds2`),
  CHEAT_TAC);;

let flatProps_op_gbag_def = new_definition
  `flatProps_op_gbag x1 =
      match x1 with
        flatLang_GlobalVarInit n -> BAG_INSERT n EMPTY_BAG
      | _4 -> EMPTY_BAG`;;

let flatProps_set_globals_def,flatProps_set_globals_ind =
  assume_definition_rec
  "termination (CHEAT_TAC)"
  [`flatProps_set_globals (flatLang_Raise t e:flatLang_exp) =
  flatProps_set_globals e`;
   `flatProps_set_globals (flatLang_Handle t e pes:flatLang_exp) =
  (BAG_UNION) (flatProps_set_globals e) (flatProps_elist_globals (MAP
  SND pes))`;
   `flatProps_set_globals (flatLang_Con t id' es:flatLang_exp) =
  flatProps_elist_globals es`;
   `flatProps_set_globals (flatLang_Fun t v e:flatLang_exp) =
  flatProps_set_globals e`;
   `flatProps_set_globals (flatLang_App t op es:flatLang_exp) =
  (BAG_UNION) (flatProps_elist_globals es) (flatProps_op_gbag op)`;
   `flatProps_set_globals (flatLang_If t e1 e2 e3:flatLang_exp) =
  (BAG_UNION) ((BAG_UNION) (flatProps_set_globals e1)
  (flatProps_set_globals e2)) (flatProps_set_globals e3)`;
   `flatProps_set_globals (flatLang_Mat t e pes:flatLang_exp) =
  (BAG_UNION) (flatProps_set_globals e) (flatProps_elist_globals (MAP
  SND pes))`;
   `flatProps_set_globals (flatLang_Let t v e1 e2:flatLang_exp) =
  (BAG_UNION) (flatProps_set_globals e1) (flatProps_set_globals e2)`;
   `flatProps_set_globals (flatLang_Letrec t fs e:flatLang_exp) =
  (BAG_UNION) (flatProps_set_globals e) (flatProps_elist_globals (MAP
  (SND o SND) fs))`;
   `flatProps_set_globals _5 = EMPTY_BAG`;
   `flatProps_elist_globals [] = EMPTY_BAG`;
   `flatProps_elist_globals (CONS e es) = (BAG_UNION)
  (flatProps_set_globals e) (flatProps_elist_globals es)`];;


let _ = size_thms "flatLang_exp";;
(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 flatPropsScript.sml:850-856: the tactic that proves the
   termination *)
let flatProps_esgc_free_def,flatProps_esgc_free_ind = define_wf
  `MEASURE flatLang_exp_size`
  [`flatProps_esgc_free x1 =
        match x1 with
          (flatLang_Raise t e:flatLang_exp) -> flatProps_esgc_free e
        | (flatLang_Handle t e pes) ->
       flatProps_esgc_free e /\ ALL flatProps_esgc_free (MAP SND
         pes)
        | (flatLang_Con t id' es) -> ALL flatProps_esgc_free es
        | (flatLang_Fun t v e) -> flatProps_set_globals e =
          EMPTY_BAG
        | (flatLang_App t op es) -> ALL flatProps_esgc_free es
        | (flatLang_If t e1 e2 e3) ->
       flatProps_esgc_free e1 /\ flatProps_esgc_free e2 /\
         flatProps_esgc_free e3
        | (flatLang_Mat t e pes) -> flatProps_esgc_free e /\ ALL
          flatProps_esgc_free (MAP SND pes)
        | (flatLang_Let t v e1 e2) -> flatProps_esgc_free e1 /\
          flatProps_esgc_free e2
        | (flatLang_Letrec t fs e) ->
       flatProps_esgc_free e /\ flatProps_elist_globals (MAP (SND o
         SND) fs) = EMPTY_BAG
        | _6 -> T`];;

(* HOL4 flatPropsScript.sml:858-859: a theorem that HOL4 states as
   the value of an ML expression: esgc_free_def *)

let elist_globals_eq_empty = prove
 (`flatProps_elist_globals l = EMPTY_BAG <=> (!e. MEM e l ==>
  flatProps_set_globals e = EMPTY_BAG)`,
  CHEAT_TAC);;

(* elist_globals_append *)
let flatProps_elist_globals_append = prove
 (`flatProps_elist_globals (APPEND xs ys) = (BAG_UNION)
  (flatProps_elist_globals xs) (flatProps_elist_globals ys)`,
  CHEAT_TAC);;

(* elist_globals_FOLDR *)
let flatProps_elist_globals_FOLDR = prove
 (`flatProps_elist_globals es = ITLIST (BAG_UNION) (MAP
  flatProps_set_globals es) EMPTY_BAG`,
  CHEAT_TAC);;

let elist_globals_REVERSE = prove
 (`flatProps_elist_globals (REVERSE es) = flatProps_elist_globals es`,
  CHEAT_TAC);;

(* initial_state_clock *)
let flatProps_initial_state_clock = prove
 (`state_clock
     (flatSem_initial_state ffi k ec) = k /\
     ((state_clock_fupd (K k1) (flatSem_initial_state ffi k ec)) =
       flatSem_initial_state ffi k1 ec)`,
  CHEAT_TAC);;

let build_rec_env_eq_MAP = prove
 (`flatSem_build_rec_env funs cl_env env = APPEND (MAP (\(f,x,e).
  (f,flatSem_Recclosure cl_env funs f)) funs) env`,
  CHEAT_TAC);;

let evaluate_decs_add_to_clock_io_events_mono_alt = prove
 (`flatSem_evaluate_decs (s:('c,'ffi)flatSem_state) ds = (s1,res) /\
   flatSem_evaluate_decs (flatSem_state_clock_fupd (K
     (flatSem_state_clock s + extra)) s) ds = (s2,res2) ==>
     ffi_state_io_events (state_ffi
   s1) <<= ffi_state_io_events (state_ffi s2)`,
  (REPEAT STRIP_TAC THEN
   MP_TAC(ISPECL [`ds:flatLang_exp list`;
     `s:(C,ast_FFI)flatSem_state`; `extra:num`]
            flatProps_evaluate_decs_add_to_clock_io_events_mono) THEN
   ASM_REWRITE_TAC[FST]));;

(* generic proof support for most val_rel/state_rel examples *)

let isClosure_def = new_definition
  `isClosure exp = (
     (?vs n x. exp = flatSem_Closure vs n x) \/
     (?vs fs x. exp = flatSem_Recclosure vs fs x))`;;

(* HOL4 flatPropsScript.sml:921-923: ML code, not ported *)

(* HOL4 flatPropsScript.sml:925-927: a theorem that HOL4 states as
   the value of an ML expression: isClosure_simps *)

let simple_basic_val_rel_def = define_cases
  [`simple_basic_val_rel (flatSem_Litv l:flatSem_v) v = (v =
  (flatSem_Litv l:flatSem_v))`;
   `simple_basic_val_rel (flatSem_Loc b i:flatSem_v) v = (v =
  (flatSem_Loc b i:flatSem_v))`;
   `simple_basic_val_rel (flatSem_Conv stmp vs1:flatSem_v) v = (?vs2.
  v = flatSem_Conv stmp vs2)`;
   `simple_basic_val_rel (flatSem_Vectorv vs1:flatSem_v) v = (?vs2. v
  = flatSem_Vectorv vs2)`;
   `simple_basic_val_rel (flatSem_Closure vs nm exp:flatSem_v) v = F`;
   `simple_basic_val_rel (flatSem_Recclosure vs exps nm:flatSem_v)
  v = F`];;

let v_container_xs_def = define_cases
  [`v_container_xs (flatSem_Litv _8:flatSem_v) = []`;
   `v_container_xs (flatSem_Loc _11 _12:flatSem_v) = []`;
   `v_container_xs (flatSem_Conv _14 vs:flatSem_v) = vs`;
   `v_container_xs (flatSem_Vectorv vs:flatSem_v) = vs`;
   `v_container_xs (flatSem_Closure vs nm exp:flatSem_v) = []`;
   `v_container_xs (flatSem_Recclosure vs exps nm:flatSem_v) = []`];;

let flatProps_simple_val_rel_def = new_definition
  `flatProps_simple_val_rel vr = (
     (!v1 v2. (vr v1 v2 ==> isClosure v1 = isClosure v2)) /\ (!v1 v2.
       ~(isClosure v1) ==> vr v1 v2 = (
         simple_basic_val_rel v1 v2 /\ ALL2 vr (v_container_xs v1)
           (v_container_xs v2))))`;;

(* HOL4 flatPropsScript.sml:953-954: a theorem that HOL4 states as
   the value of an ML expression: simple_val_rel_rew *)

(* HOL4 flatPropsScript.sml:956-960: a theorem that HOL4 states as
   the value of an ML expression: simple_val_rel_simps *)

let simple_val_rel_isClosure = prove
 (`flatProps_simple_val_rel vr /\ vr x y ==> (isClosure x = isClosure
  y)`,
  (REWRITE_TAC[flatProps_simple_val_rel_def] THEN MESON_TAC[]));;

let flatProps_simple_state_rel_def = new_definition
  `flatProps_simple_state_rel vr sr <=>
     (!s t. sr s t ==> ALL2 (semanticPrimitivesProps_sv_rel vr)
       (state_refs s) (state_refs t)) /\
     (!s t srefs trefs.
         sr s t /\ ALL2 (semanticPrimitivesProps_sv_rel vr) srefs
           trefs ==> sr (state_refs_fupd (K srefs) s) (state_refs_fupd
           (K trefs) t)) /\
     (!s t. sr s t ==> ALL2 (OPTREL vr) (flatSem_state_globals s)
       (flatSem_state_globals t)) /\
     (!s t sglob tglob.
         sr s t /\ ALL2 (OPTREL vr) sglob tglob ==> sr
           (flatSem_state_globals_fupd (K sglob) s)
           (flatSem_state_globals_fupd (K tglob) t)) /\
     (!s t. sr s t ==> state_ffi s = state_ffi t) /\
     (!s t sffi tffi.
         sr s t /\ sffi = tffi ==> sr (state_ffi_fupd (K sffi) s)
           (state_ffi_fupd (K tffi) t))`;;

let simple_do_eq_thm_ind = prove
 (`(!x1 y1 x2 y2 b.
   flatProps_simple_val_rel vr /\
   flatSem_do_eq x1 y1 = Eq_val b /\
   vr x1 x2 /\ vr y1 y2 ==>
   flatSem_do_eq x2 y2 = Eq_val b) /\
   (!x1 y1 x2 y2 b.
   flatProps_simple_val_rel vr /\
   flatSem_do_eq_list x1 y1 = Eq_val b /\
   ALL2 vr x1 x2 /\ ALL2 vr y1 y2 ==>
   flatSem_do_eq_list x2 y2 = Eq_val b)`,
  CHEAT_TAC);;

(* HOL4 flatPropsScript.sml:1005: a theorem that HOL4 states as the
   value of an ML expression: simple_do_eq_thm *)

let simple_state_rel_store_assign = prove
 (`flatProps_simple_state_rel vr sr /\
   store_assign lnum x (state_refs s) = SOME srefs' /\
   sr s t /\ semanticPrimitivesProps_sv_rel vr x y ==>
   (?trefs'. store_assign lnum y (state_refs t) = SOME trefs' /\
   sr (state_refs_fupd (K srefs') s) (state_refs_fupd (K trefs')
     t))`,
  CHEAT_TAC);;

let simple_state_rel_store_alloc = prove
 (`flatProps_simple_state_rel vr sr /\
   store_alloc x (state_refs s) = (srefs',lnum) /\
   sr s t /\ semanticPrimitivesProps_sv_rel vr x y ==>
   (?trefs'. store_alloc y (state_refs t) = (trefs',lnum) /\
   sr (state_refs_fupd (K srefs') s) (state_refs_fupd (K trefs')
     t))`,
  CHEAT_TAC);;

let simple_state_rel_store_lookup = prove
 (`flatProps_simple_state_rel vr sr /\
   store_lookup lnum (state_refs s) = SOME x /\
   sr s t ==>
   (?y. store_lookup lnum (state_refs t) = SOME y /\
     semanticPrimitivesProps_sv_rel vr x y)`,
  CHEAT_TAC);;

let simple_v_to_char_list_v_rel = prove
 (`flatProps_simple_val_rel vr ==>
   (!x y ls. vr x y /\ flatSem_v_to_char_list x = SOME ls ==>
     flatSem_v_to_char_list y = SOME ls)`,
  CHEAT_TAC);;

let simple_v_to_list_v_rel = prove
 (`flatProps_simple_val_rel vr ==>
   (!x y ls. vr x y /\ flatSem_v_to_list x = SOME ls ==>
   (?ls'. flatSem_v_to_list y = SOME ls' /\ ALL2 vr ls ls'))`,
  CHEAT_TAC);;

let simple_v_rel_list_to_v = prove
 (`flatProps_simple_val_rel vr ==>
   (!x y. ALL2 vr x y ==> vr (flatSem_list_to_v x)
     (flatSem_list_to_v y))`,
  CHEAT_TAC);;

let simple_vs_to_string_v_rel = prove
 (`flatProps_simple_val_rel vr ==>
   (!vs ws str. ALL2 vr vs ws /\ flatSem_vs_to_string vs = SOME str
     ==>
   flatSem_vs_to_string ws = SOME str)`,
  CHEAT_TAC);;

(* simple_val_rel_v_to_words *)
let flatProps_simple_val_rel_v_to_words = prove
 (`flatProps_simple_val_rel vr ==>
   (!x y ws. vr x y /\ flatSem_v_to_words x = SOME ws ==>
   flatSem_v_to_words y = SOME ws)`,
  CHEAT_TAC);;

(* simple_val_rel_v_to_bytes *)
let flatProps_simple_val_rel_v_to_bytes = prove
 (`flatProps_simple_val_rel vr ==>
   (!x y ws. vr x y /\ flatSem_v_to_bytes x = SOME ws ==>
   flatSem_v_to_bytes y = SOME ws)`,
  CHEAT_TAC);;

(* [local] *)
let check_type_LIST_REL_same = prove
 (`ALL2 vr vs1 vs2 /\
   ALL (flatSem_check_type ty) (MAP flat_to_v vs1) /\
   flatProps_simple_val_rel vr ==>
   vs2 = vs1`,
  CHEAT_TAC);;

(* HOL4 flatPropsScript.sml:1157: ML code, not ported *)

let simple_do_app_thm = prove
 (`flatProps_simple_val_rel vr /\
   flatProps_simple_state_rel vr sr ==>
   (!s1 vs1 t1 r1 s2 vs2.
   flatSem_do_app s1 op vs1 = SOME (t1,r1) ==>
   sr s1 s2 /\ ALL2 vr vs1 vs2 ==>
   (?t2 r2. semanticPrimitivesProps_result_rel vr vr r1 r2 /\
   sr t1 t2 /\ flatSem_do_app s2 op vs2 = SOME (t2,r2)))`,
  CHEAT_TAC);;

let evaluate_match_def = new_definition
  `flatProps_evaluate_match env s v pes err_v =
     (match pmatch_rows pes s v with Match_type_error -> (s,Rerr
       (Rabort Rtype_error)) | No_match -> (s,Rerr (Rraise err_v)) |
       Match (env',p',e') ->
         (if ALL_DISTINCT (flatLang_pat_bindings p') then
           flatSem_evaluate (flatSem_environment_v_fupd (K (APPEND
           env' (flatSem_environment_v env))) env) s [e'] else
           (s,Rerr (Rabort Rtype_error))))`;;

let evaluate_Mat = prove
 (`flatSem_evaluate env s [(flatLang_Mat tra e pes:flatLang_exp)] =
   (match flatSem_evaluate env s [e] with (s,Rval v) ->
       (if ~(pmatch_rows pes s (HD v) = Match_type_error) then
         flatProps_evaluate_match env s (HD v) pes flatSem_bind_exn_v
         else (s,Rerr (Rabort Rtype_error))) | res -> res)`,
  CHEAT_TAC);;

let evaluate_Handle = prove
 (`flatSem_evaluate env s [(flatLang_Handle _16 e pes:flatLang_exp)] =
   (match flatSem_evaluate env s [e] with (s,Rerr (Rraise v)) ->
       (if ~(pmatch_rows pes s v = Match_type_error) then
         flatProps_evaluate_match env s v pes v else (s,Rerr (Rabort
         Rtype_error))) | res -> res)`,
  CHEAT_TAC);;

let evaluate_match_NIL = prove
 (`flatProps_evaluate_match env s v [] err_v =
     (s,Rerr (Rraise err_v))`,
  CHEAT_TAC);;

let evaluate_match_CONS = prove
 (`flatProps_evaluate_match env s v (CONS (p,e) pes) err_v =
     (match flatSem_pmatch s p v [] with No_match ->
       flatProps_evaluate_match env s v pes err_v | Match_type_error ->
       (s,Rerr (Rabort Rtype_error)) | Match env_v' ->
         (if ALL_DISTINCT (flatLang_pat_bindings p) /\
           ~(pmatch_rows pes s v = Match_type_error) then
           flatSem_evaluate (flatSem_environment_v_fupd (K (APPEND
           env_v' (flatSem_environment_v env))) env) s [e] else
           (s,Rerr (Rabort Rtype_error))))`,
  CHEAT_TAC);;

(* HOL4 flatPropsScript.sml:1432-1446: the ML values that the
   definitions below antiquote *)

(* HOL4 flatPropsScript.sml:1448: a theorem that HOL4 states as the
   value of an ML expression: flat_evaluate_def *)

let flatProps_store_v_vs_def = define_cases
  [`flatProps_store_v_vs (semanticPrimitives_Varray vs) = vs`;
   `flatProps_store_v_vs (semanticPrimitives_Refv v) = [v]`;
   `flatProps_store_v_vs (semanticPrimitives_Thunk m v) = [v]`;
   `flatProps_store_v_vs (semanticPrimitives_W8array xs) = []`];;

let result_vs_def = new_definition
  `result_vs x1 =
      match x1 with
        Rval xs -> xs
      | (Rerr (Rraise x)) -> [x]
      | (Rerr (Rabort y)) -> []`;;

(* HOL4 flatPropsScript.sml:1463-1469: a theorem whose statement the
   port cannot state yet: v_size_aux *)

let no_Mat_def,no_Mat_ind = assume_definition_rec
  "termination (CHEAT_TAC)"
  [`no_Mat (flatLang_Raise t e) <=> no_Mat e`;
   `no_Mat (flatLang_Lit t l:flatLang_exp) <=> T`;
   `no_Mat (flatLang_Var_local t v) <=> T`;
   `no_Mat (flatLang_Con t n es:flatLang_exp) <=> ALL no_Mat es`;
   `no_Mat (flatLang_App t op es:flatLang_exp) <=> ALL no_Mat es`;
   `no_Mat (flatLang_Fun t v e:flatLang_exp) <=> no_Mat e`;
   `no_Mat (flatLang_If t x1 x2 x3:flatLang_exp) <=> no_Mat x1 /\
  no_Mat x2 /\ no_Mat x3`;
   `no_Mat (flatLang_Let t vo e1 e2:flatLang_exp) <=> no_Mat e1 /\
  no_Mat e2`;
   `no_Mat (flatLang_Mat t e pes:flatLang_exp) <=> F`;
   `no_Mat (flatLang_Handle t e pes:flatLang_exp) <=> no_Mat e /\ ALL
  no_Mat (MAP SND pes) /\
        (match pes with [(flatLang_Pvar _24,_25)] -> T | _26 ->
          F)`;
   `no_Mat (flatLang_Letrec t funs e:flatLang_exp) <=> ALL no_Mat
  (MAP (SND o SND) funs) /\ no_Mat e`];;

let no_Mat_decs_def,no_Mat_decs_ind = define_rec
  [`no_Mat_decs [] = T`;
   `no_Mat_decs (CONS e xs) = (no_Mat e /\ no_Mat_decs xs)`];;

let mk_flat_install_conf_def = new_definition
  `flatProps_mk_flat_install_conf cc co =
     (mk_install_config cc co:'c install_config)`;;

(* and the names that this file reads as variables are constants again *)
let _ = do_list unhide_constant
  ["C"];;

(* and the overloads that this file cannot see are back in the
   interface *)
let _ = unhide_overloads ();;
