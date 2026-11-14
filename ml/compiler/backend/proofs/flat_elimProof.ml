(* ======================================================== *)
(*  flat_elimProof: ported from HOL4's
    compiler/backend/proofs/flat_elimProofScript.sml
    A proof theory about flat_elim.ml, with 9 definitions and 63
    theorems.  Needed by source_to_flatProof.ml.  *)
(* ======================================================== *)

(*
  Correctness proof for flatLang dead code elimination
*)

needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/flatLang.ml";;
needs "compiler/backend/flat_elim.ml";;
needs "compiler/backend/semantics/flatProps.ml";;
needs "compiler/backend/semantics/flatSem.ml";;
needs "lib/spt_closure.ml";;
needs "lib/sptree.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "semantics/evaluate.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;
needs "semantics/semanticPrimitives.ml";;

(* the theories whose names the Ancestors blocks of the source
   bring, which are the ones that its statements read: the
   overloads of every other theory come out of the interface
   while this file loads *)
let _ = hol4_ancestors "flat_elimProof"
  ["ast"; "ffi"; "flatLang"; "flatProps"; "flatSem"; "flat_elim";
   "misc"];;

(************************** LEMMAS ***************************)

(* HOL4 flat_elimProofScript.sml:15-56: code that the source has in a
   comment *)

let is_pure_EVERY_aconv = prove
 (`!es. ALL (\a. flat_elim_is_pure a) es = ALL flat_elim_is_pure es`,
  (REWRITE_TAC[ETA_AX]));;

let find_lookupsL_MEM = prove
 (`!e es. MEM e es ==> domain (find_lookups e) SUBSET domain
  (find_lookupsL es)`,
  CHEAT_TAC);;

let find_lookupsL_APPEND = prove
 (`!l1 l2. find_lookupsL (APPEND l1 l2) =
      sptree_union (find_lookupsL l1) (find_lookupsL l2)`,
  CHEAT_TAC);;

let find_lookupsL_REVERSE = prove
 (`!l. find_lookupsL l = find_lookupsL (REVERSE l)`,
  CHEAT_TAC);;

let find_loc_EVERY_isEmpty = prove
 (`!l (reachable:1 spt).
      ALL (\e. (\t. t = LN) (inter (find_loc e) reachable)) l <=>
        (\t. t = LN) (inter (find_locL l) reachable)`,
  CHEAT_TAC);;


(************************** DEFINITIONS ***************************)

(* HOL4 flat_elimProofScript.sml:99-105: a theorem whose statement
   the port cannot state yet: SUM_MAP_v3_size *)

(* the termination relation that HOL4 gives is
     MEASURE (\e. match e with INL x -> flatSem_v_size x | INR y ->
       list_size flatSem_v_size y)
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 flat_elimProofScript.sml:118-126: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let find_v_globals_def,find_v_globals_ind = define_mutual_guess_cheat
  [`find_v_globals (Conv _2 vl:flatSem_v) = ((find_v_globalsL vl):1
  spt)`;
   `find_v_globals (Closure env _4 e:flatSem_v) =
            ((sptree_union (find_v_globalsL (MAP SND
              (flatSem_environment_v env))) (find_lookups e)):1 spt)`;
   `find_v_globals (Recclosure env vves _6:flatSem_v) =
            ((sptree_union (find_v_globalsL (MAP SND
              (flatSem_environment_v env)))
                (find_lookupsL (MAP (SND o SND) vves))):1 spt)`;
   `find_v_globals (Vectorv vl:flatSem_v) = ((find_v_globalsL vl):1
  spt)`;
   `find_v_globals _7 = ((LN):1 spt)`;
   `find_v_globalsL [] = LN`;
   `find_v_globalsL (CONS h t) = sptree_union (find_v_globals h)
  (find_v_globalsL t)`];;

(* HOL4 flat_elimProofScript.sml:128: ML code, not ported *)

let find_v_globalsL_APPEND = prove
 (`!l1 l2. find_v_globalsL (APPEND l1 l2) =
      sptree_union (find_v_globalsL l1) (find_v_globalsL l2)`,
  CHEAT_TAC);;

let find_v_globalsL_REVERSE = prove
 (`!l. find_v_globalsL l = find_v_globalsL (REVERSE l)`,
  CHEAT_TAC);;

let find_v_globalsL_MEM = prove
 (`!k v vs.
   MEM (k,v) vs ==> domain (find_v_globals v) SUBSET domain
     (find_v_globalsL (MAP SND vs))`,
  CHEAT_TAC);;

let find_v_globalsL_EL = prove
 (`!n vs. n < LENGTH vs ==>
   domain (find_v_globals (EL n vs)) SUBSET domain (find_v_globalsL
     vs)`,
  CHEAT_TAC);;

(* [local] *)
let find_v_globalsL_EL_trans = prove
 (`n < LENGTH vs /\ domain (find_v_globalsL vs) SUBSET R ==>
   domain (find_v_globals (EL n vs)) SUBSET R`,
  (MESON_TAC[find_v_globalsL_EL; SUBSET_TRANS]));;

let find_v_globals_MAP_Recclosure = prove
 (`!funs v l.
   domain (find_v_globalsL (MAP (\x. Recclosure env l (f x)) funs)) =
   (if NULL funs then {} else domain (find_v_globalsL (MAP SND
     (flatSem_environment_v env))) UNION
           domain (find_lookupsL (MAP (SND o SND) l)))`,
  CHEAT_TAC);;

let find_v_globalsL_REPLICATE = prove
 (`!n v vs. domain (find_v_globalsL (REPLICATE n v)) SUBSET
      domain (find_v_globals v)`,
  CHEAT_TAC);;

let find_v_globalsL_LUPDATE = prove
 (`!n vs (reachable:1 spt) v.
   n < LENGTH vs /\
   domain (find_v_globalsL vs) SUBSET domain reachable /\
   domain (find_v_globals v) SUBSET domain reachable ==> domain
     (find_v_globalsL (LUPDATE v n vs)) SUBSET domain reachable`,
  CHEAT_TAC);;

let find_v_globals_v_to_list = prove
 (`!x (reachable:1 spt) xs.
      domain (find_v_globals x) SUBSET domain reachable /\
        v_to_list x = SOME xs ==> domain (find_v_globalsL xs) SUBSET
        domain reachable`,
  CHEAT_TAC);;

let find_v_globals_list_to_v = prove
 (`!xs (reachable:1 spt) x.
      domain (find_v_globalsL xs) SUBSET domain reachable /\
        list_to_v xs = x ==> domain (find_v_globals x) SUBSET domain
        reachable`,
  CHEAT_TAC);;

let _ = size_thms "flatSem_v";;
let _ = size_thms "store_v";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let find_refs_globals_def,find_refs_globals_ind = define_wf
  `MEASURE (\x0. list_size (store_v_size flatSem_v_size) x0)`
  [`find_refs_globals x1 =
        match x1 with
          CONS (semanticPrimitives_Refv a) t ->
           sptree_union (find_v_globals a) (find_refs_globals t)
        | (CONS (semanticPrimitives_Varray l) t) ->
           sptree_union (find_v_globalsL l) (find_refs_globals t)
        | (CONS (semanticPrimitives_Thunk _8 a) t) ->
           sptree_union (find_v_globals a) (find_refs_globals t)
        | (CONS _9 t) -> find_refs_globals t
        | [] -> LN`];;

(* HOL4 flat_elimProofScript.sml:225: ML code, not ported *)

let find_refs_globals_MEM = prove
 (`!refs (reachable:1 spt).
      domain (find_refs_globals refs) SUBSET R ==> (!a.
          MEM (semanticPrimitives_Refv a) refs ==> domain
            (find_v_globals a) SUBSET R) /\
      (!vs.
          MEM (semanticPrimitives_Varray vs) refs ==> domain
            (find_v_globalsL vs) SUBSET R) /\
      (!m a.
          MEM (semanticPrimitives_Thunk m a) refs ==> domain
            (find_v_globals a) SUBSET R)`,
  CHEAT_TAC);;

let find_refs_globals_EL = prove
 (`n < LENGTH refs /\ domain (find_refs_globals refs) SUBSET R ==>
     (!a.
             EL n refs = semanticPrimitives_Refv a ==> domain
               (find_v_globals a) SUBSET R) /\
     (!vs.
             EL n refs = semanticPrimitives_Varray vs ==> domain
               (find_v_globalsL vs) SUBSET R) /\
     (!m a.
             EL n refs = semanticPrimitives_Thunk m a ==> domain
               (find_v_globals a) SUBSET R)`,
  (MESON_TAC[MEM_EL; find_refs_globals_MEM]));;

let find_refs_globals_LUPDATE = prove
 (`!(reachable:1 spt) refs n.
      n < LENGTH refs /\ domain (find_refs_globals refs) SUBSET
        domain reachable ==>
      (!a.
          domain (find_v_globals a) SUBSET domain reachable ==>
              domain (find_refs_globals (LUPDATE
                (semanticPrimitives_Refv a) n refs)) SUBSET domain
                reachable) /\
   (!vs.
      domain (find_v_globalsL vs) SUBSET domain reachable ==>
          domain (find_refs_globals (LUPDATE
            (semanticPrimitives_Varray vs) n refs)) SUBSET domain
            reachable) /\
   (!ws.
      domain (find_refs_globals (LUPDATE (semanticPrimitives_W8array
        ws) n refs)) SUBSET domain reachable) /\
   (!m a.
      domain (find_v_globals a) SUBSET domain reachable ==>
          domain (find_refs_globals (LUPDATE
            (semanticPrimitives_Thunk m a) n refs)) SUBSET domain
            reachable)`,
  CHEAT_TAC);;

let find_refs_globals_APPEND = prove
 (`!refs new. find_refs_globals (APPEND refs new) =
      sptree_union (find_refs_globals refs) (find_refs_globals new)`,
  CHEAT_TAC);;

let find_env_globals_def = new_definition
  `find_env_globals env = find_v_globalsL (MAP SND
  (flatSem_environment_v env))`;;

let find_result_globals_def = new_definition
  `find_result_globals x1 =
        match x1 with
          SOME (Rraise v) -> find_v_globals v
        | _10 -> LN`;;

(* HOL4 flat_elimProofScript.sml:294: ML code, not ported *)

let find_sem_prim_res_globals_def = define_cases
  [`find_sem_prim_res_globals (Rerr e:(flatSem_v
  list,flatSem_v)semanticPrimitives_result) =
            find_result_globals (SOME e)`;
   `find_sem_prim_res_globals (Rval e) = find_v_globalsL e`];;

(* HOL4 flat_elimProofScript.sml:303-306: the ML values that the
   definitions below antiquote *)

(* the termination relation that HOL4 gives is
     MEASURE flatSem_v_size
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 flat_elimProofScript.sml:317-324: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let v_has_Eval_def1,v_has_Eval_def1_ind = define_guess_cheat
  [`v_has_Eval x1 =
        match x1 with
          (Closure env _12 e:flatSem_v) -> (has_Eval e \/
       EX v_has_Eval (MAP SND (flatSem_environment_v env)))
        | (Conv _13 vl) -> EX v_has_Eval vl
        | (Recclosure env nm_es _14) ->
       (EX v_has_Eval (MAP SND (flatSem_environment_v env)) \/
         EX has_Eval (MAP (SND o SND) nm_es))
        | (Vectorv vl) -> EX v_has_Eval vl
        | _15 -> F`];;

(* HOL4 flat_elimProofScript.sml:326: a theorem that HOL4 states as
   the value of an ML expression: v_has_Eval_def *)

(* s_g = state globals, t_g = removed state globals *)
let globals_rel_def = new_definition
  `globals_rel (reachable:1 spt) s_g t_g <=>
       LENGTH s_g = LENGTH t_g /\
       (!n.
         n IN domain reachable /\ n < LENGTH t_g ==> EL n s_g = EL n
           t_g) /\
       (!n x.
         n < LENGTH t_g /\ EL n t_g = SOME x ==> EL n s_g = SOME x)
           /\
       (!n.
         n < LENGTH t_g /\ EL n s_g = NONE ==> EL n t_g = NONE) /\
       (!n x.
           n IN domain reachable /\ n < LENGTH t_g /\
         EL n t_g = SOME x ==> ~(v_has_Eval x) /\ domain
           (find_v_globals x) SUBSET domain reachable)`;;

let globals_rel_trans = prove
 (`!reachable s1 s2 s3.
      globals_rel reachable s1 s2 /\ globals_rel reachable s2 s3
        ==> globals_rel reachable s1 s3`,
  (REWRITE_TAC[globals_rel_def] THEN MESON_TAC[]));;

let decs_closed_def = new_definition
  `decs_closed (reachable:1 spt) decs <=> (!r t.
   analyse_code decs = (r,t) ==> domain r SUBSET domain reachable /\
     (!n m.
     n IN domain reachable /\ is_reachable t n m ==> m IN domain
       reachable))`;;

let decs_closed_reduce = prove
 (`!reachable e t. decs_closed reachable (CONS e t) ==> decs_closed
  reachable t`,
  CHEAT_TAC);;

let decs_closed_reduce_HD = prove
 (`!reachable e t.
      decs_closed reachable (CONS e t) ==> decs_closed reachable
        [e]`,
  CHEAT_TAC);;

(* s = state, t = removed state *)
let flat_state_rel_def = new_definition
  `flat_state_rel reachable (s:('c,'ffi)flatSem_state)
  (t:('c,'ffi)flatSem_state) <=> flatSem_state_clock
     s = flatSem_state_clock t /\ flatSem_state_refs s =
       flatSem_state_refs t /\ flatSem_state_ffi
     s = flatSem_state_ffi t /\ globals_rel reachable
       (flatSem_state_globals s) (flatSem_state_globals t) /\
     domain (find_refs_globals (flatSem_state_refs s)) SUBSET domain
       reachable /\
     ALL (ALL ((~) o v_has_Eval) o store_v_vs) (flatSem_state_refs
       s)`;;

let flat_state_rel_trans = prove
 (`!reachable s1 s2 s3.
     flat_state_rel reachable s1 s2 /\
     flat_state_rel reachable s2 s3 ==> flat_state_rel reachable s1
       s3`,
  (REWRITE_TAC[flat_state_rel_def] THEN MESON_TAC[globals_rel_trans]));;

(**************************** FLATLANG LEMMAS *****************************)

let pmatch_Match_reachable = prove
 (`(!(s:('c,'ffi)flatSem_state) p v l a (reachable:1 spt).
   pmatch s p v l = Match a /\
      domain (find_v_globals v) SUBSET domain reachable /\
      domain (find_v_globalsL (MAP SND l)) SUBSET domain reachable /\
      domain (find_refs_globals (flatSem_state_refs s)) SUBSET domain
        reachable ==> domain (find_v_globalsL (MAP SND a)) SUBSET domain
        reachable) /\
   (!(s:('c,'ffi)flatSem_state) p vs l a (reachable:1 spt).
      pmatch_list s p vs l = Match a /\
      domain (find_v_globalsL vs) SUBSET domain reachable /\
      domain (find_v_globalsL (MAP SND l)) SUBSET domain reachable /\
      domain (find_refs_globals (flatSem_state_refs s)) SUBSET
        domain reachable ==> domain (find_v_globalsL (MAP SND a))
        SUBSET domain reachable)`,
  CHEAT_TAC);;

let find_v_globals_list_to_v_APPEND = prove
 (`!xs (reachable:1 spt) ys.
      domain (find_v_globalsL xs) SUBSET domain reachable /\
      domain (find_v_globalsL ys) SUBSET domain reachable ==>
        domain (find_v_globals (list_to_v (APPEND xs ys))) SUBSET
        domain reachable`,
  CHEAT_TAC);;

(* [simp] *)
let find_v_globals_Unitv = prove
 (`find_v_globals Unitv = LN`,
  CHEAT_TAC);;

let EVERY_EL_IMP = prove
 (`ALL P xs /\ n < LENGTH xs ==> P (EL n xs)`,
  (REWRITE_TAC[GSYM ALL_EL] THEN MESON_TAC[]));;

(* [local] *)
let not_v_has_Eval_EVERY_EL = prove
 (`ALL ((~) o v_has_Eval) xs /\ i < LENGTH xs ==> ~(v_has_Eval (EL i
  xs))`,
  (REWRITE_TAC[GSYM ALL_EL; o_THM] THEN MESON_TAC[]));;

(* HOL4 flat_elimProofScript.sml:462: the ML values that the
   definitions below antiquote *)

let v_has_Eval_list_to_v = prove
 (`v_has_Eval (list_to_v xs) = EX v_has_Eval xs`,
  CHEAT_TAC);;

let v_has_Eval_v_to_list = prove
 (`!v xs. v_to_list v = SOME xs ==> v_has_Eval v = EX v_has_Eval xs`,
  CHEAT_TAC);;

(* HOL4 flat_elimProofScript.sml:479-481: ML code, not ported *)

(* HOL4 flat_elimProofScript.sml:483: ML code, not ported *)

(* [local] *)
let fvg_map_char_empty = prove
 (`find_v_globals (list_to_v (MAP (\c. Litv (ast_Char c)) ss)) = LN`,
  CHEAT_TAC);;

(* [local] *)
let not_LE_LESS_IMP = prove
 (`(~(x >= y)) ==> ((x:num) < y)`,
  (ARITH_TAC));;

(* [local] *)
let EL_REP_NONE_SOME_trivia = prove
 (`n < LENGTH xs + i ==>
   (EL n (APPEND xs (REPLICATE i NONE)) = SOME y <=>
     n < LENGTH xs /\ EL n xs = SOME y)`,
  CHEAT_TAC);;

(* pair_case_eq[local] *)
let flat_elimProof_pair_case_eq = prove
 (`pair_CASE x f = v <=> (?x1 x2. x = (x1,x2) /\ f x1 x2 = v)`,
  CHEAT_TAC);;

(* pair_lam_lem[local] *)
let flat_elimProof_pair_lam_lem = prove
 (`!f v z. (let (x,y) = z in f x y) = v <=> (?x1 x2. z = (x1,x2) /\ (f
  x1 x2 = v))`,
  CHEAT_TAC);;

(* HOL4 flat_elimProofScript.sml:519: ML code, not ported *)

(* HOL4 flat_elimProofScript.sml:521-524: a theorem that HOL4 states
   as the value of an ML expression: do_app_cases *)


(* [local,simp] *)
let fvg_v_to_flat = prove
 (`domain (find_v_globals (v_to_flat v)) SUBSET domain reachable /\
   ~(v_has_Eval (v_to_flat v))`,
  CHEAT_TAC);;

let do_app_SOME_flat_state_rel = prove
 (`!reachable state removed_state op l new_state result
  new_removed_state.
      flat_state_rel reachable state removed_state /\ ~(op =
        flatLang_Src ast_Opapp) /\
      domain (find_v_globalsL l) SUBSET domain reachable /\
      domain (find_lookups (App tra op [])) SUBSET domain reachable
        /\
      ALL ((~) o v_has_Eval) l ==>
          do_app state op l = SOME (new_state,result) /\ ~(result =
            Rerr (Rabort Rtype_error)) ==> (?new_removed_state.
              flat_state_rel reachable new_state new_removed_state /\
              do_app removed_state op l =
                  SOME (new_removed_state,result) /\
              domain (find_sem_prim_res_globals (list_result result))
                SUBSET
                  domain reachable /\
              ALL ((~) o v_has_Eval) (result_vs (list_result
                result)))`,
  CHEAT_TAC);;


(**************************** MAIN LEMMAS *****************************)

let flat_state_rel_pmatch = prove
 (`(!((new_state:('c,'ffi)flatSem_state)) p a env.
     flat_state_rel reachable new_state new_removed_state ==>
     pmatch new_removed_state p a env =
     pmatch new_state p a env) /\
   (!((new_state:('c,'ffi)flatSem_state)) p a env.
     flat_state_rel reachable new_state new_removed_state ==>
     pmatch_list new_removed_state p a env =
     pmatch_list new_state p a env)`,
  CHEAT_TAC);;

let flat_state_rel_pmatch_rows = prove
 (`flat_state_rel reachable new_state new_removed_state ==>
   pmatch_rows (pes:(flatLang_pat#flatLang_exp) list)
     new_removed_state a =
   pmatch_rows pes new_state a`,
  CHEAT_TAC);;

let pmatch_rows_find_lookups = prove
 (`pmatch_rows pes q a = Match (env',p',e') /\
   domain (find_lookupsL (MAP SND pes)) SUBSET domain reachable ==>
   domain (find_lookups e') SUBSET domain reachable`,
  CHEAT_TAC);;

let pmatch_not_has_Eval = prove
 (`(
   !(s:('c,'ffi)flatSem_state) p v bindings env.
   pmatch s p v bindings = Match env /\ ~(v_has_Eval v) /\
   ALL (ALL ((~) o v_has_Eval) o store_v_vs) (flatSem_state_refs s)
     /\
   ALL ((~) o v_has_Eval o SND) bindings ==>
   ALL ((~) o v_has_Eval o SND) env) /\ (
   !(s:('c,'ffi)flatSem_state) ps vs bindings env.
   pmatch_list s ps vs bindings = Match env /\
   ALL ((~) o v_has_Eval) vs /\
   ALL (ALL ((~) o v_has_Eval) o store_v_vs) (flatSem_state_refs s)
     /\
   ALL ((~) o v_has_Eval o SND) bindings ==>
   ALL ((~) o v_has_Eval o SND) env)`,
  CHEAT_TAC);;

(* has_Eval_def[local] *)
let flat_elimProof_has_Eval_def = prove
 (`(has_Eval (Handle _17 e pes:flatLang_exp) = (has_Eval e \/ EX
  has_Eval (MAP SND pes))) /\
   (has_Eval (Con _18 _19 es) = EX has_Eval es) /\
   (has_Eval (Fun _20 _21 e) = has_Eval e) /\
   (has_Eval (App t op es) = (op = flatLang_Src ast_Eval \/ EX
     has_Eval es)) /\
   (has_Eval (If t e1 e2 e3) = (has_Eval e1 \/ has_Eval e2 \/
     has_Eval e3)) /\
   (has_Eval (Mat t e pes) = (has_Eval e \/ EX has_Eval (MAP SND
     pes))) /\
   (has_Eval (Let _22 opt e1 e2) = (has_Eval e1 \/ has_Eval e2)) /\
   (has_Eval (Letrec _23 funs e) = (has_Eval e \/ EX has_Eval (MAP
     (SND o SND) funs))) /\
   (has_Eval (Raise _24 e) = has_Eval e) /\
   (has_Eval (flatLang_Var_local _25 _26) = F) /\
   (has_Eval (Lit _27 v) = F)`,
  CHEAT_TAC);;

(******** EVALUATE INDUCTION ********)

(* HOL4 flat_elimProofScript.sml:773-776: ML code, not ported *)

let evaluate_keep_flat_state_rel_eq_lemma = prove
 (`(!env ((state:('c,'ffi)flatSem_state)) exprL new_state
       result (reachable:1 spt) removed_state.
       flatSem_evaluate env state exprL = (new_state,result) /\
       domain (find_lookupsL exprL) SUBSET domain reachable /\
       flat_state_rel reachable state removed_state /\
       domain (find_env_globals env) SUBSET domain reachable /\
       ALL (((~)) o v_has_Eval o SND) (flatSem_environment_v env) /\
       ALL (((~)) o has_Eval) exprL /\ ~(result = Rerr (Rabort
         Rtype_error)) ==> (?new_removed_state.
       evaluate env removed_state exprL = (new_removed_state,result)
         /\
       flat_state_rel reachable new_state new_removed_state /\
       domain (find_sem_prim_res_globals result) SUBSET domain
         reachable /\
       ALL (((~)) o v_has_Eval) (result_vs result)))`,
  CHEAT_TAC);;

(******** EVALUATE SPECIALISATION ********)

let evaluate_sing_keep_flat_state_rel_eq = prove
 (`!env ((state:('c,'ffi)flatSem_state)) exprL new_state result expr
     reachable removed_state.
     flatSem_evaluate (flatSem_environment_v_fupd (K []) env) state
       exprL = (new_state,result) /\
     flat_state_rel reachable state removed_state /\
     exprL = [expr] /\
     keep reachable expr /\
     domain (find_lookups expr) SUBSET domain reachable /\
     ~(has_Eval expr) /\ ~(result = Rerr (Rabort Rtype_error)) ==>
       (?new_removed_state.
       evaluate (flatSem_environment_v_fupd (K []) env) removed_state
         exprL = (new_removed_state,result) /\
       flat_state_rel reachable new_state new_removed_state)`,
  CHEAT_TAC);;

(******** EVALUATE_DEC ********)

let evaluate_dec_flat_state_rel = prove
 (`!((state:('c,'ffi)flatSem_state)) dec new_state result
     reachable removed_state.
     evaluate_dec state dec = (new_state,result) /\
     decs_closed reachable [dec] /\
     flat_state_rel reachable state removed_state /\ keep reachable
       dec /\
     ~(has_Eval_dec dec) /\ ~(result = SOME (Rabort Rtype_error)) ==>
       (?new_removed_state.
       evaluate_dec removed_state dec =
           (new_removed_state,result) /\
       flat_state_rel reachable new_state new_removed_state)`,
  CHEAT_TAC);;

let total_pat_IMP = prove
 (`(!(s:('c,'ffi)flatSem_state) p v env res.
      pmatch s p v env = res /\ total_pat p ==> ~(res = No_match)) /\
   (!(s:('c,'ffi)flatSem_state) ps vs env res.
      LENGTH ps = LENGTH vs /\
      pmatch_list s ps vs env = res /\
      total_pat_list ps ==> ~(res = No_match))`,
  CHEAT_TAC);;

let EXISTS_total_pat = prove
 (`EX total_pat (MAP FST pes) ==> ~(pmatch_rows pes new_state v =
  No_match)`,
  CHEAT_TAC);;


(********************** CASE: *NOT* keep reachable h ***********************)

(******** EVALUATE MUTUAL INDUCTION ********)

let evaluate_flat_state_rel_lemma = prove
 (`(!env ((state:('c,'ffi)flatSem_state)) exprL new_state result
       reachable removed_state.
       flatSem_evaluate env state exprL = (new_state,result) /\
       ALL flat_elim_is_pure exprL /\
       ALL (((~)) o v_has_Eval o SND) (flatSem_environment_v env) /\
       ALL (((~)) o has_Eval) exprL /\
       ALL (\e. (\t. t = LN) (inter (find_loc e) reachable)) exprL /\
       flat_state_rel reachable state removed_state /\ ~(result =
         Rerr (Rabort Rtype_error)) ==> (?values. flat_state_rel
         reachable new_state removed_state /\
       result = Rval values /\
       ALL (((~)) o v_has_Eval) values))`,
  CHEAT_TAC);;

(******** EVALUATE SPECIALISATION ********)

let evaluate_sing_notKeep_flat_state_rel = prove
 (`!env state exprL new_state result expr
       reachable removed_state.
       flatSem_evaluate (flatSem_environment_v_fupd (K []) env) state
         exprL = (new_state,result) /\
       exprL = [expr] /\
       ~(has_Eval expr) /\
       ~(keep reachable expr) /\
       flat_state_rel reachable state removed_state /\ ~(result =
         Rerr (Rabort Rtype_error)) ==> flat_state_rel reachable
         new_state removed_state /\
       (?(value:flatSem_v). result = Rval [value])`,
  CHEAT_TAC);;


(******************************* MAIN PROOFS ******************************)

let flat_decs_removal_lemma = prove
 (`!((state:('c,'ffi)flatSem_state)) decs new_state result
      reachable removed_decs removed_state.
      evaluate_decs state decs = (new_state,result) /\ ~(result =
        SOME (Rabort Rtype_error)) /\
      remove_unreachable reachable decs = removed_decs /\
      flat_state_rel reachable state removed_state /\
      ALL ((~) o has_Eval_dec) decs /\
      decs_closed reachable decs ==> (?new_removed_state. state_ffi
      new_removed_state = state_ffi new_state /\
      evaluate_decs removed_state removed_decs =
          (new_removed_state,result))`,
  CHEAT_TAC);;

let flat_removal_thm = prove
 (`!ffi k decs new_state result roots tree
       reachable removed_decs.
       evaluate_decs (flatSem_initial_state ffi k ec) decs =
         (new_state,result) /\ ~(result = SOME (Rabort Rtype_error)) /\
       (roots,tree) = analyse_code decs /\
       reachable = closure_spt roots tree /\
       ~(EX has_Eval_dec decs) /\
       remove_unreachable reachable decs = removed_decs ==> (?s.
         state_ffi
       s = state_ffi new_state /\
       evaluate_decs (flatSem_initial_state ffi k ec) removed_decs
         = (s,result))`,
  CHEAT_TAC);;

let flat_remove_eval_sim = prove
 (`flatProps_eval_sim ffi ds1 (remove_flat_prog ds1) ec ec
                    (\d1 d2. d2 = remove_flat_prog d1) F`,
  CHEAT_TAC);;

(* HOL4 flat_elimProofScript.sml:1676-1678: a theorem that HOL4
   states as the value of an ML expression: flat_remove_semantics *)

(* syntactic results *)

(* [local] *)
let elist_globals_filter = prove
 (`flatProps_elist_globals ds = EMPTY_BAG ==>
    flatProps_elist_globals (FILTER P ds) = EMPTY_BAG`,
  CHEAT_TAC);;

(* [local] *)
let esgc_free_filter = prove
 (`ALL flatProps_esgc_free ds ==>
    ALL flatProps_esgc_free (FILTER P ds)`,
  CHEAT_TAC);;

(* [local] *)
let elist_globals_filter_SUB_BAG = prove
 (`flatProps_elist_globals (FILTER P ds) <=
    flatProps_elist_globals ds`,
  CHEAT_TAC);;

let remove_flat_prog_elist_globals_eq_empty = prove
 (`flatProps_elist_globals ds = EMPTY_BAG ==>
   flatProps_elist_globals (remove_flat_prog ds) = EMPTY_BAG`,
  CHEAT_TAC);;

let remove_flat_prog_esgc_free = prove
 (`ALL flatProps_esgc_free ds ==>
   ALL flatProps_esgc_free (remove_flat_prog ds)`,
  CHEAT_TAC);;

let remove_flat_prog_sub_bag = prove
 (`flatProps_elist_globals (remove_flat_prog ds) <=
   flatProps_elist_globals ds`,
  CHEAT_TAC);;

let remove_flat_prog_distinct_globals = prove
 (`BAG_ALL_DISTINCT (flatProps_elist_globals ds) ==>
   BAG_ALL_DISTINCT (flatProps_elist_globals (remove_flat_prog ds))`,
  CHEAT_TAC);;

(* and the overloads that this file cannot see are back in the
   interface *)
let _ = unhide_overloads ();;
