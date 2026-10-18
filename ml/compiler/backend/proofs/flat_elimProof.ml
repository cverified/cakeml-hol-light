(* ======================================================== *)
(*  flat_elimProof: ported from HOL4's
    compiler/backend/proofs/flat_elimProofScript.sml  *)
(* ======================================================== *)

(*
  Correctness proof for flatLang dead code elimination
*)

needs "compiler/backend/flatLang.ml";;
needs "compiler/backend/flat_elim.ml";;
needs "compiler/backend/semantics/flatProps.ml";;
needs "compiler/backend/semantics/flatSem.ml";;
needs "lib/spt_closure.ml";;
needs "lib/sptree.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;
needs "semantics/semanticPrimitives.ml";;

(************************** LEMMAS ***************************)

(* HOL4 flat_elimProofScript.sml:15-56: code that the source has in a
   comment *)


(************************** DEFINITIONS ***************************)

let _ = size_thms "flatSem_v";;
(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 flat_elimProofScript.sml:118-126: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let find_v_globals_def = cake_define_list_try_tac (fun () ->
  `MEASURE (\e. match e with INL x -> flatSem_v_size x | INR y ->
     list_size flatSem_v_size y)`)
  CHEAT_TAC
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
   `find_v_globalsL (h :: t) = sptree_union (find_v_globals h)
  (find_v_globalsL t)`];;

(* HOL4 flat_elimProofScript.sml:128: ML code, not ported *)

let find_refs_globals_def = cake_define
  `find_refs_globals x1 =
        match x1 with
          (semanticPrimitives_Refv a :: t) ->
           sptree_union (find_v_globals a) (find_refs_globals t)
        | (semanticPrimitives_Varray l :: t) ->
           sptree_union (find_v_globalsL l) (find_refs_globals t)
        | (semanticPrimitives_Thunk _8 a :: t) ->
           sptree_union (find_v_globals a) (find_refs_globals t)
        | (_9 :: t) -> find_refs_globals t
        | [] -> LN`;;

(* HOL4 flat_elimProofScript.sml:225: ML code, not ported *)

let find_env_globals_def = cake_define
  `find_env_globals env = find_v_globalsL (MAP SND
  (flatSem_environment_v env))`;;

let find_result_globals_def = cake_define
  `find_result_globals x1 =
        match x1 with
          SOME (Rraise v) -> find_v_globals v
        | _10 -> LN`;;

(* HOL4 flat_elimProofScript.sml:294: ML code, not ported *)

let find_sem_prim_res_globals_def = cake_define_list
  [`find_sem_prim_res_globals (Rerr e:(flatSem_v
  list,flatSem_v)semanticPrimitives_result) =
            find_result_globals (SOME e)`;
   `find_sem_prim_res_globals (Rval e) = find_v_globalsL e`];;

(* HOL4 flat_elimProofScript.sml:303-306: ML code, not ported *)

let _ = size_thms "flatSem_v";;
(* HOL4 flat_elimProofScript.sml:317-324: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let v_has_Eval_def1 = cake_define_try_tac (fun () ->
  `MEASURE flatSem_v_size`)
  CHEAT_TAC
  `v_has_Eval x1 =
        match x1 with
          (Closure env _12 e:flatSem_v) -> (has_Eval e \/
       EXISTS v_has_Eval (MAP SND (flatSem_environment_v env)))
        | (Conv _13 vl) -> EXISTS v_has_Eval vl
        | (Recclosure env nm_es _14) ->
       (EXISTS v_has_Eval (MAP SND (flatSem_environment_v env)) \/
         EXISTS has_Eval (MAP (SND o SND) nm_es))
        | (Vectorv vl) -> EXISTS v_has_Eval vl
        | _15 -> F`;;

(* s_g = state globals, t_g = removed state globals *)
let globals_rel_def = cake_define
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
         EL n t_g = SOME x ==> ~v_has_Eval x /\ domain
           (find_v_globals x) SUBSET domain reachable)`;;

let decs_closed_def = cake_define
  `decs_closed (reachable:1 spt) decs <=> (!r t.
   analyse_code decs = (r,t) ==> domain r SUBSET domain reachable /\
     (!n m.
     n IN domain reachable /\ is_reachable t n m ==> m IN domain
       reachable))`;;

(* s = state, t = removed state *)
let flat_state_rel_def = cake_define
  `flat_state_rel reachable (s:('c,'ffi)flatSem_state) t <=> state_clock
     s = state_clock t /\ state_refs s = state_refs t /\ state_ffi
     s = state_ffi t /\ globals_rel reachable (flatSem_state_globals
       s) (flatSem_state_globals t) /\
     domain (find_refs_globals (state_refs s)) SUBSET domain
       reachable /\
     EVERY (EVERY ((~) o v_has_Eval) o store_v_vs) (state_refs s)`;;

(**************************** FLATLANG LEMMAS
   *****************************)

(* HOL4 flat_elimProofScript.sml:462: ML code, not ported *)

(* HOL4 flat_elimProofScript.sml:479-481: ML code, not ported *)

(* HOL4 flat_elimProofScript.sml:483: ML code, not ported *)

(* HOL4 flat_elimProofScript.sml:519: ML code, not ported *)


(**************************** MAIN LEMMAS *****************************)

(******** EVALUATE INDUCTION ********)

(* HOL4 flat_elimProofScript.sml:773-776: ML code, not ported *)

(******** EVALUATE SPECIALISATION ********)

(******** EVALUATE_DEC ********)


(********************** CASE: *NOT* keep reachable h
   ***********************)

(******** EVALUATE MUTUAL INDUCTION ********)

(******** EVALUATE SPECIALISATION ********)


(******************************* MAIN PROOFS
   ******************************)

(* syntactic results *)
