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

(*
Theorem wf_find_loc_wf_find_locL:
     (∀ e locs . find_loc  e = locs ⇒ wf locs) ∧
    (∀ l locs . find_locL l = locs ⇒ wf locs)
Proof
    ho_match_mp_tac find_loc_ind >> rw[find_loc_def, wf_union] >>
      rw[wf_def] >>
    Cases_on `dest_GlobalVarInit op` >> fs[wf_insert]
QED

Theorem wf_find_locL:
     ∀ l . wf(find_locL l)
Proof
    metis_tac[wf_find_loc_wf_find_locL]
QED

Theorem wf_find_loc:
     ∀ e . wf(find_loc e)
Proof
    metis_tac[wf_find_loc_wf_find_locL]
QED

Theorem wf_find_lookups_wf_find_lookupsL:
     (∀ e lookups . find_lookups e = lookups ⇒ wf lookups) ∧
    (∀ l lookups . find_lookupsL l = lookups ⇒ wf lookups)
Proof
    ho_match_mp_tac find_lookups_ind >>
    rw[find_lookups_def, wf_union] >> rw[wf_def] >>
    Cases_on `dest_GlobalVarLookup op` >> fs[wf_insert]
QED

Theorem wf_find_lookupsL:
     ∀ l . wf(find_lookupsL l)
Proof
    metis_tac[wf_find_lookups_wf_find_lookupsL]
QED

Theorem wf_find_lookups:
     ∀ e . wf(find_lookups e)
Proof
    metis_tac[wf_find_lookups_wf_find_lookupsL]
QED
*)


(************************** DEFINITIONS ***************************)

let find_v_globals_def = cake_define_list
  [`find_v_globals (Conv _2 vl:flatSem_v) = ((find_v_globalsL vl):1
  spt)`;
   `find_v_globals (Closure env _4 e:flatSem_v) =
            sptree_union (find_v_globalsL (MAP SND
              (semanticPrimitives_sem_env_v env))) (find_lookups e)`;
   `find_v_globals (Recclosure env vves _6:flatSem_v) =
            sptree_union (find_v_globalsL (MAP SND
              (semanticPrimitives_sem_env_v env)))
                (find_lookupsL (MAP (SND o SND) vves))`;
   `find_v_globals (Vectorv vl:flatSem_v) = find_v_globalsL vl`;
   `find_v_globals _7 = LN`;
   `find_v_globalsL [] = LN`;
   `find_v_globalsL (h :: t) = sptree_union (find_v_globals h)
  (find_v_globalsL t)`];;

(* HOL4 ML code, not ported:
val find_v_globals_ind = theorem "find_v_globals_ind";
*)

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

(* HOL4 ML code, not ported:
val find_refs_globals_ind = theorem "find_refs_globals_ind";
*)

let find_env_globals_def = cake_define
  `find_env_globals env = find_v_globalsL (MAP SND
  (semanticPrimitives_sem_env_v env))`;;

let find_result_globals_def = cake_define
  `find_result_globals x1 =
        match x1 with
          SOME (Rraise v) -> find_v_globals v
        | _10 -> LN`;;

(* HOL4 ML code, not ported:
val find_result_globals_ind = theorem "find_result_globals_ind";
*)

let find_sem_prim_res_globals_def = cake_define_list
  [`find_sem_prim_res_globals (Rerr e:(flatSem_v
  list,flatSem_v)semanticPrimitives_result) =
            find_result_globals (SOME e)`;
   `find_sem_prim_res_globals (Rval e) = find_v_globalsL e`];;

(* HOL4 ML code, not ported:
val s =  ``s:('c,'ffi) state``
val t = mk_var ("t", type_of s)
val new_state = mk_var ("new_state", type_of s);
val state = mk_var ("state", type_of s);
*)

let _ = size_thms "flatSem_v";;
(* HOL4 termination: \\ gvs [list_size_pair_size_MAP_FST_SND] \\ rw
   [] \\ Cases_on ‘env’ \\ gvs [environment_size_def] \\ imp_res_tac
   MEM_list_size \\ pop_assum $ qspec_then ‘v_size’ mp_tac \\ gvs
   [list_size_pair_size_MAP_FST_SND] *)
let v_has_Eval_def1 = cake_define_wf
  `MEASURE flatSem_v_size`
  `v_has_Eval x1 =
        match x1 with
          (Closure env _12 e:semanticPrimitives_v) -> (has_Eval e \/
       EXISTS v_has_Eval (MAP SND (semanticPrimitives_sem_env_v
         env)))
        | (Conv _13 vl) -> EXISTS v_has_Eval vl
        | (Recclosure env nm_es _14) ->
       (EXISTS v_has_Eval (MAP SND (semanticPrimitives_sem_env_v
         env)) \/
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

(* HOL4 ML code, not ported:
val v_has_Eval_Unitv = EVAL ``v_has_Eval Unitv``;
*)

(* HOL4 ML code, not ported:
fun qif_pat_tac qpat (tac : tactic) goal = if can (rename [qpat]) goal
  then tac goal
  else ALL_TAC goal
*)

(* HOL4 ML code, not ported:
fun conseq xs = ConseqConv.CONSEQ_REWRITE_TAC (xs, [], [])
*)

(* HOL4 ML code, not ported:
val eqs = flatSemTheory.case_eq_thms;
*)


(**************************** MAIN LEMMAS *****************************)

(******** EVALUATE INDUCTION ********)

(* HOL4 ML code, not ported:
val evaluate_exp_ind = evaluate_ind
  |> Q.SPECL [`P`, `\_ _. T`, `\_ _. T`]
  |> UNDISCH |> CONJUNCT1 |> DISCH_ALL
  |> Q.GEN `P`
*)

(******** EVALUATE SPECIALISATION ********)

(******** EVALUATE_DEC ********)


(********************** CASE: *NOT* keep reachable h
   ***********************)

(******** EVALUATE MUTUAL INDUCTION ********)

(******** EVALUATE SPECIALISATION ********)


(******************************* MAIN PROOFS
   ******************************)

(* syntactic results *)
