(* ======================================================== *)
(*  flatProps: ported from HOL4's
    compiler/backend/semantics/flatPropsScript.sml  *)
(* ======================================================== *)

(*
  Properties about flatLang and its semantics
*)

needs "compiler/backend/flatLang.ml";;
needs "compiler/backend/pattern_matching/pattern_semantics.ml";;
needs "compiler/backend/semantics/flatSem.ml";;
needs "lib/lprefix_lub.ml";;
needs "semantics/ast.ml";;
needs "semantics/evaluate.ml";;
needs "semantics/namespace.ml";;
needs "semantics/proofs/evaluateProps.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;
needs "semantics/semanticPrimitives.ml";;

(* HOL4 ML code, not ported:
val s =  ``s:('c,'ffi) state``
val st = ``st:('c,'ffi) state``
val st' = ``st':('d,'ffi) state``
*)

(* Alternate definition for build_rec_env *)

let bind_locals_list_def = cake_define
  `bind_locals_list ts ks = MAP2 (\t x. (flatLang_Var_local t x)) ts
  ks`;;

(*
Theorem pmatch_evaluate_vars:
  (!^s p v evs env' ts.
    flatSem$pmatch s p v evs = Match env' ∧
    ALL_DISTINCT (pat_bindings p (MAP FST evs)) ∧
    LENGTH ts = LENGTH (pat_bindings p (MAP FST evs))
    ⇒
    flatSem$evaluate (env with v := env') s (bind_locals_list ts
      (pat_bindings p (MAP FST evs))) = (s,Rval (MAP SND env'))) ∧
   (!^s ps vs evs env' ts.
    flatSem$pmatch_list s ps vs evs = Match env' ∧
    ALL_DISTINCT (pats_bindings ps (MAP FST evs)) ∧
    LENGTH ts = LENGTH (pats_bindings ps (MAP FST evs))
    ⇒
    flatSem$evaluate (env with v := env') s (bind_locals_list ts
      (pats_bindings ps (MAP FST evs))) = (s,Rval (MAP SND env')))
Proof
  ho_match_mp_tac pmatch_ind >>
  srw_tac[][pat_bindings_def, pmatch_def]
  >- (
    match_mp_tac evaluate_vars >> srw_tac[][] >>
    qexists_tac`(x,v)::evs` >> srw_tac[][] )
  >- (
    match_mp_tac evaluate_vars >> srw_tac[][] >>
    first_assum(match_exists_tac o concl) >> simp[] )
  >- (
    match_mp_tac evaluate_vars >> srw_tac[][] >>
    first_assum(match_exists_tac o concl) >> simp[] )
  >- (
    first_x_assum (match_mp_tac o MP_CANON) >>
    every_case_tac >> full_simp_tac(srw_ss())[] )
  >- (
    first_x_assum (match_mp_tac o MP_CANON) >>
    every_case_tac >> full_simp_tac(srw_ss())[] )
  >- (
    match_mp_tac evaluate_vars >> srw_tac[][] >>
    first_assum(match_exists_tac o concl) >> simp[] ) >>
  every_case_tac >> full_simp_tac(srw_ss())[] >>
  `ALL_DISTINCT (pat_bindings p (MAP FST evs))`
          by metis_tac[pat_bindings_accum, ALL_DISTINCT_APPEND] >>
  rfs [] >> fs [] >>
  `pat_bindings p (MAP FST evs) = MAP FST a`
               by (imp_res_tac pmatch_extend >>
                   srw_tac[][] >>
                   metis_tac [pat_bindings_accum]) >>
  fsrw_tac[QUANT_INST_ss[record_default_qp]][] >>
  rev_full_simp_tac(srw_ss())[]
QED

Theorem pmatch_evaluate_vars_lem:
  ∀p v bindings env ^s ts.
    pmatch s p v [] = Match bindings ∧
    ALL_DISTINCT (pat_bindings p []) ∧
    LENGTH ts = LENGTH (pat_bindings p [])
    ⇒
    evaluate (env with v := bindings) s (bind_locals_list ts
      (pat_bindings p [])) = (s,Rval (MAP SND bindings))
Proof
  rw [] >>
  imp_res_tac pmatch_evaluate_vars >>
  fs []
QED
*)

let eval_sim_def = cake_define
  `flatProps_eval_sim ffi ds1 ds2 ec ec2 rel allow_fail =
     (!k res1 s2.
       evaluate_decs (initial_state ffi k ec) ds1 =
         (s2,res1) /\
       (allow_fail \/ ~(res1 = SOME (Rabort Rtype_error))) /\
       rel ds1 ds2 ==>
       (?ck res2 t2.
         evaluate_decs (initial_state ffi (k + ck) ec2) ds2 =
           (t2,res2) /\ ?_ffi
         s2 = ?_ffi t2 /\
         (res1 = NONE ==> res2 = NONE) /\
         (!v. res1 = SOME (Rraise v) ==> (?v1. res2 = SOME (Rraise
           v1))) /\
         (!a. res1 = SOME (Rabort a) ==> res2 = SOME (Rabort a))))`;;
hol4_overload "eval_sim" "flatProps_eval_sim";;

let op_gbag_def = cake_define
  `flatProps_op_gbag x1 =
      match x1 with
        (GlobalVarInit n) -> BAG_INSERT n EMPTY_BAG
      | _1 -> EMPTY_BAG`;;
hol4_overload "op_gbag" "flatProps_op_gbag";;

let _ = size_thms "exp";;
let _ = size_thms "list";;
(* HOL4 termination: \\ rw [flatLangTheory.exp_size_def] \\ fs [GSYM
   o_DEF] >- (irule LESS_EQ_LESS_TRANS \\ qexists_tac ‘list_size
   (pair_size mlstring_size (pair_size mlstring_size exp_size)) fs’
   \\ gvs [] \\ Induct_on ‘fs’ \\ gvs [FORALL_PROD]) \\ irule
   LESS_EQ_LESS_TRANS \\ qexists_tac ‘list_size (pair_size pat_size
   exp_size) pes’ \\ gvs [] \\ Induct_on ‘pes’ \\ gvs [FORALL_PROD] *)
let set_globals_def = cake_define_wf
  `MEASURE (\a. match a with INL e -> exp_size e | INR es -> list_size
  exp_size es)`
  `flatProps_set_globals x1 =
        match x1 with
          (Raise t e) -> flatProps_set_globals e
        | (Handle t e pes) -> BAG_UNION (flatProps_set_globals e)
          (flatProps_elist_globals (MAP SND pes))
        | (Con t id es) -> flatProps_elist_globals es
        | (Fun t v e) -> flatProps_set_globals e
        | (App t op es) -> BAG_UNION (flatProps_elist_globals es)
          (op_gbag op)
        | (If t e1 e2 e3) -> BAG_UNION (BAG_UNION
       (flatProps_set_globals e1) (flatProps_set_globals e2))
         (flatProps_set_globals e3)
        | (Mat t e pes) -> BAG_UNION (flatProps_set_globals e)
          (flatProps_elist_globals (MAP SND pes))
        | (Let t v e1 e2) -> BAG_UNION (flatProps_set_globals e1)
          (flatProps_set_globals e2)
        | (Letrec t fs e) -> BAG_UNION
       (flatProps_set_globals e) (flatProps_elist_globals (MAP (SND o
         SND) fs))
        | _2 -> EMPTY_BAG
        | [] -> EMPTY_BAG
        | (e :: es) -> BAG_UNION (flatProps_set_globals e)
          (flatProps_elist_globals es)`;;
hol4_overload "elist_globals" "flatProps_elist_globals";;
hol4_overload "set_globals" "flatProps_set_globals";;


let _ = size_thms "exp";;
(* HOL4 termination: \\ rw [] \\ gvs
   [list_size_pair_size_MAP_FST_SND] \\ drule MEM_list_size \\
   disch_then $ qspec_then ‘exp_size’ mp_tac \\ gvs [] *)
let esgc_free_def = cake_define_wf
  `MEASURE exp_size`
  `flatProps_esgc_free x1 =
        match x1 with
          (Raise t e) -> flatProps_esgc_free e
        | (Handle t e pes) ->
       flatProps_esgc_free e /\ EVERY flatProps_esgc_free (MAP SND
         pes)
        | (Con t id es) -> EVERY flatProps_esgc_free es
        | (Fun t v e) -> set_globals e = EMPTY_BAG
        | (App t op es) -> EVERY flatProps_esgc_free es
        | (If t e1 e2 e3) ->
       flatProps_esgc_free e1 /\ flatProps_esgc_free e2 /\
         flatProps_esgc_free e3
        | (Mat t e pes) -> flatProps_esgc_free e /\ EVERY
          flatProps_esgc_free (MAP SND pes)
        | (Let t v e1 e2) -> flatProps_esgc_free e1 /\
          flatProps_esgc_free e2
        | (Letrec t fs e) ->
       flatProps_esgc_free e /\ elist_globals (MAP (SND o SND) fs) =
         EMPTY_BAG
        | _3 -> T`;;
hol4_overload "esgc_free" "flatProps_esgc_free";;

(* generic proof support for most val_rel/state_rel examples *)

let isClosure_def = cake_define
  `isClosure exp = (
     (?vs n x. exp = Closure vs n x) \/
     (?vs fs x. exp = Recclosure vs fs x))`;;

(* HOL4 ML code, not ported:
val v_conss = TypeBase.nchotomy_of ``: v``
  |> concl |> dest_forall |> snd |> strip_disj
  |> map (rhs o snd o strip_exists)
*)

let simple_basic_val_rel_def = cake_define
  `(simple_basic_val_rel (Litv l) v = (v = Litv l)) /\
   (simple_basic_val_rel (Loc b i) v = (v = Loc b i)) /\
   (simple_basic_val_rel (Conv stmp vs1) v = (?vs2. v = Conv stmp
     vs2)) /\
   (simple_basic_val_rel (Vectorv vs1) v = (?vs2. v = Vectorv vs2))
     /\
   (simple_basic_val_rel (Closure vs nm exp) v = F) /\
   (simple_basic_val_rel (Recclosure vs exps nm) v = F)`;;

let v_container_xs_def = cake_define_list
  [`v_container_xs (Litv _4:flatSem_v) = []`;
   `v_container_xs (Loc _5 _6:flatSem_v) = []`;
   `v_container_xs (Conv _7 vs:flatSem_v) = vs`;
   `v_container_xs (Vectorv vs:flatSem_v) = vs`;
   `v_container_xs (Closure vs nm exp:flatSem_v) = []`;
   `v_container_xs (Recclosure vs exps nm:flatSem_v) = []`];;

let simple_val_rel_def = cake_define
  `flatProps_simple_val_rel vr = (
     (!v1 v2. (vr v1 v2 ==> isClosure v1 = isClosure v2)) /\ (!v1 v2.
       ~isClosure v1 ==> vr v1 v2 = (
         simple_basic_val_rel v1 v2 /\ LIST_REL vr (v_container_xs
           v1) (v_container_xs v2))))`;;
hol4_overload "simple_val_rel" "flatProps_simple_val_rel";;

let simple_state_rel_def = cake_define
  `flatProps_simple_state_rel vr sr <=>
     (!s t. sr s t ==> LIST_REL (sv_rel vr) (?_refs s) (?_refs t)) /\
     (!s t srefs trefs.
         sr s t /\ LIST_REL (sv_rel vr) srefs trefs ==> sr
           (?_refs_fupd (K srefs) s) (?_refs_fupd (K trefs) t)) /\
     (!s t. sr s t ==> LIST_REL (OPTREL vr) (flatSem_state_globals s)
       (flatSem_state_globals t)) /\
     (!s t sglob tglob.
         sr s t /\ LIST_REL (OPTREL vr) sglob tglob ==> sr
           (flatSem_state_globals_fupd (K sglob) s)
           (flatSem_state_globals_fupd (K tglob) t)) /\
     (!s t. sr s t ==> ?_ffi s = ?_ffi t) /\
     (!s t sffi tffi.
         sr s t /\ sffi = tffi ==> sr (?_ffi_fupd (K sffi) s)
           (?_ffi_fupd (K tffi) t))`;;
hol4_overload "simple_state_rel" "flatProps_simple_state_rel";;

(* HOL4 ML code, not ported:
val sv_rel_cases = semanticPrimitivesPropsTheory.sv_rel_cases;
*)

let evaluate_match_def = cake_define
  `flatProps_evaluate_match env s v pes err_v =
     (match pmatch_rows pes s v with Match_type_error -> (s,Rerr
       (Rabort Rtype_error)) | No_match -> (s,Rerr (Rraise err_v)) |
       Match (env',p',e') ->
         (if ALL_DISTINCT (pat_bindings p') then evaluate
           (?_v_fupd (K (env' ++ ?_v env)) env) s [e'] else (s,Rerr
           (Rabort Rtype_error))))`;;
hol4_overload "evaluate_match" "flatProps_evaluate_match";;

(* HOL4 ML code, not ported:
local
  val tm1 = ``flatLang$Mat``
  val tm2 = ``flatLang$Handle``
in
  val flat_evaluate_def =
    flatSemTheory.evaluate_def
    |> CONJUNCTS
    |> filter (fn th => not (can (find_term (aconv tm1)) (concl th))
      andalso
                        not (can (find_term (aconv tm2)) (concl th)))
    |> (fn thms => thms @ [GEN_ALL evaluate_Handle])
    |> (fn thms => thms @ [GEN_ALL evaluate_Mat])
    |> (fn thms => thms @ [GEN_ALL evaluate_match_NIL])
    |> (fn thms => thms @ [GEN_ALL evaluate_match_CONS])
    |> LIST_CONJ
end
*)

let store_v_vs_def = cake_define
  `flatProps_store_v_vs (Varray vs) = vs /\
   flatProps_store_v_vs (Refv v) = [v] /\
   flatProps_store_v_vs (Thunk m v) = [v] /\
   flatProps_store_v_vs (W8array xs) = []`;;
hol4_overload "store_v_vs" "flatProps_store_v_vs";;

let result_vs_def = cake_define
  `result_vs x1 =
      match x1 with
        (Rval xs) -> xs
      | (Rerr (Rraise x)) -> [x]
      | (Rerr (Rabort y)) -> []`;;

let no_Mat_def = cake_define_list
  [`no_Mat (flatLang_Raise t e) <=> no_Mat e`;
   `no_Mat (Lit t l:flatLang_exp) <=> T`;
   `no_Mat (Var_local t v:flatLang_exp) <=> T`;
   `no_Mat (Con t n es:flatLang_exp) <=> EVERY no_Mat es`;
   `no_Mat (App t op es:flatLang_exp) <=> EVERY no_Mat es`;
   `no_Mat (Fun t v e:flatLang_exp) <=> no_Mat e`;
   `no_Mat (If t x1 x2 x3:flatLang_exp) <=> no_Mat x1 /\ no_Mat x2 /\
  no_Mat x3`;
   `no_Mat (Let t vo e1 e2:flatLang_exp) <=> no_Mat e1 /\ no_Mat e2`;
   `no_Mat (Mat t e pes:flatLang_exp) <=> F`;
   `no_Mat (Handle t e pes:flatLang_exp) <=> no_Mat e /\ EVERY no_Mat
  (MAP SND pes) /\
        (match pes with [(Pvar _8,_9)] -> T | _10 -> F)`;
   `no_Mat (Letrec t funs e:flatLang_exp) <=> EVERY no_Mat (MAP (SND
  o SND) funs) /\ no_Mat e`];;

let no_Mat_decs_def = cake_define
  `no_Mat_decs [] = T /\
   no_Mat_decs (e :: xs) = (no_Mat e /\ no_Mat_decs xs)`;;

let mk_flat_install_conf_def = cake_define
  `mk_flat_install_conf cc co =
     (mk_install_config cc co:'c install_config)`;;
