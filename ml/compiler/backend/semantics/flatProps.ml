(* ======================================================== *)
(*  flatProps: ported from HOL4's
    compiler/backend/semantics/flatPropsScript.sml  *)
(* ======================================================== *)

(*
  Properties about flatLang and its semantics
*)

needs "compiler/backend/flatLang.ml";;
needs "compiler/backend/semantics/flatSem.ml";;
needs "lib/lprefix_lub.ml";;
needs "semantics/ast.ml";;
needs "semantics/evaluate.ml";;
needs "semantics/proofs/evaluateProps.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;
needs "semantics/semanticPrimitives.ml";;

(* HOL4 flatPropsScript.sml:31-33: the ML values that the definitions
   below antiquote *)

(* Alternate definition for build_rec_env *)

let bind_locals_list_def = cake_define
  `bind_locals_list ts ks = MAP2 (\t x. (flatLang_Var_local t x)) ts
  ks`;;

(* HOL4 flatPropsScript.sml:546-605: code that the source has in a
   comment *)

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

let op_gbag_def = cake_define
  `flatProps_op_gbag x1 =
      match x1 with
        flatLang_GlobalVarInit n -> BAG_INSERT n EMPTY_BAG
      | _1 -> EMPTY_BAG`;;
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
  ((BAG_UNION)
        (flatProps_set_globals e1) (flatProps_set_globals e2))
          (flatProps_set_globals e3)`;
   `flatProps_set_globals (Mat t e pes:flatLang_exp) = (BAG_UNION)
  (flatProps_set_globals e) (flatProps_elist_globals (MAP SND pes))`;
   `flatProps_set_globals (Let t v e1 e2:flatLang_exp) = (BAG_UNION)
  (flatProps_set_globals e1) (flatProps_set_globals e2)`;
   `flatProps_set_globals (Letrec t fs e:flatLang_exp) = (BAG_UNION)
        (flatProps_set_globals e) (flatProps_elist_globals (MAP
          (SND o SND) fs))`;
   `flatProps_set_globals _2 = EMPTY_BAG`;
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
        | _3 -> T`;;
hol4_overload "esgc_free" "flatProps_esgc_free";;

(* generic proof support for most val_rel/state_rel examples *)

let isClosure_def = cake_define
  `isClosure exp = (
     (?vs n x. exp = Closure vs n x) \/
     (?vs fs x. exp = Recclosure vs fs x))`;;

(* HOL4 flatPropsScript.sml:921-923: the ML values that the
   definitions below antiquote *)

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
  [`v_container_xs (Litv _5:flatSem_v) = []`;
   `v_container_xs (Loc _8 _9:flatSem_v) = []`;
   `v_container_xs (Conv _11 vs:flatSem_v) = vs`;
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

(* HOL4 flatPropsScript.sml:1157: ML code, not ported *)

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

(* HOL4 flatPropsScript.sml:1432-1446: the ML values that the
   definitions below antiquote *)

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
        (match pes with [(Pvar _19,_20)] -> T | _21 -> F)`;
   `no_Mat (Letrec t funs e:flatLang_exp) <=> EVERY no_Mat (MAP
  (SND o SND) funs) /\ no_Mat e`];;

let no_Mat_decs_def = cake_define_list
  [`no_Mat_decs [] = T`;
   `no_Mat_decs (e :: xs) = (no_Mat e /\ no_Mat_decs xs)`];;

let mk_flat_install_conf_def = cake_define
  `flatProps_mk_flat_install_conf cc co =
     (mk_install_config cc co:'c install_config)`;;
hol4_overload "mk_flat_install_conf" "flatProps_mk_flat_install_conf";;
