(* ======================================================== *)
(*  flat_patternProof: ported from HOL4's
    compiler/backend/proofs/flat_patternProofScript.sml  *)
(* ======================================================== *)

(*
  Correctness proof for flat_pattern
*)

needs "basis/pure/mlstring.ml";;
needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/flatLang.ml";;
needs "compiler/backend/flat_pattern.ml";;
needs "compiler/backend/pattern_matching/pattern_semantics.ml";;
needs "compiler/backend/semantics/backendProps.ml";;
needs "compiler/backend/semantics/flatProps.ml";;
needs "compiler/backend/semantics/flatSem.ml";;
needs "misc/misc.ml";;
needs "semantics/evaluate.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;
needs "semantics/semanticPrimitives.ml";;
(* HOL4 ancestors outside the port: bag *)

(* HOL4 ML code, not ported:
val build_rec_env_merge = flatPropsTheory.build_rec_env_merge;
*)

(* simple properties *)

(* decoding the encoded names *)

(* lists and lookups *)

let pure_eval_to_def = cake_define
  `pure_eval_to s env exp v = (evaluate env s [exp] = (s,Rval [v]))`;;

let ALOOKUP_rel_def = cake_define
  `ALOOKUP_rel P R env1 env2 =
   (!x. P x ==> OPTREL R (ALOOKUP env1 x) (ALOOKUP env2 x))`;;

(*
Theorem pat_bindings_evaluate_FOLDR_lemma:
  !new_names.
  (!x. MEM x xs ==> IS_SOME (f x)) /\
  (!x. IMAGE (THE o f) (set xs) ⊆ new_names) /\
  (!x. MEM x xs ==> (?rv. !env2.
    ALOOKUP_rel (\x. x ∉ new_names) (=) env2.v env.v ==>
    evaluate env2 s [g x] = (s, Rval [rv])))
  ==>
  evaluate env s
    [FOLDR (λx exp. flatLang$Let t (f x) (g x) exp) exp xs] =
  evaluate (env with v := MAP (λx. (THE (f x),
        case evaluate env s [g x] of (_, Rval rv) => HD rv)) (REVERSE
          xs)
             ++ env.v) s [exp]
Proof
  rw []
  \\ DEP_REWRITE_TAC [pat_bindings_evaluate_FOLDR_lemma1]
  \\ simp [ALOOKUP_rel_refl]
QED
*)

(* HOL4 ML code, not ported:
val EVERY_EL_IMP = ASSUME ``EVERY P xs`` |> REWRITE_RULE [EVERY_EL]
  |> DISCH_ALL
*)

(* a note on 'naming' below. the existing (encoded) names in the program
   (in the original x and exp)
   are < j for starting val j. during the recursion, j increases to i,
     with
   new names i < nm < j appearing in the new env, and in *expressions*
     in
   n_bindings. note *names* in n_bindings/pre_bindings come from the
     original
   program. also new/old names mix in env, thus the many filters. *)

(* HOL4 ML code, not ported:
val s = ``s:('c, 'ffi) flatSem$state``;
val s1 = mk_var ("s1", type_of s);
val s2 = mk_var ("s2", type_of s);
*)
(* on the right side of the state relation, the pattern compiler's
   config is
   also needed in the compiler state *)
(* HOL4 ML code, not ported:
val t = ``t:('c, 'ffi) flatSem$state``;
*)

(* HOL4 ML code, not ported:
val _ = IndDefLib.add_mono_thm ALOOKUP_rel_mono_rel;
*)

let v_rel = cake_inductive
  `(!v v'. simple_basic_val_rel v v' /\
     LIST_REL flat_patternProof_v_rel (v_container_xs v)
       (v_container_xs v') ==>
     flat_patternProof_v_rel v v') /\
   (!N env1 n x env2 cfg.
      flat_patternProof_env_rel N env1 env2 /\
      FST (flat_pattern_compile_exp cfg x) < N ==>
      flat_patternProof_v_rel (flatSem_Closure env1 n x)
        (flatSem_Closure env2 n (SND (SND (flat_pattern_compile_exp
          cfg x))))) /\
   (!N env1 fs x env2 cfg.
      flat_patternProof_env_rel N env1 env2 /\
      EVERY (\(n,m,e). FST (flat_pattern_compile_exp cfg e) < N) fs
        ==>
      flat_patternProof_v_rel (flatSem_Recclosure env1 fs x)
        (flatSem_Recclosure env2
          (MAP (\(n,m,e). (n,m,SND (SND (flat_pattern_compile_exp cfg
            e)))) fs) x)) /\
   (!N env1 env2.
      ALOOKUP_rel (\x. dec_name_to_num x < N) flat_patternProof_v_rel
        (flatSem_environment_v env1) (flatSem_environment_v env2) ==>
      flat_patternProof_env_rel N env1 env2)`;;
hol4_overload "env_rel" "flat_patternProof_env_rel";;
hol4_overload "v_rel" "flat_patternProof_v_rel";;

(* HOL4 ML code, not ported:
val env_rel_def = ``env_rel N env1 env2``
    |> SIMP_CONV bool_ss [v_rel_cases]
*)

let install_conf_rel_def = cake_define
  `install_conf_rel pat_cfg ic1 ic2 <=>
     (install_config_compile_oracle ic2 =
         pure_co (MAP (compile_dec pat_cfg)) o
           install_config_compile_oracle ic1) /\
     (install_config_compile ic1 = pure_cc (MAP (compile_dec
       pat_cfg)) (install_config_compile ic2))`;;

let state_rel_def = cake_define
  `flat_patternProof_state_rel cfg (s:('c,'ffi)flatSem_state)
  (t:('c,'ffi)flatSem_state) <=> state_clock
     t = state_clock s /\
     LIST_REL (semanticPrimitivesProps_sv_rel
       flat_patternProof_v_rel) (state_refs s) (state_refs t) /\
       state_ffi
     t = state_ffi s /\
     LIST_REL (OPTREL flat_patternProof_v_rel) (flatSem_state_globals
       s) (flatSem_state_globals t) /\
     install_conf_rel cfg (flatSem_state_eval_config s)
       (flatSem_state_eval_config t)`;;
hol4_overload "state_rel" "flat_patternProof_state_rel";;

(* HOL4 overload (expanded in the port):
     nv_rel = \N. ALOOKUP_rel (\x. dec_name_to_num x < N) v_rel *)

let match_rel_def = cake_define
  `match_rel N x2 x3 =
        match (x2,x3) with
          (Match env1,Match env2) -> (\N. ALOOKUP_rel (\x.
            dec_name_to_num x < N) flat_patternProof_v_rel) N env1 env2
        | (No_match,No_match) -> T
        | (Match_type_error,Match_type_error) -> T
        | (_1,_2) -> F`;;

let _ = size_thms "flatSem_v";;
(* HOL4 termination: \\ rw [] \\ fs [MEM_SPLIT, SUM_APPEND,
   v_size_aux] *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let encode_val_def = cake_define_tac (
  `MEASURE flatSem_v_size`,
  CHEAT_TAC)
  `encode_val others =
      match others with
        (Litv l:flatSem_v) -> Litv l
      | (Conv stmp xs) -> pattern_semantics_Term
     (match stmp with NONE -> NONE | SOME (i,_3) -> SOME i)
     (MAP encode_val xs)
      | (Loc _4 n) -> pattern_semantics_RefPtr n
      | others -> pattern_semantics_Other`;;

let encode_refs_def = cake_define
  `encode_refs s = FUN_FMAP (\i. encode_val (match EL i (state_refs s)
  with semanticPrimitives_Refv v -> v))
     (count (LENGTH (state_refs s)) INTER {i | ?v. EL i
       (state_refs s) = semanticPrimitives_Refv v})`;;

(* HOL4 ML code, not ported:
val evaluate_ind2 = induct_tweakLib.list_single_induct evaluate_ind;
*)

(* set_globals and esgc properties *)
