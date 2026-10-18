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

(* HOL4 flat_patternProofScript.sml:14: ML code, not ported *)

(* simple properties *)

(* decoding the encoded names *)

(* lists and lookups *)

let pure_eval_to_def = cake_define
  `pure_eval_to s env exp v = (evaluate env s [exp] = (s,Rval [v]))`;;

let ALOOKUP_rel_def = cake_define
  `ALOOKUP_rel P R env1 env2 =
   (!x. P x ==> OPTREL R (ALOOKUP env1 x) (ALOOKUP env2 x))`;;

(* HOL4 flat_patternProofScript.sml:382-401: code that the source has
   in a comment *)

(* HOL4 flat_patternProofScript.sml:411-412: ML code, not ported *)

(* a note on 'naming' below. the existing (encoded) names in the program
   (in the original x and exp)
   are < j for starting val j. during the recursion, j increases to i,
     with
   new names i < nm < j appearing in the new env, and in *expressions*
     in
   n_bindings. note *names* in n_bindings/pre_bindings come from the
     original
   program. also new/old names mix in env, thus the many filters. *)

(* HOL4 flat_patternProofScript.sml:651-653: ML code, not ported *)
(* on the right side of the state relation, the pattern compiler's
   config is
   also needed in the compiler state *)
(* HOL4 flat_patternProofScript.sml:656: ML code, not ported *)

(* HOL4 flat_patternProofScript.sml:658: ML code, not ported *)

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

(* HOL4 flat_patternProofScript.sml:688-689: ML code, not ported *)

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

(* HOL4 flat_patternProofScript.sml:722-723: the overload nv_rel,
   which the port expands *)

let match_rel_def = cake_define
  `match_rel N x2 x3 =
        match (x2,x3) with
          (Match env1,Match env2) -> (\N. ALOOKUP_rel (\x.
            dec_name_to_num x < N) flat_patternProof_v_rel) N env1 env2
        | (No_match,No_match) -> T
        | (Match_type_error,Match_type_error) -> T
        | (_1,_2) -> F`;;

let _ = size_thms "flatSem_v";;
(* HOL4 flat_patternProofScript.sml:974-978: the tactic that proves
   the termination *)
let encode_val_def = cake_define_wf
  `MEASURE flatSem_v_size`
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

(* HOL4 flat_patternProofScript.sml:1541: ML code, not ported *)

(* set_globals and esgc properties *)
