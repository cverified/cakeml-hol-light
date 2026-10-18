(* ======================================================== *)
(*  flat_patternProof: ported from HOL4's
    compiler/backend/proofs/flat_patternProofScript.sml
    A proof theory about flat_pattern.ml, with 8 definitions and 123
    theorems.  Needed by source_to_flatProof.ml.  *)
(* ======================================================== *)

(*
  Correctness proof for flat_pattern
*)

needs "basis/pure/mlstring.ml";;
needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/flatLang.ml";;
needs "compiler/backend/flat_pattern.ml";;
needs "compiler/backend/pattern_matching/pattern_common.ml";;
needs "compiler/backend/pattern_matching/pattern_semantics.ml";;
needs "compiler/backend/semantics/backendProps.ml";;
needs "compiler/backend/semantics/flatProps.ml";;
needs "compiler/backend/semantics/flatSem.ml";;
needs "lib/indexedLists.ml";;
needs "lib/sptree.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "semantics/evaluate.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;
needs "semantics/semanticPrimitives.ml";;
(* HOL4 ancestors outside the port: bag *)

(* HOL4 flat_patternProofScript.sml:14: ML code, not ported *)

(* simple properties *)
let op_sets_globals_gbag = cake_theorem "op_sets_globals_gbag"
  (fun () ->
    `op_sets_globals op = (~(flatProps_op_gbag op = EMPTY_BAG))`)
  CHEAT_TAC;;

let compile_exp_set_globals_FST_SND =
  cake_theorem "compile_exp_set_globals_FST_SND"
  (fun () ->
    `(!cfg x. FST (SND (flat_pattern_compile_exp cfg x)) =
       (~(flatProps_set_globals x = EMPTY_BAG))) /\
      (!cfg xs. FST (SND (flat_pattern_compile_exps cfg xs)) =
       (~(flatProps_elist_globals xs = EMPTY_BAG))) /\
     (!cfg ps. FST (SND (compile_match cfg ps)) =
       (~(flatProps_elist_globals (MAP SND ps) = EMPTY_BAG)))`)
  CHEAT_TAC;;

let compile_exp_set_globals_tup =
  cake_theorem "compile_exp_set_globals_tup"
  (fun () ->
    `(!cfg x i sg y. flat_pattern_compile_exp cfg x = (i,sg,y) ==>
       sg = (~(flatProps_set_globals x = EMPTY_BAG))) /\
      (!cfg xs i sg ys. flat_pattern_compile_exps cfg xs =
        (i,sg,ys) ==>
       sg = (~(flatProps_elist_globals xs = EMPTY_BAG))) /\
     (!cfg ps i sg ps2. compile_match cfg ps = (i,sg,ps2) ==>
       sg = (~(flatProps_elist_globals (MAP SND ps) =
         EMPTY_BAG)))`)
  CHEAT_TAC;;

(* decoding the encoded names *)

let sum_string_ords_eq = cake_theorem "sum_string_ords_eq"
  (fun () ->
    `sum_string_ords i s = SUM (MAP (\c. ORD c - 35) (DROP i (explode
  s)))`)
  CHEAT_TAC;;

let dec_enc_aux = cake_theorem "dec_enc_aux"
  (fun () ->
    `!xs. dec_name_to_num (implode (enc_num_to_name_aux i xs)) =
     i + SUM (MAP (\c. ORD c - 35) xs)`)
  CHEAT_TAC;;

let dec_enc = cake_theorem "dec_enc"
  (fun () ->
    `dec_name_to_num (enc_num_to_name i) = i`)
  CHEAT_TAC;;

let enc_num_to_name_inj = cake_theorem "enc_num_to_name_inj"
  (fun () ->
    `(enc_num_to_name i = enc_num_to_name j) = (i = j)`)
  CHEAT_TAC;;

(* lists and lookups *)

let LIST_REL_ALOOKUP_OPTREL = cake_theorem "LIST_REL_ALOOKUP_OPTREL"
  (fun () ->
    `!xs ys.
     LIST_REL R xs ys /\
     (!x y. R x y /\ MEM x xs /\ MEM y ys /\ (v = FST x \/ v = FST
       y) ==>
       FST x = FST y /\ R2 (SND x) (SND y)) ==> OPTREL R2
         (ALOOKUP xs v) (ALOOKUP ys v)`)
  CHEAT_TAC;;

let LIST_REL_ALOOKUP = cake_theorem "LIST_REL_ALOOKUP"
  (fun () ->
    `!xs ys.
     LIST_REL R xs ys /\
     (!x y. R x y /\ MEM x xs /\ MEM y ys /\ (v = FST x \/ v =
       FST y) ==> x = y) ==> ALOOKUP xs v = ALOOKUP ys v`)
  CHEAT_TAC;;

let LIST_REL_FILTER_MONO = cake_theorem "LIST_REL_FILTER_MONO"
  (fun () ->
    `!xs ys.
     LIST_REL R (FILTER P1 xs) (FILTER P2 ys) /\
     (!x. MEM x xs /\ P3 x ==> P1 x) /\
     (!y. MEM y ys /\ P4 y ==> P2 y) /\
     (!x y. MEM x xs /\ MEM y ys /\ R x y ==> P3 x = P4 y) ==>
       LIST_REL R (FILTER P3 xs) (FILTER P4 ys)`)
  CHEAT_TAC;;

let COND_false = cake_theorem "COND_false"
  (fun () ->
    `~P ==> ((if P then x else y) = y)`)
  CHEAT_TAC;;

let COND_true = cake_theorem "COND_true"
  (fun () ->
    `P ==> ((if P then x else y) = x)`)
  CHEAT_TAC;;

(* HOL4 flat_patternProofScript.sml:165-166: a theorem that HOL4
   states as the value of an ML expression: FILTER_EQ_MONO *)

(* HOL4 flat_patternProofScript.sml:168-171: a theorem that HOL4
   states as the value of an ML expression: FILTER_EQ_MONO_TRANS *)

let FILTER_EQ_ALOOKUP_EQ = cake_theorem "FILTER_EQ_ALOOKUP_EQ"
  (fun () ->
    `!xs ys. FILTER P xs = ys /\ (!z. P (x,z)) ==>
     ALOOKUP xs x = ALOOKUP ys x`)
  CHEAT_TAC;;

(* HOL4 flat_patternProofScript.sml:183-184: a theorem that HOL4
   states as the value of an ML expression: ALOOKUP_FILTER_EQ *)

let MEM_enumerate_EL = cake_theorem "MEM_enumerate_EL"
  (fun () ->
    `!xs i x. MEM x (enumerate i xs) = (?j. j < LENGTH xs /\ x = (i +
  j,EL j xs))`)
  CHEAT_TAC;;

let ALL_DISTINCT_enumerate = cake_theorem "ALL_DISTINCT_enumerate"
  (fun () ->
    `!xs i. ALL_DISTINCT (enumerate i xs)`)
  CHEAT_TAC;;

let pure_eval_to_def = cake_define
  `pure_eval_to s env exp v = (evaluate env s [exp] = (s,Rval [v]))`;;

let pmatch_list_Match_IMP_LENGTH =
  cake_theorem "pmatch_list_Match_IMP_LENGTH"
  (fun () ->
    `!xs ys env env' s. pmatch_list s xs ys env = Match env' ==>
     LENGTH xs = LENGTH ys`)
  CHEAT_TAC;;

let APPEND_LENGTH_EQ = cake_theorem "APPEND_LENGTH_EQ"
  (fun () ->
    `!xs xs'. LENGTH xs = LENGTH xs' ==>
     (xs ++ ys = xs' ++ ys' <=> xs = xs' /\ ys = ys')`)
  CHEAT_TAC;;

let pmatch_list_append_Match_exists =
  cake_theorem "pmatch_list_append_Match_exists"
  (fun () ->
    `(pmatch_list s (xs ++ ys) vs pre_bindings = Match bindings) =
     (?vs1 vs2 bindings1. vs = vs1 ++ vs2 /\
     pmatch_list s xs vs1 pre_bindings = Match bindings1 /\
     pmatch_list s ys vs2 bindings1 = Match bindings)`)
  CHEAT_TAC;;

let ALOOKUP_rel_def = cake_define
  `ALOOKUP_rel P R env1 env2 =
   (!x. P x ==> OPTREL R (ALOOKUP env1 x) (ALOOKUP env2 x))`;;

let ALOOKUP_rel_empty = cake_theorem "ALOOKUP_rel_empty"
  (fun () ->
    `ALOOKUP_rel P R [] []`)
  CHEAT_TAC;;

let ALOOKUP_rel_cons_false = cake_theorem "ALOOKUP_rel_cons_false"
  (fun () ->
    `(~(P x) ==> ALOOKUP_rel P R ((x,y) :: env1) env2 = ALOOKUP_rel P R
  env1 env2) /\
     (~(P x) ==> ALOOKUP_rel P R env1 ((x,y) :: env2) =
       ALOOKUP_rel P R env1 env2)`)
  CHEAT_TAC;;

let ALOOKUP_rel_APPEND_L_false =
  cake_theorem "ALOOKUP_rel_APPEND_L_false"
  (fun () ->
    `EVERY ((~) o P o FST) xs ==>
     ALOOKUP_rel P R (xs ++ ys) zs =
     ALOOKUP_rel P R ys zs`)
  CHEAT_TAC;;

let ALOOKUP_rel_refl = cake_theorem "ALOOKUP_rel_refl"
  (fun () ->
    `(!x y. P x /\ MEM (x,y) xs ==> R y y) ==> ALOOKUP_rel P R xs xs`)
  CHEAT_TAC;;

let ALOOKUP_rel_cons = cake_theorem "ALOOKUP_rel_cons"
  (fun () ->
    `(P x ==> R y z) /\ ALOOKUP_rel P R ys zs ==>
     ALOOKUP_rel P R ((x,y) :: ys) ((x,z) :: zs)`)
  CHEAT_TAC;;

let ALOOKUP_rel_mono = cake_theorem "ALOOKUP_rel_mono"
  (fun () ->
    `ALOOKUP_rel P R xs ys /\
     (!x y z. P' x ==> P x) /\
     (!x y z. P' x /\ R y z ==> R' y z) ==>
     ALOOKUP_rel P' R' xs ys`)
  CHEAT_TAC;;

let ALOOKUP_rel_mono_rel = cake_theorem "ALOOKUP_rel_mono_rel"
  (fun () ->
    `(!y z. R y z ==> R' y z) ==>
     ALOOKUP_rel P R xs ys ==>
     ALOOKUP_rel P R' xs ys`)
  CHEAT_TAC;;

let ALOOKUP_rel_append_suff = cake_theorem "ALOOKUP_rel_append_suff"
  (fun () ->
    `ALOOKUP_rel P R xs1 xs3 /\ ALOOKUP_rel P R xs2 xs4 ==>
     ALOOKUP_rel P R (xs1 ++ xs2) (xs3 ++ xs4)`)
  CHEAT_TAC;;

let ALOOKUP_rel_EQ_ALOOKUP = cake_theorem "ALOOKUP_rel_EQ_ALOOKUP"
  (fun () ->
    `ALOOKUP_rel P (=) xs ys /\ P x ==>
     ALOOKUP xs x = ALOOKUP ys x`)
  CHEAT_TAC;;

let ALOOKUP_rel_eq_fst = cake_theorem "ALOOKUP_rel_eq_fst"
  (fun () ->
    `!xs ys.
     LIST_REL (\x y. FST x = FST y /\ (P (FST x) ==> R (SND x) (SND
       y))) xs ys ==>
     ALOOKUP_rel P R xs ys`)
  CHEAT_TAC;;

let env_set_v_noop = cake_theorem "env_set_v_noop"
  (fun () ->
    `sem_env_v_fupd (K (flatSem_environment_v env))
       an_env = env`)
  CHEAT_TAC;;

let pat_bindings_evaluate_FOLDR_lemma =
  cake_theorem "pat_bindings_evaluate_FOLDR_lemma"
  (fun () ->
    `!h xs.
     (!x. MEM x xs ==> IS_SOME (f x)) /\
     (!x. IMAGE (THE o f) (set_of_list xs) SUBSET new_names) /\
     (!x. MEM x xs ==> (!env2.
       ALOOKUP_rel (\x. ~(x IN new_names)) (=)
         (flatSem_environment_v env2) (flatSem_environment_v env) ==>
       evaluate env2 s [g x] = (s,Rval [h x]))) ==>
     (!env2.
     ALOOKUP_rel (\x. ~(x IN new_names)) (=) (flatSem_environment_v
       env2) (flatSem_environment_v env) ==>
     evaluate env2 s
       [ITLIST (\x exp. flatLang_Let t (f x) (g x) exp) xs exp] =
     evaluate (flatSem_environment_v_fupd (K (MAP (\x. (THE (f x),h
       x)) (REVERSE xs) ++ flatSem_environment_v env2)) env2)
           s [exp])`)
  CHEAT_TAC;;

(* HOL4 flat_patternProofScript.sml:382-401: code that the source has
   in a comment *)

let EVERY_MAPi_simple = cake_theorem "EVERY_MAPi_simple"
  (fun () ->
    `(!i j x. P (f i x) = P (f j x)) ==>
     EVERY P (MAPi f xs) = EVERY P (MAP (f 0) xs)`)
  CHEAT_TAC;;

(* HOL4 flat_patternProofScript.sml:411-412: the ML values that the
   definitions below antiquote *)

(* a note on 'naming' below. the existing (encoded) names in the program
   (in the original x and exp)
   are < j for starting val j. during the recursion, j increases to i, with
   new names i < nm < j appearing in the new env, and in *expressions* in
   n_bindings. note *names* in n_bindings/pre_bindings come from the original
   program. also new/old names mix in env, thus the many filters. *)

let compile_pat_bindings_simulation =
  cake_theorem "compile_pat_bindings_simulation"
  (fun () ->
    `!t i n_bindings exp exp2 spt s vs pre_bindings bindings env s2 res
  vset.
     compile_pat_bindings t i n_bindings exp = (spt,exp2) /\
     pmatch_list s (MAP FST n_bindings) vs pre_bindings = Match
       bindings /\
     evaluate env s [exp2] = (s2,res) /\
     LIST_REL (\(_1,k,v_exp) v. !env2.
           k IN domain spt /\
           ALOOKUP_rel ((\k. k > j /\ k < i) o dec_name_to_num) (=)
             (flatSem_environment_v env2) (flatSem_environment_v env)
             ==>
           pure_eval_to s env2 v_exp v)
       n_bindings vs /\
     EVERY ((\k. k < j) o dec_name_to_num o FST) pre_bindings /\
     j < i /\
     ALOOKUP_rel ((\k. k < j) o dec_name_to_num) (=)
       (flatSem_environment_v env)
       (pre_bindings ++ base_vs) /\
     EVERY (\(p,k,_2). EVERY (\nm. dec_name_to_num nm < j)
       (pat_bindings p) /\
           j < k /\ k < i) n_bindings ==>
     (?env2. evaluate env2 s [exp] = (s2,res) /\
     ALOOKUP_rel ((\k. k < j) o dec_name_to_num) (=)
       (flatSem_environment_v env2) (bindings ++ base_vs))`)
  CHEAT_TAC;;

(* HOL4 flat_patternProofScript.sml:651-653: the ML values that the
   definitions below antiquote *)
(* on the right side of the state relation, the pattern compiler's config is
   also needed in the compiler state *)
(* HOL4 flat_patternProofScript.sml:656: the ML values that the
   definitions below antiquote *)

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

(* HOL4 flat_patternProofScript.sml:680-686: a theorem that HOL4
   states as the value of an ML expression: v_rel_l_cases *)

(* HOL4 flat_patternProofScript.sml:688-689: the ML values that the
   definitions below antiquote *)

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

let flat_patternProof_state_rel_initial_state =
  cake_theorem "state_rel_initial_state"
  (fun () ->
    `install_conf_rel cfg ic1 ic2 ==>
     flat_patternProof_state_rel cfg (flatSem_initial_state ffi k
       ic1)
       (flatSem_initial_state ffi k ic2)`)
  CHEAT_TAC;;

let flat_patternProof_state_rel_IMP_clock =
  cake_theorem "state_rel_IMP_clock[local]"
  (fun () ->
    `flat_patternProof_state_rel cfg s t ==> state_clock t =
  state_clock s`)
  CHEAT_TAC;;

(* HOL4 flat_patternProofScript.sml:722-723: the overload nv_rel,
   which the port expands *)

let match_rel_def = cake_define
  `match_rel N x2 x3 =
        match (x2,x3) with
          (Match env1,Match env2) -> (\N. ALOOKUP_rel (\x.
            dec_name_to_num x < N) flat_patternProof_v_rel) N env1 env2
        | (No_match,No_match) -> T
        | (Match_type_error,Match_type_error) -> T
        | (_3,_4) -> F`;;

let match_rel_thms = cake_theorem "match_rel_thms[simp]"
  (fun () ->
    `(match_rel N Match_type_error e <=> e = Match_type_error) /\
     (match_rel N e Match_type_error <=> e = Match_type_error) /\
     (match_rel N No_match e <=> e = No_match) /\
     (match_rel N e No_match <=> e = No_match)`)
  CHEAT_TAC;;

let match_rel_IMP = cake_theorem "match_rel_IMP"
  (fun () ->
    `match_rel N e e' ==>
       (e = No_match /\ e = e') \/
       (e = Match_type_error /\ e = e') \/ (?env1 env2. e = Match
         env1 /\ e' = Match env2 /\ (\N. ALOOKUP_rel (\x.
         dec_name_to_num x < N) flat_patternProof_v_rel) N env1 env2)`)
  CHEAT_TAC;;

let MAX_ADD_LESS = cake_theorem "MAX_ADD_LESS"
  (fun () ->
    `(MAX i j + k < l) = (i + k < l /\ j + k < l)`)
  CHEAT_TAC;;

let LESS_MAX_ADD = cake_theorem "LESS_MAX_ADD"
  (fun () ->
    `(l < MAX i j + k) = (l < i + k \/ l < j + k)`)
  CHEAT_TAC;;

let MAX_ADD_LE = cake_theorem "MAX_ADD_LE"
  (fun () ->
    `(MAX i j + k <= l) = (i + k <= l /\ j + k <= l)`)
  CHEAT_TAC;;

let flat_patternProof_env_rel_mono = cake_theorem "env_rel_mono"
  (fun () ->
    `flat_patternProof_env_rel i env1 env2 /\ j <= i ==>
     flat_patternProof_env_rel j env1 env2`)
  CHEAT_TAC;;

let env_rel_ALOOKUP = cake_theorem "env_rel_ALOOKUP"
  (fun () ->
    `flat_patternProof_env_rel N env1 env2 /\ dec_name_to_num n < N ==>
     OPTREL flat_patternProof_v_rel (ALOOKUP
       (flatSem_environment_v env1) n) (ALOOKUP (flatSem_environment_v
       env2) n)`)
  CHEAT_TAC;;

let ALOOKUP_MAP_3 = cake_theorem "ALOOKUP_MAP_3"
  (fun () ->
    `(!x. MEM x xs ==> FST (f x) = FST x) ==>
     ALOOKUP (MAP f xs) x = OPTION_MAP (\y. SND (f (x,y)))
       (ALOOKUP xs x)`)
  CHEAT_TAC;;

let ALOOKUP_rel_MAP_same = cake_theorem "ALOOKUP_rel_MAP_same"
  (fun () ->
    `(!x. MEM x xs ==> FST (f x) = FST (g x) /\
       (P (FST (g x)) ==> R (SND (f x)) (SND (g x)))) ==>
     ALOOKUP_rel P R (MAP f xs) (MAP g xs)`)
  CHEAT_TAC;;

let do_opapp_thm = cake_theorem "do_opapp_thm"
  (fun () ->
    `do_opapp vs1 = SOME (env1,exp) /\ LIST_REL flat_patternProof_v_rel
  vs1 vs2 ==>
     (?i sg exp' env2 cfg. flat_pattern_compile_exp cfg exp =
       (i,sg,exp') /\
     flat_patternProof_env_rel (i + 1) env1 env2 /\ do_opapp vs2
       = SOME (env2,exp'))`)
  CHEAT_TAC;;

let do_opapp_thm_REVERSE = cake_theorem "do_opapp_thm_REVERSE"
  (fun () ->
    `do_opapp (REVERSE vs1) = SOME (env1,exp) /\ LIST_REL
  flat_patternProof_v_rel vs1 vs2 ==>
     (?i sg exp' env2 cfg.
     flat_pattern_compile_exp cfg exp = (i,sg,exp') /\
     flat_patternProof_env_rel (i + 1) env1 env2 /\
     do_opapp (REVERSE vs2) = SOME (env2,exp'))`)
  CHEAT_TAC;;

let pmatch_thm = cake_theorem "pmatch_thm"
  (fun () ->
    `(!(s:('c,'ffi)flatSem_state) p v vs r s1 v1 vs1.
       pmatch s p v vs = r /\ ~(r = Match_type_error) /\
       flat_patternProof_state_rel cfg s s1 /\
       flat_patternProof_v_rel v v1 /\
       (\N. ALOOKUP_rel (\x. dec_name_to_num x < N)
         flat_patternProof_v_rel) N vs vs1 ==> (?r1. pmatch s1 p v1 vs1
         = r1 /\ match_rel N r r1)) /\
     (!(s:('c,'ffi)flatSem_state) ps v vs r s1 v1 vs1.
       pmatch_list s ps v vs = r /\ ~(r = Match_type_error) /\
       flat_patternProof_state_rel cfg s s1 /\
       LIST_REL flat_patternProof_v_rel v v1 /\
       (\N. ALOOKUP_rel (\x. dec_name_to_num x < N)
         flat_patternProof_v_rel) N vs vs1 ==> (?r1. pmatch_list s1 ps
         v1 vs1 = r1 /\ match_rel N r r1))`)
  CHEAT_TAC;;

let simple_val_rel_step_isClosure =
  cake_theorem "simple_val_rel_step_isClosure"
  (fun () ->
    `simple_basic_val_rel x y ==> ~(isClosure x) /\ ~(isClosure y)`)
  CHEAT_TAC;;

let flat_patternProof_simple_val_rel = cake_theorem "simple_val_rel"
  (fun () ->
    `flatProps_simple_val_rel flat_patternProof_v_rel`)
  CHEAT_TAC;;

let flat_patternProof_simple_state_rel = cake_theorem "simple_state_rel"
  (fun () ->
    `flatProps_simple_state_rel flat_patternProof_v_rel
  (flat_patternProof_state_rel cfg)`)
  CHEAT_TAC;;

(* HOL4 flat_patternProofScript.sml:929-930: a theorem that HOL4
   states as the value of an ML expression: do_app_thm *)

let do_app_thm_REVERSE = cake_theorem "do_app_thm_REVERSE"
  (fun () ->
    `do_app s1 op (REVERSE vs1) = SOME (t1,r1) /\
     flat_patternProof_state_rel cfg s1 s2 /\ LIST_REL
       flat_patternProof_v_rel vs1 vs2 ==>
     (?t2 r2. semanticPrimitivesProps_result_rel
       flat_patternProof_v_rel flat_patternProof_v_rel r1 r2 /\
     flat_patternProof_state_rel cfg t1 t2 /\ do_app s2 op
       (REVERSE vs2) = SOME (t2,r2))`)
  CHEAT_TAC;;

let do_if_helper = cake_theorem "do_if_helper"
  (fun () ->
    `do_if b x y = SOME e /\ flat_patternProof_v_rel b b' ==>
     ((b' = Boolv T) = (b = Boolv T)) /\ ((b' = Boolv F) = (b =
       Boolv F))`)
  CHEAT_TAC;;

let MAX_LIST_LESS_EVERY = cake_theorem "MAX_LIST_LESS_EVERY"
  (fun () ->
    `(MAX_LIST xs < N) = (0 < N /\ EVERY (\x. x < N) xs)`)
  CHEAT_TAC;;

let max_dec_name_LESS_EVERY = cake_theorem "max_dec_name_LESS_EVERY"
  (fun () ->
    `(max_dec_name ns < N) = (0 < N /\ EVERY (\n. dec_name_to_num n <
  N) ns)`)
  CHEAT_TAC;;

let _ = size_thms "flatSem_v";;
(* HOL4 flat_patternProofScript.sml:974-978: the tactic that proves
   the termination *)
let encode_val_def = cake_define_wf
  `MEASURE flatSem_v_size`
  `encode_val others =
      match others with
        (Litv l:flatSem_v) -> Litv l
      | (Conv stmp xs) -> pattern_semantics_Term
     (match stmp with NONE -> NONE | SOME (i,_5) -> SOME i)
     (MAP encode_val xs)
      | (Loc _6 n) -> pattern_semantics_RefPtr n
      | others -> pattern_semantics_Other`;;

let decode_test_simulation = cake_theorem "decode_test_simulation"
  (fun () ->
    `dt_test test enc_v = SOME b /\
     pure_eval_to s env x v /\
     enc_v = encode_val v ==>
     pure_eval_to s env (flat_pattern_decode_test tr test x)
       (Boolv b)`)
  CHEAT_TAC;;

let app_pos_Term_IMP = cake_theorem "app_pos_Term_IMP"
  (fun () ->
    `!xs n. app_pos refs (Pos n pos) (pattern_semantics_Term c xs) =
  SOME y ==>
     n < LENGTH xs /\ app_pos refs pos (EL n xs) = SOME y`)
  CHEAT_TAC;;

let encode_refs_def = cake_define
  `encode_refs s = FUN_FMAP (\i. encode_val (match EL i (state_refs s)
  with semanticPrimitives_Refv v -> v))
     (count (LENGTH (state_refs s)) INTER {i | ?v. EL i
       (state_refs s) = semanticPrimitives_Refv v})`;;

let FLOOKUP_encode_refs = cake_theorem "FLOOKUP_encode_refs"
  (fun () ->
    `FLOOKUP (encode_refs s) n = (if n < LENGTH (state_refs s) then
  (match EL n (state_refs s) with semanticPrimitives_Refv v -> SOME
  (encode_val v) | _7 -> NONE) else NONE)`)
  CHEAT_TAC;;

let decode_pos_simulation = cake_theorem "decode_pos_simulation"
  (fun () ->
    `!pos exp x.
     app_pos (encode_refs s) pos (encode_val x) = SOME enc_y /\
     pure_eval_to s env exp x ==>
     (?y. enc_y = encode_val y /\
     pure_eval_to s env (decode_pos tr exp pos) y)`)
  CHEAT_TAC;;

(* HOL4 flat_patternProofScript.sml:1052-1054: a theorem that HOL4
   states as the value of an ML expression: fold_Boolv *)

let flat_patternProof_do_eq_Boolv = cake_theorem "do_eq_Boolv"
  (fun () ->
    `do_eq (Boolv x) (Boolv y) = Eq_val (x = y)`)
  CHEAT_TAC;;

let do_if_Boolv = cake_theorem "do_if_Boolv"
  (fun () ->
    `do_if (Boolv x) y z = SOME (if x then y else z)`)
  CHEAT_TAC;;

let flat_patternProof_evaluate_Bool = cake_theorem "evaluate_Bool"
  (fun () ->
    `evaluate env s [flatLang_Bool t b] = (s,Rval [Boolv b])`)
  CHEAT_TAC;;

let SmartIf_thm = cake_theorem "SmartIf_thm"
  (fun () ->
    `SmartIf t e p q =
       (if ?t. e = flatLang_Bool t T then p else
       if ?t. e = flatLang_Bool t F then q else
       If t e p q)`)
  CHEAT_TAC;;

let evaluate_SmartIf = cake_theorem "evaluate_SmartIf"
  (fun () ->
    `evaluate env s [SmartIf t x y z] = evaluate env s [If t x y z]`)
  CHEAT_TAC;;

let decode_guard_simulation = cake_theorem "decode_guard_simulation"
  (fun () ->
    `!b.
     dt_eval_guard (encode_refs s) (encode_val y) gd = SOME b /\
     pure_eval_to s env x y ==>
     pure_eval_to s env (decode_guard tr x gd) (Boolv b)`)
  CHEAT_TAC;;

let simp_guard_thm = cake_theorem "simp_guard_thm"
  (fun () ->
    `!gd x. dt_eval_guard r v gd = SOME x ==>
     dt_eval_guard r v (simp_guard gd) = SOME x`)
  CHEAT_TAC;;

let decode_dtree_simulation = cake_theorem "decode_dtree_simulation"
  (fun () ->
    `dt_eval (encode_refs s) (encode_val y) dtree = SOME v /\
     pure_eval_to s env x y ==>
     evaluate env s [decode_dtree tr exps x default_x dtree] =
     evaluate env s [match v with MatchSuccess i -> (match
       sptree_lookup i exps with
       SOME exp -> exp | NONE -> default_x) | _8 -> default_x]`)
  CHEAT_TAC;;

let encode_pat_match_simulation =
  cake_theorem "encode_pat_match_simulation"
  (fun () ->
    `(!(s:('c,'ffi)flatSem_state) pat v pre_bindings res.
     flatSem_pmatch s pat v pre_bindings = res /\ ~(res =
       Match_type_error) ==>
     pattern_semantics_pmatch (encode_refs s) (encode_pat pat)
       (encode_val v) =
     (if res = No_match then PMatchFailure else PMatchSuccess)) /\
     (!(s:('c,'ffi)flatSem_state) ps vs pre_bindings res.
     flatSem_pmatch_list s ps vs pre_bindings = res /\ ~(res =
       Match_type_error) ==>
     pattern_semantics_pmatch_list (encode_refs s) (MAP encode_pat
       ps)
       (MAP encode_val vs) =
     (if res = No_match then PMatchFailure else PMatchSuccess))`)
  CHEAT_TAC;;

let pmatch_rows_encode = cake_theorem "pmatch_rows_encode"
  (fun () ->
    `!pats j_offs.
     ~(pmatch_rows pats s v = Match_type_error) ==>
     (match (pattern_semantics_match (encode_refs s)
       (MAPi (\j (p,_10). (encode_pat p,j + j_offs)) pats)
           (encode_val v)) with NONE -> F | SOME (MatchSuccess n)
             -> (?i env. n = i + j_offs /\ i < LENGTH pats /\
           pmatch s (FST (EL i pats)) v [] = Match env /\
           pmatch_rows pats s v = Match (env,EL i pats)) | _9 ->
             pmatch_rows pats s v = No_match)`)
  CHEAT_TAC;;

let naive_pattern_match_correct =
  cake_theorem "naive_pattern_match_correct"
  (fun () ->
    `!t mats vs bindings exp res.
      LIST_REL (pure_eval_to s env) (MAP SND mats) vs /\
      pmatch_list s (MAP FST mats) vs bindings = res /\ ~(res =
        Match_type_error) /\
      naive_pattern_match t mats = exp ==>
      pure_eval_to s env exp (Boolv (~(res = No_match)))`)
  CHEAT_TAC;;

(* HOL4 flat_patternProofScript.sml:1308-1312: a theorem that HOL4
   states as the value of an ML expression:
   naive_pattern_match_correct_inst *)

let naive_pattern_matches_correct =
  cake_theorem "naive_pattern_matches_correct"
  (fun () ->
    `!t x mats dflt exp v res.
     naive_pattern_matches t x mats dflt = exp /\
     pure_eval_to s env x v /\
     pmatch_rows mats s v = res /\ ~(res = Match_type_error) ==>
     evaluate env s [exp] = (match res with Match (_11,_12,exp) ->
         evaluate env s [exp] | _13 -> evaluate env s [dflt])`)
  CHEAT_TAC;;

let pmatch_rows_same_FST = cake_theorem "pmatch_rows_same_FST"
  (fun () ->
    `!pats pats2. MAP FST pats = MAP FST pats2 ==>
     (match pmatch_rows pats s v with Match_type_error ->
       pmatch_rows pats2 s v = Match_type_error | No_match ->
       pmatch_rows pats2 s v = No_match | Match (env,p,e) -> (?i. i <
       LENGTH pats2 /\ EL i pats = (p,e) /\
           pmatch_rows pats2 s v = Match (env,EL i pats2)))`)
  CHEAT_TAC;;

(* HOL4 flat_patternProofScript.sml:1358-1360: a theorem that HOL4
   states as the value of an ML expression: comp_thm *)

let evaluate_compile_pats = cake_theorem "evaluate_compile_pats"
  (fun () ->
    `~(pmatch_rows pats s v = Match_type_error) /\
     pure_eval_to s env exp v ==>
     evaluate env s [compile_pats cfg naive t N exp default_x pats]
       =
     evaluate env s [match pmatch_rows pats s v with Match
       (env',p',e') -> compile_pat_rhs t N exp (p',e') | _14 ->
       default_x]`)
  CHEAT_TAC;;

let compile_match_pmatch_rows = cake_theorem "compile_match_pmatch_rows"
  (fun () ->
    `!pats k sg pats2 res.
     compile_match cfg pats = (k,sg,pats2) /\
     flat_patternProof_state_rel s_cfg s t /\
     flat_patternProof_v_rel v v' /\
     k <= N /\
     pmatch_rows pats s v = res ==>
     (match res with Match_type_error -> T | No_match ->
       pmatch_rows pats2 t v' = No_match | Match (env,p,e) -> (?i env'.
       i < LENGTH pats /\ i < LENGTH pats2 /\
           (p,e) = EL i pats /\ (\N. ALOOKUP_rel (\x.
             dec_name_to_num x < N) flat_patternProof_v_rel) N env env'
             /\
           pmatch_rows pats2 t v' = Match (env',EL i pats2)))`)
  CHEAT_TAC;;

let compile_match_EL = cake_theorem "compile_match_EL"
  (fun () ->
    `!pats pats2 k sg i.
     compile_match cfg pats = (k,sg,pats2) /\
     i < LENGTH pats /\
     EL i pats = (pat,exp) ==>
     (?exp_i sg exp'.
     flat_pattern_compile_exp cfg exp = (exp_i,sg,exp') /\
     EL i pats2 = (pat,exp') /\
     exp_i <= k /\ max_dec_name (pat_bindings pat) <= k)`)
  CHEAT_TAC;;

let evaluate_compile_pat_rhs = cake_theorem "evaluate_compile_pat_rhs"
  (fun () ->
    `evaluate (sem_env_v_fupd f env3) s
       [compile_pat_rhs tr N (flatLang_Var_local tr
         (enc_num_to_name N))
       (p,exp)] = (t,res) /\
     pmatch s p v [] = Match bindings /\
     flat_patternProof_env_rel M env1 env2 /\
     (\N. ALOOKUP_rel (\x. dec_name_to_num x < N)
       flat_patternProof_v_rel) M l_bindings bindings /\
     f (sem_env_v env3) = (enc_num_to_name N,v) ::
       flatSem_environment_v env2 /\
     N <= M /\
     max_dec_name (pat_bindings p) < N - 1 ==>
     (?ext_env.
     evaluate ext_env s [exp] = (t,res) /\
     flat_patternProof_env_rel (N - 1)
       (flatSem_environment_v_fupd (K (l_bindings ++
       flatSem_environment_v env1)) env1) ext_env)`)
  CHEAT_TAC;;

let flat_patternProof_state_rel_dec_clock =
  cake_theorem "state_rel_dec_clock"
  (fun () ->
    `flat_patternProof_state_rel cfg s1 s2 ==>
  flat_patternProof_state_rel cfg (dec_clock s1) (dec_clock s2)`)
  CHEAT_TAC;;

let OPTION_ALL_FORALL = cake_theorem "OPTION_ALL_FORALL"
  (fun () ->
    `OPTION_ALL P x = (!y. x = SOME y ==> P y)`)
  CHEAT_TAC;;

let do_eval_thm = cake_theorem "do_eval_thm"
  (fun () ->
    `do_eval xs (flatSem_state_eval_config s) = SOME
  (decs,eval_config,rv) /\
     flat_patternProof_state_rel cfg s t /\
     LIST_REL flat_patternProof_v_rel xs ys ==>
     (?rv' decs' eval_config'.
     do_eval ys (flatSem_state_eval_config t) = SOME
       (decs',eval_config',rv') /\
     flat_patternProof_state_rel cfg
       (flatSem_state_eval_config_fupd (K eval_config) s)
       (flatSem_state_eval_config_fupd (K eval_config') t) /\
     flat_patternProof_v_rel rv rv' /\
     decs' = MAP (compile_dec cfg) decs)`)
  CHEAT_TAC;;

let flat_patternProof_evaluate_decs_sing =
  cake_theorem "evaluate_decs_sing"
  (fun () ->
    `evaluate_decs s [d] = evaluate_dec s d`)
  CHEAT_TAC;;

(* HOL4 flat_patternProofScript.sml:1541: ML code, not ported *)

let compile_exps_evaluate = cake_theorem "compile_exps_evaluate"
  (fun () ->
    `(!env1 ((s1:('c,'ffi)flatSem_state)) xs t1 r1 i sg ys N env2 s2
  cfg.
       evaluate env1 s1 xs = (t1,r1) /\
       flat_pattern_compile_exps cfg xs = (i,sg,ys) /\
       flat_patternProof_env_rel N env1 env2 /\
         flat_patternProof_state_rel s_cfg s1 s2 /\ i < N /\ ~(r1 = Rerr
         (Rabort Rtype_error)) ==>
       (?t2 r2.
         semanticPrimitivesProps_result_rel (LIST_REL
           flat_patternProof_v_rel) flat_patternProof_v_rel r1 r2 /\
         flat_patternProof_state_rel s_cfg t1 t2 /\
         evaluate env2 s2 ys = (t2,r2))) /\
     (!((s1:('c,'ffi)flatSem_state)) decs s2 t1 cfg decs' res.
       evaluate_decs s1 decs = (t1,res) /\
       decs' = MAP (compile_dec cfg) decs /\
       flat_patternProof_state_rel s_cfg s1 s2 /\ ~(res = SOME
         (Rabort Rtype_error)) ==>
       (?t2 res'.
         evaluate_decs s2 decs' = (t2,res') /\
         OPTREL (exc_rel flat_patternProof_v_rel) res res' /\
         flat_patternProof_state_rel s_cfg t1 t2))`)
  CHEAT_TAC;;

let compile_decs_eval_sim = cake_theorem "compile_decs_eval_sim"
  (fun () ->
    `install_conf_rel cfg ic1 ic2 ==>
     flatProps_eval_sim ffi prog prog' ic1 ic2
       (\decs decs'. MAP (compile_dec cfg2) decs = decs') F`)
  CHEAT_TAC;;

let compile_decs_semantics = cake_theorem "compile_decs_semantics"
  (fun () ->
    `install_conf_rel cfg ic1 ic2 /\ ~(flatSem_semantics ic1 ffi prog =
  Fail) ==>
     flatSem_semantics ic1 ffi prog =
     flatSem_semantics ic2 ffi (MAP (compile_dec cfg1) prog)`)
  CHEAT_TAC;;

(* set_globals and esgc properties *)

let set_globals_decode_pos = cake_theorem "set_globals_decode_pos"
  (fun () ->
    `!p exp. flatProps_set_globals exp = EMPTY_BAG ==>
     flatProps_set_globals (decode_pos t exp p) = EMPTY_BAG`)
  CHEAT_TAC;;

let set_globals_decode_test = cake_theorem "set_globals_decode_test"
  (fun () ->
    `flatProps_set_globals exp = EMPTY_BAG ==>
     flatProps_set_globals (flat_pattern_decode_test t d exp) =
       EMPTY_BAG`)
  CHEAT_TAC;;

let set_globals_decode_guard = cake_theorem "set_globals_decode_guard"
  (fun () ->
    `flatProps_set_globals exp = EMPTY_BAG ==>
     flatProps_set_globals (decode_guard t exp gd) = EMPTY_BAG`)
  CHEAT_TAC;;

let set_globals_decode_dtree_empty =
  cake_theorem "set_globals_decode_dtree_empty"
  (fun () ->
    `flatProps_set_globals x = EMPTY_BAG /\ flatProps_set_globals dflt =
  EMPTY_BAG /\
     EVERY (\y. flatProps_set_globals y = EMPTY_BAG) (toList
       br_spt) ==>
     flatProps_set_globals (decode_dtree t br_spt x dflt dtree) =
       EMPTY_BAG`)
  CHEAT_TAC;;

let inv_on_FOLDR = cake_theorem "inv_on_FOLDR"
  (fun () ->
    `!f. (!x v. MEM x xs ==> f (g x v) = f v) ==>
     f (ITLIST g xs v) = f v`)
  CHEAT_TAC;;

let set_globals_compile_pat_bindings =
  cake_theorem "set_globals_compile_pat_bindings"
  (fun () ->
    `!t i n_bindings exp.
     EVERY (\(_15,_16,v_exp). flatProps_set_globals v_exp =
       EMPTY_BAG) n_bindings ==>
     flatProps_set_globals (SND (compile_pat_bindings t i
       n_bindings exp)) =
     flatProps_set_globals exp`)
  CHEAT_TAC;;

let set_globals_naive_pattern_match =
  cake_theorem "set_globals_naive_pattern_match"
  (fun () ->
    `!t xs. EVERY (\v. flatProps_set_globals (SND v) = EMPTY_BAG) xs ==>
     flatProps_set_globals (naive_pattern_match t xs) = EMPTY_BAG`)
  CHEAT_TAC;;

let set_globals_naive_pattern_matches =
  cake_theorem "set_globals_naive_pattern_matches"
  (fun () ->
    `flatProps_set_globals x = EMPTY_BAG ==>
     (flatProps_set_globals (naive_pattern_matches t x ps dflt)) <=
     (flatProps_elist_globals (dflt :: MAP SND ps))`)
  CHEAT_TAC;;

let set_toList_fromList = cake_theorem "set_toList_fromList"
  (fun () ->
    `set_of_list (toList (fromList xs)) = set_of_list xs`)
  CHEAT_TAC;;

let set_globals_compile_pats = cake_theorem "set_globals_compile_pats"
  (fun () ->
    `(~naive ==> flatProps_elist_globals (dflt :: MAP SND ps) =
  EMPTY_BAG) /\
     flatProps_set_globals x = EMPTY_BAG ==>
     flatProps_set_globals (compile_pats cfg naive t N x dflt ps)
       <=
     flatProps_elist_globals (dflt :: MAP SND ps)`)
  CHEAT_TAC;;

let SUB_BAG_2 = cake_theorem "SUB_BAG_2"
  (fun () ->
    `x <= y /\ x' <= y' ==> (BAG_UNION) x x' <= (BAG_UNION) y y'`)
  CHEAT_TAC;;

let compile_exp_set_globals = cake_theorem "compile_exp_set_globals"
  (fun () ->
    `(!cfg exp N sg exp'.
     flat_pattern_compile_exp cfg exp = (N,sg,exp') ==>
     flatProps_set_globals exp' <= flatProps_set_globals exp) /\
     (!cfg exps N sg exps'.
     flat_pattern_compile_exps cfg exps = (N,sg,exps') ==>
     flatProps_elist_globals exps' <= flatProps_elist_globals exps)
       /\
     (!cfg m N sg m'.
     compile_match cfg m = (N,sg,m') ==>
     flatProps_elist_globals (MAP SND m') <=
       flatProps_elist_globals (MAP SND m))`)
  CHEAT_TAC;;

let flat_patternProof_FST_SND_EQ_CASE = cake_theorem "FST_SND_EQ_CASE"
  (fun () ->
    `FST = (\(a,b). a) /\ SND = (\(a,b). b)`)
  CHEAT_TAC;;

let compile_decs_elist_globals =
  cake_theorem "compile_decs_elist_globals"
  (fun () ->
    `!decs.
     flatProps_elist_globals (MAP (compile_dec cfg) decs) <=
     flatProps_elist_globals decs`)
  CHEAT_TAC;;

let esgc_free_decode_pos = cake_theorem "esgc_free_decode_pos"
  (fun () ->
    `!p exp. flatProps_esgc_free exp ==>
     flatProps_esgc_free (decode_pos t exp p)`)
  CHEAT_TAC;;

let esgc_free_decode_test = cake_theorem "esgc_free_decode_test"
  (fun () ->
    `flatProps_esgc_free exp ==> flatProps_esgc_free
  (flat_pattern_decode_test t d exp)`)
  CHEAT_TAC;;

let esgc_free_decode_guard = cake_theorem "esgc_free_decode_guard"
  (fun () ->
    `flatProps_esgc_free exp ==> flatProps_esgc_free (decode_guard t
  exp gd)`)
  CHEAT_TAC;;

let esgc_free_decode_dtree = cake_theorem "esgc_free_decode_dtree"
  (fun () ->
    `flatProps_esgc_free v_exp /\ flatProps_esgc_free dflt /\
     EVERY (\y. flatProps_esgc_free y) (toList br_spt) ==>
     flatProps_esgc_free (decode_dtree t br_spt v_exp dflt dtree)`)
  CHEAT_TAC;;

let esgc_free_compile_pat_bindings =
  cake_theorem "esgc_free_compile_pat_bindings"
  (fun () ->
    `!t i n_bindings exp.
     flatProps_esgc_free exp /\
     EVERY (\(_17,_18,v_exp). flatProps_esgc_free v_exp) n_bindings
       ==>
     flatProps_esgc_free (SND (compile_pat_bindings t i
       n_bindings exp))`)
  CHEAT_TAC;;

let esgc_free_naive_pattern_match =
  cake_theorem "esgc_free_naive_pattern_match"
  (fun () ->
    `!t xs. EVERY flatProps_esgc_free (MAP SND xs) ==>
     flatProps_esgc_free (naive_pattern_match t xs)`)
  CHEAT_TAC;;

let esgc_free_naive_pattern_matches =
  cake_theorem "esgc_free_naive_pattern_matches"
  (fun () ->
    `!t x xs dflt. EVERY flatProps_esgc_free (x :: dflt :: MAP SND xs)
  ==>
     flatProps_esgc_free (naive_pattern_matches t x xs dflt)`)
  CHEAT_TAC;;

let esgc_free_compile_pats = cake_theorem "esgc_free_compile_pats"
  (fun () ->
    `flatProps_esgc_free dflt /\ EVERY flatProps_esgc_free (MAP SND ps)
  ==>
     flatProps_esgc_free (compile_pats cfg naive t N
       (flatLang_Var_local t' nm) dflt ps)`)
  CHEAT_TAC;;

let compile_exp_esgc_free = cake_theorem "compile_exp_esgc_free"
  (fun () ->
    `(!cfg exp N sg exp'.
     flat_pattern_compile_exp cfg exp = (N,sg,exp') /\
     flatProps_esgc_free exp ==>
     flatProps_esgc_free exp') /\
     (!cfg exps N sg exps'.
     flat_pattern_compile_exps cfg exps = (N,sg,exps') /\
     EVERY flatProps_esgc_free exps ==>
     EVERY flatProps_esgc_free exps') /\
     (!cfg m N sg m'.
     compile_match cfg m = (N,sg,m') /\
     EVERY (flatProps_esgc_free o SND) m ==>
     EVERY (flatProps_esgc_free o SND) m')`)
  CHEAT_TAC;;

let flat_patternProof_compile_decs_esgc_free =
  cake_theorem "compile_decs_esgc_free"
  (fun () ->
    `!decs.
     EVERY flatProps_esgc_free decs ==>
     EVERY flatProps_esgc_free (MAP (compile_dec cfg) decs)`)
  CHEAT_TAC;;

let naive_pattern_match_no_Mat =
  cake_theorem "naive_pattern_match_no_Mat"
  (fun () ->
    `!t xs. EVERY (no_Mat o SND) xs ==>
     no_Mat (naive_pattern_match t xs)`)
  CHEAT_TAC;;

let naive_pattern_matches_no_Mat =
  cake_theorem "naive_pattern_matches_no_Mat"
  (fun () ->
    `!t x xs dflt. EVERY no_Mat (x :: dflt :: MAP SND xs) ==>
     no_Mat (naive_pattern_matches t x xs dflt)`)
  CHEAT_TAC;;

let compile_pat_bindings_no_Mat =
  cake_theorem "compile_pat_bindings_no_Mat"
  (fun () ->
    `!t i n_bindings exp.
     no_Mat exp /\
     EVERY (\(_19,_20,v_exp). no_Mat v_exp) n_bindings ==>
     no_Mat (SND (compile_pat_bindings t i n_bindings exp))`)
  CHEAT_TAC;;

let decode_pos_no_Mat = cake_theorem "decode_pos_no_Mat"
  (fun () ->
    `!p exp. no_Mat exp ==>
     no_Mat (decode_pos t exp p)`)
  CHEAT_TAC;;

let decode_test_no_Mat = cake_theorem "decode_test_no_Mat"
  (fun () ->
    `no_Mat exp ==> no_Mat (flat_pattern_decode_test t d exp)`)
  CHEAT_TAC;;

let decode_guard_no_Mat = cake_theorem "decode_guard_no_Mat"
  (fun () ->
    `no_Mat exp ==> no_Mat (decode_guard t exp gd)`)
  CHEAT_TAC;;

let decode_dtree_no_Mat = cake_theorem "decode_dtree_no_Mat"
  (fun () ->
    `no_Mat v_exp /\ no_Mat dflt /\
     EVERY no_Mat (toList br_spt) ==>
     no_Mat (decode_dtree t br_spt v_exp dflt dtree)`)
  CHEAT_TAC;;

let compile_pats_no_Mat = cake_theorem "compile_pats_no_Mat"
  (fun () ->
    `no_Mat dflt /\ no_Mat x /\ EVERY no_Mat (MAP SND ps) ==>
     no_Mat (compile_pats cfg naive t N x dflt ps)`)
  CHEAT_TAC;;

let compile_exp_no_Mat = cake_theorem "compile_exp_no_Mat"
  (fun () ->
    `(!cfg exp N sg exp'.
     flat_pattern_compile_exp cfg exp = (N,sg,exp') ==>
     no_Mat exp') /\
     (!cfg exps N sg exps'.
     flat_pattern_compile_exps cfg exps = (N,sg,exps') ==>
     EVERY no_Mat exps') /\
     (!cfg pats N sg pats'.
     compile_match cfg pats = (N,sg,pats') ==>
     EVERY no_Mat (MAP SND pats'))`)
  CHEAT_TAC;;

let compile_decs_no_Mat = cake_theorem "compile_decs_no_Mat"
  (fun () ->
    `!decs. no_Mat_decs (MAP (compile_dec cfg) decs)`)
  CHEAT_TAC;;
