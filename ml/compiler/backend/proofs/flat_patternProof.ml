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
needs "semantics/ffi/ffi.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;
needs "semantics/semanticPrimitives.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "flat_patternProof"
  ["backendProps"; "backend_common"; "ffi"; "flatLang"; "flatProps";
   "flatSem"; "flat_pattern"; "misc"; "mlstring"; "pattern_semantics";
   "semanticPrimitives"; "semanticPrimitivesProps"];;
(* HOL4 ancestors outside the port: bag *)

(* HOL4 flat_patternProofScript.sml:14: ML code, not ported *)

(* simple properties *)
let op_sets_globals_gbag = prove
 (`op_sets_globals op = (~(flatProps_op_gbag op = EMPTY_BAG))`,
  CHEAT_TAC);;

let compile_exp_set_globals_FST_SND = prove
 (`(!cfg x. FST (SND (flat_pattern_compile_exp cfg x)) =
     (~(flatProps_set_globals x = EMPTY_BAG))) /\
    (!cfg xs. FST (SND (flat_pattern_compile_exps cfg xs)) =
     (~(flatProps_elist_globals xs = EMPTY_BAG))) /\
   (!cfg ps. FST (SND (compile_match cfg ps)) =
     (~(flatProps_elist_globals (MAP SND ps) = EMPTY_BAG)))`,
  CHEAT_TAC);;

let compile_exp_set_globals_tup = prove
 (`(!cfg x i sg y. flat_pattern_compile_exp cfg x = (i,sg,y) ==>
     sg = (~(flatProps_set_globals x = EMPTY_BAG))) /\
    (!cfg xs i sg ys. flat_pattern_compile_exps cfg xs = (i,sg,ys)
      ==>
     sg = (~(flatProps_elist_globals xs = EMPTY_BAG))) /\
   (!cfg ps i sg ps2. compile_match cfg ps = (i,sg,ps2) ==>
     sg = (~(flatProps_elist_globals (MAP SND ps) = EMPTY_BAG)))`,
  CHEAT_TAC);;

(* decoding the encoded names *)

let sum_string_ords_eq = prove
 (`sum_string_ords i s = SUM (MAP (\c. ORD c - 35) (DROP i (explode
  s)))`,
  CHEAT_TAC);;

let dec_enc_aux = prove
 (`!xs. dec_name_to_num (implode (enc_num_to_name_aux i xs)) =
   i + SUM (MAP (\c. ORD c - 35) xs)`,
  CHEAT_TAC);;

let dec_enc = prove
 (`dec_name_to_num (enc_num_to_name i) = i`,
  CHEAT_TAC);;

let enc_num_to_name_inj = prove
 (`(enc_num_to_name i = enc_num_to_name j) = (i = j)`,
  CHEAT_TAC);;

(* lists and lookups *)

let LIST_REL_ALOOKUP_OPTREL = prove
 (`!xs ys.
   ALL2 R xs ys /\
   (!x y. R x y /\ MEM x xs /\ MEM y ys /\ (v = FST x \/ v = FST y)
     ==>
     FST x = FST y /\ R2 (SND x) (SND y)) ==> OPTREL R2 (ALOOKUP xs
       v) (ALOOKUP ys v)`,
  CHEAT_TAC);;

let LIST_REL_ALOOKUP = prove
 (`!xs ys.
   ALL2 R xs ys /\
   (!x y. R x y /\ MEM x xs /\ MEM y ys /\ (v = FST x \/ v = FST y)
     ==> x = y) ==> ALOOKUP xs v = ALOOKUP ys v`,
  CHEAT_TAC);;

let LIST_REL_FILTER_MONO = prove
 (`!xs ys.
   ALL2 R (FILTER P1 xs) (FILTER P2 ys) /\
   (!x. MEM x xs /\ P3 x ==> P1 x) /\
   (!y. MEM y ys /\ P4 y ==> P2 y) /\
   (!x y. MEM x xs /\ MEM y ys /\ R x y ==> P3 x = P4 y) ==> ALL2 R
     (FILTER P3 xs) (FILTER P4 ys)`,
  CHEAT_TAC);;

let COND_false = prove
 (`~P ==> ((if P then x else y) = y)`,
  CHEAT_TAC);;

let COND_true = prove
 (`P ==> ((if P then x else y) = x)`,
  CHEAT_TAC);;

(* HOL4 flat_patternProofScript.sml:165-166: a theorem that HOL4
   states as the value of an ML expression: FILTER_EQ_MONO *)

(* HOL4 flat_patternProofScript.sml:168-171: a theorem that HOL4
   states as the value of an ML expression: FILTER_EQ_MONO_TRANS *)

let FILTER_EQ_ALOOKUP_EQ = prove
 (`!xs ys. FILTER P xs = ys /\ (!z. P (x,z)) ==>
   ALOOKUP xs x = ALOOKUP ys x`,
  CHEAT_TAC);;

(* HOL4 flat_patternProofScript.sml:183-184: a theorem that HOL4
   states as the value of an ML expression: ALOOKUP_FILTER_EQ *)

let MEM_enumerate_EL = prove
 (`!xs i x. MEM x (enumerate i xs) = (?j. j < LENGTH xs /\ x = (i +
  j,EL j xs))`,
  CHEAT_TAC);;

let ALL_DISTINCT_enumerate = prove
 (`!xs i. ALL_DISTINCT (enumerate i xs)`,
  CHEAT_TAC);;

let pure_eval_to_def = new_definition
  `pure_eval_to s env exp v = (flatSem_evaluate env s [exp] = (s,Rval
  [v]))`;;

let pmatch_list_Match_IMP_LENGTH = prove
 (`!xs ys env env' s. flatSem_pmatch_list s xs ys env = Match env' ==>
   LENGTH xs = LENGTH ys`,
  CHEAT_TAC);;

let APPEND_LENGTH_EQ = prove
 (`!xs xs'. LENGTH xs = LENGTH xs' ==>
   (APPEND xs ys = APPEND xs' ys' <=> xs = xs' /\ ys = ys')`,
  CHEAT_TAC);;

let pmatch_list_append_Match_exists = prove
 (`(flatSem_pmatch_list s (APPEND xs ys) vs pre_bindings = Match
  bindings) =
   (?vs1 vs2 bindings1. vs = APPEND vs1 vs2 /\
   flatSem_pmatch_list s xs vs1 pre_bindings = Match bindings1 /\
   flatSem_pmatch_list s ys vs2 bindings1 = Match bindings)`,
  CHEAT_TAC);;

let ALOOKUP_rel_def = new_definition
  `ALOOKUP_rel P R env1 env2 =
   (!x. P x ==> OPTREL R (ALOOKUP env1 x) (ALOOKUP env2 x))`;;

let ALOOKUP_rel_empty = prove
 (`ALOOKUP_rel P R [] []`,
  CHEAT_TAC);;

let ALOOKUP_rel_cons_false = prove
 (`(~(P x) ==> ALOOKUP_rel P R (CONS (x,y) env1) env2 = ALOOKUP_rel P R
  env1 env2) /\
   (~(P x) ==> ALOOKUP_rel P R env1 (CONS (x,y) env2) = ALOOKUP_rel
     P R env1 env2)`,
  CHEAT_TAC);;

let ALOOKUP_rel_APPEND_L_false = prove
 (`ALL ((~) o P o FST) xs ==>
   ALOOKUP_rel P R (APPEND xs ys) zs =
   ALOOKUP_rel P R ys zs`,
  CHEAT_TAC);;

let ALOOKUP_rel_refl = prove
 (`(!x y. P x /\ MEM (x,y) xs ==> R y y) ==> ALOOKUP_rel P R xs xs`,
  CHEAT_TAC);;

let ALOOKUP_rel_cons = prove
 (`(P x ==> R y z) /\ ALOOKUP_rel P R ys zs ==>
   ALOOKUP_rel P R (CONS (x,y) ys) (CONS (x,z) zs)`,
  CHEAT_TAC);;

let ALOOKUP_rel_mono = prove
 (`ALOOKUP_rel P R xs ys /\
   (!x y z. P' x ==> P x) /\
   (!x y z. P' x /\ R y z ==> R' y z) ==>
   ALOOKUP_rel P' R' xs ys`,
  CHEAT_TAC);;

let ALOOKUP_rel_mono_rel = prove
 (`(!y z. R y z ==> R' y z) ==>
   ALOOKUP_rel P R xs ys ==>
   ALOOKUP_rel P R' xs ys`,
  CHEAT_TAC);;

let ALOOKUP_rel_append_suff = prove
 (`ALOOKUP_rel P R xs1 xs3 /\ ALOOKUP_rel P R xs2 xs4 ==>
   ALOOKUP_rel P R (APPEND xs1 xs2) (APPEND xs3 xs4)`,
  CHEAT_TAC);;

let ALOOKUP_rel_EQ_ALOOKUP = prove
 (`ALOOKUP_rel P (=) xs ys /\ P x ==>
   ALOOKUP xs x = ALOOKUP ys x`,
  CHEAT_TAC);;

let ALOOKUP_rel_eq_fst = prove
 (`!xs ys.
   ALL2 (\x y. FST x = FST y /\ (P (FST x) ==> R (SND x) (SND y))) xs
     ys ==>
   ALOOKUP_rel P R xs ys`,
  CHEAT_TAC);;

let env_set_v_noop = prove
 (`flatSem_environment_v_fupd (K (flatSem_environment_v env))
     an_env = env`,
  CHEAT_TAC);;

let pat_bindings_evaluate_FOLDR_lemma = prove
 (`!h xs.
   (!x. MEM x xs ==> IS_SOME (f x)) /\
   (!x. IMAGE (THE o f) (set_of_list xs) SUBSET new_names) /\
   (!x. MEM x xs ==> (!env2.
     ALOOKUP_rel (\x. ~(x IN new_names)) (=) (flatSem_environment_v
       env2) (flatSem_environment_v env) ==>
     flatSem_evaluate env2 s [g x] = (s,Rval [h x]))) ==>
   (!env2.
   ALOOKUP_rel (\x. ~(x IN new_names)) (=) (flatSem_environment_v
     env2) (flatSem_environment_v env) ==>
   flatSem_evaluate env2 s
     [ITLIST (\x exp. flatLang_Let t (f x) (g x) exp) xs exp] =
   flatSem_evaluate (flatSem_environment_v_fupd (K (APPEND (MAP (\x.
     (THE (f x),h x)) (REVERSE xs)) (flatSem_environment_v env2))) env2)
         s [exp])`,
  CHEAT_TAC);;

(* HOL4 flat_patternProofScript.sml:382-401: code that the source has
   in a comment *)

let EVERY_MAPi_simple = prove
 (`(!i j x. P (f i x) = P (f j x)) ==>
   ALL P (MAPi f xs) = ALL P (MAP (f 0) xs)`,
  CHEAT_TAC);;

(* HOL4 flat_patternProofScript.sml:411-412: the ML values that the
   definitions below antiquote *)

(* a note on 'naming' below. the existing (encoded) names in the program
   (in the original x and exp)
   are < j for starting val j. during the recursion, j increases to i, with
   new names i < nm < j appearing in the new env, and in *expressions* in
   n_bindings. note *names* in n_bindings/pre_bindings come from the original
   program. also new/old names mix in env, thus the many filters. *)

let compile_pat_bindings_simulation = prove
 (`!t i n_bindings exp exp2 spt s vs pre_bindings bindings env s2 res
  vset.
   compile_pat_bindings t i n_bindings exp = (spt,exp2) /\
   flatSem_pmatch_list s (MAP FST n_bindings) vs pre_bindings = Match
     bindings /\
   flatSem_evaluate env s [exp2] = (s2,res) /\
   ALL2 (\(_1,k,v_exp) v. !env2.
         k IN domain spt /\
         ALOOKUP_rel ((\k. k > j /\ k < i) o dec_name_to_num) (=)
           (flatSem_environment_v env2) (flatSem_environment_v env) ==>
         pure_eval_to s env2 v_exp v)
     n_bindings vs /\
   ALL ((\k. k < j) o dec_name_to_num o FST) pre_bindings /\
   j < i /\
   ALOOKUP_rel ((\k. k < j) o dec_name_to_num) (=)
     (flatSem_environment_v env)
     (APPEND pre_bindings base_vs) /\
   ALL (\(p,k,_2). ALL (\nm. dec_name_to_num nm < j)
     (flatLang_pat_bindings p) /\
         j < k /\ k < i) n_bindings ==>
   (?env2. flatSem_evaluate env2 s [exp] = (s2,res) /\
   ALOOKUP_rel ((\k. k < j) o dec_name_to_num) (=)
     (flatSem_environment_v env2) (APPEND bindings base_vs))`,
  CHEAT_TAC);;

(* HOL4 flat_patternProofScript.sml:651-653: the ML values that the
   definitions below antiquote *)
(* on the right side of the state relation, the pattern compiler's config is
   also needed in the compiler state *)
(* HOL4 flat_patternProofScript.sml:656: the ML values that the
   definitions below antiquote *)

(* HOL4 flat_patternProofScript.sml:658: ML code, not ported *)

let flat_patternProof_v_rel = cake_inductive
  `(!v v'. simple_basic_val_rel v v' /\
     ALL2 flat_patternProof_v_rel (v_container_xs v) (v_container_xs
       v') ==>
     flat_patternProof_v_rel v v') /\
   (!N env1 n x env2 cfg.
      flat_patternProof_env_rel N env1 env2 /\
      FST (flat_pattern_compile_exp cfg x) < N ==>
      flat_patternProof_v_rel (flatSem_Closure env1 n x)
        (flatSem_Closure env2 n (SND (SND (flat_pattern_compile_exp
          cfg x))))) /\
   (!N env1 fs x env2 cfg.
      flat_patternProof_env_rel N env1 env2 /\
      ALL (\(n,m,e). FST (flat_pattern_compile_exp cfg e) < N) fs ==>
      flat_patternProof_v_rel (flatSem_Recclosure env1 fs x)
        (flatSem_Recclosure env2
          (MAP (\(n,m,e). (n,m,SND (SND (flat_pattern_compile_exp cfg
            e)))) fs) x)) /\
   (!N env1 env2.
      ALOOKUP_rel (\x. dec_name_to_num x < N) flat_patternProof_v_rel
        (flatSem_environment_v env1) (flatSem_environment_v env2) ==>
      flat_patternProof_env_rel N env1 env2)`;;

(* HOL4 flat_patternProofScript.sml:680-686: a theorem that HOL4
   states as the value of an ML expression: v_rel_l_cases *)

(* HOL4 flat_patternProofScript.sml:688-689: the ML values that the
   definitions below antiquote *)

let install_conf_rel_def = new_definition
  `install_conf_rel pat_cfg ic1 ic2 <=>
     (install_config_compile_oracle ic2 =
         pure_co (MAP (compile_dec pat_cfg)) o
           install_config_compile_oracle ic1) /\
     (install_config_compile ic1 = pure_cc (MAP (compile_dec
       pat_cfg)) (install_config_compile ic2))`;;

let flat_patternProof_state_rel_def = new_definition
  `flat_patternProof_state_rel cfg (s:('c,'ffi)flatSem_state)
  (t:('c,'ffi)flatSem_state) <=> flatSem_state_clock
     t = flatSem_state_clock s /\
     ALL2 (semanticPrimitivesProps_sv_rel flat_patternProof_v_rel)
       (flatSem_state_refs s) (flatSem_state_refs t) /\
       flatSem_state_ffi
     t = flatSem_state_ffi s /\
     ALL2 (OPTREL flat_patternProof_v_rel) (flatSem_state_globals s)
       (flatSem_state_globals t) /\
     install_conf_rel cfg (flatSem_state_eval_config s)
       (flatSem_state_eval_config t)`;;

(* state_rel_initial_state *)
let flat_patternProof_state_rel_initial_state = prove
 (`install_conf_rel cfg ic1 ic2 ==>
   flat_patternProof_state_rel cfg (flatSem_initial_state ffi k ic1)
     (flatSem_initial_state ffi k ic2)`,
  CHEAT_TAC);;

(* state_rel_IMP_clock[local] *)
let flat_patternProof_state_rel_IMP_clock = prove
 (`flat_patternProof_state_rel cfg s t ==> state_clock t = state_clock
  s`,
  CHEAT_TAC);;

(* HOL4 flat_patternProofScript.sml:722-723: the overload nv_rel,
   which the port expands *)

let match_rel_def = new_definition
  `match_rel N x2 x3 =
        match (x2,x3) with
          (Match env1,Match env2) -> (\N. ALOOKUP_rel (\x.
            dec_name_to_num x < N) flat_patternProof_v_rel) N env1 env2
        | (No_match,No_match) -> T
        | (Match_type_error,Match_type_error) -> T
        | (_3,_4) -> F`;;

let match_rel_thms = prove
 (`(match_rel N Match_type_error e <=> e = Match_type_error) /\
   (match_rel N e Match_type_error <=> e = Match_type_error) /\
   (match_rel N No_match e <=> e = No_match) /\
   (match_rel N e No_match <=> e = No_match)`,
  CHEAT_TAC);;
add_simp match_rel_thms;;

let match_rel_IMP = prove
 (`match_rel N e e' ==>
     (e = No_match /\ e = e') \/
     (e = Match_type_error /\ e = e') \/ (?env1 env2. e = Match
       env1 /\ e' = Match env2 /\ (\N. ALOOKUP_rel (\x.
       dec_name_to_num x < N) flat_patternProof_v_rel) N env1 env2)`,
  CHEAT_TAC);;

let MAX_ADD_LESS = prove
 (`(MAX i j + k < l) = (i + k < l /\ j + k < l)`,
  CHEAT_TAC);;

let LESS_MAX_ADD = prove
 (`(l < MAX i j + k) = (l < i + k \/ l < j + k)`,
  CHEAT_TAC);;

let MAX_ADD_LE = prove
 (`(MAX i j + k <= l) = (i + k <= l /\ j + k <= l)`,
  CHEAT_TAC);;

(* env_rel_mono *)
let flat_patternProof_env_rel_mono = prove
 (`flat_patternProof_env_rel i env1 env2 /\ j <= i ==>
   flat_patternProof_env_rel j env1 env2`,
  CHEAT_TAC);;

let env_rel_ALOOKUP = prove
 (`flat_patternProof_env_rel N env1 env2 /\ dec_name_to_num n < N ==>
   OPTREL flat_patternProof_v_rel (ALOOKUP (flatSem_environment_v
     env1) n) (ALOOKUP (flatSem_environment_v env2) n)`,
  CHEAT_TAC);;

let ALOOKUP_MAP_3 = prove
 (`(!x. MEM x xs ==> FST (f x) = FST x) ==>
   ALOOKUP (MAP f xs) x = OPTION_MAP (\y. SND (f (x,y))) (ALOOKUP
     xs x)`,
  CHEAT_TAC);;

let ALOOKUP_rel_MAP_same = prove
 (`(!x. MEM x xs ==> FST (f x) = FST (g x) /\
     (P (FST (g x)) ==> R (SND (f x)) (SND (g x)))) ==>
   ALOOKUP_rel P R (MAP f xs) (MAP g xs)`,
  CHEAT_TAC);;

let do_opapp_thm = prove
 (`flatSem_do_opapp vs1 = SOME (env1,exp) /\ ALL2
  flat_patternProof_v_rel vs1 vs2 ==>
   (?i sg exp' env2 cfg. flat_pattern_compile_exp cfg exp =
     (i,sg,exp') /\
   flat_patternProof_env_rel (i + 1) env1 env2 /\ flatSem_do_opapp
     vs2 = SOME (env2,exp'))`,
  CHEAT_TAC);;

let do_opapp_thm_REVERSE = prove
 (`flatSem_do_opapp (REVERSE vs1) = SOME (env1,exp) /\ ALL2
  flat_patternProof_v_rel vs1 vs2 ==>
   (?i sg exp' env2 cfg.
   flat_pattern_compile_exp cfg exp = (i,sg,exp') /\
   flat_patternProof_env_rel (i + 1) env1 env2 /\
   flatSem_do_opapp (REVERSE vs2) = SOME (env2,exp'))`,
  CHEAT_TAC);;

let pmatch_thm = prove
 (`(!(s:('c,'ffi)flatSem_state) p v vs r s1 v1 vs1.
     flatSem_pmatch s p v vs = r /\ ~(r = Match_type_error) /\
     flat_patternProof_state_rel cfg s s1 /\
     flat_patternProof_v_rel v v1 /\
     (\N. ALOOKUP_rel (\x. dec_name_to_num x < N)
       flat_patternProof_v_rel) N vs vs1 ==> (?r1. flatSem_pmatch s1 p
       v1 vs1 = r1 /\ match_rel N r r1)) /\
   (!(s:('c,'ffi)flatSem_state) ps v vs r s1 v1 vs1.
     flatSem_pmatch_list s ps v vs = r /\ ~(r = Match_type_error) /\
     flat_patternProof_state_rel cfg s s1 /\
     ALL2 flat_patternProof_v_rel v v1 /\
     (\N. ALOOKUP_rel (\x. dec_name_to_num x < N)
       flat_patternProof_v_rel) N vs vs1 ==> (?r1. flatSem_pmatch_list
       s1 ps v1 vs1 = r1 /\ match_rel N r r1))`,
  CHEAT_TAC);;

let simple_val_rel_step_isClosure = prove
 (`simple_basic_val_rel x y ==> ~(isClosure x) /\ ~(isClosure y)`,
  CHEAT_TAC);;

(* simple_val_rel *)
let flat_patternProof_simple_val_rel = prove
 (`flatProps_simple_val_rel flat_patternProof_v_rel`,
  CHEAT_TAC);;

(* simple_state_rel *)
let flat_patternProof_simple_state_rel = prove
 (`flatProps_simple_state_rel flat_patternProof_v_rel
  (flat_patternProof_state_rel cfg)`,
  CHEAT_TAC);;

(* HOL4 flat_patternProofScript.sml:929-930: a theorem that HOL4
   states as the value of an ML expression: do_app_thm *)

let do_app_thm_REVERSE = prove
 (`flatSem_do_app s1 op (REVERSE vs1) = SOME (t1,r1) /\
   flat_patternProof_state_rel cfg s1 s2 /\ ALL2
     flat_patternProof_v_rel vs1 vs2 ==>
   (?t2 r2. semanticPrimitivesProps_result_rel
     flat_patternProof_v_rel flat_patternProof_v_rel r1 r2 /\
   flat_patternProof_state_rel cfg t1 t2 /\ flatSem_do_app s2 op
     (REVERSE vs2) = SOME (t2,r2))`,
  CHEAT_TAC);;

let do_if_helper = prove
 (`flatSem_do_if b x y = SOME e /\ flat_patternProof_v_rel b b' ==>
   ((b' = flatSem_Boolv T) = (b = flatSem_Boolv T)) /\ ((b' =
     flatSem_Boolv F) = (b = flatSem_Boolv F))`,
  CHEAT_TAC);;

let MAX_LIST_LESS_EVERY = prove
 (`(MAX_LIST xs < N) = (0 < N /\ ALL (\x. x < N) xs)`,
  CHEAT_TAC);;

let max_dec_name_LESS_EVERY = prove
 (`(max_dec_name ns < N) = (0 < N /\ ALL (\n. dec_name_to_num n < N)
  ns)`,
  CHEAT_TAC);;

(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 flat_patternProofScript.sml:974-978: the tactic that proves
   the termination *)
let encode_val_def,encode_val_ind = define_wf
  `MEASURE flatSem_v_size`
  [`encode_val others =
      match others with
        (flatSem_Litv l:flatSem_v) -> flatSem_Litv l
      | (flatSem_Conv stmp xs) -> pattern_semantics_Term
     (match stmp with NONE -> NONE | SOME (i,_5) -> SOME i)
     (MAP encode_val xs)
      | (flatSem_Loc _6 n) -> pattern_semantics_RefPtr n
      | others -> pattern_semantics_Other`];;

let decode_test_simulation = prove
 (`dt_test test enc_v = SOME b /\
   pure_eval_to s env x v /\
   enc_v = encode_val v ==>
   pure_eval_to s env (flat_pattern_decode_test tr test x)
     (flatSem_Boolv b)`,
  CHEAT_TAC);;

let app_pos_Term_IMP = prove
 (`!xs n. app_pos refs (Pos n pos) (pattern_semantics_Term c xs) = SOME
  y ==>
   n < LENGTH xs /\ app_pos refs pos (EL n xs) = SOME y`,
  CHEAT_TAC);;

let encode_refs_def = new_definition
  `encode_refs s = FUN_FMAP (\i. encode_val (match EL i (state_refs s)
  with semanticPrimitives_Refv v -> v))
     (count (LENGTH (state_refs s)) INTER {i | ?v. EL i
       (state_refs s) = semanticPrimitives_Refv v})`;;

let FLOOKUP_encode_refs = prove
 (`FLOOKUP (encode_refs s) n = (if n < LENGTH (state_refs s) then
  (match EL n (state_refs s) with semanticPrimitives_Refv v -> SOME
  (encode_val v) | _7 -> NONE) else NONE)`,
  CHEAT_TAC);;

let decode_pos_simulation = prove
 (`!pos exp x.
   app_pos (encode_refs s) pos (encode_val x) = SOME enc_y /\
   pure_eval_to s env exp x ==>
   (?y. enc_y = encode_val y /\
   pure_eval_to s env (decode_pos tr exp pos) y)`,
  CHEAT_TAC);;

(* HOL4 flat_patternProofScript.sml:1052-1054: a theorem that HOL4
   states as the value of an ML expression: fold_Boolv *)

(* do_eq_Boolv *)
let flat_patternProof_do_eq_Boolv = prove
 (`flatSem_do_eq (flatSem_Boolv x) (flatSem_Boolv y) = Eq_val (x = y)`,
  CHEAT_TAC);;

let do_if_Boolv = prove
 (`flatSem_do_if (flatSem_Boolv x) y z = SOME (if x then y else z)`,
  CHEAT_TAC);;

(* evaluate_Bool *)
let flat_patternProof_evaluate_Bool = prove
 (`flatSem_evaluate env s [flatLang_Bool t b] = (s,Rval [flatSem_Boolv
  b])`,
  CHEAT_TAC);;

let SmartIf_thm = prove
 (`SmartIf t e p q =
     (if ?t. e = flatLang_Bool t T then p else
     if ?t. e = flatLang_Bool t F then q else
     flatLang_If t e p q)`,
  CHEAT_TAC);;

let evaluate_SmartIf = prove
 (`flatSem_evaluate env s [SmartIf t x y z] = flatSem_evaluate env s
  [flatLang_If t x y z]`,
  CHEAT_TAC);;

let decode_guard_simulation = prove
 (`!b.
   dt_eval_guard (encode_refs s) (encode_val y) gd = SOME b /\
   pure_eval_to s env x y ==>
   pure_eval_to s env (decode_guard tr x gd) (flatSem_Boolv b)`,
  CHEAT_TAC);;

let simp_guard_thm = prove
 (`!gd x. dt_eval_guard r v gd = SOME x ==>
   dt_eval_guard r v (simp_guard gd) = SOME x`,
  CHEAT_TAC);;

let decode_dtree_simulation = prove
 (`dt_eval (encode_refs s) (encode_val y) dtree = SOME v /\
   pure_eval_to s env x y ==>
   flatSem_evaluate env s [decode_dtree tr exps x default_x dtree] =
   flatSem_evaluate env s [match v with MatchSuccess i -> (match
     sptree_lookup i exps with
     SOME exp -> exp | NONE -> default_x) | _8 -> default_x]`,
  CHEAT_TAC);;

let encode_pat_match_simulation = prove
 (`(!(s:('c,'ffi)flatSem_state) pat v pre_bindings res.
   flatSem_pmatch s pat v pre_bindings = res /\ ~(res =
     Match_type_error) ==>
   pattern_semantics_pmatch (encode_refs s) (encode_pat pat)
     (encode_val v) =
   (if res = No_match then PMatchFailure else PMatchSuccess)) /\
   (!(s:('c,'ffi)flatSem_state) ps vs pre_bindings res.
   flatSem_pmatch_list s ps vs pre_bindings = res /\ ~(res =
     Match_type_error) ==>
   pattern_semantics_pmatch_list (encode_refs s) (MAP encode_pat ps)
     (MAP encode_val vs) =
   (if res = No_match then PMatchFailure else PMatchSuccess))`,
  CHEAT_TAC);;

let pmatch_rows_encode = prove
 (`!pats j_offs.
   ~(pmatch_rows pats s v = Match_type_error) ==>
   (match (pattern_semantics_match (encode_refs s)
     (MAPi (\j (p,_10). (encode_pat p,j + j_offs)) pats)
         (encode_val v)) with NONE -> F | SOME (MatchSuccess n) ->
           (?i env. n = i + j_offs /\ i < LENGTH pats /\
         flatSem_pmatch s (FST (EL i pats)) v [] = Match env /\
         pmatch_rows pats s v = Match (env,EL i pats)) | _9 ->
           pmatch_rows pats s v = No_match)`,
  CHEAT_TAC);;

let naive_pattern_match_correct = prove
 (`!t mats vs bindings exp res.
    ALL2 (pure_eval_to s env) (MAP SND mats) vs /\
    flatSem_pmatch_list s (MAP FST mats) vs bindings = res /\ ~(res =
      Match_type_error) /\
    naive_pattern_match t mats = exp ==>
    pure_eval_to s env exp (flatSem_Boolv (~(res = No_match)))`,
  CHEAT_TAC);;

(* HOL4 flat_patternProofScript.sml:1308-1312: a theorem that HOL4
   states as the value of an ML expression:
   naive_pattern_match_correct_inst *)

let naive_pattern_matches_correct = prove
 (`!t x mats dflt exp v res.
   naive_pattern_matches t x mats dflt = exp /\
   pure_eval_to s env x v /\
   pmatch_rows mats s v = res /\ ~(res = Match_type_error) ==>
   flatSem_evaluate env s [exp] = (match res with Match (_11,_12,exp)
     ->
       flatSem_evaluate env s [exp] | _13 -> flatSem_evaluate env s
         [dflt])`,
  CHEAT_TAC);;

let pmatch_rows_same_FST = prove
 (`!pats pats2. MAP FST pats = MAP FST pats2 ==>
   (match pmatch_rows pats s v with Match_type_error -> pmatch_rows
     pats2 s v = Match_type_error | No_match -> pmatch_rows pats2 s v =
     No_match | Match (env,p,e) -> (?i. i < LENGTH pats2 /\ EL i pats =
     (p,e) /\
         pmatch_rows pats2 s v = Match (env,EL i pats2)))`,
  CHEAT_TAC);;

(* HOL4 flat_patternProofScript.sml:1358-1360: a theorem that HOL4
   states as the value of an ML expression: comp_thm *)

let evaluate_compile_pats = prove
 (`~(pmatch_rows pats s v = Match_type_error) /\
   pure_eval_to s env exp v ==>
   flatSem_evaluate env s [compile_pats cfg naive t N exp default_x
     pats] =
   flatSem_evaluate env s [match pmatch_rows pats s v with Match
     (env',p',e') -> compile_pat_rhs t N exp (p',e') | _14 ->
     default_x]`,
  CHEAT_TAC);;

let compile_match_pmatch_rows = prove
 (`!pats k sg pats2 res.
   compile_match cfg pats = (k,sg,pats2) /\
   flat_patternProof_state_rel s_cfg s t /\
   flat_patternProof_v_rel v v' /\
   k <= N /\
   pmatch_rows pats s v = res ==>
   (match res with Match_type_error -> T | No_match -> pmatch_rows
     pats2 t v' = No_match | Match (env,p,e) -> (?i env'. i < LENGTH
     pats /\ i < LENGTH pats2 /\
         (p,e) = EL i pats /\ (\N. ALOOKUP_rel (\x. dec_name_to_num x
           < N) flat_patternProof_v_rel) N env env' /\
         pmatch_rows pats2 t v' = Match (env',EL i pats2)))`,
  CHEAT_TAC);;

let compile_match_EL = prove
 (`!pats pats2 k sg i.
   compile_match cfg pats = (k,sg,pats2) /\
   i < LENGTH pats /\
   EL i pats = (pat,exp) ==>
   (?exp_i sg exp'.
   flat_pattern_compile_exp cfg exp = (exp_i,sg,exp') /\
   EL i pats2 = (pat,exp') /\
   exp_i <= k /\ max_dec_name (flatLang_pat_bindings pat) <= k)`,
  CHEAT_TAC);;

let evaluate_compile_pat_rhs = prove
 (`flatSem_evaluate (flatSem_environment_v_fupd f env3) s
     [compile_pat_rhs tr N (flatLang_Var_local tr (enc_num_to_name
       N))
     (p,exp)] = (t,res) /\
   flatSem_pmatch s p v [] = Match bindings /\
   flat_patternProof_env_rel M env1 env2 /\
   (\N. ALOOKUP_rel (\x. dec_name_to_num x < N)
     flat_patternProof_v_rel) M l_bindings bindings /\
   f (flatSem_environment_v env3) = CONS (enc_num_to_name N,v)
     (flatSem_environment_v env2) /\
   N <= M /\
   max_dec_name (flatLang_pat_bindings p) < N - 1 ==>
   (?ext_env.
   flatSem_evaluate ext_env s [exp] = (t,res) /\
   flat_patternProof_env_rel (N - 1) (flatSem_environment_v_fupd (K
     (APPEND l_bindings (flatSem_environment_v env1))) env1) ext_env)`,
  CHEAT_TAC);;

(* state_rel_dec_clock *)
let flat_patternProof_state_rel_dec_clock = prove
 (`flat_patternProof_state_rel cfg s1 s2 ==>
  flat_patternProof_state_rel cfg (flatSem_dec_clock s1)
  (flatSem_dec_clock s2)`,
  CHEAT_TAC);;

let OPTION_ALL_FORALL = prove
 (`OPTION_ALL P x = (!y. x = SOME y ==> P y)`,
  CHEAT_TAC);;

let do_eval_thm = prove
 (`flatSem_do_eval xs (flatSem_state_eval_config s) = SOME
  (decs,eval_config,rv) /\
   flat_patternProof_state_rel cfg s t /\
   ALL2 flat_patternProof_v_rel xs ys ==>
   (?rv' decs' eval_config'.
   flatSem_do_eval ys (flatSem_state_eval_config t) = SOME
     (decs',eval_config',rv') /\
   flat_patternProof_state_rel cfg (flatSem_state_eval_config_fupd (K
     eval_config) s)
     (flatSem_state_eval_config_fupd (K eval_config') t) /\
   flat_patternProof_v_rel rv rv' /\
   decs' = MAP (compile_dec cfg) decs)`,
  CHEAT_TAC);;

(* evaluate_decs_sing *)
let flat_patternProof_evaluate_decs_sing = prove
 (`flatSem_evaluate_decs s [d] = evaluate_dec s d`,
  CHEAT_TAC);;

(* HOL4 flat_patternProofScript.sml:1541: ML code, not ported *)

let compile_exps_evaluate = prove
 (`(!env1 ((s1:('c,'ffi)flatSem_state)) xs t1 r1 i sg ys N env2 s2 cfg.
     flatSem_evaluate env1 s1 xs = (t1,r1) /\
     flat_pattern_compile_exps cfg xs = (i,sg,ys) /\
     flat_patternProof_env_rel N env1 env2 /\
       flat_patternProof_state_rel s_cfg s1 s2 /\ i < N /\ ~(r1 = Rerr
       (Rabort Rtype_error)) ==>
     (?t2 r2.
       semanticPrimitivesProps_result_rel (ALL2
         flat_patternProof_v_rel) flat_patternProof_v_rel r1 r2 /\
       flat_patternProof_state_rel s_cfg t1 t2 /\
       flatSem_evaluate env2 s2 ys = (t2,r2))) /\
   (!((s1:('c,'ffi)flatSem_state)) decs s2 t1 cfg decs' res.
     flatSem_evaluate_decs s1 decs = (t1,res) /\
     decs' = MAP (compile_dec cfg) decs /\
     flat_patternProof_state_rel s_cfg s1 s2 /\ ~(res = SOME (Rabort
       Rtype_error)) ==>
     (?t2 res'.
       flatSem_evaluate_decs s2 decs' = (t2,res') /\
       OPTREL (exc_rel flat_patternProof_v_rel) res res' /\
       flat_patternProof_state_rel s_cfg t1 t2))`,
  CHEAT_TAC);;

let compile_decs_eval_sim = prove
 (`install_conf_rel cfg ic1 ic2 ==>
   flatProps_eval_sim ffi prog prog' ic1 ic2
     (\decs decs'. MAP (compile_dec cfg2) decs = decs') F`,
  CHEAT_TAC);;

let compile_decs_semantics = prove
 (`install_conf_rel cfg ic1 ic2 /\ ~(flatSem_semantics ic1 ffi prog =
  pattern_semantics_Fail) ==>
   flatSem_semantics ic1 ffi prog =
   flatSem_semantics ic2 ffi (MAP (compile_dec cfg1) prog)`,
  CHEAT_TAC);;

(* set_globals and esgc properties *)

let set_globals_decode_pos = prove
 (`!p exp. flatProps_set_globals exp = EMPTY_BAG ==>
   flatProps_set_globals (decode_pos t exp p) = EMPTY_BAG`,
  CHEAT_TAC);;

let set_globals_decode_test = prove
 (`flatProps_set_globals exp = EMPTY_BAG ==>
   flatProps_set_globals (flat_pattern_decode_test t d exp) =
     EMPTY_BAG`,
  CHEAT_TAC);;

let set_globals_decode_guard = prove
 (`flatProps_set_globals exp = EMPTY_BAG ==>
   flatProps_set_globals (decode_guard t exp gd) = EMPTY_BAG`,
  CHEAT_TAC);;

let set_globals_decode_dtree_empty = prove
 (`flatProps_set_globals x = EMPTY_BAG /\ flatProps_set_globals dflt =
  EMPTY_BAG /\
   ALL (\y. flatProps_set_globals y = EMPTY_BAG) (toList br_spt) ==>
   flatProps_set_globals (decode_dtree t br_spt x dflt dtree) =
     EMPTY_BAG`,
  CHEAT_TAC);;

let inv_on_FOLDR = prove
 (`!f. (!x v. MEM x xs ==> f (g x v) = f v) ==>
   f (ITLIST g xs v) = f v`,
  CHEAT_TAC);;

let set_globals_compile_pat_bindings = prove
 (`!t i n_bindings exp.
   ALL (\(_15,_16,v_exp). flatProps_set_globals v_exp = EMPTY_BAG)
     n_bindings ==>
   flatProps_set_globals (SND (compile_pat_bindings t i n_bindings
     exp)) =
   flatProps_set_globals exp`,
  CHEAT_TAC);;

let set_globals_naive_pattern_match = prove
 (`!t xs. ALL (\v. flatProps_set_globals (SND v) = EMPTY_BAG) xs ==>
   flatProps_set_globals (naive_pattern_match t xs) = EMPTY_BAG`,
  CHEAT_TAC);;

let set_globals_naive_pattern_matches = prove
 (`flatProps_set_globals x = EMPTY_BAG ==>
   (flatProps_set_globals (naive_pattern_matches t x ps dflt)) <=
   (flatProps_elist_globals (CONS dflt (MAP SND ps)))`,
  CHEAT_TAC);;

let set_toList_fromList = prove
 (`set_of_list (toList (fromList xs)) = set_of_list xs`,
  CHEAT_TAC);;

let set_globals_compile_pats = prove
 (`(~naive ==> flatProps_elist_globals (CONS dflt (MAP SND ps)) =
  EMPTY_BAG) /\
   flatProps_set_globals x = EMPTY_BAG ==>
   flatProps_set_globals (compile_pats cfg naive t N x dflt ps) <=
   flatProps_elist_globals (CONS dflt (MAP SND ps))`,
  CHEAT_TAC);;

let SUB_BAG_2 = prove
 (`x <= y /\ x' <= y' ==> (BAG_UNION) x x' <= (BAG_UNION) y y'`,
  CHEAT_TAC);;

let compile_exp_set_globals = prove
 (`(!cfg exp N sg exp'.
   flat_pattern_compile_exp cfg exp = (N,sg,exp') ==>
   flatProps_set_globals exp' <= flatProps_set_globals exp) /\
   (!cfg exps N sg exps'.
   flat_pattern_compile_exps cfg exps = (N,sg,exps') ==>
   flatProps_elist_globals exps' <= flatProps_elist_globals exps) /\
   (!cfg m N sg m'.
   compile_match cfg m = (N,sg,m') ==>
   flatProps_elist_globals (MAP SND m') <= flatProps_elist_globals
     (MAP SND m))`,
  CHEAT_TAC);;

(* FST_SND_EQ_CASE *)
let flat_patternProof_FST_SND_EQ_CASE = prove
 (`FST = (\(a,b). a) /\ SND = (\(a,b). b)`,
  CHEAT_TAC);;

let compile_decs_elist_globals = prove
 (`!decs.
   flatProps_elist_globals (MAP (compile_dec cfg) decs) <=
   flatProps_elist_globals decs`,
  CHEAT_TAC);;

let esgc_free_decode_pos = prove
 (`!p exp. flatProps_esgc_free exp ==>
   flatProps_esgc_free (decode_pos t exp p)`,
  CHEAT_TAC);;

let esgc_free_decode_test = prove
 (`flatProps_esgc_free exp ==> flatProps_esgc_free
  (flat_pattern_decode_test t d exp)`,
  CHEAT_TAC);;

let esgc_free_decode_guard = prove
 (`flatProps_esgc_free exp ==> flatProps_esgc_free (decode_guard t exp
  gd)`,
  CHEAT_TAC);;

let esgc_free_decode_dtree = prove
 (`flatProps_esgc_free v_exp /\ flatProps_esgc_free dflt /\
   ALL (\y. flatProps_esgc_free y) (toList br_spt) ==>
   flatProps_esgc_free (decode_dtree t br_spt v_exp dflt dtree)`,
  CHEAT_TAC);;

let esgc_free_compile_pat_bindings = prove
 (`!t i n_bindings exp.
   flatProps_esgc_free exp /\
   ALL (\(_17,_18,v_exp). flatProps_esgc_free v_exp) n_bindings ==>
   flatProps_esgc_free (SND (compile_pat_bindings t i n_bindings
     exp))`,
  CHEAT_TAC);;

let esgc_free_naive_pattern_match = prove
 (`!t xs. ALL flatProps_esgc_free (MAP SND xs) ==>
   flatProps_esgc_free (naive_pattern_match t xs)`,
  CHEAT_TAC);;

let esgc_free_naive_pattern_matches = prove
 (`!t x xs dflt. ALL flatProps_esgc_free (CONS x (CONS dflt (MAP SND
  xs))) ==>
   flatProps_esgc_free (naive_pattern_matches t x xs dflt)`,
  CHEAT_TAC);;

let esgc_free_compile_pats = prove
 (`flatProps_esgc_free dflt /\ ALL flatProps_esgc_free (MAP SND ps) ==>
   flatProps_esgc_free (compile_pats cfg naive t N
     (flatLang_Var_local t' nm) dflt ps)`,
  CHEAT_TAC);;

let compile_exp_esgc_free = prove
 (`(!cfg exp N sg exp'.
   flat_pattern_compile_exp cfg exp = (N,sg,exp') /\
   flatProps_esgc_free exp ==>
   flatProps_esgc_free exp') /\
   (!cfg exps N sg exps'.
   flat_pattern_compile_exps cfg exps = (N,sg,exps') /\
   ALL flatProps_esgc_free exps ==>
   ALL flatProps_esgc_free exps') /\
   (!cfg m N sg m'.
   compile_match cfg m = (N,sg,m') /\
   ALL (flatProps_esgc_free o SND) m ==>
   ALL (flatProps_esgc_free o SND) m')`,
  CHEAT_TAC);;

(* compile_decs_esgc_free *)
let flat_patternProof_compile_decs_esgc_free = prove
 (`!decs.
   ALL flatProps_esgc_free decs ==>
   ALL flatProps_esgc_free (MAP (compile_dec cfg) decs)`,
  CHEAT_TAC);;

let naive_pattern_match_no_Mat = prove
 (`!t xs. ALL (no_Mat o SND) xs ==>
   no_Mat (naive_pattern_match t xs)`,
  CHEAT_TAC);;

let naive_pattern_matches_no_Mat = prove
 (`!t x xs dflt. ALL no_Mat (CONS x (CONS dflt (MAP SND xs))) ==>
   no_Mat (naive_pattern_matches t x xs dflt)`,
  CHEAT_TAC);;

let compile_pat_bindings_no_Mat = prove
 (`!t i n_bindings exp.
   no_Mat exp /\
   ALL (\(_19,_20,v_exp). no_Mat v_exp) n_bindings ==>
   no_Mat (SND (compile_pat_bindings t i n_bindings exp))`,
  CHEAT_TAC);;

let decode_pos_no_Mat = prove
 (`!p exp. no_Mat exp ==>
   no_Mat (decode_pos t exp p)`,
  CHEAT_TAC);;

let decode_test_no_Mat = prove
 (`no_Mat exp ==> no_Mat (flat_pattern_decode_test t d exp)`,
  CHEAT_TAC);;

let decode_guard_no_Mat = prove
 (`no_Mat exp ==> no_Mat (decode_guard t exp gd)`,
  CHEAT_TAC);;

let decode_dtree_no_Mat = prove
 (`no_Mat v_exp /\ no_Mat dflt /\
   ALL no_Mat (toList br_spt) ==>
   no_Mat (decode_dtree t br_spt v_exp dflt dtree)`,
  CHEAT_TAC);;

let compile_pats_no_Mat = prove
 (`no_Mat dflt /\ no_Mat x /\ ALL no_Mat (MAP SND ps) ==>
   no_Mat (compile_pats cfg naive t N x dflt ps)`,
  CHEAT_TAC);;

let compile_exp_no_Mat = prove
 (`(!cfg exp N sg exp'.
   flat_pattern_compile_exp cfg exp = (N,sg,exp') ==>
   no_Mat exp') /\
   (!cfg exps N sg exps'.
   flat_pattern_compile_exps cfg exps = (N,sg,exps') ==>
   ALL no_Mat exps') /\
   (!cfg pats N sg pats'.
   compile_match cfg pats = (N,sg,pats') ==>
   ALL no_Mat (MAP SND pats'))`,
  CHEAT_TAC);;

let compile_decs_no_Mat = prove
 (`!decs. no_Mat_decs (MAP (compile_dec cfg) decs)`,
  CHEAT_TAC);;
