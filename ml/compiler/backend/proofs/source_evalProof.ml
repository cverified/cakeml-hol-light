(* ======================================================== *)
(*  source_evalProof: ported from HOL4's
    compiler/backend/proofs/source_evalProofScript.sml
    A proof theory, with 27 definitions, 1 datatype and 94 theorems.
    Needed by backendProof.ml, source_letProof.ml,
    source_to_flatProof.ml and source_to_sourceProof.ml.  *)
(* ======================================================== *)

(*
  Proofs that the eval mode of the source semantics can
  be switched to one that includes an oracle.
*)

needs "compiler/backend/flat_to_clos.ml";;
needs "lib/peg.ml";;
needs "semantics/ast.ml";;
needs "semantics/evaluate.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/namespace.ml";;
needs "semantics/proofs/evaluateProps.ml";;
needs "semantics/proofs/namespaceProps.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "semantics/semantics.ml";;

let _ = do_list hide_constant ["compile_decs"; "id"];;

(* this file reads the name of a record field as a variable and
   needs the accessors of that field as well, so only these
   pairs come out of the interface *)
let _ = hide_overloads
  ["compile","backend_compile";
   "compile","bvi_let_compile";
   "compile","bvi_to_data_compile";
   "compile","bvl_const_compile";
   "compile","bvl_handle_compile";
   "compile","bvl_to_bvi_compile";
   "compile","clos_annotate_compile";
   "compile","clos_call_compile";
   "compile","clos_fvs_compile";
   "compile","clos_known_compile";
   "compile","clos_mti_compile";
   "compile","clos_to_bvl_compile";
   "compile","compiler_compile";
   "compile","data_live_compile";
   "compile","data_space_compile";
   "compile","data_to_word_compile";
   "compile","flat_to_clos_compile";
   "compile","lab_to_target_compile";
   "compile","source_to_flat_compile";
   "compile","source_to_source_compile";
   "compile","stack_alloc_compile";
   "compile","stack_names_compile";
   "compile","stack_rawcall_compile";
   "compile","stack_remove_compile";
   "compile","stack_to_lab_compile";
   "compile","word_bignum_compile";
   "compile","word_to_stack_compile";
   "compile","word_to_word_compile";
   "init_state","init_state"];;
(* HOL4 ancestors outside the port: string *)

(* The things the translator is expected to produce from the
   compiler definition etc. *)

let compiler_instance_FIELDS = define_record "compiler_instance"
  ["compiler_fun","(num#num)#'config#dec list->('config#word8 \
   list#word64 list) option";
   "config_v","'config->semanticPrimitives_v";
   "config_dom","'config->bool";
   "decs_v","dec list->semanticPrimitives_v";
   "decs_dom","dec list->bool";
   "init_state","'config"];;

let v_rel_abs = cake_define
  `v_fun_abs fun_dom fun_v v = (some (\x. fun_v x = v /\ x IN
  fun_dom))`;;

let mk_compiler_fun_from_ci_def = cake_define
  `mk_compiler_fun_from_ci ci (env_id,cfg_v,decs) =
     OPTION_BIND (v_fun_abs (compiler_instance_config_dom ci)
       (compiler_instance_config_v ci) cfg_v) (\cfg.
     OPTION_BIND (compiler_instance_compiler_fun ci
       (env_id,cfg,decs)) (\(cfg2,bs,ws).
     SOME (compiler_instance_config_v ci cfg2,bs,ws)))`;;

(* HOL4 source_evalProofScript.sml:41: the overload ci_comp, which
   the port expands *)

let mk_init_eval_state_def = cake_define
  `mk_init_eval_state ci = EvalDecs (mk_eval_decs_state
  (mk_compiler_fun_from_ci ci) (compiler_instance_config_v ci
  (compiler_instance_init_state ci)) (0,0,1) (v_fun_abs
  (compiler_instance_decs_dom ci) (compiler_instance_decs_v ci)))`;;

(* an instance of custom_do_eval that behaves as much as possible
   like the no-oracle semantics *)

let v_to_nat_def = cake_define
  `v_to_nat v = (match v with (semanticPrimitives_Litv (ast_IntLit
  i)) -> (if (&0) <= i then SOME (num_of_int i) else NONE) | _1 ->
  NONE)`;;

let v_to_env_id_def = cake_define
  `v_to_env_id v = (match v with semanticPrimitives_Conv NONE
  [gen_id_v; id_v] -> (match (v_to_nat gen_id_v,v_to_nat id_v) with
  (SOME gen_id,SOME id') -> SOME (gen_id,id') | _2 -> NONE) | _3 ->
  NONE)`;;

let do_eval_record_def = cake_define
  `do_eval_record ci vs (orac:num->(num#num)#semanticPrimitives_v#dec
  list) = (match vs with [env_id_v; st_v; decs_v; st_v2; bs_v; ws_v] ->
       (let ((i,_4),st,_5) = orac 0 in
       (match (v_to_env_id env_id_v,v_fun_abs
         (compiler_instance_decs_dom ci) (compiler_instance_decs_v ci)
         decs_v) with (SOME env_id,SOME decs) ->
         (if compiler_agrees (mk_compiler_fun_from_ci ci)
             (env_id,st_v,decs) (st_v2,bs_v,ws_v) /\ st_v = st then
         let orac' = (\j. if j = 0 then ((i + 1,0),st_v2,[]) else
           if j = SUC i then (env_id,st,decs) else orac j) in SOME
           (env_id,orac',decs) else NONE) | _6 -> NONE)) | _7 ->
           NONE)`;;

(* a somewhat generic env rel *)

let source_evalProof_env_rel_def = cake_define
  `source_evalProof_env_rel v_rel' (env:semanticPrimitives_v sem_env)
  env' <=> sem_env_c
     env = sem_env_c env' /\ nsDom (sem_env_v env) = nsDom (sem_env_v
       env') /\
     nsDomMod (sem_env_v env) = nsDomMod (sem_env_v env') /\
     (!nm x y. nsLookup (sem_env_v env) nm = SOME x /\ nsLookup
       (sem_env_v env') nm = SOME y ==>
         v_rel' x y)`;;
hol4_overload "env_rel" "source_evalProof_env_rel";;

let env_rel_mono_rel = prove
 (`(!y z. R y z ==> R' y z) ==>
   source_evalProof_env_rel R env env' ==>
   source_evalProof_env_rel R' env env'`,
  CHEAT_TAC);;

(* HOL4 source_evalProofScript.sml:106: ML code, not ported *)

let env_rel_add_nsBind = prove
 (`source_evalProof_env_rel R (sem_env_v_fupd (K ev) env)
  (sem_env_v_fupd (K ev') env') /\ R x y ==>
   source_evalProof_env_rel R (sem_env_v_fupd (K (nsBind n x ev))
     env) (sem_env_v_fupd (K (nsBind n y ev')) env')`,
  CHEAT_TAC);;

let env_rel_add_nsBindList = prove
 (`!xs ys. source_evalProof_env_rel R (sem_env_v_fupd (K ev) env)
  (sem_env_v_fupd (K ev') env') /\
   LIST_REL (RPROD (=) R) xs ys ==>
   source_evalProof_env_rel R (sem_env_v_fupd (K (nsBindList xs
     ev)) env) (sem_env_v_fupd (K (nsBindList ys ev')) env')`,
  CHEAT_TAC);;

let env_rel_nsLift = prove
 (`source_evalProof_env_rel R (sem_env_c_fupd (K c) (sem_env_v_fupd (K
  v) env))
     (sem_env_c_fupd (K c') (sem_env_v_fupd (K v') env')) ==>
   source_evalProof_env_rel R (sem_env_c_fupd (K (nsLift mn c))
     (sem_env_v_fupd (K (nsLift mn v)) env))
     (sem_env_c_fupd (K (nsLift mn c')) (sem_env_v_fupd (K (nsLift
       mn v')) env'))`,
  CHEAT_TAC);;

(* HOL4 source_evalProofScript.sml:144-148: a theorem that HOL4
   states as the value of an ML expression: env_rel_nsEmpty *)

(* HOL4 source_evalProofScript.sml:150: ML code, not ported *)

let env_rel_nsAppend = prove
 (`source_evalProof_env_rel R (sem_env_v_fupd (K a) env) (sem_env_v_fupd
  (K c) env') /\
   source_evalProof_env_rel R (sem_env_v_fupd (K b) env)
     (sem_env_v_fupd (K d) env') ==>
   source_evalProof_env_rel R (sem_env_v_fupd (K (nsAppend a b)) env)
     (sem_env_v_fupd (K (nsAppend c d)) env')`,
  CHEAT_TAC);;

let env_rel_extend_dec_env = prove
 (`source_evalProof_env_rel R env1 env2 /\ source_evalProof_env_rel R
  env3 env4 ==>
   source_evalProof_env_rel R (extend_dec_env env1 env3)
     (extend_dec_env env2 env4)`,
  CHEAT_TAC);;

let env_rel_nsLookup_v = prove
 (`source_evalProof_env_rel R env env' /\ nsLookup (sem_env_v env) id' =
  SOME v ==>
   (?v'. nsLookup (sem_env_v env') id' = SOME v' /\ R v v')`,
  CHEAT_TAC);;

(* [local] *)
let env_rel_nsLookup_c = prove
 (`source_evalProof_env_rel R env env' /\ nsLookup (sem_env_c env) id' =
  r ==> sem_env_c
   env' = sem_env_c env`,
  CHEAT_TAC);;


(* various trivia *)

(* HOL4 source_evalProofScript.sml:194-196: a theorem that HOL4
   states as the value of an ML expression: alist_to_ns_to_bind2 *)

(* HOL4 source_evalProofScript.sml:198-200: a theorem that HOL4
   states as the value of an ML expression: nsSing_eq_bind *)

(* [local] *)
let pair_CASE_eq_pairarg = prove
 (`pair_CASE p f = (\(x,y). f x y) p`,
  CHEAT_TAC);;

(* HOL4 source_evalProofScript.sml:208: the ML values that the
   definitions below antiquote *)

(* first step. switch over to recording semantics and move envs
   out of Env values and into the state *)

let source_evalProof_v_rel = cake_inductive
  `(!env'. v_to_env_id v = SOME id' /\ lookup_env es id' = SOME env' /\
         source_evalProof_env_rel (source_evalProof_v_rel es) env
           env' ==>
     source_evalProof_v_rel es (semanticPrimitives_Env env id') v) /\
   (LIST_REL (source_evalProof_v_rel es) xs ys ==>
     source_evalProof_v_rel es (semanticPrimitives_Vectorv xs)
       (semanticPrimitives_Vectorv ys)) /\
   (LIST_REL (source_evalProof_v_rel es) xs ys ==>
     source_evalProof_v_rel es (semanticPrimitives_Conv stmp xs)
       (semanticPrimitives_Conv stmp ys)) /\
   (source_evalProof_env_rel (source_evalProof_v_rel es) env env' ==>
     source_evalProof_v_rel es (semanticPrimitives_Closure env nm x)
       (semanticPrimitives_Closure env' nm x)) /\
   (source_evalProof_env_rel (source_evalProof_v_rel es) env env' ==>
     source_evalProof_v_rel es (semanticPrimitives_Recclosure env
       funs nm) (semanticPrimitives_Recclosure env' funs nm)) /\
   (source_evalProof_v_rel es (semanticPrimitives_Litv l)
     (semanticPrimitives_Litv l)) /\
   (source_evalProof_v_rel es (semanticPrimitives_Loc br n)
     (semanticPrimitives_Loc br n))`;;
hol4_overload "v_rel" "source_evalProof_v_rel";;

(* HOL4 source_evalProofScript.sml:229-237: a theorem that HOL4
   states as the value of an ML expression: v_rel_l_simps *)

(* v_rel_Boolv *)
let source_evalProof_v_rel_Boolv = prove
 (`source_evalProof_v_rel es (semanticPrimitives_Boolv b) v = (v =
  semanticPrimitives_Boolv b)`,
  CHEAT_TAC);;

(* HOL4 source_evalProofScript.sml:245: ML code, not ported *)

let recorded_orac_wf_def = cake_define
  `recorded_orac_wf compiler
  (orac:num->(num#num)#semanticPrimitives_v#dec list) <=>
   (0 < FST (FST (orac 0)) ==>
     (?r. compiler (orac (FST (FST (orac 0)))) = SOME r /\
         FST (SND (orac 0)) = FST r)) /\
   (!j. j < FST (FST (orac 0)) /\ 0 < j ==>
     (?r. compiler (orac j) = SOME r /\ FST (SND (orac (j + 1))) =
       FST r))`;;

let s_rel_def = cake_define
  `source_evalProof_s_rel ci s s' <=>
   (?dec_s orac_s' refs'. s' =
     semanticPrimitives_state_eval_state_fupd (K (SOME (EvalOracle
     orac_s'))) (semanticPrimitives_state_refs_fupd (K refs') s) /\
   LIST_REL (semanticPrimitivesProps_sv_rel (source_evalProof_v_rel
     orac_s')) (semanticPrimitives_state_refs s) refs' /\
     semanticPrimitives_state_eval_state
   s = SOME (EvalDecs dec_s) /\ eval_oracle_state_custom_do_eval
   orac_s' = do_eval_record ci /\ eval_decs_state_compiler_state
   dec_s = (FST (SND (oracle orac_s' 0))) /\
     eval_decs_state_decode_decs
   dec_s = v_fun_abs (compiler_instance_decs_dom ci)
     (compiler_instance_decs_v ci) /\ eval_decs_state_compiler
   dec_s = mk_compiler_fun_from_ci ci /\
   (
    // (0 < FST (FST (orac_s.oracle 0)) ==>
    // (FST (SND (orac_s.oracle 1))) = init_eds.compiler_state) /\
    0 = FST (FST (oracle orac_s' 0)) ==>
      eval_decs_state_compiler_state
     dec_s = compiler_instance_config_v ci
       (compiler_instance_init_state ci)) /\
   (0 < FST (FST (oracle orac_s' 0)) ==>
     FST (SND (oracle orac_s' 1)) = compiler_instance_config_v ci
       (compiler_instance_init_state ci)) /\
       eval_decs_state_env_id_counter
   dec_s = (eval_oracle_state_generation orac_s',
         LENGTH (EL (eval_oracle_state_generation orac_s')
           (eval_oracle_state_envs orac_s')),LENGTH
           (eval_oracle_state_envs orac_s')) /\
           eval_oracle_state_generation
   orac_s' < LENGTH (eval_oracle_state_envs orac_s') /\
   recorded_orac_wf (mk_compiler_fun_from_ci ci) (oracle orac_s'))`;;
hol4_overload "s_rel" "source_evalProof_s_rel";;

let orac_s_def = cake_define
  `orac_s x1 =
      match x1 with
        SOME (EvalOracle es) -> es
      | _8 -> ARB "not EvalOracle"`;;

(* HOL4 source_evalProofScript.sml:285: ML code, not ported *)

let es_forward_def = cake_define
  `es_forward es es' <=>
   (LENGTH (eval_oracle_state_envs es) <= LENGTH
     (eval_oracle_state_envs es')) /\
   (!env_id env. lookup_env es env_id = SOME env ==>
     lookup_env es' env_id = SOME env)`;;

let es_forward_refl = prove
 (`es_forward es es`,
  CHEAT_TAC);;

let es_forward_trans = prove
 (`es_forward es es' /\ es_forward es' es'' ==>
   es_forward es es''`,
  CHEAT_TAC);;

let v_rel_forward = prove
 (`!x y. source_evalProof_v_rel es x y ==> es_forward es es' ==>
  source_evalProof_v_rel es' x y`,
  CHEAT_TAC);;

let forward_rules = prove
 (`(source_evalProof_v_rel es x y /\ es_forward es es' ==>
  source_evalProof_v_rel es' x y) /\
   (LIST_REL (source_evalProof_v_rel es) xs ys /\ es_forward es es'
     ==>
     LIST_REL (source_evalProof_v_rel es') xs ys) /\
   (source_evalProof_env_rel (source_evalProof_v_rel es) env env' /\
     es_forward es es' ==>
     source_evalProof_env_rel (source_evalProof_v_rel es') env env')
       /\
   (!xs ys. LIST_REL (semanticPrimitivesProps_sv_rel
     (source_evalProof_v_rel es)) xs ys /\ es_forward es es' ==>
     LIST_REL (semanticPrimitivesProps_sv_rel
       (source_evalProof_v_rel es')) xs ys)`,
  CHEAT_TAC);;

(* a stronger notion that applies end-to-end over evaluate/evaluate_decs,
   where the generation stack will match at either end and the previous
   generations will be untouched. *)
let es_stack_forward_def = cake_define
  `es_stack_forward es es' <=> eval_oracle_state_generation
   es' = eval_oracle_state_generation es /\
   (!j. j < eval_oracle_state_generation es ==> EL j
     (eval_oracle_state_envs es') = EL j (eval_oracle_state_envs es))`;;

let es_stack_forward_refl = prove
 (`es_stack_forward es es`,
  CHEAT_TAC);;

let es_stack_forward_trans = prove
 (`es_stack_forward es1 es2 /\ es_stack_forward es2 es3 ==>
   es_stack_forward es1 es3`,
  CHEAT_TAC);;

let match_result_rel_def = cake_define
  `source_evalProof_match_result_rel nerr R mr1 mr2 <=> (match mr1
  with No_match -> mr2 = No_match | Match_type_error -> nerr \/ mr2 =
  Match_type_error | Match x -> (?y. mr2 = Match y /\ R x y))`;;
hol4_overload "match_result_rel" "source_evalProof_match_result_rel";;

let store_lookup_rel = prove
 (`LIST_REL (semanticPrimitivesProps_sv_rel R) refs refs' ==>
   OPTREL (semanticPrimitivesProps_sv_rel R) (store_lookup i refs)
     (store_lookup i refs')`,
  CHEAT_TAC);;

(* HOL4 source_evalProofScript.sml:373: the ML values that the
   definitions below antiquote *)

let s_rel_store_lookup = prove
 (`source_evalProof_s_rel ((ci:'cfg compiler_instance)) s t /\ j = i /\
  es = orac_s (semanticPrimitives_state_eval_state t) ==>
   OPTREL (semanticPrimitivesProps_sv_rel (source_evalProof_v_rel
     es)) (store_lookup i (semanticPrimitives_state_refs s))
     (store_lookup j (semanticPrimitives_state_refs t))`,
  CHEAT_TAC);;

let v_to_nat_SOME = prove
 (`v_to_nat v = SOME n ==>
   v = nat_to_v n`,
  CHEAT_TAC);;

let v_to_env_id_SOME = prove
 (`v_to_env_id v = SOME id' ==>
   v = semanticPrimitives_Conv NONE [nat_to_v (FST id'); nat_to_v
     (SND id')]`,
  CHEAT_TAC);;

let pmatch = prove
 (`source_evalProof_s_rel ((ci:'cfg compiler_instance)) s t /\ es =
  orac_s (semanticPrimitives_state_eval_state t) /\
  source_evalProof_env_rel (source_evalProof_v_rel es) env env' ==>
   (!env_c s_refs p x binds y binds'.
   s_refs = semanticPrimitives_state_refs s /\ env_c = sem_env_c env
     /\
   source_evalProof_v_rel es x y /\
   LIST_REL (RPROD (=) (source_evalProof_v_rel es)) binds binds' ==>
   source_evalProof_match_result_rel T (LIST_REL (RPROD (=)
     (source_evalProof_v_rel es)))
     (semanticPrimitives_pmatch env_c s_refs p x binds)
     (semanticPrimitives_pmatch (sem_env_c env')
       (semanticPrimitives_state_refs t) p y binds')) /\
   (!env_c s_refs ps xs binds ys binds'.
   s_refs = semanticPrimitives_state_refs s /\ env_c = sem_env_c env
     /\
   LIST_REL (source_evalProof_v_rel es) xs ys /\
   LIST_REL (RPROD (=) (source_evalProof_v_rel es)) binds binds' ==>
   source_evalProof_match_result_rel T (LIST_REL (RPROD (=)
     (source_evalProof_v_rel es)))
     (semanticPrimitives_pmatch_list env_c s_refs ps xs binds)
     (semanticPrimitives_pmatch_list (sem_env_c env')
       (semanticPrimitives_state_refs t) ps ys binds'))`,
  CHEAT_TAC);;

(* [local] *)
let pmatch_drule_form = prove
 (`semanticPrimitives_pmatch (sem_env_c env)
  (semanticPrimitives_state_refs s) p x [] = res /\
   source_evalProof_s_rel ((ci:'cfg compiler_instance)) s t /\
     source_evalProof_env_rel (source_evalProof_v_rel (orac_s
     (semanticPrimitives_state_eval_state t))) env env' /\
   source_evalProof_v_rel (orac_s
     (semanticPrimitives_state_eval_state t)) x y ==>
   source_evalProof_match_result_rel T (LIST_REL (RPROD (=)
     (source_evalProof_v_rel (orac_s
     (semanticPrimitives_state_eval_state t)))))
     res (semanticPrimitives_pmatch (sem_env_c env')
       (semanticPrimitives_state_refs t) p y [])`,
  CHEAT_TAC);;

let can_pmatch_all = prove
 (`can_pmatch_all (sem_env_c env) (semanticPrimitives_state_refs s) pats
  x /\
   source_evalProof_s_rel ((ci:'cfg compiler_instance)) s t /\
   source_evalProof_env_rel (source_evalProof_v_rel (orac_s
     (semanticPrimitives_state_eval_state t))) env env' /\
   source_evalProof_v_rel (orac_s
     (semanticPrimitives_state_eval_state t)) x y ==>
   can_pmatch_all (sem_env_c env') (semanticPrimitives_state_refs
     t) pats y`,
  CHEAT_TAC);;

(* Num_11 *)
let num_11 = prove
 (`(&0) <= i /\ (&0) <= j ==> (num_of_int i = num_of_int j) = (i = j)`,
  CHEAT_TAC);;

(* do_eq *)
let source_evalProof_do_eq = prove
 (`(!x y x' y' b. semanticPrimitives_do_eq x y = Eq_val b /\
   source_evalProof_v_rel es x x' /\
   source_evalProof_v_rel es y y' ==>
   semanticPrimitives_do_eq x' y' = Eq_val b) /\
   (!xs ys xs' ys' b. semanticPrimitives_do_eq_list xs ys = Eq_val b
     /\
   LIST_REL (source_evalProof_v_rel es) xs xs' /\
   LIST_REL (source_evalProof_v_rel es) ys ys' ==>
   semanticPrimitives_do_eq_list xs' ys' = Eq_val b)`,
  CHEAT_TAC);;

let store_assign = prove
 (`store_assign lnum sv refs = SOME refs2 /\
   LIST_REL (semanticPrimitivesProps_sv_rel R) refs refs3 /\
   semanticPrimitivesProps_sv_rel R sv sv' ==>
   (?refs4.
   LIST_REL (semanticPrimitivesProps_sv_rel R) refs2 refs4 /\
   store_assign lnum sv' refs3 = SOME refs4)`,
  CHEAT_TAC);;

let store_lookup = prove
 (`LIST_REL (semanticPrimitivesProps_sv_rel R) refs refs' /\
   store_lookup n refs = SOME sv ==>
   (?sv'. semanticPrimitivesProps_sv_rel R sv sv' /\
   store_lookup n refs' = SOME sv')`,
  CHEAT_TAC);;

let v_rel_list_to_v = prove
 (`!xs ys.
   source_evalProof_v_rel es (semanticPrimitives_list_to_v xs)
     (semanticPrimitives_list_to_v ys) <=>
   LIST_REL (source_evalProof_v_rel es) xs ys`,
  CHEAT_TAC);;

(* v_to_list *)
let source_evalProof_v_to_list = prove
 (`!x y xs. semanticPrimitives_v_to_list x = SOME xs /\
   source_evalProof_v_rel es x y ==>
   (?ys. semanticPrimitives_v_to_list y = SOME ys /\
   LIST_REL (source_evalProof_v_rel es) xs ys)`,
  CHEAT_TAC);;

let v_to_char_list = prove
 (`!x y xs. semanticPrimitives_v_to_char_list x = SOME xs /\
   source_evalProof_v_rel es x y ==>
   semanticPrimitives_v_to_char_list y = SOME xs`,
  CHEAT_TAC);;

let vs_to_string = prove
 (`!xs ys s. semanticPrimitives_vs_to_string xs = SOME s /\
   LIST_REL (source_evalProof_v_rel es) xs ys ==>
   semanticPrimitives_vs_to_string ys = SOME s`,
  CHEAT_TAC);;

(* HOL4 source_evalProofScript.sml:600-604: a theorem that HOL4
   states as the value of an ML expression: sv_rel_l_cases *)

(* [local] *)
let v_rel_check_type = prove
 (`source_evalProof_v_rel x v1 v2 ==>
   (semanticPrimitives_check_type ty v1 =
     semanticPrimitives_check_type ty v2) /\
   (semanticPrimitives_dest_Litv v1 = semanticPrimitives_dest_Litv
     v2)`,
  CHEAT_TAC);;

(* [local] *)
let LIST_REL_v_rel_check_type = prove
 (`LIST_REL (source_evalProof_v_rel x) vs1 vs2 ==>
   (EVERY (semanticPrimitives_check_type ty) vs1 <=> EVERY
     (semanticPrimitives_check_type ty) vs2)`,
  CHEAT_TAC);;

let do_app_sim = prove
 (`semanticPrimitives_do_app (semanticPrimitives_state_refs
  s,semanticPrimitives_state_ffi s) op (REVERSE xs) = SOME
  ((refs,ffi),r) /\
   source_evalProof_s_rel ((ci:'cfg compiler_instance)) s t /\
   LIST_REL (source_evalProof_v_rel (orac_s
     (semanticPrimitives_state_eval_state t))) xs ys /\ ~(r = Rerr
     (Rabort Rtype_error)) ==>
   (?ref1 refs' r' es.
     es = orac_s (semanticPrimitives_state_eval_state t) /\
     semanticPrimitives_do_app (semanticPrimitives_state_refs
       t,semanticPrimitives_state_ffi t) op (REVERSE ys) = SOME
       ((refs',ffi),r') /\
     LIST_REL (semanticPrimitivesProps_sv_rel (source_evalProof_v_rel
       es)) refs refs' /\
     semanticPrimitivesProps_result_rel (source_evalProof_v_rel es)
       (source_evalProof_v_rel es) r r')`,
  CHEAT_TAC);;

let pairarg_to_pair_map = prove
 (`(\(x,y). (f x,g y)) = (f ## g)`,
  CHEAT_TAC);;

let s_rel_clock = prove
 (`source_evalProof_s_rel ((ci:'cfg compiler_instance)) s t ==>
  semanticPrimitives_state_clock s = semanticPrimitives_state_clock t /\
     source_evalProof_s_rel ci (evaluate_dec_clock s)
       (evaluate_dec_clock t)`,
  CHEAT_TAC);;

let concrete_v_rel = prove
 (`!x y. source_evalProof_v_rel es x y ==> concrete_v x ==> y = x`,
  CHEAT_TAC);;

let v_to_list_concrete = prove
 (`!x xs. semanticPrimitives_v_to_list x = SOME xs ==>
   concrete_v x = EVERY concrete_v xs`,
  CHEAT_TAC);;

let maybe_all_list_SOME = prove
 (`!xs ys. maybe_all_list xs = SOME ys ==> xs = MAP SOME ys`,
  CHEAT_TAC);;

let maybe_all_list_EVERY = prove
 (`maybe_all_list xs = SOME ys ==> EVERY (\x. ~(x = NONE)) xs`,
  CHEAT_TAC);;

let v_to_word8_list_concrete = prove
 (`v_to_word8_list x = SOME xs ==>
   concrete_v x`,
  CHEAT_TAC);;

let v_to_word64_list_concrete = prove
 (`v_to_word64_list x = SOME xs ==>
   concrete_v x`,
  CHEAT_TAC);;

let compiler_agrees = prove
 (`compiler_agrees f (id',st_v,decs) (st_v2,bs_v,ws_v) ==>
   concrete_v st_v /\ concrete_v st_v2 /\ concrete_v bs_v /\
     concrete_v ws_v`,
  CHEAT_TAC);;

let recorded_orac_wf_step = prove
 (`recorded_orac_wf compiler orac /\
   compiler_agrees compiler args (st_v2,bs_v,ws_v) /\
   (0 < FST (FST (orac 0)) ==> FST (SND args) = (FST (SND (orac 0))))
     ==>
   recorded_orac_wf compiler
     (\j. if j = 0 then ((FST (FST (orac 0)) + 1,0),st_v2,[]) else
       if j = SUC (FST (FST (orac 0))) then args else orac j)`,
  CHEAT_TAC);;

let do_eval_sim = prove
 (`semanticPrimitives_do_eval (REVERSE xs)
  (semanticPrimitives_state_eval_state s) = SOME (env,decs,es) /\
   source_evalProof_s_rel ((ci:'cfg compiler_instance)) (s:'a
     semanticPrimitives_state) t /\
   LIST_REL (source_evalProof_v_rel (orac_s
     (semanticPrimitives_state_eval_state t))) xs ys ==>
   (?env' es'.
   es_forward (orac_s (semanticPrimitives_state_eval_state t))
     (orac_s es') /\
   semanticPrimitives_do_eval (REVERSE ys)
     (semanticPrimitives_state_eval_state t) = SOME (env',decs,es') /\
   source_evalProof_env_rel (source_evalProof_v_rel (orac_s es')) env
     env' /\
   source_evalProof_s_rel ci
     (semanticPrimitives_state_eval_state_fupd (K es) s)
     (semanticPrimitives_state_eval_state_fupd (K es') t) /\
   (!s2 t2. source_evalProof_s_rel ci (s2:'a
     semanticPrimitives_state) t2 /\
     es_forward (orac_s es') (orac_s
       (semanticPrimitives_state_eval_state t2)) /\
     es_stack_forward (orac_s es') (orac_s
       (semanticPrimitives_state_eval_state t2)) ==>
     es_forward (orac_s (semanticPrimitives_state_eval_state t2))
         (orac_s (reset_env_generation
           (semanticPrimitives_state_eval_state t)
           (semanticPrimitives_state_eval_state t2))) /\
     source_evalProof_s_rel ci
         (semanticPrimitives_state_eval_state_fupd (K
           (reset_env_generation (semanticPrimitives_state_eval_state s)
           (semanticPrimitives_state_eval_state s2))) s2)
         (semanticPrimitives_state_eval_state_fupd (K
           (reset_env_generation (semanticPrimitives_state_eval_state t)
           (semanticPrimitives_state_eval_state t2))) t2) /\
     es_stack_forward (orac_s (semanticPrimitives_state_eval_state
       t))
         (orac_s (reset_env_generation
           (semanticPrimitives_state_eval_state t)
           (semanticPrimitives_state_eval_state t2)))))`,
  CHEAT_TAC);;

let declare_env_sim = prove
 (`declare_env (semanticPrimitives_state_eval_state s) env = SOME (v,es)
  /\
   source_evalProof_s_rel ((ci:'cfg compiler_instance)) s t /\
   source_evalProof_env_rel (source_evalProof_v_rel (orac_s
     (semanticPrimitives_state_eval_state t))) env env' ==>
   (?v' es2.
   es_forward (orac_s (semanticPrimitives_state_eval_state t))
     (orac_s es2) /\
   declare_env (semanticPrimitives_state_eval_state t) env' = SOME
     (v',es2) /\
   source_evalProof_v_rel (orac_s es2) v v' /\
   source_evalProof_s_rel ci
     (semanticPrimitives_state_eval_state_fupd (K es) s)
     (semanticPrimitives_state_eval_state_fupd (K es2) t) /\
   es_stack_forward (orac_s (semanticPrimitives_state_eval_state
     t)) (orac_s es2))`,
  CHEAT_TAC);;

let abort_def = cake_define
  `source_evalProof_abort r <=> (match r with Rerr (Rabort a) -> T |
  _9 -> F)`;;
hol4_overload "abort" "source_evalProof_abort";;

(* [simp] *)
let abort_simps = prove
 (`source_evalProof_abort (Rerr (Rabort a)) = T /\
   source_evalProof_abort (Rerr (Rraise e)) = F /\
   source_evalProof_abort (Rval v) = F`,
  CHEAT_TAC);;

(* [local] *)
let abort_imp_intro = prove
 (`(!v. x = Rval v ==> P) /\ (!e. x = Rerr (Rraise e) ==> P) ==>
   (~(source_evalProof_abort x) ==> P)`,
  CHEAT_TAC);;

(* case splits for evaluate proofs *)
(* HOL4 source_evalProofScript.sml:931-936: a proof *)

(* take a step of forward-consistency-type reasoning *)
(* HOL4 source_evalProofScript.sml:939-941: ML code, not ported *)

(* quantifier instantiation based on s_rel, v_rel etc *)
(* HOL4 source_evalProofScript.sml:944-957: a proof *)

(* [local] *)
let env_rel_imp_c = prove
 (`source_evalProof_env_rel x env env' ==> sem_env_c env' = sem_env_c
  env`,
  CHEAT_TAC);;

let eval_simulation = prove
 (`(!((s:'ffi semanticPrimitives_state)) env exps s' res es t env'.
   evaluate s env exps = (s',res) /\
   source_evalProof_s_rel ((ci:'cfg compiler_instance)) s t /\
   source_evalProof_env_rel (source_evalProof_v_rel (orac_s
     (semanticPrimitives_state_eval_state t))) env env' /\ ~(res = Rerr
     (Rabort Rtype_error)) ==>
   (?es' t' res'.
   evaluate t env' exps = (t',res') /\
   source_evalProof_s_rel ci s' t' /\
   es' = orac_s (semanticPrimitives_state_eval_state t') /\
   semanticPrimitivesProps_result_rel (LIST_REL
     (source_evalProof_v_rel es')) (source_evalProof_v_rel es') res res'
     /\
   es_forward (orac_s (semanticPrimitives_state_eval_state t)) es' /\
   (~(source_evalProof_abort res') ==> es_stack_forward (orac_s
     (semanticPrimitives_state_eval_state t)) es'))) /\
   (!((s:'ffi semanticPrimitives_state)) env x pes err_x s' res es t
     env' y err_y.
   evaluate_evaluate_match s env x pes err_x = (s',res) /\
   source_evalProof_s_rel ci s t /\
   es = orac_s (semanticPrimitives_state_eval_state t) /\
   source_evalProof_env_rel (source_evalProof_v_rel es) env env' /\
   source_evalProof_v_rel es x y /\
   source_evalProof_v_rel es err_x err_y /\ ~(res = Rerr (Rabort
     Rtype_error)) ==>
   (?es' t' res'.
   evaluate_evaluate_match t env' y pes err_y = (t',res') /\
   source_evalProof_s_rel ci s' t' /\
   es' = orac_s (semanticPrimitives_state_eval_state t') /\
   semanticPrimitivesProps_result_rel (LIST_REL
     (source_evalProof_v_rel es')) (source_evalProof_v_rel es') res res'
     /\
   es_forward es es' /\
   (~(source_evalProof_abort res') ==> es_stack_forward es es'))) /\
   (!((s:'ffi semanticPrimitives_state)) env decs s' res t env'.
   evaluate_evaluate_decs s env decs = (s',res) /\
   source_evalProof_s_rel ci s t /\
   source_evalProof_env_rel (source_evalProof_v_rel (orac_s
     (semanticPrimitives_state_eval_state t))) env env' /\ ~(res = Rerr
     (Rabort Rtype_error)) ==>
   (?es' t' res'.
   evaluate_evaluate_decs t env' decs = (t',res') /\
   source_evalProof_s_rel ci s' t' /\
   es' = orac_s (semanticPrimitives_state_eval_state t') /\
   semanticPrimitivesProps_result_rel (source_evalProof_env_rel
     (source_evalProof_v_rel es')) (source_evalProof_v_rel es') res res'
     /\
   es_forward (orac_s (semanticPrimitives_state_eval_state t)) es' /\
   (~(source_evalProof_abort res') ==> es_stack_forward (orac_s
     (semanticPrimitives_state_eval_state t)) es')))`,
  CHEAT_TAC);;

(* HOL4 source_evalProofScript.sml:1049-1224: a proof *)

(* HOL4 source_evalProofScript.sml:1226-1256: a proof *)

(* HOL4 source_evalProofScript.sml:1258-1266: a proof *)

(* HOL4 source_evalProofScript.sml:1268-1280: a proof *)

(* HOL4 source_evalProofScript.sml:1282-1295: a proof *)

(* HOL4 source_evalProofScript.sml:1297-1309: a proof *)

(* HOL4 source_evalProofScript.sml:1311-1326: a proof *)

(* HOL4 source_evalProofScript.sml:1328-1340: a proof *)

(* check_dup_ctors_thm *)
let source_evalProof_check_dup_ctors_thm = prove
 (`check_dup_ctors (tvs,tn,condefs) = ALL_DISTINCT (MAP FST condefs)`,
  CHEAT_TAC);;

(* HOL4 source_evalProofScript.sml:1358-1366: a proof *)

(* HOL4 source_evalProofScript.sml:1368-1373: a proof *)

(* HOL4 source_evalProofScript.sml:1375-1383: a proof *)

(* HOL4 source_evalProofScript.sml:1385: a proof *)

(* HOL4 source_evalProofScript.sml:1387: the overload shift_seq,
   which the port expands *)

let do_eval_oracle_def = cake_define
  `do_eval_oracle (f:(num#num)#semanticPrimitives_v#dec
  list->(semanticPrimitives_v#word8 list#word64 list) option) (g:dec
  list->dec list) vs (orac:num->(num#num)#semanticPrimitives_v#dec list)
  =
   (match vs with [env_id_v; st_v; decs_v; st_v2; bs_v; ws_v] ->
       (let (env_id,st,decs) = orac 0 in
       (match (f (env_id,st,decs),v_to_word8_list bs_v,
             v_to_word64_list ws_v) with (SOME (st_v2,c_bs,c_ws),SOME
               bs,SOME ws) ->
             (if bs = c_bs /\ ws = c_ws /\ st_v2 = (FST (SND (orac
               1))) then SOME (env_id,misc_shift_seq 1 orac,g decs)
               else NONE) | _10 -> NONE)) | _11 -> NONE)`;;

let insert_gen_oracle_def = cake_define
  `insert_gen_oracle ci g shift_f orac es = (match es with SOME
  (EvalOracle s) -> SOME (EvalOracle (oracle_fupd (K (misc_shift_seq
  (shift_f (oracle s 0)) orac))
  (eval_oracle_state_custom_do_eval_fupd (K (do_eval_oracle
  (mk_compiler_fun_from_ci ci) g)) s))) | _12 -> es)`;;

(* HOL4 source_evalProofScript.sml:1414: the overload insert_oracle,
   which the port expands *)

let orac_agrees_def = cake_define
  `orac_agrees orac es = (match es with SOME (EvalOracle s) ->
       (!j. j < FST (FST (oracle s 0)) ==> orac j = oracle s (j +
         1)) | _13 -> F)`;;

(* the infinite extension of an oracle is still well-formed with
   respect to the compiler function *)
let orac_extended_wf_def = cake_define
  `orac_extended_wf f orac =
   (!i x. f (orac i) = SOME x ==> FST x = FST (SND (orac (SUC
     i))))`;;

let record_forward_def = cake_define
  `record_forward es es' = (match es with SOME (EvalOracle s) -> (?s'.
  es' = SOME (EvalOracle s') /\
         (FST (FST (oracle s 0)) <= FST (FST (oracle s' 0))) /\
         (!j. 0 < j /\ j < FST (FST (oracle s 0)) + 1 ==> oracle
             s' j = oracle s j)) | _14 -> (match es' with SOME
               (EvalOracle _15) -> F | _16 -> T))`;;

let record_forward_refl = prove
 (`record_forward es es`,
  CHEAT_TAC);;

let record_forward_trans = prove
 (`record_forward es1 es2 /\ record_forward es2 es3 ==>
   record_forward es1 es3`,
  CHEAT_TAC);;

let orac_agrees_backward = prove
 (`orac_agrees orac es2 /\ record_forward es1 es2 ==>
   orac_agrees orac es1`,
  CHEAT_TAC);;

let is_record_def = cake_define
  `is_record ci es <=> (match es with SOME (EvalOracle s) ->
  eval_oracle_state_custom_do_eval
         s = do_eval_record ci | _17 -> F)`;;

let is_record_IMP = prove
 (`is_record ((ci:'cfg compiler_instance)) es ==> (?orac_st. es = SOME
  (EvalOracle orac_st))`,
  CHEAT_TAC);;

let insert_do_eval = prove
 (`semanticPrimitives_do_eval vs es = SOME (env,decs,es') /\
   is_record ci es ==>
   is_record ci es' /\
   record_forward es es' /\
   (orac_agrees orac es' /\
   orac_extended_wf (mk_compiler_fun_from_ci ci) orac ==>
   semanticPrimitives_do_eval vs ((\ci. insert_gen_oracle ci I (FST o
     FST)) ci orac es) = SOME (env,decs,
     (\ci. insert_gen_oracle ci I (FST o FST)) ci orac es')) /\
   (recorded_orac_wf (mk_compiler_fun_from_ci ci) (oracle (orac_s
     es)) ==>
     recorded_orac_wf (mk_compiler_fun_from_ci ci) (oracle (orac_s
       es')))`,
  CHEAT_TAC);;

let insert_declare_env = prove
 (`declare_env es1 env = SOME (x,es2) /\
   is_record ci es1 ==>
   is_record ci es2 /\
   record_forward es1 es2 /\
   (orac_agrees orac es2 ==>
   declare_env ((\ci. insert_gen_oracle ci I (FST o FST)) ci orac
     es1) env = SOME (x,
     (\ci. insert_gen_oracle ci I (FST o FST)) ci orac es2)) /\
   (recorded_orac_wf (mk_compiler_fun_from_ci ci) (oracle (orac_s
     es1)) ==>
     recorded_orac_wf (mk_compiler_fun_from_ci ci) (oracle (orac_s
       es2)))`,
  CHEAT_TAC);;

let reset_env_generation_orac_eqs = prove
 (`(is_record ci (reset_env_generation es2 es3) = is_record ci es3) /\
   (record_forward es1 (reset_env_generation es2 es3) =
     record_forward es1 es3) /\
   (orac_agrees orac (reset_env_generation es2 es3) = orac_agrees
     orac es3) /\
   (reset_env_generation ((\ci. insert_gen_oracle ci I (FST o FST))
     ci orac es1) es2 =
     reset_env_generation es1 es2) /\
   (reset_env_generation es1 ((\ci. insert_gen_oracle ci I (FST o
     FST)) ci orac es2) =
     (\ci. insert_gen_oracle ci I (FST o FST)) ci orac
       (reset_env_generation es1 es2)) /\
   (oracle (orac_s (reset_env_generation es2 es3)) = oracle (orac_s
     es3))`,
  CHEAT_TAC);;

(* HOL4 source_evalProofScript.sml:1547-1548: a theorem that HOL4
   states as the value of an ML expression: record_forward_trans_sym *)

let evaluate_is_record_forward = prove
 (`(!((s:'ffi semanticPrimitives_state)) env exps s' res.
   evaluate s env exps = (s',res) /\
   is_record ((ci:'cfg compiler_instance))
     (semanticPrimitives_state_eval_state s) ==>
   is_record ci (semanticPrimitives_state_eval_state s') /\
   record_forward (semanticPrimitives_state_eval_state s)
     (semanticPrimitives_state_eval_state s') /\
   (recorded_orac_wf (mk_compiler_fun_from_ci ci) (oracle (orac_s
     (semanticPrimitives_state_eval_state s))) ==>
     recorded_orac_wf (mk_compiler_fun_from_ci ci) (oracle (orac_s
       (semanticPrimitives_state_eval_state s'))))) /\
   (!((s:'ffi semanticPrimitives_state)) env x pes err_x s' res.
   evaluate_evaluate_match s env x pes err_x = (s',res) /\
   is_record ci (semanticPrimitives_state_eval_state s) ==>
   is_record ci (semanticPrimitives_state_eval_state s') /\
   record_forward (semanticPrimitives_state_eval_state s)
     (semanticPrimitives_state_eval_state s') /\
   (recorded_orac_wf (mk_compiler_fun_from_ci ci) (oracle (orac_s
     (semanticPrimitives_state_eval_state s))) ==>
     recorded_orac_wf (mk_compiler_fun_from_ci ci) (oracle (orac_s
       (semanticPrimitives_state_eval_state s'))))) /\
   (!((s:'ffi semanticPrimitives_state)) env decs s' res.
   evaluate_evaluate_decs s env decs = (s',res) /\
   is_record ci (semanticPrimitives_state_eval_state s) ==>
   is_record ci (semanticPrimitives_state_eval_state s') /\
   record_forward (semanticPrimitives_state_eval_state s)
     (semanticPrimitives_state_eval_state s') /\
   (recorded_orac_wf (mk_compiler_fun_from_ci ci) (oracle (orac_s
     (semanticPrimitives_state_eval_state s))) ==>
     recorded_orac_wf (mk_compiler_fun_from_ci ci) (oracle (orac_s
       (semanticPrimitives_state_eval_state s')))))`,
  CHEAT_TAC);;

(* HOL4 source_evalProofScript.sml:1624-1626: a proof *)

(* HOL4 source_evalProofScript.sml:1628-1630: a proof *)

(* HOL4 source_evalProofScript.sml:1632-1636: ML code, not ported *)

(* HOL4 source_evalProofScript.sml:1638-1641: a proof *)

(* HOL4 source_evalProofScript.sml:1643: ML code, not ported *)

let insert_oracle_correct = prove
 (`(!((s:'ffi semanticPrimitives_state)) env exps s' res.
   evaluate s env exps = (s',res) /\
   is_record ci (semanticPrimitives_state_eval_state s) /\
   orac_agrees orac (semanticPrimitives_state_eval_state s') /\
   orac_extended_wf (mk_compiler_fun_from_ci ci) orac /\ ~(res = Rerr
     (Rabort Rtype_error)) ==>
   evaluate (semanticPrimitives_state_eval_state_fupd ((\ci.
     insert_gen_oracle ci I (FST o FST)) ci orac) s) env exps =
   (semanticPrimitives_state_eval_state_fupd ((\ci. insert_gen_oracle
     ci I (FST o FST)) ci orac) s',res)) /\
   (!((s:'ffi semanticPrimitives_state)) env x pes err_x s' res.
   evaluate_evaluate_match s env x pes err_x = (s',res) /\
   is_record ci (semanticPrimitives_state_eval_state s) /\
   orac_agrees orac (semanticPrimitives_state_eval_state s') /\
   orac_extended_wf (mk_compiler_fun_from_ci ci) orac /\ ~(res = Rerr
     (Rabort Rtype_error)) ==>
   evaluate_evaluate_match (semanticPrimitives_state_eval_state_fupd
     ((\ci. insert_gen_oracle ci I (FST o FST)) ci orac) s)
     env x pes err_x =
   (semanticPrimitives_state_eval_state_fupd ((\ci. insert_gen_oracle
     ci I (FST o FST)) ci orac) s',res)) /\
   (!((s:'ffi semanticPrimitives_state)) env decs s' res.
   evaluate_evaluate_decs s env decs = (s',res) /\
   is_record ci (semanticPrimitives_state_eval_state s) /\
   orac_agrees orac (semanticPrimitives_state_eval_state s') /\
   orac_extended_wf (mk_compiler_fun_from_ci ci) orac /\ ~(res = Rerr
     (Rabort Rtype_error)) ==>
   evaluate_evaluate_decs (semanticPrimitives_state_eval_state_fupd
     ((\ci. insert_gen_oracle ci I (FST o FST)) ci orac) s) env decs =
   (semanticPrimitives_state_eval_state_fupd ((\ci.
     insert_gen_oracle ci I (FST o FST)) ci orac) s',res))`,
  CHEAT_TAC);;

(* HOL4 source_evalProofScript.sml:1702-1706: a proof *)
    (* Eval *)
(* HOL4 source_evalProofScript.sml:1708-1730: a proof *)
    (* Opapp *)
(* HOL4 source_evalProofScript.sml:1732-1748: a proof *)

(* HOL4 source_evalProofScript.sml:1750-1755: a proof *)

(* HOL4 source_evalProofScript.sml:1757: a proof *)

let v_rel_concrete_v = prove
 (`(!v. concrete_v v ==> source_evalProof_v_rel es v v) /\
   (!vs. concrete_v_list vs ==> LIST_REL (source_evalProof_v_rel
     es) vs vs)`,
  CHEAT_TAC);;

let env_rel_concrete_v = prove
 (`nsAll (K concrete_v) (sem_env_v env) ==>
   source_evalProof_env_rel (source_evalProof_v_rel es) env env`,
  CHEAT_TAC);;

(* [local] *)
let neq_IMP_to_cases = prove
 (`!y. (~(x = y) ==> P) ==> (x = y) \/ (~(x = y))`,
  CHEAT_TAC);;

(* [local] *)
let less_sub_1_cases = prove
 (`k <= clock /\ (k <= clock - 1 ==> P) ==>
   (k = clock \/ k <= clock - (1:num))`,
  CHEAT_TAC);;

let evaluate_record_suffix = prove
 (`(!((s:'ffi semanticPrimitives_state)) env exps s' res.
   evaluate s env exps = (s',res) /\
   is_record ci (semanticPrimitives_state_eval_state s) /\
   k <= semanticPrimitives_state_clock s ==>
   (let ev = evaluate (semanticPrimitives_state_clock_fupd (\c. c -
     k) s) env exps in
   (
   k <= semanticPrimitives_state_clock s' /\
   ev = (semanticPrimitives_state_clock_fupd (\c. c - k) s',res)) \/
     (
   ?s''. ev = (s'',Rerr (Rabort Rtimeout_error)) /\
   record_forward (semanticPrimitives_state_eval_state s'')
     (semanticPrimitives_state_eval_state s')))) /\
   (!((s:'ffi semanticPrimitives_state)) env x pes err_x s' res.
   evaluate_evaluate_match s env x pes err_x = (s',res) /\
   is_record ci (semanticPrimitives_state_eval_state s) /\
   k <= semanticPrimitives_state_clock s ==>
   (let ev = evaluate_evaluate_match
     (semanticPrimitives_state_clock_fupd (\c. c - k) s) env x pes err_x
     in
   (
   k <= semanticPrimitives_state_clock s' /\
   ev = (semanticPrimitives_state_clock_fupd (\c. c - k) s',res)) \/
     (
   ?s''. ev = (s'',Rerr (Rabort Rtimeout_error)) /\
   record_forward (semanticPrimitives_state_eval_state s'')
     (semanticPrimitives_state_eval_state s')))) /\
   (!((s:'ffi semanticPrimitives_state)) env decs s' res.
   evaluate_evaluate_decs s env decs = (s',res) /\
   is_record ci (semanticPrimitives_state_eval_state s) /\
   k <= semanticPrimitives_state_clock s ==>
   (let ev = evaluate_evaluate_decs
     (semanticPrimitives_state_clock_fupd (\c. c - k) s) env decs in
   (
   k <= semanticPrimitives_state_clock s' /\
   ev = (semanticPrimitives_state_clock_fupd (\c. c - k) s',res)) \/
     (
   ?s''. ev = (s'',Rerr (Rabort Rtimeout_error)) /\
   record_forward (semanticPrimitives_state_eval_state s'')
     (semanticPrimitives_state_eval_state s'))))`,
  CHEAT_TAC);;

(* Constructs the oracle from an evaluation by using the recorded
   events, padding with null events if necessary. *)
let extract_oracle_def = cake_define
  `extract_oracle s env decs n =
     (match (OLEAST (\k. ?s' res.
       evaluate_evaluate_decs (semanticPrimitives_state_clock_fupd (K
         k) s) env decs = (s',res) /\
         n < FST (FST (oracle (orac_s
           (semanticPrimitives_state_eval_state s')) 0)))) with NONE ->
           NONE | SOME k ->
       (let (s',_18) = evaluate_evaluate_decs
         (semanticPrimitives_state_clock_fupd (K k) s) env decs in
         SOME (oracle (orac_s (semanticPrimitives_state_eval_state
           s')) (n + 1))))`;;

let evaluate_decs_clock_record_common_prefix = prove
 (`evaluate_evaluate_decs s env decs = (s',res) /\
   evaluate_evaluate_decs (semanticPrimitives_state_clock_fupd (K k)
     s) env decs = (s'',res') /\
   is_record ((ci:'cfg compiler_instance))
     (semanticPrimitives_state_eval_state s) /\
   j < FST (FST (oracle (orac_s (semanticPrimitives_state_eval_state
     s')) 0)) /\
   j < FST (FST (oracle (orac_s (semanticPrimitives_state_eval_state
     s'')) 0)) ==> oracle
   (orac_s (semanticPrimitives_state_eval_state s')) (j + 1) = oracle
     (orac_s (semanticPrimitives_state_eval_state s'')) (j + 1)`,
  CHEAT_TAC);;

(* [local] *)
let recorded_orac_wf_defined = prove
 (`recorded_orac_wf compiler orac /\
   i <= FST (FST (orac 0)) /\
   0 < i ==> ~(compiler (orac i) = NONE)`,
  CHEAT_TAC);;

let extract_oracle_agrees = prove
 (`evaluate_evaluate_decs (semanticPrimitives_state_clock_fupd (K k) t)
  env decs = (t',res) /\
   source_evalProof_s_rel ((ci:'cfg compiler_instance)) s t /\
   (!i r. extract_oracle t env decs i = SOME r /\
     ~(mk_compiler_fun_from_ci ci r = NONE) ==>
     orac i = r) ==>
   orac_agrees orac (semanticPrimitives_state_eval_state t')`,
  CHEAT_TAC);;

let get_oracle_def = cake_define
  `get_oracle ci s env decs =
     (let es_record = EvalOracle (mk_eval_oracle_state (K
       ((0,0),compiler_instance_config_v ci
       (compiler_instance_init_state ci),[])) (do_eval_record ci) [[]]
       0) in
     extract_oracle (semanticPrimitives_state_eval_state_fupd (K
       (SOME es_record)) s) env decs)`;;

let put_oracle_def = cake_define
  `put_oracle ci orac = ((\ci. insert_gen_oracle ci I (FST o FST)) ci
  orac
     (SOME (EvalOracle (mk_eval_oracle_state (K
       ((0,0),compiler_instance_config_v ci
       (compiler_instance_init_state ci),[])) (do_eval_record ci)
       [[]] 0))))`;;

let result_rel_IMP_cases = prove
 (`semanticPrimitivesProps_result_rel r_rel e_rel r r' ==>
   ((?x. r = Rval x) \/ (?y. r = Rerr (Rraise y)) \/ (?a. r = Rerr
     (Rabort a)))`,
  CHEAT_TAC);;

(* [local] *)
let s_rel_clock2 = prove
 (`!k. source_evalProof_s_rel ci s t ==> source_evalProof_s_rel ci
  (semanticPrimitives_state_clock_fupd (K k) s)
  (semanticPrimitives_state_clock_fupd (K k) t)`,
  CHEAT_TAC);;

let precond_eval_state_def = cake_define
  `precond_eval_state orac ci s env decs = (match
  semanticPrimitives_state_eval_state s with NONE -> T | SOME (EvalDecs
  eds) -> EvalDecs eds = mk_init_eval_state ci /\
         (orac_extended_wf (mk_compiler_fun_from_ci ci) orac) /\
         (!i r x. get_oracle ci s env decs i = SOME r /\
           mk_compiler_fun_from_ci ci r = SOME x ==>
             orac i = r) | SOME (EvalOracle _19) -> F)`;;

(* [local] *)
let extract_oracle_SOME_SUC = prove
 (`IS_SOME (extract_oracle s env decs (SUC i)) ==>
   IS_SOME (extract_oracle s env decs i)`,
  CHEAT_TAC);;

(* [local] *)
let extract_oracle_0_st = prove
 (`extract_oracle t env decs 0 = SOME r /\
   ~(semantics_prog s env decs ffi_Fail) /\
   source_evalProof_s_rel ci s t /\
   nsAll (K concrete_v) (sem_env_v env) ==>
   FST (SND r) = compiler_instance_config_v ci
     (compiler_instance_init_state ci)`,
  CHEAT_TAC);;

(* [local] *)
let orac_agrees_s_rel_IMP = prove
 (`orac_agrees orac (semanticPrimitives_state_eval_state t) ==>
   source_evalProof_s_rel ci s t ==>
   i < FST (FST (oracle (orac_s (semanticPrimitives_state_eval_state
     t)) 0)) ==>
   orac i = oracle (orac_s (semanticPrimitives_state_eval_state t))
     (i + 1)`,
  CHEAT_TAC);;

(* [local] *)
let extract_oracle_SUC_st = prove
 (`IS_SOME (extract_oracle t env decs (SUC i)) /\
   source_evalProof_s_rel ci s t /\
   nsAll (K concrete_v) (sem_env_v env) /\
   ~(semantics_prog s env decs ffi_Fail) ==>
   (?r r' x. extract_oracle t env decs (SUC i) = SOME r' /\
   extract_oracle t env decs i = SOME r /\
   mk_compiler_fun_from_ci ci r = SOME x /\
   FST (SND r') = FST x)`,
  CHEAT_TAC);;

let get_oracle_props = prove
 (`nsAll (K concrete_v) (sem_env_v env) /\ semanticPrimitives_state_refs
   s = [] /\ semanticPrimitives_state_eval_state
   s = SOME (mk_init_eval_state ci) /\
   ~(semantics_prog s env decs ffi_Fail) ==>
   (!r. get_oracle ci s env decs 0 = SOME r ==>
     FST (SND r) = compiler_instance_config_v ci
       (compiler_instance_init_state ci)) /\
   (!i r'. get_oracle ci s env decs (SUC i) = SOME r' ==>
     (?r x. get_oracle ci s env decs i = SOME r /\
       mk_compiler_fun_from_ci ci r = SOME x /\
         FST (SND r') = FST x))`,
  CHEAT_TAC);;

let evaluate_prog_with_clock_put_oracle = prove
 (`precond_eval_state orac ci s1 env decs /\
   evaluate_prog_with_clock s1 env k decs = (ffi,res) /\ ~(res = Rerr
     (Rabort Rtype_error)) /\ semanticPrimitives_state_refs
   s1 = [] /\
   nsAll (K concrete_v) (sem_env_v env) /\
   ~(semantics_prog s1 env decs ffi_Fail) ==>
   (?res'.
   evaluate_prog_with_clock
     (semanticPrimitives_state_eval_state_fupd (K (put_oracle ci
       orac)) s1)
     env k decs = (ffi,res') /\
   semanticPrimitivesProps_result_rel (K (K T)) (K (K T)) res res')`,
  CHEAT_TAC);;

let oracle_semantics_prog = prove
 (`~(semantics_prog s1 env decs ffi_Fail) /\
   semantics_prog (semanticPrimitives_state_eval_state_fupd (K
     (put_oracle ci orac)) s1)
     env decs outcome /\
   precond_eval_state orac ((ci:'cfg compiler_instance)) s1 env decs
     /\ semanticPrimitives_state_refs
   s1 = [] /\
   nsAll (K concrete_v) (sem_env_v env) ==>
   semantics_prog s1 env decs outcome`,
  CHEAT_TAC);;

(* for use in source-to-source phases, a proof that the oracle can be adjusted
   by any stateless compiler *)

let adjust_oracle_def = cake_define
  `adjust_oracle ci f es = (match es with
     NONE -> es | SOME (EvalDecs _20) -> es | SOME (EvalOracle o_s)
       -> SOME (EvalOracle
         (eval_oracle_state_custom_do_eval_fupd (K (do_eval_oracle
           (mk_compiler_fun_from_ci ci) f)) o_s)))`;;

let adjust_oracle_insert_gen_oracle = prove
 (`adjust_oracle ci f (insert_gen_oracle ci g shift_f orac es) =
     insert_gen_oracle ci f shift_f orac es`,
  CHEAT_TAC);;

(* HOL4 source_evalProofScript.sml:2249: the overload
   s_adjust_oracle, which the port expands *)

let is_insert_oracle_def = cake_define
  `is_insert_oracle ci f es = (?es' shift_f orac. es =
  insert_gen_oracle ci f shift_f orac es')`;;

(* [local] *)
let is_insert_decs = prove
 (`is_insert_oracle ci f (SOME (EvalDecs eds))`,
  CHEAT_TAC);;

(* [local] *)
let do_eval_adjust = prove
 (`semanticPrimitives_do_eval vs es = SOME (env1,decs,es1) /\
   is_insert_oracle ci f es ==>
   (
     semanticPrimitives_do_eval vs (adjust_oracle ci (g o f) es) =
       SOME (env1,g decs,adjust_oracle ci (g o f) es1) \/
       semanticPrimitives_do_eval vs (adjust_oracle ci (g o f) es) =
       SOME (env1,decs,adjust_oracle ci (g o f) es1)) /\
   is_insert_oracle ci f es1`,
  CHEAT_TAC);;

(* [local] *)
let declare_env_adjust = prove
 (`declare_env (adjust_oracle ci f es) env = (match declare_env es env
  with
     NONE -> NONE | SOME (x,es2) -> SOME (x,adjust_oracle ci f
       es2))`,
  CHEAT_TAC);;

(* [local] *)
let adjust_oracle_reset = prove
 (`adjust_oracle ci f (reset_env_generation es1 es2) =
     reset_env_generation (adjust_oracle ci f es1) (adjust_oracle
       ci f es2)`,
  CHEAT_TAC);;

(* [local] *)
let is_insert_related = prove
 (`is_insert_oracle ci f (SOME (EvalOracle es)) ==>
   (eval_oracle_state_custom_do_eval es2 =
     eval_oracle_state_custom_do_eval es /\ oracle es2 = oracle es) ==>
   is_insert_oracle ci f (SOME (EvalOracle es2))`,
  CHEAT_TAC);;

(* [local] *)
let is_insert_reset = prove
 (`is_insert_oracle ci f (reset_env_generation es1 es2) =
  is_insert_oracle ci f es2`,
  CHEAT_TAC);;

(* [local] *)
let declare_env_is_insert = prove
 (`declare_env es env = SOME (x,es2) /\
   is_insert_oracle ci f es ==>
   is_insert_oracle ci f es2`,
  CHEAT_TAC);;

let adjust_oracle_evaluate = prove
 (`(!((s:'ffi semanticPrimitives_state)) env ds s' res.
     evaluate_evaluate_decs s env ds = (s',res) /\ ~(res = Rerr
       (Rabort Rtype_error)) ==>
       evaluate_evaluate_decs s env (compile_decs ds) = (s',res)) ==>
   (!((s:'ffi semanticPrimitives_state)) env exps s' res.
     evaluate s env exps = (s',res) /\
     is_insert_oracle ci f (semanticPrimitives_state_eval_state s) /\
       ~(res = Rerr (Rabort Rtype_error)) ==>
       is_insert_oracle ci f (semanticPrimitives_state_eval_state s')
         /\
       evaluate (semanticPrimitives_state_eval_state_fupd
         (adjust_oracle ci (compile_decs o f)) s) env exps =
           (semanticPrimitives_state_eval_state_fupd (adjust_oracle
             ci (compile_decs o f)) s',res)) /\
   (!((s:'ffi semanticPrimitives_state)) env x pes err_x s' res.
     evaluate_evaluate_match s env x pes err_x = (s',res) /\
     is_insert_oracle ci f (semanticPrimitives_state_eval_state s) /\
       ~(res = Rerr (Rabort Rtype_error)) ==>
       is_insert_oracle ci f (semanticPrimitives_state_eval_state s')
         /\
       evaluate_evaluate_match
         (semanticPrimitives_state_eval_state_fupd (adjust_oracle ci
         (compile_decs o f)) s) env x pes err_x =
           (semanticPrimitives_state_eval_state_fupd (adjust_oracle
             ci (compile_decs o f)) s',res)) /\
   (!((s:'ffi semanticPrimitives_state)) env ds s' res.
     evaluate_evaluate_decs s env ds = (s',res) /\
     is_insert_oracle ci f (semanticPrimitives_state_eval_state s) /\
       ~(res = Rerr (Rabort Rtype_error)) ==>
       is_insert_oracle ci f (semanticPrimitives_state_eval_state s')
         /\
       evaluate_evaluate_decs
         (semanticPrimitives_state_eval_state_fupd (adjust_oracle ci
         (compile_decs o f)) s) env ds =
           (semanticPrimitives_state_eval_state_fupd (adjust_oracle
             ci (compile_decs o f)) s',res))`,
  CHEAT_TAC);;

(* HOL4 source_evalProofScript.sml:2431-2435: a theorem that HOL4
   states as the value of an ML expression: adjust_oracle_ev_decs *)

let adjust_oracle_semantics_prog = prove
 (`!compile' f.
   (!((s:'ffi semanticPrimitives_state)) env ds s' res.
     evaluate_evaluate_decs s env ds = (s',res) /\ ~(res = Rerr
       (Rabort Rtype_error)) ==>
       evaluate_evaluate_decs s env (compile' ds) = (s',res)) ==>
   is_insert_oracle ci f (semanticPrimitives_state_eval_state
     ((s:'ffi semanticPrimitives_state))) /\
   ~(semantics_prog ((s:'ffi semanticPrimitives_state)) env prog
     ffi_Fail) /\
   semantics_prog ((s:'ffi semanticPrimitives_state)) env prog
     outcome ==>
   semantics_prog (semanticPrimitives_state_eval_state_fupd
     (adjust_oracle ci (compile' o f)) ((s:'ffi
     semanticPrimitives_state))) env prog outcome`,
  CHEAT_TAC);;

(* and the names that this file reads as variables are constants again *)
let _ = do_list unhide_constant
  ["compile_decs";
   "id"];;

(* and the accessors of those fields are overloaded again *)
let _ = unhide_overloads ();;
