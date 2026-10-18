(* ======================================================== *)
(*  source_evalProof: ported from HOL4's
    compiler/backend/proofs/source_evalProofScript.sml  *)
(* ======================================================== *)

(*
  Proofs that the eval mode of the source semantics can
  be switched to one that includes an oracle.
*)

needs "lib/peg.ml";;
needs "semantics/ast.ml";;
needs "semantics/evaluate.ml";;
needs "semantics/namespace.ml";;
needs "semantics/proofs/evaluateProps.ml";;
needs "semantics/proofs/namespaceProps.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "semantics/semantics.ml";;
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

let env_rel_def = cake_define
  `source_evalProof_env_rel v_rel' (env:semanticPrimitives_v sem_env)
  env' <=> sem_env_c
     env = sem_env_c env' /\ nsDom (sem_env_v env) = nsDom (sem_env_v
       env') /\
     nsDomMod (sem_env_v env) = nsDomMod (sem_env_v env') /\
     (!nm x y. nsLookup (sem_env_v env) nm = SOME x /\ nsLookup
       (sem_env_v env') nm = SOME y ==>
         v_rel' x y)`;;
hol4_overload "env_rel" "source_evalProof_env_rel";;

(* HOL4 source_evalProofScript.sml:106: ML code, not ported *)

(* HOL4 source_evalProofScript.sml:150: ML code, not ported *)


(* various trivia *)

(* HOL4 source_evalProofScript.sml:208: the ML values that the
   definitions below antiquote *)

(* first step. switch over to recording semantics and move envs
   out of Env values and into the state *)

let v_rel = cake_inductive
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
   (0 = FST (FST (oracle orac_s' 0)) ==>
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

(* a stronger notion that applies end-to-end over
   evaluate/evaluate_decs,
   where the generation stack will match at either end and the previous
   generations will be untouched. *)
let es_stack_forward_def = cake_define
  `es_stack_forward es es' <=> eval_oracle_state_generation
   es' = eval_oracle_state_generation es /\
   (!j. j < eval_oracle_state_generation es ==> EL j
     (eval_oracle_state_envs es') = EL j (eval_oracle_state_envs es))`;;

let match_result_rel_def = cake_define
  `source_evalProof_match_result_rel nerr R mr1 mr2 <=> (match mr1
  with No_match -> mr2 = No_match | Match_type_error -> nerr \/ mr2 =
  Match_type_error | Match x -> (?y. mr2 = Match y /\ R x y))`;;
hol4_overload "match_result_rel" "source_evalProof_match_result_rel";;

(* HOL4 source_evalProofScript.sml:373: the ML values that the
   definitions below antiquote *)

let abort_def = cake_define
  `source_evalProof_abort r <=> (match r with Rerr (Rabort a) -> T |
  _9 -> F)`;;
hol4_overload "abort" "source_evalProof_abort";;

(* case splits for evaluate proofs *)
(* HOL4 source_evalProofScript.sml:931-936: ML code, not ported *)

(* take a step of forward-consistency-type reasoning *)
(* HOL4 source_evalProofScript.sml:939-941: ML code, not ported *)

(* quantifier instantiation based on s_rel, v_rel etc *)
(* HOL4 source_evalProofScript.sml:944-957: ML code, not ported *)

(* HOL4 source_evalProofScript.sml:1049-1224: ML code, not ported *)

(* HOL4 source_evalProofScript.sml:1226-1256: ML code, not ported *)

(* HOL4 source_evalProofScript.sml:1258-1266: ML code, not ported *)

(* HOL4 source_evalProofScript.sml:1268-1280: ML code, not ported *)

(* HOL4 source_evalProofScript.sml:1282-1295: ML code, not ported *)

(* HOL4 source_evalProofScript.sml:1297-1309: ML code, not ported *)

(* HOL4 source_evalProofScript.sml:1311-1326: ML code, not ported *)

(* HOL4 source_evalProofScript.sml:1328-1340: ML code, not ported *)

(* HOL4 source_evalProofScript.sml:1358-1366: ML code, not ported *)

(* HOL4 source_evalProofScript.sml:1368-1373: ML code, not ported *)

(* HOL4 source_evalProofScript.sml:1375-1383: ML code, not ported *)

(* HOL4 source_evalProofScript.sml:1385: ML code, not ported *)

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

let is_record_def = cake_define
  `is_record ci es <=> (match es with SOME (EvalOracle s) ->
  eval_oracle_state_custom_do_eval
         s = do_eval_record ci | _17 -> F)`;;

(* HOL4 source_evalProofScript.sml:1624-1626: ML code, not ported *)

(* HOL4 source_evalProofScript.sml:1628-1630: ML code, not ported *)

(* HOL4 source_evalProofScript.sml:1632-1636: ML code, not ported *)

(* HOL4 source_evalProofScript.sml:1638-1641: ML code, not ported *)

(* HOL4 source_evalProofScript.sml:1643: ML code, not ported *)

(* HOL4 source_evalProofScript.sml:1702-1706: ML code, not ported *)
    (* Eval *)
(* HOL4 source_evalProofScript.sml:1708-1730: ML code, not ported *)
    (* Opapp *)
(* HOL4 source_evalProofScript.sml:1732-1748: ML code, not ported *)

(* HOL4 source_evalProofScript.sml:1750-1755: ML code, not ported *)

(* HOL4 source_evalProofScript.sml:1757: ML code, not ported *)

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

let precond_eval_state_def = cake_define
  `precond_eval_state orac ci s env decs = (match
  semanticPrimitives_state_eval_state s with NONE -> T | SOME (EvalDecs
  eds) -> EvalDecs eds = mk_init_eval_state ci /\
         (orac_extended_wf (mk_compiler_fun_from_ci ci) orac) /\
         (!i r x. get_oracle ci s env decs i = SOME r /\
           mk_compiler_fun_from_ci ci r = SOME x ==>
             orac i = r) | SOME (EvalOracle _19) -> F)`;;

(* for use in source-to-source phases, a proof that the oracle can be
   adjusted
   by any stateless compiler *)

let adjust_oracle_def = cake_define
  `adjust_oracle ci f es = (match es with
     NONE -> es | SOME (EvalDecs _20) -> es | SOME (EvalOracle o_s)
       -> SOME (EvalOracle
         (eval_oracle_state_custom_do_eval_fupd (K (do_eval_oracle
           (mk_compiler_fun_from_ci ci) f)) o_s)))`;;

(* HOL4 source_evalProofScript.sml:2249: the overload
   s_adjust_oracle, which the port expands *)

let is_insert_oracle_def = cake_define
  `is_insert_oracle ci f es = (?es' shift_f orac. es =
  insert_gen_oracle ci f shift_f orac es')`;;
