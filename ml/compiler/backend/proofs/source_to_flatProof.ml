(* ======================================================== *)
(*  source_to_flatProof: ported from HOL4's
    compiler/backend/proofs/source_to_flatProofScript.sml
    A proof theory about source_to_flat.ml, with 48 definitions, 2
    datatypes and 188 theorems.  Needed by backendProof.ml.  *)
(* ======================================================== *)

(*
  Correctness proof for source_to_flat
*)

needs "basis/pure/mlstring.ml";;
needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/flatLang.ml";;
needs "compiler/backend/flat_pattern.ml";;
needs "compiler/backend/pattern_matching/pattern_semantics.ml";;
needs "compiler/backend/proofs/flat_elimProof.ml";;
needs "compiler/backend/proofs/flat_patternProof.ml";;
needs "compiler/backend/proofs/source_evalProof.ml";;
needs "compiler/backend/semantics/backendProps.ml";;
needs "compiler/backend/semantics/flatProps.ml";;
needs "compiler/backend/semantics/flatSem.ml";;
needs "compiler/backend/source_to_flat.ml";;
needs "lib/lprefix_lub.ml";;
needs "lib/sptree.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/namespace.ml";;
needs "semantics/proofs/namespaceProps.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "semantics/semantics.ml";;

(* HOL4 source_to_flatProofScript.sml:20: ML code, not ported *)

(* -- *)

(* value relation *)


(* bind locals with an arbitrary trace *)
let bind_locals_def = cake_define
  `bind_locals ts locals comp_map =
     nsBindList (MAP2 (\t x. (x,source_to_flat_Local t x)) ts
       locals) comp_map`;;

let global_env_FIELDS = define_record "global_env"
  ["v","(flatSem_v option) list";
   "c","((num#num option)#num,stamp)fmap";
   "tys","(num,(num#num) list)fmap"];;

let has_bools_def = cake_define
  `has_bools genv <=>
     FLOOKUP genv ((true_tag,SOME bool_id),0) = SOME (TypeStamp
       (implode "True") bool_type_num) /\
     FLOOKUP genv ((false_tag,SOME bool_id),0) = SOME (TypeStamp
       (implode "False") bool_type_num)`;;

let has_lists_def = cake_define
  `has_lists genv <=>
     FLOOKUP genv ((cons_tag,SOME list_id),2) = SOME (TypeStamp
       (implode "::") list_type_num) /\
     FLOOKUP genv ((nil_tag,SOME list_id),0) = SOME (TypeStamp
       (implode "[]") list_type_num)`;;

let has_exns_def = cake_define
  `has_exns genv <=>
     FLOOKUP genv ((div_tag,NONE),0) = SOME div_stamp /\
     FLOOKUP genv ((chr_tag,NONE),0) = SOME chr_stamp /\
     FLOOKUP genv ((subscript_tag,NONE),0) = SOME subscript_stamp /\
     FLOOKUP genv ((bind_tag,NONE),0) = SOME bind_stamp`;;

let genv_c_ok_def = cake_define
  `genv_c_ok genv_c <=>
     has_bools genv_c /\
     has_exns genv_c /\
     has_lists genv_c /\
     (!cn1 cn2 l1 l2 stamp1 stamp2.
       FLOOKUP genv_c (cn1,l1) = SOME stamp1 /\
       FLOOKUP genv_c (cn2,l2) = SOME stamp2 ==>
       (ctor_same_type (SOME stamp1) (SOME stamp2) <=> ctor_same_type
         (SOME cn1) (SOME cn2))) /\
     (!cn1 cn2 l1 l2 stamp.
       FLOOKUP genv_c (cn1,l1) = SOME stamp /\
       FLOOKUP genv_c (cn2,l2) = SOME stamp ==>
       cn1 = cn2 /\ l1 = l2)`;;

let genv_c_tys_ok_def = cake_define
  `genv_c_tys_ok genv_c genv_tys <=>
   (!cn ty_id arity.
     ((cn,SOME ty_id),arity) IN FDOM genv_c ==>
       (?ctors. FLOOKUP genv_tys ty_id = SOME ctors /\
       MEM (cn,arity) ctors))`;;

let v_rel = cake_inductive
  `(!genv lit.
     source_to_flatProof_v_rel genv ((Litv lit):semanticPrimitives_v)
       ((Litv lit):flatSem_v)) /\
   (!genv cn cn' vs vs'.
     LIST_REL (source_to_flatProof_v_rel genv) vs vs' /\
     FLOOKUP (global_env_c genv) (cn',LENGTH vs) = SOME cn ==>
     source_to_flatProof_v_rel genv (Conv (SOME cn) vs) (Conv (SOME
       cn') vs')) /\
   (!genv vs vs'.
     LIST_REL (source_to_flatProof_v_rel genv) vs vs' ==>
     source_to_flatProof_v_rel genv (Conv NONE vs) (Conv NONE vs'))
       /\
   (!genv comp_map env env_v_local x e env_v_local' t ts.
     source_to_flatProof_env_rel genv env_v_local
       (flatSem_environment_v env_v_local') /\
     global_env_inv genv comp_map (set_of_list (MAP FST
       (flatSem_environment_v env_v_local'))) env /\
     LENGTH ts = LENGTH (flatSem_environment_v env_v_local') + 1 ==>
     source_to_flatProof_v_rel genv
       (Closure (sem_env_v_fupd (K (nsAppend env_v_local (sem_env_v
         env))) env) x e)
       (Closure env_v_local' x
         (compile_exp t
           (source_to_flat_environment_v_fupd (K (bind_locals ts (x
             :: MAP FST (flatSem_environment_v env_v_local'))
             (source_to_flat_environment_v comp_map))) comp_map)
           e))) /\
   (!genv comp_map env env_v_local funs x env_v_local' t ts.
     source_to_flatProof_env_rel genv env_v_local
       (flatSem_environment_v env_v_local') /\
     global_env_inv genv comp_map (set_of_list (MAP FST
       (flatSem_environment_v env_v_local'))) env /\
     LENGTH ts = LENGTH funs + LENGTH (flatSem_environment_v
       env_v_local') ==>
     source_to_flatProof_v_rel genv
       (Recclosure (sem_env_v_fupd (K (nsAppend env_v_local
         (sem_env_v env))) env) funs x)
       (Recclosure env_v_local'
         (compile_funs t
           (source_to_flat_environment_v_fupd (K (bind_locals ts (MAP
             FST funs ++ MAP FST (flatSem_environment_v env_v_local'))
             (source_to_flat_environment_v comp_map))) comp_map) funs)
           x)) /\
   (!genv comp_map env funs flat_env x y e new_vars t1 t2.
     MAP FST new_vars = MAP FST (REVERSE funs) /\
     global_env_inv genv comp_map {} env /\ flatSem_environment_v
     flat_env = [] /\
     find_recfun x funs = SOME (y,e) /\
     (!x. x IN set_of_list (MAP FST funs) ==>
        (?n y e t1 t2 t3.
          ALOOKUP new_vars x = SOME (source_to_flat_Glob t1 n) /\
          n < LENGTH (global_env_v genv) /\
          find_recfun x funs = SOME (y,e) /\
          EL n (global_env_v genv) =
            SOME (Closure flat_env y
                   (compile_exp t2 (source_to_flat_environment_v_fupd
                     (K (nsBindList ((y,source_to_flat_Local t3 y) ::
                     new_vars) (source_to_flat_environment_v comp_map)))
                     comp_map) e)))) ==>
     source_to_flatProof_v_rel genv
       (Recclosure env funs x)
       (Closure flat_env y
         (compile_exp t1
           (source_to_flat_environment_v_fupd (K (nsBindList
             ((y,source_to_flat_Local t2 y) :: new_vars)
             (source_to_flat_environment_v comp_map))) comp_map)
           e))) /\
   (!genv loc b.
     source_to_flatProof_v_rel genv (Loc b loc) (Loc b (loc + 1))) /\
   (!genv vs vs'.
     LIST_REL (source_to_flatProof_v_rel genv) vs vs' ==>
     source_to_flatProof_v_rel genv (Vectorv vs) (Vectorv vs')) /\
   (!genv.
     source_to_flatProof_env_rel genv nsEmpty []) /\
   (!genv x v env env' v'.
     source_to_flatProof_env_rel genv env env' /\
     source_to_flatProof_v_rel genv v v' ==>
     source_to_flatProof_env_rel genv (nsBind x v env) ((x,v') ::
       env')) /\
   (!genv comp_map shadowers env.
     (!x v.
        ~(
        x IN IMAGE Short shadowers) /\
        nsLookup (sem_env_v env) x = SOME v ==>
        (?n v' t.
          nsLookup (source_to_flat_environment_v comp_map) x = SOME
            (source_to_flat_Glob t n) /\
          n < LENGTH (global_env_v genv) /\
          EL n (global_env_v genv) = SOME v' /\
          source_to_flatProof_v_rel genv v v')) /\
     (!x arity stamp.
       nsLookup (sem_env_c env) x = SOME (arity,stamp) ==>
       (?cn ty_gp. nsLookup (source_to_flat_environment_c comp_map) x
         = SOME (cn,ty_gp) /\
         FLOOKUP (global_env_c genv) ((cn,OPTION_MAP FST
           ty_gp),arity) = SOME stamp /\
         (!ty_id ctors. ty_gp = SOME (ty_id,ctors) ==>
             FLOOKUP (global_env_tys genv) ty_id = SOME ctors))) ==>
     global_env_inv genv comp_map shadowers env)`;;
hol4_overload "env_rel" "source_to_flatProof_env_rel";;
hol4_overload "v_rel" "source_to_flatProof_v_rel";;

(* HOL4 source_to_flatProofScript.sml:275-334: code that the source
   has in a comment *)

let subglobals_def = cake_define
  `subglobals g1 g2 <=>
     LENGTH g1 <= LENGTH g2 /\
     (!n. n < LENGTH g1 /\ IS_SOME (EL n g1) ==> EL n g1 = EL n
       g2)`;;

let result_rel = cake_inductive
  `(!genv v v'.
     f genv v v' ==>
     source_to_flatProof_result_rel f genv (Rval v) (Rval v')) /\
   (!genv v v'.
     source_to_flatProof_v_rel genv v v' ==>
     source_to_flatProof_result_rel f genv (Rerr (Rraise v)) (Rerr
       (Rraise v'))) /\
   (!genv a.
     source_to_flatProof_result_rel f genv (Rerr (Rabort a)) (Rerr
       (Rabort a)))`;;
hol4_overload "result_rel" "source_to_flatProof_result_rel";;

let sv_rel = cake_inductive
  `(!genv v v'.
     source_to_flatProof_v_rel genv v v' ==>
     source_to_flatProof_sv_rel genv (semanticPrimitives_Refv v)
       (semanticPrimitives_Refv v')) /\
   (!genv w.
     source_to_flatProof_sv_rel genv (semanticPrimitives_W8array w)
       (semanticPrimitives_W8array w)) /\
   (!genv vs vs'.
     LIST_REL (source_to_flatProof_v_rel genv) vs vs' ==>
     source_to_flatProof_sv_rel genv (semanticPrimitives_Varray vs)
       (semanticPrimitives_Varray vs')) /\
   (!genv m v v'.
     source_to_flatProof_v_rel genv v v' ==>
     source_to_flatProof_sv_rel genv (semanticPrimitives_Thunk m
       v) (semanticPrimitives_Thunk m v'))`;;
hol4_overload "sv_rel" "source_to_flatProof_sv_rel";;

let s_rel = cake_inductive
  `(!genv s s'.
     ~NULL (state_refs s') /\
     LIST_REL (sv_rel genv) (state_refs s) (TL (state_refs s')) /\
       state_clock
     s = state_clock s' /\ state_ffi
     s = state_ffi s' ==>
     source_to_flatProof_s_rel genv s s')`;;
hol4_overload "s_rel" "source_to_flatProof_s_rel";;

let env_all_rel = cake_inductive
  `(!genv map' env_v_local env env' locals.
     (?l. env_v_local = alist_to_ns l /\ MAP FST l = locals) /\
     global_env_inv genv map' (set_of_list locals) env /\
     env_rel genv env_v_local env' ==>
     env_all_rel genv map'
       (mk_sem_env (nsAppend env_v_local (sem_env_v env)) (sem_env_c
         env))
       (mk_flatSem_environment env')
       locals)`;;

let match_result_rel_def = cake_define
  `source_to_flatProof_match_result_rel genv env' x3 x4 =
        match (x3,x4) with
          (Match env,Match env_i1) ->
        (?env''. env = env'' ++ env' /\ env_rel genv (alist_to_ns
          env'') env_i1)
        | (No_match,No_match) -> T
        | (Match_type_error,_1) -> T
        | (_2,_3) -> F`;;
hol4_overload "match_result_rel"
  "source_to_flatProof_match_result_rel";;

(* semantic functions respect relation *)

(* HOL4 source_to_flatProofScript.sml:1061-1062: the ML values that
   the definitions below antiquote *)

(* compiler correctness *)

let env_domain_eq_def = cake_define
  `env_domain_eq (var_map:source_to_flat_environment) (env:'a sem_env)
  <=>
     nsDom (source_to_flat_environment_v var_map) = nsDom (sem_env_v
       env) /\
     nsDomMod (source_to_flat_environment_v var_map) = nsDomMod
       (sem_env_v env) /\
     nsDom (source_to_flat_environment_c var_map) = nsDom (sem_env_c
       env) /\
     nsDomMod (source_to_flat_environment_c var_map) = nsDomMod
       (sem_env_c env)`;;

(* HOL4 source_to_flatProofScript.sml:2022: ML code, not ported *)

let idx_prev_def = cake_define
  `idx_prev idx idx2 <=> next_indices_vidx
   idx <= next_indices_vidx idx2 /\ next_indices_tidx idx <=
     next_indices_tidx idx2 /\ next_indices_eidx idx <=
     next_indices_eidx idx2`;;

let idx_types_INDUCT,idx_types_RECURSION = define_datatype
  "idx_types = Idx_Var | Idx_Type | Idx_Exn";;

let ALL_DISJOINT_DEF = cake_define
  `ALL_DISJOINT xs <=>
   (!i j. i < LENGTH xs /\ j < LENGTH xs /\ ~(i = j) ==> EL i xs
     INTER EL j xs = {})`;;

let idx_block_def = cake_define
  `idx_block start_idx end_idx =
   {(i,Idx_Var) | next_indices_vidx start_idx <= i /\ i <
     next_indices_vidx end_idx} UNION
   {(i,Idx_Type) | next_indices_tidx start_idx <= i /\ i <
     next_indices_tidx end_idx} UNION
   {(i,Idx_Exn) | next_indices_eidx start_idx <= i /\ i <
     next_indices_eidx end_idx}`;;

let idx_final_block_def = cake_define
  `idx_final_block start_idx =
   {(i,Idx_Var) | next_indices_vidx start_idx <= i} UNION
   {(i,Idx_Type) | next_indices_tidx start_idx <= i} UNION
   {(i,Idx_Exn) | next_indices_eidx start_idx <= i}`;;

let genv_allocated_idxs_def = cake_define
  `genv_allocated_idxs genv =
      {(i,Idx_Var) | i < LENGTH (global_env_v genv) /\ ~(EL i
        (global_env_v genv) = NONE)} UNION
         {(i,Idx_Type) | ?cn a. ((cn,SOME i),a) IN FDOM (global_env_c
           genv)} UNION
         {(i,Idx_Type) | i IN FDOM (global_env_tys genv)} UNION
         {(i,Idx_Exn) | ?a. ((i,NONE),a) IN FDOM (global_env_c
           genv)}`;;

(* simple invariants on env generations and stores: allocation from the
   next field will always be free *)
let env_gen_inv_def = cake_define
  `env_gen_inv (e:environment_generation_store) =
     (domain (envs e) SUBSET count (next e))`;;

let env_store_inv_def = cake_define
  `env_store_inv (e:environment_store) =
     (domain (environment_store_env_gens e) SUBSET count (next e))`;;

(* The source oracle states can always be decoded according to the
   optional decode function provided. The state
   part of the oracle sequence should be what is produced by repeatedly
   applying compile_prog *)
let src_orac_step_invs_def = cake_define
  `src_orac_step_invs ci (g:dec list->dec list) eval_state =
   (match (ci,eval_state) with (NONE,NONE) -> T | (SOME dec,SOME
     (EvalOracle s)) -> (
     (!k env_id state_v decs. oracle s k = (env_id,state_v,decs) ==>
         (?c x. dec state_v = SOME (c,x))) /\
     (let c_orac = FST o THE o dec o FST o SND o oracle s in
     (!k env_id state_v decs. oracle s k = (env_id,state_v,decs) ==>
         c_orac (SUC k) = FST (inc_compile_prog env_id (c_orac k)
           (g decs))))) | _4 -> F)`;;

(* the flatLang oracle is derived from the source oracle by compile_prog,
   and the two compile oracles agree also *)
let orac_rel_inner_def = cake_define
  `orac_rel_inner dec s (s_compiler:compiler_fun) (g:dec list->dec
  list) c <=>
     (!k env_id state_v decs. eval_oracle_state_oracle s k =
       (env_id,state_v,decs) ==>
         (let x = THE (dec state_v) in
         let f_decs = SND (inc_compile_prog env_id (FST x) (g decs))
           in install_config_compile_oracle
         c k = (SND x,f_decs) /\
         (~(s_compiler (env_id,state_v,decs) = NONE) ==>
             (?bytes words f_st st_v2. install_config_compile
             c (SND x) f_decs = SOME (bytes,words,f_st) /\
             s_compiler (env_id,state_v,decs) = SOME
               (st_v2,bytes,words) /\
             (!x2. dec st_v2 = SOME x2 ==> SND x2 = f_st)))))`;;

let orac_rel_def = cake_define
  `orac_rel interp g src_eval flat_eval <=> (match (interp,src_eval)
  with (_5,NONE) -> T | (SOME dec,SOME (EvalOracle s)) -> (
     ?s_compiler. eval_oracle_state_custom_do_eval
     s = do_eval_oracle s_compiler g /\
     orac_rel_inner dec s s_compiler g flat_eval) | _6 -> F)`;;

let src_orac_next_cfg_inner_def = cake_define
  `src_orac_next_cfg_inner interp orac_0 = (match (interp,orac_0) with
  (SOME dec,(env_id,state_v,decs)) ->
       (match dec state_v with SOME (c,x) -> SOME c | _7 -> NONE)
         | _8 -> NONE)`;;

let src_orac_next_cfg_def = cake_define
  `src_orac_next_cfg interp eval_state = (match eval_state with SOME
  (EvalOracle s) -> src_orac_next_cfg_inner interp (oracle s 0) | _9
  -> NONE)`;;

(* every env stored in the eval state is related to a concrete env
   representation in the next oracle state *)
let src_orac_env_invs_def = cake_define
  `src_orac_env_invs interp genv eval_state = (match eval_state with
  NONE -> T | SOME (EvalOracle s) ->
     (?c. src_orac_next_cfg interp eval_state = SOME c /\
       env_store_inv (envs c) /\ next (envs
       c) = LENGTH (envs s) /\
       (!g_id id'. g_id < LENGTH (envs s) /\ id' < LENGTH (EL g_id
         (envs s)) ==>
         (?comp_map_gen comp_map.
         sptree_lookup g_id (environment_store_env_gens (envs c)) =
           SOME comp_map_gen /\
         sptree_lookup id' comp_map_gen = SOME comp_map /\
         global_env_inv genv comp_map {} (EL id' (EL g_id (envs
           s)))))) | _10 -> F)`;;

let src_orac_gen_inv_def = cake_define
  `src_orac_gen_inv eval_state = (match eval_state with NONE -> T | SOME
  (EvalOracle s) -> generation
     s < LENGTH (envs s))`;;

let src_orac_invs_def = cake_define
  `src_orac_invs interp g genv eval_state <=>
   src_orac_step_invs interp g eval_state /\
   src_orac_env_invs interp genv eval_state /\
   src_orac_gen_inv eval_state`;;

(* the current generation of envs in the compiler state matches that
   generation in oracle state - this one is tricky, because it will stop
   being true for a while if some declaration are never executed because
   of an exception that is later handled *)
let env_gen_rel_def = cake_define
  `env_gen_rel gen eval_state = (match eval_state with NONE -> T | SOME
  (EvalOracle s) -> generation
         gen = generation s /\ generation
         s < LENGTH (envs s) /\ next
         gen = LENGTH (EL (generation s) (envs s)) | _11 -> F)`;;

(* the oracle state is in the future, where this generation
   has already been compiled and its environments saved *)
let env_gen_future_rel_def = cake_define
  `env_gen_future_rel interp gen eval_state =
     (match src_orac_next_cfg interp eval_state with SOME c ->
       (?gen_final.
         sptree_lookup (generation gen) (environment_store_env_gens
           (envs c)) = SOME gen_final /\
         subspt (envs gen) gen_final) | NONE -> T)`;;

(* indexes and ranges: the source-to-flat compiler allocates names in order.
   however, evaluation order is different to compile order. each block of
   decs is compiled together, but evaluated one at a time, and evaluation may
   call Eval and jump to the processing of another block.
   so, index parameters (idx, end_idx, others) and fin_idx:
     - idx .. end_idx are the indices used in this block
     - fin_idx is the final state after all completed compilation, so the
        indices after fin_idx are still available
       + fin_idx changes with each Eval, so we keep it out of the index tuple
         to make the invariant (and inductive hyps) easier to instantiate
     - other blocks may be on the stack of dec blocks being evaluated
   all of those blocks of indices are disjoint, and they are also disjoint
   from those indices that have actually been initialised. *)
let idx_range_rel_def = cake_define
  `idx_range_rel interp genv s_n_ts s_n_en s_eval idxs <=>
     (?idx end_idx fin_idx other_blocks.
     idxs = (idx,end_idx,other_blocks) /\
     (match src_orac_next_cfg interp s_eval with NONE -> T | SOME c
       -> fin_idx = next c) /\
     idx_prev end_idx fin_idx /\
     ALL_DISJOINT [idx_block idx end_idx; idx_final_block fin_idx;
       other_blocks;
         genv_allocated_idxs genv] /\
     (!cn t. t >= s_n_ts ==> ~(TypeStamp cn t IN FRANGE (global_env_c
       genv))) /\
     (!cn. cn >= s_n_en ==> ~(ExnStamp cn IN FRANGE (global_env_c
       genv))))`;;

(* in eval mode, the length of the allocated globals space will end at the
   next vidx available for the next compilation. if no eval config, we've
   lost that information, but the prior end index will be before *)
let fin_idx_match_def = cake_define
  `fin_idx_match len end_idx next_cfg = (match next_cfg with NONE ->
  next_indices_vidx end_idx <= len | SOME c -> next_indices_vidx
  (next c) = len)`;;

let eval_ref_inv_def = cake_define
  `eval_ref_inv first_global first_ref <=>
   first_global = [SOME (Loc T 0)] /\
   (?v. first_ref = [semanticPrimitives_Refv v])`;;

let invariant_def = cake_define
  `source_to_flatProof_invariant interp g gen genv idxs s s_i1 <=>
     genv_c_ok (global_env_c genv) /\
     genv_c_tys_ok (global_env_c genv) (global_env_tys genv) /\
     s_rel genv s s_i1 /\
     idx_range_rel interp genv
       (semanticPrimitives_state_next_type_stamp s)
       (semanticPrimitives_state_next_exn_stamp
          s) (semanticPrimitives_state_eval_state s) idxs /\
     src_orac_invs interp g genv (semanticPrimitives_state_eval_state
       s) /\
     orac_rel interp g (semanticPrimitives_state_eval_state s)
       (flatSem_state_eval_config s_i1) /\ global_env_v
     genv = flatSem_state_globals s_i1 /\
     eval_ref_inv (TAKE 1 (flatSem_state_globals s_i1)) (TAKE 1
       (state_refs s_i1)) /\
     env_gen_inv gen /\
     fin_idx_match (LENGTH (flatSem_state_globals s_i1)) (FST (SND
       idxs))
         (src_orac_next_cfg interp
           (semanticPrimitives_state_eval_state s))`;;
hol4_overload "invariant" "source_to_flatProof_invariant";;

(* subsequent oracle config will still have the previous envs in store *)
let orac_config_envs_subspt_def = cake_define
  `orac_config_envs_subspt interp es1 es2 <=>
     OPTREL (\c c'. subspt (environment_store_env_gens (envs c))
       (environment_store_env_gens (envs c')))
     (src_orac_next_cfg interp es1)
     (src_orac_next_cfg interp es2)`;;

(* this relation holds over any successful evaluate or evaluate_decs
   - the eval generation stack will be back to the same generation
*)
let eval_state_call_rel_def = cake_define
  `eval_state_call_rel es1 es2 <=>
     (match es1 with SOME (EvalOracle s1) -> (?s2. es2 = SOME
       (EvalOracle s2) /\ generation
         s2 = generation s1 /\
         LENGTH (envs s1) <= LENGTH (envs s2) /\
         (!i. i < generation s1 ==> EL i (envs s2) = EL i (envs
           s1))) | _12 -> T)`;;

let orac_forward_rel_def = cake_define
  `orac_forward_rel interp es1 es2 <=>
   orac_config_envs_subspt interp es1 es2 /\
   eval_state_call_rel es1 es2`;;

(* HOL4 source_to_flatProofScript.sml:2424-2426: ML code, not ported *)

(* FIXME also in flat_pattern *)

(* HOL4 source_to_flatProofScript.sml:3704-3706: the ML values that
   the definitions below antiquote *)

(* HOL4 source_to_flatProofScript.sml:3708-3710: the ML values that
   the definitions below antiquote *)

let abort_def = cake_define
  `source_to_flatProof_abort r <=> (match r with Rerr (Rabort a) -> T
  | _13 -> F)`;;
hol4_overload "abort" "source_to_flatProof_abort";;

(* HOL4 source_to_flatProofScript.sml:3869-3870: ML code, not ported *)

(* HOL4 source_to_flatProofScript.sml:3872-3897: a proof *)

(* HOL4 source_to_flatProofScript.sml:3899-3913: a proof *)

(* HOL4 source_to_flatProofScript.sml:3915-3935: a proof *)

(* HOL4 source_to_flatProofScript.sml:3937-3946: a proof *)
    (* tuple *)
(* HOL4 source_to_flatProofScript.sml:3948-3953: a proof *)
  (* named constructor *)
(* HOL4 source_to_flatProofScript.sml:3955-3968: a proof *)

(* HOL4 source_to_flatProofScript.sml:3970-4023: a proof *)

(* HOL4 source_to_flatProofScript.sml:4025-4038: a proof *)

(* HOL4 source_to_flatProofScript.sml:4145-4153: a proof *)
    (* empty array creation *)
(* HOL4 source_to_flatProofScript.sml:4155-4187: a proof *)
    (* Rerr *)
(* HOL4 source_to_flatProofScript.sml:4189-4282: a proof *)
    (* Opapp *)
(* HOL4 source_to_flatProofScript.sml:4284-4294: a proof *)
      (* out of clock *)
(* HOL4 source_to_flatProofScript.sml:4296-4490: a proof *)

(* HOL4 source_to_flatProofScript.sml:4492-4527: a proof *)

(* HOL4 source_to_flatProofScript.sml:4529-4550: a proof *)

(* HOL4 source_to_flatProofScript.sml:4552-4575: a proof *)

(* HOL4 source_to_flatProofScript.sml:4577-4585: a proof *)
    (* anonymous bind *)
(* HOL4 source_to_flatProofScript.sml:4587-4623: a proof *)

(* HOL4 source_to_flatProofScript.sml:4625-4660: a proof *)

(* HOL4 source_to_flatProofScript.sml:4662-4699: a proof *)

(* HOL4 source_to_flatProofScript.sml:4701: a proof *)
  (* no decs *)
(* HOL4 source_to_flatProofScript.sml:4703-4706: a proof *)

(* HOL4 source_to_flatProofScript.sml:4751: a proof *)
  (* sequence of decs *)
(* HOL4 source_to_flatProofScript.sml:4753-4800: a proof *)

(* HOL4 source_to_flatProofScript.sml:4802-4888: a proof *)

(* HOL4 source_to_flatProofScript.sml:4890-4929: a proof *)

(* HOL4 source_to_flatProofScript.sml:4931-4966: a proof *)
(* HOL4 source_to_flatProofScript.sml:4967: code that the source has
   in a comment *)
(* HOL4 source_to_flatProofScript.sml:4968-4991: a proof *)

(* HOL4 source_to_flatProofScript.sml:4993-4997: a proof *)

(* HOL4 source_to_flatProofScript.sml:4999-5004: a proof *)
    (* incorrect eval state type *)
(* HOL4 source_to_flatProofScript.sml:5006-5101: a proof *)

(* HOL4 source_to_flatProofScript.sml:5103-5163: a proof *)

(* HOL4 source_to_flatProofScript.sml:5165-5189: a proof *)

(* HOL4 source_to_flatProofScript.sml:5191-5216: a proof *)
  (* result case *)
(* HOL4 source_to_flatProofScript.sml:5218-5229: a proof *)

(* HOL4 source_to_flatProofScript.sml:5231: a proof *)

let init_eval_state_ok_def = cake_define
  `init_eval_state_ok x1 =
        match x1 with
          NONE -> T
        | (SOME (EvalDecs _14)) -> F
        | (SOME (EvalOracle s)) -> generation
       s = 0 /\ envs s = [[]]`;;

let init_genv_ty_els_def = cake_define
  `init_genv_ty_els = [
     (bool_id,[(false_tag,0,TypeStamp (implode "False")
       bool_type_num);
         (true_tag,0,TypeStamp (implode "True") bool_type_num)]);
     (list_id,REVERSE [(cons_tag,2,TypeStamp (implode "::")
       list_type_num);
         (nil_tag,0,TypeStamp (implode "[]") list_type_num)])]`;;

let init_genv_els_def = cake_define
  `init_genv_els = FLAT (MAP (\(id',xs).
         MAP (\(tag,arity,stamp). (((tag,SOME id'),arity),stamp)) xs)
     init_genv_ty_els) ++ [
     (((div_tag,NONE),0),div_stamp);
     (((chr_tag,NONE),0),chr_stamp);
     (((subscript_tag,NONE),0),subscript_stamp);
     (((bind_tag,NONE),0),bind_stamp)]`;;

let init_genv_def = cake_define
  `init_genv = mk_global_env [] (FEMPTY |++ init_genv_els) (FEMPTY
  |++ MAP (I ## MAP (I ## FST)) init_genv_ty_els)`;;

let init_genv_next = cake_define
  `init_genv_next = mk_next_indices 0 (SUC (MAX_LIST (MAP (\v. match
  SND v with TypeStamp _15 i -> i | _16 -> 0) init_genv_els))) (SUC
  (MAX_LIST (MAP (\v. match SND v with ExnStamp i -> i | _17 -> 0)
  init_genv_els)))`;;

let init_global_env_inv_def = cake_define
  `init_global_env_inv genv comp_map env <=> sem_env_v
   env = nsEmpty /\
   (match sem_env_c env with Bind ns ms -> ms = [] /\
     EVERY (\(x,(arity,stamp)). match nsLookup
       (source_to_flat_environment_c comp_map) (Short x) with
       NONE -> F | SOME (cn,ty_gp) ->
         FLOOKUP (global_env_c genv) ((cn,OPTION_MAP FST
           ty_gp),arity) = SOME stamp /\
         (match ty_gp with NONE -> T | SOME (ty_id,ctors) ->
             FLOOKUP (global_env_tys genv) ty_id = SOME ctors))
               ns)`;;

let precondition1_def = cake_define
  `precondition1 interp g s1 env1 conf eval_conf prog <=>
   src_orac_step_invs interp g (semanticPrimitives_state_eval_state
     s1) /\
   orac_rel interp g (semanticPrimitives_state_eval_state s1)
     eval_conf /\
   (match src_orac_next_cfg interp
     (semanticPrimitives_state_eval_state s1) with NONE -> T | SOME cfg
     -> cfg = FST (source_to_flat_compile_prog conf prog)) /\
     next_indices_vidx (next
   conf) = 0 /\ state_refs
   s1 = [] /\
   init_global_env_inv init_genv (source_to_flat_config_mod_env conf)
     env1 /\
   init_eval_state_ok (semanticPrimitives_state_eval_state s1) /\
   idx_prev init_genv_next (next conf) /\
   EVERY (\(_18,stamp). match stamp with TypeStamp cn t -> t <
     semanticPrimitives_state_next_type_stamp s1 | ExnStamp cn -> cn <
     semanticPrimitives_state_next_exn_stamp s1) init_genv_els /\ envs
   conf = envs empty_config`;;

(* - connect semantics theorems of flat-to-flat passes --------------------- *)

let precondition_def = cake_define
  `precondition interp s env cfg ec prog <=>
   (?ec1 g. precondition1 interp g s env cfg ec1 prog /\
     install_conf_rel (source_to_flat_config_pattern_cfg cfg) ec1
       ec)`;;

(* - esgc_free theorems for compile_exp ------------------------------------ *)

(* - esgc_free theorems for compile_decs ----------------------------------- *)

(* - the source_to_flat compiler produces things which are esgc_free ------- *)

let _ = size_thms "dec";;
let num_bindings_def = cake_define_wf
  `MEASURE dec_size`
  `num_bindings x1 =
        match x1 with
          Dlet _19 p e ->
        (match simple_dlet p e with SOME _20 -> 0 | _21 -> LENGTH
          (pat_bindings p))
        | (Dletrec _22 f) -> LENGTH f
        | (Dmod _23 ds) -> SUM (MAP num_bindings ds)
        | (Dlocal lds ds) ->
           SUM (MAP num_bindings lds) + SUM (MAP num_bindings ds)
        | (Denv _24) -> 1
        | _25 -> 0`;;

(* HOL4 source_to_flatProofScript.sml:5824-5825: ML code, not ported *)

(* not sure if this variant of the inc. compiler is the one we need *)
