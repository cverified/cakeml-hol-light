(* ======================================================== *)
(*  source_to_flatProof: ported from HOL4's
    compiler/backend/proofs/source_to_flatProofScript.sml  *)
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

(* HOL4 ML code, not ported:
val build_rec_env_merge = flatPropsTheory.build_rec_env_merge;
*)

(* -- *)

(* value relation *)


(* bind locals with an arbitrary trace *)
let bind_locals_def = cake_define
  `bind_locals ts locals comp_map =
     nsBindList (MAP2 (\t x. (x,Local t x)) ts locals) comp_map`;;

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
          ALOOKUP new_vars x = SOME (Glob t1 n) /\
          n < LENGTH (global_env_v genv) /\
          find_recfun x funs = SOME (y,e) /\
          EL n (global_env_v genv) =
            SOME (Closure flat_env y
                   (compile_exp t2 (source_to_flat_environment_v_fupd
                     (K (nsBindList ((y,Local t3 y) :: new_vars)
                     (source_to_flat_environment_v comp_map))) comp_map)
                     e)))) ==>
     source_to_flatProof_v_rel genv
       (Recclosure env funs x)
       (Closure flat_env y
         (compile_exp t1
           (source_to_flat_environment_v_fupd (K (nsBindList
             ((y,Local t2 y) :: new_vars) (source_to_flat_environment_v
             comp_map))) comp_map)
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
            (Glob t n) /\
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

(*
Theorem v_rel_eqns:
   (!genv l v.
    v_rel genv (Litv l) v ⇔
      (v = Litv l)) ∧
   (!genv vs v.
    v_rel genv (Conv cn vs) v ⇔
      ?vs' cn'.
        LIST_REL (v_rel genv) vs vs' ∧
        v = Conv cn' vs' ∧
        case cn of
        | NONE => cn' = NONE
        | SOME cn =>
          ?cn2. cn' = SOME cn2 ∧ FLOOKUP genv.c (cn2, LENGTH vs) = SOME
            cn) ∧
   (!genv l v b.
    v_rel genv (Loc b l) v ⇔
      (v = Loc b l)) ∧
   (!genv vs v.
    v_rel genv (Vectorv vs) v ⇔
      ?vs'. LIST_REL (v_rel genv) vs vs' ∧ (v = Vectorv vs')) ∧
   (!genv fp v.
      v_rel genv (FP_WordTree fp) v <=>
      v = Litv (Word64 (compress_word fp))) /\
   (! genv fp v cn.
      v_rel genv (FP_BoolTree fp) v <=>
      FLOOKUP (genv.c) (((if (compress_bool fp) then true_tag else
        false_tag),SOME bool_id), 0) =
        SOME (TypeStamp (if (compress_bool fp) then «True» else «False»)
          bool_type_num) /\
      v = Boolv (compress_bool fp)) /\
   (!genv env'.
    env_rel genv nsEmpty env' ⇔
      env' = []) ∧
   (!genv x v env env'.
    env_rel genv (nsBind x v env) env' ⇔
      ?v' env''. v_rel genv v v' ∧ env_rel genv env env'' ∧ env' =
        ((x,v')::env'')) ∧
   (!genv comp_map shadowers env.
    global_env_inv genv comp_map shadowers env ⇔
      (!x v.
       x ∉ IMAGE Short shadowers ∧
       nsLookup env.v x = SOME v
       ⇒
       ?n v' t.
         nsLookup comp_map.v x = SOME (Glob t n) ∧
         n < LENGTH genv.v ∧
         EL n genv.v = SOME v' ∧
         v_rel genv v v') ∧
      (!x arity stamp.
        nsLookup env.c x = SOME (arity, stamp) ⇒
        ∃cn. nsLookup comp_map.c x = SOME cn ∧
          FLOOKUP genv.c (cn,arity) = SOME stamp))
Proof
  srw_tac[][semanticPrimitivesTheory.Boolv_def,flatSemTheory.Boolv_def]
    >>
  srw_tac[][Once v_rel_cases] >>
  srw_tac[][Q.SPECL[`genv`,`nsEmpty`](CONJUNCT1(CONJUNCT2 v_rel_cases))]
    >>
  srw_tac[][flatSemTheory.Boolv_def, semanticPrimitivesTheory.Boolv_def]
    >>
  every_case_tac >>
  fs [genv_c_ok_def, has_bools_def] >>
  TRY eq_tac >>
  rw [] >>
  metis_tac []
*)

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

let s_rel = cake_inductive
  `(!genv s s'.
     ~NULL (state_refs s') /\
     LIST_REL (sv_rel genv) (state_refs s) (TL (state_refs s')) /\
       state_clock
     s = state_clock s' /\ state_ffi
     s = state_ffi s' ==>
     source_to_flatProof_s_rel genv s s')`;;

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

(* HOL4 ML code, not ported:
val s_i1 = ``s_i1 : ('f_orac_st, 'ffi) flatSem$state``;
val s1_i1 = mk_var ("s1_i1", type_of s_i1);
*)

(* compiler correctness *)

let env_domain_eq_def = cake_define
  `env_domain_eq (var_map:source_to_flat_environment) (env:'a sem_env)
  <=>
     nsDom (global_env_v var_map) = nsDom (sem_env_v env) /\
     nsDomMod (global_env_v var_map) = nsDomMod (sem_env_v env) /\
     nsDom (global_env_c var_map) = nsDom (sem_env_c env) /\
     nsDomMod (global_env_c var_map) = nsDomMod (sem_env_c env)`;;

(* HOL4 ML code, not ported:
val result_rel_imp = hd (RES_CANON result_rel_cases);
*)

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

(* the flatLang oracle is derived from the source oracle by
   compile_prog,
   and the two compile oracles agree also *)
let orac_rel_inner_def = cake_define
  `orac_rel_inner dec s (s_compiler:(num#num)#flatSem_v#dec
  list->(flatSem_v#word8 list#word64 list) option) (g:dec list->dec
  list) c <=>
     (!k env_id state_v decs. oracle s k = (env_id,state_v,decs) ==>
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

(* indexes and ranges: the source-to-flat compiler allocates names in
   order.
   however, evaluation order is different to compile order. each block
     of
   decs is compiled together, but evaluated one at a time, and
     evaluation may
   call Eval and jump to the processing of another block.
   so, index parameters (idx, end_idx, others) and fin_idx:
     - idx .. end_idx are the indices used in this block
     - fin_idx is the final state after all completed compilation, so
       the
        indices after fin_idx are still available
       + fin_idx changes with each Eval, so we keep it out of the index
         tuple
         to make the invariant (and inductive hyps) easier to
           instantiate
     - other blocks may be on the stack of dec blocks being evaluated
   all of those blocks of indices are disjoint, and they are also
     disjoint
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

(* in eval mode, the length of the allocated globals space will end at
   the
   next vidx available for the next compilation. if no eval config,
     we've
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

(* subsequent oracle config will still have the previous envs in store
   *)
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

(* HOL4 ML code, not ported:
val s = mk_var("s",
  ``evaluate$evaluate`` |> type_of |> strip_fun |> #1 |> el 1
  |> type_subst[alpha |-> ``:'ffi``]);
*)

(* FIXME also in flat_pattern *)

(* HOL4 ML code, not ported:
val extend_env_v_empty =
  ``extend_env <| c := c; v := nsEmpty |> <| c := c'; v := nsEmpty |>``
  |> SIMP_CONV (srw_ss ()) [extend_env_def];
*)

(* HOL4 ML code, not ported:
val extend_dec_env_v_empty =
  ``extend_dec_env <| c := c; v := nsEmpty |> <| c := c'; v := nsEmpty
    |>``
  |> SIMP_CONV (srw_ss ()) [extend_dec_env_def];
*)

let abort_def = cake_define
  `source_to_flatProof_abort r <=> (match r with Rerr (Rabort a) -> T
  | _13 -> F)`;;
hol4_overload "abort" "source_to_flatProof_abort";;

(* HOL4 ML code, not ported:
val trans_thms = [SUBMAP_TRANS, SUBSET_TRANS,
    subglobals_trans, orac_forward_rel_trans];
*)

(* HOL4 ML code, not ported:
Resume compile_correct[seq]:
  rw []
  \\ fs [pair_case_eq] \\ fs []
  \\ first_x_assum (drule_then (drule_then drule))
  \\ disch_then (qspec_then ‘t’ mp_tac)
  \\ reverse (fs [result_case_eq])
  >- (
    rw []
    \\ fs [result_rel_cases]
    \\ asm_exists_tac \\ simp []
  )
  \\ fs [pair_case_eq]
  \\ rveq \\ fs []
  \\ rw []
  \\ fs [result_rel_cases]
  \\ rveq \\ fs []
  \\ drule_then drule env_all_rel_weak
  \\ rw []
  \\ first_x_assum (drule_then (drule_then drule))
  \\ disch_then (qspec_then ‘t’ mp_tac)
  \\ simp []
  \\ impl_tac >- (CCONTR_TAC >> fs [])
  \\ imp_res_tac evaluate_sing \\ fs [] \\ rveq \\ fs []
  \\ rw [] \\ fs [] \\ rveq \\ fs []
  \\ metis_tac (v_rel_weak :: trans_thms)
QED
*)

(* HOL4 ML code, not ported:
Resume compile_correct[Raise]:
  rw []
  \\ fs [pair_case_eq]
  \\ rveq \\ fs []
  \\ first_x_assum (drule_then (drule_then drule))
  \\ disch_then (qspec_then ‘t’ mp_tac)
  \\ simp []
  \\ impl_tac >- (CCONTR_TAC \\ fs [])
  \\ rw []
  \\ fs [result_rel_cases] \\ rveq \\ fs [] \\ rveq \\ fs []
  \\ imp_res_tac evaluatePropsTheory.evaluate_sing
  \\ imp_res_tac evaluate_sing
  \\ rveq \\ fs []
  \\ asm_exists_tac \\ simp []
QED
*)

(* HOL4 ML code, not ported:
Resume compile_correct[Handle]:
  rw []
  \\ fs [pair_case_eq] \\ fs []
  \\ first_x_assum (drule_then (drule_then drule))
  \\ disch_then (qspec_then ‘t’ mp_tac)
  \\ simp []
  \\ impl_tac >- (CCONTR_TAC \\ fs [])
  \\ rw []
  \\ imp_res_tac result_rel_imp \\ fs [] \\ rveq \\ fs []
  \\ TRY (asm_exists_tac \\ simp [])
  \\ fs [bool_case_eq, Q.ISPEC `(a, b)` EQ_SYM_EQ]
  \\ drule_then drule env_all_rel_weak
  \\ rw []
  \\ first_x_assum (drule_then drule)
  \\ rpt (disch_then drule)
  \\ disch_then (first_assum o mp_then (Pat `v_rel`) mp_tac)
  \\ disch_then (qspec_then ‘t’ mp_tac)
  \\ DEP_REWRITE_TAC [GEN_ALL can_pmatch_all_IMP_pmatch_rows]
  \\ rw [] \\ fs []
  \\ metis_tac trans_thms
QED
*)

(* HOL4 ML code, not ported:
Resume compile_correct[Con]:
  rw []
  \\ fs [pair_case_eq] \\ fs []
  \\ first_x_assum (drule_then (drule_then drule))
  \\ disch_then (qspec_then ‘t’ mp_tac)
  \\ simp []
  \\ impl_tac >- (CCONTR_TAC \\ fs [])
  \\ rw []
  \\ fs [do_con_check_def, opt_case_bool_eq, EXISTS_PROD]
  >- (
*)
    (* tuple *)
(* HOL4 ML code, not ported:
    rfs [build_conv_def, compile_exps_reverse, evaluate_def]
    \\ imp_res_tac result_rel_imp \\ fs [] \\ rveq \\ fs
      [result_rel_eqns]
    \\ simp [v_rel_eqns]
    \\ goal_assum (first_assum o mp_then (Pat `s_rel`) mp_tac)
    \\ simp []
  )
*)
  (* named constructor *)
(* HOL4 ML code, not ported:
  \\ rveq \\ fs [build_conv_def, compile_exps_reverse, evaluate_def]
  \\ fs [env_all_rel_cases] \\ rveq \\ fs []
  \\ fs [v_rel_global_eqn]
  \\ first_x_assum drule
  \\ rw [EXISTS_PROD]
  \\ simp [type_group_id_type_MAP, evaluate_def]
  \\ imp_res_tac result_rel_imp \\ fs [] \\ rveq \\ fs [result_rel_eqns]
  \\ fs [option_case_eq, pair_case_eq] \\ rveq \\ fs []
  \\ goal_assum (qsubterm_then `s_rel _ _ _` mp_tac)
  \\ simp [v_rel_eqns, result_rel_eqns]
  \\ imp_res_tac evaluatePropsTheory.evaluate_length
  \\ fs []
  \\ metis_tac [FLOOKUP_SUBMAP]
QED
*)

(* HOL4 ML code, not ported:
Resume compile_correct[Var]:
  rw []
  \\ fs [option_case_eq]
  \\ fs [env_all_rel_cases]
  \\ rveq \\ fs []
  \\ fs [nsLookup_nsAppend_some]
  >- ((* Local variable *)
    fs [nsLookup_alist_to_ns_some,bind_locals_def] >>
    rw [] >>
    drule env_rel_lookup >>
    disch_then drule >>
    rw [GSYM nsAppend_to_nsBindList] >>
    simp[MAP2_MAP]>>
    every_case_tac >>
    fs [nsLookup_nsAppend_some, nsLookup_nsAppend_none,
      nsLookup_alist_to_ns_some,
        nsLookup_alist_to_ns_none,evaluate_def]>>
    fs[ALOOKUP_NONE,MAP_MAP_o,o_DEF,LAMBDA_PROD]>>
    `(λ(p1:tra,p2:tvarN). p2) = SND` by fs[FUN_EQ_THM,FORALL_PROD]>>
    fs[]>>rfs[MAP_ZIP]
    >- metis_tac [ALOOKUP_MEM,PAIR,FST,MEM_MAP, SUBMAP_REFL,
      subglobals_refl]
    >- metis_tac [ALOOKUP_MEM,PAIR,FST,MEM_MAP, SUBMAP_REFL,
      subglobals_refl]
    >- (
      drule ALOOKUP_MEM >>
      rw [MEM_MAP] >>
      pairarg_tac>>fs[compile_var_def]>>
      simp [evaluate_def, result_rel_cases] >>
      metis_tac [SUBMAP_REFL, subglobals_refl])
    >- metis_tac [ALOOKUP_MEM,PAIR,FST,MEM_MAP])
  >- ( (* top-level variable *)
    rw [GSYM nsAppend_to_nsBindList,bind_locals_def] >>
    fs [nsLookup_alist_to_ns_none] >>
    fs [v_rel_global_eqn, ALOOKUP_NONE, METIS_PROVE [] ``~x ∨ y ⇔ x ⇒
      y``] >>
    first_x_assum drule >>
    rw [] >>
    simp[MAP2_MAP]>>
    every_case_tac >>
    fs [nsLookup_nsAppend_some, nsLookup_nsAppend_none,
      nsLookup_alist_to_ns_some,
        nsLookup_alist_to_ns_none]>>
    fs[ALOOKUP_NONE,MAP_MAP_o,o_DEF,LAMBDA_PROD]
    >- (Cases_on`p1`>>fs[])
    >- (
      drule ALOOKUP_MEM >>
      simp[MEM_MAP,MEM_ZIP,EXISTS_PROD]>>
      rw[]>>
      metis_tac[MEM_EL,LENGTH_MAP])
    >- (
      rfs [ALOOKUP_TABULATE] >>
      rw [] >>
      simp [evaluate_def, result_rel_cases,compile_var_def] >>
      simp [do_app_def] >>
      imp_res_tac invariant_globals >>
      fs [] >>
      metis_tac [subglobals_refl, SUBMAP_REFL]))
QED
*)

(* HOL4 ML code, not ported:
Resume compile_correct[Fun]:
  rw [Once v_rel_cases] >>
  goal_assum (first_assum o mp_then (Pat `invariant`) mp_tac) >>
  fs [env_all_rel_cases, subglobals_refl] >>
  srw_tac[][] >>
  rename [`global_env_inv genv comp_map (set (MAP FST locals)) env`] >>
  MAP_EVERY qexists_tac [`comp_map`, `env`, `alist_to_ns
    locals`,`t`,`None::ts`] >>
  imp_res_tac env_rel_dom >>
  srw_tac[][] >>
  simp [bind_locals_def, namespaceTheory.nsBindList_def] >>
  fs [ADD1]
  >- metis_tac [sem_env_eq_lemma]
  >- metis_tac[LENGTH_MAP]
QED
*)

(* HOL4 ML code, not ported:
Resume compile_correct[App]:
  rpt disch_tac
  \\ fs [pair_case_eq] \\ fs []
  \\ first_x_assum (drule_then (drule_then drule))
  \\ disch_then (qspec_then ‘t’ mp_tac)
  \\ simp []
  \\ (impl_tac >- (CCONTR_TAC \\ fs []))
  \\ Cases_on `op = AallocEmpty`
  >- (
*)
    (* empty array creation *)
(* HOL4 ML code, not ported:
    rw []
    \\ fs [semanticPrimitivesTheory.do_app_def,
      astTheory.getOpClass_def]
    \\ every_case_tac \\ fs [] \\ rveq \\ fs []
    >- (
      drule (CONJUNCT1 evaluatePropsTheory.evaluate_length) >>
      rw [] >>
      fs [LENGTH_EQ_NUM_compute] >>
      rveq >> fs [] >>
      simp [compile_exp_def, evaluate_def] >>
      pairarg_tac >>
      fs [store_alloc_def, compile_exp_def] >>
      rpt var_eq_tac >>
      fs [result_rel_cases, Once v_rel_cases] >>
      simp [do_app_def] >>
      pairarg_tac >>
      fs [store_alloc_def] >>
      goal_assum (first_assum o mp_then (Pat `subglobals`) mp_tac) >>
      fs [invariant_def, s_rel_cases] >>
      imp_res_tac NOT_NULL_EQ >>
      rveq >> fs [ADD1] >>
      imp_res_tac LIST_REL_LENGTH >>
      simp [REPLICATE, sv_rel_cases])
    >- (
      rw []
      \\ fs [compile_exps_reverse]
      \\ fs [result_rel_cases] \\ rveq \\ fs []
      \\ drule_then (simp o single) evaluate_foldr_let_err
      \\ goal_assum (first_assum o mp_then (Pat `s_rel`) mp_tac)
      \\ simp []
      )
  )
  \\ reverse (fs [result_case_eq]) \\ rveq \\ fs []
  >- (
*)
    (* Rerr *)
(* HOL4 ML code, not ported:
    rw [evaluate_def]
    \\ fs [compile_exps_reverse, result_rel_cases]
    \\ goal_assum (first_assum o mp_then (Pat `s_rel`) mp_tac)
    \\ simp []
    \\ rpt (CASE_TAC \\ fs [])
    \\ gvs [compile_exp_def, evaluate_def]
  )
  \\ Cases_on `op = Eval`
  >- (
    rw[]
    \\ fs [evaluateTheory.do_eval_res_def, astTheory.getOpClass_def]
    \\ fs [astOp_to_flatOp_def, evaluate_def, compile_exps_reverse,
        evaluate_decs_append, miscTheory.opt_bind_def]
    \\ fs [list_case_eq, option_case_eq, pair_case_eq]
    \\ rveq \\ fs []
    \\ imp_res_tac result_rel_imp \\ fs [result_rel_cases]
    \\ rveq \\ fs []
    \\ fs [compile_exps_reverse, pair_case_eq]
    \\ drule_then drule (Q.SPEC `REVERSE ys` do_eval)
    \\ simp []
    \\ disch_then drule
    \\ rw []
    \\ simp [pmatch_rows_drop_4, pat_bindings_def]
    \\ simp [evaluate_def, drop_4_via_el]
    \\ drule_then assume_tac invariant_dec_clock
    \\ fs [bool_case_eq] \\ rveq \\ fs []
    >- (
      fs [invariant_def]
      \\ goal_assum (qsubterm_then `s_rel _ _` mp_tac)
      \\ fs [s_rel_cases]
    )
    \\ fs [Q.ISPEC `(a, b)` EQ_SYM_EQ, pair_case_eq]
    \\ fs [inc_compile_prog_def]
    \\ rpt (pairarg_tac \\ fs [])
    \\ rveq \\ fs []
    \\ simp [glob_alloc_def, evaluate_def, do_app_def, Unitv_def]
    \\ first_x_assum (qsubterm_then `compile_decs _ _ _ _ _ _` mp_tac)
    \\ fs [dec_clock_def, evaluateTheory.dec_clock_def]
    \\ rfs []
    \\ disch_then drule
    \\ simp [idx_prev_refl]
    \\ impl_tac >- (
      rpt strip_tac \\ fs []
    )
    \\ rw []
    \\ fs [evaluate_decs_append]
    \\ reverse (fs [result_case_eq, error_result_case_eq])
    \\ rveq \\ fs [] \\ fsrw_tac [SATISFY_ss] []
    >- (
      rveq \\ fs []
      \\ drule_then (drule_then drule) invariant_end_eval
      \\ rw []
      \\ asm_exists_tac
      \\ imp_res_tac invariant_IMP_s_rel
      \\ simp []
      \\ metis_tac trans_thms
    )
    \\ fs [option_case_eq, pair_case_eq] \\ rveq \\ fs []
    \\ drule_then drule declare_env_store_env_id
    \\ simp []
    \\ impl_tac >- (
      qpat_x_assum `orac_forward_rel _ _ _` mp_tac
      \\ rw [orac_forward_rel_def, orac_config_envs_subspt_def]
      \\ fs [OPTREL_SOME, subspt_lookup, lookup_insert]
      \\ imp_res_tac compile_decs_generation
      \\ fs []
      \\ first_x_assum (qsubterm_then `lookup _ _.envs.env_gens` mp_tac)
      \\ rw []
      \\ irule global_env_inv_append
      \\ simp []
      \\ drule_then irule global_env_inv_weak
      \\ fsrw_tac [SATISFY_ss] trans_thms
    )
    \\ rw []
    \\ simp [store_lookup_def]
    \\ drule_then drule invariant_end_eval
    \\ simp []
    \\ disch_then (qsubterm_then `orac_config_envs_subspt _ _ _` mp_tac)
    \\ impl_tac >- (
      simp []
      \\ drule_then irule orac_forward_rel_trans
      \\ simp []
    )
    \\ rw []
    \\ simp [miscTheory.opt_bind_def]
    \\ asm_exists_tac
    \\ simp []
    \\ drule_then (qsubterm_then `invariant _ _ _ _ _ _ _` mp_tac)
        invariant_change_eval_ref
    \\ simp []
    \\ metis_tac (invariant_IMP_s_rel :: trans_thms)
  )
  \\ Cases_on `op = Opapp`
  >- (
*)
    (* Opapp *)
(* HOL4 ML code, not ported:
    fs [Q.ISPEC `(a, b)` EQ_SYM_EQ, pair_case_eq, option_case_eq,
      astTheory.getOpClass_def] >>
    rw [] >>
    rveq >> fs [] >>
    fs [astOp_to_flatOp_def, evaluate_def, compile_exps_reverse] >>
    fs [result_rel_eqns] >> rveq >> fs [] >>
    drule_then assume_tac EVERY2_REVERSE >>
    drule_then drule do_opapp >>
    rw [] >>
    imp_res_tac invariant_dec_clock >>
    rw []
    >- (
*)
      (* out of clock *)
(* HOL4 ML code, not ported:
      fs [] >> rveq >> fs [] >>
      simp [result_rel_eqns] >>
      asm_exists_tac >>
      simp []
    ) >>
    fs [Q.ISPEC `(a, b)` EQ_SYM_EQ] >>
    first_x_assum (drule_then (drule_then drule)) >>
    simp [dec_clock_def] >>
    disch_then (qsubterm_then `evaluate _ _ _` mp_tac) >>
    rw [] >>
    fs [evaluateTheory.dec_clock_def, dec_clock_def] >>
    metis_tac (SUBSET_TRANS :: trans_thms)
  )
  \\ Cases_on `op = Env_id`
  >- (
    fs [option_case_eq, pair_case_eq, result_rel_eqns,
      astTheory.getOpClass_def]
    \\ rw []
    \\ fs [semanticPrimitivesTheory.do_app_def]
    \\ fs [case_eq_thms, semanticPrimitivesTheory.v_case_eq,
      pair_case_eq]
    \\ rveq \\ fs []
    \\ fs [v_rel_eqns]
    \\ rveq \\ fs []
    \\ imp_res_tac evaluate_length
    \\ fs [compile_exps_length]
    \\ fs [LENGTH_EQ_NUM_compute]
    \\ fs [compile_exp_def]
    \\ rw [result_rel_eqns, v_rel_eqns]
    \\ asm_exists_tac \\ fs []
    \\ fs [invariant_def, s_rel_cases]
  ) >>
  Cases_on ‘getOpClass op’ >> gs[]
  >- (
    Cases_on ‘op’ >> gs[astTheory.getOpClass_def] >>
    Cases_on ‘t'’ >> gvs[])
  >- (
    Cases_on ‘op’ >> gs[astTheory.getOpClass_def] >>
    Cases_on ‘t'’ >> gvs[])
  >~ [‘getOpClass op = Force’]
  >- (
    Cases_on ‘op’ >> gvs[astTheory.getOpClass_def] >>
    Cases_on ‘t'’ >> gvs[] >>
    gvs[AllCaseEqs(), evaluateTheory.dec_clock_def,
      flatSemTheory.dec_clock_def,
        PULL_EXISTS] >> rw[]
    >- (
      gvs[astOp_to_flatOp_def, evaluate_def, compile_exps_reverse,
          AllCaseEqs()] >>
      qpat_x_assum `result_rel _ _ _ r_i1` mp_tac >>
      rw[Once result_rel_cases] >>
      gvs[oneline semanticPrimitivesTheory.dest_thunk_def, AllCaseEqs()]
        >>
      rgs[Once v_rel_cases] >> gvs[] >>
      simp[dest_thunk_def, AllCaseEqs(), PULL_EXISTS] >>
      gvs[store_lookup_def, s_rel_cases, LIST_REL_EL_EQN] >>
      `∃v''. EL n (TL s'_i1.refs) = Thunk Evaluated v'' ∧
             v_rel genv' v v''` by (
        first_x_assum (qspec_then`n` mp_tac) >>
        gvs[] >> rw[Once sv_rel_cases]) >>
      simp[REWRITE_RULE [ADD1] EL, Once result_rel_cases] >>
      goal_assum drule >> rw[])
    >- (
      gvs[astOp_to_flatOp_def, evaluate_def, compile_exps_reverse,
          AllCaseEqs()] >>
      qpat_x_assum `result_rel _ _ _ r_i1` mp_tac >>
      rw[Once result_rel_cases] >>
      gvs[oneline semanticPrimitivesTheory.dest_thunk_def, AllCaseEqs()]
        >>
      rgs[Once v_rel_cases] >> gvs[] >>
      simp[dest_thunk_def, AllCaseEqs(), PULL_EXISTS] >>
      gvs[store_lookup_def, s_rel_cases, LIST_REL_EL_EQN] >>
      `∃v'. EL n (TL s'_i1.refs) = Thunk NotEvaluated v' ∧
             v_rel genv' v v'` by (
        first_x_assum (qspec_then`n` mp_tac) >>
        gvs[] >> rw[Once sv_rel_cases]) >>
      simp[REWRITE_RULE [ADD1] EL, Once result_rel_cases, PULL_EXISTS]
        >>
      simp[AppUnit_def, dec_clock_def] >>
      ntac 5 $ simp[Once evaluate_def] >>
      drule do_opapp >> simp[PULL_EXISTS] >>
      disch_then drule >> simp[Once v_rel_cases] >> strip_tac >> gvs[]
        >>
      goal_assum drule >> simp[]
      )
    >- (
      gvs[astOp_to_flatOp_def, evaluate_def, compile_exps_reverse,
          AllCaseEqs()] >>
      qpat_x_assum `result_rel _ _ _ r_i1` mp_tac >>
      rw[Once result_rel_cases] >>
      gvs[oneline semanticPrimitivesTheory.dest_thunk_def, AllCaseEqs()]
        >>
      rgs[Once v_rel_cases] >> gvs[] >>
      simp[dest_thunk_def, AllCaseEqs(), PULL_EXISTS] >>
      gvs[store_lookup_def, s_rel_cases, LIST_REL_EL_EQN] >>
      `∃v'. EL n (TL s'_i1.refs) = Thunk NotEvaluated v' ∧
             v_rel genv' v v'` by (
        first_x_assum (qspec_then`n` mp_tac) >>
        gvs[] >> rw[Once sv_rel_cases]) >>
      simp[REWRITE_RULE [ADD1] EL, Once result_rel_cases, PULL_EXISTS]
        >>
      simp[AppUnit_def, dec_clock_def] >>
      ntac 5 $ simp[Once evaluate_def] >>
      drule do_opapp >> simp[PULL_EXISTS] >>
      disch_then drule >> simp[Once v_rel_cases] >> strip_tac >> gvs[]
        >>
      dxrule invariant_dec_clock >> strip_tac >>
      gvs[evaluateTheory.dec_clock_def, flatSemTheory.dec_clock_def] >>
      last_x_assum drule_all >> disch_then $ qspec_then ‘t1’ assume_tac
        >> gvs[] >>
      gvs[Once result_rel_cases] >>
      gvs[oneline semanticPrimitivesTheory.update_thunk_def,
          oneline flatSemTheory.update_thunk_def, AllCaseEqs()] >>
      `dest_thunk [y] s'_i1'.refs = NotThunk` by (
        qpat_x_assum `v_rel _ v'3' y` mp_tac >>
        Cases_on `v'3'` >> Cases_on `y` >>
        rw[Once v_rel_cases, dest_thunk_def, Boolv_def] >>
        gvs[semanticPrimitivesTheory.dest_thunk_def, store_lookup_def]
          >>
        reverse $ rw []
        >- (Cases_on `s'_i1'.refs` >> gvs []) >>
        `n' < LENGTH s'_i1'.refs -1` by (Cases_on `s'_i1'.refs` >>
          gvs[]) >>
        gvs[] >>
        first_x_assum drule >> simp[REWRITE_RULE [ADD1] EL] >>
        Cases_on `EL n' st2.refs` >> Cases_on `EL n' (TL s'_i1'.refs)`
          >>
        rw[Once sv_rel_cases] >> gvs[] >> Cases_on `t'` >> gvs[]) >>
          gvs[] >>
      Cases_on `s'_i1'.refs` >> gvs[] >>
      qexists `genv'3'` >> gvs[] >>
      imp_res_tac SUBMAP_TRANS >> gvs[] >>
      imp_res_tac subglobals_trans >> gvs[] >>
      gvs[store_assign_def, store_v_same_type_def, REWRITE_RULE [ADD1]
        EL] >>
      rw[]
      >- (
        first_x_assum drule >>
        Cases_on `EL n st2.refs` >> Cases_on `EL n t'` >> gvs[] >>
        rw[Once sv_rel_cases])
      >- rw[REWRITE_RULE [ADD1] LUPDATE_def]
      >- (
        rw[REWRITE_RULE [ADD1] LUPDATE_def, EL_LUPDATE] >>
        simp[Once sv_rel_cases])
      >- (
        rw[REWRITE_RULE [ADD1] LUPDATE_def] >>
        gvs[invariant_def] >>
        rw[REWRITE_RULE [ADD1] LUPDATE_def] >>
        gvs[s_rel_cases, LIST_REL_EL_EQN] >>
        rw[EL_LUPDATE] >> simp[Once sv_rel_cases])
      >- (
        gvs[evaluateTheory.dec_clock_def] >>
        drule_then irule orac_forward_rel_trans >> gvs[])
      )
    >- (
      gvs[astOp_to_flatOp_def, evaluate_def, compile_exps_reverse,
          AllCaseEqs()] >>
      qpat_x_assum `result_rel _ _ _ r_i1` mp_tac >>
      rw[Once result_rel_cases] >>
      gvs[oneline semanticPrimitivesTheory.dest_thunk_def, AllCaseEqs()]
        >>
      rgs[Once v_rel_cases] >> gvs[] >>
      simp[dest_thunk_def, AllCaseEqs(), PULL_EXISTS] >>
      gvs[store_lookup_def, s_rel_cases, LIST_REL_EL_EQN] >>
      `∃v'. EL n (TL s'_i1.refs) = Thunk NotEvaluated v' ∧
             v_rel genv' v v'` by (
        first_x_assum (qspec_then`n` mp_tac) >>
        gvs[] >> rw[Once sv_rel_cases]) >>
      simp[REWRITE_RULE [ADD1] EL, Once result_rel_cases, PULL_EXISTS]
        >>
      simp[AppUnit_def, dec_clock_def] >>
      ntac 5 $ simp[Once evaluate_def] >>
      drule do_opapp >> simp[PULL_EXISTS] >>
      disch_then drule >> simp[Once v_rel_cases] >> strip_tac >> gvs[]
        >>
      dxrule invariant_dec_clock >> strip_tac >>
      gvs[evaluateTheory.dec_clock_def, flatSemTheory.dec_clock_def] >>
      last_x_assum drule_all >> disch_then $ qspec_then ‘t1’ assume_tac
        >> gvs[] >>
      qpat_x_assum `result_rel _ _ _ r_i1` mp_tac >> rw[Once
        result_rel_cases] >>
      goal_assum drule >> simp[] >>
      imp_res_tac SUBMAP_TRANS >> gvs[] >>
      imp_res_tac subglobals_trans >> gvs[] >>
      drule_then irule orac_forward_rel_trans >> gvs[]
      )) >>
  fs [Q.ISPEC `(a, b)` EQ_SYM_EQ, option_case_eq, pair_case_eq] >>
  rw [] >>
  rveq >> fs [] >>
  fs [result_rel_eqns] >> rveq >> fs [] >>
  drule_then assume_tac EVERY2_REVERSE >>
  imp_res_tac s_rel_cases >>
  drule do_app >> simp [] >>
  rpt (disch_then drule) >>
  (impl_tac >- fs [invariant_def, s_rel_cases]) >>
  rw [] >>
  `astOp_to_flatOp op ≠ Src Opapp ∧ astOp_to_flatOp op ≠ Src Eval ∧
   astOp_to_flatOp op ≠ Src (ThunkOp ForceThunk)`
  by (
    rw [astOp_to_flatOp_def] >>
    Cases_on `op` >>
    simp [] >>
    fs [astTheory.getOpClass_def] >>
    Cases_on `t'` >> gvs []) >>
  fs [evaluate_def, compile_exps_reverse] >>
  imp_res_tac do_app_state_unchanged >>
  imp_res_tac do_app_const >>
  rename [`result_rel v_rel genv2`] >>
  qexists_tac `genv2` >>
  simp [] >>
  conj_tac >> TRY (fs [result_rel_cases] \\ NO_TAC) >>
  fs [invariant_def, s_rel_cases] >>
  rpt (TOP_CASE_TAC >> gs[result_rel_cases,
    semanticPrimitivesTheory.Boolv_def, Boolv_def, v_rel_eqns]) >>
  TRY COND_CASES_TAC >> gs[] >>
  simp[ Once v_rel_rules]
QED
*)

(* HOL4 ML code, not ported:
Resume compile_correct[Log]:
  rw [] >>
  fs [pair_case_eq] >> fs [] >>
  first_x_assum (drule_then (drule_then drule)) >>
  disch_then (qspec_then ‘t’ mp_tac) >>
  simp [] >>
  impl_tac >- ( strip_tac >> full_simp_tac(srw_ss())[] ) >>
  rw [] >>
  reverse (fs [result_case_eq]) >> rveq >> fs []
  >- (
    goal_assum (qsubterm_then `invariant _ _ _ _` mp_tac) >>
    fs [result_rel_cases] >> rveq >> fs [] >>
    every_case_tac >>
    simp [evaluate_def]
  ) >>
  imp_res_tac evaluatePropsTheory.evaluate_sing >>
  reverse (fs [option_case_eq, exp_or_val_case_eq, result_rel_eqns])
  >- (
    rveq >> fs [] >>
    fs [evaluate_def, do_if_def, do_log_def, bool_case_eq] >> rveq >> fs
      [] >>
    goal_assum (qsubterm_then `invariant _ _ _ _` mp_tac) >>
    fs [invariant_def, v_rel_Bool_eqn, Boolv_11] >>
    drule_then (fn t => simp [t]) evaluate_Bool >>
    simp [result_rel_eqns, v_rel_Bool_eqn]
  ) >>
  fs [] >> rveq >> fs [] >>
  drule_then drule env_all_rel_weak >>
  rw [] >>
  first_x_assum (drule_then (drule_then drule)) >>
  disch_then (qspec_then ‘t’ mp_tac) >>
  rw [] >>
  goal_assum (qsubterm_then `invariant _ _ _ _` mp_tac) >>
  fs [evaluate_def, do_if_def, do_log_def, bool_case_eq] >> rveq >> fs
    [] >>
  fs [invariant_def, v_rel_Bool_eqn, Boolv_11] >>
  metis_tac trans_thms
QED
*)

(* HOL4 ML code, not ported:
Resume compile_correct[If]:
  rw [] >> fs [pair_case_eq] >> fs [] >>
  first_x_assum (drule_then (drule_then drule)) >>
  disch_then (qspec_then ‘t’ mp_tac) >>
  simp [] >>
  (impl_tac >- (CCONTR_TAC >> fs [])) >>
  rw [] >>
  imp_res_tac result_rel_imp >> rveq >> fs [] >> rveq >> fs
    [result_rel_eqns] >>
  TRY (asm_exists_tac >> simp [] >> NO_TAC) >>
  fs [option_case_eq] >> fs [] >>
  drule_then drule env_all_rel_weak >>
  rw [] >>
  first_x_assum (drule_then (drule_then drule)) >>
  disch_then (qspec_then ‘t’ mp_tac) >>
  rw [] >>
  imp_res_tac evaluatePropsTheory.evaluate_sing >>
  goal_assum (qsubterm_then `invariant _ _ _ _` mp_tac) >>
  fs [semanticPrimitivesTheory.do_if_def, bool_case_eq] >> rveq >> fs []
    >>
  fs [invariant_def, do_if_def] >>
  rfs [v_rel_Bool_eqn, Boolv_11] >>
  metis_tac trans_thms
QED
*)

(* HOL4 ML code, not ported:
Resume compile_correct[Mat]:
  rw [] \\ fs [pair_case_eq] \\ fs []
  \\ first_x_assum (drule_then (drule_then drule))
  \\ disch_then (qspec_then ‘t’ mp_tac)
  \\ simp []
  \\ (impl_tac >- (CCONTR_TAC >> fs []))
  \\ rw []
  \\ imp_res_tac result_rel_imp \\ fs [] \\ rveq \\ fs [result_rel_eqns]
  \\ TRY (asm_exists_tac \\ simp [])
  \\ fs [bool_case_eq, Q.ISPEC `(a, b)` EQ_SYM_EQ]
  \\ imp_res_tac evaluatePropsTheory.evaluate_sing
  \\ fs [] \\ rveq \\ fs []
  \\ drule_then drule env_all_rel_weak
  \\ rw []
  \\ first_x_assum (drule_then (drule_then (drule_then drule)))
  \\ disch_then (qspec_then `bind_exn_v` mp_tac)
  \\ disch_then (qspec_then ‘t’ mp_tac)
  \\ DEP_REWRITE_TAC [GEN_ALL can_pmatch_all_IMP_pmatch_rows]
  \\ conj_tac >- metis_tac []
  \\ impl_tac >- (fs [invariant_def, v_rel_lems])
  \\ rw []
  \\ simp []
  \\ metis_tac trans_thms
QED
*)

(* HOL4 ML code, not ported:
Resume compile_correct[Let]:
  rw [] \\ fs [pair_case_eq] \\ fs []
  \\ first_x_assum (drule_then (drule_then drule))
  \\ simp [GSYM PULL_FORALL]
  \\ (impl_tac >- (CCONTR_TAC >> fs []))
  \\ rw []
  \\ rename [`Let opt_name _ _`]
  \\ Cases_on `opt_name`
  >- (
*)
    (* anonymous bind *)
(* HOL4 ML code, not ported:
    pop_assum (qspec_then ‘t’ strip_assume_tac)
    \\ simp [compile_exp_def, evaluate_def]
    \\ imp_res_tac result_rel_imp \\ fs [] \\ rveq \\ fs
      [result_rel_eqns]
    \\ TRY (asm_exists_tac \\ simp [])
    \\ fs [namespaceTheory.nsOptBind_def]
    \\ drule_then drule env_all_rel_weak
    \\ rw []
    \\ first_x_assum (drule_then (drule_then drule))
    \\ disch_then (qspec_then ‘t’ mp_tac)
    \\ rw []
    \\ simp [Q.prove (`env with v updated_by opt_bind NONE x = env`,
          simp [environment_component_equality,miscTheory.opt_bind_def]
            )]
    \\ metis_tac trans_thms
  )
  \\ pop_assum (qspec_then ‘x::t’ strip_assume_tac)
  \\ simp [compile_exp_def, evaluate_def]
  \\ imp_res_tac result_rel_imp \\ fs [] \\ rveq \\ fs [result_rel_eqns]
  \\ TRY (asm_exists_tac \\ simp [])
  \\ drule_then drule env_all_rel_weak
  \\ rw []
  \\ imp_res_tac evaluate_sing
  \\ fs [] \\ rveq \\ fs []
  \\ simp [bind_locals_fold_nsBind]
  \\ last_x_assum mp_tac
  \\ disch_then (qsubterm_then `evaluate _ _ _ ` mp_tac)
  \\ disch_then drule
  \\ impl_tac >- (
    fs [env_all_rel_cases]
    \\ fs [namespaceTheory.nsOptBind_def, miscTheory.opt_bind_def]
    \\ simp [PULL_EXISTS, listTheory.MAP_EQ_CONS, EXISTS_PROD]
    \\ metis_tac [env_rel_bind_one, pred_setTheory.INSERT_SING_UNION,
      global_env_inv_add_locals]
  )
  \\ rw []
  \\ simp []
  \\ metis_tac trans_thms
QED
*)

(* HOL4 ML code, not ported:
Resume compile_correct[Letrec]:
  rw [] >> fs [pair_case_eq] >>
  rw [evaluate_def] >>
  TRY (fs [compile_funs_map,MAP_MAP_o,o_DEF,UNCURRY] >>
       full_simp_tac(srw_ss())[FST_triple,ETA_AX] >>
       NO_TAC) >>
  fs [GSYM nsAppend_to_nsBindList] >>
  rw_tac std_ss [GSYM MAP_APPEND] >>
  simp[nsAppend_bind_locals]>>
  first_x_assum match_mp_tac >> simp[] >>
  full_simp_tac(srw_ss())[env_all_rel_cases] >>
  rw [] >>
  qexists_tac `build_rec_env funs <|v := nsAppend (alist_to_ns l)
    env'.v; c := env'.c|> (alist_to_ns l)` >>
  qexists_tac `env'` >>
  rw [semanticPrimitivesPropsTheory.build_rec_env_merge
    ,build_rec_env_merge]
  >- (
    simp [MAP_MAP_o, UNCURRY, combinTheory.o_DEF] >>
    metis_tac [])
  >- metis_tac [global_env_inv_add_locals] >>
  rw_tac std_ss [GSYM nsAppend_alist_to_ns] >>
  match_mp_tac env_rel_append >>
  rw [compile_funs_map, MAP_MAP_o, combinTheory.o_DEF, UNCURRY] >>
  rw [env_rel_el, EL_MAP, UNCURRY] >>
  simp [Once v_rel_cases] >>
  qexists_tac `comp_map` >>
  qexists_tac `env'` >>
  qexists_tac `alist_to_ns l` >>
  qexists_tac `t` >>
  qexists_tac `REPLICATE (LENGTH funs) None ++ ts` >>
  drule env_rel_dom >>
  rw [compile_funs_map, MAP_MAP_o, combinTheory.o_DEF, UNCURRY,
      bind_locals_def, nsAppend_to_nsBindList] >>
  rw [sem_env_component_equality]
  >- metis_tac[]
  >- metis_tac [LENGTH_MAP]
QED
*)

(* HOL4 ML code, not ported:
Resume compile_correct[pattern]:
  rw [] >> fs [pair_case_eq] >>
  drule_then drule pmatch_invariant >>
  disch_then (qsubterm_then `pmatch _ _ _ _` mp_tac) >>
  simp [] >>
  disch_then drule >>
  strip_tac >>
  imp_res_tac match_result_rel_imp >> fs []
  >- (
    last_x_assum (qsubterm_then `evaluate_match _ _ _ _ _` mp_tac) >>
    disch_then drule >>
    fs [pmatch_rows_def]
  ) >>
  qsubterm_then `nsBindList _ _` assume_tac
    (GEN_ALL nsBindList_pat_tups_bind_locals) >>
  fs [] >>
  last_x_assum (qsubterm_then `evaluate _ _ _` mp_tac) >>
  disch_then drule >>
  simp[]>>
  reverse IF_CASES_TAC THEN1 fs [pmatch_rows_def] >>
  impl_tac >> fs [] >>
  simp[s_rel_cases] >>
  fs [env_all_rel_cases, match_result_rel_def] >>
  rveq >> fs [] >>
  rw [environment_component_equality, sem_env_component_equality] >>
  qexists_tac `alist_to_ns (env1 ++ l)` >>
  qexists_tac`env'` >>
  rw []
  >- (
    drule (CONJUNCT1 pmatch_extend) >>
    drule env_rel_dom >>
    rw [])
  >- metis_tac [global_env_inv_add_locals]
  >- (
    rw_tac std_ss [GSYM nsAppend_alist_to_ns] >>
    match_mp_tac env_rel_append >>
    rw [])
QED
*)

(* HOL4 ML code, not ported:
Resume compile_correct[empty_decs]:
*)
  (* no decs *)
(* HOL4 ML code, not ported:
  rw [] \\ asm_exists_tac \\ simp []
  \\ simp [v_rel_global_eqn, subglobals_refl,
      empty_env_def, env_domain_eq_def]
QED
*)

(* HOL4 ML code, not ported:
Resume compile_correct[cons_decs]:
*)
  (* sequence of decs *)
(* HOL4 ML code, not ported:
  rw [] \\ fs [pair_case_eq]
  \\ rpt (pairarg_tac \\ fs [])
  \\ rveq \\ fs []
  \\ imp_res_tac compile_decs_idx_prev
  \\ first_x_assum (drule_then drule)
  \\ impl_tac >- (
    fs [invariant_def]
    \\ imp_res_tac compile_decs_env_gen_inv
    \\ imp_res_tac compile_decs_future_rel
    \\ rpt strip_tac \\ fs []
    \\ fsrw_tac [SATISFY_ss] [idx_prev_trans]
  )
  \\ rw []
  \\ simp [evaluate_decs_append]
  \\ reverse (fs [result_case_eq]) \\ rveq \\ fs [] \\ rveq \\ fs []
  >- (
    goal_assum (first_assum o mp_then (Pat `result_rel`) mp_tac)
    \\ rw []
    \\ fs []
    \\ drule_then irule invariant_idx_range_shrink_gen
    \\ imp_res_tac compile_decs_env_gen_inv
    \\ fs []
  )
  \\ fs [pair_case_eq] \\ fs []
  \\ drule_then drule global_env_inv_weak
  \\ rw []
  \\ first_x_assum (drule_then drule)
  \\ simp [global_env_inv_append]
  \\ imp_res_tac env_gen_future_rel_forward
  \\ (impl_tac >- (rpt strip_tac \\ fs [combine_dec_result_def]))
  \\ rw []
  \\ simp [abort_compile_dec_result]
  \\ simp [combine_dec_result_def, result_case_eq]
  \\ asm_exists_tac
  \\ rw [] \\ fs []
  \\ fsrw_tac [SATISFY_ss] trans_thms
  >- (
    imp_res_tac env_domain_eq_append
    \\ fs [extend_dec_env_def]
  )
  >- (
    mp_tac global_env_inv_append
    \\ simp [extend_dec_env_def]
    \\ disch_then irule
    \\ imp_res_tac global_env_inv_weak
    \\ simp []
  )
QED
*)

(* HOL4 ML code, not ported:
Resume compile_correct[Dlet]:
  rename [‘simple_dlet p e’] >>
  reverse $ Cases_on ‘simple_dlet p e’
  >-
   (rename [‘simple_dlet p e = SOME p_’] >>
    PairCases_on ‘p_’ >> gvs [] >>
    pop_assum mp_tac >>
    simp [simple_dlet_def, AllCaseEqs()] >>
    strip_tac >> gvs [evaluateTheory.evaluate_def] >>
    qpat_x_assum ‘_ = (s',r)’ mp_tac >>
    simp [AllCaseEqs(),semanticPrimitivesTheory.pmatch_def] >>
    strip_tac >> gvs [] >>
    ‘∃t1 i1. nsLookup comp_map.v p_1 = SOME (Glob t1 i1)’ by
      (gvs [v_rel_global_eqn] >> res_tac >> gvs []) >>
    gvs [flatSemTheory.evaluate_def] >>
    first_x_assum $ irule_at $ Pos hd >>
    simp [subglobals_refl] >>
    conj_tac >- simp [env_domain_eq_def] >>
    gvs [v_rel_global_eqn] >>
    gvs [nsLookup_nsBind_If] >>
    res_tac \\ gvs []) >>
  pop_assum $ full_simp_tac std_ss o single >>
  rw [] >> fs [pair_case_eq] >> fs [] >>
  `env_all_rel genv comp_map env <|v := []|> []`
    by (simp [env_all_rel_cases] \\ simp [v_rel_rules]) >>
  first_x_assum (drule_then drule) >>
  simp [bind_locals_def, EVAL ``nsBindList [] ns``] >>
  simp [bind_locals_def] >>
  simp [Q.prove (`(x with v := x.v) = (x : source_to_flat$environment)`,
      simp [source_to_flatTheory.environment_component_equality])] >>
  disch_then $ qspec_then ‘(REVERSE (pat_bindings p) ++ path)’ mp_tac >>
  (impl_tac >- (CCONTR_TAC >> fs [])) >>
  rw [] >>
  simp [] >>
  imp_res_tac not_abort_IMP_cases >> fs [result_rel_eqns] >>
  rveq >> fs [] >>
  simp [evaluate_def] >>
  TRY (asm_exists_tac >> simp [result_rel_eqns]) >>
  fs [] >>
  drule invariant_idx_range_shrink >>
  disch_then (qsubterm_then `(_, _, _)` mp_tac) >>
  simp [] >>
  (impl_tac >- simp [idx_prev_def]) >>
  rw [] >>
  imp_res_tac result_rel_imp >> fs [] >> rveq >> fs [result_rel_eqns] >>
  TRY (asm_exists_tac >> simp []) >>
  imp_res_tac evaluate_sing >>
  fs [] >> rveq >> fs [pmatch_rows_def] >>
  drule_then drule env_all_rel_weak >>
  simp [] >> disch_tac >>
  drule pmatch_invariant >>
  disch_then (qsubterm_then `pmatch _ _ _ _ _` mp_tac) >>
  disch_then (qsubterm_then `flatSem$pmatch _ _ _` mp_tac) >>
  disch_then drule >>
  simp [] >> disch_tac >>
  imp_res_tac invariant_genv_c_ok >>
  imp_res_tac match_result_rel_imp >> fs [] >>
  TRY (asm_exists_tac >> simp [result_rel_eqns, v_rel_lems]) >>
  fs [match_result_rel_def] >>
  drule (CONJUNCT1 pmatch_bindings) >>
  rw [] >>
  qpat_x_assum `invariant _ _ _ _ (_ with vidx := _, _, _) _ _` kall_tac
    >>
  drule invariant_make_varls >>
  disch_then (qsubterm_then `evaluate _ _ _` mp_tac) >>
  simp [] >>
  (impl_tac >- fs [idx_prev_def]) >>
  rw [] >>
  simp [] >>
  imp_res_tac invariant_IMP_s_rel >>
  asm_exists_tac >> simp [] >>
  rw []
  >- (
    metis_tac [subglobals_trans]
  )
  >- (
    simp [env_domain_eq_def] >>
    simp [GSYM MAP_MAP_o, fst_alloc_defs, EXTENSION] >>
    rw [MEM_MAP] >>
    imp_res_tac env_rel_dom >>
    fs [] >>
    metis_tac [FST, MEM_MAP]
  )
  >- (
    first_x_assum irule >>
    metis_tac [env_rel_weak, SUBMAP_REFL]
  )
QED
*)

(* HOL4 ML code, not ported:
Resume compile_correct[Dletrec]:
  rpt disch_tac \\ fs [ELIM_UNCURRY, Q.ISPEC `FST` ETA_THM]
  \\ simp [compile_funs_dom2]
  \\ drule invariant_make_varls
  \\ disch_then (qsubterm_then `evaluate _ _ _` mp_tac)
  \\ simp []
  \\ impl_tac
  >- (
    simp [build_rec_env_merge, MAP_MAP_o, o_DEF, ELIM_UNCURRY, ETA_THM]
    \\ simp [compile_funs_dom2]
    \\ fs [idx_prev_def]
  )
  \\ rw []
  \\ simp []
  \\ imp_res_tac invariant_IMP_s_rel
  \\ asm_exists_tac
  \\ fs [build_rec_env_merge, MAP_MAP_o, o_DEF]
  \\ conj_tac
  >- (
    simp [env_domain_eq_def]
    \\ simp [semanticPrimitivesPropsTheory.build_rec_env_merge]
    \\ simp [GSYM MAP_MAP_o, fst_alloc_defs]
    \\ simp [MAP_MAP_o, o_DEF, ELIM_UNCURRY, MAP_REVERSE]
  )
  \\ simp [semanticPrimitivesPropsTheory.build_rec_env_merge]
  \\ fs [MAP_MAP_o, o_DEF, ELIM_UNCURRY, Q.ISPEC `FST` ETA_THM]
  \\ fs [compile_funs_dom2]
  \\ first_x_assum irule
  \\ simp [source_to_flatTheory.compile_funs_map, MAP_MAP_o]
  \\ simp [env_rel_LIST_REL, EVERY2_MAP]
  \\ irule EVERY2_refl
  \\ simp [FORALL_PROD]
  \\ simp [Once v_rel_cases]
  \\ rw [source_to_flatTheory.compile_funs_map, MAP_EQ_f, FORALL_PROD]
  \\ qexistsl_tac [`comp_map`, `env`, `nsEmpty`, `path`, `MAP (K None)
    funs`]
  \\ simp []
  \\ drule_then (fn t => simp [t]) global_env_inv_weak
  \\ rw []
  \\ simp [bind_locals_def, MAP2_MAP, ZIP_MAP, MAP_MAP_o, o_DEF,
    v_rel_rules]
QED
*)

(* HOL4 ML code, not ported:
Resume compile_correct[Dtype]:
  rpt $ pop_assum mp_tac >>
  simp [markerTheory.Case_def] >>
  MAP_EVERY qid_spec_tac [`genv`, `idx`, `comp_map`, `env`, `s`, `s_i1`]
    >>
  Induct_on `tds`
  >- ( (* No tds *)
    rw [evaluate_def] >>
    simp [build_tdefs_def, v_rel_global_eqn, env_domain_eq_def] >>
    qexists_tac `genv` >>
    simp [subglobals_refl] >>
    fs [invariant_def, s_rel_cases] >>
    simp [Q.prove (`(n with tidx := n.tidx) = n`,
      simp [next_indices_component_equality])]
  ) >>
  strip_tac >>
  rename [`EVERY check_dup_ctors (td::tds)`] >>
  `?tvs tn ctors. td = (tvs, tn ,ctors)` by metis_tac [pair_CASES] >>
  rw [evaluate_def] >>
  pairarg_tac >>
  fs [] >>
  simp [evaluate_def] >>
  drule_then (drule_then drule) alloc_tags_invariant >>
  impl_tac
  >- (
    fs [check_dup_ctors_thm] >>
    fs [idx_prev_def]
  ) >>
  rw [] >>
  drule_then drule global_env_inv_weak >>
  rw [subglobals_refl] >>
  first_x_assum (drule_then drule) >>
  imp_res_tac invariant_IMP_s_rel >>
  fs [ADD1] >>
  rw [] >>
  simp [o_DEF, ADD1] >>
  qexists_tac ‘genv''’ >>
*)
  (* goal_assum (first_assum o mp_then (Pat `invariant`) mp_tac) >> *)
(* HOL4 ML code, not ported:
  simp [build_tdefs_def, Once nsAppend_foldl] >>
  simp [GSYM extend_dec_env_v_empty, GSYM extend_env_v_empty] >>
  rw [] >> simp []
  >- (
    metis_tac [SUBMAP_TRANS]
  )
  >- (
    metis_tac [SUBMAP_TRANS]
  )
  >- (
    simp [build_tdefs_def, Once nsAppend_foldl] >>
    simp [GSYM extend_dec_env_v_empty, GSYM extend_env_v_empty] >>
    irule env_domain_eq_append >>
    simp []
  )
  >- (
    simp [build_tdefs_def, Once nsAppend_foldl] >>
    simp [GSYM extend_dec_env_v_empty, GSYM extend_env_v_empty] >>
    irule global_env_inv_append >>
    simp [] >>
    drule_then irule global_env_inv_weak >>
    simp []
  )
QED
*)

(* HOL4 ML code, not ported:
Resume compile_correct[Dtabbrev]:
  rw [] >>
  asm_exists_tac >>
  fs [v_rel_global_eqn, empty_env_def, env_domain_eq_def,
    subglobals_refl]
QED
*)

(* HOL4 ML code, not ported:
Resume compile_correct[Denv]:
  rw []
  \\ fs [option_case_eq, pair_case_eq]
  \\ fs [declare_env_def, option_case_eq, CaseEq "eval_state"]
  \\ rveq \\ fs []
  >- (
*)
    (* incorrect eval state type *)
(* HOL4 ML code, not ported:
    fs [invariant_def, orac_rel_def]
    \\ rfs []
  )
  \\ simp [evaluate_def, do_app_def, env_id_tuple_def]
  \\ rfs [invariant_def, fin_idx_match_def, src_orac_invs_def]
  \\ drule_then strip_assume_tac step_1
  \\ fs []
  \\ `idx.vidx < LENGTH s_i1.globals ∧ EL idx.vidx s_i1.globals = NONE`
    by (
    fs [s_rel_cases, idx_range_rel_def, idx_prev_def,
      genv_allocated_idxs_def]
    \\ rveq \\ fs []
    \\ qspecl_then [`(i,Idx_Var)`, `0`] drule ALL_DISJOINT_elem
    \\ simp [idx_block_def]
  )
  \\ csimp [env_domain_eq_def]
  \\ qmatch_goalsub_abbrev_tac `LUPDATE (SOME v)`
  \\ qexists_tac `genv with <| v := LUPDATE (SOME v) idx.vidx genv.v |>`
  \\ `subglobals genv.v (LUPDATE (SOME v) idx.vidx genv.v)`
    by (
    rw [subglobals_def, EL_LUPDATE]
    \\ rw [] \\ fs [IS_SOME_EXISTS] \\ fs []
    \\ rfs [invariant_def, s_rel_cases]
  )
  \\ simp [src_orac_next_cfg_def]
  \\ fs [EL_LUPDATE, invariant_def, s_rel_cases]
  \\ rfs []
  \\ rw []
  \\ TRY (fs [src_orac_step_invs_def, orac_rel_def,
    src_orac_gen_inv_def,
        orac_rel_inner_def]
    \\ rfs [src_orac_next_cfg_def]
    \\ fsrw_tac [SATISFY_ss] [] \\ NO_TAC)
  >- (
    drule_then irule LIST_REL_sv_rel_weak
    \\ simp []
  )
  >- (
    fs [idx_range_rel_def, src_orac_next_cfg_def,
      genv_allocated_idxs_def]
    \\ rfs []
    \\ drule_then irule (Q.SPECL [`0`, `3`] ALL_DISJOINT_MOVE)
    \\ simp [LUPDATE_compute]
    \\ qexists_tac `{(idx.vidx, Idx_Var)}`
    \\ simp [EXTENSION, idx_types_FORALL, FORALL_PROD]
    \\ fs [idx_block_def, EL_LUPDATE, bool_case_eq, idx_prev_def]
    \\ metis_tac []
  )
  >- (
    fs [src_orac_env_invs_def, env_gen_future_rel_def]
    \\ rfs [src_orac_next_cfg_def]
    \\ fs [env_gen_rel_def, oEL_THM]
    \\ rveq \\ fs []
    \\ fs [EL_LUPDATE, EL_APPEND_IF]
    \\ rw []
    \\ fs [EL_APPEND_IF]
    \\ rw []
    \\ TRY (res_tac \\ fs [] \\ drule_then irule global_env_inv_weak)
    \\ fs [subspt_lookup]
    \\ first_x_assum (qspec_then `id` mp_tac)
    \\ simp [lookup_insert]
    \\ rfs []
    \\ rw [miscTheory.EL_CONS_IF]
    \\ drule_then irule global_env_inv_weak
    \\ simp []
  )
  >- (
    fs [orac_rel_def]
    \\ qexists_tac `s_compiler`
    \\ fsrw_tac [SATISFY_ss] [orac_rel_inner_def]
  )
  >- (
    fs [eval_ref_inv_def]
    \\ Cases_on `s_i1.globals` \\ fs []
    \\ Cases_on `idx.vidx` \\ fs []
    \\ simp [LUPDATE_def]
  )
  >- (
    fs [env_gen_inv_def]
    \\ drule_then irule SUBSET_TRANS
    \\ simp [pred_setTheory.COUNT_MONO]
  )
  >- (
    simp [orac_forward_rel_def, eval_state_call_rel_def, EL_LUPDATE]
    \\ rfs [orac_config_envs_subspt_def, src_orac_next_cfg_def]
  )
  >- (
    fs [env_gen_rel_def, oEL_THM]
    \\ simp [EL_LUPDATE]
  )
  >- (
    simp [Once v_rel_cases]
    \\ fs [EL_LUPDATE, markerTheory.Abbrev_def, v_rel_eqns]
    \\ simp [nat_to_v_def, v_rel_eqns]
    \\ fs [oEL_THM]
    \\ rveq \\ fs []
    \\ fs [env_gen_rel_def]
  )
QED
*)

(* HOL4 ML code, not ported:
Resume compile_correct[Dexn]:
  reverse (rw [evaluate_def]) >>
  fs [v_rel_eqns, invariant_def, s_rel_cases] >>
  qexists_tac `genv with c := FUNION genv.c
      (FEMPTY |+ (((idx.eidx,NONE),LENGTH ts), ExnStamp
        s.next_exn_stamp))` >>
  rfs [SUBMAP_FUNION_ID, subglobals_refl, env_domain_eq_def, UNION_COMM]
    >>
  rw []
  >- (
    drule_then irule LIST_REL_sv_rel_weak
    \\ simp [subglobals_refl, SUBMAP_FUNION_ID]
  )
  >- (
    drule_then irule genv_c_ok_extend >>
    simp [FLOOKUP_UPDATE] >>
    simp [semanticPrimitivesTheory.ctor_same_type_def, same_type_def] >>
    simp [ctor_same_type_def] >>
    CCONTR_TAC >> fs [idx_range_rel_def] >>
    rfs [FRANGE_FLOOKUP]
  )
  >- (
    fs [genv_c_tys_ok_def]
  )
  >- (
    drule_then irule LIST_REL_sv_rel_weak
    \\ simp [subglobals_refl, SUBMAP_FUNION_ID]
  )
  >- (
    fs [idx_range_rel_def, FRANGE_FUNION, genv_allocated_idxs_def] >>
    rw [] >>
    TRY asm_exists_tac >>
    fs [FRANGE_FLOOKUP, FLOOKUP_FUNION, option_case_eq, FLOOKUP_UPDATE]
      >>
    drule_then irule (Q.SPECL [`0`, `3`] ALL_DISJOINT_MOVE) >>
    simp [LUPDATE_compute] >>
    qexists_tac `{(idx.eidx, Idx_Exn)}` >>
    simp [EXTENSION, FORALL_PROD, idx_types_FORALL, idx_block_def] >>
    fs [idx_prev_def] >>
    metis_tac []
  )
  >- (
    drule_then irule src_orac_invs_weak
    \\ simp [subglobals_refl, SUBMAP_FUNION_ID]
  )
  >- (
    gvs [v_rel_global_eqn]
    \\ simp [FLOOKUP_FUNION, option_case_eq, FLOOKUP_UPDATE]
    \\ CCONTR_TAC
    \\ fs [GSYM quantHeuristicsTheory.IS_SOME_EQ_NOT_NONE,
      IS_SOME_EXISTS]
    \\ rfs [FDOM_FLOOKUP]
    \\ res_tac >>
    rfs [] >>
    rveq >> fs [] >>
    fs [idx_range_rel_def, ALL_DISJOINT_DEF, genv_allocated_idxs_def] >>
    first_x_assum (qspecl_then [`0`, `3`] mp_tac) >>
    simp [EXTENSION] >>
    qexists_tac `(idx.eidx, Idx_Exn)` >>
    fs [idx_block_def, idx_prev_def] >>
    fs [FLOOKUP_DEF] >>
    asm_exists_tac >>
    simp []
  )
QED
*)

(* HOL4 ML code, not ported:
Resume compile_correct[Dmod]:
  rw [] >> fs [pair_case_eq] >> fs [] >>
  rpt (pairarg_tac >> fs []) >>
  rw [] >>
  first_x_assum drule >>
  disch_then drule >>
  simp [] >>
  (impl_tac >- (strip_tac >> fs [])) >>
  rw [] >>
  rw [] >>
  qexists_tac `genv'` >>
  simp [case_eq_thms, PULL_EXISTS] >>
  imp_res_tac not_abort_IMP_cases >> fs [result_rel_eqns] >>
  rw []
  >- (
    fs [env_domain_eq_def, lift_env_def] >>
    rw [nsDom_nsLift, nsDomMod_nsLift])
  >- (
    rw [] >>
    fs [v_rel_global_eqn] >>
    rw [lift_env_def, nsLookup_nsLift] >>
    CASE_TAC >>
    rw [] >>
    fs [])
QED
*)

(* HOL4 ML code, not ported:
Resume compile_correct[Dlocal]:
  rw [] >> fs [pair_case_eq] >> fs [] >>
  rpt (pairarg_tac >> fs []) >>
  rveq >> fs [] >>
  imp_res_tac compile_decs_idx_prev >>
  first_x_assum (drule_then drule) >>
  simp [] >>
  impl_tac >- (
    fs [invariant_def]
    \\ imp_res_tac compile_decs_env_gen_inv
    \\ imp_res_tac compile_decs_future_rel
    \\ rpt strip_tac \\ fs []
    \\ fsrw_tac [SATISFY_ss] [idx_prev_trans]
  ) >>
  rw [evaluate_decs_append] >>
  reverse (fs [case_eq_thms])
  >- ( (* err case *)
    fs [] >>
    rw [] >>
    asm_exists_tac >>
    rw [] >>
    fs [] >>
    drule_then irule invariant_idx_range_shrink_gen >>
    imp_res_tac compile_decs_env_gen_inv >>
    simp []
  ) >>
*)
  (* result case *)
(* HOL4 ML code, not ported:
  rveq >>
  fs [] >>
  first_x_assum (drule_then drule) >>
  imp_res_tac env_gen_future_rel_forward >>
  impl_tac
  >- metis_tac [global_env_inv_append, global_env_inv_weak] >>
  rw [] >>
  imp_res_tac evaluate_decs_append >>
  fs [] >>
  asm_exists_tac >>
  metis_tac trans_thms
QED
*)

(* HOL4 ML code, not ported:
Finalise compile_correct;
*)

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

(* - connect semantics theorems of flat-to-flat passes
   --------------------- *)

let precondition_def = cake_define
  `precondition interp s env cfg ec prog <=>
   (?ec1 g. precondition1 interp g s env cfg ec1 prog /\
     install_conf_rel (source_to_flat_config_pattern_cfg cfg) ec1
       ec)`;;

(* - esgc_free theorems for compile_exp
   ------------------------------------ *)

(* - esgc_free theorems for compile_decs
   ----------------------------------- *)

(* - the source_to_flat compiler produces things which are esgc_free
   ------- *)

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

(* HOL4 ML code, not ported:
val COUNT_LIST_ADD_SYM = COUNT_LIST_ADD
  |> CONV_RULE (SIMP_CONV bool_ss [Once ADD_SYM]);
*)

(* not sure if this variant of the inc. compiler is the one we need *)
