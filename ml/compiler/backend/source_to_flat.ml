(* ======================================================== *)
(*  source_to_flat: ported from HOL4's
    compiler/backend/source_to_flatScript.sml  *)
(* ======================================================== *)

(*
  This is the compiler phase that translates the CakeML source
  language into flatLang.

  The translator to flatLang keeps two mappings, one mapping module
  paths to indices into the genv, and the other mapping module paths
  to constructor ids.  All variable references are replaced with
  global references to the genv index if they are in the
  mappings. This includes top-level letrec names which are all put
  into the mapping before translating any of the let rec functions.
  This enables the semantics of let rec to just create Closures rather
  than Recclosures.
*)

needs "compiler/backend/flatLang.ml";;
needs "compiler/backend/flat_elim.ml";;
needs "compiler/backend/flat_pattern.ml";;
needs "semantics/ast.ml";;
needs "semantics/evaluate.ml";;

let var_name_INDUCT,var_name_RECURSION = define_datatype
  "var_name = Glob (tra) (num) | Local (tra) (mlstring)";;

let source_to_flat_environment_FIELDS =
  define_record "source_to_flat_environment"
  ["c","(mlstring,mlstring,num#(num#(num#num) list) option)namespace";
   "v","(mlstring,mlstring,var_name)namespace"];;

let environment_generation_store_FIELDS =
  define_record "environment_generation_store"
  ["next","num";
   "generation","num";
   "envs","source_to_flat_environment sptree_num_map"];;

let environment_store_FIELDS = define_record "environment_store"
  ["next","num";
   "env_gens","(source_to_flat_environment sptree_num_map) \
   sptree_num_map"];;

let compile_var_def = cake_define
  `compile_var t (Glob _1 i) = flatLang_App t (flatLang_GlobalVarLookup
  i) [] /\
   compile_var t (Local _2 s) = flatLang_Var_local t s`;;

(* HOL4 termination: >> rw [ast_pat1_size] >> fs [MEM_SPLIT,
   SUM_APPEND] *)
let compile_pat_def = cake_define_wf
  `MEASURE (pat_size o SND)`
  `(compile_pat env (ast_Pvar semanticPrimitives_v) = flatLang_Pvar
  semanticPrimitives_v) /\
   (compile_pat env flatLang_Pany = flatLang_Pany) /\
   (compile_pat env (flatLang_Plit l) = flatLang_Plit l) /\
   (compile_pat env (ast_Pcon id ps) =
     flatLang_Pcon
       (OPTION_JOIN (OPTION_MAP (nsLookup (?_c env)) id))
       (MAP (compile_pat env) ps)) /\
   (compile_pat env (flatLang_Pref p) = flatLang_Pref (compile_pat
     env p)) /\
   (compile_pat env (flatLang_Pas p i) = flatLang_Pas (compile_pat
     env p) i) /\
   (compile_pat env (ast_Ptannot p t) = compile_pat env p)`;;

let pat_tups_def = cake_define
  `(pat_tups t [] = []) /\
   (pat_tups t (x :: xs) =
    (let t' = mk_cons t ((LENGTH xs) + 1) in
      (x,Local t' x) :: pat_tups t xs))`;;

let astOp_to_flatOp_def = cake_define
  `(astOp_to_flatOp (flatLang_op:ast_op):flatLang_op) =
   (match flatLang_op with ast_Opderef -> flatLang_El 0 | _3 ->
     flatLang_Src flatLang_op)`;;

let type_group_id_type_def = cake_define
  `type_group_id_type NONE = NONE /\
   type_group_id_type (SOME (cn,NONE)) = SOME (cn,NONE) /\
   type_group_id_type (SOME (cn,(SOME (ty_id,ctors)))) = SOME
     (cn,SOME ty_id)`;;

let str_sep_def = cake_define
  `str_sep = (strlit "_")`;;

let join_all_names_aux_def = cake_define
  `join_all_names_aux [] ys = ys /\
   join_all_names_aux (x :: xs) ys =
     (match ys with [] -> join_all_names_aux xs (x :: ys) | _4 ->
       join_all_names_aux xs (x :: str_sep :: ys))`;;

let join_all_names_def = cake_define
  `join_all_names xs =
     (match xs with [x] -> x | _5 -> mlstring_concat
       (join_all_names_aux xs []))`;;

(* HOL4 termination: *)
let compile_exp_def = cake_define_wf
  `inv_image (<) (\x. match x with INL (t,x,e) -> exp_size e | INR (INL
  (t,x,es)) -> list_size exp_size es | INR (INR (INL (t,x,pes))) ->
          list_size (pair_size pat_size exp_size) pes | INR (INR (INR
            (t,x,funs))) ->
          list_size (pair_size mlstring_size
                     (pair_size mlstring_size exp_size)) funs)`
  `source_to_flat_compile_exp t env x3 =
        match (t,env,x3) with
          ((t:mlstring
            list),(env:source_to_flat_environment),(flatLang_Raise e))
            ->
       flatLang_Raise backend_common_None (source_to_flat_compile_exp
         t env e)
        | (t,env,(flatLang_Handle e pes)) ->
       flatLang_Handle backend_common_None
         (source_to_flat_compile_exp t env e) (compile_pes t env pes)
        | (t,env,(ast_Lit l)) -> flatLang_Lit backend_common_None l
        | (t,env,(flatLang_Con cn es)) ->
       flatLang_Con backend_common_None (OPTION_JOIN (OPTION_MAP
         (type_group_id_type o nsLookup (?_c env)) cn))
             (source_to_flat_compile_exps t env es)
        | (t,env,(ast_Var x)) ->
       match nsLookup (?_v env) x with NONE -> flatLang_Var_local
         backend_common_None (strlit "") | SOME x -> compile_var
         backend_common_None x
        | (t,env,(flatLang_Fun x e)) ->
       flatLang_Fun (join_all_names t) x
         (source_to_flat_compile_exp t (?_v_fupd (K (nsBind x (Local
           backend_common_None x) (?_v env))) env) e)
        | (t,env,(ast_App flatLang_op es)) ->
       if flatLang_op = ast_AallocEmpty then
         ITLIST (flatLang_Let backend_common_None NONE)
           (REVERSE (source_to_flat_compile_exps t env es))
             (flatLang_App backend_common_None (flatLang_Src ast_Aalloc)
             [pattern_semantics_Lit backend_common_None (ast_IntLit
             (&0));
                              pattern_semantics_Lit
                                backend_common_None (ast_IntLit (&0))])
                                else
       if flatLang_op = ast_Eval then
         flatLang_Mat backend_common_None (flatLang_Con
           backend_common_None NONE (source_to_flat_compile_exps t env
           es))
           [(flatLang_Pcon NONE [flatLang_Pany; flatLang_Pany;
             flatLang_Pany; flatLang_Pany; flatLang_Pvar (strlit
             "bytes"); flatLang_Pvar (strlit "words")],
               flatLang_Let backend_common_None NONE (flatLang_App
                 backend_common_None (flatLang_Src ast_Eval)
                       (MAP (flatLang_Var_local backend_common_None)
                         [(strlit "bytes"); (strlit "words")]))
                   (flatLang_Let backend_common_None (SOME (strlit
                     "r")) (flatLang_App backend_common_None
                     (flatLang_GlobalVarLookup 0) [])
                       (flatLang_App backend_common_None (flatLang_El
                         0) [flatLang_Var_local backend_common_None
                         (strlit "r")])))] else
       if flatLang_op = ast_Env_id then (match es with [_6] -> (match
         source_to_flat_compile_exps t env es with x :: xs -> x | _7 ->
         flatLang_Var_local backend_common_None (strlit "")) | _8 ->
         flatLang_App backend_common_None (flatLang_El 0)
         (source_to_flat_compile_exps t env es)) else
         flatLang_App backend_common_None (astOp_to_flatOp
           flatLang_op) (source_to_flat_compile_exps t env es)
        | (t,env,(ast_Log lop e1 e2)) ->
         match lop with Andalso ->
           pattern_semantics_If backend_common_None
              (source_to_flat_compile_exp t env e1)
              (source_to_flat_compile_exp t env e2)
              (flatLang_Bool backend_common_None F) | Orelse ->
           pattern_semantics_If backend_common_None
              (source_to_flat_compile_exp t env e1)
              (flatLang_Bool backend_common_None T)
              (source_to_flat_compile_exp t env e2)
        | (t,env,(pattern_semantics_If e1 e2 e3)) ->
       pattern_semantics_If backend_common_None
          (source_to_flat_compile_exp t env e1)
          (source_to_flat_compile_exp t env e2)
          (source_to_flat_compile_exp t env e3)
        | (t,env,(flatLang_Mat e pes)) ->
       flatLang_Mat backend_common_None (source_to_flat_compile_exp t
         env e) (compile_pes t env pes)
        | (t,env,(flatLang_Let (SOME x) e1 e2)) ->
         flatLang_Let backend_common_None (SOME x)
           (source_to_flat_compile_exp (x :: t) env e1)
           (source_to_flat_compile_exp t (?_v_fupd (K (nsBind x
             (Local backend_common_None x) (?_v env))) env) e2)
        | (t,env,(flatLang_Let NONE e1 e2)) ->
       flatLang_Let backend_common_None NONE
         (source_to_flat_compile_exp t env e1)
         (source_to_flat_compile_exp t env e2)
        | (t,env,(ast_Letrec funs e)) ->
       let fun_names = MAP FST funs in
       let new_env = nsBindList (MAP (\x. (x,Local
         backend_common_None x)) fun_names) (?_v env) in
         flatLang_Letrec (join_all_names t) (compile_funs t (?_v_fupd
           (K new_env) env) funs)
                  (source_to_flat_compile_exp t (?_v_fupd (K new_env)
                    env) e)
        | (t,env,(ast_Tannot e _9)) -> source_to_flat_compile_exp t
          env e
        | (t,env,(ast_Lannot e (Locs st en))) ->
          source_to_flat_compile_exp t env e
        | (t,env,[]) -> []
        | (t,env,(e :: es)) ->
        source_to_flat_compile_exp t env e ::
          source_to_flat_compile_exps t env es
        | (t,env,[]) -> []
        | (t,env,((p,e) :: pes)) ->
       let pbs = flatLang_pat_bindings p in
       let pts = pat_tups backend_common_None pbs in
       (compile_pat env p,source_to_flat_compile_exp t (?_v_fupd (K
         (nsBindList pts (?_v env))) env) e) :: compile_pes t env pes
        | (t,env,[]) -> []
        | (t,env,((f,x,e) :: funs)) ->
       (f,x,source_to_flat_compile_exp (f :: t) (?_v_fupd (K (nsBind
         x (Local backend_common_None x) (?_v env))) env) e) ::
       compile_funs t env funs`;;

let om_tra_def = cake_define
  `om_tra = pattern_semantics_Cons orphan_trace 1`;;

let alloc_defs_def = cake_define
  `(alloc_defs n next [] = []) /\
   (alloc_defs n next (x :: xs) =
     (x,Glob om_tra next) :: alloc_defs (n + 1) (next + 1) xs)`;;

let make_varls_def = cake_define
  `make_varls n t idx x4 =
        match (t,x4) with
          (t,[]) -> flatLang_Con backend_common_None NONE []
        | (t,[x]) -> flatLang_App backend_common_None
          (flatLang_GlobalVarInit idx) [flatLang_Var_local
          backend_common_None x]
        | ((t:tra),(x :: xs)) ->
         flatLang_Let backend_common_None NONE (flatLang_App
           backend_common_None (flatLang_GlobalVarInit idx)
           [flatLang_Var_local backend_common_None x])
           (make_varls (n + 1) backend_common_None (idx + 1)
             xs):flatLang_exp`;;

let empty_env_def = cake_define
  `source_to_flat_empty_env = mk_? nsEmpty nsEmpty`;;

let extend_env_def = cake_define
  `extend_env e1 e2 =
     mk_? (nsAppend (?_v e1) (?_v e2)) (nsAppend (?_c e1) (?_c
       e2))`;;

let lift_env_def = cake_define
  `lift_env mn e = mk_? (nsLift mn (?_v e)) (nsLift mn (?_c e))`;;

let next_indices_FIELDS = define_record "next_indices"
  ["vidx","num";
   "tidx","num";
   "eidx","num"];;

let lookup_inc_def = cake_define
  `lookup_inc i t =
     (match sptree_lookup i t with NONE -> (0,sptree_insert i 1 t)
       | SOME n -> (n,sptree_insert i (n + 1) t))`;;

let alloc_tags1_def = cake_define
  `(alloc_tags1 [] = (nsEmpty,LN,[])) /\
   (alloc_tags1 ((cn,ts) :: ctors) =
     (let (ns,cids,tag_list) = alloc_tags1 ctors in
     let arity = LENGTH ts in
     let (pattern_semantics_tag,new_cids) = lookup_inc arity cids in
       (nsBind cn pattern_semantics_tag
         ns,new_cids,(pattern_semantics_tag,arity) :: tag_list)))`;;

let alloc_tags_def = cake_define
  `alloc_tags tid ctors =
     (let (con_ns,cid_spt,tag_list) = alloc_tags1 (REVERSE ctors) in
     let data = SOME (tid,REVERSE tag_list) in
     (nsMap (\pattern_semantics_tag. (pattern_semantics_tag,data))
       con_ns,cid_spt))`;;

let env_id_tuple_def = cake_define
  `env_id_tuple gen id = flatLang_Con backend_common_None NONE
     [pattern_semantics_Lit backend_common_None (ast_IntLit
       (&gen)); pattern_semantics_Lit backend_common_None (ast_IntLit
       (&id))]`;;

let simple_dlet_def = cake_define
  `simple_dlet p e =
     (match p with ast_Pvar pv -> (match e with ast_Var
       semanticPrimitives_v -> SOME (pv,semanticPrimitives_v) | _10
       -> NONE) | _11 -> NONE)`;;

(* HOL4 termination: *)
let compile_decs_def = cake_define_wf
  `MEASURE (list_size dec_size o SND o SND o SND o SND o SND)`
  `source_to_flat_compile_decs t n next env envs x6 =
        match (t,x6) with
          ((t:mlstring list),[Dlet locs p e]) ->
        match simple_dlet p e with SOME (pv,semanticPrimitives_v) ->
            (match nsLookup (?_v env) semanticPrimitives_v with SOME
              (Glob t i) ->
                    (n,next,mk_? (alist_to_ns [(pv,Glob t i)])
                      nsEmpty,envs,[]) | _12 -> (n,next,mk_? nsEmpty
                      nsEmpty,envs,[])) | NONE ->
            (let n' = n + 4 in
            let xs = REVERSE (flatLang_pat_bindings p) in
            let e' = source_to_flat_compile_exp (xs ++ t) env e in
            let l = LENGTH xs in
            let n'' = n' + l in
              (n'',(next_indices_vidx_fupd (K (next_indices_vidx next
                + l)) next),
               mk_? (alist_to_ns (alloc_defs n' (next_indices_vidx
                 next) xs)) nsEmpty,
               envs,
               [flatLang_Mat backend_common_None e'
                  [(compile_pat env p,make_varls 0
                    backend_common_None (next_indices_vidx next) xs)]]))
        | (t,[Dletrec locs funs]) ->
        let fun_names = MAP FST funs in
        let new_env = nsBindList (MAP (\x. (x,Local
          backend_common_None x)) fun_names) (?_v env) in
        let flat_funs = compile_funs t (?_v_fupd (K new_env) env)
          funs in
        let n' = n + 1 in
        let env' = mk_? (alist_to_ns (alloc_defs n'
          (next_indices_vidx next) (REVERSE fun_names))) nsEmpty in
          (n' + LENGTH funs,(next_indices_vidx_fupd (K
            (next_indices_vidx next + LENGTH funs)) next),
           env',envs,
           [(flatLang_Letrec (join_all_names t) flat_funs
              (make_varls 0 backend_common_None (next_indices_vidx
                next) (REVERSE fun_names)))])
        | (t,[Dtype locs type_def]) ->
       let new_env = MAPi (\tid (_13,_14,constrs). alloc_tags
         (next_indices_tidx next + tid) constrs) type_def in
        (n,(next_indices_tidx_fupd (K (next_indices_tidx next +
          LENGTH type_def)) next),
         mk_? nsEmpty (FOLDL (\ns (l,cids). nsAppend l ns) nsEmpty
           new_env),
         envs,
         [])
        | (_15,[Dtabbrev locs tvs tn t]) ->
        (n,next,source_to_flat_empty_env,envs,[])
        | (t,[Dexn locs cn ts]) ->
        (n,(next_indices_eidx_fupd (K (next_indices_eidx next + 1))
          next),
         mk_? nsEmpty (nsSing cn (next_indices_eidx next,NONE)),
         envs,
         [])
        | (t,[Dmod mn ds]) ->
        let (n',next',new_env,envs',ds') =
          source_to_flat_compile_decs (mn :: t) n next env envs ds in
          (n',next',(lift_env mn new_env),envs',ds')
        | (t,[Dlocal lds ds]) ->
        let (n',next1,new_env1,envs',lds') =
          source_to_flat_compile_decs t n next env envs lds in
        let (n'',next2,new_env2,envs'',ds') =
          source_to_flat_compile_decs t n' next1
           (extend_env new_env1 env) envs' ds in
             (n'',next2,new_env2,envs'',lds' ++ ds')
        | (t,[Denv nenv]) ->
        (n + 1,next_indices_vidx_fupd (K (next_indices_vidx next +
          1)) next,
           mk_? (nsBind nenv (Glob backend_common_None
             (next_indices_vidx next)) nsEmpty) nsEmpty,?_envs_fupd (K
             (sptree_insert (?_next envs) env (?_envs envs)))
             (?_next_fupd (K (?_next envs + 1))
           envs),
           [(flatLang_App backend_common_None (flatLang_GlobalVarInit
             (next_indices_vidx next))
               [env_id_tuple (?_generation envs) (?_next envs)])])
        | (t,[]) ->
       (n,next,source_to_flat_empty_env,envs,[])
        | (t,(d :: ds)) ->
        let (n',next1,new_env1,envs1,d') =
          source_to_flat_compile_decs t n next env envs [d] in
        let (n'',next2,new_env2,envs2,ds') =
          source_to_flat_compile_decs t n' next1 (extend_env new_env1
            env) envs1 ds in
          (n'',next2,extend_env new_env2 new_env1,envs2,d' ++ ds')`;;

let source_to_flat_config_FIELDS = define_record "source_to_flat_config"
  ["next","next_indices";
   "mod_env","source_to_flat_environment";
   "pattern_cfg","flat_pattern_config";
   "envs","environment_store"];;

let empty_config_def = cake_define
  `empty_config =
     mk_? (mk_next_indices 0 0 0) source_to_flat_empty_env
       (flat_pattern_init_config 0) (mk_? 0 LN)`;;

let compile_flat_def = cake_define
  `compile_flat pcfg =
     MAP (compile_dec pcfg) o remove_flat_prog`;;

let glob_alloc_def = cake_define
  `glob_alloc next c =
       (flatLang_Let om_tra NONE
         (flatLang_App om_tra
           (flatLang_GlobalVarAlloc (next_indices_vidx next -
             next_indices_vidx (?_next c))) [])
         (flatLang_Con om_tra NONE []))`;;

let alloc_env_ref_def = cake_define
  `alloc_env_ref = (flatLang_App backend_common_None
  (flatLang_GlobalVarInit 0)
     [flatLang_App backend_common_None (flatLang_Src ast_Opref)
       [flatLang_Con backend_common_None NONE []]])`;;

let compile_prog_def = cake_define
  `source_to_flat_compile_prog c p =
     (let next = next_indices_vidx_fupd (K (next_indices_vidx (?_next
       c) + 1)) (?_next c) in
     let envs = mk_? 0 (?_next (?_envs c)) LN in
     let (_16,next,e,gen,p') = source_to_flat_compile_decs [] 1 next
       (source_to_flat_config_mod_env c) envs p in
     let envs2 = mk_? (?_next (?_envs c) + 1) (sptree_insert (?_next
       (?_envs c)) (?_envs gen) (environment_store_env_gens (?_envs c)))
       in
     (source_to_flat_config_mod_env_fupd (K e) (?_envs_fupd (K envs2)
       (?_next_fupd (K next) c)),
         glob_alloc next c :: alloc_env_ref :: p'))`;;

let lookup_env_id_def = cake_define
  `lookup_env_id env_id envs = (match sptree_lookup (FST env_id)
  (environment_store_env_gens envs) with NONE ->
  source_to_flat_empty_env | SOME gen -> (match sptree_lookup (SND
  env_id) gen with NONE -> source_to_flat_empty_env | SOME env ->
  env))`;;

let store_env_id_def = cake_define
  `store_env_id gen id =
     flatLang_Let backend_common_None (SOME (strlit "r"))
       (flatLang_App backend_common_None (flatLang_GlobalVarLookup 0)
       [])
       (flatLang_App backend_common_None (flatLang_Src
         ast_Opassign) [flatLang_Var_local backend_common_None
         (strlit "r"); env_id_tuple gen id])`;;

let inc_compile_prog_def = cake_define
  `inc_compile_prog env_id c p =
     (let env = lookup_env_id env_id (?_envs c) in
     let envs = mk_? 0 (?_next (?_envs c)) LN in
     let (_17,next,e,gen,p') = source_to_flat_compile_decs [] 1
       (?_next c) env envs p in
     let gen_envs = sptree_insert (?_next gen) (extend_env e env)
       (?_envs gen) in
     let envs2 = mk_? (?_next (?_envs c) + 1) (sptree_insert (?_next
       (?_envs c)) gen_envs (environment_store_env_gens (?_envs c))) in
     (?_envs_fupd (K envs2) (?_next_fupd (K next) c),(
         glob_alloc next c :: p') ++ [store_env_id (?_generation
           gen) (?_next gen)]))`;;

let compile_def = cake_define
  `source_to_flat_compile c p =
     (let (c',p') = source_to_flat_compile_prog c p in
     let p' = compile_flat (source_to_flat_config_pattern_cfg c') p'
       in
       (c',p'))`;;

(* note that flat_elim is always disabled in the eval/incremental case
   *)
let inc_compile_def = cake_define
  `inc_compile env_id c p =
     (let (c',p') = inc_compile_prog env_id c p in
     let p' = MAP (compile_dec (source_to_flat_config_pattern_cfg
       c')) p' in
       (c',p'))`;;
