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

needs "basis/pure/mlstring.ml";;
needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/flatLang.ml";;
needs "compiler/backend/flat_elim.ml";;
needs "compiler/backend/flat_pattern.ml";;
needs "compiler/backend/pattern_matching/pattern_semantics.ml";;
needs "lib/indexedLists.ml";;
needs "lib/location.ml";;
needs "lib/sptree.ml";;
needs "semantics/ast.ml";;
needs "semantics/evaluate.ml";;
needs "semantics/namespace.ml";;

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
  `compile_var t (Glob _1 i) = App t (GlobalVarLookup i) [] /\
   compile_var t (Local _2 s) = Var_local t s`;;

let _ = size_thms "pat";;
(* HOL4 termination: >> rw [ast_pat1_size] >> fs [MEM_SPLIT,
   SUM_APPEND] *)
let compile_pat_def = cake_define_wf
  `MEASURE (pat_size o SND)`
  `(compile_pat env (ast_Pvar v) = flatLang_Pvar v) /\
   (compile_pat env Pany = Pany) /\
   (compile_pat env (Plit l) = Plit l) /\
   (compile_pat env (ast_Pcon id' ps) =
     flatLang_Pcon
       (OPTION_JOIN (OPTION_MAP (nsLookup (?_c env)) id'))
       (MAP (compile_pat env) ps)) /\
   (compile_pat env (Pref p) = Pref (compile_pat env p)) /\
   (compile_pat env (Pas p i) = Pas (compile_pat env p) i) /\
   (compile_pat env (Ptannot p t) = compile_pat env p)`;;

let pat_tups_def = cake_define
  `(pat_tups t [] = []) /\
   (pat_tups t (x :: xs) =
    (let t' = mk_cons t ((LENGTH xs) + 1) in
      (x,Local t' x) :: pat_tups t xs))`;;

let astOp_to_flatOp_def = cake_define
  `(astOp_to_flatOp (op:ast_op):flatLang_op) =
   (match op with Opderef -> flatLang_El 0 | _3 -> flatLang_Src
     op)`;;

let type_group_id_type_def = cake_define
  `type_group_id_type x1 =
      match x1 with
        NONE -> NONE
      | (SOME (cn,NONE)) -> SOME (cn,NONE)
      | (SOME (cn,(SOME (ty_id,ctors)))) -> SOME (cn,SOME ty_id)`;;

let str_sep_def = cake_define
  `str_sep = (implode "_")`;;

let join_all_names_aux_def = cake_define
  `join_all_names_aux [] ys = ys /\
   join_all_names_aux (x :: xs) ys =
     (match ys with [] -> join_all_names_aux xs (x :: ys) | _5 ->
       join_all_names_aux xs (x :: str_sep :: ys))`;;

let join_all_names_def = cake_define
  `join_all_names xs =
     (match xs with [x] -> x | _6 -> concat (join_all_names_aux xs
       []))`;;

let compile_exp_def = cake_define_list
  [`source_to_flat_compile_exp (t:mlstring list)
  (env:source_to_flat_environment) (Raise e:flatLang_exp) =
        Raise None (source_to_flat_compile_exp t env e)`;
   `source_to_flat_compile_exp t env (Handle e pes:flatLang_exp) =
        Handle None (source_to_flat_compile_exp t env e)
          (compile_pes t env pes)`;
   `source_to_flat_compile_exp t env (ast_Lit l:flatLang_exp) =
  flatLang_Lit None l`;
   `source_to_flat_compile_exp t env (Con cn es:flatLang_exp) =
        Con None (OPTION_JOIN (OPTION_MAP (type_group_id_type o
          nsLookup (?_c env)) cn))
              (source_to_flat_compile_exps t env es)`;
   `source_to_flat_compile_exp t env (Var x:flatLang_exp) =
        (match nsLookup (?_v env) x with NONE -> Var_local None
          (implode "") | SOME x -> compile_var None x)`;
   `source_to_flat_compile_exp t env (Fun x e:flatLang_exp) =
        Fun (join_all_names t) x
          (source_to_flat_compile_exp t (?_v_fupd (K (nsBind x
            (Local None x) (?_v env))) env) e)`;
   `source_to_flat_compile_exp t env (ast_App op es:flatLang_exp) =
        (if op = AallocEmpty then
          ITLIST (Let None NONE)
            (REVERSE (source_to_flat_compile_exps t env es))
              (flatLang_App None (Src Aalloc) [Lit None (IntLit
              (&(&0)));
                              Lit None (IntLit (&(&0)))]) else
        if op = Eval then
          flatLang_Mat None (Con None NONE
            (source_to_flat_compile_exps t env es))
            [(Pcon NONE [Pany; Pany; Pany; Pany; Pvar (implode
              "bytes"); Pvar (implode "words")],
                flatLang_Let None NONE (flatLang_App None (Src Eval)
                        (MAP (Var_local None) [(implode "bytes");
                          (implode "words")]))
                    (Let None (SOME (implode "r")) (App None
                      (GlobalVarLookup 0) [])
                        (flatLang_App None (El 0) [Var_local None
                          (implode "r")])))] else
        if op = Env_id then (match es with [_7] -> (match
          source_to_flat_compile_exps t env es with x :: xs -> x | _8 ->
          Var_local None (implode "")) | _9 -> App None (El 0)
          (source_to_flat_compile_exps t env es)) else
          flatLang_App None (astOp_to_flatOp op)
            (source_to_flat_compile_exps t env es))`;
   `source_to_flat_compile_exp t env (Log lop e1 e2:flatLang_exp) =
          (match lop with Andalso ->
            If None
               (source_to_flat_compile_exp t env e1)
               (source_to_flat_compile_exp t env e2)
               (Bool None F) | Orelse ->
            If None
               (source_to_flat_compile_exp t env e1)
               (Bool None T)
               (source_to_flat_compile_exp t env e2))`;
   `source_to_flat_compile_exp t env (If e1 e2 e3:dTree) =
        If None
           (source_to_flat_compile_exp t env e1)
           (source_to_flat_compile_exp t env e2)
           (source_to_flat_compile_exp t env e3)`;
   `source_to_flat_compile_exp t env (Mat e pes:flatLang_exp) =
        Mat None (source_to_flat_compile_exp t env e)
          (compile_pes t env pes)`;
   `source_to_flat_compile_exp t env (Let (SOME x) e1 e2:flatLang_exp) =
          Let None (SOME x) (source_to_flat_compile_exp (x :: t) env
            e1)
            (source_to_flat_compile_exp t (?_v_fupd (K (nsBind x
              (Local None x) (?_v env))) env) e2)`;
   `source_to_flat_compile_exp t env (Let NONE e1 e2:flatLang_exp) =
        Let None NONE (source_to_flat_compile_exp t env e1)
          (source_to_flat_compile_exp t env e2)`;
   `source_to_flat_compile_exp t env (ast_Letrec funs e:flatLang_exp) =
        (let fun_names = MAP FST funs in
        let new_env = nsBindList (MAP (\x. (x,Local None x))
          fun_names) (?_v env) in
          flatLang_Letrec (join_all_names t) (compile_funs t
            (?_v_fupd (K new_env) env) funs)
                   (source_to_flat_compile_exp t (?_v_fupd (K
                     new_env) env) e))`;
   `source_to_flat_compile_exp t env (Tannot e _10:flatLang_exp) =
  source_to_flat_compile_exp t env e`;
   `source_to_flat_compile_exp t env (Lannot e (Locs st
  en):flatLang_exp) = source_to_flat_compile_exp t env e`;
   `source_to_flat_compile_exps t env [] = []`;
   `source_to_flat_compile_exps t env (e :: es) =
         source_to_flat_compile_exp t env e ::
           source_to_flat_compile_exps t env es`;
   `compile_pes t env [] = []`;
   `compile_pes t env ((p,e) :: pes) =
        (let pbs = pat_bindings p in
        let pts = pat_tups None pbs in
        (compile_pat env p,source_to_flat_compile_exp t (?_v_fupd
          (K (nsBindList pts (?_v env))) env) e) :: compile_pes t env
          pes)`;
   `compile_funs t env [] = []`;
   `compile_funs t env ((f,x,e) :: funs) =
        (f,x,source_to_flat_compile_exp (f :: t) (?_v_fupd (K
          (nsBind x (Local None x) (?_v env))) env) e) ::
        compile_funs t env funs`];;
hol4_overload "compile_exp" "source_to_flat_compile_exp";;
hol4_overload "compile_exps" "source_to_flat_compile_exps";;

let om_tra_def = cake_define
  `om_tra = Cons orphan_trace 1`;;

let alloc_defs_def = cake_define
  `(alloc_defs n next [] = []) /\
   (alloc_defs n next (x :: xs) =
     (x,Glob om_tra next) :: alloc_defs (n + 1) (next + 1) xs)`;;

let make_varls_def = cake_define
  `make_varls n t idx x4 =
        match (t,x4) with
          (t,[]) -> Con None NONE []
        | (t,[x]) -> App None (GlobalVarInit idx) [Var_local None x]
        | ((t:tra),(x :: xs)) ->
         (Let None NONE (App None (GlobalVarInit idx) [Var_local None
           x])
           (make_varls (n + 1) None (idx + 1) xs):flatLang_exp)`;;

let empty_env_def = cake_define
  `source_to_flat_empty_env = mk_? nsEmpty nsEmpty`;;
hol4_overload "empty_env" "source_to_flat_empty_env";;

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
     let (tag,new_cids) = lookup_inc arity cids in
       (nsBind cn tag ns,new_cids,(tag,arity) :: tag_list)))`;;

let alloc_tags_def = cake_define
  `alloc_tags tid ctors =
     (let (con_ns,cid_spt,tag_list) = alloc_tags1 (REVERSE ctors) in
     let data = SOME (tid,REVERSE tag_list) in
     (nsMap (\tag. (tag,data)) con_ns,cid_spt))`;;

let env_id_tuple_def = cake_define
  `env_id_tuple gen id' = Con None NONE
     [Lit None (IntLit (&gen)); Lit None (IntLit (&id'))]`;;

let simple_dlet_def = cake_define
  `simple_dlet p e =
     (match p with ast_Pvar pv -> (match e with ast_Var v -> SOME
       (pv,v) | _11 -> NONE) | _12 -> NONE)`;;

let _ = size_thms "dec";;
let _ = size_thms "list";;
(* HOL4 termination: *)
let compile_decs_def = cake_define_wf
  `MEASURE (list_size dec_size o SND o SND o SND o SND o SND)`
  `source_to_flat_compile_decs t n next env envs x6 =
        match (t,x6) with
          ((t:mlstring list),[Dlet locs p e]) ->
        (match simple_dlet p e with SOME (pv,v) ->
            (match nsLookup (?_v env) v with SOME (Glob t i) ->
                    (n,next,mk_? (alist_to_ns [(pv,Glob t i)])
                      nsEmpty,envs,[]) | _13 -> (n,next,mk_? nsEmpty
                      nsEmpty,envs,[])) | NONE ->
            (let n' = n + 4 in
            let xs = REVERSE (pat_bindings p) in
            let e' = compile_exp (xs ++ t) env e in
            let l = LENGTH xs in
            let n'' = n' + l in
              (n'',(next_indices_vidx_fupd (K (next_indices_vidx next
                + l)) next),
               mk_? (alist_to_ns (alloc_defs n' (next_indices_vidx
                 next) xs)) nsEmpty,
               envs,
               [Mat None e'
                  [(compile_pat env p,make_varls 0 None
                    (next_indices_vidx next) xs)]])))
        | (t,[Dletrec locs funs]) ->
        (let fun_names = MAP FST funs in
        let new_env = nsBindList (MAP (\x. (x,Local None x))
          fun_names) (?_v env) in
        let flat_funs = compile_funs t (?_v_fupd (K new_env) env)
          funs in
        let n' = n + 1 in
        let env' = mk_? (alist_to_ns (alloc_defs n'
          (next_indices_vidx next) (REVERSE fun_names))) nsEmpty in
          (n' + LENGTH funs,(next_indices_vidx_fupd (K
            (next_indices_vidx next + LENGTH funs)) next),
           env',envs,
           [(flatLang_Letrec (join_all_names t) flat_funs
              (make_varls 0 None (next_indices_vidx next) (REVERSE
                fun_names)))]))
        | (t,[Dtype locs type_def]) ->
       (let new_env = MAPi (\tid (_14,_15,constrs). alloc_tags
         (next_indices_tidx next + tid) constrs) type_def in
        (n,(next_indices_tidx_fupd (K (next_indices_tidx next +
          LENGTH type_def)) next),
         mk_? nsEmpty (FOLDL (\ns (l,cids). nsAppend l ns) nsEmpty
           new_env),
         envs,
         []))
        | (_16,[Dtabbrev locs tvs tn t]) ->
        (n,next,empty_env,envs,[])
        | (t,[Dexn locs cn ts]) ->
        (n,(next_indices_eidx_fupd (K (next_indices_eidx next + 1))
          next),
         mk_? nsEmpty (nsSing cn (next_indices_eidx next,NONE)),
         envs,
         [])
        | (t,[Dmod mn ds]) ->
        (let (n',next',new_env,envs',ds') =
          source_to_flat_compile_decs (mn :: t) n next env envs ds in
          (n',next',(lift_env mn new_env),envs',ds'))
        | (t,[Dlocal lds ds]) ->
        (let (n',next1,new_env1,envs',lds') =
          source_to_flat_compile_decs t n next env envs lds in
        let (n'',next2,new_env2,envs'',ds') =
          source_to_flat_compile_decs t n' next1
           (extend_env new_env1 env) envs' ds in
             (n'',next2,new_env2,envs'',lds' ++ ds'))
        | (t,[Denv nenv]) ->
        (n + 1,next_indices_vidx_fupd (K (next_indices_vidx next +
          1)) next,
           mk_? (nsBind nenv (Glob None (next_indices_vidx next))
             nsEmpty) nsEmpty,?_envs_fupd (K (insert (?_next envs) env
             (?_envs envs))) (?_next_fupd (K (?_next envs + 1))
           envs),
           [(App None (GlobalVarInit (next_indices_vidx next))
               [env_id_tuple (?_generation envs) (?_next envs)])])
        | (t,[]) ->
       (n,next,empty_env,envs,[])
        | (t,(d :: ds)) ->
        (let (n',next1,new_env1,envs1,d') =
          source_to_flat_compile_decs t n next env envs [d] in
        let (n'',next2,new_env2,envs2,ds') =
          source_to_flat_compile_decs t n' next1 (extend_env new_env1
            env) envs1 ds in
          (n'',next2,extend_env new_env2 new_env1,envs2,d' ++
            ds'))`;;
hol4_overload "compile_decs" "source_to_flat_compile_decs";;

let source_to_flat_config_FIELDS = define_record "source_to_flat_config"
  ["next","next_indices";
   "mod_env","source_to_flat_environment";
   "pattern_cfg","flat_pattern_config";
   "envs","environment_store"];;

let empty_config_def = cake_define
  `empty_config =
     mk_? (mk_next_indices 0 0 0) empty_env
       (flat_pattern_init_config 0) (mk_? 0 LN)`;;

let compile_flat_def = cake_define
  `compile_flat pcfg =
     MAP (compile_dec pcfg) o remove_flat_prog`;;

let glob_alloc_def = cake_define
  `glob_alloc next c =
       (Let om_tra NONE
         (App om_tra
           (GlobalVarAlloc (next_indices_vidx next -
             next_indices_vidx (?_next c))) [])
         (flatLang_Con om_tra NONE []))`;;

let alloc_env_ref_def = cake_define
  `alloc_env_ref = (App None (GlobalVarInit 0)
     [App None (Src Opref) [Con None NONE []]])`;;

let compile_prog_def = cake_define
  `source_to_flat_compile_prog c p =
     (let next = next_indices_vidx_fupd (K (next_indices_vidx (?_next
       c) + 1)) (?_next c) in
     let envs = mk_? 0 (?_next (?_envs c)) LN in
     let (_17,next,e,gen,p') = compile_decs [] 1 next
       (source_to_flat_config_mod_env c) envs p in
     let envs2 = mk_? (?_next (?_envs c) + 1) (insert (?_next (?_envs
       c)) (?_envs gen) (environment_store_env_gens (?_envs c))) in
     (source_to_flat_config_mod_env_fupd (K e) (?_envs_fupd (K envs2)
       (?_next_fupd (K next) c)),
         glob_alloc next c :: alloc_env_ref :: p'))`;;
hol4_overload "compile_prog" "source_to_flat_compile_prog";;

let lookup_env_id_def = cake_define
  `lookup_env_id env_id envs = (match lookup (FST env_id)
  (environment_store_env_gens envs) with NONE -> empty_env | SOME gen
  -> (match lookup (SND env_id) gen with NONE -> empty_env | SOME env
  -> env))`;;

let store_env_id_def = cake_define
  `store_env_id gen id' =
     Let None (SOME (implode "r")) (flatLang_App None
       (GlobalVarLookup 0) [])
       (App None (Src Opassign) [Var_local None (implode "r");
         env_id_tuple gen id'])`;;

let inc_compile_prog_def = cake_define
  `inc_compile_prog env_id c p =
     (let env = lookup_env_id env_id (?_envs c) in
     let envs = mk_? 0 (?_next (?_envs c)) LN in
     let (_18,next,e,gen,p') = compile_decs [] 1 (?_next c) env envs
       p in
     let gen_envs = insert (?_next gen) (extend_env e env) (?_envs
       gen) in
     let envs2 = mk_? (?_next (?_envs c) + 1) (insert (?_next (?_envs
       c)) gen_envs (environment_store_env_gens (?_envs c))) in
     (?_envs_fupd (K envs2) (?_next_fupd (K next) c),(
         glob_alloc next c :: p') ++ [store_env_id (?_generation
           gen) (?_next gen)]))`;;

let compile_def = cake_define
  `source_to_flat_compile c p =
     (let (c',p') = compile_prog c p in
     let p' = compile_flat (source_to_flat_config_pattern_cfg c') p'
       in
       (c',p'))`;;
hol4_overload "compile" "source_to_flat_compile";;

(* note that flat_elim is always disabled in the eval/incremental case
   *)
let inc_compile_def = cake_define
  `inc_compile env_id c p =
     (let (c',p') = inc_compile_prog env_id c p in
     let p' = MAP (compile_dec (source_to_flat_config_pattern_cfg
       c')) p' in
       (c',p'))`;;
