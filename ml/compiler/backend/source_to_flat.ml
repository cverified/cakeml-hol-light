(* ======================================================== *)
(*  source_to_flat: ported from HOL4's
    compiler/backend/source_to_flatScript.sml
    A definition theory, with 31 definitions, 6 datatypes and 8
    theorems.  Needed by backend.ml, backendProof.ml, presLang.ml
    and source_to_flatProof.ml.  *)
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
needs "lib/indexedLists.ml";;
needs "lib/location.ml";;
needs "lib/sptree.ml";;
needs "semantics/ast.ml";;
needs "semantics/evaluate.ml";;
needs "semantics/namespace.ml";;

(* the theories whose names the Ancestors blocks of the source
   bring, which are the ones that its statements read: the
   overloads of every other theory come out of the interface
   while this file loads *)
let _ = hol4_ancestors "source_to_flat"
  ["ast"; "evaluate"; "flatLang"; "flat_elim"; "flat_pattern"];;

let var_name_INDUCT,var_name_RECURSION = define_datatype
  "var_name = source_to_flat_Glob (tra) (num) | source_to_flat_Local \
   (tra) (mlstring)";;
hol4_overload "Glob" "source_to_flat_Glob";;
hol4_overload "Local" "source_to_flat_Local";;

let source_to_flat_environment_FIELDS =
  define_record "source_to_flat_environment"
  ["c","(mlstring,mlstring,num#(num#(num#num) list) option)namespace";
   "v","(mlstring,mlstring,var_name)namespace"];;

let environment_generation_store_FIELDS =
  define_record "environment_generation_store"
  ["next","num";
   "generation","num";
   "envs","source_to_flat_environment spt"];;
hol4_field_overload "next" "environment_generation_store_next";;
hol4_field_overload "next_fupd"
  "environment_generation_store_next_fupd";;
hol4_field_overload "generation"
  "environment_generation_store_generation";;
hol4_field_overload "generation_fupd"
  "environment_generation_store_generation_fupd";;
hol4_field_overload "envs" "environment_generation_store_envs";;
hol4_field_overload "envs_fupd"
  "environment_generation_store_envs_fupd";;

let environment_store_FIELDS = define_record "environment_store"
  ["next","num";
   "env_gens","(source_to_flat_environment spt) spt"];;
hol4_field_overload "next" "environment_store_next";;
hol4_field_overload "next_fupd" "environment_store_next_fupd";;

let compile_var_def = cake_define_list
  [`compile_var t (source_to_flat_Glob _1 i) = App t
  (flatLang_GlobalVarLookup i) []`;
   `compile_var t (source_to_flat_Local _3 s:var_name) =
  flatLang_Var_local t s`];;

(* HOL4 source_to_flatScript.sml:51-55: a theorem whose statement the
   port cannot state yet: ast_pat1_size *)

let _ = size_thms "pattern_semantics_pat";;
(* HOL4 source_to_flatScript.sml:68-72: the tactic that proves the
   termination *)
let compile_pat_def = cake_define_wf
  `MEASURE (pattern_semantics_pat_size o SND)`
  `(compile_pat env (ast_Pvar v) = flatLang_Pvar v) /\
   (compile_pat env Pany = Pany) /\
   (compile_pat env (Plit l) = Plit l) /\
   (compile_pat env (ast_Pcon id' ps) =
     flatLang_Pcon
       (OPTION_JOIN (OPTION_MAP (nsLookup
         (source_to_flat_environment_c env)) id'))
       (MAP (compile_pat env) ps)) /\
   (compile_pat env (Pref p) = Pref (compile_pat env p)) /\
   (compile_pat env (Pas p i) = Pas (compile_pat env p) i) /\
   (compile_pat env (ast_Ptannot p t) = compile_pat env p)`;;

let pat_tups_def = cake_define_list
  [`pat_tups t [] = []`;
   `pat_tups t (x :: xs) =
       (let t' = mk_cons t ((LENGTH xs) + 1) in
         (x,source_to_flat_Local t' x) :: pat_tups t xs)`];;

let astOp_to_flatOp_def = cake_define
  `(astOp_to_flatOp (op:ast_op):flatLang_op) =
   (match op with ast_Opderef -> flatLang_El 0 | _4 ->
     flatLang_Src op)`;;

let type_group_id_type_def = cake_define
  `type_group_id_type x1 =
      match x1 with
        NONE -> NONE
      | (SOME (cn,NONE)) -> SOME (cn,NONE)
      | (SOME (cn,(SOME (ty_id,ctors)))) -> SOME (cn,SOME ty_id)`;;

let type_group_id_type_MAP = prove
 (`type_group_id_type = OPTION_MAP (I ## OPTION_MAP FST)`,
  CHEAT_TAC);;

let str_sep_def = cake_define
  `str_sep = (implode "_")`;;

let join_all_names_aux_def = cake_define_list
  [`join_all_names_aux [] ys = ys`;
   `join_all_names_aux (x :: xs) ys =
      (match ys with [] -> join_all_names_aux xs (x :: ys) | _6
        -> join_all_names_aux xs (x :: str_sep :: ys))`];;

let join_all_names_def = cake_define
  `join_all_names xs =
     (match xs with [x] -> x | _7 -> mlstring_concat
       (join_all_names_aux xs []))`;;

let _ = size_thms "ast_exp";;
let _ = size_thms "ast_pat";;
let _ = size_thms "mlstring";;
(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
let source_to_flat_compile_exp_def = cake_define_list_wf
  `inv_image (<) (\x. match x with INL (t,x,e) -> ast_exp_size e | INR
  (INL (t,x,es)) -> list_size ast_exp_size es | INR (INR (INL
  (t,x,pes))) -> list_size (pair_size ast_pat_size ast_exp_size) pes |
  INR (INR (INR (t,x,funs))) -> list_size (pair_size mlstring_size
  (pair_size mlstring_size ast_exp_size)) funs)`
  [`source_to_flat_compile_exp (t:mlstring list)
  (env:source_to_flat_environment) (Raise e:ast_exp) =
        flatLang_Raise backend_common_None
          (source_to_flat_compile_exp t env e)`;
   `source_to_flat_compile_exp (t:mlstring list)
  (env:source_to_flat_environment) (Handle e pes:ast_exp) =
        flatLang_Handle backend_common_None
          (source_to_flat_compile_exp t env e) (compile_pes t env
          pes)`;
   `source_to_flat_compile_exp (t:mlstring list)
  (env:source_to_flat_environment) (ast_Lit l) = flatLang_Lit
  backend_common_None l`;
   `source_to_flat_compile_exp (t:mlstring list)
  (env:source_to_flat_environment) (Con cn es:ast_exp) =
        flatLang_Con backend_common_None (OPTION_JOIN (OPTION_MAP
          (type_group_id_type o nsLookup (source_to_flat_environment_c
          env)) cn))
              (source_to_flat_compile_exps t env es)`;
   `source_to_flat_compile_exp (t:mlstring list)
  (env:source_to_flat_environment) (ast_Var x:ast_exp) =
        (match nsLookup (source_to_flat_environment_v env) x with
          NONE -> flatLang_Var_local backend_common_None (implode "") |
          // Can't happen
          SOME x -> compile_var backend_common_None x)`;
   `source_to_flat_compile_exp (t:mlstring list)
  (env:source_to_flat_environment) (Fun x e:ast_exp) =
        flatLang_Fun (join_all_names t) x
          (source_to_flat_compile_exp t
            (source_to_flat_environment_v_fupd (K (nsBind x
            (source_to_flat_Local backend_common_None x)
            (source_to_flat_environment_v env))) env) e)`;
   `source_to_flat_compile_exp (t:mlstring list)
  (env:source_to_flat_environment) (ast_App op es) =
        (if op = ast_AallocEmpty then
          ITLIST (flatLang_Let backend_common_None NONE)
            (REVERSE (source_to_flat_compile_exps t env es))
              (flatLang_App backend_common_None (flatLang_Src
              ast_Aalloc) [flatLang_Lit backend_common_None (ast_IntLit
              (&0));
                              flatLang_Lit backend_common_None
                                (ast_IntLit (&0))]) else
        if op = ast_Eval then
          flatLang_Mat backend_common_None (flatLang_Con
            backend_common_None NONE (source_to_flat_compile_exps t env
            es))
            [(flatLang_Pcon NONE [flatLang_Pany; flatLang_Pany;
              flatLang_Pany; flatLang_Pany; flatLang_Pvar (implode
              "bytes"); flatLang_Pvar (implode "words")],
                flatLang_Let backend_common_None NONE (flatLang_App
                  backend_common_None (flatLang_Src ast_Eval)
                        (MAP (flatLang_Var_local
                          backend_common_None) [(implode "bytes");
                          (implode "words")]))
                    (flatLang_Let backend_common_None (SOME (implode
                      "r")) (flatLang_App backend_common_None
                      (flatLang_GlobalVarLookup 0) [])
                        (flatLang_App backend_common_None
                          (flatLang_El 0) [flatLang_Var_local
                          backend_common_None (implode "r")])))] else
        if op = ast_Env_id then (match es with [_8] -> (match
          source_to_flat_compile_exps t env es with x :: xs -> x | _9 ->
          flatLang_Var_local backend_common_None (implode "")) |
            // Can't happen
            // possible only if one of es raises an exception
            _10 -> flatLang_App backend_common_None (flatLang_El 0)
              (source_to_flat_compile_exps t env es)) else
          flatLang_App backend_common_None (astOp_to_flatOp op)
            (source_to_flat_compile_exps t env es))`;
   `source_to_flat_compile_exp (t:mlstring list)
  (env:source_to_flat_environment) (ast_Log lop e1 e2) =
          (match lop with Andalso ->
            flatLang_If backend_common_None
               (source_to_flat_compile_exp t env e1)
               (source_to_flat_compile_exp t env e2)
               (flatLang_Bool backend_common_None F) | Orelse ->
            flatLang_If backend_common_None
               (source_to_flat_compile_exp t env e1)
               (flatLang_Bool backend_common_None T)
               (source_to_flat_compile_exp t env e2))`;
   `source_to_flat_compile_exp (t:mlstring list)
  (env:source_to_flat_environment) (If e1 e2 e3:ast_exp) =
        flatLang_If backend_common_None
           (source_to_flat_compile_exp t env e1)
           (source_to_flat_compile_exp t env e2)
           (source_to_flat_compile_exp t env e3)`;
   `source_to_flat_compile_exp (t:mlstring list)
  (env:source_to_flat_environment) (Mat e pes:ast_exp) =
        flatLang_Mat backend_common_None
          (source_to_flat_compile_exp t env e) (compile_pes t env
          pes)`;
   `source_to_flat_compile_exp (t:mlstring list)
  (env:source_to_flat_environment) (Let (SOME x) e1 e2:ast_exp) =
          flatLang_Let backend_common_None (SOME x)
            (source_to_flat_compile_exp (x :: t) env e1)
            (source_to_flat_compile_exp t
              (source_to_flat_environment_v_fupd (K (nsBind x
              (source_to_flat_Local backend_common_None x)
              (source_to_flat_environment_v env))) env) e2)`;
   `source_to_flat_compile_exp (t:mlstring list)
  (env:source_to_flat_environment) (Let NONE e1 e2:ast_exp) =
        flatLang_Let backend_common_None NONE
          (source_to_flat_compile_exp t env e1)
          (source_to_flat_compile_exp t env e2)`;
   `source_to_flat_compile_exp (t:mlstring list)
  (env:source_to_flat_environment) (ast_Letrec funs e) =
        (let fun_names = MAP FST funs in
        let new_env = nsBindList (MAP (\x. (x,source_to_flat_Local
          backend_common_None x)) fun_names)
          (source_to_flat_environment_v env) in
          flatLang_Letrec (join_all_names t) (compile_funs t
            (source_to_flat_environment_v_fupd (K new_env) env) funs)
                   (source_to_flat_compile_exp t
                     (source_to_flat_environment_v_fupd (K new_env)
                     env) e))`;
   `source_to_flat_compile_exp (t:mlstring list)
  (env:source_to_flat_environment) (ast_Tannot e _11) =
  source_to_flat_compile_exp t env e`;
   `// When encountering a Lannot, we update the trace we are passing
    source_to_flat_compile_exp (t:mlstring list)
      (env:source_to_flat_environment) (ast_Lannot e (Locs st en)) =
      source_to_flat_compile_exp t env e`;
   `source_to_flat_compile_exps (t:mlstring list)
  (env:source_to_flat_environment) [] = []`;
   `source_to_flat_compile_exps (t:mlstring list)
  (env:source_to_flat_environment) (e :: es) =
         source_to_flat_compile_exp t env e ::
           source_to_flat_compile_exps t env es`;
   `compile_pes (t:mlstring list) (env:source_to_flat_environment) []
  = []`;
   `compile_pes (t:mlstring list) (env:source_to_flat_environment)
  ((p,e) :: pes) =
        (let pbs = pat_bindings p in
        let pts = pat_tups backend_common_None pbs in
        (compile_pat env p,source_to_flat_compile_exp t
          (source_to_flat_environment_v_fupd (K (nsBindList pts
          (source_to_flat_environment_v env))) env) e) :: compile_pes
          t env pes)`;
   `compile_funs (t:mlstring list) (env:source_to_flat_environment)
  [] = []`;
   `compile_funs (t:mlstring list) (env:source_to_flat_environment)
  ((f,x,e) :: funs) =
        (f,x,source_to_flat_compile_exp (f :: t)
          (source_to_flat_environment_v_fupd (K (nsBind x
          (source_to_flat_Local backend_common_None x)
          (source_to_flat_environment_v env))) env) e) ::
        compile_funs t env funs`];;
hol4_overload "compile_exp" "source_to_flat_compile_exp";;
hol4_overload "compile_exps" "source_to_flat_compile_exps";;

let compile_exps_append = prove
 (`!env es es'.
    compile_exps t env (es ++ es') =
    compile_exps t env es ++ compile_exps t env es'`,
  CHEAT_TAC);;

let compile_exps_reverse = prove
 (`!env es.
    compile_exps t env (REVERSE es) = REVERSE (compile_exps t env
      es)`,
  CHEAT_TAC);;

let compile_funs_map = prove
 (`!env funs.
    compile_funs t env funs =
      MAP (\(f,x,e). (f,x,compile_exp
        (f :: t) (source_to_flat_environment_v_fupd (K (nsBind x
          (source_to_flat_Local backend_common_None x)
          (source_to_flat_environment_v env))) env) e)) funs`,
  CHEAT_TAC);;

let compile_funs_dom = prove
 (`!funs.
    (MAP (\(x,y,z). x) funs) =
    (MAP (\(x,y,z). x) (compile_funs t env funs))`,
  CHEAT_TAC);;

let om_tra_def = cake_define
  `om_tra = Cons orphan_trace 1`;;

let alloc_defs_def = cake_define_list
  [`alloc_defs n next' [] = []`;
   `alloc_defs n next' (x :: xs) =
        (x,source_to_flat_Glob om_tra next') :: alloc_defs (n +
          1) (next' + 1) xs`];;

let fst_alloc_defs = prove
 (`!n next' l. MAP FST (alloc_defs n next' l) = l`,
  CHEAT_TAC);;

let alloc_defs_append = prove
 (`!m n l1 l2.
     alloc_defs m n (l1 ++ l2) =
     alloc_defs m n l1 ++ alloc_defs (m + LENGTH l1) (n + LENGTH
       l1) l2`,
  CHEAT_TAC);;

let make_varls_def = cake_define
  `make_varls n t idx x4 =
        match (t,x4) with
          (t,[]) -> Con backend_common_None NONE []
        | (t,[x]) -> App backend_common_None (flatLang_GlobalVarInit
          idx) [flatLang_Var_local backend_common_None x]
        | ((t:tra),(x :: xs)) ->
         (Let backend_common_None NONE (App backend_common_None
           (flatLang_GlobalVarInit idx) [flatLang_Var_local
           backend_common_None x])
           (make_varls (n + 1) backend_common_None (idx + 1)
             xs):flatLang_exp)`;;

let empty_env_def = cake_define
  `source_to_flat_empty_env = mk_source_to_flat_environment nsEmpty
  nsEmpty`;;
hol4_overload "empty_env" "source_to_flat_empty_env";;

let extend_env_def = cake_define
  `extend_env e1 e2 =
     mk_source_to_flat_environment (nsAppend
       (source_to_flat_environment_c e1)
       (source_to_flat_environment_c e2)) (nsAppend
       (source_to_flat_environment_v e1)
       (source_to_flat_environment_v e2))`;;

let lift_env_def = cake_define
  `lift_env mn e = mk_source_to_flat_environment (nsLift mn
  (source_to_flat_environment_c e)) (nsLift mn
  (source_to_flat_environment_v e))`;;

let next_indices_FIELDS = define_record "next_indices"
  ["vidx","num";
   "tidx","num";
   "eidx","num"];;

let lookup_inc_def = cake_define
  `lookup_inc i t =
     (match sptree_lookup i t with NONE -> (0,sptree_insert i 1 t)
       | SOME n -> (n,sptree_insert i (n + 1) t))`;;

let alloc_tags1_def = cake_define_list
  [`alloc_tags1 [] = (nsEmpty,LN,[])`;
   `alloc_tags1 ((cn,ts) :: ctors) =
        (let (ns,cids,tag_list) = alloc_tags1 ctors in
        let arity = LENGTH ts in
        let (tag,new_cids) = lookup_inc arity cids in
          (nsBind cn tag ns,new_cids,(tag,arity) :: tag_list))`];;

let alloc_tags_def = cake_define
  `alloc_tags tid ctors =
     (let (con_ns,cid_spt,tag_list) = alloc_tags1 (REVERSE ctors) in
     let data = SOME (tid,REVERSE tag_list) in
     (nsMap (\tag. (tag,data)) con_ns,cid_spt))`;;

let env_id_tuple_def = cake_define
  `env_id_tuple gen id' = Con backend_common_None NONE
     [Lit backend_common_None (ast_IntLit (&gen)); Lit
       backend_common_None (ast_IntLit (&id'))]`;;

let simple_dlet_def = cake_define
  `simple_dlet p e =
     (match p with ast_Pvar pv -> (match e with ast_Var v -> SOME
       (pv,v) | _12 -> NONE) | _13 -> NONE)`;;

let _ = size_thms "dec";;
let source_to_flat_compile_decs_def = cake_define_wf
  `MEASURE (list_size dec_size o SND o SND o SND o SND o SND)`
  `source_to_flat_compile_decs t n next' env envs' x6 =
        match (t,x6) with
          ((t:mlstring list),[Dlet locs p e]) ->
        (match simple_dlet p e with SOME (pv,v) ->
            (match nsLookup (source_to_flat_environment_v env) v with
              SOME (source_to_flat_Glob t i) ->
                    (n,next',mk_source_to_flat_environment nsEmpty
                      (alist_to_ns [(pv,source_to_flat_Glob t
                      i)]),envs',[]) | _14 ->
                      (n,next',mk_source_to_flat_environment nsEmpty
                      nsEmpty,envs',[])) | NONE ->
            (let n' = n + 4 in
            let xs = REVERSE (pat_bindings p) in
            let e' = compile_exp (xs ++ t) env e in
            let l = LENGTH xs in
            let n'' = n' + l in
              (n'',(next_indices_vidx_fupd (K (next_indices_vidx
                next' + l)) next'),
               mk_source_to_flat_environment nsEmpty (alist_to_ns
                 (alloc_defs n' (next_indices_vidx next') xs)),
               envs',
               [Mat backend_common_None e'
                  [(compile_pat env p,make_varls 0
                    backend_common_None (next_indices_vidx next')
                    xs)]])))
        | (t,[Dletrec locs funs]) ->
        (let fun_names = MAP FST funs in
        let new_env = nsBindList (MAP (\x. (x,source_to_flat_Local
          backend_common_None x)) fun_names)
          (source_to_flat_environment_v env) in
        let flat_funs = compile_funs t
          (source_to_flat_environment_v_fupd (K new_env) env) funs in
        let n' = n + 1 in
        let env' = mk_source_to_flat_environment nsEmpty (alist_to_ns
          (alloc_defs n' (next_indices_vidx next') (REVERSE fun_names)))
          in
          (n' + LENGTH funs,(next_indices_vidx_fupd (K
            (next_indices_vidx next' + LENGTH funs)) next'),
           env',envs',
           [(flatLang_Letrec (join_all_names t) flat_funs
              (make_varls 0 backend_common_None (next_indices_vidx
                next') (REVERSE fun_names)))]))
        | (t,[Dtype locs type_def]) ->
       (let new_env = MAPi (\tid (_15,_16,constrs). alloc_tags
         (next_indices_tidx next' + tid) constrs) type_def in
        (n,(next_indices_tidx_fupd (K (next_indices_tidx next' +
          LENGTH type_def)) next'),
         mk_source_to_flat_environment (FOLDL (\ns (l,cids). nsAppend
           l ns) nsEmpty new_env) nsEmpty,
         envs',
         []))
        | (_17,[Dtabbrev locs tvs tn t]) ->
        (n,next',source_to_flat_empty_env,envs',[])
        | (t,[Dexn locs cn ts]) ->
        (n,(next_indices_eidx_fupd (K (next_indices_eidx next' + 1))
          next'),
         mk_source_to_flat_environment (nsSing cn (next_indices_eidx
           next',NONE)) nsEmpty,
         envs',
         [])
        | (t,[Dmod mn ds]) ->
        (let (n',next',new_env,envs',ds') =
          source_to_flat_compile_decs (mn :: t) n next' env envs' ds in
          (n',next',(lift_env mn new_env),envs',ds'))
        | (t,[Dlocal lds ds]) ->
        (let (n',next1,new_env1,envs',lds') =
          source_to_flat_compile_decs t n next' env envs' lds in
        let (n'',next2,new_env2,envs'',ds') =
          source_to_flat_compile_decs t n' next1
           (extend_env new_env1 env) envs' ds in
             (n'',next2,new_env2,envs'',lds' ++ ds'))
        | (t,[Denv nenv]) ->
        (n + 1,next_indices_vidx_fupd (K (next_indices_vidx next' +
          1)) next',
           mk_source_to_flat_environment nsEmpty (nsBind nenv
             (source_to_flat_Glob backend_common_None (next_indices_vidx
             next')) nsEmpty),envs_fupd (K (sptree_insert (next envs')
             env (envs envs'))) (next_fupd (K (next envs' + 1))
           envs'),
           [(App backend_common_None (flatLang_GlobalVarInit
             (next_indices_vidx next'))
               [env_id_tuple (generation envs') (next envs')])])
        | (t,[]) ->
       (n,next',source_to_flat_empty_env,envs',[])
        | (t,(d :: ds)) ->
        (let (n',next1,new_env1,envs1,d') =
          source_to_flat_compile_decs t n next' env envs' [d] in
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
hol4_field_overload "next" "source_to_flat_config_next";;
hol4_field_overload "next_fupd" "source_to_flat_config_next_fupd";;
hol4_field_overload "envs" "source_to_flat_config_envs";;
hol4_field_overload "envs_fupd" "source_to_flat_config_envs_fupd";;

let empty_config_def = cake_define
  `empty_config =
     mk_source_to_flat_config (mk_next_indices 0 0 0)
       source_to_flat_empty_env (flat_pattern_init_config 0)
       (mk_environment_store 0 LN)`;;

let compile_flat_def = cake_define
  `compile_flat pcfg =
     MAP (compile_dec pcfg) o remove_flat_prog`;;

let glob_alloc_def = cake_define
  `glob_alloc next' c =
       (Let om_tra NONE
         (App om_tra
           (flatLang_GlobalVarAlloc (next_indices_vidx next' -
             next_indices_vidx (next c))) [])
         (flatLang_Con om_tra NONE []))`;;

let alloc_env_ref_def = cake_define
  `alloc_env_ref = (App backend_common_None (flatLang_GlobalVarInit 0)
     [App backend_common_None (flatLang_Src ast_Opref) [Con
       backend_common_None NONE []]])`;;

let source_to_flat_compile_prog_def = cake_define
  `source_to_flat_compile_prog c p =
     (let next' = next_indices_vidx_fupd (K (next_indices_vidx (next
       c) + 1)) (next c) in
     let envs' = mk_environment_generation_store 0 (next (envs c)) LN
       in
     let (_18,next',e,gen,p') = source_to_flat_compile_decs [] 1
       next' (source_to_flat_config_mod_env c) envs' p in
     let envs2 = mk_environment_store (next (envs c) + 1)
       (sptree_insert (next (envs c)) (envs gen)
       (environment_store_env_gens (envs c))) in
     (source_to_flat_config_mod_env_fupd (K e) (envs_fupd (K envs2)
       (next_fupd (K next') c)),
         glob_alloc next' c :: alloc_env_ref :: p'))`;;
hol4_overload "compile_prog" "source_to_flat_compile_prog";;

let lookup_env_id_def = cake_define
  `lookup_env_id env_id envs' = (match sptree_lookup (FST env_id)
  (environment_store_env_gens envs') with NONE ->
  source_to_flat_empty_env | SOME gen -> (match sptree_lookup (SND
  env_id) gen with NONE -> source_to_flat_empty_env | SOME env ->
  env))`;;

let store_env_id_def = cake_define
  `store_env_id gen id' =
     Let backend_common_None (SOME (implode "r")) (flatLang_App
       backend_common_None (flatLang_GlobalVarLookup 0) [])
       (App backend_common_None (flatLang_Src ast_Opassign)
         [flatLang_Var_local backend_common_None (implode "r");
         env_id_tuple gen id'])`;;

let inc_compile_prog_def = cake_define
  `inc_compile_prog env_id c p =
     (let env = lookup_env_id env_id (envs c) in
     let envs' = mk_environment_generation_store 0 (next (envs c)) LN
       in
     let (_19,next',e,gen,p') = source_to_flat_compile_decs [] 1
       (next c) env envs' p in
     let gen_envs = sptree_insert (next gen) (extend_env e env) (envs
       gen) in
     let envs2 = mk_environment_store (next (envs c) + 1)
       (sptree_insert (next (envs c)) gen_envs
       (environment_store_env_gens (envs c))) in
     (envs_fupd (K envs2) (next_fupd (K next') c),(
         glob_alloc next' c :: p') ++ [store_env_id (generation
           gen) (next gen)]))`;;

let source_to_flat_compile_def = cake_define
  `source_to_flat_compile c p =
     (let (c',p') = source_to_flat_compile_prog c p in
     let p' = compile_flat (source_to_flat_config_pattern_cfg c') p'
       in
       (c',p'))`;;
hol4_overload "compile" "source_to_flat_compile";;

(* note that flat_elim is always disabled in the eval/incremental case *)
let inc_compile_def = cake_define
  `inc_compile env_id c p =
     (let (c',p') = inc_compile_prog env_id c p in
     let p' = MAP (compile_dec (source_to_flat_config_pattern_cfg
       c')) p' in
       (c',p'))`;;

(* and the overloads that this file cannot see are back in the
   interface *)
let _ = unhide_overloads ();;
