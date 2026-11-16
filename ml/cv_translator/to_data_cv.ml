(* ======================================================== *)
(*  to_data_cv: ported from HOL4's
    cv_translator/to_data_cvScript.sml
    A definition theory, with 28 definitions and 141 theorems.
    Needed by 6 files of the port.  *)
(* ======================================================== *)

(*
  Translation of the to_data compiler function.
*)

needs "basis/pure/basis_cv.ml";;
needs "basis/pure/mlstring.ml";;
needs "characteristic/cfFFIType.ml";;
needs "compiler/backend/backend.ml";;
needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/bvi_tailrec.ml";;
needs "compiler/backend/bvl_const.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/clos_known.ml";;
needs "compiler/backend/clos_mti.ml";;
needs "compiler/backend/clos_op.ml";;
needs "compiler/backend/cv_compute/backend_asm.ml";;
needs "compiler/backend/db_vars.ml";;
needs "compiler/backend/flatLang.ml";;
needs "compiler/backend/flat_elim.ml";;
needs "compiler/backend/flat_pattern.ml";;
needs "compiler/backend/flat_to_clos.ml";;
needs "compiler/backend/source_to_flat.ml";;
needs "lib/cv_std.ml";;
needs "lib/indexedLists.ml";;
needs "lib/sptree.ml";;
needs "lib/term.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "semantics/namespace.ml";;
needs "semantics/proofs/source_cv.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "to_data_cv"
  ["backend"; "backend_asm"; "basis_cv"; "source_cv"];;

let _ = do_list hide_constant ["Num"; "Pair"];;

(* HOL4 to_data_cvScript.sml:10: ML code, not ported *)

(* [local,cv_inline] *)
let to_data_cv_list_mem = MEM;;

(* source_let *)

(* HOL4 to_data_cvScript.sml:16-19: ML code, not ported *)

(* HOL4 to_data_cvScript.sml:21: ML code, not ported *)
(* [cv_pre] *)
let source_let_compile_decs_pre = prove
 (`!v. source_let_compile_decs_pre v`,
  CHEAT_TAC);;

(* source_to_source *)

(* HOL4 to_data_cvScript.sml:31: ML code, not ported *)

(* source_to_flat *)
(* HOL4 to_data_cvScript.sml:34-40: ML code, not ported *)

let compile_pat_alt_def,compile_pat_alt_ind = define_guess
  `(compile_pat_alt env (ast_Pvar v) = flat_Pvar v) /\
   (compile_pat_alt env ast_Pany = (ast_Pany:ast_pat)) /\
   (compile_pat_alt env (ast_Plit l) = (ast_Plit l:ast_pat)) /\
   (compile_pat_alt env (ast_Pcon id ps) =
        flat_Pcon
          (OPTION_JOIN (OPTION_MAP (nsLookup (sem_env_c env)) id))
          (compile_pats_alt env ps)) /\
   (compile_pat_alt env (ast_Pref p) = ast_Pref (compile_pat_alt env p)) /\
   (compile_pat_alt env (ast_Pas p i) = ast_Pas (compile_pat_alt env p) i) /\
   (compile_pat_alt env (ast_Ptannot p t) = compile_pat_alt env p) /\
   (compile_pats_alt env [] = []) /\
   (compile_pats_alt env (CONS p ps) = CONS (compile_pat_alt env p)
    (compile_pats_alt env ps))`;;

(* HOL4 to_data_cvScript.sml:57: ML code, not ported *)

let compile_pat_alt_thm = prove
 (`(!v env. compile_pat_alt env v = compile_pat env v) /\
   (!v env. compile_pats_alt env v = MAP (compile_pat env) v)`,
  CHEAT_TAC);;

(* HOL4 to_data_cvScript.sml:66: ML code, not ported *)

(* HOL4 to_data_cvScript.sml:68-71: ML code, not ported *)

(* [cv_pre,local] *)
let source_to_flat_compile_exp_pre = prove
 (`(!t env v. source_to_flat_compile_exp_pre t env v) /\
   (!t env v. source_to_flat_compile_exps_pre t env v) /\
   (!t env v. source_to_flat_compile_pes_pre t env v) /\
   (!t env v. source_to_flat_compile_funs_pre t env v)`,
  CHEAT_TAC);;

let make_varls_alt_def,make_varls_alt_ind = define_guess
  `make_varls_alt idx x2 =
     match x2 with
       [] -> flat_Con backend_common_None NONE []
     | [x] -> flat_App backend_common_None (flat_GlobalVarInit idx)
       [flat_Var_local backend_common_None x]
     | CONS x xs ->
         (flat_Let backend_common_None NONE (flat_App backend_common_None
           (flat_GlobalVarInit idx) [flat_Var_local backend_common_None x])
           (make_varls_alt (idx + 1) xs):flat_exp)`;;

(* HOL4 to_data_cvScript.sml:93: ML code, not ported *)

let make_varls_alt_thm = prove
 (`!n tra idx xs. make_varls n tra idx xs = make_varls_alt idx xs`,
  CHEAT_TAC);;

(* HOL4 to_data_cvScript.sml:102: ML code, not ported *)

let list_size_mono = prove
 (`(!x. m x <= m' x) ==> list_size m xs <= list_size m' xs`,
  CHEAT_TAC);;

(* the clauses in two quotations: m is (('m , namespace) alist) and (_)list;
   v is (('n , 'v) alist) and (_#_)list; xs is (_#_)list and (_)list, which
   one quotation cannot typecheck *)
let nsMap_alt_def,nsMap_alt_ind = define_guess_clauses
  [`nsMap_alt data (Bind v m) = Bind (MAP (\(n,x). (n,(x,data))) v)
    (nsMap_alts data m)`;
   `(nsMap_alts data [] = []) /\
    (nsMap_alts data (CONS (x,y) xs) = CONS (x,nsMap_alt data y)
    (nsMap_alts data xs))`];;

let nsMap_alt_thm = prove
 (`(!data b. nsMap_alt (data:'d) (b:('a,'b,'c)namespace) = nsMap (\tag.
  (tag,data)) b) /\
   (!data xs. nsMap_alts (data:'d) (xs:('a#('a,'b,'c)namespace) list) =
     (MAP (\(mn,e). (mn,nsMap (\tag. (tag,data)) e)) xs))`,
  CHEAT_TAC);;

(* HOL4 to_data_cvScript.sml:126: ML code, not ported *)

(* HOL4 to_data_cvScript.sml:128-129: ML code, not ported *)

(* the clauses in two quotations: ds is (dec list) and (_)list; funs is
   ((varN # varN # exp) list) and (_#_)list; lds is (dec list) and (_)list,
   which one quotation cannot typecheck *)
let compile_decs_alt_def,compile_decs_alt_ind = define_guess_clauses
  [`(compile_dec_alt (t:mlstring list) n next' env envs' (Dlet locs p e) =
         match simple_dlet p e with SOME (pv,v) ->
             (match nsLookup (sem_env_v env) v with SOME
                 (source_to_flat_Glob t i) ->
                     (n,next',mk_sem_env (alist_to_ns
                         [(pv,source_to_flat_Glob t i)]) nsEmpty,envs',[])
              | _ -> (n,next',mk_sem_env nsEmpty nsEmpty,envs',[]))
         | NONE ->
             let n' = n + 4 in
             let xs = REVERSE (ast_pat_bindings p) in
             let e' = source_to_flat_compile_exp (APPEND xs t) env e in
             let l = LENGTH xs in
             let n'' = n' + l in
               (n'',(next_indices_vidx_fupd (K (next_indices_vidx next' +
                   l)) next'),
                mk_sem_env (alist_to_ns (alloc_defs n' (next_indices_vidx
                    next') xs)) nsEmpty,
                envs',
                [(flat_Mat backend_common_None e'
                  [(compile_pat env p,make_varls 0 data_to_word_None
                      (next_indices_vidx next') xs)])])) /\
    (compile_dec_alt (t:mlstring list) n next' env envs' (Dletrec locs funs) =
         let fun_names = MAP FST funs in
         let new_env = nsBindList (MAP (\x. (x,source_to_flat_Local
             backend_common_None x)) fun_names) (sem_env_v env) in
         let flat_funs = compile_funs t (sem_env_v_fupd (K new_env) env)
             funs in
         let n' = n + 1 in
         let env' = mk_sem_env (alist_to_ns (alloc_defs n'
             (next_indices_vidx next') (REVERSE fun_names))) nsEmpty in
           (n' + LENGTH funs,(next_indices_vidx_fupd (K (next_indices_vidx
               next' + LENGTH funs)) next'),
            env',envs',
            [(flat_Letrec (join_all_names t) flat_funs
               (make_varls 0 data_to_word_None (next_indices_vidx
                   next') (REVERSE fun_names)))])) /\
    (compile_dec_alt (t:mlstring list) n next' env envs' (Dtype locs type_def)
      =
        let new_env = MAPi (\tid (_,_,constrs). alloc_tags
            (next_indices_tidx next' + tid) constrs) type_def in
         (n,(next_indices_tidx_fupd (K (next_indices_tidx next' + LENGTH
             type_def)) next'),
          mk_sem_env nsEmpty (FOLDL (\ns (l,cids). nsAppend l ns) nsEmpty
              new_env),
          envs',[])) /\
    (compile_dec_alt _ n next' env envs' (Dtabbrev locs tvs tn t) =
         (n,next',source_to_flat_empty_env,envs',[])) /\
    (compile_dec_alt (t:mlstring list) n next' env envs' (Dexn locs cn ts) =
         (n,(next_indices_eidx_fupd (K (next_indices_eidx next' + 1))
             next'),
          mk_sem_env nsEmpty (nsSing cn (next_indices_eidx next',NONE)),
          envs',[])) /\
    (compile_dec_alt (t:mlstring list) n next' env envs' (Dlocal lds ds) =
         let (n',next1,new_env1,envs',lds') = compile_decs_alt t n next'
             env envs' lds in
         let (n'',next2,new_env2,envs'',ds') = compile_decs_alt t n' next1
            (source_to_flat_extend_env new_env1 env) envs' ds in
                (n'',next2,new_env2,envs'',APPEND lds' ds')) /\
    (compile_dec_alt (t:mlstring list) n next' env envs' (Denv nenv) =
         (n + 1,next_indices_vidx_fupd (K (next_indices_vidx next' + 1))
             next',
            mk_sem_env (nsBind nenv (source_to_flat_Glob
                backend_common_None (next_indices_vidx next')) nsEmpty)
                nsEmpty,envs_fupd (K (sptree_insert (next envs') env (envs
                envs'))) (next_fupd (K (next envs' + 1))
            envs'),
            [(flat_App backend_common_None (flat_GlobalVarInit
                (next_indices_vidx next'))
                [env_id_tuple (generation envs') (next envs')])])) /\
    (compile_decs_alt (t:mlstring list) n next' env envs' [] =
        (n,next',source_to_flat_empty_env,envs',[])) /\
    (compile_decs_alt (t:mlstring list) n next' env envs' (CONS d ds) =
         let (n',next1,new_env1,envs1,d') = compile_dec_alt t n next' env
             envs' d in
         let (n'',next2,new_env2,envs2,ds') =
           compile_decs_alt t n' next1 (source_to_flat_extend_env new_env1
               env) envs1 ds in
           (n'',next2,source_to_flat_extend_env new_env2
               new_env1,envs2,APPEND d' ds'))`;
   `compile_dec_alt (t:mlstring list) n next' env envs' (Dmod mn ds) =
         let (n',next',new_env,envs',ds') = compile_decs_alt (CONS mn t) n
             next' env envs' ds in
           (n',next',(lift_env mn new_env),envs',ds')`];;

let compile_decs_cons = prove
 (`source_to_flat_compile_decs t n next env envs (CONS d ds) =
      let (n',next1,new_env1,envs1,d') = source_to_flat_compile_decs t n
        next env envs [d] in
      let (n'',next2,new_env2,envs2,ds') =
        source_to_flat_compile_decs t n' next1 (source_to_flat_extend_env
          new_env1 env) envs1 ds in
        (n'',next2,source_to_flat_extend_env new_env2
          new_env1,envs2,APPEND d' ds')`,
  CHEAT_TAC);;

let compile_decs_thm = prove
 (`!t n next' env envs' xs.
   source_to_flat_compile_decs t n next' env envs' xs = compile_decs_alt t
     n next' env envs' xs`,
  CHEAT_TAC);;

(* HOL4 to_data_cvScript.sml:237: ML code, not ported *)

(* HOL4 to_data_cvScript.sml:239: ML code, not ported *)

(* HOL4 to_data_cvScript.sml:241: ML code, not ported *)

(* flat_pattern *)

let compile_pat_bindings_clocked_def,compile_pat_bindings_clocked_ind =
  define_guess
  `compile_pat_bindings_clocked x1 t i m exp =
   match (x1,m) with
     (_,[]) -> (LN,exp)
   | (0,m) -> (LN,exp)
   | (SUC ck,CONS (ast_Pany,_,_) m) ->
     compile_pat_bindings_clocked ck t i m exp
   | (SUC ck,CONS (ast_Pvar s,k,x) m) -> (
     let (spt,exp2) = compile_pat_bindings_clocked ck t i m exp in
     (sptree_insert k one spt,flat_Let t (SOME s) x exp2))
   | (SUC ck,CONS (ast_Plit _,_,_) m) ->
     compile_pat_bindings_clocked ck t i m exp
   | (SUC ck,CONS (ast_Pcon _ ps,k,x) m) -> (
     let j_nms = MAP (\(j,p). let k = i + 1 + j in
         let nm = enc_num_to_name k in
         ((j,nm),(p,k,flat_Var_local t nm))) (enumerate 0 ps) in
     let (spt,exp2) = compile_pat_bindings_clocked ck t (i + 2 + LENGTH ps)
         (APPEND (MAP SND j_nms) m) exp in
     let j_nms_used = FILTER (\(_,(_,k,_)). IS_SOME (sptree_lookup k spt))
       j_nms in
     let exp3 = ITLIST (\((j,nm),_) exp.
         flat_Let t (SOME nm) (flat_App t (flat_El j) [x]) exp) j_nms_used
           exp2 in
     let spt2 = (if NULL j_nms_used then spt else sptree_insert k one spt)
       in
     (spt2,exp3))
   | (SUC ck,CONS (ast_Pas p v,k,x) m) -> (
     let nm = enc_num_to_name (i + 1) in
     let (spt,exp2) = compile_pat_bindings_clocked ck t (i + 2)
                       (CONS (p,i + 1,flat_Var_local t nm) m) exp in
     (sptree_insert k one spt,flat_Let t (SOME v) x
                             (flat_Let t (SOME nm) (flat_Var_local t v)
                               exp2)))
   | (SUC ck,CONS (ast_Pref p,k,x) m) -> (
     let nm = enc_num_to_name (i + 1) in
     let (spt,exp2) = compile_pat_bindings_clocked ck t (i + 2)
         (CONS (p,i + 1,flat_Var_local t nm) m) exp in
     (sptree_insert k one spt,flat_Let t (SOME nm) (flat_App t (flat_El
       0) [x]) exp2))`;;

(* HOL4 to_data_cvScript.sml:279-280: ML code, not ported *)

(* [cv_pre,local] *)
let compile_pat_bindings_clocked_pre = prove
 (`!v0 v1 v2 v exp. compile_pat_bindings_clocked_pre v0 v1 v2 v exp`,
  CHEAT_TAC);;

(* TODO: Maybe move to HOL? *)
let list_size_SUM = prove
 (`list_size f ls =
   LENGTH ls + SUM (MAP f ls)`,
  CHEAT_TAC);;

make_size "pattern_semantics_pat";;
let compile_pat_bindings_thm = prove
 (`!n t i m exp.
   SUM (MAP (pattern_semantics_pat_size o FST) m) + LENGTH m <= n ==>
   compile_pat_bindings_clocked n t i m exp = compile_pat_bindings t i m
     exp`,
  CHEAT_TAC);;

let compile_pat_bindings_clocked_eq = prove
 (`compile_pat_bindings t i m exp = compile_pat_bindings_clocked (SUM (MAP
  (pattern_semantics_pat_size o FST) m) + LENGTH m) t i m exp`,
  CHEAT_TAC);;

(* HOL4 to_data_cvScript.sml:325: ML code, not ported *)

(* [cv_pre] *)
let flatLang_pat_size_pre = prove
 (`(!v. flatLang_pat_size_pre v) /\
   (!v. flatLang_pat1_size_pre v)`,
  CHEAT_TAC);;

(* HOL4 to_data_cvScript.sml:334: ML code, not ported *)

let naive_pattern_match_clocked_def,naive_pattern_match_clocked_ind =
  define_guess
  `naive_pattern_match_clocked x1' t xs =
   match (x1',xs) with
     (0,xs) -> json_Bool t T
   | (SUC ck,[]) -> json_Bool t T
   | (SUC ck,CONS (flat_Pany,_) mats) -> naive_pattern_match_clocked ck t
     mats
   | (SUC ck,CONS (flat_Pvar _,_) mats) -> naive_pattern_match_clocked ck t
     mats
   | (SUC ck,CONS (flat_Plit l,v) mats) -> SmartIf t
     (flat_App t (flat_Src ast_Equality) [v; flat_Lit t l])
       (naive_pattern_match_clocked ck t mats) (json_Bool t F)
   | (SUC ck,CONS (flat_Pcon NONE ps,v) mats) ->
     naive_pattern_match_clocked ck t (APPEND (MAPi (\i p. (p,flat_App t
       (flat_El i) [v])) ps) mats)
   | (SUC ck,CONS (flat_Pas p i,v) mats) ->
     naive_pattern_match_clocked ck t (CONS (p,v) mats)
   | (SUC ck,CONS (flat_Pcon (SOME stmp) ps,v) mats) ->
     SmartIf t (flat_App t (flat_TagLenEq (FST stmp) (LENGTH ps)) [v])
       (naive_pattern_match_clocked ck t (APPEND (MAPi (\i p. (p,flat_App t
         (flat_El i) [v])) ps) mats))
       (json_Bool t F)
   | (SUC ck,CONS (flat_Pref p,v) mats) ->
     naive_pattern_match_clocked ck t (CONS (p,flat_App t (flat_El 0)
       [v]) mats)`;;

(* HOL4 to_data_cvScript.sml:357: ML code, not ported *)

(* [cv_pre] *)
let naive_pattern_match_clocked_pre = prove
 (`!v0 t v. naive_pattern_match_clocked_pre v0 t v`,
  CHEAT_TAC);;

let naive_pattern_match_clocked_thm = prove
 (`!ck t xs. SUM (MAP (pattern_semantics_pat_size o FST) xs) + LENGTH xs <= ck
  ==>
   naive_pattern_match_clocked ck t xs = naive_pattern_match t xs`,
  CHEAT_TAC);;

let naive_pattern_matched_clocked_eq = prove
 (`naive_pattern_match t xs = naive_pattern_match_clocked (SUM (MAP
  (pattern_semantics_pat_size o FST) xs) + LENGTH xs) t xs`,
  CHEAT_TAC);;

(* HOL4 to_data_cvScript.sml:389: ML code, not ported *)

let encode_pat_alt_def,encode_pat_alt_ind = define_guess
  `(encode_pat_alt flat_Pany = pattern_semantics_Any) /\
   (encode_pat_alt (flat_Plit l) = pattern_semantics_Lit l) /\
   (encode_pat_alt (flat_Pvar _) = bvi_tailrec_Any) /\
   (encode_pat_alt (flat_Pcon stmp ps) = backend_common_Cons
      (match stmp with NONE -> NONE | SOME (i,NONE) -> SOME (i,NONE)
          | SOME (i,SOME (ty,ctors)) -> SOME (i,SOME ctors))
      (encode_pats_alt ps)) /\
   (encode_pat_alt (flat_Pas p v) = encode_pat_alt p) /\
   (encode_pat_alt (flat_Pref p) = pattern_semantics_Ref (encode_pat_alt p)) /\
   (encode_pats_alt [] = []) /\
   (encode_pats_alt (CONS x xs) = CONS (encode_pat_alt x) (encode_pats_alt
    xs))`;;

let encode_pat_alt_thm = prove
 (`(!p. encode_pat_alt p = encode_pat p) /\
   (!ps. encode_pats_alt ps = MAP encode_pat ps)`,
  CHEAT_TAC);;

(* HOL4 to_data_cvScript.sml:414: ML code, not ported *)

(* HOL4 to_data_cvScript.sml:416: ML code, not ported *)

(* HOL4 to_data_cvScript.sml:418-422: ML code, not ported *)

(* HOL4 to_data_cvScript.sml:424: ML code, not ported *)

(* HOL4 to_data_cvScript.sml:426: ML code, not ported *)

(* HOL4 to_data_cvScript.sml:428: ML code, not ported *)

(* HOL4 to_data_cvScript.sml:430-434: a proof *)

(* HOL4 to_data_cvScript.sml:436: ML code, not ported *)

(* [cv_pre] *)
let flat_pattern_dec_name_to_num_pre = prove
 (`!name. flat_pattern_dec_name_to_num_pre name`,
  CHEAT_TAC);;

(* the clauses in three quotations: fs is ((varN # varN # exp) list) and
   (_)list; ps is ((pat # exp) list), (_)list and (_#_)list; t is tra and
   varN; xs is (exp list), (_#_#_)list and (_)list, which one quotation
   cannot typecheck *)
let compile_exp_alt_def,compile_exp_alt_ind = define_guess_clauses
  [`(compile_exp_alt cfg (flat_Var_local t vid) =
        (dec_name_to_num vid,F,flat_Var_local t vid)) /\
    (compile_exp_alt cfg (flat_Raise t x) =
        let (i,sg,y) = compile_exp_alt cfg x in
        (i,sg,flat_Raise t y)) /\
    (compile_exp_alt cfg (flat_Handle t x ps) =
        let (i,sgx,y) = compile_exp_alt cfg x in
        let (j,sgp,ps2) = compile_match_alt cfg ps in
        let k = MAX i j + 2 in
        let nm = enc_num_to_name k in
        let v = flat_Var_local t nm in
        let r = flat_Raise t v in
        let exp = compile_pats cfg sgp t k v r ps2 in
        (k,(sgx \/ sgp),flat_Handle t y [(flat_Pvar nm,exp)])) /\
    (compile_exp_alt cfg (flat_Con t ts xs) =
        let (i,sg,ys) = compile_exp_alts_alt cfg (REVERSE xs) in
        (i,sg,flat_Con t ts (REVERSE ys))) /\
    (compile_exp_alt cfg (flat_App t op xs) =
        let (i,sg,ys) = compile_exp_alts_alt cfg (REVERSE xs) in
        (i,(sg \/ op_sets_globals op),flat_App t op (REVERSE ys))) /\
    (compile_exp_alt cfg (flat_Mat t x ps) =
        let (i,sgx,y) = compile_exp_alt cfg x in
        let (j,sgp,ps2) = compile_match_alt cfg ps in
        let k = MAX i j + 2 in
        let nm = enc_num_to_name k in
        let v = flat_Var_local t nm in
        let r = flat_Raise t (flat_Con t (SOME (bind_tag,NONE)) []) in
        let exp = compile_pats cfg sgp t k v r ps2 in
        (k,(sgx \/ sgp),flat_Let t (SOME nm) y exp)) /\
    (compile_exp_alt cfg (flat_Let t v x1 x2) =
        let (i,sg1,y1) = compile_exp_alt cfg x1 in
        let (j,sg2,y2) = compile_exp_alt cfg x2 in
        let k = (match v with NONE -> 0 | SOME vid -> dec_name_to_num vid)
            in
        (MAX i (MAX j k),(sg1 \/ sg2),flat_Let t v y1 y2)) /\
    (compile_exp_alt cfg (flat_If t x1 x2 x3) =
        let (i,sg1,y1) = compile_exp_alt cfg x1 in
        let (j,sg2,y2) = compile_exp_alt cfg x2 in
        let (k,sg3,y3) = compile_exp_alt cfg x3 in
        (MAX i (MAX j k),(sg1 \/ sg2 \/ sg3),SmartIf t y1 y2 y3)) /\
    (compile_exp_alt cfg exp = (0,F,exp)) /\
    (compile_exp_alts_alt cfg [] = (0,F,[])) /\
    (compile_letexps_alt cfg [] = []) /\
    (compile_match_alt cfg [] = (0,F,[])) /\
    (compile_match_alt cfg (CONS (p,x) ps) =
        let (i,sgx,y) = compile_exp_alt cfg x in
        let j = max_dec_name (ast_pat_bindings p) in
        let (k,sgp,ps2) = compile_match_alt cfg ps in
        (MAX i (MAX j k),(sgx \/ sgp),(CONS (p,y) ps2)))`;
   `(compile_exp_alt cfg (flat_Fun t vs x) =
        let (i,sg,y) = compile_exp_alt cfg x in
        (i,sg,flat_Fun t vs y)) /\
    (compile_exp_alt cfg (flat_Letrec t fs x) =
        let ys = compile_letexps_alt cfg fs in
        let (i,sgx,y) = compile_exp_alt cfg x in
        let j = MAX_LIST (MAP (\(_,_,(j,_,_)). j) ys) in
        let sgfs = EX (\(_,_,(_,sg,_)). sg) ys in
        let fs2 = MAP (\(a,b,(_,_,exp)). (a,b,exp)) ys in
        (MAX i j,(sgfs \/ sgx),flat_Letrec t fs2 y)) /\
    (compile_letexps_alt cfg (CONS (a,b,c) xs) = CONS (a,b,compile_exp_alt
    cfg c) (compile_letexps_alt cfg xs))`;
   `compile_exp_alts_alt cfg (CONS x xs) =
        let (i,sgx,y) = compile_exp_alt cfg x in
        let (j,sgy,ys) = compile_exp_alts_alt cfg xs in
        (MAX i j,(sgx \/ sgy),CONS y ys)`];;

(* TODO: move *)
let cv_REV_size = prove
 (`!x acc. cv_size (cv_REV x acc) <= cv_size x + cv_size acc`,
  CHEAT_TAC);;

(* TODO: move *)
let cv_REVERSE_size = prove
 (`!x. cv_size (cv_REVERSE x) <= cv_size x`,
  CHEAT_TAC);;

(* HOL4 to_data_cvScript.sml:536-544: a proof *)

(* [cv_pre] *)
let compile_exp_alt_pre = prove
 (`(!cfg v. compile_exp_alt_pre cfg v) /\
   (!cfg v. compile_exp_alts_alt_pre cfg v) /\
   (!cfg v. compile_letexps_alt_pre cfg v) /\
   (!cfg v. compile_match_alt_pre cfg v)`,
  CHEAT_TAC);;

let compile_exp_alt_thm = prove
 (`(!cfg exp. compile_exp_alt cfg exp = bvi_to_data_compile_exp cfg exp) /\
   (!cfg xs. compile_exp_alts_alt cfg xs = bvl_to_bvi_compile_exps cfg xs)
     /\
   (!cfg xs. compile_letexps_alt cfg xs = MAP (\(x,y,z).
     (x,y,bvi_to_data_compile_exp cfg z)) xs) /\
   (!cfg xs. compile_match_alt cfg xs = compile_match cfg xs)`,
  CHEAT_TAC);;

(* HOL4 to_data_cvScript.sml:568: ML code, not ported *)

(* HOL4 to_data_cvScript.sml:570: ML code, not ported *)

(* flat_elim *)

(* HOL4 to_data_cvScript.sml:574: ML code, not ported *)

(* [cv_pre] *)
let flat_elim_has_Eval_pre = prove
 (`(!v. flat_elim_has_Eval_pre v) /\
   (!v. flat_elim_has_Eval_list_pre v) /\
   (!v. flat_elim_has_Eval_pats_pre v) /\
   (!v. flat_elim_has_Eval_funs_pre v)`,
  CHEAT_TAC);;

let cv_size_map_snd = prove
 (`!z. cv_size (cv_map_snd z) <= cv_size z`,
  CHEAT_TAC);;

(* HOL4 to_data_cvScript.sml:594-612: a proof *)

(* [cv_pre] *)
let flat_elim_find_loc_pre = prove
 (`(!v. flat_elim_find_loc_pre v) /\
   (!v. flat_elim_find_locL_pre v)`,
  CHEAT_TAC);;

(* HOL4 to_data_cvScript.sml:623-641: a proof *)

(* [cv_pre] *)
let flat_elim_find_lookups_pre = prove
 (`(!v. flat_elim_find_lookups_pre v) /\
   (!v. flat_elim_find_lookupsL_pre v)`,
  CHEAT_TAC);;

(* HOL4 to_data_cvScript.sml:651: ML code, not ported *)

(* the clauses in two quotations: es is (exp list) and (_)list; pes is ((pat
   # exp) list) and (_#_)list; t is tra and varN, which one quotation cannot
   typecheck *)
(* the termination relation that HOL4 gives is
     MEASURE (\e. sum_CASE e flat_exp_size (list_size flat_exp_size))
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 to_data_cvScript.sml:668-671: the tactic that proves the termination *)
let is_pure_alt_def,is_pure_alt_ind = define_guess_clauses
  [`(is_pure_alt (flat_Handle t e pes) = is_pure_alt e) /\
    (is_pure_alt (flat_Lit t l) = T) /\
    (is_pure_alt (flat_Con t id_option es) = is_pure_alts es) /\
    (is_pure_alt (flat_Var_local t str) = T) /\
    (is_pure_alt (flat_App t (flat_GlobalVarInit g) es) = is_pure_alts es) /\
    (is_pure_alt (flat_If t e1 e2 e3) = (is_pure_alt e1 /\ is_pure_alt e2
    /\ is_pure_alt e3)) /\
    (is_pure_alt (flat_Mat t e1 pes) =
          (is_pure_alt e1 /\ is_pure_alts (MAP SND pes) /\ EX total_pat
              (MAP FST pes))) /\
    (is_pure_alt (flat_Let t opt e1 e2) = (is_pure_alt e1 /\ is_pure_alt e2))
      /\
    (is_pure_alt _ = F) /\
    (is_pure_alts [] = T) /\
    (is_pure_alts (CONS x xs) = (is_pure_alt x /\ is_pure_alts xs))`;
   `(is_pure_alt (flat_Fun t name body) = T) /\
    (is_pure_alt (flat_Letrec t funs e) = is_pure_alt e)`];;

(* HOL4 to_data_cvScript.sml:673-679: a proof *)

(* [cv_pre] *)
let is_pure_alt_pre = prove
 (`(!v. is_pure_alt_pre v) /\
   (!v. is_pure_alts_pre v)`,
  CHEAT_TAC);;

let is_pure_alt_thm = prove
 (`(!v. is_pure_alt v = flat_elim_is_pure v) /\
   (!v. is_pure_alts v = ALL flat_elim_is_pure v)`,
  CHEAT_TAC);;

(* HOL4 to_data_cvScript.sml:698: ML code, not ported *)

(* the clauses in three quotations: es is (exp list) and (_)list; l is lit
   and (exp list); t is tra and varN, which one quotation cannot typecheck *)
let is_hidden_alt_def,is_hidden_alt_ind = define_guess_clauses
  [`(is_hidden_alt (flat_Raise t e) = is_hidden_alt e) /\
    (is_hidden_alt (flat_Handle t e pes) = F) /\
    (is_hidden_alt (flat_Lit t l) = T) /\
    (is_hidden_alt (flat_Con t id_option es) = is_hidden_alts es) /\
    (is_hidden_alt (flat_Var_local t str) = T) /\
    (is_hidden_alt (flat_App t (flat_GlobalVarInit g) [e]) = is_hidden_alt e)
      /\
    (is_hidden_alt (flat_App t (flat_GlobalVarLookup g) [e]) = F) /\
    (is_hidden_alt (flat_If t e1 e2 e3) = (is_hidden_alt e1 /\ is_hidden_alt
    e2 /\ is_hidden_alt e3)) /\
    (is_hidden_alt (flat_Mat t e1 [p,e2]) = (is_hidden_alt e1
    /\ is_hidden_alt e2)) /\
    (is_hidden_alt (flat_Let t opt e1 e2) = (is_hidden_alt e1
    /\ is_hidden_alt e2)) /\
    (is_hidden_alt _ = F) /\
    (is_hidden_alts [] = T) /\
    (is_hidden_alts (CONS x xs) = (is_hidden_alt x /\ is_hidden_alts xs))`;
   `(is_hidden_alt (flat_Fun t name body) = T) /\
    (is_hidden_alt (flat_Letrec t funs e) = is_hidden_alt e)`;
   `is_hidden_alt (flat_App t (flat_Src ast_Opapp) l) = F`];;

(* HOL4 to_data_cvScript.sml:719: ML code, not ported *)

(* [cv_pre] *)
let is_hidden_alt_pre = prove
 (`(!v. is_hidden_alt_pre v) /\
   (!v. is_hidden_alts_pre v)`,
  CHEAT_TAC);;

let is_hidden_alt_thm = prove
 (`(!v. is_hidden_alt v = is_hidden v) /\
   (!v. is_hidden_alts v = ALL is_hidden v)`,
  CHEAT_TAC);;

(* HOL4 to_data_cvScript.sml:738: ML code, not ported *)

let spt_fold_union_def,spt_fold_union_ind = define_guess
  `(spt_fold_union acc LN = acc) /\
   (spt_fold_union acc (LS a) = sptree_union a acc) /\
   (spt_fold_union acc (BN t1 t2) = spt_fold_union (spt_fold_union acc t1)
    t2) /\
   (spt_fold_union acc (BS t1 a t2) = spt_fold_union (sptree_union a
    (spt_fold_union acc t1)) t2)`;;

let spt_fold_union_thm = prove
 (`!acc t. spt_fold_union acc t = spt_fold sptree_union acc t`,
  CHEAT_TAC);;

(* HOL4 to_data_cvScript.sml:753: ML code, not ported *)

(* HOL4 to_data_cvScript.sml:755: ML code, not ported *)

(* [cv_pre] *)
let spt_closure_closure_spt_pre = prove
 (`!reachable tree. spt_closure_closure_spt_pre reachable tree`,
  CHEAT_TAC);;

(* HOL4 to_data_cvScript.sml:765: ML code, not ported *)

(* HOL4 to_data_cvScript.sml:767: ML code, not ported *)

(* flat_to_clos *)

(* HOL4 to_data_cvScript.sml:771: ML code, not ported *)

let list_size_thm = prove
 (`list_size f xs = LENGTH xs + SUM (MAP f xs)`,
  CHEAT_TAC);;

(* the clauses in two quotations: funs is ((varN # varN # exp) list) and
   (_)list; t is tra and varN; xs is (_)list and (_#_#_)list, which one
   quotation cannot typecheck *)
(* the termination relation that HOL4 gives is
     MEASURE (\x.
                     match x with
                       sum_INL (m,e) -> list_size flat_exp_size e
                     | sum_INR (sum_INL (m,e)) -> flat_exp_size e
                     | sum_INR (sum_INR (m,e)) -> list_size (flat_exp_size o
                       SND
                       o SND) e)
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 to_data_cvScript.sml:812-823: the tactic that proves the termination *)
let flat_to_clos_compile_alt_def,flat_to_clos_compile_alt_ind =
  define_guess_clauses
  [`(flat_to_clos_compile_alts m [] = []) /\
    (flat_to_clos_compile_alts m (CONS x xs) = CONS
    (flat_to_clos_compile_alt m x) (flat_to_clos_compile_alts m xs)) /\
    (flat_to_clos_compile_alt m (flat_Raise t e) = (clos_Raise t
    (flat_to_clos_compile_alt m (e)))) /\
    (flat_to_clos_compile_alt m (flat_Lit t l) = (compile_lit t l)) /\
    (flat_to_clos_compile_alt m (flat_Var_local t v) = (clos_Var t
    (indexedLists_findi (SOME v) m))) /\
    (flat_to_clos_compile_alt m (flat_Con t n es) =
         let tag = (match n with SOME (t,_) -> t | _ -> 0) in
           (SmartCons t tag (flat_to_clos_compile_alts m (REVERSE es)))) /\
    (flat_to_clos_compile_alt m (flat_App t op es) =
         match dest_nop op es with SOME e -> flat_to_clos_compile_alt m e
         | NONE -> (flat_to_clos_compile_op t op
             (flat_to_clos_compile_alts m (REVERSE es)))) /\
    (flat_to_clos_compile_alt m (flat_If t x1 x2 x3) =
         (flat_If t (flat_to_clos_compile_alt m (x1))
               (flat_to_clos_compile_alt m (x2))
               (flat_to_clos_compile_alt m (x3)))) /\
    (flat_to_clos_compile_alt m (flat_Let t vo e1 e2) =
         (ast_Let t [flat_to_clos_compile_alt m (e1)]
             (flat_to_clos_compile_alt (CONS vo m) (e2)))) /\
    (flat_to_clos_compile_alt m (flat_Mat t e pes) = (clos_Op t (clos_IntOp
    (clos_Const (&0))) [])) /\
    (flat_to_clos_compile_alt m (flat_Handle t e pes) =
         match dest_pat pes with SOME (v,h) -> (flat_Handle t
             (flat_to_clos_compile_alt m (e)) (flat_to_clos_compile_alt (CONS
             (SOME v) m) (h)))
         | _ -> flat_to_clos_compile_alt m (e)) /\
    (flat_to_clos_compile_lets_alt m [] = [])`;
   `(flat_to_clos_compile_alt m (flat_Fun t v e) =
         (clos_Fn t NONE NONE 1 (flat_to_clos_compile_alt (CONS (SOME
             v) m) (e)))) /\
    (flat_to_clos_compile_alt m (flat_Letrec t funs e) =
         let new_m = APPEND (MAP (\n. SOME (FST n)) funs) m in
           (clos_Letrec (MAP (\n. join_strings t (FST n)) funs) NONE NONE
              (flat_to_clos_compile_lets_alt new_m funs)
              (flat_to_clos_compile_alt new_m (e)))) /\
    (flat_to_clos_compile_lets_alt m (CONS (f,v,x) xs) = CONS
    (1,flat_to_clos_compile_alt (CONS (SOME v) m) x)
    (flat_to_clos_compile_lets_alt m xs))`];;

(* HOL4 to_data_cvScript.sml:825-826: ML code, not ported *)

(* HOL4 to_data_cvScript.sml:828-847: a proof *)

(* [cv_pre] *)
let flat_to_clos_compile_alts_pre = prove
 (`(!m v. flat_to_clos_compile_alts_pre m v) /\
   (!m v. flat_to_clos_compile_alt_pre m v) /\
   (!m v. flat_to_clos_compile_lets_alt_pre m v)`,
  CHEAT_TAC);;

let flat_to_clos_compile_alt_thm = prove
 (`(!m xs. flat_to_clos_compile_alts m xs = source_to_flat_compile m xs) /\
   (!m x. flat_to_clos_compile_alt m x = HD (source_to_flat_compile m [x]))
     /\
   (!m xs. flat_to_clos_compile_lets_alt m xs =
          (MAP (\(f,v,x). (1,HD (source_to_flat_compile (CONS (SOME v) m)
            [x]))) xs))`,
  CHEAT_TAC);;

(* HOL4 to_data_cvScript.sml:871: ML code, not ported *)

(* HOL4 to_data_cvScript.sml:873-879: a proof *)

(* [cv_pre] *)
let closLang_has_install_pre = prove
 (`(!v. closLang_has_install_pre v) /\
   (!v. closLang_has_install_list_pre v)`,
  CHEAT_TAC);;

(* HOL4 to_data_cvScript.sml:889: ML code, not ported *)

(* to_clos *)

(* HOL4 to_data_cvScript.sml:893: ML code, not ported *)

(* clos_mti *)

(* HOL4 to_data_cvScript.sml:897: ML code, not ported *)

(* HOL4 to_data_cvScript.sml:899: ML code, not ported *)

(* the clauses in three quotations: es is (exp list) and (_)list; fs is
   (_#_)list and (_)list; funs is ((num # exp) list) and (_)list; t is tra,
   mlstring and (mlstring list), which one quotation cannot typecheck *)
(* the termination relation that HOL4 gives is
     MEASURE (\x. match x with sum_INL (n,_,_) -> n
                                   | sum_INR (sum_INL (n,_,_)) -> n
                                   | sum_INR (sum_INR (n,_,_)) -> n)
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
let intro_multi_alt_def,intro_multi_alt_ind = define_guess_clauses
  [`(intro_multi_alt 0 max_app exp = (clos_Var (backend_common_SourceLoc 0 0
    0 0) 0)) /\
    (intro_multi_alt (SUC ck) max_app (clos_Var t n) = (clos_Var t n)) /\
    (intro_multi_alt (SUC ck) max_app (clos_If t e1 e2 e3) =
       (clos_If t ((intro_multi_alt ck max_app (e1)))
             ((intro_multi_alt ck max_app (e2)))
             ((intro_multi_alt ck max_app (e3))))) /\
    (intro_multi_alt (SUC ck) max_app (clos_Let t es e) =
        (clos_Let t (intro_multis_alt ck max_app es) ((intro_multi_alt
            ck max_app (e))))) /\
    (intro_multi_alt (SUC ck) max_app (clos_Raise t e) =
        (clos_Raise t ((intro_multi_alt ck max_app (e))))) /\
    (intro_multi_alt (SUC ck) max_app (clos_Handle t e1 e2) =
        (clos_Handle t ((intro_multi_alt ck max_app (e1)))
            ((intro_multi_alt ck max_app (e2))))) /\
    (intro_multi_alt (SUC ck) max_app (clos_Tick t e) =
        (clos_Tick t ((intro_multi_alt ck max_app (e))))) /\
    (intro_multi_alt (SUC ck) max_app (clos_Call t ticks n es) =
        (clos_Call t ticks n (intro_multis_alt ck max_app es))) /\
    (intro_multi_alt (SUC ck) max_app (clos_App t NONE e es) =
        let (es',e') = collect_apps max_app es e in
          (clos_App t NONE ((intro_multi_alt ck max_app (e')))
              (intro_multis_alt ck max_app es'))) /\
    (intro_multi_alt (SUC ck) max_app (clos_App t (SOME l) e es) =
        (clos_App t (SOME l) ((intro_multi_alt ck max_app (e)))
            (intro_multis_alt ck max_app es))) /\
    (intro_multi_alt (SUC ck) max_app (clos_Op t op es) =
        (clos_Op t op (intro_multis_alt ck max_app es))) /\
    (intro_multis_alt 0 max_app _ = []) /\
    (intro_multis_alt (SUC ck) max_app [] = []) /\
    (intro_multis_alt (SUC ck) max_app (CONS e1 es) = CONS (intro_multi_alt
    ck max_app e1) (intro_multis_alt ck max_app es)) /\
    (intro_multi_collect_alt 0 max_app _ = []) /\
    (intro_multi_collect_alt (SUC ck) max_app [] = [])`;
   `(intro_multi_alt (SUC ck) max_app (clos_Fn t NONE NONE num_args e) =
        let (num_args',e') = collect_args max_app num_args e in
          (clos_Fn t NONE NONE num_args' ((intro_multi_alt ck max_app
              (e'))))) /\
    (intro_multi_alt (SUC ck) max_app (clos_Fn t loc fvs num_args e) =
          (clos_Fn t loc fvs num_args ((intro_multi_alt ck max_app
              (e))))) /\
    (intro_multi_collect_alt (SUC ck) max_app (CONS (num_args,e) fs) =
       let (num_args',e') = collect_args max_app num_args e in
         (CONS (num_args',intro_multi_alt ck max_app e')
             (intro_multi_collect_alt ck max_app fs)))`;
   `(intro_multi_alt (SUC ck) max_app (clos_Letrec t NONE NONE funs e) =
        (clos_Letrec t NONE NONE (intro_multi_collect_alt ck max_app funs)
                ((intro_multi_alt ck max_app (e))))) /\
    (intro_multi_alt (SUC ck) max_app (clos_Letrec t (SOME loc) fvs funs e) =
         (clos_Letrec t (SOME loc) fvs funs ((intro_multi_alt ck
             max_app (e))))) /\
    (intro_multi_alt (SUC ck) max_app (clos_Letrec t NONE (SOME fvs) funs e) =
         (clos_Letrec t NONE (SOME fvs) funs ((intro_multi_alt ck
             max_app (e)))))`];;

(* the clauses in 6 quotations: a0 is tra, mlstring and (mlstring list); a1
   is exp, num, (num option) and op; a2 is exp, num, (num list option), (exp
   list) and (_)list; a3 is (exp list), (_)list, num, ((num # exp) list) and
   (_#_)list; es is (exp list) and (_)list; x is tra and exp, which one
   quotation cannot typecheck *)
(* the termination relation that HOL4 gives is
     MEASURE (\x. match x with
                                   sum_INL e -> flat_exp_size e
                                   | sum_INR es -> list_size flat_exp_size es)
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 to_data_cvScript.sml:967-972: the tactic that proves the termination *)
let exp_size_alt_def,exp_size_alt_ind = define_guess_clauses
  [`(exp_size_alt (clos_Var x y) = (1:num)) /\
    (exp_size_alt (clos_If a b c d) = ((1 + exp_size_alt b + exp_size_alt c
    + exp_size_alt d):num)) /\
    (exp_size_alt (clos_Let a es e) = ((1 + exp_size_alt e + exp_sizes_alt
    es):num)) /\
    (exp_size_alt (clos_Handle a0 a1 a2) = ((1 + exp_size_alt a1 +
    exp_size_alt a2):num)) /\
    (exp_size_alt (clos_Raise a0 a1) = ((1 + exp_size_alt a1):num)) /\
    (exp_size_alt (clos_Tick a0 a1) = ((1 + exp_size_alt a1):num)) /\
    (exp_sizes_alt [] = 0)`;
   `(exp_size_alt (clos_Call a0 a1 a2 a3) = ((1 + exp_sizes_alt a3):num)) /\
    (exp_sizes_alt (CONS x xs) = 1 + exp_size_alt x + exp_sizes_alt xs)`;
   `exp_size_alt (clos_App a0 a1 a2 a3) = ((1 + exp_size_alt a2 +
    exp_sizes_alt a3):num)`;
   `exp_size_alt (clos_Fn a0 a1 a2 a3 a4) = ((1 + exp_size_alt a4):num)`;
   `exp_size_alt (clos_Letrec a0 a1 a2 a3 a4) = ((1 + exp_sizes_alt (MAP
    SND a3) + exp_size_alt a4):num)`;
   `exp_size_alt (clos_Op a0 a1 a2) = ((1 + exp_sizes_alt a2):num)`];;

(* HOL4 to_data_cvScript.sml:974-982: a proof *)

(* [cv_pre] *)
let exp_size_alt_pre = prove
 (`(!v. exp_size_alt_pre v) /\
   (!v. exp_sizes_alt_pre v)`,
  CHEAT_TAC);;

let exp_sizes_alt_cons = prove
 (`exp_sizes_alt (CONS x xs) = 1 + exp_size_alt x + exp_sizes_alt xs`,
  CHEAT_TAC);;

let exp_sizes_alt_append = prove
 (`!xs ys. exp_sizes_alt (APPEND xs ys) = exp_sizes_alt xs + exp_sizes_alt ys`,
  CHEAT_TAC);;

(* HOL4 to_data_cvScript.sml:1004: ML code, not ported *)

(* [cv_pre] *)
let intro_multi_alt_pre = prove
 (`(!v0 max_app v. intro_multi_alt_pre v0 max_app v) /\
   (!v0 max_app v. intro_multis_alt_pre v0 max_app v) /\
   (!v0 max_app v. intro_multi_collect_alt_pre v0 max_app v)`,
  CHEAT_TAC);;

let exp_size_alt_pos = prove
 (`!e. exp_size_alt e = 0 <=> F`,
  CHEAT_TAC);;
add_simp exp_size_alt_pos;;

let exp_sizes_alt_pos = prove
 (`!es. exp_sizes_alt es = 0 <=> es = []`,
  CHEAT_TAC);;
add_simp exp_sizes_alt_pos;;

let collect_apps_size_alt = prove
 (`!max_app args e args' e'.
     collect_apps max_app args e = (args',e') ==>
     exp_size_alt e' <= exp_size_alt e`,
  CHEAT_TAC);;

let collect_apps_sizes_alt = prove
 (`!max_app args e args' e'.
     collect_apps max_app args e = (args',e') ==>
     exp_size_alt e' + exp_sizes_alt args' <= exp_size_alt e +
       exp_sizes_alt args`,
  CHEAT_TAC);;

let collect_args_size_alt = prove
 (`!max_app args e args' e'.
     collect_args max_app args e = (args',e') ==>
     exp_size_alt e' <= exp_size_alt e`,
  CHEAT_TAC);;

let intro_multi_cons = prove
 (`!e es. intro_multi max_app (CONS e es) = CONS (HD (intro_multi max_app
  [e])) (intro_multi max_app es)`,
  CHEAT_TAC);;

let intro_multi_thm = prove
 (`(!ck max_app e. exp_size_alt e <= ck ==> intro_multi_alt ck max_app e = HD
  (intro_multi max_app [e])) /\
   (!ck max_app es. exp_sizes_alt es <= ck ==> intro_multis_alt ck max_app
     es = intro_multi max_app es) /\
   (!ck max_app es. exp_sizes_alt (MAP SND es) <= ck ==>
     intro_multi_collect_alt ck max_app es =
                              MAP (\(num_args,e).
                              let (num_args',e') = collect_args max_app
                                num_args e in
                              (num_args',HD (intro_multi max_app [e'])))
                              es)`,
  CHEAT_TAC);;

let intro_multi_alt_eq = prove
 (`intro_multi max_app es = intro_multis_alt (exp_sizes_alt es) max_app es`,
  CHEAT_TAC);;

(* HOL4 to_data_cvScript.sml:1090: ML code, not ported *)

(* HOL4 to_data_cvScript.sml:1092: ML code, not ported *)

(* clos_number *)

(* HOL4 to_data_cvScript.sml:1096-1102: a proof *)

(* [cv_pre] *)
let clos_number_renumber_code_locs_list_pre = prove
 (`(!n v. clos_number_renumber_code_locs_list_pre n v) /\
   (!n v. clos_number_renumber_code_locs_pre n v)`,
  CHEAT_TAC);;

(* clos_known *)

(* the clauses in three quotations: fns is ((num # exp) list) and (_#_)list;
   t is tra, mlstring and (mlstring list); xs is (exp list) and (_)list,
   which one quotation cannot typecheck *)
(* the termination relation that HOL4 gives is
     MEASURE (\x. sum_CASE x (flat_exp_size o SND) (list_size flat_exp_size o
       SND))
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 to_data_cvScript.sml:1155-1158: the tactic that proves the
   termination *)
let get_size_sc_aux_alt_def,get_size_sc_aux_alt_ind = define_guess_clauses
  [`(get_size_sc_aux_alt n (clos_Var t v) = n - 1) /\
    (get_size_sc_aux_alt n (clos_If t x1 x2 x3) =
         let n = n - 1 in if n = 0 then 0 else let n =
             get_size_sc_aux_alt n x1 in if n = 0 then 0 else let n =
             get_size_sc_aux_alt n x2 in if n = 0 then 0 else
             get_size_sc_aux_alt n x3) /\
    (get_size_sc_aux_alt n (clos_Let t xs x2) =
         let n = n - 1 in if n = 0 then 0 else let n =
             get_size_sc_aux_alts n xs in if n = 0 then 0 else
             get_size_sc_aux_alt n x2) /\
    (get_size_sc_aux_alt n (clos_Raise t x1) =
         let n = n - 1 in if n = 0 then 0 else get_size_sc_aux_alt n x1) /\
    (get_size_sc_aux_alt n (clos_Handle t x1 x2) =
         let n = n - 1 in if n = 0 then 0 else let n =
             get_size_sc_aux_alt n x1 in if n = 0 then 0 else
             get_size_sc_aux_alt n x2) /\
    (get_size_sc_aux_alt n (clos_Op t op xs) =
         let n = n - 1 in if n = 0 then 0 else get_size_sc_aux_alts n
             xs) /\
    (get_size_sc_aux_alt n (clos_Tick t x) = get_size_sc_aux_alt n x) /\
    (get_size_sc_aux_alt n (clos_Call t ticks dest xs) =
         let n = n - 1 in if n = 0 then 0 else get_size_sc_aux_alts n
             xs) /\
    (get_size_sc_aux_alt n (clos_App t loc_opt x1 xs) =
         let n = n - 1 in if n = 0 then 0 else let n =
             get_size_sc_aux_alt n x1 in if n = 0 then 0 else
             get_size_sc_aux_alts n xs) /\
    (get_size_sc_aux_alts n [] = n) /\
    (get_size_sc_aux_alts n (CONS x xs) =
         if n = 0 then n else let n = get_size_sc_aux_alt n x in if n
             = 0 then n else get_size_sc_aux_alts n xs)`;
   `get_size_sc_aux_alt n (clos_Fn t loc_opt ws_opt num_args x1) =
         let n = n - 1 in if n = 0 then 0 else get_size_sc_aux_alt n x1`;
   `get_size_sc_aux_alt n (clos_Letrec t loc_opt ws_opt fns x1) =
         let n = n - 1 in if n = 0 then 0 else let n =
             get_size_sc_aux_alts n (MAP SND fns) in if n = 0 then 0 else
             get_size_sc_aux_alt n x1`];;

(* HOL4 to_data_cvScript.sml:1160-1166: a proof *)

(* [cv_pre] *)
let get_size_sc_aux_alt_pre = prove
 (`(!n v. get_size_sc_aux_alt_pre n v) /\
   (!n v. get_size_sc_aux_alts_pre n v)`,
  CHEAT_TAC);;

let get_size_aux_sc_alt_thm = prove
 (`(!n v. get_size_sc_aux_alt n v = get_size_sc_aux n [v]) /\
   (!n vs. get_size_sc_aux_alts n vs = get_size_sc_aux n vs)`,
  CHEAT_TAC);;

(* HOL4 to_data_cvScript.sml:1187: ML code, not ported *)

(* HOL4 to_data_cvScript.sml:1189: ML code, not ported *)

(* HOL4 to_data_cvScript.sml:1191: ML code, not ported *)

(* the clauses in three quotations: fns is ((num # exp) list) and (_)list; t
   is tra, mlstring and (mlstring list); xs is (exp list), (_)list and
   (_#_)list; xs2 is (exp list) and (_)list, which one quotation cannot
   typecheck *)
(* the termination relation that HOL4 gives is
     MEASURE (\a. match a with sum_INL x -> clos_exp_size x
                                   | sum_INR (sum_INL xs) -> list_size
                                     flat_exp_size xs
                                   | sum_INR (sum_INR (_,xs)) -> list_size
                                     flat_exp_size (MAP SND xs))
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 to_data_cvScript.sml:1246-1252: the tactic that proves the
   termination *)
let free_alt_def,free_alt_ind = define_guess_clauses
  [`(free_alt (clos_Var t v) = ((clos_Var t v),db_vars_Var v)) /\
    (free_alt (clos_If t x1 x2 x3) =
         let (c1,l1) = free_alt (x1) in
         let (c2,l2) = free_alt (x2) in
         let (c3,l3) = free_alt (x3) in
           ((clos_If t (c1) (c2) (c3)),mk_Union l1 (mk_Union l2 l3))) /\
    (free_alt (clos_Let t xs x2) =
         let (c1,l1) = free_alts xs in
         let (c2,l2) = free_alt (x2) in
           ((clos_Let t c1 (c2)),mk_Union l1 (db_vars_Shift (LENGTH xs)
               l2))) /\
    (free_alt (clos_Raise t x1) =
         let (c1,l1) = free_alt (x1) in
           ((clos_Raise t (c1)),l1)) /\
    (free_alt (clos_Tick t x1) =
         let (c1,l1) = free_alt (x1) in
           ((clos_Tick t (c1)),l1)) /\
    (free_alt (clos_Op t op xs) =
         let (c1,l1) = free_alts xs in
           ((clos_Op t op c1),l1)) /\
    (free_alt (clos_App t loc_opt x1 xs2) =
         let (c1,l1) = free_alt (x1) in
         let (c2,l2) = free_alts xs2 in
           ((clos_App t loc_opt (c1) c2),mk_Union l1 l2)) /\
    (free_alt (clos_Handle t x1 x2) =
         let (c1,l1) = free_alt (x1) in
         let (c2,l2) = free_alt (x2) in
           ((clos_Handle t (c1) (c2)),mk_Union l1 (db_vars_Shift 1 l2))) /\
    (free_alt (clos_Call t ticks dest xs) =
         let (c1,l1) = free_alts xs in
           ((clos_Call t ticks dest c1),l1)) /\
    (free_alts [] = ([],typeSystem_Empty)) /\
    (free_alts (CONS (x:clos_exp) xs) =
         let (c1,l1) = free_alt x in
         let (c2,l2) = free_alts xs in
           (CONS c1 c2,mk_Union l1 l2)) /\
    (free_let_alts m [] = [])`;
   `(free_alt (clos_Fn t loc _ num_args x1) =
         let (c1,l1) = free_alt (x1) in
         let l2 = db_vars_Shift num_args l1 in
           ((clos_Fn t loc (SOME (vars_to_list l2)) num_args (c1)),l2)) /\
    (free_let_alts m (CONS (n,x) xs) =
       let (c,l) = free_alt (x) in CONS ((n,c),db_vars_Shift (n + m)
           l) (free_let_alts m xs))`;
   `free_alt (clos_Letrec t loc _ fns x1) =
         let m = LENGTH fns in
         let res = free_let_alts m fns in
         let c1 = MAP FST res in
         let l1 = list_mk_Union (MAP SND res) in
         let (c2,l2) = free_alt (x1) in
           ((clos_Letrec t loc (SOME (vars_to_list l1)) c1 (c2)),
            mk_Union l1 (db_vars_Shift (LENGTH fns) l2))`];;

(* HOL4 to_data_cvScript.sml:1254: ML code, not ported *)

(* [cv_pre] *)
let free_alt_pre = prove
 (`(!v. free_alt_pre v) /\
   (!v. free_alts_pre v) /\
   (!m v. free_let_alts_pre m v)`,
  CHEAT_TAC);;

(* [local] *)
let free_LENGTH_LEMMA = prove
 (`!xs ys s1. clos_known_free xs = (ys,s1) ==> LENGTH xs = LENGTH ys`,
  CHEAT_TAC);;

let free_alt_thm = prove
 (`(!v. free_alt v = (\(x,y). (HD x,y)) (clos_known_free [v])) /\
   (!v. free_alts v = clos_known_free v) /\
   (!m v. free_let_alts m v =
          MAP (\(n,x). let (c,l) = clos_known_free [x] in
                         ((n,HD c),db_vars_Shift (n + m) l)) v)`,
  CHEAT_TAC);;

(* HOL4 to_data_cvScript.sml:1288: ML code, not ported *)

(* HOL4 to_data_cvScript.sml:1290: ML code, not ported *)

(* the clauses in three quotations: t is tra, mlstring and (mlstring list);
   xs is (exp list) and (_)list, which one quotation cannot typecheck *)
let contains_closures_alt_def,contains_closures_alt_ind = define_guess_clauses
  [`(contains_closures_alt (clos_Var t v) = F) /\
    (contains_closures_alt (clos_If t x1 x2 x3) =
         if contains_closures_alt (x1) then T else if
             contains_closures_alt (x2) then T else contains_closures_alt
             (x3)) /\
    (contains_closures_alt (clos_Let t xs x2) =
         if contains_closures_alts xs then T else contains_closures_alt
             (x2)) /\
    (contains_closures_alt (clos_Raise t x1) = contains_closures_alt (x1)) /\
    (contains_closures_alt (clos_Handle t x1 x2) =
         if contains_closures_alt (x1) then T else
             contains_closures_alt (x2)) /\
    (contains_closures_alt (clos_Op t op xs) = contains_closures_alts xs) /\
    (contains_closures_alt (clos_Tick t x) = contains_closures_alt (x)) /\
    (contains_closures_alt (clos_Call t ticks dest xs) =
    contains_closures_alts xs) /\
    (contains_closures_alt (clos_App t loc_opt x1 xs) =
         if contains_closures_alt (x1) then T else
             contains_closures_alts xs) /\
    (contains_closures_alts [] = F) /\
    (contains_closures_alts (CONS x xs) =
        if contains_closures_alt x then T else contains_closures_alts
            xs)`;
   `contains_closures_alt (clos_Fn t loc_opt ws_opt num_args x1) = T`;
   `contains_closures_alt (clos_Letrec t loc_opt ws_opt fns x1) = T`];;

(* HOL4 to_data_cvScript.sml:1319: ML code, not ported *)

(* [cv_pre] *)
let contains_closures_alt_pre = prove
 (`(!v. contains_closures_alt_pre v) /\
   (!v. contains_closures_alts_pre v)`,
  CHEAT_TAC);;

let contains_closures_cons = prove
 (`!v vs. contains_closures (CONS v vs) = (contains_closures [v] \/
  contains_closures vs)`,
  CHEAT_TAC);;

let contains_closures_alt_thm = prove
 (`(!v. contains_closures_alt v = contains_closures [v]) /\
   (!v. contains_closures_alts v = contains_closures v)`,
  CHEAT_TAC);;

(* HOL4 to_data_cvScript.sml:1343: ML code, not ported *)

let merge_alt_def,merge_alt_ind = define_guess_clauses
  [`(merge_alt clos_known_Impossible y = y) /\
    (merge_alt x clos_known_Impossible = x) /\
    (merge_alt (clos_known_ClosNoInline m1 n1) (clos_known_ClosNoInline m2 n2)
      =
         if m1 = m2 /\ n1 = n2 then clos_known_ClosNoInline m1 n1 else
             clos_known_Other) /\
    (merge_alt (clos_known_Clos m1 n1 e1 s1) (clos_known_Clos m2 n2 e2 s2) =
         if m1 = m2 /\ n1 = n2 /\ e1 = e2 /\ s1 = s2 then
             (clos_known_Clos m1 n1 e1 s1:val_approx) else clos_known_Other) /\
    (merge_alt (clos_known_Int i) (clos_known_Int j) = if i = j then
    (clos_known_Int i:val_approx) else clos_known_Other) /\
    (merge_alt _ _ = clos_known_Other) /\
    (merge_alts _ _ = [])`;
   `merge_alt (clos_known_Tuple tg1 xs) (clos_known_Tuple tg2 ys) =
         if LENGTH xs = LENGTH ys /\ tg1 = tg2 then clos_known_Tuple tg1
             (merge_alts xs ys)
         else clos_known_Other`;
   `merge_alts (CONS x xs) (CONS y ys) = CONS (merge_alt x y) (merge_alts
    xs ys)`];;

(* HOL4 to_data_cvScript.sml:1364: ML code, not ported *)

(* [cv_pre] *)
let merge_alt_pre = prove
 (`(!v0 v. merge_alt_pre v0 v) /\
   (!v0 v. merge_alts_pre v0 v)`,
  CHEAT_TAC);;

let merge_alt_thm = prove
 (`(!v0 v. merge_alt v0 v = clos_known_merge v0 v) /\
   (!v0 v. merge_alts v0 v = MAP2 clos_known_merge v0 v)`,
  CHEAT_TAC);;

(* HOL4 to_data_cvScript.sml:1382: ML code, not ported *)

(* HOL4 to_data_cvScript.sml:1384: ML code, not ported *)

(* [cv_pre] *)
let clos_known_known_op_pre = prove
 (`!v as g. clos_known_known_op_pre v as g`,
  CHEAT_TAC);;

(* HOL4 to_data_cvScript.sml:1394: ML code, not ported *)

(* HOL4 to_data_cvScript.sml:1396: ML code, not ported *)

(* HOL4 to_data_cvScript.sml:1398: ML code, not ported *)

(* HOL4 to_data_cvScript.sml:1400: ML code, not ported *)

(* HOL4 to_data_cvScript.sml:1402: ML code, not ported *)

let pure_alt_def,pure_alt_ind = define_guess
  `(pure_alt (clos_Var _ _) <=> T) /\
   (pure_alt (clos_If _ e1 e2 e3) <=> pure_alt e1 /\ pure_alt e2
    /\ pure_alt e3) /\
   (pure_alt (clos_Let _ es e2) <=> pure_alts es /\ pure_alt e2) /\
   (pure_alt (clos_Raise _ _) <=> F) /\
   (pure_alt (clos_Handle _ e1 e2) <=> pure_alt e1) /\
   (pure_alt (clos_Tick _ _) <=> F) /\
   (pure_alt (clos_Call _ _ _ _) <=> F) /\
   (pure_alt (clos_App _ _ _ _) <=> F) /\
   (pure_alt (clos_Fn _ _ _ _ _) <=> T) /\
   (pure_alt (clos_Letrec _ _ _ _ x) <=> pure_alt x) /\
   (pure_alt (clos_Op _ opn es) <=> pure_alts es /\ clos_pure_op opn) /\
   (pure_alts [] = T) /\
   (pure_alts (CONS x xs) <=> pure_alt x /\ pure_alts xs)`;;

(* HOL4 to_data_cvScript.sml:1432: ML code, not ported *)

(* [cv_pre] *)
let pure_alt_pre = prove
 (`(!v. pure_alt_pre v) /\
   (!v. pure_alts_pre v)`,
  CHEAT_TAC);;

let pure_alt_thm = prove
 (`(!v. pure_alt v = pure v) /\
   (!v. pure_alts v = ALL pure v)`,
  CHEAT_TAC);;

(* HOL4 to_data_cvScript.sml:1450: ML code, not ported *)

let decide_inline_alt_def = new_definition
  `decide_inline_alt c fapx app_lopt app_arity =
     match fapx with clos_known_ClosNoInline loc arity ->
           if app_lopt = NONE /\ app_arity = arity then inlD_Annotate loc
             else inlD_Nothing
       | clos_known_Clos loc arity body body_size ->
           if app_lopt = NONE /\ app_arity = arity then
             (if body_size < c * (1 + app_arity) /\
                 ~(contains_closures [body]) /\
                 clos_known_closed (clos_Fn (implode "") NONE NONE app_arity
                   body) then
                 // Consider moving these checks to the point where Clos approximations
                 // are created, and bake them into the val_approx_val relation.
                 inlD_LetInline body
                else inlD_Annotate loc)
           else inlD_Nothing
       | _ -> inlD_Nothing`;;

(* HOL4 to_data_cvScript.sml:1472: ML code, not ported *)

let decide_inline_alt_thm = prove
 (`decide_inline c fapx app_lopt app_arity = decide_inline_alt
  (clos_known_config_inline_factor c) fapx app_lopt app_arity`,
  CHEAT_TAC);;

let decide_inline_alt_LetInline = prove
 (`!c fapx lopt arity body.
     decide_inline_alt c fapx lopt arity = inlD_LetInline body ==> 0 < c`,
  CHEAT_TAC);;

(* the clauses in three quotations: fns is ((num # exp) list) and (_)list; t
   is tra, mlstring and (mlstring list); xs is (exp list), (_)list and
   (_#_)list, which one quotation cannot typecheck *)
(* the termination relation that HOL4 gives is
     inv_image (MEASURE I LEX MEASURE I)
                                (\x. match x with
                                   sum_INL (c,_,x,vs,g) -> (c,clos_exp_size x)
                                   | sum_INR (sum_INL (c,_,xs,vs,g)) ->
                                     (c,list_size clos_exp_size xs)
                                   | sum_INR (sum_INR (clos,vs,c,_,g,xs)) ->
                                     (c,list_size (pair_size (\x. x)
                                       flat_exp_size)
                                     xs))
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 to_data_cvScript.sml:1583-1591: the tactic that proves the
   termination *)
let known_alt_def,known_alt_ind = define_guess_clauses
  [`(known_alt inl_factor inl_max (clos_Var t v) vs (g:val_approx spt) =
         ((((clos_Var t v:clos_exp),any_el v vs clos_known_Other)),g)) /\
    (known_alt inl_factor inl_max (clos_If t x1 x2 x3) vs (g:val_approx spt) =
         let (ea1,g) = known_alt inl_factor inl_max (x1) vs g in
         let (ea2,g) = known_alt inl_factor inl_max (x2) vs g in
         let (ea3,g) = known_alt inl_factor inl_max (x3) vs g in
         let (e1,a1) = ea1 in
         let (e2,a2) = ea2 in
         let (e3,a3) = ea3 in
           (((clos_If t e1 e2 e3),clos_known_merge a2 a3),g)) /\
    (known_alt inl_factor inl_max (clos_Let t xs x2) vs (g:val_approx spt) =
         let (ea1,g) = known_alts inl_factor inl_max xs vs g in
         let (ea2,g) = known_alt inl_factor inl_max (x2) (APPEND (MAP SND
             ea1) vs) g in
         let (e2,a2) = ea2 in
           (((clos_Let t (MAP FST ea1) e2,a2)),g)) /\
    (known_alt inl_factor inl_max (clos_Raise t x1) vs (g:val_approx spt) =
         let (ea1,g) = known_alt inl_factor inl_max (x1) vs g in
         let (e1,a1) = ea1 in
           (((clos_Raise t e1,clos_known_Impossible)),g)) /\
    (known_alt inl_factor inl_max (clos_Tick t x1) vs (g:val_approx spt) =
         let (ea1,g) = known_alt inl_factor inl_max (x1) vs g in
         let (e1,a1) = ea1 in
           (((clos_Tick t e1,a1)),g)) /\
    (known_alt inl_factor inl_max (clos_Handle t x1 x2) vs (g:val_approx spt) =
         let (ea1,g) = known_alt inl_factor inl_max (x1) vs g in
         let (ea2,g) = known_alt inl_factor inl_max (x2) (CONS
             clos_known_Other vs) g in
         let (e1,a1) = ea1 in
         let (e2,a2) = ea2 in
           (((clos_Handle t e1 e2,clos_known_merge a1 a2)),g)) /\
    (known_alt inl_factor inl_max (clos_Call t ticks dest xs) vs (g:val_approx
    spt) =
         let (ea1,g) = known_alts inl_factor inl_max xs vs g in
           (((clos_Call t ticks dest (MAP FST
               ea1),clos_known_Other)),g)) /\
    (known_alt inl_factor inl_max (clos_Op t op xs) vs (g:val_approx spt) =
         let (ea1,g) = known_alts inl_factor inl_max xs vs g in
         let (a,g) = known_op op (REVERSE (MAP SND ea1)) g in
         let e =
             (if isGlobal op then
               match gO_destApx a with gO_None -> clos_op_SmartOp t op (MAP
                   FST ea1)
                 | gO_Int i -> clos_Op t (clos_IntOp (clos_Const i)) (MAP
                     FST ea1)
                 | gO_NullTuple tag -> clos_Op t (clos_BlockOp (clos_Cons
                     tag)) (MAP FST ea1)
              else clos_op_SmartOp t op (MAP FST ea1)) in
           (((e,a)),g)) /\
    (known_alt inl_factor inl_max (clos_App t loc_opt x xs) vs (g:val_approx
    spt) =
         let (ea2,g) = known_alts inl_factor inl_max xs vs g in
         let (ea1,g) = known_alt inl_factor inl_max (x) vs g in
         let (e1,a1) = ea1 in
           match decide_inline_alt inl_factor a1 loc_opt (LENGTH xs) with
               inlD_Nothing -> (((clos_App t loc_opt e1 (MAP FST
               ea2),clos_known_Other)),g)
             | inlD_Annotate new_loc -> (((clos_App t (SOME new_loc) e1
                 (MAP FST ea2),clos_known_Other)),g)
             | inlD_LetInline body ->
                 let (eabody,_) = known_alt (inl_factor DIV 2) inl_max
                     (body) (MAP SND ea2) g in
                 let (ebody,abody) = eabody in
                   if pure x then
                     (((
                        // We don't have to evaluate x
                        clos_Let (mk_cons t 0) (MAP FST ea2)
                              (clos_known_mk_Ticks t 1 (LENGTH xs)
                                  ebody),abody)),g)
                   else (((
                        // We need to evaluate x for its side-effects,
                        // but we must do so after evaluating the args.
                        clos_Let (mk_cons t 0) (SNOC e1 (MAP FST ea2))
                              (clos_known_mk_Ticks t 1 (LENGTH xs)
                                  ebody),abody)),g)) /\
    (known_alts inl_factor inl_max [] vs (g:val_approx spt) = ([],g)) /\
    (known_alts inl_factor inl_max (CONS (x:clos_exp) xs) vs (g:val_approx spt)
    =
         let (eas1,g) = known_alt inl_factor inl_max (x) vs g in
         let (eas2,g) = known_alts inl_factor inl_max (xs) vs g in
           (CONS eas1 eas2,g)) /\
    (known_let_alts _ _ _ _ _ [] = [])`;
   `(known_alt inl_factor inl_max (clos_Fn t loc_opt ws_opt num_args x1) vs
    (g:val_approx spt) =
         let (ea1,g) = known_alt inl_factor inl_max (x1) (APPEND (REPLICATE
             num_args clos_known_Other) vs) g in
         let (body,a1) = ea1 in
           (((clos_Fn t loc_opt NONE num_args body,
              (match loc_opt with SOME loc -> clos_approx inl_max loc
                  num_args x1
                | NONE -> clos_known_Other))),g)) /\
    (known_let_alts clos vs inl_factor inl_max (g:val_approx spt) (CONS
    (num_args,x) xs) =
       let
         new_vs = APPEND (APPEND (REPLICATE num_args clos_known_Other)
             clos) vs in let
         res = known_alt inl_factor inl_max x new_vs g in CONS
             (num_args,FST (FST res)) (known_let_alts clos vs inl_factor
             inl_max g xs))`;
   `known_alt inl_factor inl_max (clos_Letrec t loc_opt _ fns x1) vs
    (g:val_approx spt) =
         let clos = (match loc_opt with
                       NONE -> REPLICATE (LENGTH fns) clos_known_Other
                    | SOME loc -> clos_gen_noinline loc 0 fns) in
         // The following ignores SetGlobal within fns, but it shouldn't
         // appear there, and missing it just means this opt will do less.
         let new_fns = known_let_alts clos vs inl_factor inl_max g fns in
         let (ea1,g) = known_alt inl_factor inl_max (x1) (APPEND clos vs) g
             in
         let (e1,a1) = ea1 in
           (((clos_Letrec t loc_opt NONE new_fns e1,a1)),g)`];;

(* HOL4 to_data_cvScript.sml:1593-1606: a proof *)

(* [cv_pre] *)
let clos_op_lift_exps_pre = prove
 (`!v n binds. clos_op_lift_exps_pre v n binds`,
  CHEAT_TAC);;

let eq_pure_list_alt,eq_pure_list_alt_ind = define_guess
  `eq_pure_list_alt x1 x2 =
   match (x1,x2) with
     (SUC ck,[x,y]) ->
    (match eq_direct x y with SOME z -> display_List [z]
     | NONE ->
       (match dest_Op clos_op_dest_Cons x,dest_Op clos_op_dest_Cons y with
         (NONE,NONE) -> display_List [clos_Op backend_common_None (clos_BlockOp
         clos_Equal) [x; y]]
       | (SOME (t1,xs),SOME (t2,ys)) ->
            if ~(t1 = t2) \/ ~(LENGTH xs = LENGTH ys) then display_List
              [MakeBool F]
            else eq_pure_list_alt ck (ZIP (REVERSE xs) (REVERSE ys))
       | (SOME (t1,xs),NONE) ->
            misc_Append (misc_List [clos_Op backend_common_None
              (clos_BlockOp (clos_TagLenEq t1 (LENGTH xs))) [y]])
                   (eq_pure_list_alt ck (MAPi (\i x. (x,clos_Op
                     backend_common_None (clos_BlockOp (clos_ElemAt i)) [y]))
                     (REVERSE xs)))
       | (NONE,SOME (t1,ys)) -> eq_pure_list_alt ck [(y,x)]))
   | (SUC ck,CONS xy xys) -> misc_Append (eq_pure_list_alt ck [xy])
     (eq_pure_list_alt ck xys)
   | (_,_) -> misc_Nil`;;

(* HOL4 to_data_cvScript.sml:1633: ML code, not ported *)

(* [cv_pre] *)
let eq_pure_list_alt_pre = prove
 (`!v0 v. eq_pure_list_alt_pre v0 v`,
  CHEAT_TAC);;

(* HOL4 to_data_cvScript.sml:1644-1648: a theorem that HOL4 states as the
   value of an ML expression: SUM_MAP_const *)

let eq_pure_list_alt_thm = prove
 (`!ck xs. SUM (MAP (\(x,y). 1 + cons_measure x + cons_measure y +
                              (if cons_measure x < cons_measure y then 1
                                else 0)) xs) <= ck ==> eq_pure_list_alt ck xs
                                = eq_pure_list xs`,
  CHEAT_TAC);;

let eq_pure_list_alt_eq = prove
 (`!xs. eq_pure_list xs = eq_pure_list_alt
                          (SUM (MAP (\(x,y). 1 + cons_measure x +
                            cons_measure y +
                              (if cons_measure x < cons_measure y then 1
                                else 0)) xs)) xs`,
  CHEAT_TAC);;

(* the termination relation that HOL4 gives is
     MEASURE (\x. sum_CASE x flat_exp_size (list_size flat_exp_size))
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 to_data_cvScript.sml:1719-1723: the tactic that proves the
   termination *)
let cons_measure_alt_def,cons_measure_alt_ind = define_guess
  `(cons_measure_alt x =
    (match dest_Op clos_op_dest_Cons x with NONE -> 0
     | SOME (_,xs) -> cons_measures_alt xs + LENGTH xs + 1)) /\
   (cons_measures_alt [] = 0) /\
   (cons_measures_alt (CONS x xs) = cons_measure_alt x + cons_measures_alt
    xs)`;;

(* HOL4 to_data_cvScript.sml:1725-1736: a proof *)

(* [cv_pre] *)
let cons_measure_alt_pre = prove
 (`(!x. cons_measure_alt_pre x) /\
   (!v. cons_measures_alt_pre v)`,
  CHEAT_TAC);;

(* HOL4 to_data_cvScript.sml:1746-1747: a theorem that HOL4 states as the
   value of an ML expression: cons_measure_pmatch_elim *)

let cons_measure_alt_thm = prove
 (`(!x. cons_measure_alt x = cons_measure x) /\
   (!v. cons_measures_alt v = SUM (MAP cons_measure v))`,
  CHEAT_TAC);;

(* HOL4 to_data_cvScript.sml:1761: ML code, not ported *)

(* HOL4 to_data_cvScript.sml:1763: ML code, not ported *)

(* HOL4 to_data_cvScript.sml:1765: ML code, not ported *)

let cv_mul_zero = prove
 (`cv_mul (Num 0) x = Num 0`,
  CHEAT_TAC);;

let cv_lt_zero = prove
 (`cv_lt x (Num 0) = Num 0`,
  CHEAT_TAC);;

(* [local] *)
let cv_lt_eq_SUC = prove
 (`cv_lt x y = Num (SUC k) <=>
   k = 0 /\ (?n m. x = Num n /\ y = Num m /\ n < m)`,
  CHEAT_TAC);;

(* why doesn't online cvTheory.cv_mul_def achieve this?*)
let cv_mul_oneline = prove
 (`cv_mul x y =
   match (x,y) with
     (Num m,Num n) -> Num (m * n)
   | _ -> Num 0`,
  CHEAT_TAC);;

let cv_add_oneline = prove
 (`cv_add x y =
   match (x,y) with
     (Num m,Num n) -> Num (m + n)
   | (Num m,_) -> Num m
   | (_,Num n) -> Num n
   | _ -> Num 0`,
  CHEAT_TAC);;

(* HOL4 to_data_cvScript.sml:1809-1829: a proof *)

(* [cv_pre] *)
let known_alt_pre = prove
 (`(!inl_factor inl_max v vs g. known_alt_pre inl_factor inl_max v vs g) /\
   (!inl_factor inl_max v vs g. known_alts_pre inl_factor inl_max v vs g) /\
   (!v1 v2 v3 v4 v5 v. known_let_alts_pre v1 v2 v3 v4 v5 v)`,
  CHEAT_TAC);;

let known_alt_thm = prove
 (`(!inf' inm v vs g c.
     inf' = clos_known_config_inline_factor c /\ inm =
       clos_known_config_inline_max_body_size c ==>
     known_alt (clos_known_config_inline_factor c)
       (clos_known_config_inline_max_body_size c) v vs g =
     (\(x,y). (HD x,y)) (known c [v] vs g)) /\
   (!inf' inm v vs g c.
     inf' = clos_known_config_inline_factor c /\ inm =
       clos_known_config_inline_max_body_size c ==>
     known_alts (clos_known_config_inline_factor c)
       (clos_known_config_inline_max_body_size c) v vs g =
     known c v vs g) /\
   (!clos vs inf' inm g fns c.
     inf' = clos_known_config_inline_factor c /\ inm =
       clos_known_config_inline_max_body_size c ==>
     known_let_alts clos vs (clos_known_config_inline_factor c)
       (clos_known_config_inline_max_body_size c) g fns =
     MAP (\(num_args,x).
            let new_vs = APPEND (APPEND (REPLICATE num_args
              clos_known_Other) clos) vs in
              let res = known c [x] new_vs g in
                (num_args,FST (HD (FST res)))) fns)`,
  CHEAT_TAC);;

(* HOL4 to_data_cvScript.sml:1876-1878: ML code, not ported *)

(* HOL4 to_data_cvScript.sml:1880: ML code, not ported *)

(* [cv_pre] *)
let clos_fvs_remove_fvs_sing_pre = prove
 (`(!fvs v. clos_fvs_remove_fvs_sing_pre fvs v) /\
   (!fvs v. clos_fvs_remove_fvs_list_pre fvs v) /\
   (!m fvs v. clos_fvs_remove_fvs_let_pre m fvs v)`,
  CHEAT_TAC);;

(* HOL4 to_data_cvScript.sml:1890: ML code, not ported *)

(* HOL4 to_data_cvScript.sml:1892: ML code, not ported *)

(* HOL4 to_data_cvScript.sml:1894: ML code, not ported *)

(* [cv_pre] *)
let clos_ticks_remove_ticks_sing_pre = prove
 (`(!v. clos_ticks_remove_ticks_sing_pre v) /\
   (!v. clos_ticks_remove_ticks_list_pre v) /\
   (!v. clos_ticks_remove_ticks_let_pre v)`,
  CHEAT_TAC);;

(* HOL4 to_data_cvScript.sml:1904: ML code, not ported *)

(* HOL4 to_data_cvScript.sml:1906: ML code, not ported *)

(* [cv_pre] *)
let clos_letop_let_op_sing_pre = prove
 (`(!v. clos_letop_let_op_sing_pre v) /\
   (!v. clos_letop_let_op_list_pre v) /\
   (!v. clos_letop_let_op_let_pre v)`,
  CHEAT_TAC);;

(* HOL4 to_data_cvScript.sml:1917: ML code, not ported *)

(* HOL4 to_data_cvScript.sml:1919: ML code, not ported *)

(* clos_call *)

(* TODO: free_def is duplicated between clos_known and clos_call; it
   should probably be moved to a common ancestor theory *)
let free_eq_free = prove
 (`!xs. clos_known_free xs = clos_call_free xs`,
  CHEAT_TAC);;

(* HOL4 to_data_cvScript.sml:1949: ML code, not ported *)

(* HOL4 to_data_cvScript.sml:1951-1958: a proof *)

(* [cv_pre] *)
let clos_call_calls_sing_pre = prove
 (`(!v g. clos_call_calls_sing_pre v g) /\
   (!v g. clos_call_calls_sing_list_pre v g)`,
  CHEAT_TAC);;

(* HOL4 to_data_cvScript.sml:1980: ML code, not ported *)

(* HOL4 to_data_cvScript.sml:1982: ML code, not ported *)

(* clos_annotate *)

(* HOL4 to_data_cvScript.sml:1986: ML code, not ported *)
(* [cv_pre] *)
let clos_annotate_shift_sing_pre = prove
 (`(!v m l i. clos_annotate_shift_sing_pre v m l i) /\
   (!v m l i. clos_annotate_shift_list_pre v m l i) /\
   (!fns_len k new_i v. clos_annotate_shift_letrec_pre fns_len k new_i v)`,
  CHEAT_TAC);;

(* HOL4 to_data_cvScript.sml:1996: ML code, not ported *)
(* [cv_pre] *)
let clos_annotate_alt_free_sing_pre = prove
 (`(!v. clos_annotate_alt_free_sing_pre v) /\
   (!v. clos_annotate_alt_free_list_pre v) /\
   (!m v. clos_annotate_alt_free_letrec_pre m v)`,
  CHEAT_TAC);;

(* HOL4 to_data_cvScript.sml:2006-2007: ML code, not ported *)

(* compile_common from clos_to_bvl *)

(* HOL4 to_data_cvScript.sml:2011-2012: ML code, not ported *)

(* bvl_jump *)

let cv_LENGTH_right_depth = prove
 (`cv_LENGTH cv_xs = Num (cv_right_depth cv_xs)`,
  CHEAT_TAC);;

let cv_right_depth_cv_TAKE = prove
 (`!cv_xs n.
     n <= cv_right_depth cv_xs ==>
     cv_right_depth (cv_TAKE (Num n) cv_xs) = n`,
  CHEAT_TAC);;

let cv_right_depth_cv_DROP = prove
 (`!cv_xs n.
     n <= cv_right_depth cv_xs ==>
     cv_right_depth (cv_DROP (Num n) cv_xs) = cv_right_depth cv_xs - n`,
  CHEAT_TAC);;

(* HOL4 to_data_cvScript.sml:2043-2050: a proof *)

(* clos_to_bvl *)

(* HOL4 to_data_cvScript.sml:2054-2055: ML code, not ported *)

let cv_size_cv_map_snd_le = prove
 (`!xs. cv_size (cv_map_snd xs) <= cv_size xs`,
  CHEAT_TAC);;

(* HOL4 to_data_cvScript.sml:2065-2071: a proof *)

(* [cv_pre,local] *)
let clos_to_bvl_get_src_names_sing_pre = prove
 (`(!v l. clos_to_bvl_get_src_names_sing_pre v l) /\
   (!v l. clos_to_bvl_get_src_names_list_pre v l)`,
  CHEAT_TAC);;

(* HOL4 to_data_cvScript.sml:2081: ML code, not ported *)

(* HOL4 to_data_cvScript.sml:2083: ML code, not ported *)

(* HOL4 to_data_cvScript.sml:2085: ML code, not ported *)
(* [cv_pre] *)
let clos_to_bvl_recc_Lets_pre = prove
 (`!n nargs k rest.
     clos_to_bvl_recc_Lets_pre n nargs k rest <=> k <= LENGTH nargs`,
  CHEAT_TAC);;

(* HOL4 to_data_cvScript.sml:2093: ML code, not ported *)

(* HOL4 to_data_cvScript.sml:2095: ML code, not ported *)
(* [cv_pre] *)
let clos_to_bvl_build_recc_lets_pre = prove
 (`!nargs vs n1 fns_l c3.
     clos_to_bvl_build_recc_lets_pre nargs vs n1 fns_l c3 <=> ~(nargs =
       []) /\ fns_l <= LENGTH nargs`,
  CHEAT_TAC);;

(* HOL4 to_data_cvScript.sml:2105: ML code, not ported *)

(* HOL4 to_data_cvScript.sml:2107-2113: a proof *)

(* [cv_pre] *)
let clos_to_bvl_compile_exp_sing_pre = prove
 (`(!max_app v aux. clos_to_bvl_compile_exp_sing_pre max_app v aux) /\
   (!max_app v aux. clos_to_bvl_compile_exp_list_pre max_app v aux)`,
  CHEAT_TAC);;

(* HOL4 to_data_cvScript.sml:2124: ML code, not ported *)

(* HOL4 to_data_cvScript.sml:2126: ML code, not ported *)

(* HOL4 to_data_cvScript.sml:2128-2130: a proof *)

let cv_clos_to_bvl_code_split_imp = prove
 (`!x y z r1 r2.
     cv_clos_to_bvl_code_split x y z = Pair r1 r2 /\ ~(cv_size y = 0)
       /\ ~(cv_size z = 0) ==>
     cv_size r1 < cv_size x + cv_size y + cv_size z /\
     cv_size r2 < cv_size x + cv_size y + cv_size z`,
  CHEAT_TAC);;

(* HOL4 to_data_cvScript.sml:2144-2147: a proof *)

(* [cv_pre] *)
let clos_to_bvl_code_sort_pre = prove
 (`!v. clos_to_bvl_code_sort_pre v`,
  CHEAT_TAC);;

(* HOL4 to_data_cvScript.sml:2156: ML code, not ported *)

(* to_bvl *)

(* HOL4 to_data_cvScript.sml:2160: ML code, not ported *)

(* bvl_const *)

(* Bring everything from bvl to the front -- everything because this file is
   too big for me to try everything separately. *)

let mk_add_const_def = new_definition
  `mk_add_const = (\x1 c2.
             if c2 = (&0) then x1 else word_Op (clos_IntOp clos_Add) [x1;
               word_Op (clos_IntOp (clos_Const c2)) []])`;;

let mk_add_def = new_definition
  `mk_add = (\x1 x2.
   (let
      default = word_Op (clos_IntOp clos_Add) [x1; x2] in
      match dest_simple x2 with
        NONE ->
          (match case_op_const x1 with
             NONE -> default
           | SOME v5 ->
             (match case_op_const x2 with
               NONE -> default
             | SOME (op2,x21,n22) ->
               (match v5 with
                 (op1,x11,n12) ->
                   if op1 = clos_IntOp clos_Add /\ op2 = clos_IntOp clos_Add
                     then
                     mk_add_const (word_Op (clos_IntOp clos_Add) [x11; x21])
                       (n22 + n12)
                   else if op1 = clos_IntOp clos_Add /\ op2 = clos_IntOp
                     clos_Sub then
                     word_Op (clos_IntOp clos_Sub)
                       [word_Op (clos_IntOp clos_Sub) [x11; x21];
                        word_Op (clos_IntOp (clos_Const (n22 + n12))) []]
                   else if op1 = clos_IntOp clos_Sub /\ op2 = clos_IntOp
                     clos_Add then
                     mk_add_const (word_Op (clos_IntOp clos_Sub) [x11; x21])
                       (n22 + n12)
                   else default)))
      | SOME n2 ->
        (match case_op_const x1 with
          NONE ->
            (match dest_simple x1 with
               NONE -> mk_add_const x1 n2
             | SOME n1 -> word_Op (clos_IntOp (clos_Const (n2 + n1))) [])
        | SOME (clos_IntOp clos_Add,x11,n12) -> mk_add_const x11 (n2 + n12)
        | SOME (clos_IntOp clos_Sub,x11,n12) ->
          word_Op (clos_IntOp clos_Sub) [x11; word_Op (clos_IntOp
            (clos_Const (n2 + n12))) []]
        | SOME (op,x11,n12) -> default)))`;;

let mk_sub_def = new_definition
  `mk_sub = (\x1 x2.
   (let
      default = word_Op (clos_IntOp clos_Sub) [x1; x2] in
      match dest_simple x2 with
        NONE ->
          (match case_op_const x1 with
             NONE -> default
           | SOME v5 ->
             (match case_op_const x2 with
               NONE -> default
             | SOME (op2,x21,n22) ->
               (match v5 with
                 (op1,x11,n12) ->
                   if op1 = clos_IntOp clos_Add /\ op2 = clos_IntOp clos_Add
                     then
                     word_Op (clos_IntOp clos_Add)
                       [word_Op (clos_IntOp clos_Sub) [x11; x21];
                        word_Op (clos_IntOp (clos_Const (n22 - n12))) []]
                   else if op1 = clos_IntOp clos_Add /\ op2 = clos_IntOp
                     clos_Sub then
                     word_Op (clos_IntOp clos_Sub)
                       [word_Op (clos_IntOp clos_Add) [x11; x21];
                        word_Op (clos_IntOp (clos_Const (n22 - n12))) []]
                   else if op1 = clos_IntOp clos_Sub /\ op2 = clos_IntOp
                     clos_Add then
                     mk_add_const (word_Op (clos_IntOp clos_Add) [x11; x21])
                       (n22 - n12)
                   else default)))
      | SOME n2 ->
        (match case_op_const x1 with
          NONE ->
            (match dest_simple x1 with
               NONE -> default
             | SOME n1 -> word_Op (clos_IntOp (clos_Const (n2 - n1))) [])
        | SOME (clos_IntOp clos_Add,x11,n12) ->
          word_Op (clos_IntOp clos_Sub) [x11; word_Op (clos_IntOp
            (clos_Const (n2 - n12))) []]
        | SOME (clos_IntOp clos_Sub,x11,n12) -> mk_add_const x11 (n2 - n12)
        | SOME (op,x11,n12) -> default)))`;;

let mk_mul_def = new_definition
  `mk_mul = (\x1 x2.
   (let
      default = word_Op (clos_IntOp clos_Mult) [x1; x2] in
      match dest_simple x2 with
        NONE ->
          (match case_op_const x1 with
             NONE -> default
           | SOME v5 ->
             (match case_op_const x2 with
               NONE -> default
             | SOME (op2,x21,n22) ->
               (match v5 with
                 (op1,x11,n12) ->
                   if op1 = clos_IntOp clos_Mult /\ op2 = clos_IntOp
                     clos_Mult then
                     word_Op (clos_IntOp clos_Mult)
                       [word_Op (clos_IntOp (clos_Const (n22 * n12))) [];
                        word_Op (clos_IntOp clos_Mult) [x11; x21]]
                   else default)))
      | SOME n2 ->
        (match case_op_const x1 with
          NONE ->
            (match dest_simple x1 with
               NONE ->
                 if n2 = 1 then x1
                 else if n2 = --1 then
                   (let
                      default = word_Op (clos_IntOp clos_Sub) [x1; word_Op
                        (clos_IntOp (clos_Const (&0))) []] in
                      match case_op_const x1 with
                        NONE ->
                          (match dest_simple x1 with
                             NONE -> default
                           | SOME n1 -> word_Op (clos_IntOp (clos_Const
                             (--n1))) [])
                      | SOME (clos_IntOp clos_Add,x11,n12) ->
                        word_Op (clos_IntOp clos_Sub) [x11; word_Op
                          (clos_IntOp (clos_Const (--n12))) []]
                      | SOME (clos_IntOp clos_Sub,x11,n12) ->
                        mk_add_const x11 (--n12)
                      | SOME (op,x11,n12) -> default)
                 else default
             | SOME n1 -> word_Op (clos_IntOp (clos_Const (n2 * n1))) [])
        | SOME (clos_IntOp clos_Mult,x11,n12) ->
          word_Op (clos_IntOp clos_Mult) [x11; word_Op (clos_IntOp
            (clos_Const (n2 * n12))) []]
        | SOME (op,x11,n12) -> default)))`;;

(* HOL4 to_data_cvScript.sml:2298-2306: a theorem that HOL4 states as the
   value of an ML expression: SmartOp2_eq *)

(* HOL4 to_data_cvScript.sml:2308-2313: ML code, not ported *)

(* HOL4 to_data_cvScript.sml:2315: ML code, not ported *)
(* [cv_pre] *)
let bvl_const_compile_sing_pre = prove
 (`(!v env. bvl_const_compile_sing_pre env v) /\
   (!v env. bvl_const_compile_list_pre env v)`,
  CHEAT_TAC);;

(* HOL4 to_data_cvScript.sml:2323: ML code, not ported *)

(* bvl_handle *)

(* HOL4 to_data_cvScript.sml:2327-2329: ML code, not ported *)

(* HOL4 to_data_cvScript.sml:2331: ML code, not ported *)
(* [cv_pre,local] *)
let bvl_handle_compile_sing_pre = prove
 (`(!v l n. bvl_handle_compile_sing_pre l n v) /\
   (!v l n. bvl_handle_compile_list_pre l n v)`,
  CHEAT_TAC);;

(* HOL4 to_data_cvScript.sml:2339-2341: ML code, not ported *)

(* HOL4 to_data_cvScript.sml:2343: ML code, not ported *)
(* [cv_pre] *)
let bvl_handle_handle_adj_vars_pre = prove
 (`(!v l d. bvl_handle_handle_adj_vars_pre l d v) /\
   (!v l d. bvl_handle_handle_adj_vars1_pre l d v)`,
  CHEAT_TAC);;

(* HOL4 to_data_cvScript.sml:2351-2360: a proof *)

(* [cv_pre] *)
let bvl_handle_handle_simp_pre = prove
 (`(!v. bvl_handle_handle_simp_pre v) /\
   (!v. bvl_handle_handle_simp_list_pre v) /\
   (!x1 x2 l. bvl_handle_make_handle_pre x1 x2 l)`,
  CHEAT_TAC);;

(* HOL4 to_data_cvScript.sml:2371-2372: ML code, not ported *)

(* HOL4 to_data_cvScript.sml:2374-2378: a proof *)

(* [cv_pre] *)
let bvl_handle_compile_seqs_pre = prove
 (`!cut_size e acc. bvl_handle_compile_seqs_pre cut_size e acc`,
  CHEAT_TAC);;

(* HOL4 to_data_cvScript.sml:2387: ML code, not ported *)

(* bvl_inline *)

(* HOL4 to_data_cvScript.sml:2391: ML code, not ported *)

(* HOL4 to_data_cvScript.sml:2393: ML code, not ported *)
(* [cv_pre,local] *)
let bvl_inline_is_small_sing_pre = prove
 (`(!v n. bvl_inline_is_small_sing_pre n v) /\
   (!v n. bvl_inline_is_small_list_pre n v)`,
  CHEAT_TAC);;

(* HOL4 to_data_cvScript.sml:2401: ML code, not ported *)

(* HOL4 to_data_cvScript.sml:2403: ML code, not ported *)
(* [cv_pre,local] *)
let bvl_inline_is_rec_sing_pre = prove
 (`(!v n. bvl_inline_is_rec_sing_pre n v) /\
   (!v n. bvl_inline_is_rec_list_pre n v)`,
  CHEAT_TAC);;

(* HOL4 to_data_cvScript.sml:2411: ML code, not ported *)

(* HOL4 to_data_cvScript.sml:2413: ML code, not ported *)
(* [cv_pre,local] *)
let bvl_inline_tick_inline_all_pre = prove
 (`!v limit' cs aux. bvl_inline_tick_inline_all_pre limit' cs v aux`,
  CHEAT_TAC);;

(* HOL4 to_data_cvScript.sml:2420: ML code, not ported *)

(* HOL4 to_data_cvScript.sml:2422: ML code, not ported *)
(* [cv_pre,local] *)
let bvl_inline_let_op_one_pre = prove
 (`(!v. bvl_inline_let_op_one_pre v) /\
   (!v. bvl_inline_let_op_list_pre v)`,
  CHEAT_TAC);;

(* HOL4 to_data_cvScript.sml:2430: ML code, not ported *)

(* HOL4 to_data_cvScript.sml:2432: ML code, not ported *)
(* [cv_pre,local] *)
let bvl_inline_remove_ticks_sing_pre = prove
 (`(!v. bvl_inline_remove_ticks_sing_pre v) /\
   (!v. bvl_inline_remove_ticks_list_pre v)`,
  CHEAT_TAC);;

(* HOL4 to_data_cvScript.sml:2440-2442: ML code, not ported *)

(* bvi_tailrec *)

(* HOL4 to_data_cvScript.sml:2446-2447: ML code, not ported *)

(* [local] *)
let term_ok_int_eq = prove
 (`term_ok_int ts expr <=>
   (match expr with bvi_Var i -> if i < LENGTH ts then EL i ts =
     bvi_tailrec_Int else F
   | bvi_Op op xs ->
      (if xs = [] /\ word_inst_is_const op then T else match xs with [x; y]
        -> is_arith op /\ term_ok_int ts x /\ term_ok_int ts y
         | _ -> F)
   | _ -> F)`,
  CHEAT_TAC);;

(* HOL4 to_data_cvScript.sml:2468: ML code, not ported *)
(* [cv_pre,local] *)
let bvi_tailrec_term_ok_int_pre = prove
 (`!ts expr. bvi_tailrec_term_ok_int_pre ts expr`,
  CHEAT_TAC);;

(* HOL4 to_data_cvScript.sml:2477: ML code, not ported *)

(* [local] *)
let cv_bvi_tailrec_get_bin_args_lemma = prove
 (`cv_bvi_tailrec_get_bin_args (Pair t v) = Pair x (Pair y z) ==>
   cv_size y <= cv_size v /\
   cv_size z <= cv_size v`,
  CHEAT_TAC);;

(* HOL4 to_data_cvScript.sml:2488-2493: a proof *)

(* [cv_pre] *)
let bvi_tailrec_term_ok_any_pre = prove
 (`!ts list' v. bvi_tailrec_term_ok_any_pre ts list' v`,
  CHEAT_TAC);;

(* HOL4 to_data_cvScript.sml:2503: ML code, not ported *)
(* [cv_pre] *)
let bvi_tailrec_scan_expr_sing_pre = prove
 (`(!v ts loc. bvi_tailrec_scan_expr_sing_pre ts loc v) /\
   (!v ts loc. bvi_tailrec_scan_expr_list_pre ts loc v)`,
  CHEAT_TAC);;

(* HOL4 to_data_cvScript.sml:2511: ML code, not ported *)
(* [cv_pre] *)
let bvi_tailrec_rewrite_pre = prove
 (`!loc next' opr acc ts v. bvi_tailrec_rewrite_pre loc next' opr acc ts v`,
  CHEAT_TAC);;

(* HOL4 to_data_cvScript.sml:2520: ML code, not ported *)
(* [cv_pre] *)
let bvi_tailrec_has_rec_sing_pre = prove
 (`(!v loc. bvi_tailrec_has_rec_sing_pre loc v) /\
   (!v loc. bvi_tailrec_has_rec_list_pre loc v)`,
  CHEAT_TAC);;

(* HOL4 to_data_cvScript.sml:2528-2529: ML code, not ported *)

(* HOL4 to_data_cvScript.sml:2531: ML code, not ported *)
(* [cv_pre] *)
let bvi_tailrec_compile_each_pre = prove
 (`!next' v. bvi_tailrec_compile_each_pre next' v`,
  CHEAT_TAC);;

(* HOL4 to_data_cvScript.sml:2539: ML code, not ported *)

(* bvi_let *)

let cv_size_LAST = prove
 (`!g. cv_size (cv_LAST g) <= cv_size g`,
  CHEAT_TAC);;

let cv_size_FRONT = prove
 (`!g. cv_size (cv_FRONT g) <= cv_size g`,
  CHEAT_TAC);;

(* HOL4 to_data_cvScript.sml:2555-2565: a proof *)

(* [cv_pre] *)
let bvi_let_compile_sing_pre = prove
 (`(!env d v. bvi_let_compile_sing_pre env d v) /\
   (!env d v. bvi_let_compile_list_pre env d v)`,
  CHEAT_TAC);;

(* HOL4 to_data_cvScript.sml:2575: ML code, not ported *)

(* bvi_inline *)

(* HOL4 to_data_cvScript.sml:2579: ML code, not ported *)
(* [cv_pre,local] *)
let bvi_inline_bvi_mk_tick_pre = prove
 (`!n e. bvi_inline_bvi_mk_tick_pre n e`,
  CHEAT_TAC);;

(* HOL4 to_data_cvScript.sml:2586-2587: ML code, not ported *)

(* HOL4 to_data_cvScript.sml:2589: ML code, not ported *)
(* [cv_pre,local] *)
let bvi_inline_inline_exp_pre = prove
 (`(!cs v. bvi_inline_inline_exp_pre cs v) /\
   (!cs v. bvi_inline_inline_exps_pre cs v)`,
  CHEAT_TAC);;

(* HOL4 to_data_cvScript.sml:2598-2600: ML code, not ported *)
(* [cv_pre,local] *)
let bvi_inline_remove_ticks_exp_pre = prove
 (`(!v. bvi_inline_remove_ticks_exp_pre v) /\
   (!v. bvi_inline_remove_ticks_exps_pre v)`,
  CHEAT_TAC);;

(* HOL4 to_data_cvScript.sml:2609-2611: ML code, not ported *)

(* bvi_tmc *)

(* HOL4 to_data_cvScript.sml:2615: ML code, not ported *)

(* HOL4 to_data_cvScript.sml:2617: ML code, not ported *)

(* [cv_pre] *)
let bvi_tmc_bvi_to_cb_aux_pre = prove
 (`(!n loc tag v. bvi_tmc_bvi_to_cb_aux_sing_pre n loc tag v) /\
   (!n loc tag v. bvi_tmc_bvi_to_cb_aux_pre n loc tag v)`,
  CHEAT_TAC);;

(* HOL4 to_data_cvScript.sml:2627-2628: ML code, not ported *)

(* HOL4 to_data_cvScript.sml:2630: ML code, not ported *)
(* [cv_pre] *)
let bvi_tmc_compile_each_pre = prove
 (`!next' v. bvi_tmc_compile_each_pre next' v`,
  CHEAT_TAC);;

(* HOL4 to_data_cvScript.sml:2638: ML code, not ported *)

(* bvl_to_bvi *)

(* HOL4 to_data_cvScript.sml:2642-2644: ML code, not ported *)

(* HOL4 to_data_cvScript.sml:2646: ML code, not ported *)

(* [local] *)
let destLet_lemma = prove
 (`cv_bvl_to_bvi_destLet (cv_fst z) = Pair x1 x2 ==>
   cv_size x1 <= cv_size z /\
   cv_size x2 <= cv_size z`,
  CHEAT_TAC);;

(* [local] *)
let destLet_lemma2 = prove
 (`cv_bvl_to_bvi_destLet (cv_snd z) = Pair x1 x2 ==>
   cv_size x1 <= cv_size z /\
   cv_size x2 <= cv_size z`,
  CHEAT_TAC);;

(* HOL4 to_data_cvScript.sml:2672-2679: a proof *)

(* [cv_pre] *)
let bvl_to_bvi_compile_exps_sing_pre = prove
 (`(!n v. bvl_to_bvi_compile_exps_sing_pre n v) /\
   (!n v. bvl_to_bvi_compile_exps_list_pre n v)`,
  CHEAT_TAC);;

(* HOL4 to_data_cvScript.sml:2689: ML code, not ported *)

(* HOL4 to_data_cvScript.sml:2691: ML code, not ported *)
(* [cv_pre] *)
let bvl_to_bvi_global_count_sing_pre = prove
 (`(!v. bvl_to_bvi_global_count_sing_pre v) /\
   (!v. bvl_to_bvi_global_count_list_pre v)`,
  CHEAT_TAC);;

(* HOL4 to_data_cvScript.sml:2699-2700: ML code, not ported *)

(* to_bvi *)

(* HOL4 to_data_cvScript.sml:2704: ML code, not ported *)

(* to_data *)

let num_size_acc_def,num_size_acc_ind = define_guess
  `num_size_acc n acc =
     if n < 2 EXP 32 then acc + (2:num) else num_size_acc (n DIV 2 EXP
       32) (acc + 1)`;;

let num_size_eq_acc = prove
 (`num_size n = num_size_acc n 0`,
  CHEAT_TAC);;

(* HOL4 to_data_cvScript.sml:2722-2723: ML code, not ported *)

(* HOL4 to_data_cvScript.sml:2725: ML code, not ported *)
(* [cv_pre,local] *)
let data_live_compile_pre = prove
 (`!v live. data_live_compile_pre v live`,
  CHEAT_TAC);;

(* HOL4 to_data_cvScript.sml:2732-2733: ML code, not ported *)

(* HOL4 to_data_cvScript.sml:2735: ML code, not ported *)

(* [cv_pre,local] *)
let bvi_to_data_compile_sing_pre = prove
 (`(!n env tail live v. bvi_to_data_compile_sing_pre n env tail live v) /\
   (!n env live v. bvi_to_data_compile_list_pre n env live v)`,
  CHEAT_TAC);;

(* HOL4 to_data_cvScript.sml:2754-2757: ML code, not ported *)

(* HOL4 to_data_cvScript.sml:2759-2763: ML code, not ported *)

(* [local] *)
let bvi_to_data_compile_sing = prove
 (`FST (bvi_to_data_compile n env t l [x]) = FST (bvi_to_data_compile_sing n
  env t l x)`,
  CHEAT_TAC);;

(* HOL4 to_data_cvScript.sml:2773: ML code, not ported *)

(* Explorer *)

(* HOL4 to_data_cvScript.sml:2777: ML code, not ported *)

(* [cv_pre] *)
let jsonLang_num_to_hex_digit_pre = prove
 (`!n. jsonLang_num_to_hex_digit_pre n`,
  CHEAT_TAC);;

(* HOL4 to_data_cvScript.sml:2785-2790: a proof *)

(* [cv_pre] *)
let presLang_num_to_hex_pre = prove
 (`!n. presLang_num_to_hex_pre n`,
  CHEAT_TAC);;

(* HOL4 to_data_cvScript.sml:2799: ML code, not ported *)

(* HOL4 to_data_cvScript.sml:2801: ML code, not ported *)

(* HOL4 to_data_cvScript.sml:2803: ML code, not ported *)

(* [cv_pre] *)
let presLang_exp_to_display_pre = prove
 (`(!c. presLang_exp_to_display_pre c) /\
   (!v. presLang_exp_to_display_list_pre v) /\
   (!v. presLang_pat_exp_to_display_list_pre v) /\
   (!v. presLang_fun_to_display_list_pre v)`,
  CHEAT_TAC);;

(* HOL4 to_data_cvScript.sml:2815: ML code, not ported *)

(* HOL4 to_data_cvScript.sml:2817: ML code, not ported *)

(* HOL4 to_data_cvScript.sml:2819: ML code, not ported *)

(* [cv_pre] *)
let presLang_flat_to_display_pre = prove
 (`(!v. presLang_flat_to_display_pre v) /\
   (!v. presLang_flat_to_display_list_pre v) /\
   (!v. presLang_pat_flat_to_display_list_pre v) /\
   (!v. presLang_fun_flat_to_display_list_pre v)`,
  CHEAT_TAC);;

(* HOL4 to_data_cvScript.sml:2831: ML code, not ported *)

(* HOL4 to_data_cvScript.sml:2833-2838: a proof *)

(* [cv_pre] *)
let presLang_num_to_varn_aux_pre = prove
 (`!n. presLang_num_to_varn_aux_pre n`,
  CHEAT_TAC);;

(* HOL4 to_data_cvScript.sml:2851: ML code, not ported *)

(* HOL4 to_data_cvScript.sml:2853-2857: a proof *)

(* [cv_pre] *)
let presLang_num_to_varn_list_pre = prove
 (`!ls n. presLang_num_to_varn_list_pre ls n`,
  CHEAT_TAC);;

(* HOL4 to_data_cvScript.sml:2866: ML code, not ported *)

(* HOL4 to_data_cvScript.sml:2868: ML code, not ported *)

(* [cv_pre] *)
let presLang_clos_to_display_pre = prove
 (`(!ns h v. presLang_clos_to_display_pre ns h v) /\
   (!ns h v. presLang_clos_to_display_list_pre ns h v) /\
   (!ns h i v. presLang_clos_to_display_lets_pre ns h i v) /\
   (!ns h i len v. presLang_clos_to_display_letrecs_pre ns h i len v)`,
  CHEAT_TAC);;

(* HOL4 to_data_cvScript.sml:2880: ML code, not ported *)

(* [cv_pre] *)
let presLang_bvl_to_display_pre = prove
 (`(!ns h v. presLang_bvl_to_display_pre ns h v) /\
   (!ns h v. presLang_bvl_to_display_list_pre ns h v) /\
   (!ns h i v. presLang_bvl_to_display_lets_pre ns h i v)`,
  CHEAT_TAC);;

(* HOL4 to_data_cvScript.sml:2891: ML code, not ported *)

(* [cv_pre] *)
let presLang_bvi_to_display_pre = prove
 (`(!ns h v. presLang_bvi_to_display_pre ns h v) /\
   (!ns h v. presLang_bvi_to_display_list_pre ns h v) /\
   (!ns h i v. presLang_bvi_to_display_lets_pre ns h i v)`,
  CHEAT_TAC);;

(* HOL4 to_data_cvScript.sml:2902: ML code, not ported *)

(* HOL4 to_data_cvScript.sml:2904: ML code, not ported *)

(* HOL4 to_data_cvScript.sml:2906: ML code, not ported *)

(* HOL4 to_data_cvScript.sml:2908: ML code, not ported *)

(* and the names it reads as variables are constants again *)
let _ = do_list unhide_constant
  ["Num";
   "Pair"];;

(* and the interface *)
let _ = unhide_overloads ();;
