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
needs "compiler/backend/flat_elim.ml";;
needs "compiler/backend/flat_pattern.ml";;
needs "compiler/backend/pattern_matching/pattern_semantics.ml";;
needs "compiler/backend/proofs/flat_elimProof.ml";;
needs "compiler/backend/proofs/flat_patternProof.ml";;
needs "compiler/backend/proofs/source_evalProof.ml";;
needs "compiler/backend/semantics/backendProps.ml";;
needs "compiler/backend/semantics/flatProps.ml";;
needs "compiler/backend/semantics/flatSem.ml";;
needs "compiler/backend/source_to_flat.ml";;
needs "lib/indexedLists.ml";;
needs "lib/lprefix_lub.ml";;
needs "lib/sptree.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "semantics/evaluate.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/namespace.ml";;
needs "semantics/proofs/namespaceProps.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "semantics/semantics.ml";;

(* the theories whose names the Ancestors blocks of the source
   bring, which are the ones that its statements read: the
   overloads of every other theory come out of the interface
   while this file loads *)
let _ = hol4_ancestors "source_to_flatProof"
  ["backendProps"; "backend_common"; "ffi"; "flatLang"; "flatProps";
   "flatSem"; "flat_elimProof"; "flat_patternProof"; "misc";
   "namespaceProps"; "semanticPrimitives"; "semanticPrimitivesProps";
   "semantics"; "source_evalProof"; "source_to_flat"];;

let _ = do_list hide_constant ["gc"; "id"; "path"; "vars"];;

(* HOL4 source_to_flatProofScript.sml:20: ML code, not ported *)

(* [local] *)
let compile_exps_length = prove
 (`LENGTH (compile_exps t m es) = LENGTH es`,
  CHEAT_TAC);;

let mapi_map = prove
 (`!f g l. MAPi f (MAP g l) = MAPi (\i x. f i (g x)) l`,
  CHEAT_TAC);;

(* [local] *)
let fst_lem = prove
 (`(\(p1,p1',p2). p1) = FST`,
  CHEAT_TAC);;

(* [local] *)
let funion_submap = prove
 (`FUNION x y SUBMAP z /\ DISJOINT (FDOM x) (FDOM y) ==> y SUBMAP z`,
  CHEAT_TAC);;

(* [local] *)
let flookup_funion_submap = prove
 (`(FUNION x y) SUBMAP z /\
    FLOOKUP (FUNION x y) k = SOME v ==>
    FLOOKUP z k = SOME v`,
  CHEAT_TAC);;

let FILTER_MAPi_ID = prove
 (`!ls f. FILTER P (MAPi f ls) = MAPi f ls <=>
   (!n. n < LENGTH ls ==> P (f n (EL n ls)))`,
  CHEAT_TAC);;

(* -- *)

(* value relation *)


(* bind locals with an arbitrary trace *)
let bind_locals_def = new_definition
  `bind_locals ts locals comp_map =
     nsBindList (MAP2 (\t x. (x,source_to_flat_Local t x)) ts
       locals) comp_map`;;

(* [local] *)
let nsAppend_bind_locals = prove
 (`!funs.
   nsAppend (alist_to_ns (MAP (\x. (x,source_to_flat_Local t x)) (MAP
     FST funs))) (bind_locals ts locals comp_map) =
   bind_locals (APPEND (REPLICATE (LENGTH funs) t) ts) (APPEND (MAP
     FST funs) locals) comp_map`,
  CHEAT_TAC);;

(* [local] *)
let nsBindList_pat_tups_bind_locals = prove
 (`!ls.
   ?tss.
   nsBindList (pat_tups t ls) (bind_locals ts locals comp_map) =
   bind_locals (APPEND tss ts) (APPEND ls locals) comp_map /\
   LENGTH tss = LENGTH ls`,
  CHEAT_TAC);;

let global_env_FIELDS = define_record "global_env"
  ["v","(flatSem_v option) list";
   "c","((num#num option)#num,stamp)fmap";
   "tys","(num,(num#num) list)fmap"];;

let submap_distinct_fupdate_flookup = prove
 (`~(x IN FDOM f) ==>
     (f |+ (x,y) SUBMAP g <=> FLOOKUP g x = SOME y /\ f SUBMAP g)`,
  CHEAT_TAC);;

let submap_fupdate_flookup = prove
 (`(f |+ (x,y) SUBMAP g <=> FLOOKUP g x = SOME y /\ f \\ x SUBMAP g)`,
  CHEAT_TAC);;

let has_bools_def = new_definition
  `has_bools genv <=>
     FLOOKUP genv ((true_tag,SOME bool_id),0) = SOME (TypeStamp
       (implode "True") bool_type_num) /\
     FLOOKUP genv ((false_tag,SOME bool_id),0) = SOME (TypeStamp
       (implode "False") bool_type_num)`;;

let has_lists_def = new_definition
  `has_lists genv <=>
     FLOOKUP genv ((cons_tag,SOME list_id),2) = SOME (TypeStamp
       (implode "::") list_type_num) /\
     FLOOKUP genv ((nil_tag,SOME list_id),0) = SOME (TypeStamp
       (implode "[]") list_type_num)`;;

let has_exns_def = new_definition
  `has_exns genv <=>
     FLOOKUP genv ((div_tag,NONE),0) = SOME div_stamp /\
     FLOOKUP genv ((chr_tag,NONE),0) = SOME chr_stamp /\
     FLOOKUP genv ((subscript_tag,NONE),0) = SOME subscript_stamp /\
     FLOOKUP genv ((bind_tag,NONE),0) = SOME bind_stamp`;;

let genv_c_ok_def = new_definition
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

let genv_c_tys_ok_def = new_definition
  `genv_c_tys_ok genv_c genv_tys <=>
   (!cn ty_id arity.
     ((cn,SOME ty_id),arity) IN FDOM genv_c ==>
       (?ctors. FLOOKUP genv_tys ty_id = SOME ctors /\
       MEM (cn,arity) ctors))`;;

let source_to_flatProof_v_rel = cake_inductive
  `(!genv lit.
     source_to_flatProof_v_rel genv ((Litv lit):semanticPrimitives_v)
       ((Litv lit):flatSem_v)) /\
   (!genv cn cn' vs vs'.
     ALL2 (source_to_flatProof_v_rel genv) vs vs' /\
     FLOOKUP (global_env_c genv) (cn',LENGTH vs) = SOME cn ==>
     source_to_flatProof_v_rel genv (Conv (SOME cn) vs) (Conv (SOME
       cn') vs')) /\
   (!genv vs vs'.
     ALL2 (source_to_flatProof_v_rel genv) vs vs' ==>
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
           (source_to_flat_environment_v_fupd (K (bind_locals ts
             (CONS x (MAP FST (flatSem_environment_v env_v_local')))
             (source_to_flat_environment_v comp_map))) comp_map)
           e))) /\
   (
    // For expression level let recs
    !genv comp_map env env_v_local funs x env_v_local' t ts.
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
           (source_to_flat_environment_v_fupd (K (bind_locals ts
             (APPEND (MAP FST funs) (MAP FST (flatSem_environment_v
             env_v_local'))) (source_to_flat_environment_v comp_map)))
             comp_map) funs)
           x)) /\
   (
    // For top-level let recs
    !genv comp_map env funs flat_env x y e new_vars t1 t2.
     MAP FST new_vars = MAP FST (REVERSE funs) /\
     global_env_inv genv comp_map {} env /\ flatSem_environment_v
     flat_env = [] /\
     find_recfun x funs = SOME (y,e) /\
     (
      // A syntactic way of relating the recursive function environment, rather
      // * than saying that they build v_rel related environments, which looks to
      // * require step-indexing
      !x. x IN set_of_list (MAP FST funs) ==>
        (?n y e t1 t2 t3.
          ALOOKUP new_vars x = SOME (source_to_flat_Glob t1 n) /\
          n < LENGTH (global_env_v genv) /\
          find_recfun x funs = SOME (y,e) /\
          EL n (global_env_v genv) =
            SOME (Closure flat_env y
                   (compile_exp t2 (source_to_flat_environment_v_fupd
                     (K (nsBindList (CONS (y,source_to_flat_Local t3 y)
                     new_vars) (source_to_flat_environment_v comp_map)))
                     comp_map) e)))) ==>
     source_to_flatProof_v_rel genv
       (Recclosure env funs x)
       (Closure flat_env y
         (compile_exp t1
           (source_to_flat_environment_v_fupd (K (nsBindList (CONS
             (y,source_to_flat_Local t2 y) new_vars)
             (source_to_flat_environment_v comp_map))) comp_map)
           e))) /\
   (!genv loc b.
     source_to_flatProof_v_rel genv (Loc b loc) (Loc b (loc + 1))) /\
   (!genv vs vs'.
     ALL2 (source_to_flatProof_v_rel genv) vs vs' ==>
     source_to_flatProof_v_rel genv (Vectorv vs) (Vectorv vs')) /\
   (!genv.
     source_to_flatProof_env_rel genv nsEmpty []) /\
   (!genv x v env env' v'.
     source_to_flatProof_env_rel genv env env' /\
     source_to_flatProof_v_rel genv v v' ==>
     source_to_flatProof_env_rel genv (nsBind x v env) (CONS (x,v')
       env')) /\
   (!genv comp_map shadowers env.
     (!x v.
        ~(x IN IMAGE Short shadowers) /\
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

(* HOL4 source_to_flatProofScript.sml:336-343: a theorem that HOL4
   states as the value of an ML expression: v_rel_eqns *)

(* HOL4 source_to_flatProofScript.sml:345-351: a theorem that HOL4
   states as the value of an ML expression: v_rel_more_eqns *)

(* HOL4 source_to_flatProofScript.sml:353-354: a theorem that HOL4
   states as the value of an ML expression: v_rel_global_eqn *)

let env_rel_LIST_REL = prove
 (`!xs ys. env_rel genv (alist_to_ns xs) ys <=>
   ALL2 (\x y. FST x = FST y /\ source_to_flatProof_v_rel genv (SND
     x) (SND y)) xs ys`,
  CHEAT_TAC);;

(* [local] *)
let env_rel_dom = prove
 (`!genv env env'.
     env_rel genv env env' ==>
     (?l. env = alist_to_ns l /\ MAP FST l = MAP FST env')`,
  CHEAT_TAC);;

(* [local] *)
let env_rel_lookup = prove
 (`!genv env x v env'.
     ALOOKUP env x = SOME v /\
     env_rel genv (alist_to_ns env) env' ==>
     (?v'.
       source_to_flatProof_v_rel genv v v' /\
       ALOOKUP env' x = SOME v')`,
  CHEAT_TAC);;

(* env_rel_append[local] *)
let source_to_flatProof_env_rel_append = prove
 (`!genv env1 env2 env1' env2'.
     env_rel genv env1 env1' /\
     env_rel genv env2 env2' ==>
     env_rel genv (nsAppend env1 env2) (APPEND env1' env2')`,
  CHEAT_TAC);;

(* [local] *)
let env_rel_one = prove
 (`env_rel genv (nsBind a b nsEmpty) xs <=>
   (?v. xs = [(a,v)] /\ source_to_flatProof_v_rel genv b v)`,
  CHEAT_TAC);;

(* HOL4 source_to_flatProofScript.sml:434-437: a theorem that HOL4
   states as the value of an ML expression: env_rel_bind_one *)

(* env_rel_el[local] *)
let source_to_flatProof_env_rel_el = prove
 (`!genv env env_i1.
     env_rel genv (alist_to_ns env) env_i1 <=>
     LENGTH env = LENGTH env_i1 /\
     (!n. n < LENGTH env ==>
         (FST (EL n env) = FST (EL n env_i1)) /\
         source_to_flatProof_v_rel genv (SND (EL n env)) (SND (EL n
           env_i1)))`,
  CHEAT_TAC);;

let subglobals_def = new_definition
  `subglobals g1 g2 <=>
     LENGTH g1 <= LENGTH g2 /\
     (!n. n < LENGTH g1 /\ IS_SOME (EL n g1) ==> EL n g1 = EL n
       g2)`;;

(* [local] *)
let subglobals_refl = prove
 (`!g. subglobals g g`,
  CHEAT_TAC);;

(* [local] *)
let subglobals_trans = prove
 (`!g1 g2 g3. subglobals g1 g2 /\ subglobals g2 g3 ==> subglobals g1
  g3`,
  CHEAT_TAC);;

(* [local] *)
let subglobals_refl_append = prove
 (`!g1 g2 g3.
     subglobals (APPEND g1 g2) (APPEND g1 g3) = subglobals g2 g3 /\
     (LENGTH g2 = LENGTH g3 ==> subglobals (APPEND g2 g1) (APPEND
       g3 g1) = subglobals g2 g3)`,
  CHEAT_TAC);;

(* [local] *)
let v_rel_weakening = prove
 (`(!genv v v'.
     source_to_flatProof_v_rel genv v v' ==>
     (!genv'. global_env_c genv = global_env_c genv' /\
       global_env_tys genv = global_env_tys genv' /\
         subglobals (global_env_v genv) (global_env_v genv') ==>
           source_to_flatProof_v_rel genv' v v')) /\
    (!genv env env'.
     env_rel genv env env' ==>
     (!genv'. global_env_c genv = global_env_c genv' /\
       global_env_tys genv = global_env_tys genv' /\
         subglobals (global_env_v genv) (global_env_v genv') ==>
           env_rel genv' env env')) /\
    (!genv comp_map shadowers env.
     global_env_inv genv comp_map shadowers env ==>
     (!genv'. global_env_c genv = global_env_c genv' /\
       global_env_tys genv = global_env_tys genv' /\
         subglobals (global_env_v genv) (global_env_v genv') ==>
           global_env_inv genv' comp_map shadowers env))`,
  CHEAT_TAC);;

(* [local] *)
let v_rel_weakening2 = prove
 (`(!genv v v'.
    source_to_flatProof_v_rel genv v v' ==>
    (!gc'. global_env_c genv SUBMAP global_env_c genv' /\
      global_env_tys genv SUBMAP global_env_tys genv' /\ global_env_v
      genv = global_env_v genv' ==>
    source_to_flatProof_v_rel genv' v v')) /\
   (!genv env env'.
    env_rel genv env env' ==>
    (!gc'. global_env_c genv SUBMAP global_env_c genv' /\
      global_env_tys genv SUBMAP global_env_tys genv' /\ global_env_v
      genv = global_env_v genv' ==>
    env_rel genv' env env')) /\
   (!genv comp_map shadowers env.
    global_env_inv genv comp_map shadowers env ==>
    (!gc'. global_env_c genv SUBMAP global_env_c genv' /\
      global_env_tys genv SUBMAP global_env_tys genv' /\ global_env_v
      genv = global_env_v genv' ==>
    global_env_inv genv' comp_map shadowers env))`,
  CHEAT_TAC);;

(* [local] *)
let drestrict_lem = prove
 (`f1 SUBMAP f2 ==> FUNION (DRESTRICT f2 (COMPL (FDOM f1))) f1 = f2`,
  CHEAT_TAC);;

let v_rel_weak = prove
 (`!genv v v' genv'.
   source_to_flatProof_v_rel genv v v' /\ global_env_c
   genv SUBMAP global_env_c genv' /\ global_env_tys
   genv SUBMAP global_env_tys genv' /\
   subglobals (global_env_v genv) (global_env_v genv') ==>
   source_to_flatProof_v_rel genv' v v'`,
  CHEAT_TAC);;

let env_rel_weak = prove
 (`!genv env env' genv'.
   env_rel genv env env' /\ global_env_c
   genv SUBMAP global_env_c genv' /\ global_env_tys
   genv SUBMAP global_env_tys genv' /\
   subglobals (global_env_v genv) (global_env_v genv') ==>
   env_rel genv' env env'`,
  CHEAT_TAC);;

let global_env_inv_weak = prove
 (`!genv comp_map shadowers env genv'.
   global_env_inv genv comp_map shadowers env /\ global_env_c
   genv SUBMAP global_env_c genv' /\ global_env_tys
   genv SUBMAP global_env_tys genv' /\
   subglobals (global_env_v genv) (global_env_v genv') ==>
   global_env_inv genv' comp_map shadowers env`,
  CHEAT_TAC);;

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

(* [local] *)
let result_rel_eqns = prove
 (`(!genv v r.
     result_rel f genv (Rval v) r <=>
       (?v'. f genv v v' /\ r = Rval v')) /\
    (!genv v r.
     result_rel f genv (Rerr (Rraise v)) r <=>
       (?v'. source_to_flatProof_v_rel genv v v' /\ r = Rerr (Rraise
         v'))) /\
    (!genv v r a.
     result_rel f genv (Rerr (Rabort a)) r <=>
       r = Rerr (Rabort a))`,
  CHEAT_TAC);;

let sv_rel = cake_inductive
  `(!genv v v'.
     source_to_flatProof_v_rel genv v v' ==>
     source_to_flatProof_sv_rel genv (semanticPrimitives_Refv v)
       (semanticPrimitives_Refv v')) /\
   (!genv w.
     source_to_flatProof_sv_rel genv (semanticPrimitives_W8array w)
       (semanticPrimitives_W8array w)) /\
   (!genv vs vs'.
     ALL2 (source_to_flatProof_v_rel genv) vs vs' ==>
     source_to_flatProof_sv_rel genv (semanticPrimitives_Varray vs)
       (semanticPrimitives_Varray vs')) /\
   (!genv m v v'.
     source_to_flatProof_v_rel genv v v' ==>
     source_to_flatProof_sv_rel genv (semanticPrimitives_Thunk m
       v) (semanticPrimitives_Thunk m v'))`;;
hol4_overload "sv_rel" "source_to_flatProof_sv_rel";;

(* [local] *)
let sv_rel_weak = prove
 (`!genv sv sv' genv'.
    sv_rel genv sv sv' /\ global_env_c
    genv SUBMAP global_env_c genv' /\ global_env_tys
    genv SUBMAP global_env_tys genv' /\
    subglobals (global_env_v genv) (global_env_v genv') ==>
    sv_rel genv' sv sv'`,
  CHEAT_TAC);;

let s_rel = cake_inductive
  `(!genv s s'.
     ~(NULL (state_refs s')) /\
     ALL2 (sv_rel genv) (state_refs s) (TL (state_refs s')) /\
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

(* [local] *)
let env_all_rel_weak = prove
 (`!genv map' locals env env' genv'.
    env_all_rel genv map' env env' locals /\ global_env_c
    genv SUBMAP global_env_c genv' /\ global_env_tys
    genv SUBMAP global_env_tys genv' /\
    subglobals (global_env_v genv) (global_env_v genv') ==>
    env_all_rel genv' map' env env' locals`,
  CHEAT_TAC);;

let source_to_flatProof_match_result_rel_def = new_definition
  `source_to_flatProof_match_result_rel genv env' x3 x4 =
        match (x3,x4) with
          (Match env,Match env_i1) ->
        (?env''. env = APPEND env'' env' /\ env_rel genv (alist_to_ns
          env'') env_i1)
        | (No_match,No_match) -> T
        | (Match_type_error,_1) -> T
        | (_2,_3) -> F`;;
hol4_overload "match_result_rel"
  "source_to_flatProof_match_result_rel";;

let match_result_rel_imp = prove
 (`match_result_rel genv env m1 m2 ==>
   (m1 = Match_type_error \/
     (m1 = No_match /\ m2 = No_match) \/ (?env1 env2. m1 = Match
       env1 /\ m2 = Match env2))`,
  CHEAT_TAC);;

(* semantic functions respect relation *)

(* do_eq[local] *)
let source_to_flatProof_do_eq = prove
 (`!genv. genv_c_ok (global_env_c genv) ==>
    (!v1 v2 r v1_i1 v2_i1.
     do_eq v1 v2 = r /\
     source_to_flatProof_v_rel genv v1 v1_i1 /\
     source_to_flatProof_v_rel genv v2 v2_i1 ==>
     do_eq v1_i1 v2_i1 = r) /\
    (!vs1 vs2 r vs1_i1 vs2_i1.
     do_eq_list vs1 vs2 = r /\
     ALL2 (source_to_flatProof_v_rel genv) vs1 vs1_i1 /\
     ALL2 (source_to_flatProof_v_rel genv) vs2 vs2_i1 ==>
     do_eq_list vs1_i1 vs2_i1 = r)`,
  CHEAT_TAC);;

let genv_lookup_nil = prove
 (`genv_c_ok genv_c ==>
   (
   FLOOKUP genv_c cn = SOME (TypeStamp (implode "[]")
     list_type_num) <=> cn = ((nil_tag,SOME list_id),0))`,
  CHEAT_TAC);;

let genv_lookup_cons = prove
 (`genv_c_ok genv_c ==>
   (
   FLOOKUP genv_c cn = SOME (TypeStamp (implode "::")
     list_type_num) <=> cn = ((cons_tag,SOME list_id),2))`,
  CHEAT_TAC);;

(* v_to_char_list[local] *)
let source_to_flatProof_v_to_char_list = prove
 (`!genv. genv_c_ok (global_env_c genv) ==>
    (!v1 v2 vs1.
     source_to_flatProof_v_rel genv v1 v2 /\
     v_to_char_list v1 = SOME vs1 ==>
     v_to_char_list v2 = SOME vs1)`,
  CHEAT_TAC);;

(* v_to_list[local] *)
let source_to_flatProof_v_to_list = prove
 (`!genv. genv_c_ok (global_env_c genv) ==>
    (!v1 v2 vs1.
     source_to_flatProof_v_rel genv v1 v2 /\
     v_to_list v1 = SOME vs1 ==>
     (?vs2.
       v_to_list v2 = SOME vs2 /\
       ALL2 (source_to_flatProof_v_rel genv) vs1 vs2))`,
  CHEAT_TAC);;

(* vs_to_string[local] *)
let source_to_flatProof_vs_to_string = prove
 (`!v1 v2 s.
     ALL2 (source_to_flatProof_v_rel genv) v1 v2 ==>
     vs_to_string v1 = SOME s ==>
     vs_to_string v2 = SOME s`,
  CHEAT_TAC);;

(* [local] *)
let v_rel_lems = prove
 (`!genv. genv_c_ok (global_env_c genv) ==>
     (!b. source_to_flatProof_v_rel genv (Boolv b) (Boolv b)) /\
     source_to_flatProof_v_rel genv div_exn_v div_exn_v /\
     source_to_flatProof_v_rel genv chr_exn_v chr_exn_v /\
     source_to_flatProof_v_rel genv bind_exn_v bind_exn_v /\
     source_to_flatProof_v_rel genv sub_exn_v subscript_exn_v`,
  CHEAT_TAC);;

(* list_to_v_v_rel *)
let source_to_flatProof_list_to_v_v_rel = prove
 (`!xs ys.
     has_lists (global_env_c genv) /\ ALL2 (source_to_flatProof_v_rel
       genv) xs ys ==>
       source_to_flatProof_v_rel genv (list_to_v xs) (list_to_v ys)`,
  CHEAT_TAC);;

let LIST_REL_IMP_EL2 = prove
 (`// TODO: move
   !P xs ys. ALL2 P xs ys ==> (!i. i < LENGTH ys ==> P (EL i xs)
     (EL i ys))`,
  CHEAT_TAC);;

let LIST_REL_IMP_EL = prove
 (`// TODO: move
   !P xs ys. ALL2 P xs ys ==> (!i. i < LENGTH xs ==> P (EL i xs)
     (EL i ys))`,
  CHEAT_TAC);;

(* [local] *)
let NOT_NULL_EQ = prove
 (`(~(NULL xs)) = (?y ys. xs = CONS y ys)`,
  CHEAT_TAC);;

(* v_rel_check_type *)
let source_to_flatProof_v_rel_check_type = prove
 (`source_to_flatProof_v_rel genv v1 w1 /\ genv_c_ok (global_env_c
  genv) /\ check_type ty v1 ==> check_type ty w1`,
  CHEAT_TAC);;

(* [local] *)
let do_test_lemma = prove
 (`do_test test ty v1 v2 = Eq_val b /\
   genv_c_ok (global_env_c genv) /\
   source_to_flatProof_v_rel genv v1 w1 /\ source_to_flatProof_v_rel
     genv v2 w2 ==>
   do_test test ty w1 w2 = Eq_val b`,
  CHEAT_TAC);;

let check_type_IMP_v_rel = prove
 (`check_type ty v /\ genv_c_ok (global_env_c genv) ==>
  source_to_flatProof_v_rel genv v (v_to_flat v)`,
  CHEAT_TAC);;

let check_type_v_rel_flat_to_v = prove
 (`check_type ty v /\ source_to_flatProof_v_rel genv v y /\ genv_c_ok
  (global_env_c genv) ==> flat_to_v y = v`,
  CHEAT_TAC);;

let check_type_v_rel_MAP_flat_to_v = prove
 (`!v y.
     ALL (check_type ty) v /\ ALL2 (source_to_flatProof_v_rel genv) v
       y /\ genv_c_ok (global_env_c genv) ==>
     MAP flat_to_v y = v`,
  CHEAT_TAC);;

(* [local] *)
let do_arith_INL = prove
 (`ALL (check_type ty) vs /\ genv_c_ok (global_env_c genv) /\
   ALL2 (source_to_flatProof_v_rel genv) vs vs_i1 /\
   do_arith a ty vs = SOME (INL exn) ==>
   exn = div_exn_v /\
   ALL (check_type ty) (MAP flat_to_v vs_i1) /\
   (?e. do_arith a ty (MAP flat_to_v vs_i1) = SOME (INL e))`,
  CHEAT_TAC);;

(* [local] *)
let do_arith_INR = prove
 (`ALL (check_type ty) vs /\ genv_c_ok (global_env_c genv) /\
   ALL2 (source_to_flatProof_v_rel genv) vs vs_i1 /\
   do_arith a ty vs = SOME (INR r) ==>
   ALL (check_type ty) (MAP flat_to_v vs_i1) /\
   (?r'. do_arith a ty (MAP flat_to_v vs_i1) = SOME (INR r') /\
        source_to_flatProof_v_rel genv r (v_to_flat r'))`,
  CHEAT_TAC);;

(* [local] *)
let do_conversion_INL = prove
 (`check_type ty1 v /\ genv_c_ok (global_env_c genv) /\
   source_to_flatProof_v_rel genv v v_i1 /\
   do_conversion v ty1 ty2 = SOME (INL exn) ==>
   exn = chr_exn_v /\
   check_type ty1 (flat_to_v v_i1) /\
   (?e. do_conversion (flat_to_v v_i1) ty1 ty2 = SOME (INL e))`,
  CHEAT_TAC);;

(* [local] *)
let do_conversion_INR = prove
 (`check_type ty1 v /\ genv_c_ok (global_env_c genv) /\
   source_to_flatProof_v_rel genv v v_i1 /\
   do_conversion v ty1 ty2 = SOME (INR r) ==>
   check_type ty1 (flat_to_v v_i1) /\
   (?r'. do_conversion (flat_to_v v_i1) ty1 ty2 = SOME (INR r') /\
        source_to_flatProof_v_rel genv r (v_to_flat r'))`,
  CHEAT_TAC);;

(* HOL4 source_to_flatProofScript.sml:1061-1062: the ML values that
   the definitions below antiquote *)

(* do_app[local] *)
let source_to_flatProof_do_app = prove
 (`!genv s1 s2 op vs r ((s1_i1:('f_orac_st,'ffi)flatSem_state)) vs_i1.
     do_app s1 op vs = SOME (s2,r) /\
     ALL2 (sv_rel genv) (FST s1) (TL (flatSem_state_refs s1_i1)) /\
     ~(NULL (flatSem_state_refs s1_i1)) /\
     ALL2 (source_to_flatProof_v_rel genv) vs vs_i1 /\
     SND s1 = flatSem_state_ffi s1_i1 /\
     genv_c_ok (global_env_c genv) /\ ~(op = ast_AallocEmpty) /\ ~(op
       = ast_Env_id) ==>
      (?r_i1 s2_i1.
        ALL2 (sv_rel genv) (FST s2) (TL (state_refs s2_i1)) /\
        ~(NULL (state_refs s2_i1)) /\
        SND s2 = state_ffi s2_i1 /\ flatSem_state_globals
        s1_i1 = flatSem_state_globals s2_i1 /\
        TAKE 1 (flatSem_state_refs s1_i1) = TAKE 1 (state_refs s2_i1)
          /\
        result_rel source_to_flatProof_v_rel genv r r_i1 /\
        do_app s1_i1 (astOp_to_flatOp op) vs_i1 = SOME
          (s2_i1,r_i1))`,
  CHEAT_TAC);;

(* [local] *)
let find_recfun = prove
 (`!x funs e comp_map y t.
     find_recfun x funs = SOME (y,e) ==>
     find_recfun x (compile_funs t comp_map funs) =
       SOME (y,compile_exp (CONS x t)
         (source_to_flat_environment_v_fupd (K (nsBind y
         (source_to_flat_Local backend_common_None y)
         (source_to_flat_environment_v comp_map))) comp_map) e)`,
  CHEAT_TAC);;

(* [local] *)
let do_app_rec_help = prove
 (`!genv comp_map env_v_local env_v_local' env_v_top funs t.
     env_rel genv env_v_local (flatSem_environment_v env_v_local') /\
     global_env_inv genv comp_map (set_of_list (MAP FST
       (flatSem_environment_v env_v_local'))) env' /\
     LENGTH ts = LENGTH funs' + LENGTH (flatSem_environment_v
       env_v_local') ==>
      env_rel genv
        (alist_to_ns
           (MAP
              (\(f,n,e).
                 (f,
                  Recclosure
                    (sem_env_v_fupd (K (nsAppend env_v_local
                      (sem_env_v env'))) env')
                    funs' f)) funs))
        (MAP
           (\(fn,n,e).
              (fn,
               Recclosure env_v_local'
                 (compile_funs t
                    (source_to_flat_environment_v_fupd (K
                      (ITLIST (\(x,v) e. nsBind x v e)
                       (MAP2 (\t x. (x,source_to_flat_Local t x)) ts
                          (APPEND (MAP FST funs') (MAP FST
                            (flatSem_environment_v env_v_local'))))
                            (source_to_flat_environment_v comp_map)))
                            comp_map) funs')
                 fn))
           (compile_funs t
              (source_to_flat_environment_v_fupd (K
                (ITLIST (\(x,v) e. nsBind x v e)
                 (MAP2 (\t x. (x,source_to_flat_Local t x)) ts
                    (APPEND (MAP FST funs') (MAP FST
                      (flatSem_environment_v env_v_local'))))
                      (source_to_flat_environment_v comp_map)))
                      comp_map) funs))`,
  CHEAT_TAC);;

(* [local] *)
let global_env_inv_add_locals = prove
 (`!genv comp_map locals1 locals2 env.
     global_env_inv genv comp_map locals1 env ==>
     global_env_inv genv comp_map (locals2 UNION locals1) env`,
  CHEAT_TAC);;

(* [local] *)
let global_env_inv_extend2 = prove
 (`!genv comp_map env new_vars env' locals env_c.
     set_of_list (MAP (Short o FST) new_vars) = nsDom env' /\
     global_env_inv genv comp_map locals env /\
     global_env_inv genv (source_to_flat_environment_v_fupd (K
       (alist_to_ns new_vars)) comp_map) locals (mk_sem_env env' env_c)
       ==>
     global_env_inv genv (source_to_flat_environment_v_fupd (K
       (nsBindList new_vars (source_to_flat_environment_v comp_map)))
       comp_map) locals
         (sem_env_v_fupd (K (nsAppend env' (sem_env_v env))) env)`,
  CHEAT_TAC);;

(* [local] *)
let lookup_build_rec_env_lem = prove
 (`!x cl_env funs' funs.
     ALOOKUP (MAP (\(fn,n,e). (fn,Recclosure cl_env funs' fn)) funs)
       x = SOME v ==>
     v = semanticPrimitives_Recclosure cl_env funs' x`,
  CHEAT_TAC);;

(* [local] *)
let sem_env_eq_lemma = prove
 (`!(env:'a sem_env) x. (sem_env_v_fupd (K x) env) = mk_sem_env x
  (sem_env_c env)`,
  CHEAT_TAC);;

(* [local] *)
let do_opapp = prove
 (`!genv vs vs_i1 env e.
     semanticPrimitives_do_opapp vs = SOME (env,e) /\
     ALL2 (source_to_flatProof_v_rel genv) vs vs_i1 ==>
      (?comp_map env_i1 locals t1 ts.
        env_all_rel genv comp_map env env_i1 locals /\
        LENGTH ts = LENGTH locals /\
        flatSem_do_opapp vs_i1 = SOME (env_i1,compile_exp t1
          (source_to_flat_environment_v_fupd (K (bind_locals ts locals
          (source_to_flat_environment_v comp_map))) comp_map) e))`,
  CHEAT_TAC);;

(* [simp] *)
let pat_bindings_compile_pat = prove
 (`!comp_map (p:ast_pat). pat_bindings (compile_pat comp_map p) =
  pat_bindings p`,
  CHEAT_TAC);;

(* [local] *)
let eta2 = prove
 (`!f x. (\y. f x y) = f x`,
  CHEAT_TAC);;

(* [local] *)
let ctor_same_type_refl = prove
 (`ctor_same_type x x`,
  CHEAT_TAC);;

(* [local] *)
let ctor_same_type_SND = prove
 (`ctor_same_type (SOME x) (SOME y) = (SND x = SND y)`,
  CHEAT_TAC);;

let genv_c_ok_pmatch_stamps_ok = prove
 (`s_rel genv s t /\
   nsLookup comp_map_c nm = SOME (flat_cn,ty_gp) /\
   same_type src_stamp src_stamp' /\
   genv_c_ok (global_env_c genv) /\
   genv_c_tys_ok (global_env_c genv) (global_env_tys genv) /\
   FLOOKUP (global_env_c genv) ((flat_cn,OPTION_MAP FST ty_gp),l) =
     SOME src_stamp /\
   FLOOKUP (global_env_c genv) (flat_stamp',l') = SOME src_stamp' /\
   (!ty_id ctors. ty_gp = SOME (ty_id,ctors) ==>
     FLOOKUP (global_env_tys genv) ty_id = SOME ctors) ==>
   pmatch_stamps_ok (SOME (flat_cn,ty_gp)) (SOME flat_stamp') l l'`,
  CHEAT_TAC);;

(* [local] *)
let FST_PAIR_MAP_I = prove
 (`FST ((I ## f) x) = FST x`,
  CHEAT_TAC);;

let genv_c_ok_same_type_FST_eq_imp_same_ctor = prove
 (`genv_c_ok genv_c /\
   FLOOKUP genv_c (cn1,l1) = SOME stamp1 /\
   FLOOKUP genv_c (cn2,l2) = SOME stamp2 /\
   same_type stamp1 stamp2 /\
   FST cn1 = FST cn2 /\ l1 = l2 ==>
   same_ctor stamp1 stamp2`,
  CHEAT_TAC);;

(* pmatch[local] *)
let source_to_flatProof_pmatch = prove
 (`(!cenv s p v env r env' env'' env_i1
  (s_i1:('f_orac_st,'ffi)flatSem_state) v_i1 st'.
    semanticPrimitives_pmatch cenv s p v env = r /\
    s_rel genv st' s_i1 /\
    global_env_inv genv comp_map2 shadowers senv /\
    genv_c_ok (global_env_c genv) /\
    genv_c_tys_ok (global_env_c genv) (global_env_tys genv) /\
    cenv = sem_env_c senv /\ source_to_flat_environment_c
    comp_map2 = source_to_flat_environment_c comp_map /\
    env = APPEND env' env'' /\ flatSem_state_globals
    s_i1 = global_env_v genv /\
    s = state_refs st' /\
    source_to_flatProof_v_rel genv v v_i1 /\
    env_rel genv (alist_to_ns env') env_i1 ==>
    (?r_i1.
      flatSem_pmatch s_i1 (compile_pat comp_map p) v_i1 env_i1 = r_i1
        /\
      match_result_rel genv env'' r r_i1)) /\
   (!cenv s ps vs env r env' env'' env_i1
     (s_i1:('f_orac_st,'ffi)flatSem_state) vs_i1 st'.
    pmatch_list cenv s ps vs env = r /\
    global_env_inv genv comp_map2 shadowers senv /\
    genv_c_ok (global_env_c genv) /\
    genv_c_tys_ok (global_env_c genv) (global_env_tys genv) /\
    cenv = sem_env_c senv /\ source_to_flat_environment_c
    comp_map2 = source_to_flat_environment_c comp_map /\
    env = APPEND env' env'' /\ flatSem_state_globals
    s_i1 = global_env_v genv /\
    s_rel genv st' s_i1 /\
    s = state_refs st' /\
    ALL2 (source_to_flatProof_v_rel genv) vs vs_i1 /\
    env_rel genv (alist_to_ns env') env_i1 ==>
    (?r_i1.
      pmatch_list s_i1 (MAP (compile_pat comp_map) ps) vs_i1 env_i1 =
        r_i1 /\
      match_result_rel genv env'' r r_i1))`,
  CHEAT_TAC);;

(* compiler correctness *)

(* [local] *)
let opt_bind_lem = prove
 (`opt_bind NONE = (\x y. y)`,
  CHEAT_TAC);;

(* [local] *)
let env_updated_lem = prove
 (`flatSem_environment_v_fupd (\y. y)
     env = (env:'a flatSem_environment)`,
  CHEAT_TAC);;

(* [local] *)
let evaluate_foldr_let_err = prove
 (`!env s s' exps e x.
     flatSem_evaluate env s exps = (s',Rerr x) ==>
     evaluate env s [ITLIST (Let t NONE) exps e] = (s',Rerr x)`,
  CHEAT_TAC);;

let env_domain_eq_def = new_definition
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

(* [local] *)
let env_domain_eq_append = prove
 (`env_domain_eq env1 env1' /\
    env_domain_eq env2 env2' ==>
    env_domain_eq (extend_env env1 env2) (extend_dec_env env1'
      env2')`,
  CHEAT_TAC);;

(* [local] *)
let global_env_inv_append = prove
 (`!genv var_map1 var_map2 env1 env2.
     env_domain_eq var_map1 env1 /\
     global_env_inv genv var_map1 {} env1 /\
     global_env_inv genv var_map2 {} env2 ==>
     global_env_inv genv (extend_env var_map1 var_map2) {}
       (extend_dec_env env1 env2)`,
  CHEAT_TAC);;

(* HOL4 source_to_flatProofScript.sml:2022: ML code, not ported *)

let idx_prev_def = new_definition
  `idx_prev idx idx2 <=> next_indices_vidx
   idx <= next_indices_vidx idx2 /\ next_indices_tidx idx <=
     next_indices_tidx idx2 /\ next_indices_eidx idx <=
     next_indices_eidx idx2`;;

let idx_prev_refl = prove
 (`idx_prev idx idx`,
  CHEAT_TAC);;

let idx_prev_trans = prove
 (`idx_prev idx idx2 /\ idx_prev idx2 idx3 ==> idx_prev idx idx3`,
  CHEAT_TAC);;

let idx_types_INDUCT,idx_types_RECURSION = define_datatype
  "idx_types = Idx_Var | Idx_Type | Idx_Exn";;

let idx_types_FORALL = prove
 (`(!x. P x) = (P Idx_Var /\ P Idx_Type /\ P Idx_Exn)`,
  CHEAT_TAC);;

let ALL_DISJOINT_DEF = new_definition
  `ALL_DISJOINT xs <=>
   (!i j. i < LENGTH xs /\ j < LENGTH xs /\ ~(i = j) ==> EL i xs
     INTER EL j xs = {})`;;

let ALL_DISJOINT_CONS = prove
 (`(ALL_DISJOINT [x] = T) /\
   (ALL_DISJOINT (CONS x (CONS y zs)) = (DISJOINT x y /\
     ALL_DISJOINT (CONS (x UNION y) zs)))`,
  CHEAT_TAC);;

let idx_block_def = new_definition
  `idx_block start_idx end_idx =
   {(i,Idx_Var) | next_indices_vidx start_idx <= i /\ i <
     next_indices_vidx end_idx} UNION
   {(i,Idx_Type) | next_indices_tidx start_idx <= i /\ i <
     next_indices_tidx end_idx} UNION
   {(i,Idx_Exn) | next_indices_eidx start_idx <= i /\ i <
     next_indices_eidx end_idx}`;;

let idx_final_block_def = new_definition
  `idx_final_block start_idx =
   {(i,Idx_Var) | next_indices_vidx start_idx <= i} UNION
   {(i,Idx_Type) | next_indices_tidx start_idx <= i} UNION
   {(i,Idx_Exn) | next_indices_eidx start_idx <= i}`;;

let genv_allocated_idxs_def = new_definition
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
let env_gen_inv_def = new_definition
  `env_gen_inv (e:environment_generation_store) =
     (domain (environment_generation_store_envs e) SUBSET count
       (environment_generation_store_next e))`;;

let env_store_inv_def = new_definition
  `env_store_inv (e:environment_store) =
     (domain (environment_store_env_gens e) SUBSET count
       (environment_store_next e))`;;

let inc_compile_prog_env_submap = prove
 (`inc_compile_prog env_id c p = (c',p') /\
   env_store_inv (source_to_flat_config_envs c) ==>
   env_store_inv (envs c') /\
   subspt (environment_store_env_gens (source_to_flat_config_envs
     c)) (environment_store_env_gens (envs c'))`,
  CHEAT_TAC);;

(* The source oracle states can always be decoded according to the
   optional decode function provided. The state
   part of the oracle sequence should be what is produced by repeatedly
   applying compile_prog *)
let src_orac_step_invs_def = new_definition
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
let orac_rel_inner_def = new_definition
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

let orac_rel_def = new_definition
  `orac_rel interp g src_eval flat_eval <=> (match (interp,src_eval)
  with (_5,NONE) -> T | (SOME dec,SOME (EvalOracle s)) -> (
     ?s_compiler. eval_oracle_state_custom_do_eval
     s = do_eval_oracle s_compiler g /\
     orac_rel_inner dec s s_compiler g flat_eval) | _6 -> F)`;;

let orac_rel_SOME_eval = prove
 (`orac_rel interp g (SOME eval_state) flat_eval ==>
   (?dec orac_st.
   interp = SOME dec /\ eval_state = EvalOracle orac_st)`,
  CHEAT_TAC);;

let src_orac_next_cfg_inner_def = new_definition
  `src_orac_next_cfg_inner interp orac_0 = (match (interp,orac_0) with
  (SOME dec,(env_id,state_v,decs)) ->
       (match dec state_v with SOME (c,x) -> SOME c | _7 -> NONE)
         | _8 -> NONE)`;;

let src_orac_next_cfg_def = new_definition
  `src_orac_next_cfg interp eval_state = (match eval_state with SOME
  (EvalOracle s) -> src_orac_next_cfg_inner interp (oracle s 0) | _9
  -> NONE)`;;

(* every env stored in the eval state is related to a concrete env
   representation in the next oracle state *)
let src_orac_env_invs_def = new_definition
  `src_orac_env_invs interp genv eval_state = (match eval_state with
  NONE -> T | SOME (EvalOracle s) ->
     (?c. src_orac_next_cfg interp eval_state = SOME c /\
       env_store_inv (source_to_flat_config_envs c) /\ next
         (source_to_flat_config_envs
       c) = LENGTH (envs s) /\
       (!g_id id'. g_id < LENGTH (envs s) /\ id' < LENGTH (EL g_id
         (envs s)) ==>
         (?comp_map_gen comp_map.
         sptree_lookup g_id (environment_store_env_gens
           (source_to_flat_config_envs c)) = SOME comp_map_gen /\
         sptree_lookup id' comp_map_gen = SOME comp_map /\
         global_env_inv genv comp_map {} (EL id' (EL g_id (envs
           s)))))) | _10 -> F)`;;

let src_orac_gen_inv_def = new_definition
  `src_orac_gen_inv eval_state = (match eval_state with NONE -> T | SOME
  (EvalOracle s) -> generation
     s < LENGTH (envs s))`;;

let src_orac_invs_def = new_definition
  `src_orac_invs interp g genv eval_state <=>
   src_orac_step_invs interp g eval_state /\
   src_orac_env_invs interp genv eval_state /\
   src_orac_gen_inv eval_state`;;

let src_orac_invs_weak = prove
 (`src_orac_invs interp g genv src_eval /\ global_env_c
   genv SUBMAP global_env_c genv' /\ global_env_tys
   genv SUBMAP global_env_tys genv' /\
   subglobals (global_env_v genv) (global_env_v genv') ==>
   src_orac_invs interp g genv' src_eval`,
  CHEAT_TAC);;

(* the current generation of envs in the compiler state matches that
   generation in oracle state - this one is tricky, because it will stop
   being true for a while if some declaration are never executed because
   of an exception that is later handled *)
let env_gen_rel_def = new_definition
  `env_gen_rel gen eval_state = (match eval_state with NONE -> T | SOME
  (EvalOracle s) -> environment_generation_store_generation
         gen = generation s /\ generation
         s < LENGTH (envs s) /\ environment_generation_store_next
         gen = LENGTH (EL (generation s) (envs s)) | _11 -> F)`;;

(* the oracle state is in the future, where this generation
   has already been compiled and its environments saved *)
let env_gen_future_rel_def = new_definition
  `env_gen_future_rel interp gen eval_state =
     (match src_orac_next_cfg interp eval_state with SOME c ->
       (?gen_final.
         sptree_lookup (environment_generation_store_generation gen)
           (environment_store_env_gens (source_to_flat_config_envs c)) =
           SOME gen_final /\
         subspt (environment_generation_store_envs gen) gen_final)
           | NONE -> T)`;;

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
let idx_range_rel_def = new_definition
  `idx_range_rel interp genv s_n_ts s_n_en s_eval idxs <=>
     (?idx end_idx fin_idx other_blocks.
     idxs = (idx,end_idx,other_blocks) /\
     (match src_orac_next_cfg interp s_eval with NONE -> T | SOME c
       -> fin_idx = source_to_flat_config_next c) /\
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
let fin_idx_match_def = new_definition
  `fin_idx_match len end_idx next_cfg = (match next_cfg with NONE ->
  next_indices_vidx end_idx <= len | SOME c -> next_indices_vidx
  (source_to_flat_config_next c) = len)`;;

let eval_ref_inv_def = new_definition
  `eval_ref_inv first_global first_ref <=>
   first_global = [SOME (Loc T 0)] /\
   (?v. first_ref = [semanticPrimitives_Refv v])`;;

let source_to_flatProof_invariant_def = new_definition
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
let orac_config_envs_subspt_def = new_definition
  `orac_config_envs_subspt interp es1 es2 <=>
     OPTREL (\c c'. subspt (environment_store_env_gens
       (source_to_flat_config_envs c)) (environment_store_env_gens (envs
       c')))
     (src_orac_next_cfg interp es1)
     (src_orac_next_cfg interp es2)`;;

let orac_config_envs_subspt_trans = prove
 (`orac_config_envs_subspt interp es1 es2 /\
   orac_config_envs_subspt interp es2 es3 ==>
   orac_config_envs_subspt interp es1 es3`,
  CHEAT_TAC);;

let orac_config_envs_subspt_refl = prove
 (`orac_config_envs_subspt interp es1 es1`,
  CHEAT_TAC);;

(* this relation holds over any successful evaluate or evaluate_decs
   - the eval generation stack will be back to the same generation
*)
let eval_state_call_rel_def = new_definition
  `eval_state_call_rel es1 es2 <=>
     (match es1 with SOME (EvalOracle s1) -> (?s2. es2 = SOME
       (EvalOracle s2) /\ generation
         s2 = generation s1 /\
         LENGTH (envs s1) <= LENGTH (envs s2) /\
         (!i. i < generation s1 ==> EL i (envs s2) = EL i (envs
           s1))) | _12 -> T)`;;

let eval_state_call_rel_trans = prove
 (`eval_state_call_rel es1 es2 /\ eval_state_call_rel es2 es3 ==>
   eval_state_call_rel es1 es3`,
  CHEAT_TAC);;

let eval_state_call_rel_refl = prove
 (`eval_state_call_rel es1 es1`,
  CHEAT_TAC);;

let orac_forward_rel_def = new_definition
  `orac_forward_rel interp es1 es2 <=>
   orac_config_envs_subspt interp es1 es2 /\
   eval_state_call_rel es1 es2`;;

let orac_forward_rel_trans = prove
 (`orac_forward_rel interp es1 es2 /\ orac_forward_rel interp es2 es3
  ==>
   orac_forward_rel interp es1 es3`,
  CHEAT_TAC);;

(* [simp] *)
let orac_forward_rel_refl = prove
 (`orac_forward_rel interp es1 es1`,
  CHEAT_TAC);;

let can_pmatch_all_IMP_pmatch_rows = prove
 (`can_pmatch_all (sem_env_c env) (state_refs st) (MAP FST pes) v /\
   source_to_flatProof_invariant interp g gen genv idxs st s_i1 /\
   env_all_rel genv comp_map env env_i1 locals /\
   source_to_flatProof_v_rel genv v v' ==> ~(pmatch_rows
     (compile_pes t (source_to_flat_environment_v_fupd (K
       (bind_locals ts locals (source_to_flat_environment_v comp_map)))
       comp_map) pes)
     s_i1 v' = Match_type_error)`,
  CHEAT_TAC);;

(* HOL4 source_to_flatProofScript.sml:2424-2426: ML code, not ported *)

let invariant_globals = prove
 (`source_to_flatProof_invariant interp g gen genv idxs s s_i1 ==>
  flatSem_state_globals s_i1 = global_env_v genv`,
  CHEAT_TAC);;

let invariant_genv_c_ok = prove
 (`source_to_flatProof_invariant interp g gen genv idxs s s_i1 ==>
  genv_c_ok (global_env_c genv)`,
  CHEAT_TAC);;

let invariant_change_clock = prove
 (`source_to_flatProof_invariant interp g gen genv env st1 st2 ==>
   source_to_flatProof_invariant interp g gen genv env
     (state_clock_fupd (K k) st1) (state_clock_fupd (K k) st2)`,
  CHEAT_TAC);;

let invariant_dec_clock = prove
 (`source_to_flatProof_invariant interp g gen genv env st1 st2 ==>
  state_clock
   st1 = state_clock st2 /\
   source_to_flatProof_invariant interp g gen genv env (dec_clock
     st1) (dec_clock st2)`,
  CHEAT_TAC);;

let v_rel_Bool_eqn = prove
 (`genv_c_ok (global_env_c genv) ==> (source_to_flatProof_v_rel genv
  (Boolv b) v <=> (v = Boolv b))`,
  CHEAT_TAC);;

(* evaluate_Bool *)
let source_to_flatProof_evaluate_Bool = prove
 (`s_rel genv s s' /\ genv_c_ok (global_env_c genv) ==>
   evaluate env s' [flatLang_Bool t b] = (s',Rval [Boolv b])`,
  CHEAT_TAC);;

(* Boolv_11 *)
let source_to_flatProof_Boolv_11 = prove
 (`(Boolv b = Boolv b') = (b = b')`,
  CHEAT_TAC);;

(* [local] *)
let opt_case_bool_eq = prove
 (`option_CASE opt nc scc <=> (opt = NONE /\ nc) \/ (?x. opt = SOME x
  /\ scc x)`,
  CHEAT_TAC);;

let bind_locals_fold_nsBind = prove
 (`nsBind nm (source_to_flat_Local t nm:var_name) (bind_locals ts locals
  v_map) =
   bind_locals (CONS t ts) (CONS nm locals) v_map`,
  CHEAT_TAC);;

let compile_decs_idx_prev = prove
 (`!t n next' env envs' ds n' next' env' envs' ds_i1.
     source_to_flat_compile_decs t n next' env envs' ds =
       (n',next',env',envs',ds_i1) ==>
     idx_prev next' next'`,
  CHEAT_TAC);;

let inc_compile_prog_idx_prev = prove
 (`inc_compile_prog env_id c0 decs = (c1,fdecs) ==>
   idx_prev (next c0) (next c1)`,
  CHEAT_TAC);;

let compile_decs_generation = prove
 (`!t n next' env envs' ds n' next' env' envs' ds_i1.
     source_to_flat_compile_decs t n next' env envs' ds =
       (n',next',env',envs',ds_i1) ==> generation
     envs' = generation envs'`,
  CHEAT_TAC);;

let compile_decs_env_gen_inv = prove
 (`!t n next' env envs' ds n' next' env' envs' ds_i1.
     source_to_flat_compile_decs t n next' env envs' ds =
       (n',next',env',envs',ds_i1) /\
     env_gen_inv envs' ==>
     env_gen_inv envs' /\
     subspt (envs envs') (envs envs')`,
  CHEAT_TAC);;

(* HOL4 source_to_flatProofScript.sml:2556-2559: a theorem that HOL4
   states as the value of an ML expression: v_rel_eqns_non_global *)

let ALL_DISJOINT_SUBSETS = prove
 (`!xs ys. ALL_DISJOINT xs /\ ALL2 (\x y. y SUBSET x) xs ys ==>
   ALL_DISJOINT ys`,
  CHEAT_TAC);;

let ALL_DISJOINT_MOVE = prove
 (`!i j mv_set xs ys.
   ALL_DISJOINT xs /\
   ys = LUPDATE (EL i xs DIFF mv_set) i (LUPDATE (EL j xs UNION
     mv_set) j xs) /\
   mv_set SUBSET EL i xs /\
   i < LENGTH xs /\
   j < LENGTH xs ==>
   ALL_DISJOINT ys`,
  CHEAT_TAC);;

let idx_range_shrink = prove
 (`idx_range_rel i genv nts nes eval_config (l_idx,r_idx,etc) /\
   idx_prev l_idx l_idx' /\ idx_prev l_idx' r_idx ==>
   idx_range_rel i genv nts nes eval_config (l_idx',r_idx,etc)`,
  CHEAT_TAC);;

let invariant_idx_range_shrink = prove
 (`source_to_flatProof_invariant interp g gen genv (l_idx,r_idx,etc) st
  st' /\
   idx_prev l_idx l_idx' /\ idx_prev l_idx' r_idx ==>
   source_to_flatProof_invariant interp g gen genv
     (l_idx',r_idx,etc) st st'`,
  CHEAT_TAC);;

let invariant_idx_range_shrink_gen = prove
 (`source_to_flatProof_invariant interp g gen genv (l_idx,r_idx,etc) st
  st' /\
   idx_prev l_idx l_idx' /\ idx_prev l_idx' r_idx /\
   (env_gen_inv gen ==> env_gen_inv gen') ==>
   source_to_flatProof_invariant interp g gen' genv
     (l_idx',r_idx,etc) st st'`,
  CHEAT_TAC);;

let pmatch_invariant = prove
 (`source_to_flatProof_invariant interp g gen genv idxs st st' /\
   env_all_rel genv comp_map2 env env' locals /\
     source_to_flat_environment_c
   comp_map2 = source_to_flat_environment_c comp_map /\
   source_to_flatProof_v_rel genv v v' ==>
   match_result_rel genv [] (pmatch (sem_env_c env) (state_refs st) p
     v [])
     (pmatch st' (compile_pat comp_map p) v' [])`,
  CHEAT_TAC);;

(* [local] *)
let evaluate_make_varls = prove
 (`!n t idx vars' g g' s env vals len.
     flatSem_state_globals
     s = APPEND (APPEND g (REPLICATE len NONE)) g' /\
     LENGTH g = idx /\
     LENGTH vals = LENGTH vars' /\
     len = LENGTH vars' /\
     (!n. n < LENGTH vals ==> ALOOKUP (flatSem_environment_v env) (EL
       n vars') = SOME (EL n vals)) ==>
     flatSem_evaluate env s [make_varls n t idx vars'] =
     (flatSem_state_globals_fupd (K (APPEND (APPEND g (MAP SOME
       vals)) g')) s,Rval [flatSem_Conv NONE []])`,
  CHEAT_TAC);;

let EL_APPEND_IF = prove
 (`EL i (APPEND xs ys) = (if i < LENGTH xs then EL i xs else EL (i -
  LENGTH xs) ys)`,
  CHEAT_TAC);;

let ALL_DISJOINT_elem = prove
 (`!x i. ALL_DISJOINT xs /\
   i < LENGTH xs /\
   x IN EL i xs ==>
   ALL I (MAPi (\j y. j = i \/ ~(x IN y)) xs)`,
  CHEAT_TAC);;

let subglobals_NONE = prove
 (`subglobals (REPLICATE n NONE) g <=> n <= LENGTH g`,
  CHEAT_TAC);;

(* [local] *)
let EL_add_SOME_SOME = prove
 (`~(EL i (APPEND (APPEND pre (MAP SOME xs)) post) = NONE) <=>
     (~(EL i (APPEND (APPEND pre (REPLICATE (LENGTH xs) NONE)) post)
       = NONE) \/
       (LENGTH pre <= i /\ i < LENGTH pre + LENGTH xs))`,
  CHEAT_TAC);;

(* [local] *)
let ALOOKUP_alloc_defs_EL = prove
 (`!funs l n m.
     ALL_DISTINCT (MAP (\(x,y,z). x) funs) /\
     n < LENGTH funs ==>
     (?tt.
     ALOOKUP (alloc_defs m l (MAP FST (REVERSE funs))) (EL n (MAP FST
       funs)) =
       SOME (source_to_flat_Glob tt ((l + LENGTH funs) - (n + 1))))`,
  CHEAT_TAC);;

(* [local] *)
let ALOOKUP_alloc_defs = prove
 (`!env x v l tt.
     ALOOKUP (REVERSE env) x = SOME v ==>
     (?n t.
       ALOOKUP (alloc_defs tt l (MAP FST (REVERSE env))) x = SOME
         (source_to_flat_Glob t (l + n)) /\
       n < LENGTH (MAP FST env) /\
       EL n (REVERSE (MAP SOME (MAP SND env))) = SOME v)`,
  CHEAT_TAC);;

(* [local] *)
let global_env_inv_extend = prove
 (`!pat_env genv pat_env' tt g1 g2.
     env_rel genv (alist_to_ns pat_env) pat_env' /\ global_env_v
     genv = APPEND (APPEND g1 (MAP SOME (REVERSE (MAP SND
       pat_env')))) g2 /\
     ALL_DISTINCT (MAP FST pat_env) ==>
     global_env_inv genv
       (mk_source_to_flat_environment nsEmpty (alist_to_ns
         (alloc_defs tt (LENGTH g1) (REVERSE (MAP FST pat_env')))))
       {}
       (mk_sem_env (alist_to_ns pat_env) nsEmpty)`,
  CHEAT_TAC);;

let LIST_REL_sv_rel_weak = prove
 (`ALL2 (sv_rel genv) vs vs' /\
   subglobals (global_env_v genv) (global_env_v genv') /\
     global_env_c
   genv SUBMAP global_env_c genv' /\ global_env_tys
   genv SUBMAP global_env_tys genv' ==>
   ALL2 (sv_rel genv') vs vs'`,
  CHEAT_TAC);;

let idx_range_rel_v_REPLICATE_NONE = prove
 (`idx_range_rel interp genv nts nes eval_state (idx,end_idx,others) /\
   fin_idx_match (LENGTH (global_env_v genv)) end_idx
         (src_orac_next_cfg interp eval_state) /\
   n + next_indices_vidx idx <= next_indices_vidx end_idx ==>
   (?pre post. global_env_v genv = APPEND (APPEND pre (REPLICATE n
     NONE)) post /\
     LENGTH pre = next_indices_vidx idx)`,
  CHEAT_TAC);;

let invariant_make_varls = prove
 (`source_to_flatProof_invariant interp g gen genv (idx,end_idx,others)
  st st' /\ next_indices_vidx
   idx = vidx /\ next_indices_vidx
   idx + LENGTH vars <= next_indices_vidx end_idx /\
   vars = REVERSE (MAP FST (flatSem_environment_v env)) /\
   ALL_DISTINCT (MAP FST (flatSem_environment_v env)) ==>
   (?genv' st''.
   evaluate env st' [make_varls n t vidx vars] = (st'',Rval [Unitv])
     /\
   source_to_flatProof_invariant interp g gen genv'
     (next_indices_vidx_fupd (K (next_indices_vidx idx + LENGTH vars))
     idx,end_idx,others)
     st st'' /\ global_env_c
   genv' = global_env_c genv /\ global_env_tys
   genv' = global_env_tys genv /\
   subglobals (global_env_v genv) (global_env_v genv') /\
   (!env1 tt. env_rel genv' (alist_to_ns env1) (flatSem_environment_v
     env) ==>
     global_env_inv genv'
       (mk_source_to_flat_environment nsEmpty (alist_to_ns
         (alloc_defs tt vidx (REVERSE (MAP FST (flatSem_environment_v
         env))))))
       {}
       (mk_sem_env (alist_to_ns env1) nsEmpty)))`,
  CHEAT_TAC);;

let compile_funs_dom2 = prove
 (`MAP FST (compile_funs t env funs) = MAP FST funs`,
  CHEAT_TAC);;

let genv_c_ok_extend = prove
 (`genv_c_ok c /\
   (!cn arity stamp. FLOOKUP c_ext (cn,arity) = SOME stamp ==>
     (same_type (ExnStamp 0) stamp <=> SND cn = NONE) /\
     (!cn' arity' stamp'. FLOOKUP c_ext (cn',arity') = SOME stamp'
       ==>
       (same_type stamp stamp' <=> ctor_same_type (SOME cn) (SOME
         cn')) /\
       (stamp = stamp' ==> (cn = cn' /\ arity = arity'))) /\
     (!cn' arity' stamp'. FLOOKUP c (cn',arity') = SOME stamp' ==>
       ~(stamp = stamp') /\
       (~(SND cn = NONE) ==> ~(SND cn = SND cn')) /\
       (!s s' n. stamp = TypeStamp s n ==> ~(stamp' = TypeStamp s'
         n)))) ==>
   genv_c_ok (FUNION c c_ext)`,
  CHEAT_TAC);;

let genv_c_tys_ok_extend = prove
 (`genv_c_tys_ok c tys /\
   genv_c_tys_ok c_ext tys_ext /\
   DISJOINT (FDOM tys) (FDOM tys_ext) ==>
   genv_c_tys_ok (FUNION c c_ext) (FUNION tys tys_ext)`,
  CHEAT_TAC);;

(* maybe_all_list_SOME *)
let source_to_flatProof_maybe_all_list_SOME = prove
 (`!xs ys. maybe_all_list xs = SOME ys ==> xs = MAP SOME ys`,
  CHEAT_TAC);;

let some_f_inj_eq = prove
 (`INJ f UNIV UNIV /\ y = f x ==>
   (some (\x. y = f x)) = SOME x`,
  CHEAT_TAC);;

let v_to_word8_list_rel = prove
 (`v_to_word8_list bytes_v = SOME bytes /\
   source_to_flatProof_v_rel genv bytes_v v' /\
   genv_c_ok (global_env_c genv) ==>
   flatSem_v_to_bytes v' = SOME bytes`,
  CHEAT_TAC);;

let v_to_word64_list_rel = prove
 (`v_to_word64_list words_v = SOME words /\
   source_to_flatProof_v_rel genv words_v v' /\
   genv_c_ok (global_env_c genv) ==>
   flatSem_v_to_words v' = SOME words`,
  CHEAT_TAC);;

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let keep_glob_alloc = prove
 (cake_as_vars (fun () ->
    `keep calc (glob_alloc next st)`),
  CHEAT_TAC);;

let inc_compile_prog_nonempty = prove
 (`inc_compile_prog env_id st decs = (st',fdecs) ==> ~(fdecs = [])`,
  CHEAT_TAC);;

let src_orac_env_invs_lookup_env = prove
 (`lookup_env es env_id = SOME env /\
   src_orac_env_invs interp genv (SOME (EvalOracle es)) /\ oracle
   es 0 = (env_id,st_v,decs) ==>
   (?c x gen comp_map.
   (THE interp) st_v = SOME (c,x) /\
   sptree_lookup (FST env_id) (environment_store_env_gens
     (source_to_flat_config_envs c)) = SOME gen /\
   sptree_lookup (SND env_id) gen = SOME comp_map /\
   global_env_inv genv comp_map {} env)`,
  CHEAT_TAC);;

(* FST_SND_EQ_CASE[local] *)
let source_to_flatProof_FST_SND_EQ_CASE = prove
 (`FST = (\(a,b). a) /\ SND = (\(a,b). b)`,
  CHEAT_TAC);;

(* [local] *)
let step_1 = prove
 (`src_orac_step_invs interp g (SOME (EvalOracle es)) ==>
   (?i_f env_id0 st_v0 decs0 fdecs0 c0 x0 env_id1 st_v1 decs1 c1 x1.
   interp = SOME i_f /\ oracle
   es 0 = (env_id0,st_v0,decs0) /\ oracle
   es 1 = (env_id1,st_v1,decs1) /\
   i_f st_v0 = SOME (c0,x0) /\
   i_f st_v1 = SOME (c1,x1) /\
   inc_compile_prog env_id0 c0 (g decs0) = (c1,fdecs0) /\
   src_orac_next_cfg (SOME i_f) (SOME (EvalOracle es)) = SOME c0)`,
  CHEAT_TAC);;

let subglobals_add_NONE = prove
 (`subglobals gs (APPEND gs (REPLICATE n NONE))`,
  CHEAT_TAC);;

let do_eval = prove
 (`!vs'.
   do_eval vs (semanticPrimitives_state_eval_state s) = SOME
     (env,decs,eval_state) /\
   source_to_flatProof_invariant interp g gen genv idxs s t /\
   ALL2 (source_to_flatProof_v_rel genv) vs vs' ==>
   (?genv' env_id c decs' eval_config' c' idx end_idx fin_idx other.
   idxs = (idx,end_idx,other) /\
   do_eval (DROP 4 vs') (flatSem_state_eval_config t) = SOME
     (decs',eval_config',Unitv) /\
   LENGTH vs' = 6 /\
   inc_compile_prog env_id c decs = (c',decs') /\ ~(decs' = []) /\
   source_to_flatProof_invariant interp g
     (mk_environment_generation_store 0 (next
     (source_to_flat_config_envs c)) LN) genv'
     (source_to_flat_config_next c,next c',idx_block idx end_idx
       UNION other)
     (semanticPrimitives_state_eval_state_fupd (K eval_state) s)
       (flatSem_state_globals_fupd (K (APPEND (flatSem_state_globals t)
       (REPLICATE (next_indices_vidx (next c') - next_indices_vidx
       (source_to_flat_config_next c)) NONE)))
       (flatSem_state_eval_config_fupd (K eval_config') t)) /\
   env_gen_rel (mk_environment_generation_store 0 (next
     (source_to_flat_config_envs c)) LN) eval_state /\
   (let (_13,_14,_15,gen,_16) = source_to_flat_compile_decs [] 1
     (source_to_flat_config_next c)
     (lookup_env_id env_id (source_to_flat_config_envs c))
     (mk_environment_generation_store 0 (next
       (source_to_flat_config_envs c)) LN) decs in
     env_gen_future_rel interp gen eval_state) /\
   global_env_inv genv' (lookup_env_id env_id
     (source_to_flat_config_envs c)) {} env /\
   src_orac_next_cfg interp eval_state = SOME c' /\
   idx_prev end_idx (next c') /\ global_env_c
   genv SUBMAP global_env_c genv' /\ global_env_tys
   genv SUBMAP global_env_tys genv' /\
   subglobals (global_env_v genv) (global_env_v genv') /\
   orac_config_envs_subspt interp
     (semanticPrimitives_state_eval_state s) eval_state /\
   (match semanticPrimitives_state_eval_state s with SOME (EvalOracle
     s) ->
     (?s'. eval_state = SOME (EvalOracle s') /\ envs
     s' = envs (add_env_generation s) /\ generation
     s' = generation (add_env_generation s)) | _17 -> F))`,
  CHEAT_TAC);;

let invariant_end_eval = prove
 (`source_to_flatProof_invariant interp g gen' genv
  (x,end_idx1,idx_block idx end_idx UNION other) st st' /\
   source_to_flatProof_invariant interp g gen prev_genv
     (idx,end_idx,other) prev_st prev_st' /\
   orac_forward_rel interp begin_eval_state
     (semanticPrimitives_state_eval_state st) /\
   idx_prev end_idx end_idx1 /\
   orac_config_envs_subspt interp
     (semanticPrimitives_state_eval_state prev_st) begin_eval_state /\
   (match semanticPrimitives_state_eval_state prev_st with SOME
     (EvalOracle s) ->
     (?s'. begin_eval_state = SOME (EvalOracle s') /\ envs
     s' = envs (add_env_generation s) /\ generation
     s' = generation (add_env_generation s)) | _18 -> F) ==>
   source_to_flatProof_invariant interp g gen genv
     (idx,end_idx,other) (semanticPrimitives_state_eval_state_fupd (K
     (reset_env_generation (semanticPrimitives_state_eval_state prev_st)
     (semanticPrimitives_state_eval_state st))) st)
     st' /\
   orac_forward_rel interp (semanticPrimitives_state_eval_state
     prev_st)
     (reset_env_generation (semanticPrimitives_state_eval_state
       prev_st) (semanticPrimitives_state_eval_state st)) /\
   (env_gen_rel gen (semanticPrimitives_state_eval_state prev_st) ==>
     env_gen_rel gen (reset_env_generation
       (semanticPrimitives_state_eval_state prev_st)
       (semanticPrimitives_state_eval_state st)))`,
  CHEAT_TAC);;

let alloc_tags1_imp = prove
 (`!ctors ns spt tag_list.
   alloc_tags1 ctors = (ns,spt,tag_list) /\
   ALL_DISTINCT (MAP FST ctors) ==>
   (?cn_tags.
   ns = alist_to_ns (MAP (\(cn,tag,arity). (cn,tag)) cn_tags) /\
   set_of_list (MAP SND cn_tags) = {(tag,arity) |
     ?max'. sptree_lookup arity spt = SOME max' /\ tag < max'} /\
   tag_list = MAP SND cn_tags /\
   ALL_DISTINCT tag_list /\
   ALL2 (\(cn,ts) (cn',_19,arity). cn = cn' /\ arity = LENGTH ts)
     ctors cn_tags /\
   MAP FST ctors = MAP FST cn_tags)`,
  CHEAT_TAC);;

(* FIXME also in flat_pattern *)
(* ALOOKUP_MAP_3 *)
let source_to_flatProof_ALOOKUP_MAP_3 = prove
 (`(!x. MEM x xs ==> FST (f x) = FST x) ==>
   ALOOKUP (MAP f xs) x = OPTION_MAP (\y. SND (f (x,y))) (ALOOKUP
     xs x)`,
  CHEAT_TAC);;

let alloc_tags_invariant = prove
 (`alloc_tags (next_indices_tidx idx) (ctors:(mlstring#ast_t list) list)
  = (ns,cids) /\
   source_to_flatProof_invariant interp g gen genv (idx,end_idx,os)
     st st' /\
   global_env_inv genv comp_map {} env /\
   ALL_DISTINCT (MAP FST ctors) /\ next_indices_tidx
   idx + 1 <= next_indices_tidx end_idx ==>
   (?genv'. global_env_c
   genv SUBMAP global_env_c genv' /\ global_env_tys
   genv SUBMAP global_env_tys genv' /\ global_env_v
   genv' = global_env_v genv /\
   source_to_flatProof_invariant interp g gen genv'
     (next_indices_tidx_fupd (K (next_indices_tidx idx + 1))
     idx,end_idx,os)
     (semanticPrimitives_state_next_type_stamp_fupd (K
       (semanticPrimitives_state_next_type_stamp st + 1)) st) st' /\
   (let build_env = mk_sem_env nsEmpty (alist_to_ns
         (REVERSE (build_constrs
           (semanticPrimitives_state_next_type_stamp st) ctors))) in
    global_env_inv genv' (mk_source_to_flat_environment ns nsEmpty)
      {} build_env /\
    env_domain_eq (mk_source_to_flat_environment ns nsEmpty)
      build_env))`,
  CHEAT_TAC);;

(* [local] *)
let nsAppend_foldl' = prove
 (`!l ns ns'.
    nsAppend (FOLDL (\ns (l,cids). nsAppend l ns) ns' l) ns =
    FOLDL (\ns (l,cids). nsAppend l ns) (nsAppend ns' ns) l`,
  CHEAT_TAC);;

(* [local] *)
let nsAppend_foldl = prove
 (`!l ns.
    FOLDL (\ns (l,cids). nsAppend l ns) ns l =
    nsAppend (FOLDL (\ns (l,cids). nsAppend l ns) nsEmpty l) ns`,
  CHEAT_TAC);;

(* [local] *)
let build_tdefs_no_mod = prove
 (`!idx tdefs. nsDomMod (build_tdefs idx tdefs) = {[]}`,
  CHEAT_TAC);;

(* HOL4 source_to_flatProofScript.sml:3704-3706: the ML values that
   the definitions below antiquote *)

(* HOL4 source_to_flatProofScript.sml:3708-3710: the ML values that
   the definitions below antiquote *)

let nsLookup_nsBind_If = prove
 (`nsLookup (nsBind n v e) nm = (if nm = Short n then SOME v else
  nsLookup e nm)`,
  CHEAT_TAC);;

let invariant_IMP_s_rel = prove
 (`source_to_flatProof_invariant interp g gen genv idx st st' ==>
  s_rel genv st st'`,
  CHEAT_TAC);;

let source_to_flatProof_abort_def = new_definition
  `source_to_flatProof_abort r <=> (match r with Rerr (Rabort a) -> T
  | _20 -> F)`;;
hol4_overload "abort" "source_to_flatProof_abort";;

(* [local] *)
let not_abort_IMP_cases = prove
 (`(~(abort r) ==> P) ==>
   ((?a. r = Rerr (Rabort a)) \/ (~(abort r) /\ P))`,
  CHEAT_TAC);;

(* abort_simps[simp] *)
let source_to_flatProof_abort_simps = prove
 (`abort (Rerr (Rabort a)) = T /\
   abort (Rerr (Rraise e)) = F /\
   abort (Rval v) = F`,
  CHEAT_TAC);;

(* compile_correct *)
let source_to_flatProof_compile_correct = prove
 (`(!((s:'ffi semanticPrimitives_state)) env es s' r genv comp_map
  env_i1 (s_i1:('f_orac_st,'ffi)flatSem_state) es_i1 locals t ts gen
  idxs.
     evaluate s env es = (s',r) /\
     source_to_flatProof_invariant interp g gen genv idxs s s_i1 /\
     env_all_rel genv comp_map env env_i1 locals /\
     LENGTH ts = LENGTH locals /\
     env_gen_rel gen (semanticPrimitives_state_eval_state s) /\ ~(r =
       Rerr (Rabort Rtype_error)) /\
     es_i1 = compile_exps t (source_to_flat_environment_v_fupd (K
       (bind_locals ts locals (source_to_flat_environment_v comp_map)))
       comp_map) es ==>
     (?s'_i1 r_i1 genv'.
     flatSem_evaluate env_i1 s_i1 es_i1 = (s'_i1,r_i1) /\
     result_rel (ALL2 o source_to_flatProof_v_rel) genv' r r_i1 /\
     s_rel genv' s' s'_i1 /\
     (~(abort r) ==>
       source_to_flatProof_invariant interp g gen genv' idxs s' s'_i1
         /\
       env_gen_rel gen (semanticPrimitives_state_eval_state s') /\
       orac_forward_rel interp (semanticPrimitives_state_eval_state
         s) (semanticPrimitives_state_eval_state s') /\ global_env_c
       genv SUBMAP global_env_c genv' /\ global_env_tys
       genv SUBMAP global_env_tys genv' /\
       subglobals (global_env_v genv) (global_env_v genv')))) /\
   (!((s:'ffi semanticPrimitives_state)) env v pes err_v genv
     comp_map s' r env_i1 (s_i1:('f_orac_st,'ffi)flatSem_state) v_i1
     pes_i1
          err_v_i1 locals t ts gen idxs.
     evaluate_evaluate_match s env v pes err_v = (s',r) /\
     source_to_flatProof_invariant interp g gen genv idxs s s_i1 /\
     env_all_rel genv comp_map env env_i1 locals /\
     source_to_flatProof_v_rel genv v v_i1 /\
     LENGTH ts = LENGTH locals /\
     env_gen_rel gen (semanticPrimitives_state_eval_state s) /\ ~(r =
       Rerr (Rabort Rtype_error)) /\
     pes_i1 = compile_pes t (source_to_flat_environment_v_fupd (K
       (bind_locals ts locals (source_to_flat_environment_v comp_map)))
       comp_map) pes /\ ~(pmatch_rows pes_i1 s_i1 v_i1 =
       Match_type_error) /\
     source_to_flatProof_v_rel genv err_v err_v_i1 ==>
     (?s'_i1 r_i1 genv'.
     flatProps_evaluate_match env_i1 s_i1 v_i1 pes_i1 err_v_i1 =
       (s'_i1,r_i1) /\
     result_rel (ALL2 o source_to_flatProof_v_rel) genv' r r_i1 /\
     s_rel genv' s' s'_i1 /\
     (~(abort r) ==>
       source_to_flatProof_invariant interp g gen genv' idxs s' s'_i1
         /\
       env_gen_rel gen (semanticPrimitives_state_eval_state s') /\
       orac_forward_rel interp (semanticPrimitives_state_eval_state
         s) (semanticPrimitives_state_eval_state s') /\ global_env_c
       genv SUBMAP global_env_c genv' /\ global_env_tys
       genv SUBMAP global_env_tys genv' /\
       subglobals (global_env_v genv) (global_env_v genv')))) /\
   (!((s:'ffi semanticPrimitives_state)) env ds s' r path' t idx
     end_idx os comp_map (s_i1:('f_orac_st,'ffi)flatSem_state) idx'
         comp_map' ds_i1 t' genv gen gen'.
     evaluate_evaluate_decs s env ds = (s',r) /\
     source_to_flatProof_invariant interp g gen genv (idx,end_idx,os)
       s s_i1 /\
     source_to_flat_compile_decs path' t idx comp_map gen ds =
         (t',idx',comp_map',gen',ds_i1) /\
     global_env_inv genv comp_map {} env /\ ~(r = Rerr (Rabort
       Rtype_error)) /\
     env_gen_rel gen (semanticPrimitives_state_eval_state s) /\
     env_gen_future_rel interp gen'
       (semanticPrimitives_state_eval_state s) /\
     idx_prev idx' end_idx ==>
     (?((s1_i1:('f_orac_st,'ffi)flatSem_state)) genv' r_i1.
     flatSem_evaluate_decs s_i1 ds_i1 = (s1_i1,r_i1) /\
     s_rel genv' s' s1_i1 /\
     (~(abort r) ==>
       source_to_flatProof_invariant interp g gen' genv'
         (idx',end_idx,os) s' s1_i1 /\
       orac_forward_rel interp (semanticPrimitives_state_eval_state
         s) (semanticPrimitives_state_eval_state s') /\ global_env_c
       genv SUBMAP global_env_c genv' /\ global_env_tys
       genv SUBMAP global_env_tys genv' /\
       subglobals (global_env_v genv) (global_env_v genv')) /\
     (!env'.
       r = Rval env' ==>
       r_i1 = NONE /\
       env_domain_eq comp_map' env' /\
       env_gen_rel gen' (semanticPrimitives_state_eval_state s') /\
       global_env_inv genv' comp_map' {} env') /\
     (!err.
       r = Rerr err ==>
       (?err_i1.
         r_i1 = SOME err_i1 /\
         result_rel (\a b (c:'a). T) genv' (Rerr err) (Rerr
           err_i1)))))`,
  CHEAT_TAC);;

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

let invariant_change_eval_ref = prove
 (`source_to_flatProof_invariant interp g gen genv idxs st st' ==>
   source_to_flatProof_invariant interp g gen genv idxs st
     (state_refs_fupd (K (CONS (semanticPrimitives_Refv y) (TL
       (state_refs st')))) st')`,
  CHEAT_TAC);;

let declare_env_store_env_id = prove
 (`declare_env (semanticPrimitives_state_eval_state st) env = SOME
  (x,es2) /\
   source_to_flatProof_invariant interp g gen genv idxs st
     (s_i1:('f_orac_st,'ffi)flatSem_state) /\
   env_gen_rel gen (semanticPrimitives_state_eval_state st) /\
   gen_id = environment_generation_store_generation gen /\
   id = environment_generation_store_next gen /\
   (match src_orac_next_cfg interp
     (semanticPrimitives_state_eval_state st) with NONE -> T | SOME c ->
     (match sptree_lookup gen_id (environment_store_env_gens
     (source_to_flat_config_envs c)) with NONE -> F | SOME gen' ->
     (match sptree_lookup id gen' with NONE -> F | SOME e ->
     global_env_inv genv e {} env))) ==>
   (?y.
   evaluate_decs s_i1 [store_env_id gen_id id] =
     (flatSem_state_refs_fupd (K (CONS (semanticPrimitives_Refv y)
       (TL (flatSem_state_refs s_i1)))) s_i1,NONE) /\
   source_to_flatProof_invariant interp g
     (environment_generation_store_next_fupd (K
     (environment_generation_store_next gen + 1)) gen) genv idxs
     (semanticPrimitives_state_eval_state_fupd (K es2) st) s_i1 /\
   (?xs. flatSem_state_globals s_i1 = CONS (SOME (Loc T 0)) xs) /\
   source_to_flatProof_v_rel genv x y /\
   orac_forward_rel interp (semanticPrimitives_state_eval_state st)
     es2)`,
  CHEAT_TAC);;

(* [local] *)
let pmatch_rows_drop_4 = prove
 (`LENGTH vs = 6 ==>
   pmatch_rows [(Pcon NONE [Pany; Pany; Pany; Pany; Pvar b; Pvar
     w],exp)]
     st (Conv NONE vs) =
   Match ([(w,LAST vs); (b,EL 4 vs)],
     Pcon NONE [Pany; Pany; Pany; Pany; Pvar b; Pvar w],exp)`,
  CHEAT_TAC);;

(* [local] *)
let drop_4_via_el = prove
 (`LENGTH vs = 6 ==> [EL 4 vs; LAST vs] = DROP 4 vs`,
  CHEAT_TAC);;

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

(* [local] *)
let abort_compile_dec_result = prove
 (`abort (combine_dec_result env r) = abort r`,
  CHEAT_TAC);;

(* [local] *)
let invariant_env_gen_inv = prove
 (`source_to_flatProof_invariant interp g gen genv (idx,end_idx,os) s
  s_i1 ==>
   env_gen_inv gen`,
  CHEAT_TAC);;

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let compile_decs_future_rel = prove
 (cake_as_vars (fun () ->
    `source_to_flat_compile_decs t n next env envs ds =
  (n2,next2,env2,envs2,ds2) /\
     env_gen_future_rel interp envs2 eval_state /\
     env_gen_inv envs ==>
     env_gen_future_rel interp envs eval_state`),
  CHEAT_TAC);;

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let env_gen_future_rel_forward = prove
 (cake_as_vars (fun () ->
    `env_gen_future_rel interp envs eval_state /\
     orac_forward_rel interp eval_state eval_state2 ==>
     env_gen_future_rel interp envs eval_state2`),
  CHEAT_TAC);;

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

let init_eval_state_ok_def = new_definition
  `init_eval_state_ok x1 =
        match x1 with
          NONE -> T
        | (SOME (EvalDecs _21)) -> F
        | (SOME (EvalOracle s)) -> generation
       s = 0 /\ envs s = [[]]`;;

let init_genv_ty_els_def = new_definition
  `init_genv_ty_els = [
     (bool_id,[(false_tag,0,TypeStamp (implode "False")
       bool_type_num);
         (true_tag,0,TypeStamp (implode "True") bool_type_num)]);
     (list_id,REVERSE [(cons_tag,2,TypeStamp (implode "::")
       list_type_num);
         (nil_tag,0,TypeStamp (implode "[]") list_type_num)])]`;;

let init_genv_els_def = new_definition
  `init_genv_els = APPEND (FLAT (MAP (\(id',xs).
         MAP (\(tag,arity,stamp). (((tag,SOME id'),arity),stamp)) xs)
     init_genv_ty_els)) [
     (((div_tag,NONE),0),div_stamp);
     (((chr_tag,NONE),0),chr_stamp);
     (((subscript_tag,NONE),0),subscript_stamp);
     (((bind_tag,NONE),0),bind_stamp)]`;;

let init_genv_def = new_definition
  `init_genv = mk_global_env [] (FEMPTY |++ init_genv_els) (FEMPTY
  |++ MAP (I ## MAP (I ## FST)) init_genv_ty_els)`;;

let init_genv_ok = prove
 (`genv_c_ok (global_env_c init_genv)`,
  CHEAT_TAC);;

let init_genv_tys_ok = prove
 (`genv_c_tys_ok (global_env_c init_genv) (global_env_tys init_genv)`,
  CHEAT_TAC);;

let init_genv_next = new_definition
  `init_genv_next = mk_next_indices 0 (SUC (MAX_LIST (MAP (\v. match
  SND v with TypeStamp _22 i -> i | _23 -> 0) init_genv_els))) (SUC
  (MAX_LIST (MAP (\v. match SND v with ExnStamp i -> i | _24 -> 0)
  init_genv_els)))`;;

let init_global_env_inv_def = new_definition
  `init_global_env_inv genv comp_map env <=> sem_env_v
   env = nsEmpty /\
   (match sem_env_c env with Bind ns ms -> ms = [] /\
     ALL (\(x,(arity,stamp)). match nsLookup
       (source_to_flat_environment_c comp_map) (Short x) with
       NONE -> F | SOME (cn,ty_gp) ->
         FLOOKUP (global_env_c genv) ((cn,OPTION_MAP FST
           ty_gp),arity) = SOME stamp /\
         (match ty_gp with NONE -> T | SOME (ty_id,ctors) ->
             FLOOKUP (global_env_tys genv) ty_id = SOME ctors))
               ns)`;;

let init_global_env_inv_imp = prove
 (`init_global_env_inv genv comp_map env ==>
   global_env_inv genv comp_map {} env`,
  CHEAT_TAC);;

let precondition1_def = new_definition
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
   ALL (\(_25,stamp). match stamp with TypeStamp cn t -> t <
     semanticPrimitives_state_next_type_stamp s1 | ExnStamp cn -> cn <
     semanticPrimitives_state_next_exn_stamp s1) init_genv_els /\ envs
   conf = envs empty_config`;;

let precondition1_change_clock = prove
 (`precondition1 interp g s1 env1 conf eval_conf prog ==>
   precondition1 interp g (state_clock_fupd (K k) s1) env1 conf
     eval_conf prog`,
  CHEAT_TAC);;

let idx_block_union_final = prove
 (`idx_prev idx idx' ==>
   idx_block idx idx' UNION idx_final_block idx' = idx_final_block
     idx`,
  CHEAT_TAC);;

(* [local] *)
let precondition_stamp_helper = prove
 (`ALL (\(_26,stamp). match stamp with TypeStamp cn t -> t < type_stamp
  | ExnStamp cn -> cn < exn_stamp) init_genv_els ==>
   (!cn t. t >= type_stamp ==> ~(TypeStamp cn t IN FRANGE
     (global_env_c init_genv))) /\
   (!cn. cn >= exn_stamp ==> ~(ExnStamp cn IN FRANGE (global_env_c
     init_genv)))`,
  CHEAT_TAC);;

let invariant_begin_alloc_blanks = prove
 (`precondition1 interp g s1 env1 cfg eval_conf prog /\
   cfg' = FST (source_to_flat_compile_prog cfg prog) /\
   init_globs = CONS (SOME (Loc T 0)) (REPLICATE (next_indices_vidx
     (next cfg') - 1) NONE) ==>
   source_to_flatProof_invariant interp g
     (mk_environment_generation_store 0 (next (envs cfg)) LN)
     (global_env_v_fupd (K init_globs) init_genv)
     (next_indices_vidx_fupd (K 1) (next cfg),next cfg',{})
     s1
     (flatSem_state_globals_fupd (K init_globs) (state_refs_fupd (K
       [semanticPrimitives_Refv (Conv NONE [])])
       (flatSem_initial_state (state_ffi s1) (state_clock s1)
       eval_conf)))`,
  CHEAT_TAC);;

let compile_prog_correct = prove
 (`precondition1 interp g s env cfg eval_conf ds /\
   source_to_flat_compile_prog cfg ds = (cfg',ds') /\
   evaluate_decs s env ds = (s',r) /\ ~(r = Rerr (Rabort
     Rtype_error)) ==>
   (?s_i1 s_i1' genv' r_i1.
   s_i1 = flatSem_initial_state (state_ffi s) (state_clock s)
     eval_conf /\
   evaluate_decs s_i1 ds' = (s_i1',r_i1) /\
   s_rel genv' s' s_i1' /\
   (!res. r = Rval res ==> r_i1 = NONE) /\
   (!err. r = Rerr err ==> (?err'. r_i1 = SOME err' /\
         ~(err' = Rabort Rtype_error) /\ result_rel (\a (b:1)
           (c:1). T) genv' (Rerr err) (Rerr err'))))`,
  CHEAT_TAC);;

(* [local] *)
let SND_eq = prove
 (`SND x = y <=> (?a. x = (a,y))`,
  CHEAT_TAC);;

(* compile_prog_semantics *)
(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let source_to_flatProof_compile_prog_semantics = prove
 (cake_as_vars (fun () ->
    `precondition1 interp g s1 env1 conf eval_conf prog ==>
      ~(semantics_prog s1 env1 prog Fail) ==>
      semantics_prog s1 env1 prog
         (semantics eval_conf (state_ffi s1)
             (SND (source_to_flat_compile_prog conf prog)))`),
  CHEAT_TAC);;

(* - connect semantics theorems of flat-to-flat passes --------------------- *)

let compile_flat_correct = prove
 (`install_conf_rel cfg ec1 ec2 /\ ~(semantics ec1 ffi prog = Fail) ==>
   semantics ec1 ffi prog =
   semantics ec2 ffi (compile_flat cfg prog)`,
  CHEAT_TAC);;

let precondition_def = new_definition
  `precondition interp s env cfg ec prog <=>
   (?ec1 g. precondition1 interp g s env cfg ec1 prog /\
     install_conf_rel (source_to_flat_config_pattern_cfg cfg) ec1
       ec)`;;

(* compile_semantics *)
(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let source_to_flatProof_compile_semantics = prove
 (cake_as_vars (fun () ->
    `precondition interp s env cfg ec prog ==>
     ~(semantics_prog s env prog Fail) ==>
     semantics_prog s env prog
        (semantics ec (state_ffi s) (SND (source_to_flat_compile
          cfg prog)))`),
  CHEAT_TAC);;

(* - esgc_free theorems for compile_exp ------------------------------------ *)

let op_gbag_astOp_to_flatOp = prove
 (`flatProps_op_gbag (astOp_to_flatOp op) = EMPTY_BAG`,
  CHEAT_TAC);;

(* compile_exp_esgc_free *)
let source_to_flatProof_compile_exp_esgc_free = prove
 (`(!tra env exp.
      flatProps_esgc_free (compile_exp tra env exp) /\
      flatProps_set_globals (compile_exp tra env exp) = EMPTY_BAG) /\
   (!tra env exps.
      ALL flatProps_esgc_free (compile_exps tra env exps) /\
      flatProps_elist_globals (compile_exps tra env exps) =
        EMPTY_BAG) /\
   (!tra env pes.
      ALL flatProps_esgc_free (MAP SND (compile_pes tra env pes)) /\
      flatProps_elist_globals (MAP SND (compile_pes tra env pes)) =
        EMPTY_BAG) /\
   (!tra env funs.
      ALL flatProps_esgc_free (MAP (SND o SND) (compile_funs tra env
        funs)) /\
      flatProps_elist_globals (MAP (SND o SND) (compile_funs tra
        env funs)) = EMPTY_BAG)`,
  CHEAT_TAC);;

(* - esgc_free theorems for compile_decs ----------------------------------- *)

let set_globals_make_varls = prove
 (`!a b c d. flatProps_set_globals (make_varls a b c d) =
             LIST_TO_BAG (MAP ((+) c) (COUNT_LIST (LENGTH d)))`,
  CHEAT_TAC);;

let make_varls_esgc_free = prove
 (`!n t idx xs.
     flatProps_esgc_free (make_varls n t idx xs)`,
  CHEAT_TAC);;

let nsAll_extend_env = prove
 (`nsAll P (source_to_flat_environment_v e1) /\ nsAll P
  (source_to_flat_environment_v e2) ==> nsAll P
  (source_to_flat_environment_v (extend_env e1 e2))`,
  CHEAT_TAC);;

(* compile_decs_esgc_free *)
let source_to_flatProof_compile_decs_esgc_free = prove
 (`!t n next' env envs' decs n' next' env' envs' decs'.
     source_to_flat_compile_decs t n next' env envs' decs =
       (n',next',env',envs',decs') ==>
      ALL flatProps_esgc_free decs'`,
  CHEAT_TAC);;

(* - the source_to_flat compiler produces things which are esgc_free ------- *)

(* compile_prog_esgc_free *)
let source_to_flatProof_compile_prog_esgc_free = prove
 (`source_to_flat_compile_prog c p = (c1,p1) ==>
   ALL flatProps_esgc_free p1`,
  CHEAT_TAC);;

let compile_flat_esgc_free = prove
 (`compile_flat cfg ds = ds' /\
   ALL flatProps_esgc_free ds ==>
   ALL flatProps_esgc_free ds'`,
  CHEAT_TAC);;

(* compile_esgc_free *)
let source_to_flatProof_compile_esgc_free = prove
 (`ALL flatProps_esgc_free (SND (source_to_flat_compile c p))`,
  CHEAT_TAC);;

let inc_compile_prog_esgc_free = prove
 (`ALL flatProps_esgc_free (SND (inc_compile_prog env_id c p))`,
  CHEAT_TAC);;

let inc_compile_esgc_free = prove
 (`ALL flatProps_esgc_free (SND (inc_compile env_id c p))`,
  CHEAT_TAC);;

let compile_no_Mat = prove
 (`no_Mat_decs (SND (source_to_flat_compile c prog))`,
  CHEAT_TAC);;

let inc_compile_no_Mat = prove
 (`no_Mat_decs (SND (inc_compile env_id c prog))`,
  CHEAT_TAC);;

(* mem_size_lemma[local] *)
let source_to_flatProof_mem_size_lemma = prove
 (`list_size sz xs < N ==> (MEM x xs ==> sz x < N)`,
  CHEAT_TAC);;

let _ = size_thms "dec";;
(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
let num_bindings_def,num_bindings_ind = define_wf
  `MEASURE dec_size`
  [`num_bindings x1 =
        match x1 with
          Dlet _27 p e ->
        (match simple_dlet p e with SOME _28 -> 0 | _29 -> LENGTH
          (pat_bindings p))
        | (Dletrec _30 f) -> LENGTH f
        | (Dmod _31 ds) -> SUM (MAP num_bindings ds)
        | (Dlocal lds ds) ->
           SUM (MAP num_bindings lds) + SUM (MAP num_bindings ds)
        | (Denv _32) -> 1
        | _33 -> 0`];;

let compile_decs_num_bindings = prove
 (`!t n next' env envs' decs n' next' env' envs' decs'.
     source_to_flat_compile_decs t n next' env envs' decs =
       (n',next',env',envs',decs') ==> next_indices_vidx
      next' <= next_indices_vidx next' /\
      SUM (MAP num_bindings decs) = next_indices_vidx next' -
        next_indices_vidx next'`,
  CHEAT_TAC);;

(* HOL4 source_to_flatProofScript.sml:5824-5825: ML code, not ported *)

let MAPi_SNOC = prove
 (`// TODO: move
   !xs x f. MAPi f (SNOC x xs) = SNOC (f (LENGTH xs) x) (MAPi f xs)`,
  CHEAT_TAC);;

(* compile_decs_elist_globals *)
let source_to_flatProof_compile_decs_elist_globals = prove
 (`!t n next' env envs' decs n' next' env' envs' decs'.
     source_to_flat_compile_decs t n next' env envs' decs =
       (n',next',env',envs',decs') ==>
     flatProps_elist_globals decs' =
       LIST_TO_BAG (MAP ((+) (next_indices_vidx next')) (COUNT_LIST
         (SUM (MAP num_bindings decs))))`,
  CHEAT_TAC);;

let compile_flat_sub_bag = prove
 (`flatProps_elist_globals (compile_flat cfg p) <=
   flatProps_elist_globals p`,
  CHEAT_TAC);;

(* HOL4 source_to_flatProofScript.sml:5885-5887: a theorem that HOL4
   states as the value of an ML expression:
   compile_flat_BAG_ALL_DISTINCT *)

let compile_globals_BAG_ALL_DISTINCT = prove
 (`BAG_ALL_DISTINCT (flatProps_elist_globals (SND
  (source_to_flat_compile c prog)))`,
  CHEAT_TAC);;

let inc_compile_globals_BAG_ALL_DISTINCT = prove
 (`BAG_ALL_DISTINCT (flatProps_elist_globals (SND (inc_compile env_id
  c prog)))`,
  CHEAT_TAC);;

let SUB_BAG_IMP = prove
 (`(B1 <= B2) ==> BAG_IN x B1 ==> BAG_IN x B2`,
  CHEAT_TAC);;

(* not sure if this variant of the inc. compiler is the one we need *)
let monotonic_globals_state_co_compile = prove
 (`source_to_flat_compile conf prog = (conf',p) /\ FST (FST (orac 0)) =
  conf' /\
   is_state_oracle (\c (env_id,decs). inc_compile env_id c (f decs))
     orac ==>
   oracle_monotonic
     (IMAGE SUC o SET_OF_BAG o flatProps_elist_globals o SND) (<)
     (0 INSERT IMAGE SUC (SET_OF_BAG (flatProps_elist_globals p)))
     (state_co (\c (env_id,decs). inc_compile env_id c (f decs))
       orac)`,
  CHEAT_TAC);;

(* and the names that this file reads as variables are constants again *)
let _ = do_list unhide_constant
  ["gc";
   "id";
   "path";
   "vars"];;

(* and the overloads that this file cannot see are back in the
   interface *)
let _ = unhide_overloads ();;
