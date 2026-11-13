(* ======================================================== *)
(*  typeSound: ported from HOL4's
    semantics/proofs/typeSoundScript.sml
    A proof theory, with 1 definition and 45 theorems.  Needed by
    compilerProof.ml and semanticsProps.ml.  *)
(* ======================================================== *)

(*
  Proof of type soundness: a type-correct program does not crash.
*)

needs "basis/pure/mlstring.ml";;
needs "semantics/ast.ml";;
needs "semantics/evaluate.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/fpSem.ml";;
needs "semantics/namespace.ml";;
needs "semantics/proofs/evaluateProps.ml";;
needs "semantics/proofs/namespaceProps.ml";;
needs "semantics/proofs/primSemEnv.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;
needs "semantics/proofs/typeSoundInvariants.ml";;
needs "semantics/proofs/typeSysProps.ml";;
needs "semantics/proofs/weakening.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "semantics/semantics.ml";;
needs "semantics/typeSystem.ml";;

(* the theories whose names the Ancestors blocks of the source
   bring, which are the ones that its statements read: the
   overloads of every other theory come out of the interface
   while this file loads *)
let _ = hol4_ancestors "typeSound"
  ["ast"; "evaluate"; "evaluateProps"; "fpSem"; "namespaceProps";
   "primSemEnv"; "semanticPrimitives"; "semanticPrimitivesProps";
   "semantics"; "typeSoundInvariants"; "typeSysProps"; "typeSystem";
   "weakening"];;

(* HOL4 typeSoundScript.sml:17-32: ML code, not ported *)

let list_rel_flat = prove
 (`!R l1 l2. LIST_REL (LIST_REL R) l1 l2 ==> LIST_REL R (FLAT l1)
  (FLAT l2)`,
  CHEAT_TAC);;

(* [local] *)
let fst_triple = prove
 (`(\(x,y,z). x) = FST`,
  CHEAT_TAC);;

let disjoint_image = prove
 (`!s1 s2 f. DISJOINT (IMAGE f s1) (IMAGE f s2) ==> DISJOINT s1 s2`,
  CHEAT_TAC);;

(* [local] *)
let sing_list = prove
 (`!l. LENGTH l = 1 <=> (?x. l = [x])`,
  CHEAT_TAC);;

(* [local] *)
let EVERY_LIST_REL = prove
 (`EVERY (\x. f x y) l = LIST_REL (\x y. f x y) l (REPLICATE (LENGTH
  l) y)`,
  CHEAT_TAC);;

(* [simp] *)
let v_unchanged = prove
 (`!tenv x. type_env_v_fupd (K (type_env_v tenv)) tenv = tenv`,
  CHEAT_TAC);;

let check_dup_ctors_thm = prove
 (`check_dup_ctors (tvs,tn,condefs) = ALL_DISTINCT (MAP FST condefs)`,
  CHEAT_TAC);;

(* Classifying values of basic types *)
let prim_canonical_values_thm = prove
 (`(type_v tvs ctMap tenvS v Tint /\ ctMap_ok ctMap ==> (?n. v =
  semanticPrimitives_Litv (ast_IntLit n))) /\
   (type_v tvs ctMap tenvS v Tchar /\ ctMap_ok ctMap ==> (?c. v =
     semanticPrimitives_Litv (ast_Char c))) /\
   (type_v tvs ctMap tenvS v Tstring /\ ctMap_ok ctMap ==> (?s. v =
     semanticPrimitives_Litv (ast_StrLit s))) /\
   (type_v tvs ctMap tenvS v Tword8 /\ ctMap_ok ctMap ==> (?n. v =
     semanticPrimitives_Litv (ast_Word8 n))) /\
   (type_v tvs ctMap tenvS v Tword64 /\ ctMap_ok ctMap ==> (?n. v =
     semanticPrimitives_Litv (ast_Word64 n))) /\
   (type_v tvs ctMap tenvS v Tdouble /\ ctMap_ok ctMap ==> (?n. v =
     semanticPrimitives_Litv (ast_Float64 n))) /\
   (type_v tvs ctMap tenvS v (Ttup ts) /\ ctMap_ok ctMap ==>
    (?vs. v = semanticPrimitives_Conv NONE vs /\ LENGTH ts = LENGTH
      vs)) /\
   (type_v tvs ctMap tenvS v (Tfn t1 t2) /\ ctMap_ok ctMap ==>
    (?env n e. v = semanticPrimitives_Closure env n e) \/
    (?env funs n. v = semanticPrimitives_Recclosure env funs n)) /\
   (type_v tvs ctMap tenvS v (Tref t1) /\ ctMap_ok ctMap /\ type_s
     ctMap envS tenvS ==>
    (?n v2. v = semanticPrimitives_Loc T n /\ store_lookup n envS =
      SOME (semanticPrimitives_Refv v2) /\
            type_v 0 ctMap tenvS v2 t1)) /\
   (type_v tvs ctMap tenvS v Tword8array /\ ctMap_ok ctMap /\ type_s
     ctMap envS tenvS ==>
    (?n ws. v = semanticPrimitives_Loc T n /\ store_lookup n envS =
      SOME (semanticPrimitives_W8array ws) /\
            FLOOKUP tenvS n = SOME W8array_t)) /\
   (type_v tvs ctMap tenvS v (Tarray t) /\ ctMap_ok ctMap /\ type_s
     ctMap envS tenvS ==>
    (?n vs. v = semanticPrimitives_Loc T n /\ store_lookup n envS =
      SOME (semanticPrimitives_Varray vs) /\
            EVERY (\v. type_v 0 ctMap tenvS v t) vs /\
            FLOOKUP tenvS n = SOME (Varray_t t))) /\
   (type_v tvs ctMap tenvS v (Tvector t) /\ ctMap_ok ctMap ==>
    (?vs. v = semanticPrimitives_Vectorv vs /\ EVERY (\v. type_v
      tvs ctMap tenvS v t) vs))`,
  CHEAT_TAC);;

(* [local] *)
let has_lists_v_to_list = prove
 (`!ctMap tvs tenvS t3.
     ctMap_ok ctMap /\
     ctMap_has_lists ctMap /\
     type_v tvs ctMap tenvS v (Tlist t3) ==>
     (?vs. semanticPrimitives_v_to_list v = SOME vs /\
          EVERY (\v. type_v tvs ctMap tenvS v t3) vs /\
          (t3 = Tchar ==> (?vs. semanticPrimitives_v_to_char_list v =
            SOME vs)) /\
          (t3 = Tstring ==> (?str. semanticPrimitives_vs_to_string
            vs = SOME str)))`,
  CHEAT_TAC);;

let ctor_canonical_values_thm = prove
 (`(type_v tvs ctMap tenvS v Tbool /\ ctMap_ok ctMap /\ ctMap_has_bools
  ctMap ==>
    (?b. v = semanticPrimitives_Boolv b)) /\
   (type_v tvs ctMap tenvS v (Tlist t) /\ ctMap_ok ctMap /\
     ctMap_has_lists ctMap ==>
    (?vs.
      semanticPrimitives_v_to_list v = SOME vs /\
      EVERY (\v. type_v tvs ctMap tenvS v t) vs /\
      (t = Tchar ==> (?vs. semanticPrimitives_v_to_char_list v = SOME
        vs)) /\
      (t = Tstring ==> (?str. semanticPrimitives_vs_to_string vs =
        SOME str)))) /\
   (type_v tvs ctMap tenvS v (Tapp ts ti) /\
    ctMap_ok ctMap /\
    FLOOKUP ctMap stamp = SOME (tvs',ts',ti) ==>
    (?cn n vs. same_type stamp (TypeStamp cn n) /\ v =
      semanticPrimitives_Conv (SOME (TypeStamp cn n)) vs) \/
    (?n vs. same_type stamp (ExnStamp n) /\ v =
      semanticPrimitives_Conv (SOME (ExnStamp n)) vs))`,
  CHEAT_TAC);;

(* [local] *)
let same_type_refl = prove
 (`!t. same_type t t`,
  CHEAT_TAC);;

(* [local] *)
let eq_same_type = prove
 (`(!v1 v2 tvs ctMap cns tenvS t.
      ctMap_ok ctMap /\
      type_v tvs ctMap tenvS v1 t /\
      type_v tvs ctMap tenvS v2 t ==> ~(semanticPrimitives_do_eq v1
        v2 = Eq_type_error)) /\
   (!vs1 vs2 tvs ctMap cns tenvS ts.
      ctMap_ok ctMap /\
      LIST_REL (type_v tvs ctMap tenvS) vs1 ts /\
      LIST_REL (type_v tvs ctMap tenvS) vs2 ts ==>
        ~(semanticPrimitives_do_eq_list vs1 vs2 = Eq_type_error))`,
  CHEAT_TAC);;

(* [local] *)
let type_env_conv_thm = prove
 (`!ctMap envC tenvC.
     nsAll2 (type_ctor ctMap) envC tenvC ==>
     (!cn tvs ts tn ti.
       (nsLookup tenvC cn = SOME (tvs,ts,ti) ==>
        (?cn' stamp.
          nsLookup envC cn = SOME (LENGTH ts,stamp) /\
          FLOOKUP ctMap stamp = SOME (tvs,ts,ti))) /\
       (nsLookup tenvC cn = NONE ==> nsLookup envC cn = NONE))`,
  CHEAT_TAC);;

(* [local] *)
let type_funs_fst = prove
 (`!tenv tenvE funs tenv'.
     type_funs tenv tenvE funs tenv' ==>
     MAP FST funs = MAP FST tenv'`,
  CHEAT_TAC);;

(* [local] *)
let type_recfun_env_help = prove
 (`!fn funs funs' ctMap tenv bindings tenvE env tenvS tvs bindings'.
     ALL_DISTINCT (MAP FST funs') /\
     tenv_ok tenv /\
     type_all_env ctMap tenvS env (type_env_v_fupd (K (add_tenvE
       tenvE (type_env_v tenv))) tenv) /\
     tenv_val_exp_ok tenvE /\
     num_tvs tenvE = 0 /\
     (!fn t. (ALOOKUP bindings fn = SOME t) ==> (ALOOKUP bindings' fn
       = SOME t)) /\
     type_funs tenv (bind_var_list 0 bindings' (bind_tvar tvs tenvE))
       funs' bindings' /\
     type_funs tenv (bind_var_list 0 bindings' (bind_tvar tvs tenvE))
       funs bindings ==>
     LIST_REL (\(x,y) (x',y'). x = x' /\ (\(tvs,t). type_v tvs ctMap
       tenvS y t) y')
              (MAP (\(fn,n,e). (fn,semanticPrimitives_Recclosure env
                funs' fn)) funs)
              (MAP (\(x,t). (x,tvs,t)) bindings)`,
  CHEAT_TAC);;

(* [local] *)
let type_recfun_env = prove
 (`!funs ctMap tenvS tvs tenv tenvE env bindings.
     tenv_ok tenv /\
     type_all_env ctMap tenvS env (type_env_v_fupd (K (add_tenvE
       tenvE (type_env_v tenv))) tenv) /\
     tenv_val_exp_ok tenvE /\
     num_tvs tenvE = 0 /\
     type_funs tenv (bind_var_list 0 bindings (bind_tvar tvs tenvE))
       funs bindings /\
     ALL_DISTINCT (MAP FST funs) ==>
     LIST_REL (\(x,y) (x',y'). x = x' /\ (\(tvs,t). type_v tvs ctMap
       tenvS y t) y')
              (MAP (\(fn,n,e). (fn,semanticPrimitives_Recclosure env
                funs fn)) funs)
              (MAP (\(x,t). (x,tvs,t)) bindings)`,
  CHEAT_TAC);;

(* HOL4 typeSoundScript.sml:411-420: a proof *)

(* [local] *)
let type_v_Boolv = prove
 (`ctMap_has_bools ctMap ==> type_v tvs ctMap tenvS
  (semanticPrimitives_Boolv b) Tbool`,
  CHEAT_TAC);;

(* remove_lambda_prod[local] *)
let typeSound_remove_lambda_prod = prove
 (`(\(x,y). P x y) = (\xy. P (FST xy) (SND xy))`,
  CHEAT_TAC);;

let opapp_type_sound = prove
 (`!ctMap tenvS vs ts t.
     ctMap_ok ctMap /\
     type_op ast_Opapp ts t /\
     LIST_REL (type_v 0 ctMap tenvS) vs ts ==>
     (?env e tenv tenvE.
       tenv_ok tenv /\
       tenv_val_exp_ok tenvE /\
       num_tvs tenvE = 0 /\
       type_all_env ctMap tenvS env (type_env_v_fupd (K (add_tenvE
         tenvE (type_env_v tenv))) tenv) /\
       type_e tenv tenvE e t /\
       semanticPrimitives_do_opapp vs = SOME (env,e))`,
  CHEAT_TAC);;

let store_type_extension_def = new_definition
  `store_type_extension tenvS1 tenvS2 =
   (?tenvS'. (tenvS2 = FUNION tenvS' tenvS1) /\
            (!l. (FLOOKUP tenvS' l = NONE) \/ (FLOOKUP tenvS1 l =
              NONE)))`;;

let store_type_extension_weakS = prove
 (`!tenvS1 tenvS2.
     store_type_extension tenvS1 tenvS2 ==> weakS tenvS2 tenvS1`,
  CHEAT_TAC);;

let store_type_extension_refl = prove
 (`!tenvS. store_type_extension tenvS tenvS`,
  CHEAT_TAC);;

let store_type_extension_trans = prove
 (`!s1 s2 s3.
     store_type_extension s1 s2 /\ store_type_extension s2 s3 ==>
     store_type_extension s1 s3`,
  CHEAT_TAC);;

let store_assign_type_sound = prove
 (`!ctMap tenvS store sv st l.
     type_s ctMap store tenvS /\
     FLOOKUP tenvS l = SOME st /\
     type_sv ctMap tenvS sv st ==>
     (?store'.
       store_assign l sv store = SOME store' /\
       type_s ctMap store' tenvS)`,
  CHEAT_TAC);;

let store_alloc_type_sound = prove
 (`!ctMap tenvS store sv st.
     ctMap_ok ctMap /\
     type_s ctMap store tenvS /\
     type_sv ctMap tenvS sv st ==>
     (?store' tenvS' n.
       store_type_extension tenvS tenvS' /\
       store_alloc sv store = (store',n) /\
       type_s ctMap store' tenvS' /\
       FLOOKUP tenvS' n = SOME st)`,
  CHEAT_TAC);;

(* HOL4 typeSoundScript.sml:618-632: code that the source has in a
   comment *)

let type_v_list_to_v = prove
 (`!x xs t.
     type_v n ctMap tenvS x t /\
     semanticPrimitives_v_to_list x = SOME xs ==>
     type_v n ctMap tenvS (semanticPrimitives_list_to_v xs) t`,
  CHEAT_TAC);;

let type_v_list_to_v_APPEND = prove
 (`!xs ys t.
     ctMap_has_lists ctMap /\
     type_v 0 ctMap tenvS (semanticPrimitives_list_to_v xs) (Tapp [t]
       Tlist_num) /\
     type_v 0 ctMap tenvS (semanticPrimitives_list_to_v ys) (Tapp [t]
       Tlist_num) ==>
     type_v 0 ctMap tenvS (semanticPrimitives_list_to_v (xs ++ ys))
       (Tapp [t] Tlist_num)`,
  CHEAT_TAC);;

let do_eq_Boolv = prove
 (`semanticPrimitives_do_eq (semanticPrimitives_Boolv b)
  (semanticPrimitives_Boolv b') = Eq_val (b = b')`,
  CHEAT_TAC);;

let prim_canonical_Boolv_thm = prove
 (`(type_v tvs ctMap tenvS v Tbool /\ ctMap_ok ctMap /\ ctMap_has_bools
  ctMap ==>
   (?b. v = semanticPrimitives_Boolv b))`,
  CHEAT_TAC);;

(* [local] *)
let prim_canonical_Boolv_cases = prove
 (`type_v tvs ctMap tenvS v (Tapp [] Tbool_num) /\
   ctMap_ok ctMap /\
   ctMap_has_bools ctMap ==>
   v = semanticPrimitives_Boolv T \/ v = semanticPrimitives_Boolv F`,
  CHEAT_TAC);;

let op_type_sound = prove
 (`!ctMap tenvS vs op ts t store (ffi:'ffi ffi_state).
     good_ctMap ctMap /\ ~(op = ast_Opapp) /\
     type_s ctMap store tenvS /\
     type_op op ts t /\
     check_freevars 0 [] t /\
     LIST_REL (type_v 0 ctMap tenvS) vs (REVERSE ts) ==>
   (?tenvS' store' ffi' r.
     store_type_extension tenvS tenvS' /\
     type_s ctMap store' tenvS' /\
     semanticPrimitives_do_app (store,ffi) op (REVERSE vs) = SOME
       ((store',ffi'),r) /\
     (match r with Rval v -> type_v 0 ctMap tenvS' v t | Rerr
       (Rraise v) -> type_v 0 ctMap tenvS' v Texn | Rerr (Rabort
       (Rffi_error _1)) -> T | Rerr (Rabort _2) -> F))`,
  CHEAT_TAC);;

let build_conv_type_sound = prove
 (`!envC cn vs tvs ts ctMap tenvS ts' tn tenvC tvs' tenvE l.
   nsAll2 (type_ctor ctMap) envC tenvC /\
   do_con_check envC (SOME cn) l /\
   num_tvs tenvE = 0 /\
   EVERY (check_freevars (num_tvs (bind_tvar tvs tenvE)) []) ts' /\
   LENGTH tvs' = LENGTH ts' /\
   LIST_REL (type_v tvs ctMap tenvS) vs
     (REVERSE (MAP (type_subst (alist_to_fmap (ZIP tvs' ts'))) ts))
       /\
   nsLookup tenvC cn = SOME (tvs',ts,tn) ==>
   (?v.
     build_conv envC (SOME cn) (REVERSE vs) = SOME v /\
     type_v tvs ctMap tenvS v (Tapp ts' tn))`,
  CHEAT_TAC);;

let same_ctor_and_same_tid = prove
 (`!stamp1 stamp2.
    same_ctor stamp1 stamp2 /\
    same_type stamp1 stamp2 ==>
    stamp1 = stamp2`,
  CHEAT_TAC);;

(* HOL4 typeSoundScript.sml:1125-1139: a proof *)

let pat_type_sound = prove
 (`(!(cenv:(mlstring,mlstring,num#stamp)namespace) st p v bindings tenv
  ctMap tbindings t new_tbindings tenvS tvs.
    ctMap_ok ctMap /\
    nsAll2 (type_ctor ctMap) cenv (type_env_c tenv) /\
    type_v tvs ctMap tenvS v t /\
    type_p tvs tenv p t new_tbindings /\
    type_s ctMap st tenvS /\
    LIST_REL (\(x,v) (x',t). x = x' /\ type_v tvs ctMap tenvS v t)
      bindings tbindings ==>
    semanticPrimitives_pmatch cenv st p v bindings = No_match \/
    (?bindings'.
      semanticPrimitives_pmatch cenv st p v bindings = Match
        bindings' /\
      LIST_REL (\(x,v) (x',t). x = x' /\ type_v tvs ctMap tenvS v t)
        bindings'
        (new_tbindings ++ tbindings))) /\
   (!(cenv:(mlstring,mlstring,num#stamp)namespace) st ps vs bindings
     tenv ctMap tbindings new_tbindings ts tenvS tvs.
    ctMap_ok ctMap /\
    nsAll2 (type_ctor ctMap) cenv (type_env_c tenv) /\
    LIST_REL (type_v tvs ctMap tenvS) vs ts /\
    type_ps tvs tenv ps ts new_tbindings /\
    type_s ctMap st tenvS /\
    LIST_REL (\(x,v) (x',t). x = x' /\ type_v tvs ctMap tenvS v t)
      bindings tbindings ==>
    semanticPrimitives_pmatch_list cenv st ps vs bindings = No_match
      \/
    (?bindings'.
      semanticPrimitives_pmatch_list cenv st ps vs bindings = Match
        bindings' /\
      LIST_REL (\(x,v) (x',t). x = x' /\ type_v tvs ctMap tenvS v t)
        bindings'
        (new_tbindings ++ tbindings)))`,
  CHEAT_TAC);;

let lookup_var_sound = prove
 (`!n tvs tenvE targs t ctMap tenvS env tenv.
    lookup_var n (bind_tvar tvs tenvE) tenv = SOME (LENGTH targs,t)
      /\
    ctMap_ok ctMap /\
    tenv_val_exp_ok tenvE /\
    num_tvs tenvE = 0 /\
    EVERY (check_freevars tvs []) targs /\
    type_all_env ctMap tenvS env (type_env_v_fupd (K (add_tenvE tenvE
      (type_env_v tenv))) tenv) ==>
    (?v. nsLookup (sem_env_v env) n = SOME v /\ type_v tvs ctMap
      tenvS v (deBruijn_subst 0 targs t))`,
  CHEAT_TAC);;

(* TODO: Move *)
let EVERY_REPLICATE = prove
 (`EVERY (\x. type_v tvs ctMap tenv x t') vs =
   EVERY (\x. type_v tvs ctMap tenv (FST x) (SND x)) (ZIP vs
     (REPLICATE (LENGTH vs) t'))`,
  CHEAT_TAC);;

(* EVERY_LIST_REL *)
let typeSound_EVERY_LIST_REL = prove
 (`EVERY (\v. type_v n ctMap tenvS v t) vs =
   LIST_REL (type_v n ctMap tenvS) vs (REPLICATE (LENGTH vs) t)`,
  CHEAT_TAC);;

let exp_type_sound = prove
 (`(!(s:'ffi semanticPrimitives_state) env es r s' tenv tenvE ts tvs
  tenvS.
     evaluate s env es = (s',r) /\
     tenv_ok tenv /\
     tenv_val_exp_ok tenvE /\
     good_ctMap ctMap /\
     num_tvs tenvE = 0 /\
     type_all_env ctMap tenvS env (type_env_v_fupd (K (add_tenvE
       tenvE (type_env_v tenv))) tenv) /\
     type_s ctMap (semanticPrimitives_state_refs s) tenvS /\
     (~(tvs = 0) ==> EVERY is_value es) /\
     type_es tenv (bind_tvar tvs tenvE) es ts ==>
     (?tenvS'.
       type_s ctMap (semanticPrimitives_state_refs s') tenvS' /\
       store_type_extension tenvS tenvS' /\
         semanticPrimitives_state_next_type_stamp
       s' = semanticPrimitives_state_next_type_stamp s /\
         semanticPrimitives_state_next_exn_stamp
       s' = semanticPrimitives_state_next_exn_stamp s /\
       (match r with Rval vs -> LIST_REL (type_v tvs ctMap tenvS') vs
         ts | Rerr (Rraise v) -> type_v 0 ctMap tenvS' v Texn | Rerr
         (Rabort Rtimeout_error) -> T | Rerr (Rabort (Rffi_error _3)) ->
         T | Rerr (Rabort Rtype_error) -> F))) /\
   (!(s:'ffi semanticPrimitives_state) env v pes err_v r s' tenv
     tenvE t1 t2 tvs tenvS.
     evaluate_evaluate_match s env v pes err_v = (s',r) /\
     tenv_ok tenv /\
     tenv_val_exp_ok tenvE /\
     good_ctMap ctMap /\
     num_tvs tenvE = 0 /\
     type_all_env ctMap tenvS env (type_env_v_fupd (K (add_tenvE
       tenvE (type_env_v tenv))) tenv) /\
     type_s ctMap (semanticPrimitives_state_refs s) tenvS /\
     type_v tvs ctMap tenvS v t1 /\
     type_v 0 ctMap tenvS err_v Texn /\
     type_pes tvs tvs tenv tenvE pes t1 t2 ==>
     (?tenvS'.
       type_s ctMap (semanticPrimitives_state_refs s') tenvS' /\
       store_type_extension tenvS tenvS' /\
         semanticPrimitives_state_next_type_stamp
       s' = semanticPrimitives_state_next_type_stamp s /\
         semanticPrimitives_state_next_exn_stamp
       s' = semanticPrimitives_state_next_exn_stamp s /\
       (match r with Rval vs -> type_v tvs ctMap tenvS' (HD vs) t2
         | Rerr (Rraise v) -> type_v 0 ctMap tenvS' v Texn | Rerr
         (Rabort Rtimeout_error) -> T | Rerr (Rabort (Rffi_error _4))
         -> T | Rerr (Rabort Rtype_error) -> F)))`,
  CHEAT_TAC);;

(* HOL4 typeSoundScript.sml:1920-1967: a proof *)

(* [local] *)
let build_tdefs_build_tenv = prove
 (`!tenvT (tds:(mlstring list#mlstring#(mlstring#ast_t list) list) list)
  (tids:num list) next' (ctMap:(stamp,mlstring list#t list#num)fmap).
     EVERY (\(_5,_6,ctors). ALL_DISTINCT (MAP FST ctors)) tds /\
     LENGTH tds = LENGTH tids ==>
     nsAll2
       (type_ctor (ctMap |++ REVERSE (type_def_to_ctMap tenvT next'
         tds tids)))
       (build_tdefs next' tds:(mlstring,mlstring,num#stamp)namespace)
       (build_ctor_tenv tenvT tds tids)`,
  CHEAT_TAC);;

(* [local] *)
let type_sound_invariant_union = prove
 (`type_sound_invariant st env ctMap tenvS (tids1 UNION tids2) tenv ==>
    type_sound_invariant st env ctMap tenvS tids1 tenv`,
  CHEAT_TAC);;

(* [local] *)
let check_ctor_tenv_dups = prove
 (`!tenvT tds. check_ctor_tenv tenvT tds ==> EVERY check_dup_ctors tds`,
  CHEAT_TAC);;

let type_all_env_extend = prove
 (`type_all_env ctMap tenvS env1 tenv1 /\ type_all_env ctMap tenvS env2
  tenv2 ==> type_all_env ctMap tenvS (extend_dec_env env1 env2)
        (extend_dec_tenv tenv1 tenv2)`,
  CHEAT_TAC);;

let type_e_con_check = prove
 (`(!tenv tenvE e t.
     type_e tenv tenvE e t ==>
     nsAll2 (type_ctor ctMap) envc (type_env_c tenv) ==>
     every_exp (one_con_check envc) e) /\
   (!tenv tenvE es ts.
     type_es tenv tenvE es ts ==>
     nsAll2 (type_ctor ctMap) envc (type_env_c tenv) ==>
     EVERY (every_exp (one_con_check envc)) es) /\
   (!tenv tenvE funs env.
     type_funs tenv tenvE funs env ==>
     nsAll2 (type_ctor ctMap) envc (type_env_c tenv) ==>
     EVERY (\(f,n,e). every_exp (one_con_check envc) e) funs)`,
  CHEAT_TAC);;

let decs_type_sound_no_check = prove
 (`!(st:'ffi semanticPrimitives_state) env ds st' r ctMap tenvS tenv
  tids tenv'.
    evaluate_evaluate_decs st env ds = (st',r) /\
    type_ds F tenv ds tids tenv' /\
    type_sound_invariant st env ctMap tenvS tids tenv ==>
    (?ctMap' tenvS'.
      weakCT ctMap' ctMap /\
      FRANGE ((SND o SND) o_f ctMap') DIFF FRANGE ((SND o SND) o_f
        ctMap) SUBSET tids /\
      store_type_extension tenvS tenvS' /\
      (match r with Rval env' ->
        type_all_env ctMap' tenvS' env' tenv' /\
        type_sound_invariant st' (extend_dec_env env' env)
          ctMap' tenvS' {} (extend_dec_tenv tenv' tenv) | Rerr
            (Rraise err_v) ->
        type_v 0 ctMap' tenvS' err_v Texn /\
        type_sound_invariant st' env ctMap' tenvS' {} tenv | Rerr
          (Rabort Rtype_error) -> F | Rerr (Rabort Rtimeout_error) ->
          T | Rerr (Rabort (Rffi_error _7)) -> T))`,
  CHEAT_TAC);;

let decs_type_sound = prove
 (`!(st:'ffi semanticPrimitives_state) env ds extra_checks st' r ctMap
  tenvS tenv tids tenv'.
    evaluate_evaluate_decs st env ds = (st',r) /\
    type_ds extra_checks tenv ds tids tenv' /\
    type_sound_invariant st env ctMap tenvS tids tenv ==>
    (?ctMap' tenvS'.
      weakCT ctMap' ctMap /\
      FRANGE ((SND o SND) o_f ctMap') DIFF FRANGE ((SND o SND) o_f
        ctMap) SUBSET tids /\
      store_type_extension tenvS tenvS' /\
      (match r with Rval env' ->
        type_all_env ctMap' tenvS' env' tenv' /\
        type_sound_invariant st' (extend_dec_env env' env)
          ctMap' tenvS' {} (extend_dec_tenv tenv' tenv) | Rerr
            (Rraise err_v) ->
        type_v 0 ctMap' tenvS' err_v Texn /\
        type_sound_invariant st' env ctMap' tenvS' {} tenv | Rerr
          (Rabort Rtype_error) -> F | Rerr (Rabort (Rffi_error _8)) ->
          T | Rerr (Rabort Rtimeout_error) -> T))`,
  CHEAT_TAC);;

let semantics_type_sound = prove
 (`!(st:'ffi semanticPrimitives_state) env tops r checks ctMap tenvS
  tenv new_tenv tids.
    semantics_prog st env tops r /\
    type_ds checks tenv tops tids new_tenv /\
    type_sound_invariant st env ctMap tenvS tids tenv ==> ~(r =
      ffi_Fail)`,
  CHEAT_TAC);;

(* and the overloads that this file cannot see are back in the
   interface *)
let _ = unhide_overloads ();;
