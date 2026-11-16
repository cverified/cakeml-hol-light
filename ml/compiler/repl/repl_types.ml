(* ======================================================== *)
(*  repl_types: ported from HOL4's
    compiler/repl/repl_typesScript.sml
    A definition theory, with 8 definitions, 1 datatype and 31
    theorems.  Needed by replProof.ml and repl_init.ml.  *)
(* ======================================================== *)

(*
  Proofs about how the REPL uses types and the type inferencer
*)

needs "basis/pure/mlstring.ml";;
needs "compiler/inference/infer.ml";;
needs "compiler/inference/inferProps.ml";;
needs "compiler/inference/infer_t.ml";;
needs "compiler/inference/proofs/envRel.ml";;
needs "compiler/inference/proofs/inferSound.ml";;
needs "compiler/repl/evaluate_init.ml";;
needs "compiler/repl/evaluate_skip.ml";;
needs "compiler/repl/repl_check_and_tweak.ml";;
needs "semantics/evaluate.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/namespace.ml";;
needs "semantics/primTypes.ml";;
needs "semantics/proofs/namespaceProps.ml";;
needs "semantics/proofs/primSemEnv.ml";;
needs "semantics/proofs/semanticsProps.ml";;
needs "semantics/proofs/typeSound.ml";;
needs "semantics/proofs/typeSoundInvariants.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "semantics/semantics.ml";;
needs "semantics/typeSystem.ml";;
needs "translator/ml_prog.ml";;
needs "translator/monadic/monad_base/ml_monadBase.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "repl_types"
  ["envRel"; "evaluate"; "evaluate_init"; "evaluate_skip"; "infer";
   "inferProps"; "inferSound"; "ml_prog"; "namespaceProps"; "primSemEnv";
   "repl_check_and_tweak"; "semanticPrimitives"; "semantics";
   "semanticsProps"; "typeSound"; "typeSoundInvariants"];;

let _ = do_list hide_constant ["id"];;

let simple_type_INDUCT,simple_type_RECURSION = define_datatype
  "simple_type =
     repl_types_Bool
   | repl_types_Str
   | repl_types_Exn";;

let to_type_def = define_cases
  `(to_type repl_types_Bool = Infer_Tapp [] Tbool_num) /\
   (to_type repl_types_Str = Infer_Tapp [] Tstring_num) /\
   (to_type repl_types_Exn = Infer_Tapp [] Texn_num)`;;

let check_ref_types_def = new_definition
  `check_ref_types types' (env:semanticPrimitives_v sem_env)
  (CommandLineProof_name,ty,loc) <=>
     nsLookup (inf_env_inf_v types') CommandLineProof_name = SOME
       (0,Infer_Tapp [to_type ty] Tref_num) /\
     nsLookup (sem_env_v env) CommandLineProof_name = SOME
       (semanticPrimitives_Loc T loc)`;;

let repl_types_roll_back_def = new_definition
  `repl_types_roll_back ((old_ienv:inf_env),(old_next_id:num))
  ((new_ienv:inf_env),(new_next_id:num)) =
     (old_ienv,new_next_id)`;;

let FST_roll_back = prove
 (`FST (repl_types_roll_back x y) = FST x`,
  CHEAT_TAC);;
add_simp FST_roll_back;;

let SND_roll_back = prove
 (`SND (repl_types_roll_back x y) = SND y`,
  CHEAT_TAC);;
add_simp SND_roll_back;;

let repl_types = cake_inductive
  `((!ffi rs decs types' (s:'ffi semanticPrimitives_state) env ck b.
        infertype_prog_inc (infer_init_config,start_type_id) decs =
          M_success types' /\
        evaluate_evaluate_decs (semanticPrimitives_state_clock_fupd (K ck)
          (ml_prog_init_state ffi)) init_env decs = (s,Rval env) /\
        ALL (check_ref_types (FST types') (extend_dec_env env init_env)) rs
          ==>
        repl_types b (ffi,rs) (types',s,extend_dec_env env init_env))) /\
   ((!ffi rs types' junk ck t e (s:'ffi semanticPrimitives_state) env.
        repl_types T (ffi,rs) (types',s,env) ==>
        repl_types T (ffi,rs)
          (types',semanticPrimitives_state_next_exn_stamp_fupd (K
          (semanticPrimitives_state_next_exn_stamp s + e))
          (semanticPrimitives_state_next_type_stamp_fupd (K
          (semanticPrimitives_state_next_type_stamp s + t))
          (semanticPrimitives_state_clock_fupd (K
          (semanticPrimitives_state_clock s - ck))
          (semanticPrimitives_state_refs_fupd (K (APPEND
          (semanticPrimitives_state_refs s) junk)) s))),env))) /\
   ((!ffi rs decs types' new_types (s:'ffi semanticPrimitives_state) env
     new_env new_s b.
        repl_types b (ffi,rs) (types',s,env) /\
        infertype_prog_inc types' decs = M_success new_types /\
        evaluate_evaluate_decs s env decs = (new_s,Rval new_env) ==>
        repl_types b (ffi,rs) (new_types,new_s,extend_dec_env new_env env)))
          /\
   ((!ffi rs decs types' new_types (s:'ffi semanticPrimitives_state) env e
     new_s b.
        repl_types b (ffi,rs) (types',s,env) /\
        infertype_prog_inc types' decs = M_success new_types /\
        evaluate_evaluate_decs s env decs = (new_s,Rerr (Rraise e)) ==>
        repl_types b (ffi,rs) (repl_types_roll_back types'
          new_types,new_s,env))) /\
   ((!ffi rs decs types' new_types (s:'ffi semanticPrimitives_state) env e
       new_s CommandLineProof_name loc new_store b.
        repl_types b (ffi,rs) (types',s,env) /\
        infertype_prog_inc types' decs = M_success new_types /\
        evaluate_evaluate_decs s env decs = (new_s,Rerr (Rraise e)) /\
        MEM (CommandLineProof_name,repl_types_Exn,loc) rs /\
        store_assign loc (semanticPrimitives_Refv e)
          (semanticPrimitives_state_refs new_s) = SOME new_store ==>
        repl_types b (ffi,rs) (repl_types_roll_back types'
          new_types,semanticPrimitives_state_refs_fupd (K new_store)
          new_s,env))) /\
   ((!ffi rs types' (s:'ffi semanticPrimitives_state) env t
     CommandLineProof_name loc new_store b.
        repl_types b (ffi,rs) (types',s,env) /\
        MEM (CommandLineProof_name,repl_types_Str,loc) rs /\
        store_assign loc (semanticPrimitives_Refv (semanticPrimitives_Litv
          (ast_StrLit t))) (semanticPrimitives_state_refs s) = SOME new_store
          ==>
        repl_types b (ffi,rs) (types',semanticPrimitives_state_refs_fupd
          (K new_store) s,env)))`;;

(* Mirror definitions for repl_types using the type system directly *)
let to_type_TS_def = define_cases
  `(to_type_TS repl_types_Bool = Tapp [] Tbool_num) /\
   (to_type_TS repl_types_Str = Tapp [] Tstring_num) /\
   (to_type_TS repl_types_Exn = Tapp [] Texn_num)`;;

let check_ref_types_TS_def = new_definition
  `check_ref_types_TS types' (env:semanticPrimitives_v sem_env)
  (CommandLineProof_name,ty,loc) <=>
     nsLookup (sem_env_v types') CommandLineProof_name = SOME (0,Tapp
       [to_type_TS ty] Tref_num) /\
     nsLookup (sem_env_v env) CommandLineProof_name = SOME
       (semanticPrimitives_Loc T loc)`;;

let repl_types_TS = cake_inductive
  `((!ffi rs decs tids tenv (s:'ffi semanticPrimitives_state) env ck.
        type_ds T prim_tenv decs tids tenv /\
        DISJOINT tids {Tlist_num,Tbool_num,Texn_num} /\
        evaluate_evaluate_decs (semanticPrimitives_state_clock_fupd (K ck)
          (ml_prog_init_state ffi)) init_env decs = (s,Rval env) /\
        ALL (check_ref_types_TS (extend_dec_tenv tenv prim_tenv)
          (extend_dec_env env init_env)) rs ==>
        repl_types_TS (ffi,rs) (tids,extend_dec_tenv tenv
          prim_tenv,s,extend_dec_env env init_env))) /\
   ((!ffi rs decs tids tenv (s:'ffi semanticPrimitives_state) env
       new_tids new_tenv new_env new_s.
        repl_types_TS (ffi,rs) (tids,tenv,s,env) /\
        type_ds T tenv decs new_tids new_tenv /\
        DISJOINT tids new_tids /\
        evaluate_evaluate_decs s env decs = (new_s,Rval new_env) ==>
        repl_types_TS (ffi,rs) (tids UNION new_tids,extend_dec_tenv new_tenv
          tenv,new_s,extend_dec_env new_env env))) /\
   ((!ffi rs decs tids tenv (s:'ffi semanticPrimitives_state) env
       new_tids new_tenv new_s e.
        repl_types_TS (ffi,rs) (tids,tenv,s,env) /\
        type_ds T tenv decs new_tids new_tenv /\
        DISJOINT tids new_tids /\
        evaluate_evaluate_decs s env decs = (new_s,Rerr (Rraise e)) ==>
        repl_types_TS (ffi,rs) (tids UNION new_tids,tenv,new_s,env))) /\
   ((!ffi rs decs tids tenv (s:'ffi semanticPrimitives_state) env
       new_tids new_tenv new_s e CommandLineProof_name loc new_store.
        repl_types_TS (ffi,rs) (tids,tenv,s,env) /\
        type_ds T tenv decs new_tids new_tenv /\
        DISJOINT tids new_tids /\
        evaluate_evaluate_decs s env decs = (new_s,Rerr (Rraise e)) /\
        MEM (CommandLineProof_name,repl_types_Exn,loc) rs /\
        store_assign loc (semanticPrimitives_Refv e)
          (semanticPrimitives_state_refs new_s) = SOME new_store ==>
        repl_types_TS (ffi,rs) (tids UNION
          new_tids,tenv,semanticPrimitives_state_refs_fupd (K new_store)
          new_s,env))) /\
   ((!ffi rs tids tenv (s:'ffi semanticPrimitives_state) env t
     CommandLineProof_name loc new_store.
        repl_types_TS (ffi,rs) (tids,tenv,s,env) /\
        MEM (CommandLineProof_name,repl_types_Str,loc) rs /\
        store_assign loc (semanticPrimitives_Refv (semanticPrimitives_Litv
          (ast_StrLit t))) (semanticPrimitives_state_refs s) = SOME new_store
          ==>
        repl_types_TS (ffi,rs)
          (tids,tenv,semanticPrimitives_state_refs_fupd (K new_store)
          s,env)))`;;

let init_config_tenv_to_ienv = prove
 (`infer_init_config = tenv_to_ienv prim_tenv`,
  CHEAT_TAC);;

let ienv_to_tenv_init_config = prove
 (`ienv_to_tenv infer_init_config = prim_tenv`,
  CHEAT_TAC);;

let tenv_ok_prim_tenv = prove
 (`tenv_ok prim_tenv`,
  CHEAT_TAC);;
add_simp tenv_ok_prim_tenv;;

let env_rel_init_config = prove
 (`envRel_env_rel prim_tenv infer_init_config`,
  CHEAT_TAC);;

let inf_set_tids_ienv_init_config = prove
 (`inf_set_tids_ienv (count start_type_id) infer_init_config`,
  CHEAT_TAC);;
add_simp inf_set_tids_ienv_init_config;;

let ienv_ok_init_config = prove
 (`ienv_ok {} infer_init_config`,
  CHEAT_TAC);;

let repl_types_ienv_ok = prove
 (`!b (ffi:'ffi ffi_state) rs types' s env.
   repl_types b (ffi,rs) (types',s,env) ==>
   ienv_ok {} (FST types')`,
  CHEAT_TAC);;

let repl_types_next_id = prove
 (`!b (ffi:'ffi ffi_state) rs types' s env.
   repl_types b (ffi,rs) (types',s,env) ==>
   start_type_id <= SND types'`,
  CHEAT_TAC);;

let convert_t_to_type = prove
 (`convert_t (to_type t) = to_type_TS t`,
  CHEAT_TAC);;

let check_ref_types_check_ref_types_TS = prove
 (`check_ref_types ienv env x ==>
   check_ref_types_TS (ienv_to_tenv ienv) env x`,
  CHEAT_TAC);;

let ref_lookup_ok_def = new_definition
  `ref_lookup_ok refs
  ((CommandLineProof_name:(mlstring,mlstring)namespace_id),ty,loc) =
     (?(v:semanticPrimitives_v).
       store_lookup loc refs = SOME (semanticPrimitives_Refv v) /\
       (ty = repl_types_Bool ==> v = semanticPrimitives_Boolv T \/ v =
         semanticPrimitives_Boolv F) /\
       (ty = repl_types_Str ==> (?t. v = semanticPrimitives_Litv (ast_StrLit
         t))) /\
       (ty = repl_types_Exn ==> (?s ls. v = semanticPrimitives_Conv (SOME
         (ExnStamp s)) ls)))`;;

let type_d_tids_disjoint = prove
 (`(!b tenv d tids tenv'.
    type_d b tenv d tids tenv' ==>
      DISJOINT tids (set_of_list (CONS Tlist_num (CONS Tbool_num
        prim_type_nums)))) /\
   (!b tenv ds tids tenv'.
    type_ds b tenv ds tids tenv' ==>
      DISJOINT tids (set_of_list (CONS Tlist_num (CONS Tbool_num
        prim_type_nums))))`,
  CHEAT_TAC);;

let ref_lookup_ok_store_assign = prove
 (`ALL (ref_lookup_ok store) rs /\
   MEM (n,repl_types_Str,loc) rs /\
   store_assign loc (semanticPrimitives_Refv (semanticPrimitives_Litv
     (ast_StrLit t))) store = SOME new_store ==>
   ALL (ref_lookup_ok new_store) rs`,
  CHEAT_TAC);;

let type_v_invert_strlit = prove
 (`!n ct tenv l ty.
   l = semanticPrimitives_Litv (ast_StrLit t) /\
   type_v n ct tenv l ty ==>
   ty = Tstring`,
  CHEAT_TAC);;

let ref_lookup_ok_store_assign_exn = prove
 (`ALL (ref_lookup_ok store) rs /\
   MEM (n,repl_types_Exn,loc) rs /\
   type_v 0 ctMap tenvS e (Tapp [] Texn_num) /\ ctMap_ok ctMap /\
   store_assign loc (semanticPrimitives_Refv e) store = SOME new_store ==>
   ALL (ref_lookup_ok new_store) rs`,
  CHEAT_TAC);;

let type_v_invert_exn = prove
 (`!n ct tenv l ty.
   l = semanticPrimitives_Conv (SOME (ExnStamp s)) ls /\
   ctMap_ok ct /\
   type_v n ct tenv l ty ==>
   ty = Tapp [] Texn_num`,
  CHEAT_TAC);;

let type_s_store_assign_StrLit = prove
 (`type_s ctMap st tenvS /\
   ALL (ref_lookup_ok st) rs /\
   MEM (n,repl_types_Str,loc) rs /\
   store_assign loc (semanticPrimitives_Refv (semanticPrimitives_Litv
     (ast_StrLit t))) st = SOME new_st ==>
   type_s ctMap new_st tenvS`,
  CHEAT_TAC);;

let type_s_store_assign_exn = prove
 (`type_s ctMap st tenvS /\
   ALL (ref_lookup_ok st) rs /\
   MEM (n,repl_types_Exn,loc) rs /\
   ctMap_ok ctMap /\
   type_v 0 ctMap tenvS e (Tapp [] Texn_num) /\
   store_assign loc (semanticPrimitives_Refv e) st = SOME new_st ==>
   type_s ctMap new_st tenvS`,
  CHEAT_TAC);;

(* HOL4 repl_typesScript.sml:410-508: a proof *)

let repl_types_TS_thm = prove
 (`!(ffi:'ffi ffi_state) rs tids tenv s env.
     repl_types_TS (ffi,rs) (tids,tenv,s,env) ==>
       (
        // Probably keep more information about ctMap tenvS
        ?ctMap tenvS.
         FRANGE ((SND o SND) o_f ctMap) SUBSET tids UNION prim_type_ids /\
         type_sound_invariant s env ctMap tenvS {} tenv) /\
       ALL (ref_lookup_ok (semanticPrimitives_state_refs s)) rs /\
       (!decs new_tids new_tenv new_s res.
         type_ds T tenv decs new_tids new_tenv /\
         DISJOINT tids new_tids /\
         evaluate_evaluate_decs s env decs = (new_s,res) ==> ~(res = Rerr
           (Rabort Rtype_error)))`,
  CHEAT_TAC);;

let DISJOINT_set_ids = prove
 (`tids SUBSET count id ==>
   DISJOINT tids (set_ids id id')`,
  CHEAT_TAC);;

let set_ids_SUBSET = prove
 (`set_ids id id' SUBSET count id'`,
  CHEAT_TAC);;
add_simp set_ids_SUBSET;;

let count_id_MORE = prove
 (`tids SUBSET count id /\ id <= id' ==> tids SUBSET count id'`,
  CHEAT_TAC);;

let set_ids_UNION = prove
 (`id <= id' /\ sid <= id ==>
   set_ids sid id' = set_ids sid id UNION set_ids id id'`,
  CHEAT_TAC);;

let repl_types_F_repl_types_TS = prove
 (`!(ffi:'ffi ffi_state) rs types' s env.
     repl_types F (ffi,rs) (types',s,env) ==>
     repl_types_TS (ffi,rs) (set_ids start_type_id (SND
       types'),ienv_to_tenv (FST types'),s,env)`,
  CHEAT_TAC);;

let repl_types_F_thm = prove
 (`!(ffi:'ffi ffi_state) rs types' s env.
     repl_types F (ffi,rs) (types',s,env) ==>
       ALL (ref_lookup_ok (semanticPrimitives_state_refs s)) rs /\
       (!decs new_t new_s res.
         infertype_prog_inc types' decs = M_success new_t /\
         evaluate_evaluate_decs s env decs = (new_s,res) ==> ~(res = Rerr
           (Rabort Rtype_error)))`,
  CHEAT_TAC);;

let repl_types_skip_alt = prove
 (`repl_types T (ffi,rs) (t,s,env) /\ semanticPrimitives_state_ffi
   s = semanticPrimitives_state_ffi s1 /\ semanticPrimitives_state_refs
   s <<= semanticPrimitives_state_refs s1 /\ semanticPrimitives_state_clock
   s1 <= semanticPrimitives_state_clock s
     /\ semanticPrimitives_state_eval_state
   s = semanticPrimitives_state_eval_state s1
     /\ semanticPrimitives_state_next_type_stamp
   s <= semanticPrimitives_state_next_type_stamp s1
     /\ semanticPrimitives_state_next_exn_stamp
   s <= semanticPrimitives_state_next_exn_stamp s1 ==>
   repl_types T (ffi,rs) (t,s1,env)`,
  CHEAT_TAC);;

let repl_types_set_clock = prove
 (`!b ffi rs t s env.
     repl_types b (ffi,rs) (t,s,env) ==>
     (!ck. repl_types b (ffi,rs) (t,semanticPrimitives_state_clock_fupd (K
       ck) s,env))`,
  CHEAT_TAC);;

(* [local] *)
let INJ_count_ADD = prove
 (`INJ f a (count k) ==> INJ f a (count (t + k))`,
  CHEAT_TAC);;

let repl_types_T_F = prove
 (`!(ffi:'ffi ffi_state) rs types' t env1.
     repl_types T (ffi,rs) (types',t,env1) ==>
     (?s env fr ft fe l.
       repl_types F (ffi,rs) (types',s,env) /\
       evaluate_skip_state_rel l fr ft fe s t /\
       envRel_env_rel fr ft fe env env1 /\
       ALL (\(a,b,loc). loc < l) rs)`,
  CHEAT_TAC);;

let repl_types_thm = prove
 (`!(ffi:'ffi ffi_state) b rs types' s env.
     repl_types b (ffi,rs) (types',s,env) ==>
       ALL (ref_lookup_ok (semanticPrimitives_state_refs s)) rs /\
       (!decs new_t new_s res.
         infertype_prog_inc types' decs = M_success new_t /\
         evaluate_evaluate_decs s env decs = (new_s,res) ==> ~(res = Rerr
           (Rabort Rtype_error)))`,
  CHEAT_TAC);;

(* and the names it reads as variables are constants again *)
let _ = do_list unhide_constant
  ["id"];;

(* and the interface *)
let _ = unhide_overloads ();;
