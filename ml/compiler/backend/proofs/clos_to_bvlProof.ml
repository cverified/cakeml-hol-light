(* ======================================================== *)
(*  clos_to_bvlProof: ported from HOL4's
    compiler/backend/proofs/clos_to_bvlProofScript.sml  *)
(* ======================================================== *)

(*
  Correctness proof for clos_to_bvl
*)

needs "basis/pure/mlstring.ml";;
needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/bvl_const.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/clos_annotate.ml";;
needs "compiler/backend/clos_call.ml";;
needs "compiler/backend/clos_known.ml";;
needs "compiler/backend/clos_mti.ml";;
needs "compiler/backend/clos_number.ml";;
needs "compiler/backend/clos_to_bvl.ml";;
needs "compiler/backend/pattern_matching/pattern_semantics.ml";;
needs "compiler/backend/proofs/bvi_letProof.ml";;
needs "compiler/backend/semantics/backendProps.ml";;
needs "compiler/backend/semantics/closProps.ml";;
needs "compiler/backend/semantics/closSem.ml";;
needs "lib/sptree.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;
needs "semantics/semanticPrimitives.ml";;

needs "basis/pure/mlstring.ml";;
needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/bvl_const.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/clos_annotate.ml";;
needs "compiler/backend/clos_call.ml";;
needs "compiler/backend/clos_known.ml";;
needs "compiler/backend/clos_mti.ml";;
needs "compiler/backend/clos_number.ml";;
needs "compiler/backend/clos_to_bvl.ml";;
needs "compiler/backend/pattern_matching/pattern_semantics.ml";;
needs "compiler/backend/proofs/bvi_letProof.ml";;
needs "compiler/backend/semantics/backendProps.ml";;
needs "compiler/backend/semantics/closProps.ml";;
needs "compiler/backend/semantics/closSem.ml";;
needs "lib/sptree.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;
needs "semantics/semanticPrimitives.ml";;
(* HOL4 ancestors outside the port: bvl_jumpProof clos_constantProof
   clos_mtiProof clos_numberProof clos_knownProof clos_annotateProof
   clos_callProof clos_fvsProof *)

(* TODO: move? *)

(* HOL4 ML code, not ported:
val EVERY2_GENLIST = LIST_REL_GENLIST |> EQ_IMP_RULE |> snd |> Q.GEN`l`
*)

(* HOL4 ML code, not ported:
val ARITH_TAC = intLib.ARITH_TAC;
*)

(* -- *)

(* correctness of partial/over application *)

let global_table_def = cake_define
  `global_table max_app =
     Block tuple_tag
       (FLAT (GENLIST (\tot. GENLIST
         (\prev. bvlSem_CodePtr (partial_app_fn_location max_app
           tot prev)) tot) max_app))`;;

let unpack_closure = cake_inductive
  `(
    total_args >= 0 ==>
    unpack_closure (Block closure_tag (bvlSem_CodePtr l :: Number
      total_args :: fvs))
          ([],num_of_int total_args,Block closure_tag (bvlSem_CodePtr
            l :: Number total_args :: fvs))) /\
   (
    ~(prev_args = []) /\
    rem_args >= 0 ==>
    unpack_closure (Block partial_app_tag (bvlSem_CodePtr l :: Number
      rem_args :: clo :: prev_args))
          (prev_args,num_of_int rem_args + LENGTH prev_args,clo))`;;

(* -- *)

(* value relation *)

let code_installed_def = cake_define
  `clos_to_bvlProof_code_installed aux code =
     EVERY (\(n,num_args,exp). sptree_lookup n code = SOME
       (num_args,exp)) aux`;;

let closure_code_installed_def = cake_define
  `closure_code_installed max_app code exps_ps (env:closSem_v list) =
     EVERY (\((n,exp),p).
       n <= max_app /\ ~(
       n = 0) /\
       (?aux c aux1.
         (clos_to_bvl_compile_exps max_app [exp] aux = ([c],aux1)) /\
         (sptree_lookup p code = SOME (n + 1,SND (code_for_recc_case
           (LENGTH env + LENGTH exps_ps) n c))) /\
         clos_to_bvlProof_code_installed aux1 code)) exps_ps`;;

let cl_rel = cake_inductive
  `(
    num_args <= max_app /\ ~(
     num_args = 0) /\
     every_Fn_SOME [x] /\
     every_Fn_vs_SOME [x] /\
     (clos_to_bvl_compile_exps max_app [x] aux = ([c],aux1)) /\
     clos_to_bvlProof_code_installed aux1 code /\
     (sptree_lookup (p + (num_stubs max_app)) code =
       SOME (num_args + (1:num),Let (GENLIST Var num_args ++ free_let
         (Var num_args) (LENGTH env)) c)) ==>
    cl_rel max_app fs refs code
           (env,ys)
           (Closure (SOME p) [] env num_args x)
           (Block closure_tag (bvlSem_CodePtr (p + (num_stubs
             max_app)) :: Number (&(num_args - (&1))) :: ys))) /\
   (
     num_args <= max_app /\ ~(
     num_args = 0) /\
     every_Fn_SOME [x] /\
     every_Fn_vs_SOME [x] /\
     clos_to_bvl_compile_exps max_app [x] aux = ([c],aux1) /\
     clos_to_bvlProof_code_installed aux1 code /\
     sptree_lookup (p + (num_stubs max_app)) code =
       SOME (num_args + (1:num),Let (GENLIST Var (num_args + 1) ++
         free_let (Var num_args) (LENGTH env)) c) ==>
     cl_rel max_app fs refs code (env,ys)
            (Recclosure (SOME p) [] env [(num_args,x)] 0)
            (Block closure_tag (bvlSem_CodePtr (p + (num_stubs
              max_app)) :: Number (&(num_args - (&1))) :: ys))) /\
     ((exps = MAP FST exps_ps) /\
      (ps = MAP SND exps_ps) /\ (ps = GENLIST (\n. loc + (num_stubs
        max_app) + 2 * n) (LENGTH exps_ps)) /\
      (rs = MAP (\((n,e),p). Block closure_tag [bvlSem_CodePtr p;
        Number (&(n - (&1))); RefPtr T r]) exps_ps) /\
      ~(r IN fs) /\
      (FLOOKUP refs r = SOME (ValueArray (rs ++ ys))) /\
      1 < LENGTH exps /\ k < LENGTH exps /\
      every_Fn_SOME (MAP SND exps) /\
      every_Fn_vs_SOME (MAP SND exps) /\
      closure_code_installed max_app code exps_ps env ==>
      cl_rel max_app fs refs code (env,ys) (Recclosure (SOME loc)
        [] env exps k) (EL k rs))`;;

let add_args_def = cake_define
  `add_args x1 args' =
        match x1 with
          (Closure loc_opt args env num_args exp:closSem_v) ->
       SOME (Closure loc_opt (args' ++ args) env num_args exp)
        | (Recclosure loc_opt args env funs i:closSem_v) ->
       SOME (Recclosure loc_opt (args' ++ args) env funs i)
        | _1 -> NONE`;;

let get_num_args_def = cake_define
  `get_num_args x1 =
        match x1 with
          (Closure loc_opt args env num_args exp:closSem_v) ->
       SOME num_args
        | (Recclosure loc_opt args env funs i:closSem_v) ->
       SOME (FST (EL i funs))
        | _2 -> NONE`;;

let v_rel = cake_inductive
  `(v_rel max_app f refs code (Number n) (Number n)) /\
   (v_rel max_app f refs code (Word64 w) (Word64 w)) /\
   (EVERY2 (v_rel max_app f refs code) xs (ys:bvlSem_v list) ==>
    v_rel max_app f refs code (Block t xs) (Block (clos_tag_shift t)
      ys)) /\
   (FLOOKUP refs p = SOME (ByteArray T bs) /\ ~(p IN FRANGE f) ==>
    v_rel max_app f refs code (closSem_ByteVector bs) (RefPtr T p))
      /\
   ((FLOOKUP f r1 = SOME r2) ==>
    v_rel max_app f refs code (RefPtr b r1) (RefPtr b r2)) /\
   (
    EVERY2 (v_rel max_app f refs code) env fvs /\
    cl_rel max_app (FRANGE f) refs code (env,fvs) cl (Block
      closure_tag (bvlSem_CodePtr p :: Number n :: ys)) ==>
    v_rel max_app f refs code cl (Block closure_tag (bvlSem_CodePtr p
      :: Number n :: ys))) /\
   (
    EVERY2 (v_rel max_app f refs code) env fvs /\
    EVERY2 (v_rel max_app f refs code) arg_env ys /\ ~(
    arg_env = []) /\
    LENGTH arg_env < num_args /\
    (sptree_lookup (partial_app_fn_location max_app (num_args - 1)
      (LENGTH ys - 1)) code =
      SOME (num_args - LENGTH arg_env +
        1,generate_partial_app_closure_fn (num_args - 1) (LENGTH ys -
        1))) /\
    add_args cl arg_env = SOME cl_app /\
    get_num_args cl = SOME num_args /\
    cl_rel max_app (FRANGE f) refs code (env,fvs) cl cl' ==>
    v_rel max_app f refs code cl_app
                        (Block partial_app_tag
                              (bvlSem_CodePtr
                                (partial_app_fn_location max_app
                                (num_args - 1) (LENGTH ys - 1)) ::
                              Number (&(num_args - (&1) - LENGTH
                                arg_env)) :: cl' :: ys)))`;;

let env_rel_def = cake_define
  `clos_to_bvlProof_env_rel max_app f refs code x5 ys =
        match (x5,ys) with
          ([],[]) -> T
        | ([],ys) -> T
        | ((x :: xs),[]) -> F
        | ((x :: xs),(y :: ys)) ->
        v_rel max_app f refs code x y /\ clos_to_bvlProof_env_rel
          max_app f refs code xs ys`;;

(* HOL4 ML code, not ported:
val env_rel_IMP_EL =
  LESS_LENGTH_env_rel_IMP |> SPEC_ALL |> UNDISCH
  |> CONJUNCT2 |> DISCH_ALL |> GEN_ALL;
*)

(*
Definition extract_name_def:
  extract_name [] = (0,[]) /\
  extract_name (x :: xs) =
    case (some n. ?t. x = Op t (IntOp (Const (& n))) []) of
    | NONE => (0,x::xs)
    | SOME n => (n, if xs = [] then [x] else xs)
End

Definition compile_inc_def:
  compile_inc max_app (es,prog) =
    let (n,real_es) = extract_name es in
        clos_to_bvl$compile_prog max_app
          (clos_to_bvl$chain_exps n real_es ++ prog)
    : (num, num # exp) alist
End
*)

let nth_code_def = cake_define_list
  [`nth_code t_co 0 = LN`;
   `nth_code t_co (SUC n) =
      sptree_union (fromAList (SND (t_co 0))) (nth_code
        (misc_shift_seq 1 t_co) n)`];;

let compile_oracle_inv_def = cake_define
  `compile_oracle_inv max_app s_code s_cc s_co t_code t_cc t_co <=>
      s_cc = pure_cc (compile_inc max_app) t_cc /\
      t_co = pure_co (compile_inc max_app) o s_co /\
      (!n cfg ps. t_co n = (cfg,ps) ==> ALL_DISTINCT (MAP FST ps)) /\
      (!n. DISJOINT (domain (sptree_union t_code (nth_code t_co n)))
             (set_of_list (MAP FST (SND (t_co n))))) /\
      (!n cfg e ps.
        s_co n = (cfg,e,ps) ==>
        every_Fn_SOME e /\ every_Fn_vs_SOME e /\
        EVERY (\p. every_Fn_SOME [SND (SND p)]) ps /\
        EVERY (\p. every_Fn_vs_SOME [SND (SND p)]) ps)`;;

(*
val dummy_compile_oracle_inv = mk_var("compile_oracle_inv",
  type_of(#1(strip_comb(lhs(concl(SPEC_ALL compile_oracle_inv_def))))))
Definition compile_oracle_inv_def:
  ^dummy_compile_oracle_inv max_app s_code s_cc s_co t_code t_cc t_co ⇔
    T
End
*)

let ref_rel_def = cake_define
  `clos_to_bvlProof_ref_rel R x2 x3 =
        match (x2,x3) with
          (closSem_ValueArray vs,bvlSem_ValueArray ws) -> LIST_REL R
            vs ws
        | ((closSem_Thunk m1 v),(bvlSem_Thunk m2 w)) -> m1 = m2 /\ R
          v w
        | ((ByteArray as),(ByteArray g bs)) -> ~g /\ as = bs
        | (_3,_4) -> F`;;
hol4_overload "ref_rel" "clos_to_bvlProof_ref_rel";;

let state_rel_def = cake_define
  `clos_to_bvlProof_state_rel f (s:('c,'ffi)closSem_state)
  (t:('c,'ffi)bvlSem_state) <=>
     (?_ffi s = ?_ffi t) /\
     LIST_REL (OPTREL (v_rel (?_max_app s) f (?_refs t) (?_code t)))
       (?_globals s) (DROP num_added_globals (?_globals t)) /\
     get_global 0 (?_globals t) = SOME (SOME (global_table (?_max_app
       s))) /\
     INJ ((FAPPLY) f) (FDOM f) (FRANGE f) /\
     (!x y bs. FLOOKUP f x = SOME y ==> ~(FLOOKUP (?_refs t) y = SOME
       (ByteArray T bs))) /\
     (FDOM f = FDOM (?_refs s)) /\
     (FRANGE f SUBSET FDOM (?_refs t)) /\
     (!n x. (FLOOKUP (?_refs s) n = SOME x) ==>
            (?y m. (FLOOKUP f n = SOME m) /\
                  (FLOOKUP (?_refs t) m = SOME y) /\
                  ref_rel (v_rel (?_max_app s) f (?_refs t) (?_code
                    t)) x y)) /\
     (!n. n < ?_max_app s ==>
          sptree_lookup (generic_app_fn_location n) (?_code t) = SOME
            (n + 2,generate_generic_app (?_max_app s) n)) /\
     (!tot n. tot < ?_max_app s /\ n < tot ==>
       sptree_lookup (partial_app_fn_location (?_max_app s) tot n)
         (?_code t) = SOME (tot - n + 1,generate_partial_app_closure_fn
         tot n)) /\
     sptree_lookup (num_stubs (?_max_app s) - 2) (?_code t) = SOME
       (2,force_thunk_code) /\
     compile_oracle_inv (?_max_app s) (?_code s) (?_compile s)
       (?_compile_oracle s) (?_code
                              t) (?_compile t) (?_compile_oracle t)
                                /\
     (!name arity c.
       (FLOOKUP (?_code s) name = SOME (arity,c)) ==>
       (?aux1 c2 aux2.
         (clos_to_bvl_compile_exps (?_max_app s) [c] aux1 =
           ([c2],aux2)) /\
         (sptree_lookup (name + (num_stubs (?_max_app s))) (?_code t)
           = SOME (arity,c2)) /\
         clos_to_bvlProof_code_installed aux2 (?_code t)))`;;

(* HOL4 ML code, not ported:
val v_rel_SUBMAP = Q.prove(
  `!x y. v_rel max_app f1 refs1 code x y ==>
      f1 SUBMAP f2 /\ FDIFF refs1 (FRANGE f1) SUBMAP FDIFF refs2 (FRANGE
        f2) ==>
      v_rel max_app f2 refs2 code x y`,
  HO_MATCH_MP_TAC v_rel_ind \\ REPEAT STRIP_TAC
  \\ ONCE_REWRITE_TAC [v_rel_cases] \\ full_simp_tac(srw_ss())[]
  THEN1 (REPEAT (POP_ASSUM MP_TAC) \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\
    full_simp_tac(srw_ss())[])
  THEN1 ( fs[SUBMAP_DEF,FLOOKUP_DEF,FDIFF_def,DRESTRICT_DEF] )
  THEN1 (fs[SUBMAP_DEF,FLOOKUP_DEF] )
  THEN1 (imp_res_tac SUBMAP_FRANGE >>
         imp_res_tac cl_rel_SUBMAP >>
         disj2_tac >>
         full_simp_tac(srw_ss())[ETA2_THM] >>
         metis_tac [])
  THEN1 (imp_res_tac cl_rel_SUBMAP >>
         disj2_tac >>
         full_simp_tac(srw_ss())[ETA2_THM] >>
         metis_tac [SUBMAP_FRANGE] ))
  |> SPEC_ALL |> MP_CANON;
*)

(* HOL4 ML code, not ported:
val env_rel_SUBMAP = Q.prove(
  `!env1 env2.
      env_rel max_app f1 refs1 code env1 env2 /\
      f1 SUBMAP f2 /\ FDIFF refs1 (FRANGE f1) SUBMAP FDIFF refs2 (FRANGE
        f2) ==>
      env_rel max_app f2 refs2 code env1 env2`,
  Induct \\ Cases_on `env2` \\ full_simp_tac(srw_ss())[env_rel_def]
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC v_rel_SUBMAP) |> GEN_ALL;
*)

(* HOL4 ML code, not ported:
val v_rel_NEW_REF = Q.prove(
  `!x y. v_rel max_app f1 refs1 code x y ==> ~(r IN FDOM refs1) ==>
          v_rel max_app f1 (refs1 |+ (r,t)) code x y`,
  HO_MATCH_MP_TAC v_rel_ind \\ REPEAT STRIP_TAC
  \\ ONCE_REWRITE_TAC [v_rel_cases] \\ full_simp_tac(srw_ss())[]
  THEN1 (REPEAT (POP_ASSUM MP_TAC) \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\
    full_simp_tac(srw_ss())[])
  THEN1 (rw[FLOOKUP_UPDATE] \\ fs[FLOOKUP_DEF])
  THEN1 (imp_res_tac cl_rel_NEW_REF >>
         disj2_tac >>
         full_simp_tac(srw_ss())[ETA2_THM] >>
         metis_tac [])
  THEN1 (imp_res_tac cl_rel_NEW_REF >>
         disj2_tac >>
         full_simp_tac(srw_ss())[ETA2_THM] >>
         metis_tac [] ))
  |> SPEC_ALL |> MP_CANON;
*)

(* HOL4 ML code, not ported:
val v_rel_UPDATE_REF = Q.prove(
  `!x y. v_rel max_app f1 refs1 code x y ==>
          (r IN FRANGE f1) ==>
          v_rel max_app f1 (refs1 |+ (r,t)) code x y`,
  HO_MATCH_MP_TAC v_rel_ind \\ REPEAT STRIP_TAC
  \\ ONCE_REWRITE_TAC [v_rel_cases] \\ full_simp_tac(srw_ss())[]
  THEN1 (REPEAT (POP_ASSUM MP_TAC) \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\
    full_simp_tac(srw_ss())[])
  THEN1 ( rw[FLOOKUP_UPDATE] \\ fs[FLOOKUP_DEF] )
  THEN1 (imp_res_tac cl_rel_UPDATE_REF >>
         disj2_tac >>
         full_simp_tac(srw_ss())[ETA2_THM] >>
         metis_tac [])
  THEN1 (imp_res_tac cl_rel_UPDATE_REF >>
         disj2_tac >>
         full_simp_tac(srw_ss())[ETA2_THM] >>
         metis_tac [] ))
  |> SPEC_ALL |> MP_CANON;
*)

(* HOL4 ML code, not ported:
val v_rel_NEW_F = Q.prove(
  `!x y.
      v_rel max_app f2 t2.refs t2.code x y ==>
      ~(pp IN FDOM f2) ==>
      ~(qq IN FDOM t2.refs) ==>
      v_rel max_app (f2 |+ (pp,qq)) t2.refs t2.code x y`,
  HO_MATCH_MP_TAC v_rel_ind \\ REPEAT STRIP_TAC
  \\ ONCE_REWRITE_TAC [v_rel_cases] \\ full_simp_tac(srw_ss())[]
  THEN1 (REPEAT (POP_ASSUM MP_TAC) \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\
    full_simp_tac(srw_ss())[])
  THEN1 ( fs[IN_FRANGE,FLOOKUP_DEF,DOMSUB_FAPPLY_THM] \\ metis_tac[] )
  THEN1 (full_simp_tac(srw_ss())[FLOOKUP_UPDATE] \\ SRW_TAC [] [] \\
    full_simp_tac(srw_ss())[FLOOKUP_DEF])
  THEN1 (imp_res_tac cl_rel_NEW_F >>
         disj2_tac >>
         full_simp_tac(srw_ss())[ETA2_THM,DOMSUB_NOT_IN_DOM] >>
         metis_tac [])
  THEN1 (imp_res_tac cl_rel_NEW_F >>
         disj2_tac >>
         full_simp_tac(srw_ss())[ETA2_THM,DOMSUB_NOT_IN_DOM] >>
         metis_tac [] ))
  |> SPEC_ALL |> MP_CANON;
*)

(* HOL4 ML code, not ported:
val OPTREL_v_rel_NEW_F = Q.prove(
  `OPTREL (v_rel max_app f2 t2.refs t2.code) x y ==>
    ~(pp IN FDOM f2) ==>
    ~(qq IN FDOM t2.refs) ==>
    OPTREL (v_rel max_app (f2 |+ (pp,qq)) t2.refs t2.code) x y`,
  Cases_on `x` \\ Cases_on `y` \\ full_simp_tac(srw_ss())[OPTREL_def]
  \\ METIS_TAC [v_rel_NEW_F]) |> MP_CANON;
*)

(* semantic functions respect relation *)

(* HOL4 ML code, not ported:
val r = mk_var("r",``:num |-> 'a ref``);
*)

(* HOL4 ML code, not ported:
fun cases_on_op q = Cases_on q >|
  map (MAP_EVERY Cases_on) [[], [], [], [], [`b`], [`g`], [`m`], [],
    [`t`]];
*)

(* HOL4 ML code, not ported:
val v_case_eq_thms =
  LIST_CONJ [
    TypeBase.case_eq_of ``:closSem$v``,
    TypeBase.case_eq_of ``:bvlSem$v``];
*)

(* correctness of implemented primitives *)

let eq_res_def = cake_define
  `eq_res x1 =
      match x1 with
        Eq_val b -> Rval [bvlSem_Boolv b]
      | _5 -> Rerr (Rabort Rtype_error)`;;

(* HOL4 ML code, not ported:
val s = ``s:('c,'ffi) bvlSem$state``
*)

(* compiler correctness *)

(* HOL4 ML code, not ported:
val lookup_vars_IMP2 = Q.prove(
  `!vs env xs env2.
      (lookup_vars vs env = SOME xs) /\
      env_rel max_app f refs code env env2 ==>
      ?ys. (!t1. (evaluate (MAP Var vs,env2,t1) = (Rval ys,t1))) /\
           EVERY2 (v_rel max_app f refs code) xs ys /\
           (LENGTH vs = LENGTH xs)`,
  Induct \\ full_simp_tac(srw_ss())[lookup_vars_def,evaluate_def]
  \\ REPEAT STRIP_TAC
  \\ Cases_on `lookup_vars vs env` \\ full_simp_tac(srw_ss())[] \\
    SRW_TAC [] []
  \\ ONCE_REWRITE_TAC [evaluate_CONS]
  \\ full_simp_tac(srw_ss())[evaluate_def]
  \\ RES_TAC \\ IMP_RES_TAC LESS_LENGTH_env_rel_IMP \\
    full_simp_tac(srw_ss())[])
  |> INST_TYPE[alpha|->``:'c``,beta|->``:'ffi``];
*)

let num_remaining_args_def = cake_define
  `num_remaining_args x1 =
        match x1 with
          (Closure loc_opt args env num_args exp:closSem_v) ->
       SOME (num_args - LENGTH args)
        | (Recclosure loc_opt args env funs i:closSem_v) ->
       SOME (FST (EL i funs) - LENGTH args)
        | _6 -> NONE`;;

let get_loc_def = cake_define
  `get_loc x1 =
        match x1 with
          (Closure (SOME loc) args env num_args exp:bvlSem_v) -> SOME
            loc
        | (Recclosure (SOME loc) args env fns i) -> SOME (loc + 2 *
          i)
        | _7 -> NONE`;;

let get_old_args_def = cake_define
  `get_old_args x1 =
        match x1 with
          (Closure loc args env num_args exp:bvlSem_v) -> SOME args
        | (Recclosure loc args env fns i) -> SOME args
        | _8 -> NONE`;;

let get_cl_env_def = cake_define
  `get_cl_env x1 =
        match x1 with
          (Closure loc args env num_args exp:bvlSem_v) -> SOME env
        | (Recclosure loc args env fns i) -> SOME env
        | _9 -> NONE`;;

(* HOL4 ML code, not ported:
val unpack_closure_thm = Q.prove (
  `v_rel max_app f1 t1.refs t1.code func (Block tag (ptr::Number
    (&n-1)::rest)) ∧
   num_remaining_args func = SOME n
   ⇒
   ?prev_args total_args clo.
     unpack_closure (Block tag (ptr::Number (&n-1)::rest)) (prev_args,
       total_args, clo) ∧
     total_args < max_app ∧
     n = total_args − LENGTH prev_args + 1  ∧
     (tag = closure_tag ⇒ prev_args = [] ∧ clo = Block tag (ptr::Number
       (&n-1)::rest))`,
  srw_tac[][unpack_closure_cases, v_rel_cases, cl_rel_cases,
    num_remaining_args_def] >>
  full_simp_tac(srw_ss())[num_remaining_args_def] >>
  rw_tac bool_ss [] >>
  TRY ARITH_TAC >>
  full_simp_tac(srw_ss())[EL_MAP] >>
  `?n e p. EL k exps_ps = ((n,e),p)` by metis_tac [pair_CASES] >>
  full_simp_tac(srw_ss())[closure_code_installed_def, EVERY_EL] >>
  res_tac >>
  rev_full_simp_tac(srw_ss())[] >>
  TRY ARITH_TAC >>
  srw_tac [boolSimps.DNF_ss] [partial_app_tag_def,
    int_arithTheory.INT_NUM_SUB] >>
  imp_res_tac EVERY2_LENGTH >>
  full_simp_tac(srw_ss())[add_args_def, get_num_args_def, EL_MAP] >>
  TRY ARITH_TAC >>
  srw_tac [boolSimps.DNF_ss] [partial_app_tag_def,
    int_arithTheory.INT_NUM_SUB] >>
  TRY decide_tac >>
  TRY (Cases_on `ys`) >>
  full_simp_tac(srw_ss())[ADD1, num_remaining_args_def] >>
  srw_tac [ARITH_ss] [integerTheory.int_ge,
    integerTheory.INT_LE_SUB_LADD, integerTheory.INT_LE_LT1] >>
  TRY(simp[closure_tag_def]>>NO_TAC) >>
  first_x_assum (fn th => first_assum (mp_tac o MATCH_MP th)) >>
  srw_tac[][EL_MAP] >>
  decide_tac) |> INST_TYPE[alpha|->``:'ffi``];
*)

(* HOL4 ML code, not ported:
val closure_tag_neq_1 = EVAL``closure_tag = 1``|>EQF_ELIM
*)

(* HOL4 ML code, not ported:
val cEval_def = closSemTheory.evaluate_def;
val cEval_SING = closPropsTheory.evaluate_SING;
val bEval_def = bvlSemTheory.evaluate_def;
val bEval_CONS = bvlPropsTheory.evaluate_CONS;
val bEval_SING = bvlPropsTheory.evaluate_SING;
val bEval_APPEND = bvlPropsTheory.evaluate_APPEND;
val bEvalOp_def = bvlSemTheory.do_app_def;
*)

(* Differs from check_loc and dest_closure by not checking that max_app
   *)
let check_loc'_def = cake_define_list
  [`check_loc' NONE loc num_params num_args so_far <=> T`;
   `check_loc' (SOME p) loc num_params num_args so_far <=>
        (num_params = num_args) /\ (so_far = (0:num)) /\ (SOME p
          = loc)`];;

let dest_closure'_def = cake_define
  `dest_closure' loc_opt f args =
     (match f with Closure loc arg_env clo_env num_args exp ->
         (if check_loc' loc_opt loc num_args (LENGTH args) (LENGTH
           arg_env) /\ LENGTH arg_env < num_args then
           if ~(LENGTH args + LENGTH arg_env < num_args) then
             SOME (Full_app exp
                            (REVERSE (TAKE (num_args - LENGTH
                              arg_env) (REVERSE args)) ++
                             arg_env ++ clo_env)
                            (REVERSE (DROP (num_args - LENGTH
                              arg_env) (REVERSE args)))) else
             SOME (Partial_app (Closure loc (args ++ arg_env) clo_env
               num_args exp)) else
           NONE) | Recclosure loc arg_env clo_env fns i ->
         (let (num_args,exp) = EL i fns in
           if LENGTH fns <= i \/
              ~(check_loc' loc_opt (OPTION_MAP ((+) (2 * i)) loc)
                num_args (LENGTH args) (LENGTH arg_env)) \/
              ~(LENGTH arg_env < num_args) then NONE else
             let rs = GENLIST (Recclosure loc [] clo_env fns) (LENGTH
               fns) in
               if ~(LENGTH args + LENGTH arg_env < num_args) then
                 SOME (Full_app exp
                              (REVERSE (TAKE (num_args - LENGTH
                                arg_env) (REVERSE args)) ++
                              arg_env ++ rs ++ clo_env)
                              (REVERSE (DROP (num_args - LENGTH
                                arg_env) (REVERSE args)))) else
                 SOME (Partial_app (Recclosure loc (args ++
                   arg_env) clo_env fns i))) | _10 -> NONE)`;;

(* HOL4 ML code, not ported:
val cl_rel_run_lemma2 = Q.prove (
  `num_args ≤ LENGTH args'
   ⇒
   evaluate (GENLIST Var (num_args + 1), DROP (LENGTH args' - num_args)
     args' ++ [f] ++ stuff, t1) =
   (Rval (DROP (LENGTH args' - num_args) args' ++ [f]), t1)`,
  srw_tac[][] >>
  assume_tac (Q.SPECL [`0`, `DROP (LENGTH args' - num_args)
    args'++[f]++stuff`, `num_args+1`, `t1`] evaluate_genlist_vars) >>
  rev_full_simp_tac(srw_ss())[] >>
  rpt (pop_assum mp_tac) >>
  srw_tac [ARITH_ss] [ETA_THM] >>
  `LENGTH (DROP (LENGTH args' - num_args) args'++[f]) = num_args+1` by
    srw_tac [ARITH_ss] [] >>
  metis_tac [TAKE_LENGTH_APPEND]) |> Q.INST [`stuff`|-> `[]`] |>
    SIMP_RULE (srw_ss()) [];
*)

(* HOL4 ML code, not ported:
val bEval_free_let_Block = Q.prove (
  `!ys zs.
    evaluate ([x],env,s) = (Rval [Block n (y::z::ys ++ zs)], s)
    ⇒
    evaluate (free_let x (LENGTH ys),env,s) = (Rval ys,s)`,
  ho_match_mp_tac SNOC_INDUCT >>
  srw_tac[][free_let_def, bEval_def] >>
  full_simp_tac(srw_ss())[SNOC_APPEND] \\ FULL_SIMP_TAC std_ss [GSYM
    APPEND_ASSOC] >>
  res_tac >>
  full_simp_tac(srw_ss())[GENLIST, bvlPropsTheory.evaluate_SNOC,
    bEvalOp_def, bEval_def,
  do_int_app_def] >>
  simp [EL_CONS, PRE_SUB1, el_append3])
   |> Q.SPECL [`ys`,`[]`] |> SIMP_RULE std_ss [APPEND_NIL];
*)

(* HOL4 ML code, not ported:
val cl_rel_run_tac =
  qexists_tac `c` >>
  qexists_tac `aux` >>
  qexists_tac `aux1` >>
  imp_res_tac EVERY2_LENGTH >>
  full_simp_tac(srw_ss())[] >>
  srw_tac[][bEval_def, bEval_APPEND] >>
  rw_tac (std_ss) [GSYM APPEND_ASSOC] >>
  simp [cl_rel_run_lemma1, cl_rel_run_lemma2] >>
  `LENGTH (DROP (LENGTH args' − num_args) args') = num_args`
             by (srw_tac[][] >> decide_tac) >>
  qexists_tac `witness` >>
  srw_tac[][] >>
  `evaluate ([Var num_args], DROP (LENGTH args' − num_args) args' ++
    [func'],t1 with <| refs := refs; code := code |>)
      = (Rval [func'],t1 with <| refs := refs; code := code |>)`
          by (srw_tac[][bEval_def]
              >- metis_tac [EL_LENGTH_APPEND, NULL, HD]) >>
  simp [TAKE_REVERSE, LASTN_DROP] >>
  unabbrev_all_tac >>
  imp_res_tac bEval_free_let_Block >>
  rev_full_simp_tac(srw_ss())[] >>
  srw_tac[][] >>
  metis_tac [list_rel_IMP_env_rel, APPEND_ASSOC, LASTN_LENGTH_ID,
    env_rel_APPEND, LIST_REL_def, cl_rel_run_lemma3];
*)

(* HOL4 ML code, not ported:
val v_rel_run = Q.prove (
  `!f1 refs code args args' env' ptr body newenv func func' rest tag n
    loc.
    LENGTH args ≠ 0 ∧
    func' = Block tag (CodePtr ptr::Number (&n)::env') ∧
    dest_closure max_app loc func args = SOME (Full_app body newenv
      rest) ∧
    v_rel max_app f1 refs code func func' ∧
    LIST_REL (v_rel max_app f1 refs code) args args'
    ⇒
    ∃ck' body' aux1 aux2 newenv' exp'.
      lookup ptr code = SOME (n + 2,exp') ∧
      compile_exps max_app [body] aux1 = ([body'],aux2) ∧ code_installed
        aux2 code ∧
      env_rel max_app f1 refs code newenv newenv' ∧
      !t1.
        evaluate ([exp'], DROP (LENGTH args' - (n + 1)) args' ++
          [func'], inc_clock ck' (t1 with <|refs := refs; code :=
          code|>)) =
        evaluate ([body'], newenv', (t1 with <| refs := refs; code :=
          code |>))`,
  srw_tac[][] >>
  qpat_x_assum `v_rel _ x0 x1 x2 x3 x4` (fn x => mp_tac x >> simp
    [v_rel_cases] >> assume_tac x) >>
  srw_tac[][] >>
  imp_res_tac EVERY2_LENGTH >>
  imp_res_tac cl_rel_get_loc
  >- (qexists_tac `0` >>
      srw_tac[][] >>
      imp_res_tac dest_cl_imp_dest_cl' >>
*)
      (* TODO: metis_tac[cl_rel_run] is not VALID here *)
(* HOL4 ML code, not ported:
      match_mp_tac cl_rel_run >> metis_tac[]) >>
  CONV_TAC (RESORT_EXISTS_CONV List.rev) >>
  qexists_tac `generate_partial_app_closure_fn (num_args − 1) (LENGTH ys
    − 1)` >>
  srw_tac [ARITH_ss] [] >>
  imp_res_tac cl_rel_dest >>
  srw_tac[][] >>
  `v_rel max_app f1 refs code cl (Block closure_tag (CodePtr l::Number
    (&num_args')::fvs'))`
            by (srw_tac[][v_rel_cases, partial_app_tag_def] >>
                metis_tac [closure_tag_def]) >>
  `LENGTH arg_env ≠ 0 ∧ LENGTH ys ≠ 0 ∧ LENGTH ys < num_args` by
    metis_tac [LENGTH_EQ_NUM] >>
  `LIST_REL (v_rel max_app f1 refs code) (args++arg_env) (args'++ys)`
             by metis_tac [EVERY2_APPEND] >>
  assume_tac (SIMP_RULE (srw_ss()) [GSYM AND_IMP_INTRO]
    dest_closure_full_of_part |> GEN_ALL) >>
  rpt (pop_assum (fn th => first_assum (assume_tac o MATCH_MP th))) >>
  strip_assume_tac (SIMP_RULE (srw_ss()) [GSYM AND_IMP_INTRO]
    cl_rel_run) >>
  full_simp_tac(srw_ss())[] >>
  rpt (pop_assum (fn x => first_assum (strip_assume_tac o MATCH_MP x)))
    >>
  MAP_EVERY qexists_tac [`new_env'`, `aux2`, `aux1`, `body'`] >>
  srw_tac[][] >>
  `?total_args. (&num_args'):int = &total_args - 1`
        by (qexists_tac `&num_args' + 1` >>
            srw_tac[][] >>
            ARITH_TAC) >>
  full_simp_tac(srw_ss())[] >>
  imp_res_tac cl_rel_get_num_args >>
  full_simp_tac(srw_ss())[] >>
  srw_tac[][] >>
  qexists_tac `1` >>
  srw_tac[][] >>
  full_simp_tac(srw_ss())[] >>
  `num_args' + 2 = LENGTH (DROP (LENGTH args' + LENGTH ys − num_args)
    args') + (LENGTH ys +1) ∧
   0 < LENGTH (DROP (LENGTH args' + LENGTH ys − num_args) args')`
            by (srw_tac[][LENGTH_DROP, SUB_LEFT_SUB] >>
                full_simp_tac(srw_ss())[LESS_OR_EQ] >>
                TRY ARITH_TAC >>
                `num_args' = num_args -1`  by ARITH_TAC >>
                simp [] >>
                imp_res_tac dest_closure_full_app >>
                `num_args'' = num_args ∧ LENGTH old_args = LENGTH ys`
                         by (Cases_on `cl` >>
                             full_simp_tac(srw_ss())[add_args_def] >>
                             qpat_x_assum `X = func` (assume_tac o GSYM)
                               >>
                             full_simp_tac(srw_ss())[get_old_args_def,
                               get_num_args_def] >>
                             srw_tac[][] >>
                             simp []) >>
                decide_tac) >>
  full_simp_tac bool_ss [] >>
  assume_tac (SIMP_RULE (srw_ss()++ARITH_ss) [GSYM AND_IMP_INTRO]
    evaluate_partial_app_fn) >>
  pop_assum (fn th => first_assum (mp_tac o MATCH_MP th)) >>
  full_simp_tac(srw_ss())[] >>
  srw_tac[][] >>
  full_simp_tac(srw_ss())[] >>
  full_simp_tac(srw_ss())[inc_clock_def] >>
  srw_tac[][] >>
  rev_full_simp_tac(srw_ss())[] >>
  pop_assum (qspecl_then [`Number (&num_args − 1)`,
                          `partial_app_tag`,
                          `Number (&(num_args − (LENGTH ys + 1)))`,
                          `closure_tag`,
                          `CodePtr (partial_app_fn_location max_app
                            (num_args − 1) (LENGTH ys − 1))`,
                          `fvs'`,
                          `t1 with <|refs:=refs;clock := t1.clock + 1;
                            code := code|>`] mp_tac) >>
  srw_tac[][partial_app_tag_def] >>
  srw_tac[][] >>
  srw_tac[][dec_clock_def] >>
  `t1 with <|clock := t1.clock; code := code|> = t1 with code := code`
         by srw_tac[][bvlSemTheory.state_component_equality] >>
  `LENGTH args' − (LENGTH args' + LENGTH ys − num_args) + LENGTH ys − 1
    = num_args -1` by ARITH_TAC >>
  full_simp_tac(srw_ss())[] >>
  `num_args' + 1 = num_args` by ARITH_TAC >>
  `LENGTH args' + LENGTH ys − (num_args' + 1) ≤ LENGTH args'` by
    ARITH_TAC >>
  first_x_assum (qspec_then `t1 with <| clock := t1.clock; code := code
    |>` mp_tac) >>
  full_simp_tac(srw_ss())[DROP_APPEND1] >>
  srw_tac[][dec_clock_def]) |>
    INST_TYPE[alpha|->``:'c``,beta|->``:'ffi``];
*)

(* HOL4 ML code, not ported:
val mk_call_simp2 = Q.prove(
  `!n args stuff stuff' v t.
    n ≤ LENGTH args ∧ LENGTH stuff' ≠ 0
    ⇒
    evaluate ([mk_cl_call (Var n) (GENLIST Var n)], (TAKE n args) ++ [v]
      ++ stuff, t)
    =
    evaluate ([mk_cl_call (Var 0) (GENLIST (\n. Var (n+1)) n)],
      v::(args++stuff'), t)`,
  strip_tac >>
  simp [mk_cl_call_def, bEval_def, bEvalOp_def, do_int_app_def,
    el_take_append] >>
  Cases_on `v` >>
  simp [] >>
  srw_tac[][] >>
  TRY (rename [`FLOOKUP t.refs rrr`] \\ Cases_on `FLOOKUP t.refs rrr` \\
    fs []
       \\ Cases_on `x`\\ fs [] \\ IF_CASES_TAC \\ fs []) >>
  srw_tac[][] >>
  Cases_on`EL 1 l`>>simp[do_eq_def]>>
  simp[bEval_APPEND] >>
  rename [`TAKE n args ++ [xxx] ++ stuff`] >>
  qspecl_then [`0`, `TAKE n args ++ [xxx] ++ stuff`, `n`]mp_tac
    evaluate_genlist_vars >>
  qspecl_then [`1`, `xxx::(args ++ stuff')`, `n`]mp_tac
    evaluate_genlist_vars >>
  srw_tac [ARITH_ss] [ETA_THM, bEval_def, bEvalOp_def,
    do_int_app_def,el_take_append] >>
  srw_tac[][] >>
  `n+1 ≤ SUC (LENGTH args + LENGTH stuff')` by decide_tac >>
  srw_tac [ARITH_ss] [TAKE_APPEND1, TAKE_TAKE, EL_CONS])
  |> INST_TYPE[alpha|->``:'c``,beta|->``:'ffi``];
*)

(* HOL4 ML code, not ported:
val s1 = ``s1:('c,'ffi) closSem$state``;
*)


(* HOL4 ML code, not ported:
val env_rel_ind = theorem"env_rel_ind";
*)

(* more correctness properties *)

(*
Theorem even_stubs3[local]:
  !max_app. EVEN (num_stubs max_app + 3)
Proof
  Induct_on `max_app` >>
  rw [num_stubs_def, EVEN_ADD, EVEN, GSYM EVEN_MOD2] >>
  metis_tac []
QED
  *)

(* HOL4 overload (expanded in the port):
     code_loc' = λe. code_locs [e] *)

(* HOL4 ML code, not ported:
val common_def = compile_common_def
    |> REWRITE_RULE [GSYM arithmeticTheory.EVEN_MOD2, GSYM
      make_even_def];
*)

(* Initial state *)
let clos_init_def = cake_define
  `clos_init max_app s <=> ?_globals
   s = [] /\ ?_refs s = FEMPTY /\ ?_code s = FEMPTY /\ ?_max_app s
     = max_app`;;

(* actually, this can be made even stronger *)

(*
Theorem compile_prog_stubs[local]:
  ∀ls ls' n m e new_e aux.
  MEM (n,m,e) ls ∧
  compile_prog max_app ls = ls' ∧
  compile_exps max_app [e] [] = (new_e,aux) ⇒
  MEM (n+(num_stubs max_app),m,HD new_e) ls' ∧
  IS_SUBLIST ls' aux
Proof
  Induct>>fs[FORALL_PROD,compile_prog_def]>>
  rw[]>>rpt(pairarg_tac>>fs[])>>
  imp_res_tac compile_exps_SING>>fs[]>>rveq>>fs[]>>
  res_tac>>fs[]>>
  Cases_on`aux`>>
  rfs[IS_SUBLIST]>>
  DISJ2_TAC>>
  metis_tac[IS_SUBLIST_APPEND2]
QED
*)

(* HOL4 ML code, not ported:
val evaluate_add_to_clock_io_events_mono_alt =
  closPropsTheory.evaluate_add_to_clock_io_events_mono
  |> SIMP_RULE std_ss [] |> CONJUNCT1 |> SPEC_ALL
  |> DISCH ``evaluate (es,env,s) = (res,s1:('c,'ffi) closSem$state)``
  |> SIMP_RULE std_ss [] |> GEN_ALL;
*)

(* HOL4 ML code, not ported:
val evaluate_add_to_clock_io_events_mono_alt_bvl =
  bvlPropsTheory.evaluate_add_to_clock_io_events_mono
  |> SIMP_RULE std_ss [] |> SPEC_ALL
  |> DISCH ``evaluate (exps,env,s) = (res,s1:('a,'b) bvlSem$state)``
  |> SIMP_RULE std_ss [] |> GEN_ALL;
*)

let eval_sim_def = cake_define
  `clos_to_bvlProof_eval_sim ffi max_app code1 co1 cc1 es1 code2 co2 cc2
  start rel =
     (!k res1 s2.
       evaluate (es1,[],initial_state ffi max_app code1 co1 cc1 k) =
         (res1,s2) /\ ~(
       res1 = Rerr (Rabort Rtype_error)) /\
       rel code1 co1 cc1 es1 code2 co2 cc2 start ==>
       (?ck res2 t2.
         bvlSem_evaluate ([Call 0 (SOME start) []],[],
           initial_state ffi code2 co2 cc2 (k + ck)) = (res2,t2) /\
         result_rel (\x y. T) (\x y. T) res1 res2 /\ ?_ffi s2 =
           ?_ffi t2))`;;
hol4_overload "eval_sim" "clos_to_bvlProof_eval_sim";;

let init_code_def = cake_define
  `clos_to_bvlProof_init_code code1 code2 max_app <=>
     (!n.
        n < max_app ==>
        sptree_lookup (generic_app_fn_location n) code2 =
        SOME (n + 2,generate_generic_app max_app n)) /\
     (!tot prev.
        tot < max_app /\ prev < tot ==>
        sptree_lookup (partial_app_fn_location max_app tot prev)
          code2 =
        SOME ((tot + 1) - prev,generate_partial_app_closure_fn tot
          prev)) /\
     (!name arity c.
       FLOOKUP code1 name = SOME (arity,c) ==>
       (?aux1 c2 aux2.
         clos_to_bvl_compile_exps max_app [c] aux1 = ([c2],aux2) /\
         sptree_lookup (name + num_stubs max_app) code2 = SOME
           (arity,c2) /\
         clos_to_bvlProof_code_installed aux2 code2))`;;
hol4_overload "init_code" "clos_to_bvlProof_init_code";;

let chain_installed_def = cake_define
  `chain_installed start (es:closLang_exp list) code <=>
     (!i. i < LENGTH es ==> closSem_find_code (start + i)
       ([]:closSem_v list) code =
          SOME ([],(if i + 1 < LENGTH es then Let
            backend_common_None [EL i es] (Call backend_common_None 0
            (start + i + 1) []) else EL i es)))`;;

(*
Theorem ALOOKUP_compile_prog_main:
   ∀max_app prog n a e.
   ALOOKUP prog n = SOME (a,e) ∧ ¬MEM n (code_locs (MAP (SND o SND)
     prog))
   ⇒
   ALOOKUP (compile_prog max_app prog) (n + num_stubs max_app) =
     SOME (a, HD(FST(compile_exps max_app [e] [])))
Proof
  recInduct compile_prog_ind
  \\ rw[compile_prog_def]
  \\ pairarg_tac \\ fs[]
  \\ reverse(fs[CaseEq"bool"] \\ rw[])
  >- (
    first_x_assum old_drule
    \\ rw[ALOOKUP_APPEND]
    \\ reverse CASE_TAC
    >- (
      imp_res_tac ALOOKUP_MEM
      \\ fs[MEM_MAP] \\ rw[] )
    \\ CASE_TAC
    >- (
      first_x_assum match_mp_tac
      \\ fs[Once code_locs_cons] )
    \\ imp_res_tac ALOOKUP_MEM
    \\ qspec_then`[]`mp_tac(CONV_RULE(RESORT_FORALL_CONV(sort_vars
      ["aux"]))compile_exps_code_locs)
    \\ simp[]
    \\ disch_then old_drule
    \\ disch_then(assume_tac o Q.AP_TERM`combin$C MEM`)
    \\ fs[MEM_MAP,FUN_EQ_THM]
    \\ fsrw_tac[DNF_ss][EQ_IMP_THM]
    \\ first_x_assum old_drule
    \\ simp[]
    \\ rw[]
    \\ fs[Once code_locs_cons] \\ fs[]
    \\ fs[code_locs_def] )
  \\ imp_res_tac compile_exps_SING \\ fs[]
QED

Theorem ALOOKUP_compile_prog_aux:
   ∀max_app prog start a e r aux.
   ALOOKUP prog start = SOME (a,e) ∧
   ALL_DISTINCT (MAP FST (compile_prog max_app prog)) ∧
   compile_exps max_app [e] [] = (r,aux) ⇒
   code_installed aux (fromAList (compile_prog max_app prog))
Proof
  rw[]
  \\ irule code_installed_fromAList_strong
  \\ rw[]
  \\ qhdtm_x_assum`ALL_DISTINCT`kall_tac
  \\ rpt(pop_assum mp_tac)
  \\ map_every qid_spec_tac[`start`,`r`,`aux`,`e`,`a`,`prog`,`max_app`]
  \\ recInduct compile_prog_ind
  \\ rw[compile_prog_def]
  \\ pairarg_tac \\ fs[]
  \\ fs[CaseEq"bool"] \\ rw[] \\ fs[] \\ rw[]
  \\ res_tac
  \\ metis_tac[IS_SUBLIST_APPEND, APPEND_ASSOC]
QED
*)

(* TODO: there's lots to move in this file *)

(*
Theorem ksyntax_ok_intro_multi:
   clos_knownProof$syntax_ok es ⇒ clos_knownProof$syntax_ok (intro_multi
     max_app es)
Proof
  fs[clos_knownProofTheory.syntax_ok_def]
  \\ fs[GSYM clos_mtiProofTheory.intro_multi_preserves_esgc_free]
  \\ fs[clos_knownProofTheory.fv_max_def, fv_exists]
  \\ fs[EVERY_MEM, MEM_EL, PULL_EXISTS,
    clos_mtiTheory.intro_multi_length]
  \\ qspecl_then[`max_app`,`es`]strip_assume_tac intro_multi_fv1
  \\ fs[LIST_REL_EL_EQN]
QED

Theorem ksyntax_ok_compile_mti:
   clos_knownProof$syntax_ok es ⇒
   clos_knownProof$syntax_ok (clos_mti$compile do_mti max_app es)
Proof
  Cases_on`do_mti` \\ rw[clos_mtiTheory.compile_def]
  \\ fs[ksyntax_ok_intro_multi]
QED
*)

let compile_common_inc_def = cake_define
  `compile_common_inc c cc =
   (pure_cc (cond_mti_compile_inc (clos_to_bvl_config_do_mti c)
     (?_max_app c))
     (state_cc (ignore_table clos_number_compile_inc)
       (known_cc (clos_to_bvl_config_known_conf c)
         (state_cc (cond_call_compile_inc (clos_to_bvl_config_do_call
           c))
           (pure_cc clos_annotate_compile_inc cc)))))`;;

let clos_state_cc_def = cake_define
  `clos_state_cc inc (cc:'b->closLang_exp list#(num#num#closLang_exp)
  list->(word8 list#word64 list#'b) option) = (state_cc inc
  cc:'a#'b->closLang_exp list#(num#num#closLang_exp) list->(word8
  list#word64 list#'a#'b) option)`;;

(* HOL4 ML code, not ported:
fun expand_tup_def tm = let
    val x_typ = type_of tm |> dest_type |> snd |> hd
    val x = mk_var ("x", x_typ)
    val thm = EVAL ``^tm (FST ^x, SND ^x)``
  in REWRITE_RULE [pairTheory.PAIR] thm end
*)

(* HOL4 ML code, not ported:
val fvs_inc = ``clos_fvs$compile_inc : clos_prog -> clos_prog``;
*)

(* HOL4 ML code, not ported:
val known_co_facts2 = known_co_facts
  |> SIMP_RULE bool_ss [LET_DEF]
  |> UNDISCH
  |> SIMP_RULE bool_ss [IMP_CONJ_THM, FORALL_AND_THM,
        clos_callProofTheory.syntax_ok_def]
  |> BODY_CONJUNCTS
  |> map IRULE_CANON
  |> map DISCH_ALL
  |> map GEN_ALL
*)

let compile_inc_post_kcompile_def = cake_define
  `compile_inc_post_kcompile c exps = compile
  (clos_to_bvl_config_known_conf c)
     (SND (renumber_code_locs_list
         (make_even (clos_to_bvl_config_next_loc c + MAX 1 (LENGTH
           exps)))
         (compile (clos_to_bvl_config_do_mti c) (?_max_app c)
           exps)))`;;

(* HOL4 ML code, not ported:
fun promote_bool pat thm = let
    val term = find_term (can (match_term pat)) (concl thm)
  in REWRITE_RULE [ASSUME term] thm |> DISCH_ALL end
*)

(* HOL4 ML code, not ported:
val semantics_kcompile = clos_knownProofTheory.semantics_compile
  |> promote_bool ``_ = clos_knownProof$known_cc _ _``
  |> promote_bool ``_ = clos_knownProof$known_co _ _``
  |> promote_bool ``clos_known$compile _ _ = _``;
*)

(* HOL4 ML code, not ported:
fun conseq xs = ConseqConv.CONSEQ_REWRITE_TAC (xs, [], [])
*)

(* HOL4 ML code, not ported:
val c0 = ``Call None 0 loc []``;
*)

let syntax_oracle_ok_def = cake_define
  `syntax_oracle_ok c c' es co <=>
    (!n. SND (SND (co n)) = []) /\
    (clos_to_bvl_config_do_mti c ==> 1 <= ?_max_app c /\ EVERY no_mti
      es /\
      (!n. EVERY no_mti (FST (SND (co n))))) /\
    (?v. FST (co 0) = (clos_to_bvl_config_next_loc c',
        option_val_approx_spt (clos_to_bvl_config_known_conf c'),FST
          (clos_to_bvl_config_call_state c'),v)) /\
    (clos_to_bvl_config_do_call c ==> every_Fn_vs_NONE es /\
        is_state_oracle clos_call_compile_inc
            (known_co (clos_to_bvl_config_known_conf c)
                (state_co (ignore_table clos_number_compile_inc)
                    (pure_co (cond_mti_compile_inc
                      (clos_to_bvl_config_do_mti c) (?_max_app c)) o
                      co)))) /\
    (IS_SOME (clos_to_bvl_config_known_conf c) ==>
        1 <= ?_max_app c /\ every_Fn_vs_NONE es /\
        oracle_monotonic (SET_OF_BAG o closProps_elist_globals o FST
          o SND) (<)
            (SET_OF_BAG (closProps_elist_globals es)) co /\
        is_state_oracle (clos_known_compile_inc (THE
          (clos_to_bvl_config_known_conf c)))
            ((\x y. strcat x y) pure_co (fvs_inc o
                state_co (ignore_table clos_number_compile_inc)
                    (pure_co (cond_mti_compile_inc
                      (clos_to_bvl_config_do_mti c) (?_max_app c)) o
                      co))) /\
        (!n'. BAG_ALL_DISTINCT (closProps_elist_globals (FST (SND (co
          n')))) /\
                EVERY closProps_esgc_free (FST (SND (co n'))))) /\
    ~contains_App_SOME (?_max_app c) es /\ syntax_ok es /\
    (!n. ~contains_App_SOME (?_max_app c) (FST (SND (co n))) /\
            every_Fn_vs_NONE (FST (SND (co n)))) /\
    is_state_oracle (ignore_table clos_number_compile_inc)
        (pure_co (cond_mti_compile_inc (clos_to_bvl_config_do_mti
          c) (?_max_app c)) o co)`;;

(* HOL4 ML code, not ported:
val compile_exps_code_locs2 = compile_exps_code_locs |> SPEC_ALL
  |> Q.GEN `aux` |> Q.SPEC `[]` |> SIMP_RULE list_ss [] |> GEN_ALL
*)

let extracted_addrs_def = cake_define
  `extracted_addrs exps = (if exps = [] then [0] else (match
  extract_name exps with
         (n,real_es) -> MAP ((+) n) (COUNT_LIST (MAX 1 (LENGTH
           real_es)))))`;;

let req_compile_inc_addrs_def = cake_define
  `req_compile_inc_addrs extra (exps,code) = extracted_addrs exps ++
     code_locs exps ++ MAP FST code ++ code_locs (MAP (SND o SND)
       code) ++
     FLAT (MAP (\f. MAP f (code_locs exps)) extra)`;;

let can_extract_def = cake_define
  `can_extract exps = (?t n exps'.
         exps = Op t (closLang_IntOp (closLang_Const (&n))) [] ::
           exps')`;;

(* HOL4 ML code, not ported:
fun mk_to_oracle t xsq = let
    val ty = type_of t;
    val (_, rty) = dom_rng ty;
    val ts = match_type rty ``:'s clos_co``
    val (orac1, orac2) = dest_abs (inst ts t)
  in subset_req_orac_to_oracle
    |> ISPECL [orac1, orac2] |> Q.SPEC xsq
  end
*)

(* HOL4 ML code, not ported:
val annotate_compile_inc_req_intros = UNDISCH_ALL
  annotate_compile_inc_req
  |> CONJUNCTS |> map (IRULE_CANON o DISCH_ALL)
*)

(* HOL4 ML code, not ported:
val annotate_compile_inc_req_oracle = mk_to_oracle
  ``\orac1. pure_co clos_annotate$compile_inc o orac1`` `[]`
*)

(* HOL4 ML code, not ported:
val cond_call_compile_inc_req_intros = UNDISCH_ALL
  cond_call_compile_inc_req
  |> CONJUNCTS |> map (IRULE_CANON o DISCH_ALL)
*)

(* HOL4 ML code, not ported:
val cond_call_compile_inc_req_oracle = mk_to_oracle
  ``\orac1. state_co (cond_call_compile_inc dc) orac1`` `[SUC]`
*)

(* HOL4 ML code, not ported:
val known_co_req_intros = UNDISCH_ALL known_co_req
  |> CONJUNCTS |> map (IRULE_CANON o DISCH_ALL)
*)

(* HOL4 ML code, not ported:
val known_co_req_oracle = mk_to_oracle
    ``\orac. clos_knownProof$known_co kc orac`` `[SUC]`
*)

(* HOL4 ML code, not ported:
val number_compile_inc_req_intros = number_compile_inc_req
  |> SIMP_RULE bool_ss [LET_THM]
  |> UNDISCH_ALL |> CONJUNCTS |> map (IRULE_CANON o DISCH_ALL)
*)

(* HOL4 ML code, not ported:
fun abbrev_adj_tac f = first_assum (fn t => if not
    (markerSyntax.is_abbrev (concl t)) then NO_TAC else
  let
    val (v, rhs) = dest_eq (rand (concl t))
    val (v_nm, _) = dest_var v
    val x = f rhs
    val v2 = mk_var (v_nm ^ "'", type_of x)
  in markerLib.ABBREV_TAC (mk_eq (v2, x)) \\ markerLib.UNABBREV_TAC v_nm
    end);
*)

(* TODO: move *)
