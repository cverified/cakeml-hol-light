(* ======================================================== *)
(*  clos_to_bvlProof: ported from HOL4's
    compiler/backend/proofs/clos_to_bvlProofScript.sml  *)
(* ======================================================== *)

(*
  Correctness proof for clos_to_bvl
*)

needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/bvl_const.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/clos_annotate.ml";;
needs "compiler/backend/clos_call.ml";;
needs "compiler/backend/clos_known.ml";;
needs "compiler/backend/clos_mti.ml";;
needs "compiler/backend/clos_number.ml";;
needs "compiler/backend/clos_to_bvl.ml";;
needs "compiler/backend/proofs/bvl_jumpProof.ml";;
needs "compiler/backend/proofs/clos_annotateProof.ml";;
needs "compiler/backend/proofs/clos_callProof.ml";;
needs "compiler/backend/proofs/clos_constantProof.ml";;
needs "compiler/backend/proofs/clos_fvsProof.ml";;
needs "compiler/backend/proofs/clos_knownProof.ml";;
needs "compiler/backend/proofs/clos_mtiProof.ml";;
needs "compiler/backend/proofs/clos_numberProof.ml";;
needs "compiler/backend/semantics/backendProps.ml";;
needs "compiler/backend/semantics/closProps.ml";;
needs "compiler/backend/semantics/closSem.ml";;
needs "lib/sptree.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "semantics/semanticPrimitives.ml";;

needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/bvl_const.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/clos_annotate.ml";;
needs "compiler/backend/clos_call.ml";;
needs "compiler/backend/clos_known.ml";;
needs "compiler/backend/clos_mti.ml";;
needs "compiler/backend/clos_number.ml";;
needs "compiler/backend/clos_to_bvl.ml";;
needs "compiler/backend/proofs/bvl_jumpProof.ml";;
needs "compiler/backend/proofs/clos_annotateProof.ml";;
needs "compiler/backend/proofs/clos_callProof.ml";;
needs "compiler/backend/proofs/clos_constantProof.ml";;
needs "compiler/backend/proofs/clos_fvsProof.ml";;
needs "compiler/backend/proofs/clos_knownProof.ml";;
needs "compiler/backend/proofs/clos_mtiProof.ml";;
needs "compiler/backend/proofs/clos_numberProof.ml";;
needs "compiler/backend/semantics/backendProps.ml";;
needs "compiler/backend/semantics/closProps.ml";;
needs "compiler/backend/semantics/closSem.ml";;
needs "lib/sptree.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "semantics/semanticPrimitives.ml";;

(* TODO: move? *)

(* HOL4 clos_to_bvlProofScript.sml:28: ML code, not ported *)

(* HOL4 clos_to_bvlProofScript.sml:197: ML code, not ported *)

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
    total_args >= (&0) ==>
    unpack_closure (Block closure_tag (bvlSem_CodePtr l :: Number
      total_args :: fvs))
          ([],num_of_int total_args,Block closure_tag (bvlSem_CodePtr
            l :: Number total_args :: fvs))) /\
   (
    ~(prev_args = []) /\
    rem_args >= (&0) ==>
    unpack_closure (Block partial_app_tag (bvlSem_CodePtr l :: Number
      rem_args :: clo :: prev_args))
          (prev_args,num_of_int rem_args + LENGTH prev_args,clo))`;;

(* -- *)

(* value relation *)

let code_installed_def = cake_define
  `clos_to_bvlProof_code_installed aux code =
     EVERY (\(n,num_args,exp). sptree_lookup n code = SOME
       (num_args,exp)) aux`;;
hol4_overload "code_installed" "clos_to_bvlProof_code_installed";;

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
             max_app)) :: Number (&(num_args - 1)) :: ys))) /\
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
              max_app)) :: Number (&(num_args - 1)) :: ys))) /\
     ((exps = MAP FST exps_ps) /\
      (ps = MAP SND exps_ps) /\ (ps = GENLIST (\n. loc + (num_stubs
        max_app) + 2 * n) (LENGTH exps_ps)) /\
      (rs = MAP (\((n,e),p). Block closure_tag [bvlSem_CodePtr p;
        Number (&(n - 1)); RefPtr T r]) exps_ps) /\
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
  `(clos_to_bvlProof_v_rel max_app f refs code (Number n) (Number n)) /\
   (clos_to_bvlProof_v_rel max_app f refs code (Word64 w) (Word64 w))
     /\
   (EVERY2 (clos_to_bvlProof_v_rel max_app f refs code) xs
     (ys:bvlSem_v list) ==>
    clos_to_bvlProof_v_rel max_app f refs code (Block t xs) (Block
      (clos_tag_shift t) ys)) /\
   (FLOOKUP refs p = SOME (ByteArray T bs) /\ ~(p IN FRANGE f) ==>
    clos_to_bvlProof_v_rel max_app f refs code (closSem_ByteVector
      bs) (RefPtr T p)) /\
   ((FLOOKUP f r1 = SOME r2) ==>
    clos_to_bvlProof_v_rel max_app f refs code (RefPtr b r1) (RefPtr
      b r2)) /\
   (
    EVERY2 (clos_to_bvlProof_v_rel max_app f refs code) env fvs /\
    cl_rel max_app (FRANGE f) refs code (env,fvs) cl (Block
      closure_tag (bvlSem_CodePtr p :: Number n :: ys)) ==>
    clos_to_bvlProof_v_rel max_app f refs code cl (Block closure_tag
      (bvlSem_CodePtr p :: Number n :: ys))) /\
   (
    EVERY2 (clos_to_bvlProof_v_rel max_app f refs code) env fvs /\
    EVERY2 (clos_to_bvlProof_v_rel max_app f refs code) arg_env ys /\
      ~(
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
    clos_to_bvlProof_v_rel max_app f refs code cl_app
                        (Block partial_app_tag
                              (bvlSem_CodePtr
                                (partial_app_fn_location max_app
                                (num_args - 1) (LENGTH ys - 1)) ::
                              Number (&(num_args - 1 - LENGTH
                                arg_env)) :: cl' :: ys)))`;;
hol4_overload "v_rel" "clos_to_bvlProof_v_rel";;

let env_rel_def = cake_define
  `clos_to_bvlProof_env_rel max_app f refs code x5 ys =
        match (x5,ys) with
          ([],[]) -> T
        | ([],ys) -> T
        | ((x :: xs),[]) -> F
        | ((x :: xs),(y :: ys)) ->
        v_rel max_app f refs code x y /\ clos_to_bvlProof_env_rel
          max_app f refs code xs ys`;;
hol4_overload "env_rel" "clos_to_bvlProof_env_rel";;

(* HOL4 clos_to_bvlProofScript.sml:1041-1043: ML code, not ported *)

(* HOL4 clos_to_bvlProofScript.sml:1045-1061: code that the source
   has in a comment *)

let nth_code_def = cake_define_list
  [`clos_to_bvlProof_nth_code t_co 0 = LN`;
   `clos_to_bvlProof_nth_code t_co (SUC n) =
      sptree_union (fromAList (SND (t_co 0)))
        (clos_to_bvlProof_nth_code (misc_shift_seq 1 t_co) n)`];;
hol4_overload "nth_code" "clos_to_bvlProof_nth_code";;

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

(* HOL4 clos_to_bvlProofScript.sml:1083-1089: code that the source
   has in a comment *)

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
     (state_ffi s = state_ffi t) /\
     LIST_REL (OPTREL (v_rel (closSem_state_max_app s) f (state_refs
       t) (state_code t))) (state_globals s) (DROP num_added_globals
       (state_globals t)) /\
     get_global 0 (state_globals t) = SOME (SOME (global_table
       (closSem_state_max_app s))) /\
     INJ ((FAPPLY) f) (FDOM f) (FRANGE f) /\
     (!x y bs. FLOOKUP f x = SOME y ==> ~(FLOOKUP (state_refs t) y =
       SOME (ByteArray T bs))) /\
     (FDOM f = FDOM (state_refs s)) /\
     (FRANGE f SUBSET FDOM (state_refs t)) /\
     (!n x. (FLOOKUP (state_refs s) n = SOME x) ==>
            (?y m. (FLOOKUP f n = SOME m) /\
                  (FLOOKUP (state_refs t) m = SOME y) /\
                  ref_rel (v_rel (closSem_state_max_app s) f
                    (state_refs t) (state_code t)) x y)) /\
     (!n. n < closSem_state_max_app s ==>
          sptree_lookup (generic_app_fn_location n) (state_code t) =
            SOME (n + 2,generate_generic_app (closSem_state_max_app s)
            n)) /\
     (!tot n. tot < closSem_state_max_app s /\ n < tot ==>
       sptree_lookup (partial_app_fn_location (closSem_state_max_app
         s) tot n) (state_code t) = SOME (tot - n +
         1,generate_partial_app_closure_fn tot n)) /\
     sptree_lookup (num_stubs (closSem_state_max_app s) - 2)
       (state_code t) = SOME (2,force_thunk_code) /\
     compile_oracle_inv (closSem_state_max_app s) (state_code s)
       (compile s) (compile_oracle s) (state_code
                              t) (compile t) (compile_oracle t) /\
     (!name arity c.
       (FLOOKUP (state_code s) name = SOME (arity,c)) ==>
       (?aux1 c2 aux2.
         (clos_to_bvl_compile_exps (closSem_state_max_app s) [c] aux1
           = ([c2],aux2)) /\
         (sptree_lookup (name + (num_stubs (closSem_state_max_app
           s))) (state_code t) = SOME (arity,c2)) /\
         clos_to_bvlProof_code_installed aux2 (state_code t)))`;;
hol4_overload "state_rel" "clos_to_bvlProof_state_rel";;

(* HOL4 clos_to_bvlProofScript.sml:1175-1193: a proof *)

(* HOL4 clos_to_bvlProofScript.sml:1195-1201: a proof *)

(* HOL4 clos_to_bvlProofScript.sml:1217-1232: a proof *)

(* HOL4 clos_to_bvlProofScript.sml:1250-1266: a proof *)

(* HOL4 clos_to_bvlProofScript.sml:1304-1323: a proof *)

(* HOL4 clos_to_bvlProofScript.sml:1325-1331: a proof *)

(* semantic functions respect relation *)

(* HOL4 clos_to_bvlProofScript.sml:1490: the ML values that the
   definitions below antiquote *)

(* HOL4 clos_to_bvlProofScript.sml:1527-1528: ML code, not ported *)

(* HOL4 clos_to_bvlProofScript.sml:1801-1804: ML code, not ported *)

(* correctness of implemented primitives *)

let eq_res_def = cake_define
  `eq_res x1 =
      match x1 with
        Eq_val b -> Rval [bvlSem_Boolv b]
      | _5 -> Rerr (Rabort Rtype_error)`;;

(* HOL4 clos_to_bvlProofScript.sml:1864: the ML values that the
   definitions below antiquote *)

(* compiler correctness *)

(* HOL4 clos_to_bvlProofScript.sml:1874-1887: a proof *)

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
          (Closure (SOME loc) args env num_args exp:closSem_v) ->
            SOME loc
        | (Recclosure (SOME loc) args env fns i) -> SOME (loc + 2 *
          i)
        | _7 -> NONE`;;

let get_old_args_def = cake_define
  `get_old_args x1 =
        match x1 with
          (Closure loc args env num_args exp:closSem_v) -> SOME args
        | (Recclosure loc args env fns i) -> SOME args
        | _8 -> NONE`;;

let get_cl_env_def = cake_define
  `get_cl_env x1 =
        match x1 with
          (Closure loc args env num_args exp:closSem_v) -> SOME env
        | (Recclosure loc args env fns i) -> SOME env
        | _9 -> NONE`;;

(* HOL4 clos_to_bvlProofScript.sml:2209-2240: a proof *)

(* HOL4 clos_to_bvlProofScript.sml:2277: the ML values that the
   definitions below antiquote *)

(* HOL4 clos_to_bvlProofScript.sml:2279-2285: ML code, not ported *)

(* Differs from check_loc and dest_closure by not checking that max_app
   *)
let check_loc'_def = cake_define_list
  [`check_loc' NONE loc num_params num_args so_far <=> T`;
   `check_loc' (SOME p) loc num_params num_args so_far <=>
        (num_params = num_args) /\ (so_far = (0:num)) /\ (SOME
          p = loc)`];;

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
             SOME (Partial_app (closSem_Closure loc (args ++ arg_env)
               clo_env num_args exp)) else
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
                 SOME (Partial_app (closSem_Recclosure loc (args
                   ++ arg_env) clo_env fns i))) | _10 -> NONE)`;;

(* HOL4 clos_to_bvlProofScript.sml:2420-2431: a proof *)

(* HOL4 clos_to_bvlProofScript.sml:2444-2456: a proof *)

(* HOL4 clos_to_bvlProofScript.sml:2458-2480: a proof *)

(* HOL4 clos_to_bvlProofScript.sml:2668-2690: a proof *)
(* HOL4 clos_to_bvlProofScript.sml:2691: code that the source has in
   a comment *)
(* HOL4 clos_to_bvlProofScript.sml:2692-2765: a proof *)

(* HOL4 clos_to_bvlProofScript.sml:2788-2812: a proof *)

(* HOL4 clos_to_bvlProofScript.sml:2831: the ML values that the
   definitions below antiquote *)


(* HOL4 clos_to_bvlProofScript.sml:2834: ML code, not ported *)

(* more correctness properties *)

(* HOL4 clos_to_bvlProofScript.sml:5880-5888: code that the source
   has in a comment *)

(* HOL4 clos_to_bvlProofScript.sml:5890: the overload code_loc',
   which the port expands *)

(* HOL4 clos_to_bvlProofScript.sml:5957-5958: ML code, not ported *)

(* Initial state *)
let clos_init_def = cake_define
  `clos_init max_app s <=> state_globals
   s = [] /\ state_refs s = FEMPTY /\ state_code s = FEMPTY /\
     closSem_state_max_app s = max_app`;;

(* actually, this can be made even stronger *)

(* HOL4 clos_to_bvlProofScript.sml:6106-6124: code that the source
   has in a comment *)

(* HOL4 clos_to_bvlProofScript.sml:6167-6171: ML code, not ported *)

(* HOL4 clos_to_bvlProofScript.sml:6173-6177: ML code, not ported *)

let eval_sim_def = cake_define
  `clos_to_bvlProof_eval_sim ffi max_app code1 co1 cc1 es1 code2 co2 cc2
  start' rel =
     (!k res1 s2.
       evaluate (es1,[],initial_state ffi max_app code1 co1 cc1 k) =
         (res1,s2) /\ ~(
       res1 = Rerr (Rabort Rtype_error)) /\
       rel code1 co1 cc1 es1 code2 co2 cc2 start' ==>
       (?ck res2 t2.
         bvlSem_evaluate ([Call 0 (SOME start') []],[],
           initial_state ffi code2 co2 cc2 (k + ck)) = (res2,t2) /\
         semanticPrimitivesProps_result_rel (\x y. T) (\x y. T)
           res1 res2 /\ state_ffi s2 = state_ffi t2))`;;
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
  `chain_installed start' (es:closLang_exp list) code <=>
     (!i. i < LENGTH es ==> closSem_find_code (start' + i)
       ([]:closSem_v list) code =
          SOME ([],(if i + 1 < LENGTH es then Let
            backend_common_None [EL i es] (Call backend_common_None 0
            (start' + i + 1) []) else EL i es)))`;;

(* HOL4 clos_to_bvlProofScript.sml:6572-6630: code that the source
   has in a comment *)

(* TODO: there's lots to move in this file *)

(* HOL4 clos_to_bvlProofScript.sml:6767-6786: code that the source
   has in a comment *)

let compile_common_inc_def = cake_define
  `compile_common_inc c cc =
   (pure_cc (cond_mti_compile_inc (clos_to_bvl_config_do_mti c)
     (clos_to_bvl_config_max_app c))
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

(* HOL4 clos_to_bvlProofScript.sml:7118-7122: the ML values that the
   definitions below antiquote *)

(* HOL4 clos_to_bvlProofScript.sml:7179: the ML values that the
   definitions below antiquote *)

(* HOL4 clos_to_bvlProofScript.sml:7285-7293: ML code, not ported *)

let compile_inc_post_kcompile_def = cake_define
  `compile_inc_post_kcompile c exps = compile
  (clos_to_bvl_config_known_conf c)
     (SND (renumber_code_locs_list
         (make_even (clos_to_bvl_config_next_loc c + MAX 1 (LENGTH
           exps)))
         (compile (clos_to_bvl_config_do_mti c)
           (clos_to_bvl_config_max_app c) exps)))`;;

(* HOL4 clos_to_bvlProofScript.sml:7489-7491: ML code, not ported *)

(* HOL4 clos_to_bvlProofScript.sml:7493-7496: ML code, not ported *)

(* HOL4 clos_to_bvlProofScript.sml:7498: ML code, not ported *)

(* HOL4 clos_to_bvlProofScript.sml:7500: the ML values that the
   definitions below antiquote *)

let syntax_oracle_ok_def = cake_define
  `clos_to_bvlProof_syntax_oracle_ok c c' es co <=>
    (!n. SND (SND (co n)) = []) /\
    (clos_to_bvl_config_do_mti c ==> 1 <= clos_to_bvl_config_max_app
      c /\ EVERY no_mti es /\
      (!n. EVERY no_mti (FST (SND (co n))))) /\
    (?v. FST (co 0) = (clos_to_bvl_config_next_loc c',
        option_val_approx_spt (clos_to_bvl_config_known_conf c'),FST
          (clos_to_bvl_config_call_state c'),v)) /\
    (clos_to_bvl_config_do_call c ==> every_Fn_vs_NONE es /\
        is_state_oracle clos_call_compile_inc
            (known_co (clos_to_bvl_config_known_conf c)
                (state_co (ignore_table clos_number_compile_inc)
                    (pure_co (cond_mti_compile_inc
                      (clos_to_bvl_config_do_mti c)
                      (clos_to_bvl_config_max_app c)) o co)))) /\
    (IS_SOME (clos_to_bvl_config_known_conf c) ==>
        1 <= clos_to_bvl_config_max_app c /\ every_Fn_vs_NONE es /\
        oracle_monotonic (SET_OF_BAG o closProps_elist_globals o FST
          o SND) (<)
            (SET_OF_BAG (closProps_elist_globals es)) co /\
        is_state_oracle (clos_known_compile_inc (THE
          (clos_to_bvl_config_known_conf c)))
            (pure_co (clos_fvs_compile_inc:closLang_exp
              list#(num#num#closLang_exp) list->closLang_exp
              list#(num#num#closLang_exp) list) o
                state_co (ignore_table clos_number_compile_inc)
                    (pure_co (cond_mti_compile_inc
                      (clos_to_bvl_config_do_mti c)
                      (clos_to_bvl_config_max_app c)) o co)) /\
        (!n'. BAG_ALL_DISTINCT (closProps_elist_globals (FST (SND (co
          n')))) /\
                EVERY closProps_esgc_free (FST (SND (co n'))))) /\
    ~contains_App_SOME (clos_to_bvl_config_max_app c) es /\
      clos_knownProof_syntax_ok es /\
    (!n. ~contains_App_SOME (clos_to_bvl_config_max_app c) (FST (SND
      (co n))) /\
            every_Fn_vs_NONE (FST (SND (co n)))) /\
    is_state_oracle (ignore_table clos_number_compile_inc)
        (pure_co (cond_mti_compile_inc (clos_to_bvl_config_do_mti
          c) (clos_to_bvl_config_max_app c)) o co)`;;
hol4_overload "syntax_oracle_ok" "clos_to_bvlProof_syntax_oracle_ok";;

(* HOL4 clos_to_bvlProofScript.sml:7836-7837: ML code, not ported *)

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

(* HOL4 clos_to_bvlProofScript.sml:7965-7972: the ML values that the
   definitions below antiquote *)

(* HOL4 clos_to_bvlProofScript.sml:8035-8036: ML code, not ported *)

(* HOL4 clos_to_bvlProofScript.sml:8038-8039: ML code, not ported *)

(* HOL4 clos_to_bvlProofScript.sml:8092-8093: ML code, not ported *)

(* HOL4 clos_to_bvlProofScript.sml:8095-8096: ML code, not ported *)

(* HOL4 clos_to_bvlProofScript.sml:8229-8230: ML code, not ported *)

(* HOL4 clos_to_bvlProofScript.sml:8232-8233: ML code, not ported *)

(* HOL4 clos_to_bvlProofScript.sml:8270-8272: ML code, not ported *)

(* HOL4 clos_to_bvlProofScript.sml:8476-8483: ML code, not ported *)

(* TODO: move *)
