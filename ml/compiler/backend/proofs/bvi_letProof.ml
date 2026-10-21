(* ======================================================== *)
(*  bvi_letProof: ported from HOL4's
    compiler/backend/proofs/bvi_letProofScript.sml  *)
(* ======================================================== *)

(*
  Correctness proof for bvi_let
*)

needs "basis/pure/mllist.ml";;
needs "basis/pure/mlstring.ml";;
needs "basis/pure/mlvector.ml";;
needs "compiler/backend/bvi_let.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/reg_alloc/linear_scan.ml";;
needs "compiler/backend/semantics/bviProps.ml";;
needs "compiler/backend/semantics/bviSem.ml";;
needs "compiler/backend/semantics/bvlProps.ml";;
needs "compiler/backend/semantics/closSem.ml";;
needs "lib/balanced_map.ml";;
needs "lib/binary_ieee.ml";;
needs "lib/errorMonad.ml";;
needs "lib/peg.ml";;
needs "lib/set_sep.ml";;
needs "lib/sptree.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "semantics/cmlPtreeConversion.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "semantics/typeSystem.ml";;
needs "translator/monadic/monad_base/ml_monadBase.ml";;

hol4_overload "compile" "bvi_let_compile";;

let v_rel_def = cake_define
  `bvi_letProof_v_rel a x y xs ys <=> (\l n. oEL n l) ys a = SOME x`;;
hol4_overload "v_rel" "bvi_letProof_v_rel";;

let env_rel_def = cake_define
  `bvi_letProof_env_rel x1 d e1 e2 =
        match (x1,e1,e2) with
          ([],e1,e2) -> (e1 = DROP d e2)
        | ((a :: rest),(x :: e1),(y :: e2)) ->
        bvi_letProof_v_rel a x y (x :: e1) (y :: e2) /\
          bvi_letProof_env_rel rest d e1 e2
        | (_1,_2,_3) -> F`;;
hol4_overload "env_rel" "bvi_letProof_env_rel";;

let env_rel_length = cake_theorem "env_rel_length"
  (fun () ->
    `!ax env env2. bvi_letProof_env_rel ax d env env2 ==> LENGTH env
  <= LENGTH env2`)
  (LIST_INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[env_rel_def] THEN
    MATCH_REDUCE_TAC THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[LENGTH_DROP_LE];
    REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[env_rel_def] THEN
    LIST_CASES_TAC ["env"; "env2"] THEN MATCH_REDUCE_TAC THEN
    REWRITE_TAC[LENGTH; LE_SUC; LE_0] THEN STRIP_TAC THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let env_rel_LLOOKUP_NONE = cake_theorem "env_rel_LLOOKUP_NONE[local]"
  (fun () ->
    `!ax env env2 n d.
         bvi_letProof_env_rel ax d env env2 /\
         (\l n. oEL n l) ax n = NONE /\
         n < LENGTH env ==>
         n + d < LENGTH env2 /\
         EL (n + d) env2 = EL n env`)
  (LIST_INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[env_rel_def] THEN
    MATCH_REDUCE_TAC THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC[oEL] THEN STRIP_TAC THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    POP_ASSUM MP_TAC THEN REWRITE_TAC[LENGTH_DROP] THEN
    DISCH_TAC THEN CONJ_TAC THENL
    [ASM_ARITH_TAC;
     CONV_TAC SYM_CONV THEN MATCH_MP_TAC EL_DROP THEN ASM_ARITH_TAC];
    REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[env_rel_def] THEN
    LIST_CASES_TAC ["env"; "env2"] THEN MATCH_REDUCE_TAC THEN
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    STRUCT_CASES_TAC(SPEC `n:num` num_CASES) THEN
    REWRITE_TAC[oEL; LENGTH; EL; TL; ADD_CLAUSES; LT_SUC; LT;
                NOT_SUC; ARITH_EQ; SUC_SUB1;
                distinctness "option"] THEN
    STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[]]);;

let env_rel_LOOKUP_SOME = cake_theorem "env_rel_LOOKUP_SOME[local]"
  (fun () ->
    `!env env2 ax x n d.
         bvi_letProof_env_rel ax d env env2 /\
         (\l n. oEL n l) ax n = SOME x ==>
         bvi_letProof_v_rel x (EL n env) (EL n env2) (DROP n env)
           (DROP n env2)`)
  (let UNFOLD = CONV_TAC(DEPTH_CONV BETA_CONV) in
   REWRITE_TAC[v_rel_def] THEN UNFOLD THEN
   LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
   ONCE_REWRITE_TAC[env_rel_def] THEN
   LIST_CASES_TAC ["ax"; "env2"] THEN MATCH_REDUCE_TAC THEN
   REWRITE_TAC[v_rel_def] THEN UNFOLD THEN
   REWRITE_TAC[oEL; distinctness "option"] THEN
   STRUCT_CASES_TAC(SPEC `n:num` num_CASES) THEN
   REWRITE_TAC[EL; TL; HD; DROP; ARITH_EQ; NOT_SUC; SUC_SUB1;
               distinctness "option"; injectivity "option"] THEN
   STRIP_TAC THEN ASM_REWRITE_TAC[oEL] THEN
   ASM_MESON_TAC[]);;

let evaluate_delete_var_Rerr_SING =
  cake_theorem "evaluate_delete_var_Rerr_SING"
  (fun () ->
    `!x s r e env2.
        evaluate ([x],env2,s) = (Rerr e,r) /\ ~(e = Rabort
          Rtype_error) ==>
        evaluate ([delete_var x],env2,s) = (Rerr e,r)`)
  (let dv = cake_def "bvi_let_delete_var" in
   let ev = cake_def "bviSem_evaluate" in
   REPEAT GEN_TAC THEN
   STRUCT_CASES_TAC(ISPEC `x:bvi_exp` (cases_of `:bvi_exp`)) THEN
   REWRITE_TAC[dv] THEN MATCH_REDUCE_TAC THEN
   TRY(DISCH_THEN(ACCEPT_TAC o CONJUNCT1)) THEN
   DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
   GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [ev] THEN
   COND_CASES_TAC THEN
   REWRITE_TAC[PAIR_EQ; distinctness "semanticPrimitives_result";
               injectivity "semanticPrimitives_result"] THEN
   ASM_MESON_TAC[]);;

let evaluate_delete_var_Rerr =
  cake_theorem "evaluate_delete_var_Rerr[local]"
  (fun () ->
    `!xs s r e env2.
         evaluate (xs,env2,s) = (Rerr e,r) /\ ~(e = Rabort
           Rtype_error) ==>
         evaluate (MAP delete_var xs,env2,s) = (Rerr e,r)`)
  (let dv = cake_def "bvi_let_delete_var" in
   let ev = cake_def "bviSem_evaluate" in
   let da = cake_def "bviSem_do_app" in
   let daa = cake_def "bviSem_do_app_aux" in
   let fc = cake_def "bviSem_fix_clock" in
   let sei = cake_def "small_enough_int" in
   let res_rws = [PAIR_EQ;
                  distinctness "semanticPrimitives_result";
                  injectivity "semanticPrimitives_result"] in
   (* HOL4 takes the head apart inside this proof and again inside
      the next one (bvi_letProofScript.sml:79-83 and :98-101).  What
      its case analysis says is that delete_var changes a Var and
      nothing else, and that the Op it leaves there evaluates to a
      number without touching the state. *)
   let opev = prove
    (`!env2 (s:('c,'ffi)bviSem_state).
        evaluate
          ([(Op (closLang_IntOp (closLang_Const (&0))) []):bvi_exp],
           env2,s) = (Rval [(Number (&0)):bvlSem_v],s)`,
     REPEAT GEN_TAC THEN
     REWRITE_TAC[ev; fc; ARITH_RULE `MIN (a:num) a = a`] THEN
     RECORD_CASES_TAC `s:('c,'ffi)bviSem_state` THEN
     REWRITE_TAC[da; daa; REVERSE; NULL; sei;
                 INT_ARITH `--(&268435457):int <= &0 /\
                            (&0):int <= &268435457`;
                 distinctness "closLang_op"] THEN
     MATCH_REDUCE_TAC THEN REWRITE_TAC[]) in
   (* so the head leaves the same state either way ... *)
   let stateq = prove
    (`!(x:bvi_exp) env2 (s:('c,'ffi)bviSem_state) v t u w.
        evaluate ([x],env2,s) = (v,t) /\
        evaluate ([delete_var x],env2,s) = (u,w) ==> w = t`,
     REPEAT GEN_TAC THEN
     STRUCT_CASES_TAC(ISPEC `x:bvi_exp` (cases_of `:bvi_exp`)) THEN
     REWRITE_TAC[dv] THEN MATCH_REDUCE_TAC THEN
     FIRST
      [(* the ten that delete_var leaves alone: one evaluation *)
       SOLVED(DISCH_THEN(fun th ->
                MP_TAC(TRANS (SYM(CONJUNCT2 th)) (CONJUNCT1 th))) THEN
              REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
              ASM_REWRITE_TAC[]);
       (* and the Var, where both leave the state it came in with *)
       (REWRITE_TAC[opev; ev] THEN COND_CASES_TAC THEN
        REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN VAR_EQ_TAC THEN
        REFL_TAC)]) in
   (* ... and a head that succeeds still succeeds *)
   let valev = prove
    (`!(x:bvi_exp) env2 (s:('c,'ffi)bviSem_state) v t.
        evaluate ([x],env2,s) = (Rval v,t) ==>
        ?w. evaluate ([delete_var x],env2,s) = (Rval w,t)`,
     REPEAT GEN_TAC THEN
     STRUCT_CASES_TAC(ISPEC `x:bvi_exp` (cases_of `:bvi_exp`)) THEN
     REWRITE_TAC[dv] THEN MATCH_REDUCE_TAC THEN
     FIRST
      [SOLVED(DISCH_TAC THEN EXISTS_TAC `v:bvlSem_v list` THEN
              ASM_REWRITE_TAC[]);
       (REWRITE_TAC[opev; ev] THEN COND_CASES_TAC THEN
        REWRITE_TAC res_rws THEN STRIP_TAC THEN
        EXISTS_TAC `[(Number (&0)):bvlSem_v]` THEN
        ASM_REWRITE_TAC[])]) in
   LIST_INDUCT_TAC THEN REWRITE_TAC[MAP] THENL
    [REPEAT GEN_TAC THEN DISCH_THEN(ACCEPT_TAC o CONJUNCT1);
     ALL_TAC] THEN
   REPEAT GEN_TAC THEN
   GEN_REWRITE_TAC ONCE_DEPTH_CONV [bviProps_evaluate_CONS] THEN
   REPEAT STRIP_TAC THEN EVERY_CASE_TAC THEN VAR_EQ_TAC THEN
   FIRST
    [(* the head errored, so delete_var's head errors the same way *)
     RES2_THEN evaluate_delete_var_Rerr_SING
       (SOLVED(ASM_REWRITE_TAC res_rws));
     (* the head succeeded, so delete_var's head cannot error *)
     RES1_THEN valev (SOLVED(ASM_REWRITE_TAC res_rws));
     (* both succeeded, at the same state: then the hypothesis *)
     RES2_THEN stateq
      (DISCH_THEN SUBST_ALL_TAC THEN
       FIRST_ASSUM(fun ih ->
         RES2_THEN ih (SOLVED(ASM_REWRITE_TAC res_rws))))]);;

let evaluate_delete_var_Rval =
  cake_theorem "evaluate_delete_var_Rval[local]"
  (fun () ->
    `!xs env2 s a r ax env d.
         evaluate (xs,env2,(s:('c,'ffi)bviSem_state)) = (Rval a,r)
           /\
         bvi_letProof_env_rel ax d env env2 ==>
         (?b. evaluate (MAP delete_var xs,env2,s) = (Rval b,r) /\
             bvi_letProof_env_rel (extract_list xs ++ ax) d (a ++
               env) (b ++ env2))`)
  (let rty = `:(bvlSem_v list,exn_or_ret)
                semanticPrimitives_result` in
   let dv = cake_def "bvi_let_delete_var" in
   let ev = cake_def "bviSem_evaluate" in
   let da = cake_def "bviSem_do_app" in
   let daa = cake_def "bviSem_do_app_aux" in
   let fc = cake_def "bviSem_fix_clock" in
   let sei = cake_def "small_enough_int" in
   let el = cake_def "bvi_let_extract_list" in
   let ex = cake_def "bvi_let_extract" in
   let er = cake_def "bvi_letProof_env_rel" in
   let vr = cake_def "bvi_letProof_v_rel" in
   let res_rws = [PAIR_EQ;
                  distinctness "semanticPrimitives_result";
                  injectivity "semanticPrimitives_result"] in
   (* HOL4 takes the head apart inside this proof and again inside
      the next one (bvi_letProofScript.sml:79-83 and :98-101).  What
      its case analysis says is that delete_var changes a Var and
      nothing else, and that the Op it leaves there evaluates to a
      number without touching the state. *)
   let opev = prove
    (`!env2 (s:('c,'ffi)bviSem_state).
        evaluate
          ([(Op (closLang_IntOp (closLang_Const (&0))) []):bvi_exp],
           env2,s) = (Rval [(Number (&0)):bvlSem_v],s)`,
     REPEAT GEN_TAC THEN
     REWRITE_TAC[ev; fc; ARITH_RULE `MIN (a:num) a = a`] THEN
     RECORD_CASES_TAC `s:('c,'ffi)bviSem_state` THEN
     REWRITE_TAC[da; daa; REVERSE; NULL; sei;
                 INT_ARITH `--(&268435457):int <= &0 /\
                            (&0):int <= &268435457`;
                 distinctness "closLang_op"] THEN
     MATCH_REDUCE_TAC THEN REWRITE_TAC[]) in
   (* and the Var is the only head whose extract is not 0 *)
   let notvar = prove
    (`!(x:bvi_exp). ~(?i. x = Var i)
        ==> delete_var x = x /\ (!ys. extract x ys = 0)`,
     GEN_TAC THEN
     STRUCT_CASES_TAC(ISPEC `x:bvi_exp` (cases_of `:bvi_exp`)) THEN
     REWRITE_TAC[dv; ex] THEN MATCH_REDUCE_TAC THEN
     REWRITE_TAC[distinctness "bvi_exp";
                 injectivity "bvi_exp"] THEN
     MESON_TAC[]) in
   (* The splits of this proof are made by hand, with names of its
      own: the goals that EVERY_CASE_TAC leaves carry names it
      invented, and this proof has to write down the witness of an
      existential goal and the instance of the induction
      hypothesis afterwards. *)
   let tidy =
     TRY SAFE_MATCH_REDUCE_TAC THEN
     TRY SAFE_MATCH_REDUCE_ASM_TAC THEN
     PRUNE_TAC res_rws THEN MATCH_TIDY_TAC THEN
     SPLIT_ASM_TAC THEN VAR_EQ_TAC in
   let split_tail st =
     NAMED_CASES_TAC
       (list_mk_icomb "bviSem_evaluate"
          [mk_pair(`t:bvi_exp list`,
                   mk_pair(`env2:bvlSem_v list`,st))])
       [["tres"; "ts"]] THEN
     NAMED_CASES_TAC (mk_var("tres",rty)) [["tv"]; ["te"]] THEN
     tidy in
   let use_ih st =
     FIRST_X_ASSUM(fun ih ->
       MP_TAC(SPECL [`env2:bvlSem_v list`; st;
                     `tv:bvlSem_v list`;
                     `r:('c,'ffi)bviSem_state`;
                     `ax:num list`; `env:bvlSem_v list`;
                     `d:num`] ih)) THEN
     ASM_REWRITE_TAC[] THEN
     DISCH_THEN(X_CHOOSE_THEN `bb:bvlSem_v list`
                  STRIP_ASSUME_TAC) in
   let env_rel_cons =
     REWRITE_TAC[APPEND] THEN ONCE_REWRITE_TAC[er] THEN
     MATCH_REDUCE_TAC THEN REWRITE_TAC[vr] THEN
     CONV_TAC(DEPTH_CONV BETA_CONV) in
   (* the empty list: nothing evaluated and nothing extracted *)
   let base_branch =
     REPEAT GEN_TAC THEN REWRITE_TAC[ev] THEN
     REWRITE_TAC[PAIR_EQ;
                 injectivity "semanticPrimitives_result"] THEN
     STRIP_TAC THEN VAR_EQ_TAC THEN
     EXISTS_TAC `[]:bvlSem_v list` THEN
     ASM_REWRITE_TAC[APPEND; ev] in
   (* a head that delete_var leaves alone: the same value in both
      environments, so its entry of the relation is at offset 0 *)
   let nonvar_branch =
     FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP notvar th]) THEN
     STRIP_TAC THEN
     NAMED_CASES_TAC
       `evaluate ([h],env2,(s:('c,'ffi)bviSem_state))`
       [["hres"; "hs"]] THEN
     NAMED_CASES_TAC (mk_var("hres",rty)) [["hv"]; ["he"]] THEN
     tidy THEN split_tail `hs:('c,'ffi)bviSem_state` THEN
     use_ih `hs:('c,'ffi)bviSem_state` THEN
     EXISTS_TAC `HD (hv:bvlSem_v list) :: bb` THEN
     ASM_REWRITE_TAC[] THEN tidy THEN
     env_rel_cons THEN REWRITE_TAC[oEL] THEN
     ASM_REWRITE_TAC[] in
   (* and a Var, where delete_var put the Op: the value the Var
      read is still in the second environment, at the offset that
      the extract records -- past the number the Op left and past
      the values of the rest of the list *)
   let var_branch =
     FIRST_X_ASSUM(X_CHOOSE_THEN `i:num` SUBST1_TAC) THEN
     REWRITE_TAC[dv; ex] THEN SAFE_MATCH_REDUCE_TAC THEN
     REWRITE_TAC[opev] THEN
     GEN_REWRITE_TAC ONCE_DEPTH_CONV [ev] THEN
     ASM_CASES_TAC `i < LENGTH (env2:bvlSem_v list)` THEN
     ASM_REWRITE_TAC[HD] THEN tidy THEN STRIP_TAC THEN tidy THEN
     split_tail `s:('c,'ffi)bviSem_state` THEN
     use_ih `s:('c,'ffi)bviSem_state` THEN
     EXISTS_TAC `((Number (&0)):bvlSem_v) :: bb` THEN
     ASM_REWRITE_TAC[] THEN tidy THEN env_rel_cons THEN
     SUBGOAL_THEN
       `LENGTH (t:bvi_exp list) = LENGTH (bb:bvlSem_v list)`
       SUBST1_TAC THENL
     [FIRST_ASSUM(fun th -> ACCEPT_TAC(REWRITE_RULE[LENGTH_MAP]
        (MATCH_MP bviProps_evaluate_IMP_LENGTH th)));
      ALL_TAC] THEN
     REWRITE_TAC[oEL; ARITH_RULE `~(i + n + 1 = 0)`;
                 ARITH_RULE `(i + n + 1) - 1 = i + n`] THEN
     REWRITE_TAC[oEL_APPEND] THEN
     FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP oEL_EL th]) THEN
     ASM_REWRITE_TAC[] in
   LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; el; APPEND] THENL
    [base_branch; ALL_TAC] THEN
   REPEAT GEN_TAC THEN
   GEN_REWRITE_TAC ONCE_DEPTH_CONV [bviProps_evaluate_CONS] THEN
   ASM_CASES_TAC `?i. (h:bvi_exp) = Var i` THENL
   [var_branch; nonvar_branch]);;

let evaluate_SNOC_Rval = cake_theorem "evaluate_SNOC_Rval"
  (fun () ->
    `evaluate (SNOC x y,env,s) = (Rval a,r) ==>
      (?a1 a2 r1.
        a = SNOC a1 a2 /\ LENGTH y = LENGTH a2 /\
        evaluate (y,env,s) = (Rval a2,r1) /\
        evaluate ([x],env,r1) = (Rval [a1],r))`)
  (ONCE_REWRITE_TAC[bviProps_evaluate_SNOC] THEN EVERY_CASE_TAC THEN
   REWRITE_TAC[PAIR_EQ; distinctness "semanticPrimitives_result";
               injectivity "semanticPrimitives_result"] THEN
   STRIP_TAC THEN
   FIRST_ASSUM(CHOOSE_THEN SUBST_ALL_TAC o
               MATCH_MP evaluate_SING_IMP) THEN
   ASM_MESON_TAC[bviProps_evaluate_IMP_LENGTH;
                 prove(`!l x. SNOC x l = l ++ [x]`,
                       LIST_INDUCT_TAC THEN
                       ASM_REWRITE_TAC[SNOC; APPEND])]);;

let compile_CONS = cake_theorem "compile_CONS"
  (fun () ->
    `compile ax d (x :: xs) = compile ax d [x] ++ compile ax d xs`)
  (let compile_def = cake_def "bvi_let_compile" in
   STRUCT_CASES_TAC(ISPEC `xs:bvi_exp list` list_CASES) THEN
   REWRITE_TAC[compile_def; APPEND_NIL]);;

let compile_APPEND = cake_theorem "compile_APPEND"
  (fun () ->
    `!xs ys ax d. compile ax d (xs ++ ys) = compile ax d xs ++ compile
  ax d ys`)
  (let compile_def = cake_def "bvi_let_compile" in
   LIST_INDUCT_TAC THEN REWRITE_TAC[APPEND; compile_def] THEN
   ONCE_REWRITE_TAC[compile_CONS] THEN
   ASM_REWRITE_TAC[GSYM APPEND_ASSOC]);;

let IMP_COMM = cake_theorem "IMP_COMM"
  (fun () ->
    `(b1 ==> b2 ==> b3) <=> (b2 ==> b1 ==> b3)`)
  (MESON_TAC[]);;

(* HOL4 bvi_letProofScript.sml:146-150: a theorem whose statement the
   port cannot state yet: exp_size_APPEND *)

let env_rel_MAP = cake_theorem "env_rel_MAP"
  (fun () ->
    `!ax env1 env2 d a.
        bvi_letProof_env_rel ax d env1 env2 ==>
        bvi_letProof_env_rel (MAP ((+) (LENGTH a)) ax) (d +
          LENGTH a) env1 (a ++ env2)`)
  (* HOL4 moves the head of the new environment into ax with the
     append gymnastics of bvi_letProofScript.sml:157-176; the same
     induction, one element at a time *)
  (let STEP = prove
     (`!ax d e1 e2 v.
         bvi_letProof_env_rel ax d e1 e2 ==>
         bvi_letProof_env_rel (MAP SUC ax) (SUC d) e1 (CONS v e2)`,
      LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
      ONCE_REWRITE_TAC[env_rel_def] THEN REWRITE_TAC[MAP] THEN
      LIST_CASES_TAC ["e1"; "e2"] THEN EVERY_CASE_TAC THEN
      REWRITE_TAC[DROP; oEL; ARITH_EQ; NOT_SUC; SUC_SUB1;
                  v_rel_def] THEN
      CONV_TAC(DEPTH_CONV BETA_CONV) THEN STRIP_TAC THEN
      CONJ_TAC THENL
      [ASM_REWRITE_TAC[];
       FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]) in
   let MAP_SUC = prove
     (`!n ax. MAP SUC (MAP ((+) n) ax) = MAP ((+) (SUC n)) ax`,
      GEN_TAC THEN LIST_INDUCT_TAC THEN
      ASM_REWRITE_TAC[MAP; ADD_CLAUSES]) in
   let MAP_ZERO = prove
     (`!ax. MAP ((+) 0) ax = ax`,
      LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP; ADD_CLAUSES]) in
   GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
   LIST_INDUCT_TAC THENL
   [REWRITE_TAC[LENGTH; APPEND; ADD_CLAUSES; MAP_ZERO];
    REWRITE_TAC[LENGTH; APPEND; ADD_CLAUSES] THEN
    ONCE_REWRITE_TAC[GSYM MAP_SUC] THEN DISCH_TAC THEN
    MATCH_MP_TAC STEP THEN FIRST_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[]]);;

let env_rel_REPLICATE_0 = cake_theorem "env_rel_REPLICATE_0[local]"
  (fun () ->
    `!vs ax d env1 env2.
       bvi_letProof_env_rel ax d env1 env2 ==>
       bvi_letProof_env_rel (REPLICATE (LENGTH vs) 0 ++ ax) d (vs
         ++ env1) (vs ++ env2)`)
  (LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
   ASM_REWRITE_TAC[REPLICATE; LENGTH; APPEND] THEN
   ONCE_REWRITE_TAC[env_rel_def] THEN MATCH_REDUCE_TAC THEN
   CONJ_TAC THENL
   [REWRITE_TAC[v_rel_def] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC[oEL];
    ASM_SIMP_TAC[]]);;

let evaluate_env_rel = cake_theorem "evaluate_env_rel"
  (fun () ->
    `!xs env1 (s1:('c,'ffi)bviSem_state) ax env2 res s2 ys d.
        (evaluate (xs,env1,s1) = (res,s2)) /\
        bvi_letProof_env_rel ax d env1 env2 /\ ~(res = Rerr (Rabort
          Rtype_error)) ==>
        (evaluate (compile ax d xs,env2,s1) = (res,s2))`)
  ((* ---- the pieces ---------------------------------------------- *)
   let cp = cake_def "bvi_let_compile" in
   let ev = cake_def "bviSem_evaluate" in
   let er = cake_def "bvi_letProof_env_rel" in
   let vr = cake_def "bvi_letProof_v_rel" in
   let fc = cake_def "bviSem_fix_clock" in
   let fce = bviSem_fix_clock_evaluate in
   let sz = size_thms "bvi_exp" in
   let res_rws = [PAIR_EQ; distinctness "semanticPrimitives_result";
                  injectivity "semanticPrimitives_result"] in
   let rty = `:(bvlSem_v list,exn_or_ret)semanticPrimitives_result` in
   let s1t = `s1:('c,'ffi)bviSem_state` in
   let add_lt = ARITH_RULE `!m v e. m < e - v ==> m + v < e` in
   let add_sym_lt = ARITH_RULE `!m v e. m + v < e ==> v + m < e` in
   let lkn = CONV_RULE(DEPTH_CONV BETA_CONV) env_rel_LLOOKUP_NONE in
   let lks = CONV_RULE(DEPTH_CONV BETA_CONV) env_rel_LOOKUP_SOME in
   let index_lemma = prove
    (`!ax d env1 env2 v.
        bvi_letProof_env_rel ax d env1 env2 /\ v < LENGTH env1 ==>
        (oEL v ax = NONE ==> v + d < LENGTH env2 /\
                             EL (v + d) env2 = EL v env1) /\
        (!m. oEL v ax = SOME m ==> v + m < LENGTH env2 /\
                                   EL (v + m) env2 = EL v env1)`,
     REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
     [DISCH_TAC THEN
      FIRST_ASSUM(fun er_th -> FIRST_ASSUM(fun lk ->
        FIRST_ASSUM(fun lt ->
          ACCEPT_TAC(MATCH_MP lkn (CONJ er_th (CONJ lk lt))))));
      GEN_TAC THEN DISCH_TAC THEN
      FIRST_ASSUM(fun er_th -> FIRST_ASSUM(fun lk ->
        MP_TAC(MATCH_MP lks (CONJ er_th lk)))) THEN
      REWRITE_TAC[vr] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
      DISCH_THEN(MP_TAC o MATCH_MP oEL_SOME) THEN
      REWRITE_TAC[LENGTH_DROP] THEN STRIP_TAC THEN
      FIRST_ASSUM(fun lt ->
        let bound = MATCH_MP add_lt lt in
        let eld = MATCH_MP EL_DROP bound in
        CONJ_TAC THENL
        [ACCEPT_TAC(MATCH_MP add_sym_lt bound);
         FIRST_ASSUM(fun eq -> ACCEPT_TAC
           (ONCE_REWRITE_RULE[ADD_SYM] (REWRITE_RULE[eld] eq)))])]) in
   (* ---- the shared steps ---------------------------------------- *)
   let size_tac_rws rws =
     RULE_ASSUM_TAC(REWRITE_RULE(rws @ (list_size :: sz))) THEN
     REWRITE_TAC(rws @ (list_size :: sz)) THEN ASM_ARITH_TAC in
   let size_tac = size_tac_rws [] in
   let impossible =
     SUBGOAL_THEN `F` CONTR_TAC THEN
     RULE_ASSUM_TAC(REWRITE_RULE(list_size :: sz)) THEN ASM_ARITH_TAC in
   (* the clock that fix_clock puts back is the clock that the
      evaluation left (bviSem's fix_clock_evaluate), so no proof of
      this file ever has to look inside a record update *)
   let tidy =
     TRY(REWRITE_TAC[fce]) THEN RULE_ASSUM_TRY(REWRITE_RULE[fce]) THEN
     TRY(REWRITE_TAC[fc]) THEN
     TRY(RULE_ASSUM_TAC(REWRITE_RULE[fc])) THEN
     TRY SAFE_MATCH_REDUCE_TAC THEN TRY SAFE_MATCH_REDUCE_ASM_TAC THEN
     PRUNE_TAC res_rws THEN MATCH_TIDY_TAC THEN
     SPLIT_ASM_TAC THEN VAR_EQ_TAC in
   let tidy2 = tidy THEN ASM_FS_TAC THEN tidy in
   let ev_term xs' env' s' =
     list_mk_icomb "bviSem_evaluate"
       [mk_pair(xs', mk_pair(env', s'))] in
   let is_ev t =
     try fst(dest_const(fst(strip_comb t))) = "bviSem_evaluate"
     with Failure _ -> false in
   let dest_ev t =
     let a,bc = dest_pair (rand t) in
     let b,c = dest_pair bc in a,b,c in
   (* the instance of the induction hypothesis that an evaluation of
      the source asks for: the list is the key, the three arguments
      of the compiler are given *)
   let USE_IH ax' env2' d' xs' (asl,w) =
     let ih = tryfind (fun (_,th) ->
       if is_forall (concl th) then th else fail()) asl in
     let a,b,c,rt = tryfind (fun (_,th) ->
       let l,r = dest_eq(concl th) in
       if not (is_ev l) then fail() else
       let a,b,c = dest_ev l in
       if a = xs' then (a,b,c,r) else fail()) asl in
     MP_TAC(SPECL [a; b; c; ax'; env2'; fst(dest_pair rt);
                   snd(dest_pair rt); d'] ih) (asl,w) in
   let ih_plain = USE_IH `ax:num list` `env2:bvlSem_v list` `d:num` in
   let ih_ants_simple sz_tac =
     ANTS_TAC THENL
     [CONJ_TAC THENL [sz_tac; ASM_REWRITE_TAC res_rws];
      DISCH_THEN(fun th -> TRY(REWRITE_TAC[th]) THEN
        RULE_ASSUM_TRY(REWRITE_RULE[th]) THEN ASSUME_TAC th)] in
   let use_ih_for xs' =
     FIRST_ASSUM(fun eq ->
       let l,rt = dest_eq(concl eq) in
       let a,bc = dest_pair(rand l) in
       let b,c = dest_pair bc in
       if not (a = xs' && b = `env1:bvlSem_v list`) then
         failwith "use_ih_for" else
       FIRST_ASSUM(fun ih ->
         MP_TAC(SPECL [a; b; c; `ax:num list`; `env2:bvlSem_v list`;
                       fst(dest_pair rt); snd(dest_pair rt);
                       `d:num`] ih)) THEN
       ANTS_TAC THENL
       [CONJ_TAC THENL [size_tac; ASM_REWRITE_TAC res_rws];
        DISCH_THEN(fun th -> REWRITE_TAC[th])]) in
   let do_sub nm xs' s' =
     NAMED_CASES_TAC (ev_term xs' `env1:bvlSem_v list` s')
       [[nm ^ "r"; nm ^ "s"]] THEN
     NAMED_CASES_TAC (mk_var(nm ^ "r",rty))
       [[nm ^ "v"]; [nm ^ "e"]] THEN
     tidy THEN use_ih_for xs' THEN tidy in
   let unfold_case =
     REWRITE_TAC[cp] THEN
     GEN_REWRITE_TAC ONCE_DEPTH_CONV [ev] THEN
     RULE_ASSUM_TAC(ONCE_REWRITE_RULE[ev]) THEN
     REWRITE_TAC[fce; compile_HD_SING] THEN
     RULE_ASSUM_TRY(REWRITE_RULE[fce]) in
   let one_sub xs' = unfold_case THEN do_sub "h" xs' s1t in
   (* ---- the index cases: Var and Force -------------------------- *)
   let index_case =
     TRY(RULE_ASSUM_TAC(ONCE_REWRITE_RULE[ev])) THEN
     ASM_CASES_TAC `v < LENGTH (env1:bvlSem_v list)` THEN
     TRY tidy2 THEN
     TRY(REWRITE_TAC[cp]) THEN TRY(CONV_TAC(DEPTH_CONV BETA_CONV)) THEN
     TRY(FIRST_ASSUM(fun er_th -> FIRST_ASSUM(fun lt ->
           STRIP_ASSUME_TAC(MATCH_MP index_lemma
             (CONJ er_th lt))))) THEN
     TRY(NAMED_CASES_TAC `oEL v (ax:num list)` [[]; ["m"]]) THEN
     TRY(PRUNE_TAC res_rws) THEN TRY MATCH_TIDY_TAC THEN
     TRY SAFE_MATCH_REDUCE_TAC THEN
     TRY(GEN_REWRITE_TAC ONCE_DEPTH_CONV [ev]) THEN
     TRY(FIRST_ASSUM(fun imp -> FIRST_ASSUM(fun eq ->
           STRIP_ASSUME_TAC(MATCH_MP imp eq)))) THEN
     TRY(ASM_REWRITE_TAC[]) THEN TRY ASM_FS_TAC THEN
     TRY(ASM_REWRITE_TAC[]) THEN
     (* the goal and the hypothesis have to be reduced alike: one of
        them with its match turned into a guard and the other not is
        two shapes of the same thing *)
     TRY SAFE_MATCH_REDUCE_TAC THEN TRY SAFE_MATCH_REDUCE_ASM_TAC THEN
     TRY MATCH_TIDY_TAC THEN TRY(ASM_REWRITE_TAC[]) in
   (* ---- Tick: the clock is tested on both sides alike ------------ *)
   let tick_case =
     unfold_case THEN
     ASM_CASES_TAC `state_clock (s1:('c,'ffi)bviSem_state) = 0` THEN
     ASM_FS_TAC THEN ASM_REWRITE_TAC[] THEN
     TRY(use_ih_for `[e:bvi_exp]`) in
   (* ---- If: the test is the same value on both sides ------------- *)
   let if_case =
     unfold_case THEN do_sub "h" `[e1:bvi_exp]` s1t THEN
     REPEAT(COND_CASES_TAC THEN ASM_FS_TAC THEN tidy) THEN
     TRY(use_ih_for `[e2:bvi_exp]`) THEN
     TRY(use_ih_for `[e3:bvi_exp]`) THEN
     TRY(ASM_REWRITE_TAC[]) THEN TRY tidy in
   let env_rel_CONS = prove
    (`!ax d env1 env2 v.
        bvi_letProof_env_rel ax d env1 env2 ==>
        bvi_letProof_env_rel (0 :: ax) d (v :: env1) (v :: env2)`,
     REPEAT GEN_TAC THEN DISCH_TAC THEN
     ONCE_REWRITE_TAC[er] THEN MATCH_REDUCE_TAC THEN
     REWRITE_TAC[vr] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
     REWRITE_TAC[oEL] THEN ASM_REWRITE_TAC[]) in
   (* the hypothesis of the branch, which is the assumption whose left
      side is the conditional or the match that the clause of the
      semantics made: put back into the goal it collapses against the
      conditions of the branch, which are assumptions *)
   let is_shape t =
     try mem (fst(dest_const(fst(strip_comb t)))) ["COND"; "_MATCH"]
     with Failure _ -> false in
   let use_hyp tac =
     FIRST_X_ASSUM(fun th ->
       if is_eq (concl th) && is_shape (lhs (concl th))
       then MP_TAC th THEN tac else failwith "use_hyp") in
   let collapse_hyp =
     use_hyp (ASM_REWRITE_TAC[] THEN TRY SAFE_MATCH_REDUCE_TAC THEN
              TRY MATCH_TIDY_TAC THEN TRY(REWRITE_TAC res_rws) THEN
              STRIP_TAC THEN TRY(PRUNE_TAC res_rws)) in
   let ih_ants =
     CONJ_TAC THENL
     [size_tac;
      REPEAT CONJ_TAC THEN
      TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      TRY(MATCH_MP_TAC env_rel_CONS THEN ASM_REWRITE_TAC[]) THEN
      TRY(MATCH_MP_TAC env_rel_REPLICATE_0 THEN ASM_REWRITE_TAC[]) THEN
      (* the sub-result is no type error because the whole result is
         none, which the assumptions say once the hypothesis of the
         branch has collapsed and they are pruned *)
      TRY tidy2 THEN TRY collapse_hyp THEN
      TRY(PRUNE_TAC res_rws) THEN
      TRY(ASM_REWRITE_TAC res_rws) THEN
      (* and what is left is the one side condition that HOL4
         discharges with a contradiction: the sub-result is no type
         error because the whole result is none.  Seeing that means
         deciding the conditions of the branch that are still open in
         the hypothesis. *)
      TRY(REPEAT(CHANGED_TAC(COND_SPLIT_TAC THEN TRY tidy2)) THEN
          TRY(PRUNE_TAC res_rws) THEN
          TRY(ASM_REWRITE_TAC res_rws))] in
   let use_ih_auto (asl,w as gl) =
     let where = w :: map (fun (_,th) -> concl th) asl in
     let evs = filter (fun t -> is_ev t && can dest_ev t)
                      (itlist (fun t a -> find_terms is_ev t @ a)
                              where []) in
     let attempt (_,th) =
       let l,rt = dest_eq(concl th) in
       if not (is_ev l) then failwith "use_ih_auto" else
       let xs',env1',s' = dest_ev l in
       (* the hypothesis is driven by the original evaluation, never by
          the compiled one *)
       if (try fst(dest_const(fst(strip_comb xs'))) = "bvi_let_compile"
           with Failure _ -> false)
       then failwith "use_ih_auto" else
       let gt = find (fun g ->
           try let cl,env2',s2' = dest_ev g in
               s2' = s' &&
               (let f,cargs = strip_comb cl in
                fst(dest_const f) = "bvi_let_compile" &&
                List.nth cargs 2 = xs')
           with Failure _ -> false) evs in
       let cl,env2',_ = dest_ev gt in
       let _,cargs = strip_comb cl in
       (* a fact the assumptions already have is no progress, and the
          search has to go on to the next evaluation *)
       if exists (fun (_,th) -> aconv (concl th) (mk_eq(gt,rt))) asl
       then failwith "use_ih_auto" else
       FIRST_ASSUM(fun ih ->
         MP_TAC(SPECL [xs'; env1'; s'; List.nth cargs 0; env2';
                       fst(dest_pair rt); snd(dest_pair rt);
                       List.nth cargs 1] ih)) THEN
       ANTS_TAC THENL
       [ih_ants;
        DISCH_THEN(fun t ->
          TRY(REWRITE_TAC[t]) THEN RULE_ASSUM_TRY(REWRITE_RULE[t]) THEN
          ASSUME_TAC t)] in
     tryfind (fun a -> attempt a gl) asl in
   let nil_case =
     REWRITE_TAC[cp; ev] THEN RULE_ASSUM_TAC(REWRITE_RULE[ev]) THEN
     ASM_REWRITE_TAC[] in
   let cons_cons_case =
     REWRITE_TAC[cp] THEN
     GEN_REWRITE_TAC ONCE_DEPTH_CONV [GSYM compile_HD_SING] THEN
     REWRITE_TAC[APPEND] THEN
     GEN_REWRITE_TAC ONCE_DEPTH_CONV [bviProps_evaluate_CONS] THEN
     REWRITE_TAC[compile_HD_SING] THEN
     RULE_ASSUM_TAC(ONCE_REWRITE_RULE[bviProps_evaluate_CONS]) THEN
     NAMED_CASES_TAC `evaluate ([x1],env1,(s1:('c,'ffi)bviSem_state))`
       [["hres"; "hs"]] THEN
     NAMED_CASES_TAC (mk_var("hres",rty)) [["hv"]; ["he"]] THEN
     tidy THEN
     use_ih_for `[x1:bvi_exp]` THEN tidy THEN
     TRY(NAMED_CASES_TAC
           `evaluate ((x2:bvi_exp) :: xr2,env1,
                      hs:('c,'ffi)bviSem_state)`
           [["tres"; "ts"]] THEN
         NAMED_CASES_TAC (mk_var("tres",rty)) [["tv"]; ["te"]] THEN
         tidy THEN use_ih_for `(x2:bvi_exp) :: xr2` THEN tidy) in
   (* the conditions of the semantics are if-then-else as well as
      case, and both sides test the same one; the condition goes
      first, because a condition that is still open when the
      hypothesis is used leaves a side condition that the branch
      cannot settle *)
   let deep_case =
     REPEAT(CHANGED_TAC
       (TRY(CHANGED_TAC use_ih_auto) THEN TRY tidy2 THEN
        (COND_SPLIT_TAC ORELSE CASE_SPLIT_TAC ORELSE
         COND_CASES_TAC) THEN TRY tidy2 THEN
        TRY(CHANGED_TAC use_ih_auto) THEN TRY tidy2 THEN
        TRY(ASM_REWRITE_TAC[]))) THEN
     TRY(CHANGED_TAC use_ih_auto) THEN TRY tidy2 THEN
     TRY(ASM_REWRITE_TAC[]) in
   let call_case =
     REWRITE_TAC[cp] THEN
     NAMED_CASES_TAC `hh:bvi_exp option` [[]; ["ce"]] THEN
     TRY SAFE_MATCH_REDUCE_TAC THEN
     GEN_REWRITE_TAC ONCE_DEPTH_CONV [ev] THEN
     RULE_ASSUM_TRY(ONCE_REWRITE_RULE[ev]) THEN
     REWRITE_TAC[fce; compile_HD_SING; IS_NONE; IS_SOME] THEN
     RULE_ASSUM_TRY(REWRITE_RULE[fce; IS_NONE; IS_SOME]) THEN
     ASM_CASES_TAC `IS_NONE (dd:num option)` THEN TRY tidy2 THEN
     TRY tidy THEN do_sub "a" `es:bvi_exp list` s1t THEN deep_case in
   let letcall_case =
     REWRITE_TAC[cp] THEN
     GEN_REWRITE_TAC ONCE_DEPTH_CONV [ev] THEN
     RULE_ASSUM_TRY(ONCE_REWRITE_RULE[ev]) THEN
     REWRITE_TAC[fce; compile_HD_SING] THEN
     RULE_ASSUM_TRY(REWRITE_RULE[fce]) THEN
     TRY tidy THEN do_sub "a" `es:bvi_exp list` s1t THEN deep_case in
   (* ---- Let: the three shapes the compiler gives it -------------- *)
   (* HOL4 writes the list of a Let that moves into tail-position as a
      SNOC and reads the front and the last off it; HOL Light's list
      library has SNOC but none of its laws *)
   let SNOC_APPEND = prove
    (`!(l:A list) x. SNOC x l = APPEND l [x]`,
     LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[SNOC; APPEND]) in
   let NOT_SNOC_NIL = prove
    (`!(l:A list) x. ~(SNOC x l = [])`,
     LIST_INDUCT_TAC THEN REWRITE_TAC[SNOC; NOT_CONS_NIL]) in
   let SNOC_CASES = prove
    (`!l:A list. ~(l = []) ==> ?x y. l = SNOC x y`,
     GEN_TAC THEN DISCH_TAC THEN
     EXISTS_TAC `LAST (l:A list)` THEN
     EXISTS_TAC `BUTLAST (l:A list)` THEN
     REWRITE_TAC[SNOC_APPEND] THEN
     FIRST_ASSUM(fun th ->
       REWRITE_TAC[MATCH_MP APPEND_BUTLAST_LAST th])) in
   let FRONT_SNOC = prove
    (`!(l:A list) x. BUTLAST (SNOC x l) = l`,
     LIST_INDUCT_TAC THEN
     ASM_REWRITE_TAC[SNOC; BUTLAST; NOT_SNOC_NIL]) in
   let LAST_SNOC = prove
    (`!(l:A list) x. LAST (SNOC x l) = x`,
     LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[SNOC; LAST; NOT_SNOC_NIL]) in
   let LENGTH_SNOC = prove
    (`!(l:A list) x. LENGTH (SNOC x l) = LENGTH l + 1`,
     LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[SNOC; LENGTH] THEN
     ARITH_TAC) in
   let list_size_SNOC = prove
    (`!(f:A->num) x l.
        list_size f (SNOC x l) = list_size f l + (f x + 1)`,
     GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
     ASM_REWRITE_TAC[SNOC; list_size] THEN ARITH_TAC) in
   (* and the one fact about EL that the moved body needs: the value
      the Var read is the first one past the front of the list *)
   let EL_LEN_APPEND = prove
    (`!(a:A list) v l. EL (LENGTH a) (APPEND a (CONS v l)) = v`,
     LIST_INDUCT_TAC THEN
     ASM_REWRITE_TAC[LENGTH; APPEND; EL; HD; TL]) in
   let snoc_rws = [FRONT_SNOC; LAST_SNOC; LENGTH_SNOC;
                   ARITH_RULE `(a + 1) - 1 = a`] in
   let snoc_size = size_tac_rws [list_size_SNOC] in
   let no_val = TRY(REWRITE_TAC(EXISTS_SIMP :: res_rws)) THEN
                TRY(ASM_REWRITE_TAC res_rws) in
   let let_unfold =
     RULE_ASSUM_TRY(ONCE_REWRITE_RULE[ev]) THEN
     RULE_ASSUM_TRY(REWRITE_RULE[fce]) THEN
     REWRITE_TAC[cp; LET_DEF; LET_END_DEF] THEN
     CONV_TAC(DEPTH_CONV BETA_CONV) in
   (* nothing bound: the Let is its body *)
   let let_nil =
     FIRST_ASSUM(SUBST_ALL_TAC o REWRITE_RULE[LENGTH_EQ_NIL]) THEN
     RULE_ASSUM_TRY(REWRITE_RULE[ev]) THEN
     RULE_ASSUM_TRY(REWRITE_RULE[APPEND]) THEN
     TRY SAFE_MATCH_REDUCE_ASM_TAC THEN
     REWRITE_TAC[LENGTH; ARITH] THEN
     use_ih_for `[e:bvi_exp]` in
   let get_snoc =
     FIRST_ASSUM(fun th ->
       X_CHOOSE_THEN `xl:bvi_exp` (X_CHOOSE_THEN `yl:bvi_exp list`
         (fun eq -> RULE_ASSUM_TRY(REWRITE_RULE[eq]) THEN
                    REWRITE_TAC[eq]))
         (MATCH_MP SNOC_CASES (REWRITE_RULE[LENGTH_EQ_NIL] th))) in
   (* the length of the front of the list is what the moved body
      reads, so the second environment grows by exactly that much *)
   let EV_LEN xs' =
     FIRST_ASSUM(fun th ->
       let l,r = dest_eq(concl th) in
       if not (is_ev l) then failwith "EV_LEN" else
       let a,_,_ = dest_ev l in
       if not (a = xs') then failwith "EV_LEN" else
       let len = MATCH_MP bviProps_evaluate_IMP_LENGTH th in
       REWRITE_TAC[len] THEN RULE_ASSUM_TRY(REWRITE_RULE[len])) in
   let env_rel_tail =
     SUBGOAL_THEN
       `bvi_letProof_env_rel
          (MAP ((+) (LENGTH (yl:bvi_exp list))) (ax:num list))
          (d + LENGTH (yl:bvi_exp list)) env1
          (APPEND (av:bvlSem_v list) env2)`
       ASSUME_TAC THENL
     [EV_LEN `yl:bvi_exp list` THEN
      MATCH_MP_TAC env_rel_MAP THEN ASM_REWRITE_TAC[];
      ALL_TAC] in
   let sing_xl =
     FIRST_ASSUM(fun th ->
       let l,r = dest_eq(concl th) in
       if not (is_ev l) then failwith "sing_xl" else
       let a,_,_ = dest_ev l in
       if not (a = `[xl:bvi_exp]`) then failwith "sing_xl" else
       X_CHOOSE_THEN `w:bvlSem_v` SUBST_ALL_TAC
         (MATCH_MP evaluate_SING_IMP th)) in
   let var_reduce =
     RULE_ASSUM_TRY(REWRITE_RULE[GSYM APPEND_ASSOC; APPEND]) THEN
     RULE_ASSUM_TRY(ONCE_REWRITE_RULE[ev]) THEN
     EV_LEN `yl:bvi_exp list` THEN
     RULE_ASSUM_TRY(REWRITE_RULE
       [EL_LEN_APPEND; LENGTH_APPEND; LENGTH;
        ARITH_RULE `!a b. a < a + SUC b`]) THEN
     tidy in
   let ih_yl = ih_plain `yl:bvi_exp list` THEN
               ih_ants_simple snoc_size THEN tidy in
   let ih_es = ih_plain `es:bvi_exp list` THEN
               ih_ants_simple size_tac THEN tidy in
   let ih_xl =
     USE_IH `MAP ((+) (LENGTH (yl:bvi_exp list))) (ax:num list)`
            `APPEND (av:bvlSem_v list) env2`
            `d + LENGTH (yl:bvi_exp list)` `[xl:bvi_exp]` in
   let ih_body =
     USE_IH `extract_list (bvi_let_compile ax d es) ++ ax`
            `APPEND (b:bvlSem_v list) env2` `d:num` `[e:bvi_exp]` in
   let is_compile t =
     try fst(dest_const(fst(strip_comb t))) = "bvi_let_compile"
     with Failure _ -> false in
   let COMPILE_EV f =
     FIRST_ASSUM(fun th ->
       let l,r = dest_eq(concl th) in
       if not (is_ev l) then failwith "COMPILE_EV" else
       let a,_,_ = dest_ev l in
       if not (is_compile a) then failwith "COMPILE_EV" else f th) in
   let del_rerr =
     COMPILE_EV (fun th ->
       FIRST_ASSUM(fun ne0 ->
         let ne = REWRITE_RULE[injectivity "semanticPrimitives_result"]
                    ne0 in
         REWRITE_TAC[MATCH_MP evaluate_delete_var_Rerr
                       (CONJ th ne)])) in
   let del_rval =
     COMPILE_EV (fun th ->
       FIRST_ASSUM(fun er0 ->
         MP_TAC(MATCH_MP evaluate_delete_var_Rval (CONJ th er0)))) THEN
     DISCH_THEN(X_CHOOSE_THEN `b:bvlSem_v list` STRIP_ASSUME_TAC) in
   (* the body is a Var that reads the last binding: the last
      expression of the list moves into tail-position, and the front
      of the list is what the new Let binds *)
   let let_tail =
     get_snoc THEN REWRITE_TAC snoc_rws THEN
     RULE_ASSUM_TRY(REWRITE_RULE snoc_rws) THEN ASM_REWRITE_TAC[] THEN
     RULE_ASSUM_TRY(REWRITE_RULE[bviProps_evaluate_SNOC]) THEN
     GEN_REWRITE_TAC ONCE_DEPTH_CONV [ev] THEN
     REWRITE_TAC[fce; compile_HD_SING] THEN
     UNDISCH_TAC `(e:bvi_exp) = Var (LENGTH (yl:bvi_exp list))` THEN
     DISCH_THEN SUBST_ALL_TAC THEN
     NAMED_CASES_TAC `evaluate (yl,env1,(s1:('c,'ffi)bviSem_state))`
       [["ar"; "as"]] THEN
     NAMED_CASES_TAC (mk_var("ar",rty)) [["av"]; ["ae"]] THEN tidy THENL
     [ih_yl THEN env_rel_tail THEN
      NAMED_CASES_TAC `evaluate ([xl],env1,(as:('c,'ffi)bviSem_state))`
        [["br"; "bs"]] THEN
      NAMED_CASES_TAC (mk_var("br",rty)) [["bv"]; ["be"]] THEN tidy THEN
      ih_xl THEN ih_ants_simple snoc_size THEN tidy THEN
      TRY(sing_xl THEN var_reduce) THEN TRY(ASM_REWRITE_TAC res_rws);
      ih_yl THEN no_val] in
   (* and otherwise the bindings keep their places, with the Vars
      among them turned into constants and the body reading the
      original variables through the offsets that extract_list
      recorded *)
   let let_general =
     ASM_REWRITE_TAC[] THEN
     GEN_REWRITE_TAC ONCE_DEPTH_CONV [ev] THEN
     REWRITE_TAC[fce; compile_HD_SING] THEN
     NAMED_CASES_TAC `evaluate (es,env1,(s1:('c,'ffi)bviSem_state))`
       [["cr"; "cs"]] THEN
     NAMED_CASES_TAC (mk_var("cr",rty)) [["cv"]; ["cerr"]] THEN
     tidy THENL
     [ih_es THEN del_rval THEN ASM_REWRITE_TAC[] THEN tidy THEN
      ih_body THEN ih_ants_simple size_tac THEN tidy THEN
      TRY(ASM_REWRITE_TAC res_rws);
      ih_es THEN del_rerr THEN no_val THEN TRY tidy] in
   let let_case =
     let_unfold THEN
     ASM_CASES_TAC `LENGTH (es:bvi_exp list) = 0` THENL
     [let_nil;
      ASM_CASES_TAC `(e:bvi_exp) = Var (LENGTH (es:bvi_exp list) - 1)`
      THENL [let_tail; let_general]] in
   (* ---- the eleven cases ---------------------------------------- *)
   let sub_cases =
     [index_case; if_case; let_case; one_sub `[e:bvi_exp]`; tick_case;
      call_case; index_case; one_sub `es:bvi_exp list`; letcall_case;
      one_sub `es:bvi_exp list`] in
   let single_case =
     NAMED_CASES_TAC `x1:bvi_exp`
       [["v"]; ["e1"; "e2"; "e3"]; ["es"; "e"]; ["e"]; ["e"];
        ["tt"; "dd"; "es"; "hh"]; ["loc"; "v"]; ["op"; "es"];
        ["rets"; "tt"; "dd"; "es"; "e"]; ["es"]] THENL sub_cases in
   let env_rel_tac =
     SUBGOAL_THEN
       `!n xs env1 (s1:('c,'ffi)bviSem_state) ax env2 res s2 d.
          list_size bvi_exp_size xs <= n /\
          evaluate (xs,env1,s1) = (res,s2) /\
          bvi_letProof_env_rel ax d env1 env2 /\
          ~(res = Rerr (Rabort Rtype_error)) ==>
          evaluate (bvi_let_compile ax d xs,env2,s1) = (res,s2)`
       (fun th -> REPEAT GEN_TAC THEN STRIP_TAC THEN
          MATCH_MP_TAC(SPEC `list_size bvi_exp_size (xs:bvi_exp list)`
                         th) THEN
          EXISTS_TAC `env1:bvlSem_v list` THEN
          ASM_REWRITE_TAC[LE_REFL]) THEN
     INDUCT_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
     NAMED_CASES_TAC `xs:bvi_exp list` [[]; ["x1"; "xr"]] THENL
     [nil_case; impossible; nil_case; ALL_TAC] THEN
     NAMED_CASES_TAC `xr:bvi_exp list` [[]; ["x2"; "xr2"]] THENL
     [single_case; TRY cons_cons_case] in
   env_rel_tac);;

(* HOL4 bvi_letProofScript.sml:220-237: a proof *)

(* HOL4 bvi_letProofScript.sml:239-249: a proof *)

(* HOL4 bvi_letProofScript.sml:251-257: a proof *)

(* HOL4 bvi_letProofScript.sml:259-270: a proof *)

(* HOL4 bvi_letProofScript.sml:272-287: a proof *)
   (* the handler now post-processes its result (rejecting an escaping Ret);
      split that inner case (the Ret branch is impossible as res <> type error),
      then close each surviving handler outcome by the induction hypothesis *)
(* HOL4 bvi_letProofScript.sml:291-297: a proof *)

(* HOL4 bvi_letProofScript.sml:299-307: a proof *)

(* HOL4 bvi_letProofScript.sml:309-320: a proof *)

(* HOL4 bvi_letProofScript.sml:322-330: a proof *)

(* HOL4 bvi_letProofScript.sml:332-346: a proof *)

(* HOL4 bvi_letProofScript.sml:348-387: a proof *)

(* HOL4 bvi_letProofScript.sml:389: a proof *)

(* HOL4 bvi_letProofScript.sml:391-394: a theorem that HOL4 states as
   the value of an ML expression: compile_thm *)

let evaluate_compile_exp = cake_theorem "evaluate_compile_exp"
  (fun () ->
    `evaluate ([d],env,s) = (r,t) /\ ~(r = Rerr (Rabort Rtype_error))
  ==>
      evaluate ([bvi_let_compile_exp d],env,s) = (r,t)`)
  (let ce = cake_def "bvi_let_compile_exp" in
   let er = cake_def "bvi_letProof_env_rel" in
   (* compile_exp x is the one expression that compile makes of the
      list [x], which compile_HD_SING says is a singleton *)
   let exp_SING = prove
    (`!x. [bvi_let_compile_exp x] = bvi_let_compile [] 0 [x]`,
     GEN_TAC THEN REWRITE_TAC[ce] THEN
     GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
       [GSYM compile_HD_SING] THEN
     MATCH_REDUCE_TAC THEN REWRITE_TAC[compile_HD_SING]) in
   (* and at ax = [] and d = 0 the environment relation is
      reflexive: it says env = DROP 0 env *)
   let env_rel_refl = prove
    (`!env. bvi_letProof_env_rel [] 0 env env`,
     GEN_TAC THEN ONCE_REWRITE_TAC[er] THEN MATCH_REDUCE_TAC THEN
     REWRITE_TAC[DROP_0]) in
   (* the terms come from the goal, because the statement of the
      source annotates no type and the state of this one is an
      invented type variable that nothing written by hand matches;
      and the ys of evaluate_env_rel, which its statement does not
      use, comes back as a universal quantifier that SPEC_ALL takes
      off *)
   REWRITE_TAC[exp_SING] THEN STRIP_TAC THEN
   FIRST_ASSUM(fun ev ->
     let tup = rand(lhs(concl ev)) in
     let env_tm = fst(dest_pair(snd(dest_pair tup))) in
     FIRST_ASSUM(fun ne ->
       ACCEPT_TAC(SPEC_ALL(MATCH_MP evaluate_env_rel
         (CONJ ev (CONJ (ISPEC env_tm env_rel_refl) ne)))))));;

let dest_var_code_labels = cake_theorem "dest_var_code_labels[simp]"
  (fun () ->
    `!x. get_code_labels (delete_var x) = get_code_labels x`)
  (let dv = cake_def "bvi_let_delete_var" in
   let gcl = cake_def "bviProps_get_code_labels" in
   let agcl = cake_def "assign_get_code_label" in
   GEN_TAC THEN
   STRUCT_CASES_TAC(ISPEC `x:bvi_exp` (cases_of `:bvi_exp`)) THEN
   REWRITE_TAC[dv] THEN
   MATCH_REDUCE_TAC THEN
   REWRITE_TAC[gcl; agcl] THEN
   MATCH_REDUCE_TAC THEN
   REWRITE_TAC[MAP; set_of_list; UNIONS_0; UNIONS_INSERT;
               UNION_EMPTY; EMPTY_UNION]);;

let compile_code_labels = cake_theorem "compile_code_labels"
  (fun () ->
    `!x y z. BIGUNION (set_of_list (MAP get_code_labels (bvi_let_compile
  x y z))) =
             BIGUNION (set_of_list (MAP get_code_labels z))`)
  (let cp = cake_def "bvi_let_compile" in
   let gcl = cake_def "bviProps_get_code_labels" in
   let sz = size_thms "bvi_exp" in
   let labs_rws = [MAP; set_of_list; UNIONS_0; UNIONS_INSERT;
                   UNION_EMPTY; EMPTY_UNION] in
   let labs_APPEND = prove
    (`!a b. BIGUNION (set_of_list (MAP get_code_labels
              (APPEND a b))) =
            BIGUNION (set_of_list (MAP get_code_labels a)) UNION
            BIGUNION (set_of_list (MAP get_code_labels b))`,
     LIST_INDUCT_TAC THEN
     ASM_REWRITE_TAC[APPEND; MAP; set_of_list; UNIONS_0;
                     UNIONS_INSERT; UNION_EMPTY; UNION_ASSOC]) in
   (* a compiled singleton is a singleton (compile_HD_SING), so the
      labels of its head are the labels of the list *)
   let labs_SING = prove
    (`!n d x. get_code_labels (HD (bvi_let_compile n d [x])) =
              BIGUNION (set_of_list (MAP get_code_labels
                (bvi_let_compile n d [x])))`,
     REPEAT GEN_TAC THEN
     GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)
       [GSYM compile_HD_SING] THEN
     REWRITE_TAC[MAP; set_of_list; UNIONS_INSERT; UNIONS_0;
                 UNION_EMPTY]) in
   let labs_delete_var = prove
    (`!l. BIGUNION (set_of_list (MAP get_code_labels
            (MAP delete_var l))) =
          BIGUNION (set_of_list (MAP get_code_labels l))`,
     LIST_INDUCT_TAC THEN
     ASM_REWRITE_TAC[MAP; set_of_list; UNIONS_0; UNIONS_INSERT;
                     dest_var_code_labels]) in
   (* HOL4 does this induction with recInduct compile_ind, the
      induction theorem that its termination proof left behind
      (bvi_letProofScript.sml:420).  HOL Light's define keeps no
      such theorem, and compile recurses on BUTLAST, which is not
      a structural sub-term, so bvi_exp_INDUCT will not do either:
      what is left is induction on the measure that the definition
      itself was made with, and a side condition for every use of
      the hypothesis. *)
   let cond t =
     mk_binop `(<=):num->num->bool`
       (list_mk_icomb "list_size" [`bvi_exp_size`; t]) `n:num` in
   let size_tac =
     RULE_ASSUM_TAC(REWRITE_RULE(list_size :: sz)) THEN
     REWRITE_TAC(list_size :: sz) THEN ASM_ARITH_TAC in
   let use_ih_by tac t =
     SUBGOAL_THEN (cond t)
       (fun c -> FIRST_ASSUM(fun ih -> REWRITE_TAC[MATCH_MP ih c]))
     THEN TRY tac in
   let use_ih = use_ih_by size_tac in
   let finish =
     REWRITE_TAC labs_rws THEN TRY(REWRITE_TAC[UNION_ACI]) in
   let unfold = REWRITE_TAC(cp :: gcl :: labs_SING :: labs_rws) in
   (* the Let is the one clause that compiles something other than
      a sub-term: the list without its last expression, and that
      last expression as the new body *)
   let let_case =
     REWRITE_TAC[cp; LET_DEF; LET_END_DEF] THEN
     CONV_TAC(DEPTH_CONV BETA_CONV) THEN
     ASM_CASES_TAC `LENGTH (es:bvi_exp list) = 0` THEN
     ASM_REWRITE_TAC[] THENL
     [FIRST_ASSUM(SUBST_ALL_TAC o REWRITE_RULE[LENGTH_EQ_NIL]) THEN
      REWRITE_TAC(gcl :: labs_rws) THEN use_ih `[e:bvi_exp]` THEN
      finish;
      ALL_TAC] THEN
     ASM_CASES_TAC
       `(e:bvi_exp) = Var (LENGTH (es:bvi_exp list) - 1)` THEN
     ASM_REWRITE_TAC[] THENL
     [REWRITE_TAC(gcl :: labs_SING :: labs_rws) THEN
      use_ih_by (MP_TAC(ISPECL [`bvi_exp_size`; `es:bvi_exp list`]
                          list_size_BUTLAST) THEN size_tac)
        `BUTLAST (es:bvi_exp list)` THEN
      use_ih_by
        (MP_TAC(MATCH_MP (ISPEC `bvi_exp_size` list_size_LAST)
                  (REWRITE_RULE[LENGTH_EQ_NIL]
                     (ASSUME `~(LENGTH (es:bvi_exp list) = 0)`))) THEN
         size_tac)
        `[LAST (es:bvi_exp list)]` THEN
      FIRST_ASSUM(fun th ->
        GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)
          [GSYM (MATCH_MP APPEND_BUTLAST_LAST
                   (REWRITE_RULE[LENGTH_EQ_NIL] th))]) THEN
      REWRITE_TAC[labs_APPEND] THEN finish;
      REWRITE_TAC(gcl :: labs_SING :: labs_rws) THEN
      REWRITE_TAC[labs_delete_var] THEN
      use_ih `es:bvi_exp list` THEN use_ih `[e:bvi_exp]` THEN
      finish] in
   let sub_cases =
     [(* Var *)
      REWRITE_TAC[cp] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
      EVERY_CASE_TAC THEN REWRITE_TAC(gcl :: labs_rws);
      (* If *)
      unfold THEN use_ih `[e1:bvi_exp]` THEN
      use_ih `[e2:bvi_exp]` THEN use_ih `[e3:bvi_exp]` THEN finish;
      (* Let *)
      let_case;
      (* Raise *)
      unfold THEN use_ih `[e:bvi_exp]` THEN finish;
      (* Tick *)
      unfold THEN use_ih `[e:bvi_exp]` THEN finish;
      (* Call *)
      REWRITE_TAC[cp] THEN
      NAMED_CASES_TAC `hh:bvi_exp option` [[]; ["ce"]] THEN
      unfold THEN use_ih `es:bvi_exp list` THEN
      TRY(use_ih `[ce:bvi_exp]`) THEN finish;
      (* Force *)
      REWRITE_TAC[cp] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
      EVERY_CASE_TAC THEN REWRITE_TAC(gcl :: labs_rws);
      (* Op *)
      unfold THEN use_ih `es:bvi_exp list` THEN finish;
      (* LetCall *)
      unfold THEN use_ih `es:bvi_exp list` THEN
      use_ih `[e:bvi_exp]` THEN finish;
      (* Return *)
      unfold THEN use_ih `es:bvi_exp list` THEN finish] in
   let single_case =
     NAMED_CASES_TAC `z1:bvi_exp`
       [["v"]; ["e1"; "e2"; "e3"]; ["es"; "e"]; ["e"]; ["e"];
        ["tt"; "dd"; "es"; "hh"]; ["loc"; "v"]; ["op"; "es"];
        ["rets"; "tt"; "dd"; "es"; "e"]; ["es"]] THENL sub_cases in
   let cons_cons_case =
     REWRITE_TAC[cp; labs_APPEND] THEN
     use_ih `[z1:bvi_exp]` THEN use_ih `(z2:bvi_exp) :: zs2` THEN
     finish in
   let base_case =
     REPEAT GEN_TAC THEN DISCH_TAC THEN
     NAMED_CASES_TAC `z:bvi_exp list` [[]; ["z1"; "zs"]] THENL
     [REWRITE_TAC[cp];
      FIRST_ASSUM MP_TAC THEN
      REWRITE_TAC[list_size; ARITH_RULE `~(1 + a + b <= 0)`]] in
   let step_case =
     REPEAT GEN_TAC THEN DISCH_TAC THEN
     NAMED_CASES_TAC `z:bvi_exp list` [[]; ["z1"; "zs"]] THENL
     [REWRITE_TAC[cp];
      NAMED_CASES_TAC `zs:bvi_exp list` [[]; ["z2"; "zs2"]] THENL
      [single_case; cons_cons_case]] in
   SUBGOAL_THEN
     `!n x y z. list_size bvi_exp_size z <= n ==>
        BIGUNION (set_of_list (MAP get_code_labels
          (bvi_let_compile x y z))) =
        BIGUNION (set_of_list (MAP get_code_labels z))`
     (fun th -> REPEAT GEN_TAC THEN
        MATCH_MP_TAC(SPEC `list_size bvi_exp_size (z:bvi_exp list)`
                       th) THEN
        REWRITE_TAC[LE_REFL]) THEN
   INDUCT_TAC THENL [base_case; step_case]);;

let compile_exp_code_labels =
  cake_theorem "compile_exp_code_labels[simp]"
  (fun () ->
    `!x. get_code_labels (bvi_let_compile_exp x) = get_code_labels x`)
  (let ce = cake_def "bvi_let_compile_exp" in
   (* compile_exp is the head of the compiled singleton, so its
      labels are the labels of the list that compile_code_labels
      speaks about *)
   let labs_SING = prove
    (`!n d x. get_code_labels (HD (bvi_let_compile n d [x])) =
              BIGUNION (set_of_list (MAP get_code_labels
                (bvi_let_compile n d [x])))`,
     REPEAT GEN_TAC THEN
     GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)
       [GSYM compile_HD_SING] THEN
     REWRITE_TAC[MAP; set_of_list; UNIONS_INSERT; UNIONS_0;
                 UNION_EMPTY]) in
   GEN_TAC THEN REWRITE_TAC[ce] THEN
   GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
     [GSYM compile_HD_SING] THEN
   MATCH_REDUCE_TAC THEN
   GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [labs_SING] THEN
   REWRITE_TAC[compile_code_labels] THEN
   REWRITE_TAC[MAP; set_of_list; UNIONS_INSERT; UNIONS_0;
               UNION_EMPTY]);;
