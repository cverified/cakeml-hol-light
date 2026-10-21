(* ======================================================== *)
(*  bvi_letProof: ported from HOL4's
    compiler/backend/proofs/bvi_letProofScript.sml  *)
(* ======================================================== *)

(*
  Correctness proof for bvi_let
*)

needs "basis/pure/mlstring.ml";;
needs "compiler/backend/bvi_let.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/semantics/bviProps.ml";;
needs "compiler/backend/semantics/bviSem.ml";;
needs "compiler/backend/semantics/bvlProps.ml";;
needs "compiler/backend/semantics/closSem.ml";;
needs "lib/binary_ieee.ml";;
needs "lib/set_sep.ml";;
needs "semantics/ast.ml";;
needs "semantics/cmlPtreeConversion.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "semantics/typeSystem.ml";;

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
  CHEAT_TAC;;

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
