(* ======================================================== *)
(*  bvi_letProof: ported from HOL4's
    compiler/backend/proofs/bvi_letProofScript.sml  *)
(* ======================================================== *)

(*
  Correctness proof for bvi_let
*)

needs "compiler/backend/bvi_let.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/semantics/bviProps.ml";;
needs "compiler/backend/semantics/bviSem.ml";;
needs "compiler/backend/semantics/bvlProps.ml";;
needs "compiler/backend/semantics/closSem.ml";;
needs "lib/binary_ieee.ml";;
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
  CHEAT_TAC;;

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
  CHEAT_TAC;;

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
  CHEAT_TAC;;

let compile_exp_code_labels =
  cake_theorem "compile_exp_code_labels[simp]"
  (fun () ->
    `!x. get_code_labels (bvi_let_compile_exp x) = get_code_labels x`)
  CHEAT_TAC;;
