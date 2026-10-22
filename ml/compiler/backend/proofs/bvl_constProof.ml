(* ======================================================== *)
(*  bvl_constProof: ported from HOL4's
    compiler/backend/proofs/bvl_constProofScript.sml
    A proof theory about bvl_const.ml, with 2 definitions and 24
    theorems.  Needed by bvl_handleProof.ml and bvl_to_bviProof.ml.  *)
(* ======================================================== *)

(*
  Correctness proof for bvl_const
*)

needs "compiler/backend/bvl_const.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/semantics/bvlProps.ml";;
needs "compiler/backend/semantics/bvlSem.ml";;
needs "compiler/backend/semantics/closSem.ml";;
needs "lib/sptree.ml";;
needs "semantics/ast.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "semantics/typeSystem.ml";;

let v_rel_def = cake_define
  `bvl_constProof_v_rel (:'c) (:'ffi) a x y xs ys =
     (match a with Var n -> (\l n. oEL n l) ys n = SOME x | Op _1 _2
       ->
       (x = y) /\
       (!(s:('c,'ffi)bvlSem_state) env. evaluate ([a],env,s) =
         (Rval [x],s)) | _3 -> F)`;;
hol4_overload "v_rel" "bvl_constProof_v_rel";;

let env_rel_def = cake_define
  `bvl_constProof_env_rel x1 x2 x3 e1 e2 =
        match (x1,x2,x3,e1,e2) with
          ((:'c),(:'ffi),[],e1,e2) -> (e1 = e2)
        | ((:'c),(:'ffi),(NONE :: rest),(x :: e1),(y :: e2)) ->
        (x = y) /\ bvl_constProof_env_rel (:'c) (:'ffi) rest e1 e2
        | ((:'c),(:'ffi),(SOME a :: rest),(x :: e1),(y :: e2)) ->
        bvl_constProof_v_rel (:'c) (:'ffi) a x y (x :: e1) (y :: e2)
          /\ bvl_constProof_env_rel (:'c) (:'ffi) rest e1 e2
        | (_4,_5,_6,_7,_8) -> F`;;
hol4_overload "env_rel" "bvl_constProof_env_rel";;

let bvl_constProof_env_rel_length = cake_theorem "env_rel_length"
  (fun () ->
    `!ax env env2. bvl_constProof_env_rel (:'c) (:'ffi) ax env env2
  ==> LENGTH env2 = LENGTH env`)
  (* HOL4 states env_rel as four clauses, which its Induct and its
     fs [env_rel_def] use one at a time; the port states it as one
     match on the tuple of the arguments, so the clauses are taken
     off it first.  Every proof of this file that unfolds the
     relation starts that way (the rewrite is a LAND_CONV, because
     the relation stands on both sides of the clause it proves). *)
  (let er = cake_def "bvl_constProof_env_rel" in
   let erc = map (fun t ->
     prove(t, GEN_REWRITE_TAC LAND_CONV [er] THEN
              MATCH_REDUCE_TAC THEN REWRITE_TAC[]))
    [`bvl_constProof_env_rel (:'c) (:'ffi) [] e1 e2 <=> (e1 = e2)`;
     `bvl_constProof_env_rel (:'c) (:'ffi) (CONS NONE rest)
        (CONS x e1) (CONS y e2) <=>
      (x = y) /\ bvl_constProof_env_rel (:'c) (:'ffi) rest e1 e2`;
     `bvl_constProof_env_rel (:'c) (:'ffi) (CONS (SOME a) rest)
        (CONS x e1) (CONS y e2) <=>
      bvl_constProof_v_rel (:'c) (:'ffi) a x y (CONS x e1)
        (CONS y e2) /\
      bvl_constProof_env_rel (:'c) (:'ffi) rest e1 e2`;
     `bvl_constProof_env_rel (:'c) (:'ffi) (CONS h rest) [] e2
      <=> F`;
     `bvl_constProof_env_rel (:'c) (:'ffi) (CONS h rest)
        (CONS x e1) [] <=> F`] in
   LIST_INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC erc THEN
    DISCH_THEN SUBST1_TAC THEN REFL_TAC;
    REPEAT GEN_TAC THEN
    NAMED_CASES_TAC `h:bvl_exp option` [[]; ["a"]] THEN
    LIST_CASES_TAC ["env"; "env2"] THEN REWRITE_TAC erc THEN
    REWRITE_TAC[LENGTH; SUC_INJ] THEN STRIP_TAC THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let bvl_constProof_env_rel_LLOOKUP_NONE =
  cake_theorem "env_rel_LLOOKUP_NONE[local]"
  (fun () ->
    `!ax env env2 n.
         bvl_constProof_env_rel (:'c) (:'ffi) ax env env2 /\
         ((\l n. oEL n l) ax n = NONE \/ (\l n. oEL n l) ax n =
           SOME NONE) ==>
         EL n env2 = EL n env`)
  (* the environments are the same list up to the entries that the
     relation gives a value for, and oEL is HOL4's LLOOKUP *)
  (let er = cake_def "bvl_constProof_env_rel" in
   let erc = map (fun t ->
     prove(t, GEN_REWRITE_TAC LAND_CONV [er] THEN
              MATCH_REDUCE_TAC THEN REWRITE_TAC[]))
    [`bvl_constProof_env_rel (:'c) (:'ffi) [] e1 e2 <=> (e1 = e2)`;
     `bvl_constProof_env_rel (:'c) (:'ffi) (CONS NONE rest)
        (CONS x e1) (CONS y e2) <=>
      (x = y) /\ bvl_constProof_env_rel (:'c) (:'ffi) rest e1 e2`;
     `bvl_constProof_env_rel (:'c) (:'ffi) (CONS (SOME a) rest)
        (CONS x e1) (CONS y e2) <=>
      bvl_constProof_v_rel (:'c) (:'ffi) a x y (CONS x e1)
        (CONS y e2) /\
      bvl_constProof_env_rel (:'c) (:'ffi) rest e1 e2`;
     `bvl_constProof_env_rel (:'c) (:'ffi) (CONS h rest) [] e2
      <=> F`;
     `bvl_constProof_env_rel (:'c) (:'ffi) (CONS h rest)
        (CONS x e1) [] <=> F`] in
   LIST_INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC erc THEN
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[oEL] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    REPEAT GEN_TAC THEN
    NAMED_CASES_TAC `h:bvl_exp option` [[]; ["a"]] THEN
    LIST_CASES_TAC ["env"; "env2"] THEN
    REWRITE_TAC erc THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    STRUCT_CASES_TAC(SPEC `n:num` num_CASES) THEN
    REWRITE_TAC[oEL; EL; TL; HD; ARITH_EQ; NOT_SUC; SUC_SUB1;
                distinctness "option"; injectivity "option"] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    TRY(FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[])]);;

let bvl_constProof_env_rel_LOOKUP_SOME =
  cake_theorem "env_rel_LOOKUP_SOME[local]"
  (fun () ->
    `!env env2 ax x n.
         bvl_constProof_env_rel (:'c) (:'ffi) ax env env2 /\
         (\l n. oEL n l) ax n = SOME (SOME x) ==>
         bvl_constProof_v_rel (:'c) (:'ffi) x (EL n env) (EL n
           env2) (DROP n env) (DROP n env2)`)
  (* and where the relation does give a value for an entry, that
     value and the two environments from that point on are what
     v_rel relates *)
  (let er = cake_def "bvl_constProof_env_rel" in
   let erc = map (fun t ->
     prove(t, GEN_REWRITE_TAC LAND_CONV [er] THEN
              MATCH_REDUCE_TAC THEN REWRITE_TAC[]))
    [`bvl_constProof_env_rel (:'c) (:'ffi) [] e1 e2 <=> (e1 = e2)`;
     `bvl_constProof_env_rel (:'c) (:'ffi) (CONS NONE rest)
        (CONS x e1) (CONS y e2) <=>
      (x = y) /\ bvl_constProof_env_rel (:'c) (:'ffi) rest e1 e2`;
     `bvl_constProof_env_rel (:'c) (:'ffi) (CONS (SOME a) rest)
        (CONS x e1) (CONS y e2) <=>
      bvl_constProof_v_rel (:'c) (:'ffi) a x y (CONS x e1)
        (CONS y e2) /\
      bvl_constProof_env_rel (:'c) (:'ffi) rest e1 e2`;
     `bvl_constProof_env_rel (:'c) (:'ffi) (CONS h rest) [] e2
      <=> F`;
     `bvl_constProof_env_rel (:'c) (:'ffi) (CONS h rest)
        (CONS x e1) [] <=> F`] in
   LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
   NAMED_CASES_TAC `ax:(bvl_exp option) list` [[]; ["ah"; "at"]] THEN
   TRY(NAMED_CASES_TAC `ah:bvl_exp option` [[]; ["a"]]) THEN
   TRY(LIST_CASES_TAC ["env2"]) THEN
   REWRITE_TAC erc THEN
   STRUCT_CASES_TAC(SPEC `n:num` num_CASES) THEN
   REWRITE_TAC[oEL; EL; TL; HD; DROP; ARITH_EQ; NOT_SUC; SUC_SUB1;
               distinctness "option"; injectivity "option"] THEN
   STRIP_TAC THEN TRY VAR_EQ_TAC THEN ASM_REWRITE_TAC[] THEN
   TRY(FIRST_ASSUM MATCH_MP_TAC THEN
       EXISTS_TAC `at:(bvl_exp option) list` THEN
       ASM_REWRITE_TAC[]));;

let bvl_constProof_evaluate_delete_var_Rerr_SING =
  cake_theorem "evaluate_delete_var_Rerr_SING"
  (fun () ->
    `!x s r e env2.
        evaluate ([x],env2,s) = (Rerr e,r) /\ ~(e = Rabort
          Rtype_error) ==>
        evaluate ([bvl_const_delete_var x],env2,s) = (Rerr e,r)`)
  (* delete_var changes a Var and nothing else, and a Var that
     evaluates to an error is out of range, which is the one error
     that this theorem leaves out *)
  (let dv = cake_def "bvl_const_delete_var" in
   let ev = cake_def "bvlSem_evaluate" in
   let res_rws = [PAIR_EQ;
                  distinctness "semanticPrimitives_result";
                  injectivity "semanticPrimitives_result"] in
   REPEAT GEN_TAC THEN
   STRUCT_CASES_TAC(ISPEC `x:bvl_exp` (cases_of `:bvl_exp`)) THEN
   REWRITE_TAC[dv] THEN MATCH_REDUCE_TAC THEN
   TRY(DISCH_THEN(ACCEPT_TAC o CONJUNCT1)) THEN
   DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
   GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [ev] THEN
   COND_CASES_TAC THEN REWRITE_TAC res_rws THEN ASM_MESON_TAC[]);;

let bvl_constProof_evaluate_delete_var_Rerr =
  cake_theorem "evaluate_delete_var_Rerr[local]"
  (fun () ->
    `!xs s r e env2.
         evaluate (xs,env2,s) = (Rerr e,r) /\ ~(e = Rabort
           Rtype_error) ==>
         evaluate (MAP bvl_const_delete_var xs,env2,s) = (Rerr
           e,r)`)
  (let dv = cake_def "bvl_const_delete_var" in
   let ev = cake_def "bvlSem_evaluate" in
   let da = cake_def "bvlSem_do_app" in
   let dia = cake_def "bvlSem_do_int_app" in
   let fc = cake_def "bvlSem_fix_clock" in
   let res_rws = [PAIR_EQ;
                  distinctness "semanticPrimitives_result";
                  injectivity "semanticPrimitives_result"] in
   (* HOL4 takes the head apart inside this proof and again inside
      the next one (bvl_constProofScript.sml:83-86 and :101-108).
      What its case analysis says is that delete_var changes a Var
      and nothing else, and that the Op it leaves there evaluates
      to a number without touching the state. *)
   let opevi = prove
    (`!i env2 (s:('c,'ffi)bvlSem_state).
        bvlSem_evaluate
          ([(bvl_Op (closLang_IntOp (closLang_Const i)) []):bvl_exp],
           env2,s) = (Rval [(Number i):bvlSem_v],s)`,
     REPEAT GEN_TAC THEN
     REWRITE_TAC[ev; fc; ARITH_RULE `MIN (a:num) a = a`] THEN
     RECORD_CASES_TAC `s:('c,'ffi)bvlSem_state` THEN
     REWRITE_TAC[da; dia; REVERSE] THEN
     MATCH_REDUCE_TAC THEN REWRITE_TAC[]) in
   (* so the head leaves the same state either way ... *)
   let stateq = prove
    (`!(x:bvl_exp) env2 (s:('c,'ffi)bvlSem_state) v t u w.
        bvlSem_evaluate ([x],env2,s) = (v,t) /\
        bvlSem_evaluate ([bvl_const_delete_var x],env2,s) = (u,w)
        ==> w = t`,
     REPEAT GEN_TAC THEN
     STRUCT_CASES_TAC(ISPEC `x:bvl_exp` (cases_of `:bvl_exp`)) THEN
     REWRITE_TAC[dv] THEN MATCH_REDUCE_TAC THEN
     FIRST
      [(* the eight that delete_var leaves alone: one evaluation *)
       SOLVED(DISCH_THEN(fun th ->
                MP_TAC(TRANS (SYM(CONJUNCT2 th)) (CONJUNCT1 th))) THEN
              REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
              ASM_REWRITE_TAC[]);
       (* and the Var, where both leave the state it came in with *)
       (REWRITE_TAC[opevi; ev] THEN COND_CASES_TAC THEN
        REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN VAR_EQ_TAC THEN
        REFL_TAC)]) in
   (* ... and a head that succeeds still succeeds *)
   let valev = prove
    (`!(x:bvl_exp) env2 (s:('c,'ffi)bvlSem_state) v t.
        bvlSem_evaluate ([x],env2,s) = (Rval v,t) ==>
        ?w. bvlSem_evaluate ([bvl_const_delete_var x],env2,s) =
            (Rval w,t)`,
     REPEAT GEN_TAC THEN
     STRUCT_CASES_TAC(ISPEC `x:bvl_exp` (cases_of `:bvl_exp`)) THEN
     REWRITE_TAC[dv] THEN MATCH_REDUCE_TAC THEN
     FIRST
      [SOLVED(DISCH_TAC THEN EXISTS_TAC `v:bvlSem_v list` THEN
              ASM_REWRITE_TAC[]);
       (REWRITE_TAC[opevi; ev] THEN COND_CASES_TAC THEN
        REWRITE_TAC res_rws THEN STRIP_TAC THEN
        EXISTS_TAC `[(Number (&0)):bvlSem_v]` THEN
        ASM_REWRITE_TAC[])]) in
   LIST_INDUCT_TAC THEN REWRITE_TAC[MAP] THENL
    [REPEAT GEN_TAC THEN DISCH_THEN(ACCEPT_TAC o CONJUNCT1);
     ALL_TAC] THEN
   REPEAT GEN_TAC THEN
   GEN_REWRITE_TAC ONCE_DEPTH_CONV [evaluate_CONS] THEN
   REPEAT STRIP_TAC THEN EVERY_CASE_TAC THEN VAR_EQ_TAC THEN
   FIRST
    [(* the head errored, so delete_var's head errors the same way *)
     RES2_THEN bvl_constProof_evaluate_delete_var_Rerr_SING
       (SOLVED(ASM_REWRITE_TAC res_rws));
     (* the head succeeded, so delete_var's head cannot error *)
     RES1_THEN valev (SOLVED(ASM_REWRITE_TAC res_rws));
     (* both succeeded, at the same state: then the hypothesis *)
     RES2_THEN stateq
      (DISCH_THEN SUBST_ALL_TAC THEN
       FIRST_ASSUM(fun ih ->
         RES2_THEN ih (SOLVED(ASM_REWRITE_TAC res_rws))))]);;

let bvl_constProof_evaluate_delete_var_Rval =
  cake_theorem "evaluate_delete_var_Rval[local]"
  (fun () ->
    `!xs env2 s a r ax env.
         evaluate (xs,env2,(s:('c,'ffi)bvlSem_state)) = (Rval a,r)
           /\
         bvl_constProof_env_rel (:'c) (:'ffi) ax env env2 ==>
         (?b. evaluate (MAP bvl_const_delete_var xs,env2,s) = (Rval
           b,r) /\
             bvl_constProof_env_rel (:'c) (:'ffi)
               (bvl_const_extract_list xs ++ ax) (a ++ env) (b ++
               env2))`)
  (let rty = `:(bvlSem_v list,bvlSem_v)
                semanticPrimitives_result` in
   let dv = cake_def "bvl_const_delete_var" in
   let ev = cake_def "bvlSem_evaluate" in
   let da = cake_def "bvlSem_do_app" in
   let dia = cake_def "bvlSem_do_int_app" in
   let fc = cake_def "bvlSem_fix_clock" in
   let ex = cake_def "bvl_const_extract" in
   let exl = cake_def "bvl_const_extract_list" in
   let er = cake_def "bvl_constProof_env_rel" in
   let vr = cake_def "bvl_constProof_v_rel" in
   let res_rws = [PAIR_EQ;
                  distinctness "semanticPrimitives_result";
                  injectivity "semanticPrimitives_result"] in
   let erc = map (fun t ->
     prove(t, GEN_REWRITE_TAC LAND_CONV [er] THEN
              MATCH_REDUCE_TAC THEN REWRITE_TAC[]))
    [`bvl_constProof_env_rel (:'c) (:'ffi) [] e1 e2 <=> (e1 = e2)`;
     `bvl_constProof_env_rel (:'c) (:'ffi) (CONS NONE rest)
        (CONS x e1) (CONS y e2) <=>
      (x = y) /\ bvl_constProof_env_rel (:'c) (:'ffi) rest e1 e2`;
     `bvl_constProof_env_rel (:'c) (:'ffi) (CONS (SOME a) rest)
        (CONS x e1) (CONS y e2) <=>
      bvl_constProof_v_rel (:'c) (:'ffi) a x y (CONS x e1)
        (CONS y e2) /\
      bvl_constProof_env_rel (:'c) (:'ffi) rest e1 e2`] in
   let vrc = map (fun t ->
     prove(t, GEN_REWRITE_TAC LAND_CONV [vr] THEN
              MATCH_REDUCE_TAC THEN REWRITE_TAC[]))
    [`bvl_constProof_v_rel (:'c) (:'ffi) (bvl_Var n) x y xs ys <=>
      oEL n ys = SOME x`;
     `bvl_constProof_v_rel (:'c) (:'ffi) (bvl_Op op es) x y xs ys
      <=> (x = y) /\
          (!(s:('c,'ffi)bvlSem_state) env.
             bvlSem_evaluate ([bvl_Op op es],env,s) =
             (Rval [x],s))`] in
   (* the value of a constant expression, which is what extract
      leaves in the environment of the compiled code *)
   let opevi = prove
    (`!i env2 (s:('c,'ffi)bvlSem_state).
        bvlSem_evaluate
          ([(bvl_Op (closLang_IntOp (closLang_Const i)) []):bvl_exp],
           env2,s) = (Rval [(Number i):bvlSem_v],s)`,
     REPEAT GEN_TAC THEN
     REWRITE_TAC[ev; fc; ARITH_RULE `MIN (a:num) a = a`] THEN
     RECORD_CASES_TAC `s:('c,'ffi)bvlSem_state` THEN
     REWRITE_TAC[da; dia; REVERSE] THEN
     MATCH_REDUCE_TAC THEN REWRITE_TAC[]) in
   let consev = prove
    (`!tg env2 (s:('c,'ffi)bvlSem_state).
        bvlSem_evaluate
          ([(bvl_Op (closLang_BlockOp (closLang_Cons tg))
               []):bvl_exp],
           env2,s) = (Rval [(Block tg []):bvlSem_v],s)`,
     REPEAT GEN_TAC THEN
     REWRITE_TAC[ev; fc; ARITH_RULE `MIN (a:num) a = a`] THEN
     RECORD_CASES_TAC `s:('c,'ffi)bvlSem_state` THEN
     REWRITE_TAC[da; REVERSE] THEN
     MATCH_REDUCE_TAC THEN REWRITE_TAC[]) in
   (* an Op of the integers takes the value that do_int_app gives,
      and the port has do_app as one match over every operation,
      so the clause for this one is taken off it first *)
   let da_int = prove
    (`!iop vs (s:('c,'ffi)bvlSem_state).
        bvlSem_do_app (closLang_IntOp iop) vs s =
        (match bvlSem_do_int_app iop vs with
           SOME res -> Rval (res,s)
         | NONE -> Rerr (Rabort Rtype_error))`,
     REPEAT GEN_TAC THEN REWRITE_TAC[da] THEN EVERY_CASE_TAC) in
   let const_val = prove
    (`!i xs env2 (s:('c,'ffi)bvlSem_state) hv hs.
        bvlSem_evaluate
          ([bvl_Op (closLang_IntOp (closLang_Const i)) xs],env2,s) =
        (Rval hv,hs) ==> hv = [(Number i):bvlSem_v]`,
     REPEAT GEN_TAC THEN
     GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [ev] THEN
     REWRITE_TAC[da_int] THEN EVERY_CASE_TAC THEN
     PRUNE_TAC res_rws THEN
     RULE_ASSUM_TAC(REWRITE_RULE res_rws) THEN
     REWRITE_TAC res_rws THEN STRIP_TAC THEN
     FIRST_ASSUM(fun th ->
       MP_TAC(MATCH_MP (CONJUNCT1 do_int_app_eq_some) th)) THEN
     STRIP_TAC THEN TRY VAR_EQ_TAC THEN ASM_REWRITE_TAC[]) in
   let cons_val = prove
    (`!tg env2 (s:('c,'ffi)bvlSem_state) hv hs.
        bvlSem_evaluate
          ([bvl_Op (closLang_BlockOp (closLang_Cons tg)) []],
           env2,s) = (Rval hv,hs) ==> hv = [(Block tg []):bvlSem_v]`,
     REPEAT GEN_TAC THEN REWRITE_TAC[consev] THEN
     REWRITE_TAC res_rws THEN STRIP_TAC THEN ASM_REWRITE_TAC[]) in
   let null_nil = prove
    (`!l:(A)list. NULL l <=> l = []`,
     LIST_INDUCT_TAC THEN REWRITE_TAC[NULL; NOT_CONS_NIL]) in
   (* HOL4 takes the head apart here as well (its proof reads the
      shape off extract and then evaluates it); what the two cases
      that extract says something about have in common is that the
      expression it leaves is a constant with the value that the
      head had, which is what v_rel asks of it *)
   let extract_vrel = prove
    (`!(x:bvl_exp) ys e env2 (s:('c,'ffi)bvlSem_state) hv hs.
        bvl_const_delete_var x = x /\
        bvl_const_extract x ys = SOME e /\
        bvlSem_evaluate ([x],env2,s) = (Rval hv,hs) ==>
        !ps qs. bvl_constProof_v_rel (:'c) (:'ffi) e (HD hv)
                  (HD hv) ps qs`,
     REPEAT GEN_TAC THEN REWRITE_TAC[ex] THEN EVERY_CASE_TAC THENL
     [REWRITE_TAC[dv; distinctness "bvl_exp"];
      STRIP_TAC THEN TRY VAR_EQ_TAC THEN
      FIRST_ASSUM(fun th -> ASSUME_TAC(MATCH_MP const_val th)) THEN
      REPEAT GEN_TAC THEN REWRITE_TAC vrc THEN
      ASM_REWRITE_TAC[HD; opevi];
      COND_CASES_TAC THEN REWRITE_TAC[distinctness "option"] THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o REWRITE_RULE[null_nil]) THEN
      REWRITE_TAC[injectivity "option"] THEN
      STRIP_TAC THEN TRY VAR_EQ_TAC THEN
      FIRST_ASSUM(fun th -> ASSUME_TAC(MATCH_MP cons_val th)) THEN
      REPEAT GEN_TAC THEN REWRITE_TAC vrc THEN
      ASM_REWRITE_TAC[HD; consev]]) in
   let notvar_eq = prove
    (`!(x:bvl_exp). ~(?i. x = bvl_Var i)
        ==> bvl_const_delete_var x = x`,
     GEN_TAC THEN
     STRUCT_CASES_TAC(ISPEC `x:bvl_exp` (cases_of `:bvl_exp`)) THEN
     REWRITE_TAC[dv] THEN
     REWRITE_TAC[injectivity "bvl_exp"; distinctness "bvl_exp"] THEN
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
   let split_head =
     NAMED_CASES_TAC
       `bvlSem_evaluate ([h],env2,(s:('c,'ffi)bvlSem_state))`
       [["hres"; "hs"]] THEN
     NAMED_CASES_TAC (mk_var("hres",rty)) [["hv"]; ["he"]] THEN
     tidy in
   let split_tail st =
     NAMED_CASES_TAC
       (list_mk_icomb "bvlSem_evaluate"
          [mk_pair(`t:bvl_exp list`,
                   mk_pair(`env2:bvlSem_v list`,st))])
       [["tres"; "ts"]] THEN
     NAMED_CASES_TAC (mk_var("tres",rty)) [["tv"]; ["te"]] THEN
     tidy in
   let use_ih st =
     FIRST_X_ASSUM(fun ih ->
       MP_TAC(SPECL [`env2:bvlSem_v list`; st;
                     `tv:bvlSem_v list`;
                     `r:('c,'ffi)bvlSem_state`;
                     `ax:(bvl_exp option) list`;
                     `env:bvlSem_v list`] ih)) THEN
     ASM_REWRITE_TAC[] THEN
     DISCH_THEN(X_CHOOSE_THEN `bb:bvlSem_v list`
                  STRIP_ASSUME_TAC) in
   (* the empty list: nothing evaluated and nothing extracted *)
   let base_branch =
     REPEAT GEN_TAC THEN REWRITE_TAC[ev] THEN
     REWRITE_TAC[PAIR_EQ;
                 injectivity "semanticPrimitives_result"] THEN
     STRIP_TAC THEN VAR_EQ_TAC THEN
     EXISTS_TAC `[]:bvlSem_v list` THEN
     ASM_REWRITE_TAC[APPEND; ev] in
   (* a head that delete_var leaves alone: the same value in both
      environments, so its entry of the relation is NONE, or the
      constant that extract read off it *)
   let nonvar_branch =
     FIRST_ASSUM(fun nv -> REWRITE_TAC[MATCH_MP notvar_eq nv]) THEN
     STRIP_TAC THEN split_head THEN
     split_tail `hs:('c,'ffi)bvlSem_state` THEN
     use_ih `hs:('c,'ffi)bvlSem_state` THEN
     EXISTS_TAC `HD (hv:bvlSem_v list) :: bb` THEN
     ASM_REWRITE_TAC[] THEN tidy THEN
     REWRITE_TAC[APPEND] THEN
     (* the second argument of extract is only there for its
        length, so the port's extract is polymorphic in it and the
        split has to say which list this one is *)
     NAMED_CASES_TAC
       `bvl_const_extract (h:bvl_exp) (t:bvl_exp list)`
       [[]; ["ee"]] THEN
     ASM_REWRITE_TAC[] THEN REWRITE_TAC erc THEN
     ASM_REWRITE_TAC[] THEN
     FIRST_ASSUM(fun nv -> FIRST_ASSUM(fun b -> FIRST_ASSUM(fun c ->
       REWRITE_TAC[MATCH_MP extract_vrel
                     (CONJ (MATCH_MP notvar_eq nv) (CONJ b c))]))) in
   (* and a Var, where delete_var put the Op: the value the Var
      read is still in the second environment, at the offset that
      the extract records -- past the number the Op left and past
      the values of the rest of the list *)
   let var_branch =
     FIRST_X_ASSUM(X_CHOOSE_THEN `i:num` SUBST1_TAC) THEN
     REWRITE_TAC[dv; ex] THEN SAFE_MATCH_REDUCE_TAC THEN
     REWRITE_TAC[opevi] THEN
     GEN_REWRITE_TAC ONCE_DEPTH_CONV [ev] THEN
     ASM_CASES_TAC `i < LENGTH (env2:bvlSem_v list)` THEN
     ASM_REWRITE_TAC[HD] THEN tidy THEN STRIP_TAC THEN tidy THEN
     split_tail `s:('c,'ffi)bvlSem_state` THEN
     use_ih `s:('c,'ffi)bvlSem_state` THEN
     EXISTS_TAC `((Number (&0)):bvlSem_v) :: bb` THEN
     ASM_REWRITE_TAC[] THEN tidy THEN
     REWRITE_TAC[APPEND] THEN REWRITE_TAC erc THEN
     REWRITE_TAC vrc THEN
     SUBGOAL_THEN
       `LENGTH (t:bvl_exp list) = LENGTH (bb:bvlSem_v list)`
       SUBST1_TAC THENL
     [FIRST_ASSUM(fun th -> ACCEPT_TAC(REWRITE_RULE[LENGTH_MAP]
        (MATCH_MP evaluate_IMP_LENGTH th)));
      ALL_TAC] THEN
     REWRITE_TAC[oEL; ARITH_RULE `~(i + n + 1 = 0)`;
                 ARITH_RULE `(i + n + 1) - 1 = i + n`] THEN
     REWRITE_TAC[oEL_APPEND] THEN
     FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP oEL_EL th]) THEN
     ASM_REWRITE_TAC[] in
   LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; exl; APPEND] THENL
    [base_branch; ALL_TAC] THEN
   REPEAT GEN_TAC THEN
   GEN_REWRITE_TAC ONCE_DEPTH_CONV [evaluate_CONS] THEN
   ASM_CASES_TAC `?i. (h:bvl_exp) = bvl_Var i` THENL
   [var_branch; nonvar_branch]);;

let evaluate_EQ_NIL = cake_theorem "evaluate_EQ_NIL"
  (fun () ->
    `bvlSem_evaluate (xs,env,s) = (Rval [],t) <=> xs = [] /\ s = t`)
  CHEAT_TAC;;

let dest_simple_eq = cake_theorem "dest_simple_eq[local]"
  (fun () ->
    `dest_simple h = SOME y <=> (h = Op (closLang_IntOp
  (closLang_Const y)) [])`)
  CHEAT_TAC;;

let case_op_const_eq = cake_theorem "case_op_const_eq[local]"
  (fun () ->
    `case_op_const exp = SOME x <=>
     (?op x1 n2. x = (op,x1,n2) /\ (exp = Op op [x1; Op
       (closLang_IntOp (closLang_Const n2)) []]))`)
  CHEAT_TAC;;

let SmartOp_flip_thm = cake_theorem "SmartOp_flip_thm[local]"
  (fun () ->
    `(op',x1',x2') = SmartOp_flip op x1 x2 /\
     evaluate ([Op op [x1; x2]],env,s) = (res,s2) /\ ~(res = Rerr
       (Rabort Rtype_error)) ==>
     evaluate ([Op op' [x1'; x2']],env,s) = (res,s2)`)
  CHEAT_TAC;;

let SmartOp2_thm = cake_theorem "SmartOp2_thm[local]"
  (fun () ->
    `evaluate ([Op op [x1; x2]],env,s) = (res,s2) /\ ~(res = Rerr
  (Rabort Rtype_error)) ==>
     evaluate ([SmartOp2 (op,x1,x2)],env,s) = (res,s2)`)
  CHEAT_TAC;;

let SmartOp1_thm = cake_theorem "SmartOp1_thm"
  (fun () ->
    `evaluate ([Op op [x]],env,s) = (res,s2) /\ ~(res = Rerr (Rabort
  Rtype_error)) ==>
     evaluate ([SmartOp1 op x],env,s) = (res,s2)`)
  CHEAT_TAC;;

let SmartOp_thm = cake_theorem "SmartOp_thm"
  (fun () ->
    `evaluate ([Op op xs],env,s) = (res,s2) /\ ~(res = Rerr (Rabort
  Rtype_error)) ==>
      evaluate ([SmartOp op xs],env,s) = (res,s2)`)
  CHEAT_TAC;;

let bvl_constProof_evaluate_env_rel = cake_theorem "evaluate_env_rel"
  (fun () ->
    `!xs env1 (s1:('c,'ffi)bvlSem_state) ax env2 res s2 ys.
        (evaluate (xs,env1,s1) = (res,s2)) /\
        bvl_constProof_env_rel (:'c) (:'ffi) ax env1 env2 /\ ~(res
          = Rerr (Rabort Rtype_error)) ==>
        (evaluate (compile ax xs,env2,s1) = (res,s2))`)
  CHEAT_TAC;;

(* HOL4 bvl_constProofScript.sml:311-314: a theorem that HOL4 states
   as the value of an ML expression: compile_thm *)

let bvl_constProof_evaluate_compile_exp =
  cake_theorem "evaluate_compile_exp"
  (fun () ->
    `evaluate ([d],env,s) = (r,t) /\ ~(r = Rerr (Rabort Rtype_error))
  ==>
      evaluate ([bvl_const_compile_exp d],env,s) = (r,t)`)
  CHEAT_TAC;;

let delete_var_code_labels = cake_theorem "delete_var_code_labels[simp]"
  (fun () ->
    `!x. bvlProps_get_code_labels (bvl_const_delete_var x) =
  bvlProps_get_code_labels x`)
  CHEAT_TAC;;

let dest_simple_SOME_code_labels =
  cake_theorem "dest_simple_SOME_code_labels"
  (fun () ->
    `!x y. dest_simple x = SOME y ==> bvlProps_get_code_labels x = {}`)
  CHEAT_TAC;;

let SmartOp2_code_labels = cake_theorem "SmartOp2_code_labels[simp]"
  (fun () ->
    `bvlProps_get_code_labels (SmartOp2 (op,x1,x2)) =
      assign_get_code_label op UNION bvlProps_get_code_labels x1
        UNION bvlProps_get_code_labels x2`)
  CHEAT_TAC;;

let SmartOp1_code_labels = cake_theorem "SmartOp1_code_labels"
  (fun () ->
    `bvlProps_get_code_labels (SmartOp1 op x) =
  bvlProps_get_code_labels (Op op [x])`)
  CHEAT_TAC;;

let SmartOp_code_labels = cake_theorem "SmartOp_code_labels[simp]"
  (fun () ->
    `bvlProps_get_code_labels (SmartOp op xs) =
     assign_get_code_label op UNION BIGUNION (set_of_list (MAP
       bvlProps_get_code_labels xs))`)
  CHEAT_TAC;;

let MEM_extract_list_code_labels =
  cake_theorem "MEM_extract_list_code_labels"
  (fun () ->
    `!xs x. MEM (SOME x) (bvl_const_extract_list xs) ==>
  bvlProps_get_code_labels x = {}`)
  CHEAT_TAC;;

let bvl_constProof_compile_code_labels =
  cake_theorem "compile_code_labels"
  (fun () ->
    `!x y. BIGUNION (set_of_list (MAP bvlProps_get_code_labels
  (bvl_const_compile x y))) SUBSET
           BIGUNION (set_of_list (MAP bvlProps_get_code_labels y))
             UNION
           BIGUNION (set_of_list (MAP (bvlProps_get_code_labels o
             THE) (FILTER IS_SOME x)))`)
  CHEAT_TAC;;

let bvl_constProof_compile_exp_code_labels =
  cake_theorem "compile_exp_code_labels"
  (fun () ->
    `!e. bvlProps_get_code_labels (bvl_const_compile_exp e) SUBSET
  bvlProps_get_code_labels e`)
  CHEAT_TAC;;
