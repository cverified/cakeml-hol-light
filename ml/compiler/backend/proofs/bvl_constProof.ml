(* ======================================================== *)
(*  bvl_constProof: ported from HOL4's
    compiler/backend/proofs/bvl_constProofScript.sml
    A proof theory about bvl_const.ml, with 2 definitions and 24
    theorems.  Needed by bvl_handleProof.ml and bvl_to_bviProof.ml.  *)
(* ======================================================== *)

(*
  Correctness proof for bvl_const
*)

needs "basis/pure/mllist.ml";;
needs "compiler/backend/bvl_const.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/flat_elim.ml";;
needs "compiler/backend/reg_alloc/linear_scan.ml";;
needs "compiler/backend/semantics/bvlProps.ml";;
needs "compiler/backend/semantics/bvlSem.ml";;
needs "compiler/backend/semantics/closSem.ml";;
needs "compiler/inference/unify.ml";;
needs "lib/balanced_map.ml";;
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

let bvl_constProof_v_rel_def = cake_define
  `bvl_constProof_v_rel (:'c) (:'ffi) a x y xs ys =
     (match a with Var n -> (\l n. oEL n l) ys n = SOME x | Op _1 _2
       ->
       (x = y) /\
       (!(s:('c,'ffi)bvlSem_state) env. evaluate ([a],env,s) =
         (Rval [x],s)) | _3 -> F)`;;
hol4_overload "v_rel" "bvl_constProof_v_rel";;

let bvl_constProof_env_rel_def = cake_define
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

(* env_rel_length *)
let bvl_constProof_env_rel_length = prove
 (`!ax env env2. bvl_constProof_env_rel (:'c) (:'ffi) ax env env2 ==>
  LENGTH env2 = LENGTH env`,
  (* HOL4 states env_rel as four clauses, which its Induct and its
     fs [env_rel_def] use one at a time; the port states it as one
     match on the tuple of the arguments, so the clauses are taken
     off it first.  Every proof of this file that unfolds the
     relation starts that way (the rewrite is a LAND_CONV, because
     the relation stands on both sides of the clause it proves). *)
  (let er = bvl_constProof_env_rel_def in
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
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]));;

(* env_rel_LLOOKUP_NONE[local] *)
let bvl_constProof_env_rel_LLOOKUP_NONE = prove
 (`!ax env env2 n.
       bvl_constProof_env_rel (:'c) (:'ffi) ax env env2 /\
       ((\l n. oEL n l) ax n = NONE \/ (\l n. oEL n l) ax n = SOME
         NONE) ==>
       EL n env2 = EL n env`,
  (* the environments are the same list up to the entries that the
     relation gives a value for, and oEL is HOL4's LLOOKUP *)
  (let er = bvl_constProof_env_rel_def in
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
    TRY(FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[])]));;

(* env_rel_LOOKUP_SOME[local] *)
let bvl_constProof_env_rel_LOOKUP_SOME = prove
 (`!env env2 ax x n.
       bvl_constProof_env_rel (:'c) (:'ffi) ax env env2 /\
       (\l n. oEL n l) ax n = SOME (SOME x) ==>
       bvl_constProof_v_rel (:'c) (:'ffi) x (EL n env) (EL n env2)
         (DROP n env) (DROP n env2)`,
  (* and where the relation does give a value for an entry, that
     value and the two environments from that point on are what
     v_rel relates *)
  (let er = bvl_constProof_env_rel_def in
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
       ASM_REWRITE_TAC[])));;

(* evaluate_delete_var_Rerr_SING *)
let bvl_constProof_evaluate_delete_var_Rerr_SING = prove
 (`!x s r e env2.
      evaluate ([x],env2,s) = (Rerr e,r) /\ ~(e = Rabort Rtype_error)
        ==>
      evaluate ([bvl_const_delete_var x],env2,s) = (Rerr e,r)`,
  (* delete_var changes a Var and nothing else, and a Var that
     evaluates to an error is out of range, which is the one error
     that this theorem leaves out *)
  (let dv = bvl_const_delete_var_def in
   let ev = bvlSem_evaluate_def in
   let res_rws = [PAIR_EQ;
                  distinctness "semanticPrimitives_result";
                  injectivity "semanticPrimitives_result"] in
   REPEAT GEN_TAC THEN
   STRUCT_CASES_TAC(ISPEC `x:bvl_exp` (cases_of `:bvl_exp`)) THEN
   REWRITE_TAC[dv] THEN MATCH_REDUCE_TAC THEN
   TRY(DISCH_THEN(ACCEPT_TAC o CONJUNCT1)) THEN
   DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
   GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [ev] THEN
   COND_CASES_TAC THEN REWRITE_TAC res_rws THEN ASM_MESON_TAC[]));;

(* evaluate_delete_var_Rerr[local] *)
let bvl_constProof_evaluate_delete_var_Rerr = prove
 (`!xs s r e env2.
       evaluate (xs,env2,s) = (Rerr e,r) /\ ~(e = Rabort Rtype_error)
         ==>
       evaluate (MAP bvl_const_delete_var xs,env2,s) = (Rerr e,r)`,
  (let dv = bvl_const_delete_var_def in
   let ev = bvlSem_evaluate_def in
   let da = bvlSem_do_app_def in
   let dia = bvlSem_do_int_app_def in
   let fc = bvlSem_fix_clock_def in
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
         RES2_THEN ih (SOLVED(ASM_REWRITE_TAC res_rws))))]));;

(* evaluate_delete_var_Rval[local] *)
let bvl_constProof_evaluate_delete_var_Rval = prove
 (`!xs env2 s a r ax env.
       evaluate (xs,env2,(s:('c,'ffi)bvlSem_state)) = (Rval a,r) /\
       bvl_constProof_env_rel (:'c) (:'ffi) ax env env2 ==>
       (?b. evaluate (MAP bvl_const_delete_var xs,env2,s) = (Rval
         b,r) /\
           bvl_constProof_env_rel (:'c) (:'ffi)
             (bvl_const_extract_list xs ++ ax) (a ++ env) (b ++ env2))`,
  (let rty = `:(bvlSem_v list,bvlSem_v)
                semanticPrimitives_result` in
   let dv = bvl_const_delete_var_def in
   let ev = bvlSem_evaluate_def in
   let da = bvlSem_do_app_def in
   let dia = bvlSem_do_int_app_def in
   let fc = bvlSem_fix_clock_def in
   let ex = bvl_const_extract_def in
   let exl = bvl_const_extract_list_def in
   let er = bvl_constProof_env_rel_def in
   let vr = bvl_constProof_v_rel_def in
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
   [var_branch; nonvar_branch]));;

let evaluate_EQ_NIL = prove
 (`bvlSem_evaluate (xs,env,s) = (Rval [],t) <=> xs = [] /\ s = t`,
  (* the lengths of the expressions and of the values they
     evaluate to are the same, so a result of no values comes from
     no expressions, and no expression touches the state *)
  (let ev = bvlSem_evaluate_def in
   EQ_TAC THENL
   [DISCH_TAC THEN
    FIRST_ASSUM(fun th ->
      MP_TAC(MATCH_MP evaluate_IMP_LENGTH th)) THEN
    REWRITE_TAC[LENGTH; LENGTH_EQ_NIL] THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    POP_ASSUM MP_TAC THEN REWRITE_TAC[ev; PAIR_EQ] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[];
    STRIP_TAC THEN ASM_REWRITE_TAC[ev]]));;

(* [local] *)
let dest_simple_eq = prove
 (`dest_simple h = SOME y <=> (h = Op (closLang_IntOp (closLang_Const
  y)) [])`,
  (* the case split of HOL4 is the split along the patterns of the
     match, which EVERY_CASE_TAC makes (PORTING-GUIDE.md entry 1) *)
  (let ds = dest_simple_def in
   let con_rws =
     [distinctness "bvl_exp"; injectivity "bvl_exp";
      distinctness "closLang_op"; injectivity "closLang_op";
      distinctness "closLang_int_op";
      injectivity "closLang_int_op";
      distinctness "block_op"; injectivity "block_op";
      distinctness "const_part"; injectivity "const_part";
      distinctness "option"; injectivity "option"] in
   let null_nil = prove
    (`!l:(A)list. NULL l <=> l = []`,
     LIST_INDUCT_TAC THEN REWRITE_TAC[NULL; NOT_CONS_NIL]) in
   REWRITE_TAC[ds] THEN EVERY_CASE_TAC THEN
   REWRITE_TAC(NULL :: null_nil :: con_rws) THEN
   COND_CASES_TAC THEN ASM_REWRITE_TAC con_rws));;

(* [local] *)
let case_op_const_eq = prove
 (`case_op_const exp = SOME x <=>
   (?op x1 n2. x = (op,x1,n2) /\ (exp = Op op [x1; Op
     (closLang_IntOp (closLang_Const n2)) []]))`,
  (let coc = case_op_const_def in
   let con_rws =
     [distinctness "bvl_exp"; injectivity "bvl_exp";
      distinctness "closLang_op"; injectivity "closLang_op";
      distinctness "closLang_int_op";
      injectivity "closLang_int_op";
      distinctness "block_op"; injectivity "block_op";
      distinctness "const_part"; injectivity "const_part";
      distinctness "option"; injectivity "option"] in
   let null_nil = prove
    (`!l:(A)list. NULL l <=> l = []`,
     LIST_INDUCT_TAC THEN REWRITE_TAC[NULL; NOT_CONS_NIL]) in
   REWRITE_TAC[coc] THEN EVERY_CASE_TAC THEN
   REWRITE_TAC(NULL :: null_nil :: PAIR_EQ :: con_rws) THEN
   COND_CASES_TAC THEN ASM_REWRITE_TAC con_rws THEN
   TRY(MATCH_ACCEPT_TAC EQ_SYM_EQ)));;

(* [local] *)
let SmartOp_flip_thm = prove
 (`(op',x1',x2') = SmartOp_flip op x1 x2 /\
   evaluate ([Op op [x1; x2]],env,s) = (res,s2) /\ ~(res = Rerr
     (Rabort Rtype_error)) ==>
   evaluate ([Op op' [x1'; x2']],env,s) = (res,s2)`,
  (* SmartOp_flip moves a constant from the left of an operation to
     the right, which costs nothing because a constant cannot fail
     and leaves the state alone, and the operations it does it for
     are the ones where the two sides can be swapped *)
  (let ev = bvlSem_evaluate_def in
   let da = bvlSem_do_app_def in
   let dia = bvlSem_do_int_app_def in
   let fc = bvlSem_fix_clock_def in
   let sof = SmartOp_flip_def in
   let fce = bvlSem_fix_clock_evaluate in
   let rty = `:(bvlSem_v list,bvlSem_v)
                semanticPrimitives_result` in
   let res_rws = [PAIR_EQ;
                  distinctness "semanticPrimitives_result";
                  injectivity "semanticPrimitives_result"] in
   let tidy =
     TRY SAFE_MATCH_REDUCE_TAC THEN TRY SAFE_MATCH_REDUCE_ASM_TAC THEN
     PRUNE_TAC res_rws THEN MATCH_TIDY_TAC THEN SPLIT_ASM_TAC THEN
     VAR_EQ_TAC in
   let sing_tac =
     REPEAT(FIRST_X_ASSUM(fun th ->
       CHOOSE_THEN SUBST_ALL_TAC (MATCH_MP evaluate_SING th))) in
   (* the value of a constant expression *)
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
   (* an operation of two expressions evaluates them left to right
      and applies do_app to the two values the other way round
      (do_app takes the REVERSE of them) *)
   let ev_pair = prove
    (`!y1 y2 op env (s:('c,'ffi)bvlSem_state).
        bvlSem_evaluate ([bvl_Op op [y1; y2]],env,s) =
        (match bvlSem_evaluate ([y1],env,s) with
           (Rval v1,s1) ->
             (match bvlSem_evaluate ([y2],env,s1) with
                (Rval v2,s2) ->
                  (match bvlSem_do_app op [HD v2; HD v1] s2 with
                     Rerr err -> (Rerr err,s2)
                   | Rval (v,s3) -> (Rval [v],s3))
              | res -> res)
         | res -> res)`,
     REPEAT GEN_TAC THEN
     GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [ev] THEN
     REWRITE_TAC[fce] THEN
     GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
       [evaluate_CONS] THEN
     NAMED_CASES_TAC
       `bvlSem_evaluate ([y1],env,(s:('c,'ffi)bvlSem_state))`
       [["r1"; "t1"]] THEN
     NAMED_CASES_TAC (mk_var("r1",rty)) [["v1"]; ["e1"]] THEN
     tidy THEN
     TRY(NAMED_CASES_TAC
           `bvlSem_evaluate ([y2],env,(t1:('c,'ffi)bvlSem_state))`
           [["r2"; "t2"]] THEN
         NAMED_CASES_TAC (mk_var("r2",rty)) [["v2"]; ["e2"]] THEN
         tidy) THEN
     sing_tac THEN REWRITE_TAC[REVERSE; APPEND; HD] THEN
     REWRITE_TAC[injectivity "semanticPrimitives_result";
                 EXISTS_REFL] THEN
     MATCH_TIDY_TAC THEN REWRITE_TAC[]) in
   (* an operation of the integers takes the value that
      do_int_app gives it, which is the one clause of do_app that
      this proof needs *)
   let da_int = prove
    (`!iop vs (s:('c,'ffi)bvlSem_state).
        bvlSem_do_app (closLang_IntOp iop) vs s =
        (match bvlSem_do_int_app iop vs with
           SOME res -> Rval (res,s)
         | NONE -> Rerr (Rabort Rtype_error))`,
     REPEAT GEN_TAC THEN REWRITE_TAC[da] THEN EVERY_CASE_TAC) in
   (* and the two sides of an addition and of a multiplication can
      be swapped, where a subtraction becomes an addition of the
      negated constant *)
   let dia_comm = prove
    (`!w i. (bvlSem_do_int_app closLang_Add [w; Number i] =
             bvlSem_do_int_app closLang_Add [Number i; w]) /\
            (bvlSem_do_int_app closLang_Mult [w; Number i] =
             bvlSem_do_int_app closLang_Mult [Number i; w]) /\
            (bvlSem_do_int_app closLang_Sub [w; Number i] =
             bvlSem_do_int_app closLang_Add [Number (--i); w])`,
     REPEAT GEN_TAC THEN REPEAT CONJ_TAC THEN
     STRUCT_CASES_TAC(ISPEC `w:bvlSem_v` (cases_of `:bvlSem_v`)) THEN
     REWRITE_TAC[dia] THEN TRY MATCH_REDUCE_TAC THEN
     REWRITE_TAC[injectivity "option"] THEN
     REWRITE_TAC[injectivity "bvlSem_v"] THEN INT_ARITH_TAC) in
   let use_changed rws =
     FIRST_X_ASSUM(fun th ->
       let th' = REWRITE_RULE rws th in
       if concl th' = concl th then failwith "use_changed"
       else MP_TAC th') in
   let swap_tac =
     TRY(FIRST_X_ASSUM(DISJ_CASES_THEN SUBST_ALL_TAC)) THEN
     RULE_ASSUM_TRY(REWRITE_RULE[dest_simple_eq]) THEN
     VAR_EQ_TAC THEN
     use_changed [ev_pair; opevi] THEN
     REWRITE_TAC[ev_pair; opevi] THEN
     NAMED_CASES_TAC
       `bvlSem_evaluate ([x2],env,(s:('c,'ffi)bvlSem_state))`
       [["r2"; "t2"]] THEN
     NAMED_CASES_TAC (mk_var("r2",rty)) [["v2"]; ["e2"]] THEN
     tidy THEN sing_tac THEN
     REWRITE_TAC[HD; da_int; dia_comm] THEN
     TRY(DISCH_THEN ACCEPT_TAC) in
   REPEAT GEN_TAC THEN
   DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
   REWRITE_TAC[sof] THEN EVERY_CASE_TAC THEN
   REWRITE_TAC[MEM] THEN REPEAT COND_CASES_TAC THEN
   REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN VAR_EQ_TAC THEN
   TRY(SOLVED(FIRST_ASSUM ACCEPT_TAC)) THEN swap_tac));;

(* [local] *)
let SmartOp2_thm = prove
 (`evaluate ([Op op [x1; x2]],env,s) = (res,s2) /\ ~(res = Rerr (Rabort
  Rtype_error)) ==>
   evaluate ([SmartOp2 (op,x1,x2)],env,s) = (res,s2)`,
  (* The constant folding, which is where the work of this file is:
     SmartOp2 looks at eleven operations and at the shape of the two
     expressions, and every expression it builds has to evaluate to
     what the original did.  HOL4 does it with gvs and AllCaseEqs
     and intLib.COOPER_TAC; here the operation is decided first, the
     matches of dest_simple and case_op_const after it, and what is
     left of each branch is an evaluation of the same atoms in the
     same order with an integer identity between the results.
     Twenty-two of the thirty-one branches close with the general
     tactic below; the nine that restructure two operations at once
     are the folding lemmas, whose atoms the proof has to name.
     (Two minutes, of which the lemmas are three quarters.) *)
  (let ev = bvlSem_evaluate_def in
   let da = bvlSem_do_app_def in
   let de = bvlSem_do_eq_def in
   let dia = bvlSem_do_int_app_def in
   let fc = bvlSem_fix_clock_def in
   let bl = bool_def in
   let bv = bvlSem_Boolv_def in
   let so2 = SmartOp2_def in
   let fce = bvlSem_fix_clock_evaluate in
   let rty = `:(bvlSem_v list,bvlSem_v)
                semanticPrimitives_result` in
   let res_rws = [PAIR_EQ;
                  distinctness "semanticPrimitives_result";
                  injectivity "semanticPrimitives_result"] in
   let con_rws =
     [distinctness "bvl_exp"; injectivity "bvl_exp";
      distinctness "closLang_op"; injectivity "closLang_op";
      distinctness "closLang_int_op";
      injectivity "closLang_int_op";
      distinctness "block_op"; injectivity "block_op";
      distinctness "const_part"; injectivity "const_part";
      distinctness "option"; injectivity "option"] in
   let eqr = [distinctness "eq_result"; injectivity "eq_result"] in
   let tidy =
     TRY SAFE_MATCH_REDUCE_TAC THEN TRY SAFE_MATCH_REDUCE_ASM_TAC THEN
     PRUNE_TAC res_rws THEN MATCH_TIDY_TAC THEN SPLIT_ASM_TAC THEN
     VAR_EQ_TAC in
   let sing_tac =
     REPEAT(FIRST_X_ASSUM(fun th ->
       CHOOSE_THEN SUBST_ALL_TAC (MATCH_MP evaluate_SING th))) in
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
   let bool_ev = prove
    (`!b env2 (s:('c,'ffi)bvlSem_state).
        bvlSem_evaluate ([bvl_Bool b],env2,s) =
        (Rval [bvlSem_Boolv b],s)`,
     REPEAT GEN_TAC THEN
     REWRITE_TAC[bl; bv; ev; fc; ARITH_RULE `MIN (a:num) a = a`] THEN
     RECORD_CASES_TAC `s:('c,'ffi)bvlSem_state` THEN
     REWRITE_TAC[da; REVERSE] THEN
     MATCH_REDUCE_TAC THEN REWRITE_TAC[]) in
   let ev_pair = prove
    (`!y1 y2 op env (s:('c,'ffi)bvlSem_state).
        bvlSem_evaluate ([bvl_Op op [y1; y2]],env,s) =
        (match bvlSem_evaluate ([y1],env,s) with
           (Rval v1,s1) ->
             (match bvlSem_evaluate ([y2],env,s1) with
                (Rval v2,s2) ->
                  (match bvlSem_do_app op [HD v2; HD v1] s2 with
                     Rerr err -> (Rerr err,s2)
                   | Rval (v,s3) -> (Rval [v],s3))
              | res -> res)
         | res -> res)`,
     REPEAT GEN_TAC THEN
     GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [ev] THEN
     REWRITE_TAC[fce] THEN
     GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
       [evaluate_CONS] THEN
     NAMED_CASES_TAC
       `bvlSem_evaluate ([y1],env,(s:('c,'ffi)bvlSem_state))`
       [["r1"; "t1"]] THEN
     NAMED_CASES_TAC (mk_var("r1",rty)) [["v1"]; ["e1"]] THEN
     tidy THEN
     TRY(NAMED_CASES_TAC
           `bvlSem_evaluate ([y2],env,(t1:('c,'ffi)bvlSem_state))`
           [["r2"; "t2"]] THEN
         NAMED_CASES_TAC (mk_var("r2",rty)) [["v2"]; ["e2"]] THEN
         tidy) THEN
     sing_tac THEN REWRITE_TAC[REVERSE; APPEND; HD] THEN
     REWRITE_TAC[injectivity "semanticPrimitives_result";
                 EXISTS_REFL] THEN
     MATCH_TIDY_TAC THEN REWRITE_TAC[]) in
   let ev_one = prove
    (`!y op env (s:('c,'ffi)bvlSem_state).
        bvlSem_evaluate ([bvl_Op op [y]],env,s) =
        (match bvlSem_evaluate ([y],env,s) with
           (Rval v,t) ->
             (match bvlSem_do_app op [HD v] t with
                Rerr err -> (Rerr err,t)
              | Rval (w,t') -> (Rval [w],t'))
         | res -> res)`,
     REPEAT GEN_TAC THEN
     GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [ev] THEN
     REWRITE_TAC[fce] THEN
     NAMED_CASES_TAC
       `bvlSem_evaluate ([y],env,(s:('c,'ffi)bvlSem_state))`
       [["r1"; "t1"]] THEN
     NAMED_CASES_TAC (mk_var("r1",rty)) [["v1"]; ["e1"]] THEN
     tidy THEN sing_tac THEN REWRITE_TAC[REVERSE; APPEND; HD] THEN
     REWRITE_TAC[injectivity "semanticPrimitives_result";
                 EXISTS_REFL] THEN
     MATCH_TIDY_TAC THEN REWRITE_TAC[]) in
   let da_int = prove
    (`!iop vs (s:('c,'ffi)bvlSem_state).
        bvlSem_do_app (closLang_IntOp iop) vs s =
        (match bvlSem_do_int_app iop vs with
           SOME res -> Rval (res,s)
         | NONE -> Rerr (Rabort Rtype_error))`,
     REPEAT GEN_TAC THEN REWRITE_TAC[da] THEN EVERY_CASE_TAC) in
   (* the value of an operation of two numbers, which is the one
      shape of do_int_app that the folding needs; unfolding the
      definition itself costs minutes over the branches *)
   let dia_num = end_itlist CONJ (map (fun t ->
     prove(t, REWRITE_TAC[dia] THEN TRY MATCH_REDUCE_TAC THEN
              REWRITE_TAC[]))
    [`bvlSem_do_int_app closLang_Add [Number a; Number b] =
      SOME (Number (a + b))`;
     `bvlSem_do_int_app closLang_Sub [Number a; Number b] =
      SOME (Number (a - b))`;
     `bvlSem_do_int_app closLang_Mult [Number a; Number b] =
      SOME (Number (a * b))`;
     `bvlSem_do_int_app closLang_Div [Number a; Number b] =
      (if b = &0 then NONE else SOME (Number (a / b)))`;
     `bvlSem_do_int_app closLang_Mod [Number a; Number b] =
      (if b = &0 then NONE else SOME (Number (a % b)))`;
     `bvlSem_do_int_app closLang_Less [Number a; Number b] =
      SOME (bvlSem_Boolv (a < b))`;
     `bvlSem_do_int_app closLang_LessEq [Number a; Number b] =
      SOME (bvlSem_Boolv (a <= b))`;
     `bvlSem_do_int_app closLang_Greater [Number a; Number b] =
      SOME (bvlSem_Boolv (a > b))`;
     `bvlSem_do_int_app closLang_GreaterEq [Number a; Number b] =
      SOME (bvlSem_Boolv (a >= b))`;
     `bvlSem_do_int_app (closLang_Const n) [] =
      SOME (Number n)`]) in
   (* HOL4's do_int_app_eq_some, which says what the arguments were
      when the operation gave a value: this is how the proof learns
      that they are numbers *)
   let dia_eqs = CONJUNCTS do_int_app_eq_some in
   let use_dia (asl,w as gl) =
     let ths = mapfilter (fun (_,th) ->
       tryfind (fun l -> MATCH_MP l th) dia_eqs) asl in
     MAP_EVERY STRIP_ASSUME_TAC ths gl in
   let norm =
     RULE_ASSUM_TRY(REWRITE_RULE([HD; da_int; dia_num; CONS_11;
                                  injectivity "bvlSem_v"]
                                 @ res_rws)) THEN
     TRY(REWRITE_TAC[HD; da_int; dia_num]) THEN
     SPLIT_ASM_TAC THEN VAR_EQ_TAC THEN
     RULE_ASSUM_TRY(REWRITE_RULE (con_rws @ res_rws)) THEN
     TRY(FIRST_ASSUM CONTR_TAC) in
   let int_ring_fin (asl,w as gl) =
     let eqs = filter (fun (_,th) ->
         try type_of(lhs(concl th)) = `:int`
         with Failure _ -> false) asl in
     (MAP_EVERY (fun (_,th) -> MP_TAC th) eqs THEN
      CONV_TAC INT_RING) gl in
   let fin =
     TRY ASM_FS_TAC THEN norm THEN
     TRY(DISCH_THEN STRIP_ASSUME_TAC) THEN VAR_EQ_TAC THEN norm THEN
     TRY(ASM_REWRITE_TAC[]) THEN
     REWRITE_TAC[injectivity "semanticPrimitives_result"; CONS_11;
                 injectivity "bvlSem_v"; PAIR_EQ] THEN
     REPEAT CONJ_TAC THEN
     TRY(ASM_INT_ARITH_TAC ORELSE int_ring_fin) in
   (* El of a constant index is the ElemAt of that index ... *)
   let int_lt_num = prove
    (`!i n. (&0) <= i ==> (i < &n <=> num_of_int i < n)`,
     REPEAT STRIP_TAC THEN
     FIRST_ASSUM(fun th ->
       GEN_REWRITE_TAC (LAND_CONV o LAND_CONV)
         [SYM(MATCH_MP INT_OF_NUM_OF_INT th)]) THEN
     REWRITE_TAC[INT_OF_NUM_LT]) in
   let el_elemat = prove
    (`!i v (s:('c,'ffi)bvlSem_state). (&0) <= i ==>
        bvlSem_do_app (closLang_MemOp closLang_El) [v; Number i] s =
        bvlSem_do_app (closLang_BlockOp
                         (closLang_ElemAt (num_of_int i))) [v] s`,
     REPEAT GEN_TAC THEN DISCH_TAC THEN
     STRUCT_CASES_TAC(ISPEC `v:bvlSem_v` (cases_of `:bvlSem_v`)) THEN
     REWRITE_TAC[da] THEN TRY SAFE_MATCH_REDUCE_TAC THEN
     ASM_REWRITE_TAC[] THEN EVERY_CASE_TAC THEN
     FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP int_lt_num th])) in
   let el_le = INT_ARITH `!i:int. ~(i < &0) ==> &0 <= i` in
   let el_tac =
     TRY(FIRST_ASSUM(fun th ->
       let eq = MATCH_MP el_elemat (MATCH_MP el_le th) in
       RULE_ASSUM_TRY(REWRITE_RULE[eq]) THEN
       TRY(REWRITE_TAC[eq]))) in
   (* ... and an equality with a constant is the EqualConst of it,
      whichever side the constant is on *)
   let da_eqconst = prove
    (`!i j (s:('c,'ffi)bvlSem_state).
        bvlSem_do_app (closLang_BlockOp
          (closLang_EqualConst (closLang_Int i))) [Number j] s =
        Rval (bvlSem_Boolv (i = j),s)`,
     REPEAT GEN_TAC THEN REWRITE_TAC[da; bv] THEN
     MATCH_REDUCE_TAC THEN REWRITE_TAC[]) in
   let eq_eqconst = prove
    (`!i v (s:('c,'ffi)bvlSem_state).
        bvlSem_do_app (closLang_BlockOp closLang_Equal)
          [v; Number i] s =
        bvlSem_do_app (closLang_BlockOp
          (closLang_EqualConst (closLang_Int i))) [v] s`,
     REPEAT GEN_TAC THEN
     STRUCT_CASES_TAC(ISPEC `v:bvlSem_v` (cases_of `:bvlSem_v`)) THEN
     REWRITE_TAC[da] THEN TRY SAFE_MATCH_REDUCE_TAC THEN
     REWRITE_TAC[de] THEN TRY MATCH_REDUCE_TAC THEN
     REWRITE_TAC(EXISTS_REFL :: eqr) THEN
     REWRITE_TAC[injectivity "semanticPrimitives_result";
                 PAIR_EQ] THEN
     AP_TERM_TAC THEN MATCH_ACCEPT_TAC EQ_SYM_EQ) in
   let eq_eqconst2 = prove
    (`!i v (s:('c,'ffi)bvlSem_state).
        bvlSem_do_app (closLang_BlockOp closLang_Equal)
          [Number i; v] s =
        bvlSem_do_app (closLang_BlockOp
          (closLang_EqualConst (closLang_Int i))) [v] s`,
     REPEAT GEN_TAC THEN
     STRUCT_CASES_TAC(ISPEC `v:bvlSem_v` (cases_of `:bvlSem_v`)) THEN
     REWRITE_TAC[da] THEN TRY SAFE_MATCH_REDUCE_TAC THEN
     REWRITE_TAC[de] THEN TRY MATCH_REDUCE_TAC THEN
     REWRITE_TAC(EXISTS_REFL :: eqr) THEN
     REWRITE_TAC[injectivity "semanticPrimitives_result";
                 PAIR_EQ] THEN
     TRY(AP_TERM_TAC THEN MATCH_ACCEPT_TAC EQ_SYM_EQ)) in
   let eqc_tac =
     TRY(RULE_ASSUM_TRY(REWRITE_RULE[eq_eqconst; eq_eqconst2;
                                     da_eqconst]) THEN
         TRY(REWRITE_TAC[eq_eqconst; eq_eqconst2; da_eqconst])) in
   let step1 = CASE_SPLIT_TAC THEN TRY tidy THEN norm in
   let step2 = sing_tac THEN TRY use_dia THEN VAR_EQ_TAC THEN norm in
   let fold =
     REWRITE_TAC[ev_pair; ev_one; opevi; bool_ev] THEN
     REPEAT(CHANGED_TAC(step1 ORELSE step2)) THEN
     TRY(REWRITE_TAC[bool_ev]) THEN el_tac THEN eqc_tac THEN fin in
   (* the nine foldings that restructure two operations at once:
      the atoms are the proof's own, so that the splits can be
      written down *)
   let fold_lemma_tac =
     REPEAT GEN_TAC THEN
     DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
     REWRITE_TAC[ev_pair; opevi] THEN
     NAMED_CASES_TAC
       `bvlSem_evaluate ([aa],env,(s:('c,'ffi)bvlSem_state))`
       [["ar"; "ast"]] THEN
     NAMED_CASES_TAC (mk_var("ar",rty)) [["av"]; ["ae"]] THEN
     tidy THEN
     TRY(NAMED_CASES_TAC
           `bvlSem_evaluate ([bb],env,(ast:('c,'ffi)bvlSem_state))`
           [["br"; "bst"]] THEN
         NAMED_CASES_TAC (mk_var("br",rty)) [["bv"]; ["be"]] THEN
         tidy) THEN
     REPEAT(CHANGED_TAC
       (((CASE_SPLIT_TAC THEN TRY tidy) ORELSE
         (sing_tac THEN TRY use_dia THEN VAR_EQ_TAC)) THEN norm)) THEN
     fin in
   let cc x = "bvl_Op (closLang_IntOp (closLang_Const (" ^ x ^
              "))) []" in
   let o2 op u v = "bvl_Op (closLang_IntOp closLang_" ^ op ^ ") [" ^
                   u ^ "; " ^ v ^ "]" in
   let aA = o2 "Add" and sS = o2 "Sub" and mM = o2 "Mult" in
   let lem lhs rhs extra = prove
    (parse_term (Printf.sprintf
       "!(aa:bvl_exp) bb pp qq env (s:('c,'ffi)bvlSem_state) res s2.\
        \ bvlSem_evaluate ([%s],env,s) = (res,s2) /\\\
        \ ~(res = Rerr (Rabort Rtype_error))%s\
        \ ==> bvlSem_evaluate ([%s],env,s) = (res,s2)"
       lhs extra rhs),
     fold_lemma_tac) in
   let folds = [
     lem (aA (aA "aa" (cc "pp")) (aA "bb" (cc "qq")))
         (aA (aA "aa" "bb") (cc "qq + pp")) "";
     lem (aA (aA "aa" (cc "pp")) (sS "bb" (cc "qq")))
         (sS (sS "aa" "bb") (cc "qq + pp")) "";
     lem (aA (sS "aa" (cc "pp")) (aA "bb" (cc "qq")))
         (aA (sS "aa" "bb") (cc "qq + pp")) "";
     lem (aA (sS "aa" (cc "pp")) (aA "bb" (cc "qq")))
         (sS "aa" "bb") " /\\ qq + pp = &0";
     lem (sS (aA "aa" (cc "pp")) (aA "bb" (cc "qq")))
         (aA (sS "aa" "bb") (cc "qq - pp")) "";
     lem (sS (aA "aa" (cc "pp")) (sS "bb" (cc "qq")))
         (sS (aA "aa" "bb") (cc "qq - pp")) "";
     lem (sS (sS "aa" (cc "pp")) (aA "bb" (cc "qq")))
         (aA (aA "aa" "bb") (cc "qq - pp")) "";
     lem (sS (sS "aa" (cc "pp")) (aA "bb" (cc "qq")))
         (aA "aa" "bb") " /\\ qq - pp = &0";
     lem (mM (mM "aa" (cc "pp")) (mM "bb" (cc "qq")))
         (mM (cc "qq * pp") (mM "aa" "bb")) ""] in
   let use_lemma l =
     SPLIT_ASM_TAC THEN VAR_EQ_TAC THEN STRIP_TAC THEN
     FIRST_ASSUM(fun h1 -> FIRST_ASSUM(fun h2 ->
       FIRST [(fun gl -> ACCEPT_TAC(MATCH_MP l (CONJ h1 h2)) gl);
              FIRST_ASSUM(fun h3 gl ->
                ACCEPT_TAC(MATCH_MP l (CONJ h1 (CONJ h2 h3)))
                  gl)])) in
   let use_folds = FIRST (map use_lemma folds) in
   (* the eleven operations that SmartOp2 dispatches on, split only
      where the goal still asks: a blind split on all of them is
      2048 goals *)
   let opconds =
     [`op = closLang_IntOp closLang_Add`;
      `op = closLang_IntOp closLang_Sub`;
      `op = closLang_IntOp closLang_Mult`;
      `op = closLang_IntOp closLang_Div`;
      `op = closLang_IntOp closLang_Mod`;
      `op = closLang_IntOp closLang_Less`;
      `op = closLang_IntOp closLang_LessEq`;
      `op = closLang_IntOp closLang_Greater`;
      `op = closLang_IntOp closLang_GreaterEq`;
      `op = closLang_BlockOp closLang_Equal`;
      `op = closLang_MemOp closLang_El`] in
   let split_when t (asl,w as gl) =
     if can (find_term (fun u -> u = t)) w
     then (ASM_CASES_TAC t THEN ASM_REWRITE_TAC (MEM :: con_rws)) gl
     else ALL_TAC gl in
   let dispatch = MAP_EVERY split_when opconds in
   let shapes =
     EVERY_CASE_TAC THEN
     RULE_ASSUM_TRY(REWRITE_RULE[dest_simple_eq; case_op_const_eq;
                                 PAIR_EQ]) THEN
     MATCH_TIDY_TAC THEN VAR_EQ_TAC THEN
     REPEAT COND_CASES_TAC in
   REPEAT GEN_TAC THEN
   DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
   REWRITE_TAC[so2; LET_DEF; LET_END_DEF] THEN
   CONV_TAC(DEPTH_CONV BETA_CONV) THEN dispatch THEN
   shapes THEN ((SOLVED fold) ORELSE use_folds)));;

let SmartOp1_thm = prove
 (`evaluate ([Op op [x]],env,s) = (res,s2) /\ ~(res = Rerr (Rabort
  Rtype_error)) ==>
   evaluate ([SmartOp1 op x],env,s) = (res,s2)`,
  (* SmartOp1 folds an equality with a constant into a boolean *)
  (let ev = bvlSem_evaluate_def in
   let da = bvlSem_do_app_def in
   let dia = bvlSem_do_int_app_def in
   let fc = bvlSem_fix_clock_def in
   let bl = bool_def in
   let bv = bvlSem_Boolv_def in
   let so1 = SmartOp1_def in
   let dei = dest_EqualInt_def in
   let con_rws =
     [distinctness "bvl_exp"; injectivity "bvl_exp";
      distinctness "closLang_op"; injectivity "closLang_op";
      distinctness "closLang_int_op";
      injectivity "closLang_int_op";
      distinctness "block_op"; injectivity "block_op";
      distinctness "const_part"; injectivity "const_part";
      distinctness "option"; injectivity "option"] in
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
   let bool_ev = prove
    (`!b env2 (s:('c,'ffi)bvlSem_state).
        bvlSem_evaluate ([bvl_Bool b],env2,s) =
        (Rval [bvlSem_Boolv b],s)`,
     REPEAT GEN_TAC THEN
     REWRITE_TAC[bl; bv; ev; fc; ARITH_RULE `MIN (a:num) a = a`] THEN
     RECORD_CASES_TAC `s:('c,'ffi)bvlSem_state` THEN
     REWRITE_TAC[da; REVERSE] THEN
     MATCH_REDUCE_TAC THEN REWRITE_TAC[]) in
   let da_eqconst = prove
    (`!i j (s:('c,'ffi)bvlSem_state).
        bvlSem_do_app (closLang_BlockOp
          (closLang_EqualConst (closLang_Int i))) [Number j] s =
        Rval (bvlSem_Boolv (i = j),s)`,
     REPEAT GEN_TAC THEN REWRITE_TAC[da; bv] THEN
     MATCH_REDUCE_TAC THEN REWRITE_TAC[]) in
   (* what dest_EqualInt says about the operation, as
      dest_simple_eq says it about the expression *)
   let dei_eq = prove
    (`!op i. dest_EqualInt op = SOME i <=>
             op = closLang_BlockOp
                    (closLang_EqualConst (closLang_Int i))`,
     REPEAT GEN_TAC THEN REWRITE_TAC[dei] THEN EVERY_CASE_TAC THEN
     REWRITE_TAC con_rws THEN TRY(MATCH_ACCEPT_TAC EQ_SYM_EQ)) in
   REWRITE_TAC[so1] THEN EVERY_CASE_TAC THEN
   TRY(SOLVED(DISCH_THEN(ACCEPT_TAC o CONJUNCT1))) THEN
   RULE_ASSUM_TRY(REWRITE_RULE[dei_eq; dest_simple_eq]) THEN
   VAR_EQ_TAC THEN
   DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
   GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [ev] THEN
   REWRITE_TAC[bvlSem_fix_clock_evaluate; opevi; REVERSE; APPEND;
               da_eqconst] THEN
   MATCH_REDUCE_TAC THEN
   DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[bool_ev] THEN
   REWRITE_TAC[PAIR_EQ; injectivity "semanticPrimitives_result";
               CONS_11] THEN
   AP_TERM_TAC THEN MATCH_ACCEPT_TAC EQ_SYM_EQ));;

let SmartOp_thm = prove
 (`evaluate ([Op op xs],env,s) = (res,s2) /\ ~(res = Rerr (Rabort
  Rtype_error)) ==>
    evaluate ([SmartOp op xs],env,s) = (res,s2)`,
  (* and SmartOp itself is the three of them: two expressions go
     through the flip and then SmartOp2, one through SmartOp1, and
     anything else is left alone *)
  (let so = SmartOp_def in
   REWRITE_TAC[so] THEN EVERY_CASE_TAC THENL
   [DISCH_THEN(ACCEPT_TAC o CONJUNCT1);
    MATCH_ACCEPT_TAC SmartOp1_thm;
    STRIP_TAC THEN
    NAMED_CASES_TAC `SmartOp_flip op a0 a0'` [["fop"; "fr"]] THEN
    NAMED_CASES_TAC `fr:bvl_exp#bvl_exp` [["fx1"; "fx2"]] THEN
    (* the statement of this theorem does not say which state it is
       about, so its types are the ones the port invented for it,
       and what the proof hands the two lemmas has to come out of
       its own assumptions (PORTING-GUIDE.md entry 12) *)
    FIRST_ASSUM(fun fl -> FIRST_ASSUM(fun ev ->
      FIRST_ASSUM(fun nt gl ->
        let th1 = MATCH_MP SmartOp_flip_thm
                    (CONJ (SYM fl) (CONJ ev nt)) in
        ACCEPT_TAC(MATCH_MP SmartOp2_thm (CONJ th1 nt)) gl)));
    DISCH_THEN(ACCEPT_TAC o CONJUNCT1)]));;

(* evaluate_env_rel *)
let bvl_constProof_evaluate_env_rel = prove
 (`!xs env1 (s1:('c,'ffi)bvlSem_state) ax env2 res s2 ys.
      (evaluate (xs,env1,s1) = (res,s2)) /\
      bvl_constProof_env_rel (:'c) (:'ffi) ax env1 env2 /\ ~(res =
        Rerr (Rabort Rtype_error)) ==>
      (evaluate (compile ax xs,env2,s1) = (res,s2))`,
  ((* ---- the pieces ---------------------------------------------- *)
   let cp = bvl_const_compile_def in
   let ev = bvlSem_evaluate_def in
   let er = bvl_constProof_env_rel_def in
   let vr = bvl_constProof_v_rel_def in
   let fc = bvlSem_fix_clock_def in
   let bl = bool_def in
   let bv = bvlSem_Boolv_def in
   let da = bvlSem_do_app_def in
   let fce = bvlSem_fix_clock_evaluate in
   let sz = size_thms "bvl_exp" in
   let hd_sing = bvl_const_compile_HD_SING in
   let len_eq = bvl_constProof_env_rel_length in
   let lkn = CONV_RULE(DEPTH_CONV BETA_CONV)
               bvl_constProof_env_rel_LLOOKUP_NONE in
   let lks = CONV_RULE(DEPTH_CONV BETA_CONV)
               bvl_constProof_env_rel_LOOKUP_SOME in
   let res_rws = [PAIR_EQ;
                  distinctness "semanticPrimitives_result";
                  injectivity "semanticPrimitives_result"] in
   let rty = `:(bvlSem_v list,bvlSem_v)
                semanticPrimitives_result` in
   let s1t = `s1:('c,'ffi)bvlSem_state` in
   let add_lt = ARITH_RULE `!m v e. m < e - v ==> m + v < e` in
   let add_sym_lt = ARITH_RULE `!m v e. m + v < e ==> v + m < e` in
   (* the clauses of the relation, as HOL4 states it: the port has
      it as one match on the tuple of its arguments *)
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
   let env_rel_CONS = prove
    (`!ax env1 env2 v.
        bvl_constProof_env_rel (:'c) (:'ffi) ax env1 env2 ==>
        bvl_constProof_env_rel (:'c) (:'ffi) (CONS NONE ax)
          (CONS v env1) (CONS v env2)`,
     REPEAT GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC erc) in
   let bool_ev = prove
    (`!b env2 (s:('c,'ffi)bvlSem_state).
        bvlSem_evaluate ([bvl_Bool b],env2,s) =
        (Rval [bvlSem_Boolv b],s)`,
     REPEAT GEN_TAC THEN
     REWRITE_TAC[bl; bv; ev; fc; ARITH_RULE `MIN (a:num) a = a`] THEN
     RECORD_CASES_TAC `s:('c,'ffi)bvlSem_state` THEN
     REWRITE_TAC[da; REVERSE] THEN
     MATCH_REDUCE_TAC THEN REWRITE_TAC[]) in
   let boolv_11 = prove
    (`!b c. (bvlSem_Boolv b = bvlSem_Boolv c) <=> (b = c)`,
     REPEAT GEN_TAC THEN
     REWRITE_TAC[bv; injectivity "bvlSem_v";
                 bool_to_tag_def; true_tag_def;
                 false_tag_def] THEN
     BOOL_CASES_TAC `b:bool` THEN BOOL_CASES_TAC `c:bool` THEN
     REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV) in
   (* ---- the shared steps ---------------------------------------- *)
   let size_tac_rws rws =
     RULE_ASSUM_TAC(REWRITE_RULE(rws @ (list_size :: sz))) THEN
     REWRITE_TAC(rws @ (list_size :: sz)) THEN ASM_ARITH_TAC in
   let size_tac = size_tac_rws [] in
   let impossible =
     SUBGOAL_THEN `F` CONTR_TAC THEN
     RULE_ASSUM_TAC(REWRITE_RULE(list_size :: sz)) THEN
     ASM_ARITH_TAC in
   (* HOL4's fs, with the rewrites of this file: the clock that
      fix_clock puts back is the clock that the evaluation left
      (bvlSem's fix_clock_evaluate), and it has to fire before the
      definition of fix_clock or the proof is left with a record
      update -- which is what the stages of FS_TAC are for *)
   let tidy = FS_TAC [[fce]; [fc]] res_rws in
   let tidy2 = tidy THEN ASM_FS_TAC THEN tidy in
   let close_contr =
     TRY(RULE_ASSUM_TRY(REWRITE_RULE[]) THEN
         TRY(FIRST_ASSUM CONTR_TAC)) in
   let ev_term xs' env' s' =
     list_mk_icomb "bvlSem_evaluate"
       [mk_pair(xs', mk_pair(env', s'))] in
   let is_ev t =
     try fst(dest_const(fst(strip_comb t))) = "bvlSem_evaluate"
     with Failure _ -> false in
   let dest_ev t =
     let a,bc = dest_pair (rand t) in
     let b,c = dest_pair bc in a,b,c in
   (* the instance of the induction hypothesis that an evaluation of
      the source asks for: the list is the key, the environment that
      the compiler is given comes with it *)
   let USE_IH ax' env2' xs' (asl,w) =
     let ih = tryfind (fun (_,th) ->
       if is_forall (concl th) then th else fail()) asl in
     let a,b,c,rt = tryfind (fun (_,th) ->
       let l,r = dest_eq(concl th) in
       if not (is_ev l) then fail() else
       let a,b,c = dest_ev l in
       if a = xs' then (a,b,c,r) else fail()) asl in
     MP_TAC(SPECL [a; b; c; ax'; env2'; fst(dest_pair rt);
                   snd(dest_pair rt)] ih) (asl,w) in
   let ih_plain =
     USE_IH `ax:(bvl_exp option) list` `env2:bvlSem_v list` in
   let ih_ants_simple sz_tac =
     ANTS_TAC THENL
     [CONJ_TAC THENL [sz_tac; ASM_REWRITE_TAC res_rws];
      DISCH_THEN(fun th -> TRY(REWRITE_TAC[th]) THEN
        RULE_ASSUM_TRY(REWRITE_RULE[th]) THEN ASSUME_TAC th)] in
   let use_ih_gen keep xs' =
     FIRST_ASSUM(fun eq ->
       let l,rt = dest_eq(concl eq) in
       let a,bc = dest_pair(rand l) in
       let b,c = dest_pair bc in
       if not (a = xs' && b = `env1:bvlSem_v list`) then
         failwith "use_ih_gen" else
       FIRST_ASSUM(fun ih ->
         MP_TAC(SPECL [a; b; c; `ax:(bvl_exp option) list`;
                       `env2:bvlSem_v list`;
                       fst(dest_pair rt); snd(dest_pair rt)] ih)) THEN
       ANTS_TAC THENL
       [CONJ_TAC THENL [size_tac; ASM_REWRITE_TAC res_rws];
        DISCH_THEN(fun th -> TRY(REWRITE_TAC[th]) THEN
                             (if keep then ASSUME_TAC th
                              else ALL_TAC))]) in
   let use_ih_for = use_ih_gen false in
   let use_ih_keep = use_ih_gen true in
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
     REWRITE_TAC[fce; hd_sing] THEN
     RULE_ASSUM_TRY(REWRITE_RULE[fce]) in
   let one_sub xs' = unfold_case THEN do_sub "h" xs' s1t in
   let nil_case =
     REWRITE_TAC[cp; ev] THEN RULE_ASSUM_TAC(REWRITE_RULE[ev]) THEN
     ASM_REWRITE_TAC[] in
   (* ---- what the environment of the compiled code holds --------- *)
   (* the entry of the relation at an index says where the value of
      that variable is in the second environment: at the same index
      when it says nothing, at the index it records when it says a
      Var, and at the same index again when it says an expression
      that evaluates to it *)
   let index_lemma = prove
    (`!ax env1 env2 v.
        bvl_constProof_env_rel (:'c) (:'ffi) ax env1 env2 /\
        v < LENGTH env1 ==>
        v < LENGTH env2 /\
        (oEL v ax = NONE ==> EL v env2 = EL v env1) /\
        (oEL v ax = SOME NONE ==> EL v env2 = EL v env1) /\
        (!i. oEL v ax = SOME (SOME (bvl_Var i)) ==>
             v + i < LENGTH env2 /\ EL (v + i) env2 = EL v env1)`,
     REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
     [FIRST_ASSUM(fun er_th ->
        FIRST_ASSUM(fun lt ->
          ACCEPT_TAC(REWRITE_RULE[SYM(MATCH_MP len_eq er_th)] lt)));
      DISCH_TAC THEN
      FIRST_ASSUM(fun er_th -> FIRST_ASSUM(fun lk ->
        ACCEPT_TAC(MATCH_MP lkn (CONJ er_th (DISJ1 lk
          `oEL v (ax:(bvl_exp option) list) = SOME NONE`)))));
      DISCH_TAC THEN
      FIRST_ASSUM(fun er_th -> FIRST_ASSUM(fun lk ->
        ACCEPT_TAC(MATCH_MP lkn (CONJ er_th (DISJ2
          `oEL v (ax:(bvl_exp option) list) = NONE` lk)))));
      GEN_TAC THEN DISCH_TAC THEN
      FIRST_ASSUM(fun er_th -> FIRST_ASSUM(fun lk ->
        MP_TAC(MATCH_MP lks (CONJ er_th lk)))) THEN
      REWRITE_TAC vrc THEN
      DISCH_THEN(MP_TAC o MATCH_MP oEL_SOME) THEN
      REWRITE_TAC[LENGTH_DROP] THEN STRIP_TAC THEN
      FIRST_ASSUM(fun lt ->
        let bound = MATCH_MP add_lt lt in
        let eld = MATCH_MP EL_DROP bound in
        CONJ_TAC THENL
        [ACCEPT_TAC(MATCH_MP add_sym_lt bound);
         FIRST_ASSUM(fun eq -> ACCEPT_TAC
           (ONCE_REWRITE_RULE[ADD_SYM] (REWRITE_RULE[eld] eq)))])]) in
   let not_refl_tac =
     FIRST_ASSUM(fun th ->
       let bod = snd(strip_forall(concl th)) in
       let l,_ = dest_eq(dest_neg bod) in
       MP_TAC(SPEC l th) THEN REWRITE_TAC[]) in
   (* and an entry that is not a Var is an expression that
      evaluates to the value of that variable, whatever the
      environment and the state -- which is what v_rel says of an
      Op, and nothing else can be an entry at all *)
   let vrel_ev = prove
    (`!ax env1 env2 v e.
        bvl_constProof_env_rel (:'c) (:'ffi) ax env1 env2 /\
        v < LENGTH env1 /\ oEL v ax = SOME (SOME e) /\
        (!i. ~(e = bvl_Var i)) ==>
        EL v env2 = EL v env1 /\
        (!(s:('c,'ffi)bvlSem_state) env.
           bvlSem_evaluate ([e],env,s) = (Rval [EL v env1],s))`,
     REPEAT GEN_TAC THEN STRIP_TAC THEN
     FIRST_ASSUM(fun er_th -> FIRST_ASSUM(fun lk ->
       MP_TAC(MATCH_MP lks (CONJ er_th lk)))) THEN
     FIRST_X_ASSUM(fun th ->
       if is_forall(concl th) then MP_TAC th else failwith "nv") THEN
     STRUCT_CASES_TAC(ISPEC `e:bvl_exp` (cases_of `:bvl_exp`)) THEN
     DISCH_TAC THEN
     GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [vr] THEN
     TRY MATCH_REDUCE_TAC THEN REWRITE_TAC[] THEN
     TRY(DISCH_THEN(fun th -> CONJ_TAC THENL
           [ACCEPT_TAC(SYM(CONJUNCT1 th));
            ACCEPT_TAC(CONJUNCT2 th)])) THEN
     RULE_ASSUM_TRY(REWRITE_RULE[injectivity "bvl_exp"]) THEN
     not_refl_tac) in
   let index_tac =
     TRY(FIRST_ASSUM(fun er_th -> FIRST_ASSUM(fun lt ->
           STRIP_ASSUME_TAC(MATCH_MP index_lemma
             (CONJ er_th lt))))) in
   let use_index =
     TRY(FIRST_ASSUM(fun imp -> FIRST_ASSUM(fun eq ->
           STRIP_ASSUME_TAC(MATCH_MP imp eq)))) in
   let apply_vrel (asl,w as gl) =
     let lk = tryfind (fun (_,th) ->
       let l,r = dest_eq(concl th) in
       if fst(dest_const(fst(strip_comb l))) = "oEL" &&
          can (fun t -> rand(rand t)) r then th else fail()) asl in
     let e = rand(rand(rhs(concl lk))) in
     if is_var e ||
        (try fst(dest_const(fst(strip_comb e))) = "bvl_Var"
         with Failure _ -> true)
     then failwith "apply_vrel" else
     let nv = prove(mk_forall(`i:num`,
                              mk_neg(mk_eq(e,`bvl_Var i`))),
                    REWRITE_TAC[distinctness "bvl_exp"]) in
     (FIRST_ASSUM(fun er_th -> FIRST_ASSUM(fun lt ->
        let th = MATCH_MP vrel_ev
                   (CONJ er_th (CONJ lt (CONJ lk nv))) in
        REWRITE_TAC[CONJUNCT1 th] THEN
        RULE_ASSUM_TRY(REWRITE_RULE[CONJUNCT1 th]) THEN
        ASSUME_TAC(CONJUNCT2 th)))) gl in
   (* ---- Var and Force: the two clauses that read the environment *)
   let index_pre =
     RULE_ASSUM_TAC(ONCE_REWRITE_RULE[ev]) THEN
     RULE_ASSUM_TRY(REWRITE_RULE[fce]) THEN REWRITE_TAC[cp] THEN
     CONV_TAC(DEPTH_CONV BETA_CONV) THEN
     ASM_CASES_TAC `v < LENGTH (env1:bvlSem_v list)` THEN tidy2 THEN
     index_tac THEN EVERY_CASE_TAC THEN use_index in
   let var_case =
     index_pre THEN TRY apply_vrel THEN TRY(ASM_REWRITE_TAC[]) THEN
     TRY(GEN_REWRITE_TAC ONCE_DEPTH_CONV [ev]) THEN
     TRY(ASM_REWRITE_TAC[]) THEN TRY tidy2 THEN
     TRY(ASM_REWRITE_TAC[]) THEN close_contr in
   let force_case =
     index_pre THEN
     TRY(GEN_REWRITE_TAC ONCE_DEPTH_CONV [ev]) THEN
     TRY apply_vrel THEN TRY(ASM_REWRITE_TAC[]) THEN TRY tidy2 THEN
     TRY(ASM_REWRITE_TAC[]) THEN close_contr in
   (* ---- If: the compiler folds a constant condition away -------- *)
   (* and then the compiled code does not evaluate the condition at
      all, which is sound because the hypothesis says the condition
      evaluates to what the constant is *)
   let consop = `CONS:bvl_exp->(bvl_exp)list->(bvl_exp)list` in
   let hd_sing_e1 =
     INST [`ax:(bvl_exp option) list`,`n:(bvl_exp option) list`;
           `e1:bvl_exp`,`x:bvl_exp`] hd_sing in
   let bool_head bb (asl,w as gl) =
     let want = mk_eq(`HD (bvl_const_compile ax [e1])`,
                      list_mk_icomb "bvl_Bool" [bb]) in
     let cond = tryfind (fun (_,th) ->
       if concl th = want then th else fail()) asl in
     let ceq = TRANS (SYM hd_sing_e1)
                 (AP_THM (AP_TERM consop cond) `[]:bvl_exp list`) in
     (RULE_ASSUM_TRY(REWRITE_RULE[ceq; bool_ev]) THEN
      RULE_ASSUM_TRY(REWRITE_RULE res_rws) THEN
      TRY(FIRST_ASSUM CONTR_TAC) THEN tidy2 THEN
      RULE_ASSUM_TRY(REWRITE_RULE[HD; boolv_11]) THEN
      RULE_ASSUM_TRY(REWRITE_RULE[]) THEN
      TRY(FIRST_ASSUM CONTR_TAC) THEN tidy2) gl in
   let if_pre =
     RULE_ASSUM_TAC(ONCE_REWRITE_RULE[ev]) THEN
     RULE_ASSUM_TRY(REWRITE_RULE[fce]) THEN
     REWRITE_TAC[cp; LET_DEF; LET_END_DEF] THEN
     CONV_TAC(DEPTH_CONV BETA_CONV) THEN
     REWRITE_TAC[hd_sing] THEN
     NAMED_CASES_TAC (ev_term `[e1:bvl_exp]` `env1:bvlSem_v list` s1t)
       [["hr"; "hs"]] THEN
     NAMED_CASES_TAC (mk_var("hr",rty)) [["hv"]; ["he"]] THEN
     tidy THEN use_ih_keep `[e1:bvl_exp]` THEN tidy in
   let if_third =
     GEN_REWRITE_TAC ONCE_DEPTH_CONV [ev] THEN
     REWRITE_TAC[fce; hd_sing] THEN ASM_REWRITE_TAC[] THEN tidy2 THEN
     REPEAT(COND_CASES_TAC THEN TRY tidy2) THEN
     TRY(use_ih_for `[e2:bvl_exp]`) THEN
     TRY(use_ih_for `[e3:bvl_exp]`) THEN
     TRY(ASM_REWRITE_TAC res_rws) in
   let if_case =
     if_pre THEN
     COND_CASES_TAC THEN
     TRY(bool_head `T` THEN TRY(use_ih_for `[e2:bvl_exp]`) THEN
         TRY(ASM_REWRITE_TAC res_rws)) THEN
     TRY(COND_CASES_TAC THEN
         TRY(bool_head `F` THEN TRY(use_ih_for `[e3:bvl_exp]`) THEN
             TRY(ASM_REWRITE_TAC res_rws))) THEN
     TRY(CHANGED_TAC if_third) THEN
     TRY(use_ih_for `[e2:bvl_exp]`) THEN
     TRY(use_ih_for `[e3:bvl_exp]`) THEN
     TRY(ASM_REWRITE_TAC res_rws) THEN close_contr in
   (* ---- the deep cases: Handle, Tick, Call ---------------------- *)
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
      TRY tidy2 THEN TRY collapse_hyp THEN
      TRY(PRUNE_TAC res_rws) THEN
      TRY(ASM_REWRITE_TAC res_rws) THEN
      (* the sub-result is no type error because the whole result is
         none, which the assumptions say once the hypothesis of the
         branch has collapsed against the conditions of the branch *)
      TRY(REPEAT(CHANGED_TAC(COND_SPLIT_TAC THEN TRY tidy2)) THEN
          TRY(PRUNE_TAC res_rws) THEN
          TRY(ASM_REWRITE_TAC res_rws))] in
   let use_ih_auto =
     EV_PAIR_TAC "bvlSem_evaluate" "bvl_const_compile"
       (fun (xs',env1',s') rt cargs env2' ->
          FIRST_ASSUM(fun ih ->
            MP_TAC(SPECL [xs'; env1'; s'; List.nth cargs 0; env2';
                          fst(dest_pair rt);
                          snd(dest_pair rt)] ih)) THEN
          ANTS_TAC THENL
          [ih_ants;
           DISCH_THEN(fun t ->
             TRY(REWRITE_TAC[t]) THEN
             RULE_ASSUM_TRY(REWRITE_RULE[t]) THEN
             ASSUME_TAC t)]) in
   (* the conditions of the semantics are if-then-else as well as
      case, and both sides test the same one; the condition goes
      first, because a condition that is still open when the
      hypothesis is used leaves a side condition that the branch
      cannot settle (PORTING-GUIDE.md entry 14) *)
   let deep_case =
     REPEAT(CHANGED_TAC
       (TRY(CHANGED_TAC use_ih_auto) THEN TRY tidy2 THEN
        (COND_SPLIT_TAC ORELSE CASE_SPLIT_TAC ORELSE
         COND_CASES_TAC) THEN TRY tidy2 THEN
        TRY(CHANGED_TAC use_ih_auto) THEN TRY tidy2 THEN
        TRY(ASM_REWRITE_TAC[]))) THEN
     TRY(CHANGED_TAC use_ih_auto) THEN TRY tidy2 THEN
     TRY(ASM_REWRITE_TAC[]) in
   let handle_case =
     unfold_case THEN do_sub "h" `[e1:bvl_exp]` s1t THEN
     deep_case THEN close_contr in
   let tick_case =
     unfold_case THEN
     ASM_CASES_TAC `state_clock (s1:('c,'ffi)bvlSem_state) = 0` THEN
     ASM_FS_TAC THEN ASM_REWRITE_TAC[] THEN
     TRY(use_ih_for `[e:bvl_exp]`) in
   let call_case =
     unfold_case THEN do_sub "a" `es:bvl_exp list` s1t THEN
     deep_case THEN close_contr in
   (* ---- Op: the compiled operation goes through SmartOp --------- *)
   let terr = `Rerr (Rabort Rtype_error) :
                 (bvlSem_v list,bvlSem_v)semanticPrimitives_result` in
   let smartop_tac (asl,w as gl) =
     let l,r = dest_eq w in
     let xs,env',st = dest_ev l in
     let sm = rand(rator xs) in
     let _,args = strip_comb sm in
     let opp = List.nth args 0 and cs = List.nth args 1 in
     let newl = ev_term
       (mk_list([list_mk_icomb "bvl_Op" [opp; cs]],`:bvl_exp`))
       env' st in
     let nt_want = mk_neg(mk_eq(fst(dest_pair r),terr)) in
     (SUBGOAL_THEN (mk_eq(newl,r))
        (fun th -> SUBGOAL_THEN nt_want
           (fun nt -> ACCEPT_TAC(MATCH_MP SmartOp_thm
                                   (CONJ th nt))) THEN
           ASM_REWRITE_TAC res_rws) THEN
      GEN_REWRITE_TAC ONCE_DEPTH_CONV [ev] THEN
      REWRITE_TAC[fce] THEN ASM_REWRITE_TAC[] THEN tidy2) gl in
   let op_case =
     RULE_ASSUM_TAC(ONCE_REWRITE_RULE[ev]) THEN
     RULE_ASSUM_TRY(REWRITE_RULE[fce]) THEN
     REWRITE_TAC[cp] THEN
     NAMED_CASES_TAC
       (ev_term `es:bvl_exp list` `env1:bvlSem_v list` s1t)
       [["ar"; "as"]] THEN
     NAMED_CASES_TAC (mk_var("ar",rty)) [["av"]; ["ae"]] THEN
     tidy THEN use_ih_keep `es:bvl_exp list` THEN tidy THEN
     smartop_tac in
   (* ---- Let: the bindings lose their Vars and the body reads the
      environment through what extract_list recorded -------------- *)
   let is_compile t =
     try fst(dest_const(fst(strip_comb t))) = "bvl_const_compile"
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
         let ne = REWRITE_RULE
                    [injectivity "semanticPrimitives_result"] ne0 in
         REWRITE_TAC[MATCH_MP
           bvl_constProof_evaluate_delete_var_Rerr
             (CONJ th ne)])) in
   let del_rval =
     COMPILE_EV (fun th ->
       FIRST_ASSUM(fun er0 ->
         MP_TAC(MATCH_MP bvl_constProof_evaluate_delete_var_Rval
                  (CONJ th er0)))) THEN
     DISCH_THEN(X_CHOOSE_THEN `b:bvlSem_v list`
                  STRIP_ASSUME_TAC) in
   let ih_es = ih_plain `es:bvl_exp list` THEN
               ih_ants_simple size_tac THEN tidy in
   let ih_body =
     USE_IH `APPEND (bvl_const_extract_list
                       (bvl_const_compile ax es)) ax`
            `APPEND (b:bvlSem_v list) env2` `[e:bvl_exp]` in
   let let_case =
     RULE_ASSUM_TRY(ONCE_REWRITE_RULE[ev]) THEN
     RULE_ASSUM_TRY(REWRITE_RULE[fce]) THEN
     REWRITE_TAC[cp; LET_DEF; LET_END_DEF] THEN
     CONV_TAC(DEPTH_CONV BETA_CONV) THEN
     GEN_REWRITE_TAC ONCE_DEPTH_CONV [ev] THEN
     REWRITE_TAC[fce; hd_sing] THEN
     NAMED_CASES_TAC
       (ev_term `es:bvl_exp list` `env1:bvlSem_v list` s1t)
       [["cr"; "cs"]] THEN
     NAMED_CASES_TAC (mk_var("cr",rty)) [["cv"]; ["cerr"]] THEN
     tidy THENL
     [ih_es THEN del_rval THEN ASM_REWRITE_TAC[] THEN tidy THEN
      ih_body THEN ih_ants_simple size_tac THEN tidy THEN
      TRY(ASM_REWRITE_TAC res_rws);
      ih_es THEN del_rerr THEN TRY(ASM_REWRITE_TAC res_rws) THEN
      TRY tidy] in
   (* ---- a list of two or more: the compiler takes the head apart *)
   let cons_cons_case =
     REWRITE_TAC[cp] THEN
     GEN_REWRITE_TAC ONCE_DEPTH_CONV [GSYM hd_sing] THEN
     REWRITE_TAC[APPEND] THEN
     GEN_REWRITE_TAC ONCE_DEPTH_CONV [evaluate_CONS] THEN
     REWRITE_TAC[hd_sing] THEN
     RULE_ASSUM_TAC(ONCE_REWRITE_RULE[evaluate_CONS]) THEN
     NAMED_CASES_TAC (ev_term `[x1:bvl_exp]` `env1:bvlSem_v list` s1t)
       [["hres"; "hs"]] THEN
     NAMED_CASES_TAC (mk_var("hres",rty)) [["hv"]; ["he"]] THEN
     tidy THEN use_ih_for `[x1:bvl_exp]` THEN tidy THEN
     TRY(NAMED_CASES_TAC
           (ev_term `(x2:bvl_exp) :: xr2` `env1:bvlSem_v list`
              `hs:('c,'ffi)bvlSem_state`)
           [["tres"; "ts"]] THEN
         NAMED_CASES_TAC (mk_var("tres",rty)) [["tv"]; ["te"]] THEN
         tidy THEN use_ih_for `(x2:bvl_exp) :: xr2` THEN tidy) in
   (* ---- the nine cases, in the order of the datatype ------------ *)
   let sub_cases =
     [var_case; if_case; let_case; one_sub `[e:bvl_exp]`;
      handle_case; tick_case; call_case; force_case; op_case] in
   MEASURE_INDUCT_TAC `list_size bvl_exp_size` THEN
   REPEAT GEN_TAC THEN STRIP_TAC THEN
   NAMED_CASES_TAC `xs:bvl_exp list` [[]; ["x1"; "xr"]] THENL
   [nil_case; impossible; nil_case; ALL_TAC] THEN
   NAMED_CASES_TAC `xr:bvl_exp list` [[]; ["x2"; "xr2"]] THENL
   [NAMED_CASES_TAC `x1:bvl_exp`
      [["v"]; ["e1"; "e2"; "e3"]; ["es"; "e"]; ["e"]; ["e1"; "e2"];
       ["e"]; ["tt"; "dd"; "es"]; ["loc"; "v"]; ["op"; "es"]] THENL
    sub_cases;
    TRY cons_cons_case]));;

(* compile_thm *)
let bvl_constProof_compile_thm = prove
 (`!xs env (s1:('c,'ffi)bvlSem_state) res s2 ys. (evaluate (xs,env,s1)
  = (res,s2)) /\ ~(res = Rerr (Rabort Rtype_error)) ==> (evaluate
  (compile [] xs,env,s1) = (res,s2))`,
  (* evaluate_env_rel at ax = [], where env_rel [] env env is
     env = env.  The environment is taken out of the goal: the
     state of the statement has type variables of its own
     (PORTING-GUIDE.md entry 12) *)
  (let er = bvl_constProof_env_rel_def in
   let env_rel_refl = prove
    (`!env. bvl_constProof_env_rel (:'c) (:'ffi) [] env env`,
     GEN_TAC THEN ONCE_REWRITE_TAC[er] THEN
     MATCH_REDUCE_TAC THEN REWRITE_TAC[]) in
   REPEAT GEN_TAC THEN STRIP_TAC THEN
   FIRST_ASSUM(fun ev ->
     let tup = rand(lhs(concl ev)) in
     let env_tm = fst(dest_pair(snd(dest_pair tup))) in
     FIRST_ASSUM(fun ne ->
       ACCEPT_TAC(SPEC_ALL(MATCH_MP bvl_constProof_evaluate_env_rel
         (CONJ ev (CONJ (ISPEC env_tm env_rel_refl) ne))))))));;

(* evaluate_compile_exp *)
let bvl_constProof_evaluate_compile_exp = prove
 (`evaluate ([d],env,s) = (r,t) /\ ~(r = Rerr (Rabort Rtype_error)) ==>
    evaluate ([bvl_const_compile_exp d],env,s) = (r,t)`,
  (* the compiled list of one is a singleton, so compile_exp is its
     head, and compile_thm is the theorem about the whole list *)
  (let ce = bvl_const_compile_exp_def in
   STRIP_TAC THEN REWRITE_TAC[ce] THEN
   GEN_REWRITE_TAC ONCE_DEPTH_CONV [GSYM bvl_const_compile_HD_SING]
   THEN MATCH_REDUCE_TAC THEN
   REWRITE_TAC[bvl_const_compile_HD_SING] THEN
   FIRST_ASSUM(fun ev_th -> FIRST_ASSUM(fun ne ->
     ACCEPT_TAC(SPEC_ALL(MATCH_MP bvl_constProof_compile_thm
       (CONJ ev_th ne)))))));;

(* [simp] *)
let delete_var_code_labels = prove
 (`!x. bvlProps_get_code_labels (bvl_const_delete_var x) =
  bvlProps_get_code_labels x`,
  (let dv = bvl_const_delete_var_def in
   let gcl = bvlProps_get_code_labels_def in
   let agcl = assign_get_code_label_def in
   GEN_TAC THEN
   STRUCT_CASES_TAC(ISPEC `x:bvl_exp` (cases_of `:bvl_exp`)) THEN
   REWRITE_TAC[dv] THEN MATCH_REDUCE_TAC THEN
   REWRITE_TAC[gcl; agcl] THEN MATCH_REDUCE_TAC THEN
   REWRITE_TAC[MAP; set_of_list; UNIONS_0; UNIONS_INSERT;
               UNION_EMPTY; EMPTY_UNION]));;

let dest_simple_SOME_code_labels = prove
 (`!x y. dest_simple x = SOME y ==> bvlProps_get_code_labels x = {}`,
  (let gcl = bvlProps_get_code_labels_def in
   let agcl = assign_get_code_label_def in
   REPEAT GEN_TAC THEN REWRITE_TAC[dest_simple_eq] THEN
   DISCH_THEN SUBST1_TAC THEN
   REWRITE_TAC[gcl; agcl] THEN MATCH_REDUCE_TAC THEN
   REWRITE_TAC[MAP; set_of_list; UNIONS_0; UNIONS_INSERT;
               UNION_EMPTY; EMPTY_UNION]));;

(* [simp] *)
let SmartOp2_code_labels = prove
 (`bvlProps_get_code_labels (SmartOp2 (op,x1,x2)) =
    assign_get_code_label op UNION bvlProps_get_code_labels x1
      UNION bvlProps_get_code_labels x2`,
  (* SmartOp2 is the constant folding, and every expression it
     builds is made of the two it is given and of constants, so the
     labels are the same whichever branch it takes.  HOL4 decides
     the branches with rpt PURE_CASE_TAC and closes the rest with
     simp [EXTENSION] and metis_tac; here the operation is decided
     first (the eleven it looks at), then the matches, and what is
     left is a union of the same sets in another order *)
  (let so2 = SmartOp2_def in
   let bl = bool_def in
   let gcl = bvlProps_get_code_labels_def in
   let agcl = assign_get_code_label_def in
   let lset = [MAP; set_of_list; UNIONS_0; UNIONS_INSERT;
               UNION_EMPTY] in
   let con_rws =
     [distinctness "bvl_exp"; injectivity "bvl_exp";
      distinctness "closLang_op"; injectivity "closLang_op";
      distinctness "closLang_int_op";
      injectivity "closLang_int_op";
      distinctness "block_op"; injectivity "block_op";
      distinctness "const_part"; injectivity "const_part";
      distinctness "option"; injectivity "option"] in
   (* the labels of an operation, only where the operation is
      known: unfolding the definition where it is a variable leaves
      a match that says nothing and that MATCH_CONV expands into
      the choice it stands for *)
   let agcl_rws = map (fun t ->
     prove(t, REWRITE_TAC[agcl] THEN MATCH_REDUCE_TAC THEN
              REWRITE_TAC[]))
    [`assign_get_code_label (closLang_IntOp i) = ({}:num->bool)`;
     `assign_get_code_label (closLang_BlockOp b) = ({}:num->bool)`;
     `assign_get_code_label (closLang_MemOp m) = ({}:num->bool)`;
     `assign_get_code_label (closLang_Label n) = {n}`] in
   let labels_tac =
     TRY(REWRITE_TAC[bl]) THEN TRY(REWRITE_TAC[gcl]) THEN
     TRY(REWRITE_TAC agcl_rws) THEN TRY(REWRITE_TAC lset) in
   (* the operation that SmartOp2 looks at, split only where the
      goal still asks: a blind split on all eleven is 2048 goals *)
   let opconds =
     [`op = closLang_IntOp closLang_Add`;
      `op = closLang_IntOp closLang_Sub`;
      `op = closLang_IntOp closLang_Mult`;
      `op = closLang_IntOp closLang_Div`;
      `op = closLang_IntOp closLang_Mod`;
      `op = closLang_IntOp closLang_Less`;
      `op = closLang_IntOp closLang_LessEq`;
      `op = closLang_IntOp closLang_Greater`;
      `op = closLang_IntOp closLang_GreaterEq`;
      `op = closLang_BlockOp closLang_Equal`;
      `op = closLang_MemOp closLang_El`] in
   let split_when t (asl,w as gl) =
     if can (find_term (fun u -> u = t)) w
     then (ASM_CASES_TAC t THEN ASM_REWRITE_TAC (MEM :: con_rws)) gl
     else ALL_TAC gl in
   let dispatch = MAP_EVERY split_when opconds in
   let prune2 =
     RULE_ASSUM_TRY(REWRITE_RULE con_rws) THEN
     TRY(FIRST_ASSUM CONTR_TAC) THEN SPLIT_ASM_TAC THEN
     VAR_EQ_TAC in
   let closer =
     EVERY_CASE_TAC THEN REPEAT COND_CASES_TAC THEN
     RULE_ASSUM_TRY(REWRITE_RULE[dest_simple_eq; case_op_const_eq;
                                 PAIR_EQ]) THEN
     MATCH_TIDY_TAC THEN VAR_EQ_TAC THEN prune2 THEN labels_tac THEN
     TRY(ASM_REWRITE_TAC[]) THEN TRY(REWRITE_TAC[UNION_ACI]) in
   REWRITE_TAC[so2; LET_DEF; LET_END_DEF] THEN
   CONV_TAC(DEPTH_CONV BETA_CONV) THEN dispatch THEN
   closer THEN closer THEN closer));;

let SmartOp1_code_labels = prove
 (`bvlProps_get_code_labels (SmartOp1 op x) = bvlProps_get_code_labels
  (Op op [x])`,
  (* SmartOp1 folds an equality with a constant, and then both
     sides have no labels at all *)
  (let so1 = SmartOp1_def in
   let dei = dest_EqualInt_def in
   let bl = bool_def in
   let gcl = bvlProps_get_code_labels_def in
   let agcl = assign_get_code_label_def in
   let con_rws =
     [distinctness "bvl_exp"; injectivity "bvl_exp";
      distinctness "closLang_op"; injectivity "closLang_op";
      distinctness "closLang_int_op";
      injectivity "closLang_int_op";
      distinctness "block_op"; injectivity "block_op";
      distinctness "const_part"; injectivity "const_part";
      distinctness "option"; injectivity "option"] in
   let set_rws = [MAP; set_of_list; UNIONS_0; UNIONS_INSERT;
                  UNION_EMPTY; EMPTY_UNION] in
   let dei_eq = prove
    (`!op i. dest_EqualInt op = SOME i <=>
             op = closLang_BlockOp
                    (closLang_EqualConst (closLang_Int i))`,
     REPEAT GEN_TAC THEN REWRITE_TAC[dei] THEN EVERY_CASE_TAC THEN
     REWRITE_TAC con_rws THEN TRY(MATCH_ACCEPT_TAC EQ_SYM_EQ)) in
   REWRITE_TAC[so1] THEN EVERY_CASE_TAC THEN
   FIRST_ASSUM(fun th -> SUBST_ALL_TAC(REWRITE_RULE[dei_eq] th)) THEN
   REWRITE_TAC[bl; gcl; agcl] THEN MATCH_REDUCE_TAC THEN
   REWRITE_TAC set_rws THEN
   FIRST_ASSUM(fun th ->
     REWRITE_TAC[MATCH_MP dest_simple_SOME_code_labels th]) THEN
   REWRITE_TAC set_rws));;

(* [simp] *)
let SmartOp_code_labels = prove
 (`bvlProps_get_code_labels (SmartOp op xs) =
   assign_get_code_label op UNION BIGUNION (set_of_list (MAP
     bvlProps_get_code_labels xs))`,
  (let so = SmartOp_def in
   let sof = SmartOp_flip_def in
   let bl = bool_def in
   let gcl = bvlProps_get_code_labels_def in
   let agcl = assign_get_code_label_def in
   let lset = [MAP; set_of_list; UNIONS_0; UNIONS_INSERT;
               UNION_EMPTY] in
   let con_rws =
     [distinctness "bvl_exp"; injectivity "bvl_exp";
      distinctness "closLang_op"; injectivity "closLang_op";
      distinctness "closLang_int_op";
      injectivity "closLang_int_op";
      distinctness "block_op"; injectivity "block_op";
      distinctness "const_part"; injectivity "const_part";
      distinctness "option"; injectivity "option"] in
   let agcl_rws = map (fun t ->
     prove(t, REWRITE_TAC[agcl] THEN MATCH_REDUCE_TAC THEN
              REWRITE_TAC[]))
    [`assign_get_code_label (closLang_IntOp i) = ({}:num->bool)`;
     `assign_get_code_label (closLang_BlockOp b) = ({}:num->bool)`;
     `assign_get_code_label (closLang_MemOp m) = ({}:num->bool)`;
     `assign_get_code_label (closLang_Label n) = {n}`] in
   let labels_tac =
     TRY(REWRITE_TAC[bl]) THEN TRY(REWRITE_TAC[gcl]) THEN
     TRY(REWRITE_TAC agcl_rws) THEN TRY(REWRITE_TAC lset) in
   let prune2 =
     RULE_ASSUM_TRY(REWRITE_RULE con_rws) THEN
     TRY(FIRST_ASSUM CONTR_TAC) THEN SPLIT_ASM_TAC THEN
     VAR_EQ_TAC in
   (* SmartOp_flip turns a constant on the left into one on the
      right, which costs no labels because a constant has none *)
   let flip_tac =
     TRY(REWRITE_TAC[SmartOp1_code_labels]) THEN
     TRY(REWRITE_TAC[sof]) THEN TRY(REWRITE_TAC[MEM]) THEN
     EVERY_CASE_TAC THEN REPEAT COND_CASES_TAC THEN
     TRY(REWRITE_TAC[SmartOp2_code_labels]) THEN
     RULE_ASSUM_TRY(REWRITE_RULE[dest_simple_eq]) THEN
     VAR_EQ_TAC THEN prune2 THEN labels_tac THEN
     TRY(ASM_REWRITE_TAC[]) THEN TRY(REWRITE_TAC[UNION_ACI]) in
   REWRITE_TAC[so] THEN EVERY_CASE_TAC THEN
   flip_tac THEN flip_tac THEN flip_tac));;

let MEM_extract_list_code_labels = prove
 (`!xs x. MEM (SOME x) (bvl_const_extract_list xs) ==>
  bvlProps_get_code_labels x = {}`,
  (let ex = bvl_const_extract_def in
   let exl = bvl_const_extract_list_def in
   let gcl = bvlProps_get_code_labels_def in
   let agcl = assign_get_code_label_def in
   let con_rws =
     [distinctness "bvl_exp"; injectivity "bvl_exp";
      distinctness "option"; injectivity "option"] in
   let set_rws = [MAP; set_of_list; UNIONS_0; UNIONS_INSERT;
                  UNION_EMPTY; EMPTY_UNION] in
   (* whatever extract reads out of an expression is a constant,
      and a constant has no labels *)
   let extract_cl = prove
    (`!(h:bvl_exp) ys x. bvl_const_extract h ys = SOME x
        ==> bvlProps_get_code_labels x = {}`,
     REPEAT GEN_TAC THEN REWRITE_TAC[ex] THEN EVERY_CASE_TAC THEN
     TRY COND_CASES_TAC THEN REWRITE_TAC con_rws THEN
     DISCH_THEN(SUBST1_TAC o SYM) THEN
     REWRITE_TAC[gcl; agcl] THEN TRY MATCH_REDUCE_TAC THEN
     REWRITE_TAC set_rws) in
   LIST_INDUCT_TAC THEN REWRITE_TAC[exl; MEM] THEN GEN_TAC THEN
   DISCH_THEN(DISJ_CASES_THEN2
     (fun eq -> ACCEPT_TAC(MATCH_MP extract_cl (SYM eq)))
     (fun m -> FIRST_ASSUM(fun ih -> ACCEPT_TAC(MATCH_MP ih m))))));;

(* compile_code_labels *)
let bvl_constProof_compile_code_labels = prove
 (`!x y. BIGUNION (set_of_list (MAP bvlProps_get_code_labels
  (bvl_const_compile x y))) SUBSET
         BIGUNION (set_of_list (MAP bvlProps_get_code_labels y))
           UNION
         BIGUNION (set_of_list (MAP (bvlProps_get_code_labels o
           THE) (FILTER IS_SOME x)))`,
  (* HOL4 takes the induction theorem that its termination proof
     left behind (recInduct compile_ind); the port induces on the
     measure the definition was made with.  What the proof says is
     that compile adds no label of its own: every label of the
     result is one of the expressions it compiled or one of the
     expressions the environment holds *)
  (let cp = bvl_const_compile_def in
   let ex = bvl_const_extract_def in
   let exl = bvl_const_extract_list_def in
   let gcl = bvlProps_get_code_labels_def in
   let agcl = assign_get_code_label_def in
   let sz = size_thms "bvl_exp" in
   let lset = [MAP; set_of_list; UNIONS_0; UNIONS_INSERT;
               UNION_EMPTY] in
   let con_rws =
     [distinctness "bvl_exp"; injectivity "bvl_exp";
      distinctness "option"; injectivity "option"] in
   let xx = `x:(bvl_exp option) list` in
   (* the labels of a list of expressions, which is the shape that
      the statement is in: of an APPEND, and of the one-expression
      list that every clause but two compiles *)
   let labs_app = prove
    (`!a b. BIGUNION (set_of_list
               (MAP bvlProps_get_code_labels (APPEND a b))) =
            BIGUNION (set_of_list
               (MAP bvlProps_get_code_labels a)) UNION
            BIGUNION (set_of_list
               (MAP bvlProps_get_code_labels b))`,
     LIST_INDUCT_TAC THEN
     REWRITE_TAC[APPEND; MAP; set_of_list; UNIONS_0; UNIONS_INSERT;
                 UNION_EMPTY] THEN
     ASM_REWRITE_TAC[UNION_ASSOC]) in
   let labs_sing = prove
    (`!x e. BIGUNION (set_of_list
              (MAP bvlProps_get_code_labels
                 (bvl_const_compile x [e]))) =
            bvlProps_get_code_labels
              (HD (bvl_const_compile x [e]))`,
     REPEAT GEN_TAC THEN
     GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
       [GSYM bvl_const_compile_HD_SING] THEN
     REWRITE_TAC[MAP; set_of_list; UNIONS_INSERT; UNIONS_0;
                 UNION_EMPTY]) in
   let labs_delete = prove
    (`!l. BIGUNION (set_of_list (MAP bvlProps_get_code_labels
            (MAP bvl_const_delete_var l))) =
          BIGUNION (set_of_list (MAP bvlProps_get_code_labels l))`,
     LIST_INDUCT_TAC THEN
     ASM_REWRITE_TAC(delete_var_code_labels :: lset)) in
   (* an expression the environment holds has its labels in the
      set that the statement allows ... *)
   let envlabs_oEL = prove
    (`!x v e. oEL v x = SOME (SOME e) ==>
        bvlProps_get_code_labels e SUBSET
        BIGUNION (set_of_list
          (MAP (bvlProps_get_code_labels o THE) (FILTER IS_SOME x)))`,
     LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
     REWRITE_TAC[oEL; distinctness "option"] THEN
     STRUCT_CASES_TAC(SPEC `v:num` num_CASES) THEN
     REWRITE_TAC[oEL; ARITH_EQ; NOT_SUC; SUC_SUB1;
                 injectivity "option"] THENL
     [DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[FILTER; IS_SOME; MAP; set_of_list; UNIONS_INSERT;
                  o_THM; THE] THEN
      REWRITE_TAC[SUBSET_UNION];
      DISCH_TAC THEN
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `BIGUNION (set_of_list
        (MAP (bvlProps_get_code_labels o THE)
           (FILTER IS_SOME t)))` THEN
      CONJ_TAC THENL
      [FIRST_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `n:num` THEN
       ASM_REWRITE_TAC[];
       NAMED_CASES_TAC `h:bvl_exp option` [[]; ["a"]] THEN
       REWRITE_TAC[FILTER; IS_SOME; MAP; set_of_list; UNIONS_INSERT;
                   SUBSET_REFL; SUBSET_UNION]]]) in
   (* ... and what the Let clause adds to the environment holds
      constants only, so it allows nothing new *)
   let envlabs_extract = prove
    (`!ys x. BIGUNION (set_of_list
               (MAP (bvlProps_get_code_labels o THE)
                  (FILTER IS_SOME
                     (APPEND (bvl_const_extract_list ys) x)))) =
             BIGUNION (set_of_list
               (MAP (bvlProps_get_code_labels o THE)
                  (FILTER IS_SOME x)))`,
     let extract_cl = prove
      (`!(h:bvl_exp) ys x. bvl_const_extract h ys = SOME x
          ==> bvlProps_get_code_labels x = {}`,
       REPEAT GEN_TAC THEN REWRITE_TAC[ex] THEN EVERY_CASE_TAC THEN
       TRY COND_CASES_TAC THEN REWRITE_TAC con_rws THEN
       DISCH_THEN(SUBST1_TAC o SYM) THEN
       REWRITE_TAC[gcl; agcl] THEN TRY MATCH_REDUCE_TAC THEN
       REWRITE_TAC(EMPTY_UNION :: lset)) in
     LIST_INDUCT_TAC THEN
     REWRITE_TAC[exl; APPEND] THEN GEN_TAC THEN
     NAMED_CASES_TAC `bvl_const_extract (h:bvl_exp) (t:bvl_exp list)`
       [[]; ["ee"]] THEN
     ASM_REWRITE_TAC[FILTER; IS_SOME; MAP; set_of_list;
                     UNIONS_INSERT; o_THM; THE] THEN
     FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP extract_cl th]) THEN
     ASM_REWRITE_TAC[UNION_EMPTY]) in
   (* the subset goals of the proof are unions of the same sets in
      another order, which is decided by taking the left side
      apart and finding each piece on the right *)
   let sub_mono = prove
    (`!(a:num->bool) b c. a SUBSET b UNION c
        ==> !d. b SUBSET d ==> a SUBSET d UNION c`,
     SET_TAC[]) in
   let sub_un = prove
    (`!(a:num->bool) b c. a SUBSET c /\ b SUBSET c
        ==> a UNION b SUBSET c`,
     SET_TAC[]) in
   let rec sub_prove a b =
     if a = b then ISPEC a SUBSET_REFL else
     let b1,b2 = dest_binary "UNION" b in
     (try MATCH_MP SUBSET_TRANS
            (CONJ (sub_prove a b1)
                  (ISPECL [b1; b2] (CONJUNCT1 SUBSET_UNION)))
      with Failure _ ->
           MATCH_MP SUBSET_TRANS
             (CONJ (sub_prove a b2)
                   (ISPECL [b2; b1] (CONJUNCT2 SUBSET_UNION)))) in
   let sub_leaf (asl,w as gl) =
     let a,b = dest_binary "SUBSET" w in
     ACCEPT_TAC (sub_prove a b) gl in
   let sub_tac =
     REPEAT STRIP_TAC THEN
     REPEAT(MATCH_MP_TAC sub_un THEN CONJ_TAC) THEN
     FIRST [sub_leaf;
            FIRST_ASSUM(fun ih ->
              MATCH_MP_TAC(MATCH_MP sub_mono ih)) THEN sub_leaf] in
   let cond t =
     mk_binop `(<=):num->num->bool`
       (list_mk_icomb "list_size" [`bvl_exp_size`; t]) `k:num` in
   let size_tac =
     RULE_ASSUM_TAC(REWRITE_RULE(list_size :: sz)) THEN
     REWRITE_TAC(list_size :: sz) THEN ASM_ARITH_TAC in
   let use_ih env t =
     SUBGOAL_THEN (cond t)
       (fun c -> FIRST_ASSUM(fun ih ->
          MP_TAC(SPEC env (MATCH_MP ih c)))) THEN TRY size_tac in
   let rec_case subs =
     REWRITE_TAC[cp; LET_DEF; LET_END_DEF] THEN
     CONV_TAC(DEPTH_CONV BETA_CONV) THEN
     REPEAT COND_CASES_TAC THEN
     REWRITE_TAC (gcl :: lset) THEN REWRITE_TAC[GSYM labs_sing] THEN
     MAP_EVERY (use_ih xx) subs THEN REWRITE_TAC lset THEN
     sub_tac in
   (* the Var that the environment gives a value for is the one
      clause whose result is not built out of what it compiled *)
   let var_case =
     REWRITE_TAC[cp] THEN EVERY_CASE_TAC THEN REWRITE_TAC lset THEN
     TRY(FIRST_ASSUM(fun th -> MP_TAC(MATCH_MP envlabs_oEL th))) THEN
     REWRITE_TAC[gcl] THEN REWRITE_TAC lset THEN
     TRY(REWRITE_TAC[EMPTY_SUBSET]) THEN
     TRY(DISCH_THEN ACCEPT_TAC) in
   let let_case =
     REWRITE_TAC[cp; LET_DEF; LET_END_DEF] THEN
     CONV_TAC(DEPTH_CONV BETA_CONV) THEN
     REWRITE_TAC (labs_delete :: gcl :: lset) THEN
     REWRITE_TAC[GSYM labs_sing] THEN
     use_ih xx `es:bvl_exp list` THEN
     use_ih `APPEND (bvl_const_extract_list
                       (bvl_const_compile x es)) x`
       `[e:bvl_exp]` THEN
     REWRITE_TAC[envlabs_extract] THEN REWRITE_TAC lset THEN
     sub_tac in
   let handle_case =
     REWRITE_TAC[cp] THEN REWRITE_TAC (gcl :: lset) THEN
     REWRITE_TAC[GSYM labs_sing] THEN
     use_ih xx `[e1:bvl_exp]` THEN
     use_ih `CONS NONE (x:(bvl_exp option) list)` `[e2:bvl_exp]` THEN
     REWRITE_TAC[FILTER; IS_SOME] THEN REWRITE_TAC lset THEN
     sub_tac in
   let force_case =
     REWRITE_TAC[cp] THEN EVERY_CASE_TAC THEN
     REWRITE_TAC (gcl :: lset) THEN sub_tac in
   let op_case =
     REWRITE_TAC[cp] THEN
     REWRITE_TAC (SmartOp_code_labels :: gcl :: lset) THEN
     use_ih xx `es:bvl_exp list` THEN REWRITE_TAC lset THEN
     sub_tac in
   let single_case =
     NAMED_CASES_TAC `y1:bvl_exp`
       [["v"]; ["e1"; "e2"; "e3"]; ["es"; "e"]; ["e"]; ["e1"; "e2"];
        ["e"]; ["tt"; "dd"; "es"]; ["loc"; "v"]; ["op"; "es"]] THENL
     [var_case;
      rec_case [`[e1:bvl_exp]`; `[e2:bvl_exp]`; `[e3:bvl_exp]`];
      let_case;
      rec_case [`[e:bvl_exp]`];
      handle_case;
      rec_case [`[e:bvl_exp]`];
      rec_case [`es:bvl_exp list`];
      force_case;
      op_case] in
   let cons_cons_case =
     REWRITE_TAC[cp] THEN REWRITE_TAC[labs_app] THEN
     REWRITE_TAC lset THEN
     use_ih xx `[y1:bvl_exp]` THEN
     use_ih xx `(y2:bvl_exp) :: yr2` THEN
     REWRITE_TAC lset THEN sub_tac in
   let base_case =
     REPEAT GEN_TAC THEN DISCH_TAC THEN
     NAMED_CASES_TAC `y:bvl_exp list` [[]; ["y1"; "yr"]] THENL
     [REWRITE_TAC(cp :: lset) THEN REWRITE_TAC[EMPTY_SUBSET];
      FIRST_ASSUM MP_TAC THEN
      REWRITE_TAC[list_size; ARITH_RULE `~(1 + a + b <= 0)`]] in
   let step_case =
     REPEAT GEN_TAC THEN DISCH_TAC THEN
     NAMED_CASES_TAC `y:bvl_exp list` [[]; ["y1"; "yr"]] THENL
     [REWRITE_TAC(cp :: lset) THEN REWRITE_TAC[EMPTY_SUBSET];
      NAMED_CASES_TAC `yr:bvl_exp list` [[]; ["y2"; "yr2"]] THENL
      [single_case; cons_cons_case]] in
   MEASURE_INDUCT_TAC `list_size bvl_exp_size` THENL
   [base_case; step_case]));;

(* compile_exp_code_labels *)
(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let bvl_constProof_compile_exp_code_labels = prove
 (cake_as_vars (fun () ->
    `!e. bvlProps_get_code_labels (bvl_const_compile_exp e) SUBSET
  bvlProps_get_code_labels e`),
  (* the compiled list of one is a singleton, so compile_exp is the
     head of it, and the empty environment allows nothing *)
  (let ce = bvl_const_compile_exp_def in
   let labs_sing = prove
    (`!x e. BIGUNION (set_of_list
              (MAP bvlProps_get_code_labels
                 (bvl_const_compile x [e]))) =
            bvlProps_get_code_labels
              (HD (bvl_const_compile x [e]))`,
     REPEAT GEN_TAC THEN
     GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
       [GSYM bvl_const_compile_HD_SING] THEN
     REWRITE_TAC[MAP; set_of_list; UNIONS_INSERT; UNIONS_0;
                 UNION_EMPTY]) in
   GEN_TAC THEN REWRITE_TAC[ce] THEN
   GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
     [GSYM bvl_const_compile_HD_SING] THEN
   MATCH_REDUCE_TAC THEN REWRITE_TAC[GSYM labs_sing] THEN
   MP_TAC(SPECL [`[]:(bvl_exp option) list`; `[e:bvl_exp]`]
            bvl_constProof_compile_code_labels) THEN
   REWRITE_TAC[FILTER; MAP; set_of_list; UNIONS_0; UNIONS_INSERT;
               UNION_EMPTY]));;
