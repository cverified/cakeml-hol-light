(* ================================================================== *)
(*  HOL4's TOKENS and FIELDS of stringScript.sml, which the port      *)
(*  needs for mlstring's tokens and fields and for misc's             *)
(*  splitlines.  Their termination needs that SPLITP takes its        *)
(*  argument apart, so the lemmas about SPLITP come first.            *)
(* ================================================================== *)

let SPLITP_APPEND = prove
 (`!P (l:A list). APPEND (FST(SPLITP P l)) (SND(SPLITP P l)) = l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[SPLITP; APPEND] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[APPEND]);;

let SPLITP_LENGTH = prove
 (`!P (l:A list).
     LENGTH (FST(SPLITP P l)) + LENGTH (SND(SPLITP P l)) = LENGTH l`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`P:A->bool`; `l:A list`] SPLITP_APPEND) THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV)
                         [SYM th]) THEN
  REWRITE_TAC[LENGTH_APPEND]);;

let SPLITP_NIL_FST = prove
 (`!P (l:A list). NULL (FST(SPLITP P l)) ==> SND(SPLITP P l) = l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[SPLITP; NULL] THEN
  COND_CASES_TAC THEN REWRITE_TAC[NULL]);;

(* the two facts that the termination proofs use, in the form in
   which a termination goal has them *)

let SPLITP_LT = prove
 (`!P h (t:A list). ~(NULL (FST(SPLITP P (CONS h t))))
       ==> LENGTH (SND(SPLITP P (CONS h t))) < LENGTH (CONS h t)`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`P:A->bool`; `CONS (h:A) t`] SPLITP_LENGTH) THEN
  SPEC_TAC(`FST(SPLITP (P:A->bool) (CONS h t))`,`m:A list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[NULL; LENGTH] THEN ARITH_TAC);;

let SPLITP_TL_LT = prove
 (`!P h (t:A list). NULL (FST(SPLITP P (CONS h t)))
       ==> LENGTH (TL(SND(SPLITP P (CONS h t)))) < LENGTH (CONS h t)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP SPLITP_NIL_FST) THEN
  REWRITE_TAC[TL; LENGTH] THEN ARITH_TAC);;

(* and that a nonempty list is longer than its tail *)

let LENGTH_TL_LT = prove
 (`!l:A list. ~(NULL l) ==> LENGTH (TL l) < LENGTH l`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[NULL; TL; LENGTH] THEN ARITH_TAC);;

cake_term_facts :=
  SPLITP_LT :: SPLITP_TL_LT :: LENGTH_TL_LT :: (!cake_term_facts);;

(* HOL Light's machinery for a recursion does not look inside a
   let, so the definitions inline the FST and the SND of the SPLITP,
   and the form that HOL4 states is derived from that *)

let TOKENS_aux,TOKENS_ind = define_wf
  `MEASURE (LENGTH o SND)`
  [`(TOKENS P ([]:(A)list) = []) /\
   (TOKENS P (h :: t) =
      if NULL (FST (SPLITP P (h :: t)))
      then TOKENS P (TL (SND (SPLITP P (h :: t))))
      else FST (SPLITP P (h :: t)) ::
           TOKENS P (SND (SPLITP P (h :: t))))`];;

let TOKENS_def = prove
 (`(TOKENS P ([]:(A)list) = []) /\
   (TOKENS P (h :: t) =
      let l,r = SPLITP P (h :: t) in
        if NULL l then
          TOKENS P (TL r)
        else
          l :: TOKENS P r)`,
  CONJ_TAC THENL [REWRITE_TAC[TOKENS_aux]; ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [TOKENS_aux] THEN
  SPEC_TAC(`SPLITP (P:A->bool) (CONS h t)`,`pr:(A)list#(A)list`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[FST; SND]);;

let FIELDS_aux,FIELDS_ind = define_wf
  `MEASURE (LENGTH o SND)`
  [`(FIELDS P ([]:(A)list) = [[]]) /\
   (FIELDS P (h :: t) =
      if NULL (FST (SPLITP P (h :: t)))
      then [] :: FIELDS P (TL (SND (SPLITP P (h :: t))))
      else if NULL (SND (SPLITP P (h :: t)))
           then [FST (SPLITP P (h :: t))]
           else FST (SPLITP P (h :: t)) ::
                FIELDS P (TL (SND (SPLITP P (h :: t)))))`];;

let FIELDS_def = prove
 (`(FIELDS P ([]:(A)list) = [[]]) /\
   (FIELDS P (h :: t) =
      let l,r = SPLITP P (h :: t) in
        if NULL l then
          [] :: FIELDS P (TL r)
        else
          if NULL r then [l] else l :: FIELDS P (TL r))`,
  CONJ_TAC THENL [REWRITE_TAC[FIELDS_aux]; ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [FIELDS_aux] THEN
  SPEC_TAC(`SPLITP (P:A->bool) (CONS h t)`,`pr:(A)list#(A)list`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[FST; SND]);;
