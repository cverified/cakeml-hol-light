(* ================================================================== *)
(*  The theorems of sptreeTheory that a proof of phase three asks     *)
(*  for.  A key is read as a path by its lowest bit (EVEN k) and      *)
(*  (k - 1) DIV 2, so the arithmetic of that encoding comes first:    *)
(*  a key that is not 0 is 2 * ((k - 1) DIV 2) + 2 when it is even    *)
(*  and + 1 when it is odd, which makes the step of a path            *)
(*  injective.                                                        *)
(* ================================================================== *)

let SPT_BIT_DECOMP = prove
 (`!k. ~(k = 0)
       ==> 2 * ((k - 1) DIV 2) + (if EVEN k then 2 else 1) = k`,
  GEN_TAC THEN ASM_CASES_TAC `EVEN k` THEN ASM_REWRITE_TAC[] THENL
   [FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[EVEN_EXISTS]) THEN
    DISCH_THEN(X_CHOOSE_THEN `m:num` SUBST_ALL_TAC) THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `2 * m - 1 = 2 * (m - 1) + 1` SUBST1_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ARITH_RULE `(2 * m + 1) DIV 2 = m`] THEN
    ASM_ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o
                  REWRITE_RULE[NOT_EVEN; ODD_EXISTS]) THEN
    DISCH_THEN(X_CHOOSE_THEN `m:num` SUBST_ALL_TAC) THEN
    DISCH_TAC THEN
    REWRITE_TAC[ARITH_RULE `SUC (2 * m) - 1 = 2 * m`;
                ARITH_RULE `(2 * m) DIV 2 = m`] THEN
    ARITH_TAC]);;

let SPT_BIT_EQ = prove
 (`!k1 k2. ~(k1 = 0) /\ ~(k2 = 0) /\
           (k1 - 1) DIV 2 = (k2 - 1) DIV 2 /\ (EVEN k1 <=> EVEN k2)
           ==> k1 = k2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `k1:num` SPT_BIT_DECOMP) THEN
  MP_TAC(SPEC `k2:num` SPT_BIT_DECOMP) THEN
  ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_ARITH_TAC);;

let SPT_BIT_EQ_EQ = prove
 (`!k1 k2. ~(k1 = 0) /\ ~(k2 = 0)
           ==> ((k1 = k2) <=>
                (EVEN k1 <=> EVEN k2) /\
                (k1 - 1) DIV 2 = (k2 - 1) DIV 2)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[];
    STRIP_TAC THEN MATCH_MP_TAC SPT_BIT_EQ THEN ASM_REWRITE_TAC[]]);;

let SPT_DIV2_LT = prove
 (`!k. ~(k = 0) ==> (k - 1) DIV 2 < k`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`k - 1`; `2`] DIV_LE) THEN ASM_ARITH_TAC);;

let SPT_BIT_EVEN = prove
 (`!n m. (n = 2 * m + 2) <=>
         ~(n = 0) /\ EVEN n /\ (n - 1) DIV 2 = m`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[ARITH_RULE `~(2 * m + 2 = 0)`;
                ARITH_RULE `(2 * m + 2) - 1 = 2 * m + 1`;
                ARITH_RULE `(2 * m + 1) DIV 2 = m`] THEN
    REWRITE_TAC[EVEN_EXISTS] THEN EXISTS_TAC `m + 1` THEN ARITH_TAC;
    STRIP_TAC THEN MP_TAC(SPEC `n:num` SPT_BIT_DECOMP) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC]);;

let SPT_BIT_ODD = prove
 (`!n m. (n = 2 * m + 1) <=>
         ~(n = 0) /\ ~EVEN n /\ (n - 1) DIV 2 = m`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[ARITH_RULE `~(2 * m + 1 = 0)`;
                ARITH_RULE `(2 * m + 1) - 1 = 2 * m`;
                ARITH_RULE `(2 * m) DIV 2 = m`] THEN
    REWRITE_TAC[NOT_EVEN; ODD_EXISTS] THEN EXISTS_TAC `m:num` THEN
    ARITH_TAC;
    STRIP_TAC THEN MP_TAC(SPEC `n:num` SPT_BIT_DECOMP) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC]);;

(* the lookup of an insert, by induction on the key: the insert goes
   down the path of k2 and the lookup down the path of k1, and the
   two paths meet exactly where the keys are equal *)

let lookup_insert = prove
 (`!k2 k1 v (t:(A)spt).
     sptree_lookup k1 (sptree_insert k2 v t) =
     (if k1 = k2 then SOME v else sptree_lookup k1 t)`,
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `k2:num` THEN DISCH_TAC THEN
  ASM_CASES_TAC `k2 = 0` THENL
   [ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN
    STRUCT_CASES_TAC(ISPEC `t:(A)spt` (cases_of `:(A)spt`)) THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV)
      [insert_def] THEN
    REWRITE_TAC[] THEN
    GEN_REWRITE_TAC LAND_CONV [lookup_def] THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV)
      [lookup_def] THEN
    COND_CASES_TAC THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `!k1 v (t:(A)spt).
       sptree_lookup k1 (sptree_insert ((k2 - 1) DIV 2) v t) =
       (if k1 = (k2 - 1) DIV 2 then SOME v else sptree_lookup k1 t)`
    ASSUME_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[SPT_DIV2_LT];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `(k1 = k2) <=>
                ~(k1 = 0) /\ (EVEN k1 <=> EVEN k2) /\
                (k1 - 1) DIV 2 = (k2 - 1) DIV 2`
    SUBST1_TAC THENL
   [EQ_TAC THENL
     [DISCH_TAC THEN ASM_REWRITE_TAC[];
      STRIP_TAC THEN MATCH_MP_TAC SPT_BIT_EQ THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  STRUCT_CASES_TAC(ISPEC `t:(A)spt` (cases_of `:(A)spt`)) THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV)
    [insert_def] THEN
  ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [lookup_def] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV)
    [lookup_def] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN
  ASM_REWRITE_TAC[CONJUNCT1(lookup_def)]);;

(* and the domain as the keys that the lookup gives a value *)

let domain_lookup = prove
 (`!(t:(A)spt) n. n IN domain t <=> ?v. sptree_lookup n t = SOME v`,
  MATCH_MP_TAC spt_INDUCT THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[domain_def; lookup_def;
                NOT_IN_EMPTY; distinctness "option"];
    REPEAT GEN_TAC THEN
    REWRITE_TAC[domain_def; lookup_def;
                IN_SING] THEN
    COND_CASES_TAC THEN
    ASM_REWRITE_TAC[distinctness "option"; injectivity "option"] THEN
    MESON_TAC[];
    REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN
    REWRITE_TAC[domain_def; IN_UNION; IN_IMAGE] THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)
      [lookup_def] THEN
    ASM_CASES_TAC `n = 0` THEN
    ASM_REWRITE_TAC[distinctness "option";
                    ARITH_RULE `~(0 = 2 * m + 2)`;
                    ARITH_RULE `~(0 = 2 * m + 1)`] THEN
    TRY COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[SPT_BIT_EVEN; SPT_BIT_ODD];
    REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN
    REWRITE_TAC[domain_def; IN_UNION; IN_IMAGE; IN_SING] THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)
      [lookup_def] THEN
    ASM_CASES_TAC `n = 0` THEN
    ASM_REWRITE_TAC[distinctness "option"; injectivity "option";
                    ARITH_RULE `~(0 = 2 * m + 2)`;
                    ARITH_RULE `~(0 = 2 * m + 1)`] THEN
    TRY COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[SPT_BIT_EVEN; SPT_BIT_ODD]]);;

(* and HOL4's lookup_NONE_domain *)

let lookup_NONE_domain = prove
 (`!n (t:(A)spt). (sptree_lookup n t = NONE) <=> ~(n IN domain t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[domain_lookup] THEN
  STRUCT_CASES_TAC(ISPEC `sptree_lookup n (t:(A)spt)`
                         (cases_of `:(A)option`)) THEN
  REWRITE_TAC[distinctness "option"; injectivity "option"] THEN
  MESON_TAC[]);;

(* the lookup in the smart constructors, which delete uses: they
   give the LN or the LS where the children are empty, and the
   lookup is the same as in the plain constructor *)

let lookup_mk_BN = prove
 (`!k t1 (t2:(A)spt).
     sptree_lookup k (mk_BN t1 t2) = sptree_lookup k (BN t1 t2)`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [mk_BN_def] THEN
  STRUCT_CASES_TAC(ISPEC `t1:(A)spt` (cases_of `:(A)spt`)) THEN
  STRUCT_CASES_TAC(ISPEC `t2:(A)spt` (cases_of `:(A)spt`)) THEN
  MATCH_REDUCE_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC[lookup_def; COND_ID] THEN
  REPEAT COND_CASES_TAC THEN
  REWRITE_TAC[lookup_def; COND_ID]);;

let lookup_mk_BS = prove
 (`!k t1 x (t2:(A)spt).
     sptree_lookup k (mk_BS t1 x t2) = sptree_lookup k (BS t1 x t2)`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [mk_BS_def] THEN
  STRUCT_CASES_TAC(ISPEC `t1:(A)spt` (cases_of `:(A)spt`)) THEN
  STRUCT_CASES_TAC(ISPEC `t2:(A)spt` (cases_of `:(A)spt`)) THEN
  MATCH_REDUCE_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC[lookup_def; COND_ID] THEN
  COND_CASES_TAC THEN
  REWRITE_TAC[lookup_def; COND_ID]);;

(* the lookup of a delete: HOL4 sptreeScript.sml:717 *)

let lookup_delete = prove
 (`!(t:(A)spt) k1 k2.
     sptree_lookup k1 (sptree_delete k2 t) =
     (if k1 = k2 then NONE else sptree_lookup k1 t)`,
  MATCH_MP_TAC spt_INDUCT THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[delete_def; lookup_def;
                COND_ID];
    REPEAT GEN_TAC THEN
    REWRITE_TAC[delete_def] THEN
    ASM_CASES_TAC `k2 = 0` THEN ASM_CASES_TAC `k1 = 0` THEN
    ASM_REWRITE_TAC[lookup_def; COND_ID] THEN
    ASM_MESON_TAC[];
    REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
    ASM_CASES_TAC `k2 = 0` THEN ASM_CASES_TAC `k1 = 0` THEN
    ASM_CASES_TAC `EVEN k2` THEN ASM_CASES_TAC `EVEN k1` THEN
    ASM_REWRITE_TAC[delete_def; lookup_mk_BN] THEN
    ASM_REWRITE_TAC[lookup_def] THEN
    ASM_MESON_TAC[SPT_BIT_EQ_EQ];
    REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
    ASM_CASES_TAC `k2 = 0` THEN ASM_CASES_TAC `k1 = 0` THEN
    ASM_CASES_TAC `EVEN k2` THEN ASM_CASES_TAC `EVEN k1` THEN
    ASM_REWRITE_TAC[delete_def; lookup_mk_BS;
                    lookup_mk_BN] THEN
    ASM_REWRITE_TAC[lookup_def] THEN
    ASM_MESON_TAC[SPT_BIT_EQ_EQ]]);;

(* and the lookup of a union, which takes the left value where there
   is one.  HOL4's optcase_lemma, and the same as a conditional,
   which is the form that a rewrite of the port can use: a match on
   a scrutinee that is a variable is not reduced by MATCH_REDUCE_TAC
   but mangled *)

let optcase_lemma = prove
 (`!opt:(A)option.
     (match opt with NONE -> NONE | SOME v -> SOME v) = opt`,
  GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `opt:(A)option` (cases_of `:(A)option`)) THEN
  MATCH_REDUCE_TAC THEN REWRITE_TAC[]);;

let OPT_MATCH_COND = prove
 (`!(opt:(A)option) y.
     (match opt with NONE -> y | SOME v -> SOME v) =
     (if opt = NONE then y else opt)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `opt:(A)option` (cases_of `:(A)option`)) THEN
  MATCH_REDUCE_TAC THEN
  REWRITE_TAC[distinctness "option"]);;

let optcase_cond = REWRITE_RULE[OPT_MATCH_COND] optcase_lemma;;

let lookup_union = prove
 (`!(m1:(A)spt) m2 k.
     sptree_lookup k (sptree_union m1 m2) =
     (match sptree_lookup k m1 with
        NONE -> sptree_lookup k m2
      | SOME v -> SOME v)`,
  REWRITE_TAC[OPT_MATCH_COND] THEN
  MATCH_MP_TAC spt_INDUCT THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[union_def; lookup_def];
    REPEAT GEN_TAC THEN
    STRUCT_CASES_TAC(ISPEC `m2:(A)spt` (cases_of `:(A)spt`)) THEN
    REWRITE_TAC[union_def] THEN MATCH_REDUCE_TAC THEN
    ASM_CASES_TAC `k = 0` THEN
    ASM_REWRITE_TAC[lookup_def; optcase_cond;
                    distinctness "option"];
    REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
    STRUCT_CASES_TAC(ISPEC `m2:(A)spt` (cases_of `:(A)spt`)) THEN
    REWRITE_TAC[union_def] THEN MATCH_REDUCE_TAC THEN
    ASM_CASES_TAC `k = 0` THEN ASM_CASES_TAC `EVEN k` THEN
    ASM_REWRITE_TAC[lookup_def; optcase_cond;
                    distinctness "option"];
    REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
    STRUCT_CASES_TAC(ISPEC `m2:(A)spt` (cases_of `:(A)spt`)) THEN
    REWRITE_TAC[union_def] THEN MATCH_REDUCE_TAC THEN
    ASM_CASES_TAC `k = 0` THEN ASM_CASES_TAC `EVEN k` THEN
    ASM_REWRITE_TAC[lookup_def; optcase_cond;
                    distinctness "option"]]);;
