(* ================================================================ *)
(*  The theorems of sptreeTheory that LightCake proves and this   *)
(*  port needs, taken from its hol4/sptree.                       *)
(*                                                                *)
(*  LightCake is the other HOL Light port of CakeML               *)
(*  (hol-light-family/LightCake, BSD 3-Clause); its HOL4 library  *)
(*  layer is proved, and of these theories this port has only     *)
(*  the definitions that CakeML needs.  tools/lightcake.py        *)
(*  writes this file: the statements and the proofs are           *)
(*  LightCake's, with its constants under the names this port     *)
(*  gives them.  What it could not take, and why, is at the end.  *)
(* ================================================================ *)


let spt_distinct = distinctness "spt";;

let spt_inject = injectivity "spt";;

let SPTAUX_DIV2_LT = prove
 (`!k. ~(k = 0) ==> (k - 1) DIV 2 < k`,
  ARITH_TAC);;

let SPTAUX_bit_cases = prove
 (`!n. n = 0 \/ (?m. n = 2 * m + 1) \/ (?m. n = 2 * m + 2)`,
  INDUCT_TAC THEN REWRITE_TAC[NOT_SUC] THEN
  FIRST_X_ASSUM(REPEAT_TCL DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THENL
   [DISJ1_TAC THEN EXISTS_TAC `0` THEN ARITH_TAC;
    DISJ2_TAC THEN EXISTS_TAC `m:num` THEN ARITH_TAC;
    DISJ1_TAC THEN EXISTS_TAC `m + 1` THEN ARITH_TAC]);;

let SPTAUX_bit_induction = prove
 (`!P. P 0 /\ (!n. P n ==> P (2 * n + 1)) /\ (!n. P n ==> P (2 * n + 2))
       ==> !n. P n`,
  GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num`
    THEN
  REPEAT_TCL STRIP_THM_THEN SUBST1_TAC (SPEC `n:num` SPTAUX_bit_cases)
    THEN
  ASM_MESON_TAC[ARITH_RULE `m < 2 * m + 1 /\ m < 2 * m + 2`]);;

let SPTAUX_BIT_RW = prove
 (`(!m. ~(2 * m + 1 = 0)) /\ (!m. ~(2 * m + 2 = 0)) /\
   (!m. ~(0 = 2 * m + 1)) /\ (!m. ~(0 = 2 * m + 2)) /\
   (!m. EVEN (2 * m + 1) <=> F) /\ (!m. EVEN (2 * m + 2) <=> T) /\
   (!m. ODD (2 * m + 1) <=> T) /\ (!m. ODD (2 * m + 2) <=> F) /\
   (!m. ((2 * m + 1) - 1) DIV 2 = m) /\ (!m. ((2 * m + 2) - 1) DIV 2 =
     m) /\
   (!m n. 2 * m + 1 = 2 * n + 1 <=> m = n) /\
   (!m n. 2 * m + 2 = 2 * n + 2 <=> m = n) /\
   (!m n. ~(2 * m + 1 = 2 * n + 2)) /\ (!m n. ~(2 * m + 2 = 2 * n +
     1))`,
  REWRITE_TAC[EVEN_ADD; EVEN_MULT; ODD_ADD; ODD_MULT; ARITH] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN TRY ARITH_TAC THEN
  DISCH_THEN(MP_TAC o AP_TERM `EVEN`) THEN
  REWRITE_TAC[EVEN_ADD; EVEN_MULT; ARITH]);;

let SPTAUX_BITS_TAC (k:term) : tactic =
  REPEAT_TCL STRIP_THM_THEN SUBST_ALL_TAC (SPEC k SPTAUX_bit_cases);;

let lookup_ind = prove
 (`!P. (!k. P k (LN:A spt)) /\ (!k (a:A). P k (LS a)) /\
       (!k t1 t2. (~(k = 0) ==> P ((k - 1) DIV 2) (if EVEN k then t1
         else t2))
                  ==> P k (BN t1 t2)) /\
       (!k t1 (a:A) t2.
          (~(k = 0) ==> P ((k - 1) DIV 2) (if EVEN k then t1 else t2))
          ==> P k (BS t1 a t2))
       ==> !k t. P k t`,
  GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC num_WF THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN MATCH_MP_TAC spt_INDUCT THEN
  ASM_MESON_TAC[SPTAUX_DIV2_LT]);;

let lookup_rwts = prove
 (`sptree_lookup k (LN:A spt) = NONE /\
   sptree_lookup 0 (LS (a:A)) = SOME a /\
   sptree_lookup 0 (BN t1 t2) = NONE:A option /\
   sptree_lookup 0 (BS t1 (a:A) t2) = SOME a`,
  REWRITE_TAC[lookup_def]);;

let SPTAUX_lookup_bits = prove
 (`(!m. sptree_lookup (2 * m + 1) (LN:A spt) = NONE) /\
   (!m (a:A). sptree_lookup (2 * m + 1) (LS a) = NONE) /\
   (!m t1 (t2:A spt). sptree_lookup (2 * m + 1) (BN t1 t2) =
     sptree_lookup m t2) /\
   (!m t1 (a:A) t2. sptree_lookup (2 * m + 1) (BS t1 a t2) =
     sptree_lookup m t2) /\
   (!m. sptree_lookup (2 * m + 2) (LN:A spt) = NONE) /\
   (!m (a:A). sptree_lookup (2 * m + 2) (LS a) = NONE) /\
   (!m t1 (t2:A spt). sptree_lookup (2 * m + 2) (BN t1 t2) =
     sptree_lookup m t1) /\
   (!m t1 (a:A) t2. sptree_lookup (2 * m + 2) (BS t1 a t2) =
     sptree_lookup m t1)`,
  REWRITE_TAC[lookup_def; SPTAUX_BIT_RW]);;

let SPTAUX_insert_bits = prove
 (`(!a:A. sptree_insert 0 a LN = LS a) /\
   (!a a':A. sptree_insert 0 a (LS a') = LS a) /\
   (!(a:A) t1 t2. sptree_insert 0 a (BN t1 t2) = BS t1 a t2) /\
   (!(a:A) a' t1 t2. sptree_insert 0 a (BS t1 a' t2) = BS t1 a t2) /\
   (!m (a:A). sptree_insert (2 * m + 1) a LN = BN LN (sptree_insert m a
     LN)) /\
   (!m (a:A) a'. sptree_insert (2 * m + 1) a (LS a') = BS LN a'
     (sptree_insert m a LN)) /\
   (!m (a:A) t1 t2. sptree_insert (2 * m + 1) a (BN t1 t2) = BN t1
     (sptree_insert m a t2)) /\
   (!m (a:A) a' t1 t2.
      sptree_insert (2 * m + 1) a (BS t1 a' t2) = BS t1 a'
        (sptree_insert m a t2)) /\
   (!m (a:A). sptree_insert (2 * m + 2) a LN = BN (sptree_insert m a LN)
     LN) /\
   (!m (a:A) a'. sptree_insert (2 * m + 2) a (LS a') = BS (sptree_insert
     m a LN) a' LN) /\
   (!m (a:A) t1 t2. sptree_insert (2 * m + 2) a (BN t1 t2) = BN
     (sptree_insert m a t1) t2) /\
   (!m (a:A) a' t1 t2.
      sptree_insert (2 * m + 2) a (BS t1 a' t2) = BS (sptree_insert m a
        t1) a' t2)`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [insert_def] THEN
    REWRITE_TAC[SPTAUX_BIT_RW]);;

let insert_notEmpty = prove
 (`~(sptree_insert k (a:A) t = LN)`,
  SPTAUX_CASES_TAC `t:A spt` THEN ONCE_REWRITE_TAC[insert_def] THEN
  REPEAT COND_CASES_TAC THEN REWRITE_TAC[spt_distinct]);;

let wf_insert = prove
 (`!k (a:A) t. sptree_wf t ==> sptree_wf (sptree_insert k a t)`,
  MATCH_MP_TAC SPTAUX_bit_induction THEN REPEAT STRIP_TAC THEN
  SPTAUX_CASES_TAC `t:A spt` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[wf_def]) THEN
  ASM_SIMP_TAC[SPTAUX_insert_bits; wf_def; insert_notEmpty]);;

let mk_BN_thm = prove
 (`!t1 t2:A spt. mk_BN t1 t2 = if t1 = LN /\ t2 = LN then LN else BN t1
   t2`,
  REPEAT GEN_TAC THEN SPTAUX_CASES_TAC `t1:A spt` THEN
  SPTAUX_CASES_TAC `t2:A spt` THEN REWRITE_TAC[mk_BN_def;
    spt_distinct]);;

let mk_BS_thm = prove
 (`!t1 t2:A spt. mk_BS t1 x t2 = if t1 = LN /\ t2 = LN then LS x else BS
   t1 x t2`,
  REPEAT GEN_TAC THEN SPTAUX_CASES_TAC `t1:A spt` THEN
  SPTAUX_CASES_TAC `t2:A spt` THEN REWRITE_TAC[mk_BS_def;
    spt_distinct]);;

let wf_delete = prove
 (`!t k. sptree_wf (t:A spt) ==> sptree_wf (sptree_delete k t)`,
  MATCH_MP_TAC spt_INDUCT THEN REWRITE_TAC[wf_def; delete_def] THEN
  REPEAT STRIP_TAC THEN REPEAT COND_CASES_TAC THEN
  ASM_SIMP_TAC[wf_def; mk_BN_thm; mk_BS_thm] THEN
  REPEAT COND_CASES_TAC THEN ASM_SIMP_TAC[wf_def]);;

let lookup_insert1 = prove
 (`!k (a:A) t. sptree_lookup k (sptree_insert k a t) = SOME a`,
  REWRITE_TAC[lookup_insert]);;

let SPTAUX_wf_mk_BN = prove
 (`!t1 t2:A spt. sptree_wf (mk_BN t1 t2) <=> sptree_wf t1 /\ sptree_wf
   t2`,
  REPEAT GEN_TAC THEN SPTAUX_CASES_TAC `t1:A spt` THEN
  SPTAUX_CASES_TAC `t2:A spt` THEN REWRITE_TAC[mk_BN_def; wf_def;
    spt_distinct]);;

let SPTAUX_wf_mk_BS = prove
 (`!t1 (x:A) t2. sptree_wf (mk_BS t1 x t2) <=> sptree_wf t1 /\ sptree_wf
   t2`,
  REPEAT GEN_TAC THEN SPTAUX_CASES_TAC `t1:A spt` THEN
  SPTAUX_CASES_TAC `t2:A spt` THEN REWRITE_TAC[mk_BS_def; wf_def;
    spt_distinct]);;

let SPTAUX_lookup_mk_BN = prove
 (`sptree_lookup k (mk_BN t1 t2) = sptree_lookup k (BN t1 t2:A spt)`,
  SPTAUX_CASES_TAC `t1:A spt` THEN SPTAUX_CASES_TAC `t2:A spt` THEN
  REWRITE_TAC[mk_BN_def; lookup_def] THEN COND_CASES_TAC THEN
  REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[lookup_def]);;

let SPTAUX_lookup_mk_BS = prove
 (`sptree_lookup k (mk_BS t1 x t2) = sptree_lookup k (BS t1 (x:A) t2)`,
  SPTAUX_CASES_TAC `t1:A spt` THEN SPTAUX_CASES_TAC `t2:A spt` THEN
  REWRITE_TAC[mk_BS_def; lookup_def] THEN COND_CASES_TAC THEN
  REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[lookup_def]);;

let SPTAUX_lookup_cond = prove
 (`!k c (t1:A spt) t2. sptree_lookup k (if c then t1 else t2) =
                       if c then sptree_lookup k t1 else sptree_lookup k
                         t2`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[]);;

let SPTAUX_domain_bits = prove
 (`(0 IN domain (LN:A spt) <=> F) /\
   (!a:A. 0 IN domain (LS a) <=> T) /\
   (!t1 t2:A spt. 0 IN domain (BN t1 t2) <=> F) /\
   (!t1 (a:A) t2. 0 IN domain (BS t1 a t2) <=> T) /\
   (!m. (2 * m + 1) IN domain (LN:A spt) <=> F) /\
   (!m (a:A). (2 * m + 1) IN domain (LS a) <=> F) /\
   (!m t1 t2:A spt. (2 * m + 1) IN domain (BN t1 t2) <=> m IN domain t2)
     /\
   (!m t1 (a:A) t2. (2 * m + 1) IN domain (BS t1 a t2) <=> m IN domain
     t2) /\
   (!m. (2 * m + 2) IN domain (LN:A spt) <=> F) /\
   (!m (a:A). (2 * m + 2) IN domain (LS a) <=> F) /\
   (!m t1 t2:A spt. (2 * m + 2) IN domain (BN t1 t2) <=> m IN domain t1)
     /\
   (!m t1 (a:A) t2. (2 * m + 2) IN domain (BS t1 a t2) <=> m IN domain
     t1)`,
  REWRITE_TAC[domain_def; IN_UNION; IN_IMAGE; IN_INSERT; NOT_IN_EMPTY]
    THEN
  REWRITE_TAC[SPTAUX_BIT_RW; UNWIND_THM1; UNWIND_THM2] THEN
  REWRITE_TAC[ARITH_RULE `2 * m + 1 = 2 * x + 1 <=> x = m`;
              ARITH_RULE `2 * m + 2 = 2 * x + 2 <=> x = m`;
              UNWIND_THM2]);;

let set_domain_list = prove
 (`set_of_list (domain_list t) = domain (t:A spt)`,
  SPEC_TAC(`t:A spt`,`t:A spt`) THEN MATCH_MP_TAC spt_INDUCT THEN
  ASM_REWRITE_TAC[domain_list_def; domain_def; set_of_list;
    SET_OF_LIST_APPEND;
                  SET_OF_LIST_MAP] THEN
  SET_TAC[]);;

let FINITE_domain = prove
 (`FINITE (domain (t:A spt))`,
  SPEC_TAC(`t:A spt`,`t:A spt`) THEN MATCH_MP_TAC spt_INDUCT THEN
  ASM_SIMP_TAC[domain_def; FINITE_UNION; FINITE_IMAGE; FINITE_INSERT;
               FINITE_EMPTY]);;

let IN_domain = prove
 (`!n (x:A) t1 t2.
     (n IN domain (LN:A spt) <=> F) /\
     (n IN domain (LS x) <=> (n = 0)) /\
     (n IN domain (BN t1 t2) <=>
        ~(n = 0) /\ (if EVEN n then ((n - 1) DIV 2) IN domain t1
                     else ((n - 1) DIV 2) IN domain t2)) /\
     (n IN domain (BS t1 x t2) <=>
        (n = 0) \/ (if EVEN n then ((n - 1) DIV 2) IN domain t1
                    else ((n - 1) DIV 2) IN domain t2))`,
  REPEAT GEN_TAC THEN SPTAUX_BITS_TAC `n:num` THEN
  REWRITE_TAC[SPTAUX_domain_bits; SPTAUX_BIT_RW]);;

let size_insert = prove
 (`!k (v:A) m. size (sptree_insert k v m) =
               if k IN domain m then size m else size m + 1`,
  MATCH_MP_TAC SPTAUX_bit_induction THEN REPEAT STRIP_TAC THEN
  SPTAUX_CASES_TAC `m:A spt` THEN
  ASM_REWRITE_TAC[SPTAUX_insert_bits; sptree_size_def;
    SPTAUX_domain_bits;
                  CONJUNCT1 domain_def; NOT_IN_EMPTY] THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let SPTAUX_lookup_fromList_gen = prove
 (`!l:A list i n t.
     sptree_lookup n (SND (FOLDL (\(i,t) a. (i + 1,sptree_insert i a t))
       (i,t) l)) =
     if n < i then sptree_lookup n t
     else if n < LENGTH l + i then SOME (EL (n - i) l)
     else sptree_lookup n t`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[FOLDL; LENGTH; ADD_CLAUSES] THENL
   [REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[lookup_insert] THEN REPEAT GEN_TAC THEN
  ASM_CASES_TAC `n:num < i` THENL
   [ASM_SIMP_TAC[ARITH_RULE `n < i ==> n < i + 1 /\ ~(n = i)`]; ALL_TAC]
     THEN
  ASM_CASES_TAC `n:num = i` THENL
   [ASM_REWRITE_TAC[ARITH_RULE `i < i + 1 /\ i < SUC (m + i) /\ i - i =
     0`;
                    EL; HD];
    ALL_TAC] THEN
  ASM_SIMP_TAC[ARITH_RULE `~(n < i) /\ ~(n = i) ==> ~(n < i + 1)`;
               ARITH_RULE `n < SUC (m + i) <=> n < m + i + 1`] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `n - i = SUC (n - (i + 1))` SUBST1_TAC THENL
   [ASM_ARITH_TAC; REWRITE_TAC[EL; TL]]);;

let lookup_fromList = prove
 (`sptree_lookup n (sptree_fromList l) =
   if n < LENGTH l then SOME (EL n (l:A list)) else NONE`,
  REWRITE_TAC[fromList_def; SPTAUX_lookup_fromList_gen; ADD_CLAUSES; LT;
              SUB_0; lookup_rwts]);;

let domain_insert = prove
 (`domain (sptree_insert k (semanticPrimitives_v:A) t) = k INSERT domain
   t`,
  REWRITE_TAC[EXTENSION; domain_lookup; lookup_insert; IN_INSERT] THEN
  MESON_TAC[]);;

let domain_sing = prove
 (`domain (sptree_insert k (semanticPrimitives_v:A) LN) = {k}`,
  REWRITE_TAC[domain_insert; domain_def]);;

let SPTAUX_card_images = prove
 (`!s t. FINITE s /\ FINITE t
         ==> CARD (IMAGE (\n. 2 * n + 2) s UNION IMAGE (\n. 2 * n + 1)
           t) =
             CARD s + CARD t /\
             CARD (({0} UNION IMAGE (\n. 2 * n + 2) s) UNION
                   IMAGE (\n. 2 * n + 1) t) =
             CARD s + CARD t + 1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `CARD (IMAGE (\n. 2 * n + 2) s) = CARD (s:num->bool) /\
                CARD (IMAGE (\n. 2 * n + 1) t) = CARD (t:num->bool)`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_REWRITE_TAC[]
     THEN
    ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (\n. 2 * n + 2) s INTER IMAGE (\n. 2 * n + 1) t =
    {} /\
                ({0} UNION IMAGE (\n. 2 * n + 2) s) INTER
                IMAGE (\n. 2 * n + 1) t = {} /\
                {0} INTER IMAGE (\n. 2 * n + 2) s = {}`
    STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INTER; IN_UNION; IN_IMAGE; IN_INSERT;
                NOT_IN_EMPTY] THEN
    MESON_TAC[SPTAUX_BIT_RW]; ALL_TAC] THEN
  ASM_SIMP_TAC[CARD_UNION; FINITE_UNION; FINITE_IMAGE; FINITE_INSERT;
               FINITE_EMPTY; CARD_SING] THEN
  ARITH_TAC);;

let size_domain = prove
 (`!t:A spt. size t = CARD (domain t)`,
  MATCH_MP_TAC spt_INDUCT THEN
  ASM_SIMP_TAC[sptree_size_def; domain_def; SPTAUX_card_images;
    FINITE_domain;
               CARD_CLAUSES; CARD_SING] THEN ARITH_TAC);;

let domain_delete = prove
 (`domain (sptree_delete k (t:A spt)) = domain t DELETE k`,
  REWRITE_TAC[EXTENSION; domain_lookup; lookup_delete; IN_DELETE] THEN
  MESON_TAC[option_DISTINCT]);;

let SPTAUX_lrnext_bits = prove
 (`lrnext 0 = 1 /\ lrnext 1 = 2 /\ lrnext 2 = 2 /\
   (!m. lrnext (2 * m + 1) = 2 * lrnext m) /\
   (!m. lrnext (2 * m + 2) = 2 * lrnext m)`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [lrnext_def] THEN
  REWRITE_TAC[SPTAUX_BIT_RW] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ONCE_REWRITE_TAC[lrnext_def] THEN CONV_TAC NUM_REDUCE_CONV);;

let SPTAUX_lrlemma1 = prove
 (`!i. lrnext (i + lrnext i) = 2 * lrnext i`,
  MATCH_MP_TAC SPTAUX_bit_induction THEN
  REWRITE_TAC[SPTAUX_lrnext_bits; ADD_CLAUSES; ARITH] THEN
  REWRITE_TAC[ARITH_RULE `(2 * m + 1) + 2 * x = 2 * (m + x) + 1 /\
                          (2 * m + 2) + 2 * x = 2 * (m + x) + 2`] THEN
  SIMP_TAC[SPTAUX_lrnext_bits]);;

let SPTAUX_lrlemma2 = prove
 (`!i. lrnext (i + 2 * lrnext i) = 2 * lrnext i`,
  MATCH_MP_TAC SPTAUX_bit_induction THEN
  REWRITE_TAC[SPTAUX_lrnext_bits; ADD_CLAUSES; ARITH] THEN
  REWRITE_TAC[ARITH_RULE `(2 * m + 1) + 2 * 2 * x = 2 * (m + 2 * x) + 1
    /\
                          (2 * m + 2) + 2 * 2 * x = 2 * (m + 2 * x) +
                            2`] THEN
  SIMP_TAC[SPTAUX_lrnext_bits]);;

let SPTAUX_lrnext_pos = prove
 (`!i. ~(lrnext i = 0)`,
  MATCH_MP_TAC SPTAUX_bit_induction THEN
  ASM_REWRITE_TAC[SPTAUX_lrnext_bits; MULT_EQ_0; ARITH]);;

let spt_acc_thm = prove
 (`spt_acc i k =
   if k = 0 then i
   else spt_acc (i + if EVEN k then 2 * lrnext i else lrnext i) ((k - 1)
     DIV 2)`,
  SPTAUX_CASES_TAC `k:num` THEN REWRITE_TAC[spt_acc_def; NOT_SUC;
    SUC_SUB1]);;

let spt_acc_eqn = prove
 (`!k i. spt_acc i k = lrnext i * k + i`,
  MATCH_MP_TAC SPTAUX_bit_induction THEN
  CONJ_TAC THENL [REWRITE_TAC[spt_acc_def] THEN ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN GEN_TAC THEN
  ONCE_REWRITE_TAC[spt_acc_thm] THEN
  ASM_REWRITE_TAC[SPTAUX_BIT_RW; SPTAUX_lrlemma1; SPTAUX_lrlemma2] THEN
  ARITH_TAC);;

let spt_acc_0 = prove
 (`!k. spt_acc 0 k = k`,
  REWRITE_TAC[spt_acc_eqn; SPTAUX_lrnext_bits] THEN ARITH_TAC);;

let SPTAUX_foldi_thm = REWRITE_RULE[LET_DEF; LET_END_DEF] foldi_def;;

let SPTAUX_EXISTS_BITS = prove
 (`!P. (?n. P n) <=> P 0 \/ (?m. P (2 * m + 1)) \/ (?m. P (2 * m + 2))`,
  GEN_TAC THEN EQ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` MP_TAC) THEN
  REPEAT_TCL STRIP_THM_THEN SUBST1_TAC (SPEC `n:num` SPTAUX_bit_cases)
    THEN
  MESON_TAC[]);;

let SPTAUX_OFFSET_RW = prove
 (`(!i c. i + c * 0 = i) /\
   (!i c m. i + c * (2 * m + 1) = (i + c) + (2 * c) * m) /\
   (!i c m. i + c * (2 * m + 2) = (i + 2 * c) + (2 * c) * m)`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN CONV_TAC NUM_RING);;

let SPTAUX_offset_lookup = prove
 (`(!i c k (v:A). (?n. k = i + c * n /\ sptree_lookup n (LN:A spt) =
   SOME v) <=> F) /\
   (!i c k (v:A) a.
      (?n. k = i + c * n /\ sptree_lookup n (LS a) = SOME v) <=> k = i
        /\ a = v) /\
   (!i c k (v:A) t1 t2.
      (?n. k = i + c * n /\ sptree_lookup n (BN t1 t2) = SOME v) <=>
      (?n. k = (i + 2 * c) + (2 * c) * n /\ sptree_lookup n t1 = SOME v)
        \/
      (?n. k = (i + c) + (2 * c) * n /\ sptree_lookup n t2 = SOME v)) /\
   (!i c k (v:A) a t1 t2.
      (?n. k = i + c * n /\ sptree_lookup n (BS t1 a t2) = SOME v) <=>
      (k = i /\ a = v) \/
      (?n. k = (i + 2 * c) + (2 * c) * n /\ sptree_lookup n t1 = SOME v)
        \/
      (?n. k = (i + c) + (2 * c) * n /\ sptree_lookup n t2 = SOME v))`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [SPTAUX_EXISTS_BITS] THEN
  REWRITE_TAC[lookup_rwts; SPTAUX_lookup_bits; SPTAUX_OFFSET_RW;
              option_DISTINCT; option_INJ] THEN
  MESON_TAC[]);;

let SPTAUX_offset_domain = prove
 (`(!i c. IMAGE (\n. i + c * n) (domain (LN:A spt)) = {}) /\
   (!i c a:A. IMAGE (\n. i + c * n) (domain (LS a)) = {i}) /\
   (!i c t1 t2:A spt.
      IMAGE (\n. i + c * n) (domain (BN t1 t2)) =
      IMAGE (\n. (i + 2 * c) + (2 * c) * n) (domain t1) UNION
      IMAGE (\n. (i + c) + (2 * c) * n) (domain t2)) /\
   (!i c (a:A) t1 t2.
      IMAGE (\n. i + c * n) (domain (BS t1 a t2)) =
      (i INSERT IMAGE (\n. (i + 2 * c) + (2 * c) * n) (domain t1)) UNION
      IMAGE (\n. (i + c) + (2 * c) * n) (domain t2))`,
  REWRITE_TAC[CONJUNCT1 domain_def; IMAGE_CLAUSES] THEN CONJ_TAC THENL
   [REWRITE_TAC[domain_def; IMAGE_CLAUSES; SPTAUX_OFFSET_RW]; ALL_TAC]
     THEN
  CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNION; IN_INSERT] THEN
  X_GEN_TAC `k:num` THEN
  GEN_REWRITE_TAC LAND_CONV [SPTAUX_EXISTS_BITS] THEN
  REWRITE_TAC[SPTAUX_domain_bits; SPTAUX_OFFSET_RW] THEN
  MESON_TAC[]);;

let SPTAUX_UNION_RW = prove
 (`(!a s1 s2:num->bool. (a UNION s1) UNION s2 = a UNION (s1 UNION s2))
   /\
   (!i a s1 s2:num->bool.
      (i INSERT (a UNION s1)) UNION s2 = a UNION ((i INSERT s1) UNION
        s2)) /\
   (!i a:num->bool. a UNION {i} = i INSERT a)`,
  SET_TAC[]);;

let set_foldi_keys = prove
 (`!t:A spt a i. foldi (\k v a. k INSERT a) i a t =
                 a UNION IMAGE (\n. i + lrnext i * n) (domain t)`,
  MATCH_MP_TAC spt_INDUCT THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[SPTAUX_foldi_thm; SPTAUX_offset_domain;
    SPTAUX_lrlemma1;
                  SPTAUX_lrlemma2; UNION_EMPTY; SPTAUX_UNION_RW]);;

let domain_foldi = prove
 (`domain t = foldi (\k (v:A) a. k INSERT a) 0 {} t`,
  REWRITE_TAC[set_foldi_keys; UNION_EMPTY; SPTAUX_lrnext_bits;
    ADD_CLAUSES;
              MULT_CLAUSES; IMAGE_ID]);;

let SPTAUX_ACC_RW = prove
 (`(!c i. c * 0 + i = i) /\
   (!c i m. c * (2 * m + 1) + i = (2 * c) * m + (i + c)) /\
   (!c i m. c * (2 * m + 2) + i = (2 * c) * m + (i + 2 * c))`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN CONV_TAC NUM_RING);;

let domain_empty = prove
 (`!t:A spt. sptree_wf t ==> ((t = LN) <=> (domain t = EMPTY))`,
  MATCH_MP_TAC spt_INDUCT THEN
  REWRITE_TAC[wf_def; domain_def; spt_distinct; NOT_INSERT_EMPTY;
              EMPTY_UNION; IMAGE_EQ_EMPTY] THEN
  MESON_TAC[]);;

let SPTAUX_ALL_DISTINCT_CARD = prove
 (`!l:A list. ALL_DISTINCT l <=> CARD (set_of_list l) = LENGTH l`,
  LIST_INDUCT_TAC THEN
  ASM_SIMP_TAC[ALL_DISTINCT; set_of_list; LENGTH; CARD_CLAUSES;
               FINITE_SET_OF_LIST; IN_SET_OF_LIST] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[SUC_INJ] THEN
  MP_TAC(ISPEC `t:A list` CARD_SET_OF_LIST_LE) THEN ARITH_TAC);;

let SPTAUX_toListA_APPEND = prove
 (`!t:A spt acc acc'.
     toListA (APPEND acc acc') t = APPEND (toListA acc t) acc'`,
  MATCH_MP_TAC spt_INDUCT THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[toListA_def; APPEND] THEN
  ASM_REWRITE_TAC[GSYM(CONJUNCT2 APPEND)]);;

let toListA_append = prove
 (`!t:A spt acc. toListA acc t = APPEND (toListA [] t) acc`,
  REWRITE_TAC[GSYM SPTAUX_toListA_APPEND; APPEND]);;

let SPTAUX_LENGTH_toListA = prove
 (`!t:A spt acc. LENGTH (toListA acc t) = size t + LENGTH acc`,
  MATCH_MP_TAC spt_INDUCT THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[toListA_def; sptree_size_def; LENGTH] THEN
    ARITH_TAC);;

let size_zero_empty = prove
 (`!x:A spt. size x = 0 <=> domain x = EMPTY`,
  MATCH_MP_TAC spt_INDUCT THEN
  ASM_REWRITE_TAC[sptree_size_def; domain_def; ADD_EQ_0; ARITH;
                  NOT_INSERT_EMPTY; EMPTY_UNION; IMAGE_EQ_EMPTY] THEN
  MESON_TAC[]);;

let isEmpty_toListA = prove
 (`!t:A spt acc. sptree_wf t ==> ((t = LN) <=> (toListA acc t = acc))`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[toListA_def]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o AP_TERM `LENGTH:A list->num`) THEN
  REWRITE_TAC[SPTAUX_LENGTH_toListA; ARITH_RULE `a + b = b <=> a = 0`]
    THEN
  ASM_SIMP_TAC[size_zero_empty; domain_empty]);;

let isEmpty_toList = prove
 (`!t:A spt. sptree_wf t ==> ((t = LN) <=> (sptree_toList t = []))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[toList_def] THEN
  MATCH_MP_TAC isEmpty_toListA THEN ASM_REWRITE_TAC[]);;

let SPTAUX_EXISTS_lookup = prove
 (`(!x:A. (?k. sptree_lookup k (LN:A spt) = SOME x) <=> F) /\
   (!(x:A) a. (?k. sptree_lookup k (LS a) = SOME x) <=> a = x) /\
   (!(x:A) t1 t2. (?k. sptree_lookup k (BN t1 t2) = SOME x) <=>
                  (?k. sptree_lookup k t1 = SOME x) \/ (?k.
                    sptree_lookup k t2 = SOME x)) /\
   (!(x:A) a t1 t2. (?k. sptree_lookup k (BS t1 a t2) = SOME x) <=>
                  a = x \/ (?k. sptree_lookup k t1 = SOME x) \/
                  (?k. sptree_lookup k t2 = SOME x))`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [SPTAUX_EXISTS_BITS] THEN
  REWRITE_TAC[lookup_rwts; SPTAUX_lookup_bits; option_DISTINCT;
    option_INJ] THEN
  MESON_TAC[]);;

let SPTAUX_MEM_toListA = prove
 (`!t:A spt acc x. MEM x (toListA acc t) <=>
                   (MEM x acc \/ ?k. sptree_lookup k t = SOME x)`,
  MATCH_MP_TAC spt_INDUCT THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[toListA_def; MEM; SPTAUX_EXISTS_lookup] THEN
  MESON_TAC[]);;

let MEM_toList = prove
 (`!x (t:A spt). MEM x (sptree_toList t) <=> ?k. sptree_lookup k t =
   SOME x`,
  REWRITE_TAC[toList_def; SPTAUX_MEM_toListA; MEM]);;

let SPTAUX_FORALL_BITS = prove
 (`!P. (!n. P n) <=> P 0 /\ (!m. P (2 * m + 1)) /\ (!m. P (2 * m + 2))`,
  GEN_TAC THEN EQ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN X_GEN_TAC `n:num` THEN
  REPEAT_TCL STRIP_THM_THEN SUBST1_TAC (SPEC `n:num` SPTAUX_bit_cases)
    THEN
  ASM_REWRITE_TAC[]);;

let SPTAUX_lookup_NONE_LN = prove
 (`!t:A spt. sptree_wf t ==> (((!n. sptree_lookup n t = NONE) <=> t =
   LN) /\
                      ((!n. NONE = sptree_lookup n t) <=> t = LN))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[domain_empty] THEN
  REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; GSYM lookup_NONE_domain] THEN
  MESON_TAC[]);;

let spt_eq_thm = prove
 (`!t1 t2:A spt. sptree_wf t1 /\ sptree_wf t2 ==>
                 ((t1 = t2) <=> !n. sptree_lookup n t1 = sptree_lookup n
                   t2)`,
  MATCH_MP_TAC spt_INDUCT THEN REPEAT STRIP_TAC THEN
  SPTAUX_CASES_TAC `t2:A spt` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[wf_def]) THEN
  REWRITE_TAC[spt_distinct; spt_inject] THEN
  ONCE_REWRITE_TAC[SPTAUX_FORALL_BITS] THEN
  REWRITE_TAC[lookup_rwts; SPTAUX_lookup_bits; option_DISTINCT;
    option_INJ] THEN
  ASM_SIMP_TAC[SPTAUX_lookup_NONE_LN] THEN ASM_MESON_TAC[]);;

let wf_mk_wf = prove
 (`!t:A spt. sptree_wf (mk_wf t)`,
  MATCH_MP_TAC spt_INDUCT THEN
  ASM_SIMP_TAC[wf_def; mk_wf_def; SPTAUX_wf_mk_BS; SPTAUX_wf_mk_BN]);;

let wf_mk_id = prove
 (`!t:A spt. sptree_wf t ==> (mk_wf t = t)`,
  MATCH_MP_TAC spt_INDUCT THEN REWRITE_TAC[wf_def; mk_wf_def] THEN
  SIMP_TAC[mk_BS_thm; mk_BN_thm]);;

let lookup_mk_wf = prove
 (`!x t:A spt. sptree_lookup x (mk_wf t) = sptree_lookup x t`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  MATCH_MP_TAC spt_INDUCT THEN REPEAT STRIP_TAC THEN
  SPTAUX_BITS_TAC `x:num` THEN
  ASM_REWRITE_TAC[mk_wf_def; SPTAUX_lookup_mk_BS; SPTAUX_lookup_mk_BN;
                  lookup_rwts; SPTAUX_lookup_bits]);;

let domain_mk_wf = prove
 (`!t:A spt. domain (mk_wf t) = domain t`,
  REWRITE_TAC[EXTENSION; domain_lookup; lookup_mk_wf]);;

let mk_wf_eq = prove
 (`!t1 t2:A spt. (mk_wf t1 = mk_wf t2) <=> !x. sptree_lookup x t1 =
   sptree_lookup x t2`,
  MESON_TAC[spt_eq_thm; wf_mk_wf; lookup_mk_wf]);;

let insert_mk_wf = prove
 (`!x (v:A) t. sptree_insert x v (mk_wf t) = mk_wf (sptree_insert x v
   t)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `sptree_insert x v (mk_wf t) = mk_wf (sptree_insert x
    (v:A) (mk_wf t))`
    SUBST1_TAC THENL
   [MESON_TAC[wf_insert; wf_mk_wf; wf_mk_id]; ALL_TAC] THEN
  REWRITE_TAC[mk_wf_eq; lookup_insert; lookup_mk_wf]);;

let delete_mk_wf = prove
 (`!x t:A spt. sptree_delete x (mk_wf t) = mk_wf (sptree_delete x t)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `sptree_delete x (mk_wf t) = mk_wf (sptree_delete x
    (mk_wf (t:A spt)))`
    SUBST1_TAC THENL
   [MESON_TAC[wf_delete; wf_mk_wf; wf_mk_id]; ALL_TAC] THEN
  REWRITE_TAC[mk_wf_eq; lookup_delete; lookup_mk_wf]);;

let domain_fromAList = prove
 (`!ls:(num#A)list. domain (fromAList ls) = set_of_list (MAP FST ls)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[fromAList_def; domain_def; MAP;
    set_of_list] THEN
  SPTAUX_CASES_TAC `h:num#A` THEN
  ASM_REWRITE_TAC[fromAList_def; domain_insert; FST]);;

let wf_fromAList = prove
 (`!ls:(num#A)list. sptree_wf (fromAList ls)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[fromAList_def; wf_def] THEN
  SPTAUX_CASES_TAC `h:num#A` THEN
  ASM_SIMP_TAC[fromAList_def; wf_insert]);;

let SPTAUX_toListA_map = prove
 (`!s:A spt acc. toListA (MAP (f:A->B) acc) (sptree_map f s) = MAP f
   (toListA acc s)`,
  MATCH_MP_TAC spt_INDUCT THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[map_def; toListA_def; MAP] THEN
  ASM_REWRITE_TAC[GSYM(CONJUNCT2 MAP)]);;

let toList_map = prove
 (`!s:A spt. sptree_toList (sptree_map (f:A->B) s) = MAP f
   (sptree_toList s)`,
  REWRITE_TAC[toList_def; GSYM SPTAUX_toListA_map; MAP]);;

let domain_map = prove
 (`!s:A spt. domain (sptree_map (f:A->B) s) = domain s`,
  MATCH_MP_TAC spt_INDUCT THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[map_def; domain_def]);;

let map_LN = prove
 (`!t:A spt. (sptree_map (f:A->B) t = LN) <=> (t = LN)`,
  GEN_TAC THEN SPTAUX_CASES_TAC `t:A spt` THEN
  REWRITE_TAC[map_def; spt_distinct]);;

let wf_map = prove
 (`!t:A spt (f:A->B). sptree_wf (sptree_map f t) = sptree_wf t`,
  MATCH_MP_TAC spt_INDUCT THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[map_def; wf_def; map_LN]);;

let map_map_o = prove
 (`!t:A spt (f:B->C) (g:A->B). sptree_map f (sptree_map g t) =
   sptree_map (f o g) t`,
  MATCH_MP_TAC spt_INDUCT THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[map_def; o_THM]);;

let map_insert = prove
 (`!(f:A->B) x y z. sptree_map f (sptree_insert x y z) = sptree_insert x
   (f y) (sptree_map f z)`,
  GEN_TAC THEN MATCH_MP_TAC SPTAUX_bit_induction THEN REPEAT STRIP_TAC
    THEN
  SPTAUX_CASES_TAC `z:A spt` THEN
  ASM_REWRITE_TAC[SPTAUX_insert_bits; map_def]);;

let map_fromAList = prove
 (`sptree_map (f:A->B) (fromAList ls) = fromAList (MAP (\(k,v). (k,f v))
   ls)`,
  SPEC_TAC(`ls:(num#A)list`,`ls:(num#A)list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[fromAList_def; map_def; MAP] THEN
  SPTAUX_CASES_TAC `h:num#A` THEN
  ASM_REWRITE_TAC[fromAList_def; map_insert]);;

let insert_insert = prove
 (`!x1 x2 (v1:A) v2 t.
     sptree_insert x1 v1 (sptree_insert x2 v2 t) =
     if x1 = x2 then sptree_insert x1 v1 t else sptree_insert x2 v2
       (sptree_insert x1 v1 t)`,
  MATCH_MP_TAC SPTAUX_bit_induction THEN REPEAT STRIP_TAC THEN
  SPTAUX_BITS_TAC `x2:num` THEN SPTAUX_CASES_TAC `t:A spt` THEN
  ASM_REWRITE_TAC[SPTAUX_insert_bits; SPTAUX_BIT_RW] THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[SPTAUX_insert_bits] THEN
  ASM_MESON_TAC[]);;

let insert_shadow = prove
 (`!t a (b:A) c. sptree_insert a b (sptree_insert a c t) = sptree_insert
   a b t`,
  ONCE_REWRITE_TAC[insert_insert] THEN REWRITE_TAC[]);;

let lookup_0_spt_center = prove
 (`!spt:A spt. sptree_lookup 0 spt = spt_center spt`,
  GEN_TAC THEN SPTAUX_CASES_TAC `spt:A spt` THEN
  REWRITE_TAC[lookup_rwts; spt_center_def]);;

let SPTAUX_lookup_gen_bits = prove
 (`(!t:A spt. sptree_lookup 0 t = spt_center t) /\
   (!m t:A spt. sptree_lookup (2 * m + 1) t = sptree_lookup m (spt_right
     t)) /\
   (!m t:A spt. sptree_lookup (2 * m + 2) t = sptree_lookup m (spt_left
     t))`,
  REWRITE_TAC[lookup_0_spt_center] THEN CONJ_TAC THEN REPEAT GEN_TAC
    THEN
  SPTAUX_CASES_TAC `t:A spt` THEN
  REWRITE_TAC[SPTAUX_lookup_bits; spt_right_def; spt_left_def;
    lookup_rwts]);;

let lookup_spt_right = prove
 (`sptree_lookup i (spt_right spt) = sptree_lookup ((i * 2) + 1) (spt:A
   spt)`,
  REWRITE_TAC[ONCE_REWRITE_RULE[MULT_SYM] SPTAUX_lookup_gen_bits]);;

let lookup_spt_left = prove
 (`sptree_lookup i (spt_left spt) = sptree_lookup ((i * 2) + 2) (spt:A
   spt)`,
  REWRITE_TAC[ONCE_REWRITE_RULE[MULT_SYM] SPTAUX_lookup_gen_bits]);;

let subspt_lookup = prove
 (`!t1 t2:A spt.
     subspt t1 t2 <=>
     !x y. (sptree_lookup x t1 = SOME y) ==> (sptree_lookup x t2 = SOME
       y)`,
  MATCH_MP_TAC spt_INDUCT THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[subspt_eq] THEN ONCE_REWRITE_TAC[SPTAUX_FORALL_BITS] THEN
  ASM_REWRITE_TAC[lookup_rwts; SPTAUX_lookup_bits;
    SPTAUX_lookup_gen_bits;
                  option_DISTINCT; option_INJ; spt_center_def;
                  FORALL_UNWIND_THM1; FORALL_UNWIND_THM2] THEN
  MESON_TAC[]);;

let subspt_domain = prove
 (`!t1 (t2:1 spt). subspt t1 t2 <=> domain t1 SUBSET domain t2`,
  REWRITE_TAC[subspt_lookup; domain_lookup; SUBSET; FORALL_ONE_THM;
              EXISTS_ONE_THM] THEN
  MESON_TAC[]);;

let subspt_def = prove
 (`!sp1 sp2:A spt.
     subspt sp1 sp2 <=>
     !k. k IN domain sp1 ==> k IN domain sp2 /\
         (sptree_lookup k sp2 = sptree_lookup k sp1)`,
  REWRITE_TAC[subspt_lookup; domain_lookup] THEN
  MESON_TAC[option_INJ]);;

let subspt_refl = prove
 (`subspt sp (sp:A spt)`,
  REWRITE_TAC[subspt_lookup]);;

let subspt_trans = prove
 (`subspt sp1 sp2 /\ subspt sp2 sp3 ==> subspt sp1 (sp3:A spt)`,
  REWRITE_TAC[subspt_lookup] THEN MESON_TAC[]);;

let subspt_LN = prove
 (`(subspt LN (sp:A spt) <=> T) /\ (subspt sp (LN:A spt) <=> (domain sp
   = {}))`,
  REWRITE_TAC[subspt_def; EXTENSION; domain_def; NOT_IN_EMPTY] THEN
  MESON_TAC[]);;

let domain_eq = prove
 (`!t1:A spt t2:B spt.
     (domain t1 = domain t2) <=>
     !k. (sptree_lookup k t1 = NONE) <=> (sptree_lookup k t2 = NONE)`,
  REWRITE_TAC[EXTENSION; lookup_NONE_domain] THEN MESON_TAC[]);;

let wf_filter_v = prove
 (`!t:A spt f. sptree_wf t ==> sptree_wf (filter_v f t)`,
  MATCH_MP_TAC spt_INDUCT THEN REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[wf_def]) THEN
  REWRITE_TAC[filter_v_def] THEN REPEAT COND_CASES_TAC THEN
  ASM_SIMP_TAC[wf_def; SPTAUX_wf_mk_BN; SPTAUX_wf_mk_BS]);;

let wf_mk_BN = prove
 (`sptree_wf t1 /\ sptree_wf t2 ==> sptree_wf (mk_BN t1 (t2:A spt))`,
  REWRITE_TAC[SPTAUX_wf_mk_BN]);;

let wf_mk_BS = prove
 (`sptree_wf t1 /\ sptree_wf t2 ==> sptree_wf (mk_BS t1 (a:A) t2)`,
  REWRITE_TAC[SPTAUX_wf_mk_BS]);;

let wf_mapi = prove
 (`sptree_wf (sptree_mapi (f:num->A->B) pt)`,
  REWRITE_TAC[mapi_def] THEN
  SUBGOAL_THEN `!pt:A spt n. sptree_wf (mapi0 (f:num->A->B) n pt)`
    (fun th -> REWRITE_TAC[th]) THEN
  MATCH_MP_TAC spt_INDUCT THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[mapi0_def; LET_DEF; LET_END_DEF; wf_def;
    SPTAUX_wf_mk_BN;
                  SPTAUX_wf_mk_BS]);;

let num_set_domain_eq = prove
 (`!t1 t2:1 spt. sptree_wf t1 /\ sptree_wf t2 ==> ((domain t1 = domain
   t2) <=> (t1 = t2))`,
  SIMP_TAC[spt_eq_thm] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[EXTENSION; domain_lookup; EXISTS_ONE_THM] THEN
  EQ_TAC THEN DISCH_TAC THEN X_GEN_TAC `n:num` THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
    SPTAUX_CASES_TAC `sptree_lookup n (t1:1 spt)` THEN
    SPTAUX_CASES_TAC `sptree_lookup n (t2:1 spt)` THEN
    REWRITE_TAC[option_DISTINCT; option_INJ] THEN MESON_TAC[one];
    ASM_REWRITE_TAC[]]);;

let difference_sub = prove
 (`(difference a b = LN) ==> (domain (a:A spt) SUBSET domain (b:B
   spt))`,
  DISCH_THEN(MP_TAC o AP_TERM `domain:A spt->num->bool`) THEN
  REWRITE_TAC[domain_difference; domain_def] THEN SET_TAC[]);;

let delete_fail = prove
 (`!n t:A spt. sptree_wf t ==> (~(n IN domain t) <=> (sptree_delete n t
   = t))`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN ASM_SIMP_TAC[spt_eq_thm; wf_delete; lookup_delete]
     THEN
    GEN_TAC THEN COND_CASES_TAC THEN ASM_MESON_TAC[lookup_NONE_domain];
    DISCH_THEN(MP_TAC o AP_TERM `domain:A spt->num->bool`) THEN
    REWRITE_TAC[domain_delete] THEN SET_TAC[]]);;

let size_delete = prove
 (`!n t:A spt. size (sptree_delete n t) =
               if sptree_lookup n t = NONE then size t else size t - 1`,
  REWRITE_TAC[size_domain; domain_delete; lookup_NONE_domain] THEN
  SIMP_TAC[CARD_DELETE; FINITE_domain] THEN MESON_TAC[]);;

let lookup_fromList_outside = prove
 (`!k. LENGTH args <= k ==> (sptree_lookup k (sptree_fromList (args:A
   list)) = NONE)`,
  SIMP_TAC[lookup_fromList; GSYM NOT_LT]);;

let IMP_size_LESS_size = prove
 (`!x y:A spt. subspt x y /\ ~(domain x = domain y) ==> size x < size
   y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[size_domain] THEN
  MATCH_MP_TAC CARD_PSUBSET THEN REWRITE_TAC[FINITE_domain; PSUBSET]
    THEN
  ASM_REWRITE_TAC[] THEN UNDISCH_TAC `subspt (x:A spt) y` THEN
  REWRITE_TAC[subspt_def; SUBSET] THEN MESON_TAC[]);;

let domain_list_to_num_set = prove
 (`!xs. x IN domain (list_to_num_set xs) <=> MEM x xs`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[list_to_num_set_def; domain_def; NOT_IN_EMPTY; MEM;
                  domain_insert; IN_INSERT]);;

let domain_list_insert = prove
 (`!xs x t. x IN domain (list_insert xs t) <=> MEM x xs \/ x IN domain
   t`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[list_insert_def; MEM; domain_insert; IN_INSERT] THEN
  MESON_TAC[]);;

let domain_FOLDR_delete = prove
 (`!ls live:A spt.
     domain (ITLIST sptree_delete ls live) = (domain live) DIFF
       (set_of_list ls)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[ITLIST; set_of_list; DIFF_EMPTY; domain_delete] THEN
  SET_TAC[]);;

let lookup_list_to_num_set = prove
 (`!xs. sptree_lookup x (list_to_num_set xs) = if MEM x xs then SOME one
   else NONE`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[list_to_num_set_def; lookup_rwts; MEM; lookup_insert]
    THEN
  MESON_TAC[]);;

let domain_alist_insert = prove
 (`!a b (locs':A spt). (LENGTH a = LENGTH b) ==>
                      (domain (alist_insert a b locs') =
                       domain locs' UNION set_of_list a)`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; NOT_SUC; SUC_INJ; alist_insert_def; set_of_list;
              UNION_EMPTY] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[domain_insert] THEN SET_TAC[]);;

let alist_insert_append = prove
 (`!a1 a2 (s:A spt) b1 b2.
     (LENGTH a1 = LENGTH a2) ==>
     (alist_insert (APPEND a1 b1) (APPEND a2 b2) s =
      alist_insert a1 a2 (alist_insert b1 b2 s))`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; NOT_SUC; SUC_INJ; alist_insert_def; APPEND] THEN
  ASM_SIMP_TAC[alist_insert_def]);;

let wf_LN = prove
 (`sptree_wf (LN:A spt)`,
  REWRITE_TAC[wf_def]);;

let wf_fromList = prove
 (`sptree_wf (sptree_fromList (ls:A list))`,
  REWRITE_TAC[fromList_def] THEN
  SUBGOAL_THEN `!ls:A list i t. sptree_wf t ==>
     sptree_wf (SND (FOLDL (\(i,t) a. (i + 1,sptree_insert i a t)) (i,t)
       ls))`
    (fun th -> MATCH_MP_TAC th THEN REWRITE_TAC[wf_LN]) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[FOLDL] THEN
  ASM_SIMP_TAC[wf_insert]);;

let wf_list_to_num_set = prove
 (`!ls. sptree_wf (list_to_num_set ls)`,
  LIST_INDUCT_TAC THEN ASM_SIMP_TAC[list_to_num_set_def; wf_insert;
    wf_LN]);;

let SPTAUX_LENGTH_MAPi = prove
 (`!(f:num->A->B) l. LENGTH (MAPi f l) = LENGTH l`,
  GEN_REWRITE_TAC I [SWAP_FORALL_THM] THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAPi_DEF; LENGTH]);;

let SPTAUX_EL_MAPi = prove
 (`!l (f:num->A->B) n. n < LENGTH l ==> EL n (MAPi f l) = f n (EL n l)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; CONJUNCT1 LT] THEN
  GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[MAPi_DEF; EL; HD; TL; LT_SUC] THEN
  ASM_SIMP_TAC[o_THM]);;

let insert_swap = prove
 (`!t a (b:A) c d.
     ~(a = c) ==> (sptree_insert a b (sptree_insert c d t) =
       sptree_insert c d (sptree_insert a b t))`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [insert_insert] THEN
  ASM_REWRITE_TAC[]);;

let alist_insert_pull_insert = prove
 (`!xs ys (z:A spt).
     ~MEM x xs ==>
     (alist_insert xs ys (sptree_insert x y z) = sptree_insert x y
       (alist_insert xs ys z))`,
  MATCH_MP_TAC alist_insert_ind THEN
  REWRITE_TAC[alist_insert_def; MEM; DE_MORGAN_THM] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC insert_swap THEN ASM_MESON_TAC[]);;

let alist_insert_REVERSE = prove
 (`!xs ys (s:A spt).
     ALL_DISTINCT xs /\ (LENGTH xs = LENGTH ys) ==>
     (alist_insert (REVERSE xs) (REVERSE ys) s = alist_insert xs ys s)`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; NOT_SUC; SUC_INJ; REVERSE; alist_insert_def;
              ALL_DISTINCT] THEN
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[alist_insert_append; LENGTH_REVERSE; alist_insert_def]
    THEN
  ASM_SIMP_TAC[alist_insert_pull_insert]);;

let insert_unchanged = prove
 (`!t x. (sptree_lookup x t = SOME (y:A)) ==> (sptree_insert x y t =
   t)`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  MATCH_MP_TAC SPTAUX_bit_induction THEN REPEAT STRIP_TAC THEN
  SPTAUX_CASES_TAC `t:A spt` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[lookup_rwts; SPTAUX_lookup_bits;
                              option_DISTINCT; option_INJ]) THEN
  TRY(FIRST_ASSUM CONTR_TAC) THEN ASM_SIMP_TAC[SPTAUX_insert_bits]);;

let SPTAUX_delete_mk_BN = prove
 (`(!t1 t2:A spt. sptree_delete 0 (mk_BN t1 t2) = mk_BN t1 t2) /\
   (!m t1 t2:A spt. sptree_delete (2 * m + 1) (mk_BN t1 t2) = mk_BN t1
     (sptree_delete m t2)) /\
   (!m t1 t2:A spt. sptree_delete (2 * m + 2) (mk_BN t1 t2) = mk_BN
     (sptree_delete m t1) t2)`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  SPTAUX_CASES_TAC `t1:A spt` THEN SPTAUX_CASES_TAC `t2:A spt` THEN
  REWRITE_TAC[mk_BN_def; delete_def; SPTAUX_BIT_RW]);;

let SPTAUX_delete_mk_BS = prove
 (`(!t1 (s:A) t2. sptree_delete 0 (mk_BS t1 s t2) = mk_BN t1 t2) /\
   (!m t1 (s:A) t2.
      sptree_delete (2 * m + 1) (mk_BS t1 s t2) = mk_BS t1 s
        (sptree_delete m t2)) /\
   (!m t1 (s:A) t2.
      sptree_delete (2 * m + 2) (mk_BS t1 s t2) = mk_BS (sptree_delete m
        t1) s t2)`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  SPTAUX_CASES_TAC `t1:A spt` THEN SPTAUX_CASES_TAC `t2:A spt` THEN
  REWRITE_TAC[mk_BS_def; mk_BN_def; delete_def; SPTAUX_BIT_RW]);;

let SPTAUX_BIT_LT = prove
 (`(!p q. 2 * p + 1 < 2 * q + 1 <=> p < q) /\
   (!p q. 2 * p + 2 < 2 * q + 2 <=> p < q)`,
  ARITH_TAC);;

let SPTAUX_delete_delete_same = prove
 (`!f:A spt n. sptree_delete n (sptree_delete n f) = sptree_delete n f`,
  MATCH_MP_TAC spt_INDUCT THEN REPEAT STRIP_TAC THEN
  SPTAUX_BITS_TAC `n:num` THEN
  ASM_REWRITE_TAC[delete_def; SPTAUX_BIT_RW; SPTAUX_delete_mk_BN;
                  SPTAUX_delete_mk_BS]);;

let SPTAUX_delete_delete_lt = prove
 (`!f:A spt n k. n < k ==> sptree_delete n (sptree_delete k f) =
   sptree_delete k (sptree_delete n f)`,
  MATCH_MP_TAC spt_INDUCT THEN REPEAT STRIP_TAC THEN
  SPTAUX_BITS_TAC `n:num` THEN SPTAUX_BITS_TAC `k:num` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPTAUX_BIT_LT; LT_REFL]) THEN
  TRY(FIRST_ASSUM CONTR_TAC) THEN
  ASM_SIMP_TAC[delete_def; SPTAUX_BIT_RW; SPTAUX_delete_mk_BN;
               SPTAUX_delete_mk_BS] THEN
  ASM_MESON_TAC[]);;

let delete_delete = prove
 (`!f:A spt n k.
     sptree_delete n (sptree_delete k f) =
     if n = k then sptree_delete n f else sptree_delete k (sptree_delete
       n f)`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[SPTAUX_delete_delete_same] THEN
  REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
    (ARITH_RULE `n < k \/ k < (n:num) \/ n = k`) THENL
   [MATCH_MP_TAC SPTAUX_delete_delete_lt THEN ASM_REWRITE_TAC[];
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC SPTAUX_delete_delete_lt THEN
    ASM_REWRITE_TAC[];
    ASM_MESON_TAC[]]);;

let size_map = prove
 (`size (sptree_map (f:A->B) t) = size t`,
  REWRITE_TAC[size_domain; domain_map]);;

let SPTAUX_EXISTS_lookup_P = prove
 (`(!P. (?k v. sptree_lookup k (LN:A spt) = SOME v /\ P v) <=> F) /\
   (!P (a:A). (?k v. sptree_lookup k (LS a) = SOME v /\ P v) <=> P a) /\
   (!P t1 t2:A spt. (?k v. sptree_lookup k (BN t1 t2) = SOME v /\ P v)
     <=>
                    (?k v. sptree_lookup k t1 = SOME v /\ P v) \/
                    (?k v. sptree_lookup k t2 = SOME v /\ P v)) /\
   (!P (a:A) t1 t2. (?k v. sptree_lookup k (BS t1 a t2) = SOME v /\ P v)
     <=>
                    P a \/ (?k v. sptree_lookup k t1 = SOME v /\ P v) \/
                    (?k v. sptree_lookup k t2 = SOME v /\ P v))`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [SPTAUX_EXISTS_BITS] THEN
  REWRITE_TAC[lookup_rwts; SPTAUX_lookup_bits; option_DISTINCT;
    option_INJ;
              UNWIND_THM1; UNWIND_THM2] THEN
  MESON_TAC[]);;

let SPTAUX_FORALL_lookup_P = prove
 (`(!P. (!k v. sptree_lookup k (LN:A spt) = SOME v ==> P v) <=> T) /\
   (!P (a:A). (!k v. sptree_lookup k (LS a) = SOME v ==> P v) <=> P a)
     /\
   (!P t1 t2:A spt. (!k v. sptree_lookup k (BN t1 t2) = SOME v ==> P v)
     <=>
                    (!k v. sptree_lookup k t1 = SOME v ==> P v) /\
                    (!k v. sptree_lookup k t2 = SOME v ==> P v)) /\
   (!P (a:A) t1 t2. (!k v. sptree_lookup k (BS t1 a t2) = SOME v ==> P
     v) <=>
                    P a /\ (!k v. sptree_lookup k t1 = SOME v ==> P v)
                      /\
                    (!k v. sptree_lookup k t2 = SOME v ==> P v))`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [SPTAUX_FORALL_BITS] THEN
  REWRITE_TAC[lookup_rwts; SPTAUX_lookup_bits; option_DISTINCT;
    option_INJ;
              FORALL_UNWIND_THM1; FORALL_UNWIND_THM2] THEN
  MESON_TAC[]);;

let adjacent_domain = prove
 (`!tree x y. is_adjacent tree x y ==> x IN domain tree`,
  REWRITE_TAC[is_adjacent_def; domain_lookup] THEN MESON_TAC[]);;

let reachable_domain = prove
 (`!tree x y. is_reachable tree x y ==> (x = y \/ x IN domain tree)`,
  GEN_TAC THEN REWRITE_TAC[is_reachable_def] THEN
  MATCH_MP_TAC RTC_INDUCT_L THEN MESON_TAC[adjacent_domain]);;

let reachable_LHS_NOTIN = prove
 (`!tree n x. is_reachable tree n x /\ ~(n IN domain tree) ==> n = x`,
  REWRITE_TAC[is_reachable_def] THEN ONCE_REWRITE_TAC[RTC_CASES_R] THEN
  MESON_TAC[adjacent_domain]);;

let rtc_is_adjacent = prove
 (`(!k. k IN t ==> !n. (is_adjacent fullTree k n ==> n IN t)) ==>
   !x y. RTC (is_adjacent fullTree) x y ==> x IN t ==> y IN t`,
  DISCH_TAC THEN MATCH_MP_TAC RTC_INDUCT_L THEN ASM_MESON_TAC[]);;

(* What this port cannot take from LightCake's sptree
   yet, with the names of its own that each proof
   uses:

     spt_INDUCT                       cake_type
     spt_CASE                         case_def
     spt_case_eq                      case_eq
     spt_size_def                     size_def
     SPTAUX_TC_TAC                    WF_REL_THMS
     SPTAUX_CASES_TAC                 CASES_ON
     insert_ind                       cake_ind
     isEmpty_union                    spt_CASE
     wf_union                         isEmpty_union spt_CASE
     SPTAUX_optcase_lemma             option_CASE
     wf_inter                         spt_CASE
     SPTAUX_optcase_NONE              option_CASE
     lookup_inter                     SPTAUX_optcase_NONE option_CASE
                                      spt_CASE
     lookup_inter_eq                  SPTAUX_optcase_NONE inter_eq
                                      option_CASE spt_CASE
     lookup_inter_EQ                  lookup_inter option_CASE
     lookup_inter_assoc               lookup_inter option_CASE
     lookup_difference                spt_CASE
     lookup_inter_alt                 lookup_inter option_CASE
     domain_union                     option_CASE
     domain_inter                     lookup_inter option_CASE
     domain_difference                lookup_difference
     domain_fromList                  count_DEF
     lookup_mapi0                     option_CASE
     lookup_mapi                      OPTION_MAP_DEF lookup_mapi0
                                      option_CASE
     SPTAUX_MEM_foldi                 CONS
     MEM_toAList                      SPTAUX_MEM_foldi
     SPTAUX_ALOOKUP_MEM               ALOOKUP_DEF
     SPTAUX_ALOOKUP_FAILS             ALOOKUP_DEF
     ALOOKUP_toAList                  MEM_toAList SPTAUX_ALOOKUP_FAILS
                                      SPTAUX_ALOOKUP_MEM
     insert_union                     spt_CASE
     SPTAUX_LENGTH_foldi              CONS
     LENGTH_toAList                   SPTAUX_LENGTH_foldi
     set_MAP_FST_toAList_domain       MEM_toAList
     ALL_DISTINCT_MAP_FST_toAList     set_MAP_FST_toAList_domain
     SPTAUX_ITLIST_UNCURRY            CONS UNCURRY
     SPTAUX_foldi_FOLDR_toAList_lemma CONS SPTAUX_ITLIST_UNCURRY UNCURRY
     foldi_FOLDR_toAList              SPTAUX_foldi_FOLDR_toAList_lemma
                                      UNCURRY
     inter_eq                         wf_inter
     union_mk_wf                      wf_union
     inter_mk_wf                      lookup_inter wf_inter
     union_LN                         spt_CASE
     inter_LN                         spt_CASE
     union_assoc                      spt_CASE
     inter_assoc                      inter_eq lookup_inter option_CASE
     lookup_fromAList                 ALOOKUP_DEF ALOOKUP_THM
     lookup_fromAList_toAList         ALOOKUP_toAList lookup_fromAList
     fromAList_toAList                lookup_fromAList_toAList
     union_insert_LN                  insert_union
     fromAList_append                 insert_union union_LN union_assoc
                                      union_insert_LN
     lookup_map                       OPTION_MAP_DEF
     subspt_union                     option_CASE
     subspt_FOLDL_union               subspt_union
     domain_mapi                      OPTION_MAP_DEF lookup_mapi
     lookup_FOLDL_union               OPTION_CHOICE_DEF option_CASE
     map_union                        spt_CASE
     lookup_filter_v                  option_CASE
     SPTAUX_ALOOKUP_MAP_lemma         ALOOKUP_DEF OPTION_MAP_DEF
     MAP_foldi                        CONS
     mapi_Alist                       ALOOKUP_toAList
                                      SPTAUX_ALOOKUP_MAP_lemma
                                      lookup_fromAList lookup_mapi
     union_num_set_sym                spt_CASE
     union_disjoint_sym               option_CASE wf_union
     wf_difference                    spt_CASE
     size_diff_less                   lookup_difference
     inter_eq_LN                      domain_inter wf_inter
     list_to_num_set_append           insert_union union_LN union_assoc
                                      union_insert_LN
     map_map_K                        K_THM
     lookup_map_K                     K_THM OPTION_MAP_DEF lookup_map
     alist_insert_ind                 CONS
     lookup_alist_insert              ALOOKUP_DEF option_CASE
     size_list_to_num_set             nub_DEF
     mapi_fromList                    OPTION_MAP_DEF lookup_mapi
     SPTAUX_DROP_0                    DROP_DEF
     SPTAUX_TAKE_DROP_UPDATE          DROP_DEF SPTAUX_DROP_0 TAKE_DEF
     insert_fromList_IN_domain        SPTAUX_TAKE_DROP_UPDATE
     list_size_APPEND                 list_size
     size_mapi                        domain_mapi
     SUM_MAP_same_LE                  SUM
     SUM_MAP_same_LESS                SUM SUM_MAP_same_LE
     size_fromList                    count_DEF domain_fromList
     SPTAUX_spts_to_alist_aux_thm     CONS list_CASE option_CASE
                                      pair_CASE
     SPTAUX_SUM_add_pause             SUM list_CASE pair_CASE
                                      spt_size_def
     SPTAUX_SUM_MAP_APPEND            SUM
     SPTAUX_SUM_MAP_REVERSE           SPTAUX_SUM_MAP_APPEND SUM
     SPTAUX_spt_size_left_right       K_THM spt_size_def
     spts_to_alist_aux_size           RVEQ_TAC SPTAUX_SUM_MAP_APPEND
                                      SPTAUX_SUM_MAP_REVERSE
                                      SPTAUX_SUM_add_pause
                                      SPTAUX_spt_size_left_right
                                      SPTAUX_spts_to_alist_aux_thm SUM
                                      spt_size_def
     spts_to_alist_def                pair_CASE
     SPTAUX_LENGTH_COUNT_LIST         COUNT_LIST_DEF
     SPTAUX_ALOOKUP_ZIP_MAP_SUC       ALOOKUP_DEF
     SPTAUX_ALOOKUP_ZIP_COUNT_LIST    ALOOKUP_DEF COUNT_LIST_DEF
                                      SPTAUX_ALOOKUP_ZIP_MAP_SUC
                                      SPTAUX_LENGTH_COUNT_LIST
     fromList_fromAList               SPTAUX_ALOOKUP_ZIP_COUNT_LIST
                                      lookup_fromAList
     domain_spt_fold_union            domain_union
     SPTAUX_closure_spt_size          domain_spt_fold_union domain_union
                                      lookup_inter_EQ size_diff_less
     closure_spt_ind                  RVEQ_TAC SPTAUX_closure_spt_size
     num_set_tree_union_empty         spt_CASE
     wf_num_set_tree_union            num_set_tree_union_empty spt_CASE
     domain_num_set_tree_union        spt_CASE
     num_set_tree_union_sym           spt_CASE union_num_set_sym
     lookup_num_set_tree_union        SPTAUX_optcase_lemma option_CASE
                                      spt_CASE
     wf_spt_fold_union                wf_union
     wf_closure_spt                   lookup_inter_EQ wf_spt_fold_union
                                      wf_union
     is_adjacent_num_set_tree_union   lookup_num_set_tree_union
                                      option_CASE
     is_reachable_num_set_tree_union  is_adjacent_num_set_tree_union
     closure_spt_lemma                domain_spt_fold_union domain_union
                                      lookup_inter_alt
     closure_spt_thm                  closure_spt_lemma
     _                                cake_add_simps domain_inter
                                      domain_mapi domain_union inter_LN
                                      inter_eq inter_mk_wf isEmpty_union
                                      map_map_K size_fromList size_mapi
                                      subspt_union union_LN union_mk_wf
                                      wf_inter

*)
