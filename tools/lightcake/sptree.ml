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

let wf_insert = prove
 (`!k (a:A) t. sptree_wf t ==> sptree_wf (sptree_insert k a t)`,
  MATCH_MP_TAC SPTAUX_bit_induction THEN REPEAT STRIP_TAC THEN
  SPTAUX_CASES_TAC `t:A spt` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[wf_def]) THEN
  ASM_SIMP_TAC[SPTAUX_insert_bits; wf_def; insert_notEmpty]);;

let wf_delete = prove
 (`!t k. sptree_wf (t:A spt) ==> sptree_wf (sptree_delete k t)`,
  MATCH_MP_TAC spt_INDUCT THEN REWRITE_TAC[wf_def; delete_def] THEN
  REPEAT STRIP_TAC THEN REPEAT COND_CASES_TAC THEN
  ASM_SIMP_TAC[wf_def; mk_BN_thm; mk_BS_thm] THEN
  REPEAT COND_CASES_TAC THEN ASM_SIMP_TAC[wf_def]);;

(* HOL4 proves lookup_insert1 first; here it follows from lookup_insert
  *)

let SPTAUX_optcase_lemma = prove
 (`!opt. option_CASE opt NONE (\v:A. SOME v) = opt`,
  GEN_TAC THEN SPTAUX_CASES_TAC `opt:A option` THEN
    REWRITE_TAC[option_CASE]);;

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

let SPTAUX_optcase_NONE = prove
 (`!x:A option. option_CASE x NONE (\v. NONE:B option) = NONE`,
  GEN_TAC THEN SPTAUX_CASES_TAC `x:A option` THEN
    REWRITE_TAC[option_CASE]);;

let SPTAUX_lookup_cond = prove
 (`!k c (t1:A spt) t2. sptree_lookup k (if c then t1 else t2) =
                       if c then sptree_lookup k t1 else sptree_lookup k
                         t2`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[]);;

let lookup_inter_EQ = prove
 (`((sptree_lookup x (inter t1 t2) = SOME (y:A)) <=>
      (sptree_lookup x t1 = SOME y) /\ ~(sptree_lookup x (t2:B spt) =
        NONE)) /\
   ((sptree_lookup x (inter t1 t2) = NONE) <=>
      (sptree_lookup x t1 = NONE) \/ (sptree_lookup x t2 = NONE))`,
  REWRITE_TAC[lookup_inter] THEN
  SPTAUX_CASES_TAC `sptree_lookup x (t1:A spt)` THEN
  SPTAUX_CASES_TAC `sptree_lookup x (t2:B spt)` THEN
  REWRITE_TAC[option_CASE; option_DISTINCT; option_INJ]);;

let lookup_inter_assoc = prove
 (`sptree_lookup x (inter t1 (inter t2 t3)) =
   sptree_lookup x (inter (inter (t1:A spt) (t2:B spt)) (t3:C spt))`,
  REWRITE_TAC[lookup_inter] THEN
  SPTAUX_CASES_TAC `sptree_lookup x (t1:A spt)` THEN
  SPTAUX_CASES_TAC `sptree_lookup x (t2:B spt)` THEN
  SPTAUX_CASES_TAC `sptree_lookup x (t3:C spt)` THEN
  REWRITE_TAC[option_CASE]);;

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

let lookup_inter_alt = prove
 (`sptree_lookup x (inter t1 t2) =
   if x IN domain (t2:B spt) then sptree_lookup x (t1:A spt) else NONE`,
  REWRITE_TAC[lookup_inter; domain_lookup] THEN
  SPTAUX_CASES_TAC `sptree_lookup x (t2:B spt)` THEN
  SPTAUX_CASES_TAC `sptree_lookup x (t1:A spt)` THEN
  REWRITE_TAC[option_CASE; option_DISTINCT; option_INJ] THEN
    MESON_TAC[]);;

let domain_union = prove
 (`domain (sptree_union t1 t2) = domain t1 UNION domain (t2:A spt)`,
  REWRITE_TAC[EXTENSION; domain_lookup; lookup_union; IN_UNION] THEN
  X_GEN_TAC `k:num` THEN SPTAUX_CASES_TAC `sptree_lookup k (t1:A spt)`
    THEN
  REWRITE_TAC[option_CASE; option_DISTINCT; option_INJ] THEN
    MESON_TAC[]);;

let domain_inter = prove
 (`domain (inter t1 t2) = domain (t1:A spt) INTER domain (t2:B spt)`,
  REWRITE_TAC[EXTENSION; domain_lookup; lookup_inter; IN_INTER] THEN
  X_GEN_TAC `k:num` THEN SPTAUX_CASES_TAC `sptree_lookup k (t1:A spt)`
    THEN
  SPTAUX_CASES_TAC `sptree_lookup k (t2:B spt)` THEN
  REWRITE_TAC[option_CASE; option_DISTINCT; option_INJ] THEN
    MESON_TAC[]);;

let domain_insert = prove
 (`domain (sptree_insert k (v:A) t) = k INSERT domain t`,
  REWRITE_TAC[EXTENSION; domain_lookup; lookup_insert; IN_INSERT] THEN
  MESON_TAC[]);;

let domain_difference = prove
 (`!t1 t2. domain (difference t1 t2) =
           domain (t1:A spt) DIFF domain (t2:B spt)`,
  REWRITE_TAC[EXTENSION; domain_lookup; lookup_difference; IN_DIFF] THEN
  REPEAT GEN_TAC THEN SPTAUX_CASES_TAC `sptree_lookup x (t2:B spt)` THEN
  REWRITE_TAC[option_DISTINCT; option_INJ] THEN MESON_TAC[]);;

let domain_sing = prove
 (`domain (sptree_insert k (v:A) LN) = {k}`,
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

let domain_delete = prove
 (`domain (sptree_delete k (t:A spt)) = domain t DELETE k`,
  REWRITE_TAC[EXTENSION; domain_lookup; lookup_delete; IN_DELETE] THEN
  MESON_TAC[option_DISTINCT]);;

(*
  ------------------------------------------------------------------------- *)
(* foldi, spt_acc, sptree_mapi
             *)
(*
  ------------------------------------------------------------------------- *)

let SPTAUX_lrnext_bits = prove
 (`lrnext 0 = 1 /\ lrnext 1 = 2 /\ lrnext 2 = 2 /\
   (!m. lrnext (2 * m + 1) = 2 * lrnext m) /\
   (!m. lrnext (2 * m + 2) = 2 * lrnext m)`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [lrnext_def] THEN
  REWRITE_TAC[SPTAUX_BIT_RW] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ONCE_REWRITE_TAC[lrnext_def] THEN CONV_TAC NUM_REDUCE_CONV);;

(* HOL4: lrlemma1, lrlemma2 (local) *)

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

let domain_foldi = prove
 (`domain t = foldi (\k (v:A) a. k INSERT a) 0 {} t`,
  REWRITE_TAC[set_foldi_keys; UNION_EMPTY; SPTAUX_lrnext_bits;
    ADD_CLAUSES;
              MULT_CLAUSES; IMAGE_ID]);;

let mapi0_def = cake_def
  `(mapi0 (f:num->A->B) i LN = LN) /\
   (mapi0 f i (LS a) = LS (f i a)) /\
   (mapi0 f i (BN t1 t2) =
      let inc = lrnext i in
      mk_BN (mapi0 f (i + 2 * inc) t1) (mapi0 f (i + inc) t2)) /\
   (mapi0 f i (BS t1 a t2) =
      let inc = lrnext i in
      mk_BS (mapi0 f (i + 2 * inc) t1) (f i a) (mapi0 f (i + inc)
        t2))`;;

let mapi_def = new_definition
  `sptree_mapi (f:num->A->B) pt = mapi0 f 0 pt`;;

let SPTAUX_ACC_RW = prove
 (`(!c i. c * 0 + i = i) /\
   (!c i m. c * (2 * m + 1) + i = (2 * c) * m + (i + c)) /\
   (!c i m. c * (2 * m + 2) + i = (2 * c) * m + (i + 2 * c))`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN CONV_TAC NUM_RING);;

let lookup_mapi0 = prove
 (`!pt:A spt i k.
     sptree_lookup k (mapi0 (f:num->A->B) i pt) =
     option_CASE (sptree_lookup k pt) NONE (\v. SOME (f (spt_acc i k)
       v))`,
  MATCH_MP_TAC spt_INDUCT THEN REPEAT STRIP_TAC THEN
  SPTAUX_BITS_TAC `k:num` THEN
  ASM_REWRITE_TAC[mapi0_def; LET_DEF; LET_END_DEF; lookup_rwts;
                  SPTAUX_lookup_bits; SPTAUX_lookup_mk_BN;
                    SPTAUX_lookup_mk_BS;
                  option_CASE; spt_acc_eqn; SPTAUX_lrlemma1;
                    SPTAUX_lrlemma2;
                  SPTAUX_ACC_RW]);;

let MEM_toAList = prove
 (`!t:A spt k v. MEM (k,v) (toAList t) <=> (sptree_lookup k t = SOME
   v)`,
  REWRITE_TAC[toAList_def; SPTAUX_MEM_foldi; MEM; SPTAUX_lrnext_bits;
              ADD_CLAUSES; MULT_CLAUSES; UNWIND_THM1; UNWIND_THM2]);;

(* alist lemmas (alist unit), proved here for local use *)

let ALOOKUP_toAList = prove
 (`!t:A spt x. ALOOKUP (toAList t) x = sptree_lookup x t`,
  REPEAT GEN_TAC THEN SPTAUX_CASES_TAC `sptree_lookup x (t:A spt)` THENL
   [ASM_REWRITE_TAC[SPTAUX_ALOOKUP_FAILS; MEM_toAList; option_DISTINCT];
    ALL_TAC] THEN
  SPTAUX_CASES_TAC `ALOOKUP (toAList (t:A spt)) x` THENL
   [ASM_MESON_TAC[SPTAUX_ALOOKUP_FAILS; MEM_toAList];
    ASM_MESON_TAC[SPTAUX_ALOOKUP_MEM; MEM_toAList]]);;

let LENGTH_toAList = prove
 (`LENGTH (toAList t) = size (t:A spt)`,
  REWRITE_TAC[toAList_def; SPTAUX_LENGTH_foldi; LENGTH; ADD_CLAUSES]);;

(* list lemma (list unit), proved here for local use *)

let SPTAUX_ALL_DISTINCT_CARD = prove
 (`!l:A list. ALL_DISTINCT l <=> CARD (set_of_list l) = LENGTH l`,
  LIST_INDUCT_TAC THEN
  ASM_SIMP_TAC[ALL_DISTINCT; set_of_list; LENGTH; CARD_CLAUSES;
               FINITE_SET_OF_LIST; IN_SET_OF_LIST] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[SUC_INJ] THEN
  MP_TAC(ISPEC `t:A list` CARD_SET_OF_LIST_LE) THEN ARITH_TAC);;

let set_MAP_FST_toAList_domain = prove
 (`set_of_list (MAP FST (toAList t)) = domain (t:A spt)`,
  REWRITE_TAC[EXTENSION; IN_SET_OF_LIST; MEM_MAP; EXISTS_PAIR_THM;
              MEM_toAList; domain_lookup] THEN
  MESON_TAC[FST]);;

let ALL_DISTINCT_MAP_FST_toAList = prove
 (`!t:A spt. ALL_DISTINCT (MAP FST (toAList t))`,
  REWRITE_TAC[SPTAUX_ALL_DISTINCT_CARD; set_MAP_FST_toAList_domain;
              LENGTH_MAP; LENGTH_toAList; size_domain]);;

(* HOL4: foldi_FOLDR_toAList_lemma (local) *)

let SPTAUX_toListA_APPEND = prove
 (`!t:A spt acc acc'.
     toListA (APPEND acc acc') t = APPEND (toListA acc t) acc'`,
  MATCH_MP_TAC spt_INDUCT THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[toListA_def; APPEND] THEN
  ASM_REWRITE_TAC[GSYM(CONJUNCT2 APPEND)]);;

let toListA_append = prove
 (`!t:A spt acc. toListA acc t = APPEND (toListA [] t) acc`,
  REWRITE_TAC[GSYM SPTAUX_toListA_APPEND; APPEND]);;

let isEmpty_toListA = prove
 (`!t:A spt acc. sptree_wf t ==> ((t = LN) <=> (toListA acc t = acc))`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[toListA_def]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o AP_TERM `LENGTH:A list->num`) THEN
  REWRITE_TAC[SPTAUX_LENGTH_toListA; ARITH_RULE `a + b = b <=> a = 0`]
    THEN
  ASM_SIMP_TAC[size_zero_empty; domain_empty]);;

let toList_def = new_definition
  `sptree_toList (m:A spt) = toListA [] m`;;

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

(* HOL4: MEM_toListA (local) *)

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

(*
  ------------------------------------------------------------------------- *)
(* Extensionality
      *)
(*
  ------------------------------------------------------------------------- *)

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

(* the theorem inter_eq (the constant inter_eq is inter_eq_def) *)

let inter_eq = prove
 (`!t1:A spt t2:B spt t3 t4:C spt.
     (inter t1 t2 = inter t3 t4) <=>
     !x. sptree_lookup x (inter t1 t2) = sptree_lookup x (inter t3 t4)`,
  MESON_TAC[spt_eq_thm; wf_inter]);;

let union_mk_wf = prove
 (`!t1 t2:A spt. sptree_union (mk_wf t1) (mk_wf t2) = mk_wf
   (sptree_union t1 t2)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `sptree_union (mk_wf t1) (mk_wf t2) =
                mk_wf (sptree_union (mk_wf t1) (mk_wf (t2:A spt)))`
                  SUBST1_TAC THENL
   [MESON_TAC[wf_union; wf_mk_wf; wf_mk_id]; ALL_TAC] THEN
  REWRITE_TAC[mk_wf_eq; lookup_union; lookup_mk_wf]);;

let inter_mk_wf = prove
 (`!t1:A spt t2:B spt. inter (mk_wf t1) (mk_wf t2) = mk_wf (inter t1
   t2)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `inter (mk_wf t1) (mk_wf t2) =
                mk_wf (inter (mk_wf (t1:A spt)) (mk_wf (t2:B spt)))`
    SUBST1_TAC THENL
   [MESON_TAC[wf_inter; wf_mk_wf; wf_mk_id]; ALL_TAC] THEN
  REWRITE_TAC[mk_wf_eq; lookup_inter; lookup_mk_wf]);;

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

let lookup_fromAList_toAList = prove
 (`!t:A spt x. sptree_lookup x (fromAList (toAList t)) = sptree_lookup x
   t`,
  REWRITE_TAC[lookup_fromAList; ALOOKUP_toAList]);;

let wf_fromAList = prove
 (`!ls:(num#A)list. sptree_wf (fromAList ls)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[fromAList_def; wf_def] THEN
  SPTAUX_CASES_TAC `h:num#A` THEN
  ASM_SIMP_TAC[fromAList_def; wf_insert]);;

let fromAList_toAList = prove
 (`!t:A spt. sptree_wf t ==> (fromAList (toAList t) = t)`,
  MESON_TAC[wf_fromAList; lookup_fromAList_toAList; spt_eq_thm]);;

let union_insert_LN = prove
 (`!x (y:A) t2. sptree_union (sptree_insert x y LN) t2 = sptree_insert x
   y t2`,
  REWRITE_TAC[GSYM insert_union]);;

let fromAList_append = prove
 (`!l1 l2:(num#A)list.
     fromAList (APPEND l1 l2) = sptree_union (fromAList l1) (fromAList
       l2)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[APPEND; fromAList_def; union_LN] THEN
  SPTAUX_CASES_TAC `h:num#A` THEN ASM_REWRITE_TAC[fromAList_def] THEN
  GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [insert_union] THEN
  ONCE_REWRITE_TAC[union_assoc] THEN REWRITE_TAC[union_insert_LN]);;

(*
  ------------------------------------------------------------------------- *)
(* sptree_map
             *)
(*
  ------------------------------------------------------------------------- *)

let map_def = cake_def
  `(sptree_map (f:A->B) LN = LN) /\
   (sptree_map f (LS a) = LS (f a)) /\
   (sptree_map f (BN t1 t2) = BN (sptree_map f t1) (sptree_map f t2)) /\
   (sptree_map f (BS t1 a t2) = BS (sptree_map f t1) (f a) (sptree_map f
     t2))`;;

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

(*
  ------------------------------------------------------------------------- *)
(* The sub-sptree_map relation, a partial order.
             *)
(*
  ------------------------------------------------------------------------- *)

let spt_left_def = cake_def
  `(spt_left (LN:A spt) = LN) /\
   (spt_left (LS (x:A)) = LN) /\
   (spt_left (BN t1 t2) = t1) /\
   (spt_left (BS t1 x t2) = t1)`;;

let spt_right_def = cake_def
  `(spt_right (LN:A spt) = LN) /\
   (spt_right (LS (x:A)) = LN) /\
   (spt_right (BN t1 t2) = t2) /\
   (spt_right (BS t1 x t2) = t2)`;;

let spt_center_def = cake_def
  `(spt_center (LS (x:A)) = SOME x) /\
   (spt_center (BS t1 x t2) = SOME x) /\
   (spt_center LN = NONE) /\
   (spt_center (BN t1 t2) = NONE)`;;

(* HOL4: lookup_0_spt_center, lookup_spt_right, lookup_spt_left (proved
     *)
(* later in the HOL4 script); SPTAUX_lookup_gen_bits in key form 2m+c
    *)

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

(* HOL4: subspt_eq is the definition *)

let subspt_eq = cake_def
  `(subspt (LN:A spt) t <=> T) /\
   (subspt (LS x) t <=> (spt_center t = SOME x)) /\
   (subspt (BN t1 t2) t <=>
      subspt t1 (spt_left t) /\ subspt t2 (spt_right t)) /\
   (subspt (BS t1 x t2) t <=>
      (spt_center t = SOME x) /\
      subspt t1 (spt_left t) /\ subspt t2 (spt_right t))`;;

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

let subspt_union = prove
 (`subspt s (sptree_union s (t:A spt))`,
  REWRITE_TAC[subspt_lookup; lookup_union] THEN REPEAT GEN_TAC THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[option_CASE]);;

let subspt_FOLDL_union = prove
 (`!ls t:A spt. subspt t (FOLDL sptree_union t ls)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[FOLDL; subspt_refl] THEN
  ASM_MESON_TAC[subspt_union; subspt_trans]);;

let domain_eq = prove
 (`!t1:A spt t2:B spt.
     (domain t1 = domain t2) <=>
     !k. (sptree_lookup k t1 = NONE) <=> (sptree_lookup k t2 = NONE)`,
  REWRITE_TAC[EXTENSION; lookup_NONE_domain] THEN MESON_TAC[]);;

(*
  ------------------------------------------------------------------------- *)
(* filter_v, sptree_mapi, and further lemmas
             *)
(*
  ------------------------------------------------------------------------- *)

(* filter values stored in sptree *)

let filter_v_def = cake_def
  `(filter_v (f:A->bool) LN = LN) /\
   (filter_v f (LS x) = if f x then LS x else LN) /\
   (filter_v f (BN l r) = mk_BN (filter_v f l) (filter_v f r)) /\
   (filter_v f (BS l x r) =
      if f x then mk_BS (filter_v f l) x (filter_v f r)
      else mk_BN (filter_v f l) (filter_v f r))`;;

let lookup_filter_v = prove
 (`!k t:A spt f.
     sptree_lookup k (filter_v f t) =
     option_CASE (sptree_lookup k t) NONE (\v. if f v then SOME v else
       NONE)`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  MATCH_MP_TAC spt_INDUCT THEN REPEAT STRIP_TAC THEN
  SPTAUX_BITS_TAC `k:num` THEN
  REWRITE_TAC[filter_v_def] THEN
  REPEAT COND_CASES_TAC THEN
  ASM_REWRITE_TAC[lookup_rwts; SPTAUX_lookup_bits; SPTAUX_lookup_mk_BN;
                  SPTAUX_lookup_mk_BS; option_CASE]);;

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

(* HOL4: ALOOKUP_MAP_lemma (local) *)

let mapi_Alist = prove
 (`sptree_mapi (f:num->A->B) pt =
   fromAList (MAP (\kv. (FST kv,f (FST kv) (SND kv))) (toAList pt))`,
  SIMP_TAC[spt_eq_thm; wf_mapi; wf_fromAList] THEN
  REWRITE_TAC[lookup_fromAList; lookup_mapi; SPTAUX_ALOOKUP_MAP_lemma;
              ALOOKUP_toAList] THEN
  GEN_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[ETA_AX]);;

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

let union_disjoint_sym = prove
 (`!t1 t2:A spt.
     sptree_wf t1 /\ sptree_wf t2 /\ DISJOINT (domain t1) (domain t2)
       ==>
     sptree_union t1 t2 = sptree_union t2 t1`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[spt_eq_thm; wf_union; lookup_union]
    THEN
  X_GEN_TAC `n:num` THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o REWRITE_RULE[DISJOINT;
    EXTENSION;
    IN_INTER; NOT_IN_EMPTY; domain_lookup]) THEN
  SPTAUX_CASES_TAC `sptree_lookup n (t1:A spt)` THEN
  SPTAUX_CASES_TAC `sptree_lookup n (t2:A spt)` THEN
  REWRITE_TAC[option_CASE; option_DISTINCT; option_INJ] THEN
    MESON_TAC[]);;

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

let spt_fold_def = cake_def
  `(spt_fold (f:A->B->B) acc LN = acc) /\
   (spt_fold f acc (LS a) = f a acc) /\
   (spt_fold f acc (BN t1 t2) = spt_fold f (spt_fold f acc t1) t2) /\
   (spt_fold f acc (BS t1 a t2) = spt_fold f (f a (spt_fold f acc t1))
     t2)`;;

let IMP_size_LESS_size = prove
 (`!x y:A spt. subspt x y /\ ~(domain x = domain y) ==> size x < size
   y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[size_domain] THEN
  MATCH_MP_TAC CARD_PSUBSET THEN REWRITE_TAC[FINITE_domain; PSUBSET]
    THEN
  ASM_REWRITE_TAC[] THEN UNDISCH_TAC `subspt (x:A spt) y` THEN
  REWRITE_TAC[subspt_def; SUBSET] THEN MESON_TAC[]);;

let size_diff_less = prove
 (`!x:A spt y:B spt z:C spt t.
     domain z SUBSET domain y /\ t IN domain y /\
     ~(t IN domain z) /\ t IN domain x ==>
     size (difference x y) < size (difference x z)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC IMP_size_LESS_size THEN CONJ_TAC
    THENL
   [REWRITE_TAC[subspt_lookup; lookup_difference] THEN REPEAT GEN_TAC
     THEN
    COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
    SUBGOAL_THEN `sptree_lookup x' (z:C spt) = NONE` (fun th ->
      REWRITE_TAC[th]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[lookup_NONE_domain]) THEN
    REWRITE_TAC[lookup_NONE_domain] THEN ASM SET_TAC[];
    REWRITE_TAC[domain_difference; EXTENSION; IN_DIFF] THEN
    DISCH_THEN(MP_TAC o SPEC `t:num`) THEN ASM_REWRITE_TAC[]]);;

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

let list_to_num_set_append = prove
 (`!l1 l2. list_to_num_set (APPEND l1 l2) =
           sptree_union (list_to_num_set l1) (list_to_num_set l2)`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[APPEND; list_to_num_set_def;
    union_LN] THEN
  GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [insert_union] THEN
  ONCE_REWRITE_TAC[union_assoc] THEN REWRITE_TAC[union_insert_LN]);;

let domain_alist_insert = prove
 (`!a b (locs:A spt). (LENGTH a = LENGTH b) ==>
                      (domain (alist_insert a b locs) =
                       domain locs UNION set_of_list a)`,
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

let insert_fromList_IN_domain = prove
 (`!ls k (v:A).
     k < LENGTH ls ==>
     sptree_insert k v (sptree_fromList ls) =
     sptree_fromList (APPEND (APPEND (TAKE k ls) [v]) (DROP (SUC k)
       ls))`,
  REPEAT STRIP_TAC THEN
  SIMP_TAC[spt_eq_thm; wf_insert; wf_fromList] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o SPEC `v:A` o MATCH_MP
    SPTAUX_TAKE_DROP_UPDATE) THEN
  ASM_REWRITE_TAC[lookup_insert; lookup_fromList] THEN
  X_GEN_TAC `n:num` THEN ASM_CASES_TAC `n:num = k` THEN
    ASM_SIMP_TAC[]);;

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

(* HOL4: delete_mk_BN, delete_mk_BS (local), in key form *)

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

let list_size_APPEND = prove
 (`list_size (f:A->num) (APPEND xs ys) = list_size f xs + list_size f
   ys`,
  SPEC_TAC(`xs:A list`,`xs:A list`) THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[APPEND; list_size] THEN ARITH_TAC);;

let size_map = prove
 (`size (sptree_map (f:A->B) t) = size t`,
  REWRITE_TAC[size_domain; domain_map]);;

let size_mapi = prove
 (`size (sptree_mapi (f:num->A->B) t) = size t`,
  REWRITE_TAC[size_domain; domain_mapi]);;

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

let domain_spt_fold_union = prove
 (`!tree:(A spt)spt y.
     domain (spt_fold sptree_union y tree) =
     domain y UNION
     {n | ?k aSet. sptree_lookup k tree = SOME aSet /\ n IN domain
       aSet}`,
  MATCH_MP_TAC spt_INDUCT THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[spt_fold_def; domain_union] THEN
  REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM] THEN X_GEN_TAC `n:num`
    THEN
  REWRITE_TAC[SPTAUX_EXISTS_lookup_P] THEN MESON_TAC[]);;

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

let wf_spt_fold_union = prove
 (`!tree:(A spt)spt y.
     (!n x. (sptree_lookup n tree = SOME x) ==> sptree_wf x) /\
       sptree_wf y
     ==> sptree_wf (spt_fold sptree_union y tree)`,
  MATCH_MP_TAC spt_INDUCT THEN
  REWRITE_TAC[spt_fold_def; SPTAUX_FORALL_lookup_P] THEN
  REPEAT STRIP_TAC THEN ASM_MESON_TAC[wf_union]);;

let wf_closure_spt = prove
 (`!reachable tree.
     sptree_wf reachable /\ (!n x. sptree_lookup n tree = SOME x ==>
       sptree_wf x)
     ==> sptree_wf (closure_spt reachable tree)`,
  MATCH_MP_TAC closure_spt_ind THEN REPEAT GEN_TAC THEN
  DISCH_TAC THEN STRIP_TAC THEN ONCE_REWRITE_TAC[closure_spt_def] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
    [`inter (tree:(1 spt)spt) (reachable:1 spt)`;
     `spt_fold sptree_union LN (inter (tree:(1 spt)spt) (reachable:1
       spt))`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC wf_union THEN ASM_REWRITE_TAC[]
    THEN
  MATCH_MP_TAC wf_spt_fold_union THEN REWRITE_TAC[wf_LN;
    lookup_inter_EQ] THEN
  ASM_MESON_TAC[]);;

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

let is_adjacent_num_set_tree_union = prove
 (`!t1 t2 n m. is_adjacent t1 n m ==> is_adjacent (num_set_tree_union t1
   t2) n m`,
  REWRITE_TAC[is_adjacent_def; lookup_num_set_tree_union] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[option_CASE] THEN
  SPTAUX_CASES_TAC `sptree_lookup n (t2:(1 spt)spt)` THEN
  REWRITE_TAC[option_CASE; option_INJ; UNWIND_THM1] THEN
  ASM_REWRITE_TAC[lookup_union; option_CASE]);;

let is_reachable_num_set_tree_union = prove
 (`!t1 t2 n m. is_reachable t1 n m
               ==> is_reachable (num_set_tree_union t1 t2) n m`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[is_reachable_def] THEN
  MATCH_MP_TAC RTC_MONO THEN
    REWRITE_TAC[is_adjacent_num_set_tree_union]);;

let closure_spt_lemma = prove
 (`!reachable tree closure (roots:num->bool).
     closure_spt reachable tree = closure /\
     roots SUBSET domain reachable /\
     (!k. k IN domain reachable ==> ?n. n IN roots /\ is_reachable tree
       n k)
     ==> domain closure = {a | ?n. n IN roots /\ is_reachable tree n
       a}`,
  MATCH_MP_TAC closure_spt_ind THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[closure_spt_def] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN COND_CASES_TAC THENL
   [STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `a:num` THEN
    EQ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `!x y. RTC (is_adjacent tree) x y ==> x IN domain (reachable:1 spt)
            ==> y IN domain reachable`
     (fun th -> ASM_MESON_TAC[th; is_reachable_def; SUBSET]) THEN
    MATCH_MP_TAC rtc_is_adjacent THEN
    UNDISCH_TAC
     `subspt (spt_fold sptree_union LN (inter (tree:(1 spt)spt)
       (reachable:1 spt)))
             reachable` THEN
    REWRITE_TAC[subspt_domain; SUBSET; domain_spt_fold_union;
      domain_def;
                IN_UNION; NOT_IN_EMPTY; IN_ELIM_THM; is_adjacent_def;
                lookup_inter_alt] THEN
    REWRITE_TAC[domain_lookup] THEN MESON_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
    [`inter (tree:(1 spt)spt) (reachable:1 spt)`;
     `spt_fold sptree_union LN (inter (tree:(1 spt)spt) (reachable:1
       spt))`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[domain_union] THEN CONJ_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `k:num` THEN REWRITE_TAC[IN_UNION] THEN
  STRIP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC
   `k IN domain (spt_fold sptree_union LN (inter (tree:(1 spt)spt)
     (reachable:1 spt)))` THEN
  REWRITE_TAC[domain_spt_fold_union; domain_def; IN_UNION; NOT_IN_EMPTY;
              IN_ELIM_THM; lookup_inter_alt] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `k' IN domain (reachable:1 spt)` ASSUME_TAC THENL
   [ASM_MESON_TAC[option_DISTINCT]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k':num` o check (is_forall o concl)) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `n:num` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[is_reachable_def] THEN
  MATCH_MP_TAC RTC_TRANS_L THEN EXISTS_TAC `k':num` THEN
  ASM_REWRITE_TAC[GSYM is_reachable_def; is_adjacent_def] THEN
  EXISTS_TAC `aSet:1 spt` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[domain_lookup; EXISTS_ONE_THM]) THEN
  ASM_MESON_TAC[option_DISTINCT]);;

(* What this port cannot take from LightCake's sptree yet, with the names of its own that each proof uses:

     SPTAUX_DIV2_LT                   SPTAUX_TC_TAC WF_REL_THMS
     SPTAUX_BIT_RW                    SPTAUX_TC_TAC measure
     SPTAUX_lookup_bits               SPTAUX_TC_TAC measure
     SPTAUX_insert_bits               sptree_size_def
     insert_notEmpty                  spt_distinct
     mk_BN_thm                        spt_distinct
     mk_BS_thm                        spt_distinct
     lookup_insert1                   spt_CASE
     isEmpty_union                    spt_CASE spt_distinct
     wf_union                         spt_CASE
     SPTAUX_wf_mk_BN                  spt_distinct
     SPTAUX_wf_mk_BS                  spt_distinct
     wf_inter                         spt_CASE
     lookup_inter                     spt_CASE
     lookup_inter_eq                  spt_CASE
     lookup_difference                LOG WF_REL_THMS measure spt_CASE
     SPTAUX_domain_bits               CONS domain_list_def
     set_domain_list                  domain_list_def
     size_insert                      sptree_size_def
     domain_fromList                  count_DEF
     size_domain                      sptree_size_def
     SPTAUX_lrnext_pos                SPTAUX_TC_TAC measure spt_acc_def
     spt_acc_thm                      spt_acc_def
     spt_acc_eqn                      spt_acc_def
     spt_acc_0                        SPTAUX_foldi_thm
     set_foldi_keys                   SPTAUX_foldi_thm
     lookup_mapi                      CONS OPTION_MAP_DEF
     SPTAUX_MEM_foldi                 CONS SPTAUX_foldi_thm
     SPTAUX_ALOOKUP_MEM               ALOOKUP_DEF
     SPTAUX_ALOOKUP_FAILS             ALOOKUP_DEF
     insert_union                     spt_CASE
     domain_empty                     spt_distinct
     SPTAUX_LENGTH_foldi              CONS SPTAUX_foldi_thm sptree_size_def
     SPTAUX_ITLIST_UNCURRY            CONS UNCURRY
     SPTAUX_foldi_FOLDR_toAList_lemma CONS SPTAUX_foldi_thm UNCURRY
     foldi_FOLDR_toAList              CONS UNCURRY
     SPTAUX_LENGTH_toListA            sptree_size_def
     size_zero_empty                  sptree_size_def
     spt_eq_thm                       spt_distinct spt_inject
     union_LN                         spt_CASE
     inter_LN                         spt_CASE
     union_assoc                      spt_CASE
     inter_assoc                      CONS
     lookup_fromAList                 ALOOKUP_DEF ALOOKUP_THM
     lookup_map                       OPTION_MAP_DEF
     map_LN                           spt_distinct
     domain_mapi                      OPTION_MAP_DEF
     lookup_FOLDL_union               OPTION_CHOICE_DEF
     map_union                        spt_CASE
     SPTAUX_ALOOKUP_MAP_lemma         ALOOKUP_DEF OPTION_MAP_DEF
     MAP_foldi                        CONS SPTAUX_foldi_thm
     union_num_set_sym                spt_CASE spt_inject
     wf_difference                    spt_CASE
     inter_eq_LN                      CONS
     map_map_K                        K_THM
     lookup_map_K                     CONS K_THM OPTION_MAP_DEF
     alist_insert_ind                 CONS
     lookup_alist_insert              ALOOKUP_DEF
     size_list_to_num_set             nub_DEF sptree_size_def
     mapi_fromList                    OPTION_MAP_DEF
     SPTAUX_DROP_0                    DROP_DEF
     SPTAUX_TAKE_DROP_UPDATE          DROP_DEF TAKE_DEF
     SUM_MAP_same_LE                  SUM
     SUM_MAP_same_LESS                SUM
     size_fromList                    CONS count_DEF
     SPTAUX_spts_to_alist_aux_thm     CONS
     SPTAUX_SUM_add_pause             SUM spt_size_def
     SPTAUX_SUM_MAP_APPEND            SUM
     SPTAUX_SUM_MAP_REVERSE           SUM
     SPTAUX_spt_size_left_right       K_THM spt_distinct spt_size_def
     spts_to_alist_aux_size           RVEQ_TAC SPTAUX_spts_to_alist_eqn SUM WF_REL_THMS measure spt_distinct
     spts_to_alist_def                SPTAUX_spts_to_alist_eqn
     SPTAUX_LENGTH_COUNT_LIST         COUNT_LIST_DEF
     SPTAUX_ALOOKUP_ZIP_MAP_SUC       ALOOKUP_DEF
     SPTAUX_ALOOKUP_ZIP_COUNT_LIST    ALOOKUP_DEF COUNT_LIST_DEF
     fromList_fromAList               spt_CASE
     SPTAUX_closure_spt_size          WF_REL_THMS measure
     closure_spt_ind                  RVEQ_TAC
     num_set_tree_union_empty         spt_CASE spt_distinct
     wf_num_set_tree_union            spt_CASE
     domain_num_set_tree_union        spt_CASE
     num_set_tree_union_sym           spt_CASE
     lookup_num_set_tree_union        spt_CASE
     closure_spt_thm                  isEmpty_def sptree_size_def

*)
