(* ================================================================ *)
(*  The theorems of words4Theory that LightCake proves and this   *)
(*  port needs, taken from its hol4/words4.                       *)
(*                                                                *)
(*  LightCake is the other HOL Light port of CakeML               *)
(*  (hol-light-family/LightCake, BSD 3-Clause); its HOL4 library  *)
(*  layer is proved, and of these theories this port has only     *)
(*  the definitions that CakeML needs.  tools/lightcake.py        *)
(*  writes this file: the statements and the proofs are           *)
(*  LightCake's, with its constants under the names this port     *)
(*  gives them.  What it could not take, and why, is at the end.  *)
(* ================================================================ *)


let MOD_2EXP_def = prove
 (`!x n. MOD_2EXP x n = n MOD 2 EXP x`,
  REWRITE_TAC[MOD_2EXP]);;

let WORDSAUX_EXP2_LT = prove
 (`!m n. 2 EXP m < 2 EXP n <=> m < n`,
  REWRITE_TAC[LT_EXP] THEN ARITH_TAC);;

let WORDSAUX_EXP2_LE = prove
 (`!m n. 2 EXP m <= 2 EXP n <=> m <= n`,
  REWRITE_TAC[LE_EXP] THEN ARITH_TAC);;

let BIT0_ODD = prove
 (`numbit 0 = ODD`,
  REWRITE_TAC[FUN_EQ_THM; numbit; EXP; DIV_1]);;

let BIT_ZERO = prove
 (`!b. ~numbit b 0`,
  REWRITE_TAC[numbit; DIV_0; ODD]);;

let NOT_BIT_GT_TWOEXP = prove
 (`!i n. n < 2 EXP i ==> ~numbit i n`,
  SIMP_TAC[numbit; DIV_LT; ODD]);;

let BIT_DIV2 = prove
 (`!n i. numbit n (i DIV 2) <=> numbit (SUC n) i`,
  REWRITE_TAC[numbit; EXP; DIV_DIV]);;

let TWOEXP_MONO2 = prove
 (`!a b. a <= b ==> 2 EXP a <= 2 EXP b`,
  REWRITE_TAC[WORDSAUX_EXP2_LE]);;

let TWOEXP_MONO = prove
 (`!a b. a < b ==> 2 EXP a < 2 EXP b`,
  REWRITE_TAC[WORDSAUX_EXP2_LT]);;

let DIV_MULT_THM2 = prove
 (`!n. 2 * (n DIV 2) = n - n MOD 2`,
  GEN_TAC THEN MP_TAC(SPECL [`n:num`; `2`] DIVISION) THEN ARITH_TAC);;

let TWOEXP_NOT_ZERO = EXP_2_NE_0;;

let ZERO_LT_TWOEXP = prove
 (`!n. 0 < 2 EXP n`,
  REWRITE_TAC[EXP_LT_0] THEN ARITH_TAC);;

let ODD_MOD2_LEM = ODD_MOD;;

let LESS_MULT_MONO2 = prove
 (`!a b x y. a < x /\ b < y ==> a * b < x * y`,
  MESON_TAC[LT_MULT2]);;

let DIV_GT0 = prove
 (`!a b. b <= a /\ 0 < b ==> 0 < a DIV b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ARITH_RULE `0 < n <=> 1 <= n`] THEN
  ASM_SIMP_TAC[LE_RDIV_EQ; ARITH_RULE `0 < b ==> ~(b = 0)`] THEN
  ASM_ARITH_TAC);;

let MOD_ZERO_GT = prove
 (`!n a. ~(a = 0) /\ a MOD 2 EXP n = 0 ==> 2 EXP n <= a`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
  UNDISCH_TAC `a MOD 2 EXP n = 0` THEN ASM_SIMP_TAC[MOD_LT]);;

let ADD_BIT0 = prove
 (`!m n. numbit 0 (m + n) <=> ~(numbit 0 m <=> numbit 0 n)`,
  REWRITE_TAC[BIT0_ODD; ODD_ADD]);;

let BIT_IMP_GE_TWOEXP = prove
 (`!i n. numbit i n ==> 2 EXP i <= n`,
  MESON_TAC[NOT_BIT_GT_TWOEXP; NOT_LT]);;

let MOD_ADD_1 = prove
 (`!n. 0 < n ==> !x. ~((x + 1) MOD n = 0) ==> (x + 1) MOD n = x MOD n +
   1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`x:num`; `n:num`] DIVISION) THEN
  ASM_SIMP_TAC[ARITH_RULE `0 < n ==> ~(n = 0)`] THEN
  ABBREV_TAC `q = x DIV n` THEN ABBREV_TAC `r = x MOD n` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `(q * n + r) + 1 = q * n + (r + 1)`] THEN
  ASM_SIMP_TAC[MOD_MULT_ADD] THEN
  ASM_CASES_TAC `r + 1 = n` THENL
   [UNDISCH_TAC `~((x + 1) MOD n = 0)` THEN
    ASM_REWRITE_TAC[ARITH_RULE `(q * n + r) + 1 = q * n + (r + 1)`] THEN
    ASM_SIMP_TAC[MOD_MULT_ADD; MOD_REFL; ARITH_RULE `0 < n ==> ~(n =
      0)`];
    MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC]);;

let NUMBIT_MOD_2EXP = prove
 (`!i k n. numbit i (n MOD 2 EXP k) <=> i < k /\ numbit i n`,
  REPEAT GEN_TAC THEN
  MP_TAC(AP_TERM `\s:num->bool. i IN s` (SPECL [`n:num`; `k:num`]
    BITS_OF_NUM_MOD)) THEN
  REWRITE_TAC[IN_BITS_OF_NUM; IN_ELIM_THM; GSYM numbit] THEN
    MESON_TAC[]);;

let NUMBIT_DIV_2EXP = prove
 (`!i k n. numbit i (n DIV 2 EXP k) <=> numbit (k + i) n`,
  REWRITE_TAC[numbit; DIV_DIV; EXP_ADD]);;

let NUMBIT_EQ = prove
 (`!m n. m = n <=> !i. numbit i m <=> numbit i n`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM BITS_OF_NUM_EQ]
    THEN
  REWRITE_TAC[EXTENSION; IN_BITS_OF_NUM; GSYM numbit]);;

let BIT_TIMES2 = prove
 (`!z n. numbit z (2 * n) <=> 0 < z /\ numbit (z - 1) n`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC(SPEC `z:num` num_CASES) THEN
  REWRITE_TAC[numbit; EXP; DIV_1; ODD_MULT; ARITH; LT_REFL; SUC_SUB1;
    LT_0] THEN
  REWRITE_TAC[GSYM DIV_DIV] THEN SIMP_TAC[DIV_MULT; ARITH_EQ]);;

let BIT_TIMES2_1 = prove
 (`!n z. numbit z (2 * n + 1) <=> z = 0 \/ numbit z (2 * n)`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC(SPEC `z:num` num_CASES) THEN
  REWRITE_TAC[numbit; EXP; DIV_1; ODD_ADD; ODD_MULT; ARITH; NOT_SUC]
    THEN
  REWRITE_TAC[GSYM DIV_DIV] THEN SIMP_TAC[DIV_MULT; ARITH_EQ] THEN
  AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

let NUMBIT_COMPLEMENT = prove
 (`!n c i. c < 2 EXP n
           ==> (numbit i ((2 EXP n - 1) - c) <=> i < n /\ ~numbit i c)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[numbit] THEN
  ASM_CASES_TAC `i < n:num` THEN ASM_REWRITE_TAC[] THENL
   [ALL_TAC;
    SUBGOAL_THEN `((2 EXP n - 1) - c) DIV 2 EXP i = 0`
     (fun th -> REWRITE_TAC[th; ODD]) THEN
    MATCH_MP_TAC DIV_LT THEN TRANS_TAC LTE_TRANS `2 EXP n` THEN
    REWRITE_TAC[WORDSAUX_EXP2_LE] THEN
    MP_TAC(SPEC `n:num` EXP_2_NE_0) THEN ASM_ARITH_TAC] THEN
  SUBGOAL_THEN `2 EXP n = 2 EXP (n - i) * 2 EXP i` SUBST_ALL_TAC THENL
   [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
     ALL_TAC] THEN
  MP_TAC(SPECL [`c:num`; `2 EXP i`] DIVISION) THEN
    REWRITE_TAC[EXP_2_NE_0] THEN
  MP_TAC(SPEC `n - i:num` EXP_2_NE_0) THEN
  SUBGOAL_THEN `~(n - i = 0)` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `c < 2 EXP (n - i) * 2 EXP i` THEN
  SPEC_TAC(`n - i:num`,`k:num`) THEN
  SPEC_TAC(`c DIV 2 EXP i`,`q:num`) THEN SPEC_TAC(`c MOD 2 EXP
    i`,`r:num`) THEN
  SPEC_TAC(`2 EXP i`,`p:num`) THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC
    THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
  SUBGOAL_THEN `q < 2 EXP k` MP_TAC THENL
   [MP_TAC(SPECL [`q:num`; `2 EXP k`; `p:num`] LT_MULT_RCANCEL) THEN
     ASM_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `d:num` o GEN_REWRITE_RULE I [LT_EXISTS]) THEN
  SUBGOAL_THEN `(2 EXP k * p - 1 - (q * p + r)) DIV p = d` SUBST1_TAC
    THENL
   [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `(p - 1) - r` THEN
    ASM_REWRITE_TAC[RIGHT_ADD_DISTRIB; MULT_CLAUSES] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `EVEN(q + SUC d)` MP_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[EVEN_EXP; ARITH]
     THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[EVEN_ADD; EVEN; GSYM NOT_EVEN] THEN CONV_TAC TAUT]);;

let BIT_EXP_SUB1 = prove
 (`!b n. numbit b (2 EXP n - 1) <=> b < n`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`n:num`; `0`; `b:num`] NUMBIT_COMPLEMENT) THEN
  REWRITE_TAC[ZERO_LT_TWOEXP; SUB_0; BIT_ZERO]);;

let BIT_COMPLEMENT = prove
 (`!n i a.
     numbit i (2 EXP n - a MOD 2 EXP n) <=>
     (a MOD 2 EXP n = 0 /\ i = n) \/
     (~(a MOD 2 EXP n = 0) /\ i < n /\ ~numbit i (a MOD 2 EXP n - 1))`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`a:num`; `2 EXP n`] MOD_LT_EQ) THEN
  REWRITE_TAC[EXP_2_NE_0] THEN
  SPEC_TAC(`a MOD 2 EXP n`,`b:num`) THEN GEN_TAC THEN DISCH_TAC THEN
  ASM_CASES_TAC `b = 0` THEN ASM_REWRITE_TAC[SUB_0] THENL
   [MP_TAC(AP_TERM `\s:num->bool. i IN s` (SPEC `n:num`
     BITS_OF_NUM_POW2)) THEN
    REWRITE_TAC[IN_BITS_OF_NUM; GSYM numbit; IN_SING];
    SUBGOAL_THEN `2 EXP n - b = (2 EXP n - 1) - (b - 1)` SUBST1_TAC
      THENL
     [ASM_ARITH_TAC; MATCH_MP_TAC NUMBIT_COMPLEMENT THEN
       ASM_ARITH_TAC]]);;

let dimindex_def = prove
 (`dimindex(:A) = if FINITE(:A) then CARD(:A) else 1`,
  REWRITE_TAC[dimindex]);;

let FCP_BETA = prove
 (`!(g:num->bool) i.
     i < dimindex(:N) ==> (bit i (word_of_bits g:N word) <=> g i)`,
  SIMP_TAC[BIT_WORD_OF_BITS; IN]);;

let fcp_CART_EQ = prove
 (`!x y:N word. x = y <=> !i. i < dimindex(:N) ==> (bit i x <=> bit i
   y)`,
  REWRITE_TAC[WORD_EQ_BITS_ALT]);;

let index_sum = prove
 (`dimindex(:(A,B)finite_sum) = dimindex(:A) + dimindex(:B)`,
  REWRITE_TAC[DIMINDEX_FINITE_SUM]);;

let dimword_def = prove
 (`dimword(:A) = 2 EXP dimindex(:A)`,
  REWRITE_TAC[dimword]);;

let INT_MIN_def = prove
 (`INT_MIN(:A) = 2 EXP (dimindex(:A) - 1)`,
  REWRITE_TAC[INT_MIN]);;

let UINT_MAX_def = prove
 (`UINT_MAX(:A) = dimword(:A) - 1`,
  REWRITE_TAC[UINT_MAX]);;

let INT_MAX_def = prove
 (`INT_MAX(:A) = INT_MIN(:A) - 1`,
  REWRITE_TAC[INT_MAX]);;

let ZERO_LT_dimword = prove
 (`0 < dimword(:N)`,
  REWRITE_TAC[dimword_def; ZERO_LT_TWOEXP]);;

let DIMINDEX_GT_0 = prove
 (`0 < dimindex(:A)`,
  REWRITE_TAC[DIMINDEX_GE_1; ARITH_RULE `0 < n <=> 1 <= n`]);;

let dimindex_lt_dimword = prove
 (`dimindex(:N) < dimword(:N)`,
  REWRITE_TAC[dimword_def; LT_POW2_REFL]);;

let dimword_8 = prove
 (`dimword(:8) = 256`,
  REWRITE_TAC[dimword_def; DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV);;

let dimword_64 = prove
 (`dimword(:64) = 18446744073709551616`,
  REWRITE_TAC[dimword_def; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV);;

let dimword_IS_TWICE_INT_MIN = prove
 (`dimword(:N) = 2 * INT_MIN(:N)`,
  REWRITE_TAC[dimword_def; INT_MIN_def; GSYM(CONJUNCT2 EXP)] THEN
  AP_TERM_TAC THEN MP_TAC(ISPEC `(:N)` DIMINDEX_GE_1) THEN ARITH_TAC);;

let LT_DIMINDEX_LE_HB = prove
 (`!b. b < dimindex(:N) <=> b <= dimindex(:N) - 1`,
  MP_TAC(ISPEC `(:N)` DIMINDEX_GE_1) THEN ARITH_TAC);;

let HB_LT_DIMINDEX = prove
 (`dimindex(:N) - 1 < dimindex(:N)`,
  MP_TAC(ISPEC `(:N)` DIMINDEX_GE_1) THEN ARITH_TAC);;

let w2n_lt = prove
 (`!w:N word. val w < dimword(:N)`,
  REWRITE_TAC[dimword_def; VAL_BOUND]);;

let w2n_11 = VAL_EQ;;

let n2w_w2n = WORD_VAL;;

let w2n_n2w = prove
 (`!n. val(word n:N word) = n MOD dimword(:N)`,
  REWRITE_TAC[VAL_WORD; dimword_def]);;

let n2w_11 = prove
 (`!m n. (word m:N word = word n) <=> m MOD dimword(:N) = n MOD
   dimword(:N)`,
  REWRITE_TAC[GSYM VAL_EQ; w2n_n2w]);;

let n2w_mod = prove
 (`!n. word(n MOD dimword(:N)):N word = word n`,
  REWRITE_TAC[dimword_def; WORD_MOD_SIZE]);;

let mod_dimindex = prove
 (`!n. n MOD dimindex(:N) < dimword(:N)`,
  GEN_TAC THEN TRANS_TAC LT_TRANS `dimindex(:N)` THEN
  REWRITE_TAC[dimindex_lt_dimword; MOD_LT_EQ; DIMINDEX_NONZERO]);;

let ranged_word_nchotomy = prove
 (`!w:N word. ?n. w = word n /\ n < dimword(:N)`,
  GEN_TAC THEN EXISTS_TAC `val(w:N word)` THEN
  REWRITE_TAC[WORD_VAL; w2n_lt]);;

let WORD_FINITE = prove
 (`!s:N word->bool. FINITE s`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `IMAGE (word:num->N word) {n | n < 2 EXP dimindex(:N)}`
    THEN
  SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG_LT] THEN
  REWRITE_TAC[SUBSET; IN_IMAGE; IN_ELIM_THM] THEN
  MESON_TAC[WORD_VAL; VAL_BOUND]);;

let n2w_def = prove
 (`!n. word n:N word = word_of_bits (\i. numbit i n)`,
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD; BIT_WORD_OF_BITS; IN; numbit]
    THEN
  MESON_TAC[]);;

let word_index_n2w = prove
 (`!n i. bit i (word n:N word) <=> if i < dimindex(:N) then numbit i n
   else F`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[BIT_WORD;
    numbit]);;

let word_bit_n2w = prove
 (`!b n. bit b (word n:N word) <=> b <= dimindex(:N) - 1 /\ numbit b n`,
  REWRITE_TAC[BIT_WORD; numbit; GSYM LT_DIMINDEX_LE_HB]);;

let word_0 = prove
 (`!i. i < dimindex(:N) ==> ~bit i (word 0:N word)`,
  REWRITE_TAC[BIT_WORD_0]);;

let word_bit_def = prove
 (`!b w:N word. bit b w <=> b <= dimindex(:N) - 1 /\ bit b w`,
  REWRITE_TAC[GSYM LT_DIMINDEX_LE_HB] THEN MESON_TAC[BIT_GUARD]);;

let word_bit = prove
 (`!w:N word b. b < dimindex(:N) ==> (bit b w <=> bit b w)`,
  REWRITE_TAC[]);;

let word_bit_thm = prove
 (`!n w:N word. bit n w <=> n < dimindex(:N) /\ bit n w`,
  MESON_TAC[BIT_GUARD]);;

let w2w_def = word_zx;;

let word_msb_n2w = prove
 (`!n. word_msb (word n:N word) <=> numbit (dimindex(:N) - 1) n`,
  REWRITE_TAC[word_msb; BIT_WORD; numbit; HB_LT_DIMINDEX]);;

let word_msb_n2w_numeric = prove
 (`!n. word_msb (word n:N word) <=> INT_MIN(:N) <= n MOD dimword(:N)`,
  REWRITE_TAC[word_msb; MSB_VAL; VAL_WORD; INT_MIN_def; dimword_def]);;

let word_msb_neg = prove
 (`!w:N word. word_msb w <=> word_ilt w (word 0)`,
  REWRITE_TAC[word_msb; MSB_IVAL; WORD_ILT; IVAL_WORD_0]);;

let word_add_def = prove
 (`!v w:N word. word_add v w = word(val v + val w)`,
  REWRITE_TAC[WORD_ADD; WORD_VAL]);;

let word_mul_def = prove
 (`!v w:N word. word_mul v w = word(val v * val w)`,
  REWRITE_TAC[WORD_MUL; WORD_VAL]);;

let word_2comp_def = prove
 (`!w:N word. word_neg w = word(dimword(:N) - val w)`,
  GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_NEG_CASES; VAL_WORD;
    dimword_def] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[SUB_0; MOD_REFL] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
  MP_TAC(SPEC `dimindex(:N)` EXP_2_NE_0) THEN ASM_ARITH_TAC);;

let word_sub_def = prove
 (`!v w:N word. word_sub v w = word_add v (word_neg w)`,
  WORD_ARITH_TAC);;

let word_div_def = prove
 (`!v w:N word. word_udiv v w = word(val v DIV val w)`,
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_UDIV; VAL_WORD] THEN
  REPEAT GEN_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
  MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC `val(v:N word)` THEN
  REWRITE_TAC[DIV_LE; VAL_BOUND]);;

let word_1comp_def = prove
 (`!w:N word. word_not w = word_of_bits (\i. ~bit i w):N word`,
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_NOT; BIT_WORD_OF_BITS; IN] THEN
  MESON_TAC[]);;

let word_and_def = prove
 (`!v w:N word. word_and v w = word_of_bits (\i. bit i v /\ bit i w):N
   word`,
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_AND; BIT_WORD_OF_BITS; IN] THEN
  MESON_TAC[]);;

let word_or_def = prove
 (`!v w:N word. word_or v w = word_of_bits (\i. bit i v \/ bit i w):N
   word`,
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_OR; BIT_WORD_OF_BITS; IN] THEN
  MESON_TAC[]);;

let word_xor_def = prove
 (`!v w:N word. word_xor v w = word_of_bits (\i. ~(bit i v <=> bit i
   w)):N word`,
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_XOR; BIT_WORD_OF_BITS; IN] THEN
  MESON_TAC[]);;

let word_lsl_def = prove
 (`!w:N word n.
     word_shl w n =
     word_of_bits (\i. i < dimindex(:N) /\ n <= i /\ bit (i - n) w):N
       word`,
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_SHL; BIT_WORD_OF_BITS; IN] THEN
  MESON_TAC[]);;

let word_lsr_def = prove
 (`!w:N word n.
     word_ushr w n =
     word_of_bits (\i. i + n < dimindex(:N) /\ bit (i + n) w):N word`,
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_USHR; BIT_WORD_OF_BITS; IN]
    THEN
  REPEAT STRIP_TAC THEN ASM_MESON_TAC[BIT_GUARD]);;

let word_asr_def = prove
 (`!w:N word n.
     word_ishr w n =
     word_of_bits (\i. if dimindex(:N) <= i + n then word_msb w
                       else bit (i + n) w):N word`,
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_ISHR; BIT_WORD_OF_BITS; IN;
              word_msb] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[GSYM NOT_LT] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

let word_ror_def = prove
 (`!w:N word n.
     word_ror w n =
     word_of_bits (\i. bit ((i + n) MOD dimindex(:N)) w):N word`,
  REWRITE_TAC[word_ror; WORD_EQ_BITS_ALT; BIT_WORD_OF_BITS; IN_ELIM_THM;
    IN]);;

let WORD_LO = WORD_ULT;;

let WORD_LS = WORD_ULE;;

let WORD_LTi = WORD_ILT;;

let WORD_NOT_LOWER = prove
 (`!a b:N word. ~(word_ult a b) <=> word_ule b a`,
  REWRITE_TAC[WORD_ULT; WORD_ULE; NOT_LT]);;

let WORD_NOT_LOWER_EQUAL = prove
 (`!a b:N word. ~(word_ule a b) <=> word_ult b a`,
  REWRITE_TAC[WORD_ULT; WORD_ULE; NOT_LE]);;

let WORD_LOWER_REFL = prove
 (`!a:N word. ~(word_ult a a)`,
  REWRITE_TAC[WORD_ULT; LT_REFL]);;

let WORD_LOWER_NOT_EQ = prove
 (`!a b:N word. word_ult a b ==> ~(a = b)`,
  MESON_TAC[WORD_LOWER_REFL]);;

let WORD_LOWER_EQ_TRANS = prove
 (`!a b c:N word. word_ule a b /\ word_ule b c ==> word_ule a c`,
  REWRITE_TAC[WORD_ULE; LE_TRANS]);;

let WORD_LO_word_0 = prove
 (`(!n:N word. word_ult (word 0) n <=> ~(n = word 0)) /\
   (!n:N word. ~(word_ult n (word 0)))`,
  REWRITE_TAC[WORD_ULT; VAL_WORD_0; GSYM VAL_EQ_0] THEN ARITH_TAC);;

let WORD_LO_word_T = prove
 (`(!n:N word. ~(word_ult (word_neg (word 1)) n)) /\
   (!n:N word. word_ult n (word_neg (word 1)) <=> ~(n = word_neg (word
     1)))`,
  REWRITE_TAC[WORD_ULT; GSYM VAL_EQ; VAL_WORD_NEG_1] THEN
  CONJ_TAC THEN GEN_TAC THEN MP_TAC(ISPEC `n:N word` VAL_BOUND) THEN
  ARITH_TAC);;

let word_lo_n2w = prove
 (`!a b. word_ult (word a:N word) (word b) <=>
         a MOD dimword(:N) < b MOD dimword(:N)`,
  REWRITE_TAC[WORD_ULT; w2n_n2w]);;

let word_ls_n2w = prove
 (`!a b. word_ule (word a:N word) (word b) <=>
         a MOD dimword(:N) <= b MOD dimword(:N)`,
  REWRITE_TAC[WORD_ULE; w2n_n2w]);;

let WORD_LT = prove
 (`!a b:N word.
     word_ilt a b <=>
     (word_msb a <=> word_msb b) /\ val a < val b \/ word_msb a /\
       ~word_msb b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD_ILT; word_msb; IVAL_VAL] THEN
  MP_TAC(ISPEC `a:N word` INT_VAL_BOUND) THEN
  MP_TAC(ISPEC `b:N word` INT_VAL_BOUND) THEN
  MAP_EVERY ASM_CASES_TAC
   [`bit (dimindex(:N) - 1) (a:N word)`; `bit (dimindex(:N) - 1) (b:N
     word)`] THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES; GSYM INT_OF_NUM_LT] THEN
    INT_ARITH_TAC);;

let WORD_LE = prove
 (`!a b:N word.
     word_ile a b <=>
     (word_msb a <=> word_msb b) /\ val a <= val b \/ word_msb a /\
       ~word_msb b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD_ILE; word_msb; IVAL_VAL] THEN
  MP_TAC(ISPEC `a:N word` INT_VAL_BOUND) THEN
  MP_TAC(ISPEC `b:N word` INT_VAL_BOUND) THEN
  MAP_EVERY ASM_CASES_TAC
   [`bit (dimindex(:N) - 1) (a:N word)`; `bit (dimindex(:N) - 1) (b:N
     word)`] THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES; GSYM INT_OF_NUM_LE] THEN
    INT_ARITH_TAC);;

let WORD_NOT_LESS = prove
 (`!a b:N word. ~(word_ilt a b) <=> word_ile b a`,
  REWRITE_TAC[WORD_ILT; WORD_ILE; INT_NOT_LT]);;

let WORD_LESS_REFL = prove
 (`!a:N word. ~(word_ilt a a)`,
  REWRITE_TAC[WORD_ILT; INT_LT_REFL]);;

let WORD_LESS_OR_EQ = prove
 (`!a b:N word. word_ile a b <=> word_ilt a b \/ a = b`,
  REWRITE_TAC[WORD_ILT; WORD_ILE; GSYM IVAL_EQ] THEN INT_ARITH_TAC);;

let WORD_LESS_EQ_TRANS = prove
 (`!a b c:N word. word_ile a b /\ word_ile b c ==> word_ile a c`,
  REWRITE_TAC[WORD_ILE] THEN INT_ARITH_TAC);;

let word_lt_n2w = prove
 (`!a b. word_ilt (word a:N word) (word b) <=>
         let sa = numbit (dimindex(:N) - 1) a
         and sb = numbit (dimindex(:N) - 1) b in
         (sa <=> sb) /\ a MOD dimword(:N) < b MOD dimword(:N) \/ sa /\
           ~sb`,
  REWRITE_TAC[WORD_LT; GSYM word_msb_n2w; w2n_n2w] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[]);;

let WORD_ADD_COMM = WORD_ADD_SYM;;

let WORD_MULT_COMM = WORD_MUL_SYM;;

let WORD_MULT_ASSOC = WORD_MUL_ASSOC;;

let WORD_AND_COMM = WORD_AND_SYM;;

let WORD_OR_COMM = WORD_OR_SYM;;

let WORD_OR_IDEM = WORD_OR_REFL;;

let WORD_EQ_SUB_ZERO = WORD_SUB_EQ_0;;

let WORD_NEG = WORD_NEG_AS_ADD;;

let words_WORD_AND_ASSOC = prove
 (`!a b c:N word. word_and (word_and a b) c = word_and a (word_and b
   c)`,
  REWRITE_TAC[WORD_AND_ASSOC]);;

let words_WORD_OR_ASSOC = prove
 (`!a b c:N word. word_or (word_or a b) c = word_or a (word_or b c)`,
  REWRITE_TAC[WORD_OR_ASSOC]);;

let WORD_LEFT_AND_OVER_OR = prove
 (`!a b c:N word.
     word_and a (word_or b c) = word_or (word_and a b) (word_and a c)`,
  WORD_BITWISE_TAC);;

let WORD_LEFT_ADD_DISTRIB = WORD_RULE
 `!v w x:N word.
     word_mul v (word_add w x) = word_add (word_mul v w) (word_mul v
       x)`;;

let WORD_LEFT_SUB_DISTRIB = WORD_RULE
 `!v w x:N word.
     word_mul v (word_sub w x) = word_sub (word_mul v w) (word_mul v
       x)`;;

let WORD_MULT_CLAUSES = WORD_RULE
 `!v w:N word.
     word_mul (word 0) v = word 0 /\ word_mul v (word 0) = word 0 /\
     word_mul (word 1) v = v /\ word_mul v (word 1) = v /\
     word_mul (word_add v (word 1)) w = word_add (word_mul v w) w /\
     word_mul v (word_add w (word 1)) = word_add v (word_mul v w)`;;

let WORD_NEG_MUL = WORD_RULE
 `!w:N word. word_neg w = word_mul (word_neg (word 1)) w`;;

let WORD_ADD_SUB = WORD_RULE
 `!v w:N word. word_sub (word_add v w) w = v`;;

let WORD_SUB_PLUS = WORD_RULE
 `!v w x:N word. word_sub v (word_add w x) = word_sub (word_sub v w)
   x`;;

let WORD_SUB_INTRO = WORD_RULE
 `(!x y:N word. word_add (word_neg y) x = word_sub x y) /\
  (!x y:N word. word_add x (word_neg y) = word_sub x y) /\
  (!x y z:N word. word_add (word_mul (word_neg x) y) z = word_sub z
    (word_mul x y)) /\
  (!x y z:N word. word_add z (word_mul (word_neg x) y) = word_sub z
    (word_mul x y)) /\
  (!x:N word. word_mul (word_neg (word 1)) x = word_neg x) /\
  (!x y z:N word. word_sub z (word_mul (word_neg x) y) = word_add z
    (word_mul x y)) /\
  (!x y z:N word.
     word_sub (word_mul (word_neg x) y) z = word_neg (word_add (word_mul
       x y) z))`;;

let WORD_ADD_LINV = WORD_RULE
 `!w:N word. word_add (word_neg w) w = word 0`;;

let WORD_ADD_RINV = WORD_RULE
 `!w:N word. word_add w (word_neg w) = word 0`;;

let WORD_ADD_SUB_ASSOC = WORD_RULE
 `!v w x:N word. word_sub (word_add v w) x = word_add v (word_sub w
   x)`;;

let WORD_ADD_SUB_SYM = WORD_RULE
 `!v w x:N word. word_sub (word_add v w) x = word_add (word_sub v x)
   w`;;

let WORD_NEG_ADD = WORD_RULE
 `!v w:N word. word_neg (word_add v w) = word_add (word_neg v) (word_neg
   w)`;;

let WORD_SUB_SUB = WORD_RULE
 `!v w x:N word. word_sub v (word_sub w x) = word_sub (word_add v x)
   w`;;

let WORD_EQ_ADD_LCANCEL = prove
 (`!v w x:N word. word_add v w = word_add v x <=> w = x`,
  MESON_TAC[WORD_RULE `!v w:N word. word_sub (word_add v w) v = w`]);;

let WORD_ADD_INV_0_EQ = prove
 (`!v w:N word. word_add v w = v <=> w = word 0`,
  MESON_TAC[WORD_RULE `!v w:N word. word_sub (word_add v w) v = w`;
            WORD_SUB_REFL; WORD_ADD_0]);;

let WORD_EQ_NEG = prove
 (`!v w:N word. word_neg v = word_neg w <=> v = w`,
  MESON_TAC[WORD_NEG_NEG]);;

let WORD_ADD_EQ_SUB = prove
 (`!v w x:N word. word_add v w = x <=> v = word_sub x w`,
  MESON_TAC[WORD_RULE `!v w:N word. word_sub (word_add v w) w = v`;
            WORD_RULE `!v w:N word. word_add (word_sub v w) w = v`]);;

let WORD_EQ_SUB_RADD = prove
 (`!v w x:N word. word_sub v w = x <=> v = word_add x w`,
  MESON_TAC[WORD_RULE `!v w:N word. word_sub (word_add v w) w = v`;
            WORD_RULE `!v w:N word. word_add (word_sub v w) w = v`]);;

let WORD_LITERAL_ADD = prove
 (`(!m n. word_add (word_neg (word m)) (word_neg (word n)):N word =
          word_neg (word (m + n))) /\
   (!m n. word_add (word m) (word_neg (word n)):N word =
          if n <= m then word (m - n) else word_neg (word (n - m)))`,
  CONJ_TAC THEN REPEAT GEN_TAC THENL
   [REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[WORD_SUB; GSYM NOT_LE;
    ARITH_RULE `~(n <= m) ==> m <= n`] THEN
  CONV_TAC WORD_RULE);;

let n2w_SUC = prove
 (`!n. word (SUC n):N word = word_add (word n) (word 1)`,
  REWRITE_TAC[ADD1; WORD_ADD]);;

let n2w_sub = prove
 (`!a b. b <= a ==> word (a - b):N word = word_sub (word a) (word b)`,
  SIMP_TAC[WORD_SUB]);;

let word_2comp_n2w = prove
 (`!n. word_neg (word n):N word = word (dimword(:N) - n MOD
   dimword(:N))`,
  REWRITE_TAC[word_2comp_def; w2n_n2w]);;

let w2n_minus1 = prove
 (`val (word_neg (word 1):N word) = dimword(:N) - 1`,
  REWRITE_TAC[VAL_WORD_NEG_1; dimword_def]);;

let MOD_COMPLEMENT = prove
 (`!n q a. 0 < n /\ 0 < q /\ a < q * n ==>
           (q * n - a) MOD n = (n - a MOD n) MOD n`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:num`; `n:num`] DIVISION) THEN
  ASM_SIMP_TAC[ARITH_RULE `0 < n ==> ~(n = 0)`] THEN
  ABBREV_TAC `k = a DIV n` THEN ABBREV_TAC `r = a MOD n` THEN STRIP_TAC
    THEN
  SUBGOAL_THEN `k < q` ASSUME_TAC THENL
   [MP_TAC(SPECL [`k:num`; `q:num`; `n:num`] LT_MULT_RCANCEL) THEN
    ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `q * n - a = (q - k - 1) * n + (n - r)` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[RIGHT_SUB_DISTRIB; MULT_CLAUSES] THEN
    SUBGOAL_THEN `(k + 1) * n <= q * n` MP_TAC THENL
     [REWRITE_TAC[LE_MULT_RCANCEL] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[RIGHT_ADD_DISTRIB; MULT_CLAUSES] THEN ASM_ARITH_TAC;
    REWRITE_TAC[MOD_MULT_ADD]]);;

let w2n_add = prove
 (`!a b:N word.
     ~word_msb a /\ ~word_msb b ==> val (word_add a b) = val a + val b`,
  REWRITE_TAC[word_msb; MSB_VAL; NOT_LE] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[VAL_WORD_ADD_CASES] THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[] THEN
  MP_TAC(CONJUNCT1 TWICE_MSB) THEN ASM_ARITH_TAC);;

let w2n_add_2 = prove
 (`!a b:N word.
     val a + val b < dimword(:N) ==> val (word_add a b) = val a + val
       b`,
  SIMP_TAC[VAL_WORD_ADD_CASES; dimword_def]);;

let word_sub_w2n = prove
 (`!x y:N word. word_ule y x ==> val (word_sub x y) = val x - val y`,
  SIMP_TAC[WORD_ULE; VAL_WORD_SUB_CASES]);;

let TWO_COMP_POS = prove
 (`!a:N word.
     ~word_msb a ==>
     (if a = word 0 then ~word_msb (word_neg a) else word_msb (word_neg
       a))`,
  GEN_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[WORD_NEG_0; word_msb; BIT_WORD_0] THEN
  REWRITE_TAC[MSB_VAL; VAL_WORD_NEG_CASES] THEN
  ASM_REWRITE_TAC[VAL_EQ_0] THEN
  MP_TAC(CONJUNCT1 TWICE_MSB) THEN ARITH_TAC);;

let WORD_ADD_BIT0 = prove
 (`!a b:N word. bit 0 (word_add a b) <=> ~(bit 0 a <=> bit 0 b)`,
  REWRITE_TAC[BIT_WORD_ADD_CLAUSES]);;

let word_bit_test = prove
 (`!n w:N word. bit n w <=> ~(word_and w (word (2 EXP n)) = word 0)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_AND; BIT_WORD_POW2; BIT_WORD_0]
    THEN
  MESON_TAC[BIT_GUARD]);;

let word_bit_or = prove
 (`!n w1 w2:N word. bit n (word_or w1 w2) <=> bit n w1 \/ bit n w2`,
  REWRITE_TAC[BIT_WORD_OR_ALT]);;

let word_bit_and = prove
 (`!n w1 w2:N word. bit n (word_and w1 w2) <=> bit n w1 /\ bit n w2`,
  REWRITE_TAC[BIT_WORD_AND_ALT]);;

let WORD_NEG_1_T = prove
 (`!i. i < dimindex(:N) ==> bit i (word_neg (word 1):N word)`,
  REWRITE_TAC[WORD_NEG_1; BIT_WORD_NOT; BIT_WORD_0]);;

let word_arith_lemma1 = prove
 (`!n m x:N word.
     word_add (word n) (word m):N word = word (n + m) /\
     word_add (word_add x (word n)) (word m) = word_add x (word (n + m))
       /\
     word_sub (word_sub x (word n)) (word m) = word_sub x (word (n +
       m))`,
  REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE);;

let word_arith_lemma2 = prove
 (`!n m. word_sub (word n) (word m):N word =
         if n < m then word_neg (word (m - n)) else word (n - m)`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NOT_LT]) THEN
  ASM_SIMP_TAC[WORD_SUB; LT_IMP_LE] THEN CONV_TAC WORD_RULE);;

let word_arith_lemma4 = prove
 (`!x n m. word_sub (word_add x (word n)) (word m):N word =
           if n < m then word_sub x (word (m - n)) else word_add x (word
             (n - m))`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NOT_LT]) THEN
  ASM_SIMP_TAC[WORD_SUB; LT_IMP_LE] THEN CONV_TAC WORD_RULE);;

let WORD_EQ_ADD_RCANCEL = prove
 (`!v w x:N word. word_add v w = word_add x w <=> v = x`,
  MESON_TAC[WORD_RULE `!v w:N word. word_sub (word_add v w) w = v`]);;

let WORD_EQ_CANCEL_TAC =
  ONCE_REWRITE_TAC[GSYM WORD_SUB_EQ_0] THEN
  FIRST
   [MATCH_MP_TAC(MESON[] `!x y:N word. x = y ==> (x = word 0 <=> y =
     word 0)`) THEN
    CONV_TAC WORD_RULE;
    MATCH_MP_TAC(MESON[WORD_NEG_EQ_0]
      `!x y:N word. x = word_neg y ==> (x = word 0 <=> y = word 0)`)
        THEN
    CONV_TAC WORD_RULE];;

let WORD_EQ_ADD_CANCEL = prove
 (`!v w x:N word.
     (word_add v w = word_add x w <=> v = x) /\
     (word_add w v = word_add x w <=> v = x) /\
     (word_add v w = word_add w x <=> v = x) /\
     (word_add w v = word_add w x <=> v = x) /\
     (w = word_add x w <=> x = word 0) /\
     (word_add v w = w <=> v = word 0) /\
     (w = word_add w x <=> x = word 0) /\
     (word_add w v = w <=> v = word 0)`,
  REPEAT GEN_TAC THEN REPEAT CONJ_TAC THEN WORD_EQ_CANCEL_TAC);;

let n2w_and_1 = prove
 (`!n. word_and (word n) (word 1):N word = word (n MOD 2)`,
  GEN_TAC THEN REWRITE_TAC[WORD_AND_1; BIT_WORD; EXP; DIV_1] THEN
  REWRITE_TAC[DIMINDEX_GT_0] THEN
  MP_TAC(SPEC `n:num` ODD_MOD) THEN
  MP_TAC(SPECL [`n:num`; `2`] MOD_LT_EQ) THEN REWRITE_TAC[ARITH_EQ] THEN
  SPEC_TAC(`n MOD 2`,`r:num`) THEN GEN_TAC THEN
  ASM_CASES_TAC `ODD n` THEN ASM_REWRITE_TAC[] THEN
  REPEAT DISCH_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC);;

let word_LSL_n2w = prove
 (`!m k. word_shl (word m:N word) k = word (m * 2 EXP k)`,
  REWRITE_TAC[WORD_SHL_WORD; MULT_SYM]);;

let WORD_MUL_LSL = prove
 (`!a:N word n. word_shl a n = word_mul (word (2 EXP n)) a`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_shl] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM WORD_VAL] THEN
  REWRITE_TAC[GSYM WORD_MUL; MULT_SYM]);;

let w2n_lsr = VAL_WORD_USHR;;

let LSR_ADD = WORD_USHR_COMPOSE;;

let LSL_ONE = WORD_RULE
 `!w:N word. word_shl w 1 = word_add w w`;;

let word_1_lsl = prove
 (`!n. word_shl (word 1:N word) n = word (2 EXP n)`,
  REWRITE_TAC[WORD_SHL_WORD; MULT_CLAUSES]);;

let word_lsl_n2w = prove
 (`!n m. word_shl (word m:N word) n =
         if dimindex(:N) - 1 < n then word 0 else word (m * 2 EXP n)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_LSL_n2w] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[GSYM WORD_MOD_SIZE] THEN
  AP_TERM_TAC THEN REWRITE_TAC[MOD_0; MOD_EQ_0] THEN
  EXISTS_TAC `m * 2 EXP (n - dimindex(:N))` THEN
  REWRITE_TAC[GSYM MULT_ASSOC; GSYM EXP_ADD] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC);;

let WORD_ADD_LSL = prove
 (`!n a b:N word.
     word_shl (word_add a b) n = word_add (word_shl a n) (word_shl b
       n)`,
  REWRITE_TAC[WORD_MUL_LSL] THEN CONV_TAC WORD_RULE);;

let WORD_2COMP_LSL = prove
 (`!n a:N word. word_shl (word_neg a) n = word_neg (word_shl a n)`,
  REWRITE_TAC[WORD_MUL_LSL] THEN CONV_TAC WORD_RULE);;

let LSL_BITWISE = prove
 (`(!n v w:N word.
      word_and (word_shl w n) (word_shl v n) = word_shl (word_and w v)
        n) /\
   (!n v w:N word.
      word_or (word_shl w n) (word_shl v n) = word_shl (word_or w v) n)
        /\
   (!n v w:N word.
      word_xor (word_shl w n) (word_shl v n) = word_shl (word_xor w v)
        n)`,
  REWRITE_TAC[WORD_SHL_AND; WORD_SHL_OR; WORD_SHL_XOR]);;

let ASR_UINT_MAX = prove
 (`!n. word_ishr (word_UINT_MAX:N word) n = word_UINT_MAX`,
  GEN_TAC THEN REWRITE_TAC[GSYM IVAL_EQ; IVAL_WORD_ISHR] THEN
  SUBGOAL_THEN `ival(word_UINT_MAX:N word) = -- &1` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM IVAL_WORD_NEG_1; IVAL_EQ] THEN
    REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_UINT_MAX; VAL_WORD_NEG_1];
    MATCH_MP_TAC INT_DIV_UNIQ THEN EXISTS_TAC `(&2:int) pow n - &1` THEN
    REWRITE_TAC[INT_ABS_POW; INT_ABS_NUM] THEN
    MP_TAC(SPECL [`n:num`; `&2:int`] INT_POW_LE_1) THEN
      INT_ARITH_TAC]);;

let lsl_lsr = prove
 (`!w:N word n.
     val w * 2 EXP n < dimword(:N) ==> word_ushr (word_shl w n) n = w`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_USHR;
    VAL_WORD_SHL] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[dimword_def]) THEN
  ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_SIMP_TAC[MOD_LT] THEN
  SIMP_TAC[ONCE_REWRITE_RULE[MULT_SYM] DIV_MULT; EXP_2_NE_0]);;

let n2w_DIV = prove
 (`!a n. a < dimword(:N) ==> word (a DIV 2 EXP n):N word = word_ushr
   (word a) n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_ushr; VAL_WORD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[dimword_def]) THEN ASM_SIMP_TAC[MOD_LT]);;

let WORD_w2w_OVER_BITWISE = prove
 (`(!v w:A word. word_and (word_zx v) (word_zx w) = word_zx (word_and v
   w):B word) /\
   (!v w:A word. word_or (word_zx v) (word_zx w) = word_zx (word_or v
     w):B word) /\
   (!v w:A word. word_xor (word_zx v) (word_zx w) = word_zx (word_xor v
     w):B word)`,
  REWRITE_TAC[WORD_ZX_AND; WORD_ZX_OR; WORD_ZX_XOR]);;

let WORD_AND_EXP_SUB1 = prove
 (`!m n. word_and (word n) (word (2 EXP m - 1)):N word = word (n MOD 2
   EXP m)`,
  REWRITE_TAC[WORD_AND_MASK_WORD; VAL_WORD; MOD_MOD_EXP_MIN] THEN
  ONCE_REWRITE_TAC[GSYM WORD_MOD_SIZE] THEN REWRITE_TAC[MOD_MOD_EXP_MIN]
    THEN
  REPEAT GEN_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  ARITH_TAC);;

let NUMBIT_ADD_2EXP = prove
 (`!k a i. a < 2 EXP k ==> (numbit i (a + 2 EXP k) <=> i = k \/ numbit i
   a)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`2 EXP k * 1`; `a:num`] BITS_OF_NUM_ADD) THEN
  ASM_SIMP_TAC[DISJOINT_BITS_HILO; MULT_CLAUSES; BITS_OF_NUM_POW2] THEN
  DISCH_THEN(MP_TAC o AP_TERM `\s:num->bool. i IN s`) THEN
  REWRITE_TAC[IN_BITS_OF_NUM; GSYM numbit; IN_UNION; IN_SING;
    ADD_SYM]);;

let word_add_n2w = prove
 (`!m n. word_add (word m) (word n):N word = word (m + n)`,
  REWRITE_TAC[WORD_ADD]);;

let word_mul_n2w = prove
 (`!m n. word_mul (word m) (word n):N word = word (m * n)`,
  REWRITE_TAC[WORD_MUL]);;

let IVAL_NEG_VAL = prove
 (`!a:N word. ival a < &0 ==> &(val (word_neg a)) = --(ival a)`,
  GEN_TAC THEN REWRITE_TAC[GSYM MSB_IVAL; IVAL_VAL] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES; VAL_WORD_NEG_CASES] THEN
  UNDISCH_TAC `bit (dimindex(:N) - 1) (a:N word)` THEN
  REWRITE_TAC[MSB_VAL] THEN DISCH_TAC THEN
  MP_TAC(ISPEC `a:N word` VAL_BOUND) THEN
  MP_TAC(SPEC `dimindex(:N) - 1` EXP_2_NE_0) THEN
  COND_CASES_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REPEAT DISCH_TAC THEN ASM_SIMP_TAC[GSYM INT_OF_NUM_SUB; LT_IMP_LE]
    THEN
  REWRITE_TAC[INT_OF_NUM_POW] THEN INT_ARITH_TAC);;

let IVAL_POS_VAL = prove
 (`!a:N word. &0 <= ival a ==> &(val a) = ival a`,
  GEN_TAC THEN REWRITE_TAC[GSYM INT_NOT_LT; GSYM MSB_IVAL; IVAL_VAL]
    THEN
  SIMP_TAC[BITVAL_CLAUSES] THEN INT_ARITH_TAC);;

let word_quot_def = prove
 (`!a b:N word.
     word_jdiv a b =
     if word_msb a then
       if word_msb b then word_udiv (word_neg a) (word_neg b)
       else word_neg (word_udiv (word_neg a) b)
     else if word_msb b then word_neg (word_udiv a (word_neg b))
     else word_udiv a b`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[word_jdiv; imodular; word_div_def; word_msb; MSB_IVAL]
    THEN
  REWRITE_TAC[WORD_IWORD; GSYM INT_OF_NUM_DIV; GSYM IWORD_INT_NEG] THEN
  MP_TAC(ISPEC `a:N word` IVAL_NEG_VAL) THEN MP_TAC(ISPEC `b:N word`
    IVAL_NEG_VAL) THEN
  MP_TAC(ISPEC `a:N word` IVAL_POS_VAL) THEN MP_TAC(ISPEC `b:N word`
    IVAL_POS_VAL) THEN
  SPEC_TAC(`&(val(word_neg(a:N word))):int`,`na:int`) THEN
  SPEC_TAC(`&(val(word_neg(b:N word))):int`,`nb:int`) THEN
  SPEC_TAC(`&(val(a:N word)):int`,`va:int`) THEN
  SPEC_TAC(`&(val(b:N word)):int`,`vb:int`) THEN
  SPEC_TAC(`ival(a:N word)`,`x:int`) THEN SPEC_TAC(`ival(b:N
    word)`,`y:int`) THEN
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `x:int < &0` THEN ASM_CASES_TAC `y:int < &0` THEN
  ASM_REWRITE_TAC[GSYM INT_NOT_LT] THEN
  REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
  REWRITE_TAC[INT_SGN; INT_ABS] THEN
  ASM_REWRITE_TAC[GSYM INT_NOT_LT] THEN
  ASM_CASES_TAC `x:int = &0` THEN ASM_CASES_TAC `y:int = &0` THEN
  ASM_REWRITE_TAC[INT_DIV_0; INT_DIV_ZERO; INT_NEG_0; INT_LT_REFL] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[INT_NOT_LT]) THEN
  ASM_SIMP_TAC[INT_ARITH `x:int < &0 ==> ~(&0 < x)`;
               INT_ARITH `&0 <= x /\ ~(x = &0) ==> &0 < x`] THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  TRY INT_ARITH_TAC THEN ASM_INT_ARITH_TAC);;

let int_mod = prove
 (`!i j. ~(j = &0) ==> integer_int_mod i j = i - int_div i j * j`,
  REWRITE_TAC[integer_int_mod]);;

let INT_MUL_CALCULATE = prove
 (`(!m n. &m * &n:int = &(m * n)) /\
   (!x y:int. --x * y = --(x * y)) /\
   (!x y:int. x * --y = --(x * y)) /\
   (!x:int. --(--x) = x)`,
  REWRITE_TAC[INT_OF_NUM_MUL; INT_MUL_LNEG; INT_MUL_RNEG;
    INT_NEG_NEG]);;

let INT_ADD = INT_OF_NUM_ADD;;

let INT_MUL = INT_OF_NUM_MUL;;

let INT_MUL_COMM = INT_MUL_SYM;;

let INT_EQ_NEG = INT_EQ_NEG2;;

let INT_ABS_EQ_ID = INT_ABS_REFL;;

let integer_NUM_OF_INT = NUM_OF_INT_OF_NUM;;

let integer_INT_LT = prove
 (`!m n. &m:int < &n <=> m < n`,
  REWRITE_TAC[INT_OF_NUM_LT]);;

let integer_INT_SUB = prove
 (`!n m. m <= n ==> &n - &m:int = &(n - m)`,
  SIMP_TAC[INT_OF_NUM_SUB]);;

let integer_INT_ABS = prove
 (`!n:int. abs n = if n < &0 then --n else n`,
  INT_ARITH_TAC);;

let integer_int_le = prove
 (`!x y:int. x <= y <=> ~(y < x)`,
  INT_ARITH_TAC);;

let integer_int_ge = INT_GE;;

let integer_int_gt = INT_GT;;

let integer_int_sub = INT_SUB;;

let INT_OF_NUM = prove
 (`!i. &(num_of_int i) = i <=> &0 <= i`,
  MESON_TAC[NUM_OF_INT]);;

let NUM_POSINT_EXISTS = prove
 (`!i:int. &0 <= i ==> ?n. i = &n`,
  REWRITE_TAC[GSYM INT_OF_NUM_EXISTS]);;

let INT_LDISTRIB = prove
 (`!z y x:int. x * (y + z) = x * y + x * z`,
  REWRITE_TAC[INT_ADD_LDISTRIB]);;

let INT_LE_LT1 = prove
 (`!x y:int. x <= y <=> x < y + &1`,
  INT_ARITH_TAC);;

let INT = prove
 (`!n. &(SUC n):int = &n + &1`,
  REWRITE_TAC[INT_OF_NUM_SUC]);;

let EQ_ADDL = prove
 (`!x y. x = x + y <=> y = 0`,
  ARITH_TAC);;

let integer_word_INT_MAX_def = prove
 (`integer_word_INT_MAX(:A) = &(INT_MIN(:A)) - &1`,
  REWRITE_TAC[integer_word_INT_MAX]);;

let integer_word_INT_MIN_def = prove
 (`integer_word_INT_MIN(:A) = --integer_word_INT_MAX(:A) - &1`,
  REWRITE_TAC[integer_word_INT_MIN]);;

let IVAL_IWORD_INT_RANGE = prove
 (`!i. integer_word_INT_MIN(:N) <= i /\ i <= integer_word_INT_MAX(:N)
   <=>
       --(&2 pow (dimindex(:N) - 1)) <= i /\ i < &2 pow (dimindex(:N) -
         1)`,
  REWRITE_TAC[integer_word_INT_MIN_def; integer_word_INT_MAX_def;
    INT_MIN_def] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_POW] THEN INT_ARITH_TAC);;

let i2w_def = prove
 (`!i. iword i:N word =
       if i < &0 then word_neg (word (num_of_int (--i))) else word
         (num_of_int i)`,
  GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[WORD_IWORD] THENL
   [SUBGOAL_THEN `&(num_of_int(--i)) = --i` SUBST1_TAC THENL
     [MATCH_MP_TAC INT_OF_NUM_OF_INT THEN ASM_INT_ARITH_TAC;
      REWRITE_TAC[GSYM IWORD_INT_NEG; INT_NEG_NEG]];
    SUBGOAL_THEN `&(num_of_int i) = i` SUBST1_TAC THENL
     [MATCH_MP_TAC INT_OF_NUM_OF_INT THEN ASM_INT_ARITH_TAC;
       REFL_TAC]]);;

let w2i_def = prove
 (`!w:N word. ival w = if word_msb w then --(&(val (word_neg w))) else
   &(val w)`,
  GEN_TAC THEN REWRITE_TAC[word_msb; MSB_IVAL] THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[IVAL_NEG_VAL; INT_NEG_NEG] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC IVAL_POS_VAL THEN
    ASM_INT_ARITH_TAC);;

let w2i_i2w = prove
 (`!i. integer_word_INT_MIN(:N) <= i /\ i <= integer_word_INT_MAX(:N)
       ==> ival (iword i:N word) = i`,
  REWRITE_TAC[IVAL_IWORD_INT_RANGE; IVAL_IWORD]);;

let word_0_w2i = IVAL_WORD_0;;

let word_i2w_add = prove
 (`!a b. word_add (iword a) (iword b):N word = iword (a + b)`,
  REWRITE_TAC[IWORD_INT_ADD]);;

let word_i2w_mul = prove
 (`!a b. word_mul (iword a) (iword b):N word = iword (a * b)`,
  REWRITE_TAC[IWORD_INT_MUL]);;

let i2w_pos = prove
 (`!n. iword (&n):N word = word n`,
  REWRITE_TAC[WORD_IWORD]);;

let i2w_w2n_w2w = prove
 (`!w:A word. iword (&(val w)):B word = word_zx w`,
  REWRITE_TAC[GSYM WORD_IWORD; word_zx]);;

let MULT_MINUS_ONE = prove
 (`!i. word_mul (word_neg (word 1)) (iword i):N word = iword (--i)`,
  REWRITE_TAC[IWORD_INT_NEG] THEN CONV_TAC WORD_RULE);;

let w2w_i2w = prove
 (`!i. dimindex(:A) <= dimindex(:B)
       ==> word_zx (iword i:B word):A word = iword i`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_zx; WORD_IWORD; IWORD_EQ] THEN
  MP_TAC(ISPEC `i:int` (INST_TYPE [`:B`,`:N`] VAL_IWORD_CONG)) THEN
  SUBGOAL_THEN `(&2:int) pow dimindex(:A) divides &2 pow dimindex(:B)`
    MP_TAC THENL
   [REWRITE_TAC[int_divides] THEN EXISTS_TAC `(&2:int) pow (dimindex(:B)
     - dimindex(:A))` THEN
    REWRITE_TAC[GSYM INT_POW_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
    CONV_TAC INTEGER_RULE]);;

let NUMBIT_MUL_2EXP = prove
 (`!i k n. numbit i (n * 2 EXP k) <=> k <= i /\ numbit (i - k) n`,
  REPEAT GEN_TAC THEN
  MP_TAC(AP_TERM `\s:num->bool. i IN s` (SPECL [`n:num`; `k:num`]
    (CONJUNCT2 BITS_OF_NUM_MUL))) THEN
  REWRITE_TAC[IN_BITS_OF_NUM; GSYM numbit; IN_IMAGE] THEN
  DISCH_THEN SUBST1_TAC THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[ADD_SUB2; LE_ADD];
    STRIP_TAC THEN EXISTS_TAC `i - k:num` THEN ASM_REWRITE_TAC[] THEN
    ASM_ARITH_TAC]);;

let ZERO_LT_INT_MIN = prove
 (`0 < INT_MIN(:N)`,
  REWRITE_TAC[INT_MIN_def; ZERO_LT_TWOEXP]);;

let ZERO_LT_UINT_MAX = prove
 (`0 < UINT_MAX(:N)`,
  REWRITE_TAC[UINT_MAX_def] THEN MP_TAC ONE_LT_dimword THEN ARITH_TAC);;

let w2n_eq_0 = prove
 (`!w:N word. val w = 0 <=> w = word 0`,
  REWRITE_TAC[VAL_EQ_0]);;

let WORD_NOT_XOR = prove
 (`!a b:N word.
     word_xor (word_not a) (word_not b) = word_xor a b /\
     word_xor a (word_not b) = word_not (word_xor a b) /\
     word_xor (word_not a) b = word_not (word_xor a b)`,
  REPEAT GEN_TAC THEN REPEAT CONJ_TAC THEN WORD_BITWISE_TAC);;

let WORD_AND_ABSORD = prove
 (`!a b:N word. word_or a (word_and a b) = a`,
  WORD_BITWISE_TAC);;

let WORD_AND_COMP = prove
 (`!a:N word. word_and a (word_not a) = word 0`,
  WORD_BITWISE_TAC);;

let w2w_id = WORD_ZX_TRIVIAL;;

let sw2sw_id = WORD_SX_TRIVIAL;;

let WORD_SUB_RZERO = WORD_SUB_0;;

let WORD_LCANCEL_SUB = prove
 (`!v w x:N word. word_sub v w = word_sub x w <=> v = x`,
  MESON_TAC[WORD_RULE `!v w:N word. word_add (word_sub v w) w = v`]);;

let WORD_RCANCEL_SUB = prove
 (`!v w x:N word. word_sub v w = word_sub v x <=> w = x`,
  MESON_TAC[WORD_RULE `!v w:N word. word_sub v (word_sub v w) = w`]);;

let WORD_ADD_LID_UNIQ = prove
 (`!v w:N word. word_add v w = w <=> v = word 0`,
  REWRITE_TAC[WORD_ADD_EQ_SUB; WORD_SUB_REFL]);;

let WORD_ADD_RID_UNIQ = prove
 (`!v w:N word. word_add v w = v <=> w = word 0`,
  REWRITE_TAC[WORD_ADD_INV_0_EQ]);;

let WORD_NEG1_MUL_LCANCEL = prove
 (`!v w:N word.
     word_mul (word_neg (word 1)) v = word_mul (word_neg (word 1)) w <=>
       v = w`,
  REWRITE_TAC[GSYM WORD_NEG_MUL; WORD_EQ_NEG]);;

let WORD_NEG1_MUL_RCANCEL = prove
 (`!v w:N word.
     word_mul v (word_neg (word 1)) = word_mul w (word_neg (word 1)) <=>
       v = w`,
  ONCE_REWRITE_TAC[WORD_MUL_SYM] THEN
    REWRITE_TAC[WORD_NEG1_MUL_LCANCEL]);;

let WORD_LESS_EQ_REFL = prove
 (`!a:N word. word_ile a a`,
  REWRITE_TAC[WORD_ILE; INT_LE_REFL]);;

let WORD_LOWER_EQ_REFL = prove
 (`!a:N word. word_ule a a`,
  REWRITE_TAC[WORD_ULE; LE_REFL]);;

let WORD_LS_word_0 = prove
 (`!n:N word. word_ule n (word 0) <=> n = word 0`,
  REWRITE_TAC[WORD_ULE; VAL_WORD_0; GSYM VAL_EQ_0] THEN ARITH_TAC);;

let WORD_LO_word_0R = CONJUNCT2 WORD_LO_word_0;;

let word_T_not_zero = prove
 (`~(word_neg (word 1):N word = word 0)`,
  REWRITE_TAC[WORD_NEG_EQ_0; GSYM VAL_EQ_0; VAL_WORD_1; ARITH_EQ]);;

let WORD_LS_word_T = prove
 (`(!n:N word. word_ule (word_neg (word 1)) n <=> n = word_neg (word 1))
   /\
   (!n:N word. word_ule n (word_neg (word 1)))`,
  REWRITE_TAC[WORD_ULE; GSYM VAL_EQ; VAL_WORD_NEG_1] THEN
  CONJ_TAC THEN GEN_TAC THEN MP_TAC(ISPEC `n:N word` VAL_BOUND) THEN
    ARITH_TAC);;

let WORD_LO_word_T_L = CONJUNCT1 WORD_LO_word_T;;

let WORD_LO_word_T_R = prove
 (`!n:N word. ~(word_ult n (word_neg (word 1))) <=> n = word_neg (word
   1)`,
  REWRITE_TAC[WORD_LO_word_T] THEN MESON_TAC[]);;

let WORD_LESS_0_word_T = prove
 (`~(word_ilt (word 0) (word_neg (word 1):N word)) /\
   ~(word_ile (word 0) (word_neg (word 1):N word)) /\
   word_ilt (word_neg (word 1)) (word 0:N word) /\
   word_ile (word_neg (word 1)) (word 0:N word)`,
  REWRITE_TAC[WORD_ILT; WORD_ILE; IVAL_WORD_0; IVAL_WORD_NEG_1] THEN
    INT_ARITH_TAC);;

let SIZES_DIMWORD = prove
 (`dimword(:1) = 2 /\
   dimword(:(A)tybit0) = dimword(:A) * dimword(:A) /\
   dimword(:(A)tybit1) = 2 * dimword(:A) * dimword(:A)`,
  REWRITE_TAC[dimword_def; DIMINDEX_1; DIMINDEX_TYBIT0; DIMINDEX_TYBIT1]
    THEN
  REWRITE_TAC[ARITH_RULE `2 * d = d + d`; EXP_ADD; EXP_1] THEN CONV_TAC
    NUM_RING);;

let SIZES_INT_MIN = prove
 (`INT_MIN(:1) = 1 /\
   INT_MIN(:(A)tybit0) = dimword(:(A)tybit0) DIV 2 /\
   INT_MIN(:(A)tybit1) = dimword(:(A)tybit1) DIV 2`,
  REWRITE_TAC[dimword_IS_TWICE_INT_MIN; ARITH_RULE `(2 * n) DIV 2 = n`]
    THEN
  REWRITE_TAC[INT_MIN_def; DIMINDEX_1] THEN CONV_TAC NUM_REDUCE_CONV);;

let SIZES_THMS = prove
 (`dimindex(:1) = 1 /\
   dimindex(:(A)tybit0) = 2 * dimindex(:A) /\
   dimindex(:(A)tybit1) = 2 * dimindex(:A) + 1 /\
   dimword(:1) = 2 /\
   dimword(:(A)tybit0) = dimword(:A) * dimword(:A) /\
   dimword(:(A)tybit1) = 2 * dimword(:A) * dimword(:A) /\
   INT_MIN(:1) = 1 /\
   INT_MIN(:(A)tybit0) = dimword(:(A)tybit0) DIV 2 /\
   INT_MIN(:(A)tybit1) = dimword(:(A)tybit1) DIV 2 /\
   INT_MAX(:1) = 0 /\
   INT_MAX(:(A)tybit0) = INT_MIN(:(A)tybit0) - 1 /\
   INT_MAX(:(A)tybit1) = INT_MIN(:(A)tybit1) - 1 /\
   UINT_MAX(:1) = 1 /\
   UINT_MAX(:(A)tybit0) = dimword(:(A)tybit0) - 1 /\
   UINT_MAX(:(A)tybit1) = dimword(:(A)tybit1) - 1`,
  REWRITE_TAC[DIMINDEX_1; DIMINDEX_TYBIT0; DIMINDEX_TYBIT1;
    SIZES_DIMWORD;
              SIZES_INT_MIN; INT_MAX_def; UINT_MAX_def] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* What this port cannot take from LightCake's words4
   yet, with the names of its own that each proof
   uses:

     BITS_THM                         -- Exception: Failure "TAC_PROOF:
                                      Unsolved goals".
     LOG                              LOG_DEF
     LOG2_PROPERTY                    LOG LOG2_def
     LOG2_UNIQUE                      LOG2_PROPERTY
     LOG2_TWOEXP                      LOG2_UNIQUE
     BIT_def                          -- Error: Unbound value BITS_THM
     BITS_THM2                        -- Error: Unbound value BITS_THM
     BITS_ZEROL                       -- Error: Unbound value BITS_THM
     BITSLT_THM                       -- Error: Unbound value BITS_THM
     BITSLT_THM2                      -- Error: Unbound value BITSLT_THM
     NOT_BITS2                        -- Error: Unbound value BITSLT_THM
     NUMBIT_BITS                      -- Error: Unbound value BITS_THM
     BIT_OF_BITS_THM                  -- Error: Unbound value
                                      NUMBIT_BITS
     BIT_BITS_THM                     -- Error: Unbound value
                                      NUMBIT_BITS
     BIT_COMP_THM3                    -- Error: Unbound value BITS_THM
     BIT_LOG2                         LOG2_PROPERTY
     LT_TWOEXP                        LOG2_PROPERTY
     word_slice_def                   -- Exception: Failure "TAC_PROOF:
                                      Unsolved goals".
     word_bits_def                    -- Exception: Failure "TAC_PROOF:
                                      Unsolved goals".
     word_extract_def                 M word_extract_DEF
     w2w                              M
     BIT_WORD_BITS                    -- Exception: Failure
     BIT_WORD_EXTRACT                 BIT_WORD_BITS M word_extract_DEF
     VAL_WORD_BITS                    -- Error: Unbound value
                                      BIT_WORD_BITS
     word_bits_subword                -- Error: Unbound value
                                      BIT_WORD_BITS
     word_extract_subword             BIT_WORD_EXTRACT M
     word_bits_n2w                    -- Error: Unbound value
                                      BIT_WORD_BITS
     w2w_n2w                          M NUMBIT_BITS
     word_extract_n2w                 M NUMBIT_BITS w2w_n2w
                                      word_bits_n2w word_extract_DEF
     WORD_BITS_EXTRACT                BIT_WORD_BITS BIT_WORD_EXTRACT
     WORD_w2w_EXTRACT                 BIT_WORD_EXTRACT M
     WORD_ALL_BITS                    -- Error: Unbound value
                                      BIT_WORD_BITS
     WORD_BITS_COMP_THM               -- Error: Unbound value
                                      BIT_WORD_BITS
     w2w_w2w                          -- Error: Unbound value
                                      BIT_WORD_BITS
     word_bits_w2w                    BIT_WORD_BITS M
     w2n_w2w                          BITS_THM M VAL_WORD_BITS
     BIT_ATOM_CASES_TAC               failwith term
     WORD_EXTRACT_COMP_THM            BIT_ATOM_CASES_TAC
                                      BIT_WORD_EXTRACT
     WORD_EXTRACT_BITS_COMP           BIT_ATOM_CASES_TAC BIT_WORD_BITS
                                      BIT_WORD_EXTRACT M
     WORD_EXTRACT_MIN_HIGH            BIT_ATOM_CASES_TAC
                                      BIT_WORD_EXTRACT
     WORD_EXTRACT_ID                  BIT_WORD_EXTRACT
     WORD_EXTRACT_LSL2                BIT_ATOM_CASES_TAC
                                      BIT_WORD_EXTRACT
     WORD_EXTRACT_ZX                  BIT_WORD_EXTRACT
     WORD_EXTRACT_OVER_ADD            WORD_EXTRACT_ZX
     WORD_EXTRACT_OVER_MUL            WORD_EXTRACT_ZX
     WORD_EXTRACT_OVER_BITWISE        BIT_WORD_EXTRACT
     WORD_w2w_OVER_MUL                -- Error: Unbound value
                                      VAL_WORD_BITS
     word_lsr_n2w                     BIT_ATOM_CASES_TAC BIT_WORD_BITS
     WORD_BITS_LSL                    BIT_ATOM_CASES_TAC BIT_WORD_BITS
     w2w_LSL                          BIT_ATOM_CASES_TAC BIT_WORD_BITS
     BITWISE_LT_2EXP                  BITWISE_def SBIT_def
     NUMBIT_BITWISE                   BITWISE_LT_2EXP BITWISE_def
                                      SBIT_def
     word_and_n2w                     NUMBIT_BITWISE
     word_concat_def                  M
     word_join_def                    BIT_ATOM_CASES_TAC M
     word_ror_n2w                     -- Error: Unbound value BITS_THM
     INT_DIV                          -- Exception: Failure "TAC_PROOF:
                                      Unsolved goals".
     INT_DIV_NEG                      -- Exception: Failure "TAC_PROOF:
                                      Unsolved goals".
     INT_DIV_UNIQUE                   -- Exception: Failure
                                      "MATCH_MP_TAC: No match".
     INT_DIV_LMUL                     -- Exception: Failure "TAC_PROOF:
                                      Unsolved goals".
     INT_MOD                          -- Exception: Failure
     INT_MOD0                         -- Exception: Failure
     INT_DIV_CALCULATE                -- Error: Unbound value INT_DIV
     integer_word_UINT_MAX_def        integer_word_UINT_MAX_DEF
     w2n_i2w                          -- Exception: Failure
     i2w_DIV                          -- Exception: Failure "TAC_PROOF:
                                      Unsolved goals".
     byte_index_def                   byte_index_DEF
     get_byte_def                     get_byte_DEF
     word_slice_alt_def               -- Exception: Failure "TAC_PROOF:
                                      Unsolved goals".
     set_byte_def                     set_byte_DEF
     word_of_bytes_def                CONS word_of_bytes_DEF
     bytes_to_word_def                bytes_to_word_DEF list_CASE
     set_byte_change_a                byte_index_DEF set_byte_DEF
     bytes_to_word_eq                 CONS bytes_to_word_def list_CASE
     bytes_to_word_same               bytes_to_word_eq
     BYTE_INDEX_BOUND                 byte_index_DEF
     get_byte_set_byte                BYTE_INDEX_BOUND get_byte_DEF
                                      set_byte_DEF
     word_to_bytes_aux_def            word_to_bytes_aux_DEF
     word_to_bytes_def                word_to_bytes_DEF
     align_def                        align_DEF
     aligned_def                      aligned_DEF
     byte_align_def                   byte_align_DEF
     byte_aligned_def                 byte_aligned_DEF
     BIT_ALIGN                        BIT_ATOM_CASES_TAC align_DEF
     align_w2n                        BIT_ALIGN
     align_shift                      BIT_ALIGN
     aligned_w2n                      align_w2n aligned_DEF
     align_align_MAX                  BIT_ALIGN
     align_align                      align_align_MAX
     aligned_align                    align_align aligned_DEF
     align_aligned                    aligned_DEF
     aligned_0                        BIT_ALIGN aligned_DEF
     aligned_extract                  BIT_ALIGN BIT_WORD_EXTRACT
                                      aligned_DEF
     aligned_bitwise_and              aligned_w2n
     MOD_0_aligned                    aligned_w2n
     aligned_lsl_leq                  MOD_0_aligned
     aligned_ge_dim                   aligned_w2n
     aligned_hol_light                aligned_w2n
     aligned_add_sub                  aligned_ge_dim aligned_hol_light
     aligned_add_sub_cor              aligned_add_sub
     byte_aligned_add                 aligned_add_sub_cor
                                      byte_aligned_DEF
     aligned_mul_shift_1              aligned_0 aligned_hol_light
     aligned_pow2                     MOD_0_aligned
     aligned_add_pow                  MOD_0_aligned aligned_add_sub
                                      aligned_pow2
     align_ls                         align_w2n
     VAL_ALIGN                        align_w2n
     aligned_between                  VAL_ALIGN aligned_w2n
     align_add_aligned                VAL_ALIGN align_w2n aligned_ge_dim
                                      aligned_w2n
     align_add_aligned_gen            MOD_0_aligned align_add_aligned
                                      align_w2n aligned_add_sub_cor
     FCP_T_F                          K_THM
     word_lo_def                      nzcv_DEF v
     word_lt_def                      nzcv_DEF v
     LOG2_CONV                        Comb Const LOG2_UNIQUE Num _
                                      failwith find power_num
     _                                FCP_T_F aligned_add_pow
                                      cake_add_simps

*)
