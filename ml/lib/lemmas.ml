(* ================================================================== *)
(*  The lemmas that the proofs of phase three need and that neither   *)
(*  HOL Light nor the ported library theories have.                   *)
(*                                                                    *)
(*  This file defines nothing, so it can be loaded again into a       *)
(*  running session (tools/bin/reload), where a change in             *)
(*  ml/lib/hol4.ml costs the session.  A lemma that a single proof    *)
(*  needs stays in that proof; this is for the ones that the files    *)
(*  share.                                                            *)
(* ================================================================== *)

(* HOL4's EL_DROP, which the proofs of the port need and which HOL
   Light has not (it has no DROP of its own) *)

let EL_DROP = prove
 (`!l n k. n + k < LENGTH l ==> EL n (DROP k l) = EL (n + k) l`,
  LIST_INDUCT_TAC THENL
  [REWRITE_TAC[LENGTH; LT];
   REPEAT GEN_TAC THEN
   STRUCT_CASES_TAC(SPEC `k:num` num_CASES) THEN
   REWRITE_TAC[DROP; LENGTH; EL; TL; ADD_CLAUSES; ARITH_EQ;
               NOT_SUC; SUC_SUB1; LT_SUC] THEN
   DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
   ASM_REWRITE_TAC[]]);;

(* HOL4's LLOOKUP_EQ_EL, and the step over an APPEND that its
   proofs take with EL_APPEND2: oEL is HOL4's LLOOKUP, and
   ml/lib/hol4.ml defines it, so the lemmas about it come here *)

let oEL_EL = prove
 (`!l n. n < LENGTH l ==> oEL n l = SOME (EL n l)`,
  LIST_INDUCT_TAC THENL
  [REWRITE_TAC[LENGTH; LT];
   REPEAT GEN_TAC THEN
   STRUCT_CASES_TAC(SPEC `n:num` num_CASES) THEN
   REWRITE_TAC[oEL; LENGTH; EL; TL; HD; ARITH_EQ; NOT_SUC;
               SUC_SUB1; LT_SUC] THEN
   DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
   ASM_REWRITE_TAC[]]);;

let oEL_APPEND = prove
 (`!l m i. oEL (i + LENGTH l) (APPEND l m) = oEL i m`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; APPEND; ADD_CLAUSES; oEL; NOT_SUC;
              SUC_SUB1] THEN
  ASM_REWRITE_TAC[]);;

(* the two size facts that a measure induction over a definition
   which recurses on BUTLAST and LAST needs (HOL4 gets them from
   its own size simp set) *)

let list_size_BUTLAST = prove
 (`!(f:A->num) l. list_size f (BUTLAST l) <= list_size f l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[BUTLAST; list_size; LE_REFL] THEN
  COND_CASES_TAC THEN REWRITE_TAC[list_size; LE_0] THEN
  ASM_ARITH_TAC);;

let list_size_LAST = prove
 (`!(f:A->num) l. ~(l = []) ==> f (LAST l) <= list_size f l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[NOT_CONS_NIL; LAST; list_size] THEN
  COND_CASES_TAC THENL
  [ARITH_TAC;
   FIRST_ASSUM(fun ih -> FIRST_ASSUM(fun c ->
     MP_TAC(MATCH_MP ih c))) THEN ARITH_TAC]);;

(* and the other direction of HOL4's LLOOKUP_EQ_EL *)

let oEL_SOME = prove
 (`!l n x. oEL n l = SOME x ==> n < LENGTH l /\ EL n l = x`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[oEL; distinctness "option"] THEN
  STRUCT_CASES_TAC(SPEC `n:num` num_CASES) THEN
  REWRITE_TAC[oEL; ARITH_EQ; NOT_SUC; SUC_SUB1; LENGTH; EL; TL;
              HD; LT_0; LT_SUC; injectivity "option"] THEN
  FIRST_ASSUM MATCH_ACCEPT_TAC);;

(* HOL4's DROP_0: the clauses of DROP decide on the number, so
   DROP 0 of a list that is a variable does not reduce *)

let DROP_0 = prove
 (`!l:A list. DROP 0 l = l`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[DROP]);;

(* HOL4's SNOC and its laws.  ml/lib/hol4.ml defines SNOC, because
   a few sources define a function by recursion on one, and HOL4
   carries some seventy lemmas about it that HOL Light has none of.
   These are the ones a proof needs to read the front and the last
   expression off a list that a pass recurses on
   (PORTING-GUIDE.md entry 15); BUTLAST is HOL Light's name for
   what the sources call FRONT. *)

let SNOC_APPEND = prove
 (`!(l:A list) x. SNOC x l = APPEND l [x]`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[SNOC; APPEND]);;

let NOT_SNOC_NIL = prove
 (`!(l:A list) x. ~(SNOC x l = [])`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[SNOC; NOT_CONS_NIL]);;

let SNOC_CASES = prove
 (`!l:A list. ~(l = []) ==> ?x y. l = SNOC x y`,
  GEN_TAC THEN DISCH_TAC THEN
  EXISTS_TAC `LAST (l:A list)` THEN
  EXISTS_TAC `BUTLAST (l:A list)` THEN
  REWRITE_TAC[SNOC_APPEND] THEN
  FIRST_ASSUM(fun th ->
    REWRITE_TAC[MATCH_MP APPEND_BUTLAST_LAST th]));;

let FRONT_SNOC = prove
 (`!(l:A list) x. BUTLAST (SNOC x l) = l`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[SNOC; BUTLAST; NOT_SNOC_NIL]);;

let LAST_SNOC = prove
 (`!(l:A list) x. LAST (SNOC x l) = x`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[SNOC; LAST; NOT_SNOC_NIL]);;

let LENGTH_SNOC = prove
 (`!(l:A list) x. LENGTH (SNOC x l) = LENGTH l + 1`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[SNOC; LENGTH] THEN
  ARITH_TAC);;

(* and the size of one, which the measure of such an induction
   asks for and HOL4 gets from its own size simp set *)

let list_size_SNOC = prove
 (`!(f:A->num) x l.
     list_size f (SNOC x l) = list_size f l + (f x + 1)`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[SNOC; list_size] THEN ARITH_TAC);;

(* the value that a Var reads when a pass has moved an expression
   into tail-position: the first one past the front of the list *)

let EL_LEN_APPEND = prove
 (`!(a:A list) v l. EL (LENGTH a) (APPEND a (CONS v l)) = v`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[LENGTH; APPEND; EL; HD; TL]);;

(* ------------------------------------------------------------------ *)
(* NULL as an equation, which HOL4 has as NULL_EQ of listTheory, and  *)
(* the list cases with names that an induction has not taken.         *)
(* ------------------------------------------------------------------ *)

let NULL_EQ = prove
 (`!l:A list. NULL l <=> l = []`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[NULL; NOT_CONS_NIL]);;

let list_CASES_v = prove
 (`!l:A list. l = [] \/ (?v vs. l = CONS v vs)`,
  MESON_TAC[list_CASES]);;

(* ------------------------------------------------------------------ *)
(* The finite maps of HOL4's finite_mapTheory: the port has the       *)
(* definitions (ml/lib/finite_map.ml), and a proof needs the facts    *)
(* about the representing function that they are phrased with.        *)
(* ------------------------------------------------------------------ *)

let FMAP_FN_FINITE = prove
 (`!fm:(A,B)fmap. FINITE {x | ~(fmap_fn fm x = NONE)}`,
  GEN_TAC THEN ONCE_REWRITE_TAC[CONJUNCT2 fmap_tybij] THEN
  REWRITE_TAC[ETA_AX; CONJUNCT1 fmap_tybij]);;

let FMAP_FN_FUPDATE = prove
 (`!(fm:(A,B)fmap) kv.
     fmap_fn (fm |+ kv) =
     (\x. if x = FST kv then SOME (SND kv) else fmap_fn fm x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FUPDATE] THEN
  REWRITE_TAC[GSYM(CONJUNCT2 fmap_tybij)] THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC
    `(FST (kv:A#B)) INSERT
     {x | ~(fmap_fn (fm:(A,B)fmap) x = NONE)}` THEN
  REWRITE_TAC[FINITE_INSERT; FMAP_FN_FINITE] THEN
  REWRITE_TAC[SUBSET; IN_INSERT; IN_ELIM_THM] THEN
  GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

let FAPPLY_FUPDATE_THM = prove
 (`!(fm:(A,B)fmap) k v x.
     FAPPLY (fm |+ (k,v)) x = (if x = k then v else FAPPLY fm x)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[fmap_apply; FMAP_FN_FUPDATE; FST; SND] THEN
  COND_CASES_TAC THEN REWRITE_TAC[THE]);;

(* the range of a finite map, which HOL4 has as IN_FRANGE of
   finite_mapTheory; the port cannot have that name, because CakeML
   has a theorem of its own called IN_FRANGE (copying_gc.ml) *)

let FMAP_IN_FRANGE = prove
 (`!(f:(A,B)fmap) v.
     v IN FRANGE f <=> ?k. k IN FDOM f /\ FAPPLY f k = v`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[FRANGE; FDOM; fmap_apply; IN_ELIM_THM] THEN
  EQ_TAC THEN STRIP_TAC THENL
   [EXISTS_TAC `k:A` THEN
    ASM_REWRITE_TAC[THE; distinctness "option"];
    EXISTS_TAC `k:A` THEN
    REPEAT(FIRST_X_ASSUM MP_TAC) THEN
    STRUCT_CASES_TAC(ISPEC `fmap_fn (f:(A,B)fmap) k`
                           (cases_of `:(B)option`)) THEN
    REWRITE_TAC[THE; injectivity "option"; distinctness "option"] THEN
    MESON_TAC[]]);;

(* and the reflexivity of SUBMAP, which HOL4 has as SUBMAP_REFL *)

let SUBMAP_REFL = prove
 (`!f:(A,B)fmap. f SUBMAP f`,
  REWRITE_TAC[SUBMAP]);;

(* ------------------------------------------------------------------ *)
(* The list lemmas of HOL4 that a proof of phase three asks for and   *)
(* HOL Light does not have: the pointwise reading of LIST_REL, and    *)
(* the split of a bounded quantifier that it needs.                   *)
(* ------------------------------------------------------------------ *)

let FORALL_LT_SUC = prove
 (`!P m. (!n. n < SUC m ==> P n) <=>
         P 0 /\ (!n. n < m ==> P (SUC n))`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN CONJ_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
      REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
      ASM_ARITH_TAC];
    STRIP_TAC THEN X_GEN_TAC `n:num` THEN
    STRUCT_CASES_TAC(SPEC `n:num` num_CASES) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

let LIST_REL_EL_EQN = prove
 (`!(R:A->B->bool) l1 l2.
     ALL2 R l1 l2 <=>
     LENGTH l1 = LENGTH l2 /\
     (!n. n < LENGTH l1 ==> R (EL n l1) (EL n l2))`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN X_GEN_TAC `l2:B list` THEN
  STRUCT_CASES_TAC(ISPEC `l2:B list` list_CASES_v) THEN
  ASM_REWRITE_TAC[ALL2; LENGTH; CONJUNCT1 LT; SUC_INJ; FORALL_LT_SUC;
                  EL; HD; TL; ARITH_RULE `~(0 = SUC n)`;
                  ARITH_RULE `~(SUC n = 0)`] THEN
  CONV_TAC TAUT);;

(* and the domain of an update, HOL4's FDOM_FUPDATE *)

let FDOM_FUPDATE = prove
 (`!(f:(A,B)fmap) k v. FDOM (f |+ (k,v)) = k INSERT FDOM f`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[FDOM; FMAP_FN_FUPDATE; FST; SND; EXTENSION;
              IN_INSERT; IN_ELIM_THM] THEN
  GEN_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[distinctness "option"]);;

(* ------------------------------------------------------------------ *)
(* The length and the splits of LIST_REL, which HOL4's listTheory     *)
(* has as LIST_REL_LENGTH and LIST_REL_SPLIT1; the two halves of the  *)
(* split are a lemma each, because the proofs are an induction over   *)
(* the first list and an induction over the second.                   *)
(* ------------------------------------------------------------------ *)

let LIST_REL_LENGTH = prove
 (`!(R:A->B->bool) l1 l2. ALL2 R l1 l2 ==> LENGTH l1 = LENGTH l2`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN X_GEN_TAC `l2:B list` THEN
  STRUCT_CASES_TAC(ISPEC `l2:B list` list_CASES_v) THEN
  REWRITE_TAC[ALL2; LENGTH; SUC_INJ] THEN ASM_MESON_TAC[]);;

let LIST_REL_APPEND_I = prove
 (`!(P:A->B->bool) xs1 ys1 xs2 ys2.
     ALL2 P xs1 ys1 /\ ALL2 P xs2 ys2
     ==> ALL2 P (APPEND xs1 xs2) (APPEND ys1 ys2)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN X_GEN_TAC `ys1:B list` THEN
  STRUCT_CASES_TAC(ISPEC `ys1:B list` list_CASES_v) THEN
  REWRITE_TAC[APPEND; ALL2] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN FIRST_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[]);;

let LIST_REL_APPEND_E = prove
 (`!(P:A->B->bool) xs1 xs2 zs.
     ALL2 P (APPEND xs1 xs2) zs
     ==> ?u1 u2. zs = APPEND u1 u2 /\ ALL2 P xs1 u1 /\
                 ALL2 P xs2 u2`,
  GEN_TAC THEN LIST_INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[APPEND] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`[]:B list`; `zs:B list`] THEN
    ASM_REWRITE_TAC[APPEND; ALL2];
    REPEAT GEN_TAC THEN
    STRUCT_CASES_TAC(ISPEC `zs:B list` list_CASES_v) THEN
    REWRITE_TAC[APPEND; ALL2] THEN STRIP_TAC THEN
    USE_IH THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`CONS (v:B) u1`; `u2:B list`] THEN
    ASM_REWRITE_TAC[APPEND; ALL2]]);;

let LIST_REL_SPLIT1 = prove
 (`!(P:A->B->bool) xs2 xs1 zs.
     ALL2 P (APPEND xs1 xs2) zs <=>
     ?ys1 ys2. zs = APPEND ys1 ys2 /\ ALL2 P xs1 ys1 /\
               ALL2 P xs2 ys2`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [MATCH_ACCEPT_TAC LIST_REL_APPEND_E;
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LIST_REL_APPEND_I THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------ *)
(* The addresses of a list in memory: the n-th one is the first       *)
(* shifted n times by the width of an element, which every proof      *)
(* about a heap, a word list or a store takes apart.  WORD_RULE       *)
(* proves each of them; they stand here because a proof that unfolds  *)
(* a definition by SUC may not have ADD1 in its rewrite set (the      *)
(* clause of the definition would no longer fire), and one that       *)
(* splits a list by APPEND needs the sum.                             *)
(* ------------------------------------------------------------------ *)

let WORD_ADD_MUL_0 = prove
 (`!(a:(N)word) b. a + b * n2w 0 = a`,
  CONV_TAC WORD_RULE);;

let WORD_ADD_0_MUL = prove
 (`!(a:(N)word) b. a + n2w 0 * b = a`,
  CONV_TAC WORD_RULE);;

let WORD_ADD_MUL_SUC = prove
 (`!(a:(N)word) b m. a + b * n2w (SUC m) = (a + b) + b * n2w m`,
  REWRITE_TAC[ADD1; WORD_ADD] THEN CONV_TAC WORD_RULE);;

let WORD_ADD_SUC_MUL = prove
 (`!(a:(N)word) b m. a + n2w (SUC m) * b = (a + b) + n2w m * b`,
  REWRITE_TAC[ADD1; WORD_ADD] THEN CONV_TAC WORD_RULE);;

let WORD_ADD_MUL_ADD1 = prove
 (`!(a:(N)word) b m. a + b * n2w (m + 1) = (a + b) + b * n2w m`,
  REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE);;

let WORD_ADD_ADD1_MUL = prove
 (`!(a:(N)word) b m. a + n2w (m + 1) * b = (a + b) + n2w m * b`,
  REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE);;

let WORD_ADD_MUL_SPLIT = prove
 (`!(a:(N)word) b m n.
     a + b * n2w (m + n) = (a + b * n2w m) + b * n2w n`,
  REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE);;

let WORD_ADD_SPLIT_MUL = prove
 (`!(a:(N)word) b m n.
     a + n2w (m + n) * b = (a + n2w m * b) + n2w n * b`,
  REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE);;
