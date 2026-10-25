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

(* and of a restriction of the domain, which HOL4 states as
   FLOOKUP_DRESTRICT: the set of the keys it keeps is a part of the
   domain, so it is finite as well *)

let FMAP_FN_DRESTRICT = prove
 (`!(fm:(A,B)fmap) s.
     fmap_fn (DRESTRICT fm s) =
     (\x. if x IN s then fmap_fn fm x else NONE)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[DRESTRICT] THEN
  REWRITE_TAC[GSYM(CONJUNCT2 fmap_tybij)] THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{x | ~(fmap_fn (fm:(A,B)fmap) x = NONE)}` THEN
  REWRITE_TAC[FMAP_FN_FINITE; SUBSET; IN_ELIM_THM] THEN
  GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

let FLOOKUP_DRESTRICT = prove
 (`!(fm:(A,B)fmap) s x.
     FLOOKUP (DRESTRICT fm s) x =
     (if x IN s then FLOOKUP fm x else NONE)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FLOOKUP; FMAP_FN_DRESTRICT]);;

let FAPPLY_FUPDATE_THM = prove
 (`!(fm:(A,B)fmap) k v x.
     FAPPLY (fm |+ (k,v)) x = (if x = k then v else FAPPLY fm x)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[fmap_apply; FMAP_FN_FUPDATE; FST; SND] THEN
  COND_CASES_TAC THEN REWRITE_TAC[THE]);;

(* two finite maps with the same representing function are the same
   map, which is what every equation between finite maps is proved
   with *)

let FMAP_FN_INJ = prove
 (`!(a:(A,B)fmap) b. fmap_fn a = fmap_fn b ==> a = b`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[GSYM (CONJUNCT1 fmap_tybij)] THEN
  ASM_REWRITE_TAC[]);;

(* and HOL4's FUPDATE_COMMUTES: two updates of different keys can be
   made in either order *)

let FUPDATE_COMMUTES = prove
 (`!(f:(A,B)fmap) k1 v1 k2 v2. ~(k1 = k2)
     ==> f |+ (k1,v1) |+ (k2,v2) = f |+ (k2,v2) |+ (k1,v1)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FMAP_FN_INJ THEN
  REWRITE_TAC[FMAP_FN_FUPDATE; FST; SND; FUN_EQ_THM] THEN
  GEN_TAC THEN REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM_LIST(fun ths -> MAP_EVERY MP_TAC ths) THEN MESON_TAC[]);;

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

(* ------------------------------------------------------------------ *)
(* TAKE and DROP of the same number split a list, and DROP at a       *)
(* position is the element there followed by the DROP after it:       *)
(* HOL4's TAKE_DROP and rich_list's DROP_EL_CONS, which the proofs    *)
(* that take a list apart at an index go through.                     *)
(* ------------------------------------------------------------------ *)

let TAKE_DROP = prove
 (`!(l:A list) n. TAKE n l ++ DROP n l = l`,
  LIST_INDUCT_TAC THEN GEN_TAC THEN
  REWRITE_TAC[TAKE; DROP; APPEND] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[APPEND]);;

let DROP_EL_CONS = prove
 (`!(l:A list) n. n < LENGTH l
                  ==> DROP n l = EL n l :: DROP (SUC n) l`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[LENGTH; LT];
    GEN_TAC THEN STRUCT_CASES_TAC(SPEC `n:num` num_CASES) THEN
    REWRITE_TAC[DROP; EL; HD; TL; NOT_SUC; SUC_SUB1; DROP_0;
                LENGTH; LT_SUC; LT_0] THEN
    ASM_REWRITE_TAC[]]);;

(* HOL4's DROP_DROP_T: two DROPs of a list are one of the sum *)

let DROP_DROP = prove
 (`!(l:A list) m n. DROP n (DROP m l) = DROP (n + m) l`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[DROP];
    REPEAT GEN_TAC THEN
    STRUCT_CASES_TAC(SPEC `m:num` num_CASES) THEN
    REWRITE_TAC[DROP; NOT_SUC; SUC_SUB1; ADD_CLAUSES; DROP_0;
                ADD_SUC] THEN
    ASM_REWRITE_TAC[]]);;

(* HOL4's TAKE_0, LENGTH_TAKE, TAKE_SUM, TAKE_TAKE, DROP_TAKE,   *)
(* TAKE_LENGTH_APPEND, DROP_LENGTH_APPEND, TAKE_APPEND1,         *)
(* DROP_APPEND1 and DROP_APPEND2.  The clauses of TAKE and DROP   *)
(* decide on the number, so a TAKE of none, and a TAKE or a DROP  *)
(* of as many as a first list has, do not reduce by themselves;   *)
(* the proofs that copy a part of a list into another go through  *)
(* these.                                                         *)
(* ------------------------------------------------------------------ *)

let TAKE_0 = prove
 (`!l:A list. TAKE 0 l = []`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[TAKE]);;

let LENGTH_TAKE = prove
 (`!(l:A list) k. k <= LENGTH l ==> LENGTH (TAKE k l) = k`,
  LIST_INDUCT_TAC THEN GEN_TAC THEN REWRITE_TAC[TAKE; LENGTH] THENL
   [ARITH_TAC;
    DISCH_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[LENGTH] THEN
    SUBGOAL_THEN `LENGTH (TAKE (k - 1) (t:A list)) = k - 1`
      SUBST1_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      ASM_ARITH_TAC]]);;

let TAKE_SUM = prove
 (`!(l:A list) a b.
     TAKE (a + b) l = TAKE a l ++ TAKE b (DROP a l)`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[TAKE; DROP; APPEND] THEN
  STRUCT_CASES_TAC(SPEC `a:num` num_CASES) THEN
  ASM_REWRITE_TAC[TAKE_0; TAKE; DROP; APPEND; ADD_CLAUSES;
                  NOT_SUC; SUC_SUB1]);;

let TAKE_TAKE = prove
 (`!(l:A list) m k. k <= m ==> TAKE k (TAKE m l) = TAKE k l`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[TAKE] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  (ASM_CASES_TAC `m = 0` THENL
    [ASM_REWRITE_TAC[TAKE] THEN
     (SUBGOAL_THEN `k = 0` SUBST1_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC]) THEN
     REWRITE_TAC[TAKE_0];
     ALL_TAC]) THEN
  ASM_REWRITE_TAC[TAKE] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
  FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC);;

let DROP_TAKE = prove
 (`!(l:A list) m k. DROP k (TAKE m l) = TAKE (m - k) (DROP k l)`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[TAKE; DROP];
    REPEAT GEN_TAC THEN REWRITE_TAC[TAKE] THEN
    (ASM_CASES_TAC `m = 0` THENL
      [ASM_REWRITE_TAC[DROP; ARITH_RULE `0 - k = 0`; TAKE_0];
       ALL_TAC]) THEN
    ASM_REWRITE_TAC[DROP] THEN
    (ASM_CASES_TAC `k = 0` THENL
      [ASM_REWRITE_TAC[SUB_0; TAKE; DROP_0]; ALL_TAC]) THEN
    ASM_REWRITE_TAC[] THEN
    (SUBGOAL_THEN `(m - 1) - (k - 1) = m - k` SUBST1_TAC THENL
      [ASM_ARITH_TAC; ALL_TAC]) THEN
    REWRITE_TAC[]]);;

let TAKE_LENGTH_APPEND = prove
 (`!(l1:A list) l2. TAKE (LENGTH l1) (l1 ++ l2) = l1`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[LENGTH; APPEND; TAKE; TAKE_0; NOT_SUC;
                  SUC_SUB1]);;

let DROP_LENGTH_APPEND = prove
 (`!(l1:A list) l2. DROP (LENGTH l1) (l1 ++ l2) = l2`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[LENGTH; APPEND; DROP; DROP_0; NOT_SUC;
                  SUC_SUB1]);;

let TAKE_APPEND1 = prove
 (`!(l1:A list) l2 k.
     k <= LENGTH l1 ==> TAKE k (l1 ++ l2) = TAKE k l1`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; APPEND; TAKE] THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN
    (SUBGOAL_THEN `k = 0` SUBST1_TAC THENL
      [ASM_ARITH_TAC; ALL_TAC]) THEN
    REWRITE_TAC[TAKE_0];
    REPEAT GEN_TAC THEN DISCH_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

let DROP_APPEND1 = prove
 (`!(l1:A list) l2 k.
     k <= LENGTH l1 ==> DROP k (l1 ++ l2) = DROP k l1 ++ l2`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; APPEND; DROP] THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN
    (SUBGOAL_THEN `k = 0` SUBST1_TAC THENL
      [ASM_ARITH_TAC; ALL_TAC]) THEN
    REWRITE_TAC[DROP_0; APPEND];
    REPEAT GEN_TAC THEN DISCH_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[APPEND] THEN FIRST_ASSUM MATCH_MP_TAC THEN
    ASM_ARITH_TAC]);;

let DROP_APPEND2 = prove
 (`!(l1:A list) l2 k.
     LENGTH l1 <= k
     ==> DROP k (l1 ++ l2) = DROP (k - LENGTH l1) l2`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`l1:A list`; `l2:A list`] DROP_LENGTH_APPEND) THEN
  DISCH_THEN(fun th ->
    MP_TAC(AP_TERM
      `DROP (k - LENGTH (l1:A list)):A list->A list` th)) THEN
  REWRITE_TAC[DROP_DROP] THEN
  (SUBGOAL_THEN `(k - LENGTH (l1:A list)) + LENGTH l1 = k`
     SUBST1_TAC THENL
    [ASM_ARITH_TAC; ALL_TAC]) THEN
  DISCH_THEN ACCEPT_TAC);;

(* ------------------------------------------------------------------ *)
(* HOL4's MEM_FLAT: an element of the flattening is an element of
   one of the lists *)

let MEM_FLAT = prove
 (`!ls (x:A). MEM x (FLAT ls) <=> ?l. MEM l ls /\ MEM x l`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[FLAT; MEM; MEM_APPEND] THEN MESON_TAC[]);;

(* a universal quantifier that every element of two lists satisfies
   can be pulled out of an ALL2.  The lists are of a length by the
   instance at 0, and an element by the instance at the quantified
   value; it is a lemma of its own because the type of a list of a
   statement is often a type variable that no term can be written
   down for *)

let ALL2_SWAP = prove
 (`!(P:num->A->B->bool) l m.
     (!k. ALL2 (\x y. P k x y) l m) ==> ALL2 (\x y. !k. P k x y) l m`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LIST_REL_EL_EQN] THEN
  DISCH_TAC THEN CONJ_TAC THENL
   [FIRST_ASSUM(fun th -> MATCH_ACCEPT_TAC(CONJUNCT1(SPEC `0` th)));
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM(fun th -> MP_TAC(SPEC `k:num` th)) THEN
    ASM_SIMP_TAC[]]);;

(* the lookup of a finite map read by its domain and its
   application, HOL4's FLOOKUP_DEF, and what a SUBMAP does to one,
   HOL4's FLOOKUP_SUBMAP *)

let FLOOKUP_DEF = prove
 (`!(fm:(A,B)fmap) x.
     FLOOKUP fm x =
     (if x IN FDOM fm then SOME (FAPPLY fm x) else NONE)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FLOOKUP; FDOM; fmap_apply;
                                  IN_ELIM_THM] THEN
  STRUCT_CASES_TAC(ISPEC `fmap_fn (fm:(A,B)fmap) x`
                         (cases_of `:(B)option`)) THEN
  REWRITE_TAC[THE; distinctness "option"]);;

let FLOOKUP_SUBMAP = prove
 (`!(f:(A,B)fmap) g k v.
     f SUBMAP g /\ FLOOKUP f k = SOME v ==> FLOOKUP g k = SOME v`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SUBMAP; FLOOKUP_DEF] THEN
  REPEAT COND_CASES_TAC THEN
  REWRITE_TAC[distinctness "option"; injectivity "option"] THEN
  ASM_MESON_TAC[]);;

(* what a SUBMAP says of a point of the domain of the smaller map,
   which is HOL4's SUBMAP_DEF read forwards *)

let SUBMAP_FAPPLY = prove
 (`!(f:(A,B)fmap) g n.
     f SUBMAP g ==> n IN FDOM f
     ==> n IN FDOM g /\ FAPPLY f n = FAPPLY g n`,
  REWRITE_TAC[SUBMAP] THEN MESON_TAC[]);;

(* the lookup of an update, HOL4's FLOOKUP_UPDATE, and the point of
   a lookup that gives a value, which is in the domain *)

let FLOOKUP_UPDATE = prove
 (`!(fm:(A,B)fmap) k v x.
     FLOOKUP (fm |+ (k,v)) x =
     (if x = k then SOME v else FLOOKUP fm x)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[FLOOKUP; FMAP_FN_FUPDATE; FST; SND]);;

let FLOOKUP_IN_FDOM = prove
 (`!(fm:(A,B)fmap) x v. FLOOKUP fm x = SOME v ==> x IN FDOM fm`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FLOOKUP_DEF] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[distinctness "option"]);;

(* ------------------------------------------------------------------ *)
(* HOL4's ALL_DISTINCT is the two clauses; ml/lib/hol4.ml defines it  *)
(* with PAIRWISE, so the clauses are a lemma (the list of a cons has  *)
(* no repetition when the head is not in the tail and the tail has    *)
(* none).                                                             *)
(* ------------------------------------------------------------------ *)

let ALL_DISTINCT_CLAUSES =
  let allnotmem = prove
   (`!h t. ALL (\y. ~((h:A) = y)) t <=> ~(MEM h t)`,
    GEN_TAC THEN LIST_INDUCT_TAC THEN
    ASM_REWRITE_TAC[ALL; MEM; DE_MORGAN_THM]) in
  prove
   (`(ALL_DISTINCT ([]:A list) <=> T) /\
     (!h t. ALL_DISTINCT (CONS (h:A) t) <=>
            ~(MEM h t) /\ ALL_DISTINCT t)`,
    REWRITE_TAC[ALL_DISTINCT; PAIRWISE; allnotmem]);;

(* ------------------------------------------------------------------ *)
(* The bits of a slice of a word (HOL4 reads one off with its         *)
(* fcpTheory.FCP_BETA): the slice keeps the bits of the range and the *)
(* shift of word_slice_alt puts them back where they were, so a bit   *)
(* of the slice is a bit of the word in the range.  A proof about the *)
(* bytes of a word goes through this.                                 *)
(* ------------------------------------------------------------------ *)

let BIT_WORD_SLICE_ALT = prove
 (`!h l (w:(N)word) j. l <= h
     ==> (bit j (word_slice_alt h l w) <=>
          l <= j /\ j < h /\ j < dimindex (:N) /\ bit j w)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[word_slice_alt; BIT_WORD_SHL; BIT_WORD_SUBWORD] THEN
  REWRITE_TAC[ARITH_RULE `MIN a b = if a <= b then a else b`] THEN
  ASM_CASES_TAC `l:num <= j` THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[ARITH_RULE `l <= j ==> l + (j - l) = j`;
               ARITH_RULE `l <= j ==> (l + j) - l = j`] THEN
  COND_CASES_TAC THEN
  ASM_CASES_TAC `bit j (w:(N)word)` THEN ASM_REWRITE_TAC[] THEN
  ARITH_NO_BIT_TAC);;

(* and that two conditionals with the same condition and the same
   then-branch agree exactly when the condition holds or the two
   else-branches agree *)

let COND_SAME_IFF = prove
 (`!c u v1 v2. (((if c then u else v1) <=> (if c then u else v2))
                <=> (c \/ (v1 <=> v2)))`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC TAUT);;

(* ------------------------------------------------------------------ *)
(* The bits a number has above its size: a number below two to the r  *)
(* has no bit at r or above, which is how a field of a header is seen *)
(* to stay inside the range the encoding gives it.                    *)
(* ------------------------------------------------------------------ *)

let BIT_WORD_HI = prove
 (`!n r (i:num). n < 2 EXP r /\ r <= i
     ==> ~(bit i ((n2w n):(N)word))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[BIT_WORD] THEN
  SUBGOAL_THEN `n DIV 2 EXP i = 0` SUBST1_TAC THENL
   [MATCH_MP_TAC DIV_LT THEN
    TRANS_TAC LTE_TRANS `2 EXP r` THEN
    ASM_SIMP_TAC[LE_EXP; ARITH];
    REWRITE_TAC[ODD]]);;

(* the bits of HOL4's word_slice, which keeps the bits of the range
   where they are (its word_slice_alt leaves the top one out) *)

let BIT_WORD_SLICE = prove
 (`!h l (w:(N)word) j. j < dimindex (:N)
     ==> (bit j (word_slice h l w) <=> l <= j /\ j <= h /\ bit j w)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[word_slice; word_bits; BIT_WORD_SHL;
              BIT_WORD_SUBWORD] THEN
  REWRITE_TAC[ARITH_RULE `MIN a b = if a <= b then a else b`] THEN
  ASM_CASES_TAC `l:num <= j` THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[ARITH_RULE `l <= j ==> l + j - l = j`] THEN
  COND_CASES_TAC THEN
  ASM_CASES_TAC `bit j (w:(N)word)` THEN ASM_REWRITE_TAC[] THEN
  ARITH_NO_BIT_TAC);;

(* the same for word_slice_alt, which needs no l <= h when the bit
   asked after is one of the word *)

let BIT_WORD_SLICE_ALT_LT = prove
 (`!h l (w:(N)word) j. j < dimindex (:N)
     ==> (bit j (word_slice_alt h l w) <=>
          l <= j /\ j < h /\ bit j w)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[word_slice_alt; BIT_WORD_SHL; BIT_WORD_SUBWORD] THEN
  REWRITE_TAC[ARITH_RULE `MIN a b = if a <= b then a else b`] THEN
  ASM_CASES_TAC `l:num <= j` THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[ARITH_RULE `l <= j ==> l + j - l = j`] THEN
  COND_CASES_TAC THEN
  ASM_CASES_TAC `bit j (w:(N)word)` THEN ASM_REWRITE_TAC[] THEN
  ARITH_NO_BIT_TAC);;

(* a shift up that the same shift down undoes, when every bit of the
   word stays inside it, and the or of something below the shift
   that the shift down loses *)

let USHR_SHL_CANCEL = prove
 (`!(x:(N)word) s. (!j. bit j x ==> j + s < dimindex (:N))
     ==> word_ushr (word_shl x s) s = x`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_USHR; BIT_WORD_SHL] THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  REWRITE_TAC[ARITH_RULE `s <= j + s /\ (j + s) - s = j`] THEN
  ASM_CASES_TAC `bit j (x:(N)word)` THEN ASM_SIMP_TAC[]);;

let USHR_OR_LOW = prove
 (`!(x:(N)word) b s. (!j. bit j b ==> j < s)
     ==> word_ushr (word_or x b) s = word_ushr x s`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_USHR; BIT_WORD_OR] THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  ASM_CASES_TAC `j + s < dimindex (:N)` THENL
   [ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `bit (j + s) (b:(N)word)` THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `j + s` th)) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (ARITH_RULE `j + s < s ==> F`)) THEN
    REWRITE_TAC[];
    ASM_SIMP_TAC[BIT_TRIVIAL;
                 ARITH_RULE `~((a:num) < b) ==> b <= a`]]);;

