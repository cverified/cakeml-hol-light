(* ================================================================ *)
(*  The theorems of tailrecTheory that LightCake proves and this  *)
(*  port needs, taken from its hol4/tailrec.                      *)
(*                                                                *)
(*  LightCake is the other HOL Light port of CakeML               *)
(*  (hol-light-family/LightCake, BSD 3-Clause); its HOL4 library  *)
(*  layer is proved, and of these theories this port has only     *)
(*  the definitions that CakeML needs.  tools/lightcake.py        *)
(*  writes this file: the statements and the proofs are           *)
(*  LightCake's, with its constants under the names this port     *)
(*  gives them.  What it could not take, and why, is at the end.  *)
(* ================================================================ *)


let LSMALLAUX_FORALL_NUM = MESON[num_CASES]
  `!P. (!n. P n) <=> P 0 /\ (!n. P (SUC n))`;;

let LSMALLAUX_EXISTS_NUM = MESON[num_CASES]
  `!P. (?n. P n) <=> P 0 \/ (?n. P (SUC n))`;;

let LSMALLAUX_FORALL_LT_SUC = prove
 (`!(R:num->bool) k.
     (!m. m < SUC k ==> R m) <=> R 0 /\ (!m. m < k ==> R (SUC m))`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [MESON_TAC[LT_0; LT_SUC];
    STRIP_TAC THEN INDUCT_TAC THEN ASM_SIMP_TAC[LT_SUC]]);;

let TAILREC_THM = prove
 (`!f1 (f2:A->B) g x.
     tailrec_TAILREC f1 f2 g x =
     if g x then tailrec_TAILREC f1 f2 g (f1 x) else f2 x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[TAILREC_def] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [WHILE] THEN
  COND_CASES_TAC THEN REWRITE_TAC[]);;

let TAILREC_EQ_THM = prove
 (`(f1 = f1') /\ (f2 = (f2':A->B)) /\ (g = g') /\ (s = s') ==>
   (tailrec_TAILREC f1 f2 g = tailrec_TAILREC f1' f2' g') /\
   (TAILREC_PRE f1 g s = TAILREC_PRE f1' g' s')`,
  STRIP_TAC THEN ASM_REWRITE_TAC[]);;

(* What this port cannot take from LightCake's tailrec
   yet, with the names of its own that each proof
   uses:

     TAILREC_PRE_THM                  ITER_ALT
     TAILREC_PRE_INDUCT               ITER_ALT TAILREC_PRE_THM
     TAILREC_PRE_IMP                  ITER
     SHORT_TAILREC_THM                TAILREC_PRE_THM
     SHORT_TAILREC_PRE_INDUCT         TAILREC_PRE_INDUCT
     SHORT_TAILREC_SIM                SHORT_TAILREC_PRE_INDUCT
                                      SHORT_TAILREC_THM
     _                                cake_add_simps

*)
