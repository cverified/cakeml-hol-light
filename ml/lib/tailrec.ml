(* ======================================================== *)
(*  tailrec: ported from HOL4's
    examples/machine-code/hoare-triple/tailrecScript.sml
    A HOL4 library theory, of which the port has the definitions
    that CakeML needs, and 2 theorems of it from LightCake.  Needed
    by unify.ml and word_bignumProof.ml.  *)
(* ======================================================== *)

(* this file needs nothing of the port *)

(* of no theory of the port: what it registers is in the scope of every file *)
let _ = cake_library ();;
(* HOL4 ancestors outside the port: pred_set arithmetic While sum *)

let TAILREC_PRE_def = new_definition
  `TAILREC_PRE f1 guard' precondition' (x:'a) <=>
     (!k. (!m. m < k ==> guard' (ITER m f1 x)) ==> precondition'
       (ITER k f1 x)) /\
     (?n. ~(guard' (ITER n f1 x)))`;;

let TAILREC_def = new_definition
  `tailrec_TAILREC f1 (f2:'a->'b) g x = f2 (WHILE g f1 x)`;;

let SHORT_TAILREC_def = new_definition
  `SHORT_TAILREC (f:'a->('a+'b)#bool) =
     tailrec_TAILREC (OUTL o FST o f) (OUTR o FST o f) (ISL o FST
       o f)`;;

let SHORT_TAILREC_PRE_def = new_definition
  `SHORT_TAILREC_PRE (f:'a->('a+'b)#bool) =
     TAILREC_PRE (OUTL o FST o f) (ISL o FST o f) (SND o f)`;;

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
     TAILREC_THM                      -- Exception: Failure "TAC_PROOF:
                                      Unsolved goals".
     TAILREC_PRE_IMP                  ITER
     SHORT_TAILREC_THM                TAILREC_PRE_THM TAILREC_THM
     SHORT_TAILREC_PRE_INDUCT         TAILREC_PRE_INDUCT
     SHORT_TAILREC_SIM                SHORT_TAILREC_PRE_INDUCT
                                      SHORT_TAILREC_THM
     _                                cake_add_simps

*)
