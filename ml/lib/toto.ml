(* ======================================================== *)
(*  toto: ported from HOL4's
    src/finite_maps/totoScript.sml
    A HOL4 library theory, of which the port has the definitions
    that CakeML needs, and 9 theorems of it from LightCake.  Needed
    by 11 files of the port.  *)
(* ======================================================== *)

needs "lib/ternaryComparisons.ml";;

(* this file is of no theory of the port: the overloads it
   registers are in the scope of every file *)
let _ = hol4_lib ();;
(* HOL4 ancestors outside the port: pred_set relation pair arithmetic
   numeral string list set_relation *)

let TotOrd = new_definition
  `TotOrd (c:'a->'a->ordering) = (
      (!x y. (c x y = EQUAL) <=> (x = y)) /\
      (!x y. (c x y = GREATER) <=> (c y x = LESS)) /\
      (!x y z. (c x y = LESS) /\ (c y z = LESS) ==> (c x z =
        LESS)))`;;

(* ================================================================ *)
(*  The theorems of totoTheory that LightCake proves and this     *)
(*  port needs, taken from its hol4/toto.                         *)
(*                                                                *)
(*  LightCake is the other HOL Light port of CakeML               *)
(*  (hol-light-family/LightCake, BSD 3-Clause); its HOL4 library  *)
(*  layer is proved, and of these theories this port has only     *)
(*  the definitions that CakeML needs.  tools/lightcake.py        *)
(*  writes this file: the statements and the proofs are           *)
(*  LightCake's, with its constants under the names this port     *)
(*  gives them.  What it could not take, and why, is at the end.  *)
(* ================================================================ *)


let trichotomous_ALT = prove
 (`!R:A->A->bool. trichotomous R <=> !x y. ~R x y /\ ~R y x ==> x = y`,
  REWRITE_TAC[trichotomous] THEN MESON_TAC[]);;

let SPLIT_PAIRS = prove
 (`!x y:A#B. x = y <=> FST x = FST y /\ SND x = SND y`,
  REWRITE_TAC[FORALL_PAIR_THM; PAIR_EQ]);;

let all_cpn_distinct = prove
 (`(~(LESS = EQUAL) /\ ~(LESS = GREATER) /\ ~(EQUAL = GREATER)) /\
   (~(EQUAL = LESS) /\ ~(GREATER = LESS) /\ ~(GREATER = EQUAL))`,
  REWRITE_TAC[distinctness "ordering"]);;

let TO_equal_eq = prove
 (`!c:A->A->ordering. TotOrd c ==> (!x y. c x y = EQUAL <=> x = y)`,
  SIMP_TAC[TotOrd]);;

let TO_refl = prove
 (`!c:A->A->ordering. TotOrd c ==> (!x. c x x = EQUAL)`,
  SIMP_TAC[TotOrd]);;

let TO_antisym = prove
 (`!c:A->A->ordering. TotOrd c ==> (!x y. c x y = GREATER <=> c y x =
   LESS)`,
  SIMP_TAC[TotOrd]);;

let TO_cpn_eqn = prove
 (`!c. TotOrd (c:A->A->ordering)
       ==> (!x y. c x y = LESS ==> ~(x = y)) /\
           (!x y. c x y = GREATER ==> ~(x = y)) /\
           (!x y. c x y = EQUAL ==> x = y)`,
  REWRITE_TAC[TotOrd] THEN MESON_TAC[distinctness "ordering"]);;

let StrongOrder_ALT = prove
 (`!Z:A->A->bool. StrongOrder Z <=> irreflexive Z /\ transitive Z`,
  REWRITE_TAC[StrongOrder]);;

let StrongLinearOrder_LESS = prove
 (`StrongLinearOrder ((<):num->num->bool)`,
  REWRITE_TAC[StrongLinearOrder; StrongOrder; irreflexive_def;
    transitive_def;
              trichotomous] THEN
  ARITH_TAC);;

(* What this port cannot take from LightCake's toto
   yet, with the names of its own that each proof
   uses:

     cpn_distinct                     ordering_distinct
     cpn_case_def                     ordering_case_def
     cpn_nchotomy                     ordering_nchotomy
     TotOrd_TO_of_LO                  TO_of_LinearOrder
     TotOrd_inv                       TO_inv
     TO_inv_TO_inv                    TO_inv
     LEX_ALT                          LEX_DEF
     lexTO_thm                        CASE_TERM LEX_DEF
                                      StrongLinearOrder_of_TO
                                      TO_of_LinearOrder lexTO
                                      ordering_case_def
                                      ordering_nchotomy
     lexTO_ALT                        CASE_TERM lexTO lexTO_thm
     TO_lexTO                         lexTO lexTO_thm ordering_case_eq
     TO_numOrd                        TotOrd_TO_of_LO numOrd
     TO_injection                     imageOrd
     StrongLinearOrder_of_TO_TO_of_LinearOrder StrongLinearOrder_of_TO
                                       TO_of_LinearOrder
                                       ordering_case_def
     TO_of_LinearOrder_LEX
                                      StrongLinearOrder_of_TO_TO_of_LinearOrder
                                      TO_of_LinearOrder lexTO
     LCMPAUX_StrongLinearOrder_of_TO_LESS StrongLinearOrder_of_TO
                                       ordering_case_def
                                       ordering_nchotomy
     Strong_Strong_of_TO
                                      LCMPAUX_StrongLinearOrder_of_TO_LESS
                                      StrongLinearOrder_of_TO
                                      ordering_nchotomy
     TotOrd_TO_of_Strong              TO_of_LinearOrder TotOrd_TO_of_LO
     TO_of_less_rel                   TO_of_LinearOrder
     TO_of_greater_ler                TO_of_LinearOrder
     SLO_LEX                          LEX_THM
     SLO_listorder                    listorder

*)
