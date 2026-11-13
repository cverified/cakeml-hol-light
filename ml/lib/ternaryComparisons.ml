(* ======================================================== *)
(*  ternaryComparisons: ported from HOL4's
    src/sort/ternaryComparisonsScript.sml  *)
(* ======================================================== *)

(* this file needs nothing of the port *)

(* this file is of no theory of the port: the overloads it
   registers are in the scope of every file *)
let _ = hol4_lib ();;

let ordering_INDUCT,ordering_RECURSION = define_datatype
  "ordering = LESS | EQUAL | GREATER";;
let pair_compare_def = new_definition
  `pair_compare c1 c2 (a,b) (x,y) =
      (match c1 a x with
         EQUAL -> c2 b y | res -> res)`;;

let num_compare_def = new_definition
  `num_compare n1 n2 =
     (if n1 = n2 then
       EQUAL else if n1 < n2 then
       LESS else
       GREATER)`;;
let list_compare_def,list_compare_ind = define_guess
  [`list_compare cmp l1 l2 =
        match (l1,l2) with
          ([],[]) -> EQUAL
        | ([],l2) -> LESS
        | (l1,[]) -> GREATER
        | ((x :: l1),(y :: l2)) ->
        (match cmp (x:'a) y with
          LESS -> LESS | EQUAL -> list_compare cmp l1 l2 |
            GREATER -> GREATER)`];;

let invert_comparison_def = define_cases
  [`invert_comparison GREATER = LESS`;
   `invert_comparison LESS = GREATER`;
   `invert_comparison EQUAL = EQUAL`];;

(* ================================================================ *)
(*  The theorems of ternaryComparisonsTheory that LightCake proves and this*)
(*  port needs, taken from its hol4/ternaryComparisons.           *)
(*                                                                *)
(*  LightCake is the other HOL Light port of CakeML               *)
(*  (hol-light-family/LightCake, BSD 3-Clause); its HOL4 library  *)
(*  layer is proved, and of these theories this port has only     *)
(*  the definitions that CakeML needs.  tools/lightcake.py        *)
(*  writes this file: the statements and the proofs are           *)
(*  LightCake's, with its constants under the names this port     *)
(*  gives them.  What it could not take, and why, is at the end.  *)
(* ================================================================ *)


let ordering_induction = ordering_INDUCT;;

let ordering_Axiom = ordering_RECURSION;;

let ordering_nchotomy = prove
 (`!a. a = LESS \/ a = EQUAL \/ a = GREATER`,
  MATCH_MP_TAC ordering_INDUCT THEN REWRITE_TAC[]);;

let ordering_distinct = prove
 (`~(LESS = EQUAL) /\ ~(LESS = GREATER) /\ ~(EQUAL = GREATER)`,
  REWRITE_TAC[distinctness "ordering"]);;

let ordering_eq_dec = prove
 (`(!x:ordering. x = x <=> T) /\
   (LESS = EQUAL <=> F) /\ (LESS = GREATER <=> F) /\
   (EQUAL = LESS <=> F) /\ (EQUAL = GREATER <=> F) /\
   (GREATER = LESS <=> F) /\ (GREATER = EQUAL <=> F)`,
  REWRITE_TAC[distinctness "ordering"]);;

let option_compare_ind = prove
 (`!P. (!c:A->B->ordering. P c (NONE:A option) (NONE:B option)) /\
       (!c v0. P c NONE (SOME v0)) /\
       (!c v3. P c (SOME v3) NONE) /\
       (!c v1 v2. P c (SOME v1) (SOME v2))
       ==> !v v1 v2. P v v1 v2`,
  GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `c:A->B->ordering` THEN
  MATCH_MP_TAC option_INDUCT THEN CONJ_TAC THENL [ALL_TAC; GEN_TAC] THEN
  MATCH_MP_TAC option_INDUCT THEN ASM_REWRITE_TAC[]);;

let invert_eq_EQUAL = prove
 (`!x. invert_comparison x = EQUAL <=> x = EQUAL`,
  MATCH_MP_TAC ordering_INDUCT THEN
  REWRITE_TAC[invert_comparison_def; distinctness "ordering"]);;

let ordering_distinct1 = prove
 (`~(EQUAL = LESS)`,
  REWRITE_TAC[distinctness "ordering"]);;

let ordering_distinct2 = prove
 (`~(GREATER = EQUAL)`,
  REWRITE_TAC[distinctness "ordering"]);;

(* What this port cannot take from LightCake's ternaryComparisons
   yet, with the names of its own that each proof
   uses:

     ordering_case_def                case_def
     ordering_case_eq                 case_eq
     compare_equal                    ordering_case_def
     list_merge_ind                   cake_ind
     _                                bool_compare_def cake_add_simps
                                      option_compare_def

*)
