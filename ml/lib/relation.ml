(* ================================================================== *)
(*  HOL4's relationTheory, of which the port needs the reflexive      *)
(*  transitive closure (which HOL4 defines inductively) and the       *)
(*  transitive closure.                                               *)
(* ================================================================== *)

let RTC_RULES,RTC_INDUCT,RTC_CASES = new_inductive_definition
  `(!x. RTC R x x) /\
   (!x y z. R x y /\ RTC R y z ==> RTC R x z)`;;

let TC_DEF = new_definition
  `TC (R:A->A->bool) a b <=>
   !P. (!x y. R x y ==> P x y) /\
       (!x y z. P x y /\ P y z ==> P x z) ==> P a b`;;

(* the properties of a relation that HOL4's relationTheory defines,
   and the orders it builds from them *)

let transitive_def = new_definition
  `transitive (R:A->A->bool) <=> !x y z. R x y /\ R y z ==> R x z`;;

let reflexive_def = new_definition
  `reflexive (R:A->A->bool) <=> !x. R x x`;;

let irreflexive_def = new_definition
  `irreflexive (R:A->A->bool) <=> !x. ~(R x x)`;;

let symmetric_def = new_definition
  `symmetric (R:A->A->bool) <=> !x y. R x y <=> R y x`;;

let antisymmetric_def = new_definition
  `antisymmetric (R:A->A->bool) <=>
   !x y. R x y /\ R y x ==> x = y`;;

let total_def = new_definition
  `total (R:A->A->bool) <=> !x y. R x y \/ R y x`;;

let trichotomous = new_definition
  `trichotomous (R:A->A->bool) <=> !a b. R a b \/ R b a \/ a = b`;;

let StrongOrder = new_definition
  `StrongOrder (Z:A->A->bool) <=> irreflexive Z /\ transitive Z`;;

let StrongLinearOrder = new_definition
  `StrongLinearOrder (Z:A->A->bool) <=>
   StrongOrder Z /\ trichotomous Z`;;

(* the reflexive closure, and the intersection and the inclusion of
   two relations, which HOL4 writes as infixes *)

let RC_DEF = new_definition
  `RC (R:A->A->bool) x y <=> x = y \/ R x y`;;

let RINTER = new_definition
  `RINTER (R1:A->B->bool) R2 x y <=> R1 x y /\ R2 x y`;;

let RSUBSET = new_definition
  `RSUBSET (R1:A->B->bool) R2 <=> !x y. R1 x y ==> R2 x y`;;
