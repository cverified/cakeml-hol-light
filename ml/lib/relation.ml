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
