(* ======================================================== *)
(*  walkstar: ported from HOL4's
    examples/algorithms/unification/triangular/first-order/
      walkstarScript.sml
    A HOL4 library theory, of which the port has the definitions
    that CakeML needs.  Needed by 6 files of the port.  *)
(* ======================================================== *)

needs "lib/subst.ml";;
needs "lib/term.ml";;
needs "lib/walk.ml";;

(* this file is of no theory of the port: the overloads it
   registers are in the scope of every file *)
let _ = hol4_lib ();;
(* HOL4 ancestors outside the port: relation pair bag prim_rec
   finite_map pred_set *)

let WALKSTARR_RULES,WALKSTARR_INDUCT,WALKSTARR_CASES =
  new_inductive_definition
  `(!s t t1 t2 r1 r2.
      walk s t = term_Pair t1 t2 /\ WALKSTARR s t1 r1 /\
      WALKSTARR s t2 r2
      ==> WALKSTARR s t (term_Pair r1 r2)) /\
   (!s t. (!t1 t2. ~(walk s t = term_Pair t1 t2))
      ==> WALKSTARR s t (walk s t))`;;

let walkstar_def = new_definition
  `walkstar s t = @r. WALKSTARR s t r`;;

(* the occurs check, which HOL4 makes with Hol_reln in the same
   file (walkstarScript.sml) *)

let oc_RULES,oc_INDUCT,oc_CASES =
  new_inductive_definition
  `(!s t v. v IN vars t /\ ~(v IN FDOM s) ==> oc s t v) /\
   (!s t v u t'. u IN vars t /\ vwalk s u = t' /\ oc s t' v
      ==> oc s t v)`;;

let walkstarR_def = new_definition
  `walkstarR s =
    inv_image ((LEX) (TC (mlt1 (TC (vR s)))) (MEASURE pair_count))
      (\t. (varb t,t))`;;
