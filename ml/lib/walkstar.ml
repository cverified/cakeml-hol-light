(* ======================================================== *)
(*  walkstar: ported from HOL4's
    examples/algorithms/unification/triangular/first-order/
      walkstarScript.sml
    A HOL4 library theory, of which the port has the definitions and
    2 theorems that CakeML needs.  Needed by 5 files of the port.  *)
(* ======================================================== *)

needs "lib/subst.ml";;
needs "lib/term.ml";;
needs "lib/walk.ml";;

(* of no theory of the port: what it registers is in the scope of every file *)
let _ = cake_library ();;
(* HOL4 ancestors outside the port: relation pair bag prim_rec finite_map
   pred_set *)

let WALKSTARR_RULES,WALKSTARR_INDUCT,WALKSTARR_CASES =
  new_inductive_definition
  `(!s t t1 t2 r1 r2.
      walk s t = term_Pair t1 t2 /\ WALKSTARR s t1 r1 /\
      WALKSTARR s t2 r2
      ==> WALKSTARR s t (term_Pair r1 r2)) /\
   (!s t. (!t1 t2. ~(walk s t = term_Pair t1 t2))
      ==> WALKSTARR s t (walk s t))`;;

let walkstar = new_definition
  `walkstar s t = @r. WALKSTARR s t r`;;

(* the equations that HOL4 reads off its schema, under the
   hypothesis that the substitution is wellfounded: walkstar_def
   is its Theorem of that name and walkstar_thm the three clauses
   of it *)

let walkstar_def = prove
 (`wfs s ==> !t. walkstar s t =
     match walk s t with
       term_Var v4 -> term_Var v4
     | term_Pair t1 t2 -> term_Pair (walkstar s t1) (walkstar s t2)
     | term_Const v7 -> term_Const v7`,
  CHEAT_TAC);;

let walkstar_thm = prove
 (`wfs s ==>
   (walkstar s (term_Var v) =
      match vwalk s v with
        term_Var v4 -> term_Var v4
      | term_Pair t1 t2 -> term_Pair (walkstar s t1) (walkstar s t2)
      | term_Const v7 -> term_Const v7) /\
   (walkstar s (term_Pair t1 t2) =
      term_Pair (walkstar s t1) (walkstar s t2)) /\
   (walkstar s (term_Const c) = term_Const c)`,
  CHEAT_TAC);;

(* the occurs check, which HOL4 makes with Hol_reln in the same
   file (walkstarScript.sml) *)

let oc_RULES,oc_INDUCT,oc_CASES =
  new_inductive_definition
  `(!s t v. v IN vars t /\ ~(v IN FDOM s) ==> oc s t v) /\
   (!s t v u t'. u IN vars t /\ vwalk s u = t' /\ oc s t' v
      ==> oc s t v)`;;

let walkstarR_def = new_definition
  `walkstarR s =
    inv_image ((LEX) (TC (mlt1 (TC (vR s)))) (MEASURE pair_count)) (\t.
      (varb t,t))`;;
