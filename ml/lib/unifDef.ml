(* ======================================================== *)
(*  unifDef: ported from HOL4's
    examples/algorithms/unification/triangular/first-order/
      unifDefScript.sml  *)
(*  Of this HOL4 library theory only the definitions that the
    CakeML port needs are ported.  *)
(* ======================================================== *)

needs "lib/subst.ml";;
needs "lib/term.ml";;
needs "lib/walk.ml";;
needs "lib/walkstar.ml";;
(* HOL4 ancestors outside the port: string arithmetic finite_map
   pred_set bag relation prim_rec pair *)

let ext_s_check_def = cake_define
  `ext_s_check s v t = (if oc s t v then NONE else SOME (s |+ (v,t)))`;;

let UNIFYR_RULES,UNIFYR_INDUCT,UNIFYR_CASES =
  new_inductive_definition
  `(!s t1 t2 v1 v2.
      walk s t1 = term_Var v1 /\ walk s t2 = term_Var v2
      ==> UNIFYR s t1 t2
            (SOME (if v1 = v2 then s
                   else s |+ (v1,term_Var v2)))) /\
   (!s t1 t2 v1.
      walk s t1 = term_Var v1 /\
      (!v2. ~(walk s t2 = term_Var v2))
      ==> UNIFYR s t1 t2 (ext_s_check s v1 (walk s t2))) /\
   (!s t1 t2 v2.
      (!v1. ~(walk s t1 = term_Var v1)) /\
      walk s t2 = term_Var v2
      ==> UNIFYR s t1 t2 (ext_s_check s v2 (walk s t1))) /\
   (!s t1 t2 t1a t1d t2a t2d sx r.
      walk s t1 = term_Pair t1a t1d /\
      walk s t2 = term_Pair t2a t2d /\
      UNIFYR s t1a t2a (SOME sx) /\ UNIFYR sx t1d t2d r
      ==> UNIFYR s t1 t2 r) /\
   (!s t1 t2 t1a t1d t2a t2d.
      walk s t1 = term_Pair t1a t1d /\
      walk s t2 = term_Pair t2a t2d /\
      UNIFYR s t1a t2a NONE
      ==> UNIFYR s t1 t2 NONE) /\
   (!s t1 t2 c1 c2.
      walk s t1 = term_Const c1 /\ walk s t2 = term_Const c2
      ==> UNIFYR s t1 t2 (if c1 = c2 then SOME s else NONE)) /\
   (!s t1 t2 t1a t1d c2.
      walk s t1 = term_Pair t1a t1d /\ walk s t2 = term_Const c2
      ==> UNIFYR s t1 t2 NONE) /\
   (!s t1 t2 c1 t2a t2d.
      walk s t1 = term_Const c1 /\ walk s t2 = term_Pair t2a t2d
      ==> UNIFYR s t1 t2 NONE)`;;

let unify_def = new_definition
  `unify s t1 t2 = @r. UNIFYR s t1 t2 r`;;
