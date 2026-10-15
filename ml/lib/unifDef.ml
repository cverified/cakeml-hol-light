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

cake_declare "oc" `:(num,(A)term)fmap->(A)term->num->bool`;;
cake_declare "unify"
  `:(num,(A)term)fmap->(A)term->(A)term->
      ((num,(A)term)fmap)option`;;

let ext_s_check_def = cake_define
  `ext_s_check s v t = (if oc s t v then NONE else SOME (s |+ (v,t)))`;;
