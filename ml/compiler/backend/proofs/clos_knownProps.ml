(* ======================================================== *)
(*  clos_knownProps: ported from HOL4's
    compiler/backend/proofs/clos_knownPropsScript.sml  *)
(* ======================================================== *)

(*
  Lemmas used in proof of clos_known
*)

needs "compiler/backend/clos_known.ml";;
needs "compiler/backend/semantics/closProps.ml";;
needs "lib/mergesort.ml";;
needs "lib/sptree.ml";;

(* HOL4 clos_knownPropsScript.sml:10: ML code, not ported *)

(* See merge as a join operation on a semi-lattice: it's a join because
   it's
   a little akin to a union: as merge is used, more and more values
     might
   inhabit the approximation, with Other at the top corresponding to
   anything at all. *)

let subapprox_def = cake_define
  `subapprox a1 a2 <=> merge a1 a2 = a2`;;

(* HOL4 clos_knownPropsScript.sml:61: ML code, not ported *)

let better_definedg_def = cake_define
  `better_definedg g1 g2 <=>
     (!k. k IN domain g1 ==> k IN domain g2 /\ subapprox (THE
       (sptree_lookup k g1)) (THE (sptree_lookup k g2)))`;;
