(* ======================================================== *)
(*  clos_knownProps: ported from HOL4's
    compiler/backend/proofs/clos_knownPropsScript.sml
    A proof theory about clos_known.ml, with 2 definitions and 20
    theorems.  Needed by clos_knownProof.ml.  *)
(* ======================================================== *)

(*
  Lemmas used in proof of clos_known
*)

needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/clos_known.ml";;
needs "compiler/backend/semantics/closProps.ml";;
needs "lib/sptree.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "clos_knownProps"
  ["closProps"; "clos_known"];;

(* HOL4 clos_knownPropsScript.sml:10: ML code, not ported *)

let merge_Other = prove
 (`clos_known_merge (clos_known_Other:val_approx) a =
  (clos_known_Other:val_approx) /\ clos_known_merge a clos_known_Other
  = clos_known_Other`,
  CHEAT_TAC);;
add_simp merge_Other;;

let merge_Impossible = prove
 (`clos_known_merge a clos_known_Impossible = a`,
  CHEAT_TAC);;
add_simp merge_Impossible;;

(* See merge as a join operation on a semi-lattice: it's a join because it's
   a little akin to a union: as merge is used, more and more values might
   inhabit the approximation, with Other at the top corresponding to
   anything at all. *)
let merge_comm = prove
 (`!a1 a2. clos_known_merge a1 a2 = clos_known_merge a2 a1`,
  CHEAT_TAC);;

let merge_assoc = prove
 (`!a1 a2 a3. clos_known_merge a1 (clos_known_merge a2 a3) =
  clos_known_merge (clos_known_merge a1 a2) a3`,
  CHEAT_TAC);;

let merge_idem = prove
 (`clos_known_merge a a = a`,
  CHEAT_TAC);;
add_simp merge_idem;;

let subapprox_def = new_definition
  `subapprox a1 a2 <=> clos_known_merge a1 a2 = a2`;;

(* HOL4 clos_knownPropsScript.sml:61: ML code, not ported *)
hol4_overload "◁" "subapprox";;

let subapprox_refl = prove
 (`subapprox a a`,
  CHEAT_TAC);;
add_simp subapprox_refl;;

let subapprox_trans = prove
 (`subapprox a1 a2 /\ subapprox a2 a3 ==> subapprox a1 a3`,
  CHEAT_TAC);;

let subapprox_antisym = prove
 (`subapprox a1 a2 /\ subapprox a2 a1 ==> a1 = a2`,
  CHEAT_TAC);;

let subapprox_merge = prove
 (`subapprox a (clos_known_merge a b) /\ subapprox a (clos_known_merge
  b a)`,
  CHEAT_TAC);;
add_simp subapprox_merge;;

let subapprox_Other = prove
 (`(subapprox clos_known_Other a <=> (a = clos_known_Other)) /\
  subapprox a clos_known_Other`,
  CHEAT_TAC);;
add_simp subapprox_Other;;

let subapprox_Int = prove
 (`(subapprox a (clos_known_Int i) <=> a = clos_known_Int i \/ a =
  clos_known_Impossible) /\
   (subapprox (clos_known_Int i) a <=> a = clos_known_Int i \/ a =
     clos_known_Other)`,
  CHEAT_TAC);;
add_simp subapprox_Int;;


let subapprox_ClosNoInline = prove
 (`(subapprox a (clos_known_ClosNoInline m n) <=> a =
  clos_known_ClosNoInline m n \/ a = clos_known_Impossible) /\
   (subapprox (clos_known_ClosNoInline m n) a <=> a =
     clos_known_ClosNoInline m n \/ a = clos_known_Other)`,
  CHEAT_TAC);;
add_simp subapprox_ClosNoInline;;

let subapprox_Clos = prove
 (`(subapprox a (clos_known_Clos m n e s) <=> a = clos_known_Clos m n e
  s \/ a = clos_known_Impossible) /\
   (subapprox (clos_known_Clos m n e s) a <=> a = clos_known_Clos m
     n e s \/ a = clos_known_Other)`,
  CHEAT_TAC);;
add_simp subapprox_Clos;;

let subapprox_Impossible = prove
 (`(subapprox a clos_known_Impossible <=> a = clos_known_Impossible)
  /\ subapprox clos_known_Impossible a`,
  CHEAT_TAC);;
add_simp subapprox_Impossible;;

let subapprox_Tuple = prove
 (`subapprox (clos_known_Tuple tg1 as1) (clos_known_Tuple tg2 as2) <=>
  tg1 = tg2 /\ ALL2 subapprox as1 as2`,
  CHEAT_TAC);;
add_simp subapprox_Tuple;;

let better_definedg_def = new_definition
  `better_definedg g1 g2 <=>
     (!k. k IN domain g1 ==> k IN domain g2 /\ subapprox (THE
       (sptree_lookup k g1)) (THE (sptree_lookup k g2)))`;;

let better_definedg_refl = prove
 (`better_definedg g g`,
  CHEAT_TAC);;
add_simp better_definedg_refl;;

let better_definedg_trans = prove
 (`better_definedg g1 g2 /\ better_definedg g2 g3 ==> better_definedg
  g1 g3`,
  CHEAT_TAC);;

let known_op_better_definedg = prove
 (`known_op opn apxs g0 = (a,g) ==> better_definedg g0 g`,
  CHEAT_TAC);;

let known_better_definedg = prove
 (`!c es apxs g0 alist g.
     known c es apxs g0 = (alist,g) ==> better_definedg g0 g`,
  CHEAT_TAC);;

let mk_Ticks_alt = prove
 (`(!t tc e. clos_known_mk_Ticks t tc 0 e = e) /\
   (!t tc n e. clos_known_mk_Ticks t tc (SUC n) e =
     clos_known_mk_Ticks t (tc + 1) n (closLang_Tick (mk_cons t tc)
     e))`,
  CHEAT_TAC);;
