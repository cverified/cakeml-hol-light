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
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/clos_known.ml";;
needs "compiler/backend/semantics/closProps.ml";;
needs "lib/mergesort.ml";;
needs "lib/sptree.ml";;

(* HOL4 clos_knownPropsScript.sml:10: ML code, not ported *)

let merge_Other = cake_theorem "merge_Other[simp]"
  (fun () ->
    `merge (clos_known_Other:val_approx) a =
  (clos_known_Other:val_approx) /\ merge a clos_known_Other =
  clos_known_Other`)
  CHEAT_TAC;;

let merge_Impossible = cake_theorem "merge_Impossible[simp]"
  (fun () ->
    `merge a clos_known_Impossible = a`)
  CHEAT_TAC;;

(* See merge as a join operation on a semi-lattice: it's a join because it's
   a little akin to a union: as merge is used, more and more values might
   inhabit the approximation, with Other at the top corresponding to
   anything at all. *)
let merge_comm = cake_theorem "merge_comm"
  (fun () ->
    `!a1 a2. merge a1 a2 = merge a2 a1`)
  CHEAT_TAC;;

let merge_assoc = cake_theorem "merge_assoc"
  (fun () ->
    `!a1 a2 a3. merge a1 (merge a2 a3) = merge (merge a1 a2) a3`)
  CHEAT_TAC;;

let merge_idem = cake_theorem "merge_idem[simp]"
  (fun () ->
    `merge a a = a`)
  CHEAT_TAC;;

let subapprox_def = cake_define
  `subapprox a1 a2 <=> merge a1 a2 = a2`;;

(* HOL4 clos_knownPropsScript.sml:61: ML code, not ported *)
hol4_overload "◁" "subapprox";;

let subapprox_refl = cake_theorem "subapprox_refl[simp]"
  (fun () ->
    `(subapprox) a a`)
  CHEAT_TAC;;

let subapprox_trans = cake_theorem "subapprox_trans"
  (fun () ->
    `(subapprox) a1 a2 /\ (subapprox) a2 a3 ==> (subapprox) a1 a3`)
  CHEAT_TAC;;

let subapprox_antisym = cake_theorem "subapprox_antisym"
  (fun () ->
    `(subapprox) a1 a2 /\ (subapprox) a2 a1 ==> a1 = a2`)
  CHEAT_TAC;;

let subapprox_merge = cake_theorem "subapprox_merge[simp]"
  (fun () ->
    `(subapprox) a (merge a b) /\ (subapprox) a (merge b a)`)
  CHEAT_TAC;;

let subapprox_Other = cake_theorem "subapprox_Other[simp]"
  (fun () ->
    `((subapprox) clos_known_Other a <=> (a = clos_known_Other)) /\
  (subapprox) a clos_known_Other`)
  CHEAT_TAC;;

let subapprox_Int = cake_theorem "subapprox_Int[simp]"
  (fun () ->
    `((subapprox) a (Int i) <=> a = Int i \/ a = clos_known_Impossible)
  /\
     ((subapprox) (Int i) a <=> a = Int i \/ a =
       clos_known_Other)`)
  CHEAT_TAC;;


let subapprox_ClosNoInline = cake_theorem "subapprox_ClosNoInline[simp]"
  (fun () ->
    `((subapprox) a (clos_known_ClosNoInline m n) <=> a =
  clos_known_ClosNoInline m n \/ a = clos_known_Impossible) /\
     ((subapprox) (clos_known_ClosNoInline m n) a <=> a =
       clos_known_ClosNoInline m n \/ a = clos_known_Other)`)
  CHEAT_TAC;;

let subapprox_Clos = cake_theorem "subapprox_Clos[simp]"
  (fun () ->
    `((subapprox) a (clos_known_Clos m n e s) <=> a = clos_known_Clos m
  n e s \/ a = clos_known_Impossible) /\
     ((subapprox) (clos_known_Clos m n e s) a <=> a =
       clos_known_Clos m n e s \/ a = clos_known_Other)`)
  CHEAT_TAC;;

let subapprox_Impossible = cake_theorem "subapprox_Impossible[simp]"
  (fun () ->
    `((subapprox) a clos_known_Impossible <=> a =
  clos_known_Impossible) /\ (subapprox) clos_known_Impossible a`)
  CHEAT_TAC;;

let subapprox_Tuple = cake_theorem "subapprox_Tuple[simp]"
  (fun () ->
    `(subapprox) (clos_known_Tuple tg1 as1) (clos_known_Tuple tg2 as2)
  <=> tg1 = tg2 /\ LIST_REL subapprox as1 as2`)
  CHEAT_TAC;;

let better_definedg_def = cake_define
  `better_definedg g1 g2 <=>
     (!k. k IN domain g1 ==> k IN domain g2 /\ (subapprox) (THE
       (sptree_lookup k g1)) (THE (sptree_lookup k g2)))`;;

let better_definedg_refl = cake_theorem "better_definedg_refl[simp]"
  (fun () ->
    `better_definedg g g`)
  CHEAT_TAC;;

let better_definedg_trans = cake_theorem "better_definedg_trans"
  (fun () ->
    `better_definedg g1 g2 /\ better_definedg g2 g3 ==>
  better_definedg g1 g3`)
  CHEAT_TAC;;

let known_op_better_definedg = cake_theorem "known_op_better_definedg"
  (fun () ->
    `known_op opn apxs g0 = (a,g) ==> better_definedg g0 g`)
  CHEAT_TAC;;

let known_better_definedg = cake_theorem "known_better_definedg"
  (fun () ->
    `!c es apxs g0 alist g.
       known c es apxs g0 = (alist,g) ==> better_definedg g0 g`)
  CHEAT_TAC;;

let mk_Ticks_alt = cake_theorem "mk_Ticks_alt"
  (fun () ->
    `(!t tc e. clos_known_mk_Ticks t tc 0 e = e) /\
     (!t tc n e. clos_known_mk_Ticks t tc (SUC n) e =
       clos_known_mk_Ticks t (tc + 1) n (closLang_Tick (mk_cons t tc)
       e))`)
  CHEAT_TAC;;
