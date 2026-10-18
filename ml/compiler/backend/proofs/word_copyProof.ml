(* ======================================================== *)
(*  word_copyProof: ported from HOL4's
    compiler/backend/proofs/word_copyProofScript.sml  *)
(* ======================================================== *)

(*
  Correctness proof for word_copy
*)

needs "compiler/backend/reg_alloc/reg_alloc.ml";;
needs "compiler/backend/semantics/wordConvs.ml";;
needs "compiler/backend/semantics/wordProps.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/backend/word_copy.ml";;
needs "lib/sptree.ml";;

(* HOL4 word_copyProofScript.sml:10: the ML values that the
   definitions below antiquote *)

let CPstate_inv_def = cake_define
  `CPstate_inv cs = (
    (!v c. sptree_lookup v (copy_state_to_eq cs) = SOME c ==> c <
      copy_state_next cs) /\
    (!c. c IN domain (copy_state_from_eq cs) ==> c < copy_state_next
      cs) /\
    (!s c. ALOOKUP (copy_state_store_to_eq cs) s = SOME c ==> c <
      copy_state_next cs) /\
    (!c v. sptree_lookup c (copy_state_from_eq cs) = SOME v ==>
      sptree_lookup v (copy_state_to_eq cs) = SOME c))`;;

(* As a corollary, different classes have different representatives *)
(* unused *)

let both_alloc_vars_def = cake_define
  `both_alloc_vars (t,s) = (is_alloc_var t /\ is_alloc_var s)`;;

(* t := s *)

let CPstate_models_def = cake_define
  `CPstate_models cs S <=>
   (!v c vrep.
     sptree_lookup v (copy_state_to_eq cs) = SOME c ==>
     sptree_lookup c (copy_state_from_eq cs) = SOME vrep ==>
     sptree_lookup v (wordSem_state_locals S) = sptree_lookup vrep
       (wordSem_state_locals S)) /\
   (!s c vrep.
     ALOOKUP (copy_state_store_to_eq cs) s = SOME c ==>
     sptree_lookup c (copy_state_from_eq cs) = SOME vrep ==>
     FLOOKUP (wordSem_state_store S) s = sptree_lookup vrep
       (wordSem_state_locals S))`;;

(* unused *)
(* HOL4 word_copyProofScript.sml:740-750: code that the source has in
   a comment *)

(* HOL4 word_copyProofScript.sml:872-895: ML code, not ported *)
(* HOL4 word_copyProofScript.sml:896-903: code that the source has in
   a comment *)
(* HOL4 word_copyProofScript.sml:904-906: ML code, not ported *)
        (* use appropriate case_cong *)
(* HOL4 word_copyProofScript.sml:908-916: ML code, not ported *)

(* "inst" is constant wordSem$inst *)

(* HOL4 word_copyProofScript.sml:966-981: code that the source has in
   a comment *)

(* Conditional body congruence for Loop: if the body transformation
   preserves semantics when the body doesn't error, then the Loop
   transformation preserves semantics when the Loop doesn't error. *)

(* HOL4 word_copyProofScript.sml:1386-1395: ML code, not ported *)

(* HOL4 word_copyProofScript.sml:1397: ML code, not ported *)

(* Main semantics result *)
