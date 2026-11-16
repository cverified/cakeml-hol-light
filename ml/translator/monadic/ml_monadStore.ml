(* ======================================================== *)
(*  ml_monadStore: ported from HOL4's
    translator/monadic/ml_monadStoreScript.sml
    A definition theory, with no definitions and 25 theorems.  No
    file of the port needs it.  *)
(* ======================================================== *)

(*
  This file defines theorems and lemmas used in the ml_monadStoreLib
*)

needs "basis/pure/mlstring.ml";;
needs "characteristic/cf.ml";;
needs "characteristic/cfApp.ml";;
needs "characteristic/cfFFIType.ml";;
needs "characteristic/cfHeapsBase.ml";;
needs "characteristic/cfStore.ml";;
needs "lib/set_sep.ml";;
needs "semantics/evaluate.ml";;
needs "semantics/namespace.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "translator/ml_prog.ml";;
needs "translator/monadic/ml_monad_translator.ml";;
needs "translator/monadic/ml_monad_translatorBase.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "ml_monadStore"
  ["cf"; "cfApp"; "cfHeapsBase"; "cfStore"; "cfTactics"; "evaluate";
   "ml_monad_translatorBase"; "semanticPrimitives"];;

let _ = do_list hide_constant ["C"; "TYPE"];;

(* HOL4 ml_monadStoreScript.sml:11-12: a theorem that HOL4 states as the
   value of an ML expression: HCOND_EXTRACT *)

(* HOL4 ml_monadStoreScript.sml:14-15: a theorem that HOL4 states as the
   value of an ML expression: SEP_EXISTS_SEPARATE *)

(* HOL4 ml_monadStoreScript.sml:17-18: a theorem that HOL4 states as the
   value of an ML expression: SEP_EXISTS_INWARD *)

let ALLOCATE_ARRAY_evaluate = prove
 (`!env s n xname xv.
    (nsLookup (sem_env_v env) (Short xname) = SOME xv) ==>
    eval_rel s env (ast_App ast_Aalloc [ast_Lit (ast_IntLit (&n)); ast_Var
      (Short xname)])
      (semanticPrimitives_state_refs_fupd (K (APPEND
        (semanticPrimitives_state_refs s) [semanticPrimitives_Varray (REPLICATE
        n xv)])) s)
      (semanticPrimitives_Loc T (LENGTH (semanticPrimitives_state_refs
        s)))`,
  CHEAT_TAC);;

let ALLOCATE_EMPTY_RARRAY_evaluate = prove
 (`!env s.
     eval_rel s env (ast_App ast_Opref [ast_App ast_AallocEmpty [ast_Con
       NONE []]])
       (semanticPrimitives_state_refs_fupd (K (APPEND (APPEND
         (semanticPrimitives_state_refs s) [semanticPrimitives_Varray []])
         [semanticPrimitives_Refv (semanticPrimitives_Loc T (LENGTH
         (semanticPrimitives_state_refs s)))])) s)
       (semanticPrimitives_Loc T (LENGTH (semanticPrimitives_state_refs s)
         + 1))`,
  CHEAT_TAC);;

let LIST_REL_REPLICATE = prove
 (`!n TYPE' x v. TYPE' x v ==> ALL2 TYPE' (REPLICATE n x) (REPLICATE n v)`,
  CHEAT_TAC);;

let GC_INWARDS = prove
 (`GC * A = A * GC`,
  CHEAT_TAC);;

let GC_DUPLICATE_0 = prove
 (`H * GC = H * GC * GC`,
  CHEAT_TAC);;

let GC_DUPLICATE_1 = prove
 (`A * (B * GC * C) = A * GC * (B * GC * C)`,
  CHEAT_TAC);;

let GC_DUPLICATE_2 = prove
 (`A * (B * GC) = A * GC * (B * GC)`,
  CHEAT_TAC);;

let GC_DUPLICATE_3 = prove
 (`A * GC * B = GC * (A * GC * B)`,
  CHEAT_TAC);;

let store2heap_aux_decompose_store1 = prove
 (`A (store2heap_aux n a) ==>
   B (store2heap_aux (n + LENGTH a) b) ==>
   (A * B) (store2heap_aux n (APPEND a b))`,
  CHEAT_TAC);;

let store2heap_aux_decompose_store2 = prove
 (`A (store2heap_aux n [a]) ==>
   B (store2heap_aux (n + 1) b) ==>
   (A * B) (store2heap_aux n (CONS a b))`,
  CHEAT_TAC);;

let cons_to_append = prove
 (`CONS a (CONS b c) = APPEND [a; b] c`,
  CHEAT_TAC);;

let append_empty = prove
 (`a = APPEND a []`,
  CHEAT_TAC);;

(* H_STAR_GC_SAT_IMP *)
let ml_monadStore_H_STAR_GC_SAT_IMP = prove
 (`H s ==> (H * GC) s`,
  CHEAT_TAC);;

let store2heap_REF_SAT = prove
 (`(REF (semanticPrimitives_Loc T l) v) (store2heap_aux l
  [semanticPrimitives_Refv v])`,
  CHEAT_TAC);;

let store2heap_eliminate_ffi_thm = prove
 (`H (store2heap (semanticPrimitives_state_refs s)) ==> (GC * H) (st2heap
  (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8 list->word8
  list->ffi->(ffi cfHeapsBase_ffi_result) option)) list) s)`,
  CHEAT_TAC);;

let rarray_exact_thm = prove
 (`((l = l' + 1) /\ (n = l')) ==>
   RARRAY (semanticPrimitives_Loc T l) av (store2heap_aux n
     [semanticPrimitives_Varray av; semanticPrimitives_Refv
     (semanticPrimitives_Loc T l')])`,
  CHEAT_TAC);;

let farray_exact_thm = prove
 (`(n = l) ==>
   ARRAY (semanticPrimitives_Loc T l) av (store2heap_aux n
     [semanticPrimitives_Varray av])`,
  CHEAT_TAC);;

let eliminate_inherited_references_thm = prove
 (`!a b. H (store2heap_aux (LENGTH a) b) ==>
   (GC * H) (store2heap_aux 0 (APPEND a b))`,
  CHEAT_TAC);;

let eliminate_substore_thm = prove
 (`(H1 * GC * H2) (store2heap_aux (n + LENGTH a) b) ==>
   (H1 * GC * H2) (store2heap_aux n (APPEND a b))`,
  CHEAT_TAC);;

let eliminate_store_elem_thm = prove
 (`(H1 * GC * H2) (store2heap_aux (n + 1) b) ==>
   (H1 * GC * H2) (store2heap_aux n (CONS a b))`,
  CHEAT_TAC);;

let H_STAR_empty = prove
 (`H * emp = H`,
  CHEAT_TAC);;

(* H_STAR_TRUE *)
let ml_monadStore_H_STAR_TRUE = prove
 (`(H * &T = H) /\ (&T * H = H)`,
  CHEAT_TAC);;

(* and the names it reads as variables are constants again *)
let _ = do_list unhide_constant
  ["C";
   "TYPE"];;

(* and the interface *)
let _ = unhide_overloads ();;
