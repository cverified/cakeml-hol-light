(* ======================================================== *)
(*  word_simpProof: ported from HOL4's
    compiler/backend/proofs/word_simpProofScript.sml  *)
(* ======================================================== *)

(*
  Correctness proof for word_simp
*)

needs "basis/pure/mllist.ml";;
needs "compiler/backend/semantics/wordProps.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/backend/stackLang.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/backend/word_simp.ml";;
(* HOL4 ancestors outside the port: alist *)

(* HOL4 word_simpProofScript.sml:10: the ML values that the
   definitions below antiquote *)

(** verification of Seq_assoc **)

(** verification of const_fp **)

(* gc *)

let is_gc_word_const_def = cake_define_list
  [`is_gc_word_const (wordLang_Loc _3 _4) = T`;
   `is_gc_word_const (wordLang_Word w) = is_gc_const w`];;

let gc_fun_const_ok_def = cake_define
  `gc_fun_const_ok (f:('a word_loc) list#('a word->'a word_loc)#('a
  word->bool)#(store_name,'a word_loc)fmap->(('a word_loc) list#('a
  word->'a word_loc)#(store_name,'a word_loc)fmap) option) =
     (!x y. f x = SOME y ==> EVERY2 (\a b. is_gc_word_const a ==>
       b = a) (FST x) (FST y))`;;


let sf_gc_consts_def = cake_define
  `sf_gc_consts (StackFrame _5 l0 sv h) (StackFrame _6 l0' sw h') =
   (EVERY2 (\(ak,av) (bk,bv). (ak = bk) /\ (is_gc_word_const av
     ==> bv = av)) sv sw /\ l0 = l0' /\ h = h')`;;

(* HOL4 word_simpProofScript.sml:146-152: code that the source has in
   a comment *)

(* Assign *)

(* Move *)

(* TODO: In need of cleanup *)

(* If *)

(* Helpful lemmas about locals *)
(*TODO move*)

(* Lookup thms *)

(* LIST_REL/EVERY2 thms *)

(* Stack thms *)

(*TODO delete*)

(* HOL4 word_simpProofScript.sml:510-514: code that the source has in
   a comment *)

let get_above_handler_def = cake_define
  `get_above_handler s = (match EL (LENGTH (stack s) -
  (wordSem_state_handler s + 1)) (stack s) with StackFrame _7 _8 _9
  (SOME (h,_10,_11)) -> h)`;;

(*TODO move*)

(* HOL4 word_simpProofScript.sml:761-851: ML code, not ported *)

(* HOL4 word_simpProofScript.sml:853-891: ML code, not ported *)

(* HOL4 word_simpProofScript.sml:893: ML code, not ported *)

(* HOL4 word_simpProofScript.sml:1149-1156: ML code, not ported *)

(* HOL4 word_simpProofScript.sml:1158: ML code, not ported *)

(* the duplicate-if pass *)

(* HOL4 word_simpProofScript.sml:1282-1285: ML code, not ported *)

(* putting it all together *)
