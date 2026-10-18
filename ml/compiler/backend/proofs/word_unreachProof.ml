(* ======================================================== *)
(*  word_unreachProof: ported from HOL4's
    compiler/backend/proofs/word_unreachProofScript.sml
    A proof theory about word_unreach.ml, with 1 definition and 19
    theorems.  Needed by word_to_wordProof.ml.  *)
(* ======================================================== *)

(*
  Correctness proof for word_unreach
*)

needs "compiler/backend/reg_alloc/reg_alloc.ml";;
needs "compiler/backend/semantics/wordConvs.ml";;
needs "compiler/backend/semantics/wordProps.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/backend/stackLang.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/backend/word_unreach.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "misc/misc.ml";;

(* HOL4 word_unreachProofScript.sml:10: the ML values that the
   definitions below antiquote *)

(* -- proofs about semantics -- *)

let word_unreachProof_evaluate_Skip_Seq =
  cake_theorem "evaluate_Skip_Seq"
  (fun () ->
    `wordSem_evaluate ((Seq Skip p:clash_tree),s) = wordSem_evaluate
  (p,(s:('a,'c,'ffi)wordSem_state))`)
  CHEAT_TAC;;

let word_unreachProof_evaluate_Seq_Skip =
  cake_theorem "evaluate_Seq_Skip"
  (fun () ->
    `!p1 s. wordSem_evaluate ((Seq p1 Skip:clash_tree),s) =
  wordSem_evaluate (p1,(s:('a,'c,'ffi)wordSem_state))`)
  CHEAT_TAC;;

let word_unreachProof_evaluate_Seq_assoc =
  cake_theorem "evaluate_Seq_assoc"
  (fun () ->
    `wordSem_evaluate ((Seq p1 (Seq p2 p3):clash_tree),s) =
  wordSem_evaluate (Seq (Seq p1 p2) p3,s)`)
  CHEAT_TAC;;

let ALL_DISTINCT_merge_moves = cake_theorem "ALL_DISTINCT_merge_moves"
  (fun () ->
    `ALL_DISTINCT (MAP FST (word_unreach_merge_moves l1 l2))`)
  CHEAT_TAC;;

let copy_vars_def = cake_define_list
  [`word_unreachProof_copy_vars [] from to = to`;
   `word_unreachProof_copy_vars ((l,r) :: rest) from to =
      sptree_insert l (THE (sptree_lookup r from))
        (word_unreachProof_copy_vars rest from to)`];;
hol4_overload "copy_vars" "word_unreachProof_copy_vars";;

let copy_vars_append = cake_theorem "copy_vars_append"
  (fun () ->
    `!xs ys from to.
       word_unreachProof_copy_vars (xs ++ ys) from to =
         word_unreachProof_copy_vars xs from
         (word_unreachProof_copy_vars ys from to)`)
  CHEAT_TAC;;

let evaluate_Move = cake_theorem "evaluate_Move"
  (fun () ->
    `wordSem_evaluate (wordLang_Move pri moves,s) =
     (if ALL_DISTINCT (MAP FST moves) then
       match wordSem_get_vars (MAP SND moves) s with
         NONE -> (SOME wordSem_Error,s) | SOME l ->
           (NONE,wordSem_state_locals_fupd (K
           (word_unreachProof_copy_vars moves (wordSem_state_locals s)
           (wordSem_state_locals s))) s) else (SOME wordSem_Error,s))`)
  CHEAT_TAC;;

let copy_vars_MEM_acc = cake_theorem "copy_vars_MEM_acc"
  (fun () ->
    `!xs acc n w.
       MEM n acc ==>
       sptree_insert n w (word_unreachProof_copy_vars (anub xs acc)
         s t) =
       sptree_insert n w (word_unreachProof_copy_vars (anub xs
         (FILTER (\x. ~(n = x)) acc)) s t)`)
  CHEAT_TAC;;

let copy_vars_anub = cake_theorem "copy_vars_anub"
  (fun () ->
    `word_unreachProof_copy_vars (anub xs []) =
  word_unreachProof_copy_vars xs`)
  CHEAT_TAC;;

let lookup_copy_vars_ignore = cake_theorem "lookup_copy_vars_ignore"
  (fun () ->
    `!l1 h1 x y.
       ALOOKUP l1 h1 = NONE ==>
       sptree_lookup h1 (word_unreachProof_copy_vars l1 x y) =
         sptree_lookup h1 y`)
  CHEAT_TAC;;

let lookup_copy_vars = cake_theorem "lookup_copy_vars"
  (fun () ->
    `!l1 h1 y s t z.
       ALOOKUP l1 h1 = SOME y /\
       sptree_lookup h1 (word_unreachProof_copy_vars l1 s t) = SOME
         z ==>
       THE (sptree_lookup y s) = z`)
  CHEAT_TAC;;

let get_vars_IS_SOME_lookup =
  cake_theorem "get_vars_IS_SOME_lookup[local]"
  (fun () ->
    `!xs s.
       (?ws. wordSem_get_vars xs s = SOME ws) <=>
       EVERY (\x. IS_SOME (sptree_lookup x (wordSem_state_locals
         s))) xs`)
  CHEAT_TAC;;

let IMP_EVERY_MAP_SND_anub = cake_theorem "IMP_EVERY_MAP_SND_anub"
  (fun () ->
    `!xs acc p.
       EVERY p (MAP SND xs) ==>
       EVERY p (MAP SND (anub xs acc))`)
  CHEAT_TAC;;

let merge_moves_Skip = cake_theorem "merge_moves_Skip"
  (fun () ->
    `!l1 l2 s res s1.
       wordSem_evaluate (Seq (wordLang_Move n1 l1) (wordLang_Move
         n2 l2),s) = (res,s1) /\ ~(
       res = SOME wordSem_Error) ==>
       wordSem_evaluate (wordLang_Move m
         (word_unreach_merge_moves l1 l2),s) = (res,s1)`)
  CHEAT_TAC;;

let merge_moves_thm = cake_theorem "merge_moves_thm"
  (fun () ->
    `!p l1 l2 s res s1.
       wordSem_evaluate (Seq (wordLang_Move n1 l1) (Seq
         (wordLang_Move n2 l2) p),s) = (res,s1) /\ ~(
       res = SOME wordSem_Error) ==>
       wordSem_evaluate (Seq (wordLang_Move m
         (word_unreach_merge_moves l1 l2)) p,s) = (res,s1)`)
  CHEAT_TAC;;

let evaluate_SimpSeq = cake_theorem "evaluate_SimpSeq[local]"
  (fun () ->
    `wordSem_evaluate (Seq p1 p2,s) = (res,s1) /\ ~(res = SOME
  wordSem_Error) ==>
     wordSem_evaluate (SimpSeq p1 p2,s) = (res,s1)`)
  CHEAT_TAC;;

let push_env_handler = cake_theorem "push_env_handler[local]"
  (fun () ->
    `wordSem_push_env x' (match handler with NONE -> NONE | SOME
  (y1,q2,y2,y3) -> SOME (y1,Seq_assoc_right q2 Skip,y2,y3))
  (wordSem_dec_clock s) =
     wordSem_push_env x' handler (wordSem_dec_clock s)`)
  CHEAT_TAC;;

let evaluate_Seq_assoc_right_lemma =
  cake_theorem "evaluate_Seq_assoc_right_lemma"
  (fun () ->
    `!p1 p2 s res s1.
       wordSem_evaluate (Seq p1 p2,(s:('a,'c,'ffi)wordSem_state)) =
         (res,s1) /\ ~(res = SOME wordSem_Error) ==>
       wordSem_evaluate (Seq_assoc_right p1 p2,s) = (res,s1)`)
  CHEAT_TAC;;

let evaluate_Loop_body_eq = cake_theorem "evaluate_Loop_body_eq[local]"
  (fun () ->
    `(!(s:('a,'b,'c)wordSem_state) res s1. wordSem_evaluate ((p1:'a
  wordLang_prog),s) = (res,s1) /\ ~(res = SOME wordSem_Error) ==>
                 wordSem_evaluate ((p2:'a wordLang_prog),s) =
                   (res,s1)) ==>
     (!(s:('a,'b,'c)wordSem_state) res s1. wordSem_evaluate (Loop
       names p1 exit_names,s) = (res,s1) /\ ~(res = SOME wordSem_Error)
       ==>
                wordSem_evaluate (Loop names p2 exit_names,s) =
                  (res,s1))`)
  CHEAT_TAC;;

(* HOL4 word_unreachProofScript.sml:351-364: a proof *)

(* HOL4 word_unreachProofScript.sml:366: a proof *)

let evaluate_remove_unreach = cake_theorem "evaluate_remove_unreach"
  (fun () ->
    `!p s res s1.
       wordSem_evaluate (p,s) = (res,s1) /\ ~(res = SOME
         wordSem_Error) ==>
       wordSem_evaluate (remove_unreach p,s) = (res,s1)`)
  CHEAT_TAC;;
