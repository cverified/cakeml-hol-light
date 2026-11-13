(* ======================================================== *)
(*  word_unreach: ported from HOL4's
    compiler/backend/word_unreachScript.sml
    A definition theory, with 5 definitions and 1 theorem.  Needed
    by backend.ml, backend_passes.ml, wordConvsProof.ml,
    word_to_word.ml, word_to_wordProof.ml and word_unreachProof.ml.  *)
(* ======================================================== *)

(*
  This compilation pass removes trivially unreachable code.
*)

needs "compiler/backend/stackLang.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;

(* the theories whose names the Ancestors blocks of the source
   bring, which are the ones that its statements read: the
   overloads of every other theory come out of the interface
   while this file loads *)
let _ = hol4_ancestors "word_unreach"
  ["wordLang"];;

(* function that makes all Seq associate to the right *)

let dest_Seq_Move_def = new_definition
  `dest_Seq_Move x1 =
      match x1 with
        wordLang_Move n l -> SOME (n,l,Skip)
      | (Seq (wordLang_Move n l) rest) -> SOME (n,l,rest)
      | _1 -> NONE`;;

let word_unreach_merge_moves_def = new_definition
  `word_unreach_merge_moves l1 l2 =
     (let l2' = MAP (\(x,y). match ALOOKUP l1 y with NONE -> (x,y) |
       SOME v -> (x,v)) l2 in
       anub (l2' ++ l1) ([]:num list))`;;
hol4_overload "merge_moves" "word_unreach_merge_moves";;

let SimpSeq_def = new_definition
  `SimpSeq p1 (p2:'a wordLang_prog) =
     (let default = Seq p1 p2 in
       if p2 = Skip then p1 else
         match p1 with Skip -> p2 | Raise _2 -> p1 | Return _3 _4 ->
           p1 | Break _5 -> p1 | Continue _6 -> p1 | wordLang_Move n1 l1
           ->
             (match dest_Seq_Move p2 with NONE -> default | SOME
               (n2,l2,rest) ->
                    // if n1 ≠ n2 then default else
                    (let l = word_unreach_merge_moves l1 l2 in
                      if rest = Skip then wordLang_Move (MAX n1
                        n2) l else Seq (wordLang_Move (MAX n1 n2) l)
                        rest)) | _7 -> default)`;;

let _ = size_thms "wordLang_prog";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let seq_assoc_right_def,seq_assoc_right_ind = define_wf
  `MEASURE (\(x0,x1). wordLang_prog_size (\x. 0) x0)`
  [`Seq_assoc_right p1 acc =
        match p1 with
          wordLang_Skip -> acc
        | (Seq q1 q2) ->
        Seq_assoc_right q1 (Seq_assoc_right q2 acc)
        | (If v n r q1 q2) ->
        SimpSeq (If v n r (Seq_assoc_right q1 Skip) (Seq_assoc_right
          q2 Skip)) acc
        | (wordLang_MustTerminate q) ->
        SimpSeq (wordLang_MustTerminate (Seq_assoc_right q Skip))
          acc
        | (Call ret_prog dest args handler) ->
        (match ret_prog with NONE -> Call ret_prog dest args handler
          | SOME (x1,x2,q1,x3,x4) ->
            SimpSeq (Call (SOME (x1,x2,Seq_assoc_right q1
              Skip,x3,x4))
              dest args
                 (match handler with NONE -> NONE | SOME
                   (y1,q2,y2,y3) -> SOME (y1,Seq_assoc_right q2
                   Skip,y2,y3))) acc)
        | (Loop names body exit_names) ->
        SimpSeq (Loop names (Seq_assoc_right body Skip) exit_names)
          acc
        | p1 -> SimpSeq p1 acc`];;

let remove_unreach_def = new_definition
  `remove_unreach (e:'a wordLang_prog) =
     Seq_assoc_right e Skip`;;

(* [local] *)
let remove_unreach_test = prove
 (`remove_unreach (wordLang_Seq (wordLang_Move 1 [(1,11); (2,22);
  (3,33)])
                       (wordLang_Move 1 [(3,1); (2,99)])) =
   wordLang_Move 1 [(3,11); (2,99); (1,11)]`,
  CHEAT_TAC);;

(* and the overloads that this file cannot see are back in the
   interface *)
let _ = unhide_overloads ();;
