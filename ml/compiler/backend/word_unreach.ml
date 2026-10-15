(* ======================================================== *)
(*  word_unreach: ported from HOL4's
    compiler/backend/word_unreachScript.sml  *)
(* ======================================================== *)

(*
  This compilation pass removes trivially unreachable code.
*)

needs "compiler/backend/stackLang.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;

(* function that makes all Seq associate to the right *)

let dest_Seq_Move_def = cake_define
  `dest_Seq_Move x1 =
      match x1 with
        (wordLang_Move n l) -> SOME (n,l,Skip)
      | (Seq (Move n l) rest) -> SOME (n,l,rest)
      | _1 -> NONE`;;

let merge_moves_def = cake_define
  `word_unreach_merge_moves l1 l2 =
     (let l2' = MAP (\(x,y). match ALOOKUP l1 y with NONE -> (x,y) |
       SOME v -> (x,v)) l2 in
       anub (l2' ++ l1) ([]:num list))`;;
hol4_overload "merge_moves" "word_unreach_merge_moves";;

let SimpSeq_def = cake_define
  `SimpSeq p1 (p2:'a wordLang_prog) =
     (let default = Seq p1 p2 in
       if p2 = Skip then p1 else
         match p1 with Skip -> p2 | Raise _2 -> p1 | Return _3 _4 ->
           p1 | Break _5 -> p1 | Continue _6 -> p1 | Move n1 l1 ->
             (match dest_Seq_Move p2 with NONE -> default | SOME
               (n2,l2,rest) ->
                    (let l = merge_moves l1 l2 in
                      if rest = Skip then Move (MAX n1 n2) l else
                        Seq (Move (MAX n1 n2) l) rest)) | _7 ->
                        default)`;;

let seq_assoc_right_def = cake_define
  `Seq_assoc_right p1 acc =
        match p1 with
          Skip -> acc
        | (Seq q1 q2) ->
        Seq_assoc_right q1 (Seq_assoc_right q2 acc)
        | (If v n r q1 q2) ->
        SimpSeq (If v n r (Seq_assoc_right q1 Skip) (Seq_assoc_right
          q2 Skip)) acc
        | (wordLang_MustTerminate q) ->
        SimpSeq (wordLang_MustTerminate (Seq_assoc_right q Skip)) acc
        | (Call ret_prog dest args handler) ->
        match ret_prog with NONE -> Call ret_prog dest args handler |
          SOME (x1,x2,q1,x3,x4) ->
            SimpSeq (Call (SOME (x1,x2,Seq_assoc_right q1
              Skip,x3,x4))
              dest args
                 (match handler with NONE -> NONE | SOME
                   (y1,q2,y2,y3) -> SOME (y1,Seq_assoc_right q2
                   Skip,y2,y3))) acc
        | (Loop names body exit_names) ->
        SimpSeq (Loop names (Seq_assoc_right body Skip) exit_names)
          acc
        | p1 -> SimpSeq p1 acc`;;

let remove_unreach_def = cake_define
  `remove_unreach (e:'a wordLang_prog) =
     Seq_assoc_right e Skip`;;
