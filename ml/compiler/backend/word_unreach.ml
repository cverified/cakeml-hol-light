(* ======================================================== *)
(*  word_unreach: ported from HOL4's
    compiler/backend/word_unreachScript.sml  *)
(* ======================================================== *)

(*
  This compilation pass removes trivially unreachable code.
*)

needs "compiler/backend/wordLang.ml";;

(* function that makes all Seq associate to the right *)

let dest_Seq_Move_def = cake_define
  `dest_Seq_Move x1 =
      match x1 with
        (wordLang_Move n l) -> SOME (n,l,wordLang_Skip)
      | (wordLang_Seq (wordLang_Move n l) rest) -> SOME (n,l,rest)
      | _1 -> NONE`;;

let merge_moves_def = cake_define
  `word_unreach_merge_moves l1 l2 =
     (let l2' = MAP (\(x,y). match ALOOKUP l1 y with NONE -> (x,y) |
       SOME v -> (x,v)) l2 in
       anub (l2' ++ l1) ([]:num list))`;;

let SimpSeq_def = cake_define
  `SimpSeq p1 (p2:'a wordLang_prog) =
     (let default = wordLang_Seq p1 p2 in
       if p2 = wordLang_Skip then p1 else
         match p1 with wordLang_Skip -> p2 | wordLang_Raise _2 -> p1
           | wordLang_Return _3 _4 -> p1 | wordLang_Break _5 -> p1 |
           wordLang_Continue _6 -> p1 | wordLang_Move n1 l1 ->
             (match dest_Seq_Move p2 with NONE -> default | SOME
               (n2,l2,rest) ->
                    (let l = word_unreach_merge_moves l1 l2 in
                      if rest = wordLang_Skip then wordLang_Move
                        (MAX n1 n2) l else wordLang_Seq
                        (wordLang_Move (MAX n1 n2) l) rest)) | _7 ->
                        default)`;;

let Seq_assoc_right_def = cake_define
  `Seq_assoc_right p1 acc =
        match p1 with
          wordLang_Skip -> acc
        | (wordLang_Seq q1 q2) ->
        Seq_assoc_right q1 (Seq_assoc_right q2 acc)
        | (wordLang_If v n r q1 q2) ->
        SimpSeq (wordLang_If v n r (Seq_assoc_right q1 wordLang_Skip)
          (Seq_assoc_right q2 wordLang_Skip)) acc
        | (wordLang_MustTerminate q) ->
        SimpSeq (wordLang_MustTerminate (Seq_assoc_right q
          wordLang_Skip)) acc
        | (wordLang_Call ret_prog dest args handler) ->
        match ret_prog with NONE -> wordLang_Call ret_prog dest args
          handler | SOME (x1,x2,q1,x3,x4) ->
            SimpSeq (wordLang_Call (SOME (x1,x2,Seq_assoc_right q1
              wordLang_Skip,x3,x4))
              dest args
                 (match handler with NONE -> NONE | SOME
                   (y1,q2,y2,y3) -> SOME (y1,Seq_assoc_right q2
                   wordLang_Skip,y2,y3))) acc
        | (wordLang_Loop names body exit_names) ->
        SimpSeq (wordLang_Loop names (Seq_assoc_right body
          wordLang_Skip) exit_names) acc
        | p1 -> SimpSeq p1 acc`;;

let remove_unreach_def = cake_define
  `remove_unreach (e:'a wordLang_prog) =
     Seq_assoc_right e wordLang_Skip`;;
