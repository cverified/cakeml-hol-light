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

needs "compiler/backend/wordLang.ml";;
needs "misc/misc.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "word_unreach"
  ["wordLang"];;

(* function that makes all Seq associate to the right *)

let dest_Seq_Move_def = new_definition
  `dest_Seq_Move x1 =
   match x1 with
     word_Move n l -> SOME (n,l,word_Skip)
   | word_Seq (word_Move n l) rest -> SOME (n,l,rest)
   | _ -> NONE`;;

let word_unreach_merge_moves_def = new_definition
  `word_unreach_merge_moves l1 l2 =
     let l2' = MAP (\(x,y). match ALOOKUP l1 y with NONE -> (x,y)
                            | SOME v -> (x,v)) l2 in
       anub (APPEND l2' l1) ([]:num list)`;;

let SimpSeq_def = new_definition
  `SimpSeq p1 (p2:'a word_prog) =
     let default = word_Seq p1 p2 in
       if p2 = word_Skip then p1 else match p1 with word_Skip -> p2
         | word_Raise _ -> p1
         | word_Return _ _ -> p1
         | word_Break _ -> p1
         | word_Continue _ -> p1
         | word_Move n1 l1 ->
             (match dest_Seq_Move p2 with NONE -> default
              | SOME (n2,l2,rest) ->
                    // if n1 ≠ n2 then default else
                    let l = word_unreach_merge_moves l1 l2 in
                      if rest = word_Skip then word_Move (MAX n1 n2) l
                      else word_Seq (word_Move (MAX n1 n2) l) rest)
         | _ -> default`;;

make_size "word_prog";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let seq_assoc_right_def,seq_assoc_right_ind = define_wf
  `MEASURE (\(x0,x1). word_prog_size (\x. 0) x0)`
  `Seq_assoc_right p1 acc =
     match p1 with
       word_Skip -> acc
     | word_Seq q1 q2 ->
        Seq_assoc_right q1 (Seq_assoc_right q2 acc)
     | word_If v n r q1 q2 ->
        SimpSeq (word_If v n r (Seq_assoc_right q1 word_Skip)
          (Seq_assoc_right q2 word_Skip)) acc
     | word_MustTerminate q ->
        SimpSeq (word_MustTerminate (Seq_assoc_right q word_Skip)) acc
     | word_Call ret_prog dest args handler ->
        (match ret_prog with NONE -> word_Call ret_prog dest args handler
        | SOME (x1,x2,q1,x3,x4) ->
            SimpSeq (word_Call (SOME (x1,x2,Seq_assoc_right q1
              word_Skip,x3,x4))
              dest args
                 (match handler with NONE -> NONE
                  | SOME (y1,q2,y2,y3) -> SOME (y1,Seq_assoc_right q2
                    word_Skip,y2,y3))) acc)
     | word_Loop names body exit_names ->
        SimpSeq (word_Loop names (Seq_assoc_right body word_Skip)
          exit_names) acc
     | p1 -> SimpSeq p1 acc`;;

let remove_unreach_def = new_definition
  `remove_unreach (e:'a word_prog) =
     Seq_assoc_right e word_Skip`;;

(* [local] *)
let remove_unreach_test = prove
 (`remove_unreach (word_Seq (word_Move 1 [(1,11); (2,22); (3,33)])
                       (word_Move 1 [(3,1); (2,99)])) =
   word_Move 1 [(3,11); (2,99); (1,11)]`,
  CHEAT_TAC);;

(* and the interface *)
let _ = unhide_overloads ();;
