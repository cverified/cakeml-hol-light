(* ======================================================== *)
(*  word_depth: ported from HOL4's
    compiler/backend/word_depthScript.sml
    A definition theory, with 5 definitions, 1 datatype and no
    theorems.  Needed by dataSem.ml, data_to_word.ml,
    data_to_word_bignumProof.ml and word_depthProof.ml.  *)
(* ======================================================== *)

(*
  Computes the call graph for wordLang program with an acyclic call
  graph. This graph is in turn used to compute the max stack depth
  used by the wordLang program.
*)

needs "compiler/backend/wordLang.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "word_depth"
  ["wordLang"];;

(* representation of acyclic call graph, i.e. call tree *)

let call_tree_INDUCT,call_tree_RECURSION = define_datatype
  "call_tree =
     word_depth_Leaf
   | word_depth_Unknown
   | word_depth_Const num call_tree
   | word_depth_Call num call_tree
   | word_depth_Branch call_tree call_tree";;

(* computing the max stack depth *)

let max_depth_def,max_depth_ind = define_rec
  `(max_depth frame_sizes word_depth_Leaf = SOME 0) /\
   (max_depth frame_sizes word_depth_Unknown = NONE) /\
   (max_depth frame_sizes (word_depth_Const n t) =
      OPTION_MAP ((+) n) (max_depth frame_sizes t)) /\
   (max_depth frame_sizes (word_depth_Branch t1 t2) =
      OPTION_MAP2 MAX (max_depth frame_sizes t1) (max_depth frame_sizes
          t2)) /\
   (max_depth frame_sizes (word_depth_Call n t) =
      OPTION_MAP2 (+) (sptree_lookup n frame_sizes) (max_depth
          frame_sizes t))`;;

(* computing the call graph *)

let mk_Branch_def = new_definition
  `mk_Branch t1 t2 =
     if t1 = t2 then t1 else if t1 = word_depth_Leaf then t2 else if t2 =
       word_depth_Leaf then t1 else if t1 = word_depth_Unknown then t1 else
       if t2 = word_depth_Unknown then t2 else word_depth_Branch t1 t2`;;

let call_graph_def,call_graph_ind = assume_definition_rec
  "termination (CHEAT_TAC)"
  `call_graph funs n ns total' x5 =
     match x5 with
       word_Seq p1 p2 ->
        mk_Branch (call_graph funs n ns total' p1) (call_graph funs n ns
          total' p2)
     | word_If _ _ _ p1 p2 ->
        mk_Branch (call_graph funs n ns total' p1) (call_graph funs n ns
          total' p2)
     | word_Call ret dest args handler ->
        (match dest with NONE -> word_depth_Unknown
        | SOME d ->
          (if MEM d ns /\ ret = NONE then word_depth_Leaf else match
            sptree_lookup d funs with NONE -> word_depth_Unknown
          | SOME ((a:num),body) ->
            (match ret with NONE ->
              (if LENGTH ns < total' then
                 mk_Branch (word_depth_Call d (word_depth_Leaf))
                   (call_graph funs d (CONS d ns) total' body)
               else word_depth_Leaf)
            | SOME (_,_,ret_prog,_,_) ->
              (let new_funs = sptree_delete d funs in
                match handler with NONE -> word_depth_Branch
                  (word_depth_Call n (word_depth_Call d word_depth_Leaf))
                      (mk_Branch (word_depth_Call n (call_graph new_funs d
                        [d] total' body))
                              (call_graph funs n ns total' ret_prog))
                | SOME (_,p,_,_) -> word_depth_Branch (word_depth_Call n
                  (word_depth_Const 3 (word_depth_Call d word_depth_Leaf)))
                   (mk_Branch (word_depth_Call n (word_depth_Const 3
                     (call_graph new_funs d [d] total' body)))
                   (mk_Branch (call_graph funs n ns total' p)
                              (call_graph funs n ns total' ret_prog)))))))
     | word_MustTerminate p -> call_graph funs n ns total' p
     | word_Alloc _ _ -> word_depth_Call n word_depth_Leaf
     | word_Install _ _ _ _ _ -> word_depth_Unknown
     | word_Loop _ body _ -> call_graph funs n ns total' body
     | _ -> word_depth_Leaf`;;

let full_call_graph_def = new_definition
  `full_call_graph n funs =
     match sptree_lookup n funs with NONE -> word_depth_Unknown
     | SOME (a,prog) -> word_depth_Branch (word_depth_Call n
       word_depth_Leaf)
                              (call_graph funs n [n] (sptree__size funs)
                                prog)`;;

let max_depth_graphs_def,max_depth_graphs_ind = define_rec
  `(max_depth_graphs ss [] all' funs all_funs = SOME 0) /\
   (max_depth_graphs ss (CONS n ns) all' funs all_funs =
      match sptree_lookup n all_funs with NONE -> NONE
      | SOME (a,body) ->
          OPTION_MAP2 MAX (sptree_lookup n ss)
         (OPTION_MAP2 MAX (max_depth ss (call_graph funs n all'
             (sptree__size all_funs) body))
                          (max_depth_graphs ss ns all' funs all_funs)))`;;

(* and the interface *)
let _ = unhide_overloads ();;
