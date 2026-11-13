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

needs "compiler/backend/stackLang.ml";;
needs "compiler/backend/wordLang.ml";;
needs "semantics/ast.ml";;

(* the theories whose names the Ancestors blocks of the source
   bring, which are the ones that its statements read: the
   overloads of every other theory come out of the interface
   while this file loads *)
let _ = hol4_ancestors "word_depth"
  ["wordLang"];;

(* representation of acyclic call graph, i.e. call tree *)

let call_tree_INDUCT,call_tree_RECURSION = define_datatype
  "call_tree = word_depth_Leaf | word_depth_Unknown | \
   word_depth_Const (num) (call_tree) | word_depth_Call (num) \
   (call_tree) | word_depth_Branch (call_tree) (call_tree)";;
hol4_overload "Leaf" "word_depth_Leaf";;
hol4_overload "Unknown" "word_depth_Unknown";;
hol4_overload "Const" "word_depth_Const";;
hol4_overload "Call" "word_depth_Call";;
hol4_overload "Branch" "word_depth_Branch";;

(* computing the max stack depth *)

let max_depth_def,max_depth_ind = define_rec
  [`max_depth frame_sizes (word_depth_Leaf:call_tree) = SOME 0`;
   `max_depth frame_sizes word_depth_Unknown = NONE`;
   `max_depth frame_sizes (Const n t:call_tree) =
      OPTION_MAP ((+) n) (max_depth frame_sizes t)`;
   `max_depth frame_sizes (word_depth_Branch t1 t2:call_tree) =
      OPTION_MAP2 MAX (max_depth frame_sizes t1) (max_depth
        frame_sizes t2)`;
   `max_depth frame_sizes (Call n t:call_tree) =
      OPTION_MAP2 (+) (sptree_lookup n frame_sizes) (max_depth
        frame_sizes t)`];;

(* computing the call graph *)

let mk_Branch_def = new_definition
  `mk_Branch t1 t2 =
     (if t1 = t2 then t1 else
     if t1 = word_depth_Leaf then t2 else
     if t2 = word_depth_Leaf then t1 else
     if t1 = word_depth_Unknown then t1 else
     if t2 = word_depth_Unknown then t2 else
       word_depth_Branch t1 t2)`;;

let _ = size_thms "wordLang_prog";;
let call_graph_def,call_graph_ind = assume_definition_rec
  "termination (CHEAT_TAC)"
  [`call_graph funs n ns total' x5 =
        match x5 with
          wordLang_Seq p1 p2 ->
        mk_Branch (call_graph funs n ns total' p1) (call_graph funs
          n ns total' p2)
        | (If _1 _2 _3 p1 p2) ->
        mk_Branch (call_graph funs n ns total' p1) (call_graph funs
          n ns total' p2)
        | (Call ret dest args handler) ->
        (match dest with NONE -> word_depth_Unknown | SOME d ->
          (if MEM d ns /\ ret = NONE then word_depth_Leaf else
          match sptree_lookup d funs with NONE -> word_depth_Unknown
            | SOME ((a:num),body) ->
            (match ret with NONE ->
              (if LENGTH ns < total' then
                 mk_Branch (Call d (word_depth_Leaf))
                   (call_graph funs d (d :: ns) total' body) else
                     word_depth_Leaf) | SOME (_4,_5,ret_prog,_6,_7) ->
              (let new_funs = sptree_delete d funs in
                match handler with NONE -> word_depth_Branch
                  (word_depth_Call n (word_depth_Call d
                  word_depth_Leaf))
                      (mk_Branch (Call n (call_graph new_funs d [d]
                        total' body))
                              (call_graph funs n ns total'
                                ret_prog)) | SOME (_8,p,_9,_10) ->
                                word_depth_Branch (word_depth_Call n
                                (Const 3 (word_depth_Call d
                                word_depth_Leaf)))
                   (mk_Branch (Call n (Const 3 (call_graph new_funs
                     d [d] total' body)))
                   (mk_Branch (call_graph funs n ns total' p)
                              (call_graph funs n ns total'
                                ret_prog)))))))
        | (wordLang_MustTerminate p) -> call_graph funs n ns total'
          p
        | (Alloc _11 _12) -> Call n word_depth_Leaf
        | (Install _13 _14 _15 _16 _17) -> word_depth_Unknown
        | (Loop _18 body _19) -> call_graph funs n ns total' body
        | _20 -> word_depth_Leaf`];;

let full_call_graph_def = new_definition
  `full_call_graph n funs =
     (match sptree_lookup n funs with NONE -> word_depth_Unknown |
       SOME (a,prog) -> word_depth_Branch (word_depth_Call n
       word_depth_Leaf)
                              (call_graph funs n [n] (sptree_size
                                funs) prog))`;;

let max_depth_graphs_def,max_depth_graphs_ind = define_rec
  [`max_depth_graphs ss [] all' funs all_funs = SOME 0`;
   `max_depth_graphs ss (n :: ns) all' funs all_funs =
      (match sptree_lookup n all_funs with NONE -> NONE | SOME
        (a,body) ->
          OPTION_MAP2 MAX (sptree_lookup n ss)
         (OPTION_MAP2 MAX (max_depth ss (call_graph funs n all'
           (sptree_size all_funs) body))
                          (max_depth_graphs ss ns all' funs
                            all_funs)))`];;

(* and the overloads that this file cannot see are back in the
   interface *)
let _ = unhide_overloads ();;
