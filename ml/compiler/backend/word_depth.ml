(* ======================================================== *)
(*  word_depth: ported from HOL4's
    compiler/backend/word_depthScript.sml  *)
(* ======================================================== *)

(*
  Computes the call graph for wordLang program with an acyclic call
  graph. This graph is in turn used to compute the max stack depth
  used by the wordLang program.
*)

needs "compiler/backend/stackLang.ml";;
needs "compiler/backend/wordLang.ml";;
needs "lib/sptree.ml";;
needs "semantics/ast.ml";;

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

let max_depth_def = cake_define
  `max_depth frame_sizes Leaf = SOME 0 /\
   max_depth frame_sizes Unknown = NONE /\
   max_depth frame_sizes (Const n t) =
     OPTION_MAP ((+) n) (max_depth frame_sizes t) /\
   max_depth frame_sizes (Branch t1 t2) =
     OPTION_MAP2 MAX (max_depth frame_sizes t1) (max_depth
       frame_sizes t2) /\
   max_depth frame_sizes (Call n t) =
     OPTION_MAP2 (+) (lookup n frame_sizes) (max_depth frame_sizes
       t)`;;

(* computing the call graph *)

let mk_Branch_def = cake_define
  `mk_Branch t1 t2 =
     (if t1 = t2 then t1 else
     if t1 = Leaf then t2 else
     if t2 = Leaf then t1 else
     if t1 = Unknown then t1 else
     if t2 = Unknown then t2 else
       Branch t1 t2)`;;

let _ = size_thms "prog";;
(* HOL4 termination: \\ rpt strip_tac \\ fs [size_delete] \\
   imp_res_tac miscTheory.lookup_zero \\ fs [] *)
let call_graph_def = cake_define_wf
  `(inv_image (MEASURE I LEX MEASURE I LEX MEASURE I)
         (\(funs,n,ns,total,p). (size funs,total - LENGTH
           ns,prog_size (K 0) p)))`
  `call_graph funs n ns total x5 =
        match x5 with
          (Seq p1 p2) ->
        mk_Branch (call_graph funs n ns total p1) (call_graph funs n
          ns total p2)
        | (If _1 _2 _3 p1 p2) ->
        mk_Branch (call_graph funs n ns total p1) (call_graph funs n
          ns total p2)
        | (Call ret dest args handler) ->
        match dest with NONE -> Unknown | SOME d ->
          (if MEM d ns /\ ret = NONE then Leaf else
          match lookup d funs with NONE -> Unknown | SOME
            ((a:num),body) ->
            (match ret with NONE ->
              (if LENGTH ns < total then
                 mk_Branch (Call d (Leaf))
                   (call_graph funs d (d :: ns) total body) else
                     Leaf) | SOME (_4,_5,ret_prog,_6,_7) ->
              (let new_funs = delete d funs in
                match handler with NONE -> Branch (Call n (Call d
                  Leaf))
                      (mk_Branch (Call n (call_graph new_funs d [d]
                        total body))
                              (call_graph funs n ns total ret_prog))
                                | SOME (_8,p,_9,_10) -> Branch (Call n
                                (Const 3 (Call d Leaf)))
                   (mk_Branch (Call n (Const 3 (call_graph new_funs d
                     [d] total body)))
                   (mk_Branch (call_graph funs n ns total p)
                              (call_graph funs n ns total
                                ret_prog))))))
        | (MustTerminate p) -> call_graph funs n ns total p
        | (Alloc _11 _12) -> Call n Leaf
        | (Install _13 _14 _15 _16 _17) -> Unknown
        | (Loop _18 body _19) -> call_graph funs n ns total body
        | _20 -> Leaf`;;

let full_call_graph_def = cake_define
  `full_call_graph n funs =
     (match lookup n funs with NONE -> Unknown | SOME (a,prog) ->
       Branch (Call n Leaf)
                              (call_graph funs n [n] (size funs)
                                prog))`;;

let max_depth_graphs_def = cake_define
  `max_depth_graphs ss [] all' funs all_funs = SOME 0 /\
   max_depth_graphs ss (n :: ns) all' funs all_funs =
     (match lookup n all_funs with NONE -> NONE | SOME (a,body) ->
         OPTION_MAP2 MAX (lookup n ss)
        (OPTION_MAP2 MAX (max_depth ss (call_graph funs n all' (size
          all_funs) body))
                         (max_depth_graphs ss ns all' funs
                           all_funs)))`;;
