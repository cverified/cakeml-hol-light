(* ======================================================== *)
(*  word_depthProof: ported from HOL4's
    compiler/backend/proofs/word_depthProofScript.sml
    A proof theory about word_depth.ml, with no definitions and 12
    theorems.  Needed by data_to_word_bignumProof.ml.  *)
(* ======================================================== *)

(*
  Proves correctness of the max_depth applied to the call graph of a
  wordLang program as produced by the word_depth$call_graph function.
*)

needs "compiler/backend/semantics/backendProps.ml";;
needs "compiler/backend/semantics/wordProps.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/backend/stackLang.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/backend/word_depth.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "lib/sptree.ml";;

(* the theories whose names the Ancestors blocks of the source
   bring, which are the ones that its statements read: the
   overloads of every other theory come out of the interface
   while this file loads *)
let _ = hol4_ancestors "word_depthProof"
  ["backendProps"; "wordLang"; "wordProps"; "wordSem"; "word_depth"];;

(* [local,simp] *)
let option_le_X_MAX_X = prove
 (`option_le x (OPTION_MAP2 MAX m x) /\
   option_le x (OPTION_MAP2 MAX x m)`,
  CHEAT_TAC);;

(* [local,simp] *)
let OPTION_MAP2_MAX_IDEMPOT = prove
 (`OPTION_MAP2 MAX x x = x`,
  CHEAT_TAC);;

(* [local,simp] *)
let OPTION_MAP2_SOME_0 = prove
 (`OPTION_MAP2 (+) x (SOME 0) = x /\
   OPTION_MAP2 MAX x (SOME 0) = x`,
  CHEAT_TAC);;

let max_depth_mk_Branch = prove
 (`!t1 t2. max_depth s (mk_Branch t1 t2) = max_depth s (Branch t1 t2)`,
  CHEAT_TAC);;

let MEM_max_depth_graphs = prove
 (`!ns name y.
     MEM name ns /\ sptree_lookup name code = SOME y ==>
     option_le (max_depth_graphs ss [name] xs funs code)
               (max_depth_graphs ss ns xs funs code)`,
  CHEAT_TAC);;

let option_le_max_depth_graph = prove
 (`!funs h ns1 t x1 ns2.
     set_of_list ns2 SUBSET set_of_list ns1 /\ LENGTH ns2 <= LENGTH
       ns1 ==>
     option_le
       (max_depth ss (call_graph funs h ns1 t x1))
       (max_depth ss (call_graph funs h ns2 t x1))`,
  CHEAT_TAC);;

let option_le_max_depth_graphs = prove
 (`!ns ns1 ns2.
     set_of_list ns2 SUBSET set_of_list ns1 /\ LENGTH ns2 <= LENGTH
       ns1 ==>
     option_le (max_depth_graphs ss ns ns1 funs funs2)
               (max_depth_graphs ss ns ns2 funs funs2)`,
  CHEAT_TAC);;

(* [local] *)
let LENGTH_LESS_size = prove
 (`!name ns funs y.
     ~(MEM name ns) /\ set_of_list ns SUBSET domain funs /\
       ALL_DISTINCT ns /\
     sptree_lookup name funs = SOME y ==>
     LENGTH ns < sptree_size funs`,
  CHEAT_TAC);;

let max_depth_call_graph_lemma = prove
 (`!prog s res s1 funs n ns funs2.
     wordSem_evaluate (prog,s) = (res,s1) /\
     subspt funs funs2 /\ subspt funs2 (wordSem_state_code s) /\
       wordSem_state_locals_size
     s = sptree_lookup n (wordSem_state_stack_size s) /\ ~(res = SOME
       wordSem_Error) /\
     MEM n ns /\ ALL_DISTINCT ns /\ set_of_list ns SUBSET domain
       funs2 ==>
     option_le (wordSem_state_stack_max s1)
       (OPTION_MAP2 MAX (wordSem_state_stack_max s)
         (OPTION_MAP2 (+) (stack_size (stack s))
           (OPTION_MAP2 MAX
             (max_depth_graphs (wordSem_state_stack_size s) ns ns
               funs funs2)
             (max_depth (wordSem_state_stack_size s) (call_graph funs
               n ns (sptree_size funs2) prog))))) /\
     (~(max_depth_graphs (wordSem_state_stack_size s) ns ns funs
       funs2 = NONE) /\ ~(max_depth (wordSem_state_stack_size s)
       (call_graph funs n ns (sptree_size funs2) prog) = NONE) ==>
       wordSem_state_stack_size
      s1 = wordSem_state_stack_size s /\
      ((res = NONE \/ (?k. res = SOME (Break k)) \/ (?k. res = SOME
        (Continue k))) ==> wordSem_state_locals_size s1 =
        wordSem_state_locals_size s))`,
  CHEAT_TAC);;

(* HOL4 word_depthProofScript.sml:290-382: a proof *)
  (* non-tail-call case *)
(* HOL4 word_depthProofScript.sml:384-732: a proof *)


(* HOL4 word_depthProofScript.sml:735-753: a proof *)
  (* cont_loop case: res' = NONE or Continue 0 *)
(* HOL4 word_depthProofScript.sml:755-757: a proof *)
     (* res' = NONE *)
(* HOL4 word_depthProofScript.sml:759-769: a proof *)
     (* res' = SOME (Continue 0) *)
(* HOL4 word_depthProofScript.sml:771-782: a proof *)
  (* exit_loop case — Break 0 auto-solved by gvs with strengthened IH *)
(* HOL4 word_depthProofScript.sml:784-786: a proof *)

(* HOL4 word_depthProofScript.sml:788: a proof *)

let max_depth_call_graph = prove
 (`!prog s res s1 funs n a.
     wordSem_evaluate (prog,s) = (res,s1) /\ subspt funs
       (wordSem_state_code s) /\
     sptree_lookup n funs = SOME (a,prog) /\
       wordSem_state_locals_size
     s = sptree_lookup n (wordSem_state_stack_size s) /\ ~(res = SOME
       wordSem_Error) ==>
     option_le (wordSem_state_stack_max s1)
       (OPTION_MAP2 MAX (wordSem_state_stack_max s)
         (OPTION_MAP2 (+) (stack_size (stack s))
           (max_depth (wordSem_state_stack_size s) (full_call_graph
             n funs))))`,
  CHEAT_TAC);;

let max_depth_Call_SOME = prove
 (`wordSem_evaluate (Call (SOME (n1,n2,Skip,n3,n4)) (SOME dest) args
  NONE,s) = (res,s1) /\ ~(res = SOME wordSem_Error) /\ subspt funs
  (wordSem_state_code s) ==>
   option_le (wordSem_state_stack_max s1)
     (OPTION_MAP2 MAX (wordSem_state_stack_max s)
       (OPTION_MAP2 (+) (wordSem_state_locals_size s)
         (OPTION_MAP2 (+) (stack_size (stack s))
           (max_depth (wordSem_state_stack_size s) (full_call_graph
             dest funs)))))`,
  CHEAT_TAC);;

let max_depth_Call_NONE = prove
 (`wordSem_evaluate (Call NONE (SOME dest) args NONE,s) = (res,s1) /\
  ~(res = SOME wordSem_Error) /\ subspt funs (wordSem_state_code s) ==>
   option_le (wordSem_state_stack_max s1)
     (OPTION_MAP2 MAX (wordSem_state_stack_max s)
       (OPTION_MAP2 (+) (stack_size (stack s))
         (max_depth (wordSem_state_stack_size s) (full_call_graph
           dest funs))))`,
  CHEAT_TAC);;

(* and the overloads that this file cannot see are back in the
   interface *)
let _ = unhide_overloads ();;
