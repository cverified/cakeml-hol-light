(* ======================================================== *)
(*  stack_rawcall: ported from HOL4's
    compiler/backend/stack_rawcallScript.sml
    A definition theory, with 7 definitions and 4 theorems.  Needed
    by stack_rawcallProof.ml, stack_to_lab.ml and
    stack_to_labProof.ml.  *)
(* ======================================================== *)

(*
  This compiler phase introduces calls past the stack allocation code
  that is present at almost every start of function. A call past stack
  allocation is called a RawCall. RawCalls are introduced to shortcut
  some bookkeeping during tail-calls to known locations, i.e
  `Call NONE (INL dest) ..`.
*)

needs "compiler/backend/data_to_word.ml";;
needs "compiler/backend/stackLang.ml";;
needs "lib/sptree.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "stack_rawcall"
  ["data_to_word"; "stackLang"];;

(* collect stack allocation information *)

let seq_stack_alloc_def = new_definition
  `seq_stack_alloc (p:'a stackLang_prog) =
     (match p with word_bignum_Seq (stackLang_StackAlloc k) _1 ->
       SOME k | _2 -> NONE)`;;

let seq_stack_alloc_pmatch = prove
 (`seq_stack_alloc (p:'a stackLang_prog) =
     (match p with word_bignum_Seq (stackLang_StackAlloc k) _3 ->
       SOME k | _4 -> NONE)`,
  CHEAT_TAC);;

let collect_info_def,collect_info_ind = define_rec
  [`collect_info [] f = f`;
   `collect_info (CONS (n,(b:'a stackLang_prog)) xs) f =
         collect_info xs (match seq_stack_alloc b with NONE ->
             f | SOME k -> sptree_insert n k f)`];;

(* optimise based on stack allocation information *)

let dest_case_def = new_definition
  `dest_case (p1:'a stackLang_prog) (p2:'a stackLang_prog) =
     (match p1 with stackLang_StackFree k -> (match p2 with
       word_depth_Call NONE (INL d) NONE -> SOME (k,d) | _5 -> NONE)
       | _6 -> NONE)`;;

let dest_case_pmatch = prove
 (`dest_case (p1:'a stackLang_prog) (p2:'a stackLang_prog) =
     (match p1 with stackLang_StackFree k -> (match p2 with
       word_depth_Call NONE (INL d) NONE -> SOME (k,d) | _7 -> NONE) |
       _8 -> NONE)`,
  CHEAT_TAC);;

let comp_seq_def = new_definition
  `comp_seq (p1:'a stackLang_prog) (p2:'a stackLang_prog) i (default:'a
  stackLang_prog) =
   (match dest_case p1 p2 with SOME (k,dest) ->
       (match sptree_lookup dest i with NONE -> default | SOME l ->
            (if l = k then stackLang_RawCall dest else
            if l < k then word_bignum_Seq (stackLang_StackFree (k -
              l)) (stackLang_RawCall dest) else
                word_bignum_Seq wordLang_Tick (word_bignum_Seq
                  (stackLang_StackAlloc (l - k)) (stackLang_RawCall
                  dest)))) | _9 -> default)`;;

let _ = size_thms "stackLang_prog";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let stack_rawcall_comp_def,stack_rawcall_comp_ind = define_wf
  `MEASURE (\(x0,x1). stackLang_prog_size (\x. 0) x1)`
  [`stack_rawcall_comp i (p:'a stackLang_prog) =
     (match p with word_bignum_Seq p1 p2 -> comp_seq p1 p2 i
       (word_bignum_Seq (stack_rawcall_comp i p1) (stack_rawcall_comp i
       p2)) | word_bignum_If c r ri p1 p2 -> word_bignum_If c r ri
       (stack_rawcall_comp i p1) (stack_rawcall_comp i p2) |
       word_bignum_Loop p1 -> word_bignum_Loop (stack_rawcall_comp i
       p1) | word_depth_Call (SOME (p1,lr,l1,l2)) dest NONE ->
         word_depth_Call (SOME (stack_rawcall_comp i p1,lr,l1,l2))
           dest NONE | word_depth_Call (SOME (p1,lr,l1,l2)) dest (SOME
           (p2,k1,k2)) ->
         word_depth_Call (SOME (stack_rawcall_comp i
           p1,lr,l1,l2)) dest (SOME (stack_rawcall_comp i
           p2,k1,k2)) | _10 -> p)`];;
(* HOL4 stack_rawcallScript.sml:85-93: a theorem that HOL4 states as
   the value of an ML expression: comp_pmatch *)

let comp_top_def = new_definition
  `comp_top i (p:'a stackLang_prog) =
     (match p with word_bignum_Seq p1 p2 -> word_bignum_Seq
       (stack_rawcall_comp i p1) (stack_rawcall_comp i p2) | _11 ->
       stack_rawcall_comp i p)`;;

let comp_top_pmatch = prove
 (`comp_top i (p:'a stackLang_prog) =
     (match p with word_bignum_Seq p1 p2 -> word_bignum_Seq
       (stack_rawcall_comp i p1) (stack_rawcall_comp i p2) | _12 ->
       stack_rawcall_comp i p)`,
  CHEAT_TAC);;

let stack_rawcall_compile_def = new_definition
  `stack_rawcall_compile prog =
     (let i = collect_info prog LN in
       MAP (\(n,(b:'a stackLang_prog)). (n,comp_top i b)) prog)`;;
