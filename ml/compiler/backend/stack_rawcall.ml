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

needs "compiler/backend/closLang.ml";;
needs "compiler/backend/dataLang.ml";;
needs "compiler/backend/data_to_word.ml";;
needs "compiler/backend/stackLang.ml";;
needs "lib/sptree.ml";;
needs "semantics/ast.ml";;

(* the theories whose names the Ancestors blocks of the source
   bring, which are the ones that its statements read: the
   overloads of every other theory come out of the interface
   while this file loads *)
let _ = hol4_ancestors "stack_rawcall"
  ["data_to_word"; "stackLang"];;

(* collect stack allocation information *)

let seq_stack_alloc_def = cake_define
  `seq_stack_alloc (p:'a stackLang_prog) =
     (match p with Seq (stackLang_StackAlloc k) _1 -> SOME k | _2
       -> NONE)`;;

let seq_stack_alloc_pmatch = prove
 (`seq_stack_alloc (p:'a stackLang_prog) =
     (match p with Seq (stackLang_StackAlloc k) _3 -> SOME k | _4
       -> NONE)`,
  CHEAT_TAC);;

let collect_info_def = cake_define_list
  [`collect_info [] f = f`;
   `collect_info ((n,(b:'a stackLang_prog)) :: xs) f =
         collect_info xs (match seq_stack_alloc b with NONE ->
           f | SOME k -> insert n k f)`];;

(* optimise based on stack allocation information *)

let dest_case_def = cake_define
  `dest_case (p1:'a stackLang_prog) (p2:'a stackLang_prog) =
     (match p1 with stackLang_StackFree k -> (match p2 with Call
       NONE (INL d) NONE -> SOME (k,d) | _5 -> NONE) | _6 -> NONE)`;;

let dest_case_pmatch = prove
 (`dest_case (p1:'a stackLang_prog) (p2:'a stackLang_prog) =
     (match p1 with stackLang_StackFree k -> (match p2 with Call
       NONE (INL d) NONE -> SOME (k,d) | _7 -> NONE) | _8 -> NONE)`,
  CHEAT_TAC);;

let comp_seq_def = cake_define
  `comp_seq (p1:'a stackLang_prog) (p2:'a stackLang_prog) i (default:'a
  stackLang_prog) =
   (match dest_case p1 p2 with SOME (k,dest) ->
       (match lookup dest i with NONE -> default | SOME l ->
            (if l = k then stackLang_RawCall dest else
            if l < k then Seq (stackLang_StackFree (k - l))
              (stackLang_RawCall dest) else
                Seq Tick (Seq (stackLang_StackAlloc (l - k))
                  (stackLang_RawCall dest)))) | _9 -> default)`;;

let stack_rawcall_comp_def = cake_define
  `stack_rawcall_comp i (p:'a stackLang_prog) =
     (match p with Seq p1 p2 -> comp_seq p1 p2 i (Seq
       (stack_rawcall_comp i p1) (stack_rawcall_comp i p2)) | If c r ri
       p1 p2 -> If c r ri (stack_rawcall_comp i p1) (stack_rawcall_comp
       i p2) | Loop p1 -> Loop (stack_rawcall_comp i p1) | Call (SOME
       (p1,lr,l1,l2)) dest NONE ->
         Call (SOME (stack_rawcall_comp i p1,lr,l1,l2)) dest NONE |
           Call (SOME (p1,lr,l1,l2)) dest (SOME (p2,k1,k2)) ->
         Call (SOME (stack_rawcall_comp i p1,lr,l1,l2)) dest (SOME
           (stack_rawcall_comp i p2,k1,k2)) | _10 -> p)`;;
hol4_overload "comp" "stack_rawcall_comp";;
(* HOL4 stack_rawcallScript.sml:85-93: a theorem that HOL4 states as
   the value of an ML expression: comp_pmatch *)

let comp_top_def = cake_define
  `comp_top i (p:'a stackLang_prog) =
     (match p with Seq p1 p2 -> Seq (comp i p1) (comp i p2) | _11
       -> comp i p)`;;

let comp_top_pmatch = prove
 (`comp_top i (p:'a stackLang_prog) =
     (match p with Seq p1 p2 -> Seq (comp i p1) (comp i p2) | _12
       -> comp i p)`,
  CHEAT_TAC);;

let stack_rawcall_compile_def = cake_define
  `stack_rawcall_compile prog =
     (let i = collect_info prog LN in
       MAP (\(n,(b:'a stackLang_prog)). (n,comp_top i b)) prog)`;;
hol4_overload "compile" "stack_rawcall_compile";;

(* and the overloads that this file cannot see are back in the
   interface *)
let _ = unhide_overloads ();;
