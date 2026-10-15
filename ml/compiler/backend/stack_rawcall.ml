(* ======================================================== *)
(*  stack_rawcall: ported from HOL4's
    compiler/backend/stack_rawcallScript.sml  *)
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
needs "compiler/backend/pattern_matching/pattern_semantics.ml";;
needs "compiler/backend/stackLang.ml";;
needs "lib/sptree.ml";;

(* collect stack allocation information *)

let seq_stack_alloc_def = cake_define
  `seq_stack_alloc (p:'a stackLang_prog) =
     (match p with Seq (stackLang_StackAlloc k) _1 -> SOME k | _2
       -> NONE)`;;

let collect_info_def = cake_define_list
  [`collect_info [] f = f`;
   `collect_info ((n,(b:'a stackLang_prog)) :: xs) f =
         collect_info xs (match seq_stack_alloc b with NONE -> f
           | SOME k -> insert n k f)`];;

(* optimise based on stack allocation information *)

let dest_case_def = cake_define
  `dest_case (p1:'a stackLang_prog) (p2:'a stackLang_prog) =
     (match p1 with stackLang_StackFree k -> (match p2 with Call
       NONE (INL d) NONE -> SOME (k,d) | _3 -> NONE) | _4 -> NONE)`;;

let comp_seq_def = cake_define
  `comp_seq (p1:'a stackLang_prog) (p2:'a stackLang_prog) i (default:'a
  stackLang_prog) =
   (match dest_case p1 p2 with SOME (k,dest) ->
       (match lookup dest i with NONE -> default | SOME l ->
            (if l = k then stackLang_RawCall dest else
            if l < k then Seq (stackLang_StackFree (k - l))
              (stackLang_RawCall dest) else
                Seq Tick (Seq (stackLang_StackAlloc (l - k))
                  (stackLang_RawCall dest)))) | _5 -> default)`;;

(* HOL4 ML code, not ported:
local
val q = `
  comp i (p:'a stackLang$prog) =
    case p of
    | Seq p1 p2 => comp_seq p1 p2 i (Seq (comp i p1) (comp i p2))
    | If c r ri p1 p2 => If c r ri (comp i p1) (comp i p2)
    | Loop p1 => Loop (comp i p1)
    | Call (SOME (p1,lr,l1,l2)) dest NONE =>
        Call (SOME (comp i p1,lr,l1,l2)) dest NONE
    | Call (SOME (p1,lr,l1,l2)) dest (SOME (p2,k1,k2)) =>
        Call (SOME (comp i p1,lr,l1,l2)) dest (SOME (comp i p2,k1,k2))
    | _ => p`
in
val comp_def = Define q;
*)

let comp_top_def = cake_define
  `comp_top i (p:'a stackLang_prog) =
     (match p with Seq p1 p2 -> Seq (data_to_word_comp i p1)
       (data_to_word_comp i p2) | _6 -> data_to_word_comp i p)`;;

let compile_def = cake_define
  `stack_rawcall_compile prog =
     (let i = collect_info prog LN in
       MAP (\(n,(b:'a stackLang_prog)). (n,comp_top i b)) prog)`;;
hol4_overload "compile" "stack_rawcall_compile";;
