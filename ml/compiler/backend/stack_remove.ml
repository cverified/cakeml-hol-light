(* ======================================================== *)
(*  stack_remove: ported from HOL4's
    compiler/backend/stack_removeScript.sml
    A definition theory, with 27 definitions and 1 theorem.  Needed
    by backendProof.ml, backend_passes.ml, stack_removeProof.ml,
    stack_to_lab.ml and stack_to_labProof.ml.  *)
(* ======================================================== *)

(*
  This compiler phase implements all stack operations as normal memory
  load/store operations.
*)

needs "basis/pure/mlstring.ml";;
needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/stackLang.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "lib/byte.ml";;
needs "misc/misc.ml";;
(* for bytes_in_word *)
needs "semantics/ast.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "stack_remove"
  ["misc"; "mlstring"; "stackLang"];;

let _ = do_list hide_constant ["dummy"; "gc"; "gen_gc"];;


(* -- compiler -- *)

let max_stack_alloc_def = new_definition
  `max_stack_alloc = 255`;;

let word_offset_def = new_definition
  `word_offset n = (n2w (dimindex (:'a) DIV 8 * n):'a word)`;;

let store_list_def = new_definition
  `stack_remove_store_list = [NextFree; EndOfHeap; HeapLength; OtherHeap;
  TriggerGC;
                 AllocSize; Handler; Globals; GlobReal; ProgStart;
                   BitmapBase;
                 GenStart; CodeBuffer; CodeBufferEnd; BitmapBuffer;
                   BitmapBufferEnd;
                 Temp (n2w 00); Temp (n2w 01); Temp (n2w 02); Temp (n2w 03);
                   Temp (n2w 04);
                 Temp (n2w 05); Temp (n2w 06); Temp (n2w 07); Temp (n2w 08);
                   Temp (n2w 09);
                 Temp (n2w 10); Temp (n2w 11); Temp (n2w 12); Temp (n2w 13);
                   Temp (n2w 14);
                 Temp (n2w 15); Temp (n2w 16); Temp (n2w 17); Temp (n2w 18);
                   Temp (n2w 19);
                 Temp (n2w 20); Temp (n2w 21); Temp (n2w 22); Temp (n2w 23);
                   Temp (n2w 24);
                 Temp (n2w 25); Temp (n2w 26); Temp (n2w 27); Temp (n2w 28);
                   Temp (n2w 29);
                 Temp (n2w 30); Temp (n2w 31)]`;;

let store_pos_def = new_definition
  `store_pos name =
     match INDEX_FIND 0 (\n. n = name) stack_remove_store_list with NONE ->
       0
     | SOME (i,_) -> i + 1`;;

let store_length_def = new_definition
  `store_length =
     if EVEN (LENGTH stack_remove_store_list) then LENGTH
       stack_remove_store_list
     else LENGTH stack_remove_store_list + 1`;;

let store_offset_def = new_definition
  `store_offset name = (n2w 0) - word_offset (store_pos name)`;;

let stack_err_lab_def = new_definition
  `stack_err_lab = 2`;;

let halt_inst_def = new_definition
  `halt_inst w = stack_Seq ((\r w. stack_Inst (asm_Const r w)) 1 w)
  (stack_Halt 1)`;;

(*
    k is stack pointer register
    k+1 is base of store array (and last stack address)
    k+2 is CurrHeap (which is kept in a register for improved speed)
*)

let single_stack_alloc_def = new_definition
  `single_stack_alloc jump k n =
     if jump then
       stack_Seq (stack_Inst (asm_Arith (asm_Binop asm_Sub k k (Imm
         (word_offset n)))))
           (stack_JumpLower k (k + 1) stack_err_lab)
     else stack_Seq (stack_Inst (asm_Arith (asm_Binop asm_Sub k k (Imm
       (word_offset n)))))
           (stack_If asm_Lower k (Reg (k + 1)) (halt_inst (n2w 2))
             stack_Skip)`;;

(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 stack_removeScript.sml:85-87: the tactic that proves the termination *)
let stack_alloc_def,stack_alloc_ind = define_wf
  `MEASURE (SND o SND)`
  `stack_alloc jump k n =
     if n = 0 then stack_Skip else if n <= max_stack_alloc then
       single_stack_alloc jump k n else stack_Seq (single_stack_alloc jump k
       max_stack_alloc)
           (stack_alloc jump k (n - max_stack_alloc))`;;

let single_stack_free_def = new_definition
  `single_stack_free k n =
     stack_Inst (asm_Arith (asm_Binop asm_Add k k (Imm (word_offset n))))`;;

(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 stack_removeScript.sml:100-102: the tactic that proves the
   termination *)
let stack_free_def,stack_free_ind = define_wf
  `MEASURE SND`
  `stack_remove_stack_free k n =
     if n = 0 then stack_Skip else if n <= max_stack_alloc then
       single_stack_free k n else stack_Seq (single_stack_free k
       max_stack_alloc)
           (stack_remove_stack_free k (n - max_stack_alloc))`;;

(* upshift the stack pointer *)
(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 stack_removeScript.sml:112-114: the tactic that proves the
   termination *)
let upshift_def,upshift_ind = define_wf
  `MEASURE SND`
  `upshift r n =
     if n <= max_stack_alloc then
       (stack_Inst (asm_Arith (asm_Binop asm_Add r r (Imm (word_offset
         n))))):'a stack_prog
     else stack_Seq (stack_Inst (asm_Arith (asm_Binop asm_Add r r (Imm
       (word_offset max_stack_alloc)))))
       (upshift r (n - max_stack_alloc))`;;

(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 stack_removeScript.sml:123-125: the tactic that proves the
   termination *)
let downshift_def,downshift_ind = define_wf
  `MEASURE SND`
  `downshift r n =
     if n <= max_stack_alloc then
       (stack_Inst (asm_Arith (asm_Binop asm_Sub r r (Imm (word_offset
         n))))):'a stack_prog
     else stack_Seq (stack_Inst (asm_Arith (asm_Binop asm_Sub r r (Imm
       (word_offset max_stack_alloc)))))
       (downshift r (n - max_stack_alloc))`;;

(* Shifts k up and down to store r into n*)
let stack_store_def = new_definition
  `stack_store k r n =
      stack_Seq (upshift k n)
     (stack_Seq (stack_Inst (asm_Mem asm_Store r (Addr k (n2w 0))))
       (downshift k n))`;;

let stack_load_def = new_definition
  `stack_load r n =
     (stack_Seq (upshift r n) (stack_Inst (asm_Mem asm_Load r (Addr r
       (n2w 0)))):'a stack_prog)`;;

let copy_each_def = new_definition
  `copy_each t1 t2 =
     (\cmp r ri c. stack_Loop (stack_If cmp r ri c (stack_Break 0)))
       asm_NotEqual 1 (Imm (n2w 1))
       (stack_list_Seq [(\r a. stack_Inst (asm_Mem asm_Load r (Addr a (n2w
         0)))) t1 t2;
                  (\r1. stack_Inst (asm_Arith (asm_Binop asm_Add r1 r1 (Imm
                    (bytes_in_word))))) t2;
                  stack_If asm_Test 1 (Imm (n2w 1)) stack_Skip ((\r1 r2.
                    stack_Inst (asm_Arith (asm_Binop asm_Add r1 r1 (Reg r2))))
                    t1 3);
                  (\r v. stack_Inst (asm_Arith (asm_Shift Lsr r r (Imm (n2w
                    v))))) 1 1;
                  (\r a. stack_Inst (asm_Mem asm_Store r (Addr a (n2w 0))))
                    t1 2;
                  (\r1. stack_Inst (asm_Arith (asm_Binop asm_Add r1 r1
                    (Imm (bytes_in_word))))) 2])`;;

let copy_loop_def = new_definition
  `copy_loop t1 t2 =
     stack_list_Seq [(\r a. stack_Inst (asm_Mem asm_Load r (Addr a (n2w
       0)))) 1 t2;
               (\r1. stack_Inst (asm_Arith (asm_Binop asm_Add r1 r1 (Imm
                 (bytes_in_word))))) t2;
               (\cmp r ri c. stack_Loop (stack_If cmp r ri c (stack_Break
                 0))) asm_Less 1 (Imm (n2w 0))
                 (stack_list_Seq [copy_each t1 t2;
                            (\r a. stack_Inst (asm_Mem asm_Load r (Addr a
                              (n2w 0)))) 1 t2;
                            (\r1. stack_Inst (asm_Arith (asm_Binop asm_Add
                              r1 r1 (Imm (bytes_in_word))))) t2]);
               copy_each t1 t2]`;;

make_size "stack_prog";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let stack_remove_comp_def,stack_remove_comp_ind = define_wf
  `MEASURE (\(x0,x1,x2,x3). stack_prog_size (\x. 0) x3)`
  `stack_remove_comp jump off k (p:'a stack_prog) =
     match p with
       // remove store accesses
       stack_Get r name ->
         if name = CurrHeap then (\dest src. stack_Inst (asm_Arith
           (asm_Binop asm_Or dest src (Reg src)))) r (k + 2)
         else stack_Inst (asm_Mem asm_Load r (Addr (k + 1) (store_offset
           name)))
     | stack_Set name r ->
         if name = CurrHeap then (\dest src. stack_Inst (asm_Arith
           (asm_Binop asm_Or dest src (Reg src)))) (k + 2) r
         else stack_Inst (asm_Mem asm_Store r (Addr (k + 1) (store_offset
           name)))
     | stack_OpCurrHeap op r n ->
         stack_Inst (asm_Arith (asm_Binop op r n (Reg (k + 2))))
     |
       // remove stack operations
       stack_StackFree n -> stack_remove_stack_free k n
     | stack_StackAlloc n -> stack_alloc jump k n
     | stack_StackStore r n ->
       let w = word_offset n in
       if asm_offset_ok 0 off w then
         stack_Inst (asm_Mem asm_Store r (Addr k w))
       else stack_store k r n
     | stack_StackLoad r n ->
       let w = word_offset n in
       if asm_offset_ok 0 off w then
         stack_Inst (asm_Mem asm_Load r (Addr k w))
       else stack_Seq ((\dest src. stack_Inst (asm_Arith (asm_Binop asm_Or
         dest src (Reg src)))) r k) (stack_load r n)
     | stack_DataBufferWrite r1 r2 -> stack_Inst (asm_Mem asm_Store r2 (Addr
       r1 (n2w 0)))
     |
       // remove data buffer
       stack_StackLoadAny r i -> stack_Seq (stack_Seq ((\dest src.
         stack_Inst (asm_Arith (asm_Binop asm_Or dest src (Reg src)))) r i)
         ((\r1 r2. stack_Inst (asm_Arith (asm_Binop asm_Add r1 r1 (Reg r2)))) r
         k))
                              (stack_Inst (asm_Mem asm_Load r (Addr r (n2w
                                0))))
     | stack_StackStoreAny r i -> stack_Seq (stack_Inst (asm_Arith
       (asm_Binop asm_Add k k (Reg i))))
                           (stack_Seq (stack_Inst (asm_Mem asm_Store r (Addr
                             k (n2w 0))))
                              (stack_Inst (asm_Arith (asm_Binop asm_Sub k k
                                (Reg i)))))
     | stack_StackGetSize r -> stack_Seq (stack_Seq ((\dest src. stack_Inst
       (asm_Arith (asm_Binop asm_Or dest src (Reg src)))) r k) ((\r1 r2.
       stack_Inst (asm_Arith (asm_Binop asm_Sub r1 r1 (Reg r2)))) r (k + 1)))
                             ((\r v. stack_Inst (asm_Arith (asm_Shift Lsr r
                               r (Imm (n2w v))))) r (backend_common_word_shift
                               (:'a)))
     | stack_StackSetSize r -> stack_Seq ((\r v. stack_Inst (asm_Arith
       (asm_Shift Lsl r r (Imm (n2w v))))) r (backend_common_word_shift (:'a)))
                             (stack_Seq ((\dest src. stack_Inst (asm_Arith
                               (asm_Binop asm_Or dest src (Reg src)))) k (k +
                               1)) ((\r1 r2. stack_Inst (asm_Arith (asm_Binop
                               asm_Add r1 r1 (Reg r2)))) k r))
     | stack_BitmapLoad r v ->
         stack_list_Seq [stack_Inst (asm_Mem asm_Load r (Addr (k + 1)
           (store_offset BitmapBase)));
                   (\r1 r2. stack_Inst (asm_Arith (asm_Binop asm_Add r1 r1
                     (Reg r2)))) r v;
                   (\r v. stack_Inst (asm_Arith (asm_Shift Lsl r r (Imm (n2w
                     v))))) r (backend_common_word_shift (:'a));
                   stack_Inst (asm_Mem asm_Load r (Addr r (n2w 0)))]
     | stack_StoreConsts t1 t2 _ ->
         stack_list_Seq [stack_Inst (asm_Mem asm_Load t2 (Addr (k + 1)
           (store_offset BitmapBase)));
                   (\r1 r2. stack_Inst (asm_Arith (asm_Binop asm_Add r1 r1
                     (Reg r2)))) t2 1;
                   (\r v. stack_Inst (asm_Arith (asm_Shift Lsl r r (Imm (n2w
                     v))))) t2 (backend_common_word_shift (:'a));
                   copy_loop t1 t2;
                   (\dest src. stack_Inst (asm_Arith (asm_Binop asm_Or dest
                     src (Reg src)))) t1 1;
                   (\dest src. stack_Inst (asm_Arith (asm_Binop asm_Or dest
                     src (Reg src)))) t2 1]
     |
       // for the rest, just leave it unchanged
       stack_Seq p1 p2 -> stack_Seq (stack_remove_comp jump off k p1)
         (stack_remove_comp jump off k p2)
     | stack_If c r ri p1 p2 -> stack_If c r ri (stack_remove_comp jump off
       k p1) (stack_remove_comp jump off k p2)
     | stack_Loop p1 -> stack_Loop (stack_remove_comp jump off k p1)
     | stack_Call ret dest exc ->
         stack_Call (match ret with NONE -> NONE
               | SOME (p1,lr,l1,l2) -> SOME (stack_remove_comp jump off k
                 p1,lr,l1,l2))
           dest (match exc with NONE -> NONE
                 | SOME (p2,l1,l2) -> SOME (stack_remove_comp jump off k
                   p2,l1,l2))
     | p -> p`;;

let stack_remove_prog_comp_def = new_definition
  `stack_remove_prog_comp jump off k (n,p) = (n,stack_remove_comp jump off k
  p)`;;

(* -- init code -- *)

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let store_list_code_def,store_list_code_ind = define_wf
  `MEASURE (\(x0,x1,x2). list_size (sum_size (\n. n) (\x. 0)) x2)`
  `(store_list_code a t [] = stack_Skip) /\
   (store_list_code a t (CONS (INL w) xs) =
     stack_Seq (stack_list_Seq [(\r w. stack_Inst (asm_Const r w)) t w; (\r
       a. stack_Inst (asm_Mem asm_Store r (Addr a (n2w 0)))) t a; (\r1.
       stack_Inst (asm_Arith (asm_Binop asm_Add r1 r1 (Imm (bytes_in_word)))))
       a])
         (store_list_code a t xs)) /\
   (store_list_code a t (CONS (INR i) xs) =
     stack_Seq (stack_list_Seq [(\r a. stack_Inst (asm_Mem asm_Store r (Addr
       a (n2w 0)))) i a; (\r1. stack_Inst (asm_Arith (asm_Binop asm_Add r1 r1
       (Imm (bytes_in_word))))) a])
         (store_list_code a t xs))`;;

(* k+1 is base, k is stack pointer, discards 0 *)
let init_memory_def = new_definition
  `init_memory k xs =
     stack_list_Seq [(\r w. stack_Inst (asm_Const r w)) 0 bytes_in_word;
               (\r1 r2. stack_Inst (asm_Arith (asm_Binop asm_Sub r1 r1 (Reg
                 r2)))) k 0;
               (\r w. stack_Inst (asm_Const r w)) 0 (n2w 0);
               (\r a. stack_Inst (asm_Mem asm_Store r (Addr a (n2w 0)))) 0
                 k;
               store_list_code (k + 1) 0 xs]`;;

let store_init_def = new_definition
  `store_init gen_gc' (k:num) = UPDATE_LIST (K (INL (n2w 0)))
       [(CurrHeap,INR (k + 2));
        (GlobReal,INR (k + 2));
        (NextFree,INR (k + 2));
        (TriggerGC,INR (if gen_gc' then k + 2 else 2));
        (EndOfHeap,INR 2);
        (HeapLength,INR 5);
        (OtherHeap,INR 2);
        (BitmapBase,INR 3);
        (BitmapBuffer,INR 4);
        (BitmapBufferEnd,INR 6);
        (CodeBuffer,INR 7);
        (CodeBufferEnd,INR 1)]`;;

(* init code assumes:
    reg 1: start of program
    reg 2: first address in heap
    reg 3: first address in stack (and one past last address of heap)
    reg 4: one past last address of stack *)

let stack_remove_init_code_def = new_definition
  `stack_remove_init_code gen_gc' max_heap k =
     let max_heap = (if max_heap * w2n (bytes_in_word:'a word) < dimword
       (:'a) then n2w max_heap * bytes_in_word
                     else (n2w 0) - (n2w 1)) in
       stack_list_Seq [
                 // compute the middle address, store in reg0
                 (\dest src. stack_Inst (asm_Arith (asm_Binop asm_Or dest
                   src (Reg src)))) 0 4;
                 (\r1 r2. stack_Inst (asm_Arith (asm_Binop asm_Sub r1 r1
                   (Reg r2)))) 0 2;
                 (\r v. stack_Inst (asm_Arith (asm_Shift Lsr r r (Imm (n2w
                   v))))) 0 (1 + backend_common_word_shift (:'a));
                 (\r v. stack_Inst (asm_Arith (asm_Shift Lsl r r (Imm (n2w
                   v))))) 0 (backend_common_word_shift (:'a));
                 (\r1 r2. stack_Inst (asm_Arith (asm_Binop asm_Add r1 r1
                   (Reg r2)))) 0 2;
                 // if reg3 is not between start and end of memory, then put
                 // it in the middle (i.e. split heap and stack evenly)
                 (\r w. stack_Inst (asm_Const r w)) 5 (n2w max_stack_alloc *
                   (bytes_in_word:'a word));
                 (\r1 r2. stack_Inst (asm_Arith (asm_Binop asm_Add r1 r1
                   (Reg r2)))) 2 5;
                 (\r1 r2. stack_Inst (asm_Arith (asm_Binop asm_Sub r1 r1
                   (Reg r2)))) 4 5;
                 stack_If asm_Lower 3 (Reg 2) ((\dest src. stack_Inst
                   (asm_Arith (asm_Binop asm_Or dest src (Reg src)))) 3 0)
                   (stack_If asm_Lower 4 (Reg 3) ((\dest src. stack_Inst
                     (asm_Arith (asm_Binop asm_Or dest src (Reg src)))) 3 0)
                     stack_Skip);
                 (\r w. stack_Inst (asm_Const r w)) 0 (n2w max_stack_alloc *
                   (bytes_in_word:'a word));
                 (\r1 r2. stack_Inst (asm_Arith (asm_Binop asm_Sub r1 r1
                   (Reg r2)))) 2 0;
                 (\r1 r2. stack_Inst (asm_Arith (asm_Binop asm_Add r1 r1
                   (Reg r2)))) 4 0;
                 // shrink the heap if it is too big
                 (\dest src. stack_Inst (asm_Arith (asm_Binop asm_Or dest
                   src (Reg src)))) 0 3;
                 (\r1 r2. stack_Inst (asm_Arith (asm_Binop asm_Sub r1 r1
                   (Reg r2)))) 0 2;
                 (\r w. stack_Inst (asm_Const r w)) 5 max_heap;
                 stack_If asm_Lower 5 (Reg 0) (stack_Seq ((\dest src.
                   stack_Inst (asm_Arith (asm_Binop asm_Or dest src (Reg
                   src)))) 3 2) ((\r1 r2. stack_Inst (asm_Arith (asm_Binop
                   asm_Add r1 r1 (Reg r2)))) 3 5)) stack_Skip;
                 // ensure heap is even number of words
                 (\r1 r2. stack_Inst (asm_Arith (asm_Binop asm_Sub r1 r1
                   (Reg r2)))) 3 2;
                 (\r v. stack_Inst (asm_Arith (asm_Shift Lsr r r (Imm (n2w
                   v))))) 3 (backend_common_word_shift (:'a) + 1);
                 (\r v. stack_Inst (asm_Arith (asm_Shift Lsl r r (Imm (n2w
                   v))))) 3 (backend_common_word_shift (:'a) + 1);
                 (\r1 r2. stack_Inst (asm_Arith (asm_Binop asm_Add r1 r1
                   (Reg r2)))) 3 2;
                 // split heap into two, store heap length in 5
                 (\dest src. stack_Inst (asm_Arith (asm_Binop asm_Or dest
                   src (Reg src)))) 5 3;
                 (\r1 r2. stack_Inst (asm_Arith (asm_Binop asm_Sub r1 r1
                   (Reg r2)))) 5 2;
                 (\r v. stack_Inst (asm_Arith (asm_Shift Lsr r r (Imm (n2w
                   v))))) 5 1;
                 // setup store, stack
                 (\dest src. stack_Inst (asm_Arith (asm_Binop asm_Or dest
                   src (Reg src)))) (k + 2) 2;
                 (\r1 r2. stack_Inst (asm_Arith (asm_Binop asm_Add r1 r1
                   (Reg r2)))) 2 5;
                 (\dest src. stack_Inst (asm_Arith (asm_Binop asm_Or dest
                   src (Reg src)))) k 4;
                 (\dest src. stack_Inst (asm_Arith (asm_Binop asm_Or dest
                   src (Reg src)))) (k + 1) 3;
                 (\r a. stack_Inst (asm_Mem asm_Load r (Addr a (n2w 0)))) 3
                   (k + 2);
                 (\r v. stack_Inst (asm_Arith (asm_Shift Lsr r r (Imm (n2w
                   v))))) 3 (backend_common_word_shift (:'a));
                 (\dest src. stack_Inst (asm_Arith (asm_Binop asm_Or dest
                   src (Reg src)))) 0 (k + 2);
                 (\r1. stack_Inst (asm_Arith (asm_Binop asm_Add r1 r1 (Imm
                   (bytes_in_word))))) 0;
                 (\r a. stack_Inst (asm_Mem asm_Load r (Addr a (n2w 0)))) 4
                   0;
                 (\r1. stack_Inst (asm_Arith (asm_Binop asm_Add r1 r1 (Imm
                   (bytes_in_word))))) 0;
                 (\r a. stack_Inst (asm_Mem asm_Load r (Addr a (n2w 0)))) 6
                   0;
                 (\r1. stack_Inst (asm_Arith (asm_Binop asm_Add r1 r1 (Imm
                   (bytes_in_word))))) 0;
                 (\r a. stack_Inst (asm_Mem asm_Load r (Addr a (n2w 0)))) 7
                   0;
                 (\r1. stack_Inst (asm_Arith (asm_Binop asm_Add r1 r1 (Imm
                   (bytes_in_word))))) 0;
                 (\r a. stack_Inst (asm_Mem asm_Load r (Addr a (n2w 0)))) 1
                   0;
                 init_memory k (MAP (store_init gen_gc' k) (REVERSE
                   stack_remove_store_list));
                 stack_LocValue 0 1 0]`;;

let init_stubs_def = new_definition
  `init_stubs gen_gc' max_heap k start' =
     [(0,stack_Seq (stack_remove_init_code gen_gc' max_heap k) (stack_Call
       NONE (INL start') NONE));
      (1,halt_inst (n2w 0));
      (2,halt_inst (n2w 2))]`;;

let stack_remove_stub_names_def = new_definition
  `stack_remove_stub_names one = [
     (0,implode "_Init");
     (1,implode "_Halt0");
     (2,implode "_Halt2")]`;;

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let check_init_stubs_length = prove
 (cake_as_vars (fun () ->
    `LENGTH (init_stubs gen_gc max_heap k start) + 2 =
     // gc + dummy
     stack_num_stubs`),
  (REWRITE_TAC[init_stubs_def; LENGTH; stack_num_stubs_def] THEN
    ARITH_TAC));;

(* -- full compiler -- *)

let stack_remove_compile_def = new_definition
  `stack_remove_compile jump off gen_gc' max_heap k start' prog = APPEND
  (init_stubs gen_gc' max_heap k start')
     (MAP (stack_remove_prog_comp jump off k) prog)`;;

(* and the names it reads as variables are constants again *)
let _ = do_list unhide_constant
  ["dummy";
   "gc";
   "gen_gc"];;

(* and the interface *)
let _ = unhide_overloads ();;
