(* ======================================================== *)
(*  stack_remove: ported from HOL4's
    compiler/backend/stack_removeScript.sml  *)
(* ======================================================== *)

(*
  This compiler phase implements all stack operations as normal memory
  load/store operations.
*)

needs "basis/pure/mlstring.ml";;
needs "compiler/backend/stackLang.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "lib/byte.ml";;
needs "lib/comparison.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;
(* HOL4 ancestors outside the port: (* for bytes_in_word *) *)


(* -- compiler -- *)

let max_stack_alloc_def = cake_define
  `max_stack_alloc = 255`;;

let word_offset_def = cake_define
  `word_offset n = (n2w (dimindex (:'a) DIV 8 * n):'a word)`;;

let store_list_def = cake_define
  `stack_remove_store_list = [NextFree; EndOfHeap; HeapLength;
  OtherHeap; TriggerGC;
                 AllocSize; Handler; Globals; GlobReal; ProgStart;
                   BitmapBase;
                 GenStart; CodeBuffer; CodeBufferEnd; BitmapBuffer;
                   BitmapBufferEnd;
                 Temp (n2w 00); Temp (n2w 01); Temp (n2w 02); Temp
                   (n2w 03); Temp (n2w 04);
                 Temp (n2w 05); Temp (n2w 06); Temp (n2w 07); Temp
                   (n2w 08); Temp (n2w 09);
                 Temp (n2w 10); Temp (n2w 11); Temp (n2w 12); Temp
                   (n2w 13); Temp (n2w 14);
                 Temp (n2w 15); Temp (n2w 16); Temp (n2w 17); Temp
                   (n2w 18); Temp (n2w 19);
                 Temp (n2w 20); Temp (n2w 21); Temp (n2w 22); Temp
                   (n2w 23); Temp (n2w 24);
                 Temp (n2w 25); Temp (n2w 26); Temp (n2w 27); Temp
                   (n2w 28); Temp (n2w 29);
                 Temp (n2w 30); Temp (n2w 31)]`;;
hol4_overload "store_list" "stack_remove_store_list";;

let store_pos_def = cake_define
  `store_pos name =
     (match INDEX_FIND 0 (\n. n = name) stack_remove_store_list
       with NONE -> 0 | SOME (i,_1) -> i + 1)`;;

let store_length_def = cake_define
  `store_length =
     (if EVEN (LENGTH stack_remove_store_list) then LENGTH
       stack_remove_store_list else LENGTH stack_remove_store_list +
       1)`;;

let store_offset_def = cake_define
  `store_offset name = (n2w 0) - word_offset (store_pos name)`;;

let stack_err_lab_def = cake_define
  `stack_err_lab = 2`;;

let halt_inst_def = cake_define
  `halt_inst w = stackLang_Seq ((\r w. Inst (asm_Const r w)) 1 w)
  (stackLang_Halt 1)`;;

(*
    k is stack pointer register
    k+1 is base of store array (and last stack address)
    k+2 is CurrHeap (which is kept in a register for improved speed)
*)

let single_stack_alloc_def = cake_define
  `single_stack_alloc jump k n =
     (if jump then
       stackLang_Seq (stackLang_Inst (Arith (asm_Binop asm_Sub k k
         (Imm (word_offset n)))))
           (stackLang_JumpLower k (k + 1) stack_err_lab) else
        stackLang_Seq (stackLang_Inst (Arith (asm_Binop asm_Sub k k
          (Imm (word_offset n)))))
           (stackLang_If asm_Lower k (Reg (k + 1)) (halt_inst (n2w
             2)) stackLang_Skip))`;;

(* HOL4 stack_removeScript.sml:85-87: the tactic that proves the
   termination *)
let stack_alloc_def = cake_define_wf
  `MEASURE (SND o SND)`
  `stack_alloc jump k n =
     (if n = 0 then Skip else
     if n <= max_stack_alloc then single_stack_alloc jump k n else
       stackLang_Seq (single_stack_alloc jump k max_stack_alloc)
           (stack_alloc jump k (n - max_stack_alloc)))`;;

let single_stack_free_def = cake_define
  `single_stack_free k n =
     stackLang_Inst (Arith (asm_Binop asm_Add k k (Imm
       (word_offset n))))`;;

(* HOL4 stack_removeScript.sml:100-102: the tactic that proves the
   termination *)
let stack_free_def = cake_define_wf
  `MEASURE SND`
  `stack_remove_stack_free k n =
     (if n = 0 then Skip else
     if n <= max_stack_alloc then single_stack_free k n else
       stackLang_Seq (single_stack_free k max_stack_alloc)
           (stack_remove_stack_free k (n - max_stack_alloc)))`;;
hol4_overload "stack_free" "stack_remove_stack_free";;

(* upshift the stack pointer *)
(* HOL4 stack_removeScript.sml:112-114: the tactic that proves the
   termination *)
let upshift_def = cake_define_wf
  `MEASURE SND`
  `upshift r n =
     (if n <= max_stack_alloc then
       (Inst (Arith (asm_Binop asm_Add r r (Imm (word_offset
         n))))):'a stackLang_prog else
       stackLang_Seq (stackLang_Inst (Arith (asm_Binop asm_Add r r
         (Imm (word_offset max_stack_alloc)))))
       (upshift r (n - max_stack_alloc)))`;;

(* HOL4 stack_removeScript.sml:123-125: the tactic that proves the
   termination *)
let downshift_def = cake_define_wf
  `MEASURE SND`
  `downshift r n =
     (if n <= max_stack_alloc then
       (Inst (Arith (asm_Binop asm_Sub r r (Imm (word_offset
         n))))):'a stackLang_prog else
       stackLang_Seq (stackLang_Inst (Arith (asm_Binop asm_Sub r r
         (Imm (word_offset max_stack_alloc)))))
       (downshift r (n - max_stack_alloc)))`;;

(* Shifts k up and down to store r into n*)
let stack_store_def = cake_define
  `stack_store k r n =
      stackLang_Seq (upshift k n)
     (stackLang_Seq (stackLang_Inst (asm_Mem asm_Store r (Addr k
       (n2w 0)))) (downshift k n))`;;

let stack_load_def = cake_define
  `stack_load r n =
     (stackLang_Seq (upshift r n) (stackLang_Inst (asm_Mem
       asm_Load r (Addr r (n2w 0)))):'a stackLang_prog)`;;

let copy_each_def = cake_define
  `copy_each t1 t2 =
     (\cmp r ri c. stackLang_Loop (stackLang_If cmp r ri c
       (stackLang_Break 0))) asm_NotEqual 1 (Imm (n2w 1))
       (stackLang_list_Seq [(\r a. Inst (asm_Mem asm_Load r (Addr a
         (n2w 0)))) t1 t2;
                  (\r1. Inst (Arith (asm_Binop asm_Add r1 r1 (Imm
                    (bytes_in_word))))) t2;
                  If Test 1 (Imm (n2w 1)) stackLang_Skip ((\r1 r2.
                    Inst (Arith (asm_Binop asm_Add r1 r1 (Reg r2)))) t1
                    3);
                  (\r v. Inst (Arith (asm_Shift Lsr r r (Imm (n2w
                    v))))) 1 1;
                  (\r a. Inst (asm_Mem asm_Store r (Addr a (n2w 0))))
                    t1 2;
                  (\r1. Inst (Arith (asm_Binop asm_Add r1 r1 (Imm
                    (bytes_in_word))))) 2])`;;

let copy_loop_def = cake_define
  `copy_loop t1 t2 =
     stackLang_list_Seq [(\r a. Inst (asm_Mem asm_Load r (Addr a (n2w
       0)))) 1 t2;
               (\r1. Inst (Arith (asm_Binop asm_Add r1 r1 (Imm
                 (bytes_in_word))))) t2;
               (\cmp r ri c. stackLang_Loop (stackLang_If cmp r ri c
                 (stackLang_Break 0))) Less 1 (Imm (n2w 0))
                 (stackLang_list_Seq [copy_each t1 t2;
                            (\r a. Inst (asm_Mem asm_Load r (Addr a
                              (n2w 0)))) 1 t2;
                            (\r1. Inst (Arith (asm_Binop asm_Add r1
                              r1 (Imm (bytes_in_word))))) t2]);
               copy_each t1 t2]`;;

let comp_def = cake_define
  `stack_remove_comp jump off k (p:'a stackLang_prog) =
     (match p with stackLang_Get r name ->
         (if name = CurrHeap then (\dest src. Inst (Arith (asm_Binop
           asm_Or dest src (Reg src)))) r (k + 2) else Inst (asm_Mem
           asm_Load r (Addr (k + 1) (store_offset name)))) |
           stackLang_Set name r ->
         (if name = CurrHeap then (\dest src. Inst (Arith (asm_Binop
           asm_Or dest src (Reg src)))) (k + 2) r else Inst (asm_Mem
           asm_Store r (Addr (k + 1) (store_offset name)))) |
           stackLang_OpCurrHeap op r n ->
         Inst (Arith (asm_Binop op r n (Reg (k + 2)))) |
           stackLang_StackFree n -> stack_remove_stack_free k n |
           stackLang_StackAlloc n -> stack_alloc jump k n |
           stackLang_StackStore r n ->
       (let w = word_offset n in
       if asm_offset_ok 0 off w then
         Inst (asm_Mem asm_Store r (Addr k w)) else
         stack_store k r n) | stackLang_StackLoad r n ->
       (let w = word_offset n in
       if asm_offset_ok 0 off w then
         Inst (asm_Mem asm_Load r (Addr k w)) else
         stackLang_Seq ((\dest src. Inst (Arith (asm_Binop asm_Or
           dest src (Reg src)))) r k) (stack_load r n)) |
           stackLang_DataBufferWrite r1 r2 -> Inst (asm_Mem asm_Store r2
           (Addr r1 (n2w 0))) | stackLang_StackLoadAny r i ->
           stackLang_Seq (stackLang_Seq ((\dest src. Inst (Arith
           (asm_Binop asm_Or dest src (Reg src)))) r i) ((\r1 r2. Inst
           (Arith (asm_Binop asm_Add r1 r1 (Reg r2)))) r k))
                              (stackLang_Inst (asm_Mem asm_Load r
                                (Addr r (n2w 0)))) |
                                stackLang_StackStoreAny r i ->
                                stackLang_Seq (stackLang_Inst (Arith
                                (asm_Binop asm_Add k k (Reg i))))
                           (stackLang_Seq (stackLang_Inst (asm_Mem
                             asm_Store r (Addr k (n2w 0))))
                              (stackLang_Inst (Arith (asm_Binop
                                asm_Sub k k (Reg i))))) |
                                stackLang_StackGetSize r ->
                                stackLang_Seq (stackLang_Seq ((\dest
                                src. Inst (Arith (asm_Binop asm_Or dest
                                src (Reg src)))) r k) ((\r1 r2. Inst
                                (Arith (asm_Binop asm_Sub r1 r1 (Reg
                                r2)))) r (k + 1)))
                             ((\r v. Inst (Arith (asm_Shift Lsr r r
                               (Imm (n2w v))))) r
                               (backend_common_word_shift (:'a))) |
                               stackLang_StackSetSize r -> stackLang_Seq
                               ((\r v. Inst (Arith (asm_Shift Lsl r r
                               (Imm (n2w v))))) r
                               (backend_common_word_shift (:'a)))
                             (stackLang_Seq ((\dest src. Inst (Arith
                               (asm_Binop asm_Or dest src (Reg src)))) k
                               (k + 1)) ((\r1 r2. Inst (Arith (asm_Binop
                               asm_Add r1 r1 (Reg r2)))) k r)) |
                               stackLang_BitmapLoad r v ->
         stackLang_list_Seq [Inst (asm_Mem asm_Load r (Addr (k + 1)
           (store_offset BitmapBase)));
                   (\r1 r2. Inst (Arith (asm_Binop asm_Add r1 r1 (Reg
                     r2)))) r v;
                   (\r v. Inst (Arith (asm_Shift Lsl r r (Imm (n2w
                     v))))) r (backend_common_word_shift (:'a));
                   Inst (asm_Mem asm_Load r (Addr r (n2w 0)))] |
                     stackLang_StoreConsts t1 t2 _2 ->
         stackLang_list_Seq [Inst (asm_Mem asm_Load t2 (Addr (k + 1)
           (store_offset BitmapBase)));
                   (\r1 r2. Inst (Arith (asm_Binop asm_Add r1 r1 (Reg
                     r2)))) t2 1;
                   (\r v. Inst (Arith (asm_Shift Lsl r r (Imm (n2w
                     v))))) t2 (backend_common_word_shift (:'a));
                   copy_loop t1 t2;
                   (\dest src. Inst (Arith (asm_Binop asm_Or dest src
                     (Reg src)))) t1 1;
                   (\dest src. Inst (Arith (asm_Binop asm_Or dest src
                     (Reg src)))) t2 1] | stackLang_Seq p1 p2 ->
                     stackLang_Seq (stack_remove_comp jump off k p1)
                     (stack_remove_comp jump off k p2) | If c r ri p1 p2
                     -> If c r ri (stack_remove_comp jump off k p1)
                     (stack_remove_comp jump off k p2) | stackLang_Loop
                     p1 -> stackLang_Loop (stack_remove_comp jump off k
                     p1) | Call ret dest exc ->
         Call (match ret with NONE -> NONE | SOME (p1,lr,l1,l2) ->
           SOME (stack_remove_comp jump off k p1,lr,l1,l2))
           dest (match exc with NONE -> NONE | SOME (p2,l1,l2) ->
             SOME (stack_remove_comp jump off k p2,l1,l2)) | p -> p)`;;
hol4_overload "comp" "stack_remove_comp";;

let prog_comp_def = cake_define
  `stack_remove_prog_comp jump off k (n,p) = (n,stack_remove_comp
  jump off k p)`;;
hol4_overload "prog_comp" "stack_remove_prog_comp";;

(* -- init code -- *)

let store_list_code_def = cake_define
  `(store_list_code a t [] = Skip) /\
   (store_list_code a t (INL w :: xs) =
     stackLang_Seq (stackLang_list_Seq [(\r w. Inst (asm_Const r w))
       t w; (\r a. Inst (asm_Mem asm_Store r (Addr a (n2w 0)))) t a;
       (\r1. Inst (Arith (asm_Binop asm_Add r1 r1 (Imm
       (bytes_in_word))))) a])
         (store_list_code a t xs)) /\
   (store_list_code a t (INR i :: xs) =
     stackLang_Seq (stackLang_list_Seq [(\r a. Inst (asm_Mem
       asm_Store r (Addr a (n2w 0)))) i a; (\r1. Inst (Arith (asm_Binop
       asm_Add r1 r1 (Imm (bytes_in_word))))) a])
         (store_list_code a t xs))`;;

(* k+1 is base, k is stack pointer, discards 0 *)
let init_memory_def = cake_define
  `init_memory k xs =
     stackLang_list_Seq [(\r w. Inst (asm_Const r w)) 0
       bytes_in_word;
               (\r1 r2. Inst (Arith (asm_Binop asm_Sub r1 r1 (Reg
                 r2)))) k 0;
               (\r w. Inst (asm_Const r w)) 0 (n2w 0);
               (\r a. Inst (asm_Mem asm_Store r (Addr a (n2w 0)))) 0
                 k;
               store_list_code (k + 1) 0 xs]`;;

let store_init_def = cake_define
  `store_init gen_gc' (k:num) = UPDATE_LIST
     (K (INL (n2w 0)))
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

let init_code_def = cake_define
  `stack_remove_init_code gen_gc' max_heap k =
     (let max_heap = (if max_heap * w2n (bytes_in_word:'a word) <
       dimword (:'a) then n2w max_heap * bytes_in_word else (n2w 0) -
       (n2w 1)) in
       stackLang_list_Seq [
                 (\dest src. Inst (Arith (asm_Binop asm_Or dest src
                   (Reg src)))) 0 4;
                 (\r1 r2. Inst (Arith (asm_Binop asm_Sub r1 r1 (Reg
                   r2)))) 0 2;
                 (\r v. Inst (Arith (asm_Shift Lsr r r (Imm (n2w
                   v))))) 0 (1 + backend_common_word_shift (:'a));
                 (\r v. Inst (Arith (asm_Shift Lsl r r (Imm (n2w
                   v))))) 0 (backend_common_word_shift (:'a));
                 (\r1 r2. Inst (Arith (asm_Binop asm_Add r1 r1 (Reg
                   r2)))) 0 2;
                 (\r w. Inst (asm_Const r w)) 5 (n2w max_stack_alloc
                   * (bytes_in_word:'a word));
                 (\r1 r2. Inst (Arith (asm_Binop asm_Add r1 r1 (Reg
                   r2)))) 2 5;
                 (\r1 r2. Inst (Arith (asm_Binop asm_Sub r1 r1 (Reg
                   r2)))) 4 5;
                 If asm_Lower 3 (Reg 2) ((\dest src. Inst (Arith
                   (asm_Binop asm_Or dest src (Reg src)))) 3 0)
                   (stackLang_If asm_Lower 4 (Reg 3) ((\dest src.
                     Inst (Arith (asm_Binop asm_Or dest src (Reg src))))
                     3 0) stackLang_Skip);
                 (\r w. Inst (asm_Const r w)) 0 (n2w max_stack_alloc
                   * (bytes_in_word:'a word));
                 (\r1 r2. Inst (Arith (asm_Binop asm_Sub r1 r1 (Reg
                   r2)))) 2 0;
                 (\r1 r2. Inst (Arith (asm_Binop asm_Add r1 r1 (Reg
                   r2)))) 4 0;
                 (\dest src. Inst (Arith (asm_Binop asm_Or dest src
                   (Reg src)))) 0 3;
                 (\r1 r2. Inst (Arith (asm_Binop asm_Sub r1 r1 (Reg
                   r2)))) 0 2;
                 (\r w. Inst (asm_Const r w)) 5 max_heap;
                 If asm_Lower 5 (Reg 0) (stackLang_Seq ((\dest src.
                   Inst (Arith (asm_Binop asm_Or dest src (Reg src)))) 3
                   2) ((\r1 r2. Inst (Arith (asm_Binop asm_Add r1 r1
                   (Reg r2)))) 3 5)) stackLang_Skip;
                 (\r1 r2. Inst (Arith (asm_Binop asm_Sub r1 r1 (Reg
                   r2)))) 3 2;
                 (\r v. Inst (Arith (asm_Shift Lsr r r (Imm (n2w
                   v))))) 3 (backend_common_word_shift (:'a) + 1);
                 (\r v. Inst (Arith (asm_Shift Lsl r r (Imm (n2w
                   v))))) 3 (backend_common_word_shift (:'a) + 1);
                 (\r1 r2. Inst (Arith (asm_Binop asm_Add r1 r1 (Reg
                   r2)))) 3 2;
                 (\dest src. Inst (Arith (asm_Binop asm_Or dest src
                   (Reg src)))) 5 3;
                 (\r1 r2. Inst (Arith (asm_Binop asm_Sub r1 r1 (Reg
                   r2)))) 5 2;
                 (\r v. Inst (Arith (asm_Shift Lsr r r (Imm (n2w
                   v))))) 5 1;
                 (\dest src. Inst (Arith (asm_Binop asm_Or dest src
                   (Reg src)))) (k + 2) 2;
                 (\r1 r2. Inst (Arith (asm_Binop asm_Add r1 r1 (Reg
                   r2)))) 2 5;
                 (\dest src. Inst (Arith (asm_Binop asm_Or dest src
                   (Reg src)))) k 4;
                 (\dest src. Inst (Arith (asm_Binop asm_Or dest src
                   (Reg src)))) (k + 1) 3;
                 (\r a. Inst (asm_Mem asm_Load r (Addr a (n2w 0)))) 3
                   (k + 2);
                 (\r v. Inst (Arith (asm_Shift Lsr r r (Imm (n2w
                   v))))) 3 (backend_common_word_shift (:'a));
                 (\dest src. Inst (Arith (asm_Binop asm_Or dest src
                   (Reg src)))) 0 (k + 2);
                 (\r1. Inst (Arith (asm_Binop asm_Add r1 r1 (Imm
                   (bytes_in_word))))) 0;
                 (\r a. Inst (asm_Mem asm_Load r (Addr a (n2w 0)))) 4
                   0;
                 (\r1. Inst (Arith (asm_Binop asm_Add r1 r1 (Imm
                   (bytes_in_word))))) 0;
                 (\r a. Inst (asm_Mem asm_Load r (Addr a (n2w 0)))) 6
                   0;
                 (\r1. Inst (Arith (asm_Binop asm_Add r1 r1 (Imm
                   (bytes_in_word))))) 0;
                 (\r a. Inst (asm_Mem asm_Load r (Addr a (n2w 0)))) 7
                   0;
                 (\r1. Inst (Arith (asm_Binop asm_Add r1 r1 (Imm
                   (bytes_in_word))))) 0;
                 (\r a. Inst (asm_Mem asm_Load r (Addr a (n2w 0)))) 1
                   0;
                 init_memory k (MAP (store_init gen_gc' k) (REVERSE
                   stack_remove_store_list));
                 stackLang_LocValue 0 1 0])`;;
hol4_overload "init_code" "stack_remove_init_code";;

let init_stubs_def = cake_define
  `init_stubs gen_gc' max_heap k start' =
     [(0,stackLang_Seq (stack_remove_init_code gen_gc' max_heap k)
       (stackLang_Call NONE (INL start') NONE));
      (1,halt_inst (n2w 0));
      (2,halt_inst (n2w 2))]`;;

let stub_names_def = cake_define
  `stack_remove_stub_names one = [
     (0,implode "_Init");
     (1,implode "_Halt0");
     (2,implode "_Halt2")]`;;
hol4_overload "stub_names" "stack_remove_stub_names";;

(* -- full compiler -- *)

let compile_def = cake_define
  `stack_remove_compile jump off gen_gc' max_heap k start' prog =
     init_stubs gen_gc' max_heap k start' ++
     MAP (stack_remove_prog_comp jump off k) prog`;;
hol4_overload "compile" "stack_remove_compile";;
