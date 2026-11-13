(* ======================================================== *)
(*  stack_alloc: ported from HOL4's
    compiler/backend/stack_allocScript.sml
    A definition theory, with 32 definitions and 2 theorems.  Needed
    by backendProof.ml, stack_allocProof.ml, stack_to_lab.ml and
    stack_to_labProof.ml.  *)
(* ======================================================== *)

(*
  This compiler phase introduces the implementation of the memory
  allocator and its garbage collector. It traverses the given code and
  replaces all calls to Alloc by calls to code that it inserts into
  the compiled program. the inserted code is a stackLang
  implementation of the garbage collector.
*)

needs "basis/pure/mlstring.ml";;
needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/dataLang.ml";;
needs "compiler/backend/data_to_word.ml";;
needs "compiler/backend/stackLang.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "lib/byte.ml";;
needs "lib/comparison.ml";;
needs "lib/multiword.ml";;
needs "semantics/ast.ml";;

(* the theories whose names the Ancestors blocks of the source
   bring, which are the ones that its statements read: the
   overloads of every other theory come out of the interface
   while this file loads *)
let _ = hol4_ancestors "stack_alloc"
  ["data_to_word"; "stackLang"];;

let memcpy_code_def = new_definition
  `memcpy_code =
     (\cmp r ri c. Loop (If cmp r ri c (Break 0))) asm_NotEqual 0
       (Imm (n2w 0))
       (list_Seq [(\r a. Inst (asm_Mem Load r (Addr a (n2w 0)))) 1 2;
                  (\r1. Inst (Arith (asm_Binop Add r1 r1 (Imm
                    (bytes_in_word))))) 2;
                  (\r1. Inst (Arith (asm_Binop Sub r1 r1 (Imm (n2w
                    1))))) 0;
                  (\r a. Inst (asm_Mem Store r (Addr a (n2w 0)))) 1
                    3;
                  (\r1. Inst (Arith (asm_Binop Add r1 r1 (Imm
                    (bytes_in_word))))) 3])`;;

let clear_top_inst_def = new_definition
  `clear_top_inst i n =
     (Seq ((\r v. Inst (Arith (asm_Shift Lsl r r (Imm (n2w v))))) i
       (dimindex (:'a) - n - 1))
         ((\r v. Inst (Arith (asm_Shift Lsr r r (Imm (n2w v))))) i
           (dimindex (:'a) - n - 1)):'a stackLang_prog)`;;

let word_gc_move_code_def = new_definition
  `word_gc_move_code conf =
     If Test 5 (Imm ((n2w 1):'a word)) Skip
       (list_Seq
         [(\dest src. Inst (Arith (asm_Binop Or dest src (Reg src))))
           0 5;
          Get 1 CurrHeap;
          (\r v. Inst (Arith (asm_Shift Lsr r r (Imm (n2w v))))) 0
            (shift_length conf);
          (\r v. Inst (Arith (asm_Shift Lsl r r (Imm (n2w v))))) 0
            (backend_common_word_shift (:'a));
          (\r1 r2. Inst (Arith (asm_Binop Add r1 r1 (Reg r2)))) 0 1;
          // here 0 is ptr_to_addr conf old w
          (\r a. Inst (asm_Mem Load r (Addr a (n2w 0)))) 1 0;
          // here 1 is m (ptr_to_addr conf old w)
          If Test 1 (Imm (n2w 3))
            (list_Seq [(\r v. Inst (Arith (asm_Shift Lsr r r (Imm
              (n2w v))))) 1 2;
                       (\r v. Inst (Arith (asm_Shift Lsl r r (Imm
                         (n2w v))))) 1 (shift_length conf);
                       clear_top_inst 5 (small_shift_length conf -
                         1);
                       (\r1 r2. Inst (Arith (asm_Binop Or r1 r1 (Reg
                         r2)))) 5 1])
            (list_Seq [
                       // get len+1w
                       (\r v. Inst (Arith (asm_Shift Lsr r r (Imm
                         (n2w v))))) 1 (dimindex (:'a) -
                         data_to_word_config_len_size conf);
                       (\r1. Inst (Arith (asm_Binop Add r1 r1 (Imm
                         (n2w 1))))) 1;
                       // store len+1w for later
                       (\dest src. Inst (Arith (asm_Binop Or dest src
                         (Reg src)))) 6 1;
                       // memcpy
                       (\dest src. Inst (Arith (asm_Binop Or dest src
                         (Reg src)))) 2 0;
                       (\dest src. Inst (Arith (asm_Binop Or dest src
                         (Reg src)))) 0 1;
                       memcpy_code;
                       // compute original header_addr
                       (\dest src. Inst (Arith (asm_Binop Or dest src
                         (Reg src)))) 0 6;
                       (\r v. Inst (Arith (asm_Shift Lsl r r (Imm
                         (n2w v))))) 0 (backend_common_word_shift
                         (:'a));
                       (\r1 r2. Inst (Arith (asm_Binop Sub r1 r1 (Reg
                         r2)))) 2 0;
                       // store i << 2 into header_addr
                       (\dest src. Inst (Arith (asm_Binop Or dest src
                         (Reg src)))) 0 4;
                       (\r v. Inst (Arith (asm_Shift Lsl r r (Imm
                         (n2w v))))) 0 2;
                       (\r a. Inst (asm_Mem Store r (Addr a (n2w
                         0)))) 0 2;
                       // compute update_addr conf i w, where i in 4 and w in 5
                       (\dest src. Inst (Arith (asm_Binop Or dest src
                         (Reg src)))) 1 4;
                       clear_top_inst 5 (small_shift_length conf -
                         1);
                       (\r v. Inst (Arith (asm_Shift Lsl r r (Imm
                         (n2w v))))) 1 (shift_length conf);
                       (\r1 r2. Inst (Arith (asm_Binop Or r1 r1 (Reg
                         r2)))) 5 1;
                       // add to i in 4
                       (\r1 r2. Inst (Arith (asm_Binop Add r1 r1
                         (Reg r2)))) 4 6])])`;;

let word_gc_move_list_code_def = new_definition
  `word_gc_move_list_code conf =
     (\cmp r ri c. Loop (If cmp r ri c (Break 0))) asm_NotEqual 7
       (Imm ((n2w 0):'a word))
       (list_Seq [(\r a. Inst (asm_Mem Load r (Addr a (n2w 0)))) 5 8;
                  (\r1. Inst (Arith (asm_Binop Sub r1 r1 (Imm (n2w
                    1))))) 7;
                  word_gc_move_code conf;
                  (\r a. Inst (asm_Mem Store r (Addr a (n2w 0)))) 5
                    8;
                  (\r1. Inst (Arith (asm_Binop Add r1 r1 (Imm
                    (bytes_in_word))))) 8])`;;

let word_gc_move_loop_code_def = new_definition
  `word_gc_move_loop_code conf =
     ((\cmp r ri c. Loop (If cmp r ri c (Break 0))) asm_NotEqual 3
       (Reg 8)
      (list_Seq [(\r a. Inst (asm_Mem Load r (Addr a (n2w 0)))) 7 8;
                 If Test 7 (Imm (n2w 4))
                   (list_Seq [(\r v. Inst (Arith (asm_Shift Lsr r r
                     (Imm (n2w v))))) 7 (dimindex (:'a) -
                     data_to_word_config_len_size conf);
                              (\r1. Inst (Arith (asm_Binop Add r1 r1
                                (Imm (bytes_in_word))))) 8;
                              word_gc_move_list_code conf])
                   (list_Seq [(\r v. Inst (Arith (asm_Shift Lsr r r
                     (Imm (n2w v))))) 7 (dimindex (:'a) -
                     data_to_word_config_len_size conf);
                              (\r1. Inst (Arith (asm_Binop Add r1 r1
                                (Imm (n2w 1))))) 7;
                              (\r v. Inst (Arith (asm_Shift Lsl r r
                                (Imm (n2w v))))) 7
                                (backend_common_word_shift (:'a));
                              (\r1 r2. Inst (Arith (asm_Binop Add
                                r1 r1 (Reg r2)))) 8 7])]):'a
                                stackLang_prog)`;;

(* 7 is w, 8 is index into stack, 5 is input to word_gc_move_code *)
let word_gc_move_bitmap_code_def = new_definition
  `word_gc_move_bitmap_code conf =
     (\cmp r ri c. Loop (If cmp r ri c (Break 0))) asm_NotLower 7
       (Imm (n2w 2))
      (If Test 7 (Imm (n2w 1))
         (list_Seq [(\r v. Inst (Arith (asm_Shift Lsr r r (Imm (n2w
           v))))) 7 1;
                    (\r1. Inst (Arith (asm_Binop Add r1 r1 (Imm
                      (bytes_in_word))))) 8])
         (list_Seq [stackLang_StackLoadAny 5 8;
                    (\r v. Inst (Arith (asm_Shift Lsr r r (Imm (n2w
                      v))))) 7 1;
                    word_gc_move_code conf;
                    stackLang_StackStoreAny 5 8;
                    (\r1. Inst (Arith (asm_Binop Add r1 r1 (Imm
                      (bytes_in_word))))) 8]))`;;

(* 9 is w, 8 is index into stack *)
let word_gc_move_bitmaps_code_def = new_definition
  `((word_gc_move_bitmaps_code conf):'a stackLang_prog) =
     (\cmp r ri c. Loop (If cmp r ri c (Break 0))) asm_NotTest 0 (Reg
       0)
       (list_Seq [stackLang_BitmapLoad 7 9;
                  word_gc_move_bitmap_code conf;
                  stackLang_BitmapLoad 0 9;
                  (\r1. Inst (Arith (asm_Binop Add r1 r1 (Imm (n2w
                    1))))) 9;
                  (\r v. Inst (Arith (asm_Shift Lsr r r (Imm (n2w
                    v))))) 0 (dimindex (:'a) - 1)])`;;

(* 9 is w, 8 is index into stack *)
let word_gc_move_roots_bitmaps_code_def = new_definition
  `((word_gc_move_roots_bitmaps_code conf):'a stackLang_prog) =
     (\cmp r ri c. Loop (If cmp r ri c (Break 0))) asm_NotTest 9 (Reg
       9)
       (list_Seq [(\dest src. Inst (Arith (asm_Binop Or dest src (Reg
         src)))) 0 9;
                  (\r1. Inst (Arith (asm_Binop Sub r1 r1 (Imm (n2w
                    1))))) 9;
                  (\r1. Inst (Arith (asm_Binop Add r1 r1 (Imm
                    (bytes_in_word))))) 8;
                  word_gc_move_bitmaps_code conf;
                  stackLang_StackLoadAny 9 8])`;;

let word_gen_gc_move_code_def = new_definition
  `word_gen_gc_move_code conf =
     (If Test 5 (Imm ((n2w 1):'a word)) Skip
       (list_Seq
         [(\dest src. Inst (Arith (asm_Binop Or dest src (Reg src))))
           0 5;
          Get 1 CurrHeap;
          (\r v. Inst (Arith (asm_Shift Lsr r r (Imm (n2w v))))) 0
            (shift_length conf);
          (\r v. Inst (Arith (asm_Shift Lsl r r (Imm (n2w v))))) 0
            (backend_common_word_shift (:'a));
          (\r1 r2. Inst (Arith (asm_Binop Add r1 r1 (Reg r2)))) 0 1;
          // here 0 is ptr_to_addr conf old w
          (\r a. Inst (asm_Mem Load r (Addr a (n2w 0)))) 1 0;
          // here 1 is m (ptr_to_addr conf old w)
          If Test 1 (Imm (n2w 3))
            (list_Seq [(\r v. Inst (Arith (asm_Shift Lsr r r (Imm
              (n2w v))))) 1 2;
                       (\r v. Inst (Arith (asm_Shift Lsl r r (Imm
                         (n2w v))))) 1 (shift_length conf);
                       clear_top_inst 5 (small_shift_length conf -
                         1);
                       (\r1 r2. Inst (Arith (asm_Binop Or r1 r1 (Reg
                         r2)))) 5 1])
            (list_Seq [
                       // put header in 6
                       (\dest src. Inst (Arith (asm_Binop Or dest src
                         (Reg src)))) 6 1;
                       // get len+1w
                       (\r v. Inst (Arith (asm_Shift Lsr r r (Imm
                         (n2w v))))) 1 (dimindex (:'a) -
                         data_to_word_config_len_size conf);
                       (\r1. Inst (Arith (asm_Binop Add r1 r1 (Imm
                         (n2w 1))))) 1;
                       (\r w. Inst (Const r w)) 2 (n2w 0b1100);
                       (\r1 r2. Inst (Arith (asm_Binop And r1 r1 (Reg
                         r2)))) 6 2;
                       If Equal 6 (Imm (n2w 8))
                         (
                          // is_ref_header
                          list_Seq [
                           Set (Temp (n2w 0)) 3;
                           Set (Temp (n2w 1)) 4;
                           Get 3 (Temp (n2w 2));
                           // ib
                           Get 4 (Temp (n2w 3));
                           // pb
                           // store len+1w for later
                           (\dest src. Inst (Arith (asm_Binop Or dest
                             src (Reg src)))) 6 1;
                           (\r v. Inst (Arith (asm_Shift Lsl r r (Imm
                             (n2w v))))) 1 (backend_common_word_shift
                             (:'a));
                           (\r1 r2. Inst (Arith (asm_Binop Sub r1 r1
                             (Reg r2)))) 4 6;
                           (\r1 r2. Inst (Arith (asm_Binop Sub r1 r1
                             (Reg r2)))) 3 1;
                           Set (Temp (n2w 2)) 3;
                           // new ib
                           Set (Temp (n2w 3)) 4;
                           // new pb
                           // memcpy
                           (\dest src. Inst (Arith (asm_Binop Or dest
                             src (Reg src)))) 2 0;
                           (\dest src. Inst (Arith (asm_Binop Or dest
                             src (Reg src)))) 4 0;
                           (\dest src. Inst (Arith (asm_Binop Or dest
                             src (Reg src)))) 0 6;
                           memcpy_code;
                           // compute original header_addr
                           Get 0 (Temp (n2w 3));
                           // fixed?
                           (\r v. Inst (Arith (asm_Shift Lsl r r (Imm
                             (n2w v))))) 0 2;
                           (\r a. Inst (asm_Mem Store r (Addr a (n2w
                             0)))) 0 4;
                           // compute update_addr conf i w, where w in 5
                           Get 1 (Temp (n2w 3));
                           clear_top_inst 5 (small_shift_length conf
                             - 1);
                           (\r v. Inst (Arith (asm_Shift Lsl r r (Imm
                             (n2w v))))) 1 (shift_length conf);
                           (\r1 r2. Inst (Arith (asm_Binop Or r1 r1
                             (Reg r2)))) 5 1;
                           Get 3 (Temp (n2w 0));
                           Get 4 (Temp (n2w 1))])
                         (list_Seq [
                           // store len+1w for later
                           (\dest src. Inst (Arith (asm_Binop Or dest
                             src (Reg src)))) 6 1;
                           // memcpy
                           (\dest src. Inst (Arith (asm_Binop Or dest
                             src (Reg src)))) 2 0;
                           (\dest src. Inst (Arith (asm_Binop Or dest
                             src (Reg src)))) 0 1;
                           memcpy_code;
                           // compute original header_addr
                           (\dest src. Inst (Arith (asm_Binop Or dest
                             src (Reg src)))) 0 6;
                           (\r v. Inst (Arith (asm_Shift Lsl r r (Imm
                             (n2w v))))) 0 (backend_common_word_shift
                             (:'a));
                           (\r1 r2. Inst (Arith (asm_Binop Sub r1 r1
                             (Reg r2)))) 2 0;
                           // store i << 2 into header_addr
                           (\dest src. Inst (Arith (asm_Binop Or dest
                             src (Reg src)))) 0 4;
                           (\r v. Inst (Arith (asm_Shift Lsl r r (Imm
                             (n2w v))))) 0 2;
                           (\r a. Inst (asm_Mem Store r (Addr a (n2w
                             0)))) 0 2;
                           // compute update_addr conf i w, where i in 4 and w in 5
                           (\dest src. Inst (Arith (asm_Binop Or dest
                             src (Reg src)))) 1 4;
                           clear_top_inst 5 (small_shift_length conf
                             - 1);
                           (\r v. Inst (Arith (asm_Shift Lsl r r (Imm
                             (n2w v))))) 1 (shift_length conf);
                           (\r1 r2. Inst (Arith (asm_Binop Or r1 r1
                             (Reg r2)))) 5 1;
                           // add to i in 4
                           (\r1 r2. Inst (Arith (asm_Binop Add r1
                             r1 (Reg r2)))) 4 6])])]):'a
                             stackLang_prog)`;;

let word_gen_gc_partial_move_code_def = new_definition
  `word_gen_gc_partial_move_code conf =
     // uses 0,1,2,6 as temps
     (If Test 5 (Imm ((n2w 1):'a word)) Skip
       (list_Seq
         [(\dest src. Inst (Arith (asm_Binop Or dest src (Reg src))))
           0 5;
          Get 6 (Temp (n2w 0));
          (\r v. Inst (Arith (asm_Shift Lsr r r (Imm (n2w v))))) 0
            (shift_length conf);
          (\r v. Inst (Arith (asm_Shift Lsl r r (Imm (n2w v))))) 0
            (backend_common_word_shift (:'a));
          Get 1 (Temp (n2w 1));
          If asm_Lower 0 (Reg 6) Skip
           (Seq (Get 6 (Temp (n2w 1)))
           (If asm_NotLower 0 (Reg 1) Skip (list_Seq [
              Get 1 CurrHeap;
              (\r1 r2. Inst (Arith (asm_Binop Add r1 r1 (Reg r2)))) 0
                1;
              // here 0 is ptr_to_addr conf old w
              (\r a. Inst (asm_Mem Load r (Addr a (n2w 0)))) 1 0;
              // here 1 is m (ptr_to_addr conf old w)
              If Test 1 (Imm (n2w 3))
                (list_Seq [(\r v. Inst (Arith (asm_Shift Lsr r r (Imm
                  (n2w v))))) 1 2;
                           (\r v. Inst (Arith (asm_Shift Lsl r r (Imm
                             (n2w v))))) 1 (shift_length conf);
                           clear_top_inst 5 (small_shift_length conf
                             - 1);
                           (\r1 r2. Inst (Arith (asm_Binop Or r1 r1
                             (Reg r2)))) 5 1])
                (list_Seq [
                           // put header in 6
                           (\dest src. Inst (Arith (asm_Binop Or dest
                             src (Reg src)))) 6 1;
                           // get len+1w
                           (\r v. Inst (Arith (asm_Shift Lsr r r (Imm
                             (n2w v))))) 1 (dimindex (:'a) -
                             data_to_word_config_len_size conf);
                           (\r1. Inst (Arith (asm_Binop Add r1 r1
                             (Imm (n2w 1))))) 1;
                           // store len+1w for later
                           (\dest src. Inst (Arith (asm_Binop Or dest
                             src (Reg src)))) 6 1;
                           // memcpy
                           (\dest src. Inst (Arith (asm_Binop Or dest
                             src (Reg src)))) 2 0;
                           (\dest src. Inst (Arith (asm_Binop Or dest
                             src (Reg src)))) 0 1;
                           memcpy_code;
                           // compute original header_addr
                           (\dest src. Inst (Arith (asm_Binop Or dest
                             src (Reg src)))) 0 6;
                           (\r v. Inst (Arith (asm_Shift Lsl r r (Imm
                             (n2w v))))) 0 (backend_common_word_shift
                             (:'a));
                           (\r1 r2. Inst (Arith (asm_Binop Sub r1 r1
                             (Reg r2)))) 2 0;
                           // store i << 2 into header_addr
                           (\dest src. Inst (Arith (asm_Binop Or dest
                             src (Reg src)))) 0 4;
                           (\r v. Inst (Arith (asm_Shift Lsl r r (Imm
                             (n2w v))))) 0 2;
                           (\r a. Inst (asm_Mem Store r (Addr a (n2w
                             0)))) 0 2;
                           // compute update_addr conf i w, where i in 4 and w in 5
                           (\dest src. Inst (Arith (asm_Binop Or dest
                             src (Reg src)))) 1 4;
                           clear_top_inst 5 (small_shift_length conf
                             - 1);
                           (\r v. Inst (Arith (asm_Shift Lsl r r (Imm
                             (n2w v))))) 1 (shift_length conf);
                           (\r1 r2. Inst (Arith (asm_Binop Or r1 r1
                             (Reg r2)))) 5 1;
                           // add to i in 4
                           (\r1 r2. Inst (Arith (asm_Binop Add r1
                             r1 (Reg r2)))) 4 6])])))]):'a
                             stackLang_prog)`;;

let word_gen_gc_move_bitmap_code_def = new_definition
  `word_gen_gc_move_bitmap_code conf =
     (\cmp r ri c. Loop (If cmp r ri c (Break 0))) asm_NotLower 7
       (Imm (n2w 2))
      (If Test 7 (Imm (n2w 1))
         (list_Seq [(\r v. Inst (Arith (asm_Shift Lsr r r (Imm (n2w
           v))))) 7 1;
                    (\r1. Inst (Arith (asm_Binop Add r1 r1 (Imm
                      (bytes_in_word))))) 8])
         (list_Seq [stackLang_StackLoadAny 5 8;
                    (\r v. Inst (Arith (asm_Shift Lsr r r (Imm (n2w
                      v))))) 7 1;
                    word_gen_gc_move_code conf;
                    stackLang_StackStoreAny 5 8;
                    (\r1. Inst (Arith (asm_Binop Add r1 r1 (Imm
                      (bytes_in_word))))) 8]))`;;

let word_gen_gc_partial_move_bitmap_code_def = new_definition
  `word_gen_gc_partial_move_bitmap_code conf =
     (\cmp r ri c. Loop (If cmp r ri c (Break 0))) asm_NotLower 7
       (Imm (n2w 2))
      (If Test 7 (Imm (n2w 1))
         (list_Seq [(\r v. Inst (Arith (asm_Shift Lsr r r (Imm (n2w
           v))))) 7 1;
                    (\r1. Inst (Arith (asm_Binop Add r1 r1 (Imm
                      (bytes_in_word))))) 8])
         (list_Seq [stackLang_StackLoadAny 5 8;
                    (\r v. Inst (Arith (asm_Shift Lsr r r (Imm (n2w
                      v))))) 7 1;
                    word_gen_gc_partial_move_code conf;
                    stackLang_StackStoreAny 5 8;
                    (\r1. Inst (Arith (asm_Binop Add r1 r1 (Imm
                      (bytes_in_word))))) 8]))`;;

(* 9 is w, 8 is index into stack *)
let word_gen_gc_move_bitmaps_code_def = new_definition
  `((word_gen_gc_move_bitmaps_code conf):'a stackLang_prog) =
     (\cmp r ri c. Loop (If cmp r ri c (Break 0))) asm_NotTest 0 (Reg
       0)
       (list_Seq [stackLang_BitmapLoad 7 9;
                  word_gen_gc_move_bitmap_code conf;
                  stackLang_BitmapLoad 0 9;
                  (\r1. Inst (Arith (asm_Binop Add r1 r1 (Imm (n2w
                    1))))) 9;
                  (\r v. Inst (Arith (asm_Shift Lsr r r (Imm (n2w
                    v))))) 0 (dimindex (:'a) - 1)])`;;

(* 9 is w, 8 is index into stack *)
let word_gen_gc_partial_move_bitmaps_code_def = new_definition
  `((word_gen_gc_partial_move_bitmaps_code conf):'a stackLang_prog) =
     (\cmp r ri c. Loop (If cmp r ri c (Break 0))) asm_NotTest 0 (Reg
       0)
       (list_Seq [stackLang_BitmapLoad 7 9;
                  word_gen_gc_partial_move_bitmap_code conf;
                  stackLang_BitmapLoad 0 9;
                  (\r1. Inst (Arith (asm_Binop Add r1 r1 (Imm (n2w
                    1))))) 9;
                  (\r v. Inst (Arith (asm_Shift Lsr r r (Imm (n2w
                    v))))) 0 (dimindex (:'a) - 1)])`;;

(* 9 is w, 8 is index into stack *)
let word_gen_gc_move_roots_bitmaps_code_def = new_definition
  `((word_gen_gc_move_roots_bitmaps_code conf):'a stackLang_prog) =
     (\cmp r ri c. Loop (If cmp r ri c (Break 0))) asm_NotTest 9 (Reg
       9)
       (list_Seq [(\dest src. Inst (Arith (asm_Binop Or dest src (Reg
         src)))) 0 9;
                  (\r1. Inst (Arith (asm_Binop Sub r1 r1 (Imm (n2w
                    1))))) 9;
                  (\r1. Inst (Arith (asm_Binop Add r1 r1 (Imm
                    (bytes_in_word))))) 8;
                  word_gen_gc_move_bitmaps_code conf;
                  stackLang_StackLoadAny 9 8])`;;

(* 9 is w, 8 is index into stack *)
let word_gen_gc_partial_move_roots_bitmaps_code_def = new_definition
  `((word_gen_gc_partial_move_roots_bitmaps_code conf):'a
  stackLang_prog) =
     (\cmp r ri c. Loop (If cmp r ri c (Break 0))) asm_NotTest 9 (Reg
       9)
       (list_Seq [(\dest src. Inst (Arith (asm_Binop Or dest src (Reg
         src)))) 0 9;
                  (\r1. Inst (Arith (asm_Binop Sub r1 r1 (Imm (n2w
                    1))))) 9;
                  (\r1. Inst (Arith (asm_Binop Add r1 r1 (Imm
                    (bytes_in_word))))) 8;
                  word_gen_gc_partial_move_bitmaps_code conf;
                  stackLang_StackLoadAny 9 8])`;;

let word_gen_gc_move_list_code_def = new_definition
  `word_gen_gc_move_list_code conf =
     (\cmp r ri c. Loop (If cmp r ri c (Break 0))) asm_NotEqual 7
       (Imm ((n2w 0):'a word))
       (list_Seq [(\r a. Inst (asm_Mem Load r (Addr a (n2w 0)))) 5 8;
                  (\r1. Inst (Arith (asm_Binop Sub r1 r1 (Imm (n2w
                    1))))) 7;
                  word_gen_gc_move_code conf;
                  (\r a. Inst (asm_Mem Store r (Addr a (n2w 0)))) 5
                    8;
                  (\r1. Inst (Arith (asm_Binop Add r1 r1 (Imm
                    (bytes_in_word))))) 8])`;;

let word_gen_gc_partial_move_list_code_def = new_definition
  `word_gen_gc_partial_move_list_code conf =
     (\cmp r ri c. Loop (If cmp r ri c (Break 0))) asm_NotEqual 7
       (Imm ((n2w 0):'a word))
       (list_Seq [(\r a. Inst (asm_Mem Load r (Addr a (n2w 0)))) 5 8;
                  (\r1. Inst (Arith (asm_Binop Sub r1 r1 (Imm (n2w
                    1))))) 7;
                  word_gen_gc_partial_move_code conf;
                  (\r a. Inst (asm_Mem Store r (Addr a (n2w 0)))) 5
                    8;
                  (\r1. Inst (Arith (asm_Binop Add r1 r1 (Imm
                    (bytes_in_word))))) 8])`;;

let word_gen_gc_move_data_code_def = new_definition
  `word_gen_gc_move_data_code conf =
     ((\cmp r ri c. Loop (If cmp r ri c (Break 0))) asm_NotEqual 3
       (Reg 8)
      (list_Seq [(\r a. Inst (asm_Mem Load r (Addr a (n2w 0)))) 7 8;
                 If Test 7 (Imm (n2w 4))
                   (list_Seq [(\r v. Inst (Arith (asm_Shift Lsr r r
                     (Imm (n2w v))))) 7 (dimindex (:'a) -
                     data_to_word_config_len_size conf);
                              (\r1. Inst (Arith (asm_Binop Add r1 r1
                                (Imm (bytes_in_word))))) 8;
                              word_gen_gc_move_list_code conf])
                   (list_Seq [(\r v. Inst (Arith (asm_Shift Lsr r r
                     (Imm (n2w v))))) 7 (dimindex (:'a) -
                     data_to_word_config_len_size conf);
                              (\r1. Inst (Arith (asm_Binop Add r1 r1
                                (Imm (n2w 1))))) 7;
                              (\r v. Inst (Arith (asm_Shift Lsl r r
                                (Imm (n2w v))))) 7
                                (backend_common_word_shift (:'a));
                              (\r1 r2. Inst (Arith (asm_Binop Add
                                r1 r1 (Reg r2)))) 8 7])]):'a
                                stackLang_prog)`;;

let word_gen_gc_partial_move_ref_list_code_def = new_definition
  `word_gen_gc_partial_move_ref_list_code conf =
     ((\cmp r ri c. Loop (If cmp r ri c (Break 0))) asm_NotEqual 9
       (Reg 8)
      (list_Seq [(\r a. Inst (asm_Mem Load r (Addr a (n2w 0)))) 7 8;
                 (\r v. Inst (Arith (asm_Shift Lsr r r (Imm (n2w
                   v))))) 7 (dimindex (:'a) -
                   data_to_word_config_len_size conf);
                 (\r1. Inst (Arith (asm_Binop Add r1 r1 (Imm
                   (bytes_in_word))))) 8;
                 word_gen_gc_partial_move_list_code conf]):'a
                   stackLang_prog)`;;

let word_gen_gc_partial_move_data_code_def = new_definition
  `word_gen_gc_partial_move_data_code conf =
     ((\cmp r ri c. Loop (If cmp r ri c (Break 0))) asm_NotEqual 3
       (Reg 8)
      (list_Seq [(\r a. Inst (asm_Mem Load r (Addr a (n2w 0)))) 7 8;
                 If Test 7 (Imm (n2w 4))
                   (list_Seq [(\r v. Inst (Arith (asm_Shift Lsr r r
                     (Imm (n2w v))))) 7 (dimindex (:'a) -
                     data_to_word_config_len_size conf);
                              (\r1. Inst (Arith (asm_Binop Add r1 r1
                                (Imm (bytes_in_word))))) 8;
                              word_gen_gc_partial_move_list_code
                                conf])
                   (list_Seq [(\r v. Inst (Arith (asm_Shift Lsr r r
                     (Imm (n2w v))))) 7 (dimindex (:'a) -
                     data_to_word_config_len_size conf);
                              (\r1. Inst (Arith (asm_Binop Add r1 r1
                                (Imm (n2w 1))))) 7;
                              (\r v. Inst (Arith (asm_Shift Lsl r r
                                (Imm (n2w v))))) 7
                                (backend_common_word_shift (:'a));
                              (\r1 r2. Inst (Arith (asm_Binop Add
                                r1 r1 (Reg r2)))) 8 7])]):'a
                                stackLang_prog)`;;

let word_gen_gc_move_refs_code_def = new_definition
  `word_gen_gc_move_refs_code conf =
     // r2a in 8, r1a in 0 and Temp 4w
     ((\cmp r ri c. Loop (If cmp r ri c (Break 0))) asm_NotEqual 0
       (Reg 8)
      (list_Seq [(\r a. Inst (asm_Mem Load r (Addr a (n2w 0)))) 7 8;
                 (\r v. Inst (Arith (asm_Shift Lsr r r (Imm (n2w
                   v))))) 7 (dimindex (:'a) -
                   data_to_word_config_len_size conf);
                 (\r1. Inst (Arith (asm_Binop Add r1 r1 (Imm
                   (bytes_in_word))))) 8;
                 word_gen_gc_move_list_code conf;
                 Get 0 (Temp (n2w 4))]):'a stackLang_prog)`;;

let word_gen_gc_move_loop_code_def = new_definition
  `word_gen_gc_move_loop_code conf =
     // 7 is 0w iff pbx = pb and pax = pa, 1 is pbx (Temp 4w), 2 is pb,
     // 8 is pax, 3 is pa
     (\cmp r ri c. Loop (If cmp r ri c (Break 0))) asm_NotTest 7 (Reg
       7)
       (If Equal 1 (Reg 2)
          (
           // case: pax <> pa, i.e. move_data
           list_Seq [word_gen_gc_move_data_code conf;
                     Get 5 (Temp (n2w 2));
                     Get 7 (Temp (n2w 4));
                     (\dest src. Inst (Arith (asm_Binop Or dest src
                       (Reg src)))) 1 7;
                     (\dest src. Inst (Arith (asm_Binop Or dest src
                       (Reg src)))) 2 5;
                     (\r1 r2. Inst (Arith (asm_Binop Sub r1 r1 (Reg
                       r2)))) 7 5])
          (
           // case: pbx <> pb i.e. move_refs
           list_Seq [(\dest src. Inst (Arith (asm_Binop Or dest src
             (Reg src)))) 0 1;
                     Set (Temp (n2w 6)) 8;
                     (\dest src. Inst (Arith (asm_Binop Or dest src
                       (Reg src)))) 8 2;
                     Set (Temp (n2w 5)) 8;
                     word_gen_gc_move_refs_code conf;
                     (\dest src. Inst (Arith (asm_Binop Or dest src
                       (Reg src)))) 7 8;
                     // pbx'
                     Get 1 (Temp (n2w 5));
                     // pb
                     Get 2 (Temp (n2w 5));
                     Set (Temp (n2w 4)) 2;
                     Get 2 (Temp (n2w 2));
                     // pb'
                     (\dest src. Inst (Arith (asm_Binop Or dest src
                       (Reg src)))) 3 3;
                     // pa'
                     (\dest src. Inst (Arith (asm_Binop Or dest src
                       (Reg src)))) 4 4;
                     // i'
                     (\dest src. Inst (Arith (asm_Binop Or dest src
                       (Reg src)))) 7 1;
                     (\r1 r2. Inst (Arith (asm_Binop Sub r1 r1 (Reg
                       r2)))) 7 2;
                     // pbx' - pa'
                     Get 8 (Temp (n2w 6));
                     // pax
                     (\dest src. Inst (Arith (asm_Binop Or dest src
                       (Reg src)))) 5 8;
                     // pax - pa'
                     (\r1 r2. Inst (Arith (asm_Binop Sub r1 r1 (Reg
                       r2)))) 5 3;
                     (\r1 r2. Inst (Arith (asm_Binop Or r1 r1 (Reg
                       r2)))) 7 5]))`;;

let word_gc_partial_or_full_def = new_definition
  `word_gc_partial_or_full gen_sizes partial_code full_code =
     (match gen_sizes with [] -> list_Seq ([stackLang_Get 8
       TriggerGC; stackLang_Get 7 EndOfHeap; (\r1 r2. Inst (Arith
       (asm_Binop Sub r1 r1 (Reg r2)))) 7 8] ++ full_code) | _1 ->
       list_Seq
              [stackLang_Get 8 TriggerGC;
               stackLang_Get 7 EndOfHeap;
               (\r1 r2. Inst (Arith (asm_Binop Sub r1 r1 (Reg r2))))
                 7 8;
               stackLang_If asm_NotLower 7 (Reg 1)
                 (list_Seq partial_code)
                 (list_Seq full_code)])`;;

let SetNewTrigger_def = new_definition
  `SetNewTrigger (endh:num) (ib:num) gs =
     list_Seq [(\r w. Inst (Const r w)) 1 ((get_gen_size gs):'a
       word);
               Get 7 AllocSize;
               (\dest src. Inst (Arith (asm_Binop Or dest src (Reg
                 src)))) 4 endh;
               (\r1 r2. Inst (Arith (asm_Binop Sub r1 r1 (Reg r2))))
                 4 ib;
               If asm_Lower 1 (Reg 7)
                 (If asm_Lower 4 (Reg 7)
                    (Set TriggerGC endh)
                    (If Test 7 (Imm (if dimindex (:'a) = 32 then (n2w
                      3) else (n2w 7)))
                      (Seq ((\r1 r2. Inst (Arith (asm_Binop Add r1 r1
                        (Reg r2)))) 7 ib) (Set TriggerGC 7))
                      (Set TriggerGC endh)))
                 (If asm_Lower 4 (Reg 1)
                    (Set TriggerGC endh)
                    (Seq ((\r1 r2. Inst (Arith (asm_Binop Add r1
                      r1 (Reg r2)))) 1 ib) (Set TriggerGC 1)))]`;;

let word_gc_code_def = new_definition
  `word_gc_code conf =
     (match data_to_word_config_gc_kind conf with None ->
         (list_Seq
               [Set AllocSize 1;
                Get 2 CurrHeap;
                Set NextFree 2;
                Set TriggerGC 2;
                Set EndOfHeap 2;
                If Test 1 (Reg 1) Skip (Seq ((\r w. Inst (Const r w))
                  1 (n2w 1)) (stackLang_Halt 1))]) | Simple ->
         (list_Seq
               [Set AllocSize 1;
                Set NextFree 0;
                (\r w. Inst (Const r w)) 1 (n2w 0);
                (\dest src. Inst (Arith (asm_Binop Or dest src (Reg
                  src)))) 2 1;
                Get 3 OtherHeap;
                (\dest src. Inst (Arith (asm_Binop Or dest src (Reg
                  src)))) 4 1;
                Get 5 Globals;
                (\dest src. Inst (Arith (asm_Binop Or dest src (Reg
                  src)))) 6 1;
                (\dest src. Inst (Arith (asm_Binop Or dest src (Reg
                  src)))) 8 1;
                word_gc_move_code conf;
                Set Globals 5;
                (\dest src. Inst (Arith (asm_Binop Or dest src (Reg
                  src)))) 7 5;
                (\r v. Inst (Arith (asm_Shift Lsr r r (Imm (n2w
                  v))))) 7 (shift_length conf);
                (\r v. Inst (Arith (asm_Shift Lsl r r (Imm (n2w
                  v))))) 7 (backend_common_word_shift (:'a));
                Get 9 OtherHeap;
                (\r1 r2. Inst (Arith (asm_Binop Add r1 r1 (Reg r2))))
                  7 9;
                Set GlobReal 7;
                (\r w. Inst (Const r w)) 7 (n2w 0);
                stackLang_StackLoadAny 9 8;
                (\dest src. Inst (Arith (asm_Binop Or dest src (Reg
                  src)))) 8 7;
                word_gc_move_roots_bitmaps_code conf;
                Get 8 OtherHeap;
                word_gc_move_loop_code conf;
                Get 0 CurrHeap;
                Get 1 OtherHeap;
                Get 2 HeapLength;
                (\r1 r2. Inst (Arith (asm_Binop Add r1 r1 (Reg r2))))
                  2 1;
                Set CurrHeap 1;
                Set OtherHeap 0;
                Get 0 NextFree;
                Set NextFree 8;
                Set EndOfHeap 2;
                Set TriggerGC 2;
                Get 1 AllocSize;
                (\r1 r2. Inst (Arith (asm_Binop Sub r1 r1 (Reg r2))))
                  2 8;
                If asm_Lower 2 (Reg 1) (Seq ((\r w. Inst (Const r w))
                  1 (n2w 1)) (stackLang_Halt 1)) Skip]) |
                  data_to_word_Generational gen_sizes ->
         ((word_gc_partial_or_full gen_sizes
               [
                // gen_gc_partial
                Set AllocSize 1;
                Set NextFree 0;
                Get 4 GenStart;
                Get 5 EndOfHeap;
                Get 2 CurrHeap;
                Set (Temp (n2w 0)) 4;
                (\r1 r2. Inst (Arith (asm_Binop Sub r1 r1 (Reg r2))))
                  5 2;
                Set (Temp (n2w 1)) 5;
                Get 7 HeapLength;
                Get 5 Globals;
                Get 3 OtherHeap;
                (\r v. Inst (Arith (asm_Shift Lsr r r (Imm (n2w
                  v))))) 4 (backend_common_word_shift (:'a));
                (\dest src. Inst (Arith (asm_Binop Or dest src (Reg
                  src)))) 6 3;
                word_gen_gc_partial_move_code conf;
                Set Globals 5;
                (\dest src. Inst (Arith (asm_Binop Or dest src (Reg
                  src)))) 8 5;
                (\r v. Inst (Arith (asm_Shift Lsr r r (Imm (n2w
                  v))))) 8 (shift_length conf);
                (\r v. Inst (Arith (asm_Shift Lsl r r (Imm (n2w
                  v))))) 8 (backend_common_word_shift (:'a));
                Get 9 CurrHeap;
                (\r1 r2. Inst (Arith (asm_Binop Add r1 r1 (Reg r2))))
                  8 9;
                Set GlobReal 8;
                (\r w. Inst (Const r w)) 8 (n2w 0);
                stackLang_StackLoadAny 9 8;
                word_gen_gc_partial_move_roots_bitmaps_code conf;
                Get 8 CurrHeap;
                Get 9 HeapLength;
                (\r1 r2. Inst (Arith (asm_Binop Add r1 r1 (Reg r2))))
                  9 8;
                Get 8 EndOfHeap;
                word_gen_gc_partial_move_ref_list_code conf;
                Get 8 OtherHeap;
                word_gen_gc_partial_move_data_code conf;
                Get 2 OtherHeap;
                (\dest src. Inst (Arith (asm_Binop Or dest src (Reg
                  src)))) 0 3;
                (\r1 r2. Inst (Arith (asm_Binop Sub r1 r1 (Reg r2))))
                  0 2;
                (\r v. Inst (Arith (asm_Shift Lsr r r (Imm (n2w
                  v))))) 0 (backend_common_word_shift (:'a));
                Get 3 GenStart;
                Get 1 CurrHeap;
                (\r1 r2. Inst (Arith (asm_Binop Add r1 r1 (Reg r2))))
                  3 1;
                memcpy_code;
                Get 0 NextFree;
                Set NextFree 3;
                Get 8 EndOfHeap;
                Get 2 TriggerGC;
                SetNewTrigger 8 3 gen_sizes;
                (\r w. Inst (Const r w)) 1 (n2w 0);
                Set (Temp (n2w 0)) 1;
                Set (Temp (n2w 1)) 1;
                Get 1 AllocSize;
                (\r1 r2. Inst (Arith (asm_Binop Sub r1 r1 (Reg r2))))
                  8 3;
                Get 7 CurrHeap;
                (\r1 r2. Inst (Arith (asm_Binop Sub r1 r1 (Reg r2))))
                  3 7;
                Set GenStart 3]
               [
                // There is no need for a memory check here
                // because the partial collector is guaranteed
                // to get to a state where there is enough
                // memory for the allocation. In contrast,
                // the full collector below can hit a state
                // where there is not enough memory, and so it
                // can Halt execution.
                // gen_gc_full
                Set AllocSize 1;
                Set NextFree 0;
                (\r w. Inst (Const r w)) 1 ((n2w 0):'a word);
                (\dest src. Inst (Arith (asm_Binop Or dest src (Reg
                  src)))) 2 1;
                Get 3 OtherHeap;
                Get 4 HeapLength;
                (\r1 r2. Inst (Arith (asm_Binop Add r1 r1 (Reg r2))))
                  4 3;
                Set (Temp (n2w 0)) 4;
                Set (Temp (n2w 1)) 4;
                Set (Temp (n2w 2)) 4;
                Set (Temp (n2w 4)) 4;
                Set (Temp (n2w 5)) 4;
                Set (Temp (n2w 6)) 4;
                Get 4 HeapLength;
                (\r v. Inst (Arith (asm_Shift Lsr r r (Imm (n2w
                  v))))) 4 (backend_common_word_shift (:'a));
                Set (Temp (n2w 3)) 4;
                (\dest src. Inst (Arith (asm_Binop Or dest src (Reg
                  src)))) 4 1;
                Get 5 Globals;
                (\dest src. Inst (Arith (asm_Binop Or dest src (Reg
                  src)))) 6 1;
                (\dest src. Inst (Arith (asm_Binop Or dest src (Reg
                  src)))) 8 1;
                word_gen_gc_move_code conf;
                Set Globals 5;
                (\dest src. Inst (Arith (asm_Binop Or dest src (Reg
                  src)))) 7 5;
                Get 9 OtherHeap;
                (\r v. Inst (Arith (asm_Shift Lsr r r (Imm (n2w
                  v))))) 7 (shift_length conf);
                (\r v. Inst (Arith (asm_Shift Lsl r r (Imm (n2w
                  v))))) 7 (backend_common_word_shift (:'a));
                (\r1 r2. Inst (Arith (asm_Binop Add r1 r1 (Reg r2))))
                  7 9;
                Set GlobReal 7;
                (\r w. Inst (Const r w)) 7 (n2w 0);
                stackLang_StackLoadAny 9 8;
                (\dest src. Inst (Arith (asm_Binop Or dest src (Reg
                  src)))) 8 7;
                word_gen_gc_move_roots_bitmaps_code conf;
                Get 2 (Temp (n2w 2));
                Get 8 OtherHeap;
                (\dest src. Inst (Arith (asm_Binop Or dest src (Reg
                  src)))) 7 3;
                (\r1 r2. Inst (Arith (asm_Binop Sub r1 r1 (Reg r2))))
                  7 8;
                Get 1 (Temp (n2w 6));
                (\dest src. Inst (Arith (asm_Binop Or dest src (Reg
                  src)))) 6 2;
                (\r1 r2. Inst (Arith (asm_Binop Sub r1 r1 (Reg r2))))
                  6 1;
                (\r1 r2. Inst (Arith (asm_Binop Or r1 r1 (Reg r2))))
                  7 6;
                word_gen_gc_move_loop_code conf;
                Get 0 CurrHeap;
                Get 1 OtherHeap;
                Get 2 (Temp (n2w 2));
                Set CurrHeap 1;
                Set OtherHeap 0;
                Get 0 NextFree;
                Set NextFree 3;
                Set EndOfHeap 2;
                (\dest src. Inst (Arith (asm_Binop Or dest src (Reg
                  src)))) 8 3;
                (\r1 r2. Inst (Arith (asm_Binop Sub r1 r1 (Reg r2))))
                  8 1;
                Set GenStart 8;
                SetNewTrigger 2 3 gen_sizes;
                (\r w. Inst (Const r w)) 1 (n2w 0);
                Set (Temp (n2w 0)) 1;
                Set (Temp (n2w 1)) 1;
                Set (Temp (n2w 2)) 1;
                Set (Temp (n2w 3)) 1;
                Set (Temp (n2w 4)) 1;
                Set (Temp (n2w 5)) 1;
                Set (Temp (n2w 6)) 1;
                Get 1 AllocSize;
                Get 2 TriggerGC;
                (\r1 r2. Inst (Arith (asm_Binop Sub r1 r1 (Reg r2))))
                  2 3;
                If asm_Lower 2 (Reg 1) (Seq ((\r w. Inst (Const r
                  w)) 1 (n2w 1)) (stackLang_Halt 1)) Skip]):'a
                  stackLang_prog))`;;

let stack_alloc_stubs_def = new_definition
  `stack_alloc_stubs conf = [(gc_stub_location,Seq (word_gc_code
  conf) (Return 0))]`;;
hol4_overload "stubs" "stack_alloc_stubs";;

let stack_alloc_stub_names_def = new_definition
  `stack_alloc_stub_names one = [(gc_stub_location,(implode "_GC"))]`;;
hol4_overload "stub_names" "stack_alloc_stub_names";;

(* compiler *)

let _ = size_thms "stackLang_prog";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let next_lab_def,next_lab_ind = define_wf
  `MEASURE (\(x0,x1). stackLang_prog_size (\x. 0) x0)`
  [`next_lab (p:'a stackLang_prog) aux =
     (match p with Seq p1 p2 -> next_lab p1 (next_lab p2 aux) | If
       _2 _3 _4 p1 p2 -> next_lab p1 (next_lab p2 aux) | Loop p ->
       next_lab p aux | Call NONE _5 NONE -> aux | Call NONE _6 (SOME
       (_7,_8,l2)) -> MAX aux (l2 + 2) | Call (SOME (p,_9,_10,l2)) _11
       NONE -> next_lab p (MAX aux (l2 + 2)) | Call (SOME
       (p,_12,_13,l2)) _14 (SOME (p',_15,l3)) ->
           next_lab p (next_lab p' ((MAX (MAX l2 l3 + 2) aux)))
             | _16 -> aux)`];;

(* HOL4 stack_allocScript.sml:664-674: a theorem that HOL4 states as
   the value of an ML expression: next_lab_pmatch *)

(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let stack_alloc_comp_def,stack_alloc_comp_ind = define_guess_cheat
  [`stack_alloc_comp n m p =
     (match p with Seq p1 p2 ->
         (let (q1,m) = stack_alloc_comp n m p1 in
         let (q2,m) = stack_alloc_comp n m p2 in
           (Seq q1 q2,m)) | If c r ri p1 p2 ->
         (let (q1,m) = stack_alloc_comp n m p1 in
         let (q2,m) = stack_alloc_comp n m p2 in
           (If c r ri q1 q2,m)) | Loop p1 ->
         (let (q1,m) = stack_alloc_comp n m p1 in
           (Loop q1,m)) | Call NONE dest exc -> (Call NONE dest
             NONE,m) | Call (SOME (p1,lr,l1,l2)) dest exc ->
         (let (q1,m) = stack_alloc_comp n m p1 in
          (match exc with NONE -> (Call (SOME (q1,lr,l1,l2)) dest
            NONE,m) | SOME (p2,k1,k2) ->
               (let (q2,m) = stack_alloc_comp n m p2 in
                 (Call (SOME (q1,lr,l1,l2)) dest (SOME
                   (q2,k1,k2)),m)))) | Alloc k -> (Call (SOME
                   (Skip,0,n,m)) (INL gc_stub_location) NONE,m + 1)
                   | StoreConsts k1 k2 (SOME loc) -> (Call (SOME
                   (Skip,0,n,m)) (INL loc) NONE,m + 1) | _17 ->
                   (p,m))`];;
hol4_overload "comp" "stack_alloc_comp";;

(* HOL4 stack_allocScript.sml:705-714: a theorem that HOL4 states as
   the value of an ML expression: comp_pmatch *)

let prog_comp_def = new_definition
  `stack_alloc_prog_comp (n,p) = (n,FST (comp n (next_lab p 2) p))`;;
hol4_overload "prog_comp" "stack_alloc_prog_comp";;

let stack_alloc_compile_def = new_definition
  `stack_alloc_compile c prog = stubs c ++ MAP stack_alloc_prog_comp
  prog`;;
hol4_overload "compile" "stack_alloc_compile";;

(* and the overloads that this file cannot see are back in the
   interface *)
let _ = unhide_overloads ();;
