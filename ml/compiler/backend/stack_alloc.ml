(* ======================================================== *)
(*  stack_alloc: ported from HOL4's
    compiler/backend/stack_allocScript.sml
    A definition theory, with 32 definitions and 2 theorems.  Needed
    by stack_allocProof.ml, stack_to_lab.ml and
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
needs "compiler/backend/data_to_word.ml";;
needs "compiler/backend/stackLang.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "lib/byte.ml";;
needs "semantics/ast.ml";;

(* the theories whose names the Ancestors blocks of the source
   bring, which are the ones that its statements read: the
   overloads of every other theory come out of the interface
   while this file loads *)
let _ = hol4_ancestors "stack_alloc"
  ["data_to_word"; "stackLang"];;

let memcpy_code_def = new_definition
  `memcpy_code =
     (\cmp r ri c. stackLang_Loop (stackLang_If cmp r ri c
       (stackLang_Break 0))) asm_NotEqual 0 (Imm (n2w 0))
       (data_to_word_list_Seq [(\r a. stackLang_Inst (asm_Mem
         word_bignum_Load r (Addr a (n2w 0)))) 1 2;
                  (\r1. stackLang_Inst (asm_Arith (asm_Binop
                    word_bignum_Add r1 r1 (Imm (bytes_in_word))))) 2;
                  (\r1. stackLang_Inst (asm_Arith (asm_Binop
                    word_bignum_Sub r1 r1 (Imm (n2w 1))))) 0;
                  (\r a. stackLang_Inst (asm_Mem word_bignum_Store r
                    (Addr a (n2w 0)))) 1 3;
                  (\r1. stackLang_Inst (asm_Arith (asm_Binop
                    word_bignum_Add r1 r1 (Imm (bytes_in_word)))))
                    3])`;;

let clear_top_inst_def = new_definition
  `clear_top_inst i n =
     (stackLang_Seq ((\r v. stackLang_Inst (asm_Arith (asm_Shift Lsl
       r r (Imm (n2w v))))) i (dimindex (:'a) - n - 1))
         ((\r v. stackLang_Inst (asm_Arith (asm_Shift Lsr r r (Imm
           (n2w v))))) i (dimindex (:'a) - n - 1)):'a stackLang_prog)`;;

let word_gc_move_code_def = new_definition
  `word_gc_move_code conf =
     stackLang_If asm_Test 5 (Imm ((n2w 1):'a word)) stackLang_Skip
       (data_to_word_list_Seq
         [(\dest src. stackLang_Inst (asm_Arith (asm_Binop asm_Or
           dest src (Reg src)))) 0 5;
          stackLang_Get 1 CurrHeap;
          (\r v. stackLang_Inst (asm_Arith (asm_Shift Lsr r r (Imm
            (n2w v))))) 0 (shift_length conf);
          (\r v. stackLang_Inst (asm_Arith (asm_Shift Lsl r r (Imm
            (n2w v))))) 0 (backend_common_word_shift (:'a));
          (\r1 r2. stackLang_Inst (asm_Arith (asm_Binop
            word_bignum_Add r1 r1 (Reg r2)))) 0 1;
          // here 0 is ptr_to_addr conf old w
          (\r a. stackLang_Inst (asm_Mem word_bignum_Load r (Addr a
            (n2w 0)))) 1 0;
          // here 1 is m (ptr_to_addr conf old w)
          stackLang_If asm_Test 1 (Imm (n2w 3))
            (data_to_word_list_Seq [(\r v. stackLang_Inst (asm_Arith
              (asm_Shift Lsr r r (Imm (n2w v))))) 1 2;
                       (\r v. stackLang_Inst (asm_Arith (asm_Shift
                         Lsl r r (Imm (n2w v))))) 1 (shift_length conf);
                       clear_top_inst 5 (small_shift_length conf -
                         1);
                       (\r1 r2. stackLang_Inst (asm_Arith (asm_Binop
                         asm_Or r1 r1 (Reg r2)))) 5 1])
            (data_to_word_list_Seq [
                       // get len+1w
                       (\r v. stackLang_Inst (asm_Arith (asm_Shift
                         Lsr r r (Imm (n2w v))))) 1 (dimindex (:'a) -
                         data_to_word_config_len_size conf);
                       (\r1. stackLang_Inst (asm_Arith (asm_Binop
                         word_bignum_Add r1 r1 (Imm (n2w 1))))) 1;
                       // store len+1w for later
                       (\dest src. stackLang_Inst (asm_Arith
                         (asm_Binop asm_Or dest src (Reg src)))) 6 1;
                       // memcpy
                       (\dest src. stackLang_Inst (asm_Arith
                         (asm_Binop asm_Or dest src (Reg src)))) 2 0;
                       (\dest src. stackLang_Inst (asm_Arith
                         (asm_Binop asm_Or dest src (Reg src)))) 0 1;
                       memcpy_code;
                       // compute original header_addr
                       (\dest src. stackLang_Inst (asm_Arith
                         (asm_Binop asm_Or dest src (Reg src)))) 0 6;
                       (\r v. stackLang_Inst (asm_Arith (asm_Shift
                         Lsl r r (Imm (n2w v))))) 0
                         (backend_common_word_shift (:'a));
                       (\r1 r2. stackLang_Inst (asm_Arith (asm_Binop
                         word_bignum_Sub r1 r1 (Reg r2)))) 2 0;
                       // store i << 2 into header_addr
                       (\dest src. stackLang_Inst (asm_Arith
                         (asm_Binop asm_Or dest src (Reg src)))) 0 4;
                       (\r v. stackLang_Inst (asm_Arith (asm_Shift
                         Lsl r r (Imm (n2w v))))) 0 2;
                       (\r a. stackLang_Inst (asm_Mem
                         word_bignum_Store r (Addr a (n2w 0)))) 0 2;
                       // compute update_addr conf i w, where i in 4 and w in 5
                       (\dest src. stackLang_Inst (asm_Arith
                         (asm_Binop asm_Or dest src (Reg src)))) 1 4;
                       clear_top_inst 5 (small_shift_length conf -
                         1);
                       (\r v. stackLang_Inst (asm_Arith (asm_Shift
                         Lsl r r (Imm (n2w v))))) 1 (shift_length conf);
                       (\r1 r2. stackLang_Inst (asm_Arith (asm_Binop
                         asm_Or r1 r1 (Reg r2)))) 5 1;
                       // add to i in 4
                       (\r1 r2. stackLang_Inst (asm_Arith
                         (asm_Binop word_bignum_Add r1 r1 (Reg r2))))
                         4 6])])`;;

let word_gc_move_list_code_def = new_definition
  `word_gc_move_list_code conf =
     (\cmp r ri c. stackLang_Loop (stackLang_If cmp r ri c
       (stackLang_Break 0))) asm_NotEqual 7 (Imm ((n2w 0):'a word))
       (data_to_word_list_Seq [(\r a. stackLang_Inst (asm_Mem
         word_bignum_Load r (Addr a (n2w 0)))) 5 8;
                  (\r1. stackLang_Inst (asm_Arith (asm_Binop
                    word_bignum_Sub r1 r1 (Imm (n2w 1))))) 7;
                  word_gc_move_code conf;
                  (\r a. stackLang_Inst (asm_Mem word_bignum_Store r
                    (Addr a (n2w 0)))) 5 8;
                  (\r1. stackLang_Inst (asm_Arith (asm_Binop
                    word_bignum_Add r1 r1 (Imm (bytes_in_word)))))
                    8])`;;

let word_gc_move_loop_code_def = new_definition
  `word_gc_move_loop_code conf =
     ((\cmp r ri c. stackLang_Loop (stackLang_If cmp r ri c
       (stackLang_Break 0))) asm_NotEqual 3 (Reg 8)
      (data_to_word_list_Seq [(\r a. stackLang_Inst (asm_Mem
        word_bignum_Load r (Addr a (n2w 0)))) 7 8;
                 stackLang_If asm_Test 7 (Imm (n2w 4))
                   (data_to_word_list_Seq [(\r v. stackLang_Inst
                     (asm_Arith (asm_Shift Lsr r r (Imm (n2w v))))) 7
                     (dimindex (:'a) - data_to_word_config_len_size
                     conf);
                              (\r1. stackLang_Inst (asm_Arith
                                (asm_Binop word_bignum_Add r1 r1 (Imm
                                (bytes_in_word))))) 8;
                              word_gc_move_list_code conf])
                   (data_to_word_list_Seq [(\r v. stackLang_Inst
                     (asm_Arith (asm_Shift Lsr r r (Imm (n2w v))))) 7
                     (dimindex (:'a) - data_to_word_config_len_size
                     conf);
                              (\r1. stackLang_Inst (asm_Arith
                                (asm_Binop word_bignum_Add r1 r1 (Imm
                                (n2w 1))))) 7;
                              (\r v. stackLang_Inst (asm_Arith
                                (asm_Shift Lsl r r (Imm (n2w v))))) 7
                                (backend_common_word_shift (:'a));
                              (\r1 r2. stackLang_Inst (asm_Arith
                                (asm_Binop word_bignum_Add r1 r1 (Reg
                                r2)))) 8 7])]):'a stackLang_prog)`;;

(* 7 is w, 8 is index into stack, 5 is input to word_gc_move_code *)
let word_gc_move_bitmap_code_def = new_definition
  `word_gc_move_bitmap_code conf =
     (\cmp r ri c. stackLang_Loop (stackLang_If cmp r ri c
       (stackLang_Break 0))) asm_NotLower 7 (Imm (n2w 2))
      (stackLang_If asm_Test 7 (Imm (n2w 1))
         (data_to_word_list_Seq [(\r v. stackLang_Inst (asm_Arith
           (asm_Shift Lsr r r (Imm (n2w v))))) 7 1;
                    (\r1. stackLang_Inst (asm_Arith (asm_Binop
                      word_bignum_Add r1 r1 (Imm (bytes_in_word))))) 8])
         (data_to_word_list_Seq [stackLang_StackLoadAny 5 8;
                    (\r v. stackLang_Inst (asm_Arith (asm_Shift Lsr r
                      r (Imm (n2w v))))) 7 1;
                    word_gc_move_code conf;
                    stackLang_StackStoreAny 5 8;
                    (\r1. stackLang_Inst (asm_Arith (asm_Binop
                      word_bignum_Add r1 r1 (Imm (bytes_in_word)))))
                      8]))`;;

(* 9 is w, 8 is index into stack *)
let word_gc_move_bitmaps_code_def = new_definition
  `((word_gc_move_bitmaps_code conf):'a stackLang_prog) =
     (\cmp r ri c. stackLang_Loop (stackLang_If cmp r ri c
       (stackLang_Break 0))) asm_NotTest 0 (Reg 0)
       (data_to_word_list_Seq [stackLang_BitmapLoad 7 9;
                  word_gc_move_bitmap_code conf;
                  stackLang_BitmapLoad 0 9;
                  (\r1. stackLang_Inst (asm_Arith (asm_Binop
                    word_bignum_Add r1 r1 (Imm (n2w 1))))) 9;
                  (\r v. stackLang_Inst (asm_Arith (asm_Shift Lsr
                    r r (Imm (n2w v))))) 0 (dimindex (:'a) - 1)])`;;

(* 9 is w, 8 is index into stack *)
let word_gc_move_roots_bitmaps_code_def = new_definition
  `((word_gc_move_roots_bitmaps_code conf):'a stackLang_prog) =
     (\cmp r ri c. stackLang_Loop (stackLang_If cmp r ri c
       (stackLang_Break 0))) asm_NotTest 9 (Reg 9)
       (data_to_word_list_Seq [(\dest src. stackLang_Inst (asm_Arith
         (asm_Binop asm_Or dest src (Reg src)))) 0 9;
                  (\r1. stackLang_Inst (asm_Arith (asm_Binop
                    word_bignum_Sub r1 r1 (Imm (n2w 1))))) 9;
                  (\r1. stackLang_Inst (asm_Arith (asm_Binop
                    word_bignum_Add r1 r1 (Imm (bytes_in_word))))) 8;
                  word_gc_move_bitmaps_code conf;
                  stackLang_StackLoadAny 9 8])`;;

let word_gen_gc_move_code_def = new_definition
  `word_gen_gc_move_code conf =
     (stackLang_If asm_Test 5 (Imm ((n2w 1):'a word)) stackLang_Skip
       (data_to_word_list_Seq
         [(\dest src. stackLang_Inst (asm_Arith (asm_Binop asm_Or
           dest src (Reg src)))) 0 5;
          stackLang_Get 1 CurrHeap;
          (\r v. stackLang_Inst (asm_Arith (asm_Shift Lsr r r (Imm
            (n2w v))))) 0 (shift_length conf);
          (\r v. stackLang_Inst (asm_Arith (asm_Shift Lsl r r (Imm
            (n2w v))))) 0 (backend_common_word_shift (:'a));
          (\r1 r2. stackLang_Inst (asm_Arith (asm_Binop
            word_bignum_Add r1 r1 (Reg r2)))) 0 1;
          // here 0 is ptr_to_addr conf old w
          (\r a. stackLang_Inst (asm_Mem word_bignum_Load r (Addr a
            (n2w 0)))) 1 0;
          // here 1 is m (ptr_to_addr conf old w)
          stackLang_If asm_Test 1 (Imm (n2w 3))
            (data_to_word_list_Seq [(\r v. stackLang_Inst (asm_Arith
              (asm_Shift Lsr r r (Imm (n2w v))))) 1 2;
                       (\r v. stackLang_Inst (asm_Arith (asm_Shift
                         Lsl r r (Imm (n2w v))))) 1 (shift_length conf);
                       clear_top_inst 5 (small_shift_length conf -
                         1);
                       (\r1 r2. stackLang_Inst (asm_Arith (asm_Binop
                         asm_Or r1 r1 (Reg r2)))) 5 1])
            (data_to_word_list_Seq [
                       // put header in 6
                       (\dest src. stackLang_Inst (asm_Arith
                         (asm_Binop asm_Or dest src (Reg src)))) 6 1;
                       // get len+1w
                       (\r v. stackLang_Inst (asm_Arith (asm_Shift
                         Lsr r r (Imm (n2w v))))) 1 (dimindex (:'a) -
                         data_to_word_config_len_size conf);
                       (\r1. stackLang_Inst (asm_Arith (asm_Binop
                         word_bignum_Add r1 r1 (Imm (n2w 1))))) 1;
                       (\r w. stackLang_Inst (word_depth_Const r w))
                         2 (n2w 0b1100);
                       (\r1 r2. stackLang_Inst (asm_Arith (asm_Binop
                         asm_And r1 r1 (Reg r2)))) 6 2;
                       stackLang_If asm_Equal 6 (Imm (n2w 8))
                         (
                          // is_ref_header
                          data_to_word_list_Seq [
                           stackLang_Set (Temp (n2w 0)) 3;
                           stackLang_Set (Temp (n2w 1)) 4;
                           stackLang_Get 3 (Temp (n2w 2));
                           // ib
                           stackLang_Get 4 (Temp (n2w 3));
                           // pb
                           // store len+1w for later
                           (\dest src. stackLang_Inst (asm_Arith
                             (asm_Binop asm_Or dest src (Reg src)))) 6
                             1;
                           (\r v. stackLang_Inst (asm_Arith
                             (asm_Shift Lsl r r (Imm (n2w v))))) 1
                             (backend_common_word_shift (:'a));
                           (\r1 r2. stackLang_Inst (asm_Arith
                             (asm_Binop word_bignum_Sub r1 r1 (Reg
                             r2)))) 4 6;
                           (\r1 r2. stackLang_Inst (asm_Arith
                             (asm_Binop word_bignum_Sub r1 r1 (Reg
                             r2)))) 3 1;
                           stackLang_Set (Temp (n2w 2)) 3;
                           // new ib
                           stackLang_Set (Temp (n2w 3)) 4;
                           // new pb
                           // memcpy
                           (\dest src. stackLang_Inst (asm_Arith
                             (asm_Binop asm_Or dest src (Reg src)))) 2
                             0;
                           (\dest src. stackLang_Inst (asm_Arith
                             (asm_Binop asm_Or dest src (Reg src)))) 4
                             0;
                           (\dest src. stackLang_Inst (asm_Arith
                             (asm_Binop asm_Or dest src (Reg src)))) 0
                             6;
                           memcpy_code;
                           // compute original header_addr
                           stackLang_Get 0 (Temp (n2w 3));
                           // fixed?
                           (\r v. stackLang_Inst (asm_Arith
                             (asm_Shift Lsl r r (Imm (n2w v))))) 0 2;
                           (\r a. stackLang_Inst (asm_Mem
                             word_bignum_Store r (Addr a (n2w 0)))) 0 4;
                           // compute update_addr conf i w, where w in 5
                           stackLang_Get 1 (Temp (n2w 3));
                           clear_top_inst 5 (small_shift_length conf
                             - 1);
                           (\r v. stackLang_Inst (asm_Arith
                             (asm_Shift Lsl r r (Imm (n2w v))))) 1
                             (shift_length conf);
                           (\r1 r2. stackLang_Inst (asm_Arith
                             (asm_Binop asm_Or r1 r1 (Reg r2)))) 5 1;
                           stackLang_Get 3 (Temp (n2w 0));
                           stackLang_Get 4 (Temp (n2w 1))])
                         (data_to_word_list_Seq [
                           // store len+1w for later
                           (\dest src. stackLang_Inst (asm_Arith
                             (asm_Binop asm_Or dest src (Reg src)))) 6
                             1;
                           // memcpy
                           (\dest src. stackLang_Inst (asm_Arith
                             (asm_Binop asm_Or dest src (Reg src)))) 2
                             0;
                           (\dest src. stackLang_Inst (asm_Arith
                             (asm_Binop asm_Or dest src (Reg src)))) 0
                             1;
                           memcpy_code;
                           // compute original header_addr
                           (\dest src. stackLang_Inst (asm_Arith
                             (asm_Binop asm_Or dest src (Reg src)))) 0
                             6;
                           (\r v. stackLang_Inst (asm_Arith
                             (asm_Shift Lsl r r (Imm (n2w v))))) 0
                             (backend_common_word_shift (:'a));
                           (\r1 r2. stackLang_Inst (asm_Arith
                             (asm_Binop word_bignum_Sub r1 r1 (Reg
                             r2)))) 2 0;
                           // store i << 2 into header_addr
                           (\dest src. stackLang_Inst (asm_Arith
                             (asm_Binop asm_Or dest src (Reg src)))) 0
                             4;
                           (\r v. stackLang_Inst (asm_Arith
                             (asm_Shift Lsl r r (Imm (n2w v))))) 0 2;
                           (\r a. stackLang_Inst (asm_Mem
                             word_bignum_Store r (Addr a (n2w 0)))) 0 2;
                           // compute update_addr conf i w, where i in 4 and w in 5
                           (\dest src. stackLang_Inst (asm_Arith
                             (asm_Binop asm_Or dest src (Reg src)))) 1
                             4;
                           clear_top_inst 5 (small_shift_length conf
                             - 1);
                           (\r v. stackLang_Inst (asm_Arith
                             (asm_Shift Lsl r r (Imm (n2w v))))) 1
                             (shift_length conf);
                           (\r1 r2. stackLang_Inst (asm_Arith
                             (asm_Binop asm_Or r1 r1 (Reg r2)))) 5 1;
                           // add to i in 4
                           (\r1 r2. stackLang_Inst (asm_Arith
                             (asm_Binop word_bignum_Add r1 r1 (Reg
                             r2)))) 4 6])])]):'a stackLang_prog)`;;

let word_gen_gc_partial_move_code_def = new_definition
  `word_gen_gc_partial_move_code conf =
     // uses 0,1,2,6 as temps
     (stackLang_If asm_Test 5 (Imm ((n2w 1):'a word)) stackLang_Skip
       (data_to_word_list_Seq
         [(\dest src. stackLang_Inst (asm_Arith (asm_Binop asm_Or
           dest src (Reg src)))) 0 5;
          stackLang_Get 6 (Temp (n2w 0));
          (\r v. stackLang_Inst (asm_Arith (asm_Shift Lsr r r (Imm
            (n2w v))))) 0 (shift_length conf);
          (\r v. stackLang_Inst (asm_Arith (asm_Shift Lsl r r (Imm
            (n2w v))))) 0 (backend_common_word_shift (:'a));
          stackLang_Get 1 (Temp (n2w 1));
          stackLang_If asm_Lower 0 (Reg 6) stackLang_Skip
           (stackLang_Seq (stackLang_Get 6 (Temp (n2w 1)))
           (stackLang_If asm_NotLower 0 (Reg 1) stackLang_Skip
             (data_to_word_list_Seq [
              stackLang_Get 1 CurrHeap;
              (\r1 r2. stackLang_Inst (asm_Arith (asm_Binop
                word_bignum_Add r1 r1 (Reg r2)))) 0 1;
              // here 0 is ptr_to_addr conf old w
              (\r a. stackLang_Inst (asm_Mem word_bignum_Load r (Addr
                a (n2w 0)))) 1 0;
              // here 1 is m (ptr_to_addr conf old w)
              stackLang_If asm_Test 1 (Imm (n2w 3))
                (data_to_word_list_Seq [(\r v. stackLang_Inst
                  (asm_Arith (asm_Shift Lsr r r (Imm (n2w v))))) 1 2;
                           (\r v. stackLang_Inst (asm_Arith
                             (asm_Shift Lsl r r (Imm (n2w v))))) 1
                             (shift_length conf);
                           clear_top_inst 5 (small_shift_length conf
                             - 1);
                           (\r1 r2. stackLang_Inst (asm_Arith
                             (asm_Binop asm_Or r1 r1 (Reg r2)))) 5 1])
                (data_to_word_list_Seq [
                           // put header in 6
                           (\dest src. stackLang_Inst (asm_Arith
                             (asm_Binop asm_Or dest src (Reg src)))) 6
                             1;
                           // get len+1w
                           (\r v. stackLang_Inst (asm_Arith
                             (asm_Shift Lsr r r (Imm (n2w v))))) 1
                             (dimindex (:'a) -
                             data_to_word_config_len_size conf);
                           (\r1. stackLang_Inst (asm_Arith (asm_Binop
                             word_bignum_Add r1 r1 (Imm (n2w 1))))) 1;
                           // store len+1w for later
                           (\dest src. stackLang_Inst (asm_Arith
                             (asm_Binop asm_Or dest src (Reg src)))) 6
                             1;
                           // memcpy
                           (\dest src. stackLang_Inst (asm_Arith
                             (asm_Binop asm_Or dest src (Reg src)))) 2
                             0;
                           (\dest src. stackLang_Inst (asm_Arith
                             (asm_Binop asm_Or dest src (Reg src)))) 0
                             1;
                           memcpy_code;
                           // compute original header_addr
                           (\dest src. stackLang_Inst (asm_Arith
                             (asm_Binop asm_Or dest src (Reg src)))) 0
                             6;
                           (\r v. stackLang_Inst (asm_Arith
                             (asm_Shift Lsl r r (Imm (n2w v))))) 0
                             (backend_common_word_shift (:'a));
                           (\r1 r2. stackLang_Inst (asm_Arith
                             (asm_Binop word_bignum_Sub r1 r1 (Reg
                             r2)))) 2 0;
                           // store i << 2 into header_addr
                           (\dest src. stackLang_Inst (asm_Arith
                             (asm_Binop asm_Or dest src (Reg src)))) 0
                             4;
                           (\r v. stackLang_Inst (asm_Arith
                             (asm_Shift Lsl r r (Imm (n2w v))))) 0 2;
                           (\r a. stackLang_Inst (asm_Mem
                             word_bignum_Store r (Addr a (n2w 0)))) 0 2;
                           // compute update_addr conf i w, where i in 4 and w in 5
                           (\dest src. stackLang_Inst (asm_Arith
                             (asm_Binop asm_Or dest src (Reg src)))) 1
                             4;
                           clear_top_inst 5 (small_shift_length conf
                             - 1);
                           (\r v. stackLang_Inst (asm_Arith
                             (asm_Shift Lsl r r (Imm (n2w v))))) 1
                             (shift_length conf);
                           (\r1 r2. stackLang_Inst (asm_Arith
                             (asm_Binop asm_Or r1 r1 (Reg r2)))) 5 1;
                           // add to i in 4
                           (\r1 r2. stackLang_Inst (asm_Arith
                             (asm_Binop word_bignum_Add r1 r1 (Reg
                             r2)))) 4 6])])))]):'a stackLang_prog)`;;

let word_gen_gc_move_bitmap_code_def = new_definition
  `word_gen_gc_move_bitmap_code conf =
     (\cmp r ri c. stackLang_Loop (stackLang_If cmp r ri c
       (stackLang_Break 0))) asm_NotLower 7 (Imm (n2w 2))
      (stackLang_If asm_Test 7 (Imm (n2w 1))
         (data_to_word_list_Seq [(\r v. stackLang_Inst (asm_Arith
           (asm_Shift Lsr r r (Imm (n2w v))))) 7 1;
                    (\r1. stackLang_Inst (asm_Arith (asm_Binop
                      word_bignum_Add r1 r1 (Imm (bytes_in_word))))) 8])
         (data_to_word_list_Seq [stackLang_StackLoadAny 5 8;
                    (\r v. stackLang_Inst (asm_Arith (asm_Shift Lsr r
                      r (Imm (n2w v))))) 7 1;
                    word_gen_gc_move_code conf;
                    stackLang_StackStoreAny 5 8;
                    (\r1. stackLang_Inst (asm_Arith (asm_Binop
                      word_bignum_Add r1 r1 (Imm (bytes_in_word)))))
                      8]))`;;

let word_gen_gc_partial_move_bitmap_code_def = new_definition
  `word_gen_gc_partial_move_bitmap_code conf =
     (\cmp r ri c. stackLang_Loop (stackLang_If cmp r ri c
       (stackLang_Break 0))) asm_NotLower 7 (Imm (n2w 2))
      (stackLang_If asm_Test 7 (Imm (n2w 1))
         (data_to_word_list_Seq [(\r v. stackLang_Inst (asm_Arith
           (asm_Shift Lsr r r (Imm (n2w v))))) 7 1;
                    (\r1. stackLang_Inst (asm_Arith (asm_Binop
                      word_bignum_Add r1 r1 (Imm (bytes_in_word))))) 8])
         (data_to_word_list_Seq [stackLang_StackLoadAny 5 8;
                    (\r v. stackLang_Inst (asm_Arith (asm_Shift Lsr r
                      r (Imm (n2w v))))) 7 1;
                    word_gen_gc_partial_move_code conf;
                    stackLang_StackStoreAny 5 8;
                    (\r1. stackLang_Inst (asm_Arith (asm_Binop
                      word_bignum_Add r1 r1 (Imm (bytes_in_word)))))
                      8]))`;;

(* 9 is w, 8 is index into stack *)
let word_gen_gc_move_bitmaps_code_def = new_definition
  `((word_gen_gc_move_bitmaps_code conf):'a stackLang_prog) =
     (\cmp r ri c. stackLang_Loop (stackLang_If cmp r ri c
       (stackLang_Break 0))) asm_NotTest 0 (Reg 0)
       (data_to_word_list_Seq [stackLang_BitmapLoad 7 9;
                  word_gen_gc_move_bitmap_code conf;
                  stackLang_BitmapLoad 0 9;
                  (\r1. stackLang_Inst (asm_Arith (asm_Binop
                    word_bignum_Add r1 r1 (Imm (n2w 1))))) 9;
                  (\r v. stackLang_Inst (asm_Arith (asm_Shift Lsr
                    r r (Imm (n2w v))))) 0 (dimindex (:'a) - 1)])`;;

(* 9 is w, 8 is index into stack *)
let word_gen_gc_partial_move_bitmaps_code_def = new_definition
  `((word_gen_gc_partial_move_bitmaps_code conf):'a stackLang_prog) =
     (\cmp r ri c. stackLang_Loop (stackLang_If cmp r ri c
       (stackLang_Break 0))) asm_NotTest 0 (Reg 0)
       (data_to_word_list_Seq [stackLang_BitmapLoad 7 9;
                  word_gen_gc_partial_move_bitmap_code conf;
                  stackLang_BitmapLoad 0 9;
                  (\r1. stackLang_Inst (asm_Arith (asm_Binop
                    word_bignum_Add r1 r1 (Imm (n2w 1))))) 9;
                  (\r v. stackLang_Inst (asm_Arith (asm_Shift Lsr
                    r r (Imm (n2w v))))) 0 (dimindex (:'a) - 1)])`;;

(* 9 is w, 8 is index into stack *)
let word_gen_gc_move_roots_bitmaps_code_def = new_definition
  `((word_gen_gc_move_roots_bitmaps_code conf):'a stackLang_prog) =
     (\cmp r ri c. stackLang_Loop (stackLang_If cmp r ri c
       (stackLang_Break 0))) asm_NotTest 9 (Reg 9)
       (data_to_word_list_Seq [(\dest src. stackLang_Inst (asm_Arith
         (asm_Binop asm_Or dest src (Reg src)))) 0 9;
                  (\r1. stackLang_Inst (asm_Arith (asm_Binop
                    word_bignum_Sub r1 r1 (Imm (n2w 1))))) 9;
                  (\r1. stackLang_Inst (asm_Arith (asm_Binop
                    word_bignum_Add r1 r1 (Imm (bytes_in_word))))) 8;
                  word_gen_gc_move_bitmaps_code conf;
                  stackLang_StackLoadAny 9 8])`;;

(* 9 is w, 8 is index into stack *)
let word_gen_gc_partial_move_roots_bitmaps_code_def = new_definition
  `((word_gen_gc_partial_move_roots_bitmaps_code conf):'a
  stackLang_prog) =
     (\cmp r ri c. stackLang_Loop (stackLang_If cmp r ri c
       (stackLang_Break 0))) asm_NotTest 9 (Reg 9)
       (data_to_word_list_Seq [(\dest src. stackLang_Inst (asm_Arith
         (asm_Binop asm_Or dest src (Reg src)))) 0 9;
                  (\r1. stackLang_Inst (asm_Arith (asm_Binop
                    word_bignum_Sub r1 r1 (Imm (n2w 1))))) 9;
                  (\r1. stackLang_Inst (asm_Arith (asm_Binop
                    word_bignum_Add r1 r1 (Imm (bytes_in_word))))) 8;
                  word_gen_gc_partial_move_bitmaps_code conf;
                  stackLang_StackLoadAny 9 8])`;;

let word_gen_gc_move_list_code_def = new_definition
  `word_gen_gc_move_list_code conf =
     (\cmp r ri c. stackLang_Loop (stackLang_If cmp r ri c
       (stackLang_Break 0))) asm_NotEqual 7 (Imm ((n2w 0):'a word))
       (data_to_word_list_Seq [(\r a. stackLang_Inst (asm_Mem
         word_bignum_Load r (Addr a (n2w 0)))) 5 8;
                  (\r1. stackLang_Inst (asm_Arith (asm_Binop
                    word_bignum_Sub r1 r1 (Imm (n2w 1))))) 7;
                  word_gen_gc_move_code conf;
                  (\r a. stackLang_Inst (asm_Mem word_bignum_Store r
                    (Addr a (n2w 0)))) 5 8;
                  (\r1. stackLang_Inst (asm_Arith (asm_Binop
                    word_bignum_Add r1 r1 (Imm (bytes_in_word)))))
                    8])`;;

let word_gen_gc_partial_move_list_code_def = new_definition
  `word_gen_gc_partial_move_list_code conf =
     (\cmp r ri c. stackLang_Loop (stackLang_If cmp r ri c
       (stackLang_Break 0))) asm_NotEqual 7 (Imm ((n2w 0):'a word))
       (data_to_word_list_Seq [(\r a. stackLang_Inst (asm_Mem
         word_bignum_Load r (Addr a (n2w 0)))) 5 8;
                  (\r1. stackLang_Inst (asm_Arith (asm_Binop
                    word_bignum_Sub r1 r1 (Imm (n2w 1))))) 7;
                  word_gen_gc_partial_move_code conf;
                  (\r a. stackLang_Inst (asm_Mem word_bignum_Store r
                    (Addr a (n2w 0)))) 5 8;
                  (\r1. stackLang_Inst (asm_Arith (asm_Binop
                    word_bignum_Add r1 r1 (Imm (bytes_in_word)))))
                    8])`;;

let word_gen_gc_move_data_code_def = new_definition
  `word_gen_gc_move_data_code conf =
     ((\cmp r ri c. stackLang_Loop (stackLang_If cmp r ri c
       (stackLang_Break 0))) asm_NotEqual 3 (Reg 8)
      (data_to_word_list_Seq [(\r a. stackLang_Inst (asm_Mem
        word_bignum_Load r (Addr a (n2w 0)))) 7 8;
                 stackLang_If asm_Test 7 (Imm (n2w 4))
                   (data_to_word_list_Seq [(\r v. stackLang_Inst
                     (asm_Arith (asm_Shift Lsr r r (Imm (n2w v))))) 7
                     (dimindex (:'a) - data_to_word_config_len_size
                     conf);
                              (\r1. stackLang_Inst (asm_Arith
                                (asm_Binop word_bignum_Add r1 r1 (Imm
                                (bytes_in_word))))) 8;
                              word_gen_gc_move_list_code conf])
                   (data_to_word_list_Seq [(\r v. stackLang_Inst
                     (asm_Arith (asm_Shift Lsr r r (Imm (n2w v))))) 7
                     (dimindex (:'a) - data_to_word_config_len_size
                     conf);
                              (\r1. stackLang_Inst (asm_Arith
                                (asm_Binop word_bignum_Add r1 r1 (Imm
                                (n2w 1))))) 7;
                              (\r v. stackLang_Inst (asm_Arith
                                (asm_Shift Lsl r r (Imm (n2w v))))) 7
                                (backend_common_word_shift (:'a));
                              (\r1 r2. stackLang_Inst (asm_Arith
                                (asm_Binop word_bignum_Add r1 r1 (Reg
                                r2)))) 8 7])]):'a stackLang_prog)`;;

let word_gen_gc_partial_move_ref_list_code_def = new_definition
  `word_gen_gc_partial_move_ref_list_code conf =
     ((\cmp r ri c. stackLang_Loop (stackLang_If cmp r ri c
       (stackLang_Break 0))) asm_NotEqual 9 (Reg 8)
      (data_to_word_list_Seq [(\r a. stackLang_Inst (asm_Mem
        word_bignum_Load r (Addr a (n2w 0)))) 7 8;
                 (\r v. stackLang_Inst (asm_Arith (asm_Shift Lsr r r
                   (Imm (n2w v))))) 7 (dimindex (:'a) -
                   data_to_word_config_len_size conf);
                 (\r1. stackLang_Inst (asm_Arith (asm_Binop
                   word_bignum_Add r1 r1 (Imm (bytes_in_word))))) 8;
                 word_gen_gc_partial_move_list_code conf]):'a
                   stackLang_prog)`;;

let word_gen_gc_partial_move_data_code_def = new_definition
  `word_gen_gc_partial_move_data_code conf =
     ((\cmp r ri c. stackLang_Loop (stackLang_If cmp r ri c
       (stackLang_Break 0))) asm_NotEqual 3 (Reg 8)
      (data_to_word_list_Seq [(\r a. stackLang_Inst (asm_Mem
        word_bignum_Load r (Addr a (n2w 0)))) 7 8;
                 stackLang_If asm_Test 7 (Imm (n2w 4))
                   (data_to_word_list_Seq [(\r v. stackLang_Inst
                     (asm_Arith (asm_Shift Lsr r r (Imm (n2w v))))) 7
                     (dimindex (:'a) - data_to_word_config_len_size
                     conf);
                              (\r1. stackLang_Inst (asm_Arith
                                (asm_Binop word_bignum_Add r1 r1 (Imm
                                (bytes_in_word))))) 8;
                              word_gen_gc_partial_move_list_code
                                conf])
                   (data_to_word_list_Seq [(\r v. stackLang_Inst
                     (asm_Arith (asm_Shift Lsr r r (Imm (n2w v))))) 7
                     (dimindex (:'a) - data_to_word_config_len_size
                     conf);
                              (\r1. stackLang_Inst (asm_Arith
                                (asm_Binop word_bignum_Add r1 r1 (Imm
                                (n2w 1))))) 7;
                              (\r v. stackLang_Inst (asm_Arith
                                (asm_Shift Lsl r r (Imm (n2w v))))) 7
                                (backend_common_word_shift (:'a));
                              (\r1 r2. stackLang_Inst (asm_Arith
                                (asm_Binop word_bignum_Add r1 r1 (Reg
                                r2)))) 8 7])]):'a stackLang_prog)`;;

let word_gen_gc_move_refs_code_def = new_definition
  `word_gen_gc_move_refs_code conf =
     // r2a in 8, r1a in 0 and Temp 4w
     ((\cmp r ri c. stackLang_Loop (stackLang_If cmp r ri c
       (stackLang_Break 0))) asm_NotEqual 0 (Reg 8)
      (data_to_word_list_Seq [(\r a. stackLang_Inst (asm_Mem
        word_bignum_Load r (Addr a (n2w 0)))) 7 8;
                 (\r v. stackLang_Inst (asm_Arith (asm_Shift Lsr r r
                   (Imm (n2w v))))) 7 (dimindex (:'a) -
                   data_to_word_config_len_size conf);
                 (\r1. stackLang_Inst (asm_Arith (asm_Binop
                   word_bignum_Add r1 r1 (Imm (bytes_in_word))))) 8;
                 word_gen_gc_move_list_code conf;
                 stackLang_Get 0 (Temp (n2w 4))]):'a
                   stackLang_prog)`;;

let word_gen_gc_move_loop_code_def = new_definition
  `word_gen_gc_move_loop_code conf =
     // 7 is 0w iff pbx = pb and pax = pa, 1 is pbx (Temp 4w), 2 is pb,
     // 8 is pax, 3 is pa
     (\cmp r ri c. stackLang_Loop (stackLang_If cmp r ri c
       (stackLang_Break 0))) asm_NotTest 7 (Reg 7)
       (stackLang_If asm_Equal 1 (Reg 2)
          (
           // case: pax <> pa, i.e. move_data
           data_to_word_list_Seq [word_gen_gc_move_data_code conf;
                     stackLang_Get 5 (Temp (n2w 2));
                     stackLang_Get 7 (Temp (n2w 4));
                     (\dest src. stackLang_Inst (asm_Arith (asm_Binop
                       asm_Or dest src (Reg src)))) 1 7;
                     (\dest src. stackLang_Inst (asm_Arith (asm_Binop
                       asm_Or dest src (Reg src)))) 2 5;
                     (\r1 r2. stackLang_Inst (asm_Arith (asm_Binop
                       word_bignum_Sub r1 r1 (Reg r2)))) 7 5])
          (
           // case: pbx <> pb i.e. move_refs
           data_to_word_list_Seq [(\dest src. stackLang_Inst
             (asm_Arith (asm_Binop asm_Or dest src (Reg src)))) 0 1;
                     stackLang_Set (Temp (n2w 6)) 8;
                     (\dest src. stackLang_Inst (asm_Arith (asm_Binop
                       asm_Or dest src (Reg src)))) 8 2;
                     stackLang_Set (Temp (n2w 5)) 8;
                     word_gen_gc_move_refs_code conf;
                     (\dest src. stackLang_Inst (asm_Arith (asm_Binop
                       asm_Or dest src (Reg src)))) 7 8;
                     // pbx'
                     stackLang_Get 1 (Temp (n2w 5));
                     // pb
                     stackLang_Get 2 (Temp (n2w 5));
                     stackLang_Set (Temp (n2w 4)) 2;
                     stackLang_Get 2 (Temp (n2w 2));
                     // pb'
                     (\dest src. stackLang_Inst (asm_Arith (asm_Binop
                       asm_Or dest src (Reg src)))) 3 3;
                     // pa'
                     (\dest src. stackLang_Inst (asm_Arith (asm_Binop
                       asm_Or dest src (Reg src)))) 4 4;
                     // i'
                     (\dest src. stackLang_Inst (asm_Arith (asm_Binop
                       asm_Or dest src (Reg src)))) 7 1;
                     (\r1 r2. stackLang_Inst (asm_Arith (asm_Binop
                       word_bignum_Sub r1 r1 (Reg r2)))) 7 2;
                     // pbx' - pa'
                     stackLang_Get 8 (Temp (n2w 6));
                     // pax
                     (\dest src. stackLang_Inst (asm_Arith (asm_Binop
                       asm_Or dest src (Reg src)))) 5 8;
                     // pax - pa'
                     (\r1 r2. stackLang_Inst (asm_Arith (asm_Binop
                       word_bignum_Sub r1 r1 (Reg r2)))) 5 3;
                     (\r1 r2. stackLang_Inst (asm_Arith (asm_Binop
                       asm_Or r1 r1 (Reg r2)))) 7 5]))`;;

let word_gc_partial_or_full_def = new_definition
  `word_gc_partial_or_full gen_sizes partial_code full_code =
     (match gen_sizes with [] -> data_to_word_list_Seq (APPEND
       [stackLang_Get 8 TriggerGC; stackLang_Get 7 EndOfHeap; (\r1 r2.
       stackLang_Inst (asm_Arith (asm_Binop word_bignum_Sub r1 r1 (Reg
       r2)))) 7 8] full_code) | _1 -> data_to_word_list_Seq
              [stackLang_Get 8 TriggerGC;
               stackLang_Get 7 EndOfHeap;
               (\r1 r2. stackLang_Inst (asm_Arith (asm_Binop
                 word_bignum_Sub r1 r1 (Reg r2)))) 7 8;
               stackLang_If asm_NotLower 7 (Reg 1)
                 (data_to_word_list_Seq partial_code)
                 (data_to_word_list_Seq full_code)])`;;

let SetNewTrigger_def = new_definition
  `SetNewTrigger (endh:num) (ib:num) gs =
     data_to_word_list_Seq [(\r w. stackLang_Inst (word_depth_Const r
       w)) 1 ((get_gen_size gs):'a word);
               stackLang_Get 7 AllocSize;
               (\dest src. stackLang_Inst (asm_Arith (asm_Binop
                 asm_Or dest src (Reg src)))) 4 endh;
               (\r1 r2. stackLang_Inst (asm_Arith (asm_Binop
                 word_bignum_Sub r1 r1 (Reg r2)))) 4 ib;
               stackLang_If asm_Lower 1 (Reg 7)
                 (stackLang_If asm_Lower 4 (Reg 7)
                    (stackLang_Set TriggerGC endh)
                    (stackLang_If asm_Test 7 (Imm (if dimindex (:'a)
                      = 32 then (n2w 3) else (n2w 7)))
                      (stackLang_Seq ((\r1 r2. stackLang_Inst
                        (asm_Arith (asm_Binop word_bignum_Add r1 r1 (Reg
                        r2)))) 7 ib) (stackLang_Set TriggerGC 7))
                      (stackLang_Set TriggerGC endh)))
                 (stackLang_If asm_Lower 4 (Reg 1)
                    (stackLang_Set TriggerGC endh)
                    (stackLang_Seq ((\r1 r2. stackLang_Inst
                      (asm_Arith (asm_Binop word_bignum_Add r1 r1
                      (Reg r2)))) 1 ib) (stackLang_Set TriggerGC
                      1)))]`;;

let word_gc_code_def = new_definition
  `word_gc_code conf =
     (match data_to_word_config_gc_kind conf with data_to_word_None
       ->
         (data_to_word_list_Seq
               [stackLang_Set AllocSize 1;
                stackLang_Get 2 CurrHeap;
                stackLang_Set NextFree 2;
                stackLang_Set TriggerGC 2;
                stackLang_Set EndOfHeap 2;
                stackLang_If asm_Test 1 (Reg 1) stackLang_Skip
                  (stackLang_Seq ((\r w. stackLang_Inst
                  (word_depth_Const r w)) 1 (n2w 1)) (stackLang_Halt
                  1))]) | data_to_word_Simple ->
         (data_to_word_list_Seq
               [stackLang_Set AllocSize 1;
                stackLang_Set NextFree 0;
                (\r w. stackLang_Inst (word_depth_Const r w)) 1 (n2w
                  0);
                (\dest src. stackLang_Inst (asm_Arith (asm_Binop
                  asm_Or dest src (Reg src)))) 2 1;
                stackLang_Get 3 OtherHeap;
                (\dest src. stackLang_Inst (asm_Arith (asm_Binop
                  asm_Or dest src (Reg src)))) 4 1;
                stackLang_Get 5 Globals;
                (\dest src. stackLang_Inst (asm_Arith (asm_Binop
                  asm_Or dest src (Reg src)))) 6 1;
                (\dest src. stackLang_Inst (asm_Arith (asm_Binop
                  asm_Or dest src (Reg src)))) 8 1;
                word_gc_move_code conf;
                stackLang_Set Globals 5;
                (\dest src. stackLang_Inst (asm_Arith (asm_Binop
                  asm_Or dest src (Reg src)))) 7 5;
                (\r v. stackLang_Inst (asm_Arith (asm_Shift Lsr r r
                  (Imm (n2w v))))) 7 (shift_length conf);
                (\r v. stackLang_Inst (asm_Arith (asm_Shift Lsl r r
                  (Imm (n2w v))))) 7 (backend_common_word_shift (:'a));
                stackLang_Get 9 OtherHeap;
                (\r1 r2. stackLang_Inst (asm_Arith (asm_Binop
                  word_bignum_Add r1 r1 (Reg r2)))) 7 9;
                stackLang_Set GlobReal 7;
                (\r w. stackLang_Inst (word_depth_Const r w)) 7 (n2w
                  0);
                stackLang_StackLoadAny 9 8;
                (\dest src. stackLang_Inst (asm_Arith (asm_Binop
                  asm_Or dest src (Reg src)))) 8 7;
                word_gc_move_roots_bitmaps_code conf;
                stackLang_Get 8 OtherHeap;
                word_gc_move_loop_code conf;
                stackLang_Get 0 CurrHeap;
                stackLang_Get 1 OtherHeap;
                stackLang_Get 2 HeapLength;
                (\r1 r2. stackLang_Inst (asm_Arith (asm_Binop
                  word_bignum_Add r1 r1 (Reg r2)))) 2 1;
                stackLang_Set CurrHeap 1;
                stackLang_Set OtherHeap 0;
                stackLang_Get 0 NextFree;
                stackLang_Set NextFree 8;
                stackLang_Set EndOfHeap 2;
                stackLang_Set TriggerGC 2;
                stackLang_Get 1 AllocSize;
                (\r1 r2. stackLang_Inst (asm_Arith (asm_Binop
                  word_bignum_Sub r1 r1 (Reg r2)))) 2 8;
                stackLang_If asm_Lower 2 (Reg 1) (stackLang_Seq ((\r
                  w. stackLang_Inst (word_depth_Const r w)) 1 (n2w 1))
                  (stackLang_Halt 1)) stackLang_Skip]) |
                  data_to_word_Generational gen_sizes ->
         ((word_gc_partial_or_full gen_sizes
               [
                // gen_gc_partial
                stackLang_Set AllocSize 1;
                stackLang_Set NextFree 0;
                stackLang_Get 4 GenStart;
                stackLang_Get 5 EndOfHeap;
                stackLang_Get 2 CurrHeap;
                stackLang_Set (Temp (n2w 0)) 4;
                (\r1 r2. stackLang_Inst (asm_Arith (asm_Binop
                  word_bignum_Sub r1 r1 (Reg r2)))) 5 2;
                stackLang_Set (Temp (n2w 1)) 5;
                stackLang_Get 7 HeapLength;
                stackLang_Get 5 Globals;
                stackLang_Get 3 OtherHeap;
                (\r v. stackLang_Inst (asm_Arith (asm_Shift Lsr r r
                  (Imm (n2w v))))) 4 (backend_common_word_shift (:'a));
                (\dest src. stackLang_Inst (asm_Arith (asm_Binop
                  asm_Or dest src (Reg src)))) 6 3;
                word_gen_gc_partial_move_code conf;
                stackLang_Set Globals 5;
                (\dest src. stackLang_Inst (asm_Arith (asm_Binop
                  asm_Or dest src (Reg src)))) 8 5;
                (\r v. stackLang_Inst (asm_Arith (asm_Shift Lsr r r
                  (Imm (n2w v))))) 8 (shift_length conf);
                (\r v. stackLang_Inst (asm_Arith (asm_Shift Lsl r r
                  (Imm (n2w v))))) 8 (backend_common_word_shift (:'a));
                stackLang_Get 9 CurrHeap;
                (\r1 r2. stackLang_Inst (asm_Arith (asm_Binop
                  word_bignum_Add r1 r1 (Reg r2)))) 8 9;
                stackLang_Set GlobReal 8;
                (\r w. stackLang_Inst (word_depth_Const r w)) 8 (n2w
                  0);
                stackLang_StackLoadAny 9 8;
                word_gen_gc_partial_move_roots_bitmaps_code conf;
                stackLang_Get 8 CurrHeap;
                stackLang_Get 9 HeapLength;
                (\r1 r2. stackLang_Inst (asm_Arith (asm_Binop
                  word_bignum_Add r1 r1 (Reg r2)))) 9 8;
                stackLang_Get 8 EndOfHeap;
                word_gen_gc_partial_move_ref_list_code conf;
                stackLang_Get 8 OtherHeap;
                word_gen_gc_partial_move_data_code conf;
                stackLang_Get 2 OtherHeap;
                (\dest src. stackLang_Inst (asm_Arith (asm_Binop
                  asm_Or dest src (Reg src)))) 0 3;
                (\r1 r2. stackLang_Inst (asm_Arith (asm_Binop
                  word_bignum_Sub r1 r1 (Reg r2)))) 0 2;
                (\r v. stackLang_Inst (asm_Arith (asm_Shift Lsr r r
                  (Imm (n2w v))))) 0 (backend_common_word_shift (:'a));
                stackLang_Get 3 GenStart;
                stackLang_Get 1 CurrHeap;
                (\r1 r2. stackLang_Inst (asm_Arith (asm_Binop
                  word_bignum_Add r1 r1 (Reg r2)))) 3 1;
                memcpy_code;
                stackLang_Get 0 NextFree;
                stackLang_Set NextFree 3;
                stackLang_Get 8 EndOfHeap;
                stackLang_Get 2 TriggerGC;
                SetNewTrigger 8 3 gen_sizes;
                (\r w. stackLang_Inst (word_depth_Const r w)) 1 (n2w
                  0);
                stackLang_Set (Temp (n2w 0)) 1;
                stackLang_Set (Temp (n2w 1)) 1;
                stackLang_Get 1 AllocSize;
                (\r1 r2. stackLang_Inst (asm_Arith (asm_Binop
                  word_bignum_Sub r1 r1 (Reg r2)))) 8 3;
                stackLang_Get 7 CurrHeap;
                (\r1 r2. stackLang_Inst (asm_Arith (asm_Binop
                  word_bignum_Sub r1 r1 (Reg r2)))) 3 7;
                stackLang_Set GenStart 3]
               [
                // There is no need for a memory check here
                // because the partial collector is guaranteed
                // to get to a state where there is enough
                // memory for the allocation. In contrast,
                // the full collector below can hit a state
                // where there is not enough memory, and so it
                // can Halt execution.
                // gen_gc_full
                stackLang_Set AllocSize 1;
                stackLang_Set NextFree 0;
                (\r w. stackLang_Inst (word_depth_Const r w)) 1 ((n2w
                  0):'a word);
                (\dest src. stackLang_Inst (asm_Arith (asm_Binop
                  asm_Or dest src (Reg src)))) 2 1;
                stackLang_Get 3 OtherHeap;
                stackLang_Get 4 HeapLength;
                (\r1 r2. stackLang_Inst (asm_Arith (asm_Binop
                  word_bignum_Add r1 r1 (Reg r2)))) 4 3;
                stackLang_Set (Temp (n2w 0)) 4;
                stackLang_Set (Temp (n2w 1)) 4;
                stackLang_Set (Temp (n2w 2)) 4;
                stackLang_Set (Temp (n2w 4)) 4;
                stackLang_Set (Temp (n2w 5)) 4;
                stackLang_Set (Temp (n2w 6)) 4;
                stackLang_Get 4 HeapLength;
                (\r v. stackLang_Inst (asm_Arith (asm_Shift Lsr r r
                  (Imm (n2w v))))) 4 (backend_common_word_shift (:'a));
                stackLang_Set (Temp (n2w 3)) 4;
                (\dest src. stackLang_Inst (asm_Arith (asm_Binop
                  asm_Or dest src (Reg src)))) 4 1;
                stackLang_Get 5 Globals;
                (\dest src. stackLang_Inst (asm_Arith (asm_Binop
                  asm_Or dest src (Reg src)))) 6 1;
                (\dest src. stackLang_Inst (asm_Arith (asm_Binop
                  asm_Or dest src (Reg src)))) 8 1;
                word_gen_gc_move_code conf;
                stackLang_Set Globals 5;
                (\dest src. stackLang_Inst (asm_Arith (asm_Binop
                  asm_Or dest src (Reg src)))) 7 5;
                stackLang_Get 9 OtherHeap;
                (\r v. stackLang_Inst (asm_Arith (asm_Shift Lsr r r
                  (Imm (n2w v))))) 7 (shift_length conf);
                (\r v. stackLang_Inst (asm_Arith (asm_Shift Lsl r r
                  (Imm (n2w v))))) 7 (backend_common_word_shift (:'a));
                (\r1 r2. stackLang_Inst (asm_Arith (asm_Binop
                  word_bignum_Add r1 r1 (Reg r2)))) 7 9;
                stackLang_Set GlobReal 7;
                (\r w. stackLang_Inst (word_depth_Const r w)) 7 (n2w
                  0);
                stackLang_StackLoadAny 9 8;
                (\dest src. stackLang_Inst (asm_Arith (asm_Binop
                  asm_Or dest src (Reg src)))) 8 7;
                word_gen_gc_move_roots_bitmaps_code conf;
                stackLang_Get 2 (Temp (n2w 2));
                stackLang_Get 8 OtherHeap;
                (\dest src. stackLang_Inst (asm_Arith (asm_Binop
                  asm_Or dest src (Reg src)))) 7 3;
                (\r1 r2. stackLang_Inst (asm_Arith (asm_Binop
                  word_bignum_Sub r1 r1 (Reg r2)))) 7 8;
                stackLang_Get 1 (Temp (n2w 6));
                (\dest src. stackLang_Inst (asm_Arith (asm_Binop
                  asm_Or dest src (Reg src)))) 6 2;
                (\r1 r2. stackLang_Inst (asm_Arith (asm_Binop
                  word_bignum_Sub r1 r1 (Reg r2)))) 6 1;
                (\r1 r2. stackLang_Inst (asm_Arith (asm_Binop asm_Or
                  r1 r1 (Reg r2)))) 7 6;
                word_gen_gc_move_loop_code conf;
                stackLang_Get 0 CurrHeap;
                stackLang_Get 1 OtherHeap;
                stackLang_Get 2 (Temp (n2w 2));
                stackLang_Set CurrHeap 1;
                stackLang_Set OtherHeap 0;
                stackLang_Get 0 NextFree;
                stackLang_Set NextFree 3;
                stackLang_Set EndOfHeap 2;
                (\dest src. stackLang_Inst (asm_Arith (asm_Binop
                  asm_Or dest src (Reg src)))) 8 3;
                (\r1 r2. stackLang_Inst (asm_Arith (asm_Binop
                  word_bignum_Sub r1 r1 (Reg r2)))) 8 1;
                stackLang_Set GenStart 8;
                SetNewTrigger 2 3 gen_sizes;
                (\r w. stackLang_Inst (word_depth_Const r w)) 1 (n2w
                  0);
                stackLang_Set (Temp (n2w 0)) 1;
                stackLang_Set (Temp (n2w 1)) 1;
                stackLang_Set (Temp (n2w 2)) 1;
                stackLang_Set (Temp (n2w 3)) 1;
                stackLang_Set (Temp (n2w 4)) 1;
                stackLang_Set (Temp (n2w 5)) 1;
                stackLang_Set (Temp (n2w 6)) 1;
                stackLang_Get 1 AllocSize;
                stackLang_Get 2 TriggerGC;
                (\r1 r2. stackLang_Inst (asm_Arith (asm_Binop
                  word_bignum_Sub r1 r1 (Reg r2)))) 2 3;
                stackLang_If asm_Lower 2 (Reg 1) (stackLang_Seq
                  ((\r w. stackLang_Inst (word_depth_Const r w)) 1
                  (n2w 1)) (stackLang_Halt 1)) stackLang_Skip]):'a
                  stackLang_prog))`;;

let stack_alloc_stubs_def = new_definition
  `stack_alloc_stubs conf = [(gc_stub_location,stackLang_Seq
  (word_gc_code conf) (stackLang_Return 0))]`;;

let stack_alloc_stub_names_def = new_definition
  `stack_alloc_stub_names one = [(gc_stub_location,(implode "_GC"))]`;;

(* compiler *)

let _ = size_thms "stackLang_prog";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let next_lab_def,next_lab_ind = define_wf
  `MEASURE (\(x0,x1). stackLang_prog_size (\x. 0) x0)`
  [`next_lab (p:'a stackLang_prog) aux =
     (match p with stackLang_Seq p1 p2 -> next_lab p1 (next_lab p2
       aux) | stackLang_If _2 _3 _4 p1 p2 -> next_lab p1 (next_lab p2
       aux) | stackLang_Loop p -> next_lab p aux | stackLang_Call NONE
       _5 NONE -> aux | stackLang_Call NONE _6 (SOME (_7,_8,l2)) -> MAX
       aux (l2 + 2) | stackLang_Call (SOME (p,_9,_10,l2)) _11 NONE ->
       next_lab p (MAX aux (l2 + 2)) | stackLang_Call (SOME
       (p,_12,_13,l2)) _14 (SOME (p',_15,l3)) ->
           next_lab p (next_lab p' ((MAX (MAX l2 l3 + 2) aux)))
             | _16 -> aux)`];;

(* HOL4 stack_allocScript.sml:664-674: a theorem that HOL4 states as
   the value of an ML expression: next_lab_pmatch *)

(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let stack_alloc_comp_def,stack_alloc_comp_ind = define_guess_cheat
  [`stack_alloc_comp n m p =
     (match p with stackLang_Seq p1 p2 ->
         (let (q1,m) = stack_alloc_comp n m p1 in
         let (q2,m) = stack_alloc_comp n m p2 in
           (stackLang_Seq q1 q2,m)) | stackLang_If c r ri p1 p2 ->
         (let (q1,m) = stack_alloc_comp n m p1 in
         let (q2,m) = stack_alloc_comp n m p2 in
           (stackLang_If c r ri q1 q2,m)) | stackLang_Loop p1 ->
         (let (q1,m) = stack_alloc_comp n m p1 in
           (stackLang_Loop q1,m)) | stackLang_Call NONE dest exc ->
             (stackLang_Call NONE dest NONE,m) | stackLang_Call (SOME
             (p1,lr,l1,l2)) dest exc ->
         (let (q1,m) = stack_alloc_comp n m p1 in
          (match exc with NONE -> (stackLang_Call (SOME
            (q1,lr,l1,l2)) dest NONE,m) | SOME (p2,k1,k2) ->
               (let (q2,m) = stack_alloc_comp n m p2 in
                 (stackLang_Call (SOME (q1,lr,l1,l2)) dest (SOME
                   (q2,k1,k2)),m)))) | stackLang_Alloc k ->
                   (stackLang_Call (SOME (stackLang_Skip,0,n,m))
                   (INL gc_stub_location) NONE,m + 1) |
                   stackLang_StoreConsts k1 k2 (SOME loc) ->
                   (stackLang_Call (SOME (stackLang_Skip,0,n,m))
                   (INL loc) NONE,m + 1) | _17 -> (p,m))`];;

(* HOL4 stack_allocScript.sml:705-714: a theorem that HOL4 states as
   the value of an ML expression: comp_pmatch *)

let prog_comp_def = new_definition
  `stack_alloc_prog_comp (n,p) = (n,FST (stack_alloc_comp n (next_lab
  p 2) p))`;;

let stack_alloc_compile_def = new_definition
  `stack_alloc_compile c prog = APPEND (stack_alloc_stubs c) (MAP
  stack_alloc_prog_comp prog)`;;

(* and the overloads that this file cannot see are back in the
   interface *)
let _ = unhide_overloads ();;
