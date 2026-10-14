(* ======================================================== *)
(*  stack_alloc: ported from HOL4's
    compiler/backend/stack_allocScript.sml  *)
(* ======================================================== *)

(*
  This compiler phase introduces the implementation of the memory
  allocator and its garbage collector. It traverses the given code and
  replaces all calls to Alloc by calls to code that it inserts into
  the compiled program. the inserted code is a stackLang
  implementation of the garbage collector.
*)

needs "compiler/backend/data_to_word.ml";;
needs "compiler/backend/stackLang.ml";;

let memcpy_code_def = cake_define
  `memcpy_code =
     (\cmp r ri c. word_bignum_Loop (word_bignum_If cmp r ri c
       (wordLang_Break 0))) asm_NotEqual 0 (Imm (n2w 0))
       (data_to_word_list_Seq [(\r a. wordLang_Inst (asm_Mem
         word_bignum_Load r (Addr a (n2w 0)))) 1 2;
                  (\r1. wordLang_Inst (asm_Arith (asm_Binop
                    word_bignum_Add r1 r1 (Imm (bytes_in_word))))) 2;
                  (\r1. wordLang_Inst (asm_Arith (asm_Binop
                    word_bignum_Sub r1 r1 (Imm (n2w 1))))) 0;
                  (\r a. wordLang_Inst (asm_Mem word_bignum_Store r
                    (Addr a (n2w 0)))) 1 3;
                  (\r1. wordLang_Inst (asm_Arith (asm_Binop
                    word_bignum_Add r1 r1 (Imm (bytes_in_word)))))
                    3])`;;

let clear_top_inst_def = cake_define
  `clear_top_inst i n =
     (linear_scan_Seq ((\r semanticPrimitives_v. wordLang_Inst
       (asm_Arith (wordLang_Shift Lsl r r (Imm (n2w
       semanticPrimitives_v))))) i (dimindex (:'a) - n - 1))
         ((\r semanticPrimitives_v. wordLang_Inst (asm_Arith
           (wordLang_Shift Lsr r r (Imm (n2w
           semanticPrimitives_v))))) i (dimindex (:'a) - n - 1)):'a
           stackLang_prog)`;;

let word_gc_move_code_def = cake_define
  `word_gc_move_code conf =
     word_bignum_If asm_Test 5 (Imm ((n2w 1):'a word))
       word_bignum_Skip
       (data_to_word_list_Seq
         [(\dest src. wordLang_Inst (asm_Arith (asm_Binop asm_Or dest
           src (Reg src)))) 0 5;
          wordLang_Get 1 CurrHeap;
          (\r semanticPrimitives_v. wordLang_Inst (asm_Arith
            (wordLang_Shift Lsr r r (Imm (n2w semanticPrimitives_v)))))
            0 (shift_length conf);
          (\r semanticPrimitives_v. wordLang_Inst (asm_Arith
            (wordLang_Shift Lsl r r (Imm (n2w semanticPrimitives_v)))))
            0 (backend_common_word_shift (:'a));
          (\r1 r2. wordLang_Inst (asm_Arith (asm_Binop
            word_bignum_Add r1 r1 (Reg r2)))) 0 1;
          (\r a. wordLang_Inst (asm_Mem word_bignum_Load r (Addr a
            (n2w 0)))) 1 0;
          word_bignum_If asm_Test 1 (Imm (n2w 3))
            (data_to_word_list_Seq [(\r semanticPrimitives_v.
              wordLang_Inst (asm_Arith (wordLang_Shift Lsr r r (Imm (n2w
              semanticPrimitives_v))))) 1 2;
                       (\r semanticPrimitives_v. wordLang_Inst
                         (asm_Arith (wordLang_Shift Lsl r r (Imm (n2w
                         semanticPrimitives_v))))) 1 (shift_length
                         conf);
                       clear_top_inst 5 (small_shift_length conf -
                         1);
                       (\r1 r2. wordLang_Inst (asm_Arith (asm_Binop
                         asm_Or r1 r1 (Reg r2)))) 5 1])
            (data_to_word_list_Seq [
                       (\r semanticPrimitives_v. wordLang_Inst
                         (asm_Arith (wordLang_Shift Lsr r r (Imm (n2w
                         semanticPrimitives_v))))) 1 (dimindex (:'a) -
                         data_to_word_config_len_size conf);
                       (\r1. wordLang_Inst (asm_Arith (asm_Binop
                         word_bignum_Add r1 r1 (Imm (n2w 1))))) 1;
                       (\dest src. wordLang_Inst (asm_Arith
                         (asm_Binop asm_Or dest src (Reg src)))) 6 1;
                       (\dest src. wordLang_Inst (asm_Arith
                         (asm_Binop asm_Or dest src (Reg src)))) 2 0;
                       (\dest src. wordLang_Inst (asm_Arith
                         (asm_Binop asm_Or dest src (Reg src)))) 0 1;
                       memcpy_code;
                       (\dest src. wordLang_Inst (asm_Arith
                         (asm_Binop asm_Or dest src (Reg src)))) 0 6;
                       (\r semanticPrimitives_v. wordLang_Inst
                         (asm_Arith (wordLang_Shift Lsl r r (Imm (n2w
                         semanticPrimitives_v))))) 0
                         (backend_common_word_shift (:'a));
                       (\r1 r2. wordLang_Inst (asm_Arith (asm_Binop
                         word_bignum_Sub r1 r1 (Reg r2)))) 2 0;
                       (\dest src. wordLang_Inst (asm_Arith
                         (asm_Binop asm_Or dest src (Reg src)))) 0 4;
                       (\r semanticPrimitives_v. wordLang_Inst
                         (asm_Arith (wordLang_Shift Lsl r r (Imm (n2w
                         semanticPrimitives_v))))) 0 2;
                       (\r a. wordLang_Inst (asm_Mem
                         word_bignum_Store r (Addr a (n2w 0)))) 0 2;
                       (\dest src. wordLang_Inst (asm_Arith
                         (asm_Binop asm_Or dest src (Reg src)))) 1 4;
                       clear_top_inst 5 (small_shift_length conf -
                         1);
                       (\r semanticPrimitives_v. wordLang_Inst
                         (asm_Arith (wordLang_Shift Lsl r r (Imm (n2w
                         semanticPrimitives_v))))) 1 (shift_length
                         conf);
                       (\r1 r2. wordLang_Inst (asm_Arith (asm_Binop
                         asm_Or r1 r1 (Reg r2)))) 5 1;
                       (\r1 r2. wordLang_Inst (asm_Arith
                         (asm_Binop word_bignum_Add r1 r1 (Reg r2))))
                         4 6])])`;;

let word_gc_move_list_code_def = cake_define
  `word_gc_move_list_code conf =
     (\cmp r ri c. word_bignum_Loop (word_bignum_If cmp r ri c
       (wordLang_Break 0))) asm_NotEqual 7 (Imm ((n2w 0):'a word))
       (data_to_word_list_Seq [(\r a. wordLang_Inst (asm_Mem
         word_bignum_Load r (Addr a (n2w 0)))) 5 8;
                  (\r1. wordLang_Inst (asm_Arith (asm_Binop
                    word_bignum_Sub r1 r1 (Imm (n2w 1))))) 7;
                  word_gc_move_code conf;
                  (\r a. wordLang_Inst (asm_Mem word_bignum_Store r
                    (Addr a (n2w 0)))) 5 8;
                  (\r1. wordLang_Inst (asm_Arith (asm_Binop
                    word_bignum_Add r1 r1 (Imm (bytes_in_word)))))
                    8])`;;

let word_gc_move_loop_code_def = cake_define
  `word_gc_move_loop_code conf =
     ((\cmp r ri c. word_bignum_Loop (word_bignum_If cmp r ri c
       (wordLang_Break 0))) asm_NotEqual 3 (Reg 8)
      (data_to_word_list_Seq [(\r a. wordLang_Inst (asm_Mem
        word_bignum_Load r (Addr a (n2w 0)))) 7 8;
                 word_bignum_If asm_Test 7 (Imm (n2w 4))
                   (data_to_word_list_Seq [(\r semanticPrimitives_v.
                     wordLang_Inst (asm_Arith (wordLang_Shift Lsr r r
                     (Imm (n2w semanticPrimitives_v))))) 7 (dimindex
                     (:'ga) - data_to_word_config_len_size conf);
                              (\r1. wordLang_Inst (asm_Arith
                                (asm_Binop word_bignum_Add r1 r1 (Imm
                                (bytes_in_word))))) 8;
                              word_gc_move_list_code conf])
                   (data_to_word_list_Seq [(\r semanticPrimitives_v.
                     wordLang_Inst (asm_Arith (wordLang_Shift Lsr r r
                     (Imm (n2w semanticPrimitives_v))))) 7 (dimindex
                     (:'ga) - data_to_word_config_len_size conf);
                              (\r1. wordLang_Inst (asm_Arith
                                (asm_Binop word_bignum_Add r1 r1 (Imm
                                (n2w 1))))) 7;
                              (\r semanticPrimitives_v. wordLang_Inst
                                (asm_Arith (wordLang_Shift Lsl r r (Imm
                                (n2w semanticPrimitives_v))))) 7
                                (backend_common_word_shift (:'a));
                              (\r1 r2. wordLang_Inst (asm_Arith
                                (asm_Binop word_bignum_Add r1 r1 (Reg
                                r2)))) 8 7])]):'a stackLang_prog)`;;

(* 7 is w, 8 is index into stack, 5 is input to word_gc_move_code *)
let word_gc_move_bitmap_code_def = cake_define
  `word_gc_move_bitmap_code conf =
     (\cmp r ri c. word_bignum_Loop (word_bignum_If cmp r ri c
       (wordLang_Break 0))) asm_NotLower 7 (Imm (n2w 2))
      (word_bignum_If asm_Test 7 (Imm (n2w 1))
         (data_to_word_list_Seq [(\r semanticPrimitives_v.
           wordLang_Inst (asm_Arith (wordLang_Shift Lsr r r (Imm (n2w
           semanticPrimitives_v))))) 7 1;
                    (\r1. wordLang_Inst (asm_Arith (asm_Binop
                      word_bignum_Add r1 r1 (Imm (bytes_in_word))))) 8])
         (data_to_word_list_Seq [stackLang_StackLoadAny 5 8;
                    (\r semanticPrimitives_v. wordLang_Inst
                      (asm_Arith (wordLang_Shift Lsr r r (Imm (n2w
                      semanticPrimitives_v))))) 7 1;
                    word_gc_move_code conf;
                    stackLang_StackStoreAny 5 8;
                    (\r1. wordLang_Inst (asm_Arith (asm_Binop
                      word_bignum_Add r1 r1 (Imm (bytes_in_word)))))
                      8]))`;;

(* 9 is w, 8 is index into stack *)
let word_gc_move_bitmaps_code_def = cake_define
  `((word_gc_move_bitmaps_code conf):'a stackLang_prog) =
     (\cmp r ri c. word_bignum_Loop (word_bignum_If cmp r ri c
       (wordLang_Break 0))) asm_NotTest 0 (Reg 0)
       (data_to_word_list_Seq [stackLang_BitmapLoad 7 9;
                  word_gc_move_bitmap_code conf;
                  stackLang_BitmapLoad 0 9;
                  (\r1. wordLang_Inst (asm_Arith (asm_Binop
                    word_bignum_Add r1 r1 (Imm (n2w 1))))) 9;
                  (\r semanticPrimitives_v. wordLang_Inst
                    (asm_Arith (wordLang_Shift Lsr r r (Imm (n2w
                    semanticPrimitives_v))))) 0 (dimindex (:'a) -
                    1)])`;;

(* 9 is w, 8 is index into stack *)
let word_gc_move_roots_bitmaps_code_def = cake_define
  `((word_gc_move_roots_bitmaps_code conf):'a stackLang_prog) =
     (\cmp r ri c. word_bignum_Loop (word_bignum_If cmp r ri c
       (wordLang_Break 0))) asm_NotTest 9 (Reg 9)
       (data_to_word_list_Seq [(\dest src. wordLang_Inst (asm_Arith
         (asm_Binop asm_Or dest src (Reg src)))) 0 9;
                  (\r1. wordLang_Inst (asm_Arith (asm_Binop
                    word_bignum_Sub r1 r1 (Imm (n2w 1))))) 9;
                  (\r1. wordLang_Inst (asm_Arith (asm_Binop
                    word_bignum_Add r1 r1 (Imm (bytes_in_word))))) 8;
                  word_gc_move_bitmaps_code conf;
                  stackLang_StackLoadAny 9 8])`;;

let word_gen_gc_move_code_def = cake_define
  `word_gen_gc_move_code conf =
     (word_bignum_If asm_Test 5 (Imm ((n2w 1):'a word))
       word_bignum_Skip
       (data_to_word_list_Seq
         [(\dest src. wordLang_Inst (asm_Arith (asm_Binop asm_Or dest
           src (Reg src)))) 0 5;
          wordLang_Get 1 CurrHeap;
          (\r semanticPrimitives_v. wordLang_Inst (asm_Arith
            (wordLang_Shift Lsr r r (Imm (n2w semanticPrimitives_v)))))
            0 (shift_length conf);
          (\r semanticPrimitives_v. wordLang_Inst (asm_Arith
            (wordLang_Shift Lsl r r (Imm (n2w semanticPrimitives_v)))))
            0 (backend_common_word_shift (:'a));
          (\r1 r2. wordLang_Inst (asm_Arith (asm_Binop
            word_bignum_Add r1 r1 (Reg r2)))) 0 1;
          (\r a. wordLang_Inst (asm_Mem word_bignum_Load r (Addr a
            (n2w 0)))) 1 0;
          word_bignum_If asm_Test 1 (Imm (n2w 3))
            (data_to_word_list_Seq [(\r semanticPrimitives_v.
              wordLang_Inst (asm_Arith (wordLang_Shift Lsr r r (Imm (n2w
              semanticPrimitives_v))))) 1 2;
                       (\r semanticPrimitives_v. wordLang_Inst
                         (asm_Arith (wordLang_Shift Lsl r r (Imm (n2w
                         semanticPrimitives_v))))) 1 (shift_length
                         conf);
                       clear_top_inst 5 (small_shift_length conf -
                         1);
                       (\r1 r2. wordLang_Inst (asm_Arith (asm_Binop
                         asm_Or r1 r1 (Reg r2)))) 5 1])
            (data_to_word_list_Seq [
                       (\dest src. wordLang_Inst (asm_Arith
                         (asm_Binop asm_Or dest src (Reg src)))) 6 1;
                       (\r semanticPrimitives_v. wordLang_Inst
                         (asm_Arith (wordLang_Shift Lsr r r (Imm (n2w
                         semanticPrimitives_v))))) 1 (dimindex (:'a) -
                         data_to_word_config_len_size conf);
                       (\r1. wordLang_Inst (asm_Arith (asm_Binop
                         word_bignum_Add r1 r1 (Imm (n2w 1))))) 1;
                       (\r w. wordLang_Inst (word_depth_Const r w)) 2
                         (n2w 0b1100);
                       (\r1 r2. wordLang_Inst (asm_Arith (asm_Binop
                         asm_And r1 r1 (Reg r2)))) 6 2;
                       word_bignum_If (EQUAL) 6 (Imm (n2w 8))
                         (data_to_word_list_Seq [
                           reg_alloc_Set (Temp (n2w 0)) 3;
                           reg_alloc_Set (Temp (n2w 1)) 4;
                           wordLang_Get 3 (Temp (n2w 2));
                           wordLang_Get 4 (Temp (n2w 3));
                           (\dest src. wordLang_Inst (asm_Arith
                             (asm_Binop asm_Or dest src (Reg src)))) 6
                             1;
                           (\r semanticPrimitives_v. wordLang_Inst
                             (asm_Arith (wordLang_Shift Lsl r r (Imm
                             (n2w semanticPrimitives_v))))) 1
                             (backend_common_word_shift (:'a));
                           (\r1 r2. wordLang_Inst (asm_Arith
                             (asm_Binop word_bignum_Sub r1 r1 (Reg
                             r2)))) 4 6;
                           (\r1 r2. wordLang_Inst (asm_Arith
                             (asm_Binop word_bignum_Sub r1 r1 (Reg
                             r2)))) 3 1;
                           reg_alloc_Set (Temp (n2w 2)) 3;
                           reg_alloc_Set (Temp (n2w 3)) 4;
                           (\dest src. wordLang_Inst (asm_Arith
                             (asm_Binop asm_Or dest src (Reg src)))) 2
                             0;
                           (\dest src. wordLang_Inst (asm_Arith
                             (asm_Binop asm_Or dest src (Reg src)))) 4
                             0;
                           (\dest src. wordLang_Inst (asm_Arith
                             (asm_Binop asm_Or dest src (Reg src)))) 0
                             6;
                           memcpy_code;
                           wordLang_Get 0 (Temp (n2w 3));
                           (\r semanticPrimitives_v. wordLang_Inst
                             (asm_Arith (wordLang_Shift Lsl r r (Imm
                             (n2w semanticPrimitives_v))))) 0 2;
                           (\r a. wordLang_Inst (asm_Mem
                             word_bignum_Store r (Addr a (n2w 0)))) 0 4;
                           wordLang_Get 1 (Temp (n2w 3));
                           clear_top_inst 5 (small_shift_length conf
                             - 1);
                           (\r semanticPrimitives_v. wordLang_Inst
                             (asm_Arith (wordLang_Shift Lsl r r (Imm
                             (n2w semanticPrimitives_v))))) 1
                             (shift_length conf);
                           (\r1 r2. wordLang_Inst (asm_Arith
                             (asm_Binop asm_Or r1 r1 (Reg r2)))) 5 1;
                           wordLang_Get 3 (Temp (n2w 0));
                           wordLang_Get 4 (Temp (n2w 1))])
                         (data_to_word_list_Seq [
                           (\dest src. wordLang_Inst (asm_Arith
                             (asm_Binop asm_Or dest src (Reg src)))) 6
                             1;
                           (\dest src. wordLang_Inst (asm_Arith
                             (asm_Binop asm_Or dest src (Reg src)))) 2
                             0;
                           (\dest src. wordLang_Inst (asm_Arith
                             (asm_Binop asm_Or dest src (Reg src)))) 0
                             1;
                           memcpy_code;
                           (\dest src. wordLang_Inst (asm_Arith
                             (asm_Binop asm_Or dest src (Reg src)))) 0
                             6;
                           (\r semanticPrimitives_v. wordLang_Inst
                             (asm_Arith (wordLang_Shift Lsl r r (Imm
                             (n2w semanticPrimitives_v))))) 0
                             (backend_common_word_shift (:'a));
                           (\r1 r2. wordLang_Inst (asm_Arith
                             (asm_Binop word_bignum_Sub r1 r1 (Reg
                             r2)))) 2 0;
                           (\dest src. wordLang_Inst (asm_Arith
                             (asm_Binop asm_Or dest src (Reg src)))) 0
                             4;
                           (\r semanticPrimitives_v. wordLang_Inst
                             (asm_Arith (wordLang_Shift Lsl r r (Imm
                             (n2w semanticPrimitives_v))))) 0 2;
                           (\r a. wordLang_Inst (asm_Mem
                             word_bignum_Store r (Addr a (n2w 0)))) 0 2;
                           (\dest src. wordLang_Inst (asm_Arith
                             (asm_Binop asm_Or dest src (Reg src)))) 1
                             4;
                           clear_top_inst 5 (small_shift_length conf
                             - 1);
                           (\r semanticPrimitives_v. wordLang_Inst
                             (asm_Arith (wordLang_Shift Lsl r r (Imm
                             (n2w semanticPrimitives_v))))) 1
                             (shift_length conf);
                           (\r1 r2. wordLang_Inst (asm_Arith
                             (asm_Binop asm_Or r1 r1 (Reg r2)))) 5 1;
                           (\r1 r2. wordLang_Inst (asm_Arith
                             (asm_Binop word_bignum_Add r1 r1 (Reg
                             r2)))) 4 6])])]):'a stackLang_prog)`;;

let word_gen_gc_partial_move_code_def = cake_define
  `word_gen_gc_partial_move_code conf =
     (word_bignum_If asm_Test 5 (Imm ((n2w 1):'a word))
       word_bignum_Skip
       (data_to_word_list_Seq
         [(\dest src. wordLang_Inst (asm_Arith (asm_Binop asm_Or dest
           src (Reg src)))) 0 5;
          wordLang_Get 6 (Temp (n2w 0));
          (\r semanticPrimitives_v. wordLang_Inst (asm_Arith
            (wordLang_Shift Lsr r r (Imm (n2w semanticPrimitives_v)))))
            0 (shift_length conf);
          (\r semanticPrimitives_v. wordLang_Inst (asm_Arith
            (wordLang_Shift Lsl r r (Imm (n2w semanticPrimitives_v)))))
            0 (backend_common_word_shift (:'a));
          wordLang_Get 1 (Temp (n2w 1));
          word_bignum_If asm_Lower 0 (Reg 6) word_bignum_Skip
           (linear_scan_Seq (wordLang_Get 6 (Temp (n2w 1)))
           (word_bignum_If asm_NotLower 0 (Reg 1) word_bignum_Skip
             (data_to_word_list_Seq [
              wordLang_Get 1 CurrHeap;
              (\r1 r2. wordLang_Inst (asm_Arith (asm_Binop
                word_bignum_Add r1 r1 (Reg r2)))) 0 1;
              (\r a. wordLang_Inst (asm_Mem word_bignum_Load r (Addr
                a (n2w 0)))) 1 0;
              word_bignum_If asm_Test 1 (Imm (n2w 3))
                (data_to_word_list_Seq [(\r semanticPrimitives_v.
                  wordLang_Inst (asm_Arith (wordLang_Shift Lsr r r (Imm
                  (n2w semanticPrimitives_v))))) 1 2;
                           (\r semanticPrimitives_v. wordLang_Inst
                             (asm_Arith (wordLang_Shift Lsl r r (Imm
                             (n2w semanticPrimitives_v))))) 1
                             (shift_length conf);
                           clear_top_inst 5 (small_shift_length conf
                             - 1);
                           (\r1 r2. wordLang_Inst (asm_Arith
                             (asm_Binop asm_Or r1 r1 (Reg r2)))) 5 1])
                (data_to_word_list_Seq [
                           (\dest src. wordLang_Inst (asm_Arith
                             (asm_Binop asm_Or dest src (Reg src)))) 6
                             1;
                           (\r semanticPrimitives_v. wordLang_Inst
                             (asm_Arith (wordLang_Shift Lsr r r (Imm
                             (n2w semanticPrimitives_v))))) 1 (dimindex
                             (:'a) - data_to_word_config_len_size conf);
                           (\r1. wordLang_Inst (asm_Arith (asm_Binop
                             word_bignum_Add r1 r1 (Imm (n2w 1))))) 1;
                           (\dest src. wordLang_Inst (asm_Arith
                             (asm_Binop asm_Or dest src (Reg src)))) 6
                             1;
                           (\dest src. wordLang_Inst (asm_Arith
                             (asm_Binop asm_Or dest src (Reg src)))) 2
                             0;
                           (\dest src. wordLang_Inst (asm_Arith
                             (asm_Binop asm_Or dest src (Reg src)))) 0
                             1;
                           memcpy_code;
                           (\dest src. wordLang_Inst (asm_Arith
                             (asm_Binop asm_Or dest src (Reg src)))) 0
                             6;
                           (\r semanticPrimitives_v. wordLang_Inst
                             (asm_Arith (wordLang_Shift Lsl r r (Imm
                             (n2w semanticPrimitives_v))))) 0
                             (backend_common_word_shift (:'a));
                           (\r1 r2. wordLang_Inst (asm_Arith
                             (asm_Binop word_bignum_Sub r1 r1 (Reg
                             r2)))) 2 0;
                           (\dest src. wordLang_Inst (asm_Arith
                             (asm_Binop asm_Or dest src (Reg src)))) 0
                             4;
                           (\r semanticPrimitives_v. wordLang_Inst
                             (asm_Arith (wordLang_Shift Lsl r r (Imm
                             (n2w semanticPrimitives_v))))) 0 2;
                           (\r a. wordLang_Inst (asm_Mem
                             word_bignum_Store r (Addr a (n2w 0)))) 0 2;
                           (\dest src. wordLang_Inst (asm_Arith
                             (asm_Binop asm_Or dest src (Reg src)))) 1
                             4;
                           clear_top_inst 5 (small_shift_length conf
                             - 1);
                           (\r semanticPrimitives_v. wordLang_Inst
                             (asm_Arith (wordLang_Shift Lsl r r (Imm
                             (n2w semanticPrimitives_v))))) 1
                             (shift_length conf);
                           (\r1 r2. wordLang_Inst (asm_Arith
                             (asm_Binop asm_Or r1 r1 (Reg r2)))) 5 1;
                           (\r1 r2. wordLang_Inst (asm_Arith
                             (asm_Binop word_bignum_Add r1 r1 (Reg
                             r2)))) 4 6])])))]):'a stackLang_prog)`;;

let word_gen_gc_move_bitmap_code_def = cake_define
  `word_gen_gc_move_bitmap_code conf =
     (\cmp r ri c. word_bignum_Loop (word_bignum_If cmp r ri c
       (wordLang_Break 0))) asm_NotLower 7 (Imm (n2w 2))
      (word_bignum_If asm_Test 7 (Imm (n2w 1))
         (data_to_word_list_Seq [(\r semanticPrimitives_v.
           wordLang_Inst (asm_Arith (wordLang_Shift Lsr r r (Imm (n2w
           semanticPrimitives_v))))) 7 1;
                    (\r1. wordLang_Inst (asm_Arith (asm_Binop
                      word_bignum_Add r1 r1 (Imm (bytes_in_word))))) 8])
         (data_to_word_list_Seq [stackLang_StackLoadAny 5 8;
                    (\r semanticPrimitives_v. wordLang_Inst
                      (asm_Arith (wordLang_Shift Lsr r r (Imm (n2w
                      semanticPrimitives_v))))) 7 1;
                    word_gen_gc_move_code conf;
                    stackLang_StackStoreAny 5 8;
                    (\r1. wordLang_Inst (asm_Arith (asm_Binop
                      word_bignum_Add r1 r1 (Imm (bytes_in_word)))))
                      8]))`;;

let word_gen_gc_partial_move_bitmap_code_def = cake_define
  `word_gen_gc_partial_move_bitmap_code conf =
     (\cmp r ri c. word_bignum_Loop (word_bignum_If cmp r ri c
       (wordLang_Break 0))) asm_NotLower 7 (Imm (n2w 2))
      (word_bignum_If asm_Test 7 (Imm (n2w 1))
         (data_to_word_list_Seq [(\r semanticPrimitives_v.
           wordLang_Inst (asm_Arith (wordLang_Shift Lsr r r (Imm (n2w
           semanticPrimitives_v))))) 7 1;
                    (\r1. wordLang_Inst (asm_Arith (asm_Binop
                      word_bignum_Add r1 r1 (Imm (bytes_in_word))))) 8])
         (data_to_word_list_Seq [stackLang_StackLoadAny 5 8;
                    (\r semanticPrimitives_v. wordLang_Inst
                      (asm_Arith (wordLang_Shift Lsr r r (Imm (n2w
                      semanticPrimitives_v))))) 7 1;
                    word_gen_gc_partial_move_code conf;
                    stackLang_StackStoreAny 5 8;
                    (\r1. wordLang_Inst (asm_Arith (asm_Binop
                      word_bignum_Add r1 r1 (Imm (bytes_in_word)))))
                      8]))`;;

(* 9 is w, 8 is index into stack *)
let word_gen_gc_move_bitmaps_code_def = cake_define
  `((word_gen_gc_move_bitmaps_code conf):'a stackLang_prog) =
     (\cmp r ri c. word_bignum_Loop (word_bignum_If cmp r ri c
       (wordLang_Break 0))) asm_NotTest 0 (Reg 0)
       (data_to_word_list_Seq [stackLang_BitmapLoad 7 9;
                  word_gen_gc_move_bitmap_code conf;
                  stackLang_BitmapLoad 0 9;
                  (\r1. wordLang_Inst (asm_Arith (asm_Binop
                    word_bignum_Add r1 r1 (Imm (n2w 1))))) 9;
                  (\r semanticPrimitives_v. wordLang_Inst
                    (asm_Arith (wordLang_Shift Lsr r r (Imm (n2w
                    semanticPrimitives_v))))) 0 (dimindex (:'a) -
                    1)])`;;

(* 9 is w, 8 is index into stack *)
let word_gen_gc_partial_move_bitmaps_code_def = cake_define
  `((word_gen_gc_partial_move_bitmaps_code conf):'a stackLang_prog) =
     (\cmp r ri c. word_bignum_Loop (word_bignum_If cmp r ri c
       (wordLang_Break 0))) asm_NotTest 0 (Reg 0)
       (data_to_word_list_Seq [stackLang_BitmapLoad 7 9;
                  word_gen_gc_partial_move_bitmap_code conf;
                  stackLang_BitmapLoad 0 9;
                  (\r1. wordLang_Inst (asm_Arith (asm_Binop
                    word_bignum_Add r1 r1 (Imm (n2w 1))))) 9;
                  (\r semanticPrimitives_v. wordLang_Inst
                    (asm_Arith (wordLang_Shift Lsr r r (Imm (n2w
                    semanticPrimitives_v))))) 0 (dimindex (:'a) -
                    1)])`;;

(* 9 is w, 8 is index into stack *)
let word_gen_gc_move_roots_bitmaps_code_def = cake_define
  `((word_gen_gc_move_roots_bitmaps_code conf):'a stackLang_prog) =
     (\cmp r ri c. word_bignum_Loop (word_bignum_If cmp r ri c
       (wordLang_Break 0))) asm_NotTest 9 (Reg 9)
       (data_to_word_list_Seq [(\dest src. wordLang_Inst (asm_Arith
         (asm_Binop asm_Or dest src (Reg src)))) 0 9;
                  (\r1. wordLang_Inst (asm_Arith (asm_Binop
                    word_bignum_Sub r1 r1 (Imm (n2w 1))))) 9;
                  (\r1. wordLang_Inst (asm_Arith (asm_Binop
                    word_bignum_Add r1 r1 (Imm (bytes_in_word))))) 8;
                  word_gen_gc_move_bitmaps_code conf;
                  stackLang_StackLoadAny 9 8])`;;

(* 9 is w, 8 is index into stack *)
let word_gen_gc_partial_move_roots_bitmaps_code_def = cake_define
  `((word_gen_gc_partial_move_roots_bitmaps_code conf):'a
  stackLang_prog) =
     (\cmp r ri c. word_bignum_Loop (word_bignum_If cmp r ri c
       (wordLang_Break 0))) asm_NotTest 9 (Reg 9)
       (data_to_word_list_Seq [(\dest src. wordLang_Inst (asm_Arith
         (asm_Binop asm_Or dest src (Reg src)))) 0 9;
                  (\r1. wordLang_Inst (asm_Arith (asm_Binop
                    word_bignum_Sub r1 r1 (Imm (n2w 1))))) 9;
                  (\r1. wordLang_Inst (asm_Arith (asm_Binop
                    word_bignum_Add r1 r1 (Imm (bytes_in_word))))) 8;
                  word_gen_gc_partial_move_bitmaps_code conf;
                  stackLang_StackLoadAny 9 8])`;;

let word_gen_gc_move_list_code_def = cake_define
  `word_gen_gc_move_list_code conf =
     (\cmp r ri c. word_bignum_Loop (word_bignum_If cmp r ri c
       (wordLang_Break 0))) asm_NotEqual 7 (Imm ((n2w 0):'a word))
       (data_to_word_list_Seq [(\r a. wordLang_Inst (asm_Mem
         word_bignum_Load r (Addr a (n2w 0)))) 5 8;
                  (\r1. wordLang_Inst (asm_Arith (asm_Binop
                    word_bignum_Sub r1 r1 (Imm (n2w 1))))) 7;
                  word_gen_gc_move_code conf;
                  (\r a. wordLang_Inst (asm_Mem word_bignum_Store r
                    (Addr a (n2w 0)))) 5 8;
                  (\r1. wordLang_Inst (asm_Arith (asm_Binop
                    word_bignum_Add r1 r1 (Imm (bytes_in_word)))))
                    8])`;;

let word_gen_gc_partial_move_list_code_def = cake_define
  `word_gen_gc_partial_move_list_code conf =
     (\cmp r ri c. word_bignum_Loop (word_bignum_If cmp r ri c
       (wordLang_Break 0))) asm_NotEqual 7 (Imm ((n2w 0):'a word))
       (data_to_word_list_Seq [(\r a. wordLang_Inst (asm_Mem
         word_bignum_Load r (Addr a (n2w 0)))) 5 8;
                  (\r1. wordLang_Inst (asm_Arith (asm_Binop
                    word_bignum_Sub r1 r1 (Imm (n2w 1))))) 7;
                  word_gen_gc_partial_move_code conf;
                  (\r a. wordLang_Inst (asm_Mem word_bignum_Store r
                    (Addr a (n2w 0)))) 5 8;
                  (\r1. wordLang_Inst (asm_Arith (asm_Binop
                    word_bignum_Add r1 r1 (Imm (bytes_in_word)))))
                    8])`;;

let word_gen_gc_move_data_code_def = cake_define
  `word_gen_gc_move_data_code conf =
     ((\cmp r ri c. word_bignum_Loop (word_bignum_If cmp r ri c
       (wordLang_Break 0))) asm_NotEqual 3 (Reg 8)
      (data_to_word_list_Seq [(\r a. wordLang_Inst (asm_Mem
        word_bignum_Load r (Addr a (n2w 0)))) 7 8;
                 word_bignum_If asm_Test 7 (Imm (n2w 4))
                   (data_to_word_list_Seq [(\r semanticPrimitives_v.
                     wordLang_Inst (asm_Arith (wordLang_Shift Lsr r r
                     (Imm (n2w semanticPrimitives_v))))) 7 (dimindex
                     (:'ga) - data_to_word_config_len_size conf);
                              (\r1. wordLang_Inst (asm_Arith
                                (asm_Binop word_bignum_Add r1 r1 (Imm
                                (bytes_in_word))))) 8;
                              word_gen_gc_move_list_code conf])
                   (data_to_word_list_Seq [(\r semanticPrimitives_v.
                     wordLang_Inst (asm_Arith (wordLang_Shift Lsr r r
                     (Imm (n2w semanticPrimitives_v))))) 7 (dimindex
                     (:'ga) - data_to_word_config_len_size conf);
                              (\r1. wordLang_Inst (asm_Arith
                                (asm_Binop word_bignum_Add r1 r1 (Imm
                                (n2w 1))))) 7;
                              (\r semanticPrimitives_v. wordLang_Inst
                                (asm_Arith (wordLang_Shift Lsl r r (Imm
                                (n2w semanticPrimitives_v))))) 7
                                (backend_common_word_shift (:'a));
                              (\r1 r2. wordLang_Inst (asm_Arith
                                (asm_Binop word_bignum_Add r1 r1 (Reg
                                r2)))) 8 7])]):'a stackLang_prog)`;;

let word_gen_gc_partial_move_ref_list_code_def = cake_define
  `word_gen_gc_partial_move_ref_list_code conf =
     ((\cmp r ri c. word_bignum_Loop (word_bignum_If cmp r ri c
       (wordLang_Break 0))) asm_NotEqual 9 (Reg 8)
      (data_to_word_list_Seq [(\r a. wordLang_Inst (asm_Mem
        word_bignum_Load r (Addr a (n2w 0)))) 7 8;
                 (\r semanticPrimitives_v. wordLang_Inst (asm_Arith
                   (wordLang_Shift Lsr r r (Imm (n2w
                   semanticPrimitives_v))))) 7 (dimindex (:'ga) -
                   data_to_word_config_len_size conf);
                 (\r1. wordLang_Inst (asm_Arith (asm_Binop
                   word_bignum_Add r1 r1 (Imm (bytes_in_word))))) 8;
                 word_gen_gc_partial_move_list_code conf]):'a
                   stackLang_prog)`;;

let word_gen_gc_partial_move_data_code_def = cake_define
  `word_gen_gc_partial_move_data_code conf =
     ((\cmp r ri c. word_bignum_Loop (word_bignum_If cmp r ri c
       (wordLang_Break 0))) asm_NotEqual 3 (Reg 8)
      (data_to_word_list_Seq [(\r a. wordLang_Inst (asm_Mem
        word_bignum_Load r (Addr a (n2w 0)))) 7 8;
                 word_bignum_If asm_Test 7 (Imm (n2w 4))
                   (data_to_word_list_Seq [(\r semanticPrimitives_v.
                     wordLang_Inst (asm_Arith (wordLang_Shift Lsr r r
                     (Imm (n2w semanticPrimitives_v))))) 7 (dimindex
                     (:'ga) - data_to_word_config_len_size conf);
                              (\r1. wordLang_Inst (asm_Arith
                                (asm_Binop word_bignum_Add r1 r1 (Imm
                                (bytes_in_word))))) 8;
                              word_gen_gc_partial_move_list_code
                                conf])
                   (data_to_word_list_Seq [(\r semanticPrimitives_v.
                     wordLang_Inst (asm_Arith (wordLang_Shift Lsr r r
                     (Imm (n2w semanticPrimitives_v))))) 7 (dimindex
                     (:'ga) - data_to_word_config_len_size conf);
                              (\r1. wordLang_Inst (asm_Arith
                                (asm_Binop word_bignum_Add r1 r1 (Imm
                                (n2w 1))))) 7;
                              (\r semanticPrimitives_v. wordLang_Inst
                                (asm_Arith (wordLang_Shift Lsl r r (Imm
                                (n2w semanticPrimitives_v))))) 7
                                (backend_common_word_shift (:'a));
                              (\r1 r2. wordLang_Inst (asm_Arith
                                (asm_Binop word_bignum_Add r1 r1 (Reg
                                r2)))) 8 7])]):'a stackLang_prog)`;;

let word_gen_gc_move_refs_code_def = cake_define
  `word_gen_gc_move_refs_code conf =
     ((\cmp r ri c. word_bignum_Loop (word_bignum_If cmp r ri c
       (wordLang_Break 0))) asm_NotEqual 0 (Reg 8)
      (data_to_word_list_Seq [(\r a. wordLang_Inst (asm_Mem
        word_bignum_Load r (Addr a (n2w 0)))) 7 8;
                 (\r semanticPrimitives_v. wordLang_Inst (asm_Arith
                   (wordLang_Shift Lsr r r (Imm (n2w
                   semanticPrimitives_v))))) 7 (dimindex (:'ga) -
                   data_to_word_config_len_size conf);
                 (\r1. wordLang_Inst (asm_Arith (asm_Binop
                   word_bignum_Add r1 r1 (Imm (bytes_in_word))))) 8;
                 word_gen_gc_move_list_code conf;
                 wordLang_Get 0 (Temp (n2w 4))]):'a
                   stackLang_prog)`;;

let word_gen_gc_move_loop_code_def = cake_define
  `word_gen_gc_move_loop_code conf =
     (\cmp r ri c. word_bignum_Loop (word_bignum_If cmp r ri c
       (wordLang_Break 0))) asm_NotTest 7 (Reg 7)
       (word_bignum_If (EQUAL) 1 (Reg 2)
          (data_to_word_list_Seq [word_gen_gc_move_data_code conf;
                     wordLang_Get 5 (Temp (n2w 2));
                     wordLang_Get 7 (Temp (n2w 4));
                     (\dest src. wordLang_Inst (asm_Arith (asm_Binop
                       asm_Or dest src (Reg src)))) 1 7;
                     (\dest src. wordLang_Inst (asm_Arith (asm_Binop
                       asm_Or dest src (Reg src)))) 2 5;
                     (\r1 r2. wordLang_Inst (asm_Arith (asm_Binop
                       word_bignum_Sub r1 r1 (Reg r2)))) 7 5])
          (data_to_word_list_Seq [(\dest src. wordLang_Inst
            (asm_Arith (asm_Binop asm_Or dest src (Reg src)))) 0 1;
                     reg_alloc_Set (Temp (n2w 6)) 8;
                     (\dest src. wordLang_Inst (asm_Arith (asm_Binop
                       asm_Or dest src (Reg src)))) 8 2;
                     reg_alloc_Set (Temp (n2w 5)) 8;
                     word_gen_gc_move_refs_code conf;
                     (\dest src. wordLang_Inst (asm_Arith (asm_Binop
                       asm_Or dest src (Reg src)))) 7 8;
                     wordLang_Get 1 (Temp (n2w 5));
                     wordLang_Get 2 (Temp (n2w 5));
                     reg_alloc_Set (Temp (n2w 4)) 2;
                     wordLang_Get 2 (Temp (n2w 2));
                     (\dest src. wordLang_Inst (asm_Arith (asm_Binop
                       asm_Or dest src (Reg src)))) 3 3;
                     (\dest src. wordLang_Inst (asm_Arith (asm_Binop
                       asm_Or dest src (Reg src)))) 4 4;
                     (\dest src. wordLang_Inst (asm_Arith (asm_Binop
                       asm_Or dest src (Reg src)))) 7 1;
                     (\r1 r2. wordLang_Inst (asm_Arith (asm_Binop
                       word_bignum_Sub r1 r1 (Reg r2)))) 7 2;
                     wordLang_Get 8 (Temp (n2w 6));
                     (\dest src. wordLang_Inst (asm_Arith (asm_Binop
                       asm_Or dest src (Reg src)))) 5 8;
                     (\r1 r2. wordLang_Inst (asm_Arith (asm_Binop
                       word_bignum_Sub r1 r1 (Reg r2)))) 5 3;
                     (\r1 r2. wordLang_Inst (asm_Arith (asm_Binop
                       asm_Or r1 r1 (Reg r2)))) 7 5]))`;;

let word_gc_partial_or_full_def = cake_define
  `word_gc_partial_or_full gen_sizes partial_code full_code =
     (match gen_sizes with [] -> data_to_word_list_Seq ([wordLang_Get
       8 TriggerGC; wordLang_Get 7 EndOfHeap; (\r1 r2. wordLang_Inst
       (asm_Arith (asm_Binop word_bignum_Sub r1 r1 (Reg r2)))) 7 8] ++
       full_code) | _1 -> data_to_word_list_Seq
              [wordLang_Get 8 TriggerGC;
               wordLang_Get 7 EndOfHeap;
               (\r1 r2. wordLang_Inst (asm_Arith (asm_Binop
                 word_bignum_Sub r1 r1 (Reg r2)))) 7 8;
               word_bignum_If asm_NotLower 7 (Reg 1)
                 (data_to_word_list_Seq partial_code)
                 (data_to_word_list_Seq full_code)])`;;

let SetNewTrigger_def = cake_define
  `SetNewTrigger (endh:num) (ib:num) gs =
     data_to_word_list_Seq [(\r w. wordLang_Inst (word_depth_Const r
       w)) 1 ((get_gen_size gs):'a word);
               wordLang_Get 7 AllocSize;
               (\dest src. wordLang_Inst (asm_Arith (asm_Binop asm_Or
                 dest src (Reg src)))) 4 endh;
               (\r1 r2. wordLang_Inst (asm_Arith (asm_Binop
                 word_bignum_Sub r1 r1 (Reg r2)))) 4 ib;
               word_bignum_If asm_Lower 1 (Reg 7)
                 (word_bignum_If asm_Lower 4 (Reg 7)
                    (reg_alloc_Set TriggerGC endh)
                    (word_bignum_If asm_Test 7 (Imm (if dimindex
                      (:'a) = 32 then (n2w 3) else (n2w 7)))
                      (linear_scan_Seq ((\r1 r2. wordLang_Inst
                        (asm_Arith (asm_Binop word_bignum_Add r1 r1 (Reg
                        r2)))) 7 ib) (reg_alloc_Set TriggerGC 7))
                      (reg_alloc_Set TriggerGC endh)))
                 (word_bignum_If asm_Lower 4 (Reg 1)
                    (reg_alloc_Set TriggerGC endh)
                    (linear_scan_Seq ((\r1 r2. wordLang_Inst
                      (asm_Arith (asm_Binop word_bignum_Add r1 r1
                      (Reg r2)))) 1 ib) (reg_alloc_Set TriggerGC
                      1)))]`;;

let word_gc_code_def = cake_define
  `word_gc_code conf =
     (match data_to_word_config_gc_kind conf with data_to_word_None
       ->
         (data_to_word_list_Seq
               [reg_alloc_Set AllocSize 1;
                wordLang_Get 2 CurrHeap;
                reg_alloc_Set NextFree 2;
                reg_alloc_Set TriggerGC 2;
                reg_alloc_Set EndOfHeap 2;
                word_bignum_If asm_Test 1 (Reg 1) word_bignum_Skip
                  (linear_scan_Seq ((\r w. wordLang_Inst
                  (word_depth_Const r w)) 1 (n2w 1)) (stackLang_Halt
                  1))]) | data_to_word_Simple ->
         (data_to_word_list_Seq
               [reg_alloc_Set AllocSize 1;
                reg_alloc_Set NextFree 0;
                (\r w. wordLang_Inst (word_depth_Const r w)) 1 (n2w
                  0);
                (\dest src. wordLang_Inst (asm_Arith (asm_Binop
                  asm_Or dest src (Reg src)))) 2 1;
                wordLang_Get 3 OtherHeap;
                (\dest src. wordLang_Inst (asm_Arith (asm_Binop
                  asm_Or dest src (Reg src)))) 4 1;
                wordLang_Get 5 Globals;
                (\dest src. wordLang_Inst (asm_Arith (asm_Binop
                  asm_Or dest src (Reg src)))) 6 1;
                (\dest src. wordLang_Inst (asm_Arith (asm_Binop
                  asm_Or dest src (Reg src)))) 8 1;
                word_gc_move_code conf;
                reg_alloc_Set Globals 5;
                (\dest src. wordLang_Inst (asm_Arith (asm_Binop
                  asm_Or dest src (Reg src)))) 7 5;
                (\r semanticPrimitives_v. wordLang_Inst (asm_Arith
                  (wordLang_Shift Lsr r r (Imm (n2w
                  semanticPrimitives_v))))) 7 (shift_length conf);
                (\r semanticPrimitives_v. wordLang_Inst (asm_Arith
                  (wordLang_Shift Lsl r r (Imm (n2w
                  semanticPrimitives_v))))) 7 (backend_common_word_shift
                  (:'a));
                wordLang_Get 9 OtherHeap;
                (\r1 r2. wordLang_Inst (asm_Arith (asm_Binop
                  word_bignum_Add r1 r1 (Reg r2)))) 7 9;
                reg_alloc_Set GlobReal 7;
                (\r w. wordLang_Inst (word_depth_Const r w)) 7 (n2w
                  0);
                stackLang_StackLoadAny 9 8;
                (\dest src. wordLang_Inst (asm_Arith (asm_Binop
                  asm_Or dest src (Reg src)))) 8 7;
                word_gc_move_roots_bitmaps_code conf;
                wordLang_Get 8 OtherHeap;
                word_gc_move_loop_code conf;
                wordLang_Get 0 CurrHeap;
                wordLang_Get 1 OtherHeap;
                wordLang_Get 2 HeapLength;
                (\r1 r2. wordLang_Inst (asm_Arith (asm_Binop
                  word_bignum_Add r1 r1 (Reg r2)))) 2 1;
                reg_alloc_Set CurrHeap 1;
                reg_alloc_Set OtherHeap 0;
                wordLang_Get 0 NextFree;
                reg_alloc_Set NextFree 8;
                reg_alloc_Set EndOfHeap 2;
                reg_alloc_Set TriggerGC 2;
                wordLang_Get 1 AllocSize;
                (\r1 r2. wordLang_Inst (asm_Arith (asm_Binop
                  word_bignum_Sub r1 r1 (Reg r2)))) 2 8;
                word_bignum_If asm_Lower 2 (Reg 1) (linear_scan_Seq
                  ((\r w. wordLang_Inst (word_depth_Const r w)) 1 (n2w
                  1)) (stackLang_Halt 1)) word_bignum_Skip]) |
                  data_to_word_Generational gen_sizes ->
         ((word_gc_partial_or_full gen_sizes
               [reg_alloc_Set AllocSize 1;
                reg_alloc_Set NextFree 0;
                wordLang_Get 4 GenStart;
                wordLang_Get 5 EndOfHeap;
                wordLang_Get 2 CurrHeap;
                reg_alloc_Set (Temp (n2w 0)) 4;
                (\r1 r2. wordLang_Inst (asm_Arith (asm_Binop
                  word_bignum_Sub r1 r1 (Reg r2)))) 5 2;
                reg_alloc_Set (Temp (n2w 1)) 5;
                wordLang_Get 7 HeapLength;
                wordLang_Get 5 Globals;
                wordLang_Get 3 OtherHeap;
                (\r semanticPrimitives_v. wordLang_Inst (asm_Arith
                  (wordLang_Shift Lsr r r (Imm (n2w
                  semanticPrimitives_v))))) 4
                  ((backend_common_word_shift) (:'a));
                (\dest src. wordLang_Inst (asm_Arith (asm_Binop
                  asm_Or dest src (Reg src)))) 6 3;
                word_gen_gc_partial_move_code conf;
                reg_alloc_Set Globals 5;
                (\dest src. wordLang_Inst (asm_Arith (asm_Binop
                  asm_Or dest src (Reg src)))) 8 5;
                (\r semanticPrimitives_v. wordLang_Inst (asm_Arith
                  (wordLang_Shift Lsr r r (Imm (n2w
                  semanticPrimitives_v))))) 8 (shift_length conf);
                (\r semanticPrimitives_v. wordLang_Inst (asm_Arith
                  (wordLang_Shift Lsl r r (Imm (n2w
                  semanticPrimitives_v))))) 8 (backend_common_word_shift
                  (:'a));
                wordLang_Get 9 CurrHeap;
                (\r1 r2. wordLang_Inst (asm_Arith (asm_Binop
                  word_bignum_Add r1 r1 (Reg r2)))) 8 9;
                reg_alloc_Set GlobReal 8;
                (\r w. wordLang_Inst (word_depth_Const r w)) 8 (n2w
                  0);
                stackLang_StackLoadAny 9 8;
                word_gen_gc_partial_move_roots_bitmaps_code conf;
                wordLang_Get 8 CurrHeap;
                wordLang_Get 9 HeapLength;
                (\r1 r2. wordLang_Inst (asm_Arith (asm_Binop
                  word_bignum_Add r1 r1 (Reg r2)))) 9 8;
                wordLang_Get 8 EndOfHeap;
                word_gen_gc_partial_move_ref_list_code conf;
                wordLang_Get 8 OtherHeap;
                word_gen_gc_partial_move_data_code conf;
                wordLang_Get 2 OtherHeap;
                (\dest src. wordLang_Inst (asm_Arith (asm_Binop
                  asm_Or dest src (Reg src)))) 0 3;
                (\r1 r2. wordLang_Inst (asm_Arith (asm_Binop
                  word_bignum_Sub r1 r1 (Reg r2)))) 0 2;
                (\r semanticPrimitives_v. wordLang_Inst (asm_Arith
                  (wordLang_Shift Lsr r r (Imm (n2w
                  semanticPrimitives_v))))) 0
                  ((backend_common_word_shift) (:'a));
                wordLang_Get 3 GenStart;
                wordLang_Get 1 CurrHeap;
                (\r1 r2. wordLang_Inst (asm_Arith (asm_Binop
                  word_bignum_Add r1 r1 (Reg r2)))) 3 1;
                memcpy_code;
                wordLang_Get 0 NextFree;
                reg_alloc_Set NextFree 3;
                wordLang_Get 8 EndOfHeap;
                wordLang_Get 2 TriggerGC;
                SetNewTrigger 8 3 gen_sizes;
                (\r w. wordLang_Inst (word_depth_Const r w)) 1 (n2w
                  0);
                reg_alloc_Set (Temp (n2w 0)) 1;
                reg_alloc_Set (Temp (n2w 1)) 1;
                wordLang_Get 1 AllocSize;
                (\r1 r2. wordLang_Inst (asm_Arith (asm_Binop
                  word_bignum_Sub r1 r1 (Reg r2)))) 8 3;
                wordLang_Get 7 CurrHeap;
                (\r1 r2. wordLang_Inst (asm_Arith (asm_Binop
                  word_bignum_Sub r1 r1 (Reg r2)))) 3 7;
                reg_alloc_Set GenStart 3]
               [reg_alloc_Set AllocSize 1;
                reg_alloc_Set NextFree 0;
                (\r w. wordLang_Inst (word_depth_Const r w)) 1 ((n2w
                  0):'a word);
                (\dest src. wordLang_Inst (asm_Arith (asm_Binop
                  asm_Or dest src (Reg src)))) 2 1;
                wordLang_Get 3 OtherHeap;
                wordLang_Get 4 HeapLength;
                (\r1 r2. wordLang_Inst (asm_Arith (asm_Binop
                  word_bignum_Add r1 r1 (Reg r2)))) 4 3;
                reg_alloc_Set (Temp (n2w 0)) 4;
                reg_alloc_Set (Temp (n2w 1)) 4;
                reg_alloc_Set (Temp (n2w 2)) 4;
                reg_alloc_Set (Temp (n2w 4)) 4;
                reg_alloc_Set (Temp (n2w 5)) 4;
                reg_alloc_Set (Temp (n2w 6)) 4;
                wordLang_Get 4 HeapLength;
                (\r semanticPrimitives_v. wordLang_Inst (asm_Arith
                  (wordLang_Shift Lsr r r (Imm (n2w
                  semanticPrimitives_v))))) 4
                  ((backend_common_word_shift) (:'a));
                reg_alloc_Set (Temp (n2w 3)) 4;
                (\dest src. wordLang_Inst (asm_Arith (asm_Binop
                  asm_Or dest src (Reg src)))) 4 1;
                wordLang_Get 5 Globals;
                (\dest src. wordLang_Inst (asm_Arith (asm_Binop
                  asm_Or dest src (Reg src)))) 6 1;
                (\dest src. wordLang_Inst (asm_Arith (asm_Binop
                  asm_Or dest src (Reg src)))) 8 1;
                word_gen_gc_move_code conf;
                reg_alloc_Set Globals 5;
                (\dest src. wordLang_Inst (asm_Arith (asm_Binop
                  asm_Or dest src (Reg src)))) 7 5;
                wordLang_Get 9 OtherHeap;
                (\r semanticPrimitives_v. wordLang_Inst (asm_Arith
                  (wordLang_Shift Lsr r r (Imm (n2w
                  semanticPrimitives_v))))) 7 (shift_length conf);
                (\r semanticPrimitives_v. wordLang_Inst (asm_Arith
                  (wordLang_Shift Lsl r r (Imm (n2w
                  semanticPrimitives_v))))) 7 (backend_common_word_shift
                  (:'a));
                (\r1 r2. wordLang_Inst (asm_Arith (asm_Binop
                  word_bignum_Add r1 r1 (Reg r2)))) 7 9;
                reg_alloc_Set GlobReal 7;
                (\r w. wordLang_Inst (word_depth_Const r w)) 7 (n2w
                  0);
                stackLang_StackLoadAny 9 8;
                (\dest src. wordLang_Inst (asm_Arith (asm_Binop
                  asm_Or dest src (Reg src)))) 8 7;
                word_gen_gc_move_roots_bitmaps_code conf;
                wordLang_Get 2 (Temp (n2w 2));
                wordLang_Get 8 OtherHeap;
                (\dest src. wordLang_Inst (asm_Arith (asm_Binop
                  asm_Or dest src (Reg src)))) 7 3;
                (\r1 r2. wordLang_Inst (asm_Arith (asm_Binop
                  word_bignum_Sub r1 r1 (Reg r2)))) 7 8;
                wordLang_Get 1 (Temp (n2w 6));
                (\dest src. wordLang_Inst (asm_Arith (asm_Binop
                  asm_Or dest src (Reg src)))) 6 2;
                (\r1 r2. wordLang_Inst (asm_Arith (asm_Binop
                  word_bignum_Sub r1 r1 (Reg r2)))) 6 1;
                (\r1 r2. wordLang_Inst (asm_Arith (asm_Binop asm_Or
                  r1 r1 (Reg r2)))) 7 6;
                word_gen_gc_move_loop_code conf;
                wordLang_Get 0 CurrHeap;
                wordLang_Get 1 OtherHeap;
                wordLang_Get 2 (Temp (n2w 2));
                reg_alloc_Set CurrHeap 1;
                reg_alloc_Set OtherHeap 0;
                wordLang_Get 0 NextFree;
                reg_alloc_Set NextFree 3;
                reg_alloc_Set EndOfHeap 2;
                (\dest src. wordLang_Inst (asm_Arith (asm_Binop
                  asm_Or dest src (Reg src)))) 8 3;
                (\r1 r2. wordLang_Inst (asm_Arith (asm_Binop
                  word_bignum_Sub r1 r1 (Reg r2)))) 8 1;
                reg_alloc_Set GenStart 8;
                SetNewTrigger 2 3 gen_sizes;
                (\r w. wordLang_Inst (word_depth_Const r w)) 1 (n2w
                  0);
                reg_alloc_Set (Temp (n2w 0)) 1;
                reg_alloc_Set (Temp (n2w 1)) 1;
                reg_alloc_Set (Temp (n2w 2)) 1;
                reg_alloc_Set (Temp (n2w 3)) 1;
                reg_alloc_Set (Temp (n2w 4)) 1;
                reg_alloc_Set (Temp (n2w 5)) 1;
                reg_alloc_Set (Temp (n2w 6)) 1;
                wordLang_Get 1 AllocSize;
                wordLang_Get 2 TriggerGC;
                (\r1 r2. wordLang_Inst (asm_Arith (asm_Binop
                  word_bignum_Sub r1 r1 (Reg r2)))) 2 3;
                word_bignum_If asm_Lower 2 (Reg 1)
                  (linear_scan_Seq ((\r w. wordLang_Inst
                  (word_depth_Const r w)) 1 (n2w 1)) (stackLang_Halt
                  1)) word_bignum_Skip]):'a stackLang_prog))`;;

let stubs_def = cake_define
  `stack_alloc_stubs conf = [(gc_stub_location,linear_scan_Seq
  (word_gc_code conf) (wordLang_Return 0))]`;;

let stub_names_def = cake_define
  `stack_alloc_stub_names one = [(gc_stub_location,(strlit "_GC"))]`;;

(* compiler *)

(* HOL4 ML code, not ported:
local
val next_lab_quotation = `
  next_lab (p:'a stackLang$prog) aux =
    case p of
    | Seq p1 p2 => next_lab p1 (next_lab p2 aux)
    | If _ _ _ p1 p2 => next_lab p1 (next_lab p2 aux)
    | Loop p => next_lab p aux
    | Call NONE _ NONE => aux
    | Call NONE _ (SOME (_,_,l2)) => MAX aux (l2 + 2)
    | Call (SOME (p,_,_,l2)) _ NONE => next_lab p (MAX aux (l2 + 2))
    | Call (SOME (p,_,_,l2)) _ (SOME (p',_,l3)) =>
          next_lab p (next_lab p' ((MAX (MAX l2 l3 + 2) aux)))
    | _ => aux`
in
val next_lab_def = Define next_lab_quotation;
*)

(* HOL4 ML code, not ported:
local
val comp_quotation = `
  comp n m p =
    case p of
    | Seq p1 p2 =>
        let (q1,m) = comp n m p1 in
        let (q2,m) = comp n m p2 in
          (Seq q1 q2,m)
    | If c r ri p1 p2 =>
        let (q1,m) = comp n m p1 in
        let (q2,m) = comp n m p2 in
          (If c r ri q1 q2,m)
    | Loop p1 =>
        let (q1,m) = comp n m p1 in
          (Loop q1,m)
    | Call NONE dest exc => (Call NONE dest NONE,m)
    | Call (SOME (p1,lr,l1,l2)) dest exc =>
        let (q1,m) = comp n m p1 in
         (case exc of
          | NONE => (Call (SOME (q1,lr,l1,l2)) dest NONE,m)
          | SOME (p2,k1,k2) =>
              let (q2,m) = comp n m p2 in
                (Call (SOME (q1,lr,l1,l2)) dest (SOME (q2,k1,k2)),m))
    | Alloc k => (Call (SOME (Skip,0,n,m)) (INL gc_stub_location)
      NONE,m+1)
    | StoreConsts k1 k2 (SOME loc) => (Call (SOME (Skip,0,n,m)) (INL
      loc) NONE,m+1)
    | _ => (p,m) `
in
val comp_def = Define comp_quotation
*)

let prog_comp_def = cake_define
  `stack_alloc_prog_comp (n,p) = (n,FST (data_to_word_comp n
  (next_lab p 2) p))`;;

let compile_def = cake_define
  `stack_alloc_compile c wordLang_prog = stack_alloc_stubs c ++ MAP
  stack_alloc_prog_comp wordLang_prog`;;
