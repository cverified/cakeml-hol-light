(* ======================================================== *)
(*  data_to_word: ported from HOL4's
    compiler/backend/data_to_wordScript.sml  *)
(* ======================================================== *)

(*
  This compiler phase removes the functional-programming-style data
  abstraction of dataLang and lands in wordLang where all values are
  machine words and memory is a flat finite mapping from machine
  addresses to machine words. This phase introduces the garbage
  collector and bignum library, among other things.
*)

needs "basis/pure/mlstring.ml";;
needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/dataLang.ml";;
needs "compiler/backend/stackLang.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/backend/word_bignum.ml";;
needs "compiler/backend/word_depth.ml";;
needs "compiler/backend/word_to_word.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "lib/binary_ieee.ml";;
needs "lib/byte.ml";;
needs "lib/comparison.ml";;
needs "lib/multiword.ml";;
needs "lib/sptree.ml";;
needs "lib/ternaryComparisons.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "semantics/fpSem.ml";;

let gc_kind_INDUCT,gc_kind_RECURSION = define_datatype
  "gc_kind = data_to_word_None | data_to_word_Simple | \
   data_to_word_Generational (num list)";;
hol4_overload "None" "data_to_word_None";;
hol4_overload "Simple" "data_to_word_Simple";;
hol4_overload "Generational" "data_to_word_Generational";;

let data_to_word_config_FIELDS = define_record "data_to_word_config"
  ["tag_bits","num";
   "len_bits","num";
   "pad_bits","num";
   "len_size","num";
   "has_div","bool";
   "has_longdiv","bool";
   "has_fp_ops","bool";
   "has_fp_tern","bool";
   "be","bool";
   "call_empty_ffi","bool";
   "gc_kind","gc_kind"];;

let adjust_var_def = cake_define
  `adjust_var n = 2 * n + (2:num)`;;

let adjust_set_def = cake_define
  `adjust_set (names:'a spt) =
     ((fromAList (MAP (\(n,k). (adjust_var n,one)) (toAList
       names))):one spt)`;;

let adjust_sets_def = cake_define
  `adjust_sets (names:'a spt) =
     ((LS one,adjust_set names):one spt#one spt)`;;

let unit_def = cake_define
  `data_to_word_Unit = Const (n2w 2)`;;
hol4_overload "Unit" "data_to_word_Unit";;

let GiveUp_def = cake_define
  `GiveUp = (Seq (Assign 1 (Const (--(n2w 1))))
                (Alloc 1 (adjust_sets (LN:one spt))):'a
                  wordLang_prog)`;;

let BignumHalt_def = cake_define
  `BignumHalt r = If Test r (Imm (n2w 1)) Skip GiveUp`;;

let make_header_def = cake_define
  `make_header conf tag len =
     (let l = dimindex (:'a) - data_to_word_config_len_size conf in
       (n2w len << l || tag << 2 || ((n2w 3):'a word)))`;;

let tag_mask_def = cake_define
  `tag_mask conf =
     (let l = dimindex (:'a) - data_to_word_config_len_size conf in
       (word_slice (l - 1) 2) (--((n2w 0):'a word)))`;;

let encode_header_def = cake_define
  `encode_header (conf:data_to_word_config) tag len =
     (if tag < 2 EXP (dimindex (:'a) - data_to_word_config_len_size
       conf - 2) /\
        tag < dimword (:'a) DIV 16 /\
        len < 2 EXP (dimindex (:'a) - 4) /\
        len < 2 EXP data_to_word_config_len_size conf then SOME
          ((make_header conf (n2w tag) len):'a word) else NONE)`;;

let list_Seq_def = cake_define
  `(data_to_word_list_Seq [] = wordLang_Skip) /\
   (data_to_word_list_Seq [x] = x) /\
   (data_to_word_list_Seq (x :: y :: xs) = Seq x
     (data_to_word_list_Seq (y :: xs)))`;;
hol4_overload "list_Seq" "data_to_word_list_Seq";;

let StoreEach_def = cake_define
  `(StoreEach v [] offset = Skip) /\
   (StoreEach v (x :: xs) (offset:'a word) =
      Seq (Store (Op Add [Var v; Const offset]) x)
          (StoreEach v xs (offset + bytes_in_word)))`;;

let small_shift_length_def = cake_define
  `small_shift_length conf = data_to_word_config_len_bits conf +
  data_to_word_config_tag_bits conf + 1`;;

let shift_length_def = cake_define
  `shift_length conf = 1 + data_to_word_config_pad_bits conf +
  data_to_word_config_len_bits conf + data_to_word_config_tag_bits
  conf + 1`;;

let conf_ok_def = cake_define
  `conf_ok (:'a) c <=>
     shift_length c < dimindex (:'ga) /\
     (backend_common_word_shift) (:'ga) <= shift_length c /\
       ~(data_to_word_config_len_size c = 0) /\
       data_to_word_config_len_size
     c + 7 < dimindex (:'ga)`;;

let max_heap_limit_def = cake_define
  `max_heap_limit (:'a) c =
     MIN (dimword (:'a) DIV 2 EXP shift_length c)
         (dimword (:'a) DIV 2 EXP ((backend_common_word_shift)
           (:'a) + 1))`;;

let all_ones_def = cake_define
  `all_ones m n = (if m <= n then (n2w 0) else (word_slice (m - 1) n)
  (--(n2w 0)))`;;

let maxout_bits_def = cake_define
  `maxout_bits n rep_len k =
     (if n < 2 EXP rep_len - 1 then n2w n << k else all_ones (k +
       rep_len) k)`;;

let ptr_bits_def = cake_define
  `ptr_bits conf tag len =
     (maxout_bits tag (data_to_word_config_tag_bits conf) (1 +
       data_to_word_config_len_bits conf) ||
      maxout_bits len (data_to_word_config_len_bits conf) 1)`;;

let real_addr_def = cake_define
  `((real_addr (conf:data_to_word_config) r):'a wordLang_exp) =
     (let k = (backend_common_word_shift) (:'a) in
     let l = shift_length conf in
       if k = l /\ data_to_word_config_len_bits conf = 0 /\
         data_to_word_config_tag_bits conf = 0 then
         Op Add [Lookup CurrHeap; Op Sub [Var r; Const (n2w 1)]] else
           if k <= data_to_word_config_pad_bits conf + 1 then
         Op Add [Lookup CurrHeap; (\sh e n. Shift sh e (Const (n2w
           n))) Lsr (Var r) (l - k)] else
         Op Add [Lookup CurrHeap; (\sh e n. Shift sh e (Const (n2w
           n))) Lsl ((\sh e n. Shift sh e (Const (n2w n))) Lsr (Var
           r) l) k])`;;

let real_offset_def = cake_define
  `((real_offset (conf:data_to_word_config) r):'a wordLang_exp) =
      Op Add [Const bytes_in_word;
              if dimindex (:'a) = 32 then Var r else (\sh e n.
                Shift sh e (Const (n2w n))) Lsl (Var r) 1]`;;

let real_byte_offset_def = cake_define
  `(real_byte_offset r:'a wordLang_exp) =
     Op Add [Const bytes_in_word;
             (\sh e n. Shift sh e (Const (n2w n))) Lsr (Var r) 2]`;;

let word_op_type_INDUCT,word_op_type_RECURSION = define_datatype
  "word_op_type = Bitwise (binop) | Carried (binop)";;

let lookup_word_op_def = cake_define
  `(lookup_word_op Andw = Bitwise And) /\
   (lookup_word_op Orw = Bitwise Or) /\
   (lookup_word_op Xor = Bitwise Xor) /\
   (lookup_word_op Add = Carried Add) /\
   (lookup_word_op Sub = Carried Sub)`;;

let FromList_location_def = cake_define
  `FromList_location = word_num_stubs`;;
let FromList1_location_def = cake_define
  `FromList1_location = FromList_location + 1`;;
let RefByte_location_def = cake_define
  `RefByte_location = FromList1_location + 1`;;
let RefArray_location_def = cake_define
  `RefArray_location = RefByte_location + 1`;;
let replicate_location_def = cake_define
  `Replicate_location = RefArray_location + 1`;;
let AnyArith_location_def = cake_define
  `AnyArith_location = Replicate_location + 1`;;
let add_location_def = cake_define
  `Add_location = AnyArith_location + 1`;;
let sub_location_def = cake_define
  `Sub_location = Add_location + 1`;;
let mul_location_def = cake_define
  `Mul_location = Sub_location + 1`;;
let div_location_def = cake_define
  `Div_location = Mul_location + 1`;;
let mod_location_def = cake_define
  `Mod_location = Div_location + 1`;;
let compare1_location_def = cake_define
  `Compare1_location = Mod_location + 1`;;
let compare_location_def = cake_define
  `Compare_location = Compare1_location + 1`;;
let equal1_location_def = cake_define
  `Equal1_location = Compare_location + 1`;;
let equal_location_def = cake_define
  `Equal_location = Equal1_location + 1`;;
let LongDiv1_location_def = cake_define
  `LongDiv1_location = Equal_location + 1`;;
let LongDiv_location_def = cake_define
  `LongDiv_location = LongDiv1_location + 1`;;
let MemCopy_location_def = cake_define
  `MemCopy_location = LongDiv_location + 1`;;
let ByteCopy_location_def = cake_define
  `ByteCopy_location = MemCopy_location + 1`;;
let ByteCopyAdd_location_def = cake_define
  `ByteCopyAdd_location = ByteCopy_location + 1`;;
let ByteCopySub_location_def = cake_define
  `ByteCopySub_location = ByteCopyAdd_location + 1`;;
let ByteCopyNew_location_def = cake_define
  `ByteCopyNew_location = ByteCopySub_location + 1`;;
let install_location_def = cake_define
  `Install_location = ByteCopyNew_location + 1`;;
let InstallCode_location_def = cake_define
  `InstallCode_location = Install_location + 1`;;
let InstallData_location_def = cake_define
  `InstallData_location = InstallCode_location + 1`;;
let dummy_location_def = cake_define
  `Dummy_location = InstallData_location + 1`;;
let append_location_def = cake_define
  `Append_location = Dummy_location + 1`;;
let AppendMainLoop_location_def = cake_define
  `AppendMainLoop_location = Append_location + 1`;;
let AppendLenLoop_location_def = cake_define
  `AppendLenLoop_location = AppendMainLoop_location + 1`;;
let XorLoop_location_def = cake_define
  `XorLoop_location = AppendLenLoop_location + 1`;;
let unused_location_def = cake_define
  `Unused_location = XorLoop_location + 1`;;
let StringCmpLoop_location_def = cake_define
  `StringCmpLoop_location = Unused_location + 1`;;
let bignum_location_def = cake_define
  `Bignum_location = StringCmpLoop_location + 1`;;

let SilentFFI_def = cake_define
  `SilentFFI c n names =
     (if data_to_word_config_call_empty_ffi c then
       list_Seq [Assign n (Const (n2w 0));
                 Assign 7 (Op Sub [Lookup NextFree; Lookup
                   CurrHeap]);
                 Assign 9 (Lookup HeapLength);
                 FFI (implode "") 7 n 9 n names] else Skip)`;;

let AllocVar_def = cake_define
  `AllocVar c (limit:num) (names:one spt) =
     list_Seq [Assign 1 ((\sh e n. Shift sh e (Const (n2w n))) Lsr
       (Var 1) 2);
               If Lower 1 (Imm (n2w limit))
                 (Assign 1 ((\sh e n. Shift sh e (Const (n2w n))) Lsl
                   (Op Add [Var 1; Const (n2w 1)])
                   ((backend_common_word_shift) (:'a))))
                 (Assign 1 (Const (--((n2w 1):'a word))));
               Assign 3 (Op Sub [Lookup TriggerGC; Lookup NextFree]);
               If Lower 3 (Reg 1)
                 (list_Seq [SilentFFI c 3 (FST (adjust_sets names),
                              insert 1 one (SND (adjust_sets
                                names)));
                            Alloc 1 (adjust_sets names);
                            SilentFFI c 3 (adjust_sets names)])
                              Skip]`;;

let MakeBytes_def = cake_define
  `MakeBytes n =
     (list_Seq [Assign n ((\sh e n. Shift sh e (Const (n2w n))) Lsr
       (Var n) 2);
               Assign n (Op Or [Var n; (\sh e n. Shift sh e (Const
                 (n2w n))) Lsl (Var n) 8]);
               Assign n (Op Or [Var n; (\sh e n. Shift sh e (Const
                 (n2w n))) Lsl (Var n) 16]);
               if dimindex (:'a) = 32 then Skip else
                 Assign n (Op Or [Var n; (\sh e n. Shift sh e
                   (Const (n2w n))) Lsl (Var n) 32])]:'a
                   wordLang_prog)`;;

let SmallLsr_def = cake_define
  `SmallLsr e n = (if n = 0 then e else (\sh e n. Shift sh e (Const
  (n2w n))) Lsr e n)`;;

let WriteLastByte_aux_def = cake_define
  `WriteLastByte_aux offset a b n p =
     If (EQUAL) n (Imm offset) Skip
       (Seq (Inst (Mem Store8 b (Addr a offset))) p)`;;

let WriteLastBytes_def = cake_define
  `WriteLastBytes a b n =
     WriteLastByte_aux ((n2w 0):'a word) a b n (
       WriteLastByte_aux (n2w 1) a b n (
         WriteLastByte_aux (n2w 2) a b n (
           WriteLastByte_aux (n2w 3) a b n (
             if dimindex (:'a) = 32 then Skip else
             WriteLastByte_aux (n2w 4) a b n (
               WriteLastByte_aux (n2w 5) a b n (
                 WriteLastByte_aux (n2w 6) a b n (
                   WriteLastByte_aux (n2w 7) a b n Skip)))))))`;;

let RefByte_code_def = cake_define
  `RefByte_code c =
       (let limit = MIN (2 EXP data_to_word_config_len_size c)
         (dimword (:'a) DIV 16) in
       let h = Op Add [(\sh e n. Shift sh e (Const (n2w n))) Lsr (Var
         2) 2; Const bytes_in_word] in
       let x = SmallLsr h (dimindex (:'a) - 63) in
       let y = (\sh e n. Shift sh e (Const (n2w n))) Lsl h (dimindex
         (:'a) - (backend_common_word_shift) (:'a) -
         data_to_word_config_len_size c) in
         list_Seq
           [BignumHalt 2;
            Assign 1 x;
            AllocVar c limit (fromList [one; one; one]);
            Assign 5 ((\sh e n. Shift sh e (Const (n2w n))) Lsr h
              ((backend_common_word_shift) (:'a)));
            Assign 7 ((\sh e n. Shift sh e (Const (n2w n))) Lsl (Var
              5) 2);
            Assign 9 (Lookup NextFree);
            Assign 1 (Op Add [Var 9;
                              (\sh e n. Shift sh e (Const (n2w n)))
                                Lsl (Var 5) ((backend_common_word_shift)
                                (:'a))]);
            Set NextFree (Op Add [Var 1; Const bytes_in_word]);
            Assign 3 (Op Or [(\sh e n. Shift sh e (Const (n2w n)))
              Lsl (Op Sub [Var 9; Lookup CurrHeap])
                (shift_length c - (backend_common_word_shift) (:'a));
                  Const ((n2w 1):'a word)]);
            Assign 5 (Op Or [Op Or [y; Const (n2w 7)]; Var 6]);
            MakeBytes 4;
            Store (Var 9) 5;
            Assign 11 (Op And [(\sh e n. Shift sh e (Const (n2w n)))
              Lsr (Var 2) 2;
                              Const (bytes_in_word - (n2w 1))]);
            Assign 13 (Const (n2w 0));
            Store (Var 1) 13;
            WriteLastBytes 1 4 11;
            Assign 7 (Op Sub [Var 7; Const (n2w 4)]);
            Call NONE (SOME Replicate_location)
              [0; 9; 4; 7; 3] NONE]:'a wordLang_prog)`;;

let maxout_bits_code_def = cake_define
  `Maxout_bits_code rep_len k dest n =
     (If Lower n (Imm (n2w (2 EXP rep_len - 1)))
       (Assign dest (Op Or [Var dest; (\sh e n. Shift sh e (Const
         (n2w n))) Lsl (Var n) k]))
       (Assign dest (Op Or [Var dest; Const (all_ones (k +
         rep_len) k)])):'a wordLang_prog)`;;

let make_ptr_bits_code_def = cake_define
  `Make_ptr_bits_code c tag len dest =
     (list_Seq [Assign dest (Op Or
        [Const (n2w 1); (\sh e n. Shift sh e (Const (n2w n))) Lsl (Op
          Sub [Lookup NextFree; Lookup CurrHeap])
            (shift_length c - (backend_common_word_shift) (:'a))]);
         Maxout_bits_code (data_to_word_config_tag_bits c) (1 +
           data_to_word_config_len_bits c) dest tag;
         Maxout_bits_code (data_to_word_config_len_bits c) 1 dest
           len]:'a wordLang_prog)`;;

let FromList_code_def = cake_define
  `FromList_code c =
     (let limit = MIN (2 EXP data_to_word_config_len_size c) (dimword
       (:'a) DIV 16) in
     let h = (\sh e n. Shift sh e (Const (n2w n))) Lsl (Var 2)
       (dimindex (:'a) - data_to_word_config_len_size c - 2) in
       If (EQUAL) 2 (Imm (n2w 0))
         (list_Seq [Assign 6 (Op Add [Var 6; Const ((n2w 2):'a
           word)]);
                    Return 0 [6]])
         (list_Seq
           [BignumHalt 2;
            Assign 1 (Var 2); AllocVar c limit (fromList [one; one;
              one]);
            Assign 1 (Lookup NextFree);
            Assign 5 (Op Or [h; Const (n2w 3); Var 6]);
            Assign 7 ((\sh e n. Shift sh e (Const (n2w n))) Lsr (Var
              2) 2);
            Assign 9 ((\sh e n. Shift sh e (Const (n2w n))) Lsr (Var
              6) 4);
            Make_ptr_bits_code c 9 7 3;
            Call NONE (SOME FromList1_location) [0; 1; 4; 2; 3; 5]
              NONE]):'a wordLang_prog)`;;

let FromList1_code_def = cake_define
  `FromList1_code c =
     (list_Seq
       [Store (Var 2) 10;
        Assign 2 (Op Add [Var 2; Const bytes_in_word]);
        If (EQUAL) 6 (Imm (n2w 0))
          (list_Seq
             [Set NextFree (Var 2);
              Return 0 [8]])
          (list_Seq
             [Assign 4 (real_addr c 4);
              Assign 10 (Load (Op Add [Var 4; Const bytes_in_word]));
              Assign 4 (Load (Op Add [Var 4; Const ((n2w 2) *
                bytes_in_word)]));
              Assign 6 (Op Sub [Var 6; Const (n2w 4)]);
              Call NONE (SOME FromList1_location) [0; 2; 4; 6; 8;
                10] NONE])]:'a wordLang_prog)`;;

let RefArray_code_def = cake_define
  `RefArray_code c =
         (list_Seq
           [Assign 1 ((\sh e n. Shift sh e (Const (n2w n))) Lsl (Op
             Add [((\sh e n. Shift sh e (Const (n2w n))) Lsr (Var 2) 2);
             Const (n2w 1)])
                       ((backend_common_word_shift) (:'a)));
            Set TriggerGC (Op Sub [Lookup TriggerGC; Var 1]);
            Assign 1 (Op Sub [Lookup EndOfHeap; Var 1]);
            Set EndOfHeap (Var 1);
            Assign 3 (Op Or [(\sh e n. Shift sh e (Const (n2w n)))
              Lsl (Op Sub [Var 1; Lookup CurrHeap])
                (shift_length c - (backend_common_word_shift) (:'a));
                  Const ((n2w 1):'a word)]);
            Assign 5 (Op Or [(\sh e n. Shift sh e (Const (n2w n)))
              Lsl (Var 2)
                              (dimindex (:'a) -
                                data_to_word_config_len_size c - 2);
                             Const (make_header c (n2w 2) 0)]);
            Store (Var 1) 5;
            Call NONE (SOME Replicate_location)
               [0; 1; 4; 2; 3] NONE]:'a wordLang_prog)`;;

let replicate_code_def = cake_define
  `Replicate_code =
     (If (EQUAL) 6 (Imm (n2w 0)) (Return 0 [8])
       (list_Seq [Assign 2 (Op Add [Var 2; Const (bytes_in_word)]);
                  Store (Var 2) 4;
                  Assign 6 (Op Sub [Var 6; Const (n2w 4)]);
                  Call NONE (SOME Replicate_location) [0; 2; 4; 6;
                    8] NONE]):'a wordLang_prog)`;;

let AddNumSize_def = cake_define
  `AddNumSize c src =
     (If (EQUAL) (adjust_var src) (Imm (n2w 0)) Skip
       (If Test (adjust_var src) (Imm (n2w 1))
          (Assign 1 (Op Add [Var 1; Const (n2w 4)]))
        (Assign 1 (Op Add [Var 1;
          ((\sh e n. Shift sh e (Const (n2w n))) Lsl ((\sh e n. Shift
            sh e (Const (n2w n))) Lsr
             (Load (real_addr c (adjust_var src)))
                (dimindex (:'a) - data_to_word_config_len_size
                  c))) 2]))):'a wordLang_prog)`;;

let AnyHeader_def = cake_define
  `AnyHeader c r a t1 t2 t3 =
     If (EQUAL) r (Imm ((n2w 0):'a word))
       (list_Seq [Assign 7 (Const (n2w 0));
                  Set (Temp t1) (Var r);
                  Set (Temp t2) (Var r);
                  Set (Temp t3) (Var r)])
    (If NotTest r (Imm (n2w 1))
       (list_Seq
         [Assign 7 (real_addr c r);
          Set (Temp t2) (Op Add [Var 7; Const bytes_in_word]);
          Set (Temp t1) (Op Add
            [(\sh e n. Shift sh e (Const (n2w n))) Lsl ((\sh e n.
              Shift sh e (Const (n2w n))) Lsr (Load (Var 7)) ((dimindex
              (:'a)) - data_to_word_config_len_size c)) 1;
             Op And [Const (n2w 1); (\sh e n. Shift sh e (Const (n2w
               n))) Lsr (Load (Var 7)) 4]]);
          Set (Temp t3) (Const (n2w 0))])
    (If NotLess r (Imm (n2w 0))
       (list_Seq
         [Set (Temp t1) (Const (n2w 2));
          Set (Temp t2) (Lookup (if a then OtherHeap else NextFree));
          Set (Temp t3) ((\sh e n. Shift sh e (Const (n2w n))) Lsr
            (Var r) 2);
          Assign 7 (Const (n2w 0))])
       (list_Seq
         [Set (Temp t1) (Const (n2w 3));
          Set (Temp t2) (Lookup (if a then OtherHeap else NextFree));
          Set (Temp t3) (Op Sub [Const (n2w 0); (\sh e n. Shift sh e
            (Const (n2w n))) Asr (Var r) 2]);
          Assign 7 (Const (n2w 0))])))`;;

let ShiftVar_def = cake_define
  `ShiftVar sh v n =
     (if sh = Ror then
       (let m = if n < dimindex (:'a) then n else n MOD (dimindex
         (:'a)) in
          if m = 0 then Var v else (\sh e n. Shift sh e (Const (n2w
            n))) sh (Var v) m) else if n = 0 then Var v else if dimindex
            (:'a) <= n then
       if sh = Asr then (\sh e n. Shift sh e (Const (n2w n))) sh
         (Var v) (dimindex (:'a) - 1) else Const (n2w 0) else ((\sh e
         n. Shift sh e (Const (n2w n))) sh (Var v) n):'a
         wordLang_exp)`;;

let AnyArith_code_def = cake_define
  `AnyArith_code c = (list_Seq [
       Assign 1 (Const (n2w 4));
       AddNumSize c 0;
       AddNumSize c 1;
       Set (Temp (n2w 29)) (Var 1);
       AllocVar c (2 EXP data_to_word_config_len_size c) (fromList
         [one; one; one]);
       AnyHeader c 2 F (n2w 0) (n2w 31) (n2w 12);
       AnyHeader c 4 T (n2w 1) (n2w 30) (n2w 11);
       Get 1 (Temp (n2w 11));
       Store (Lookup OtherHeap) 1;
       Get 1 (Temp (n2w 12));
       Store (Lookup NextFree) 1;
       Get 1 (Temp (n2w 29));
       Assign 2 (Lookup NextFree);
       Set (Temp (n2w 29)) (Var 2);
       Set (Temp (n2w 3)) ((\sh e n. Shift sh e (Const (n2w n))) Lsr
         (Var 6) 2);
       Assign 3 (Const (n2w 0));
       Call (SOME ([0],(fromList [one],LN),Skip,AnyArith_location,2))
         (SOME Replicate_location) [2; 3; 1; 0] NONE;
       Set (Temp (n2w 29)) (Op Add [Lookup (Temp (n2w 29)); Const
         bytes_in_word]);
       Call (SOME ([1],(fromList [one],LN),Skip,AnyArith_location,3))
         (SOME Bignum_location) [] NONE;
       Get 1 (Temp (n2w 10));
       If Test 1 (Reg 1) (Return 0 [1]) Skip;
       Assign 3 (Load (Op Add [Lookup NextFree; Const
         bytes_in_word]));
       If (EQUAL) 1 (Imm (n2w 2))
         (Seq (Assign 5 ((\sh e n. Shift sh e (Const (n2w n))) Lsr
           (Var 3) (dimindex (:'a) - 3)))
              (If Test 5 (Reg 5)
                 (Seq (Assign 1 ((\sh e n. Shift sh e (Const (n2w
                   n))) Lsl (Var 3) 2))
                      (Return 0 [1]))
                 Skip))
         (If (EQUAL) 1 (Imm (n2w 3))
           (Seq (Assign 5 ((\sh e n. Shift sh e (Const (n2w n))) Lsr
             (Op Sub [Var 3; Const (n2w 1)])
                             (dimindex (:'a) - 3)))
                (If Test 5 (Reg 5)
                   (Seq (Assign 1 (Op Sub [Const (n2w 0); (\sh e n.
                     Shift sh e (Const (n2w n))) Lsl (Var 3) 2]))
                        (Return 0 [1]))
                   Skip))
           (Assign 5 (Const (n2w 0))));
       Assign 5 (Lookup NextFree);
       Assign 6 (ShiftVar Lsr 1 1);
       Assign 8 (Op And [Var 1; Const (n2w 1)]);
       Assign 7 (Op Or [Const (n2w 0b1111);
                        ShiftVar Lsl 6 (dimindex (:'a) -
                          data_to_word_config_len_size c);
                        ShiftVar Lsl 8 4]);
       Store (Var 5) 7;
       Assign 1 (Op Sub [Var 5; Lookup CurrHeap]);
       Assign 1 (Op Or [ShiftVar Lsl 1 (shift_length c -
         (backend_common_word_shift) (:'a)); Const (n2w 1)]);
       Set NextFree (Op Add [Var 5; Const bytes_in_word;
                             ShiftVar Lsl 6
                               ((backend_common_word_shift) (:'a))]);
       Return 0 [1]]:'a wordLang_prog)`;;

let add_code_def = cake_define
  `Add_code = (Seq (Assign 6 (Const (n2w (4 * 0))))
                  (Call NONE (SOME AnyArith_location) [0; 2; 4; 6]
                    NONE):'a wordLang_prog)`;;

let sub_code_def = cake_define
  `Sub_code = (Seq (Assign 6 (Const (n2w (4 * 1))))
                  (Call NONE (SOME AnyArith_location) [0; 2; 4; 6]
                    NONE):'a wordLang_prog)`;;

let mul_code_def = cake_define
  `Mul_code = (Seq (Assign 6 (Const (n2w (4 * 4))))
                  (Call NONE (SOME AnyArith_location) [0; 2; 4; 6]
                    NONE):'a wordLang_prog)`;;

let div_code_def = cake_define
  `Div_code = (Seq (Assign 6 (Const (n2w (4 * 5))))
                  (Call NONE (SOME AnyArith_location) [0; 2; 4; 6]
                    NONE):'a wordLang_prog)`;;

let mod_code_def = cake_define
  `Mod_code = (Seq (Assign 6 (Const (n2w (4 * 6))))
                  (Call NONE (SOME AnyArith_location) [0; 2; 4; 6]
                    NONE):'a wordLang_prog)`;;

let install_code_def = cake_define
  `Install_code c =
       (list_Seq [Assign 1 (Lookup BitmapBuffer);
                 Assign 3 (Lookup CodeBuffer);
                 Set BitmapBuffer (Var 2);
                 Set CodeBuffer (Var 4);
                 Install 3 4 1 2 (LS one,LN);
                 Return 0 [3]]:'a wordLang_prog)`;;

let InstallCode_code_def = cake_define
  `InstallCode_code c =
        (If Test 2 (Imm (n2w 1))
         (Seq (Assign 2 (Lookup BitmapBuffer))
              (Call NONE (SOME InstallData_location) [0; 2; 4; 6]
                NONE))
         (list_Seq [Assign 3 (real_addr c 2);
                    Assign 2 (Load (Op Add [Var 3; Const
                      bytes_in_word]));
                    Assign 2 (ShiftVar Lsr 2 2);
                    CodeBufferWrite 6 2;
                    Assign 6 (Op Add [Var 6; Const (n2w 1)]);
                    Assign 2 (Load (Op Add [Var 3; Const ((n2w 2) *
                      bytes_in_word)]));
                    Call NONE (SOME InstallCode_location) [0; 2;
                      4; 6] NONE]):'a wordLang_prog)`;;

let InstallData_code_def = cake_define
  `InstallData_code c =
        (If Test 4 (Imm (n2w 1))
         (list_Seq [Call NONE (SOME Install_location) [0; 2; 6]
           NONE])
         (list_Seq [Assign 3 (real_addr c 4);
                    Assign 4 (Load (Op Add [Var 3; Const
                      bytes_in_word]));
                    Assign 4 (real_addr c 4);
                    Assign 4 (Load (Op Add [Var 4; Const
                      bytes_in_word]));
                    DataBufferWrite 2 4;
                    Assign 2 (Op Add [Var 2; Const bytes_in_word]);
                    Assign 4 (Load (Op Add [Var 3; Const ((n2w 2) *
                      bytes_in_word)]));
                    Call NONE (SOME InstallData_location) [0; 2;
                      4; 6] NONE]):'a wordLang_prog)`;;

let compare1_code_def = cake_define
  `Compare1_code =
     If (EQUAL) 2 (Imm (n2w 0))
       (Seq (Assign 2 (Const (n2w 1))) (Return 0 [2]))
       (list_Seq
          [Assign 8 (Load (Var 4));
           Assign 9 (Load (Var 6));
           If (EQUAL) 8 (Reg 9)
             (list_Seq
                [Assign 2 (Op Sub [Var 2; Const (n2w 1)]);
                 Assign 4 (Op Sub [Var 4; Const bytes_in_word]);
                 Assign 6 (Op Sub [Var 6; Const bytes_in_word]);
                 Call NONE (SOME Compare1_location) [0; 2; 4; 6]
                   NONE])
             (If Lower 8 (Reg 9)
               (Seq (Assign 2 (Const (n2w 0))) (Return 0 [2]))
               (Seq (Assign 2 (Const (n2w 2))) (Return 0 [2])))])`;;

let compare_code_def = cake_define
  `Compare_code c =
     If Test 2 (Imm (n2w 1))
       (list_Seq [Assign 1 (Load (real_addr c 4));
                  If Test 1 (Imm (n2w 16))
                    (Seq (Assign 2 (Const (n2w 0))) (Return 0 [2]))
                    (Seq (Assign 2 (Const (n2w 2))) (Return 0 [2]))])
    (If Test 4 (Imm (n2w 1))
       (list_Seq [Assign 1 (Load (real_addr c 2));
                  If Test 1 (Imm ((n2w 16):'a word))
                    (Seq (Assign 2 (Const (n2w 2))) (Return 0 [2]))
                    (Seq (Assign 2 (Const (n2w 0))) (Return 0 [2]))])
       (list_Seq [Assign 11 (real_addr c 2);
                  Assign 1 (Load (Var 11));
                  Assign 13 (real_addr c 4);
                  Assign 3 (Load (Var 13));
                  Assign 6 ((\sh e n. Shift sh e (Const (n2w n))) Lsr
                    (Var 1) ((dimindex (:'a) -
                    data_to_word_config_len_size c)));
                  Assign 8 ((\sh e n. Shift sh e (Const (n2w n))) Lsr
                    (Var 3) ((dimindex (:'a) -
                    data_to_word_config_len_size c)));
                  If (EQUAL) 1 (Reg 3)
                    (list_Seq
                      [Assign 2 (Op Add [Var 11; (\sh e n. Shift sh e
                        (Const (n2w n))) Lsl (Var 6)
                        ((backend_common_word_shift) (:'a))]);
                       Assign 4 (Op Add [Var 13; (\sh e n. Shift sh e
                         (Const (n2w n))) Lsl (Var 6)
                         ((backend_common_word_shift) (:'a))]);
                       If Test 1 (Imm (n2w 16))
                        (Call NONE (SOME Compare1_location) [0; 6; 2;
                          4] NONE)
                        (Call NONE (SOME Compare1_location) [0; 6; 4;
                          2] NONE)])
                    (If Test 1 (Imm (n2w 16))
                       (If Test 3 (Imm (n2w 16))
                          (If Lower 6 (Reg 8)
                             (Seq (Assign 2 (Const (n2w 0))) (Return
                               0 [2]))
                             (Seq (Assign 2 (Const (n2w 2))) (Return
                               0 [2])))
                          (Seq (Assign 2 (Const (n2w 2))) (Return 0
                            [2])))
                       (If Test 3 (Imm (n2w 16))
                          (Seq (Assign 2 (Const (n2w 0))) (Return 0
                            [2]))
                          (If Lower 6 (Reg 8)
                             (Seq (Assign 2 (Const (n2w 2))) (Return
                               0 [2]))
                             (Seq (Assign 2 (Const (n2w 0)))
                               (Return 0 [2])))))]))`;;

let equal1_code_def = cake_define
  `Equal1_code =
     list_Seq [
       If (EQUAL) 2 (Imm (n2w 0))
         (Seq (Assign 2 (Const (n2w 1))) (Return 0 [2])) Skip;
       Assign 1 (Load (Var 4));
       Assign 3 (Load (Var 6));
       Call (SOME ([5],(list_insert [0; 2; 4; 6]
         LN,LN),Skip,Equal1_location,2))
         (SOME Equal_location) [1; 3] NONE;
       If (EQUAL) 5 (Imm (n2w 1)) Skip (Return 0 [5]);
       Assign 2 (Op Sub [Var 2; Const (n2w 1)]);
       Assign 4 (Op Add [Var 4; Const bytes_in_word]);
       Assign 6 (Op Add [Var 6; Const bytes_in_word]);
       Call NONE (SOME Equal1_location) [0; 2; 4; 6] NONE]`;;

let equal_code_def = cake_define
  `Equal_code c =
     list_Seq [
       If (EQUAL) 2 (Reg 4)
         (Seq (Assign 2 (Const ((n2w 1):'a word))) (Return 0 [2]))
           Skip;
       Assign 1 (Op And [Var 2; Var 4]);
       If Test 1 (Imm (n2w 1))
         (Seq (Assign 2 (Const (n2w 0))) (Return 0 [2])) Skip;
       Assign 20 (real_addr c 2);
       Assign 40 (real_addr c 4);
       Assign 21 (Load (Var 20));
       Assign 41 (Load (Var 40));
       If Test 21 (Imm (n2w 0b1100)) (list_Seq
           [Assign 1 (Op And [Var 21; Const (tag_mask c || (n2w
             2))]);
            If (EQUAL) 1 (Imm (n2w (16 * closure_tag + 2)))
              (Seq (Assign 2 (Const (n2w 1))) (Return 0 [2])) Skip;
            If (EQUAL) 1 (Imm (n2w (16 * partial_app_tag + 2)))
              (Seq (Assign 2 (Const (n2w 1))) (Return 0 [2])) Skip;
            If (EQUAL) 21 (Reg 41)
              Skip (Seq (Assign 2 (Const (n2w 0))) (Return 0 [2]));
            Assign 6 (ShiftVar Lsr 21 ((dimindex (:'a) -
              data_to_word_config_len_size c)));
            Assign 20 (Op Add [Var 20; Const bytes_in_word]);
            Assign 40 (Op Add [Var 40; Const bytes_in_word]);
            Call NONE (SOME Equal1_location) [0; 6; 20; 40] NONE])
         Skip;
       If (EQUAL) 21 (Reg 41) Skip
         (Seq (Assign 2 (Const (n2w 0))) (Return 0 [2]));
       If Test 21 (Imm (n2w 4))
         (Seq (Assign 2 (Const (n2w 0))) (Return 0 [2])) Skip;
       Assign 1 (Op And [Var 21; Const (n2w 24)]);
       If (EQUAL) 1 (Imm (n2w 16))
         (Seq (Assign 2 (Const (n2w 0))) (Return 0 [2])) Skip;
       Assign 6 (ShiftVar Lsr 21 ((dimindex (:'a) -
         data_to_word_config_len_size c)));
       Assign 2 (Op Add [Var 20; ShiftVar Lsl 6
         ((backend_common_word_shift) (:'a))]);
       Assign 4 (Op Add [Var 40; ShiftVar Lsl 6
         ((backend_common_word_shift) (:'a))]);
       Call NONE (SOME Compare1_location) [0; 6; 2; 4] NONE]`;;

let LongDiv_code_def = cake_define
  `LongDiv_code c =
     (if data_to_word_config_has_longdiv c then
       list_Seq [Inst (Arith (LongDiv 1 3 2 4 6));
                 Set (Temp (n2w 28)) (Var 3);
                 Return 0 [1]] else
       Seq (Assign 10 (Const ((n2w 0):'a word)))
      (Seq (Assign 11 (Const (n2w (dimindex (:'a)))))
           (Call NONE (SOME LongDiv1_location) [0; 11; 6; 10; 10;
             4; 2] NONE)))`;;

let LongDiv1_code_def = cake_define
  `LongDiv1_code c =
     (if data_to_word_config_has_longdiv c then Skip else
       If Test 2 (Reg 2)
         (Seq (Set (Temp (n2w 28)) (Var 10):'a wordLang_prog) (Return
           0 [8]))
         (list_Seq [Assign 6 (Op Or [ShiftVar Lsr 6 1;
                              ShiftVar Lsl 4 (dimindex (:'a) - 1)]);
                    Assign 4 (ShiftVar Lsr 4 1);
                    Assign 8 (ShiftVar Lsl 8 1);
                    Assign 2 (Op Sub [Var 2; Const ((n2w 1):'a
                      word)]);
                    If Lower 12 (Reg 4)
                      (Call NONE (SOME LongDiv1_location)
                        [0; 2; 4; 6; 8; 10; 12] NONE) Skip;
                    If (EQUAL) 12 (Reg 4)
                      (If Lower 10 (Reg 6)
                         (Call NONE (SOME LongDiv1_location)
                            [0; 2; 4; 6; 8; 10; 12] NONE) Skip) Skip;
                    Assign 8 (Op Add [Var 8; Const (n2w 1)]);
                    Assign 16 (Op Xor [Var 6; Const (--(n2w 1))]);
                    Assign 14 (Op Xor [Var 4; Const (--(n2w 1))]);
                    Assign 1 (Const (n2w 1));
                    Inst (Arith (AddCarry 10 10 16 1));
                    Inst (Arith (AddCarry 12 12 14 1));
                    Call NONE (SOME LongDiv1_location) [0; 2; 4;
                      6; 8; 10; 12] NONE]))`;;

let append_code_def = cake_define
  `Append_code c =
     (match encode_header c 0 2 with NONE -> (Skip:'a wordLang_prog)
       | SOME (header:'a word) ->
         If Test 4 (Imm (n2w 1)) (Return 0 [2])
           (list_Seq
             [Set (Temp (n2w 0)) (Var 2);
              Set (Temp (n2w 1)) (Var 4);
              Assign 1 (Lookup NextFree);
              Assign 3 (Const header);
              Assign 5 (Op Sub [Lookup TriggerGC; Var 1]);
              Assign 7 (Op Or [(\sh e n. Shift sh e (Const (n2w n)))
                Lsl (Op Sub [Var 1; Lookup CurrHeap])
                              (shift_length c -
                                (backend_common_word_shift) (:'a));
                              Const ((n2w 1) || (word_bits
                                (small_shift_length c - 1) 0)
                              (ptr_bits c 0 2))]);
              Set (Temp (n2w 2)) (Var 7);
              Call NONE (SOME AppendMainLoop_location) [0; 1; 4;
                3; 5; 7] NONE]))`;;

let AppendMainLoop_code_def = cake_define
  `AppendMainLoop_code c =
     (list_Seq
       [Assign 1 (real_addr c 4);
        Assign 3 (Load (Op Add [Var 1; Const bytes_in_word]));
        Assign 5 (Load (Op Add [Var 1; Const ((n2w 2) *
          bytes_in_word)]));
        If Lower 8 (Imm ((n2w 3) * bytes_in_word))
          (Seq (Assign 1 (Const (n2w 0)))
               (Call NONE (SOME AppendLenLoop_location) [0; 4; 1]
                 NONE)) Skip;
        Store (Var 2) 6;
        Store (Op Add [Var 2; Const bytes_in_word]) 3;
        If Test 5 (Imm (n2w 1)) Skip
          (list_Seq
            [Assign 10 (Op Add [Var 10;
               Const (n2w (3 * 2 EXP shift_length c))]);
             Assign 8 (Op Sub [Var 8; Const ((n2w 3) *
               bytes_in_word)]);
             Store (Op Add [Var 2; Const ((n2w 2) * bytes_in_word)])
               10;
             Assign 2 (Op Add [Var 2; Const ((n2w 3) *
               bytes_in_word)]);
             Call NONE (SOME AppendMainLoop_location) [0; 2; 5; 6; 8;
               10] NONE]);
        Assign 1 (Lookup (Temp (n2w 0)));
        Assign 3 (Lookup (Temp (n2w 2)));
        Store (Op Add [Var 2; Const ((n2w 2) * bytes_in_word)]) 1;
        Set NextFree (Op Add [Var 2; Const ((n2w 3) *
          bytes_in_word)]);
        Return 0 [3]]:'a wordLang_prog)`;;

let AppendLenLoop_code_def = cake_define
  `AppendLenLoop_code c =
     If Test 2 (Imm (n2w 1))
       (list_Seq
         [Assign 1 (Op Sub [Lookup TriggerGC; Lookup NextFree]);
          Assign 1 (Op Add [Var 4; ShiftVar Lsr 1
            ((backend_common_word_shift) (:'a) - 2)]);
          Assign 4 (Lookup (Temp (n2w 0)));
          Assign 2 (Lookup (Temp (n2w 1)));
          AllocVar c (dimword (:'ga) DIV 8 - 1) (fromList [one;
            one]);
          Call NONE (SOME Append_location) [0; 4; 2] NONE])
       (list_Seq
         [Assign 2 (Load (Op Add [real_addr c 2; Const ((n2w 2) *
           bytes_in_word)]));
          Assign 4 (Op Add [Var 4; Const ((n2w 12):'a word)]);
          Call NONE (SOME AppendLenLoop_location) [0; 2; 4] NONE])`;;

let XorLoop_code_def = cake_define
  `XorLoop_code =
     (If Lower 6 (Imm (n2w 2))
       (If (EQUAL) 6 (Imm (n2w 0))
          (list_Seq [Assign 1 (Const (n2w 2));
                     Return 0 [1]])
          (list_Seq [Assign 5 (Load (Var 4));
                     Assign 3 (Load (Var 2));
                     Assign 7 (Op Xor [Var 5; Var 3]);
                     Store (Var 2) 7;
                     Assign 1 (Const (n2w 2));
                     Return 0 [1]]))
       (list_Seq [Assign 5 (Load (Var 4));
                  Assign 3 (Load (Var 2));
                  Assign 9 (Load (Op Add [Var 4; Const
                    bytes_in_word]));
                  Assign 7 (Load (Op Add [Var 2; Const
                    bytes_in_word]));
                  Assign 6 (Op Sub [Var 6; Const (n2w 2)]);
                  Assign 5 (Op Xor [Var 5; Var 3]);
                  Assign 9 (Op Xor [Var 9; Var 7]);
                  Store (Var 2) 5;
                  Store (Op Add [Var 2; Const bytes_in_word]) 9;
                  Assign 4 (Op Add [Var 4; Const ((n2w 2) *
                    bytes_in_word)]);
                  Assign 2 (Op Add [Var 2; Const ((n2w 2) *
                    bytes_in_word)]);
                  Call NONE (SOME XorLoop_location) [0; 2; 4; 6]
                    NONE]):'a wordLang_prog)`;;

let StringCmpLoop_code_def = cake_define
  `StringCmpLoop_code =
     (If (EQUAL) 6 (Imm bytes_in_word)
       (Return 0 [8; 10])
       (list_Seq
          [Inst (Mem Load8 1 (Addr 2 (n2w 0)));
           Inst (Mem Load8 3 (Addr 4 (n2w 0)));
           If NotEqual 1 (Reg 3) (Return 0 [1; 3]) Skip;
           Assign 2 (Op Add [Var 2; Const (n2w 1)]);
           Assign 4 (Op Add [Var 4; Const (n2w 1)]);
           Assign 6 (Op Sub [Var 6; Const (n2w 1)]);
           Call NONE (SOME StringCmpLoop_location) [0; 2; 4; 6; 8;
             10] NONE]):'a wordLang_prog)`;;

let get_names_def = cake_define
  `(data_to_word_get_names NONE = LN) /\
   (data_to_word_get_names (SOME x) = x)`;;
hol4_overload "get_names" "data_to_word_get_names";;

let LoadWord64_def = cake_define
  `LoadWord64 c i j =
     (Assign i (Load (Op Add [real_addr c j; Const
       bytes_in_word])):'a wordLang_prog)`;;

let LoadBignum_def = cake_define
  `LoadBignum c header word1 k = (list_Seq [
     Assign word1 (real_addr c k);
     Assign header (Load (Var word1));
     Assign word1 (Load (Op Add [Var word1; Const
       bytes_in_word]))]:'a wordLang_prog)`;;

let WriteWord64_def = cake_define
  `WriteWord64 c (header:'a word) dest i =
     (list_Seq [Assign 1 (Lookup NextFree);
               Store (Op Add [Var 1; Const bytes_in_word]) i;
               Assign 3 (Const header);
               Store (Var 1) 3;
               Set NextFree (Op Add [Var 1; Const ((n2w 2) *
                 bytes_in_word)]);
               Assign (adjust_var dest)
                 (Op Or [(\sh e n. Shift sh e (Const (n2w n))) Lsl
                   (Op Sub [Var 1; Lookup CurrHeap])
                           (shift_length c -
                             (backend_common_word_shift) (:'a));
                         Const (n2w 1)])]:'a wordLang_prog)`;;

let WriteWord64_on_32_def = cake_define
  `WriteWord64_on_32 c (header:'a word) dest i1 i2 =
     (list_Seq [Assign 1 (Lookup NextFree);
               Store (Op Add [Var 1; Const bytes_in_word]) i2;
               Store (Op Add [Var 1; Const ((n2w 2) *
                 bytes_in_word)]) i1;
               Assign 3 (Const header);
               Store (Var 1) 3;
               Set NextFree (Op Add [Var 1; Const ((n2w 3) *
                 bytes_in_word)]);
               Assign (adjust_var dest)
                 (Op Or [(\sh e n. Shift sh e (Const (n2w n))) Lsl
                   (Op Sub [Var 1; Lookup CurrHeap])
                           (shift_length c -
                             (backend_common_word_shift) (:'a));
                         Const (n2w 1)])]:'a wordLang_prog)`;;

let WriteWord32_on_32_def = cake_define
  `WriteWord32_on_32 c header dest i1 =
      list_Seq
        [Assign 1 (Lookup NextFree);
         Store (Op Add [Var 1; Const bytes_in_word]) i1;
         Assign 3 (Const header); Store (Var 1) 3;
         Set NextFree (Op Add [Var 1; Const ((n2w 2) *
           bytes_in_word)]);
         Assign (adjust_var dest)
           (Op Or
              [(\sh e n. Shift sh e (Const (n2w n))) Lsl (Op Sub [Var
                1; Lookup CurrHeap])
                 (shift_length c - (backend_common_word_shift)
                   (:'ga)); Const ((n2w 1):'a word)])]`;;

let WordOp64_on_32_def = cake_define
  `WordOp64_on_32 (opw:opw) =
     (match opw with Andw -> list_Seq [Assign 29 (Const (n2w 0));
                         Assign 27 (Const (n2w 0));
                         Assign 33 (Op And [Var 13; Var 23]);
                         Assign 31 (Op And [Var 11; Var 21])] | Orw
                           -> list_Seq [Assign 29 (Const (n2w 0));
                         Assign 27 (Const (n2w 0));
                         Assign 33 (Op Or [Var 13; Var 23]);
                         Assign 31 (Op Or [Var 11; Var 21])] | Xor ->
                           list_Seq [Assign 29 (Const (n2w 0));
                         Assign 27 (Const (n2w 0));
                         Assign 33 (Op Xor [Var 13; Var 23]);
                         Assign 31 (Op Xor [Var 11; Var 21])] | Add
                           -> list_Seq [Assign 29 (Const (n2w 0));
                         Assign 27 (Const (n2w 0));
                         Inst (Arith (AddCarry 33 13 23 29));
                         Inst (Arith (AddCarry 31 11 21 29))] | Sub
                           -> list_Seq [Assign 29 (Const (n2w 1));
                         Assign 27 (Op Xor [Const (--(n2w 1)); Var
                           23]);
                         Inst (Arith (AddCarry 33 13 27 29));
                         Assign 27 (Op Xor [Const (--(n2w 1)); Var
                           21]);
                         Inst (Arith (AddCarry 31 11 27 29))])`;;

let WordShift64_on_32_def = cake_define
  `WordShift64_on_32 sh n = list_Seq
     (if sh = Ror then
       (let n = n MOD 64 in
         (if n < 32 then
            [Assign 33 (Op Or [ShiftVar Lsl 11 (32 - n);
                              ShiftVar Lsr 13 n]);
             Assign 31 (Op Or [ShiftVar Lsl 13 (32 - n);
                              ShiftVar Lsr 11 n])] else
            [Assign 33 (Op Or [ShiftVar Lsl 13 (64 - n);
                              ShiftVar Lsr 11 (n - 32)]);
             Assign 31 (Op Or [ShiftVar Lsl 11 (64 - n);
                              ShiftVar Lsr 13 (n - 32)])])) else
       if n < 32 then
         (match sh with Lsl -> [Assign 33 (ShiftVar sh 13 n);
                    Assign 31 (Op Or [ShiftVar Lsr 13 (32 - n);
                              ShiftVar sh 11 n])] | Lsr -> [Assign 33
                                (Op Or [ShiftVar Lsl 11 (32 - n);
                              ShiftVar sh 13 n]);
                    Assign 31 (ShiftVar sh 11 n)] | Asr -> [Assign 33
                      (Op Or [ShiftVar Lsl 11 (32 - n);
                              ShiftVar Lsr 13 n]);
                    Assign 31 (ShiftVar sh 11 n)] | Ror -> []) else
         (match sh with Lsl -> [Assign 33 (Const (n2w 0)); Assign 31
           (ShiftVar sh 13 (n - 32))] | Lsr -> [Assign 33 (ShiftVar sh
           11 (n - 32)); Assign 31 (Const (n2w 0))] | Asr -> [Assign 33
           (ShiftVar sh 11 (n - 32));
                    Assign 31 (ShiftVar sh 11 32)] | Ror -> []))`;;

let smallnum_def = cake_define
  `Smallnum i =
     (if i < 0 then (n2w 0) - n2w (num_of_int (4 * (0 - i))) else
       n2w (num_of_int (4 * i)))`;;

(* HOL4 overload (expanded in the port):
     FALSE_CONST = Const (n2w 2:'a word) *)
(* HOL4 overload (expanded in the port):
     TRUE_CONST = Const (n2w 18:'a word) *)

let MemEqList_def = cake_define
  `(MemEqList a [] = (Assign 1 (Const (n2w 18:'a word)):'a
  wordLang_prog)) /\
   (MemEqList a (w :: ws) =
      Seq (Assign 5 (Load (Op Add [Var 3; Const a])))
          (If (EQUAL) 5 (Imm w) (MemEqList (a + bytes_in_word) ws)
            Skip))`;;

let get_gen_size_def = cake_define
  `(get_gen_size [] = bytes_in_word * ((--(n2w 1)):'a word)) /\
   (get_gen_size (x :: xs) =
      (if w2n (bytes_in_word:'a word) * x < dimword (:'a) then
        bytes_in_word * n2w x else bytes_in_word * (--(n2w 1))))`;;

let fp_cmp_inst_def = cake_define
  `fp_cmp_inst FP_Less = FPLess 3 0 1 /\
   fp_cmp_inst FP_LessEqual = FPLessEqual 3 0 1 /\
   fp_cmp_inst FP_Greater = FPLess 3 1 0 /\
   fp_cmp_inst FP_GreaterEqual = FPLessEqual 3 1 0 /\
   fp_cmp_inst FP_Equal = FPEqual 3 0 1`;;

let fp_top_inst_def = cake_define
  `fp_top_inst FP_Fma = FPFma 0 1 2`;;

let fp_bop_inst_def = cake_define
  `fp_bop_inst fpSem$FP_Add =
      match  with
         -> FPAdd 0 0 1
      |  -> FPSub 0 0 1
      |  -> FPMul 0 0 1
      |  -> FPDiv 0 0 1`;;

let fp_uop_inst_def = cake_define
  `fp_uop_inst fpSem$FP_Neg =
      match  with
         -> FPNeg 1 0
      |  -> FPAbs 1 0
      |  -> FPSqrt 1 0`;;

let arg1_def = cake_define
  `data_to_word_arg1 vs f x = (match vs with [v1] -> f v1 | _1 -> x)`;;
hol4_overload "arg1" "data_to_word_arg1";;

let arg2_def = cake_define
  `data_to_word_arg2 vs f x = (match vs with [v1; v2] -> f v1 v2 | _2
  -> x)`;;
hol4_overload "arg2" "data_to_word_arg2";;

let arg3_def = cake_define
  `arg3 vs f x = (match vs with [v1; v2; v3] -> f v1 v2 v3 | _3 -> x)`;;

let arg4_def = cake_define
  `arg4 vs f x = (match vs with [v1; v2; v3; v4] -> f v1 v2 v3 v4 |
  _4 -> x)`;;

(* HOL4 ML code, not ported:
val assign_defs = ref ([]:thm list);
fun assign_Define q = let
  val thm = Define q
  val _ = (assign_defs := thm :: (!assign_defs))
  in thm end;
*)

(* HOL4 ML code, not ported:
val def = assign_Define `
  assign_Const i (l:num) (dest:num) =
*)
        (* bvl_to_bvi compilation ensures that all literal
           constants fit into a machine word *)
(* HOL4 ML code, not ported:
        if i < 0
        then (Assign (adjust_var dest) (Const (0w - n2w (Num (4 * (0 -
          i))))),l)
        else (Assign (adjust_var dest) (Const (n2w (Num (4 * i)))),l)
      : 'a wordLang$prog # num`;
*)

(* HOL4 ML code, not ported:
val def = assign_Define `
  assign_SetGlobalsPtr (c:data_to_word$config) (l:num) (dest:num) v1 =
      (Seq (Set Globals (Var (adjust_var v1)))
      (Seq (Set GlobReal (real_addr c (adjust_var v1)))
           (Assign (adjust_var dest) Unit)),l)
      : 'a wordLang$prog # num`;
*)

(* HOL4 ML code, not ported:
val def = assign_Define `
  assign_Global (c:data_to_word$config) n (l:num) (dest:num) =
      (Assign (adjust_var dest) (Load (Op Add [Lookup GlobReal;
                                               Const (bytes_in_word *
                                                 n2w (n+1))])),l)
      : 'a wordLang$prog # num`;
*)

(* HOL4 ML code, not ported:
val def = assign_Define `
  assign_SetGlobal (c:data_to_word$config) n (l:num) (dest:num) v1 =
      (Seq (Store (Op Add [Lookup GlobReal; Const (bytes_in_word * n2w
        (n+1))])
                  (adjust_var v1))
           (Assign (adjust_var dest) Unit),l)
      : 'a wordLang$prog # num`;
*)

(* HOL4 ML code, not ported:
val def = assign_Define `
  assign_El (c:data_to_word$config) (l:num) (dest:num) v1 v2 =
                         (Assign (adjust_var dest)
                            (Load (Op Add [real_addr c (adjust_var v1);
                                           real_offset c (adjust_var
                                             v2)])),l)
      : 'a wordLang$prog # num`;
*)

(* HOL4 ML code, not ported:
val def = assign_Define `
  assign_ElemAt (c:data_to_word$config) n (l:num) (dest:num) v1 =
                         (Assign (adjust_var dest)
                            (Load (Op Add [real_addr c (adjust_var v1);
                                           Const (bytes_in_word +
                                                  bytes_in_word * n2w
                                                    n)])),l)
      : 'a wordLang$prog # num`;
*)

(* HOL4 ML code, not ported:
val def = assign_Define `
  assign_DerefByte (c:data_to_word$config) (l:num) (dest:num) v1 v2 =
         (list_Seq [
            Assign 1 (Op Add [real_addr c (adjust_var v1);
                              real_byte_offset (adjust_var v2)]);
            Inst (Mem Load8 3 (Addr 1 0w));
            Assign (adjust_var dest) (ShiftN Lsl (Var 3) 2)
          ], l)
      : 'a wordLang$prog # num`;
*)

(* HOL4 ML code, not ported:
val def = assign_Define `
  assign_Update (c:data_to_word$config) (l:num) (dest:num) v1 v2 v3 =
                 (Seq (Store (Op Add [real_addr c (adjust_var v1);
                                      real_offset c (adjust_var v2)])
                             (adjust_var v3))
                      (Assign (adjust_var dest) Unit),l)
      : 'a wordLang$prog # num`;
*)

(* HOL4 ML code, not ported:
val def = assign_Define `
  assign_UpdateThunk ev (c:data_to_word$config) (l:num) (dest:num) v1 v2
    =
      (case ev of
       | NotEvaluated =>
           (Seq (Store (Op Add [real_addr c (adjust_var v1);
                                Const bytes_in_word])
                       (adjust_var v2))
                (Assign (adjust_var dest) Unit),l)
       | Evaluated =>
           (case encode_header c (8 + 6) 1 of
            | NONE => (GiveUp,l)
            | SOME (header:'a word) => (list_Seq
                [Assign 1 (real_addr c (adjust_var v1));
                 Assign 3 (Const header);
                 Store (Var 1) 3;
                 Store (Op Add [Var 1; Const bytes_in_word]) (adjust_var
                   v2);
                 Assign (adjust_var dest) Unit],l)))
      : 'a wordLang$prog # num`;
*)

(* HOL4 ML code, not ported:
val def = assign_Define `
  assign_UpdateByte (c:data_to_word$config) (l:num) (dest:num) v1 v2 v3
    =
      (list_Seq [
          Assign 1 (Op Add [real_addr c (adjust_var v1);
                            real_byte_offset (adjust_var v2)]);
          Assign 3 (ShiftN Lsr (Var (adjust_var v3)) 2);
          Inst (Mem Store8 3 (Addr 1 0w));
          Assign (adjust_var dest) Unit], l)
      : 'a wordLang$prog # num`;
*)

(* HOL4 ML code, not ported:
val def = assign_Define `
  assign_ListAppend (c:data_to_word$config)
            (secn:num) (l:num) (dest:num) (names:num_set option) v1 v2 =
         (case encode_header c 0 2 of
          | NONE => (GiveUp,l)
          | SOME (header:'a word) =>
           (MustTerminate
             (Call (SOME ([adjust_var dest],adjust_sets (get_names
               names),Skip,secn,l))
                (SOME Append_location)
                   [adjust_var v2; adjust_var v1] NONE) :'a
                     wordLang$prog,l+1))
      : 'a wordLang$prog # num`;
*)

(* HOL4 ML code, not ported:
val def = assign_Define `
  assign_Cons (c:data_to_word$config) (l:num) (dest:num) tag args =
                  if LENGTH args = 0 then
                    if tag < dimword (:'a) DIV 16 then
                      (Assign (adjust_var dest) (Const (n2w (16 * tag +
                        2))),l)
                    else (GiveUp,l) (* tag is too big to be represented
                      *)
                  else
                    (case encode_header c (4 * tag) (LENGTH args) of
                     | NONE => (GiveUp,l)
                     | SOME (header:'a word) => (list_Seq
                        [Assign 1 (Lookup NextFree);
                         Assign 3 (Const header);
                         StoreEach 1 (3::MAP adjust_var args) 0w;
                         Assign (adjust_var dest)
                           (Op Or [ShiftN Lsl (Op Sub [Var 1; Lookup
                             CurrHeap])
                                     (shift_length c − shift (:'a));
                                   Const (1w ||
                                           (small_shift_length c − 1 --
                                             0)
                                              (ptr_bits c tag (LENGTH
                                                args)))]);
                         Set NextFree (Op Add [Var 1;
                           Const (bytes_in_word * n2w (LENGTH args +
                             1))])],l))
      : 'a wordLang$prog # num`;
*)

(* HOL4 ML code, not ported:
val def = assign_Define `
  assign_MutCons (c:data_to_word$config) (l:num) (dest:num) tag args =
    case c.gc_kind of
    | Generational _ => (GiveUp,l)
    | _ => assign_Cons (c:data_to_word$config) (l:num) (dest:num) tag
      args
      : 'a wordLang$prog # num`;
*)

(* HOL4 ML code, not ported:
val def = assign_Define `
  assign_ConfigGC (c:data_to_word$config)
            (secn:num) (l:num) (dest:num) (names:num_set option) v1 v2 =
             (list_Seq [SilentFFI c 3 (adjust_sets (get_names names));
                        Assign 1 (Const 0w);
                        Alloc 1 (adjust_sets (get_names names)); (* runs
                          GC *)
                        SilentFFI c 3 (adjust_sets (get_names names));
                        Assign (adjust_var dest) (Const 2w)],l)
      : 'a wordLang$prog # num`;
*)

let getWords_def = cake_define
  `getWords [] aux = (REVERSE aux,[]) /\
   getWords (c :: cs) aux =
     (match c with (b,Word w) -> getWords cs ((b,w) :: aux) | _6
       -> (REVERSE aux,c :: cs))`;;

(* HOL4 termination: \\ fs [getWords_def] \\ rw [] \\ qsuff_tac ‘∀ws
   aux (ws1:(bool # 'a word) list) vs1. (ws1,vs1) = getWords ws aux ⇒
   LENGTH vs1 ≤ LENGTH ws’ THEN1 (rw [] \\ res_tac \\ fs []) \\
   once_rewrite_tac [EQ_SYM_EQ] \\ Induct \\ fs [getWords_def] \\ fs
   [AllCaseEqs()] \\ rw[] \\ res_tac \\ fs [getWords_def] *)
let StoreAnyConsts_def = cake_define_wf
  `MEASURE (\(r1,r2,r3,vs,v). LENGTH vs)`
  `StoreAnyConsts r1 r2 r3 [] v =
     Seq (Set NextFree (Var r2))
         (match SND v with Loc n _10 -> LocValue r1 n | Word w ->
           Assign r1 (if FST v then Op Add [Const w; Var r3] else (Const
           w))) /\
   StoreAnyConsts r1 r2 r3 (v :: vs) w =
     (match ((SND v):'a word_loc) with Loc n _11 -> list_Seq
       [LocValue r1 n;
                            Store (Var r2) r1;
                            Assign r2 (Op Add [Var r2; Const
                              bytes_in_word]);
                            StoreAnyConsts r1 r2 r3 vs w] | _12 ->
                              (let (ws,vs1) = getWords (v :: vs) [] in
              Seq (StoreConsts r2 r3 r2 r3 ws)
                  (StoreAnyConsts r1 r2 r3 vs1 w)))`;;

let lookup_mem_def = cake_define
  `lookup_mem m a =
     (match sptree_lookup a m with NONE -> (F,Word ((n2w 0):'a
       word)) | SOME x -> x)`;;

let byte_len_def = cake_define
  `byte_len (:'a) num_bytes =
     (if dimindex (:'a) = 32 then num_bytes DIV 4 + 1 else
       num_bytes DIV 8 + 1)`;;

let make_byte_header_def = cake_define
  `make_byte_header conf cmp_by_contents len =
   (let tag = if cmp_by_contents then (n2w 0b00111) else (n2w
     0b10111) in
     (if dimindex (:'a) = 32 then n2w (len + 4) << (dimindex
       (:'ga) - 2 - data_to_word_config_len_size conf) || tag else
       n2w (len + 8) << (dimindex (:'ga) - 3 -
       data_to_word_config_len_size conf) || tag):'a word)`;;

let get_lowerbits_def = cake_define
  `get_lowerbits conf x2 =
        match x2 with
          (Word w) ->
        (((word_bits (small_shift_length conf - 1) 0) w) || (n2w 1))
        | _13 -> (n2w 1)`;;

let make_cons_ptr_def = cake_define
  `make_cons_ptr conf nf tag len =
     Word (
             nf << (shift_length conf -
               (backend_common_word_shift) (:'a)) || ((n2w 1):'a
               word) || get_lowerbits conf (Word (ptr_bits conf tag
               len)))`;;

let make_ptr_def = cake_define
  `make_ptr conf nf tag len =
     Word (nf << (shift_length conf - (backend_common_word_shift)
       (:'a)) || ((n2w 1):'a word))`;;

let write_bytes_def = cake_define
  `(write_bytes bs [] be = []) /\
   (write_bytes bs ((w:'a word) :: ws) be =
      (let k = dimindex (:'a) DIV 8 in
        bytes_to_word k (n2w 0) bs w be :: write_bytes (DROP k bs)
          ws be))`;;

let small_int_def = cake_define
  `small_int (:'a) i <=>
     --&(dimword (:'a) DIV 8) <= i /\ i < (&(dimword (:'a) DIV
       8):int)`;;

let part_to_words_def = cake_define
  `part_to_words c m (Int i) offset =
     (if small_int (:'a) i then SOME ((F,Word (Smallnum i)),[]) else
       let (sign,ws) = i2mw i in
             match encode_header c (if sign then 7 else 3) (LENGTH
               ws) with NONE -> NONE | SOME hd -> SOME ((T,(make_ptr c
               offset ((n2w 0):'a word) (LENGTH ws))),
                              MAP (\w. (F,Word w)) (hd :: ws))) /\
   part_to_words c m (closLang_Con t ns) (offset:'a word) =
     (if NULL ns then
        if t < dimword (:'a) DIV 16 then SOME ((F,Word (n2w (16 * t +
          2))),[]) else NONE else
        match encode_header c (4 * t) (LENGTH ns) with NONE -> NONE |
          SOME hd -> SOME ((T,Word
                              (offset << (shift_length c -
                                (backend_common_word_shift) (:'ga)) +
                              (ptr_bits c t (LENGTH ns) || (n2w
                                1)))),
                           (F,Word hd) :: (MAP (lookup_mem m) ns)))
                             /\
   part_to_words c m (W64 w) offset =
     (let ws = (if dimindex (:'ga) < 64 then [((63 >< 32) w); ((31 ><
       0) w)] else [((63 >< 0) w):'a word]) in
        match encode_header c 3 (LENGTH ws) with NONE -> NONE | SOME
          hd -> SOME ((T,(make_ptr c offset ((n2w 0):'a word) (LENGTH
          ws))),
                           MAP (\w. (F,Word w)) (hd :: ws))) /\
   part_to_words c m (Str s) offset =
     (let bytes = MAP (n2w o ORD) (explode s) in
      let n = LENGTH bytes in
      let hd = make_byte_header c T n in
      let k = byte_len (:'ga) n in
      let ws = write_bytes bytes (REPLICATE k (n2w 0))
        (data_to_word_config_be c) in
        if k < 2 EXP (dimindex (:'ga) - 4) /\ k < 2 EXP
          data_to_word_config_len_size c then SOME ((T,(make_ptr c
          offset ((n2w 0):'a word) k)),
                   MAP (\w. (F,Word w)) (hd :: ws)) else NONE)`;;

let parts_to_words_def = cake_define
  `parts_to_words c m i [] off = SOME (lookup_mem m (i - (1:num)),[]) /\
   parts_to_words c m i (x :: parts) (off:'a word) =
     (match part_to_words c m x off with NONE -> NONE | SOME (w,xs)
       ->
       (match parts_to_words c (insert i w m) (i + 1) parts
                (off + bytes_in_word * n2w (LENGTH xs)) with NONE
                  -> NONE | SOME (r,ys) -> SOME (r,xs ++ ys)))`;;

let const_parts_to_words_def = cake_define
  `const_parts_to_words c parts =
     parts_to_words c LN 0 parts (n2w 0)`;;

let get_Word_def = cake_define
  `get_Word x1 =
      match x1 with
        (Word w) -> w
      | _14 -> (n2w 0)`;;

(* HOL4 ML code, not ported:
val def = assign_Define `
  assign_Build (c:data_to_word$config)
            (secn:num) (l:num) (dest:num) (names:num_set option) ps =
    case const_parts_to_words c ps of
    | NONE => (GiveUp,l)
    | SOME (w,ws) =>
      (list_Seq
        [Assign 1 (Lookup NextFree);
         Assign 3 (ShiftN Lsl (Op Sub [Var 1; Lookup CurrHeap])
                    (shift_length c − shift (:'a)));
         StoreAnyConsts (adjust_var dest) 1 3 ws w],l)
      : 'a wordLang$prog # num`;
*)

(* HOL4 ML code, not ported:
val def = assign_Define `
  assign_ConsExtend (c:data_to_word$config)
            (secn:num) (l:num) (dest:num) (names:num_set option) tag
              args =
        (case args of
         | (old::start::len::tot::rest) =>
          (case encode_header c (4 * tag) 0 of
             NONE => (GiveUp,l)
           | SOME header =>
              let limit = MIN (2 ** c.len_size) (dimword (:'a) DIV 16)
                in
              let h = ShiftN Lsl (Var (adjust_var tot))
                        (dimindex (:'a) - c.len_size - 2) in
                (list_Seq
                  [BignumHalt (adjust_var tot);
                   Assign 1 (Var (adjust_var tot));
                   AllocVar c limit (list_insert args (get_names
                     names));
                   Assign 1 (Lookup NextFree);
                   Assign 5 (Op Or [h; Const header]);
                   Assign 7 (ShiftN Lsr (Var (adjust_var tot)) 2);
                   Assign 9 (Const (n2w tag));
                   StoreEach 1 (5::MAP adjust_var rest) 0w;
                   Make_ptr_bits_code c 9 7 3;
                   Set NextFree (Op Add [Var 1; Const bytes_in_word;
                     ShiftN Lsl (Var 7) (shift (:'a))]);
                   Assign 15 (Var (adjust_var len));
                   Assign 13 (Op Add [Var 1;
                     Const (bytes_in_word * n2w (LENGTH rest + 1))]);
                   Assign 11 (Op Add [real_addr c (adjust_var old);
                     Const bytes_in_word;
                     ShiftVar Lsl (adjust_var start) (shift (:'a) -
                       2)]);
                   If Test 15 (Reg 15) (Assign (adjust_var dest) (Var
                     3)) (list_Seq [
                     MustTerminate
                       (Call (SOME ([adjust_var dest],adjust_sets
                         (get_names names),
                             Skip,secn,l))
                          (SOME MemCopy_location) [15;11;13;3]
                            NONE)])]),l+1)
         | _ => (Skip,l))
      : 'a wordLang$prog # num`;
*)

(* HOL4 ML code, not ported:
val def = assign_Define `
  assign_Ref (c:data_to_word$config) (secn:num)
             (l:num) (dest:num) (names:num_set option) args =
          (case encode_header c 2 (LENGTH args) of
              | NONE => (GiveUp,l)
              | SOME (header:'a word) => (list_Seq
                 [Set TriggerGC (Op Sub [Lookup TriggerGC;
                     Const (bytes_in_word * n2w (LENGTH args + 1))]);
                  Assign 1 (Op Sub [Lookup EndOfHeap;
                     Const (bytes_in_word * n2w (LENGTH args + 1))]);
                  Set EndOfHeap (Var 1);
                  Assign 3 (Const header);
                  StoreEach 1 (3::MAP adjust_var args) 0w;
                  Assign (adjust_var dest)
                    (Op Or [ShiftN Lsl (Op Sub [Var 1; Lookup CurrHeap])
                              (shift_length c − shift (:'a));
                            Const 1w])],l))
      : 'a wordLang$prog # num`;
*)

(* HOL4 ML code, not ported:
val def = assign_Define `
  assign_AllocThunk (ev : thunk_mode) (c:data_to_word$config) (secn:num)
             (l:num) (dest:num) (names:num_set option) arg =
          (let tag = (case ev of
                         | Evaluated => 8 + 6
                         | NotEvaluated => 0 + 6) in
           case encode_header c tag 1 of
              | NONE => (GiveUp,l)
              | SOME (header:'a word) => (list_Seq
                 [Set TriggerGC (Op Sub [Lookup TriggerGC;
                     Const (bytes_in_word * 2w)]);
                  Assign 1 (Op Sub [Lookup EndOfHeap;
                     Const (bytes_in_word * 2w)]);
                  Set EndOfHeap (Var 1);
                  Assign 3 (Const header);
                  StoreEach 1 [3; adjust_var arg] 0w;
                  Assign (adjust_var dest)
                    (Op Or [ShiftN Lsl (Op Sub [Var 1; Lookup CurrHeap])
                              (shift_length c − shift (:'a));
                            Const 1w])],l))
      : 'a wordLang$prog # num`;
*)

(* HOL4 ML code, not ported:
val def = assign_Define `
  assign_RefByte (c:data_to_word$config) (secn:num)
             (l:num) (dest:num) (names:num_set option) immutable v1 v2 =
         (Seq
           (Assign 1 (Const (if immutable then 0w else 16w))) (* n.b.
             this would have been better done with Set Temp *)
           (MustTerminate
             (Call (SOME ([adjust_var dest],adjust_sets (get_names
               names),Skip,secn,l))
                (SOME RefByte_location)
                   [adjust_var v1; adjust_var v2; 1] NONE) :'a
                     wordLang$prog),l+1)
      : 'a wordLang$prog # num`;
*)

(* HOL4 ML code, not ported:
val def = assign_Define `
  assign_XorByte (c:data_to_word$config) (secn:num)
             (l:num) (dest:num) (names:num_set option) v1 v2 =
    (list_Seq [
        Assign 1 (real_addr c (adjust_var v1));
        Assign 3 (real_addr c (adjust_var v2));
        Assign 5 (SmallLsr (Load (Var 3)) (dimindex (:'a) -
          c.len_size));
        Assign 1 (Op Add [Var 1; Const bytes_in_word]);
        Assign 3 (Op Add [Var 3; Const (bytes_in_word:'a word)]);
        MustTerminate
          (Call
            (SOME ([adjust_var dest],adjust_sets (get_names
              names),Skip,secn,l))
            (SOME XorLoop_location) [1;3;5] NONE)],l + 1)
      : 'a wordLang$prog # num`;
*)

let SetBool_def = cake_define
  `SetBool dest cmp r ri =
   (wordLang_If cmp r ri
      (Assign dest (Const (n2w 18:'a word)))
      (Assign dest (Const (n2w 2:'a word))):'a wordLang_prog)`;;

let AssignCmp_def = cake_define
  `AssignCmp dest (Lt:opb) v1 v2 = (SetBool dest Lower v1 (Reg v2):'a
  wordLang_prog) /\
   AssignCmp dest (Gt:opb) v1 v2 = SetBool dest Lower v2 (Reg v1) /\
   AssignCmp dest (Leq:opb) v1 v2 = SetBool dest NotLower v2 (Reg v1)
     /\
   AssignCmp dest (Geq:opb) v1 v2 = SetBool dest NotLower v1 (Reg
     v2)`;;

(* HOL4 ML code, not ported:
val def = assign_Define `
  assign_StringCmp (c:data_to_word$config) (secn:num)
             (l:num) (dest:num) (names:num_set option) (b:bool)
               (cmp:ast$opb) v1 v2 =
    (let k = (dimindex (:α) − c.len_size - shift (:'a)) in
      list_Seq [
          Assign 1 (real_addr c (adjust_var v1)); (* address to header
            *)
          Assign 3 (real_addr c (adjust_var v2)); (* address to header
            *)
          Assign 5 (ShiftN Lsr (Load (Var 1)) k); (* len + bytes_in_word
            *)
          Assign 7 (ShiftN Lsr (Load (Var 3)) k); (* len + bytes_in_word
            *)
          (if b then
             If Equal 5 (Reg 7)
                (list_Seq
                 [Assign 11 (Op Add [Var 1; Const bytes_in_word]);
                  Assign 13 (Op Add [Var 3; Const bytes_in_word]);
                  MustTerminate
                  (Call (SOME ([5;7],adjust_sets (get_names
                    names),Skip,secn,l))
                        (SOME StringCmpLoop_location) [11;13;7;7;7]
                          NONE)])
                Skip
           else
             list_Seq
             [Assign 11 (Op Add [Var 1; Const bytes_in_word]);
              Assign 13 (Op Add [Var 3; Const bytes_in_word]);
              Assign 9 (Var 5);
              If Lower 7 (Reg 5) (Assign 9 (Var 7)) Skip;
              MustTerminate
              (Call (SOME ([5;7],adjust_sets (get_names
                names),Skip,secn,l))
                    (SOME StringCmpLoop_location) [11;13;9;5;7] NONE)]);
          AssignCmp (adjust_var dest) cmp 5 7],l + 1)
      : 'a wordLang$prog # num`;
*)

(* HOL4 ML code, not ported:
val def = assign_Define `
  assign_CopyByte (c:data_to_word$config) (secn:num)
             (l:num) (dest:num) (names:num_set option) args =
      (case args of
       | [v1;v2;v3;v4;v5] (* alloc_new is F *) =>
           (MustTerminate
             (Call (SOME ([adjust_var dest],adjust_sets (get_names
               names),Skip,secn,l))
                (SOME ByteCopy_location)
                   [adjust_var v1; adjust_var v2; adjust_var v3;
                    adjust_var v4; adjust_var v5] NONE) :'a
                      wordLang$prog,l+1)
       | [v1;v2;v3] (* alloc_new is T *) =>
           (MustTerminate
             (Call (SOME ([adjust_var dest],adjust_sets (get_names
               names),Skip,secn,l))
                (SOME ByteCopyNew_location)
                   [adjust_var v1; adjust_var v2;
                    adjust_var v3] NONE) :'a wordLang$prog,l+1)
       | _ => (Skip,l))
      : 'a wordLang$prog # num`;
*)

(* HOL4 ML code, not ported:
val def = assign_Define `
  assign_RefArray (c:data_to_word$config) (secn:num)
             (l:num) (dest:num) (names:num_set option) v1 v2 =
      let limit = MIN (2 ** c.len_size) (dimword (:'a) DIV 16)
      in
         (list_Seq
          [
          BignumHalt (adjust_var v1);
          Move 0 [(1,adjust_var v1)];
          AllocVar c limit (list_insert [v1; v2] (get_names names));
          MustTerminate
            (Call (SOME ([adjust_var dest],adjust_sets (get_names
              names),Skip,secn,l))
               (SOME RefArray_location)
                  [adjust_var v1; adjust_var v2] NONE) :'a wordLang$prog
          ],l+1)
      : 'a wordLang$prog # num`;
*)

(* HOL4 ML code, not ported:
val def = assign_Define `
  assign_FromList (c:data_to_word$config) (secn:num)
             (l:num) (dest:num) (names:num_set option) tag v1 v2 =
       if encode_header c (4 * tag) 0 = (NONE:'a word option) then
         (GiveUp,l) else
         (MustTerminate (list_Seq [
            Assign 1 (Const (n2w (16 * tag)));
            (Call (SOME ([adjust_var dest],adjust_sets (get_names
              names),Skip,secn,l))
               (SOME FromList_location)
                  [adjust_var v1; adjust_var v2; 1] NONE) :'a
                    wordLang$prog]),l+1)
      : 'a wordLang$prog # num`;
*)

(* HOL4 ML code, not ported:
val def = assign_Define `
  assign_LessConstSmall (l:num) (dest:num) i v1 =
                 (If Less (adjust_var v1) (Imm (n2w (4 * i)))
                    (Assign (adjust_var dest) TRUE_CONST)
                    (Assign (adjust_var dest) FALSE_CONST),l)
      : 'a wordLang$prog # num`;
*)

(* HOL4 ML code, not ported:
val def = assign_Define `
  assign_BoolTest (l:num) (dest:num) (test: ast$test) v1 v2 =
                 (If Equal (adjust_var v1) (Reg (adjust_var v2))
                   (Assign (adjust_var dest) TRUE_CONST)
                   (Assign (adjust_var dest) FALSE_CONST),l)
      : 'a wordLang$prog # num`;
*)

(* HOL4 ML code, not ported:
val def = assign_Define `
  assign_BoolNot (l:num) (dest:num) v1 =
                 (Assign (adjust_var dest)
                    (Op Xor [Var (adjust_var v1); Const 16w]),l)
      : 'a wordLang$prog # num`;
*)

(* HOL4 ML code, not ported:
val def = assign_Define `
  assign_WordTest (l:num) (dest:num) (test: ast$test) v1 v2 =
       ((case test of
         | Equal       => If Equal (adjust_var v1) (Reg (adjust_var v2))
                             (Assign (adjust_var dest) TRUE_CONST)
                             (Assign (adjust_var dest) FALSE_CONST)
         | Compare Lt  => If Lower (adjust_var v1) (Reg (adjust_var v2))
                             (Assign (adjust_var dest) TRUE_CONST)
                             (Assign (adjust_var dest) FALSE_CONST)
         | Compare Leq => If NotLower (adjust_var v2) (Reg (adjust_var
           v1))
                             (Assign (adjust_var dest) TRUE_CONST)
                             (Assign (adjust_var dest) FALSE_CONST)
         | _           => Skip),l)
      : 'a wordLang$prog # num`;
*)

(* HOL4 ML code, not ported:
val def = assign_Define `
  assign_BoundsCheckByte (c:data_to_word$config) (secn:num)
             (l:num) (dest:num) (names:num_set option) leq v1 v2 =
                   (list_Seq [Assign 1
                               (let addr = real_addr c (adjust_var v1)
                                 in
                                let header = Load addr in
                                let extra = (if dimindex (:'a) = 32 then
                                  2 else 3) in
                                let k = dimindex (:'a) - c.len_size -
                                  extra in
                                  Op Sub [ShiftN Lsr header k; Const
                                    bytes_in_word]);
                              Assign 3 (ShiftVar Ror (adjust_var v2) 2);
                              (if leq then If NotLower 1 (Reg 3) else
                                           If Lower 3 (Reg 1))
                                 (Assign (adjust_var dest) TRUE_CONST)
                                 (Assign (adjust_var dest)
                                   FALSE_CONST)],l)
      : 'a wordLang$prog # num`;
*)

(* HOL4 ML code, not ported:
val def = assign_Define `
  assign_BoundsCheckArray (c:data_to_word$config) (secn:num)
             (l:num) (dest:num) (names:num_set option) v1 v2 =
                   (list_Seq [Assign 1
                               (let addr = real_addr c (adjust_var v1)
                                 in
                                let header = Load addr in
                                let k = dimindex (:'a) - c.len_size in
                                  ShiftN Lsr header k);
                              Assign 3 (ShiftVar Ror (adjust_var v2) 2);
                              If Lower 3 (Reg 1)
                               (Assign (adjust_var dest) TRUE_CONST)
                               (Assign (adjust_var dest)
                                 FALSE_CONST)],l)
      : 'a wordLang$prog # num`;
*)

(* HOL4 ML code, not ported:
val def = assign_Define `
  assign_BoundsCheckBlock (c:data_to_word$config) (secn:num)
             (l:num) (dest:num) (names:num_set option) v1 v2 =
                   (list_Seq [If Test (adjust_var v1) (Imm 1w)
                               (Assign 1 (Const 0w))
                               (Assign 1
                                 (let addr = real_addr c (adjust_var v1)
                                   in
                                  let header = Load addr in
                                  let k = dimindex (:'a) - c.len_size in
                                    ShiftN Lsr header k));
                              Assign 3 (ShiftVar Ror (adjust_var v2) 2);
                              If Lower 3 (Reg 1)
                               (Assign (adjust_var dest) TRUE_CONST)
                               (Assign (adjust_var dest)
                                 FALSE_CONST)],l)
      : 'a wordLang$prog # num`;
*)

(* HOL4 ML code, not ported:
val def = assign_Define `
  assign_Equal (c:data_to_word$config) (secn:num)
             (l:num) (dest:num) (names:num_set option) v1 v2 =
        (list_Seq [Assign 1 (Var (adjust_var v1));
                   Assign 3 (Var (adjust_var v2));
                   Assign 5 (Op And [Var 1; Var 3]);
                   If Test 5 (Imm 1w) Skip
                     (If Equal 1 (Reg 3) Skip
                       (Seq (MustTerminate
                          (Call (SOME ([1],adjust_sets (get_names
                            names),Skip,secn,l))
                                (SOME Equal_location) [1;3] NONE))
                          (Assign 3 (Const 1w))));
                   (If Equal 1 (Reg 3)
                      (Assign (adjust_var dest) TRUE_CONST)
                      (Assign (adjust_var dest) FALSE_CONST))],l+1)
      : 'a wordLang$prog # num`;
*)

(* HOL4 ML code, not ported:
val def = assign_Define `
  assign_Less (c:data_to_word$config) (secn:num)
             (l:num) (dest:num) (names:num_set option) v1 v2 =
        (list_Seq [Assign 1 (Var (adjust_var v1));
                   Assign 3 (Var (adjust_var v2));
                   Assign 5 (Op Or [Var 1; Var 3]);
                   If Test 5 (Imm 1w) Skip
                     (Seq (MustTerminate
                          (Call (SOME ([1],adjust_sets (get_names
                            names),Skip,secn,l))
                                (SOME Compare_location) [1;3] NONE))
                          (Assign 3 (Const 1w)));
                   (If Less 1 (Reg 3)
                      (Assign (adjust_var dest) TRUE_CONST)
                      (Assign (adjust_var dest) FALSE_CONST))],l+1)
      : 'a wordLang$prog # num`;
*)

(* HOL4 ML code, not ported:
val def = assign_Define `
  assign_LessEq (c:data_to_word$config) (secn:num)
             (l:num) (dest:num) (names:num_set option) v1 v2 =
        (list_Seq [Assign 1 (Var (adjust_var v1));
                   Assign 3 (Var (adjust_var v2));
                   Assign 5 (Op Or [Var 1; Var 3]);
                   If Test 5 (Imm 1w) Skip
                     (Seq (MustTerminate
                          (Call (SOME ([1],adjust_sets (get_names
                            names),Skip,secn,l))
                                (SOME Compare_location) [1;3] NONE))
                          (Assign 3 (Const 1w)));
                   (If NotLess 3 (Reg 1)
                      (Assign (adjust_var dest) TRUE_CONST)
                      (Assign (adjust_var dest) FALSE_CONST))],l+1)
      : 'a wordLang$prog # num`;
*)

(* HOL4 ML code, not ported:
val def = assign_Define `
  assign_LengthBlock (c:data_to_word$config) (secn:num)
             (l:num) (dest:num) (names:num_set option) v1 =
                        (If Test (adjust_var v1) (Imm 1w)
                           (Assign (adjust_var dest) (Const 0w))
                           (Assign (adjust_var dest)
                              (let addr = real_addr c (adjust_var v1) in
                               let header = Load addr in
                               let k = dimindex (:'a) - c.len_size in
                               let len = ShiftN Lsr header k in
                                 (ShiftN Lsl len 2))),l)
      : 'a wordLang$prog # num`;
*)

(* HOL4 ML code, not ported:
val def = assign_Define `
  assign_Length (c:data_to_word$config) (secn:num)
             (l:num) (dest:num) (names:num_set option) v1 =
                          (Assign (adjust_var dest)
                              (let addr = real_addr c (adjust_var v1) in
                               let header = Load addr in
                               let k = dimindex (:'a) - c.len_size in
                               let len = ShiftN Lsr header k in
                                 (ShiftN Lsl len 2)),l)
      : 'a wordLang$prog # num`;
*)

(* HOL4 ML code, not ported:
val def = assign_Define `
  assign_LengthByte (c:data_to_word$config) (secn:num)
             (l:num) (dest:num) (names:num_set option) v1 =
            (Assign (adjust_var dest)
               (let addr = real_addr c (adjust_var v1) in
                let header = Load addr in
                let k = dimindex(:'a) - shift(:'a) - c.len_size in
                let fakelen = ShiftN Lsr header k in
                let len = Op Sub [fakelen; Const bytes_in_word] in
                  (ShiftN Lsl len 2)),l)
      : 'a wordLang$prog # num`;
*)

(* HOL4 ML code, not ported:
val def = assign_Define `
  assign_TagLenEq (c:data_to_word$config) (secn:num)
             (l:num) (dest:num) (names:num_set option) tag len v1 =
                        (if len = 0 then
                           if tag < dimword (:'a) DIV 16 then
                             (If Equal (adjust_var v1) (Imm (n2w (16 *
                               tag + 2)))
                                (Assign (adjust_var dest) TRUE_CONST)
                                (Assign (adjust_var dest)
                                  FALSE_CONST),l)
                           else (Assign (adjust_var dest) FALSE_CONST,l)
                         else if tag < 2 ** c.tag_bits - 1 /\
                                 len < 2 ** c.len_bits -1 then
                           (Seq
                             (Assign 1 (Op And
                                [Var (adjust_var v1);
                                 Const (all_ones (c.len_bits +
                                   c.tag_bits + 1) 0)]))
                             (If Equal 1 (Imm (ptr_bits c tag len ||
                               1w))
                                (Assign (adjust_var dest) TRUE_CONST)
                                (Assign (adjust_var dest)
                                  FALSE_CONST)),l)
                         else
                           case encode_header c (4 * tag) len of
                           | NONE => (Assign (adjust_var dest)
                             FALSE_CONST,l)
                           | SOME h =>
                             (list_Seq
                               [Assign 1 (Const 0w);
                                If Test (adjust_var v1) (Imm 1w) Skip
                                  (Assign 1 (Load (real_addr c
                                    (adjust_var v1))));
                                If Equal 1 (Imm h)
                                  (Assign (adjust_var dest) TRUE_CONST)
                                  (Assign (adjust_var dest)
                                    FALSE_CONST)],l))
      : 'a wordLang$prog # num`;
*)

(* HOL4 ML code, not ported:
val def = assign_Define `
  assign_LenEq (c:data_to_word$config) (secn:num)
             (l:num) (dest:num) (names:num_set option) len v1 =
                        (if len = 0 then
                           (If Test (adjust_var v1) (Imm 1w)
                              (Assign (adjust_var dest) TRUE_CONST)
                              (Assign (adjust_var dest) FALSE_CONST),l)
                         else if len < 2 ** c.len_bits - 1 then
                           (Seq
                             (Assign 1 (Op And
                                [Var (adjust_var v1);
                                 Const (all_ones (c.len_bits + 1) 0)]))
                             (If Equal 1 (Imm (ptr_bits c 0 len || 1w))
                                (Assign (adjust_var dest) TRUE_CONST)
                                (Assign (adjust_var dest)
                                  FALSE_CONST)),l)
                         else if len < dimword (:'a) then
                           (list_Seq
                             [Assign 1 (Const 0w);
                              If Test (adjust_var v1) (Imm 1w) Skip
                               (Assign 1
                                 (let addr = real_addr c (adjust_var v1)
                                   in
                                  let header = Load addr in
                                  let k = dimindex (:'a) - c.len_size in
                                  let len = ShiftN Lsr header k in
                                    len));
                              If Equal 1 (Imm (n2w len))
                                (Assign (adjust_var dest) TRUE_CONST)
                                (Assign (adjust_var dest)
                                  FALSE_CONST)],l)
                         else
                           (Assign (adjust_var dest) FALSE_CONST,l))
      : 'a wordLang$prog # num`;
*)

(* HOL4 ML code, not ported:
val def = assign_Define `
  assign_TagEq (c:data_to_word$config) (secn:num)
             (l:num) (dest:num) (names:num_set option) tag v1 =
               (if tag < dimword (:'a) DIV 16 then
                 (list_Seq
                   [Assign 1 (Var (adjust_var v1));
                    If Test (adjust_var v1) (Imm 1w) Skip
                      (Assign 1 (let v = adjust_var v1 in
                                 let h = Load (real_addr c v) in
                                   Op And [h; Const (tag_mask c ||
                                     2w)]));
                    If Equal 1 (Imm (n2w (16 * tag + 2)))
                      (Assign (adjust_var dest) TRUE_CONST)
                      (Assign (adjust_var dest) FALSE_CONST)],l)
                else (Assign (adjust_var dest) FALSE_CONST,l))
      : 'a wordLang$prog # num`;
*)

(* HOL4 ML code, not ported:
val def = assign_Define `
  assign_Add (c:data_to_word$config) (secn:num)
             (l:num) (dest:num) (names:num_set option) v1 v2 =
        (list_Seq [(* perform addition *)
                   Inst (Arith (AddOverflow 1 (adjust_var v1)
                                              (adjust_var v2) 3));
*)
                   (* or together bits of overflow flag, and the two
                      inputs *)
(* HOL4 ML code, not ported:
                   Assign 3 (Op Or [Var 3; Var (adjust_var v1); Var
                     (adjust_var v2)]);
*)
                   (* if the least significant bit is set, then bignum
                      is needed *)
(* HOL4 ML code, not ported:
                   If Test 3 (Imm 1w) Skip
                    (MustTerminate
                      (Call (SOME ([1],adjust_sets (get_names
                        names),Skip,secn,l))
                        (SOME Add_location) [adjust_var v1; adjust_var
                          v2] NONE));
                   Move 2 [(adjust_var dest,1)]],l+1)
      : 'a wordLang$prog # num`;
*)

(* HOL4 ML code, not ported:
val def = assign_Define `
  assign_Sub (c:data_to_word$config) (secn:num)
             (l:num) (dest:num) (names:num_set option) v1 v2 =
        (list_Seq [(* perform subtraction *)
                   Inst (Arith (SubOverflow 1 (adjust_var v1)
                                              (adjust_var v2) 3));
*)
                   (* or together bits of overflow flag, and the two
                      inputs *)
(* HOL4 ML code, not ported:
                   Assign 3 (Op Or [Var 3; Var (adjust_var v1); Var
                     (adjust_var v2)]);
*)
                   (* if the least significant bit is set, then bignum
                      is needed *)
(* HOL4 ML code, not ported:
                   If Test 3 (Imm 1w) Skip
                    (MustTerminate
                      (Call (SOME ([1],adjust_sets (get_names
                        names),Skip,secn,l))
                        (SOME Sub_location) [adjust_var v1; adjust_var
                          v2] NONE));
                   Move 2 [(adjust_var dest,1)]],l+1)
      : 'a wordLang$prog # num`;
*)

(* HOL4 ML code, not ported:
val def = assign_Define `
  assign_Mult (c:data_to_word$config) (secn:num)
             (l:num) (dest:num) (names:num_set option) v1 v2 =
        (list_Seq [Assign 1 (ShiftVar Lsr (adjust_var v1) 1);
                   Inst (Arith (LongMul 3 1 1 (adjust_var v2)));
                   Assign 3 (Op Or [Var 3;
                               Op And [Const 1w;
                                 Op Or [Var (adjust_var v1); Var
                                   (adjust_var v2)]]]);
                   Assign 1 (ShiftVar Lsr 1 1);
                   If Equal 3 (Imm 0w) Skip
                     (MustTerminate
                       (Call (SOME ([1],adjust_sets (get_names
                         names),Skip,secn,l))
                        (SOME Mul_location) [adjust_var v1; adjust_var
                          v2] NONE));
                   Move 2 [(adjust_var dest,1)]],l+1)
      : 'a wordLang$prog # num`;
*)

(* HOL4 ML code, not ported:
val def = assign_Define `
  assign_Div (c:data_to_word$config) (secn:num)
             (l:num) (dest:num) (names:num_set option) v1 v2 =
        (list_Seq [
           Assign 1 (Op Or [Var (adjust_var v1); Var (adjust_var v2)]);
           Assign 1 (Op Or [Var 1; ShiftVar Lsr 1 (dimindex (:'a)-1)]);
           If Test 1 (Imm (1w:'a word))
             (if c.has_div then
                list_Seq [Inst (Arith (Div 1 (adjust_var v1) (adjust_var
                  v2)));
                          Assign (adjust_var dest) (ShiftVar Lsl 1 2)]
              else if c.has_longdiv then
                list_Seq [Assign 1 (Const 0w);
                          Inst (Arith (LongDiv 1 3 1 (adjust_var
                            v1)(adjust_var v2)));
                          Assign (adjust_var dest) (ShiftVar Lsl 1 2)]
              else
                list_Seq
                  [Assign 1 (Const 0w);
                   MustTerminate
                    (Call (SOME ([1],adjust_sets (get_names
                      names),Skip,secn,l+1))
                      (SOME LongDiv_location)
                        [1; adjust_var v1; adjust_var v2] NONE);
                   Assign (adjust_var dest) (ShiftVar Lsl 1 2)])
             (list_Seq
                [MustTerminate
                   (Call (SOME ([1],adjust_sets (get_names
                     names),Skip,secn,l))
                      (SOME Div_location) [adjust_var v1; adjust_var v2]
                        NONE);
                 Move 2 [(adjust_var dest,1)]])],l + 2)
      : 'a wordLang$prog # num`;
*)

(* HOL4 ML code, not ported:
val def = assign_Define `
  assign_Mod (c:data_to_word$config) (secn:num)
             (l:num) (dest:num) (names:num_set option) v1 v2 =
        (list_Seq [
           Assign 1 (Op Or [Var (adjust_var v1); Var (adjust_var v2)]);
           Assign 1 (Op Or [Var 1; ShiftVar Lsr 1 (dimindex (:'a)-1)]);
           If Test 1 (Imm (1w:'a word))
             (if c.has_div then
                list_Seq [Inst (Arith (Div 1 (adjust_var v1) (adjust_var
                  v2)));
                          Inst (Arith (LongMul 3 1 1 (adjust_var v2)));
                          Assign (adjust_var dest)
                            (Op Sub [Var (adjust_var v1); Var 1])]
              else if c.has_longdiv then
                list_Seq [Assign 1 (Const 0w);
                          Inst (Arith (LongDiv 1 3 1 (adjust_var
                            v1)(adjust_var v2)));
                          Move 2 [(adjust_var dest,3)]]
              else
                list_Seq
                  [Assign 1 (Const 0w);
                   MustTerminate
                    (Call (SOME ([1],adjust_sets (get_names
                      names),Skip,secn,l+1))
                      (SOME LongDiv_location)
                        [1; adjust_var v1; adjust_var v2] NONE);
                   Get (adjust_var dest) (Temp 28w)])
             (list_Seq
                [MustTerminate
                   (Call (SOME ([1],adjust_sets (get_names
                     names),Skip,secn,l))
                      (SOME Mod_location) [adjust_var v1; adjust_var v2]
                        NONE);
                 Move 2 [(adjust_var dest,1)]])],l + 2)
      : 'a wordLang$prog # num`;
*)

(* HOL4 ML code, not ported:
val def = assign_Define `
  assign_WordOpW8 opw (c:data_to_word$config) (secn:num)
             (l:num) (dest:num) (names:num_set option) v1 v2 =
           (Assign (adjust_var dest)
            (case lookup_word_op opw of
             | Bitwise op => Op op [Var (adjust_var v1); Var (adjust_var
               v2)]
             | Carried op => let k = dimindex(:'a)-10 in
               ShiftN Lsr (ShiftN Lsl
                 (Op op [Var (adjust_var v1); Var (adjust_var v2)]) k)
                   k), l)
      : 'a wordLang$prog # num`;
*)

(* HOL4 ML code, not ported:
val def = assign_Define `
  assign_WordOpW64 opw (c:data_to_word$config) (secn:num)
             (l:num) (dest:num) (names:num_set option) v1 v2 =
       (if dimindex(:'a) = 64 then
         (case encode_header c 3 1 of
          | NONE => (GiveUp,l)
          | SOME (header:'a word) =>
                (Seq (Assign 3
                  (Op (case opw of
                          Andw => And
                        | Orw => Or
                        | Xor => Xor
                        | Add => Add
                        | Sub => Sub)
                         [Load
                            (Op Add
                               [real_addr c (adjust_var v1);
                                Const bytes_in_word]);
                          Load
                            (Op Add
                               [real_addr c (adjust_var v2);
                                Const bytes_in_word])]))
                   (WriteWord64 c header dest 3),l))
        else
         (case encode_header c 3 2 of
          | NONE => (GiveUp,l)
          | SOME header =>
            (list_Seq [
               Assign 15 (real_addr c (adjust_var v1));
               Assign 17 (real_addr c (adjust_var v2));
               Assign 11 (Load (Op Add [Var 15; Const bytes_in_word]));
               Assign 13 (Load (Op Add [Var 15; Const (2w *
                 bytes_in_word)]));
               Assign 21 (Load (Op Add [Var 17; Const bytes_in_word]));
               Assign 23 (Load (Op Add [Var 17; Const (2w *
                 bytes_in_word)]));
               WordOp64_on_32 opw;
               WriteWord64_on_32 c header dest 33 31],l)))
      : 'a wordLang$prog # num`;
*)

(* HOL4 ML code, not ported:
val def = assign_Define `
  assign_WordShiftW8 sh n (c:data_to_word$config) (secn:num)
             (l:num) (dest:num) (names:num_set option) v1 =
        (Assign (adjust_var dest)
           (case sh of
            | Lsl =>
              ShiftN Lsr
                (ShiftN Lsl (Var (adjust_var v1)) (dimindex(:'a)-10+(MIN
                  n 8)))
                (dimindex(:'a) - 10)
            | Lsr =>
              ShiftN Lsl
                (ShiftN Lsr (Var (adjust_var v1)) ((MIN n 8)+2)) 2
            | Asr =>
              ShiftN Lsl
                (ShiftN Lsr
                   (ShiftN Asr
                      (ShiftN Lsl (Var (adjust_var v1)) (dimindex(:'a) -
                        10))
                      (MIN n 8))
                   (dimindex(:'a) - 8)) 2
            | Ror =>
              (let n = n MOD 8 in
                 Op Or
                  [ShiftN Lsl (ShiftVar Lsr (adjust_var v1) (n + 2)) 2;
                   ShiftN Lsr (ShiftVar Lsl (adjust_var v1)
                     ((dimindex (:'a) - 2) - n)) (dimindex (:'a) -
                       10)])),l)
      : 'a wordLang$prog # num`;
*)

(* HOL4 ML code, not ported:
val def = assign_Define `
  assign_WordShiftW64 sh n (c:data_to_word$config) (secn:num)
             (l:num) (dest:num) (names:num_set option) v1 =
         let len = if dimindex(:'a) < 64 then 2 else 1 in
         (case encode_header c 3 len of
          | NONE => (GiveUp,l)
          | SOME (header:'a word) =>
            (if len = 1 then
               list_Seq
                 [LoadWord64 c 3 (adjust_var v1);
                  Assign 3 (ShiftVar sh 3 n);
                  WriteWord64 c header dest 3]
             else
               list_Seq [
                 Assign 15 (real_addr c (adjust_var v1));
                 Assign 11 (Load (Op Add [Var 15; Const
                   bytes_in_word]));
                 Assign 13 (Load (Op Add [Var 15; Const (2w *
                   bytes_in_word)]));
                 WordShift64_on_32 sh n;
                 WriteWord64_on_32 c header dest 33 31],l))
      : 'a wordLang$prog # num`;
*)

(* HOL4 ML code, not ported:
val def = assign_Define `
  assign_WordFromWord b (c:data_to_word$config) (secn:num)
             (l:num) (dest:num) (names:num_set option) v1 =
          if b then
            (list_Seq [Assign 1 (real_addr c (adjust_var v1));
                       Assign 1 (Load (Op Add [Var 1;
                         Const (if dimindex (:'a) = 32
                                then 2w * bytes_in_word else
                                  bytes_in_word)]));
                       Assign 1 (Op And [Var 1; Const 255w]);
                       Assign (adjust_var dest) (ShiftVar Lsl 1 2)],l)
          else
          (let
             len = if dimindex (:α) < 64 then 2 else 1
           in
             case encode_header c 3 len of
               NONE => (GiveUp,l)
             | SOME header =>
                (if len = 1 then
                   (list_Seq [Assign 3 (ShiftN Lsr (Var (adjust_var v1))
                     2);
                              WriteWord64 c header dest 3],l)
                 else
                   (list_Seq [Assign 5 (ShiftN Lsr (Var (adjust_var v1))
                     2);
                              Assign 3 (Const 0w);
                              WriteWord64_on_32 c header dest 5 3],l)))
      : 'a wordLang$prog # num`;
*)

(* HOL4 ML code, not ported:
val def = assign_Define `
  assign_WordFromInt (c:data_to_word$config) (secn:num)
             (l:num) (dest:num) (names:num_set option) v1 =
        let len = if dimindex(:'a) < 64 then 2 else 1 in
        (case encode_header c 3 len of
         | NONE => (GiveUp,l)
         | SOME (header:'a word) =>
           (if len = 1 then
             Seq
*)
               (* put the word value into 3 *)
(* HOL4 ML code, not ported:
               (If Test (adjust_var v1) (Imm 1w)
*)
                   (* smallnum case *)
(* HOL4 ML code, not ported:
                    (Assign 3 (ShiftN Asr (Var (adjust_var v1)) 2))
*)
                   (* bignum case *)
(* HOL4 ML code, not ported:
                   (Seq
                     (LoadBignum c 1 3 (adjust_var v1))
                     (If Test 1 (Imm 16w) Skip
                        (Assign 3 (Op Sub [Const 0w; Var 3])))))
               (WriteWord64 c header dest 3)
            else If Test (adjust_var v1) (Imm 1w)
              (list_Seq [
                Assign 3 (ShiftN Asr (Var (adjust_var v1)) 2);
                Assign 5 (ShiftN Asr (Var (adjust_var v1)) 31);
                WriteWord64_on_32 c header dest 3 5
              ])
              (list_Seq [
                Assign 1 (real_addr c (adjust_var v1));
                Assign 3 (Load (Var 1));
                Assign 5 (Load (Op Add [Var 1; Const bytes_in_word]));
                Assign 7 (ShiftVar Lsr 3 (dimindex (:'a) − c.len_size));
                If Equal 7 (Imm 1w)
*)
                  (* bignum of length 1 *)
(* HOL4 ML code, not ported:
                  (If Test 3 (Imm 16w)
*)
                    (* positive case *)
(* HOL4 ML code, not ported:
                    (Seq (Assign 9 (Const 0w))
                         (WriteWord64_on_32 c header dest 5 9))
*)
                    (* negative case *)
(* HOL4 ML code, not ported:
                    (Seq (Assign 9 (Const ~0w))
                    (Seq (Assign 5 (Op Sub [Const 0w; Var 5]))
                         (WriteWord64_on_32 c header dest 5 9))))
*)
                  (* longer bignum *)
(* HOL4 ML code, not ported:
                  (If Test 3 (Imm 16w)
*)
                    (* positive case *)
(* HOL4 ML code, not ported:
                    (Seq (Assign 9 (Load
                           (Op Add [Var 1; Const (2w *
                             bytes_in_word)])))
                         (WriteWord64_on_32 c header dest 5 9))
*)
                    (* negative case -- messy *)
(* HOL4 ML code, not ported:
                    (list_Seq
                      [Assign 11 (Const 0w);
                       Assign 13 (Const 1w);
                       Assign 9 (Load
                         (Op Add [Var 1; Const (2w * bytes_in_word)]));
                       Assign 5 (Op Xor [Const ~0w; Var 5]);
                       Assign 9 (Op Xor [Const ~0w; Var 9]);
                       Inst (Arith (AddCarry 15 11 5 13));
                       Inst (Arith (AddCarry 19 11 9 13));
                       WriteWord64_on_32 c header dest 15 19]))])), l)
      : 'a wordLang$prog # num`;
*)

(* HOL4 ML code, not ported:
val def = assign_Define `
  assign_WordToInt (c:data_to_word$config) (secn:num)
             (l:num) (dest:num) (names:num_set option) v =
        let len = if dimindex(:'a) < 64 then 2 else 1 in
        (case encode_header c 3 len of
           | NONE => (GiveUp,l)
           | SOME header =>
             if len = 1 then
               (list_Seq [LoadWord64 c 3 (adjust_var v);
                          Assign 1 (ShiftN Lsr (Var 3) 61);
                          If Equal 1 (Imm 0w)
                            (Assign (adjust_var dest) (ShiftN Lsl (Var
                              3) 2))
                            (WriteWord64 c header dest 3)], l)
             else
              (case encode_header c 3 1 of
               | NONE => (GiveUp,l)
               | SOME header1 =>
                 (list_Seq [
                  Assign 15 (real_addr c (adjust_var v));
                  Assign 13 (Load (Op Add [Var 15; Const
                    bytes_in_word]));
                  Assign 11 (Load (Op Add [Var 15; Const (2w *
                    bytes_in_word)]));
                  If NotEqual 13 (Imm 0w)
                    (WriteWord64_on_32 c header dest 13 11)
                    (list_Seq [
                      Assign 1 (ShiftN Lsr (Var 11) 29);
                      If Equal 1 (Imm 0w)
                        (Assign (adjust_var dest) (ShiftN Lsl (Var 11)
                          2))
                        (WriteWord32_on_32 c header1 dest 11)])],l)))
      : 'a wordLang$prog # num`;
*)

(* HOL4 ML code, not ported:
val def = assign_Define `
  assign_FFI ffi_index (c:data_to_word$config) (secn:num)
             (l:num) (dest:num) (names:num_set option) v1 v2 =
      if ¬c.call_empty_ffi ∧ ffi_index = «» then (Assign (adjust_var
        dest) Unit,l) else
        let addr1 = real_addr c (adjust_var v1) in
        let header1 = Load addr1 in
        let k = dimindex(:'a) - shift(:'a) - c.len_size in
        let fakelen1 = ShiftN Lsr header1 k in
        let addr2 = real_addr c (adjust_var v2) in
        let header2 = Load addr2 in
        let fakelen2 = ShiftN Lsr header2 k in
        (list_Seq [
          Assign 1 (Op Add [addr1; Const bytes_in_word]);
          Assign 3 (Op Sub [fakelen1; Const bytes_in_word]);
          Assign 5 (if ffi_index = «» then Const 0w else (Op Add [addr2;
            Const bytes_in_word]));
          Assign 7 (if ffi_index = «» then Const 0w else (Op Sub
            [fakelen2; Const bytes_in_word]));
          FFI ffi_index 1 3 5 7 (adjust_sets (case names of SOME names
            => names | NONE => LN));
          Assign (adjust_var dest) Unit]
        , l)
      : 'a wordLang$prog # num`;
*)

(* HOL4 ML code, not ported:
val def = assign_Define `
  assign_EqualConst p (c:data_to_word$config) (secn:num)
             (l:num) (dest:num) (names:num_set option) v =
    case part_to_words c LN p 0w of
    | SOME ((F,w),_) =>
        (If Equal (adjust_var v) (Imm (get_Word w))
                    (Assign (adjust_var dest) TRUE_CONST)
                    (Assign (adjust_var dest) FALSE_CONST),l)
    | SOME (_,words) =>
        ((case p of
          | Int _ => If Test (adjust_var v) (Imm 1w)
                       (Assign (adjust_var dest) FALSE_CONST)
                       (list_Seq
                          [Assign 1 FALSE_CONST;
                           Assign 3 (real_addr c (adjust_var v));
                           MemEqList 0w (MAP (get_Word o SND) words);
                           Assign (adjust_var dest) (Var 1)])
          | W64 _ => (list_Seq
                          [Assign 1 FALSE_CONST;
                           Assign 3 (Op Add [real_addr c (adjust_var v);
                                             Const bytes_in_word]);
                           MemEqList 0w (MAP (get_Word o SND) (TL
                             words));
                           Assign (adjust_var dest) (Var 1)])
          | Str _ => (list_Seq
                          [Assign 1 FALSE_CONST;
                           Assign 3 (real_addr c (adjust_var v));
                           MemEqList 0w (MAP (get_Word o SND) words);
                           Assign (adjust_var dest) (Var 1)])
          | _ => Skip),l)
    | _ => (Assign (adjust_var dest) FALSE_CONST,l)
      : 'a wordLang$prog # num`;
*)

(* HOL4 ML code, not ported:
val def = assign_Define `
  assign_Install (c:data_to_word$config) (secn:num)
             (l:num) (dest:num) (names:num_set option) v1 v2 v3 v4 =
        (list_Seq [BignumHalt (adjust_var v3); (* length must be
          smallint *)
                   BignumHalt (adjust_var v4); (* length must be
                     smallint *)
                   Assign 1 (Lookup BitmapBuffer);
                   Assign 3 (Op Sub [Lookup BitmapBufferEnd; Var 1]);
                   Assign 5 (ShiftVar Lsr (adjust_var v4) 2);
                   Assign 3 (ShiftVar Lsr 3 (shift (:'a)));
                   If Lower 3 (Reg 5) (* too little data space *) GiveUp
                     Skip;
                   Assign 1 (Lookup CodeBuffer);
                   Assign 3 (Op Sub [Lookup CodeBufferEnd; Var 1]);
                   Assign 5 (ShiftVar Lsr (adjust_var v3) 2);
                   If Lower 3 (Reg 5) (* too little code space *) GiveUp
                     Skip;
                   MustTerminate
                    (Call (SOME ([adjust_var dest],
                       adjust_sets (get_names names),Skip,secn,l))
                    (SOME InstallCode_location)
                      [adjust_var v1; adjust_var v2; 1] NONE)],l+1)
      : 'a wordLang$prog # num`;
*)

(* HOL4 ML code, not ported:
val def = assign_Define `
  assign_FP_cmp fpc (c:data_to_word$config) (secn:num)
             (l:num) (dest:num) (names:num_set option) v1 v2 =
       (if ~c.has_fp_ops then (GiveUp,l) else
        if dimindex(:'a) = 64 then
           ((list_Seq [
               Assign 3 (Load (Op Add
                           [real_addr c (adjust_var v1); Const
                             bytes_in_word]));
               Assign 5 (Load (Op Add
                           [real_addr c (adjust_var v2); Const
                             bytes_in_word]));
               Inst (FP (FPMovFromReg 0 3 3));
               Inst (FP (FPMovFromReg 1 5 5));
               Inst (FP (fp_cmp_inst fpc));
               Assign (adjust_var dest) (Op Add [ShiftVar Lsl 3 4; Const
                 2w])],l))
        else
           ((list_Seq [
               Assign 15 (real_addr c (adjust_var v1));
               Assign 17 (real_addr c (adjust_var v2));
               Assign 11 (Load (Op Add [Var 15; Const bytes_in_word]));
               Assign 13 (Load (Op Add [Var 15; Const (2w *
                 bytes_in_word)]));
               Assign 21 (Load (Op Add [Var 17; Const bytes_in_word]));
               Assign 23 (Load (Op Add [Var 17; Const (2w *
                 bytes_in_word)]));
               Inst (FP (FPMovFromReg 0 13 11));
               Inst (FP (FPMovFromReg 1 23 21));
               Inst (FP (fp_cmp_inst fpc));
               Assign (adjust_var dest) (Op Add [ShiftVar Lsl 3 4; Const
                 2w])],l)))
      : 'a wordLang$prog # num`;
*)

(* HOL4 ML code, not ported:
val def = assign_Define `
  assign_FP_top fpt (c:data_to_word$config) (secn:num)
              (l:num) (dest:num) (names:num_set option) v1 v2 v3 =
       (if ~c.has_fp_ops \/ ~c.has_fp_tern then (GiveUp,l) else
        if dimindex(:'a) = 64 then
         (case encode_header c 3 1 of
          | NONE => (GiveUp,l)
          | SOME (header:'a word) =>
            (list_Seq [
               Assign 3 (Load (Op Add
                           [real_addr c (adjust_var v1); Const
                             bytes_in_word]));
               Assign 5 (Load (Op Add
                           [real_addr c (adjust_var v2); Const
                             bytes_in_word]));
               Assign 7 (Load (Op Add
                           [real_addr c (adjust_var v3); Const
                             bytes_in_word]));
               Inst (FP (FPMovFromReg 0 3 3));
               Inst (FP (FPMovFromReg 1 5 5));
               Inst (FP (FPMovFromReg 2 7 7));
               Inst (FP (fp_top_inst fpt));
               Inst (FP (FPMovToReg 3 5 0));
               WriteWord64 c header dest 3],l))
        else
         (case encode_header c 3 2 of
          | NONE => (GiveUp,l)
          | SOME header =>
            (list_Seq [
               Assign 15 (real_addr c (adjust_var v1));
               Assign 17 (real_addr c (adjust_var v2));
               Assign 19 (real_addr c (adjust_var v3));
               Assign 11 (Load (Op Add [Var 15; Const bytes_in_word]));
               Assign 13 (Load (Op Add [Var 15; Const (2w *
                 bytes_in_word)]));
               Assign 21 (Load (Op Add [Var 17; Const bytes_in_word]));
               Assign 23 (Load (Op Add [Var 17; Const (2w *
                 bytes_in_word)]));
               Assign 31 (Load (Op Add [Var 19; Const bytes_in_word]));
               Assign 33 (Load (Op Add [Var 19; Const (2w *
                 bytes_in_word)]));
               Inst (FP (FPMovFromReg 0 13 11));
               Inst (FP (FPMovFromReg 1 23 21));
               Inst (FP (FPMovFromReg 2 33 31));
               Inst (FP (fp_top_inst fpt));
               Inst (FP (FPMovToReg 5 3 0));
               WriteWord64_on_32 c header dest 5 3],l)))
      : 'a wordLang$prog # num`;
*)

(* HOL4 ML code, not ported:
val def = assign_Define `
  assign_FP_bop fpb (c:data_to_word$config) (secn:num)
             (l:num) (dest:num) (names:num_set option) v1 v2 =
       (if ~c.has_fp_ops then (GiveUp,l) else
        if dimindex(:'a) = 64 then
         (case encode_header c 3 1 of
          | NONE => (GiveUp,l)
          | SOME (header:'a word) =>
            (list_Seq [
               Assign 3 (Load (Op Add
                           [real_addr c (adjust_var v1); Const
                             bytes_in_word]));
               Assign 5 (Load (Op Add
                           [real_addr c (adjust_var v2); Const
                             bytes_in_word]));
               Inst (FP (FPMovFromReg 0 3 3));
               Inst (FP (FPMovFromReg 1 5 5));
               Inst (FP (fp_bop_inst fpb));
               Inst (FP (FPMovToReg 3 5 0));
               WriteWord64 c header dest 3],l))
        else
         (case encode_header c 3 2 of
          | NONE => (GiveUp,l)
          | SOME header =>
            (list_Seq [
               Assign 15 (real_addr c (adjust_var v1));
               Assign 17 (real_addr c (adjust_var v2));
               Assign 11 (Load (Op Add [Var 15; Const bytes_in_word]));
               Assign 13 (Load (Op Add [Var 15; Const (2w *
                 bytes_in_word)]));
               Assign 21 (Load (Op Add [Var 17; Const bytes_in_word]));
               Assign 23 (Load (Op Add [Var 17; Const (2w *
                 bytes_in_word)]));
               Inst (FP (FPMovFromReg 0 13 11));
               Inst (FP (FPMovFromReg 1 23 21));
               Inst (FP (fp_bop_inst fpb));
               Inst (FP (FPMovToReg 5 3 0));
               WriteWord64_on_32 c header dest 5 3],l)))
      : 'a wordLang$prog # num`;
*)

(* HOL4 ML code, not ported:
val def = assign_Define `
  assign_FP_uop fpu (c:data_to_word$config) (secn:num)
             (l:num) (dest:num) (names:num_set option) v1 =
       (if ~c.has_fp_ops then (GiveUp,l) else
        if dimindex(:'a) = 64 then
         (case encode_header c 3 1 of
          | NONE => (GiveUp,l)
          | SOME (header:'a word) =>
            (list_Seq [
               Assign 3 (Load (Op Add
                           [real_addr c (adjust_var v1); Const
                             bytes_in_word]));
               Inst (FP (FPMovFromReg 0 3 3));
               Inst (FP (fp_uop_inst fpu));
               Inst (FP (FPMovToReg 3 5 1));
               WriteWord64 c header dest 3],l))
        else
         (case encode_header c 3 2 of
          | NONE => (GiveUp,l)
          | SOME header =>
            (list_Seq [
               Assign 15 (real_addr c (adjust_var v1));
               Assign 11 (Load (Op Add [Var 15; Const bytes_in_word]));
               Assign 13 (Load (Op Add [Var 15; Const (2w *
                 bytes_in_word)]));
               Inst (FP (FPMovFromReg 0 13 11));
               Inst (FP (fp_uop_inst fpu));
               Inst (FP (FPMovToReg 5 3 1));
               WriteWord64_on_32 c header dest 5 3],l)))
      : 'a wordLang$prog # num`;
*)

(* HOL4 ML code, not ported:
val def = assign_Define `
  assign_FinaliseCons (l:num) (dest:num) v1 =
                 (Assign (adjust_var dest) (Var (adjust_var v1)),l)
      : 'a wordLang$prog # num`;
*)

let assign_def = cake_define
  `data_to_word_assign (c:data_to_word_config) (secn:num) (l:num)
  (dest:num) (op:closLang_op)
     (args:num list) (names:(one spt) option) =
     (match op with IntOp (Const i) -> assign_Const i l dest | GlobOp
       GlobalsPtr -> (Assign (adjust_var dest) (Lookup Globals),l) |
       GlobOp SetGlobalsPtr -> arg1 args (assign_SetGlobalsPtr c l dest)
       (Skip,l) | GlobOp (SetGlobal n) -> arg1 args (assign_SetGlobal c
       n l dest) (Skip,l) | GlobOp (Global n) -> assign_Global c n l
       dest | MemOp El -> arg2 args (assign_El c l dest) (Skip,l) |
       BlockOp (ElemAt n) -> arg1 args (assign_ElemAt c n l dest)
       (Skip,l) | MemOp DerefByte -> arg2 args (assign_DerefByte c l
       dest) (Skip,l) | MemOp Update -> arg3 args (assign_Update c l
       dest) (Skip,l) | MemOp UpdateCons -> arg3 args (assign_Update c l
       dest) (Skip,l) | MemOp UpdateByte -> arg3 args (assign_UpdateByte
       c l dest) (Skip,l) | MemOp FinaliseCons -> arg1 args
       (assign_FinaliseCons l dest) (Skip,l) | BlockOp ListAppend ->
       arg2 args (assign_ListAppend c secn l dest names) (Skip,l) |
       BlockOp (Cons tag) -> assign_Cons c l dest tag args | MemOp
       (MutCons tag _15) -> assign_MutCons c l dest tag args | MemOp
       ConfigGC -> arg2 args (assign_ConfigGC c secn l dest names)
       (Skip,l) | BlockOp (Build parts) -> assign_Build c secn l dest
       names parts | BlockOp (ConsExtend tag) -> assign_ConsExtend c
       secn l dest names tag args | MemOp Ref -> assign_Ref c secn l
       dest names args | ThunkOp (AllocThunk ev) -> arg1 args
       (assign_AllocThunk ev c secn l dest names) (Skip,l) | ThunkOp
       (UpdateThunk ev) -> arg2 args (assign_UpdateThunk ev c l dest)
       (Skip,l) | MemOp (RefByte imm) -> arg2 args (assign_RefByte c
       secn l dest names imm) (Skip,l) | MemOp XorByte -> arg2 args
       (assign_XorByte c secn l dest names) (Skip,l) | MemOp (StringCmp
       b cmp) -> arg2 args (assign_StringCmp c secn l dest names b cmp)
       (Skip,l) | Label n -> (LocValue (adjust_var dest) n,l) | MemOp
       (CopyByte alloc_new) -> assign_CopyByte c secn l dest names args
       | MemOp RefArray -> arg2 args (assign_RefArray c secn l dest
       names) (Skip,l) | BlockOp (BoolTest test) -> arg2 args
       (assign_BoolTest l dest test) (Skip,l) | BlockOp BoolNot -> arg1
       args (assign_BoolNot l dest) (Skip,l) | WordOp (WordTest ws test)
       -> arg2 args (assign_WordTest l dest test) (Skip,l) | BlockOp
       (FromList tag) -> arg2 args (assign_FromList c secn l dest names
       tag) (Skip,l) | IntOp (LessConstSmall i) -> arg1 args
       (assign_LessConstSmall l dest i) (Skip,l) | MemOp
       (BoundsCheckByte leq) ->
         arg2 args (assign_BoundsCheckByte c secn l dest names leq)
           (Skip,l) | MemOp BoundsCheckArray ->
         arg2 args (assign_BoundsCheckArray c secn l dest names)
           (Skip,l) | BlockOp BoundsCheckBlock ->
         arg2 args (assign_BoundsCheckBlock c secn l dest names)
           (Skip,l) | BlockOp (EQUAL) -> arg2 args (assign_Equal c secn
           l dest names) (Skip,l) | IntOp (LESS) -> arg2 args
           (assign_Less c secn l dest names) (Skip,l) | IntOp LessEq ->
           arg2 args (assign_LessEq c secn l dest names) (Skip,l) |
           BlockOp LengthBlock -> arg1 args (assign_LengthBlock c secn l
           dest names) (Skip,l) | MemOp Length -> arg1 args
           (assign_Length c secn l dest names) (Skip,l) | MemOp
           LengthByte -> arg1 args (assign_LengthByte c secn l dest
           names) (Skip,l) | BlockOp (TagLenEq tag len) ->
         arg1 args (assign_TagLenEq c secn l dest names tag len)
           (Skip,l) | BlockOp (LenEq len) -> arg1 args (assign_LenEq
           c secn l dest names len) (Skip,l) | BlockOp (TagEq tag) ->
           arg1 args (assign_TagEq c secn l dest names tag) (Skip,l)
           | IntOp Add -> arg2 args (assign_Add c secn l dest names)
           (Skip,l) | IntOp Sub -> arg2 args (assign_Sub c secn l
           dest names) (Skip,l) | IntOp Mult -> arg2 args
           (assign_Mult c secn l dest names) (Skip,l) | IntOp Div ->
           arg2 args (assign_Div c secn l dest names) (Skip,l) |
           IntOp Mod -> arg2 args (assign_Mod c secn l dest names)
           (Skip,l) | WordOp (WordOpw W8 opw) -> arg2 args
           (assign_WordOpW8 opw c secn l dest names) (Skip,l) |
           WordOp (WordOpw W64 opw) -> arg2 args (assign_WordOpW64
           opw c secn l dest names) (Skip,l) | WordOp (WordShift W8
           sh n) -> arg1 args (assign_WordShiftW8 sh n c secn l dest
           names) (Skip,l) | WordOp (WordShift W64 sh n) -> arg1 args
           (assign_WordShiftW64 sh n c secn l dest names) (Skip,l) |
           WordOp (WordFromWord b) -> arg1 args (assign_WordFromWord
           b c secn l dest names) (Skip,l) | WordOp (WordFromInt) ->
           arg1 args (assign_WordFromInt c secn l dest names)
           (Skip,l) | WordOp (WordToInt) -> arg1 args
           (assign_WordToInt c secn l dest names) (Skip,l) | FFI
           ffi_index -> arg2 args (assign_FFI ffi_index c secn l dest
           names) (Skip,l) | BlockOp (EqualConst p) -> arg1 args
           (assign_EqualConst p c secn l dest names) (Skip,l) |
           Install -> arg4 args (assign_Install c secn l dest names)
           (Skip,l) | WordOp (FP_cmp fpc) -> arg2 args (assign_FP_cmp
           fpc c secn l dest names) (Skip,l) | WordOp (FP_top fpt) ->
           arg3 args (assign_FP_top fpt c secn l dest names) (Skip,l)
           | WordOp (FP_bop fpb) -> arg2 args (assign_FP_bop fpb c
           secn l dest names) (Skip,l) | WordOp (FP_uop fpu) -> arg1
           args (assign_FP_uop fpu c secn l dest names) (Skip,l) |
           _16 -> (Skip,l))`;;
hol4_overload "assign" "data_to_word_assign";;

let force_thunk_def = cake_define
  `force_thunk (c:data_to_word_config) secn (l:num) ret loc v1 =
     (((match encode_header c (8 + 6) 1 with NONE -> (GiveUp,l) |
       SOME (header:'a word) ->
      If Test (adjust_var v1) (Imm (n2w 1))
        (match ret with NONE -> Return 0 [adjust_var v1] | SOME
          (dest,_17) -> Assign (adjust_var dest) (Var (adjust_var v1)))
        (list_Seq
           [Assign 1 (real_addr c (adjust_var v1));
            Assign 3 (Op And [Load (Var 1); Const (n2w 0b111100)]);
            If (EQUAL) 3 (Imm (n2w ((8 + 6) * 4)))
              (match ret with NONE ->
                  list_Seq
                    [Assign 1 (Load (Op Add [Var 1; Const
                      bytes_in_word]));
                     Return 0 [1]] | SOME (dest,_18) ->
                   Assign (adjust_var dest)
                          (Load (Op Add [Var 1; Const
                            bytes_in_word])))
            (If NotEqual 3 (Imm (n2w ((0 + 6) * 4)))
              (match ret with NONE -> Return 0 [adjust_var v1] | SOME
                (dest,_19) -> Assign (adjust_var dest) (Var (adjust_var
                v1)))
              (list_Seq
                 [Assign 5 (Load (Op Add [Var 1; Const
                   bytes_in_word]));
                  (match ret with NONE -> Call NONE (SOME loc) [0;
                    adjust_var v1; 5] NONE | SOME (r,ns) -> Call (SOME
                    ([adjust_var r],adjust_sets ns,Skip,secn,l))
                              (SOME loc) [adjust_var v1; 5]
                                NONE)]))])),l + 1):'a
                                wordLang_prog#num)`;;

let comp_def = cake_define
  `data_to_word_comp c (secn:num) (l:num) (p:dataLang_prog) =
     (match p with Skip -> ((Skip:'a wordLang_prog),l) | Tick ->
       (Tick,l) | Raise n -> (Raise (adjust_var n),l) | Return ns ->
       (Return 0 (MAP adjust_var ns),l) | Move n1 n2 -> (Move 0
       [(adjust_var n1,adjust_var n2)],l) | Seq p1 p2 ->
         (let (q1,l1) = data_to_word_comp c secn l p1 in
         let (q2,l2) = data_to_word_comp c secn l1 p2 in
           (Seq q1 q2,l2)) | If n p1 p2 ->
         (let (q1,l1) = data_to_word_comp c secn l p1 in
         let (q2,l2) = data_to_word_comp c secn l1 p2 in
           (If (EQUAL) (adjust_var n) (Imm (n2w 18)) q1 q2,l2)) |
             MakeSpace n names ->
         (let k = dimindex (:'a) DIV 8 in
         let w = n2w (n * k) in
         let w = if w2n w = n * k then w else --(n2w 0) in
           (Seq (Assign 1 (Op Sub [Lookup TriggerGC; Lookup
             NextFree]))
                (If Lower 1 (Imm w)
                  (list_Seq [SilentFFI c 3 (adjust_sets names);
                             Assign 1 (Const w);
                             Alloc 1 (adjust_sets names);
                             SilentFFI c 3 (adjust_sets names)])
                 Skip),l)) | Assign dest op args names -> assign c
                   secn l dest op args names | Force ret loc v ->
                   force_thunk c secn l ret loc v | Call ret target args
                   handler ->
         (match ret with NONE -> (Call NONE target (0 :: MAP
           adjust_var args) NONE,l) | SOME (ns,names) ->
             (let ret = SOME (MAP adjust_var ns,adjust_sets
               names,Skip,secn,l) in
               match handler with NONE -> (Call ret target (MAP
                 adjust_var args) NONE,l + 1) | SOME (n,p) ->
                   (let (q1,l1) = data_to_word_comp c secn (l + 2) p
                     in
                   let handler = SOME (adjust_var n,q1,secn,l + 1) in
                     (Call ret target (MAP adjust_var args)
                       handler,l1)))))`;;
hol4_overload "comp" "data_to_word_comp";;

let compile_part_def = cake_define
  `data_to_word_compile_part c (n,arg_count,p) = (n,arg_count + 1,FST
  (comp c n 2 p))`;;
hol4_overload "compile_part" "data_to_word_compile_part";;

let MemCopy_code_def = cake_define
  `MemCopy_code =
     (If Test 2 (Reg 2) (Return 0 [8])
         (list_Seq [Assign 1 (Load (Var 4));
                    Assign 2 (Op Sub [Var 2; Const (n2w 4)]);
                    Assign 4 (Op Add [Var 4; Const bytes_in_word]);
                    Store (Var 6) 1;
                    Assign 6 (Op Add [Var 6; Const bytes_in_word]);
                    Call NONE (SOME MemCopy_location) [0; 2; 4; 6;
                      8] NONE]):'a wordLang_prog)`;;

let ByteCopy_code_def = cake_define
  `ByteCopy_code c = (list_Seq
      [Assign 4 (ShiftVar Lsr 4 2);
       Assign 6 (ShiftVar Lsr 6 2);
       Assign 10 (ShiftVar Lsr 10 2);
       Assign 1 Unit;
       Assign 2 (Op Add [real_addr c 2; Const bytes_in_word; Var 4]);
       Assign 8 (Op Add [real_addr c 8; Const bytes_in_word; Var
         10]);
       If Lower 4 (Reg 10)
         (list_Seq [Assign 3 (Op Sub [Var 6; Const (n2w 1)]);
                    Assign 2 (Op Add [Var 2; Var 3]);
                    Assign 8 (Op Add [Var 8; Var 3]);
                    Call NONE (SOME ByteCopySub_location) [0; 6; 2;
                      8; 1] NONE])
         (Call NONE (SOME ByteCopyAdd_location) [0; 6; 2; 8; 1]
           NONE)]:'a wordLang_prog)`;;

let ByteCopyAdd_code_def = cake_define
  `ByteCopyAdd_code =
   If Lower 2 (Imm (n2w 4))
     (
       If Lower 2 (Imm (n2w 2))
       (
         If (EQUAL) 2 (Imm (n2w 0)) (Return 0 [8])
         (
           list_Seq [
             Inst (Mem Load8 1 (Addr 4 (n2w 0)));
             Inst (Mem Store8 1 (Addr 6 (n2w 0)));
             Return 0 [8]]))
       (list_Seq [
         Inst (Mem Load8 1 (Addr 4 (n2w 0)));
         Inst (Mem Load8 3 (Addr 4 (n2w 1)));
         If (EQUAL) 2 (Imm (n2w 2))
           (list_Seq [
             Inst (Mem Store8 1 (Addr 6 (n2w 0)));
             Inst (Mem Store8 3 (Addr 6 (n2w 1)));
             Return 0 [8]])
           (list_Seq [
             Inst (Mem Load8 5 (Addr 4 (n2w 2)));
             Inst (Mem Store8 1 (Addr 6 (n2w 0)));
             Inst (Mem Store8 3 (Addr 6 (n2w 1)));
             Inst (Mem Store8 5 (Addr 6 (n2w 2)));
             Return 0 [8]])]))
     (list_Seq [
      Inst (Mem Load8 1 (Addr 4 (n2w 0)));
      Inst (Mem Load8 3 (Addr 4 (n2w 1)));
      Inst (Mem Load8 5 (Addr 4 (n2w 2)));
      Inst (Mem Load8 7 (Addr 4 (n2w 3)));
      Inst (Mem Store8 1 (Addr 6 (n2w 0)));
      Inst (Mem Store8 3 (Addr 6 (n2w 1)));
      Inst (Mem Store8 5 (Addr 6 (n2w 2)));
      Inst (Mem Store8 7 (Addr 6 (n2w 3)));
      Assign 9 (Op Sub [Var 2; Const (n2w 4)]);
      Assign 11 (Op Add [Var 4; Const (n2w 4)]);
      Assign 13 (Op Add [Var 6; Const (n2w 4)]);
      Call NONE (SOME ByteCopyAdd_location) [0; 9; 11; 13; 8]
        NONE])`;;

let ByteCopySub_code_def = cake_define
  `ByteCopySub_code =
   If Lower 2 (Imm (n2w 4))
     (
       If Lower 2 (Imm (n2w 2))
       (
         If (EQUAL) 2 (Imm (n2w 0)) (Return 0 [8])
         (
           list_Seq [
             Inst (Mem Load8 1 (Addr 4 (n2w 0)));
             Inst (Mem Store8 1 (Addr 6 (n2w 0)));
             Return 0 [8]]))
       (list_Seq [
         Inst (Mem Load8 1 (Addr 4 (n2w 0)));
         Inst (Mem Load8 3 (Addr 4 (--(n2w 1))));
         If (EQUAL) 2 (Imm (n2w 2))
           (list_Seq [
             Inst (Mem Store8 1 (Addr 6 (n2w 0)));
             Inst (Mem Store8 3 (Addr 6 (--(n2w 1))));
             Return 0 [8]])
           (list_Seq [
             Inst (Mem Load8 5 (Addr 4 (--(n2w 2))));
             Inst (Mem Store8 1 (Addr 6 (n2w 0)));
             Inst (Mem Store8 3 (Addr 6 (--(n2w 1))));
             Inst (Mem Store8 5 (Addr 6 (--(n2w 2))));
             Return 0 [8]])]))
     (list_Seq [
      Inst (Mem Load8 1 (Addr 4 (n2w 0)));
      Inst (Mem Load8 3 (Addr 4 (--(n2w 1))));
      Inst (Mem Load8 5 (Addr 4 (--(n2w 2))));
      Inst (Mem Load8 7 (Addr 4 (--(n2w 3))));
      Inst (Mem Store8 1 (Addr 6 (n2w 0)));
      Inst (Mem Store8 3 (Addr 6 (--(n2w 1))));
      Inst (Mem Store8 5 (Addr 6 (--(n2w 2))));
      Inst (Mem Store8 7 (Addr 6 (--(n2w 3))));
      Assign 9 (Op Sub [Var 2; Const (n2w 4)]);
      Assign 11 (Op Sub [Var 4; Const (n2w 4)]);
      Assign 13 (Op Sub [Var 6; Const (n2w 4)]);
      Call NONE (SOME ByteCopySub_location) [0; 9; 11; 13; 8]
        NONE])`;;

let ByteCopyNew_code_def = cake_define
  `ByteCopyNew_code c = (Skip:'a wordLang_prog)`;;

let stubs_def = cake_define
  `data_to_word_stubs (:'ga) data_conf = [
     (FromList_location,4,(FromList_code data_conf));
     (FromList1_location,6,FromList1_code data_conf);
     (RefByte_location,4,RefByte_code data_conf);
     (RefArray_location,3,RefArray_code data_conf);
     (Replicate_location,5,Replicate_code);
     (AnyArith_location,4,AnyArith_code data_conf);
     (Add_location,3,Add_code);
     (Sub_location,3,Sub_code);
     (Mul_location,3,Mul_code);
     (Div_location,3,Div_code);
     (Mod_location,3,Mod_code);
     (Compare1_location,4,Compare1_code);
     (Compare_location,3,Compare_code data_conf);
     (Equal1_location,4,Equal1_code);
     (Equal_location,3,Equal_code data_conf);
     (LongDiv1_location,7,LongDiv1_code data_conf);
     (LongDiv_location,4,LongDiv_code data_conf);
     (Install_location,3,Install_code data_conf);
     (InstallCode_location,4,InstallCode_code data_conf);
     (InstallData_location,4,InstallData_code data_conf);
     (Append_location,3,Append_code data_conf);
     (AppendMainLoop_location,6,AppendMainLoop_code data_conf);
     (AppendLenLoop_location,3,AppendLenLoop_code data_conf);
     (XorLoop_location,4,XorLoop_code);
     (Unused_location,6,Skip);
     (StringCmpLoop_location,6,StringCmpLoop_code);
     (MemCopy_location,5,MemCopy_code);
     (ByteCopy_location,6,ByteCopy_code data_conf);
     (ByteCopyAdd_location,5,ByteCopyAdd_code);
     (ByteCopySub_location,5,ByteCopySub_code);
     (ByteCopyNew_location,4,ByteCopyNew_code data_conf);
     (Dummy_location,0,Skip)] ++ generated_bignum_stubs
       Bignum_location`;;
hol4_overload "stubs" "data_to_word_stubs";;

let stub_names_def = cake_define
  `data_to_word_stub_names one = [
     (FromList_location,(implode "_FromList"));
     (FromList1_location,(implode "_FromList1"));
     (RefByte_location,(implode "_RefByte"));
     (RefArray_location,(implode "_RefArray"));
     (Replicate_location,(implode "_Replicate"));
     (AnyArith_location,(implode "_AnyArith"));
     (Add_location,(implode "_Add"));
     (Sub_location,(implode "_Sub"));
     (Mul_location,(implode "_Mul"));
     (Div_location,(implode "_Div"));
     (Mod_location,(implode "_Mod"));
     (Compare1_location,(implode "_Compare1"));
     (Compare_location,(implode "_Compare"));
     (Equal1_location,(implode "_Equal1"));
     (Equal_location,(implode "_Equal"));
     (LongDiv1_location,(implode "_LongDiv1"));
     (LongDiv_location,(implode "_LongDiv"));
     (Install_location,(implode "_Install"));
     (InstallCode_location,(implode "_InstallCode"));
     (InstallData_location,(implode "_InstallData"));
     (Append_location,(implode "_Append"));
     (AppendMainLoop_location,(implode "_AppendMainLoop"));
     (AppendLenLoop_location,(implode "_AppendLenLoop"));
     (XorLoop_location,(implode "_XorLoop"));
     (Unused_location,(implode "_Unused"));
     (StringCmpLoop_location,(implode "_StringCmpLoop"));
     (MemCopy_location,(implode "_MemCopy"));
     (ByteCopy_location,(implode "_ByteCopy"));
     (ByteCopyAdd_location,(implode "_ByteCopyAdd"));
     (ByteCopySub_location,(implode "_ByteCopySub"));
     (ByteCopyNew_location,(implode "_ByteCopyNew"));
     (Dummy_location,(implode "_Dummy"))] ++ GENLIST (\i. (i +
       Bignum_location,(implode "_Bignum")))
     (data_num_stubs - Bignum_location)`;;
hol4_overload "stub_names" "data_to_word_stub_names";;

let compile_def = cake_define
  `data_to_word_compile data_conf word_conf asm_conf prog =
     (let data_conf =
       (data_to_word_config_has_fp_tern_fupd (K (asm_config_ISA
         asm_conf = ARMv7 /\ 2 < asm_config_fp_reg_count asm_conf))
         (data_to_word_config_has_fp_ops_fupd (K (1 <
         asm_config_fp_reg_count asm_conf)) data_conf)) in
     let p = stubs (:'ga) data_conf ++ MAP (compile_part data_conf)
       prog in
       word_to_word_compile word_conf (asm_conf:'a asm_config) p)`;;
hol4_overload "compile" "data_to_word_compile";;

let compile_0_def = cake_define
  `compile_0 data_conf (asm_conf:'a asm_config) prog =
     (let data_conf = (data_to_word_config_has_fp_tern_fupd (K
       (asm_config_ISA asm_conf = ARMv7 /\
                              2 < asm_config_fp_reg_count asm_conf))
                                (data_to_word_config_has_fp_ops_fupd (K
                                (1 < asm_config_fp_reg_count asm_conf))
                                data_conf)) in
       stubs (:'a) data_conf ++ MAP (compile_part data_conf) prog)`;;

(* compute bignum call graph *)

(* HOL4 ML code, not ported:
val th_FF = EVAL ``full_call_graph AnyArith_location
       (fromAList (stubs (:'a) (data_conf with <| call_empty_ffi := F ;
                                                     has_longdiv := F
                                                       |>)))``
val th_FT = EVAL ``full_call_graph AnyArith_location
       (fromAList (stubs (:'a) (data_conf with <| call_empty_ffi := F ;
                                                     has_longdiv := T
                                                       |>)))``
val th_TF = EVAL ``full_call_graph AnyArith_location
       (fromAList (stubs (:'a) (data_conf with <| call_empty_ffi := T ;
                                                     has_longdiv := F
                                                       |>)))``
val th_TT = EVAL ``full_call_graph AnyArith_location
       (fromAList (stubs (:'a) (data_conf with <| call_empty_ffi := T ;
                                                     has_longdiv := T
                                                       |>)))``
*)

(* PENDING: the value is the call graph that HOL4 computes with EVAL;
   the expression that it evaluates has a free variable
   (data_conf), so the port has to compute the value as well
Definition AnyArith_call_tree_def:
  AnyArith_call_tree = ^(th_FF |> concl |> rand )
End *)

let structure_le_def = cake_define
  `structure_le x1 x2 =
      match (x1,x2) with
        (Leaf,_20) -> T
      | (_21,Unknown) -> T
      | ((Const k1 t1),(Const k2 t2)) ->
     (k1 <= k2 /\ structure_le t1 t2)
      | ((Call n1 t2),(Call m1 u2)) ->
     (n1 = m1 /\ structure_le t2 u2)
      | ((Branch t1 t2),(Branch u1 u2)) ->
     (structure_le t1 u1 /\ structure_le t2 u2)
      | (_22,_23) -> F`;;
