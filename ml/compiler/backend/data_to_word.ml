(* ======================================================== *)
(*  data_to_word: ported from HOL4's
    compiler/backend/data_to_wordScript.sml
    A definition theory, with 201 definitions, 3 datatypes and 40
    theorems.  Needed by 21 files of the port.  *)
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
needs "lib/byte.ml";;
needs "lib/comparison.ml";;
needs "lib/multiword.ml";;
needs "lib/sptree.ml";;
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
hol4_field_overload "has_fp_ops" "data_to_word_config_has_fp_ops";;
hol4_field_overload "has_fp_ops_fupd"
  "data_to_word_config_has_fp_ops_fupd";;
hol4_field_overload "be" "data_to_word_config_be";;
hol4_field_overload "be_fupd" "data_to_word_config_be_fupd";;

let adjust_var_def = cake_define
  `adjust_var n = 2 * n + (2:num)`;;

let adjust_set_def = cake_define
  `adjust_set (names:'a spt) =
     ((fromAList (MAP (\(n,k). (adjust_var n,one)) (toAList
       names))):1 spt)`;;

let adjust_sets_def = cake_define
  `adjust_sets (names:'a spt) =
     ((LS one,adjust_set names):1 spt#1 spt)`;;

let unit_def = cake_define
  `data_to_word_Unit = Const (n2w 2)`;;
hol4_overload "Unit" "data_to_word_Unit";;

let GiveUp_def = cake_define
  `GiveUp = (Seq (Assign 1 (wordLang_Const (--(n2w 1))))
                (Alloc 1 (adjust_sets (LN:1 spt))):'a
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
       (word_slice (l - 1) 2) (word_not ((n2w 0):'a word)))`;;

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

let StoreEach_def = cake_define_list
  [`StoreEach v [] (offset:'a word) = wordLang_Skip`;
   `StoreEach v (x :: xs) (offset:'a word) =
         wordLang_Seq (wordLang_Store (wordLang_Op asm_Add
           [wordLang_Var v; wordLang_Const offset]) x)
             (StoreEach v xs (offset + bytes_in_word))`];;

let small_shift_length_def = cake_define
  `small_shift_length conf = data_to_word_config_len_bits conf +
  data_to_word_config_tag_bits conf + 1`;;

let shift_length_def = cake_define
  `shift_length conf = 1 + data_to_word_config_pad_bits conf +
  data_to_word_config_len_bits conf + data_to_word_config_tag_bits
  conf + 1`;;

let conf_ok_def = cake_define
  `conf_ok (:'a) c <=>
     shift_length c < dimindex (:'a) /\
     backend_common_word_shift (:'a) <= shift_length c /\
       ~(data_to_word_config_len_size c = 0) /\
       data_to_word_config_len_size
     c + 7 < dimindex (:'a)`;;

let max_heap_limit_def = cake_define
  `max_heap_limit (:'a) c =
     MIN (dimword (:'a) DIV 2 EXP shift_length c)
         (dimword (:'a) DIV 2 EXP (backend_common_word_shift (:'a)
           + 1))`;;

let all_ones_def = cake_define
  `all_ones m n = (if m <= n then (n2w 0) else (word_slice (m - 1) n)
  (word_not (n2w 0)))`;;

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
     (let k = backend_common_word_shift (:'a) in
     let l = shift_length conf in
       if k = l /\ data_to_word_config_len_bits conf = 0 /\
         data_to_word_config_tag_bits conf = 0 then
         Op asm_Add [wordLang_Lookup CurrHeap; Op asm_Sub [Var r;
           Const (n2w 1)]] else if k <= data_to_word_config_pad_bits
           conf + 1 then
         Op asm_Add [wordLang_Lookup CurrHeap; (\sh e n. Shift sh e
           (wordLang_Const (n2w n))) Lsr (Var r) (l - k)] else
         Op asm_Add [wordLang_Lookup CurrHeap; (\sh e n. Shift sh
           e (wordLang_Const (n2w n))) Lsl ((\sh e n. Shift sh e
           (wordLang_Const (n2w n))) Lsr (Var r) l) k])`;;

let real_offset_def = cake_define
  `((real_offset (conf:data_to_word_config) r):'a wordLang_exp) =
      Op asm_Add [Const bytes_in_word;
              if dimindex (:'a) = 32 then Var r else (\sh e n.
                Shift sh e (wordLang_Const (n2w n))) Lsl (Var r) 1]`;;

let real_byte_offset_def = cake_define
  `(real_byte_offset r:'a wordLang_exp) =
     Op asm_Add [Const bytes_in_word;
             (\sh e n. Shift sh e (wordLang_Const (n2w n))) Lsr
               (Var r) 2]`;;

let word_op_type_INDUCT,word_op_type_RECURSION = define_datatype
  "word_op_type = Bitwise (binop) | Carried (binop)";;

let lookup_word_op_def = cake_define_list
  [`lookup_word_op backend_common_Andw = Bitwise And`;
   `lookup_word_op backend_common_Orw = Bitwise asm_Or`;
   `lookup_word_op (Xor:opw) = Bitwise Xor`;
   `lookup_word_op (Add:opw) = Carried asm_Add`;
   `lookup_word_op (Sub:opw) = Carried asm_Sub`];;

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

(* HOL4 data_to_wordScript.sml:273-274: a theorem that HOL4 states as
   the value of an ML expression: FromList_location_eq *)
(* HOL4 data_to_wordScript.sml:275-276: a theorem that HOL4 states as
   the value of an ML expression: FromList1_location_eq *)
(* HOL4 data_to_wordScript.sml:277-278: a theorem that HOL4 states as
   the value of an ML expression: RefByte_location_eq *)
(* HOL4 data_to_wordScript.sml:279-280: a theorem that HOL4 states as
   the value of an ML expression: RefArray_location_eq *)
(* HOL4 data_to_wordScript.sml:281-282: a theorem that HOL4 states as
   the value of an ML expression: Replicate_location_eq *)
(* HOL4 data_to_wordScript.sml:283-284: a theorem that HOL4 states as
   the value of an ML expression: AnyArith_location_eq *)
(* HOL4 data_to_wordScript.sml:285-286: a theorem that HOL4 states as
   the value of an ML expression: Add_location_eq *)
(* HOL4 data_to_wordScript.sml:287-288: a theorem that HOL4 states as
   the value of an ML expression: Sub_location_eq *)
(* HOL4 data_to_wordScript.sml:289-290: a theorem that HOL4 states as
   the value of an ML expression: Mul_location_eq *)
(* HOL4 data_to_wordScript.sml:291-292: a theorem that HOL4 states as
   the value of an ML expression: Div_location_eq *)
(* HOL4 data_to_wordScript.sml:293-294: a theorem that HOL4 states as
   the value of an ML expression: Mod_location_eq *)
(* HOL4 data_to_wordScript.sml:295-296: a theorem that HOL4 states as
   the value of an ML expression: Compare1_location_eq *)
(* HOL4 data_to_wordScript.sml:297-298: a theorem that HOL4 states as
   the value of an ML expression: Compare_location_eq *)
(* HOL4 data_to_wordScript.sml:299-300: a theorem that HOL4 states as
   the value of an ML expression: Equal1_location_eq *)
(* HOL4 data_to_wordScript.sml:301-302: a theorem that HOL4 states as
   the value of an ML expression: Equal_location_eq *)
(* HOL4 data_to_wordScript.sml:303-304: a theorem that HOL4 states as
   the value of an ML expression: LongDiv1_location_eq *)
(* HOL4 data_to_wordScript.sml:305-306: a theorem that HOL4 states as
   the value of an ML expression: LongDiv_location_eq *)
(* HOL4 data_to_wordScript.sml:307-308: a theorem that HOL4 states as
   the value of an ML expression: MemCopy_location_eq *)
(* HOL4 data_to_wordScript.sml:309-310: a theorem that HOL4 states as
   the value of an ML expression: Bignum_location_eq *)
(* HOL4 data_to_wordScript.sml:311-312: a theorem that HOL4 states as
   the value of an ML expression: ByteCopy_location_eq *)
(* HOL4 data_to_wordScript.sml:313-314: a theorem that HOL4 states as
   the value of an ML expression: ByteCopyAdd_location_eq *)
(* HOL4 data_to_wordScript.sml:315-316: a theorem that HOL4 states as
   the value of an ML expression: ByteCopySub_location_eq *)
(* HOL4 data_to_wordScript.sml:317-318: a theorem that HOL4 states as
   the value of an ML expression: ByteCopyNew_location_eq *)
(* HOL4 data_to_wordScript.sml:319-320: a theorem that HOL4 states as
   the value of an ML expression: Install_location_eq *)
(* HOL4 data_to_wordScript.sml:321-322: a theorem that HOL4 states as
   the value of an ML expression: InstallCode_location_eq *)
(* HOL4 data_to_wordScript.sml:323-324: a theorem that HOL4 states as
   the value of an ML expression: InstallData_location_eq *)
(* HOL4 data_to_wordScript.sml:325-326: a theorem that HOL4 states as
   the value of an ML expression: Dummy_location_eq *)
(* HOL4 data_to_wordScript.sml:327-328: a theorem that HOL4 states as
   the value of an ML expression: Append_location_eq *)
(* HOL4 data_to_wordScript.sml:329-330: a theorem that HOL4 states as
   the value of an ML expression: AppendMainLoop_location_eq *)
(* HOL4 data_to_wordScript.sml:331-332: a theorem that HOL4 states as
   the value of an ML expression: AppendLenLoop_location_eq *)
(* HOL4 data_to_wordScript.sml:333-334: a theorem that HOL4 states as
   the value of an ML expression: XorLoop_location_eq *)
(* HOL4 data_to_wordScript.sml:335-336: a theorem that HOL4 states as
   the value of an ML expression: Unused_location_eq *)
(* HOL4 data_to_wordScript.sml:337-338: a theorem that HOL4 states as
   the value of an ML expression: StringCmpLoop_location_eq *)

let SilentFFI_def = cake_define
  `SilentFFI c n names =
     (if data_to_word_config_call_empty_ffi c then
       list_Seq [Assign n (wordLang_Const (n2w 0));
                 Assign 7 (Op asm_Sub [wordLang_Lookup NextFree;
                   wordLang_Lookup CurrHeap]);
                 Assign 9 (wordLang_Lookup HeapLength);
                 FFI (implode "") 7 n 9 n names] else Skip)`;;

let AllocVar_def = cake_define
  `AllocVar c (limit':num) (names:1 spt) =
     list_Seq [Assign 1 ((\sh e n. Shift sh e (wordLang_Const (n2w
       n))) Lsr (Var 1) 2);
               If asm_Lower 1 (Imm (n2w limit'))
                 (Assign 1 ((\sh e n. Shift sh e (wordLang_Const (n2w
                   n))) Lsl (Op asm_Add [Var 1; Const (n2w 1)])
                   (backend_common_word_shift (:'a))))
                 (Assign 1 (wordLang_Const (--((n2w 1):'a word))));
               Assign 3 (Op asm_Sub [wordLang_Lookup TriggerGC;
                 wordLang_Lookup NextFree]);
               If asm_Lower 3 (Reg 1)
                 (list_Seq [SilentFFI c 3 (FST (adjust_sets names),
                              insert 1 one (SND (adjust_sets
                                names)));
                            Alloc 1 (adjust_sets names);
                            SilentFFI c 3 (adjust_sets names)])
                              Skip]`;;

let MakeBytes_def = cake_define
  `MakeBytes n =
     (list_Seq [Assign n ((\sh e n. Shift sh e (wordLang_Const (n2w
       n))) Lsr (Var n) 2);
               Assign n (Op asm_Or [Var n; (\sh e n. Shift sh e
                 (wordLang_Const (n2w n))) Lsl (Var n) 8]);
               Assign n (Op asm_Or [Var n; (\sh e n. Shift sh e
                 (wordLang_Const (n2w n))) Lsl (Var n) 16]);
               if dimindex (:'a) = 32 then Skip else
                 Assign n (Op asm_Or [Var n; (\sh e n. Shift sh e
                   (wordLang_Const (n2w n))) Lsl (Var n) 32])]:'a
                   wordLang_prog)`;;

let SmallLsr_def = cake_define
  `SmallLsr e n = (if n = 0 then e else (\sh e n. Shift sh e
  (wordLang_Const (n2w n))) Lsr e n)`;;

let WriteLastByte_aux_def = cake_define
  `WriteLastByte_aux offset a b n p =
     If Equal n (Imm offset) Skip
       (Seq (Inst (asm_Mem asm_Store8 b (Addr a offset))) p)`;;

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
       (let limit' = MIN (2 EXP data_to_word_config_len_size c)
         (dimword (:'a) DIV 16) in
       let h = Op asm_Add [(\sh e n. Shift sh e (wordLang_Const (n2w
         n))) Lsr (Var 2) 2; Const bytes_in_word] in
       let x = SmallLsr h (dimindex (:'a) - 63) in
       let y = (\sh e n. Shift sh e (wordLang_Const (n2w n))) Lsl h
         (dimindex (:'a) - backend_common_word_shift (:'a) -
         data_to_word_config_len_size c) in
         list_Seq
           [BignumHalt 2;
            Assign 1 x;
            AllocVar c limit' (sptree_fromList [one; one; one]);
            Assign 5 ((\sh e n. Shift sh e (wordLang_Const (n2w n)))
              Lsr h (backend_common_word_shift (:'a)));
            Assign 7 ((\sh e n. Shift sh e (wordLang_Const (n2w n)))
              Lsl (Var 5) 2);
            Assign 9 (wordLang_Lookup NextFree);
            Assign 1 (Op asm_Add [Var 9;
                              (\sh e n. Shift sh e (wordLang_Const
                                (n2w n))) Lsl (Var 5)
                                (backend_common_word_shift (:'a))]);
            Set NextFree (Op asm_Add [Var 1; Const bytes_in_word]);
            Assign 3 (Op asm_Or [(\sh e n. Shift sh e (wordLang_Const
              (n2w n))) Lsl (Op asm_Sub [Var 9; wordLang_Lookup
              CurrHeap])
                (shift_length c - backend_common_word_shift (:'a));
                  Const ((n2w 1):'a word)]);
            Assign 5 (Op asm_Or [Op asm_Or [y; Const (n2w 7)]; Var
              6]);
            MakeBytes 4;
            Store (Var 9) 5;
            Assign 11 (Op And [(\sh e n. Shift sh e (wordLang_Const
              (n2w n))) Lsr (Var 2) 2;
                              Const (bytes_in_word - (n2w 1))]);
            Assign 13 (wordLang_Const (n2w 0));
            Store (Var 1) 13;
            WriteLastBytes 1 4 11;
            Assign 7 (Op asm_Sub [Var 7; Const (n2w 4)]);
            Call NONE (SOME Replicate_location)
              [0; 9; 4; 7; 3] NONE]:'a wordLang_prog)`;;

let maxout_bits_code_def = cake_define
  `Maxout_bits_code rep_len k dest n =
     (If asm_Lower n (Imm (n2w (2 EXP rep_len - 1)))
       (Assign dest (Op asm_Or [Var dest; (\sh e n. Shift sh e
         (wordLang_Const (n2w n))) Lsl (Var n) k]))
       (Assign dest (Op asm_Or [Var dest; Const (all_ones (k +
         rep_len) k)])):'a wordLang_prog)`;;

let make_ptr_bits_code_def = cake_define
  `Make_ptr_bits_code c tag len dest =
     (list_Seq [Assign dest (Op asm_Or
        [Const (n2w 1); (\sh e n. Shift sh e (wordLang_Const (n2w
          n))) Lsl (Op asm_Sub [wordLang_Lookup NextFree;
          wordLang_Lookup CurrHeap])
            (shift_length c - backend_common_word_shift (:'a))]);
         Maxout_bits_code (data_to_word_config_tag_bits c) (1 +
           data_to_word_config_len_bits c) dest tag;
         Maxout_bits_code (data_to_word_config_len_bits c) 1 dest
           len]:'a wordLang_prog)`;;

let FromList_code_def = cake_define
  `FromList_code c =
     (let limit' = MIN (2 EXP data_to_word_config_len_size c)
       (dimword (:'a) DIV 16) in
     let h = (\sh e n. Shift sh e (wordLang_Const (n2w n))) Lsl (Var
       2) (dimindex (:'a) - data_to_word_config_len_size c - 2) in
       If Equal 2 (Imm (n2w 0))
         (list_Seq [Assign 6 (Op asm_Add [Var 6; Const ((n2w 2):'a
           word)]);
                    Return 0 [6]])
         (list_Seq
           [BignumHalt 2;
            Assign 1 (Var 2); AllocVar c limit' (sptree_fromList
              [one; one; one]);
            Assign 1 (wordLang_Lookup NextFree);
            Assign 5 (Op asm_Or [h; Const (n2w 3); Var 6]);
            Assign 7 ((\sh e n. Shift sh e (wordLang_Const (n2w n)))
              Lsr (Var 2) 2);
            Assign 9 ((\sh e n. Shift sh e (wordLang_Const (n2w n)))
              Lsr (Var 6) 4);
            Make_ptr_bits_code c 9 7 3;
            Call NONE (SOME FromList1_location) [0; 1; 4; 2; 3; 5]
              NONE]):'a wordLang_prog)`;;

let FromList1_code_def = cake_define
  `FromList1_code c =
     (list_Seq
       [Store (Var 2) 10;
        Assign 2 (Op asm_Add [Var 2; Const bytes_in_word]);
        If Equal 6 (Imm (n2w 0))
          (list_Seq
             [Set NextFree (Var 2);
              Return 0 [8]])
          (list_Seq
             [Assign 4 (real_addr c 4);
              Assign 10 (wordLang_Load (Op asm_Add [Var 4; Const
                bytes_in_word]));
              Assign 4 (wordLang_Load (Op asm_Add [Var 4; Const ((n2w
                2) * bytes_in_word)]));
              Assign 6 (Op asm_Sub [Var 6; Const (n2w 4)]);
              Call NONE (SOME FromList1_location) [0; 2; 4; 6; 8;
                10] NONE])]:'a wordLang_prog)`;;

let RefArray_code_def = cake_define
  `RefArray_code c =
         (list_Seq
           [Assign 1 ((\sh e n. Shift sh e (wordLang_Const (n2w n)))
             Lsl (Op asm_Add [((\sh e n. Shift sh e (wordLang_Const (n2w
             n))) Lsr (Var 2) 2); Const (n2w 1)])
                       (backend_common_word_shift (:'a)));
            Set TriggerGC (Op asm_Sub [wordLang_Lookup TriggerGC; Var
              1]);
            Assign 1 (Op asm_Sub [wordLang_Lookup EndOfHeap; Var 1]);
            Set EndOfHeap (Var 1);
            Assign 3 (Op asm_Or [(\sh e n. Shift sh e (wordLang_Const
              (n2w n))) Lsl (Op asm_Sub [Var 1; wordLang_Lookup
              CurrHeap])
                (shift_length c - backend_common_word_shift (:'a));
                  Const ((n2w 1):'a word)]);
            Assign 5 (Op asm_Or [(\sh e n. Shift sh e (wordLang_Const
              (n2w n))) Lsl (Var 2)
                              (dimindex (:'a) -
                                data_to_word_config_len_size c - 2);
                             Const (make_header c (n2w 2) 0)]);
            Store (Var 1) 5;
            Call NONE (SOME Replicate_location)
               [0; 1; 4; 2; 3] NONE]:'a wordLang_prog)`;;

let replicate_code_def = cake_define
  `Replicate_code =
     (If Equal 6 (Imm (n2w 0)) (Return 0 [8])
       (list_Seq [Assign 2 (Op asm_Add [Var 2; Const
         (bytes_in_word)]);
                  Store (Var 2) 4;
                  Assign 6 (Op asm_Sub [Var 6; Const (n2w 4)]);
                  Call NONE (SOME Replicate_location) [0; 2; 4; 6;
                    8] NONE]):'a wordLang_prog)`;;

let AddNumSize_def = cake_define
  `AddNumSize c src =
     (If Equal (adjust_var src) (Imm (n2w 0)) Skip
       (If Test (adjust_var src) (Imm (n2w 1))
          (Assign 1 (Op asm_Add [Var 1; Const (n2w 4)]))
        (Assign 1 (Op asm_Add [Var 1;
          ((\sh e n. Shift sh e (wordLang_Const (n2w n))) Lsl ((\sh e
            n. Shift sh e (wordLang_Const (n2w n))) Lsr
             (Load (real_addr c (adjust_var src)))
                (dimindex (:'a) - data_to_word_config_len_size
                  c))) 2]))):'a wordLang_prog)`;;

let AnyHeader_def = cake_define
  `AnyHeader c r a t1 t2 t3 =
     If Equal r (Imm ((n2w 0):'a word))
       (list_Seq [Assign 7 (wordLang_Const (n2w 0));
                  Set (Temp t1) (Var r);
                  Set (Temp t2) (Var r);
                  Set (Temp t3) (Var r)])
    (If asm_NotTest r (Imm (n2w 1))
       (list_Seq
         [Assign 7 (real_addr c r);
          Set (Temp t2) (Op asm_Add [Var 7; Const bytes_in_word]);
          Set (Temp t1) (Op asm_Add
            [(\sh e n. Shift sh e (wordLang_Const (n2w n))) Lsl ((\sh
              e n. Shift sh e (wordLang_Const (n2w n))) Lsr (Load (Var
              7)) ((dimindex (:'a)) - data_to_word_config_len_size c))
              1;
             Op And [Const (n2w 1); (\sh e n. Shift sh e
               (wordLang_Const (n2w n))) Lsr (Load (Var 7)) 4]]);
          Set (Temp t3) (wordLang_Const (n2w 0))])
    (If asm_NotLess r (Imm (n2w 0))
       (list_Seq
         [Set (Temp t1) (wordLang_Const (n2w 2));
          Set (Temp t2) (wordLang_Lookup (if a then OtherHeap else
            NextFree));
          Set (Temp t3) ((\sh e n. Shift sh e (wordLang_Const (n2w
            n))) Lsr (Var r) 2);
          Assign 7 (wordLang_Const (n2w 0))])
       (list_Seq
         [Set (Temp t1) (wordLang_Const (n2w 3));
          Set (Temp t2) (wordLang_Lookup (if a then OtherHeap else
            NextFree));
          Set (Temp t3) (Op asm_Sub [Const (n2w 0); (\sh e n. Shift
            sh e (wordLang_Const (n2w n))) Asr (Var r) 2]);
          Assign 7 (wordLang_Const (n2w 0))])))`;;

let ShiftVar_def = cake_define
  `ShiftVar sh v n =
     (if sh = Ror then
       (let m = (if n < dimindex (:'a) then n else n MOD (dimindex
         (:'a))) in
          if m = 0 then Var v else (\sh e n. Shift sh e
            (wordLang_Const (n2w n))) sh (Var v) m) else if n = 0 then
            Var v else if dimindex (:'a) <= n then
       if sh = Asr then (\sh e n. Shift sh e (wordLang_Const (n2w
         n))) sh (Var v) (dimindex (:'a) - 1) else Const (n2w 0) else
         ((\sh e n. Shift sh e (wordLang_Const (n2w n))) sh (Var v)
         n):'a wordLang_exp)`;;

let AnyArith_code_def = cake_define
  `AnyArith_code c = (list_Seq [
       Assign 1 (wordLang_Const (n2w 4));
       AddNumSize c 0;
       AddNumSize c 1;
       Set (Temp (n2w 29)) (Var 1);
       AllocVar c (2 EXP data_to_word_config_len_size c)
         (sptree_fromList [one; one; one]);
       AnyHeader c 2 F (n2w 0) (n2w 31) (n2w 12);
       AnyHeader c 4 T (n2w 1) (n2w 30) (n2w 11);
       Get 1 (Temp (n2w 11));
       Store (wordLang_Lookup OtherHeap) 1;
       Get 1 (Temp (n2w 12));
       Store (wordLang_Lookup NextFree) 1;
       Get 1 (Temp (n2w 29));
       Assign 2 (wordLang_Lookup NextFree);
       Set (Temp (n2w 29)) (Var 2);
       Set (Temp (n2w 3)) ((\sh e n. Shift sh e (wordLang_Const (n2w
         n))) Lsr (Var 6) 2);
       Assign 3 (wordLang_Const (n2w 0));
       Call (SOME ([0],(sptree_fromList
         [one],LN),Skip,AnyArith_location,2))
         (SOME Replicate_location) [2; 3; 1; 0] NONE;
       Set (Temp (n2w 29)) (Op asm_Add [wordLang_Lookup (Temp (n2w
         29)); Const bytes_in_word]);
       Call (SOME ([1],(sptree_fromList
         [one],LN),Skip,AnyArith_location,3))
         (SOME Bignum_location) [] NONE;
       Get 1 (Temp (n2w 10));
       If Test 1 (Reg 1) (Return 0 [1]) Skip;
       Assign 3 (wordLang_Load (Op asm_Add [wordLang_Lookup NextFree;
         Const bytes_in_word]));
       If Equal 1 (Imm (n2w 2))
         (Seq (Assign 5 ((\sh e n. Shift sh e (wordLang_Const (n2w
           n))) Lsr (Var 3) (dimindex (:'a) - 3)))
              (If Test 5 (Reg 5)
                 (Seq (Assign 1 ((\sh e n. Shift sh e (wordLang_Const
                   (n2w n))) Lsl (Var 3) 2))
                      (Return 0 [1]))
                 Skip))
         (If Equal 1 (Imm (n2w 3))
           (Seq (Assign 5 ((\sh e n. Shift sh e (wordLang_Const (n2w
             n))) Lsr (Op asm_Sub [Var 3; Const (n2w 1)])
                             (dimindex (:'a) - 3)))
                (If Test 5 (Reg 5)
                   (Seq (Assign 1 (Op asm_Sub [Const (n2w 0); (\sh e
                     n. Shift sh e (wordLang_Const (n2w n))) Lsl (Var 3)
                     2]))
                        (Return 0 [1]))
                   Skip))
           (Assign 5 (wordLang_Const (n2w 0))));
       Assign 5 (wordLang_Lookup NextFree);
       Assign 6 (ShiftVar Lsr 1 1);
       Assign 8 (Op And [Var 1; Const (n2w 1)]);
       Assign 7 (Op asm_Or [Const (n2w 0b1111);
                        ShiftVar Lsl 6 (dimindex (:'a) -
                          data_to_word_config_len_size c);
                        ShiftVar Lsl 8 4]);
       Store (Var 5) 7;
       Assign 1 (Op asm_Sub [Var 5; wordLang_Lookup CurrHeap]);
       Assign 1 (Op asm_Or [ShiftVar Lsl 1 (shift_length c -
         backend_common_word_shift (:'a)); Const (n2w 1)]);
       Set NextFree (Op asm_Add [Var 5; Const bytes_in_word;
                             ShiftVar Lsl 6
                               (backend_common_word_shift (:'a))]);
       Return 0 [1]]:'a wordLang_prog)`;;

let add_code_def = cake_define
  `Add_code = (Seq (Assign 6 (wordLang_Const (n2w (4 * 0))))
                  (Call NONE (SOME AnyArith_location) [0; 2; 4; 6]
                    NONE):'a wordLang_prog)`;;

let sub_code_def = cake_define
  `Sub_code = (Seq (Assign 6 (wordLang_Const (n2w (4 * 1))))
                  (Call NONE (SOME AnyArith_location) [0; 2; 4; 6]
                    NONE):'a wordLang_prog)`;;

let mul_code_def = cake_define
  `Mul_code = (Seq (Assign 6 (wordLang_Const (n2w (4 * 4))))
                  (Call NONE (SOME AnyArith_location) [0; 2; 4; 6]
                    NONE):'a wordLang_prog)`;;

let div_code_def = cake_define
  `Div_code = (Seq (Assign 6 (wordLang_Const (n2w (4 * 5))))
                  (Call NONE (SOME AnyArith_location) [0; 2; 4; 6]
                    NONE):'a wordLang_prog)`;;

let mod_code_def = cake_define
  `Mod_code = (Seq (Assign 6 (wordLang_Const (n2w (4 * 6))))
                  (Call NONE (SOME AnyArith_location) [0; 2; 4; 6]
                    NONE):'a wordLang_prog)`;;

let install_code_def = cake_define
  `Install_code c =
       (list_Seq [Assign 1 (wordLang_Lookup BitmapBuffer);
                 Assign 3 (wordLang_Lookup CodeBuffer);
                 Set BitmapBuffer (Var 2);
                 Set CodeBuffer (Var 4);
                 Install 3 4 1 2 (LS one,LN);
                 Return 0 [3]]:'a wordLang_prog)`;;

let InstallCode_code_def = cake_define
  `InstallCode_code c =
        (If Test 2 (Imm (n2w 1))
         (Seq (Assign 2 (wordLang_Lookup BitmapBuffer))
              (Call NONE (SOME InstallData_location) [0; 2; 4; 6]
                NONE))
         (list_Seq [Assign 3 (real_addr c 2);
                    Assign 2 (wordLang_Load (Op asm_Add [Var 3; Const
                      bytes_in_word]));
                    Assign 2 (ShiftVar Lsr 2 2);
                    CodeBufferWrite 6 2;
                    Assign 6 (Op asm_Add [Var 6; Const (n2w 1)]);
                    Assign 2 (wordLang_Load (Op asm_Add [Var 3; Const
                      ((n2w 2) * bytes_in_word)]));
                    Call NONE (SOME InstallCode_location) [0; 2;
                      4; 6] NONE]):'a wordLang_prog)`;;

let InstallData_code_def = cake_define
  `InstallData_code c =
        (If Test 4 (Imm (n2w 1))
         (list_Seq [Call NONE (SOME Install_location) [0; 2; 6]
           NONE])
         (list_Seq [Assign 3 (real_addr c 4);
                    Assign 4 (wordLang_Load (Op asm_Add [Var 3; Const
                      bytes_in_word]));
                    Assign 4 (real_addr c 4);
                    Assign 4 (wordLang_Load (Op asm_Add [Var 4; Const
                      bytes_in_word]));
                    DataBufferWrite 2 4;
                    Assign 2 (Op asm_Add [Var 2; Const
                      bytes_in_word]);
                    Assign 4 (wordLang_Load (Op asm_Add [Var 3; Const
                      ((n2w 2) * bytes_in_word)]));
                    Call NONE (SOME InstallData_location) [0; 2;
                      4; 6] NONE]):'a wordLang_prog)`;;

let compare1_code_def = cake_define
  `Compare1_code =
     If Equal 2 (Imm (n2w 0))
       (Seq (Assign 2 (wordLang_Const (n2w 1))) (Return 0 [2]))
       (list_Seq
          [Assign 8 (wordLang_Load (Var 4));
           Assign 9 (wordLang_Load (Var 6));
           If Equal 8 (Reg 9)
             (list_Seq
                [Assign 2 (Op asm_Sub [Var 2; Const (n2w 1)]);
                 Assign 4 (Op asm_Sub [Var 4; Const bytes_in_word]);
                 Assign 6 (Op asm_Sub [Var 6; Const bytes_in_word]);
                 Call NONE (SOME Compare1_location) [0; 2; 4; 6]
                   NONE])
             (If asm_Lower 8 (Reg 9)
               (Seq (Assign 2 (wordLang_Const (n2w 0))) (Return 0
                 [2]))
               (Seq (Assign 2 (wordLang_Const (n2w 2))) (Return 0
                 [2])))])`;;

let compare_code_def = cake_define
  `Compare_code c =
     If Test 2 (Imm (n2w 1))
       (list_Seq [Assign 1 (wordLang_Load (real_addr c 4));
                  If Test 1 (Imm (n2w 16))
                    (Seq (Assign 2 (wordLang_Const (n2w 0))) (Return
                      0 [2]))
                    (Seq (Assign 2 (wordLang_Const (n2w 2))) (Return
                      0 [2]))])
    (If Test 4 (Imm (n2w 1))
       (list_Seq [Assign 1 (wordLang_Load (real_addr c 2));
                  If Test 1 (Imm ((n2w 16):'a word))
                    (Seq (Assign 2 (wordLang_Const (n2w 2))) (Return
                      0 [2]))
                    (Seq (Assign 2 (wordLang_Const (n2w 0))) (Return
                      0 [2]))])
       (list_Seq [Assign 11 (real_addr c 2);
                  Assign 1 (wordLang_Load (Var 11));
                  Assign 13 (real_addr c 4);
                  Assign 3 (wordLang_Load (Var 13));
                  Assign 6 ((\sh e n. Shift sh e (wordLang_Const (n2w
                    n))) Lsr (Var 1) ((dimindex (:'a) -
                    data_to_word_config_len_size c)));
                  Assign 8 ((\sh e n. Shift sh e (wordLang_Const (n2w
                    n))) Lsr (Var 3) ((dimindex (:'a) -
                    data_to_word_config_len_size c)));
                  If Equal 1 (Reg 3)
                    (list_Seq
                      [Assign 2 (Op asm_Add [Var 11; (\sh e n. Shift
                        sh e (wordLang_Const (n2w n))) Lsl (Var 6)
                        (backend_common_word_shift (:'a))]);
                       Assign 4 (Op asm_Add [Var 13; (\sh e n. Shift
                         sh e (wordLang_Const (n2w n))) Lsl (Var 6)
                         (backend_common_word_shift (:'a))]);
                       If Test 1 (Imm (n2w 16))
                        (Call NONE (SOME Compare1_location) [0; 6; 2;
                          4] NONE)
                        (Call NONE (SOME Compare1_location) [0; 6; 4;
                          2] NONE)])
                    (If Test 1 (Imm (n2w 16))
                       (If Test 3 (Imm (n2w 16))
                          (If asm_Lower 6 (Reg 8)
                             (Seq (Assign 2 (wordLang_Const (n2w 0)))
                               (Return 0 [2]))
                             (Seq (Assign 2 (wordLang_Const (n2w 2)))
                               (Return 0 [2])))
                          (Seq (Assign 2 (wordLang_Const (n2w 2)))
                            (Return 0 [2])))
                       (If Test 3 (Imm (n2w 16))
                          (Seq (Assign 2 (wordLang_Const (n2w 0)))
                            (Return 0 [2]))
                          (If asm_Lower 6 (Reg 8)
                             (Seq (Assign 2 (wordLang_Const (n2w 2)))
                               (Return 0 [2]))
                             (Seq (Assign 2 (wordLang_Const (n2w
                               0))) (Return 0 [2])))))]))`;;

let equal1_code_def = cake_define
  `Equal1_code =
     list_Seq [
       If Equal 2 (Imm (n2w 0))
         (Seq (Assign 2 (wordLang_Const (n2w 1))) (Return 0 [2]))
           Skip;
       Assign 1 (wordLang_Load (Var 4));
       Assign 3 (wordLang_Load (Var 6));
       Call (SOME ([5],(list_insert [0; 2; 4; 6]
         LN,LN),Skip,Equal1_location,2))
         (SOME Equal_location) [1; 3] NONE;
       If Equal 5 (Imm (n2w 1)) Skip (Return 0 [5]);
       Assign 2 (Op asm_Sub [Var 2; Const (n2w 1)]);
       Assign 4 (Op asm_Add [Var 4; Const bytes_in_word]);
       Assign 6 (Op asm_Add [Var 6; Const bytes_in_word]);
       Call NONE (SOME Equal1_location) [0; 2; 4; 6] NONE]`;;

let equal_code_def = cake_define
  `Equal_code c =
     list_Seq [
       If Equal 2 (Reg 4)
         (Seq (Assign 2 (wordLang_Const ((n2w 1):'a word))) (Return 0
           [2])) Skip;
       Assign 1 (Op And [Var 2; Var 4]);
       If Test 1 (Imm (n2w 1))
         (Seq (Assign 2 (wordLang_Const (n2w 0))) (Return 0 [2]))
           Skip;
       Assign 20 (real_addr c 2);
       Assign 40 (real_addr c 4);
       Assign 21 (wordLang_Load (Var 20));
       Assign 41 (wordLang_Load (Var 40));
       If Test 21 (Imm (n2w 0b1100)) (list_Seq
           [Assign 1 (Op And [Var 21; Const (tag_mask c || (n2w
             2))]);
            If Equal 1 (Imm (n2w (16 * closure_tag + 2)))
              (Seq (Assign 2 (wordLang_Const (n2w 1))) (Return 0
                [2])) Skip;
            If Equal 1 (Imm (n2w (16 * partial_app_tag + 2)))
              (Seq (Assign 2 (wordLang_Const (n2w 1))) (Return 0
                [2])) Skip;
            If Equal 21 (Reg 41)
              Skip (Seq (Assign 2 (wordLang_Const (n2w 0))) (Return 0
                [2]));
            Assign 6 (ShiftVar Lsr 21 ((dimindex (:'a) -
              data_to_word_config_len_size c)));
            Assign 20 (Op asm_Add [Var 20; Const bytes_in_word]);
            Assign 40 (Op asm_Add [Var 40; Const bytes_in_word]);
            Call NONE (SOME Equal1_location) [0; 6; 20; 40] NONE])
         Skip;
       If Equal 21 (Reg 41) Skip
         (Seq (Assign 2 (wordLang_Const (n2w 0))) (Return 0 [2]));
       If Test 21 (Imm (n2w 4))
         (Seq (Assign 2 (wordLang_Const (n2w 0))) (Return 0 [2]))
           Skip;
       Assign 1 (Op And [Var 21; Const (n2w 24)]);
       If Equal 1 (Imm (n2w 16))
         (Seq (Assign 2 (wordLang_Const (n2w 0))) (Return 0 [2]))
           Skip;
       Assign 6 (ShiftVar Lsr 21 ((dimindex (:'a) -
         data_to_word_config_len_size c)));
       Assign 2 (Op asm_Add [Var 20; ShiftVar Lsl 6
         (backend_common_word_shift (:'a))]);
       Assign 4 (Op asm_Add [Var 40; ShiftVar Lsl 6
         (backend_common_word_shift (:'a))]);
       Call NONE (SOME Compare1_location) [0; 6; 2; 4] NONE]`;;

let LongDiv_code_def = cake_define
  `LongDiv_code c =
     (if data_to_word_config_has_longdiv c then
       list_Seq [Inst (Arith (asm_LongDiv 1 3 2 4 6));
                 Set (Temp (n2w 28)) (Var 3);
                 Return 0 [1]] else
       Seq (Assign 10 (wordLang_Const ((n2w 0):'a word)))
      (Seq (Assign 11 (wordLang_Const (n2w (dimindex (:'a)))))
           (Call NONE (SOME LongDiv1_location) [0; 11; 6; 10; 10;
             4; 2] NONE)))`;;

let LongDiv1_code_def = cake_define
  `LongDiv1_code c =
     (if data_to_word_config_has_longdiv c then Skip else
       If Test 2 (Reg 2)
         (Seq (Set (Temp (n2w 28)) (Var 10):'a wordLang_prog) (Return
           0 [8]))
         (list_Seq [Assign 6 (Op asm_Or [ShiftVar Lsr 6 1;
                              ShiftVar Lsl 4 (dimindex (:'a) - 1)]);
                    Assign 4 (ShiftVar Lsr 4 1);
                    Assign 8 (ShiftVar Lsl 8 1);
                    Assign 2 (Op asm_Sub [Var 2; Const ((n2w 1):'a
                      word)]);
                    If asm_Lower 12 (Reg 4)
                      (Call NONE (SOME LongDiv1_location)
                        [0; 2; 4; 6; 8; 10; 12] NONE) Skip;
                    If Equal 12 (Reg 4)
                      (If asm_Lower 10 (Reg 6)
                         (Call NONE (SOME LongDiv1_location)
                            [0; 2; 4; 6; 8; 10; 12] NONE) Skip) Skip;
                    Assign 8 (Op asm_Add [Var 8; Const (n2w 1)]);
                    Assign 16 (Op Xor [Var 6; Const (--(n2w 1))]);
                    Assign 14 (Op Xor [Var 4; Const (--(n2w 1))]);
                    Assign 1 (wordLang_Const (n2w 1));
                    Inst (Arith (asm_AddCarry 10 10 16 1));
                    Inst (Arith (asm_AddCarry 12 12 14 1));
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
              Assign 1 (wordLang_Lookup NextFree);
              Assign 3 (wordLang_Const header);
              Assign 5 (Op asm_Sub [wordLang_Lookup TriggerGC; Var
                1]);
              Assign 7 (Op asm_Or [(\sh e n. Shift sh e
                (wordLang_Const (n2w n))) Lsl (Op asm_Sub [Var 1;
                wordLang_Lookup CurrHeap])
                              (shift_length c -
                                backend_common_word_shift (:'a));
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
        Assign 3 (wordLang_Load (Op asm_Add [Var 1; Const
          bytes_in_word]));
        Assign 5 (wordLang_Load (Op asm_Add [Var 1; Const ((n2w 2) *
          bytes_in_word)]));
        If asm_Lower 8 (Imm ((n2w 3) * bytes_in_word))
          (Seq (Assign 1 (wordLang_Const (n2w 0)))
               (Call NONE (SOME AppendLenLoop_location) [0; 4; 1]
                 NONE)) Skip;
        Store (Var 2) 6;
        Store (Op asm_Add [Var 2; Const bytes_in_word]) 3;
        If Test 5 (Imm (n2w 1)) Skip
          (list_Seq
            [Assign 10 (Op asm_Add [Var 10;
               Const (n2w (3 * 2 EXP shift_length c))]);
             Assign 8 (Op asm_Sub [Var 8; Const ((n2w 3) *
               bytes_in_word)]);
             Store (Op asm_Add [Var 2; Const ((n2w 2) *
               bytes_in_word)]) 10;
             Assign 2 (Op asm_Add [Var 2; Const ((n2w 3) *
               bytes_in_word)]);
             Call NONE (SOME AppendMainLoop_location) [0; 2; 5; 6; 8;
               10] NONE]);
        Assign 1 (wordLang_Lookup (Temp (n2w 0)));
        Assign 3 (wordLang_Lookup (Temp (n2w 2)));
        Store (Op asm_Add [Var 2; Const ((n2w 2) * bytes_in_word)])
          1;
        Set NextFree (Op asm_Add [Var 2; Const ((n2w 3) *
          bytes_in_word)]);
        Return 0 [3]]:'a wordLang_prog)`;;

let AppendLenLoop_code_def = cake_define
  `AppendLenLoop_code c =
     If Test 2 (Imm (n2w 1))
       (list_Seq
         [Assign 1 (Op asm_Sub [wordLang_Lookup TriggerGC;
           wordLang_Lookup NextFree]);
          Assign 1 (Op asm_Add [Var 4; ShiftVar Lsr 1
            (backend_common_word_shift (:'a) - 2)]);
          Assign 4 (wordLang_Lookup (Temp (n2w 0)));
          Assign 2 (wordLang_Lookup (Temp (n2w 1)));
          AllocVar c (dimword (:'a) DIV 8 - 1) (sptree_fromList [one;
            one]);
          Call NONE (SOME Append_location) [0; 4; 2] NONE])
       (list_Seq
         [Assign 2 (wordLang_Load (Op asm_Add [real_addr c 2; Const
           ((n2w 2) * bytes_in_word)]));
          Assign 4 (Op asm_Add [Var 4; Const ((n2w 12):'a word)]);
          Call NONE (SOME AppendLenLoop_location) [0; 2; 4] NONE])`;;

let XorLoop_code_def = cake_define
  `XorLoop_code =
     (If asm_Lower 6 (Imm (n2w 2))
       (If Equal 6 (Imm (n2w 0))
          (list_Seq [Assign 1 (wordLang_Const (n2w 2));
                     Return 0 [1]])
          (list_Seq [Assign 5 (wordLang_Load (Var 4));
                     Assign 3 (wordLang_Load (Var 2));
                     Assign 7 (Op Xor [Var 5; Var 3]);
                     Store (Var 2) 7;
                     Assign 1 (wordLang_Const (n2w 2));
                     Return 0 [1]]))
       (list_Seq [Assign 5 (wordLang_Load (Var 4));
                  Assign 3 (wordLang_Load (Var 2));
                  Assign 9 (wordLang_Load (Op asm_Add [Var 4; Const
                    bytes_in_word]));
                  Assign 7 (wordLang_Load (Op asm_Add [Var 2; Const
                    bytes_in_word]));
                  Assign 6 (Op asm_Sub [Var 6; Const (n2w 2)]);
                  Assign 5 (Op Xor [Var 5; Var 3]);
                  Assign 9 (Op Xor [Var 9; Var 7]);
                  Store (Var 2) 5;
                  Store (Op asm_Add [Var 2; Const bytes_in_word]) 9;
                  Assign 4 (Op asm_Add [Var 4; Const ((n2w 2) *
                    bytes_in_word)]);
                  Assign 2 (Op asm_Add [Var 2; Const ((n2w 2) *
                    bytes_in_word)]);
                  Call NONE (SOME XorLoop_location) [0; 2; 4; 6]
                    NONE]):'a wordLang_prog)`;;

let StringCmpLoop_code_def = cake_define
  `StringCmpLoop_code =
     (If Equal 6 (Imm bytes_in_word)
       (Return 0 [8; 10])
       (list_Seq
          [Inst (asm_Mem asm_Load8 1 (Addr 2 (n2w 0)));
           Inst (asm_Mem asm_Load8 3 (Addr 4 (n2w 0)));
           If asm_NotEqual 1 (Reg 3) (Return 0 [1; 3]) Skip;
           Assign 2 (Op asm_Add [Var 2; Const (n2w 1)]);
           Assign 4 (Op asm_Add [Var 4; Const (n2w 1)]);
           Assign 6 (Op asm_Sub [Var 6; Const (n2w 1)]);
           Call NONE (SOME StringCmpLoop_location) [0; 2; 4; 6; 8;
             10] NONE]):'a wordLang_prog)`;;

let get_names_def = cake_define_list
  [`data_to_word_get_names NONE = LN`;
   `data_to_word_get_names (SOME x) = x`];;
hol4_overload "get_names" "data_to_word_get_names";;

let LoadWord64_def = cake_define
  `LoadWord64 c i j =
     (Assign i (wordLang_Load (Op asm_Add [real_addr c j; Const
       bytes_in_word])):'a wordLang_prog)`;;

let LoadBignum_def = cake_define
  `LoadBignum c header word1' k = (list_Seq [
     Assign word1' (real_addr c k);
     Assign header (wordLang_Load (Var word1'));
     Assign word1' (wordLang_Load (Op asm_Add [Var word1'; Const
       bytes_in_word]))]:'a wordLang_prog)`;;

let WriteWord64_def = cake_define
  `WriteWord64 c (header:'a word) dest i =
     (list_Seq [Assign 1 (wordLang_Lookup NextFree);
               Store (Op asm_Add [Var 1; Const bytes_in_word]) i;
               Assign 3 (wordLang_Const header);
               Store (Var 1) 3;
               Set NextFree (Op asm_Add [Var 1; Const ((n2w 2) *
                 bytes_in_word)]);
               Assign (adjust_var dest)
                 (Op asm_Or [(\sh e n. Shift sh e (wordLang_Const
                   (n2w n))) Lsl (Op asm_Sub [Var 1; wordLang_Lookup
                   CurrHeap])
                           (shift_length c -
                             backend_common_word_shift (:'a));
                         Const (n2w 1)])]:'a wordLang_prog)`;;

let WriteWord64_on_32_def = cake_define
  `WriteWord64_on_32 c (header:'a word) dest i1 i2 =
     (list_Seq [Assign 1 (wordLang_Lookup NextFree);
               Store (Op asm_Add [Var 1; Const bytes_in_word]) i2;
               Store (Op asm_Add [Var 1; Const ((n2w 2) *
                 bytes_in_word)]) i1;
               Assign 3 (wordLang_Const header);
               Store (Var 1) 3;
               Set NextFree (Op asm_Add [Var 1; Const ((n2w 3) *
                 bytes_in_word)]);
               Assign (adjust_var dest)
                 (Op asm_Or [(\sh e n. Shift sh e (wordLang_Const
                   (n2w n))) Lsl (Op asm_Sub [Var 1; wordLang_Lookup
                   CurrHeap])
                           (shift_length c -
                             backend_common_word_shift (:'a));
                         Const (n2w 1)])]:'a wordLang_prog)`;;

let WriteWord32_on_32_def = cake_define
  `WriteWord32_on_32 c header dest i1 =
      list_Seq
        [Assign 1 (wordLang_Lookup NextFree);
         Store (Op asm_Add [Var 1; Const bytes_in_word]) i1;
         Assign 3 (wordLang_Const header); Store (Var 1) 3;
         Set NextFree (Op asm_Add [Var 1; Const ((n2w 2) *
           bytes_in_word)]);
         Assign (adjust_var dest)
           (Op asm_Or
              [(\sh e n. Shift sh e (wordLang_Const (n2w n))) Lsl (Op
                asm_Sub [Var 1; wordLang_Lookup CurrHeap])
                 (shift_length c - backend_common_word_shift
                   (:'a)); Const ((n2w 1):'a word)])]`;;

let WordOp64_on_32_def = cake_define
  `WordOp64_on_32 (opw:opw) =
     (match opw with backend_common_Andw -> list_Seq [Assign 29
       (wordLang_Const (n2w 0));
                         Assign 27 (wordLang_Const (n2w 0));
                         Assign 33 (Op And [Var 13; Var 23]);
                         Assign 31 (Op And [Var 11; Var 21])] |
                           backend_common_Orw -> list_Seq [Assign 29
                           (wordLang_Const (n2w 0));
                         Assign 27 (wordLang_Const (n2w 0));
                         Assign 33 (Op asm_Or [Var 13; Var 23]);
                         Assign 31 (Op asm_Or [Var 11; Var 21])] |
                           Xor -> list_Seq [Assign 29 (wordLang_Const
                           (n2w 0));
                         Assign 27 (wordLang_Const (n2w 0));
                         Assign 33 (Op Xor [Var 13; Var 23]);
                         Assign 31 (Op Xor [Var 11; Var 21])] | Add
                           -> list_Seq [Assign 29 (wordLang_Const (n2w
                           0));
                         Assign 27 (wordLang_Const (n2w 0));
                         Inst (Arith (asm_AddCarry 33 13 23 29));
                         Inst (Arith (asm_AddCarry 31 11 21 29))] |
                           Sub -> list_Seq [Assign 29 (wordLang_Const
                           (n2w 1));
                         Assign 27 (Op Xor [Const (--(n2w 1)); Var
                           23]);
                         Inst (Arith (asm_AddCarry 33 13 27 29));
                         Assign 27 (Op Xor [Const (--(n2w 1)); Var
                           21]);
                         Inst (Arith (asm_AddCarry 31 11 27 29))])`;;

let WordShift64_on_32_def = cake_define
  `WordShift64_on_32 sh n = list_Seq
     (if sh = Ror then
       (let n = n MOD 64 in
         (if n < 32 then
            [Assign 33 (Op asm_Or [ShiftVar Lsl 11 (32 - n);
                              ShiftVar Lsr 13 n]);
             Assign 31 (Op asm_Or [ShiftVar Lsl 13 (32 - n);
                              ShiftVar Lsr 11 n])] else
            [Assign 33 (Op asm_Or [ShiftVar Lsl 13 (64 - n);
                              ShiftVar Lsr 11 (n - 32)]);
             Assign 31 (Op asm_Or [ShiftVar Lsl 11 (64 - n);
                              ShiftVar Lsr 13 (n - 32)])])) else
       if n < 32 then
         (match sh with Lsl -> [Assign 33 (ShiftVar sh 13 n);
                    Assign 31 (Op asm_Or [ShiftVar Lsr 13 (32 - n);
                              ShiftVar sh 11 n])] | Lsr -> [Assign 33
                                (Op asm_Or [ShiftVar Lsl 11 (32 - n);
                              ShiftVar sh 13 n]);
                    Assign 31 (ShiftVar sh 11 n)] | Asr -> [Assign 33
                      (Op asm_Or [ShiftVar Lsl 11 (32 - n);
                              ShiftVar Lsr 13 n]);
                    Assign 31 (ShiftVar sh 11 n)] | Ror -> []) else
         (match sh with Lsl -> [Assign 33 (wordLang_Const (n2w 0));
           Assign 31 (ShiftVar sh 13 (n - 32))] | Lsr -> [Assign 33
           (ShiftVar sh 11 (n - 32)); Assign 31 (wordLang_Const (n2w
           0))] | Asr -> [Assign 33 (ShiftVar sh 11 (n - 32));
                    Assign 31 (ShiftVar sh 11 32)] | Ror -> []))`;;

let smallnum_def = cake_define
  `Smallnum i =
     (if i < (&0) then (n2w 0) - n2w (num_of_int ((&4) * ((&0) -
       i))) else n2w (num_of_int ((&4) * i)))`;;

(* HOL4 data_to_wordScript.sml:1099: the overload FALSE_CONST, which
   the port expands *)
(* HOL4 data_to_wordScript.sml:1100: the overload TRUE_CONST, which
   the port expands *)

let MemEqList_def = cake_define_list
  [`MemEqList a [] = (Assign 1 (Const (n2w 18:'a word)):'a
  wordLang_prog)`;
   `MemEqList a (w :: ws) =
         ((Seq (Assign 5 (wordLang_Load (Op asm_Add [Var 3; Const
           a])))
             (If Equal 5 (Imm w) (MemEqList (a + bytes_in_word)
               ws) Skip)):'a wordLang_prog)`];;

let get_gen_size_def = cake_define_list
  [`get_gen_size [] = bytes_in_word * ((--(n2w 1)):'a word)`;
   `get_gen_size (x :: xs) =
         (if w2n (bytes_in_word:'a word) * x < dimword (:'a)
           then bytes_in_word * n2w x else bytes_in_word * (--(n2w
           1)))`];;

let fp_cmp_inst_def = cake_define_list
  [`fp_cmp_inst FP_Less = FPLess 3 0 1`;
   `fp_cmp_inst FP_LessEqual = FPLessEqual 3 0 1`;
   `fp_cmp_inst FP_Greater = FPLess 3 1 0`;
   `fp_cmp_inst FP_GreaterEqual = FPLessEqual 3 1 0`;
   `fp_cmp_inst FP_Equal = FPEqual 3 0 1`];;

let fp_top_inst_def = cake_define
  `fp_top_inst FP_Fma = FPFma 0 1 2`;;

let fp_bop_inst_def = cake_define
  `fp_bop_inst x1 =
      match x1 with
        fpSem_FP_Add -> FPAdd 0 0 1
      | fpSem_FP_Sub -> FPSub 0 0 1
      | fpSem_FP_Mul -> FPMul 0 0 1
      | fpSem_FP_Div -> FPDiv 0 0 1`;;

let fp_uop_inst_def = cake_define
  `fp_uop_inst x1 =
      match x1 with
        fpSem_FP_Neg -> FPNeg 1 0
      | fpSem_FP_Abs -> FPAbs 1 0
      | fpSem_FP_Sqrt -> FPSqrt 1 0`;;

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

let arg2_pmatch = cake_theorem "arg2_pmatch"
  (fun () ->
    `data_to_word_arg2 vs f x = (match vs with [v1; v2] -> f v1 v2 |
  _5 -> x)`)
  CHEAT_TAC;;

let arg3_pmatch = cake_theorem "arg3_pmatch"
  (fun () ->
    `arg3 vs f x = (match vs with [v1; v2; v3] -> f v1 v2 v3 | _6 ->
  x)`)
  CHEAT_TAC;;

let arg4_pmatch = cake_theorem "arg4_pmatch"
  (fun () ->
    `arg4 vs f x = (match vs with [v1; v2; v3; v4] -> f v1 v2 v3 v4 |
  _7 -> x)`)
  CHEAT_TAC;;

(* HOL4 data_to_wordScript.sml:1176-1180: ML code, not ported *)

let assign_Const_def = cake_define
  `assign_Const i (l:num) (dest:num) =
         (if i < (&0) then (Assign (adjust_var dest)
           (wordLang_Const ((n2w 0) - n2w (num_of_int ((&4) * ((&0) -
           i))))),l) else (Assign (adjust_var dest) (wordLang_Const
           (n2w (num_of_int ((&4) * i)))),l):'a wordLang_prog#num)`;;

let assign_SetGlobalsPtr_def = cake_define
  `assign_SetGlobalsPtr (c:data_to_word_config) (l:num) (dest:num) v1 =
       ((Seq (Set Globals (Var (adjust_var v1)))
       (Seq (Set GlobReal (real_addr c (adjust_var v1)))
            (Assign (adjust_var dest) data_to_word_Unit)),l):'a
              wordLang_prog#num)`;;

let assign_Global_def = cake_define
  `assign_Global (c:data_to_word_config) n (l:num) (dest:num) =
       ((Assign (adjust_var dest) (wordLang_Load (Op asm_Add
         [wordLang_Lookup GlobReal;
                              Const (bytes_in_word * n2w (n +
                                1))])),l):'a wordLang_prog#num)`;;

let assign_SetGlobal_def = cake_define
  `assign_SetGlobal (c:data_to_word_config) n (l:num) (dest:num) v1 =
       ((Seq (Store (Op asm_Add [wordLang_Lookup GlobReal; Const
         (bytes_in_word * n2w (n + 1))])
                   (adjust_var v1))
            (Assign (adjust_var dest) data_to_word_Unit),l):'a
              wordLang_prog#num)`;;

let assign_El_def = cake_define
  `assign_El (c:data_to_word_config) (l:num) (dest:num) v1 v2 =
                          ((Assign (adjust_var dest)
                             (wordLang_Load (Op asm_Add [real_addr c
                               (adjust_var v1);
                              real_offset c (adjust_var
                                v2)])),l):'a wordLang_prog#num)`;;

let assign_ElemAt_def = cake_define
  `assign_ElemAt (c:data_to_word_config) n (l:num) (dest:num) v1 =
                          ((Assign (adjust_var dest)
                             (wordLang_Load (Op asm_Add [real_addr c
                               (adjust_var v1);
                              Const (bytes_in_word +
                              bytes_in_word * n2w n)])),l):'a
                                wordLang_prog#num)`;;

let assign_DerefByte_def = cake_define
  `assign_DerefByte (c:data_to_word_config) (l:num) (dest:num) v1 v2 =
          ((list_Seq [
             Assign 1 (Op asm_Add [real_addr c (adjust_var v1);
                              real_byte_offset (adjust_var v2)]);
             Inst (asm_Mem asm_Load8 3 (Addr 1 (n2w 0)));
             Assign (adjust_var dest) ((\sh e n. Shift sh e
               (wordLang_Const (n2w n))) Lsl (Var 3) 2)],l):'a
               wordLang_prog#num)`;;

let assign_Update_def = cake_define
  `assign_Update (c:data_to_word_config) (l:num) (dest:num) v1 v2 v3 =
                  ((Seq (Store (Op asm_Add [real_addr c (adjust_var
                    v1);
                              real_offset c (adjust_var v2)])
                              (adjust_var v3))
                       (Assign (adjust_var dest)
                         data_to_word_Unit),l):'a wordLang_prog#num)`;;

let assign_UpdateThunk_def = cake_define
  `assign_UpdateThunk ev (c:data_to_word_config) (l:num) (dest:num) v1
  v2 =
       ((match ev with NotEvaluated ->
            (Seq (Store (Op asm_Add [real_addr c (adjust_var v1);
                              Const bytes_in_word])
                        (adjust_var v2))
                 (Assign (adjust_var dest) data_to_word_Unit),l) |
                   Evaluated ->
            (match encode_header c (8 + 6) 1 with NONE -> (GiveUp,l)
              | SOME (header:'a word) -> (list_Seq
                 [Assign 1 (real_addr c (adjust_var v1));
                  Assign 3 (wordLang_Const header);
                  Store (Var 1) 3;
                  Store (Op asm_Add [Var 1; Const bytes_in_word])
                    (adjust_var v2);
                  Assign (adjust_var dest)
                    data_to_word_Unit],l))):'a wordLang_prog#num)`;;

let assign_UpdateByte_def = cake_define
  `assign_UpdateByte (c:data_to_word_config) (l:num) (dest:num) v1 v2 v3
  =
       ((list_Seq [
           Assign 1 (Op asm_Add [real_addr c (adjust_var v1);
                             real_byte_offset (adjust_var v2)]);
           Assign 3 ((\sh e n. Shift sh e (wordLang_Const (n2w n)))
             Lsr (Var (adjust_var v3)) 2);
           Inst (asm_Mem asm_Store8 3 (Addr 1 (n2w 0)));
           Assign (adjust_var dest) data_to_word_Unit],l):'a
             wordLang_prog#num)`;;

let assign_ListAppend_def = cake_define
  `assign_ListAppend (c:data_to_word_config) (secn:num) (l:num)
  (dest:num) (names:(1 spt) option) v1 v2 =
          ((match encode_header c 0 2 with NONE -> (GiveUp,l) | SOME
            (header:'a word) ->
            ((wordLang_MustTerminate
              (wordLang_Call (SOME ([adjust_var dest],adjust_sets
                (data_to_word_get_names names),Skip,secn,l))
                 (SOME Append_location)
                    [adjust_var v2; adjust_var v1] NONE):'a
                      wordLang_prog),l + 1)):'a wordLang_prog#num)`;;

let assign_Cons_def = cake_define
  `assign_Cons (c:data_to_word_config) (l:num) (dest:num) tag args =
                   (if LENGTH args = 0 then
                     if tag < dimword (:'a) DIV 16 then
                       (Assign (adjust_var dest) (wordLang_Const (n2w
                         (16 * tag + 2))),l) else (GiveUp,l) else
                     (match encode_header c (4 * tag) (LENGTH args)
                       with NONE -> (GiveUp,l) | SOME (header:'a word)
                       -> (list_Seq
                         [Assign 1 (wordLang_Lookup NextFree);
                          Assign 3 (wordLang_Const header);
                          StoreEach 1 (3 :: MAP adjust_var args) (n2w
                            0);
                          Assign (adjust_var dest)
                            (Op asm_Or [(\sh e n. Shift sh e
                              (wordLang_Const (n2w n))) Lsl (Op asm_Sub
                              [Var 1; wordLang_Lookup CurrHeap])
                              (shift_length c -
                                backend_common_word_shift (:'a));
                              Const ((n2w 1) ||
                              (word_bits (small_shift_length c - 1)
                                0)
                              (ptr_bits c tag (LENGTH args)))]);
                          Set NextFree (Op asm_Add [Var 1;
                            Const (bytes_in_word * n2w (LENGTH
                              args + 1))])],l)):'a wordLang_prog#num)`;;

let assign_MutCons_def = cake_define
  `assign_MutCons (c:data_to_word_config) (l:num) (dest:num) tag args =
     (match data_to_word_config_gc_kind c with
       data_to_word_Generational _8 -> (GiveUp,l) | _9 ->
       (assign_Cons (c:data_to_word_config) (l:num) (dest:num) tag
       args:'a wordLang_prog#num))`;;

let assign_ConfigGC_def = cake_define
  `assign_ConfigGC (c:data_to_word_config) (secn:num) (l:num) (dest:num)
  (names:(1 spt) option) v1 v2 =
              ((list_Seq [SilentFFI c 3 (adjust_sets
                (data_to_word_get_names names));
                         Assign 1 (wordLang_Const (n2w 0));
                         Alloc 1 (adjust_sets (data_to_word_get_names
                           names));
                         SilentFFI c 3 (adjust_sets
                           (data_to_word_get_names names));
                         Assign (adjust_var dest) (wordLang_Const
                           (n2w 2))],l):'a wordLang_prog#num)`;;

let getWords_def = cake_define_list
  [`getWords [] aux = (REVERSE aux,[])`;
   `getWords (c :: cs) aux =
      (match c with (b,wordLang_Word w) -> getWords cs ((b,w)
        :: aux) | _11 -> (REVERSE aux,c :: cs))`];;

(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 data_to_wordScript.sml:1349-1358: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let StoreAnyConsts_def = cake_define_list_try_tac (fun () ->
  `MEASURE (\(r1,r2,r3,vs,v). LENGTH vs)`)
  CHEAT_TAC
  [`StoreAnyConsts r1 r2 r3 [] v =
      Seq (Set NextFree (Var r2))
          (match SND v with Loc n _15 -> LocValue r1 n |
            wordLang_Word w -> Assign r1 (if FST v then Op asm_Add
            [Const w; Var r3] else (Const w)))`;
   `StoreAnyConsts r1 r2 r3 (v :: vs) w =
      (match ((SND v):'a word_loc) with Loc n _16 -> list_Seq
        [LocValue r1 n;
                             Store (Var r2) r1;
                             Assign r2 (Op asm_Add [Var r2; Const
                               bytes_in_word]);
                             StoreAnyConsts r1 r2 r3 vs w] | _17 ->
                               (let (ws,vs1) = getWords (v :: vs) [] in
               Seq (StoreConsts r2 r3 r2 r3 ws)
                   (StoreAnyConsts r1 r2 r3 vs1 w)))`];;

let lookup_mem_def = cake_define
  `lookup_mem m a =
     (match sptree_lookup a m with NONE -> (F,wordLang_Word ((n2w
       0):'a word)) | SOME x -> x)`;;

let byte_len_def = cake_define
  `byte_len (:'a) num_bytes =
     (if dimindex (:'a) = 32 then num_bytes DIV 4 + 1 else
       num_bytes DIV 8 + 1)`;;

let make_byte_header_def = cake_define
  `make_byte_header conf cmp_by_contents len =
   (let tag = (if cmp_by_contents then (n2w 0b00111) else (n2w
     0b10111)) in
     (if dimindex (:'a) = 32 then n2w (len + 4) << (dimindex (:'a)
       - 2 - data_to_word_config_len_size conf) || tag else n2w (len
       + 8) << (dimindex (:'a) - 3 - data_to_word_config_len_size
       conf) || tag):'a word)`;;

let get_lowerbits_def = cake_define
  `get_lowerbits conf x2 =
        match x2 with
          wordLang_Word w ->
        (((word_bits (small_shift_length conf - 1) 0) w) || (n2w 1))
        | _18 -> (n2w 1)`;;

let make_cons_ptr_def = cake_define
  `make_cons_ptr conf nf tag len =
     wordLang_Word (
             nf << (shift_length conf - backend_common_word_shift
               (:'a)) || ((n2w 1):'a word) || get_lowerbits conf
               (wordLang_Word (ptr_bits conf tag len)))`;;

let make_ptr_def = cake_define
  `make_ptr conf nf tag len =
     wordLang_Word (nf << (shift_length conf -
       backend_common_word_shift (:'a)) || ((n2w 1):'a word))`;;

let write_bytes_def = cake_define_list
  [`write_bytes bs [] be' = []`;
   `write_bytes bs ((w:'a word) :: ws) be' =
         (let k = dimindex (:'a) DIV 8 in
           bytes_to_word k (n2w 0) bs w be' :: write_bytes
             (DROP k bs) ws be')`];;

let small_int_def = cake_define
  `small_int (:'a) i <=>
     --(&(dimword (:'a) DIV 8)) <= i /\ i < (&(dimword (:'a) DIV
       8):int)`;;

let part_to_words_def = cake_define_list
  [`part_to_words c m (closLang_Int i:const_part) (offset:'a word) =
      (if small_int (:'a) i then SOME ((F,wordLang_Word (Smallnum
        i)),[]) else let (sign,ws) = i2mw i in
              match encode_header c (if sign then 7 else 3) (LENGTH
                ws) with NONE -> NONE | SOME hd -> SOME ((T,(make_ptr c
                offset ((n2w 0):'a word) (LENGTH ws))),
                              MAP (\w. (F,wordLang_Word w)) (hd
                                :: ws)))`;
   `part_to_words c m (closLang_Con t ns) (offset:'a word) =
      (if NULL ns then
         if t < dimword (:'a) DIV 16 then SOME ((F,wordLang_Word
           (n2w (16 * t + 2))),[]) else NONE else
         match encode_header c (4 * t) (LENGTH ns) with NONE -> NONE
           | SOME hd -> SOME ((T,wordLang_Word
                              (offset << (shift_length c -
                                backend_common_word_shift (:'a)) +
                              (ptr_bits c t (LENGTH ns) || (n2w
                                1)))),
                            (F,wordLang_Word hd) :: (MAP
                              (lookup_mem m) ns)))`;
   `part_to_words c m (W64 w:const_part) (offset:'a word) =
      (let ws = (if dimindex (:'a) < 64 then [((63 >< 32) w); ((31
        >< 0) w)] else [((63 >< 0) w):'a word]) in
         match encode_header c 3 (LENGTH ws) with NONE -> NONE |
           SOME hd -> SOME ((T,(make_ptr c offset ((n2w 0):'a word)
           (LENGTH ws))),
                            MAP (\w. (F,wordLang_Word w)) (hd ::
                              ws)))`;
   `part_to_words c m (closLang_Str s:const_part) (offset:'a word) =
      (let bytes = MAP (n2w o ORD) (explode s) in
       let n = LENGTH bytes in
       let hd = make_byte_header c T n in
       let k = byte_len (:'a) n in
       let ws = write_bytes bytes (REPLICATE k (n2w 0))
         (data_to_word_config_be c) in
         if k < 2 EXP (dimindex (:'a) - 4) /\ k < 2 EXP
           data_to_word_config_len_size c then SOME ((T,(make_ptr c
           offset ((n2w 0):'a word) k)),
                    MAP (\w. (F,wordLang_Word w)) (hd :: ws))
                      else NONE)`];;

let parts_to_words_def = cake_define_list
  [`parts_to_words c m i [] (off:'a word) = SOME (lookup_mem m (i -
  (1:num)),[])`;
   `parts_to_words c m i (x :: parts') (off:'a word) =
      (match part_to_words c m x off with NONE -> NONE | SOME (w,xs)
        ->
        (match parts_to_words c (insert i w m) (i + 1) parts'
                 (off + bytes_in_word * n2w (LENGTH xs)) with
                   NONE -> NONE | SOME (r,ys) -> SOME (r,xs ++
                   ys)))`];;

let const_parts_to_words_def = cake_define
  `const_parts_to_words c parts' =
     parts_to_words c LN 0 parts' (n2w 0)`;;

let get_Word_def = cake_define
  `get_Word x1 =
      match x1 with
        wordLang_Word w -> w
      | _19 -> (n2w 0)`;;

let assign_Build_def = cake_define
  `assign_Build (c:data_to_word_config) (secn:num) (l:num) (dest:num)
  (names:(1 spt) option) ps =
     (match const_parts_to_words c ps with NONE -> (GiveUp,l) | SOME
       (w,ws) ->
       ((list_Seq
         [Assign 1 (wordLang_Lookup NextFree);
          Assign 3 ((\sh e n. Shift sh e (wordLang_Const (n2w n)))
            Lsl (Op asm_Sub [Var 1; wordLang_Lookup CurrHeap])
                     (shift_length c - backend_common_word_shift
                       (:'a)));
          StoreAnyConsts (adjust_var dest) 1 3 ws w],l):'a
            wordLang_prog#num))`;;

let assign_ConsExtend_def = cake_define
  `assign_ConsExtend (c:data_to_word_config) (secn:num) (l:num)
  (dest:num) (names:(1 spt) option) tag args =
         ((match args with (old :: start' :: len :: tot :: rest) ->
           (match encode_header c (4 * tag) 0 with
              NONE -> (GiveUp,l) | SOME header ->
               (let limit' = MIN (2 EXP data_to_word_config_len_size
                 c) (dimword (:'a) DIV 16) in
               let h = (\sh e n. Shift sh e (wordLang_Const (n2w n)))
                 Lsl (Var (adjust_var tot))
                         (dimindex (:'a) -
                           data_to_word_config_len_size c - 2) in
                 (list_Seq
                   [BignumHalt (adjust_var tot);
                    Assign 1 (Var (adjust_var tot));
                    AllocVar c limit' (list_insert args
                      (data_to_word_get_names names));
                    Assign 1 (wordLang_Lookup NextFree);
                    Assign 5 (Op asm_Or [h; Const header]);
                    Assign 7 ((\sh e n. Shift sh e (wordLang_Const
                      (n2w n))) Lsr (Var (adjust_var tot)) 2);
                    Assign 9 (wordLang_Const (n2w tag));
                    StoreEach 1 (5 :: MAP adjust_var rest) (n2w 0);
                    Make_ptr_bits_code c 9 7 3;
                    Set NextFree (Op asm_Add [Var 1; Const
                      bytes_in_word;
                      (\sh e n. Shift sh e (wordLang_Const (n2w n)))
                        Lsl (Var 7) (backend_common_word_shift (:'a))]);
                    Assign 15 (Var (adjust_var len));
                    Assign 13 (Op asm_Add [Var 1;
                      Const (bytes_in_word * n2w (LENGTH rest +
                        1))]);
                    Assign 11 (Op asm_Add [real_addr c (adjust_var
                      old);
                      Const bytes_in_word;
                      ShiftVar Lsl (adjust_var start')
                        (backend_common_word_shift (:'a) - 2)]);
                    If Test 15 (Reg 15) (Assign (adjust_var dest)
                      (Var 3)) (list_Seq [
                      wordLang_MustTerminate
                        (wordLang_Call (SOME ([adjust_var
                          dest],adjust_sets (data_to_word_get_names
                          names),
                              Skip,secn,l))
                           (SOME MemCopy_location) [15; 11; 13; 3]
                             NONE)])]),l + 1)) | _20 -> (Skip,l)):'a
                             wordLang_prog#num)`;;

let assign_Ref_def = cake_define
  `assign_Ref (c:data_to_word_config) (secn:num) (l:num) (dest:num)
  (names:(1 spt) option) args =
           ((match encode_header c 2 (LENGTH args) with NONE ->
             (GiveUp,l) | SOME (header:'a word) -> (list_Seq
                  [Set TriggerGC (Op asm_Sub [wordLang_Lookup
                    TriggerGC;
                      Const (bytes_in_word * n2w (LENGTH args +
                        1))]);
                   Assign 1 (Op asm_Sub [wordLang_Lookup EndOfHeap;
                      Const (bytes_in_word * n2w (LENGTH args +
                        1))]);
                   Set EndOfHeap (Var 1);
                   Assign 3 (wordLang_Const header);
                   StoreEach 1 (3 :: MAP adjust_var args) (n2w 0);
                   Assign (adjust_var dest)
                     (Op asm_Or [(\sh e n. Shift sh e (wordLang_Const
                       (n2w n))) Lsl (Op asm_Sub [Var 1; wordLang_Lookup
                       CurrHeap])
                              (shift_length c -
                                backend_common_word_shift (:'a));
                             Const (n2w 1)])],l)):'a
                               wordLang_prog#num)`;;

let assign_AllocThunk_def = cake_define
  `assign_AllocThunk (ev:thunk_mode) (c:data_to_word_config) (secn:num)
  (l:num) (dest:num) (names:(1 spt) option) arg =
           ((let tag = (match ev with Evaluated -> 8 + 6 |
             NotEvaluated -> 0 + 6) in
            match encode_header c tag 1 with NONE -> (GiveUp,l) |
              SOME (header:'a word) -> (list_Seq
                  [Set TriggerGC (Op asm_Sub [wordLang_Lookup
                    TriggerGC;
                      Const (bytes_in_word * (n2w 2))]);
                   Assign 1 (Op asm_Sub [wordLang_Lookup EndOfHeap;
                      Const (bytes_in_word * (n2w 2))]);
                   Set EndOfHeap (Var 1);
                   Assign 3 (wordLang_Const header);
                   StoreEach 1 [3; adjust_var arg] (n2w 0);
                   Assign (adjust_var dest)
                     (Op asm_Or [(\sh e n. Shift sh e (wordLang_Const
                       (n2w n))) Lsl (Op asm_Sub [Var 1; wordLang_Lookup
                       CurrHeap])
                              (shift_length c -
                                backend_common_word_shift (:'a));
                             Const (n2w 1)])],l)):'a
                               wordLang_prog#num)`;;

let assign_RefByte_def = cake_define
  `assign_RefByte (c:data_to_word_config) (secn:num) (l:num) (dest:num)
  (names:(1 spt) option) immutable v1 v2 =
          ((Seq
            (Assign 1 (wordLang_Const (if immutable then (n2w 0) else
              (n2w 16))))
            (wordLang_MustTerminate
              (wordLang_Call (SOME ([adjust_var dest],adjust_sets
                (data_to_word_get_names names),Skip,secn,l))
                 (SOME RefByte_location)
                    [adjust_var v1; adjust_var v2; 1] NONE):'a
                      wordLang_prog),l + 1):'a wordLang_prog#num)`;;

let assign_XorByte_def = cake_define
  `assign_XorByte (c:data_to_word_config) (secn:num) (l:num) (dest:num)
  (names:(1 spt) option) v1 v2 =
     ((list_Seq [
         Assign 1 (real_addr c (adjust_var v1));
         Assign 3 (real_addr c (adjust_var v2));
         Assign 5 (SmallLsr (Load (Var 3)) (dimindex (:'a) -
           data_to_word_config_len_size c));
         Assign 1 (Op asm_Add [Var 1; Const bytes_in_word]);
         Assign 3 (Op asm_Add [Var 3; Const (bytes_in_word:'a
           word)]);
         wordLang_MustTerminate
           (wordLang_Call
             (SOME ([adjust_var dest],adjust_sets
               (data_to_word_get_names names),Skip,secn,l))
             (SOME XorLoop_location) [1; 3; 5] NONE)],l + 1):'a
               wordLang_prog#num)`;;

let SetBool_def = cake_define
  `SetBool dest cmp r ri =
   (wordLang_If cmp r ri
      (wordLang_Assign dest (Const (n2w 18:'a word)))
      (wordLang_Assign dest (Const (n2w 2:'a word))):'a
        wordLang_prog)`;;

let AssignCmp_def = cake_define_list
  [`AssignCmp dest (Lt:opb) v1 v2 = (SetBool dest asm_Lower v1 (Reg
  v2):'a wordLang_prog)`;
   `AssignCmp dest (ast_Gt:opb) v1 v2 = ((SetBool dest asm_Lower v2
  (Reg v1)):'a wordLang_prog)`;
   `AssignCmp dest (ast_Leq:opb) v1 v2 = ((SetBool dest asm_NotLower
  v2 (Reg v1)):'a wordLang_prog)`;
   `AssignCmp dest (ast_Geq:opb) v1 v2 = ((SetBool dest
  asm_NotLower v1 (Reg v2)):'a wordLang_prog)`];;

let assign_StringCmp_def = cake_define
  `assign_StringCmp (c:data_to_word_config) (secn:num) (l:num)
  (dest:num) (names:(1 spt) option) (b:bool) (cmp:opb) v1 v2 =
     ((let k = (dimindex (:'a) - data_to_word_config_len_size c -
       backend_common_word_shift (:'a)) in
       list_Seq [
           Assign 1 (real_addr c (adjust_var v1));
           Assign 3 (real_addr c (adjust_var v2));
           Assign 5 ((\sh e n. Shift sh e (wordLang_Const (n2w n)))
             Lsr (Load (Var 1)) k);
           Assign 7 ((\sh e n. Shift sh e (wordLang_Const (n2w n)))
             Lsr (Load (Var 3)) k);
           (if b then
              If Equal 5 (Reg 7)
                 (list_Seq
                  [Assign 11 (Op asm_Add [Var 1; Const
                    bytes_in_word]);
                   Assign 13 (Op asm_Add [Var 3; Const
                     bytes_in_word]);
                   wordLang_MustTerminate
                   (wordLang_Call (SOME ([5; 7],adjust_sets
                     (data_to_word_get_names names),Skip,secn,l))
                         (SOME StringCmpLoop_location) [11; 13; 7; 7;
                           7] NONE)])
                 Skip else
              list_Seq
              [Assign 11 (Op asm_Add [Var 1; Const bytes_in_word]);
               Assign 13 (Op asm_Add [Var 3; Const bytes_in_word]);
               Assign 9 (Var 5);
               If asm_Lower 7 (Reg 5) (Assign 9 (Var 7)) Skip;
               wordLang_MustTerminate
               (wordLang_Call (SOME ([5; 7],adjust_sets
                 (data_to_word_get_names names),Skip,secn,l))
                     (SOME StringCmpLoop_location) [11; 13; 9; 5; 7]
                       NONE)]);
           AssignCmp (adjust_var dest) cmp 5 7],l + 1):'a
             wordLang_prog#num)`;;

let assign_CopyByte_def = cake_define
  `assign_CopyByte (c:data_to_word_config) (secn:num) (l:num) (dest:num)
  (names:(1 spt) option) args =
       ((match args with [v1; v2; v3; v4; v5] ->
            ((wordLang_MustTerminate
              (wordLang_Call (SOME ([adjust_var dest],adjust_sets
                (data_to_word_get_names names),Skip,secn,l))
                 (SOME ByteCopy_location)
                    [adjust_var v1; adjust_var v2; adjust_var v3;
                     adjust_var v4; adjust_var v5] NONE):'a
                       wordLang_prog),l + 1) | [v1; v2; v3] ->
            ((wordLang_MustTerminate
              (wordLang_Call (SOME ([adjust_var dest],adjust_sets
                (data_to_word_get_names names),Skip,secn,l))
                 (SOME ByteCopyNew_location)
                    [adjust_var v1; adjust_var v2;
                     adjust_var v3] NONE):'a wordLang_prog),l + 1)
                       | _21 -> (Skip,l)):'a wordLang_prog#num)`;;

let assign_RefArray_def = cake_define
  `assign_RefArray (c:data_to_word_config) (secn:num) (l:num) (dest:num)
  (names:(1 spt) option) v1 v2 =
       (let limit' = MIN (2 EXP data_to_word_config_len_size c)
         (dimword (:'a) DIV 16) in
          (list_Seq
           [
           BignumHalt (adjust_var v1);
           Move 0 [(1,adjust_var v1)];
           AllocVar c limit' (list_insert [v1; v2]
             (data_to_word_get_names names));
           wordLang_MustTerminate
             (wordLang_Call (SOME ([adjust_var dest],adjust_sets
               (data_to_word_get_names names),Skip,secn,l))
                (SOME RefArray_location)
                   [adjust_var v1; adjust_var v2] NONE):'a
                     wordLang_prog],l + 1):'a wordLang_prog#num)`;;

let assign_FromList_def = cake_define
  `assign_FromList (c:data_to_word_config) (secn:num) (l:num) (dest:num)
  (names:(1 spt) option) tag v1 v2 =
        (if encode_header c (4 * tag) 0 = (NONE:('a word) option)
          then (GiveUp,l) else
          (wordLang_MustTerminate (list_Seq [
             Assign 1 (wordLang_Const (n2w (16 * tag)));
             (Call (SOME ([adjust_var dest],adjust_sets
               (data_to_word_get_names names),Skip,secn,l))
                (SOME FromList_location)
                   [adjust_var v1; adjust_var v2; 1] NONE):'a
                     wordLang_prog]),l + 1):'a wordLang_prog#num)`;;

let assign_LessConstSmall_def = cake_define
  `assign_LessConstSmall (l:num) (dest:num) i v1 =
                  ((If Less (adjust_var v1) (Imm (n2w (4 * i)))
                     (Assign (adjust_var dest) (Const (n2w 18:'a
                       word)))
                     (Assign (adjust_var dest) (Const (n2w 2:'a
                       word))),l):'a wordLang_prog#num)`;;

let assign_BoolTest_def = cake_define
  `assign_BoolTest (l:num) (dest:num) (test:test) v1 v2 =
                  ((If Equal (adjust_var v1) (Reg (adjust_var v2))
                    (Assign (adjust_var dest) (Const (n2w 18:'a
                      word)))
                    (Assign (adjust_var dest) (Const (n2w 2:'a
                      word))),l):'a wordLang_prog#num)`;;

let assign_BoolNot_def = cake_define
  `assign_BoolNot (l:num) (dest:num) v1 =
                  ((Assign (adjust_var dest)
                     (Op Xor [Var (adjust_var v1); Const (n2w
                       16)]),l):'a wordLang_prog#num)`;;

let assign_WordTest_def = cake_define
  `assign_WordTest (l:num) (dest:num) (test:test) v1 v2 =
        (((match test with Equal -> If Equal (adjust_var v1) (Reg
          (adjust_var v2))
                              (Assign (adjust_var dest) (Const (n2w
                                18:'a word)))
                              (Assign (adjust_var dest) (Const (n2w
                                2:'a word))) | ast_Compare Lt -> If
                                asm_Lower (adjust_var v1) (Reg
                                (adjust_var v2))
                              (Assign (adjust_var dest) (Const (n2w
                                18:'a word)))
                              (Assign (adjust_var dest) (Const (n2w
                                2:'a word))) | ast_Compare ast_Leq -> If
                                asm_NotLower (adjust_var v2) (Reg
                                (adjust_var v1))
                              (Assign (adjust_var dest) (Const (n2w
                                18:'a word)))
                              (Assign (adjust_var dest) (Const
                                (n2w 2:'a word))) | _22 ->
                                Skip),l):'a wordLang_prog#num)`;;

let assign_BoundsCheckByte_def = cake_define
  `assign_BoundsCheckByte (c:data_to_word_config) (secn:num) (l:num)
  (dest:num) (names:(1 spt) option) leq v1 v2 =
                    ((list_Seq [Assign 1
                              (let addr' = real_addr c (adjust_var
                                v1) in
                              let header = Load addr' in
                              let extra = (if dimindex (:'a) = 32
                                then 2 else 3) in
                              let k = dimindex (:'a) -
                                data_to_word_config_len_size c - extra
                                in
                              Op asm_Sub [(\sh e n. Shift sh e
                                (wordLang_Const (n2w n))) Lsr header k;
                                Const bytes_in_word]);
                              Assign 3 (ShiftVar Ror (adjust_var v2)
                                2);
                              (if leq then If asm_NotLower 1 (Reg 3)
                                else
                              If asm_Lower 3 (Reg 1))
                              (Assign (adjust_var dest) (Const (n2w
                                18:'a word)))
                              (Assign (adjust_var dest) (Const
                                (n2w 2:'a word)))],l):'a
                                wordLang_prog#num)`;;

let assign_BoundsCheckArray_def = cake_define
  `assign_BoundsCheckArray (c:data_to_word_config) (secn:num) (l:num)
  (dest:num) (names:(1 spt) option) v1 v2 =
                    ((list_Seq [Assign 1
                              (let addr' = real_addr c (adjust_var
                                v1) in
                              let header = Load addr' in
                              let k = dimindex (:'a) -
                                data_to_word_config_len_size c in
                              (\sh e n. Shift sh e (wordLang_Const
                                (n2w n))) Lsr header k);
                              Assign 3 (ShiftVar Ror (adjust_var v2)
                                2);
                              If asm_Lower 3 (Reg 1)
                              (Assign (adjust_var dest) (Const (n2w
                                18:'a word)))
                              (Assign (adjust_var dest) (Const
                                (n2w 2:'a word)))],l):'a
                                wordLang_prog#num)`;;

let assign_BoundsCheckBlock_def = cake_define
  `assign_BoundsCheckBlock (c:data_to_word_config) (secn:num) (l:num)
  (dest:num) (names:(1 spt) option) v1 v2 =
                    ((list_Seq [If Test (adjust_var v1) (Imm (n2w 1))
                              (Assign 1 (wordLang_Const (n2w 0)))
                              (Assign 1
                              (let addr' = real_addr c (adjust_var
                                v1) in
                              let header = Load addr' in
                              let k = dimindex (:'a) -
                                data_to_word_config_len_size c in
                              (\sh e n. Shift sh e (wordLang_Const
                                (n2w n))) Lsr header k));
                              Assign 3 (ShiftVar Ror (adjust_var v2)
                                2);
                              If asm_Lower 3 (Reg 1)
                              (Assign (adjust_var dest) (Const (n2w
                                18:'a word)))
                              (Assign (adjust_var dest) (Const
                                (n2w 2:'a word)))],l):'a
                                wordLang_prog#num)`;;

let assign_Equal_def = cake_define
  `assign_Equal (c:data_to_word_config) (secn:num) (l:num) (dest:num)
  (names:(1 spt) option) v1 v2 =
         ((list_Seq [Assign 1 (Var (adjust_var v1));
                    Assign 3 (Var (adjust_var v2));
                    Assign 5 (Op And [Var 1; Var 3]);
                    If Test 5 (Imm (n2w 1)) Skip
                      (If Equal 1 (Reg 3) Skip
                        (Seq (wordLang_MustTerminate
                           (wordLang_Call (SOME ([1],adjust_sets
                             (data_to_word_get_names
                             names),Skip,secn,l))
                              (SOME Equal_location) [1; 3] NONE))
                           (Assign 3 (wordLang_Const (n2w 1)))));
                    (If Equal 1 (Reg 3)
                       (Assign (adjust_var dest) (Const (n2w 18:'a
                         word)))
                       (Assign (adjust_var dest) (Const (n2w 2:'a
                         word))))],l + 1):'a wordLang_prog#num)`;;

let assign_Less_def = cake_define
  `assign_Less (c:data_to_word_config) (secn:num) (l:num) (dest:num)
  (names:(1 spt) option) v1 v2 =
         ((list_Seq [Assign 1 (Var (adjust_var v1));
                    Assign 3 (Var (adjust_var v2));
                    Assign 5 (Op asm_Or [Var 1; Var 3]);
                    If Test 5 (Imm (n2w 1)) Skip
                      (Seq (wordLang_MustTerminate
                           (wordLang_Call (SOME ([1],adjust_sets
                             (data_to_word_get_names
                             names),Skip,secn,l))
                              (SOME Compare_location) [1; 3] NONE))
                           (Assign 3 (wordLang_Const (n2w 1))));
                    (If Less 1 (Reg 3)
                       (Assign (adjust_var dest) (Const (n2w 18:'a
                         word)))
                       (Assign (adjust_var dest) (Const (n2w 2:'a
                         word))))],l + 1):'a wordLang_prog#num)`;;

let assign_LessEq_def = cake_define
  `assign_LessEq (c:data_to_word_config) (secn:num) (l:num) (dest:num)
  (names:(1 spt) option) v1 v2 =
         ((list_Seq [Assign 1 (Var (adjust_var v1));
                    Assign 3 (Var (adjust_var v2));
                    Assign 5 (Op asm_Or [Var 1; Var 3]);
                    If Test 5 (Imm (n2w 1)) Skip
                      (Seq (wordLang_MustTerminate
                           (wordLang_Call (SOME ([1],adjust_sets
                             (data_to_word_get_names
                             names),Skip,secn,l))
                              (SOME Compare_location) [1; 3] NONE))
                           (Assign 3 (wordLang_Const (n2w 1))));
                    (If asm_NotLess 3 (Reg 1)
                       (Assign (adjust_var dest) (Const (n2w 18:'a
                         word)))
                       (Assign (adjust_var dest) (Const (n2w 2:'a
                         word))))],l + 1):'a wordLang_prog#num)`;;

let assign_LengthBlock_def = cake_define
  `assign_LengthBlock (c:data_to_word_config) (secn:num) (l:num)
  (dest:num) (names:(1 spt) option) v1 =
                         ((If Test (adjust_var v1) (Imm (n2w 1))
                            (Assign (adjust_var dest) (wordLang_Const
                              (n2w 0)))
                            (Assign (adjust_var dest)
                              (let addr' = real_addr c (adjust_var
                                v1) in
                              let header = Load addr' in
                              let k = dimindex (:'a) -
                                data_to_word_config_len_size c in
                              let len = (\sh e n. Shift sh e
                                (wordLang_Const (n2w n))) Lsr header k
                                in
                              ((\sh e n. Shift sh e
                                (wordLang_Const (n2w n))) Lsl len
                                2))),l):'a wordLang_prog#num)`;;

let assign_Length_def = cake_define
  `assign_Length (c:data_to_word_config) (secn:num) (l:num) (dest:num)
  (names:(1 spt) option) v1 =
                           ((Assign (adjust_var dest)
                              (let addr' = real_addr c (adjust_var
                                v1) in
                              let header = Load addr' in
                              let k = dimindex (:'a) -
                                data_to_word_config_len_size c in
                              let len = (\sh e n. Shift sh e
                                (wordLang_Const (n2w n))) Lsr header k
                                in
                              ((\sh e n. Shift sh e
                                (wordLang_Const (n2w n))) Lsl len
                                2)),l):'a wordLang_prog#num)`;;

let assign_LengthByte_def = cake_define
  `assign_LengthByte (c:data_to_word_config) (secn:num) (l:num)
  (dest:num) (names:(1 spt) option) v1 =
             ((Assign (adjust_var dest)
                (let addr' = real_addr c (adjust_var v1) in
                 let header = Load addr' in
                 let k = dimindex (:'a) - backend_common_word_shift
                   (:'a) - data_to_word_config_len_size c in
                 let fakelen = (\sh e n. Shift sh e (wordLang_Const
                   (n2w n))) Lsr header k in
                 let len = Op asm_Sub [fakelen; Const bytes_in_word]
                   in
                   ((\sh e n. Shift sh e (wordLang_Const (n2w n)))
                     Lsl len 2)),l):'a wordLang_prog#num)`;;

let assign_TagLenEq_def = cake_define
  `assign_TagLenEq (c:data_to_word_config) (secn:num) (l:num) (dest:num)
  (names:(1 spt) option) tag len v1 =
                         ((if len = 0 then
                            if tag < dimword (:'a) DIV 16 then
                              (If Equal (adjust_var v1) (Imm (n2w (16
                                * tag + 2)))
                              (Assign (adjust_var dest) (Const (n2w
                                18:'a word)))
                              (Assign (adjust_var dest) (Const (n2w
                                2:'a word))),l) else (Assign (adjust_var
                                dest) (Const (n2w 2:'a word)),l) else if
                                tag < 2 EXP data_to_word_config_tag_bits
                                c - 1 /\
                              len < 2 EXP
                                data_to_word_config_len_bits c - 1 then
                            (Seq
                              (Assign 1 (Op And
                              [Var (adjust_var v1);
                              Const (all_ones
                                (data_to_word_config_len_bits c +
                                data_to_word_config_tag_bits c + 1)
                                0)]))
                              (If Equal 1 (Imm (ptr_bits c tag len ||
                                (n2w 1)))
                              (Assign (adjust_var dest) (Const (n2w
                                18:'a word)))
                              (Assign (adjust_var dest) (Const (n2w
                                2:'a word)))),l) else
                            match encode_header c (4 * tag) len with
                              NONE -> (Assign (adjust_var dest) (Const
                              (n2w 2:'a word)),l) | SOME h ->
                              (list_Seq
                              [Assign 1 (wordLang_Const (n2w 0));
                              If Test (adjust_var v1) (Imm (n2w 1))
                                Skip
                              (Assign 1 (wordLang_Load (real_addr c
                                (adjust_var v1))));
                              If Equal 1 (Imm h)
                              (Assign (adjust_var dest) (Const (n2w
                                18:'a word)))
                              (Assign (adjust_var dest) (Const
                                (n2w 2:'a word)))],l)):'a
                                wordLang_prog#num)`;;

let assign_LenEq_def = cake_define
  `assign_LenEq (c:data_to_word_config) (secn:num) (l:num) (dest:num)
  (names:(1 spt) option) len v1 =
                         ((if len = 0 then
                            (If Test (adjust_var v1) (Imm (n2w 1))
                              (Assign (adjust_var dest) (Const (n2w
                                18:'a word)))
                              (Assign (adjust_var dest) (Const (n2w
                                2:'a word))),l) else if len < 2 EXP
                                data_to_word_config_len_bits c - 1 then
                            (Seq
                              (Assign 1 (Op And
                              [Var (adjust_var v1);
                              Const (all_ones
                                (data_to_word_config_len_bits c + 1)
                                0)]))
                              (If Equal 1 (Imm (ptr_bits c 0 len ||
                                (n2w 1)))
                              (Assign (adjust_var dest) (Const (n2w
                                18:'a word)))
                              (Assign (adjust_var dest) (Const (n2w
                                2:'a word)))),l) else if len < dimword
                                (:'a) then
                            (list_Seq
                              [Assign 1 (wordLang_Const (n2w 0));
                              If Test (adjust_var v1) (Imm (n2w 1))
                                Skip
                              (Assign 1
                              (let addr' = real_addr c (adjust_var
                                v1) in
                              let header = Load addr' in
                              let k = dimindex (:'a) -
                                data_to_word_config_len_size c in
                              let len = (\sh e n. Shift sh e
                                (wordLang_Const (n2w n))) Lsr header k
                                in
                              len));
                              If Equal 1 (Imm (n2w len))
                              (Assign (adjust_var dest) (Const (n2w
                                18:'a word)))
                              (Assign (adjust_var dest) (Const (n2w
                                2:'a word)))],l) else
                            (Assign (adjust_var dest) (Const (n2w
                              2:'a word)),l)):'a wordLang_prog#num)`;;

let assign_TagEq_def = cake_define
  `assign_TagEq (c:data_to_word_config) (secn:num) (l:num) (dest:num)
  (names:(1 spt) option) tag v1 =
                ((if tag < dimword (:'a) DIV 16 then
                  (list_Seq
                    [Assign 1 (Var (adjust_var v1));
                     If Test (adjust_var v1) (Imm (n2w 1)) Skip
                       (Assign 1 (let v = adjust_var v1 in
                              let h = Load (real_addr c v) in
                              Op And [h; Const (tag_mask c || (n2w
                                2))]));
                     If Equal 1 (Imm (n2w (16 * tag + 2)))
                       (Assign (adjust_var dest) (Const (n2w 18:'a
                         word)))
                       (Assign (adjust_var dest) (Const (n2w 2:'a
                         word)))],l) else (Assign (adjust_var dest)
                         (Const (n2w 2:'a word)),l)):'a
                         wordLang_prog#num)`;;

let assign_Add_def = cake_define
  `assign_Add (c:data_to_word_config) (secn:num) (l:num) (dest:num)
  (names:(1 spt) option) v1 v2 =
         ((list_Seq [
                    Inst (Arith (asm_AddOverflow 1 (adjust_var v1)
                              (adjust_var v2) 3));
                    Assign 3 (Op asm_Or [Var 3; Var (adjust_var v1);
                      Var (adjust_var v2)]);
                    If Test 3 (Imm (n2w 1)) Skip
                     (wordLang_MustTerminate
                       (wordLang_Call (SOME ([1],adjust_sets
                         (data_to_word_get_names names),Skip,secn,l))
                         (SOME Add_location) [adjust_var v1;
                           adjust_var v2] NONE));
                    Move 2 [(adjust_var dest,1)]],l + 1):'a
                      wordLang_prog#num)`;;

let assign_Sub_def = cake_define
  `assign_Sub (c:data_to_word_config) (secn:num) (l:num) (dest:num)
  (names:(1 spt) option) v1 v2 =
         ((list_Seq [
                    Inst (Arith (asm_SubOverflow 1 (adjust_var v1)
                              (adjust_var v2) 3));
                    Assign 3 (Op asm_Or [Var 3; Var (adjust_var v1);
                      Var (adjust_var v2)]);
                    If Test 3 (Imm (n2w 1)) Skip
                     (wordLang_MustTerminate
                       (wordLang_Call (SOME ([1],adjust_sets
                         (data_to_word_get_names names),Skip,secn,l))
                         (SOME Sub_location) [adjust_var v1;
                           adjust_var v2] NONE));
                    Move 2 [(adjust_var dest,1)]],l + 1):'a
                      wordLang_prog#num)`;;

let assign_Mult_def = cake_define
  `assign_Mult (c:data_to_word_config) (secn:num) (l:num) (dest:num)
  (names:(1 spt) option) v1 v2 =
         ((list_Seq [Assign 1 (ShiftVar Lsr (adjust_var v1) 1);
                    Inst (Arith (asm_LongMul 3 1 1 (adjust_var v2)));
                    Assign 3 (Op asm_Or [Var 3;
                              Op And [Const (n2w 1);
                              Op asm_Or [Var (adjust_var v1); Var
                                (adjust_var v2)]]]);
                    Assign 1 (ShiftVar Lsr 1 1);
                    If Equal 3 (Imm (n2w 0)) Skip
                      (wordLang_MustTerminate
                        (wordLang_Call (SOME ([1],adjust_sets
                          (data_to_word_get_names names),Skip,secn,l))
                         (SOME Mul_location) [adjust_var v1;
                           adjust_var v2] NONE));
                    Move 2 [(adjust_var dest,1)]],l + 1):'a
                      wordLang_prog#num)`;;

let assign_Div_def = cake_define
  `assign_Div (c:data_to_word_config) (secn:num) (l:num) (dest:num)
  (names:(1 spt) option) v1 v2 =
         ((list_Seq [
            Assign 1 (Op asm_Or [Var (adjust_var v1); Var (adjust_var
              v2)]);
            Assign 1 (Op asm_Or [Var 1; ShiftVar Lsr 1 (dimindex
              (:'a) - 1)]);
            If Test 1 (Imm ((n2w 1):'a word))
              (if data_to_word_config_has_div c then
                 list_Seq [Inst (Arith (asm_Div 1 (adjust_var v1)
                   (adjust_var v2)));
                           Assign (adjust_var dest) (ShiftVar Lsl 1
                             2)] else if data_to_word_config_has_longdiv
                             c then
                 list_Seq [Assign 1 (wordLang_Const (n2w 0));
                           Inst (Arith (asm_LongDiv 1 3 1 (adjust_var
                             v1) (adjust_var v2)));
                           Assign (adjust_var dest) (ShiftVar Lsl 1
                             2)] else
                 list_Seq
                   [Assign 1 (wordLang_Const (n2w 0));
                    wordLang_MustTerminate
                     (wordLang_Call (SOME ([1],adjust_sets
                       (data_to_word_get_names names),Skip,secn,l + 1))
                       (SOME LongDiv_location)
                         [1; adjust_var v1; adjust_var v2] NONE);
                    Assign (adjust_var dest) (ShiftVar Lsl 1 2)])
              (list_Seq
                 [wordLang_MustTerminate
                    (wordLang_Call (SOME ([1],adjust_sets
                      (data_to_word_get_names names),Skip,secn,l))
                       (SOME Div_location) [adjust_var v1; adjust_var
                         v2] NONE);
                  Move 2 [(adjust_var dest,1)]])],l + 2):'a
                    wordLang_prog#num)`;;

let assign_Mod_def = cake_define
  `assign_Mod (c:data_to_word_config) (secn:num) (l:num) (dest:num)
  (names:(1 spt) option) v1 v2 =
         ((list_Seq [
            Assign 1 (Op asm_Or [Var (adjust_var v1); Var (adjust_var
              v2)]);
            Assign 1 (Op asm_Or [Var 1; ShiftVar Lsr 1 (dimindex
              (:'a) - 1)]);
            If Test 1 (Imm ((n2w 1):'a word))
              (if data_to_word_config_has_div c then
                 list_Seq [Inst (Arith (asm_Div 1 (adjust_var v1)
                   (adjust_var v2)));
                           Inst (Arith (asm_LongMul 3 1 1 (adjust_var
                             v2)));
                           Assign (adjust_var dest)
                             (Op asm_Sub [Var (adjust_var v1); Var
                               1])] else if
                               data_to_word_config_has_longdiv c then
                 list_Seq [Assign 1 (wordLang_Const (n2w 0));
                           Inst (Arith (asm_LongDiv 1 3 1 (adjust_var
                             v1) (adjust_var v2)));
                           Move 2 [(adjust_var dest,3)]] else
                 list_Seq
                   [Assign 1 (wordLang_Const (n2w 0));
                    wordLang_MustTerminate
                     (wordLang_Call (SOME ([1],adjust_sets
                       (data_to_word_get_names names),Skip,secn,l + 1))
                       (SOME LongDiv_location)
                         [1; adjust_var v1; adjust_var v2] NONE);
                    Get (adjust_var dest) (Temp (n2w 28))])
              (list_Seq
                 [wordLang_MustTerminate
                    (wordLang_Call (SOME ([1],adjust_sets
                      (data_to_word_get_names names),Skip,secn,l))
                       (SOME Mod_location) [adjust_var v1; adjust_var
                         v2] NONE);
                  Move 2 [(adjust_var dest,1)]])],l + 2):'a
                    wordLang_prog#num)`;;

let assign_WordOpW8_def = cake_define
  `assign_WordOpW8 opw (c:data_to_word_config) (secn:num) (l:num)
  (dest:num) (names:(1 spt) option) v1 v2 =
            ((Assign (adjust_var dest)
             (match lookup_word_op opw with Bitwise op -> Op op [Var
               (adjust_var v1); Var (adjust_var v2)] | Carried op ->
               (let k = dimindex (:'a) - 10 in
                (\sh e n. Shift sh e (wordLang_Const (n2w n))) Lsr
                  ((\sh e n. Shift sh e (wordLang_Const (n2w n))) Lsl
                  (Op op [Var (adjust_var v1); Var (adjust_var
                    v2)]) k) k)),l):'a wordLang_prog#num)`;;

let assign_WordOpW64_def = cake_define
  `assign_WordOpW64 opw (c:data_to_word_config) (secn:num) (l:num)
  (dest:num) (names:(1 spt) option) v1 v2 =
        ((if dimindex (:'a) = 64 then
          (match encode_header c 3 1 with NONE -> (GiveUp,l) | SOME
            (header:'a word) ->
                 (Seq (Assign 3
                   (Op (match opw with
                           backend_common_Andw -> And |
                             backend_common_Orw -> Or | Xor -> Xor | Add
                             -> Add | Sub -> Sub)
                          [Load
                             (Op asm_Add
                              [real_addr c (adjust_var v1);
                              Const bytes_in_word]);
                           Load
                             (Op asm_Add
                              [real_addr c (adjust_var v2);
                              Const bytes_in_word])]))
                    (WriteWord64 c header dest 3),l)) else
          (match encode_header c 3 2 with NONE -> (GiveUp,l) | SOME
            header ->
             (list_Seq [
                Assign 15 (real_addr c (adjust_var v1));
                Assign 17 (real_addr c (adjust_var v2));
                Assign 11 (wordLang_Load (Op asm_Add [Var 15; Const
                  bytes_in_word]));
                Assign 13 (wordLang_Load (Op asm_Add [Var 15; Const
                  ((n2w 2) * bytes_in_word)]));
                Assign 21 (wordLang_Load (Op asm_Add [Var 17; Const
                  bytes_in_word]));
                Assign 23 (wordLang_Load (Op asm_Add [Var 17; Const
                  ((n2w 2) * bytes_in_word)]));
                WordOp64_on_32 opw;
                WriteWord64_on_32 c header dest 33 31],l))):'a
                  wordLang_prog#num)`;;

let assign_WordShiftW8_def = cake_define
  `assign_WordShiftW8 sh n (c:data_to_word_config) (secn:num) (l:num)
  (dest:num) (names:(1 spt) option) v1 =
         ((Assign (adjust_var dest)
            (match sh with Lsl ->
               (\sh e n. Shift sh e (wordLang_Const (n2w n))) Lsr
                 ((\sh e n. Shift sh e (wordLang_Const (n2w n))) Lsl
                   (Var (adjust_var v1)) (dimindex (:'a) - 10 + (MIN n
                   8)))
                 (dimindex (:'a) - 10) | Lsr ->
               (\sh e n. Shift sh e (wordLang_Const (n2w n))) Lsl
                 ((\sh e n. Shift sh e (wordLang_Const (n2w n))) Lsr
                   (Var (adjust_var v1)) ((MIN n 8) + 2)) 2 | Asr ->
               (\sh e n. Shift sh e (wordLang_Const (n2w n))) Lsl
                 ((\sh e n. Shift sh e (wordLang_Const (n2w n))) Lsr
                    ((\sh e n. Shift sh e (wordLang_Const (n2w n)))
                      Asr
                       ((\sh e n. Shift sh e (wordLang_Const (n2w
                         n))) Lsl (Var (adjust_var v1)) (dimindex (:'a)
                         - 10))
                       (MIN n 8))
                    (dimindex (:'a) - 8)) 2 | Ror ->
               (let n = n MOD 8 in
                  Op asm_Or
                   [(\sh e n. Shift sh e (wordLang_Const (n2w n)))
                     Lsl (ShiftVar Lsr (adjust_var v1) (n + 2)) 2;
                    (\sh e n. Shift sh e (wordLang_Const (n2w n)))
                      Lsr (ShiftVar Lsl (adjust_var v1)
                      ((dimindex (:'a) - 2) - n)) (dimindex (:'a)
                        - 10)])),l):'a wordLang_prog#num)`;;

let assign_WordShiftW64_def = cake_define
  `assign_WordShiftW64 sh n (c:data_to_word_config) (secn:num) (l:num)
  (dest:num) (names:(1 spt) option) v1 =
          (let len = (if dimindex (:'a) < 64 then 2 else 1) in
          (match encode_header c 3 len with NONE -> (GiveUp,l) | SOME
            (header:'a word) ->
             ((if len = 1 then
                list_Seq
                  [LoadWord64 c 3 (adjust_var v1);
                   Assign 3 (ShiftVar sh 3 n);
                   WriteWord64 c header dest 3] else
                list_Seq [
                  Assign 15 (real_addr c (adjust_var v1));
                  Assign 11 (wordLang_Load (Op asm_Add [Var 15; Const
                    bytes_in_word]));
                  Assign 13 (wordLang_Load (Op asm_Add [Var 15; Const
                    ((n2w 2) * bytes_in_word)]));
                  WordShift64_on_32 sh n;
                  WriteWord64_on_32 c header dest 33 31]),l)):'a
                    wordLang_prog#num)`;;

let assign_WordFromWord_def = cake_define
  `assign_WordFromWord b (c:data_to_word_config) (secn:num) (l:num)
  (dest:num) (names:(1 spt) option) v1 =
           (if b then
             (list_Seq [Assign 1 (real_addr c (adjust_var v1));
                        Assign 1 (wordLang_Load (Op asm_Add [Var 1;
                          Const (if dimindex (:'a) = 32 then (n2w 2)
                            * bytes_in_word else bytes_in_word)]));
                        Assign 1 (Op And [Var 1; Const (n2w 255)]);
                        Assign (adjust_var dest) (ShiftVar Lsl 1
                          2)],l) else
           (let
              len = (if dimindex (:'a) < 64 then 2 else 1) in
              match encode_header c 3 len with
                NONE -> (GiveUp,l) | SOME header ->
                 (if len = 1 then
                    (list_Seq [Assign 3 ((\sh e n. Shift sh e
                      (wordLang_Const (n2w n))) Lsr (Var (adjust_var
                      v1)) 2);
                              WriteWord64 c header dest 3],l) else
                    (list_Seq [Assign 5 ((\sh e n. Shift sh e
                      (wordLang_Const (n2w n))) Lsr (Var (adjust_var
                      v1)) 2);
                              Assign 3 (wordLang_Const (n2w 0));
                              WriteWord64_on_32 c header dest 5
                                3],l))):'a wordLang_prog#num)`;;

let assign_WordFromInt_def = cake_define
  `assign_WordFromInt (c:data_to_word_config) (secn:num) (l:num)
  (dest:num) (names:(1 spt) option) v1 =
         (let len = (if dimindex (:'a) < 64 then 2 else 1) in
         (match encode_header c 3 len with NONE -> (GiveUp,l) | SOME
           (header:'a word) ->
            (if len = 1 then
              Seq
                (If Test (adjust_var v1) (Imm (n2w 1))
                     (Assign 3 ((\sh e n. Shift sh e (wordLang_Const
                       (n2w n))) Asr (Var (adjust_var v1)) 2))
                    (Seq
                      (LoadBignum c 1 3 (adjust_var v1))
                      (If Test 1 (Imm (n2w 16)) Skip
                         (Assign 3 (Op asm_Sub [Const (n2w 0); Var
                           3])))))
                (WriteWord64 c header dest 3) else If Test
                  (adjust_var v1) (Imm (n2w 1))
               (list_Seq [
                 Assign 3 ((\sh e n. Shift sh e (wordLang_Const (n2w
                   n))) Asr (Var (adjust_var v1)) 2);
                 Assign 5 ((\sh e n. Shift sh e (wordLang_Const (n2w
                   n))) Asr (Var (adjust_var v1)) 31);
                 WriteWord64_on_32 c header dest 3 5])
               (list_Seq [
                 Assign 1 (real_addr c (adjust_var v1));
                 Assign 3 (wordLang_Load (Var 1));
                 Assign 5 (wordLang_Load (Op asm_Add [Var 1; Const
                   bytes_in_word]));
                 Assign 7 (ShiftVar Lsr 3 (dimindex (:'a) -
                   data_to_word_config_len_size c));
                 If Equal 7 (Imm (n2w 1))
                   (If Test 3 (Imm (n2w 16))
                     (Seq (Assign 9 (wordLang_Const (n2w 0)))
                          (WriteWord64_on_32 c header dest 5 9))
                     (Seq (Assign 9 (wordLang_Const (word_not (n2w
                       0))))
                     (Seq (Assign 5 (Op asm_Sub [Const (n2w 0); Var
                       5]))
                          (WriteWord64_on_32 c header dest 5 9))))
                   (If Test 3 (Imm (n2w 16))
                     (Seq (Assign 9 (wordLang_Load
                            (Op asm_Add [Var 1; Const ((n2w 2) *
                              bytes_in_word)])))
                          (WriteWord64_on_32 c header dest 5 9))
                     (list_Seq
                       [Assign 11 (wordLang_Const (n2w 0));
                        Assign 13 (wordLang_Const (n2w 1));
                        Assign 9 (wordLang_Load
                          (Op asm_Add [Var 1; Const ((n2w 2) *
                            bytes_in_word)]));
                        Assign 5 (Op Xor [Const (word_not (n2w 0));
                          Var 5]);
                        Assign 9 (Op Xor [Const (word_not (n2w 0));
                          Var 9]);
                        Inst (Arith (asm_AddCarry 15 11 5 13));
                        Inst (Arith (asm_AddCarry 19 11 9 13));
                        WriteWord64_on_32 c header dest 15
                          19]))])),l):'a wordLang_prog#num)`;;

let assign_WordToInt_def = cake_define
  `assign_WordToInt (c:data_to_word_config) (secn:num) (l:num)
  (dest:num) (names:(1 spt) option) v =
         (let len = (if dimindex (:'a) < 64 then 2 else 1) in
         (match encode_header c 3 len with NONE -> (GiveUp,l) | SOME
           header ->
              (if len = 1 then
                (list_Seq [LoadWord64 c 3 (adjust_var v);
                           Assign 1 ((\sh e n. Shift sh e
                             (wordLang_Const (n2w n))) Lsr (Var 3) 61);
                           If Equal 1 (Imm (n2w 0))
                             (Assign (adjust_var dest) ((\sh e n.
                               Shift sh e (wordLang_Const (n2w n))) Lsl
                               (Var 3) 2))
                             (WriteWord64 c header dest 3)],l) else
               (match encode_header c 3 1 with NONE -> (GiveUp,l) |
                 SOME header1 ->
                  (list_Seq [
                   Assign 15 (real_addr c (adjust_var v));
                   Assign 13 (wordLang_Load (Op asm_Add [Var 15;
                     Const bytes_in_word]));
                   Assign 11 (wordLang_Load (Op asm_Add [Var 15;
                     Const ((n2w 2) * bytes_in_word)]));
                   If asm_NotEqual 13 (Imm (n2w 0))
                     (WriteWord64_on_32 c header dest 13 11)
                     (list_Seq [
                       Assign 1 ((\sh e n. Shift sh e (wordLang_Const
                         (n2w n))) Lsr (Var 11) 29);
                       If Equal 1 (Imm (n2w 0))
                         (Assign (adjust_var dest) ((\sh e n. Shift
                           sh e (wordLang_Const (n2w n))) Lsl (Var 11)
                           2))
                         (WriteWord32_on_32 c header1 dest
                           11)])],l)))):'a wordLang_prog#num)`;;

let assign_FFI_def = cake_define
  `assign_FFI ffi_index (c:data_to_word_config) (secn:num) (l:num)
  (dest:num) (names:(1 spt) option) v1 v2 =
       (if ~(data_to_word_config_call_empty_ffi c) /\ ffi_index =
         (implode "") then (Assign (adjust_var dest)
         data_to_word_Unit,l) else
         let addr1 = real_addr c (adjust_var v1) in
         let header1 = Load addr1 in
         let k = dimindex (:'a) - backend_common_word_shift (:'a) -
           data_to_word_config_len_size c in
         let fakelen1 = (\sh e n. Shift sh e (wordLang_Const (n2w
           n))) Lsr header1 k in
         let addr2 = real_addr c (adjust_var v2) in
         let header2 = Load addr2 in
         let fakelen2 = (\sh e n. Shift sh e (wordLang_Const (n2w
           n))) Lsr header2 k in
         (
         list_Seq [
           Assign 1 (Op asm_Add [addr1; Const bytes_in_word]);
           Assign 3 (Op asm_Sub [fakelen1; Const bytes_in_word]);
           Assign 5 (if ffi_index = (implode "") then Const (n2w 0)
             else (Op asm_Add [addr2; Const bytes_in_word]));
           Assign 7 (if ffi_index = (implode "") then Const (n2w 0)
             else (Op asm_Sub [fakelen2; Const bytes_in_word]));
           FFI ffi_index 1 3 5 7 (adjust_sets (match names with SOME
             names -> names | NONE -> LN));
           Assign (adjust_var dest) data_to_word_Unit],l):'a
             wordLang_prog#num)`;;

let assign_EqualConst_def = cake_define
  `assign_EqualConst p (c:data_to_word_config) (secn:num) (l:num)
  (dest:num) (names:(1 spt) option) v =
     (match part_to_words c LN p (n2w 0) with SOME ((F,w),_23) ->
         (If Equal (adjust_var v) (Imm (get_Word w))
                     (Assign (adjust_var dest) (Const (n2w 18:'a
                       word)))
                     (Assign (adjust_var dest) (Const (n2w 2:'a
                       word))),l) | SOME (_24,words) ->
         ((match p with closLang_Int _25 -> If Test (adjust_var v)
           (Imm (n2w 1))
                        (Assign (adjust_var dest) (Const (n2w 2:'a
                          word)))
                        (list_Seq
                           [Assign 1 (Const (n2w 2:'a word));
                            Assign 3 (real_addr c (adjust_var v));
                            MemEqList (n2w 0) (MAP (get_Word o SND)
                              words);
                            Assign (adjust_var dest) (Var 1)]) | W64
                              _26 -> (list_Seq
                           [Assign 1 (Const (n2w 2:'a word));
                            Assign 3 (Op asm_Add [real_addr c
                              (adjust_var v);
                              Const bytes_in_word]);
                            MemEqList (n2w 0) (MAP (get_Word o SND)
                              (TL words));
                            Assign (adjust_var dest) (Var 1)]) |
                              closLang_Str _27 -> (list_Seq
                           [Assign 1 (Const (n2w 2:'a word));
                            Assign 3 (real_addr c (adjust_var v));
                            MemEqList (n2w 0) (MAP (get_Word o SND)
                              words);
                            Assign (adjust_var dest) (Var 1)]) |
                              _28 -> Skip),l) | _29 -> ((Assign
                              (adjust_var dest) (Const (n2w 2:'a
                              word)),l):'a wordLang_prog#num))`;;

let assign_Install_def = cake_define
  `assign_Install (c:data_to_word_config) (secn:num) (l:num) (dest:num)
  (names:(1 spt) option) v1 v2 v3 v4 =
         ((list_Seq [BignumHalt (adjust_var v3);
                    BignumHalt (adjust_var v4);
                    Assign 1 (wordLang_Lookup BitmapBuffer);
                    Assign 3 (Op asm_Sub [wordLang_Lookup
                      BitmapBufferEnd; Var 1]);
                    Assign 5 (ShiftVar Lsr (adjust_var v4) 2);
                    Assign 3 (ShiftVar Lsr 3
                      (backend_common_word_shift (:'a)));
                    If asm_Lower 3 (Reg 5) GiveUp Skip;
                    Assign 1 (wordLang_Lookup CodeBuffer);
                    Assign 3 (Op asm_Sub [wordLang_Lookup
                      CodeBufferEnd; Var 1]);
                    Assign 5 (ShiftVar Lsr (adjust_var v3) 2);
                    If asm_Lower 3 (Reg 5) GiveUp Skip;
                    wordLang_MustTerminate
                     (wordLang_Call (SOME ([adjust_var dest],
                        adjust_sets (data_to_word_get_names
                          names),Skip,secn,l))
                     (SOME InstallCode_location)
                       [adjust_var v1; adjust_var v2; 1] NONE)],l
                         + 1):'a wordLang_prog#num)`;;

let assign_FP_cmp_def = cake_define
  `assign_FP_cmp fpc (c:data_to_word_config) (secn:num) (l:num)
  (dest:num) (names:(1 spt) option) v1 v2 =
        ((if ~(data_to_word_config_has_fp_ops c) then (GiveUp,l) else
         if dimindex (:'a) = 64 then
            ((list_Seq [
                Assign 3 (wordLang_Load (Op asm_Add
                            [real_addr c (adjust_var v1); Const
                              bytes_in_word]));
                Assign 5 (wordLang_Load (Op asm_Add
                            [real_addr c (adjust_var v2); Const
                              bytes_in_word]));
                Inst (asm_FP (FPMovFromReg 0 3 3));
                Inst (asm_FP (FPMovFromReg 1 5 5));
                Inst (asm_FP (fp_cmp_inst fpc));
                Assign (adjust_var dest) (Op asm_Add [ShiftVar Lsl 3
                  4; Const (n2w 2)])],l)) else
            ((list_Seq [
                Assign 15 (real_addr c (adjust_var v1));
                Assign 17 (real_addr c (adjust_var v2));
                Assign 11 (wordLang_Load (Op asm_Add [Var 15; Const
                  bytes_in_word]));
                Assign 13 (wordLang_Load (Op asm_Add [Var 15; Const
                  ((n2w 2) * bytes_in_word)]));
                Assign 21 (wordLang_Load (Op asm_Add [Var 17; Const
                  bytes_in_word]));
                Assign 23 (wordLang_Load (Op asm_Add [Var 17; Const
                  ((n2w 2) * bytes_in_word)]));
                Inst (asm_FP (FPMovFromReg 0 13 11));
                Inst (asm_FP (FPMovFromReg 1 23 21));
                Inst (asm_FP (fp_cmp_inst fpc));
                Assign (adjust_var dest) (Op asm_Add [ShiftVar Lsl
                  3 4; Const (n2w 2)])],l))):'a wordLang_prog#num)`;;

let assign_FP_top_def = cake_define
  `assign_FP_top fpt (c:data_to_word_config) (secn:num) (l:num)
  (dest:num) (names:(1 spt) option) v1 v2 v3 =
        ((if ~(data_to_word_config_has_fp_ops c) \/
          ~(data_to_word_config_has_fp_tern c) then (GiveUp,l) else
         if dimindex (:'a) = 64 then
          (match encode_header c 3 1 with NONE -> (GiveUp,l) | SOME
            (header:'a word) ->
             (list_Seq [
                Assign 3 (wordLang_Load (Op asm_Add
                            [real_addr c (adjust_var v1); Const
                              bytes_in_word]));
                Assign 5 (wordLang_Load (Op asm_Add
                            [real_addr c (adjust_var v2); Const
                              bytes_in_word]));
                Assign 7 (wordLang_Load (Op asm_Add
                            [real_addr c (adjust_var v3); Const
                              bytes_in_word]));
                Inst (asm_FP (FPMovFromReg 0 3 3));
                Inst (asm_FP (FPMovFromReg 1 5 5));
                Inst (asm_FP (FPMovFromReg 2 7 7));
                Inst (asm_FP (fp_top_inst fpt));
                Inst (asm_FP (FPMovToReg 3 5 0));
                WriteWord64 c header dest 3],l)) else
          (match encode_header c 3 2 with NONE -> (GiveUp,l) | SOME
            header ->
             (list_Seq [
                Assign 15 (real_addr c (adjust_var v1));
                Assign 17 (real_addr c (adjust_var v2));
                Assign 19 (real_addr c (adjust_var v3));
                Assign 11 (wordLang_Load (Op asm_Add [Var 15; Const
                  bytes_in_word]));
                Assign 13 (wordLang_Load (Op asm_Add [Var 15; Const
                  ((n2w 2) * bytes_in_word)]));
                Assign 21 (wordLang_Load (Op asm_Add [Var 17; Const
                  bytes_in_word]));
                Assign 23 (wordLang_Load (Op asm_Add [Var 17; Const
                  ((n2w 2) * bytes_in_word)]));
                Assign 31 (wordLang_Load (Op asm_Add [Var 19; Const
                  bytes_in_word]));
                Assign 33 (wordLang_Load (Op asm_Add [Var 19; Const
                  ((n2w 2) * bytes_in_word)]));
                Inst (asm_FP (FPMovFromReg 0 13 11));
                Inst (asm_FP (FPMovFromReg 1 23 21));
                Inst (asm_FP (FPMovFromReg 2 33 31));
                Inst (asm_FP (fp_top_inst fpt));
                Inst (asm_FP (FPMovToReg 5 3 0));
                WriteWord64_on_32 c header dest 5 3],l))):'a
                  wordLang_prog#num)`;;

let assign_FP_bop_def = cake_define
  `assign_FP_bop fpb (c:data_to_word_config) (secn:num) (l:num)
  (dest:num) (names:(1 spt) option) v1 v2 =
        ((if ~(data_to_word_config_has_fp_ops c) then (GiveUp,l) else
         if dimindex (:'a) = 64 then
          (match encode_header c 3 1 with NONE -> (GiveUp,l) | SOME
            (header:'a word) ->
             (list_Seq [
                Assign 3 (wordLang_Load (Op asm_Add
                            [real_addr c (adjust_var v1); Const
                              bytes_in_word]));
                Assign 5 (wordLang_Load (Op asm_Add
                            [real_addr c (adjust_var v2); Const
                              bytes_in_word]));
                Inst (asm_FP (FPMovFromReg 0 3 3));
                Inst (asm_FP (FPMovFromReg 1 5 5));
                Inst (asm_FP (fp_bop_inst fpb));
                Inst (asm_FP (FPMovToReg 3 5 0));
                WriteWord64 c header dest 3],l)) else
          (match encode_header c 3 2 with NONE -> (GiveUp,l) | SOME
            header ->
             (list_Seq [
                Assign 15 (real_addr c (adjust_var v1));
                Assign 17 (real_addr c (adjust_var v2));
                Assign 11 (wordLang_Load (Op asm_Add [Var 15; Const
                  bytes_in_word]));
                Assign 13 (wordLang_Load (Op asm_Add [Var 15; Const
                  ((n2w 2) * bytes_in_word)]));
                Assign 21 (wordLang_Load (Op asm_Add [Var 17; Const
                  bytes_in_word]));
                Assign 23 (wordLang_Load (Op asm_Add [Var 17; Const
                  ((n2w 2) * bytes_in_word)]));
                Inst (asm_FP (FPMovFromReg 0 13 11));
                Inst (asm_FP (FPMovFromReg 1 23 21));
                Inst (asm_FP (fp_bop_inst fpb));
                Inst (asm_FP (FPMovToReg 5 3 0));
                WriteWord64_on_32 c header dest 5 3],l))):'a
                  wordLang_prog#num)`;;

let assign_FP_uop_def = cake_define
  `assign_FP_uop fpu (c:data_to_word_config) (secn:num) (l:num)
  (dest:num) (names:(1 spt) option) v1 =
        ((if ~(data_to_word_config_has_fp_ops c) then (GiveUp,l) else
         if dimindex (:'a) = 64 then
          (match encode_header c 3 1 with NONE -> (GiveUp,l) | SOME
            (header:'a word) ->
             (list_Seq [
                Assign 3 (wordLang_Load (Op asm_Add
                            [real_addr c (adjust_var v1); Const
                              bytes_in_word]));
                Inst (asm_FP (FPMovFromReg 0 3 3));
                Inst (asm_FP (fp_uop_inst fpu));
                Inst (asm_FP (FPMovToReg 3 5 1));
                WriteWord64 c header dest 3],l)) else
          (match encode_header c 3 2 with NONE -> (GiveUp,l) | SOME
            header ->
             (list_Seq [
                Assign 15 (real_addr c (adjust_var v1));
                Assign 11 (wordLang_Load (Op asm_Add [Var 15; Const
                  bytes_in_word]));
                Assign 13 (wordLang_Load (Op asm_Add [Var 15; Const
                  ((n2w 2) * bytes_in_word)]));
                Inst (asm_FP (FPMovFromReg 0 13 11));
                Inst (asm_FP (fp_uop_inst fpu));
                Inst (asm_FP (FPMovToReg 5 3 1));
                WriteWord64_on_32 c header dest 5 3],l))):'a
                  wordLang_prog#num)`;;

let assign_FinaliseCons_def = cake_define
  `assign_FinaliseCons (l:num) (dest:num) v1 =
                  ((Assign (adjust_var dest) (Var (adjust_var
                    v1)),l):'a wordLang_prog#num)`;;

(* HOL4 data_to_wordScript.sml:2460-2461: a theorem that HOL4 states
   as the value of an ML expression: all_assign_defs *)

let assign_def = cake_define
  `data_to_word_assign (c:data_to_word_config) (secn:num) (l:num)
  (dest:num) (op:closLang_op) (args:num list) (names:(1 spt) option) =
     (match op with closLang_IntOp (closLang_Const i) -> assign_Const
       i l dest | closLang_GlobOp closLang_GlobalsPtr -> (Assign
       (adjust_var dest) (wordLang_Lookup Globals),l) | closLang_GlobOp
       closLang_SetGlobalsPtr -> data_to_word_arg1 args
       (assign_SetGlobalsPtr c l dest) (Skip,l) | closLang_GlobOp
       (closLang_SetGlobal n) -> data_to_word_arg1 args
       (assign_SetGlobal c n l dest) (Skip,l) | closLang_GlobOp
       (closLang_Global n) -> assign_Global c n l dest | closLang_MemOp
       closLang_El -> data_to_word_arg2 args (assign_El c l dest)
       (Skip,l) | closLang_BlockOp (closLang_ElemAt n) ->
       data_to_word_arg1 args (assign_ElemAt c n l dest) (Skip,l) |
       closLang_MemOp closLang_DerefByte -> data_to_word_arg2 args
       (assign_DerefByte c l dest) (Skip,l) | closLang_MemOp
       closLang_Update -> arg3 args (assign_Update c l dest) (Skip,l) |
       closLang_MemOp closLang_UpdateCons -> arg3 args (assign_Update c
       l dest) (Skip,l) | closLang_MemOp closLang_UpdateByte -> arg3
       args (assign_UpdateByte c l dest) (Skip,l) | closLang_MemOp
       closLang_FinaliseCons -> data_to_word_arg1 args
       (assign_FinaliseCons l dest) (Skip,l) | closLang_BlockOp
       ListAppend -> data_to_word_arg2 args (assign_ListAppend c secn l
       dest names) (Skip,l) | closLang_BlockOp (closLang_Cons tag) ->
       assign_Cons c l dest tag args | closLang_MemOp (closLang_MutCons
       tag _30) -> assign_MutCons c l dest tag args | closLang_MemOp
       ConfigGC -> data_to_word_arg2 args (assign_ConfigGC c secn l dest
       names) (Skip,l) | closLang_BlockOp (closLang_Build parts') ->
       assign_Build c secn l dest names parts' | closLang_BlockOp
       (closLang_ConsExtend tag) -> assign_ConsExtend c secn l dest
       names tag args | closLang_MemOp closLang_Ref -> assign_Ref c secn
       l dest names args | ThunkOp (AllocThunk ev) -> data_to_word_arg1
       args (assign_AllocThunk ev c secn l dest names) (Skip,l) |
       ThunkOp (UpdateThunk ev) -> data_to_word_arg2 args
       (assign_UpdateThunk ev c l dest) (Skip,l) | closLang_MemOp
       (closLang_RefByte imm) -> data_to_word_arg2 args (assign_RefByte
       c secn l dest names imm) (Skip,l) | closLang_MemOp
       closLang_XorByte -> data_to_word_arg2 args (assign_XorByte c secn
       l dest names) (Skip,l) | closLang_MemOp (closLang_StringCmp b
       cmp) -> data_to_word_arg2 args (assign_StringCmp c secn l dest
       names b cmp) (Skip,l) | closLang_Label n -> (LocValue (adjust_var
       dest) n,l) | closLang_MemOp (closLang_CopyByte alloc_new) ->
       assign_CopyByte c secn l dest names args | closLang_MemOp
       closLang_RefArray -> data_to_word_arg2 args (assign_RefArray c
       secn l dest names) (Skip,l) | closLang_BlockOp (closLang_BoolTest
       test) -> data_to_word_arg2 args (assign_BoolTest l dest test)
       (Skip,l) | closLang_BlockOp closLang_BoolNot -> data_to_word_arg1
       args (assign_BoolNot l dest) (Skip,l) | closLang_WordOp (WordTest
       ws test) -> data_to_word_arg2 args (assign_WordTest l dest test)
       (Skip,l) | closLang_BlockOp (closLang_FromList tag) ->
       data_to_word_arg2 args (assign_FromList c secn l dest names tag)
       (Skip,l) | closLang_IntOp (closLang_LessConstSmall i) ->
       data_to_word_arg1 args (assign_LessConstSmall l dest i) (Skip,l)
       | closLang_MemOp (closLang_BoundsCheckByte leq) ->
         data_to_word_arg2 args (assign_BoundsCheckByte c secn l dest
           names leq) (Skip,l) | closLang_MemOp
           closLang_BoundsCheckArray ->
         data_to_word_arg2 args (assign_BoundsCheckArray c secn l
           dest names) (Skip,l) | closLang_BlockOp
           closLang_BoundsCheckBlock ->
         data_to_word_arg2 args (assign_BoundsCheckBlock c secn l
           dest names) (Skip,l) | closLang_BlockOp closLang_Equal ->
           data_to_word_arg2 args (assign_Equal c secn l dest names)
           (Skip,l) | closLang_IntOp closLang_Less -> data_to_word_arg2
           args (assign_Less c secn l dest names) (Skip,l) |
           closLang_IntOp closLang_LessEq -> data_to_word_arg2 args
           (assign_LessEq c secn l dest names) (Skip,l) |
           closLang_BlockOp closLang_LengthBlock -> data_to_word_arg1
           args (assign_LengthBlock c secn l dest names) (Skip,l) |
           closLang_MemOp closLang_Length -> data_to_word_arg1 args
           (assign_Length c secn l dest names) (Skip,l) | closLang_MemOp
           closLang_LengthByte -> data_to_word_arg1 args
           (assign_LengthByte c secn l dest names) (Skip,l) |
           closLang_BlockOp (closLang_TagLenEq tag len) ->
         data_to_word_arg1 args (assign_TagLenEq c secn l dest
           names tag len) (Skip,l) | closLang_BlockOp (closLang_LenEq
           len) -> data_to_word_arg1 args (assign_LenEq c secn l dest
           names len) (Skip,l) | closLang_BlockOp (closLang_TagEq
           tag) -> data_to_word_arg1 args (assign_TagEq c secn l dest
           names tag) (Skip,l) | closLang_IntOp closLang_Add ->
           data_to_word_arg2 args (assign_Add c secn l dest names)
           (Skip,l) | closLang_IntOp closLang_Sub ->
           data_to_word_arg2 args (assign_Sub c secn l dest names)
           (Skip,l) | closLang_IntOp closLang_Mult ->
           data_to_word_arg2 args (assign_Mult c secn l dest names)
           (Skip,l) | closLang_IntOp closLang_Div ->
           data_to_word_arg2 args (assign_Div c secn l dest names)
           (Skip,l) | closLang_IntOp closLang_Mod ->
           data_to_word_arg2 args (assign_Mod c secn l dest names)
           (Skip,l) | closLang_WordOp (WordOpw ast_W8 opw) ->
           data_to_word_arg2 args (assign_WordOpW8 opw c secn l dest
           names) (Skip,l) | closLang_WordOp (WordOpw ast_W64 opw) ->
           data_to_word_arg2 args (assign_WordOpW64 opw c secn l dest
           names) (Skip,l) | closLang_WordOp (WordShift ast_W8 sh n)
           -> data_to_word_arg1 args (assign_WordShiftW8 sh n c secn
           l dest names) (Skip,l) | closLang_WordOp (WordShift
           ast_W64 sh n) -> data_to_word_arg1 args
           (assign_WordShiftW64 sh n c secn l dest names) (Skip,l) |
           closLang_WordOp (WordFromWord b) -> data_to_word_arg1 args
           (assign_WordFromWord b c secn l dest names) (Skip,l) |
           closLang_WordOp (WordFromInt) -> data_to_word_arg1 args
           (assign_WordFromInt c secn l dest names) (Skip,l) |
           closLang_WordOp (WordToInt) -> data_to_word_arg1 args
           (assign_WordToInt c secn l dest names) (Skip,l) | FFI
           ffi_index -> data_to_word_arg2 args (assign_FFI ffi_index
           c secn l dest names) (Skip,l) | closLang_BlockOp
           (closLang_EqualConst p) -> data_to_word_arg1 args
           (assign_EqualConst p c secn l dest names) (Skip,l) |
           Install -> arg4 args (assign_Install c secn l dest names)
           (Skip,l) | closLang_WordOp (FP_cmp fpc) ->
           data_to_word_arg2 args (assign_FP_cmp fpc c secn l dest
           names) (Skip,l) | closLang_WordOp (FP_top fpt) -> arg3
           args (assign_FP_top fpt c secn l dest names) (Skip,l) |
           closLang_WordOp (FP_bop fpb) -> data_to_word_arg2 args
           (assign_FP_bop fpb c secn l dest names) (Skip,l) |
           closLang_WordOp (FP_uop fpu) -> data_to_word_arg1 args
           (assign_FP_uop fpu c secn l dest names) (Skip,l) | _31 ->
           (Skip,l))`;;
hol4_overload "assign" "data_to_word_assign";;

let force_thunk_def = cake_define
  `force_thunk (c:data_to_word_config) secn (l:num) ret loc v1 =
     ((match encode_header c (8 + 6) 1 with NONE -> (GiveUp,l) | SOME
       (header:'a word) ->
      If Test (adjust_var v1) (Imm (n2w 1))
        (match ret with NONE -> Return 0 [adjust_var v1] | SOME
          (dest,_32) -> Assign (adjust_var dest) (Var (adjust_var v1)))
        (list_Seq
           [Assign 1 (real_addr c (adjust_var v1));
            Assign 3 (Op And [Load (Var 1); Const (n2w 0b111100)]);
            If Equal 3 (Imm (n2w ((8 + 6) * 4)))
              (match ret with NONE ->
                  list_Seq
                    [Assign 1 (wordLang_Load (Op asm_Add [Var 1;
                      Const bytes_in_word]));
                     Return 0 [1]] | SOME (dest,_33) ->
                   Assign (adjust_var dest)
                          (wordLang_Load (Op asm_Add [Var 1; Const
                            bytes_in_word])))
            (If asm_NotEqual 3 (Imm (n2w ((0 + 6) * 4)))
              (match ret with NONE -> Return 0 [adjust_var v1] | SOME
                (dest,_34) -> Assign (adjust_var dest) (Var (adjust_var
                v1)))
              (list_Seq
                 [Assign 5 (wordLang_Load (Op asm_Add [Var 1; Const
                   bytes_in_word]));
                  (match ret with NONE -> Call NONE (SOME loc) [0;
                    adjust_var v1; 5] NONE | SOME (r,ns) -> Call (SOME
                    ([adjust_var r],adjust_sets ns,Skip,secn,l))
                              (SOME loc) [adjust_var v1; 5]
                                NONE)]))]),l + 1):'a
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
           (If Equal (adjust_var n) (Imm (n2w 18)) q1 q2,l2)) |
             dataLang_MakeSpace n names ->
         (let k = dimindex (:'a) DIV 8 in
         let w = n2w (n * k) in
         let w = (if w2n w = n * k then w else word_not (n2w 0)) in
           (Seq (Assign 1 (Op asm_Sub [wordLang_Lookup TriggerGC;
             wordLang_Lookup NextFree]))
                (If asm_Lower 1 (Imm w)
                  (list_Seq [SilentFFI c 3 (adjust_sets names);
                             Assign 1 (wordLang_Const w);
                             Alloc 1 (adjust_sets names);
                             SilentFFI c 3 (adjust_sets names)])
                 Skip),l)) | Assign dest op args names ->
                   data_to_word_assign c secn l dest op args names |
                   Force ret loc v -> force_thunk c secn l ret loc v |
                   Call ret target args handler ->
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
  (data_to_word_comp c n 2 p))`;;
hol4_overload "compile_part" "data_to_word_compile_part";;

let MemCopy_code_def = cake_define
  `MemCopy_code =
     (If Test 2 (Reg 2) (Return 0 [8])
         (list_Seq [Assign 1 (wordLang_Load (Var 4));
                    Assign 2 (Op asm_Sub [Var 2; Const (n2w 4)]);
                    Assign 4 (Op asm_Add [Var 4; Const
                      bytes_in_word]);
                    Store (Var 6) 1;
                    Assign 6 (Op asm_Add [Var 6; Const
                      bytes_in_word]);
                    Call NONE (SOME MemCopy_location) [0; 2; 4; 6;
                      8] NONE]):'a wordLang_prog)`;;

let ByteCopy_code_def = cake_define
  `ByteCopy_code c = (list_Seq
      [Assign 4 (ShiftVar Lsr 4 2);
       Assign 6 (ShiftVar Lsr 6 2);
       Assign 10 (ShiftVar Lsr 10 2);
       Assign 1 data_to_word_Unit;
       Assign 2 (Op asm_Add [real_addr c 2; Const bytes_in_word; Var
         4]);
       Assign 8 (Op asm_Add [real_addr c 8; Const bytes_in_word; Var
         10]);
       If asm_Lower 4 (Reg 10)
         (list_Seq [Assign 3 (Op asm_Sub [Var 6; Const (n2w 1)]);
                    Assign 2 (Op asm_Add [Var 2; Var 3]);
                    Assign 8 (Op asm_Add [Var 8; Var 3]);
                    Call NONE (SOME ByteCopySub_location) [0; 6; 2;
                      8; 1] NONE])
         (Call NONE (SOME ByteCopyAdd_location) [0; 6; 2; 8; 1]
           NONE)]:'a wordLang_prog)`;;

let ByteCopyAdd_code_def = cake_define
  `ByteCopyAdd_code =
   If asm_Lower 2 (Imm (n2w 4))
     (
       If asm_Lower 2 (Imm (n2w 2))
       (
         If Equal 2 (Imm (n2w 0)) (Return 0 [8])
         (
           list_Seq [
             Inst (asm_Mem asm_Load8 1 (Addr 4 (n2w 0)));
             Inst (asm_Mem asm_Store8 1 (Addr 6 (n2w 0)));
             Return 0 [8]]))
       (list_Seq [
         Inst (asm_Mem asm_Load8 1 (Addr 4 (n2w 0)));
         Inst (asm_Mem asm_Load8 3 (Addr 4 (n2w 1)));
         If Equal 2 (Imm (n2w 2))
           (list_Seq [
             Inst (asm_Mem asm_Store8 1 (Addr 6 (n2w 0)));
             Inst (asm_Mem asm_Store8 3 (Addr 6 (n2w 1)));
             Return 0 [8]])
           (list_Seq [
             Inst (asm_Mem asm_Load8 5 (Addr 4 (n2w 2)));
             Inst (asm_Mem asm_Store8 1 (Addr 6 (n2w 0)));
             Inst (asm_Mem asm_Store8 3 (Addr 6 (n2w 1)));
             Inst (asm_Mem asm_Store8 5 (Addr 6 (n2w 2)));
             Return 0 [8]])]))
     (list_Seq [
      Inst (asm_Mem asm_Load8 1 (Addr 4 (n2w 0)));
      Inst (asm_Mem asm_Load8 3 (Addr 4 (n2w 1)));
      Inst (asm_Mem asm_Load8 5 (Addr 4 (n2w 2)));
      Inst (asm_Mem asm_Load8 7 (Addr 4 (n2w 3)));
      Inst (asm_Mem asm_Store8 1 (Addr 6 (n2w 0)));
      Inst (asm_Mem asm_Store8 3 (Addr 6 (n2w 1)));
      Inst (asm_Mem asm_Store8 5 (Addr 6 (n2w 2)));
      Inst (asm_Mem asm_Store8 7 (Addr 6 (n2w 3)));
      Assign 9 (Op asm_Sub [Var 2; Const (n2w 4)]);
      Assign 11 (Op asm_Add [Var 4; Const (n2w 4)]);
      Assign 13 (Op asm_Add [Var 6; Const (n2w 4)]);
      Call NONE (SOME ByteCopyAdd_location) [0; 9; 11; 13; 8]
        NONE])`;;

let ByteCopySub_code_def = cake_define
  `ByteCopySub_code =
   If asm_Lower 2 (Imm (n2w 4))
     (
       If asm_Lower 2 (Imm (n2w 2))
       (
         If Equal 2 (Imm (n2w 0)) (Return 0 [8])
         (
           list_Seq [
             Inst (asm_Mem asm_Load8 1 (Addr 4 (n2w 0)));
             Inst (asm_Mem asm_Store8 1 (Addr 6 (n2w 0)));
             Return 0 [8]]))
       (list_Seq [
         Inst (asm_Mem asm_Load8 1 (Addr 4 (n2w 0)));
         Inst (asm_Mem asm_Load8 3 (Addr 4 (--(n2w 1))));
         If Equal 2 (Imm (n2w 2))
           (list_Seq [
             Inst (asm_Mem asm_Store8 1 (Addr 6 (n2w 0)));
             Inst (asm_Mem asm_Store8 3 (Addr 6 (--(n2w 1))));
             Return 0 [8]])
           (list_Seq [
             Inst (asm_Mem asm_Load8 5 (Addr 4 (--(n2w 2))));
             Inst (asm_Mem asm_Store8 1 (Addr 6 (n2w 0)));
             Inst (asm_Mem asm_Store8 3 (Addr 6 (--(n2w 1))));
             Inst (asm_Mem asm_Store8 5 (Addr 6 (--(n2w 2))));
             Return 0 [8]])]))
     (list_Seq [
      Inst (asm_Mem asm_Load8 1 (Addr 4 (n2w 0)));
      Inst (asm_Mem asm_Load8 3 (Addr 4 (--(n2w 1))));
      Inst (asm_Mem asm_Load8 5 (Addr 4 (--(n2w 2))));
      Inst (asm_Mem asm_Load8 7 (Addr 4 (--(n2w 3))));
      Inst (asm_Mem asm_Store8 1 (Addr 6 (n2w 0)));
      Inst (asm_Mem asm_Store8 3 (Addr 6 (--(n2w 1))));
      Inst (asm_Mem asm_Store8 5 (Addr 6 (--(n2w 2))));
      Inst (asm_Mem asm_Store8 7 (Addr 6 (--(n2w 3))));
      Assign 9 (Op asm_Sub [Var 2; Const (n2w 4)]);
      Assign 11 (Op asm_Sub [Var 4; Const (n2w 4)]);
      Assign 13 (Op asm_Sub [Var 6; Const (n2w 4)]);
      Call NONE (SOME ByteCopySub_location) [0; 9; 11; 13; 8]
        NONE])`;;

let ByteCopyNew_code_def = cake_define
  `ByteCopyNew_code c = (Skip:'a wordLang_prog)`;;

let stubs_def = cake_define
  `data_to_word_stubs (:'a) data_conf = [
     (FromList_location,4,((FromList_code data_conf):'a
       wordLang_prog));
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

let check_stubs_length = cake_theorem "check_stubs_length"
  (fun () ->
    `word_num_stubs + LENGTH (data_to_word_stubs (:'a) c) =
  data_num_stubs`)
  CHEAT_TAC;;

let check_LongDiv_location = cake_theorem "check_LongDiv_location"
  (fun () ->
    `LongDiv_location = div_location`)
  CHEAT_TAC;;

let compile_def = cake_define
  `data_to_word_compile data_conf word_conf asm_conf prog =
     (let data_conf =
       (data_to_word_config_has_fp_tern_fupd (K (asm_config_ISA
         asm_conf = ARMv7 /\ 2 < asm_config_fp_reg_count asm_conf))
         (data_to_word_config_has_fp_ops_fupd (K (1 <
         asm_config_fp_reg_count asm_conf)) data_conf)) in
     let p = data_to_word_stubs (:'a) data_conf ++ MAP
       (data_to_word_compile_part data_conf) prog in
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
       data_to_word_stubs (:'a) data_conf ++ MAP
         (data_to_word_compile_part data_conf) prog)`;;

(* compute bignum call graph *)

(* HOL4 data_to_wordScript.sml:2856-2867: the ML values that the
   definitions below antiquote *)

let AnyArith_call_tree_def = cake_define
  `AnyArith_call_tree =
     full_call_graph AnyArith_location
       (fromAList (stubs (:1)
          (data_to_word_config_has_longdiv_fupd (K F)
             (data_to_word_config_call_empty_ffi_fupd (K F) ARB))))`;;

let structure_le_def = cake_define
  `structure_le x1 x2 =
      match (x1,x2) with
        ((word_depth_Leaf:call_tree),_35) -> T
      | (_36,word_depth_Unknown) -> T
      | ((Const k1 t1),(Const k2 t2)) ->
     (k1 <= k2 /\ structure_le t1 t2)
      | ((Call n1 t2),(Call m1 u2)) ->
     (n1 = m1 /\ structure_le t2 u2)
      | ((Branch t1 t2),(Branch u1 u2)) ->
     (structure_le t1 u1 /\ structure_le t2 u2)
      | (_37,_38) -> F`;;

let AnyArith_call_tree_thm = cake_theorem "AnyArith_call_tree_thm"
  (fun () ->
    `structure_le
       (full_call_graph AnyArith_location (fromAList
         (data_to_word_stubs (:'a) (data_conf))))
       AnyArith_call_tree`)
  CHEAT_TAC;;
