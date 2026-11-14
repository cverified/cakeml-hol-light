(* ======================================================== *)
(*  data_to_word: ported from HOL4's
    compiler/backend/data_to_wordScript.sml
    A definition theory, with 201 definitions, 3 datatypes and 40
    theorems.  Needed by 20 files of the port.  *)
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

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "data_to_word"
  ["backend_common"; "dataLang"; "wordLang"; "word_bignum";
   "word_depth"; "word_to_word"];;

let gc_kind_INDUCT,gc_kind_RECURSION = define_datatype
  "gc_kind =
     // this configuration is used in data_to_wordProof and stack_alloc
     data_to_word_None
   | data_to_word_Simple
   | data_to_word_Generational (num list)
     // sizes of generations, smallest first
  ";;

let data_to_word_config_FIELDS = define_record "data_to_word_config"
  ["tag_bits","num";
   (* in each pointer *)
   "len_bits","num";
   (* in each pointer *)
   "pad_bits","num";
   (* in each pointer *)
   "len_size","num";
   (* size of length field in block header *)
   "has_div","bool";
   (* Div available in target *)
   "has_longdiv","bool";
   (* LongDiv available in target *)
   "has_fp_ops","bool";
   (* can compile floating-point ops *)
   "has_fp_tern","bool";
   (* can compile FMA *)
   "be","bool";
   (* bigendian *)
   "call_empty_ffi","bool";
   (* emit (T) / omit (F) calls to FFI "" *)
   "gc_kind","gc_kind"
   (* GC settings *)
  ];;

let adjust_var_def = new_definition
  `adjust_var n = 2 * n + (2:num)`;;

let adjust_set_def = new_definition
  `adjust_set (names:'a spt) =
     ((fromAList (MAP (\(n,k). (adjust_var n,one)) (toAList
       names))):1 spt)`;;

let adjust_sets_def = new_definition
  `adjust_sets (names:'a spt) =
     ((LS one,adjust_set names):1 spt#1 spt)`;;

let unit_def = new_definition
  `data_to_word_Unit = wordLang_Const (n2w 2)`;;

let GiveUp_def = new_definition
  `GiveUp = (wordLang_Seq (wordLang_Assign 1 (wordLang_Const (--(n2w
  1))))
                (wordLang_Alloc 1 (adjust_sets (LN:1 spt))):'a
                  wordLang_prog)`;;

let BignumHalt_def = new_definition
  `BignumHalt r = wordLang_If asm_Test r (Imm (n2w 1)) wordLang_Skip
  GiveUp`;;

let make_header_def = new_definition
  `make_header conf tag len =
     (let l = dimindex (:'a) - data_to_word_config_len_size conf in
       (n2w len << l || tag << 2 || ((n2w 3):'a word)))`;;

let tag_mask_def = new_definition
  `tag_mask conf =
     (let l = dimindex (:'a) - data_to_word_config_len_size conf in
       (word_slice (l - 1) 2) (word_not ((n2w 0):'a word)))`;;

let encode_header_def = new_definition
  `encode_header (conf:data_to_word_config) tag len =
     (if tag < 2 EXP (dimindex (:'a) - data_to_word_config_len_size
       conf - 2) /\
        tag < dimword (:'a) DIV 16 /\
        len < 2 EXP (dimindex (:'a) - 4) /\
        len < 2 EXP data_to_word_config_len_size conf then SOME
          ((make_header conf (n2w tag) len):'a word) else NONE)`;;

let _ = size_thms "wordLang_prog";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let data_to_word_list_Seq_def,data_to_word_list_Seq_ind = define_wf
  `MEASURE (\x0. list_size (wordLang_prog_size (\x. 0)) x0)`
  [`(data_to_word_list_Seq [] = wordLang_Skip) /\
   (data_to_word_list_Seq [x] = x) /\
   (data_to_word_list_Seq (CONS x (CONS y xs)) = wordLang_Seq x
     (data_to_word_list_Seq (CONS y xs)))`];;

let StoreEach_def,StoreEach_ind = define_rec
  [`StoreEach v [] (offset:'a word) = wordLang_Skip`;
   `StoreEach v (CONS x xs) (offset:'a word) =
         wordLang_Seq (wordLang_Store (wordLang_Op asm_Add
             [wordLang_Var v; wordLang_Const offset]) x)
             (StoreEach v xs (offset + bytes_in_word))`];;

let small_shift_length_def = new_definition
  `small_shift_length conf = data_to_word_config_len_bits conf +
  data_to_word_config_tag_bits conf + 1`;;

let shift_length_def = new_definition
  `shift_length conf = 1 + data_to_word_config_pad_bits conf +
  data_to_word_config_len_bits conf + data_to_word_config_tag_bits
  conf + 1`;;

let conf_ok_def = new_definition
  `conf_ok (:'a) c <=>
     shift_length c < dimindex (:'a) /\
     backend_common_word_shift (:'a) <= shift_length c /\
       ~(data_to_word_config_len_size c = 0) /\
       data_to_word_config_len_size
     c + 7 < dimindex (:'a)`;;

let max_heap_limit_def = new_definition
  `max_heap_limit (:'a) c =
     MIN (dimword (:'a) DIV 2 EXP shift_length c)
         (dimword (:'a) DIV 2 EXP (backend_common_word_shift (:'a)
           + 1))`;;

let all_ones_def = new_definition
  `all_ones m n = (if m <= n then (n2w 0) else (word_slice (m - 1) n)
  (word_not (n2w 0)))`;;

let maxout_bits_def = new_definition
  `maxout_bits n rep_len k =
     (if n < 2 EXP rep_len - 1 then n2w n << k else all_ones (k +
       rep_len) k)`;;

let ptr_bits_def = new_definition
  `ptr_bits conf tag len =
     (maxout_bits tag (data_to_word_config_tag_bits conf) (1 +
       data_to_word_config_len_bits conf) ||
      maxout_bits len (data_to_word_config_len_bits conf) 1)`;;

let real_addr_def = new_definition
  `((real_addr (conf:data_to_word_config) r):'a wordLang_exp) =
     (let k = backend_common_word_shift (:'a) in
     let l = shift_length conf in
       if k = l /\ data_to_word_config_len_bits conf = 0 /\
         data_to_word_config_tag_bits conf = 0 then
         wordLang_Op asm_Add [wordLang_Lookup CurrHeap; wordLang_Op
           asm_Sub [wordLang_Var r; wordLang_Const (n2w 1)]] else if k
           <= data_to_word_config_pad_bits conf + 1 then
         wordLang_Op asm_Add [wordLang_Lookup CurrHeap; (\sh e n.
           wordLang_Shift sh e (wordLang_Const (n2w n))) Lsr
           (wordLang_Var r) (l - k)] else
         wordLang_Op asm_Add [wordLang_Lookup CurrHeap; (\sh e n.
           wordLang_Shift sh e (wordLang_Const (n2w n))) Lsl ((\sh e
           n. wordLang_Shift sh e (wordLang_Const (n2w n))) Lsr
           (wordLang_Var r) l) k])`;;

let real_offset_def = new_definition
  `((real_offset (conf:data_to_word_config) r):'a wordLang_exp) =
      wordLang_Op asm_Add [wordLang_Const bytes_in_word;
              if dimindex (:'a) = 32 then wordLang_Var r else (\sh
                e n. wordLang_Shift sh e (wordLang_Const (n2w n)))
                Lsl (wordLang_Var r) 1]`;;

let real_byte_offset_def = new_definition
  `(real_byte_offset r:'a wordLang_exp) =
     wordLang_Op asm_Add [wordLang_Const bytes_in_word;
             (\sh e n. wordLang_Shift sh e (wordLang_Const (n2w
               n))) Lsr (wordLang_Var r) 2]`;;

let word_op_type_INDUCT,word_op_type_RECURSION = define_datatype
  "word_op_type =
     Bitwise binop
   | Carried binop";;

let lookup_word_op_def = define_cases
  [`lookup_word_op backend_common_Andw = Bitwise asm_And`;
   `lookup_word_op backend_common_Orw = Bitwise asm_Or`;
   `lookup_word_op (backend_common_Xor:opw) = Bitwise asm_Xor`;
   `lookup_word_op (backend_common_Add:opw) = Carried asm_Add`;
   `lookup_word_op (backend_common_Sub:opw) = Carried asm_Sub`];;
add_simp lookup_word_op_def;;

let FromList_location_def = new_definition
  `FromList_location = word_num_stubs`;;
let FromList1_location_def = new_definition
  `FromList1_location = FromList_location + 1`;;
let RefByte_location_def = new_definition
  `RefByte_location = FromList1_location + 1`;;
let RefArray_location_def = new_definition
  `RefArray_location = RefByte_location + 1`;;
let replicate_location_def = new_definition
  `Replicate_location = RefArray_location + 1`;;
let AnyArith_location_def = new_definition
  `AnyArith_location = Replicate_location + 1`;;
let add_location_def = new_definition
  `Add_location = AnyArith_location + 1`;;
let sub_location_def = new_definition
  `Sub_location = Add_location + 1`;;
let mul_location_def = new_definition
  `Mul_location = Sub_location + 1`;;
let data_to_word_Div_location_def = new_definition
  `Div_location = Mul_location + 1`;;
let mod_location_def = new_definition
  `Mod_location = Div_location + 1`;;
let compare1_location_def = new_definition
  `Compare1_location = Mod_location + 1`;;
let compare_location_def = new_definition
  `Compare_location = Compare1_location + 1`;;
let equal1_location_def = new_definition
  `Equal1_location = Compare_location + 1`;;
let equal_location_def = new_definition
  `Equal_location = Equal1_location + 1`;;
let LongDiv1_location_def = new_definition
  `LongDiv1_location = Equal_location + 1`;;
let LongDiv_location_def = new_definition
  `LongDiv_location = LongDiv1_location + 1`;;
let MemCopy_location_def = new_definition
  `MemCopy_location = LongDiv_location + 1`;;
let ByteCopy_location_def = new_definition
  `ByteCopy_location = MemCopy_location + 1`;;
let ByteCopyAdd_location_def = new_definition
  `ByteCopyAdd_location = ByteCopy_location + 1`;;
let ByteCopySub_location_def = new_definition
  `ByteCopySub_location = ByteCopyAdd_location + 1`;;
let ByteCopyNew_location_def = new_definition
  `ByteCopyNew_location = ByteCopySub_location + 1`;;
let install_location_def = new_definition
  `Install_location = ByteCopyNew_location + 1`;;
let InstallCode_location_def = new_definition
  `InstallCode_location = Install_location + 1`;;
let InstallData_location_def = new_definition
  `InstallData_location = InstallCode_location + 1`;;
let dummy_location_def = new_definition
  `Dummy_location = InstallData_location + 1`;;
let append_location_def = new_definition
  `Append_location = Dummy_location + 1`;;
let AppendMainLoop_location_def = new_definition
  `AppendMainLoop_location = Append_location + 1`;;
let AppendLenLoop_location_def = new_definition
  `AppendLenLoop_location = AppendMainLoop_location + 1`;;
let XorLoop_location_def = new_definition
  `XorLoop_location = AppendLenLoop_location + 1`;;
let unused_location_def = new_definition
  `Unused_location = XorLoop_location + 1`;;
let StringCmpLoop_location_def = new_definition
  `StringCmpLoop_location = Unused_location + 1`;;
let bignum_location_def = new_definition
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

let SilentFFI_def = new_definition
  `SilentFFI c n names =
     (if data_to_word_config_call_empty_ffi c then
       data_to_word_list_Seq [wordLang_Assign n (wordLang_Const (n2w
         0));
                 wordLang_Assign 7 (wordLang_Op asm_Sub
                   [wordLang_Lookup NextFree; wordLang_Lookup
                   CurrHeap]);
                 wordLang_Assign 9 (wordLang_Lookup HeapLength);
                 wordLang_FFI (implode "") 7 n 9 n names] else
                   wordLang_Skip)`;;

let AllocVar_def = new_definition
  `AllocVar c (limit':num) (names:1 spt) =
     data_to_word_list_Seq [wordLang_Assign 1 ((\sh e n.
       wordLang_Shift sh e (wordLang_Const (n2w n))) Lsr (wordLang_Var
       1) 2);
               wordLang_If asm_Lower 1 (Imm (n2w limit'))
                 (wordLang_Assign 1 ((\sh e n. wordLang_Shift sh e
                   (wordLang_Const (n2w n))) Lsl (wordLang_Op asm_Add
                   [wordLang_Var 1; wordLang_Const (n2w 1)])
                   (backend_common_word_shift (:'a))))
                 (wordLang_Assign 1 (wordLang_Const (--((n2w 1):'a
                   word))));
               wordLang_Assign 3 (wordLang_Op asm_Sub
                 [wordLang_Lookup TriggerGC; wordLang_Lookup NextFree]);
               wordLang_If asm_Lower 3 (Reg 1)
                 (data_to_word_list_Seq [SilentFFI c 3 (FST
                   (adjust_sets names),
                              sptree_insert 1 one (SND (adjust_sets
                                names)));
                            wordLang_Alloc 1 (adjust_sets names);
                            SilentFFI c 3 (adjust_sets names)])
                              wordLang_Skip]`;;

let MakeBytes_def = new_definition
  `MakeBytes n =
     (data_to_word_list_Seq [wordLang_Assign n ((\sh e n.
       wordLang_Shift sh e (wordLang_Const (n2w n))) Lsr (wordLang_Var
       n) 2);
               wordLang_Assign n (wordLang_Op asm_Or [wordLang_Var n;
                 (\sh e n. wordLang_Shift sh e (wordLang_Const (n2w n)))
                 Lsl (wordLang_Var n) 8]);
               wordLang_Assign n (wordLang_Op asm_Or [wordLang_Var n;
                 (\sh e n. wordLang_Shift sh e (wordLang_Const (n2w n)))
                 Lsl (wordLang_Var n) 16]);
               if dimindex (:'a) = 32 then wordLang_Skip else
                 wordLang_Assign n (wordLang_Op asm_Or
                   [wordLang_Var n; (\sh e n. wordLang_Shift sh e
                   (wordLang_Const (n2w n))) Lsl (wordLang_Var n)
                   32])]:'a wordLang_prog)`;;

let SmallLsr_def = new_definition
  `SmallLsr e n = (if n = 0 then e else (\sh e n. wordLang_Shift sh e
  (wordLang_Const (n2w n))) Lsr e n)`;;

let WriteLastByte_aux_def = new_definition
  `WriteLastByte_aux offset a b n p =
     wordLang_If asm_Equal n (Imm offset) wordLang_Skip
       (wordLang_Seq (wordLang_Inst (asm_Mem asm_Store8 b (Addr a
         offset))) p)`;;

let WriteLastBytes_def = new_definition
  `WriteLastBytes a b n =
     WriteLastByte_aux ((n2w 0):'a word) a b n (
       WriteLastByte_aux (n2w 1) a b n (
         WriteLastByte_aux (n2w 2) a b n (
           WriteLastByte_aux (n2w 3) a b n (
             if dimindex (:'a) = 32 then wordLang_Skip else
             WriteLastByte_aux (n2w 4) a b n (
               WriteLastByte_aux (n2w 5) a b n (
                 WriteLastByte_aux (n2w 6) a b n (
                   WriteLastByte_aux (n2w 7) a b n
                     wordLang_Skip)))))))`;;

let RefByte_code_def = new_definition
  `RefByte_code c =
       (let limit' = MIN (2 EXP data_to_word_config_len_size c)
         (dimword (:'a) DIV 16) in
       let h = wordLang_Op asm_Add [(\sh e n. wordLang_Shift sh e
         (wordLang_Const (n2w n))) Lsr (wordLang_Var 2) 2;
         wordLang_Const bytes_in_word] in
       let x = SmallLsr h (dimindex (:'a) - 63) in
       let y = (\sh e n. wordLang_Shift sh e (wordLang_Const (n2w
         n))) Lsl h (dimindex (:'a) - backend_common_word_shift (:'a) -
         data_to_word_config_len_size c) in
         data_to_word_list_Seq
           [BignumHalt 2;
            wordLang_Assign 1 x;
            AllocVar c limit' (sptree_fromList [one; one; one]);
            // compute length
            wordLang_Assign 5 ((\sh e n. wordLang_Shift sh e
              (wordLang_Const (n2w n))) Lsr h (backend_common_word_shift
              (:'a)));
            wordLang_Assign 7 ((\sh e n. wordLang_Shift sh e
              (wordLang_Const (n2w n))) Lsl (wordLang_Var 5) 2);
            wordLang_Assign 9 (wordLang_Lookup NextFree);
            // adjust end of heap
            wordLang_Assign 1 (wordLang_Op asm_Add [wordLang_Var 9;
                              (\sh e n. wordLang_Shift sh e
                                (wordLang_Const (n2w n))) Lsl
                                (wordLang_Var 5)
                                (backend_common_word_shift (:'a))]);
            wordLang_Set NextFree (wordLang_Op asm_Add [wordLang_Var
              1; wordLang_Const bytes_in_word]);
            // 3 := return value
            wordLang_Assign 3 (wordLang_Op asm_Or [(\sh e n.
              wordLang_Shift sh e (wordLang_Const (n2w n))) Lsl
              (wordLang_Op asm_Sub [wordLang_Var 9; wordLang_Lookup
              CurrHeap])
                (shift_length c - backend_common_word_shift (:'a));
                  wordLang_Const ((n2w 1):'a word)]);
            // compute header
            wordLang_Assign 5 (wordLang_Op asm_Or [wordLang_Op asm_Or
              [y; wordLang_Const (n2w 7)]; wordLang_Var 6]);
            // compute repeated byte
            MakeBytes 4;
            // store header
            wordLang_Store (wordLang_Var 9) 5;
            // write last word of byte array
            wordLang_Assign 11 (wordLang_Op asm_And [(\sh e n.
              wordLang_Shift sh e (wordLang_Const (n2w n))) Lsr
              (wordLang_Var 2) 2;
                              wordLang_Const (bytes_in_word - (n2w
                                1))]);
            wordLang_Assign 13 (wordLang_Const (n2w 0));
            wordLang_Store (wordLang_Var 1) 13;
            WriteLastBytes 1 4 11;
            wordLang_Assign 7 (wordLang_Op asm_Sub [wordLang_Var 7;
              wordLang_Const (n2w 4)]);
            // write rest of byte array
            wordLang_Call NONE (SOME Replicate_location)
              [
               // ret_loc, addr, v, n, ret_val
               0; 9; 4; 7; 3] NONE]:'a wordLang_prog)`;;

let maxout_bits_code_def = new_definition
  `Maxout_bits_code rep_len k dest n =
     (wordLang_If asm_Lower n (Imm (n2w (2 EXP rep_len - 1)))
       (wordLang_Assign dest (wordLang_Op asm_Or [wordLang_Var dest;
         (\sh e n. wordLang_Shift sh e (wordLang_Const (n2w n))) Lsl
         (wordLang_Var n) k]))
       (wordLang_Assign dest (wordLang_Op asm_Or [wordLang_Var
         dest; wordLang_Const (all_ones (k + rep_len) k)])):'a
         wordLang_prog)`;;

let make_ptr_bits_code_def = new_definition
  `Make_ptr_bits_code c tag len dest =
     (data_to_word_list_Seq [wordLang_Assign dest (wordLang_Op asm_Or
        [wordLang_Const (n2w 1); (\sh e n. wordLang_Shift sh e
          (wordLang_Const (n2w n))) Lsl (wordLang_Op asm_Sub
          [wordLang_Lookup NextFree; wordLang_Lookup CurrHeap])
            (shift_length c - backend_common_word_shift (:'a))]);
         Maxout_bits_code (data_to_word_config_tag_bits c) (1 +
           data_to_word_config_len_bits c) dest tag;
         Maxout_bits_code (data_to_word_config_len_bits c) 1 dest
           len]:'a wordLang_prog)`;;

let FromList_code_def = new_definition
  `FromList_code c =
     (let limit' = MIN (2 EXP data_to_word_config_len_size c)
       (dimword (:'a) DIV 16) in
     let h = (\sh e n. wordLang_Shift sh e (wordLang_Const (n2w n)))
       Lsl (wordLang_Var 2) (dimindex (:'a) -
       data_to_word_config_len_size c - 2) in
       wordLang_If asm_Equal 2 (Imm (n2w 0))
         (data_to_word_list_Seq [wordLang_Assign 6 (wordLang_Op
           asm_Add [wordLang_Var 6; wordLang_Const ((n2w 2):'a word)]);
                    wordLang_Return 0 [6]])
         (data_to_word_list_Seq
           [BignumHalt 2;
            wordLang_Assign 1 (wordLang_Var 2); AllocVar c limit'
              (sptree_fromList [one; one; one]);
            wordLang_Assign 1 (wordLang_Lookup NextFree);
            wordLang_Assign 5 (wordLang_Op asm_Or [h; wordLang_Const
              (n2w 3); wordLang_Var 6]);
            wordLang_Assign 7 ((\sh e n. wordLang_Shift sh e
              (wordLang_Const (n2w n))) Lsr (wordLang_Var 2) 2);
            wordLang_Assign 9 ((\sh e n. wordLang_Shift sh e
              (wordLang_Const (n2w n))) Lsr (wordLang_Var 6) 4);
            Make_ptr_bits_code c 9 7 3;
            wordLang_Call NONE (SOME FromList1_location) [0; 1; 4;
              2; 3; 5] NONE]):'a wordLang_prog)`;;

let FromList1_code_def = new_definition
  `FromList1_code c =
     // 0 = return address
     // 2 = address to write to
     // 4 = where to lookup what to write
     // 6 = how many left to write
     // 8 = value to be returned
     // 10 = first thing to write
     (data_to_word_list_Seq
       [wordLang_Store (wordLang_Var 2) 10;
        wordLang_Assign 2 (wordLang_Op asm_Add [wordLang_Var 2;
          wordLang_Const bytes_in_word]);
        wordLang_If asm_Equal 6 (Imm (n2w 0))
          (data_to_word_list_Seq
             [wordLang_Set NextFree (wordLang_Var 2);
              wordLang_Return 0 [8]])
          (data_to_word_list_Seq
             [wordLang_Assign 4 (real_addr c 4);
              wordLang_Assign 10 (wordLang_Load (wordLang_Op asm_Add
                [wordLang_Var 4; wordLang_Const bytes_in_word]));
              wordLang_Assign 4 (wordLang_Load (wordLang_Op asm_Add
                [wordLang_Var 4; wordLang_Const ((n2w 2) *
                bytes_in_word)]));
              wordLang_Assign 6 (wordLang_Op asm_Sub [wordLang_Var 6;
                wordLang_Const (n2w 4)]);
              wordLang_Call NONE (SOME FromList1_location) [0; 2;
                4; 6; 8; 10] NONE])]:'a wordLang_prog)`;;

let RefArray_code_def = new_definition
  `RefArray_code c =
         (data_to_word_list_Seq
           [wordLang_Assign 1 ((\sh e n. wordLang_Shift sh e
             (wordLang_Const (n2w n))) Lsl (wordLang_Op asm_Add [((\sh e
             n. wordLang_Shift sh e (wordLang_Const (n2w n))) Lsr
             (wordLang_Var 2) 2); wordLang_Const (n2w 1)])
                       (backend_common_word_shift (:'a)));
            wordLang_Set TriggerGC (wordLang_Op asm_Sub
              [wordLang_Lookup TriggerGC; wordLang_Var 1]);
            wordLang_Assign 1 (wordLang_Op asm_Sub [wordLang_Lookup
              EndOfHeap; wordLang_Var 1]);
            wordLang_Set EndOfHeap (wordLang_Var 1);
            // 3 := return value
            wordLang_Assign 3 (wordLang_Op asm_Or [(\sh e n.
              wordLang_Shift sh e (wordLang_Const (n2w n))) Lsl
              (wordLang_Op asm_Sub [wordLang_Var 1; wordLang_Lookup
              CurrHeap])
                (shift_length c - backend_common_word_shift (:'a));
                  wordLang_Const ((n2w 1):'a word)]);
            // compute header
            wordLang_Assign 5 (wordLang_Op asm_Or [(\sh e n.
              wordLang_Shift sh e (wordLang_Const (n2w n))) Lsl
              (wordLang_Var 2)
                              (dimindex (:'a) -
                                data_to_word_config_len_size c - 2);
                             wordLang_Const (make_header c (n2w 2)
                               0)]);
            // store header
            wordLang_Store (wordLang_Var 1) 5;
            wordLang_Call NONE (SOME Replicate_location)
               [
                // ret_loc, addr, v, n, ret_val
                0; 1; 4; 2; 3] NONE]:'a wordLang_prog)`;;

let replicate_code_def = new_definition
  `Replicate_code =
     // 0 = return address
     // 2 = address to write to
     // 4 = what to write at each location
     // 6 = how many left to write
     // 8 = value to be returned
     (wordLang_If asm_Equal 6 (Imm (n2w 0)) (wordLang_Return 0 [8])
       (data_to_word_list_Seq [wordLang_Assign 2 (wordLang_Op asm_Add
         [wordLang_Var 2; wordLang_Const (bytes_in_word)]);
                  wordLang_Store (wordLang_Var 2) 4;
                  wordLang_Assign 6 (wordLang_Op asm_Sub
                    [wordLang_Var 6; wordLang_Const (n2w 4)]);
                  wordLang_Call NONE (SOME Replicate_location) [0;
                    2; 4; 6; 8] NONE]):'a wordLang_prog)`;;

let AddNumSize_def = new_definition
  `AddNumSize c src =
     (wordLang_If asm_Equal (adjust_var src) (Imm (n2w 0))
       wordLang_Skip
       (wordLang_If asm_Test (adjust_var src) (Imm (n2w 1))
          (wordLang_Assign 1 (wordLang_Op asm_Add [wordLang_Var 1;
            wordLang_Const (n2w 4)]))
        (wordLang_Assign 1 (wordLang_Op asm_Add [wordLang_Var 1;
          ((\sh e n. wordLang_Shift sh e (wordLang_Const (n2w n)))
            Lsl ((\sh e n. wordLang_Shift sh e (wordLang_Const (n2w n)))
            Lsr
             (wordLang_Load (real_addr c (adjust_var src)))
                (dimindex (:'a) - data_to_word_config_len_size
                  c))) 2]))):'a wordLang_prog)`;;

let AnyHeader_def = new_definition
  `AnyHeader c r a t1
         // header
         t2
           // pointer
           t3 =
     // payload
     wordLang_If asm_Equal r (Imm ((n2w 0):'a word))
       (data_to_word_list_Seq [wordLang_Assign 7 (wordLang_Const (n2w
         0));
                  wordLang_Set (Temp t1) (wordLang_Var r);
                  wordLang_Set (Temp t2) (wordLang_Var r);
                  wordLang_Set (Temp t3) (wordLang_Var r)])
    (wordLang_If asm_NotTest r (Imm (n2w 1))
       (data_to_word_list_Seq
         [wordLang_Assign 7 (real_addr c r);
          wordLang_Set (Temp t2) (wordLang_Op asm_Add [wordLang_Var
            7; wordLang_Const bytes_in_word]);
          wordLang_Set (Temp t1) (wordLang_Op asm_Add
            [(\sh e n. wordLang_Shift sh e (wordLang_Const (n2w n)))
              Lsl ((\sh e n. wordLang_Shift sh e (wordLang_Const (n2w
              n))) Lsr (wordLang_Load (wordLang_Var 7)) ((dimindex
              (:'a)) - data_to_word_config_len_size c)) 1;
             wordLang_Op asm_And [wordLang_Const (n2w 1); (\sh e n.
               wordLang_Shift sh e (wordLang_Const (n2w n))) Lsr
               (wordLang_Load (wordLang_Var 7)) 4]]);
          wordLang_Set (Temp t3) (wordLang_Const (n2w 0))])
    (wordLang_If asm_NotLess r (Imm (n2w 0))
       (data_to_word_list_Seq
         [wordLang_Set (Temp t1) (wordLang_Const (n2w 2));
          wordLang_Set (Temp t2) (wordLang_Lookup (if a then
            OtherHeap else NextFree));
          wordLang_Set (Temp t3) ((\sh e n. wordLang_Shift sh e
            (wordLang_Const (n2w n))) Lsr (wordLang_Var r) 2);
          wordLang_Assign 7 (wordLang_Const (n2w 0))])
       (data_to_word_list_Seq
         [wordLang_Set (Temp t1) (wordLang_Const (n2w 3));
          wordLang_Set (Temp t2) (wordLang_Lookup (if a then
            OtherHeap else NextFree));
          wordLang_Set (Temp t3) (wordLang_Op asm_Sub [wordLang_Const
            (n2w 0); (\sh e n. wordLang_Shift sh e (wordLang_Const (n2w
            n))) Asr (wordLang_Var r) 2]);
          wordLang_Assign 7 (wordLang_Const (n2w 0))])))`;;

let ShiftVar_def = new_definition
  `ShiftVar sh v n =
     (if sh = Ror then
       (let m = (if n < dimindex (:'a) then n else n MOD (dimindex
         (:'a))) in
          if m = 0 then wordLang_Var v else (\sh e n. wordLang_Shift
            sh e (wordLang_Const (n2w n))) sh (wordLang_Var v) m) else
            if n = 0 then wordLang_Var v else if dimindex (:'a) <= n
            then
       if sh = Asr then (\sh e n. wordLang_Shift sh e
         (wordLang_Const (n2w n))) sh (wordLang_Var v) (dimindex
         (:'a) - 1) else wordLang_Const (n2w 0) else ((\sh e n.
         wordLang_Shift sh e (wordLang_Const (n2w n))) sh
         (wordLang_Var v) n):'a wordLang_exp)`;;

let AnyArith_code_def = new_definition
  `AnyArith_code c = (data_to_word_list_Seq [
       // perform allocation
       wordLang_Assign 1 (wordLang_Const (n2w 4));
       AddNumSize c 0;
       AddNumSize c 1;
       wordLang_Set (Temp (n2w 29)) (wordLang_Var 1);
       AllocVar c (2 EXP data_to_word_config_len_size c)
         (sptree_fromList [one; one; one]);
       // convert smallnums to bignum if necessary
       AnyHeader c 2 F (n2w 0) (n2w 31) (n2w 12);
       AnyHeader c 4 T (n2w 1) (n2w 30) (n2w 11);
       wordLang_Get 1 (Temp (n2w 11));
       wordLang_Store (wordLang_Lookup OtherHeap) 1;
       wordLang_Get 1 (Temp (n2w 12));
       wordLang_Store (wordLang_Lookup NextFree) 1;
       wordLang_Get 1 (Temp (n2w 29));
       wordLang_Assign 2 (wordLang_Lookup NextFree);
       wordLang_Set (Temp (n2w 29)) (wordLang_Var 2);
       wordLang_Set (Temp (n2w 3)) ((\sh e n. wordLang_Shift sh e
         (wordLang_Const (n2w n))) Lsr (wordLang_Var 6) 2);
       wordLang_Assign 3 (wordLang_Const (n2w 0));
       // zero out result array
       wordLang_Call (SOME ([0],(sptree_fromList
         [one],LN),wordLang_Skip,AnyArith_location,2))
         (SOME Replicate_location) [2; 3; 1; 0] NONE;
       // perform bignum calculation
       wordLang_Set (Temp (n2w 29)) (wordLang_Op asm_Add
         [wordLang_Lookup (Temp (n2w 29)); wordLang_Const
         bytes_in_word]);
       wordLang_Call (SOME ([1],(sptree_fromList
         [one],LN),wordLang_Skip,AnyArith_location,3))
         (SOME Bignum_location) [] NONE;
       // convert bignum to smallnum if possible without loss of info
       wordLang_Get 1 (Temp (n2w 10));
       wordLang_If asm_Test 1 (Reg 1) (wordLang_Return 0 [1])
         wordLang_Skip;
       wordLang_Assign 3 (wordLang_Load (wordLang_Op asm_Add
         [wordLang_Lookup NextFree; wordLang_Const bytes_in_word]));
       wordLang_If asm_Equal 1 (Imm (n2w 2))
         (wordLang_Seq (wordLang_Assign 5 ((\sh e n. wordLang_Shift
           sh e (wordLang_Const (n2w n))) Lsr (wordLang_Var 3) (dimindex
           (:'a) - 3)))
              (wordLang_If asm_Test 5 (Reg 5)
                 (wordLang_Seq (wordLang_Assign 1 ((\sh e n.
                   wordLang_Shift sh e (wordLang_Const (n2w n))) Lsl
                   (wordLang_Var 3) 2))
                      (wordLang_Return 0 [1]))
                 wordLang_Skip))
         (wordLang_If asm_Equal 1 (Imm (n2w 3))
           (wordLang_Seq (wordLang_Assign 5 ((\sh e n. wordLang_Shift
             sh e (wordLang_Const (n2w n))) Lsr (wordLang_Op asm_Sub
             [wordLang_Var 3; wordLang_Const (n2w 1)])
                             (dimindex (:'a) - 3)))
                (wordLang_If asm_Test 5 (Reg 5)
                   (wordLang_Seq (wordLang_Assign 1 (wordLang_Op
                     asm_Sub [wordLang_Const (n2w 0); (\sh e n.
                     wordLang_Shift sh e (wordLang_Const (n2w n))) Lsl
                     (wordLang_Var 3) 2]))
                        (wordLang_Return 0 [1]))
                   wordLang_Skip))
           (wordLang_Assign 5 (wordLang_Const (n2w 0))));
       // return the bignum
       wordLang_Assign 5 (wordLang_Lookup NextFree);
       wordLang_Assign 6 (ShiftVar Lsr 1 1);
       wordLang_Assign 8 (wordLang_Op asm_And [wordLang_Var 1;
         wordLang_Const (n2w 1)]);
       wordLang_Assign 7 (wordLang_Op asm_Or [wordLang_Const (n2w
         0b1111);
                        ShiftVar Lsl 6 (dimindex (:'a) -
                          data_to_word_config_len_size c);
                        ShiftVar Lsl 8 4]);
       wordLang_Store (wordLang_Var 5) 7;
       wordLang_Assign 1 (wordLang_Op asm_Sub [wordLang_Var 5;
         wordLang_Lookup CurrHeap]);
       wordLang_Assign 1 (wordLang_Op asm_Or [ShiftVar Lsl 1
         (shift_length c - backend_common_word_shift (:'a));
         wordLang_Const (n2w 1)]);
       wordLang_Set NextFree (wordLang_Op asm_Add [wordLang_Var 5;
         wordLang_Const bytes_in_word;
                             ShiftVar Lsl 6
                               (backend_common_word_shift (:'a))]);
       wordLang_Return 0 [1]]:'a wordLang_prog)`;;

let add_code_def = new_definition
  `Add_code = (wordLang_Seq (wordLang_Assign 6 (wordLang_Const (n2w (4 *
  0))))
                  (wordLang_Call NONE (SOME AnyArith_location) [0;
                    2; 4; 6] NONE):'a wordLang_prog)`;;

let sub_code_def = new_definition
  `Sub_code = (wordLang_Seq (wordLang_Assign 6 (wordLang_Const (n2w (4 *
  1))))
                  (wordLang_Call NONE (SOME AnyArith_location) [0;
                    2; 4; 6] NONE):'a wordLang_prog)`;;

let mul_code_def = new_definition
  `Mul_code = (wordLang_Seq (wordLang_Assign 6 (wordLang_Const (n2w (4 *
  4))))
                  (wordLang_Call NONE (SOME AnyArith_location) [0;
                    2; 4; 6] NONE):'a wordLang_prog)`;;

let div_code_def = new_definition
  `Div_code = (wordLang_Seq (wordLang_Assign 6 (wordLang_Const (n2w (4 *
  5))))
                  (wordLang_Call NONE (SOME AnyArith_location) [0;
                    2; 4; 6] NONE):'a wordLang_prog)`;;

let mod_code_def = new_definition
  `Mod_code = (wordLang_Seq (wordLang_Assign 6 (wordLang_Const (n2w (4 *
  6))))
                  (wordLang_Call NONE (SOME AnyArith_location) [0;
                    2; 4; 6] NONE):'a wordLang_prog)`;;

let install_code_def = new_definition
  `Install_code c =
       (data_to_word_list_Seq [wordLang_Assign 1 (wordLang_Lookup
         BitmapBuffer);
                 wordLang_Assign 3 (wordLang_Lookup CodeBuffer);
                 wordLang_Set BitmapBuffer (wordLang_Var 2);
                 wordLang_Set CodeBuffer (wordLang_Var 4);
                 wordLang_Install 3 4 1 2 (LS one,LN);
                 wordLang_Return 0 [3]]:'a wordLang_prog)`;;

let InstallCode_code_def = new_definition
  `InstallCode_code c =
        (wordLang_If asm_Test 2 (Imm (n2w 1))
         (wordLang_Seq (wordLang_Assign 2 (wordLang_Lookup
           BitmapBuffer))
              (wordLang_Call NONE (SOME InstallData_location) [0; 2;
                4; 6] NONE))
         (data_to_word_list_Seq [wordLang_Assign 3 (real_addr c 2);
                    wordLang_Assign 2 (wordLang_Load (wordLang_Op
                      asm_Add [wordLang_Var 3; wordLang_Const
                      bytes_in_word]));
                    wordLang_Assign 2 (ShiftVar Lsr 2 2);
                    wordLang_CodeBufferWrite 6 2;
                    wordLang_Assign 6 (wordLang_Op asm_Add
                      [wordLang_Var 6; wordLang_Const (n2w 1)]);
                    wordLang_Assign 2 (wordLang_Load (wordLang_Op
                      asm_Add [wordLang_Var 3; wordLang_Const ((n2w 2) *
                      bytes_in_word)]));
                    wordLang_Call NONE (SOME InstallCode_location)
                      [0; 2; 4; 6] NONE]):'a wordLang_prog)`;;

let InstallData_code_def = new_definition
  `InstallData_code c =
        (wordLang_If asm_Test 4 (Imm (n2w 1))
         (data_to_word_list_Seq [wordLang_Call NONE (SOME
           Install_location) [0; 2; 6] NONE])
         (data_to_word_list_Seq [wordLang_Assign 3 (real_addr c 4);
                    wordLang_Assign 4 (wordLang_Load (wordLang_Op
                      asm_Add [wordLang_Var 3; wordLang_Const
                      bytes_in_word]));
                    wordLang_Assign 4 (real_addr c 4);
                    wordLang_Assign 4 (wordLang_Load (wordLang_Op
                      asm_Add [wordLang_Var 4; wordLang_Const
                      bytes_in_word]));
                    wordLang_DataBufferWrite 2 4;
                    wordLang_Assign 2 (wordLang_Op asm_Add
                      [wordLang_Var 2; wordLang_Const bytes_in_word]);
                    wordLang_Assign 4 (wordLang_Load (wordLang_Op
                      asm_Add [wordLang_Var 3; wordLang_Const ((n2w 2) *
                      bytes_in_word)]));
                    wordLang_Call NONE (SOME InstallData_location)
                      [0; 2; 4; 6] NONE]):'a wordLang_prog)`;;

let compare1_code_def = new_definition
  `Compare1_code =
     // l is 2, a1 is 4, a2 is 6
     wordLang_If asm_Equal 2 (Imm (n2w 0))
       (wordLang_Seq (wordLang_Assign 2 (wordLang_Const (n2w 1)))
         (wordLang_Return 0 [2]))
       (data_to_word_list_Seq
          [wordLang_Assign 8 (wordLang_Load (wordLang_Var 4));
           wordLang_Assign 9 (wordLang_Load (wordLang_Var 6));
           wordLang_If asm_Equal 8 (Reg 9)
             (data_to_word_list_Seq
                [wordLang_Assign 2 (wordLang_Op asm_Sub [wordLang_Var
                  2; wordLang_Const (n2w 1)]);
                 wordLang_Assign 4 (wordLang_Op asm_Sub [wordLang_Var
                   4; wordLang_Const bytes_in_word]);
                 wordLang_Assign 6 (wordLang_Op asm_Sub [wordLang_Var
                   6; wordLang_Const bytes_in_word]);
                 wordLang_Call NONE (SOME Compare1_location) [0; 2;
                   4; 6] NONE])
             (wordLang_If asm_Lower 8 (Reg 9)
               (wordLang_Seq (wordLang_Assign 2 (wordLang_Const (n2w
                 0))) (wordLang_Return 0 [2]))
               (wordLang_Seq (wordLang_Assign 2 (wordLang_Const
                 (n2w 2))) (wordLang_Return 0 [2])))])`;;

let compare_code_def = new_definition
  `Compare_code c =
     // this code can assume that the arguments (2 and 4) are not both
     // small numbers
     wordLang_If asm_Test 2 (Imm (n2w 1))
       (
        // 1st arg is small number, means that 2nd must be bigum
        data_to_word_list_Seq [wordLang_Assign 1 (wordLang_Load
          (real_addr c 4));
                  // loads header of 2nd arg
                  wordLang_If asm_Test 1 (Imm (n2w 16))
                    (wordLang_Seq (wordLang_Assign 2 (wordLang_Const
                      (n2w 0))) (wordLang_Return 0 [2]))
                    (wordLang_Seq (wordLang_Assign 2 (wordLang_Const
                      (n2w 2))) (wordLang_Return 0 [2]))])
    (wordLang_If asm_Test 4 (Imm (n2w 1))
       (
        // 2nd arg is small number: 1st must be bigum
        data_to_word_list_Seq [wordLang_Assign 1 (wordLang_Load
          (real_addr c 2));
                  // loads header of 1st arg
                  wordLang_If asm_Test 1 (Imm ((n2w 16):'a word))
                    (wordLang_Seq (wordLang_Assign 2 (wordLang_Const
                      (n2w 2))) (wordLang_Return 0 [2]))
                    (wordLang_Seq (wordLang_Assign 2 (wordLang_Const
                      (n2w 0))) (wordLang_Return 0 [2]))])
       (data_to_word_list_Seq [wordLang_Assign 11 (real_addr c 2);
                  wordLang_Assign 1 (wordLang_Load (wordLang_Var
                    11));
                  // loads header of 1st arg
                  wordLang_Assign 13 (real_addr c 4);
                  wordLang_Assign 3 (wordLang_Load (wordLang_Var
                    13));
                  // loads header of 2nd arg
                  wordLang_Assign 6 ((\sh e n. wordLang_Shift sh e
                    (wordLang_Const (n2w n))) Lsr (wordLang_Var 1)
                    ((dimindex (:'a) - data_to_word_config_len_size
                    c)));
                  wordLang_Assign 8 ((\sh e n. wordLang_Shift sh e
                    (wordLang_Const (n2w n))) Lsr (wordLang_Var 3)
                    ((dimindex (:'a) - data_to_word_config_len_size
                    c)));
                  wordLang_If asm_Equal 1 (Reg 3)
                    (
                     // headers are the same
                     data_to_word_list_Seq
                      [wordLang_Assign 2 (wordLang_Op asm_Add
                        [wordLang_Var 11; (\sh e n. wordLang_Shift sh e
                        (wordLang_Const (n2w n))) Lsl (wordLang_Var 6)
                        (backend_common_word_shift (:'a))]);
                       wordLang_Assign 4 (wordLang_Op asm_Add
                         [wordLang_Var 13; (\sh e n. wordLang_Shift sh e
                         (wordLang_Const (n2w n))) Lsl (wordLang_Var 6)
                         (backend_common_word_shift (:'a))]);
                       wordLang_If asm_Test 1 (Imm (n2w 16))
                        (wordLang_Call NONE (SOME Compare1_location)
                          [0; 6; 2; 4] NONE)
                        (wordLang_Call NONE (SOME Compare1_location)
                          [0; 6; 4; 2] NONE)])
                    (
                     // headers are not the same
                     wordLang_If asm_Test 1 (Imm (n2w 16))
                       (wordLang_If asm_Test 3 (Imm (n2w 16))
                          (wordLang_If asm_Lower 6 (Reg 8)
                             (wordLang_Seq (wordLang_Assign 2
                               (wordLang_Const (n2w 0)))
                               (wordLang_Return 0 [2]))
                             (wordLang_Seq (wordLang_Assign 2
                               (wordLang_Const (n2w 2)))
                               (wordLang_Return 0 [2])))
                          (wordLang_Seq (wordLang_Assign 2
                            (wordLang_Const (n2w 2))) (wordLang_Return 0
                            [2])))
                       (wordLang_If asm_Test 3 (Imm (n2w 16))
                          (wordLang_Seq (wordLang_Assign 2
                            (wordLang_Const (n2w 0))) (wordLang_Return 0
                            [2]))
                          (wordLang_If asm_Lower 6 (Reg 8)
                             (wordLang_Seq (wordLang_Assign 2
                               (wordLang_Const (n2w 2)))
                               (wordLang_Return 0 [2]))
                             (wordLang_Seq (wordLang_Assign 2
                               (wordLang_Const (n2w 0)))
                               (wordLang_Return 0 [2])))))]))`;;

let equal1_code_def = new_definition
  `Equal1_code =
     data_to_word_list_Seq [
       wordLang_If asm_Equal 2 (Imm (n2w 0))
         (wordLang_Seq (wordLang_Assign 2 (wordLang_Const (n2w 1)))
           (wordLang_Return 0 [2])) wordLang_Skip;
       wordLang_Assign 1 (wordLang_Load (wordLang_Var 4));
       wordLang_Assign 3 (wordLang_Load (wordLang_Var 6));
       wordLang_Call (SOME ([5],(list_insert [0; 2; 4; 6]
         LN,LN),wordLang_Skip,Equal1_location,2))
         (SOME Equal_location) [1; 3] NONE;
       wordLang_If asm_Equal 5 (Imm (n2w 1)) wordLang_Skip
         (wordLang_Return 0 [5]);
       wordLang_Assign 2 (wordLang_Op asm_Sub [wordLang_Var 2;
         wordLang_Const (n2w 1)]);
       wordLang_Assign 4 (wordLang_Op asm_Add [wordLang_Var 4;
         wordLang_Const bytes_in_word]);
       wordLang_Assign 6 (wordLang_Op asm_Add [wordLang_Var 6;
         wordLang_Const bytes_in_word]);
       wordLang_Call NONE (SOME Equal1_location) [0; 2; 4; 6]
         NONE]`;;

let equal_code_def = new_definition
  `Equal_code c =
     data_to_word_list_Seq [
       wordLang_If asm_Equal 2 (Reg 4)
         (wordLang_Seq (wordLang_Assign 2 (wordLang_Const ((n2w 1):'a
           word))) (wordLang_Return 0 [2])) wordLang_Skip;
       wordLang_Assign 1 (wordLang_Op asm_And [wordLang_Var 2;
         wordLang_Var 4]);
       wordLang_If asm_Test 1 (Imm (n2w 1))
         (wordLang_Seq (wordLang_Assign 2 (wordLang_Const (n2w 0)))
           (wordLang_Return 0 [2])) wordLang_Skip;
       wordLang_Assign 20 (real_addr c 2);
       wordLang_Assign 40 (real_addr c 4);
       wordLang_Assign 21 (wordLang_Load (wordLang_Var 20));
       wordLang_Assign 41 (wordLang_Load (wordLang_Var 40));
       wordLang_If asm_Test 21 (Imm (n2w 0b1100))
         (data_to_word_list_Seq
           [wordLang_Assign 1 (wordLang_Op asm_And [wordLang_Var 21;
             wordLang_Const (tag_mask c || (n2w 2))]);
            wordLang_If asm_Equal 1 (Imm (n2w (16 * closure_tag +
              2)))
              (wordLang_Seq (wordLang_Assign 2 (wordLang_Const (n2w
                1))) (wordLang_Return 0 [2])) wordLang_Skip;
            wordLang_If asm_Equal 1 (Imm (n2w (16 * partial_app_tag +
              2)))
              (wordLang_Seq (wordLang_Assign 2 (wordLang_Const (n2w
                1))) (wordLang_Return 0 [2])) wordLang_Skip;
            wordLang_If asm_Equal 21 (Reg 41)
              wordLang_Skip (wordLang_Seq (wordLang_Assign 2
                (wordLang_Const (n2w 0))) (wordLang_Return 0 [2]));
            wordLang_Assign 6 (ShiftVar Lsr 21 ((dimindex (:'a) -
              data_to_word_config_len_size c)));
            wordLang_Assign 20 (wordLang_Op asm_Add [wordLang_Var 20;
              wordLang_Const bytes_in_word]);
            wordLang_Assign 40 (wordLang_Op asm_Add [wordLang_Var 40;
              wordLang_Const bytes_in_word]);
            wordLang_Call NONE (SOME Equal1_location) [0; 6; 20; 40]
              NONE])
         wordLang_Skip;
       wordLang_If asm_Equal 21 (Reg 41) wordLang_Skip
         (wordLang_Seq (wordLang_Assign 2 (wordLang_Const (n2w 0)))
           (wordLang_Return 0 [2]));
       wordLang_If asm_Test 21 (Imm (n2w 4))
         (wordLang_Seq (wordLang_Assign 2 (wordLang_Const (n2w 0)))
           (wordLang_Return 0 [2])) wordLang_Skip;
       wordLang_Assign 1 (wordLang_Op asm_And [wordLang_Var 21;
         wordLang_Const (n2w 24)]);
       wordLang_If asm_Equal 1 (Imm (n2w 16))
         (wordLang_Seq (wordLang_Assign 2 (wordLang_Const (n2w 0)))
           (wordLang_Return 0 [2])) wordLang_Skip;
       wordLang_Assign 6 (ShiftVar Lsr 21 ((dimindex (:'a) -
         data_to_word_config_len_size c)));
       wordLang_Assign 2 (wordLang_Op asm_Add [wordLang_Var 20;
         ShiftVar Lsl 6 (backend_common_word_shift (:'a))]);
       wordLang_Assign 4 (wordLang_Op asm_Add [wordLang_Var 40;
         ShiftVar Lsl 6 (backend_common_word_shift (:'a))]);
       wordLang_Call NONE (SOME Compare1_location) [0; 6; 2; 4]
         NONE]`;;

let LongDiv_code_def = new_definition
  `LongDiv_code c =
     (if data_to_word_config_has_longdiv c then
       data_to_word_list_Seq [wordLang_Inst (asm_Arith (asm_LongDiv 1
         3 2 4 6));
                 wordLang_Set (Temp (n2w 28)) (wordLang_Var 3);
                 wordLang_Return 0 [1]] else
       wordLang_Seq (wordLang_Assign 10 (wordLang_Const ((n2w 0):'a
         word)))
      (wordLang_Seq (wordLang_Assign 11 (wordLang_Const (n2w
        (dimindex (:'a)))))
           (wordLang_Call NONE (SOME LongDiv1_location) [0; 11; 6;
             10; 10; 4; 2] NONE)))`;;

let LongDiv1_code_def = new_definition
  `LongDiv1_code c =
     (if data_to_word_config_has_longdiv c then wordLang_Skip else
       // the following code is based on multiwordTheory.single_div_loop_def
       wordLang_If asm_Test 2 (Reg 2)
         (wordLang_Seq (wordLang_Set (Temp (n2w 28)) (wordLang_Var
           10):'a wordLang_prog) (wordLang_Return 0 [8]))
         (data_to_word_list_Seq [wordLang_Assign 6 (wordLang_Op
           asm_Or [ShiftVar Lsr 6 1;
                              ShiftVar Lsl 4 (dimindex (:'a) - 1)]);
                    wordLang_Assign 4 (ShiftVar Lsr 4 1);
                    wordLang_Assign 8 (ShiftVar Lsl 8 1);
                    wordLang_Assign 2 (wordLang_Op asm_Sub
                      [wordLang_Var 2; wordLang_Const ((n2w 1):'a
                      word)]);
                    wordLang_If asm_Lower 12 (Reg 4)
                      (wordLang_Call NONE (SOME LongDiv1_location)
                        [0; 2; 4; 6; 8; 10; 12] NONE) wordLang_Skip;
                    wordLang_If asm_Equal 12 (Reg 4)
                      (wordLang_If asm_Lower 10 (Reg 6)
                         (wordLang_Call NONE (SOME LongDiv1_location)
                            [0; 2; 4; 6; 8; 10; 12] NONE)
                              wordLang_Skip) wordLang_Skip;
                    wordLang_Assign 8 (wordLang_Op asm_Add
                      [wordLang_Var 8; wordLang_Const (n2w 1)]);
                    wordLang_Assign 16 (wordLang_Op asm_Xor
                      [wordLang_Var 6; wordLang_Const (--(n2w 1))]);
                    wordLang_Assign 14 (wordLang_Op asm_Xor
                      [wordLang_Var 4; wordLang_Const (--(n2w 1))]);
                    wordLang_Assign 1 (wordLang_Const (n2w 1));
                    wordLang_Inst (asm_Arith (asm_AddCarry 10 10 16
                      1));
                    wordLang_Inst (asm_Arith (asm_AddCarry 12 12 14
                      1));
                    wordLang_Call NONE (SOME LongDiv1_location)
                      [0; 2; 4; 6; 8; 10; 12] NONE]))`;;

let append_code_def = new_definition
  `Append_code c =
     (match encode_header c 0 2 with NONE -> (wordLang_Skip:'a
       wordLang_prog) | SOME (header:'a word) ->
         wordLang_If asm_Test 4 (Imm (n2w 1)) (wordLang_Return 0 [2])
           (data_to_word_list_Seq
             [wordLang_Set (Temp (n2w 0)) (wordLang_Var 2);
              wordLang_Set (Temp (n2w 1)) (wordLang_Var 4);
              wordLang_Assign 1 (wordLang_Lookup NextFree);
              wordLang_Assign 3 (wordLang_Const header);
              wordLang_Assign 5 (wordLang_Op asm_Sub [wordLang_Lookup
                TriggerGC; wordLang_Var 1]);
              wordLang_Assign 7 (wordLang_Op asm_Or [(\sh e n.
                wordLang_Shift sh e (wordLang_Const (n2w n))) Lsl
                (wordLang_Op asm_Sub [wordLang_Var 1; wordLang_Lookup
                CurrHeap])
                              (shift_length c -
                                backend_common_word_shift (:'a));
                              wordLang_Const ((n2w 1) || (word_bits
                                (small_shift_length c - 1) 0)
                              (ptr_bits c 0 2))]);
              wordLang_Set (Temp (n2w 2)) (wordLang_Var 7);
              wordLang_Call NONE (SOME AppendMainLoop_location)
                [0; 1; 4; 3; 5; 7] NONE]))`;;

let AppendMainLoop_code_def = new_definition
  `AppendMainLoop_code c =
     (data_to_word_list_Seq
       [wordLang_Assign 1 (real_addr c 4);
        wordLang_Assign 3 (wordLang_Load (wordLang_Op asm_Add
          [wordLang_Var 1; wordLang_Const bytes_in_word]));
        wordLang_Assign 5 (wordLang_Load (wordLang_Op asm_Add
          [wordLang_Var 1; wordLang_Const ((n2w 2) * bytes_in_word)]));
        wordLang_If asm_Lower 8 (Imm ((n2w 3) * bytes_in_word))
          (
           // unlucky case: GC is needed
           wordLang_Seq (wordLang_Assign 1 (wordLang_Const (n2w 0)))
               (wordLang_Call NONE (SOME AppendLenLoop_location) [0;
                 4; 1] NONE)) wordLang_Skip;
        wordLang_Store (wordLang_Var 2) 6;
        wordLang_Store (wordLang_Op asm_Add [wordLang_Var 2;
          wordLang_Const bytes_in_word]) 3;
        wordLang_If asm_Test 5 (Imm (n2w 1)) wordLang_Skip
          (
           // cons case:
           data_to_word_list_Seq
            [wordLang_Assign 10 (wordLang_Op asm_Add [wordLang_Var
              10;
               wordLang_Const (n2w (3 * 2 EXP shift_length c))]);
             wordLang_Assign 8 (wordLang_Op asm_Sub [wordLang_Var 8;
               wordLang_Const ((n2w 3) * bytes_in_word)]);
             wordLang_Store (wordLang_Op asm_Add [wordLang_Var 2;
               wordLang_Const ((n2w 2) * bytes_in_word)]) 10;
             wordLang_Assign 2 (wordLang_Op asm_Add [wordLang_Var 2;
               wordLang_Const ((n2w 3) * bytes_in_word)]);
             wordLang_Call NONE (SOME AppendMainLoop_location) [0; 2;
               5; 6; 8; 10] NONE]);
        // nil case
        wordLang_Assign 1 (wordLang_Lookup (Temp (n2w 0)));
        // arg 2 to append
        wordLang_Assign 3 (wordLang_Lookup (Temp (n2w 2)));
        // ret value
        wordLang_Store (wordLang_Op asm_Add [wordLang_Var 2;
          wordLang_Const ((n2w 2) * bytes_in_word)]) 1;
        wordLang_Set NextFree (wordLang_Op asm_Add [wordLang_Var 2;
          wordLang_Const ((n2w 3) * bytes_in_word)]);
        wordLang_Return 0 [3]]:'a wordLang_prog)`;;

let AppendLenLoop_code_def = new_definition
  `AppendLenLoop_code c =
     wordLang_If asm_Test 2 (Imm (n2w 1))
       (data_to_word_list_Seq
         [wordLang_Assign 1 (wordLang_Op asm_Sub [wordLang_Lookup
           TriggerGC; wordLang_Lookup NextFree]);
          wordLang_Assign 1 (wordLang_Op asm_Add [wordLang_Var 4;
            ShiftVar Lsr 1 (backend_common_word_shift (:'a) - 2)]);
          wordLang_Assign 4 (wordLang_Lookup (Temp (n2w 0)));
          wordLang_Assign 2 (wordLang_Lookup (Temp (n2w 1)));
          AllocVar c (dimword (:'a) DIV 8 - 1) (sptree_fromList [one;
            one]);
          wordLang_Call NONE (SOME Append_location) [0; 4; 2] NONE])
       (data_to_word_list_Seq
         [wordLang_Assign 2 (wordLang_Load (wordLang_Op asm_Add
           [real_addr c 2; wordLang_Const ((n2w 2) * bytes_in_word)]));
          wordLang_Assign 4 (wordLang_Op asm_Add [wordLang_Var 4;
            wordLang_Const ((n2w 12):'a word)]);
          wordLang_Call NONE (SOME AppendLenLoop_location) [0; 2;
            4] NONE])`;;

let XorLoop_code_def = new_definition
  `XorLoop_code =
     (wordLang_If asm_Lower 6 (Imm (n2w 2))
       (wordLang_If asm_Equal 6 (Imm (n2w 0))
          (data_to_word_list_Seq [wordLang_Assign 1 (wordLang_Const
            (n2w 2));
                     wordLang_Return 0 [1]])
          (data_to_word_list_Seq [wordLang_Assign 5 (wordLang_Load
            (wordLang_Var 4));
                     wordLang_Assign 3 (wordLang_Load (wordLang_Var
                       2));
                     wordLang_Assign 7 (wordLang_Op asm_Xor
                       [wordLang_Var 5; wordLang_Var 3]);
                     wordLang_Store (wordLang_Var 2) 7;
                     wordLang_Assign 1 (wordLang_Const (n2w 2));
                     wordLang_Return 0 [1]]))
       (data_to_word_list_Seq [wordLang_Assign 5 (wordLang_Load
         (wordLang_Var 4));
                  wordLang_Assign 3 (wordLang_Load (wordLang_Var 2));
                  wordLang_Assign 9 (wordLang_Load (wordLang_Op
                    asm_Add [wordLang_Var 4; wordLang_Const
                    bytes_in_word]));
                  wordLang_Assign 7 (wordLang_Load (wordLang_Op
                    asm_Add [wordLang_Var 2; wordLang_Const
                    bytes_in_word]));
                  wordLang_Assign 6 (wordLang_Op asm_Sub
                    [wordLang_Var 6; wordLang_Const (n2w 2)]);
                  wordLang_Assign 5 (wordLang_Op asm_Xor
                    [wordLang_Var 5; wordLang_Var 3]);
                  wordLang_Assign 9 (wordLang_Op asm_Xor
                    [wordLang_Var 9; wordLang_Var 7]);
                  wordLang_Store (wordLang_Var 2) 5;
                  wordLang_Store (wordLang_Op asm_Add [wordLang_Var
                    2; wordLang_Const bytes_in_word]) 9;
                  wordLang_Assign 4 (wordLang_Op asm_Add
                    [wordLang_Var 4; wordLang_Const ((n2w 2) *
                    bytes_in_word)]);
                  wordLang_Assign 2 (wordLang_Op asm_Add
                    [wordLang_Var 2; wordLang_Const ((n2w 2) *
                    bytes_in_word)]);
                  wordLang_Call NONE (SOME XorLoop_location) [0;
                    2; 4; 6] NONE]):'a wordLang_prog)`;;

let StringCmpLoop_code_def = new_definition
  `StringCmpLoop_code =
     (wordLang_If asm_Equal 6 (Imm bytes_in_word)
       (wordLang_Return 0 [8; 10])
       (data_to_word_list_Seq
          [wordLang_Inst (asm_Mem asm_Load8 1 (Addr 2 (n2w 0)));
           wordLang_Inst (asm_Mem asm_Load8 3 (Addr 4 (n2w 0)));
           wordLang_If asm_NotEqual 1 (Reg 3) (wordLang_Return 0 [1;
             3]) wordLang_Skip;
           wordLang_Assign 2 (wordLang_Op asm_Add [wordLang_Var 2;
             wordLang_Const (n2w 1)]);
           wordLang_Assign 4 (wordLang_Op asm_Add [wordLang_Var 4;
             wordLang_Const (n2w 1)]);
           wordLang_Assign 6 (wordLang_Op asm_Sub [wordLang_Var 6;
             wordLang_Const (n2w 1)]);
           wordLang_Call NONE (SOME StringCmpLoop_location) [0; 2;
             4; 6; 8; 10] NONE]):'a wordLang_prog)`;;

let data_to_word_get_names_def = define_cases
  [`data_to_word_get_names NONE = LN`;
   `data_to_word_get_names (SOME x) = x`];;

let LoadWord64_def = new_definition
  `LoadWord64 c i j =
     (wordLang_Assign i (wordLang_Load (wordLang_Op asm_Add
       [real_addr c j; wordLang_Const bytes_in_word])):'a
       wordLang_prog)`;;

let LoadBignum_def = new_definition
  `LoadBignum c header word1' k = (data_to_word_list_Seq [
     wordLang_Assign word1' (real_addr c k);
     wordLang_Assign header (wordLang_Load (wordLang_Var word1'));
     wordLang_Assign word1' (wordLang_Load (wordLang_Op asm_Add
       [wordLang_Var word1'; wordLang_Const bytes_in_word]))]:'a
       wordLang_prog)`;;

let WriteWord64_def = new_definition
  `// also works for storing bignums of length 1
   WriteWord64 c (header:'a word) dest i =
     (data_to_word_list_Seq [wordLang_Assign 1 (wordLang_Lookup
       NextFree);
               wordLang_Store (wordLang_Op asm_Add [wordLang_Var 1;
                 wordLang_Const bytes_in_word]) i;
               wordLang_Assign 3 (wordLang_Const header);
               wordLang_Store (wordLang_Var 1) 3;
               wordLang_Set NextFree (wordLang_Op asm_Add
                 [wordLang_Var 1; wordLang_Const ((n2w 2) *
                 bytes_in_word)]);
               wordLang_Assign (adjust_var dest)
                 (wordLang_Op asm_Or [(\sh e n. wordLang_Shift sh e
                   (wordLang_Const (n2w n))) Lsl (wordLang_Op asm_Sub
                   [wordLang_Var 1; wordLang_Lookup CurrHeap])
                           (shift_length c -
                             backend_common_word_shift (:'a));
                         wordLang_Const (n2w 1)])]:'a
                           wordLang_prog)`;;

let WriteWord64_on_32_def = new_definition
  `WriteWord64_on_32 c (header:'a word) dest i1 i2 =
     (data_to_word_list_Seq [wordLang_Assign 1 (wordLang_Lookup
       NextFree);
               wordLang_Store (wordLang_Op asm_Add [wordLang_Var 1;
                 wordLang_Const bytes_in_word]) i2;
               wordLang_Store (wordLang_Op asm_Add [wordLang_Var 1;
                 wordLang_Const ((n2w 2) * bytes_in_word)]) i1;
               wordLang_Assign 3 (wordLang_Const header);
               wordLang_Store (wordLang_Var 1) 3;
               wordLang_Set NextFree (wordLang_Op asm_Add
                 [wordLang_Var 1; wordLang_Const ((n2w 3) *
                 bytes_in_word)]);
               wordLang_Assign (adjust_var dest)
                 (wordLang_Op asm_Or [(\sh e n. wordLang_Shift sh e
                   (wordLang_Const (n2w n))) Lsl (wordLang_Op asm_Sub
                   [wordLang_Var 1; wordLang_Lookup CurrHeap])
                           (shift_length c -
                             backend_common_word_shift (:'a));
                         wordLang_Const (n2w 1)])]:'a
                           wordLang_prog)`;;

let WriteWord32_on_32_def = new_definition
  `WriteWord32_on_32 c header dest i1 =
      data_to_word_list_Seq
        [wordLang_Assign 1 (wordLang_Lookup NextFree);
         wordLang_Store (wordLang_Op asm_Add [wordLang_Var 1;
           wordLang_Const bytes_in_word]) i1;
         wordLang_Assign 3 (wordLang_Const header); wordLang_Store
           (wordLang_Var 1) 3;
         wordLang_Set NextFree (wordLang_Op asm_Add [wordLang_Var 1;
           wordLang_Const ((n2w 2) * bytes_in_word)]);
         wordLang_Assign (adjust_var dest)
           (wordLang_Op asm_Or
              [(\sh e n. wordLang_Shift sh e (wordLang_Const (n2w
                n))) Lsl (wordLang_Op asm_Sub [wordLang_Var 1;
                wordLang_Lookup CurrHeap])
                 (shift_length c - backend_common_word_shift
                   (:'a)); wordLang_Const ((n2w 1):'a word)])]`;;

let WordOp64_on_32_def = new_definition
  `WordOp64_on_32 (opw:opw) =
     (match opw with backend_common_Andw -> data_to_word_list_Seq
       [wordLang_Assign 29 (wordLang_Const (n2w 0));
                         wordLang_Assign 27 (wordLang_Const (n2w 0));
                         wordLang_Assign 33 (wordLang_Op asm_And
                           [wordLang_Var 13; wordLang_Var 23]);
                         wordLang_Assign 31 (wordLang_Op asm_And
                           [wordLang_Var 11; wordLang_Var 21])] |
                           backend_common_Orw -> data_to_word_list_Seq
                           [wordLang_Assign 29 (wordLang_Const (n2w 0));
                         wordLang_Assign 27 (wordLang_Const (n2w 0));
                         wordLang_Assign 33 (wordLang_Op asm_Or
                           [wordLang_Var 13; wordLang_Var 23]);
                         wordLang_Assign 31 (wordLang_Op asm_Or
                           [wordLang_Var 11; wordLang_Var 21])] |
                           asm_Xor -> data_to_word_list_Seq
                           [wordLang_Assign 29 (wordLang_Const (n2w 0));
                         wordLang_Assign 27 (wordLang_Const (n2w 0));
                         wordLang_Assign 33 (wordLang_Op asm_Xor
                           [wordLang_Var 13; wordLang_Var 23]);
                         wordLang_Assign 31 (wordLang_Op asm_Xor
                           [wordLang_Var 11; wordLang_Var 21])] |
                           backend_common_Add -> data_to_word_list_Seq
                           [wordLang_Assign 29 (wordLang_Const (n2w 0));
                         wordLang_Assign 27 (wordLang_Const (n2w 0));
                         wordLang_Inst (asm_Arith (asm_AddCarry 33 13
                           23 29));
                         wordLang_Inst (asm_Arith (asm_AddCarry 31 11
                           21 29))] | backend_common_Sub ->
                           data_to_word_list_Seq [wordLang_Assign 29
                           (wordLang_Const (n2w 1));
                         wordLang_Assign 27 (wordLang_Op asm_Xor
                           [wordLang_Const (--(n2w 1)); wordLang_Var
                           23]);
                         wordLang_Inst (asm_Arith (asm_AddCarry 33 13
                           27 29));
                         wordLang_Assign 27 (wordLang_Op asm_Xor
                           [wordLang_Const (--(n2w 1)); wordLang_Var
                           21]);
                         wordLang_Inst (asm_Arith (asm_AddCarry 31
                           11 27 29))])`;;

let WordShift64_on_32_def = new_definition
  `WordShift64_on_32 sh n = data_to_word_list_Seq
     (
      // inputs in 11 and 13, writes results in 31 and 33
      if sh = Ror then
       (let n = n MOD 64 in
         (if n < 32 then
            [wordLang_Assign 33 (wordLang_Op asm_Or [ShiftVar Lsl 11
              (32 - n);
                              ShiftVar Lsr 13 n]);
             wordLang_Assign 31 (wordLang_Op asm_Or [ShiftVar Lsl 13
               (32 - n);
                              ShiftVar Lsr 11 n])] else
            [wordLang_Assign 33 (wordLang_Op asm_Or [ShiftVar Lsl 13
              (64 - n);
                              ShiftVar Lsr 11 (n - 32)]);
             wordLang_Assign 31 (wordLang_Op asm_Or [ShiftVar Lsl 11
               (64 - n);
                              ShiftVar Lsr 13 (n - 32)])])) else
       if n < 32 then
         (match sh with Lsl -> [wordLang_Assign 33 (ShiftVar sh 13
           n);
                    wordLang_Assign 31 (wordLang_Op asm_Or [ShiftVar
                      Lsr 13 (32 - n);
                              ShiftVar sh 11 n])] | Lsr ->
                                [wordLang_Assign 33 (wordLang_Op asm_Or
                                [ShiftVar Lsl 11 (32 - n);
                              ShiftVar sh 13 n]);
                    wordLang_Assign 31 (ShiftVar sh 11 n)] | Asr ->
                      [wordLang_Assign 33 (wordLang_Op asm_Or [ShiftVar
                      Lsl 11 (32 - n);
                              ShiftVar Lsr 13 n]);
                    wordLang_Assign 31 (ShiftVar sh 11 n)] | Ror ->
                      []) else
         (match sh with Lsl -> [wordLang_Assign 33 (wordLang_Const
           (n2w 0)); wordLang_Assign 31 (ShiftVar sh 13 (n - 32))] | Lsr
           -> [wordLang_Assign 33 (ShiftVar sh 11 (n - 32));
           wordLang_Assign 31 (wordLang_Const (n2w 0))] | Asr ->
           [wordLang_Assign 33 (ShiftVar sh 11 (n - 32));
                    wordLang_Assign 31 (ShiftVar sh 11 32)] | Ror
                      -> []))`;;

let smallnum_def = new_definition
  `Smallnum i =
     (if i < (&0) then (n2w 0) - n2w (num_of_int ((&4) * ((&0) -
       i))) else n2w (num_of_int ((&4) * i)))`;;

(* HOL4 data_to_wordScript.sml:1099: the overload FALSE_CONST, which
   the port expands *)
(* HOL4 data_to_wordScript.sml:1100: the overload TRUE_CONST, which
   the port expands *)

let MemEqList_def,MemEqList_ind = define_rec
  [`MemEqList a [] = (wordLang_Assign 1 (wordLang_Const (n2w 18:'a
    word)):'a wordLang_prog)`;
   `MemEqList a (CONS w ws) =
         ((wordLang_Seq (wordLang_Assign 5 (wordLang_Load
             (wordLang_Op asm_Add [wordLang_Var 3; wordLang_Const a])))
             (wordLang_If asm_Equal 5 (Imm w) (MemEqList (a +
                 bytes_in_word) ws) wordLang_Skip)):'a
                 wordLang_prog)`];;

let get_gen_size_def = define_cases
  [`get_gen_size [] = bytes_in_word * ((--(n2w 1)):'a word)`;
   `get_gen_size (CONS x xs) =
         (if w2n (bytes_in_word:'a word) * x < dimword (:'a)
             then bytes_in_word * n2w x else bytes_in_word *
             (--(n2w 1)))`];;

let fp_cmp_inst_def = define_cases
  [`fp_cmp_inst FP_Less = FPLess 3 0 1`;
   `fp_cmp_inst FP_LessEqual = FPLessEqual 3 0 1`;
   `fp_cmp_inst FP_Greater = FPLess 3 1 0`;
   `fp_cmp_inst FP_GreaterEqual = FPLessEqual 3 1 0`;
   `fp_cmp_inst FP_Equal = FPEqual 3 0 1`];;

let fp_top_inst_def = new_definition
  `fp_top_inst FP_Fma = FPFma 0 1 2`;;

let fp_bop_inst_def = new_definition
  `fp_bop_inst x1 =
      match x1 with
        fpSem_FP_Add -> FPAdd 0 0 1
      | fpSem_FP_Sub -> FPSub 0 0 1
      | fpSem_FP_Mul -> FPMul 0 0 1
      | fpSem_FP_Div -> FPDiv 0 0 1`;;

let fp_uop_inst_def = new_definition
  `fp_uop_inst x1 =
      match x1 with
        fpSem_FP_Neg -> FPNeg 1 0
      | fpSem_FP_Abs -> FPAbs 1 0
      | fpSem_FP_Sqrt -> FPSqrt 1 0`;;

let arg1_def = new_definition
  `data_to_word_arg1 vs f x = (match vs with [v1] -> f v1 | _1 -> x)`;;

let arg2_def = new_definition
  `data_to_word_arg2 vs f x = (match vs with [v1; v2] -> f v1 v2 | _2
  -> x)`;;

let arg3_def = new_definition
  `arg3 vs f x = (match vs with [v1; v2; v3] -> f v1 v2 v3 | _3 -> x)`;;

let arg4_def = new_definition
  `arg4 vs f x = (match vs with [v1; v2; v3; v4] -> f v1 v2 v3 v4 |
  _4 -> x)`;;

let arg2_pmatch = prove
 (`data_to_word_arg2 vs f x = (match vs with [v1; v2] -> f v1 v2 | _5
  -> x)`,
  CHEAT_TAC);;

let arg3_pmatch = prove
 (`arg3 vs f x = (match vs with [v1; v2; v3] -> f v1 v2 v3 | _6 -> x)`,
  CHEAT_TAC);;

let arg4_pmatch = prove
 (`arg4 vs f x = (match vs with [v1; v2; v3; v4] -> f v1 v2 v3 v4 | _7
  -> x)`,
  CHEAT_TAC);;

(* HOL4 data_to_wordScript.sml:1176-1180: ML code, not ported *)

let assign_Const_def = new_definition
  `assign_Const i (l:num) (dest:num) =
         // bvl_to_bvi compilation ensures that all literal
         // constants fit into a machine word
         (if i < (&0) then (wordLang_Assign (adjust_var dest)
           (wordLang_Const ((n2w 0) - n2w (num_of_int ((&4) * ((&0) -
           i))))),l) else (wordLang_Assign (adjust_var dest)
           (wordLang_Const (n2w (num_of_int ((&4) * i)))),l):'a
           wordLang_prog#num)`;;

let assign_SetGlobalsPtr_def = new_definition
  `assign_SetGlobalsPtr (c:data_to_word_config) (l:num) (dest:num) v1 =
       ((wordLang_Seq (wordLang_Set Globals (wordLang_Var (adjust_var
         v1)))
       (wordLang_Seq (wordLang_Set GlobReal (real_addr c (adjust_var
         v1)))
            (wordLang_Assign (adjust_var dest)
              data_to_word_Unit)),l):'a wordLang_prog#num)`;;

let assign_Global_def = new_definition
  `assign_Global (c:data_to_word_config) n (l:num) (dest:num) =
       ((wordLang_Assign (adjust_var dest) (wordLang_Load
         (wordLang_Op asm_Add [wordLang_Lookup GlobReal;
                              wordLang_Const (bytes_in_word * n2w
                                (n + 1))])),l):'a wordLang_prog#num)`;;

let assign_SetGlobal_def = new_definition
  `assign_SetGlobal (c:data_to_word_config) n (l:num) (dest:num) v1 =
       ((wordLang_Seq (wordLang_Store (wordLang_Op asm_Add
         [wordLang_Lookup GlobReal; wordLang_Const (bytes_in_word * n2w
         (n + 1))])
                   (adjust_var v1))
            (wordLang_Assign (adjust_var dest)
              data_to_word_Unit),l):'a wordLang_prog#num)`;;

let assign_El_def = new_definition
  `assign_El (c:data_to_word_config) (l:num) (dest:num) v1 v2 =
                          ((wordLang_Assign (adjust_var dest)
                             (wordLang_Load (wordLang_Op asm_Add
                               [real_addr c (adjust_var v1);
                              real_offset c (adjust_var
                                v2)])),l):'a wordLang_prog#num)`;;

let assign_ElemAt_def = new_definition
  `assign_ElemAt (c:data_to_word_config) n (l:num) (dest:num) v1 =
                          ((wordLang_Assign (adjust_var dest)
                             (wordLang_Load (wordLang_Op asm_Add
                               [real_addr c (adjust_var v1);
                              wordLang_Const (bytes_in_word +
                              bytes_in_word * n2w n)])),l):'a
                                wordLang_prog#num)`;;

let assign_DerefByte_def = new_definition
  `assign_DerefByte (c:data_to_word_config) (l:num) (dest:num) v1 v2 =
          ((data_to_word_list_Seq [
             wordLang_Assign 1 (wordLang_Op asm_Add [real_addr c
               (adjust_var v1);
                              real_byte_offset (adjust_var v2)]);
             wordLang_Inst (asm_Mem asm_Load8 3 (Addr 1 (n2w 0)));
             wordLang_Assign (adjust_var dest) ((\sh e n.
               wordLang_Shift sh e (wordLang_Const (n2w n))) Lsl
               (wordLang_Var 3) 2)],l):'a wordLang_prog#num)`;;

let assign_Update_def = new_definition
  `assign_Update (c:data_to_word_config) (l:num) (dest:num) v1 v2 v3 =
                  ((wordLang_Seq (wordLang_Store (wordLang_Op asm_Add
                    [real_addr c (adjust_var v1);
                              real_offset c (adjust_var v2)])
                              (adjust_var v3))
                       (wordLang_Assign (adjust_var dest)
                         data_to_word_Unit),l):'a wordLang_prog#num)`;;

let assign_UpdateThunk_def = new_definition
  `assign_UpdateThunk ev (c:data_to_word_config) (l:num) (dest:num) v1
  v2 =
       ((match ev with NotEvaluated ->
            (wordLang_Seq (wordLang_Store (wordLang_Op asm_Add
              [real_addr c (adjust_var v1);
                              wordLang_Const bytes_in_word])
                        (adjust_var v2))
                 (wordLang_Assign (adjust_var dest)
                   data_to_word_Unit),l) | Evaluated ->
            (match encode_header c (8 + 6) 1 with NONE -> (GiveUp,l)
              | SOME (header:'a word) -> (data_to_word_list_Seq
                 [wordLang_Assign 1 (real_addr c (adjust_var v1));
                  wordLang_Assign 3 (wordLang_Const header);
                  wordLang_Store (wordLang_Var 1) 3;
                  wordLang_Store (wordLang_Op asm_Add [wordLang_Var
                    1; wordLang_Const bytes_in_word]) (adjust_var v2);
                  wordLang_Assign (adjust_var dest)
                    data_to_word_Unit],l))):'a wordLang_prog#num)`;;

let assign_UpdateByte_def = new_definition
  `assign_UpdateByte (c:data_to_word_config) (l:num) (dest:num) v1 v2 v3
  =
       ((data_to_word_list_Seq [
           wordLang_Assign 1 (wordLang_Op asm_Add [real_addr c
             (adjust_var v1);
                             real_byte_offset (adjust_var v2)]);
           wordLang_Assign 3 ((\sh e n. wordLang_Shift sh e
             (wordLang_Const (n2w n))) Lsr (wordLang_Var (adjust_var
             v3)) 2);
           wordLang_Inst (asm_Mem asm_Store8 3 (Addr 1 (n2w 0)));
           wordLang_Assign (adjust_var dest)
             data_to_word_Unit],l):'a wordLang_prog#num)`;;

let assign_ListAppend_def = new_definition
  `assign_ListAppend (c:data_to_word_config) (secn:num) (l:num)
  (dest:num) (names:(1 spt) option) v1 v2 =
          ((match encode_header c 0 2 with NONE -> (GiveUp,l) | SOME
            (header:'a word) ->
            ((wordLang_MustTerminate
              (wordLang_Call (SOME ([adjust_var dest],adjust_sets
                (data_to_word_get_names names),wordLang_Skip,secn,l))
                 (SOME Append_location)
                    [adjust_var v2; adjust_var v1] NONE):'a
                      wordLang_prog),l + 1)):'a wordLang_prog#num)`;;

let assign_Cons_def = new_definition
  `assign_Cons (c:data_to_word_config) (l:num) (dest:num) tag args =
                   (if LENGTH args = 0 then
                     if tag < dimword (:'a) DIV 16 then
                       (wordLang_Assign (adjust_var dest)
                         (wordLang_Const (n2w (16 * tag + 2))),l) else
                         (GiveUp,l) else
                     (
                      // tag is too big to be represented
                      match encode_header c (4 * tag) (LENGTH args)
                        with NONE -> (GiveUp,l) | SOME (header:'a word)
                        -> (data_to_word_list_Seq
                         [wordLang_Assign 1 (wordLang_Lookup
                           NextFree);
                          wordLang_Assign 3 (wordLang_Const header);
                          StoreEach 1 (CONS 3 (MAP adjust_var args))
                            (n2w 0);
                          wordLang_Assign (adjust_var dest)
                            (wordLang_Op asm_Or [(\sh e n.
                              wordLang_Shift sh e (wordLang_Const (n2w
                              n))) Lsl (wordLang_Op asm_Sub
                              [wordLang_Var 1; wordLang_Lookup
                              CurrHeap])
                              (shift_length c -
                                backend_common_word_shift (:'a));
                              wordLang_Const ((n2w 1) ||
                              (word_bits (small_shift_length c - 1)
                                0)
                              (ptr_bits c tag (LENGTH args)))]);
                          wordLang_Set NextFree (wordLang_Op asm_Add
                            [wordLang_Var 1;
                            wordLang_Const (bytes_in_word * n2w
                              (LENGTH args + 1))])],l)):'a
                              wordLang_prog#num)`;;

let assign_MutCons_def = new_definition
  `assign_MutCons (c:data_to_word_config) (l:num) (dest:num) tag args =
     (match data_to_word_config_gc_kind c with
       data_to_word_Generational _8 -> (GiveUp,l) | _9 ->
       (assign_Cons (c:data_to_word_config) (l:num) (dest:num) tag
       args:'a wordLang_prog#num))`;;

let assign_ConfigGC_def = new_definition
  `assign_ConfigGC (c:data_to_word_config) (secn:num) (l:num) (dest:num)
  (names:(1 spt) option) v1 v2 =
              ((data_to_word_list_Seq [SilentFFI c 3 (adjust_sets
                (data_to_word_get_names names));
                         wordLang_Assign 1 (wordLang_Const (n2w 0));
                         wordLang_Alloc 1 (adjust_sets
                           (data_to_word_get_names names));
                         // runs GC
                         SilentFFI c 3 (adjust_sets
                           (data_to_word_get_names names));
                         wordLang_Assign (adjust_var dest)
                           (wordLang_Const (n2w 2))],l):'a
                           wordLang_prog#num)`;;

let getWords_def,getWords_ind = define_rec
  [`getWords [] aux = (REVERSE aux,[])`;
   `getWords (CONS c cs) aux =
      (match c with (b,wordLang_Word w) -> getWords cs (CONS
          (b,w) aux) | _11 -> (REVERSE aux,CONS c cs))`];;

(* the termination relation that HOL4 gives is
     MEASURE (\(r1,r2,r3,vs,v). LENGTH vs)
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 data_to_wordScript.sml:1349-1358: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let StoreAnyConsts_def,StoreAnyConsts_ind = define_guess_cheat
  [`StoreAnyConsts r1 r2 r3 [] v =
      wordLang_Seq (wordLang_Set NextFree (wordLang_Var r2))
          (match SND v with wordLang_Loc n _15 ->
              wordLang_LocValue r1 n | wordLang_Word w ->
              wordLang_Assign r1 (if FST v then wordLang_Op asm_Add
              [wordLang_Const w; wordLang_Var r3] else
              (wordLang_Const w)))`;
   `StoreAnyConsts r1 r2 r3 (CONS v vs) w =
      (match ((SND v):'a word_loc) with wordLang_Loc n _16 ->
          data_to_word_list_Seq [wordLang_LocValue r1 n;
                             wordLang_Store (wordLang_Var r2) r1;
                             wordLang_Assign r2 (wordLang_Op asm_Add
                                 [wordLang_Var r2; wordLang_Const
                                 bytes_in_word]);
                             StoreAnyConsts r1 r2 r3 vs w] | _17 ->
                                 (let (ws,vs1) = getWords (CONS v vs) []
                                 in
               wordLang_Seq (wordLang_StoreConsts r2 r3 r2 r3 ws)
                   (StoreAnyConsts r1 r2 r3 vs1 w)))`];;

let lookup_mem_def = new_definition
  `lookup_mem m a =
     (match sptree_lookup a m with NONE -> (F,wordLang_Word ((n2w
       0):'a word)) | SOME x -> x)`;;

let byte_len_def = new_definition
  `byte_len (:'a) num_bytes =
     (if dimindex (:'a) = 32 then num_bytes DIV 4 + 1 else
       num_bytes DIV 8 + 1)`;;

let make_byte_header_def = new_definition
  `make_byte_header conf cmp_by_contents len =
   (let tag = (if cmp_by_contents then (n2w 0b00111) else (n2w
     0b10111)) in
     (if dimindex (:'a) = 32 then n2w (len + 4) << (dimindex (:'a)
       - 2 - data_to_word_config_len_size conf) || tag else n2w (len
       + 8) << (dimindex (:'a) - 3 - data_to_word_config_len_size
       conf) || tag):'a word)`;;

let get_lowerbits_def = new_definition
  `get_lowerbits conf x2 =
        match x2 with
          wordLang_Word w ->
        (((word_bits (small_shift_length conf - 1) 0) w) || (n2w 1))
        | _18 -> (n2w 1)`;;

let make_cons_ptr_def = new_definition
  `make_cons_ptr conf nf tag len =
     wordLang_Word (
             nf << (shift_length conf - backend_common_word_shift
               (:'a)) || ((n2w 1):'a word) || get_lowerbits conf
               (wordLang_Word (ptr_bits conf tag len)))`;;

let make_ptr_def = new_definition
  `make_ptr conf nf tag len =
     wordLang_Word (nf << (shift_length conf -
       backend_common_word_shift (:'a)) || ((n2w 1):'a word))`;;

let write_bytes_def,write_bytes_ind = define_rec
  [`write_bytes bs [] be' = []`;
   `write_bytes bs (CONS (w:'a word) ws) be' =
         (let k = dimindex (:'a) DIV 8 in
              CONS (bytes_to_word k (n2w 0) bs w be')
                  (write_bytes (DROP k bs) ws be'))`];;

let small_int_def = new_definition
  `small_int (:'a) i <=>
     --(&(dimword (:'a) DIV 8)) <= i /\ i < (&(dimword (:'a) DIV
       8):int)`;;

let part_to_words_def = define_cases
  [`part_to_words c m (closLang_Int i:const_part) (offset:'a word) =
      (if small_int (:'a) i then SOME ((F,wordLang_Word (Smallnum
          i)),[]) else let (sign,ws) = i2mw i in
              match encode_header c (if sign then 7 else 3) (LENGTH
                  ws) with NONE -> NONE | SOME hd -> SOME ((T,(make_ptr
                  c offset ((n2w 0):'a word) (LENGTH ws))),
                              MAP (\w. (F,wordLang_Word w)) (CONS
                                  hd ws)))`;
   `part_to_words c m (closLang_Con t ns) (offset:'a word) =
      (if NULL ns then
         if t < dimword (:'a) DIV 16 then SOME ((F,wordLang_Word
             (n2w (16 * t + 2))),[]) else NONE else
         match encode_header c (4 * t) (LENGTH ns) with NONE -> NONE
             | SOME hd -> SOME ((T,wordLang_Word
                              (offset << (shift_length c -
                                  backend_common_word_shift (:'a)) +
                              (ptr_bits c t (LENGTH ns) || (n2w
                                  1)))),CONS (F,wordLang_Word hd)
                                  (MAP (lookup_mem m) ns)))`;
   `part_to_words c m (closLang_W64 w:const_part) (offset:'a word) =
      (let ws = (if dimindex (:'a) < 64 then [((63 >< 32) w); ((31
          >< 0) w)] else [((63 >< 0) w):'a word]) in
         match encode_header c 3 (LENGTH ws) with NONE -> NONE |
             SOME hd -> SOME ((T,(make_ptr c offset ((n2w 0):'a word)
             (LENGTH ws))),
                            MAP (\w. (F,wordLang_Word w)) (CONS
                                hd ws)))`;
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
                    MAP (\w. (F,wordLang_Word w)) (CONS hd ws))
                        else NONE)`];;

let parts_to_words_def,parts_to_words_ind = define_rec
  [`parts_to_words c m i [] (off:'a word) = SOME (lookup_mem m (i -
    (1:num)),[])`;
   `parts_to_words c m i (CONS x parts') (off:'a word) =
      (match part_to_words c m x off with NONE -> NONE | SOME (w,xs)
          ->
        (match parts_to_words c (sptree_insert i w m) (i + 1) parts'
                 (off + bytes_in_word * n2w (LENGTH xs)) with
                     NONE -> NONE | SOME (r,ys) -> SOME (r,APPEND
                     xs ys)))`];;

let const_parts_to_words_def = new_definition
  `const_parts_to_words c parts' =
     parts_to_words c LN 0 parts' (n2w 0)`;;

let get_Word_def = new_definition
  `get_Word x1 =
      match x1 with
        wordLang_Word w -> w
      | _19 -> (n2w 0)`;;
add_simp get_Word_def;;

let assign_Build_def = new_definition
  `assign_Build (c:data_to_word_config) (secn:num) (l:num) (dest:num)
  (names:(1 spt) option) ps =
     (match const_parts_to_words c ps with NONE -> (GiveUp,l) | SOME
       (w,ws) ->
       ((data_to_word_list_Seq
         [wordLang_Assign 1 (wordLang_Lookup NextFree);
          wordLang_Assign 3 ((\sh e n. wordLang_Shift sh e
            (wordLang_Const (n2w n))) Lsl (wordLang_Op asm_Sub
            [wordLang_Var 1; wordLang_Lookup CurrHeap])
                     (shift_length c - backend_common_word_shift
                       (:'a)));
          StoreAnyConsts (adjust_var dest) 1 3 ws w],l):'a
            wordLang_prog#num))`;;

let assign_ConsExtend_def = new_definition
  `assign_ConsExtend (c:data_to_word_config) (secn:num) (l:num)
  (dest:num) (names:(1 spt) option) tag args =
         ((match args with (CONS old (CONS start' (CONS len (CONS tot
           rest)))) ->
           (match encode_header c (4 * tag) 0 with
              NONE -> (GiveUp,l) | SOME header ->
               (let limit' = MIN (2 EXP data_to_word_config_len_size
                 c) (dimword (:'a) DIV 16) in
               let h = (\sh e n. wordLang_Shift sh e (wordLang_Const
                 (n2w n))) Lsl (wordLang_Var (adjust_var tot))
                         (dimindex (:'a) -
                           data_to_word_config_len_size c - 2) in
                 (data_to_word_list_Seq
                   [BignumHalt (adjust_var tot);
                    wordLang_Assign 1 (wordLang_Var (adjust_var
                      tot));
                    AllocVar c limit' (list_insert args
                      (data_to_word_get_names names));
                    wordLang_Assign 1 (wordLang_Lookup NextFree);
                    wordLang_Assign 5 (wordLang_Op asm_Or [h;
                      wordLang_Const header]);
                    wordLang_Assign 7 ((\sh e n. wordLang_Shift sh e
                      (wordLang_Const (n2w n))) Lsr (wordLang_Var
                      (adjust_var tot)) 2);
                    wordLang_Assign 9 (wordLang_Const (n2w tag));
                    StoreEach 1 (CONS 5 (MAP adjust_var rest)) (n2w
                      0);
                    Make_ptr_bits_code c 9 7 3;
                    wordLang_Set NextFree (wordLang_Op asm_Add
                      [wordLang_Var 1; wordLang_Const bytes_in_word;
                      (\sh e n. wordLang_Shift sh e (wordLang_Const
                        (n2w n))) Lsl (wordLang_Var 7)
                        (backend_common_word_shift (:'a))]);
                    wordLang_Assign 15 (wordLang_Var (adjust_var
                      len));
                    wordLang_Assign 13 (wordLang_Op asm_Add
                      [wordLang_Var 1;
                      wordLang_Const (bytes_in_word * n2w (LENGTH
                        rest + 1))]);
                    wordLang_Assign 11 (wordLang_Op asm_Add
                      [real_addr c (adjust_var old);
                      wordLang_Const bytes_in_word;
                      ShiftVar Lsl (adjust_var start')
                        (backend_common_word_shift (:'a) - 2)]);
                    wordLang_If asm_Test 15 (Reg 15) (wordLang_Assign
                      (adjust_var dest) (wordLang_Var 3))
                      (data_to_word_list_Seq [
                      wordLang_MustTerminate
                        (wordLang_Call (SOME ([adjust_var
                          dest],adjust_sets (data_to_word_get_names
                          names),
                              wordLang_Skip,secn,l))
                           (SOME MemCopy_location) [15; 11; 13; 3]
                             NONE)])]),l + 1)) | _20 ->
                             (wordLang_Skip,l)):'a wordLang_prog#num)`;;

let assign_Ref_def = new_definition
  `assign_Ref (c:data_to_word_config) (secn:num) (l:num) (dest:num)
  (names:(1 spt) option) args =
           ((match encode_header c 2 (LENGTH args) with NONE ->
             (GiveUp,l) | SOME (header:'a word) ->
             (data_to_word_list_Seq
                  [wordLang_Set TriggerGC (wordLang_Op asm_Sub
                    [wordLang_Lookup TriggerGC;
                      wordLang_Const (bytes_in_word * n2w (LENGTH
                        args + 1))]);
                   wordLang_Assign 1 (wordLang_Op asm_Sub
                     [wordLang_Lookup EndOfHeap;
                      wordLang_Const (bytes_in_word * n2w (LENGTH
                        args + 1))]);
                   wordLang_Set EndOfHeap (wordLang_Var 1);
                   wordLang_Assign 3 (wordLang_Const header);
                   StoreEach 1 (CONS 3 (MAP adjust_var args)) (n2w
                     0);
                   wordLang_Assign (adjust_var dest)
                     (wordLang_Op asm_Or [(\sh e n. wordLang_Shift sh
                       e (wordLang_Const (n2w n))) Lsl (wordLang_Op
                       asm_Sub [wordLang_Var 1; wordLang_Lookup
                       CurrHeap])
                              (shift_length c -
                                backend_common_word_shift (:'a));
                             wordLang_Const (n2w 1)])],l)):'a
                               wordLang_prog#num)`;;

let assign_AllocThunk_def = new_definition
  `assign_AllocThunk (ev:thunk_mode) (c:data_to_word_config) (secn:num)
  (l:num) (dest:num) (names:(1 spt) option) arg =
           ((let tag = (match ev with Evaluated -> 8 + 6 |
             NotEvaluated -> 0 + 6) in
            match encode_header c tag 1 with NONE -> (GiveUp,l) |
              SOME (header:'a word) -> (data_to_word_list_Seq
                  [wordLang_Set TriggerGC (wordLang_Op asm_Sub
                    [wordLang_Lookup TriggerGC;
                      wordLang_Const (bytes_in_word * (n2w 2))]);
                   wordLang_Assign 1 (wordLang_Op asm_Sub
                     [wordLang_Lookup EndOfHeap;
                      wordLang_Const (bytes_in_word * (n2w 2))]);
                   wordLang_Set EndOfHeap (wordLang_Var 1);
                   wordLang_Assign 3 (wordLang_Const header);
                   StoreEach 1 [3; adjust_var arg] (n2w 0);
                   wordLang_Assign (adjust_var dest)
                     (wordLang_Op asm_Or [(\sh e n. wordLang_Shift sh
                       e (wordLang_Const (n2w n))) Lsl (wordLang_Op
                       asm_Sub [wordLang_Var 1; wordLang_Lookup
                       CurrHeap])
                              (shift_length c -
                                backend_common_word_shift (:'a));
                             wordLang_Const (n2w 1)])],l)):'a
                               wordLang_prog#num)`;;

let assign_RefByte_def = new_definition
  `assign_RefByte (c:data_to_word_config) (secn:num) (l:num) (dest:num)
  (names:(1 spt) option) immutable v1 v2 =
          ((wordLang_Seq
            (wordLang_Assign 1 (wordLang_Const (if immutable then
              (n2w 0) else (n2w 16))))
            (
             // n.b. this would have been better done with Set Temp
             wordLang_MustTerminate
              (wordLang_Call (SOME ([adjust_var dest],adjust_sets
                (data_to_word_get_names names),wordLang_Skip,secn,l))
                 (SOME RefByte_location)
                    [adjust_var v1; adjust_var v2; 1] NONE):'a
                      wordLang_prog),l + 1):'a wordLang_prog#num)`;;

let assign_XorByte_def = new_definition
  `assign_XorByte (c:data_to_word_config) (secn:num) (l:num) (dest:num)
  (names:(1 spt) option) v1 v2 =
     ((data_to_word_list_Seq [
         wordLang_Assign 1 (real_addr c (adjust_var v1));
         wordLang_Assign 3 (real_addr c (adjust_var v2));
         wordLang_Assign 5 (SmallLsr (wordLang_Load (wordLang_Var 3))
           (dimindex (:'a) - data_to_word_config_len_size c));
         wordLang_Assign 1 (wordLang_Op asm_Add [wordLang_Var 1;
           wordLang_Const bytes_in_word]);
         wordLang_Assign 3 (wordLang_Op asm_Add [wordLang_Var 3;
           wordLang_Const (bytes_in_word:'a word)]);
         wordLang_MustTerminate
           (wordLang_Call
             (SOME ([adjust_var dest],adjust_sets
               (data_to_word_get_names names),wordLang_Skip,secn,l))
             (SOME XorLoop_location) [1; 3; 5] NONE)],l + 1):'a
               wordLang_prog#num)`;;

let SetBool_def = new_definition
  `SetBool dest cmp r ri =
   (wordLang_If cmp r ri
      (wordLang_Assign dest (wordLang_Const (n2w 18:'a word)))
      (wordLang_Assign dest (wordLang_Const (n2w 2:'a word))):'a
        wordLang_prog)`;;

let AssignCmp_def = define_cases
  [`AssignCmp dest (ast_Lt:opb) v1 v2 = (SetBool dest asm_Lower v1
    (Reg v2):'a wordLang_prog)`;
   `AssignCmp dest (ast_Gt:opb) v1 v2 = ((SetBool dest asm_Lower v2
    (Reg v1)):'a wordLang_prog)`;
   `AssignCmp dest (ast_Leq:opb) v1 v2 = ((SetBool dest asm_NotLower
    v2 (Reg v1)):'a wordLang_prog)`;
   `AssignCmp dest (ast_Geq:opb) v1 v2 = ((SetBool dest
    asm_NotLower v1 (Reg v2)):'a wordLang_prog)`];;

let assign_StringCmp_def = new_definition
  `assign_StringCmp (c:data_to_word_config) (secn:num) (l:num)
  (dest:num) (names:(1 spt) option) (b:bool) (cmp:opb) v1 v2 =
     ((let k = (dimindex (:'a) - data_to_word_config_len_size c -
       backend_common_word_shift (:'a)) in
       data_to_word_list_Seq [
           wordLang_Assign 1 (real_addr c (adjust_var v1));
           // address to header
           wordLang_Assign 3 (real_addr c (adjust_var v2));
           // address to header
           wordLang_Assign 5 ((\sh e n. wordLang_Shift sh e
             (wordLang_Const (n2w n))) Lsr (wordLang_Load (wordLang_Var
             1)) k);
           // len + bytes_in_word
           wordLang_Assign 7 ((\sh e n. wordLang_Shift sh e
             (wordLang_Const (n2w n))) Lsr (wordLang_Load (wordLang_Var
             3)) k);
           (
            // len + bytes_in_word
            if b then
              wordLang_If asm_Equal 5 (Reg 7)
                 (data_to_word_list_Seq
                  [wordLang_Assign 11 (wordLang_Op asm_Add
                    [wordLang_Var 1; wordLang_Const bytes_in_word]);
                   wordLang_Assign 13 (wordLang_Op asm_Add
                     [wordLang_Var 3; wordLang_Const bytes_in_word]);
                   wordLang_MustTerminate
                   (wordLang_Call (SOME ([5; 7],adjust_sets
                     (data_to_word_get_names
                     names),wordLang_Skip,secn,l))
                         (SOME StringCmpLoop_location) [11; 13; 7; 7;
                           7] NONE)])
                 wordLang_Skip else
              data_to_word_list_Seq
              [wordLang_Assign 11 (wordLang_Op asm_Add [wordLang_Var
                1; wordLang_Const bytes_in_word]);
               wordLang_Assign 13 (wordLang_Op asm_Add [wordLang_Var
                 3; wordLang_Const bytes_in_word]);
               wordLang_Assign 9 (wordLang_Var 5);
               wordLang_If asm_Lower 7 (Reg 5) (wordLang_Assign 9
                 (wordLang_Var 7)) wordLang_Skip;
               wordLang_MustTerminate
               (wordLang_Call (SOME ([5; 7],adjust_sets
                 (data_to_word_get_names names),wordLang_Skip,secn,l))
                     (SOME StringCmpLoop_location) [11; 13; 9; 5; 7]
                       NONE)]);
           AssignCmp (adjust_var dest) cmp 5 7],l + 1):'a
             wordLang_prog#num)`;;

let assign_CopyByte_def = new_definition
  `assign_CopyByte (c:data_to_word_config) (secn:num) (l:num) (dest:num)
  (names:(1 spt) option) args =
       ((match args with [v1; v2; v3; v4; v5] ->
            (
             // alloc_new is F
             (wordLang_MustTerminate
              (wordLang_Call (SOME ([adjust_var dest],adjust_sets
                (data_to_word_get_names names),wordLang_Skip,secn,l))
                 (SOME ByteCopy_location)
                    [adjust_var v1; adjust_var v2; adjust_var v3;
                     adjust_var v4; adjust_var v5] NONE):'a
                       wordLang_prog),l + 1) | [v1; v2; v3] ->
            (
             // alloc_new is T
             (wordLang_MustTerminate
              (wordLang_Call (SOME ([adjust_var dest],adjust_sets
                (data_to_word_get_names names),wordLang_Skip,secn,l))
                 (SOME ByteCopyNew_location)
                    [adjust_var v1; adjust_var v2;
                     adjust_var v3] NONE):'a wordLang_prog),l + 1)
                       | _21 -> (wordLang_Skip,l)):'a
                       wordLang_prog#num)`;;

let assign_RefArray_def = new_definition
  `assign_RefArray (c:data_to_word_config) (secn:num) (l:num) (dest:num)
  (names:(1 spt) option) v1 v2 =
       (let limit' = MIN (2 EXP data_to_word_config_len_size c)
         (dimword (:'a) DIV 16) in
          (data_to_word_list_Seq
           [
           BignumHalt (adjust_var v1);
           wordLang_Move 0 [(1,adjust_var v1)];
           AllocVar c limit' (list_insert [v1; v2]
             (data_to_word_get_names names));
           wordLang_MustTerminate
             (wordLang_Call (SOME ([adjust_var dest],adjust_sets
               (data_to_word_get_names names),wordLang_Skip,secn,l))
                (SOME RefArray_location)
                   [adjust_var v1; adjust_var v2] NONE):'a
                     wordLang_prog],l + 1):'a wordLang_prog#num)`;;

let assign_FromList_def = new_definition
  `assign_FromList (c:data_to_word_config) (secn:num) (l:num) (dest:num)
  (names:(1 spt) option) tag v1 v2 =
        (if encode_header c (4 * tag) 0 = (NONE:('a word) option)
          then (GiveUp,l) else
          (wordLang_MustTerminate (data_to_word_list_Seq [
             wordLang_Assign 1 (wordLang_Const (n2w (16 * tag)));
             (wordLang_Call (SOME ([adjust_var dest],adjust_sets
               (data_to_word_get_names names),wordLang_Skip,secn,l))
                (SOME FromList_location)
                   [adjust_var v1; adjust_var v2; 1] NONE):'a
                     wordLang_prog]),l + 1):'a wordLang_prog#num)`;;

let assign_LessConstSmall_def = new_definition
  `assign_LessConstSmall (l:num) (dest:num) i v1 =
                  ((wordLang_If asm_Less (adjust_var v1) (Imm (n2w (4
                    * i)))
                     (wordLang_Assign (adjust_var dest)
                       (wordLang_Const (n2w 18:'a word)))
                     (wordLang_Assign (adjust_var dest)
                       (wordLang_Const (n2w 2:'a word))),l):'a
                       wordLang_prog#num)`;;

let assign_BoolTest_def = new_definition
  `assign_BoolTest (l:num) (dest:num) (test:test) v1 v2 =
                  ((wordLang_If asm_Equal (adjust_var v1) (Reg
                    (adjust_var v2))
                    (wordLang_Assign (adjust_var dest)
                      (wordLang_Const (n2w 18:'a word)))
                    (wordLang_Assign (adjust_var dest)
                      (wordLang_Const (n2w 2:'a word))),l):'a
                      wordLang_prog#num)`;;

let assign_BoolNot_def = new_definition
  `assign_BoolNot (l:num) (dest:num) v1 =
                  ((wordLang_Assign (adjust_var dest)
                     (wordLang_Op asm_Xor [wordLang_Var
                       (adjust_var v1); wordLang_Const (n2w
                       16)]),l):'a wordLang_prog#num)`;;

let assign_WordTest_def = new_definition
  `assign_WordTest (l:num) (dest:num) (test:test) v1 v2 =
        (((match test with ast_Equal -> wordLang_If asm_Equal
          (adjust_var v1) (Reg (adjust_var v2))
                              (wordLang_Assign (adjust_var dest)
                                (wordLang_Const (n2w 18:'a word)))
                              (wordLang_Assign (adjust_var dest)
                                (wordLang_Const (n2w 2:'a word))) |
                                ast_Compare ast_Lt -> wordLang_If
                                asm_Lower (adjust_var v1) (Reg
                                (adjust_var v2))
                              (wordLang_Assign (adjust_var dest)
                                (wordLang_Const (n2w 18:'a word)))
                              (wordLang_Assign (adjust_var dest)
                                (wordLang_Const (n2w 2:'a word))) |
                                ast_Compare ast_Leq -> wordLang_If
                                asm_NotLower (adjust_var v2) (Reg
                                (adjust_var v1))
                              (wordLang_Assign (adjust_var dest)
                                (wordLang_Const (n2w 18:'a word)))
                              (wordLang_Assign (adjust_var dest)
                                (wordLang_Const (n2w 2:'a word))) |
                                _22 -> wordLang_Skip),l):'a
                                wordLang_prog#num)`;;

let assign_BoundsCheckByte_def = new_definition
  `assign_BoundsCheckByte (c:data_to_word_config) (secn:num) (l:num)
  (dest:num) (names:(1 spt) option) leq v1 v2 =
                    ((data_to_word_list_Seq [wordLang_Assign 1
                              (let addr' = real_addr c (adjust_var
                                v1) in
                              let header = wordLang_Load addr' in
                              let extra = (if dimindex (:'a) = 32
                                then 2 else 3) in
                              let k = dimindex (:'a) -
                                data_to_word_config_len_size c - extra
                                in
                              wordLang_Op asm_Sub [(\sh e n.
                                wordLang_Shift sh e (wordLang_Const (n2w
                                n))) Lsr header k; wordLang_Const
                                bytes_in_word]);
                              wordLang_Assign 3 (ShiftVar Ror
                                (adjust_var v2) 2);
                              (if leq then dataLang_If asm_NotLower 1
                                (Reg 3) else
                              dataLang_If asm_Lower 3 (Reg 1))
                              (wordLang_Assign (adjust_var dest)
                                (wordLang_Const (n2w 18:'a word)))
                              (wordLang_Assign (adjust_var dest)
                                (wordLang_Const (n2w 2:'a
                                word)))],l):'a wordLang_prog#num)`;;

let assign_BoundsCheckArray_def = new_definition
  `assign_BoundsCheckArray (c:data_to_word_config) (secn:num) (l:num)
  (dest:num) (names:(1 spt) option) v1 v2 =
                    ((data_to_word_list_Seq [wordLang_Assign 1
                              (let addr' = real_addr c (adjust_var
                                v1) in
                              let header = wordLang_Load addr' in
                              let k = dimindex (:'a) -
                                data_to_word_config_len_size c in
                              (\sh e n. wordLang_Shift sh e
                                (wordLang_Const (n2w n))) Lsr header k);
                              wordLang_Assign 3 (ShiftVar Ror
                                (adjust_var v2) 2);
                              wordLang_If asm_Lower 3 (Reg 1)
                              (wordLang_Assign (adjust_var dest)
                                (wordLang_Const (n2w 18:'a word)))
                              (wordLang_Assign (adjust_var dest)
                                (wordLang_Const (n2w 2:'a
                                word)))],l):'a wordLang_prog#num)`;;

let assign_BoundsCheckBlock_def = new_definition
  `assign_BoundsCheckBlock (c:data_to_word_config) (secn:num) (l:num)
  (dest:num) (names:(1 spt) option) v1 v2 =
                    ((data_to_word_list_Seq [wordLang_If asm_Test
                      (adjust_var v1) (Imm (n2w 1))
                              (wordLang_Assign 1 (wordLang_Const (n2w
                                0)))
                              (wordLang_Assign 1
                              (let addr' = real_addr c (adjust_var
                                v1) in
                              let header = wordLang_Load addr' in
                              let k = dimindex (:'a) -
                                data_to_word_config_len_size c in
                              (\sh e n. wordLang_Shift sh e
                                (wordLang_Const (n2w n))) Lsr header
                                k));
                              wordLang_Assign 3 (ShiftVar Ror
                                (adjust_var v2) 2);
                              wordLang_If asm_Lower 3 (Reg 1)
                              (wordLang_Assign (adjust_var dest)
                                (wordLang_Const (n2w 18:'a word)))
                              (wordLang_Assign (adjust_var dest)
                                (wordLang_Const (n2w 2:'a
                                word)))],l):'a wordLang_prog#num)`;;

let assign_Equal_def = new_definition
  `assign_Equal (c:data_to_word_config) (secn:num) (l:num) (dest:num)
  (names:(1 spt) option) v1 v2 =
         ((data_to_word_list_Seq [wordLang_Assign 1 (wordLang_Var
           (adjust_var v1));
                    wordLang_Assign 3 (wordLang_Var (adjust_var v2));
                    wordLang_Assign 5 (wordLang_Op asm_And
                      [wordLang_Var 1; wordLang_Var 3]);
                    wordLang_If asm_Test 5 (Imm (n2w 1))
                      wordLang_Skip
                      (wordLang_If asm_Equal 1 (Reg 3) wordLang_Skip
                        (wordLang_Seq (wordLang_MustTerminate
                           (wordLang_Call (SOME ([1],adjust_sets
                             (data_to_word_get_names
                             names),wordLang_Skip,secn,l))
                              (SOME Equal_location) [1; 3] NONE))
                           (wordLang_Assign 3 (wordLang_Const (n2w
                             1)))));
                    (wordLang_If asm_Equal 1 (Reg 3)
                       (wordLang_Assign (adjust_var dest)
                         (wordLang_Const (n2w 18:'a word)))
                       (wordLang_Assign (adjust_var dest)
                         (wordLang_Const (n2w 2:'a word))))],l +
                         1):'a wordLang_prog#num)`;;

let assign_Less_def = new_definition
  `assign_Less (c:data_to_word_config) (secn:num) (l:num) (dest:num)
  (names:(1 spt) option) v1 v2 =
         ((data_to_word_list_Seq [wordLang_Assign 1 (wordLang_Var
           (adjust_var v1));
                    wordLang_Assign 3 (wordLang_Var (adjust_var v2));
                    wordLang_Assign 5 (wordLang_Op asm_Or
                      [wordLang_Var 1; wordLang_Var 3]);
                    wordLang_If asm_Test 5 (Imm (n2w 1))
                      wordLang_Skip
                      (wordLang_Seq (wordLang_MustTerminate
                           (wordLang_Call (SOME ([1],adjust_sets
                             (data_to_word_get_names
                             names),wordLang_Skip,secn,l))
                              (SOME Compare_location) [1; 3] NONE))
                           (wordLang_Assign 3 (wordLang_Const (n2w
                             1))));
                    (wordLang_If asm_Less 1 (Reg 3)
                       (wordLang_Assign (adjust_var dest)
                         (wordLang_Const (n2w 18:'a word)))
                       (wordLang_Assign (adjust_var dest)
                         (wordLang_Const (n2w 2:'a word))))],l +
                         1):'a wordLang_prog#num)`;;

let assign_LessEq_def = new_definition
  `assign_LessEq (c:data_to_word_config) (secn:num) (l:num) (dest:num)
  (names:(1 spt) option) v1 v2 =
         ((data_to_word_list_Seq [wordLang_Assign 1 (wordLang_Var
           (adjust_var v1));
                    wordLang_Assign 3 (wordLang_Var (adjust_var v2));
                    wordLang_Assign 5 (wordLang_Op asm_Or
                      [wordLang_Var 1; wordLang_Var 3]);
                    wordLang_If asm_Test 5 (Imm (n2w 1))
                      wordLang_Skip
                      (wordLang_Seq (wordLang_MustTerminate
                           (wordLang_Call (SOME ([1],adjust_sets
                             (data_to_word_get_names
                             names),wordLang_Skip,secn,l))
                              (SOME Compare_location) [1; 3] NONE))
                           (wordLang_Assign 3 (wordLang_Const (n2w
                             1))));
                    (wordLang_If asm_NotLess 3 (Reg 1)
                       (wordLang_Assign (adjust_var dest)
                         (wordLang_Const (n2w 18:'a word)))
                       (wordLang_Assign (adjust_var dest)
                         (wordLang_Const (n2w 2:'a word))))],l +
                         1):'a wordLang_prog#num)`;;

let assign_LengthBlock_def = new_definition
  `assign_LengthBlock (c:data_to_word_config) (secn:num) (l:num)
  (dest:num) (names:(1 spt) option) v1 =
                         ((wordLang_If asm_Test (adjust_var v1) (Imm
                           (n2w 1))
                            (wordLang_Assign (adjust_var dest)
                              (wordLang_Const (n2w 0)))
                            (wordLang_Assign (adjust_var dest)
                              (let addr' = real_addr c (adjust_var
                                v1) in
                              let header = wordLang_Load addr' in
                              let k = dimindex (:'a) -
                                data_to_word_config_len_size c in
                              let len = (\sh e n. wordLang_Shift sh e
                                (wordLang_Const (n2w n))) Lsr header k
                                in
                              ((\sh e n. wordLang_Shift sh e
                                (wordLang_Const (n2w n))) Lsl len
                                2))),l):'a wordLang_prog#num)`;;

let assign_Length_def = new_definition
  `assign_Length (c:data_to_word_config) (secn:num) (l:num) (dest:num)
  (names:(1 spt) option) v1 =
                           ((wordLang_Assign (adjust_var dest)
                              (let addr' = real_addr c (adjust_var
                                v1) in
                              let header = wordLang_Load addr' in
                              let k = dimindex (:'a) -
                                data_to_word_config_len_size c in
                              let len = (\sh e n. wordLang_Shift sh e
                                (wordLang_Const (n2w n))) Lsr header k
                                in
                              ((\sh e n. wordLang_Shift sh e
                                (wordLang_Const (n2w n))) Lsl len
                                2)),l):'a wordLang_prog#num)`;;

let assign_LengthByte_def = new_definition
  `assign_LengthByte (c:data_to_word_config) (secn:num) (l:num)
  (dest:num) (names:(1 spt) option) v1 =
             ((wordLang_Assign (adjust_var dest)
                (let addr' = real_addr c (adjust_var v1) in
                 let header = wordLang_Load addr' in
                 let k = dimindex (:'a) - backend_common_word_shift
                   (:'a) - data_to_word_config_len_size c in
                 let fakelen = (\sh e n. wordLang_Shift sh e
                   (wordLang_Const (n2w n))) Lsr header k in
                 let len = wordLang_Op asm_Sub [fakelen;
                   wordLang_Const bytes_in_word] in
                   ((\sh e n. wordLang_Shift sh e (wordLang_Const
                     (n2w n))) Lsl len 2)),l):'a wordLang_prog#num)`;;

let assign_TagLenEq_def = new_definition
  `assign_TagLenEq (c:data_to_word_config) (secn:num) (l:num) (dest:num)
  (names:(1 spt) option) tag len v1 =
                         ((if len = 0 then
                            if tag < dimword (:'a) DIV 16 then
                              (wordLang_If asm_Equal (adjust_var v1)
                                (Imm (n2w (16 * tag + 2)))
                              (wordLang_Assign (adjust_var dest)
                                (wordLang_Const (n2w 18:'a word)))
                              (wordLang_Assign (adjust_var dest)
                                (wordLang_Const (n2w 2:'a word))),l)
                                else (wordLang_Assign (adjust_var dest)
                                (wordLang_Const (n2w 2:'a word)),l) else
                                if tag < 2 EXP
                                data_to_word_config_tag_bits c - 1 /\
                              len < 2 EXP
                                data_to_word_config_len_bits c - 1 then
                            (wordLang_Seq
                              (wordLang_Assign 1 (wordLang_Op asm_And
                              [wordLang_Var (adjust_var v1);
                              wordLang_Const (all_ones
                                (data_to_word_config_len_bits c +
                                data_to_word_config_tag_bits c + 1)
                                0)]))
                              (wordLang_If asm_Equal 1 (Imm (ptr_bits
                                c tag len || (n2w 1)))
                              (wordLang_Assign (adjust_var dest)
                                (wordLang_Const (n2w 18:'a word)))
                              (wordLang_Assign (adjust_var dest)
                                (wordLang_Const (n2w 2:'a word)))),l)
                                else
                            match encode_header c (4 * tag) len with
                              NONE -> (wordLang_Assign (adjust_var dest)
                              (wordLang_Const (n2w 2:'a word)),l) | SOME
                              h ->
                              (data_to_word_list_Seq
                              [wordLang_Assign 1 (wordLang_Const (n2w
                                0));
                              wordLang_If asm_Test (adjust_var v1)
                                (Imm (n2w 1)) wordLang_Skip
                              (wordLang_Assign 1 (wordLang_Load
                                (real_addr c (adjust_var v1))));
                              wordLang_If asm_Equal 1 (Imm h)
                              (wordLang_Assign (adjust_var dest)
                                (wordLang_Const (n2w 18:'a word)))
                              (wordLang_Assign (adjust_var dest)
                                (wordLang_Const (n2w 2:'a
                                word)))],l)):'a wordLang_prog#num)`;;

let assign_LenEq_def = new_definition
  `assign_LenEq (c:data_to_word_config) (secn:num) (l:num) (dest:num)
  (names:(1 spt) option) len v1 =
                         ((if len = 0 then
                            (wordLang_If asm_Test (adjust_var v1)
                              (Imm (n2w 1))
                              (wordLang_Assign (adjust_var dest)
                                (wordLang_Const (n2w 18:'a word)))
                              (wordLang_Assign (adjust_var dest)
                                (wordLang_Const (n2w 2:'a word))),l)
                                else if len < 2 EXP
                                data_to_word_config_len_bits c - 1 then
                            (wordLang_Seq
                              (wordLang_Assign 1 (wordLang_Op asm_And
                              [wordLang_Var (adjust_var v1);
                              wordLang_Const (all_ones
                                (data_to_word_config_len_bits c + 1)
                                0)]))
                              (wordLang_If asm_Equal 1 (Imm (ptr_bits
                                c 0 len || (n2w 1)))
                              (wordLang_Assign (adjust_var dest)
                                (wordLang_Const (n2w 18:'a word)))
                              (wordLang_Assign (adjust_var dest)
                                (wordLang_Const (n2w 2:'a word)))),l)
                                else if len < dimword (:'a) then
                            (data_to_word_list_Seq
                              [wordLang_Assign 1 (wordLang_Const (n2w
                                0));
                              wordLang_If asm_Test (adjust_var v1)
                                (Imm (n2w 1)) wordLang_Skip
                              (wordLang_Assign 1
                              (let addr' = real_addr c (adjust_var
                                v1) in
                              let header = wordLang_Load addr' in
                              let k = dimindex (:'a) -
                                data_to_word_config_len_size c in
                              let len = (\sh e n. wordLang_Shift sh e
                                (wordLang_Const (n2w n))) Lsr header k
                                in
                              len));
                              wordLang_If asm_Equal 1 (Imm (n2w len))
                              (wordLang_Assign (adjust_var dest)
                                (wordLang_Const (n2w 18:'a word)))
                              (wordLang_Assign (adjust_var dest)
                                (wordLang_Const (n2w 2:'a word)))],l)
                                else
                            (wordLang_Assign (adjust_var dest)
                              (wordLang_Const (n2w 2:'a word)),l)):'a
                              wordLang_prog#num)`;;

let assign_TagEq_def = new_definition
  `assign_TagEq (c:data_to_word_config) (secn:num) (l:num) (dest:num)
  (names:(1 spt) option) tag v1 =
                ((if tag < dimword (:'a) DIV 16 then
                  (data_to_word_list_Seq
                    [wordLang_Assign 1 (wordLang_Var (adjust_var
                      v1));
                     wordLang_If asm_Test (adjust_var v1) (Imm (n2w
                       1)) wordLang_Skip
                       (wordLang_Assign 1 (let v = adjust_var v1 in
                              let h = wordLang_Load (real_addr c v)
                                in
                              wordLang_Op asm_And [h; wordLang_Const
                                (tag_mask c || (n2w 2))]));
                     wordLang_If asm_Equal 1 (Imm (n2w (16 * tag +
                       2)))
                       (wordLang_Assign (adjust_var dest)
                         (wordLang_Const (n2w 18:'a word)))
                       (wordLang_Assign (adjust_var dest)
                         (wordLang_Const (n2w 2:'a word)))],l) else
                         (wordLang_Assign (adjust_var dest)
                         (wordLang_Const (n2w 2:'a word)),l)):'a
                         wordLang_prog#num)`;;

let assign_Add_def = new_definition
  `assign_Add (c:data_to_word_config) (secn:num) (l:num) (dest:num)
  (names:(1 spt) option) v1 v2 =
         ((data_to_word_list_Seq [
                    // perform addition
                    wordLang_Inst (asm_Arith (asm_AddOverflow 1
                      (adjust_var v1)
                              (adjust_var v2) 3));
                    // or together bits of overflow flag, and the two inputs
                    wordLang_Assign 3 (wordLang_Op asm_Or
                      [wordLang_Var 3; wordLang_Var (adjust_var v1);
                      wordLang_Var (adjust_var v2)]);
                    // if the least significant bit is set, then bignum is needed
                    wordLang_If asm_Test 3 (Imm (n2w 1))
                      wordLang_Skip
                     (wordLang_MustTerminate
                       (wordLang_Call (SOME ([1],adjust_sets
                         (data_to_word_get_names
                         names),wordLang_Skip,secn,l))
                         (SOME Add_location) [adjust_var v1;
                           adjust_var v2] NONE));
                    wordLang_Move 2 [(adjust_var dest,1)]],l +
                      1):'a wordLang_prog#num)`;;

let assign_Sub_def = new_definition
  `assign_Sub (c:data_to_word_config) (secn:num) (l:num) (dest:num)
  (names:(1 spt) option) v1 v2 =
         ((data_to_word_list_Seq [
                    // perform subtraction
                    wordLang_Inst (asm_Arith (asm_SubOverflow 1
                      (adjust_var v1)
                              (adjust_var v2) 3));
                    // or together bits of overflow flag, and the two inputs
                    wordLang_Assign 3 (wordLang_Op asm_Or
                      [wordLang_Var 3; wordLang_Var (adjust_var v1);
                      wordLang_Var (adjust_var v2)]);
                    // if the least significant bit is set, then bignum is needed
                    wordLang_If asm_Test 3 (Imm (n2w 1))
                      wordLang_Skip
                     (wordLang_MustTerminate
                       (wordLang_Call (SOME ([1],adjust_sets
                         (data_to_word_get_names
                         names),wordLang_Skip,secn,l))
                         (SOME Sub_location) [adjust_var v1;
                           adjust_var v2] NONE));
                    wordLang_Move 2 [(adjust_var dest,1)]],l +
                      1):'a wordLang_prog#num)`;;

let assign_Mult_def = new_definition
  `assign_Mult (c:data_to_word_config) (secn:num) (l:num) (dest:num)
  (names:(1 spt) option) v1 v2 =
         ((data_to_word_list_Seq [wordLang_Assign 1 (ShiftVar Lsr
           (adjust_var v1) 1);
                    wordLang_Inst (asm_Arith (asm_LongMul 3 1 1
                      (adjust_var v2)));
                    wordLang_Assign 3 (wordLang_Op asm_Or
                      [wordLang_Var 3;
                              wordLang_Op asm_And [wordLang_Const
                                (n2w 1);
                              wordLang_Op asm_Or [wordLang_Var
                                (adjust_var v1); wordLang_Var
                                (adjust_var v2)]]]);
                    wordLang_Assign 1 (ShiftVar Lsr 1 1);
                    wordLang_If asm_Equal 3 (Imm (n2w 0))
                      wordLang_Skip
                      (wordLang_MustTerminate
                        (wordLang_Call (SOME ([1],adjust_sets
                          (data_to_word_get_names
                          names),wordLang_Skip,secn,l))
                         (SOME Mul_location) [adjust_var v1;
                           adjust_var v2] NONE));
                    wordLang_Move 2 [(adjust_var dest,1)]],l +
                      1):'a wordLang_prog#num)`;;

let assign_Div_def = new_definition
  `assign_Div (c:data_to_word_config) (secn:num) (l:num) (dest:num)
  (names:(1 spt) option) v1 v2 =
         ((data_to_word_list_Seq [
            wordLang_Assign 1 (wordLang_Op asm_Or [wordLang_Var
              (adjust_var v1); wordLang_Var (adjust_var v2)]);
            wordLang_Assign 1 (wordLang_Op asm_Or [wordLang_Var 1;
              ShiftVar Lsr 1 (dimindex (:'a) - 1)]);
            wordLang_If asm_Test 1 (Imm ((n2w 1):'a word))
              (if data_to_word_config_has_div c then
                 data_to_word_list_Seq [wordLang_Inst (asm_Arith
                   (asm_Div 1 (adjust_var v1) (adjust_var v2)));
                           wordLang_Assign (adjust_var dest)
                             (ShiftVar Lsl 1 2)] else if
                             data_to_word_config_has_longdiv c then
                 data_to_word_list_Seq [wordLang_Assign 1
                   (wordLang_Const (n2w 0));
                           wordLang_Inst (asm_Arith (asm_LongDiv 1 3
                             1 (adjust_var v1) (adjust_var v2)));
                           wordLang_Assign (adjust_var dest)
                             (ShiftVar Lsl 1 2)] else
                 data_to_word_list_Seq
                   [wordLang_Assign 1 (wordLang_Const (n2w 0));
                    wordLang_MustTerminate
                     (wordLang_Call (SOME ([1],adjust_sets
                       (data_to_word_get_names
                       names),wordLang_Skip,secn,l + 1))
                       (SOME LongDiv_location)
                         [1; adjust_var v1; adjust_var v2] NONE);
                    wordLang_Assign (adjust_var dest) (ShiftVar Lsl 1
                      2)])
              (data_to_word_list_Seq
                 [wordLang_MustTerminate
                    (wordLang_Call (SOME ([1],adjust_sets
                      (data_to_word_get_names
                      names),wordLang_Skip,secn,l))
                       (SOME Div_location) [adjust_var v1; adjust_var
                         v2] NONE);
                  wordLang_Move 2 [(adjust_var dest,1)]])],l +
                    2):'a wordLang_prog#num)`;;

let assign_Mod_def = new_definition
  `assign_Mod (c:data_to_word_config) (secn:num) (l:num) (dest:num)
  (names:(1 spt) option) v1 v2 =
         ((data_to_word_list_Seq [
            wordLang_Assign 1 (wordLang_Op asm_Or [wordLang_Var
              (adjust_var v1); wordLang_Var (adjust_var v2)]);
            wordLang_Assign 1 (wordLang_Op asm_Or [wordLang_Var 1;
              ShiftVar Lsr 1 (dimindex (:'a) - 1)]);
            wordLang_If asm_Test 1 (Imm ((n2w 1):'a word))
              (if data_to_word_config_has_div c then
                 data_to_word_list_Seq [wordLang_Inst (asm_Arith
                   (asm_Div 1 (adjust_var v1) (adjust_var v2)));
                           wordLang_Inst (asm_Arith (asm_LongMul 3 1
                             1 (adjust_var v2)));
                           wordLang_Assign (adjust_var dest)
                             (wordLang_Op asm_Sub [wordLang_Var
                               (adjust_var v1); wordLang_Var 1])] else
                               if data_to_word_config_has_longdiv c then
                 data_to_word_list_Seq [wordLang_Assign 1
                   (wordLang_Const (n2w 0));
                           wordLang_Inst (asm_Arith (asm_LongDiv 1 3
                             1 (adjust_var v1) (adjust_var v2)));
                           wordLang_Move 2 [(adjust_var dest,3)]]
                             else
                 data_to_word_list_Seq
                   [wordLang_Assign 1 (wordLang_Const (n2w 0));
                    wordLang_MustTerminate
                     (wordLang_Call (SOME ([1],adjust_sets
                       (data_to_word_get_names
                       names),wordLang_Skip,secn,l + 1))
                       (SOME LongDiv_location)
                         [1; adjust_var v1; adjust_var v2] NONE);
                    wordLang_Get (adjust_var dest) (Temp (n2w 28))])
              (data_to_word_list_Seq
                 [wordLang_MustTerminate
                    (wordLang_Call (SOME ([1],adjust_sets
                      (data_to_word_get_names
                      names),wordLang_Skip,secn,l))
                       (SOME Mod_location) [adjust_var v1; adjust_var
                         v2] NONE);
                  wordLang_Move 2 [(adjust_var dest,1)]])],l +
                    2):'a wordLang_prog#num)`;;

let assign_WordOpW8_def = new_definition
  `assign_WordOpW8 opw (c:data_to_word_config) (secn:num) (l:num)
  (dest:num) (names:(1 spt) option) v1 v2 =
            ((wordLang_Assign (adjust_var dest)
             (match lookup_word_op opw with Bitwise op -> wordLang_Op
               op [wordLang_Var (adjust_var v1); wordLang_Var
               (adjust_var v2)] | Carried op -> (let k = dimindex (:'a)
               - 10 in
                (\sh e n. wordLang_Shift sh e (wordLang_Const (n2w
                  n))) Lsr ((\sh e n. wordLang_Shift sh e
                  (wordLang_Const (n2w n))) Lsl
                  (wordLang_Op op [wordLang_Var (adjust_var v1);
                    wordLang_Var (adjust_var v2)]) k) k)),l):'a
                    wordLang_prog#num)`;;

let assign_WordOpW64_def = new_definition
  `assign_WordOpW64 opw (c:data_to_word_config) (secn:num) (l:num)
  (dest:num) (names:(1 spt) option) v1 v2 =
        ((if dimindex (:'a) = 64 then
          (match encode_header c 3 1 with NONE -> (GiveUp,l) | SOME
            (header:'a word) ->
                 (wordLang_Seq (wordLang_Assign 3
                   (wordLang_Op (match opw with
                           backend_common_Andw -> asm_And |
                             backend_common_Orw -> asm_Or | asm_Xor ->
                             asm_Xor | backend_common_Add ->
                             word_bignum_Add | backend_common_Sub ->
                             word_bignum_Sub)
                          [wordLang_Load
                             (wordLang_Op asm_Add
                              [real_addr c (adjust_var v1);
                              wordLang_Const bytes_in_word]);
                           wordLang_Load
                             (wordLang_Op asm_Add
                              [real_addr c (adjust_var v2);
                              wordLang_Const bytes_in_word])]))
                    (WriteWord64 c header dest 3),l)) else
          (match encode_header c 3 2 with NONE -> (GiveUp,l) | SOME
            header ->
             (data_to_word_list_Seq [
                wordLang_Assign 15 (real_addr c (adjust_var v1));
                wordLang_Assign 17 (real_addr c (adjust_var v2));
                wordLang_Assign 11 (wordLang_Load (wordLang_Op
                  asm_Add [wordLang_Var 15; wordLang_Const
                  bytes_in_word]));
                wordLang_Assign 13 (wordLang_Load (wordLang_Op
                  asm_Add [wordLang_Var 15; wordLang_Const ((n2w 2) *
                  bytes_in_word)]));
                wordLang_Assign 21 (wordLang_Load (wordLang_Op
                  asm_Add [wordLang_Var 17; wordLang_Const
                  bytes_in_word]));
                wordLang_Assign 23 (wordLang_Load (wordLang_Op
                  asm_Add [wordLang_Var 17; wordLang_Const ((n2w 2) *
                  bytes_in_word)]));
                WordOp64_on_32 opw;
                WriteWord64_on_32 c header dest 33 31],l))):'a
                  wordLang_prog#num)`;;

let assign_WordShiftW8_def = new_definition
  `assign_WordShiftW8 sh n (c:data_to_word_config) (secn:num) (l:num)
  (dest:num) (names:(1 spt) option) v1 =
         ((wordLang_Assign (adjust_var dest)
            (match sh with Lsl ->
               (\sh e n. wordLang_Shift sh e (wordLang_Const (n2w
                 n))) Lsr
                 ((\sh e n. wordLang_Shift sh e (wordLang_Const (n2w
                   n))) Lsl (wordLang_Var (adjust_var v1)) (dimindex
                   (:'a) - 10 + (MIN n 8)))
                 (dimindex (:'a) - 10) | Lsr ->
               (\sh e n. wordLang_Shift sh e (wordLang_Const (n2w
                 n))) Lsl
                 ((\sh e n. wordLang_Shift sh e (wordLang_Const (n2w
                   n))) Lsr (wordLang_Var (adjust_var v1)) ((MIN n 8) +
                   2)) 2 | Asr ->
               (\sh e n. wordLang_Shift sh e (wordLang_Const (n2w
                 n))) Lsl
                 ((\sh e n. wordLang_Shift sh e (wordLang_Const (n2w
                   n))) Lsr
                    ((\sh e n. wordLang_Shift sh e (wordLang_Const
                      (n2w n))) Asr
                       ((\sh e n. wordLang_Shift sh e (wordLang_Const
                         (n2w n))) Lsl (wordLang_Var (adjust_var v1))
                         (dimindex (:'a) - 10))
                       (MIN n 8))
                    (dimindex (:'a) - 8)) 2 | Ror ->
               (let n = n MOD 8 in
                  wordLang_Op asm_Or
                   [(\sh e n. wordLang_Shift sh e (wordLang_Const
                     (n2w n))) Lsl (ShiftVar Lsr (adjust_var v1) (n +
                     2)) 2;
                    (\sh e n. wordLang_Shift sh e (wordLang_Const
                      (n2w n))) Lsr (ShiftVar Lsl (adjust_var v1)
                      ((dimindex (:'a) - 2) - n)) (dimindex (:'a)
                        - 10)])),l):'a wordLang_prog#num)`;;

let assign_WordShiftW64_def = new_definition
  `assign_WordShiftW64 sh n (c:data_to_word_config) (secn:num) (l:num)
  (dest:num) (names:(1 spt) option) v1 =
          (let len = (if dimindex (:'a) < 64 then 2 else 1) in
          (match encode_header c 3 len with NONE -> (GiveUp,l) | SOME
            (header:'a word) ->
             ((if len = 1 then
                data_to_word_list_Seq
                  [LoadWord64 c 3 (adjust_var v1);
                   wordLang_Assign 3 (ShiftVar sh 3 n);
                   WriteWord64 c header dest 3] else
                data_to_word_list_Seq [
                  wordLang_Assign 15 (real_addr c (adjust_var v1));
                  wordLang_Assign 11 (wordLang_Load (wordLang_Op
                    asm_Add [wordLang_Var 15; wordLang_Const
                    bytes_in_word]));
                  wordLang_Assign 13 (wordLang_Load (wordLang_Op
                    asm_Add [wordLang_Var 15; wordLang_Const ((n2w 2) *
                    bytes_in_word)]));
                  WordShift64_on_32 sh n;
                  WriteWord64_on_32 c header dest 33 31]),l)):'a
                    wordLang_prog#num)`;;

let assign_WordFromWord_def = new_definition
  `assign_WordFromWord b (c:data_to_word_config) (secn:num) (l:num)
  (dest:num) (names:(1 spt) option) v1 =
           (if b then
             (data_to_word_list_Seq [wordLang_Assign 1 (real_addr c
               (adjust_var v1));
                        wordLang_Assign 1 (wordLang_Load (wordLang_Op
                          asm_Add [wordLang_Var 1;
                          wordLang_Const (if dimindex (:'a) = 32 then
                            (n2w 2) * bytes_in_word else
                            bytes_in_word)]));
                        wordLang_Assign 1 (wordLang_Op asm_And
                          [wordLang_Var 1; wordLang_Const (n2w 255)]);
                        wordLang_Assign (adjust_var dest) (ShiftVar
                          Lsl 1 2)],l) else
           (let
              len = (if dimindex (:'a) < 64 then 2 else 1) in
              match encode_header c 3 len with
                NONE -> (GiveUp,l) | SOME header ->
                 (if len = 1 then
                    (data_to_word_list_Seq [wordLang_Assign 3 ((\sh e
                      n. wordLang_Shift sh e (wordLang_Const (n2w n)))
                      Lsr (wordLang_Var (adjust_var v1)) 2);
                              WriteWord64 c header dest 3],l) else
                    (data_to_word_list_Seq [wordLang_Assign 5 ((\sh e
                      n. wordLang_Shift sh e (wordLang_Const (n2w n)))
                      Lsr (wordLang_Var (adjust_var v1)) 2);
                              wordLang_Assign 3 (wordLang_Const (n2w
                                0));
                              WriteWord64_on_32 c header dest 5
                                3],l))):'a wordLang_prog#num)`;;

let assign_WordFromInt_def = new_definition
  `assign_WordFromInt (c:data_to_word_config) (secn:num) (l:num)
  (dest:num) (names:(1 spt) option) v1 =
         (let len = (if dimindex (:'a) < 64 then 2 else 1) in
         (match encode_header c 3 len with NONE -> (GiveUp,l) | SOME
           (header:'a word) ->
            (if len = 1 then
              wordLang_Seq
                (
                 // put the word value into 3
                 wordLang_If asm_Test (adjust_var v1) (Imm (n2w 1))
                     (
                      // smallnum case
                      wordLang_Assign 3 ((\sh e n. wordLang_Shift sh
                        e (wordLang_Const (n2w n))) Asr (wordLang_Var
                        (adjust_var v1)) 2))
                    (
                     // bignum case
                     wordLang_Seq
                      (LoadBignum c 1 3 (adjust_var v1))
                      (wordLang_If asm_Test 1 (Imm (n2w 16))
                        wordLang_Skip
                         (wordLang_Assign 3 (wordLang_Op asm_Sub
                           [wordLang_Const (n2w 0); wordLang_Var 3])))))
                (WriteWord64 c header dest 3) else wordLang_If
                  asm_Test (adjust_var v1) (Imm (n2w 1))
               (data_to_word_list_Seq [
                 wordLang_Assign 3 ((\sh e n. wordLang_Shift sh e
                   (wordLang_Const (n2w n))) Asr (wordLang_Var
                   (adjust_var v1)) 2);
                 wordLang_Assign 5 ((\sh e n. wordLang_Shift sh e
                   (wordLang_Const (n2w n))) Asr (wordLang_Var
                   (adjust_var v1)) 31);
                 WriteWord64_on_32 c header dest 3 5])
               (data_to_word_list_Seq [
                 wordLang_Assign 1 (real_addr c (adjust_var v1));
                 wordLang_Assign 3 (wordLang_Load (wordLang_Var 1));
                 wordLang_Assign 5 (wordLang_Load (wordLang_Op
                   asm_Add [wordLang_Var 1; wordLang_Const
                   bytes_in_word]));
                 wordLang_Assign 7 (ShiftVar Lsr 3 (dimindex (:'a) -
                   data_to_word_config_len_size c));
                 wordLang_If asm_Equal 7 (Imm (n2w 1))
                   (
                    // bignum of length 1
                    wordLang_If asm_Test 3 (Imm (n2w 16))
                     (
                      // positive case
                      wordLang_Seq (wordLang_Assign 9 (wordLang_Const
                        (n2w 0)))
                          (WriteWord64_on_32 c header dest 5 9))
                     (
                      // negative case
                      wordLang_Seq (wordLang_Assign 9 (wordLang_Const
                        (word_not (n2w 0))))
                     (wordLang_Seq (wordLang_Assign 5 (wordLang_Op
                       asm_Sub [wordLang_Const (n2w 0); wordLang_Var
                       5]))
                          (WriteWord64_on_32 c header dest 5 9))))
                   (
                    // longer bignum
                    wordLang_If asm_Test 3 (Imm (n2w 16))
                     (
                      // positive case
                      wordLang_Seq (wordLang_Assign 9 (wordLang_Load
                            (wordLang_Op asm_Add [wordLang_Var 1;
                              wordLang_Const ((n2w 2) *
                              bytes_in_word)])))
                          (WriteWord64_on_32 c header dest 5 9))
                     (
                      // negative case -- messy
                      data_to_word_list_Seq
                       [wordLang_Assign 11 (wordLang_Const (n2w 0));
                        wordLang_Assign 13 (wordLang_Const (n2w 1));
                        wordLang_Assign 9 (wordLang_Load
                          (wordLang_Op asm_Add [wordLang_Var 1;
                            wordLang_Const ((n2w 2) * bytes_in_word)]));
                        wordLang_Assign 5 (wordLang_Op asm_Xor
                          [wordLang_Const (word_not (n2w 0));
                          wordLang_Var 5]);
                        wordLang_Assign 9 (wordLang_Op asm_Xor
                          [wordLang_Const (word_not (n2w 0));
                          wordLang_Var 9]);
                        wordLang_Inst (asm_Arith (asm_AddCarry 15 11
                          5 13));
                        wordLang_Inst (asm_Arith (asm_AddCarry 19 11
                          9 13));
                        WriteWord64_on_32 c header dest 15
                          19]))])),l):'a wordLang_prog#num)`;;

let assign_WordToInt_def = new_definition
  `assign_WordToInt (c:data_to_word_config) (secn:num) (l:num)
  (dest:num) (names:(1 spt) option) v =
         (let len = (if dimindex (:'a) < 64 then 2 else 1) in
         (match encode_header c 3 len with NONE -> (GiveUp,l) | SOME
           header ->
              (if len = 1 then
                (data_to_word_list_Seq [LoadWord64 c 3 (adjust_var
                  v);
                           wordLang_Assign 1 ((\sh e n.
                             wordLang_Shift sh e (wordLang_Const (n2w
                             n))) Lsr (wordLang_Var 3) 61);
                           wordLang_If asm_Equal 1 (Imm (n2w 0))
                             (wordLang_Assign (adjust_var dest) ((\sh
                               e n. wordLang_Shift sh e (wordLang_Const
                               (n2w n))) Lsl (wordLang_Var 3) 2))
                             (WriteWord64 c header dest 3)],l) else
               (match encode_header c 3 1 with NONE -> (GiveUp,l) |
                 SOME header1 ->
                  (data_to_word_list_Seq [
                   wordLang_Assign 15 (real_addr c (adjust_var v));
                   wordLang_Assign 13 (wordLang_Load (wordLang_Op
                     asm_Add [wordLang_Var 15; wordLang_Const
                     bytes_in_word]));
                   wordLang_Assign 11 (wordLang_Load (wordLang_Op
                     asm_Add [wordLang_Var 15; wordLang_Const ((n2w 2) *
                     bytes_in_word)]));
                   wordLang_If asm_NotEqual 13 (Imm (n2w 0))
                     (WriteWord64_on_32 c header dest 13 11)
                     (data_to_word_list_Seq [
                       wordLang_Assign 1 ((\sh e n. wordLang_Shift sh
                         e (wordLang_Const (n2w n))) Lsr (wordLang_Var
                         11) 29);
                       wordLang_If asm_Equal 1 (Imm (n2w 0))
                         (wordLang_Assign (adjust_var dest) ((\sh e
                           n. wordLang_Shift sh e (wordLang_Const (n2w
                           n))) Lsl (wordLang_Var 11) 2))
                         (WriteWord32_on_32 c header1 dest
                           11)])],l)))):'a wordLang_prog#num)`;;

let assign_FFI_def = new_definition
  `assign_FFI ffi_index (c:data_to_word_config) (secn:num) (l:num)
  (dest:num) (names:(1 spt) option) v1 v2 =
       (if ~(data_to_word_config_call_empty_ffi c) /\ ffi_index =
         (implode "") then (wordLang_Assign (adjust_var dest)
         data_to_word_Unit,l) else
         let addr1 = real_addr c (adjust_var v1) in
         let header1 = wordLang_Load addr1 in
         let k = dimindex (:'a) - backend_common_word_shift (:'a) -
           data_to_word_config_len_size c in
         let fakelen1 = (\sh e n. wordLang_Shift sh e (wordLang_Const
           (n2w n))) Lsr header1 k in
         let addr2 = real_addr c (adjust_var v2) in
         let header2 = wordLang_Load addr2 in
         let fakelen2 = (\sh e n. wordLang_Shift sh e (wordLang_Const
           (n2w n))) Lsr header2 k in
         (
         data_to_word_list_Seq [
           wordLang_Assign 1 (wordLang_Op asm_Add [addr1;
             wordLang_Const bytes_in_word]);
           wordLang_Assign 3 (wordLang_Op asm_Sub [fakelen1;
             wordLang_Const bytes_in_word]);
           wordLang_Assign 5 (if ffi_index = (implode "") then
             wordLang_Const (n2w 0) else (wordLang_Op asm_Add [addr2;
             wordLang_Const bytes_in_word]));
           wordLang_Assign 7 (if ffi_index = (implode "") then
             wordLang_Const (n2w 0) else (wordLang_Op asm_Sub [fakelen2;
             wordLang_Const bytes_in_word]));
           wordLang_FFI ffi_index 1 3 5 7 (adjust_sets (match names
             with SOME names -> names | NONE -> LN));
           wordLang_Assign (adjust_var dest)
             data_to_word_Unit],l):'a wordLang_prog#num)`;;

let assign_EqualConst_def = new_definition
  `assign_EqualConst p (c:data_to_word_config) (secn:num) (l:num)
  (dest:num) (names:(1 spt) option) v =
     (match part_to_words c LN p (n2w 0) with SOME ((F,w),_23) ->
         (wordLang_If asm_Equal (adjust_var v) (Imm (get_Word w))
                     (wordLang_Assign (adjust_var dest)
                       (wordLang_Const (n2w 18:'a word)))
                     (wordLang_Assign (adjust_var dest)
                       (wordLang_Const (n2w 2:'a word))),l) | SOME
                       (_24,words) ->
         ((match p with closLang_Int _25 -> wordLang_If asm_Test
           (adjust_var v) (Imm (n2w 1))
                        (wordLang_Assign (adjust_var dest)
                          (wordLang_Const (n2w 2:'a word)))
                        (data_to_word_list_Seq
                           [wordLang_Assign 1 (wordLang_Const (n2w
                             2:'a word));
                            wordLang_Assign 3 (real_addr c
                              (adjust_var v));
                            MemEqList (n2w 0) (MAP (get_Word o SND)
                              words);
                            wordLang_Assign (adjust_var dest)
                              (wordLang_Var 1)]) | closLang_W64 _26 ->
                              (data_to_word_list_Seq
                           [wordLang_Assign 1 (wordLang_Const (n2w
                             2:'a word));
                            wordLang_Assign 3 (wordLang_Op asm_Add
                              [real_addr c (adjust_var v);
                              wordLang_Const bytes_in_word]);
                            MemEqList (n2w 0) (MAP (get_Word o SND)
                              (TL words));
                            wordLang_Assign (adjust_var dest)
                              (wordLang_Var 1)]) | closLang_Str _27 ->
                              (data_to_word_list_Seq
                           [wordLang_Assign 1 (wordLang_Const (n2w
                             2:'a word));
                            wordLang_Assign 3 (real_addr c
                              (adjust_var v));
                            MemEqList (n2w 0) (MAP (get_Word o SND)
                              words);
                            wordLang_Assign (adjust_var dest)
                              (wordLang_Var 1)]) | _28 ->
                              wordLang_Skip),l) | _29 ->
                              ((wordLang_Assign (adjust_var dest)
                              (wordLang_Const (n2w 2:'a word)),l):'a
                              wordLang_prog#num))`;;

let assign_Install_def = new_definition
  `assign_Install (c:data_to_word_config) (secn:num) (l:num) (dest:num)
  (names:(1 spt) option) v1 v2 v3 v4 =
         ((data_to_word_list_Seq [BignumHalt (adjust_var v3);
                    // length must be smallint
                    BignumHalt (adjust_var v4);
                    // length must be smallint
                    wordLang_Assign 1 (wordLang_Lookup BitmapBuffer);
                    wordLang_Assign 3 (wordLang_Op asm_Sub
                      [wordLang_Lookup BitmapBufferEnd; wordLang_Var
                      1]);
                    wordLang_Assign 5 (ShiftVar Lsr (adjust_var v4)
                      2);
                    wordLang_Assign 3 (ShiftVar Lsr 3
                      (backend_common_word_shift (:'a)));
                    wordLang_If asm_Lower 3 (Reg 5)
                            // too little data space
                            GiveUp wordLang_Skip;
                    wordLang_Assign 1 (wordLang_Lookup CodeBuffer);
                    wordLang_Assign 3 (wordLang_Op asm_Sub
                      [wordLang_Lookup CodeBufferEnd; wordLang_Var 1]);
                    wordLang_Assign 5 (ShiftVar Lsr (adjust_var v3)
                      2);
                    wordLang_If asm_Lower 3 (Reg 5)
                            // too little code space
                            GiveUp wordLang_Skip;
                    wordLang_MustTerminate
                     (wordLang_Call (SOME ([adjust_var dest],
                        adjust_sets (data_to_word_get_names
                          names),wordLang_Skip,secn,l))
                     (SOME InstallCode_location)
                       [adjust_var v1; adjust_var v2; 1] NONE)],l
                         + 1):'a wordLang_prog#num)`;;

let assign_FP_cmp_def = new_definition
  `assign_FP_cmp fpc (c:data_to_word_config) (secn:num) (l:num)
  (dest:num) (names:(1 spt) option) v1 v2 =
        ((if ~(data_to_word_config_has_fp_ops c) then (GiveUp,l) else
         if dimindex (:'a) = 64 then
            ((data_to_word_list_Seq [
                wordLang_Assign 3 (wordLang_Load (wordLang_Op asm_Add
                            [real_addr c (adjust_var v1);
                              wordLang_Const bytes_in_word]));
                wordLang_Assign 5 (wordLang_Load (wordLang_Op asm_Add
                            [real_addr c (adjust_var v2);
                              wordLang_Const bytes_in_word]));
                wordLang_Inst (asm_FP (FPMovFromReg 0 3 3));
                wordLang_Inst (asm_FP (FPMovFromReg 1 5 5));
                wordLang_Inst (asm_FP (fp_cmp_inst fpc));
                wordLang_Assign (adjust_var dest) (wordLang_Op
                  asm_Add [ShiftVar Lsl 3 4; wordLang_Const (n2w
                  2)])],l)) else
            ((data_to_word_list_Seq [
                wordLang_Assign 15 (real_addr c (adjust_var v1));
                wordLang_Assign 17 (real_addr c (adjust_var v2));
                wordLang_Assign 11 (wordLang_Load (wordLang_Op
                  asm_Add [wordLang_Var 15; wordLang_Const
                  bytes_in_word]));
                wordLang_Assign 13 (wordLang_Load (wordLang_Op
                  asm_Add [wordLang_Var 15; wordLang_Const ((n2w 2) *
                  bytes_in_word)]));
                wordLang_Assign 21 (wordLang_Load (wordLang_Op
                  asm_Add [wordLang_Var 17; wordLang_Const
                  bytes_in_word]));
                wordLang_Assign 23 (wordLang_Load (wordLang_Op
                  asm_Add [wordLang_Var 17; wordLang_Const ((n2w 2) *
                  bytes_in_word)]));
                wordLang_Inst (asm_FP (FPMovFromReg 0 13 11));
                wordLang_Inst (asm_FP (FPMovFromReg 1 23 21));
                wordLang_Inst (asm_FP (fp_cmp_inst fpc));
                wordLang_Assign (adjust_var dest) (wordLang_Op
                  asm_Add [ShiftVar Lsl 3 4; wordLang_Const (n2w
                  2)])],l))):'a wordLang_prog#num)`;;

let assign_FP_top_def = new_definition
  `assign_FP_top fpt (c:data_to_word_config) (secn:num) (l:num)
  (dest:num) (names:(1 spt) option) v1 v2 v3 =
        ((if ~(data_to_word_config_has_fp_ops c) \/
          ~(data_to_word_config_has_fp_tern c) then (GiveUp,l) else
         if dimindex (:'a) = 64 then
          (match encode_header c 3 1 with NONE -> (GiveUp,l) | SOME
            (header:'a word) ->
             (data_to_word_list_Seq [
                wordLang_Assign 3 (wordLang_Load (wordLang_Op asm_Add
                            [real_addr c (adjust_var v1);
                              wordLang_Const bytes_in_word]));
                wordLang_Assign 5 (wordLang_Load (wordLang_Op asm_Add
                            [real_addr c (adjust_var v2);
                              wordLang_Const bytes_in_word]));
                wordLang_Assign 7 (wordLang_Load (wordLang_Op asm_Add
                            [real_addr c (adjust_var v3);
                              wordLang_Const bytes_in_word]));
                wordLang_Inst (asm_FP (FPMovFromReg 0 3 3));
                wordLang_Inst (asm_FP (FPMovFromReg 1 5 5));
                wordLang_Inst (asm_FP (FPMovFromReg 2 7 7));
                wordLang_Inst (asm_FP (fp_top_inst fpt));
                wordLang_Inst (asm_FP (FPMovToReg 3 5 0));
                WriteWord64 c header dest 3],l)) else
          (match encode_header c 3 2 with NONE -> (GiveUp,l) | SOME
            header ->
             (data_to_word_list_Seq [
                wordLang_Assign 15 (real_addr c (adjust_var v1));
                wordLang_Assign 17 (real_addr c (adjust_var v2));
                wordLang_Assign 19 (real_addr c (adjust_var v3));
                wordLang_Assign 11 (wordLang_Load (wordLang_Op
                  asm_Add [wordLang_Var 15; wordLang_Const
                  bytes_in_word]));
                wordLang_Assign 13 (wordLang_Load (wordLang_Op
                  asm_Add [wordLang_Var 15; wordLang_Const ((n2w 2) *
                  bytes_in_word)]));
                wordLang_Assign 21 (wordLang_Load (wordLang_Op
                  asm_Add [wordLang_Var 17; wordLang_Const
                  bytes_in_word]));
                wordLang_Assign 23 (wordLang_Load (wordLang_Op
                  asm_Add [wordLang_Var 17; wordLang_Const ((n2w 2) *
                  bytes_in_word)]));
                wordLang_Assign 31 (wordLang_Load (wordLang_Op
                  asm_Add [wordLang_Var 19; wordLang_Const
                  bytes_in_word]));
                wordLang_Assign 33 (wordLang_Load (wordLang_Op
                  asm_Add [wordLang_Var 19; wordLang_Const ((n2w 2) *
                  bytes_in_word)]));
                wordLang_Inst (asm_FP (FPMovFromReg 0 13 11));
                wordLang_Inst (asm_FP (FPMovFromReg 1 23 21));
                wordLang_Inst (asm_FP (FPMovFromReg 2 33 31));
                wordLang_Inst (asm_FP (fp_top_inst fpt));
                wordLang_Inst (asm_FP (FPMovToReg 5 3 0));
                WriteWord64_on_32 c header dest 5 3],l))):'a
                  wordLang_prog#num)`;;

let assign_FP_bop_def = new_definition
  `assign_FP_bop fpb (c:data_to_word_config) (secn:num) (l:num)
  (dest:num) (names:(1 spt) option) v1 v2 =
        ((if ~(data_to_word_config_has_fp_ops c) then (GiveUp,l) else
         if dimindex (:'a) = 64 then
          (match encode_header c 3 1 with NONE -> (GiveUp,l) | SOME
            (header:'a word) ->
             (data_to_word_list_Seq [
                wordLang_Assign 3 (wordLang_Load (wordLang_Op asm_Add
                            [real_addr c (adjust_var v1);
                              wordLang_Const bytes_in_word]));
                wordLang_Assign 5 (wordLang_Load (wordLang_Op asm_Add
                            [real_addr c (adjust_var v2);
                              wordLang_Const bytes_in_word]));
                wordLang_Inst (asm_FP (FPMovFromReg 0 3 3));
                wordLang_Inst (asm_FP (FPMovFromReg 1 5 5));
                wordLang_Inst (asm_FP (fp_bop_inst fpb));
                wordLang_Inst (asm_FP (FPMovToReg 3 5 0));
                WriteWord64 c header dest 3],l)) else
          (match encode_header c 3 2 with NONE -> (GiveUp,l) | SOME
            header ->
             (data_to_word_list_Seq [
                wordLang_Assign 15 (real_addr c (adjust_var v1));
                wordLang_Assign 17 (real_addr c (adjust_var v2));
                wordLang_Assign 11 (wordLang_Load (wordLang_Op
                  asm_Add [wordLang_Var 15; wordLang_Const
                  bytes_in_word]));
                wordLang_Assign 13 (wordLang_Load (wordLang_Op
                  asm_Add [wordLang_Var 15; wordLang_Const ((n2w 2) *
                  bytes_in_word)]));
                wordLang_Assign 21 (wordLang_Load (wordLang_Op
                  asm_Add [wordLang_Var 17; wordLang_Const
                  bytes_in_word]));
                wordLang_Assign 23 (wordLang_Load (wordLang_Op
                  asm_Add [wordLang_Var 17; wordLang_Const ((n2w 2) *
                  bytes_in_word)]));
                wordLang_Inst (asm_FP (FPMovFromReg 0 13 11));
                wordLang_Inst (asm_FP (FPMovFromReg 1 23 21));
                wordLang_Inst (asm_FP (fp_bop_inst fpb));
                wordLang_Inst (asm_FP (FPMovToReg 5 3 0));
                WriteWord64_on_32 c header dest 5 3],l))):'a
                  wordLang_prog#num)`;;

let assign_FP_uop_def = new_definition
  `assign_FP_uop fpu (c:data_to_word_config) (secn:num) (l:num)
  (dest:num) (names:(1 spt) option) v1 =
        ((if ~(data_to_word_config_has_fp_ops c) then (GiveUp,l) else
         if dimindex (:'a) = 64 then
          (match encode_header c 3 1 with NONE -> (GiveUp,l) | SOME
            (header:'a word) ->
             (data_to_word_list_Seq [
                wordLang_Assign 3 (wordLang_Load (wordLang_Op asm_Add
                            [real_addr c (adjust_var v1);
                              wordLang_Const bytes_in_word]));
                wordLang_Inst (asm_FP (FPMovFromReg 0 3 3));
                wordLang_Inst (asm_FP (fp_uop_inst fpu));
                wordLang_Inst (asm_FP (FPMovToReg 3 5 1));
                WriteWord64 c header dest 3],l)) else
          (match encode_header c 3 2 with NONE -> (GiveUp,l) | SOME
            header ->
             (data_to_word_list_Seq [
                wordLang_Assign 15 (real_addr c (adjust_var v1));
                wordLang_Assign 11 (wordLang_Load (wordLang_Op
                  asm_Add [wordLang_Var 15; wordLang_Const
                  bytes_in_word]));
                wordLang_Assign 13 (wordLang_Load (wordLang_Op
                  asm_Add [wordLang_Var 15; wordLang_Const ((n2w 2) *
                  bytes_in_word)]));
                wordLang_Inst (asm_FP (FPMovFromReg 0 13 11));
                wordLang_Inst (asm_FP (fp_uop_inst fpu));
                wordLang_Inst (asm_FP (FPMovToReg 5 3 1));
                WriteWord64_on_32 c header dest 5 3],l))):'a
                  wordLang_prog#num)`;;

let assign_FinaliseCons_def = new_definition
  `assign_FinaliseCons (l:num) (dest:num) v1 =
                  ((wordLang_Assign (adjust_var dest)
                    (wordLang_Var (adjust_var v1)),l):'a
                    wordLang_prog#num)`;;

(* HOL4 data_to_wordScript.sml:2460-2461: a theorem that HOL4 states
   as the value of an ML expression: all_assign_defs *)

let assign_def = new_definition
  `data_to_word_assign (c:data_to_word_config) (secn:num) (l:num)
  (dest:num) (op:closLang_op) (args:num list) (names:(1 spt) option) =
     (match op with closLang_IntOp (closLang_Const i) -> assign_Const
       i l dest | closLang_GlobOp closLang_GlobalsPtr ->
       (wordLang_Assign (adjust_var dest) (wordLang_Lookup Globals),l) |
       closLang_GlobOp closLang_SetGlobalsPtr -> data_to_word_arg1 args
       (assign_SetGlobalsPtr c l dest) (wordLang_Skip,l) |
       closLang_GlobOp (closLang_SetGlobal n) -> data_to_word_arg1 args
       (assign_SetGlobal c n l dest) (wordLang_Skip,l) | closLang_GlobOp
       (closLang_Global n) -> assign_Global c n l dest | closLang_MemOp
       closLang_El -> data_to_word_arg2 args (assign_El c l dest)
       (wordLang_Skip,l) | closLang_BlockOp (closLang_ElemAt n) ->
       data_to_word_arg1 args (assign_ElemAt c n l dest)
       (wordLang_Skip,l) | closLang_MemOp closLang_DerefByte ->
       data_to_word_arg2 args (assign_DerefByte c l dest)
       (wordLang_Skip,l) | closLang_MemOp closLang_Update -> arg3 args
       (assign_Update c l dest) (wordLang_Skip,l) | closLang_MemOp
       closLang_UpdateCons -> arg3 args (assign_Update c l dest)
       (wordLang_Skip,l) | closLang_MemOp closLang_UpdateByte -> arg3
       args (assign_UpdateByte c l dest) (wordLang_Skip,l) |
       closLang_MemOp closLang_FinaliseCons -> data_to_word_arg1 args
       (assign_FinaliseCons l dest) (wordLang_Skip,l) | closLang_BlockOp
       closLang_ListAppend -> data_to_word_arg2 args (assign_ListAppend
       c secn l dest names) (wordLang_Skip,l) | closLang_BlockOp
       (closLang_Cons tag) -> assign_Cons c l dest tag args |
       closLang_MemOp (closLang_MutCons tag _30) -> assign_MutCons c l
       dest tag args | closLang_MemOp closLang_ConfigGC ->
       data_to_word_arg2 args (assign_ConfigGC c secn l dest names)
       (wordLang_Skip,l) | closLang_BlockOp (closLang_Build parts') ->
       assign_Build c secn l dest names parts' | closLang_BlockOp
       (closLang_ConsExtend tag) -> assign_ConsExtend c secn l dest
       names tag args | closLang_MemOp closLang_Ref -> assign_Ref c secn
       l dest names args | closLang_ThunkOp (AllocThunk ev) ->
       data_to_word_arg1 args (assign_AllocThunk ev c secn l dest names)
       (wordLang_Skip,l) | closLang_ThunkOp (UpdateThunk ev) ->
       data_to_word_arg2 args (assign_UpdateThunk ev c l dest)
       (wordLang_Skip,l) | closLang_MemOp (closLang_RefByte imm) ->
       data_to_word_arg2 args (assign_RefByte c secn l dest names imm)
       (wordLang_Skip,l) | closLang_MemOp closLang_XorByte ->
       data_to_word_arg2 args (assign_XorByte c secn l dest names)
       (wordLang_Skip,l) | closLang_MemOp (closLang_StringCmp b cmp) ->
       data_to_word_arg2 args (assign_StringCmp c secn l dest names b
       cmp) (wordLang_Skip,l) | closLang_Label n -> (wordLang_LocValue
       (adjust_var dest) n,l) | closLang_MemOp (closLang_CopyByte
       alloc_new) -> assign_CopyByte c secn l dest names args |
       closLang_MemOp closLang_RefArray -> data_to_word_arg2 args
       (assign_RefArray c secn l dest names) (wordLang_Skip,l) |
       closLang_BlockOp (closLang_BoolTest test) -> data_to_word_arg2
       args (assign_BoolTest l dest test) (wordLang_Skip,l) |
       closLang_BlockOp closLang_BoolNot -> data_to_word_arg1 args
       (assign_BoolNot l dest) (wordLang_Skip,l) | closLang_WordOp
       (WordTest ws test) -> data_to_word_arg2 args (assign_WordTest l
       dest test) (wordLang_Skip,l) | closLang_BlockOp
       (closLang_FromList tag) -> data_to_word_arg2 args
       (assign_FromList c secn l dest names tag) (wordLang_Skip,l) |
       closLang_IntOp (closLang_LessConstSmall i) -> data_to_word_arg1
       args (assign_LessConstSmall l dest i) (wordLang_Skip,l) |
       closLang_MemOp (closLang_BoundsCheckByte leq) ->
         data_to_word_arg2 args (assign_BoundsCheckByte c secn l dest
           names leq) (wordLang_Skip,l) | closLang_MemOp
           closLang_BoundsCheckArray ->
         data_to_word_arg2 args (assign_BoundsCheckArray c secn l
           dest names) (wordLang_Skip,l) | closLang_BlockOp
           closLang_BoundsCheckBlock ->
         data_to_word_arg2 args (assign_BoundsCheckBlock c secn l
           dest names) (wordLang_Skip,l) | closLang_BlockOp
           closLang_Equal -> data_to_word_arg2 args (assign_Equal c secn
           l dest names) (wordLang_Skip,l) | closLang_IntOp
           closLang_Less -> data_to_word_arg2 args (assign_Less c secn l
           dest names) (wordLang_Skip,l) | closLang_IntOp
           closLang_LessEq -> data_to_word_arg2 args (assign_LessEq c
           secn l dest names) (wordLang_Skip,l) | closLang_BlockOp
           closLang_LengthBlock -> data_to_word_arg1 args
           (assign_LengthBlock c secn l dest names) (wordLang_Skip,l) |
           closLang_MemOp closLang_Length -> data_to_word_arg1 args
           (assign_Length c secn l dest names) (wordLang_Skip,l) |
           closLang_MemOp closLang_LengthByte -> data_to_word_arg1 args
           (assign_LengthByte c secn l dest names) (wordLang_Skip,l) |
           closLang_BlockOp (closLang_TagLenEq tag len) ->
         data_to_word_arg1 args (assign_TagLenEq c secn l dest
           names tag len) (wordLang_Skip,l) | closLang_BlockOp
           (closLang_LenEq len) -> data_to_word_arg1 args
           (assign_LenEq c secn l dest names len) (wordLang_Skip,l) |
           closLang_BlockOp (closLang_TagEq tag) -> data_to_word_arg1
           args (assign_TagEq c secn l dest names tag)
           (wordLang_Skip,l) | closLang_IntOp closLang_Add ->
           data_to_word_arg2 args (assign_Add c secn l dest names)
           (wordLang_Skip,l) | closLang_IntOp closLang_Sub ->
           data_to_word_arg2 args (assign_Sub c secn l dest names)
           (wordLang_Skip,l) | closLang_IntOp closLang_Mult ->
           data_to_word_arg2 args (assign_Mult c secn l dest names)
           (wordLang_Skip,l) | closLang_IntOp closLang_Div ->
           data_to_word_arg2 args (assign_Div c secn l dest names)
           (wordLang_Skip,l) | closLang_IntOp closLang_Mod ->
           data_to_word_arg2 args (assign_Mod c secn l dest names)
           (wordLang_Skip,l) | closLang_WordOp (WordOpw ast_W8 opw)
           -> data_to_word_arg2 args (assign_WordOpW8 opw c secn l
           dest names) (wordLang_Skip,l) | closLang_WordOp (WordOpw
           ast_W64 opw) -> data_to_word_arg2 args (assign_WordOpW64
           opw c secn l dest names) (wordLang_Skip,l) |
           closLang_WordOp (WordShift ast_W8 sh n) ->
           data_to_word_arg1 args (assign_WordShiftW8 sh n c secn l
           dest names) (wordLang_Skip,l) | closLang_WordOp (WordShift
           ast_W64 sh n) -> data_to_word_arg1 args
           (assign_WordShiftW64 sh n c secn l dest names)
           (wordLang_Skip,l) | closLang_WordOp (WordFromWord b) ->
           data_to_word_arg1 args (assign_WordFromWord b c secn l
           dest names) (wordLang_Skip,l) | closLang_WordOp
           (WordFromInt) -> data_to_word_arg1 args
           (assign_WordFromInt c secn l dest names) (wordLang_Skip,l)
           | closLang_WordOp (WordToInt) -> data_to_word_arg1 args
           (assign_WordToInt c secn l dest names) (wordLang_Skip,l) |
           closLang_FFI ffi_index -> data_to_word_arg2 args
           (assign_FFI ffi_index c secn l dest names)
           (wordLang_Skip,l) | closLang_BlockOp (closLang_EqualConst
           p) -> data_to_word_arg1 args (assign_EqualConst p c secn l
           dest names) (wordLang_Skip,l) | closLang_Install -> arg4
           args (assign_Install c secn l dest names)
           (wordLang_Skip,l) | closLang_WordOp (FP_cmp fpc) ->
           data_to_word_arg2 args (assign_FP_cmp fpc c secn l dest
           names) (wordLang_Skip,l) | closLang_WordOp (FP_top fpt) ->
           arg3 args (assign_FP_top fpt c secn l dest names)
           (wordLang_Skip,l) | closLang_WordOp (FP_bop fpb) ->
           data_to_word_arg2 args (assign_FP_bop fpb c secn l dest
           names) (wordLang_Skip,l) | closLang_WordOp (FP_uop fpu) ->
           data_to_word_arg1 args (assign_FP_uop fpu c secn l dest
           names) (wordLang_Skip,l) | _31 -> (wordLang_Skip,l))`;;

let force_thunk_def = new_definition
  `force_thunk (c:data_to_word_config) secn (l:num) ret loc v1 =
     ((match encode_header c (8 + 6) 1 with NONE -> (GiveUp,l) | SOME
       (header:'a word) ->
      wordLang_If asm_Test (adjust_var v1) (Imm (n2w 1))
        (match ret with NONE -> wordLang_Return 0 [adjust_var v1] |
          SOME (dest,_32) -> wordLang_Assign (adjust_var dest)
          (wordLang_Var (adjust_var v1)))
        (data_to_word_list_Seq
           [wordLang_Assign 1 (real_addr c (adjust_var v1));
            wordLang_Assign 3 (wordLang_Op asm_And [wordLang_Load
              (wordLang_Var 1); wordLang_Const (n2w 0b111100)]);
            closLang_If asm_Equal 3 (Imm (n2w ((8 + 6) * 4)))
              (match ret with NONE ->
                  data_to_word_list_Seq
                    [wordLang_Assign 1 (wordLang_Load (wordLang_Op
                      asm_Add [wordLang_Var 1; wordLang_Const
                      bytes_in_word]));
                     wordLang_Return 0 [1]] | SOME (dest,_33) ->
                   wordLang_Assign (adjust_var dest)
                          (wordLang_Load (wordLang_Op asm_Add
                            [wordLang_Var 1; wordLang_Const
                            bytes_in_word])))
            (wordLang_If asm_NotEqual 3 (Imm (n2w ((0 + 6) * 4)))
              (match ret with NONE -> wordLang_Return 0 [adjust_var
                v1] | SOME (dest,_34) -> wordLang_Assign (adjust_var
                dest) (wordLang_Var (adjust_var v1)))
              (data_to_word_list_Seq
                 [wordLang_Assign 5 (wordLang_Load (wordLang_Op
                   asm_Add [wordLang_Var 1; wordLang_Const
                   bytes_in_word]));
                  (match ret with NONE -> wordLang_Call NONE (SOME
                    loc) [0; adjust_var v1; 5] NONE | SOME (r,ns) ->
                    wordLang_Call (SOME ([adjust_var r],adjust_sets
                    ns,wordLang_Skip,secn,l))
                              (SOME loc) [adjust_var v1; 5]
                                NONE)]))]),l + 1):'a
                                wordLang_prog#num)`;;

let _ = size_thms "dataLang_prog";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let comp_def,comp_ind = define_wf
  `MEASURE (\(x0,x1,x2,x3). dataLang_prog_size x3)`
  [`data_to_word_comp c (secn:num) (l:num) (p:dataLang_prog) =
     (match p with dataLang_Skip -> ((wordLang_Skip:'a
       wordLang_prog),l) | dataLang_Tick -> (wordLang_Tick,l) |
       dataLang_Raise n -> (wordLang_Raise (adjust_var n),l) |
       dataLang_Return ns -> (wordLang_Return 0 (MAP adjust_var ns),l)
       | dataLang_Move n1 n2 -> (wordLang_Move 0 [(adjust_var
       n1,adjust_var n2)],l) | dataLang_Seq p1 p2 ->
         (let (q1,l1) = data_to_word_comp c secn l p1 in
         let (q2,l2) = data_to_word_comp c secn l1 p2 in
           (wordLang_Seq q1 q2,l2)) | dataLang_If n p1 p2 ->
         (let (q1,l1) = data_to_word_comp c secn l p1 in
         let (q2,l2) = data_to_word_comp c secn l1 p2 in
           (wordLang_If asm_Equal (adjust_var n) (Imm (n2w 18)) q1
             q2,l2)) | dataLang_MakeSpace n names ->
         (let k = dimindex (:'a) DIV 8 in
         let w = n2w (n * k) in
         let w = (if w2n w = n * k then w else word_not (n2w 0)) in
           (wordLang_Seq (wordLang_Assign 1 (wordLang_Op asm_Sub
             [wordLang_Lookup TriggerGC; wordLang_Lookup NextFree]))
                (wordLang_If asm_Lower 1 (Imm w)
                  (data_to_word_list_Seq [SilentFFI c 3 (adjust_sets
                    names);
                             wordLang_Assign 1 (wordLang_Const w);
                             wordLang_Alloc 1 (adjust_sets names);
                             SilentFFI c 3 (adjust_sets names)])
                 wordLang_Skip),l)) | dataLang_Assign dest op args
                   names -> data_to_word_assign c secn l dest op args
                   names | dataLang_Force ret loc v -> force_thunk c
                   secn l ret loc v | dataLang_Call ret target args
                   handler ->
         (match ret with NONE -> (wordLang_Call NONE target (CONS 0
           (MAP adjust_var args)) NONE,l) | SOME (ns,names) ->
             (let ret = SOME (MAP adjust_var ns,adjust_sets
               names,wordLang_Skip,secn,l) in
               match handler with NONE -> (wordLang_Call ret target
                 (MAP adjust_var args) NONE,l + 1) | SOME (n,p) ->
                   (let (q1,l1) = data_to_word_comp c secn (l + 2) p
                     in
                   let handler = SOME (adjust_var n,q1,secn,l + 1)
                     in
                     (wordLang_Call ret target (MAP adjust_var
                       args) handler,l1)))))`];;

let data_to_word_compile_part_def = new_definition
  `data_to_word_compile_part c (n,arg_count,p) = (n,arg_count + 1,FST
  (data_to_word_comp c n 2 p))`;;

let MemCopy_code_def = new_definition
  `MemCopy_code =
     (wordLang_If asm_Test 2 (Reg 2) (wordLang_Return 0 [8])
         (data_to_word_list_Seq [wordLang_Assign 1 (wordLang_Load
           (wordLang_Var 4));
                    wordLang_Assign 2 (wordLang_Op asm_Sub
                      [wordLang_Var 2; wordLang_Const (n2w 4)]);
                    wordLang_Assign 4 (wordLang_Op asm_Add
                      [wordLang_Var 4; wordLang_Const bytes_in_word]);
                    wordLang_Store (wordLang_Var 6) 1;
                    wordLang_Assign 6 (wordLang_Op asm_Add
                      [wordLang_Var 6; wordLang_Const bytes_in_word]);
                    wordLang_Call NONE (SOME MemCopy_location) [0;
                      2; 4; 6; 8] NONE]):'a wordLang_prog)`;;

let ByteCopy_code_def = new_definition
  `ByteCopy_code c = (data_to_word_list_Seq
      [wordLang_Assign 4 (ShiftVar Lsr 4 2);
       wordLang_Assign 6 (ShiftVar Lsr 6 2);
       wordLang_Assign 10 (ShiftVar Lsr 10 2);
       wordLang_Assign 1 data_to_word_Unit;
       wordLang_Assign 2 (wordLang_Op asm_Add [real_addr c 2;
         wordLang_Const bytes_in_word; wordLang_Var 4]);
       wordLang_Assign 8 (wordLang_Op asm_Add [real_addr c 8;
         wordLang_Const bytes_in_word; wordLang_Var 10]);
       wordLang_If asm_Lower 4 (Reg 10)
         (data_to_word_list_Seq [wordLang_Assign 3 (wordLang_Op
           asm_Sub [wordLang_Var 6; wordLang_Const (n2w 1)]);
                    wordLang_Assign 2 (wordLang_Op asm_Add
                      [wordLang_Var 2; wordLang_Var 3]);
                    wordLang_Assign 8 (wordLang_Op asm_Add
                      [wordLang_Var 8; wordLang_Var 3]);
                    wordLang_Call NONE (SOME ByteCopySub_location)
                      [0; 6; 2; 8; 1] NONE])
         (wordLang_Call NONE (SOME ByteCopyAdd_location) [0; 6; 2;
           8; 1] NONE)]:'a wordLang_prog)`;;

let ByteCopyAdd_code_def = new_definition
  `ByteCopyAdd_code =
   wordLang_If asm_Lower 2 (Imm (n2w 4))
     (
       // n <+ 4w
       wordLang_If asm_Lower 2 (Imm (n2w 2))
       (
         // n <+ 2w
         wordLang_If asm_Equal 2 (Imm (n2w 0)) (wordLang_Return 0
           [8])
         (
           // n = 0w
           data_to_word_list_Seq [
             wordLang_Inst (asm_Mem asm_Load8 1 (Addr 4 (n2w 0)));
             wordLang_Inst (asm_Mem asm_Store8 1 (Addr 6 (n2w 0)));
             wordLang_Return 0 [8]]))
       (data_to_word_list_Seq [
         wordLang_Inst (asm_Mem asm_Load8 1 (Addr 4 (n2w 0)));
         wordLang_Inst (asm_Mem asm_Load8 3 (Addr 4 (n2w 1)));
         wordLang_If asm_Equal 2 (Imm (n2w 2))
           (data_to_word_list_Seq [
             wordLang_Inst (asm_Mem asm_Store8 1 (Addr 6 (n2w 0)));
             wordLang_Inst (asm_Mem asm_Store8 3 (Addr 6 (n2w 1)));
             wordLang_Return 0 [8]])
           (data_to_word_list_Seq [
             wordLang_Inst (asm_Mem asm_Load8 5 (Addr 4 (n2w 2)));
             wordLang_Inst (asm_Mem asm_Store8 1 (Addr 6 (n2w 0)));
             wordLang_Inst (asm_Mem asm_Store8 3 (Addr 6 (n2w 1)));
             wordLang_Inst (asm_Mem asm_Store8 5 (Addr 6 (n2w 2)));
             wordLang_Return 0 [8]])]))
     (data_to_word_list_Seq [
      wordLang_Inst (asm_Mem asm_Load8 1 (Addr 4 (n2w 0)));
      wordLang_Inst (asm_Mem asm_Load8 3 (Addr 4 (n2w 1)));
      wordLang_Inst (asm_Mem asm_Load8 5 (Addr 4 (n2w 2)));
      wordLang_Inst (asm_Mem asm_Load8 7 (Addr 4 (n2w 3)));
      wordLang_Inst (asm_Mem asm_Store8 1 (Addr 6 (n2w 0)));
      wordLang_Inst (asm_Mem asm_Store8 3 (Addr 6 (n2w 1)));
      wordLang_Inst (asm_Mem asm_Store8 5 (Addr 6 (n2w 2)));
      wordLang_Inst (asm_Mem asm_Store8 7 (Addr 6 (n2w 3)));
      wordLang_Assign 9 (wordLang_Op asm_Sub [wordLang_Var 2;
        wordLang_Const (n2w 4)]);
      wordLang_Assign 11 (wordLang_Op asm_Add [wordLang_Var 4;
        wordLang_Const (n2w 4)]);
      wordLang_Assign 13 (wordLang_Op asm_Add [wordLang_Var 6;
        wordLang_Const (n2w 4)]);
      wordLang_Call NONE (SOME ByteCopyAdd_location) [0; 9; 11;
        13; 8] NONE])`;;

let ByteCopySub_code_def = new_definition
  `ByteCopySub_code =
   wordLang_If asm_Lower 2 (Imm (n2w 4))
     (
       // n <+ 4w
       wordLang_If asm_Lower 2 (Imm (n2w 2))
       (
         // n <+ 2w
         wordLang_If asm_Equal 2 (Imm (n2w 0)) (wordLang_Return 0
           [8])
         (
           // n = 0w
           data_to_word_list_Seq [
             wordLang_Inst (asm_Mem asm_Load8 1 (Addr 4 (n2w 0)));
             wordLang_Inst (asm_Mem asm_Store8 1 (Addr 6 (n2w 0)));
             wordLang_Return 0 [8]]))
       (data_to_word_list_Seq [
         wordLang_Inst (asm_Mem asm_Load8 1 (Addr 4 (n2w 0)));
         wordLang_Inst (asm_Mem asm_Load8 3 (Addr 4 (--(n2w 1))));
         wordLang_If asm_Equal 2 (Imm (n2w 2))
           (data_to_word_list_Seq [
             wordLang_Inst (asm_Mem asm_Store8 1 (Addr 6 (n2w 0)));
             wordLang_Inst (asm_Mem asm_Store8 3 (Addr 6 (--(n2w
               1))));
             wordLang_Return 0 [8]])
           (data_to_word_list_Seq [
             wordLang_Inst (asm_Mem asm_Load8 5 (Addr 4 (--(n2w
               2))));
             wordLang_Inst (asm_Mem asm_Store8 1 (Addr 6 (n2w 0)));
             wordLang_Inst (asm_Mem asm_Store8 3 (Addr 6 (--(n2w
               1))));
             wordLang_Inst (asm_Mem asm_Store8 5 (Addr 6 (--(n2w
               2))));
             wordLang_Return 0 [8]])]))
     (data_to_word_list_Seq [
      wordLang_Inst (asm_Mem asm_Load8 1 (Addr 4 (n2w 0)));
      wordLang_Inst (asm_Mem asm_Load8 3 (Addr 4 (--(n2w 1))));
      wordLang_Inst (asm_Mem asm_Load8 5 (Addr 4 (--(n2w 2))));
      wordLang_Inst (asm_Mem asm_Load8 7 (Addr 4 (--(n2w 3))));
      wordLang_Inst (asm_Mem asm_Store8 1 (Addr 6 (n2w 0)));
      wordLang_Inst (asm_Mem asm_Store8 3 (Addr 6 (--(n2w 1))));
      wordLang_Inst (asm_Mem asm_Store8 5 (Addr 6 (--(n2w 2))));
      wordLang_Inst (asm_Mem asm_Store8 7 (Addr 6 (--(n2w 3))));
      wordLang_Assign 9 (wordLang_Op asm_Sub [wordLang_Var 2;
        wordLang_Const (n2w 4)]);
      wordLang_Assign 11 (wordLang_Op asm_Sub [wordLang_Var 4;
        wordLang_Const (n2w 4)]);
      wordLang_Assign 13 (wordLang_Op asm_Sub [wordLang_Var 6;
        wordLang_Const (n2w 4)]);
      wordLang_Call NONE (SOME ByteCopySub_location) [0; 9; 11;
        13; 8] NONE])`;;

let ByteCopyNew_code_def = new_definition
  `ByteCopyNew_code c = (wordLang_Skip:'a wordLang_prog)`;;

let data_to_word_stubs_def = new_definition
  `data_to_word_stubs (:'a) data_conf = APPEND [
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
     (Unused_location,6,wordLang_Skip);
     (
      // TODO: use next time new stub is needed
      StringCmpLoop_location,6,StringCmpLoop_code);
     (MemCopy_location,5,MemCopy_code);
     (ByteCopy_location,6,ByteCopy_code data_conf);
     (ByteCopyAdd_location,5,ByteCopyAdd_code);
     (ByteCopySub_location,5,ByteCopySub_code);
     (ByteCopyNew_location,4,ByteCopyNew_code data_conf);
     (Dummy_location,0,wordLang_Skip)] (generated_bignum_stubs
       Bignum_location)`;;

let stub_names_def = new_definition
  `data_to_word_stub_names one = APPEND [
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
     (Dummy_location,(implode "_Dummy"))] (list_of_seq (\i. (i +
       Bignum_location,(implode "_Bignum")))
     (data_num_stubs - Bignum_location))`;;

let check_stubs_length = prove
 (`word_num_stubs + LENGTH (data_to_word_stubs (:'a) c) =
  data_num_stubs`,
  CHEAT_TAC);;

let check_LongDiv_location = prove
 (`LongDiv_location = div_location`,
  CHEAT_TAC);;

let data_to_word_compile_def = new_definition
  `data_to_word_compile data_conf word_conf asm_conf prog =
     (let data_conf =
       (data_to_word_config_has_fp_tern_fupd (K (asm_config_ISA
         asm_conf = ARMv7 /\ 2 < asm_config_fp_reg_count asm_conf))
         (data_to_word_config_has_fp_ops_fupd (K (1 <
         asm_config_fp_reg_count asm_conf)) data_conf)) in
     let p = APPEND (data_to_word_stubs (:'a) data_conf) (MAP
       (data_to_word_compile_part data_conf) prog) in
       word_to_word_compile word_conf (asm_conf:'a asm_config) p)`;;

let compile_0_def = new_definition
  `compile_0 data_conf (asm_conf:'a asm_config) prog =
     (let data_conf = (data_to_word_config_has_fp_tern_fupd (K
       (asm_config_ISA asm_conf = ARMv7 /\
                              2 < asm_config_fp_reg_count
                                asm_conf))
                                (data_to_word_config_has_fp_ops_fupd
                                (K (1 < asm_config_fp_reg_count
                                asm_conf)) data_conf)) in APPEND
                                (data_to_word_stubs (:'a) data_conf)
                                (MAP (data_to_word_compile_part
                                data_conf) prog))`;;

(* compute bignum call graph *)

(* HOL4 data_to_wordScript.sml:2856-2867: the ML values that the
   definitions below antiquote *)

let AnyArith_call_tree_def = new_definition
  `AnyArith_call_tree =
     full_call_graph AnyArith_location
       (fromAList (stubs (:1)
          (data_to_word_config_has_longdiv_fupd (K F)
             (data_to_word_config_call_empty_ffi_fupd (K F) ARB))))`;;

let _ = size_thms "call_tree";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let structure_le_def,structure_le_ind = define_wf
  `MEASURE (\(x0,x1). call_tree_size x0 + call_tree_size x1)`
  [`structure_le x1 x2 =
      match (x1,x2) with
        ((word_depth_Leaf:call_tree),_35) -> T
      | (_36,word_depth_Unknown) -> T
      | ((word_depth_Const k1 t1),(word_depth_Const k2 t2)) ->
     (k1 <= k2 /\ structure_le t1 t2)
      | ((word_depth_Call n1 t2),(word_depth_Call m1 u2)) ->
     (n1 = m1 /\ structure_le t2 u2)
      | ((word_depth_Branch t1 t2),(word_depth_Branch u1 u2)) ->
     (structure_le t1 u1 /\ structure_le t2 u2)
      | (_37,_38) -> F`];;

let AnyArith_call_tree_thm = prove
 (`structure_le
     (full_call_graph AnyArith_location (fromAList
       (data_to_word_stubs (:'a) (data_conf))))
     AnyArith_call_tree`,
  CHEAT_TAC);;

(* and the interface *)
let _ = unhide_overloads ();;
