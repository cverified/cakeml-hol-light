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
  ["backend_common"; "dataLang"; "wordLang"; "word_bignum"; "word_depth";
   "word_to_word"];;

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
     ((fromAList (MAP (\(n,k). (adjust_var n,one)) (toAList names))):1
       spt)`;;

let adjust_sets_def = new_definition
  `adjust_sets (names:'a spt) =
     ((LS one,adjust_set names):1 spt#1 spt)`;;

let unit_def = new_definition
  `data_to_word_Unit = word_Const (n2w 2)`;;

let GiveUp_def = new_definition
  `GiveUp = (word_Seq (word_Assign 1 (word_Const (--(n2w 1))))
                (word_Alloc 1 (adjust_sets (LN:1 spt))):'a word_prog)`;;

let BignumHalt_def = new_definition
  `BignumHalt r = word_If asm_Test r (Imm (n2w 1)) word_Skip GiveUp`;;

let make_header_def = new_definition
  `make_header conf tag len =
     let l = dimindex (:'a) - data_to_word_config_len_size conf in
       (n2w len << l || tag << 2 || ((n2w 3):'a word))`;;

let tag_mask_def = new_definition
  `tag_mask conf =
     let l = dimindex (:'a) - data_to_word_config_len_size conf in
       (word_slice (l - 1) 2) (word_not ((n2w 0):'a word))`;;

let encode_header_def = new_definition
  `encode_header (conf:data_to_word_config) tag len =
     if tag < 2 EXP (dimindex (:'a) - data_to_word_config_len_size conf - 2)
       /\
        tag < dimword (:'a) DIV 16 /\
        len < 2 EXP (dimindex (:'a) - 4) /\
        len < 2 EXP data_to_word_config_len_size conf then SOME
          ((make_header conf (n2w tag) len):'a word)
     else NONE`;;

make_size "word_prog";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let data_to_word_list_Seq_def,data_to_word_list_Seq_ind = define_wf
  `MEASURE (\x0. list_size (word_prog_size (\x. 0)) x0)`
  `(data_to_word_list_Seq [] = word_Skip) /\
   (data_to_word_list_Seq [x] = x) /\
   (data_to_word_list_Seq (CONS x (CONS y xs)) = word_Seq x
     (data_to_word_list_Seq (CONS y xs)))`;;

let StoreEach_def,StoreEach_ind = define_rec
  `(StoreEach v [] (offset:'a word) = word_Skip) /\
   (StoreEach v (CONS x xs) (offset:'a word) =
         word_Seq (word_Store (word_Op asm_Add [word_Var v; word_Const
             offset]) x)
             (StoreEach v xs (offset + bytes_in_word)))`;;

let small_shift_length_def = new_definition
  `small_shift_length conf = data_to_word_config_len_bits conf +
  data_to_word_config_tag_bits conf + 1`;;

let shift_length_def = new_definition
  `shift_length conf = 1 + data_to_word_config_pad_bits conf +
  data_to_word_config_len_bits conf + data_to_word_config_tag_bits conf + 1`;;

let conf_ok_def = new_definition
  `conf_ok (:'a) c <=>
     shift_length c < dimindex (:'a) /\
     backend_common_word_shift (:'a) <= shift_length c
       /\ ~(data_to_word_config_len_size c = 0) /\ data_to_word_config_len_size
     c + 7 < dimindex (:'a)`;;

let max_heap_limit_def = new_definition
  `max_heap_limit (:'a) c =
     MIN (dimword (:'a) DIV 2 EXP shift_length c)
         (dimword (:'a) DIV 2 EXP (backend_common_word_shift (:'a) + 1))`;;

let all_ones_def = new_definition
  `all_ones m n = if m <= n then (n2w 0) else (word_slice (m - 1) n)
  (word_not (n2w 0))`;;

let maxout_bits_def = new_definition
  `maxout_bits n rep_len k =
     if n < 2 EXP rep_len - 1 then n2w n << k else all_ones (k + rep_len)
       k`;;

let ptr_bits_def = new_definition
  `ptr_bits conf tag len =
     (maxout_bits tag (data_to_word_config_tag_bits conf) (1 +
       data_to_word_config_len_bits conf) ||
      maxout_bits len (data_to_word_config_len_bits conf) 1)`;;

let real_addr_def = new_definition
  `((real_addr (conf:data_to_word_config) r):'a word_exp) =
     let k = backend_common_word_shift (:'a) in
     let l = shift_length conf in
       if k = l /\ data_to_word_config_len_bits conf = 0
         /\ data_to_word_config_tag_bits conf = 0 then
         word_Op asm_Add [word_Lookup CurrHeap; word_Op asm_Sub [word_Var r;
           word_Const (n2w 1)]]
       else if k <= data_to_word_config_pad_bits conf + 1 then
         word_Op asm_Add [word_Lookup CurrHeap; (\sh e n. word_Shift sh e
           (word_Const (n2w n))) Lsr (word_Var r) (l - k)]
       else word_Op asm_Add [word_Lookup CurrHeap; (\sh e n. word_Shift
         sh e (word_Const (n2w n))) Lsl ((\sh e n. word_Shift sh e
         (word_Const (n2w n))) Lsr (word_Var r) l) k]`;;

let real_offset_def = new_definition
  `((real_offset (conf:data_to_word_config) r):'a word_exp) =
      word_Op asm_Add [word_Const bytes_in_word;
              if dimindex (:'a) = 32 then word_Var r else (\sh e n.
                word_Shift sh e (word_Const (n2w n))) Lsl (word_Var r) 1]`;;

let real_byte_offset_def = new_definition
  `(real_byte_offset r:'a word_exp) =
     word_Op asm_Add [word_Const bytes_in_word;
             (\sh e n. word_Shift sh e (word_Const (n2w n))) Lsr
               (word_Var r) 2]`;;

let word_op_type_INDUCT,word_op_type_RECURSION = define_datatype
  "word_op_type =
     Bitwise binop
   | Carried binop";;

let lookup_word_op_def = define_cases
  `(lookup_word_op backend_common_Andw = Bitwise asm_And) /\
   (lookup_word_op backend_common_Orw = Bitwise asm_Or) /\
   (lookup_word_op backend_common_Xor = Bitwise asm_Xor) /\
   (lookup_word_op backend_common_Add = Carried asm_Add) /\
   (lookup_word_op backend_common_Sub = Carried asm_Sub)`;;
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

(* HOL4 data_to_wordScript.sml:273-274: a theorem that HOL4 states as the
   value of an ML expression: FromList_location_eq *)
(* HOL4 data_to_wordScript.sml:275-276: a theorem that HOL4 states as the
   value of an ML expression: FromList1_location_eq *)
(* HOL4 data_to_wordScript.sml:277-278: a theorem that HOL4 states as the
   value of an ML expression: RefByte_location_eq *)
(* HOL4 data_to_wordScript.sml:279-280: a theorem that HOL4 states as the
   value of an ML expression: RefArray_location_eq *)
(* HOL4 data_to_wordScript.sml:281-282: a theorem that HOL4 states as the
   value of an ML expression: Replicate_location_eq *)
(* HOL4 data_to_wordScript.sml:283-284: a theorem that HOL4 states as the
   value of an ML expression: AnyArith_location_eq *)
(* HOL4 data_to_wordScript.sml:285-286: a theorem that HOL4 states as the
   value of an ML expression: Add_location_eq *)
(* HOL4 data_to_wordScript.sml:287-288: a theorem that HOL4 states as the
   value of an ML expression: Sub_location_eq *)
(* HOL4 data_to_wordScript.sml:289-290: a theorem that HOL4 states as the
   value of an ML expression: Mul_location_eq *)
(* HOL4 data_to_wordScript.sml:291-292: a theorem that HOL4 states as the
   value of an ML expression: Div_location_eq *)
(* HOL4 data_to_wordScript.sml:293-294: a theorem that HOL4 states as the
   value of an ML expression: Mod_location_eq *)
(* HOL4 data_to_wordScript.sml:295-296: a theorem that HOL4 states as the
   value of an ML expression: Compare1_location_eq *)
(* HOL4 data_to_wordScript.sml:297-298: a theorem that HOL4 states as the
   value of an ML expression: Compare_location_eq *)
(* HOL4 data_to_wordScript.sml:299-300: a theorem that HOL4 states as the
   value of an ML expression: Equal1_location_eq *)
(* HOL4 data_to_wordScript.sml:301-302: a theorem that HOL4 states as the
   value of an ML expression: Equal_location_eq *)
(* HOL4 data_to_wordScript.sml:303-304: a theorem that HOL4 states as the
   value of an ML expression: LongDiv1_location_eq *)
(* HOL4 data_to_wordScript.sml:305-306: a theorem that HOL4 states as the
   value of an ML expression: LongDiv_location_eq *)
(* HOL4 data_to_wordScript.sml:307-308: a theorem that HOL4 states as the
   value of an ML expression: MemCopy_location_eq *)
(* HOL4 data_to_wordScript.sml:309-310: a theorem that HOL4 states as the
   value of an ML expression: Bignum_location_eq *)
(* HOL4 data_to_wordScript.sml:311-312: a theorem that HOL4 states as the
   value of an ML expression: ByteCopy_location_eq *)
(* HOL4 data_to_wordScript.sml:313-314: a theorem that HOL4 states as the
   value of an ML expression: ByteCopyAdd_location_eq *)
(* HOL4 data_to_wordScript.sml:315-316: a theorem that HOL4 states as the
   value of an ML expression: ByteCopySub_location_eq *)
(* HOL4 data_to_wordScript.sml:317-318: a theorem that HOL4 states as the
   value of an ML expression: ByteCopyNew_location_eq *)
(* HOL4 data_to_wordScript.sml:319-320: a theorem that HOL4 states as the
   value of an ML expression: Install_location_eq *)
(* HOL4 data_to_wordScript.sml:321-322: a theorem that HOL4 states as the
   value of an ML expression: InstallCode_location_eq *)
(* HOL4 data_to_wordScript.sml:323-324: a theorem that HOL4 states as the
   value of an ML expression: InstallData_location_eq *)
(* HOL4 data_to_wordScript.sml:325-326: a theorem that HOL4 states as the
   value of an ML expression: Dummy_location_eq *)
(* HOL4 data_to_wordScript.sml:327-328: a theorem that HOL4 states as the
   value of an ML expression: Append_location_eq *)
(* HOL4 data_to_wordScript.sml:329-330: a theorem that HOL4 states as the
   value of an ML expression: AppendMainLoop_location_eq *)
(* HOL4 data_to_wordScript.sml:331-332: a theorem that HOL4 states as the
   value of an ML expression: AppendLenLoop_location_eq *)
(* HOL4 data_to_wordScript.sml:333-334: a theorem that HOL4 states as the
   value of an ML expression: XorLoop_location_eq *)
(* HOL4 data_to_wordScript.sml:335-336: a theorem that HOL4 states as the
   value of an ML expression: Unused_location_eq *)
(* HOL4 data_to_wordScript.sml:337-338: a theorem that HOL4 states as the
   value of an ML expression: StringCmpLoop_location_eq *)

let SilentFFI_def = new_definition
  `SilentFFI c n names =
     if data_to_word_config_call_empty_ffi c then
       data_to_word_list_Seq [word_Assign n (word_Const (n2w 0));
                 word_Assign 7 (word_Op asm_Sub [word_Lookup NextFree;
                   word_Lookup CurrHeap]);
                 word_Assign 9 (word_Lookup HeapLength);
                 word_FFI (implode "") 7 n 9 n names]
     else word_Skip`;;

let AllocVar_def = new_definition
  `AllocVar c (limit':num) (names:1 spt) =
     data_to_word_list_Seq [word_Assign 1 ((\sh e n. word_Shift sh e
       (word_Const (n2w n))) Lsr (word_Var 1) 2);
               word_If asm_Lower 1 (Imm (n2w limit'))
                 (word_Assign 1 ((\sh e n. word_Shift sh e (word_Const (n2w
                   n))) Lsl (word_Op asm_Add [word_Var 1; word_Const (n2w 1)])
                   (backend_common_word_shift (:'a))))
                 (word_Assign 1 (word_Const (--((n2w 1):'a word))));
               word_Assign 3 (word_Op asm_Sub [word_Lookup TriggerGC;
                 word_Lookup NextFree]);
               word_If asm_Lower 3 (Reg 1)
                 (data_to_word_list_Seq [SilentFFI c 3 (FST (adjust_sets
                   names),
                              sptree_insert 1 one (SND (adjust_sets
                                names)));
                            word_Alloc 1 (adjust_sets names);
                            SilentFFI c 3 (adjust_sets names)])
                              word_Skip]`;;

let MakeBytes_def = new_definition
  `MakeBytes n =
     (data_to_word_list_Seq [word_Assign n ((\sh e n. word_Shift sh e
       (word_Const (n2w n))) Lsr (word_Var n) 2);
               word_Assign n (word_Op asm_Or [word_Var n; (\sh e n.
                 word_Shift sh e (word_Const (n2w n))) Lsl (word_Var n) 8]);
               word_Assign n (word_Op asm_Or [word_Var n; (\sh e n.
                 word_Shift sh e (word_Const (n2w n))) Lsl (word_Var n) 16]);
               if dimindex (:'a) = 32 then word_Skip else word_Assign n
                 (word_Op asm_Or [word_Var n; (\sh e n. word_Shift sh e
                 (word_Const (n2w n))) Lsl (word_Var n) 32])]:'a word_prog)`;;

let SmallLsr_def = new_definition
  `SmallLsr e n = if n = 0 then e else (\sh e n. word_Shift sh e (word_Const
  (n2w n))) Lsr e n`;;

let WriteLastByte_aux_def = new_definition
  `WriteLastByte_aux offset a b n p =
     word_If asm_Equal n (Imm offset) word_Skip
       (word_Seq (word_Inst (asm_Mem asm_Store8 b (Addr a offset))) p)`;;

let WriteLastBytes_def = new_definition
  `WriteLastBytes a b n =
     WriteLastByte_aux ((n2w 0):'a word) a b n (
       WriteLastByte_aux (n2w 1) a b n (
         WriteLastByte_aux (n2w 2) a b n (
           WriteLastByte_aux (n2w 3) a b n (
             if dimindex (:'a) = 32 then word_Skip else WriteLastByte_aux
               (n2w 4) a b n (
               WriteLastByte_aux (n2w 5) a b n (
                 WriteLastByte_aux (n2w 6) a b n (
                   WriteLastByte_aux (n2w 7) a b n word_Skip)))))))`;;

let RefByte_code_def = new_definition
  `RefByte_code c =
       let limit' = MIN (2 EXP data_to_word_config_len_size c) (dimword
         (:'a) DIV 16) in
       let h = word_Op asm_Add [(\sh e n. word_Shift sh e (word_Const (n2w
         n))) Lsr (word_Var 2) 2; word_Const bytes_in_word] in
       let x = SmallLsr h (dimindex (:'a) - 63) in
       let y = (\sh e n. word_Shift sh e (word_Const (n2w n))) Lsl h
         (dimindex (:'a) - backend_common_word_shift (:'a) -
         data_to_word_config_len_size c) in
         data_to_word_list_Seq
           [BignumHalt 2;
            word_Assign 1 x;
            AllocVar c limit' (sptree_fromList [one; one; one]);
            // compute length
            word_Assign 5 ((\sh e n. word_Shift sh e (word_Const (n2w n)))
              Lsr h (backend_common_word_shift (:'a)));
            word_Assign 7 ((\sh e n. word_Shift sh e (word_Const (n2w n)))
              Lsl (word_Var 5) 2);
            word_Assign 9 (word_Lookup NextFree);
            // adjust end of heap
            word_Assign 1 (word_Op asm_Add [word_Var 9;
                              (\sh e n. word_Shift sh e (word_Const (n2w
                                n))) Lsl (word_Var 5)
                                (backend_common_word_shift (:'a))]);
            word_Set NextFree (word_Op asm_Add [word_Var 1; word_Const
              bytes_in_word]);
            // 3 := return value
            word_Assign 3 (word_Op asm_Or [(\sh e n. word_Shift sh e
              (word_Const (n2w n))) Lsl (word_Op asm_Sub [word_Var 9;
              word_Lookup CurrHeap])
                (shift_length c - backend_common_word_shift (:'a));
                  word_Const ((n2w 1):'a word)]);
            // compute header
            word_Assign 5 (word_Op asm_Or [word_Op asm_Or [y; word_Const
              (n2w 7)]; word_Var 6]);
            // compute repeated byte
            MakeBytes 4;
            // store header
            word_Store (word_Var 9) 5;
            // write last word of byte array
            word_Assign 11 (word_Op asm_And [(\sh e n. word_Shift sh e
              (word_Const (n2w n))) Lsr (word_Var 2) 2;
                              word_Const (bytes_in_word - (n2w 1))]);
            word_Assign 13 (word_Const (n2w 0));
            word_Store (word_Var 1) 13;
            WriteLastBytes 1 4 11;
            word_Assign 7 (word_Op asm_Sub [word_Var 7; word_Const (n2w
              4)]);
            // write rest of byte array
            word_Call NONE (SOME Replicate_location)
              [
               // ret_loc, addr, v, n, ret_val
               0; 9; 4; 7; 3] NONE]:'a word_prog`;;

let maxout_bits_code_def = new_definition
  `Maxout_bits_code rep_len k dest n =
     (word_If asm_Lower n (Imm (n2w (2 EXP rep_len - 1)))
       (word_Assign dest (word_Op asm_Or [word_Var dest; (\sh e n.
         word_Shift sh e (word_Const (n2w n))) Lsl (word_Var n) k]))
       (word_Assign dest (word_Op asm_Or [word_Var dest; word_Const
         (all_ones (k + rep_len) k)])):'a word_prog)`;;

let make_ptr_bits_code_def = new_definition
  `Make_ptr_bits_code c tag len dest =
     (data_to_word_list_Seq [word_Assign dest (word_Op asm_Or
        [word_Const (n2w 1); (\sh e n. word_Shift sh e (word_Const (n2w n)))
          Lsl (word_Op asm_Sub [word_Lookup NextFree; word_Lookup CurrHeap])
            (shift_length c - backend_common_word_shift (:'a))]);
         Maxout_bits_code (data_to_word_config_tag_bits c) (1 +
           data_to_word_config_len_bits c) dest tag;
         Maxout_bits_code (data_to_word_config_len_bits c) 1 dest len]:'a
           word_prog)`;;

let FromList_code_def = new_definition
  `FromList_code c =
     let limit' = MIN (2 EXP data_to_word_config_len_size c) (dimword (:'a)
       DIV 16) in
     let h = (\sh e n. word_Shift sh e (word_Const (n2w n))) Lsl (word_Var
       2) (dimindex (:'a) - data_to_word_config_len_size c - 2) in
       word_If asm_Equal 2 (Imm (n2w 0))
         (data_to_word_list_Seq [word_Assign 6 (word_Op asm_Add [word_Var 6;
           word_Const ((n2w 2):'a word)]);
                    word_Return 0 [6]])
         (data_to_word_list_Seq
           [BignumHalt 2;
            word_Assign 1 (word_Var 2); AllocVar c limit' (sptree_fromList
              [one; one; one]);
            word_Assign 1 (word_Lookup NextFree);
            word_Assign 5 (word_Op asm_Or [h; word_Const (n2w 3); word_Var
              6]);
            word_Assign 7 ((\sh e n. word_Shift sh e (word_Const (n2w n)))
              Lsr (word_Var 2) 2);
            word_Assign 9 ((\sh e n. word_Shift sh e (word_Const (n2w n)))
              Lsr (word_Var 6) 4);
            Make_ptr_bits_code c 9 7 3;
            word_Call NONE (SOME FromList1_location) [0; 1; 4; 2; 3; 5]
              NONE]):'a word_prog`;;

let FromList1_code_def = new_definition
  `FromList1_code c =
     // 0 = return address
     // 2 = address to write to
     // 4 = where to lookup what to write
     // 6 = how many left to write
     // 8 = value to be returned
     // 10 = first thing to write
     (data_to_word_list_Seq
       [word_Store (word_Var 2) 10;
        word_Assign 2 (word_Op asm_Add [word_Var 2; word_Const
          bytes_in_word]);
        word_If asm_Equal 6 (Imm (n2w 0))
          (data_to_word_list_Seq
             [word_Set NextFree (word_Var 2);
              word_Return 0 [8]])
          (data_to_word_list_Seq
             [word_Assign 4 (real_addr c 4);
              word_Assign 10 (word_Load (word_Op asm_Add [word_Var 4;
                word_Const bytes_in_word]));
              word_Assign 4 (word_Load (word_Op asm_Add [word_Var 4;
                word_Const ((n2w 2) * bytes_in_word)]));
              word_Assign 6 (word_Op asm_Sub [word_Var 6; word_Const (n2w
                4)]);
              word_Call NONE (SOME FromList1_location) [0; 2; 4; 6; 8;
                10] NONE])]:'a word_prog)`;;

let RefArray_code_def = new_definition
  `RefArray_code c =
         (data_to_word_list_Seq
           [word_Assign 1 ((\sh e n. word_Shift sh e (word_Const (n2w n)))
             Lsl (word_Op asm_Add [((\sh e n. word_Shift sh e (word_Const (n2w
             n))) Lsr (word_Var 2) 2); word_Const (n2w 1)])
                       (backend_common_word_shift (:'a)));
            word_Set TriggerGC (word_Op asm_Sub [word_Lookup TriggerGC;
              word_Var 1]);
            word_Assign 1 (word_Op asm_Sub [word_Lookup EndOfHeap; word_Var
              1]);
            word_Set EndOfHeap (word_Var 1);
            // 3 := return value
            word_Assign 3 (word_Op asm_Or [(\sh e n. word_Shift sh e
              (word_Const (n2w n))) Lsl (word_Op asm_Sub [word_Var 1;
              word_Lookup CurrHeap])
                (shift_length c - backend_common_word_shift (:'a));
                  word_Const ((n2w 1):'a word)]);
            // compute header
            word_Assign 5 (word_Op asm_Or [(\sh e n. word_Shift sh e
              (word_Const (n2w n))) Lsl (word_Var 2)
                              (dimindex (:'a) - data_to_word_config_len_size
                                c - 2);
                             word_Const (make_header c (n2w 2) 0)]);
            // store header
            word_Store (word_Var 1) 5;
            word_Call NONE (SOME Replicate_location)
               [
                // ret_loc, addr, v, n, ret_val
                0; 1; 4; 2; 3] NONE]:'a word_prog)`;;

let replicate_code_def = new_definition
  `Replicate_code =
     // 0 = return address
     // 2 = address to write to
     // 4 = what to write at each location
     // 6 = how many left to write
     // 8 = value to be returned
     (word_If asm_Equal 6 (Imm (n2w 0)) (word_Return 0 [8])
       (data_to_word_list_Seq [word_Assign 2 (word_Op asm_Add [word_Var 2;
         word_Const (bytes_in_word)]);
                  word_Store (word_Var 2) 4;
                  word_Assign 6 (word_Op asm_Sub [word_Var 6; word_Const
                    (n2w 4)]);
                  word_Call NONE (SOME Replicate_location) [0; 2; 4; 6;
                    8] NONE]):'a word_prog)`;;

let AddNumSize_def = new_definition
  `AddNumSize c src =
     (word_If asm_Equal (adjust_var src) (Imm (n2w 0)) word_Skip
       (word_If asm_Test (adjust_var src) (Imm (n2w 1))
          (word_Assign 1 (word_Op asm_Add [word_Var 1; word_Const (n2w 4)]))
        (word_Assign 1 (word_Op asm_Add [word_Var 1;
          ((\sh e n. word_Shift sh e (word_Const (n2w n))) Lsl ((\sh e n.
            word_Shift sh e (word_Const (n2w n))) Lsr
             (word_Load (real_addr c (adjust_var src)))
                (dimindex (:'a) - data_to_word_config_len_size c)))
                  2]))):'a word_prog)`;;

let AnyHeader_def = new_definition
  `AnyHeader c r a t1
         // header
         t2
           // pointer
           t3 =
     // payload
     word_If asm_Equal r (Imm ((n2w 0):'a word))
       (data_to_word_list_Seq [word_Assign 7 (word_Const (n2w 0));
                  word_Set (Temp t1) (word_Var r);
                  word_Set (Temp t2) (word_Var r);
                  word_Set (Temp t3) (word_Var r)])
    (word_If asm_NotTest r (Imm (n2w 1))
       (data_to_word_list_Seq
         [word_Assign 7 (real_addr c r);
          word_Set (Temp t2) (word_Op asm_Add [word_Var 7; word_Const
            bytes_in_word]);
          word_Set (Temp t1) (word_Op asm_Add
            [(\sh e n. word_Shift sh e (word_Const (n2w n))) Lsl ((\sh e n.
              word_Shift sh e (word_Const (n2w n))) Lsr (word_Load (word_Var
              7)) ((dimindex (:'a)) - data_to_word_config_len_size c)) 1;
             word_Op asm_And [word_Const (n2w 1); (\sh e n. word_Shift sh e
               (word_Const (n2w n))) Lsr (word_Load (word_Var 7)) 4]]);
          word_Set (Temp t3) (word_Const (n2w 0))])
    (word_If asm_NotLess r (Imm (n2w 0))
       (data_to_word_list_Seq
         [word_Set (Temp t1) (word_Const (n2w 2));
          word_Set (Temp t2) (word_Lookup (if a then OtherHeap else
            NextFree));
          word_Set (Temp t3) ((\sh e n. word_Shift sh e (word_Const (n2w
            n))) Lsr (word_Var r) 2);
          word_Assign 7 (word_Const (n2w 0))])
       (data_to_word_list_Seq
         [word_Set (Temp t1) (word_Const (n2w 3));
          word_Set (Temp t2) (word_Lookup (if a then OtherHeap else
            NextFree));
          word_Set (Temp t3) (word_Op asm_Sub [word_Const (n2w 0); (\sh e n.
            word_Shift sh e (word_Const (n2w n))) Asr (word_Var r) 2]);
          word_Assign 7 (word_Const (n2w 0))])))`;;

let ShiftVar_def = new_definition
  `ShiftVar sh v n =
     if sh = Ror then
       (let m = (if n < dimindex (:'a) then n else n MOD (dimindex (:'a)))
         in
          if m = 0 then word_Var v else (\sh e n. word_Shift sh e
            (word_Const (n2w n))) sh (word_Var v) m)
     else if n = 0 then word_Var v
     else if dimindex (:'a) <= n then
       if sh = Asr then (\sh e n. word_Shift sh e (word_Const (n2w n))) sh
         (word_Var v) (dimindex (:'a) - 1) else word_Const (n2w 0)
     else ((\sh e n. word_Shift sh e (word_Const (n2w n))) sh (word_Var
       v) n):'a word_exp`;;

let AnyArith_code_def = new_definition
  `AnyArith_code c = (data_to_word_list_Seq [
       // perform allocation
       word_Assign 1 (word_Const (n2w 4));
       AddNumSize c 0;
       AddNumSize c 1;
       word_Set (Temp (n2w 29)) (word_Var 1);
       AllocVar c (2 EXP data_to_word_config_len_size c) (sptree_fromList
         [one; one; one]);
       // convert smallnums to bignum if necessary
       AnyHeader c 2 F (n2w 0) (n2w 31) (n2w 12);
       AnyHeader c 4 T (n2w 1) (n2w 30) (n2w 11);
       word_Get 1 (Temp (n2w 11));
       word_Store (word_Lookup OtherHeap) 1;
       word_Get 1 (Temp (n2w 12));
       word_Store (word_Lookup NextFree) 1;
       word_Get 1 (Temp (n2w 29));
       word_Assign 2 (word_Lookup NextFree);
       word_Set (Temp (n2w 29)) (word_Var 2);
       word_Set (Temp (n2w 3)) ((\sh e n. word_Shift sh e (word_Const (n2w
         n))) Lsr (word_Var 6) 2);
       word_Assign 3 (word_Const (n2w 0));
       // zero out result array
       word_Call (SOME ([0],(sptree_fromList
         [one],LN),word_Skip,AnyArith_location,2))
         (SOME Replicate_location) [2; 3; 1; 0] NONE;
       // perform bignum calculation
       word_Set (Temp (n2w 29)) (word_Op asm_Add [word_Lookup (Temp (n2w
         29)); word_Const bytes_in_word]);
       word_Call (SOME ([1],(sptree_fromList
         [one],LN),word_Skip,AnyArith_location,3))
         (SOME Bignum_location) [] NONE;
       // convert bignum to smallnum if possible without loss of info
       word_Get 1 (Temp (n2w 10));
       word_If asm_Test 1 (Reg 1) (word_Return 0 [1]) word_Skip;
       word_Assign 3 (word_Load (word_Op asm_Add [word_Lookup NextFree;
         word_Const bytes_in_word]));
       word_If asm_Equal 1 (Imm (n2w 2))
         (word_Seq (word_Assign 5 ((\sh e n. word_Shift sh e (word_Const
           (n2w n))) Lsr (word_Var 3) (dimindex (:'a) - 3)))
              (word_If asm_Test 5 (Reg 5)
                 (word_Seq (word_Assign 1 ((\sh e n. word_Shift sh e
                   (word_Const (n2w n))) Lsl (word_Var 3) 2))
                      (word_Return 0 [1]))
                 word_Skip))
         (word_If asm_Equal 1 (Imm (n2w 3))
           (word_Seq (word_Assign 5 ((\sh e n. word_Shift sh e (word_Const
             (n2w n))) Lsr (word_Op asm_Sub [word_Var 3; word_Const (n2w 1)])
                             (dimindex (:'a) - 3)))
                (word_If asm_Test 5 (Reg 5)
                   (word_Seq (word_Assign 1 (word_Op asm_Sub [word_Const
                     (n2w 0); (\sh e n. word_Shift sh e (word_Const (n2w n)))
                     Lsl (word_Var 3) 2]))
                        (word_Return 0 [1]))
                   word_Skip))
           (word_Assign 5 (word_Const (n2w 0))));
       // return the bignum
       word_Assign 5 (word_Lookup NextFree);
       word_Assign 6 (ShiftVar Lsr 1 1);
       word_Assign 8 (word_Op asm_And [word_Var 1; word_Const (n2w 1)]);
       word_Assign 7 (word_Op asm_Or [word_Const (n2w 0b1111);
                        ShiftVar Lsl 6 (dimindex (:'a) -
                          data_to_word_config_len_size c);
                        ShiftVar Lsl 8 4]);
       word_Store (word_Var 5) 7;
       word_Assign 1 (word_Op asm_Sub [word_Var 5; word_Lookup CurrHeap]);
       word_Assign 1 (word_Op asm_Or [ShiftVar Lsl 1 (shift_length c -
         backend_common_word_shift (:'a)); word_Const (n2w 1)]);
       word_Set NextFree (word_Op asm_Add [word_Var 5; word_Const
         bytes_in_word;
                             ShiftVar Lsl 6 (backend_common_word_shift
                               (:'a))]);
       word_Return 0 [1]]:'a word_prog)`;;

let add_code_def = new_definition
  `Add_code = (word_Seq (word_Assign 6 (word_Const (n2w (4 * 0))))
                  (word_Call NONE (SOME AnyArith_location) [0; 2; 4; 6]
                    NONE):'a word_prog)`;;

let sub_code_def = new_definition
  `Sub_code = (word_Seq (word_Assign 6 (word_Const (n2w (4 * 1))))
                  (word_Call NONE (SOME AnyArith_location) [0; 2; 4; 6]
                    NONE):'a word_prog)`;;

let mul_code_def = new_definition
  `Mul_code = (word_Seq (word_Assign 6 (word_Const (n2w (4 * 4))))
                  (word_Call NONE (SOME AnyArith_location) [0; 2; 4; 6]
                    NONE):'a word_prog)`;;

let div_code_def = new_definition
  `Div_code = (word_Seq (word_Assign 6 (word_Const (n2w (4 * 5))))
                  (word_Call NONE (SOME AnyArith_location) [0; 2; 4; 6]
                    NONE):'a word_prog)`;;

let mod_code_def = new_definition
  `Mod_code = (word_Seq (word_Assign 6 (word_Const (n2w (4 * 6))))
                  (word_Call NONE (SOME AnyArith_location) [0; 2; 4; 6]
                    NONE):'a word_prog)`;;

let install_code_def = new_definition
  `Install_code c =
       (data_to_word_list_Seq [word_Assign 1 (word_Lookup BitmapBuffer);
                 word_Assign 3 (word_Lookup CodeBuffer);
                 word_Set BitmapBuffer (word_Var 2);
                 word_Set CodeBuffer (word_Var 4);
                 word_Install 3 4 1 2 (LS one,LN);
                 word_Return 0 [3]]:'a word_prog)`;;

let InstallCode_code_def = new_definition
  `InstallCode_code c =
        (word_If asm_Test 2 (Imm (n2w 1))
         (word_Seq (word_Assign 2 (word_Lookup BitmapBuffer))
              (word_Call NONE (SOME InstallData_location) [0; 2; 4; 6]
                NONE))
         (data_to_word_list_Seq [word_Assign 3 (real_addr c 2);
                    word_Assign 2 (word_Load (word_Op asm_Add [word_Var 3;
                      word_Const bytes_in_word]));
                    word_Assign 2 (ShiftVar Lsr 2 2);
                    word_CodeBufferWrite 6 2;
                    word_Assign 6 (word_Op asm_Add [word_Var 6; word_Const
                      (n2w 1)]);
                    word_Assign 2 (word_Load (word_Op asm_Add [word_Var 3;
                      word_Const ((n2w 2) * bytes_in_word)]));
                    word_Call NONE (SOME InstallCode_location) [0; 2; 4;
                      6] NONE]):'a word_prog)`;;

let InstallData_code_def = new_definition
  `InstallData_code c =
        (word_If asm_Test 4 (Imm (n2w 1))
         (data_to_word_list_Seq [word_Call NONE (SOME Install_location) [0;
           2; 6] NONE])
         (data_to_word_list_Seq [word_Assign 3 (real_addr c 4);
                    word_Assign 4 (word_Load (word_Op asm_Add [word_Var 3;
                      word_Const bytes_in_word]));
                    word_Assign 4 (real_addr c 4);
                    word_Assign 4 (word_Load (word_Op asm_Add [word_Var 4;
                      word_Const bytes_in_word]));
                    word_DataBufferWrite 2 4;
                    word_Assign 2 (word_Op asm_Add [word_Var 2; word_Const
                      bytes_in_word]);
                    word_Assign 4 (word_Load (word_Op asm_Add [word_Var 3;
                      word_Const ((n2w 2) * bytes_in_word)]));
                    word_Call NONE (SOME InstallData_location) [0; 2; 4;
                      6] NONE]):'a word_prog)`;;

let compare1_code_def = new_definition
  `Compare1_code =
     // l is 2, a1 is 4, a2 is 6
     word_If asm_Equal 2 (Imm (n2w 0))
       (word_Seq (word_Assign 2 (word_Const (n2w 1))) (word_Return 0 [2]))
       (data_to_word_list_Seq
          [word_Assign 8 (word_Load (word_Var 4));
           word_Assign 9 (word_Load (word_Var 6));
           word_If asm_Equal 8 (Reg 9)
             (data_to_word_list_Seq
                [word_Assign 2 (word_Op asm_Sub [word_Var 2; word_Const (n2w
                  1)]);
                 word_Assign 4 (word_Op asm_Sub [word_Var 4; word_Const
                   bytes_in_word]);
                 word_Assign 6 (word_Op asm_Sub [word_Var 6; word_Const
                   bytes_in_word]);
                 word_Call NONE (SOME Compare1_location) [0; 2; 4; 6] NONE])
             (word_If asm_Lower 8 (Reg 9)
               (word_Seq (word_Assign 2 (word_Const (n2w 0))) (word_Return 0
                 [2]))
               (word_Seq (word_Assign 2 (word_Const (n2w 2)))
                 (word_Return 0 [2])))])`;;

let compare_code_def = new_definition
  `Compare_code c =
     // this code can assume that the arguments (2 and 4) are not both
     // small numbers
     word_If asm_Test 2 (Imm (n2w 1))
       (
        // 1st arg is small number, means that 2nd must be bigum
        data_to_word_list_Seq [word_Assign 1 (word_Load (real_addr c 4));
                  // loads header of 2nd arg
                  word_If asm_Test 1 (Imm (n2w 16))
                    (word_Seq (word_Assign 2 (word_Const (n2w 0)))
                      (word_Return 0 [2]))
                    (word_Seq (word_Assign 2 (word_Const (n2w 2)))
                      (word_Return 0 [2]))])
    (word_If asm_Test 4 (Imm (n2w 1))
       (
        // 2nd arg is small number: 1st must be bigum
        data_to_word_list_Seq [word_Assign 1 (word_Load (real_addr c 2));
                  // loads header of 1st arg
                  word_If asm_Test 1 (Imm ((n2w 16):'a word))
                    (word_Seq (word_Assign 2 (word_Const (n2w 2)))
                      (word_Return 0 [2]))
                    (word_Seq (word_Assign 2 (word_Const (n2w 0)))
                      (word_Return 0 [2]))])
       (data_to_word_list_Seq [word_Assign 11 (real_addr c 2);
                  word_Assign 1 (word_Load (word_Var 11));
                  // loads header of 1st arg
                  word_Assign 13 (real_addr c 4);
                  word_Assign 3 (word_Load (word_Var 13));
                  // loads header of 2nd arg
                  word_Assign 6 ((\sh e n. word_Shift sh e (word_Const (n2w
                    n))) Lsr (word_Var 1) ((dimindex (:'a) -
                    data_to_word_config_len_size c)));
                  word_Assign 8 ((\sh e n. word_Shift sh e (word_Const (n2w
                    n))) Lsr (word_Var 3) ((dimindex (:'a) -
                    data_to_word_config_len_size c)));
                  word_If asm_Equal 1 (Reg 3)
                    (
                     // headers are the same
                     data_to_word_list_Seq
                      [word_Assign 2 (word_Op asm_Add [word_Var 11; (\sh e
                        n. word_Shift sh e (word_Const (n2w n))) Lsl (word_Var
                        6) (backend_common_word_shift (:'a))]);
                       word_Assign 4 (word_Op asm_Add [word_Var 13; (\sh e
                         n. word_Shift sh e (word_Const (n2w n))) Lsl (word_Var
                         6) (backend_common_word_shift (:'a))]);
                       word_If asm_Test 1 (Imm (n2w 16))
                        (word_Call NONE (SOME Compare1_location) [0; 6; 2;
                          4] NONE)
                        (word_Call NONE (SOME Compare1_location) [0; 6; 4;
                          2] NONE)])
                    (
                     // headers are not the same
                     word_If asm_Test 1 (Imm (n2w 16))
                       (word_If asm_Test 3 (Imm (n2w 16))
                          (word_If asm_Lower 6 (Reg 8)
                             (word_Seq (word_Assign 2 (word_Const (n2w 0)))
                               (word_Return 0 [2]))
                             (word_Seq (word_Assign 2 (word_Const (n2w 2)))
                               (word_Return 0 [2])))
                          (word_Seq (word_Assign 2 (word_Const (n2w 2)))
                            (word_Return 0 [2])))
                       (word_If asm_Test 3 (Imm (n2w 16))
                          (word_Seq (word_Assign 2 (word_Const (n2w 0)))
                            (word_Return 0 [2]))
                          (word_If asm_Lower 6 (Reg 8)
                             (word_Seq (word_Assign 2 (word_Const (n2w 2)))
                               (word_Return 0 [2]))
                             (word_Seq (word_Assign 2 (word_Const (n2w
                               0))) (word_Return 0 [2])))))]))`;;

let equal1_code_def = new_definition
  `Equal1_code =
     data_to_word_list_Seq [
       word_If asm_Equal 2 (Imm (n2w 0))
         (word_Seq (word_Assign 2 (word_Const (n2w 1))) (word_Return 0 [2]))
           word_Skip;
       word_Assign 1 (word_Load (word_Var 4));
       word_Assign 3 (word_Load (word_Var 6));
       word_Call (SOME ([5],(list_insert [0; 2; 4; 6]
         LN,LN),word_Skip,Equal1_location,2))
         (SOME Equal_location) [1; 3] NONE;
       word_If asm_Equal 5 (Imm (n2w 1)) word_Skip (word_Return 0 [5]);
       word_Assign 2 (word_Op asm_Sub [word_Var 2; word_Const (n2w 1)]);
       word_Assign 4 (word_Op asm_Add [word_Var 4; word_Const
         bytes_in_word]);
       word_Assign 6 (word_Op asm_Add [word_Var 6; word_Const
         bytes_in_word]);
       word_Call NONE (SOME Equal1_location) [0; 2; 4; 6] NONE]`;;

let equal_code_def = new_definition
  `Equal_code c =
     data_to_word_list_Seq [
       word_If asm_Equal 2 (Reg 4)
         (word_Seq (word_Assign 2 (word_Const ((n2w 1):'a word)))
           (word_Return 0 [2])) word_Skip;
       word_Assign 1 (word_Op asm_And [word_Var 2; word_Var 4]);
       word_If asm_Test 1 (Imm (n2w 1))
         (word_Seq (word_Assign 2 (word_Const (n2w 0))) (word_Return 0 [2]))
           word_Skip;
       word_Assign 20 (real_addr c 2);
       word_Assign 40 (real_addr c 4);
       word_Assign 21 (word_Load (word_Var 20));
       word_Assign 41 (word_Load (word_Var 40));
       word_If asm_Test 21 (Imm (n2w 0b1100)) (data_to_word_list_Seq
           [word_Assign 1 (word_Op asm_And [word_Var 21; word_Const
             (tag_mask c || (n2w 2))]);
            word_If asm_Equal 1 (Imm (n2w (16 * closure_tag + 2)))
              (word_Seq (word_Assign 2 (word_Const (n2w 1))) (word_Return 0
                [2])) word_Skip;
            word_If asm_Equal 1 (Imm (n2w (16 * partial_app_tag + 2)))
              (word_Seq (word_Assign 2 (word_Const (n2w 1))) (word_Return 0
                [2])) word_Skip;
            word_If asm_Equal 21 (Reg 41)
              word_Skip (word_Seq (word_Assign 2 (word_Const (n2w 0)))
                (word_Return 0 [2]));
            word_Assign 6 (ShiftVar Lsr 21 ((dimindex (:'a) -
              data_to_word_config_len_size c)));
            word_Assign 20 (word_Op asm_Add [word_Var 20; word_Const
              bytes_in_word]);
            word_Assign 40 (word_Op asm_Add [word_Var 40; word_Const
              bytes_in_word]);
            word_Call NONE (SOME Equal1_location) [0; 6; 20; 40] NONE])
         word_Skip;
       word_If asm_Equal 21 (Reg 41) word_Skip
         (word_Seq (word_Assign 2 (word_Const (n2w 0))) (word_Return 0
           [2]));
       word_If asm_Test 21 (Imm (n2w 4))
         (word_Seq (word_Assign 2 (word_Const (n2w 0))) (word_Return 0 [2]))
           word_Skip;
       word_Assign 1 (word_Op asm_And [word_Var 21; word_Const (n2w 24)]);
       word_If asm_Equal 1 (Imm (n2w 16))
         (word_Seq (word_Assign 2 (word_Const (n2w 0))) (word_Return 0 [2]))
           word_Skip;
       word_Assign 6 (ShiftVar Lsr 21 ((dimindex (:'a) -
         data_to_word_config_len_size c)));
       word_Assign 2 (word_Op asm_Add [word_Var 20; ShiftVar Lsl 6
         (backend_common_word_shift (:'a))]);
       word_Assign 4 (word_Op asm_Add [word_Var 40; ShiftVar Lsl 6
         (backend_common_word_shift (:'a))]);
       word_Call NONE (SOME Compare1_location) [0; 6; 2; 4] NONE]`;;

let LongDiv_code_def = new_definition
  `LongDiv_code c =
     if data_to_word_config_has_longdiv c then
       data_to_word_list_Seq [word_Inst (asm_Arith (asm_LongDiv 1 3 2 4 6));
                 word_Set (Temp (n2w 28)) (word_Var 3);
                 word_Return 0 [1]]
     else word_Seq (word_Assign 10 (word_Const ((n2w 0):'a word)))
      (word_Seq (word_Assign 11 (word_Const (n2w (dimindex (:'a)))))
           (word_Call NONE (SOME LongDiv1_location) [0; 11; 6; 10; 10; 4;
             2] NONE))`;;

let LongDiv1_code_def = new_definition
  `LongDiv1_code c =
     if data_to_word_config_has_longdiv c then word_Skip else
       // the following code is based on multiwordTheory.single_div_loop_def
       word_If asm_Test 2 (Reg 2)
         (word_Seq (word_Set (Temp (n2w 28)) (word_Var 10):'a word_prog)
           (word_Return 0 [8]))
         (data_to_word_list_Seq [word_Assign 6 (word_Op asm_Or [ShiftVar Lsr
           6 1;
                              ShiftVar Lsl 4 (dimindex (:'a) - 1)]);
                    word_Assign 4 (ShiftVar Lsr 4 1);
                    word_Assign 8 (ShiftVar Lsl 8 1);
                    word_Assign 2 (word_Op asm_Sub [word_Var 2; word_Const
                      ((n2w 1):'a word)]);
                    word_If asm_Lower 12 (Reg 4)
                      (word_Call NONE (SOME LongDiv1_location)
                        [0; 2; 4; 6; 8; 10; 12] NONE) word_Skip;
                    word_If asm_Equal 12 (Reg 4)
                      (word_If asm_Lower 10 (Reg 6)
                         (word_Call NONE (SOME LongDiv1_location)
                            [0; 2; 4; 6; 8; 10; 12] NONE) word_Skip)
                              word_Skip;
                    word_Assign 8 (word_Op asm_Add [word_Var 8; word_Const
                      (n2w 1)]);
                    word_Assign 16 (word_Op asm_Xor [word_Var 6; word_Const
                      (--(n2w 1))]);
                    word_Assign 14 (word_Op asm_Xor [word_Var 4; word_Const
                      (--(n2w 1))]);
                    word_Assign 1 (word_Const (n2w 1));
                    word_Inst (asm_Arith (asm_AddCarry 10 10 16 1));
                    word_Inst (asm_Arith (asm_AddCarry 12 12 14 1));
                    word_Call NONE (SOME LongDiv1_location) [0; 2; 4; 6;
                      8; 10; 12] NONE])`;;

let append_code_def = new_definition
  `Append_code c =
     (match encode_header c 0 2 with NONE -> (word_Skip:'a word_prog)
      | SOME (header:'a word) ->
         word_If asm_Test 4 (Imm (n2w 1)) (word_Return 0 [2])
           (data_to_word_list_Seq
             [word_Set (Temp (n2w 0)) (word_Var 2);
              word_Set (Temp (n2w 1)) (word_Var 4);
              word_Assign 1 (word_Lookup NextFree);
              word_Assign 3 (word_Const header);
              word_Assign 5 (word_Op asm_Sub [word_Lookup TriggerGC;
                word_Var 1]);
              word_Assign 7 (word_Op asm_Or [(\sh e n. word_Shift sh e
                (word_Const (n2w n))) Lsl (word_Op asm_Sub [word_Var 1;
                word_Lookup CurrHeap])
                              (shift_length c - backend_common_word_shift
                                (:'a));
                              word_Const ((n2w 1) || (word_bits
                                (small_shift_length c - 1) 0)
                              (ptr_bits c 0 2))]);
              word_Set (Temp (n2w 2)) (word_Var 7);
              word_Call NONE (SOME AppendMainLoop_location) [0; 1; 4; 3;
                5; 7] NONE]))`;;

let AppendMainLoop_code_def = new_definition
  `AppendMainLoop_code c =
     (data_to_word_list_Seq
       [word_Assign 1 (real_addr c 4);
        word_Assign 3 (word_Load (word_Op asm_Add [word_Var 1; word_Const
          bytes_in_word]));
        word_Assign 5 (word_Load (word_Op asm_Add [word_Var 1; word_Const
          ((n2w 2) * bytes_in_word)]));
        word_If asm_Lower 8 (Imm ((n2w 3) * bytes_in_word))
          (
           // unlucky case: GC is needed
           word_Seq (word_Assign 1 (word_Const (n2w 0)))
               (word_Call NONE (SOME AppendLenLoop_location) [0; 4; 1]
                 NONE)) word_Skip;
        word_Store (word_Var 2) 6;
        word_Store (word_Op asm_Add [word_Var 2; word_Const bytes_in_word])
          3;
        word_If asm_Test 5 (Imm (n2w 1)) word_Skip
          (
           // cons case:
           data_to_word_list_Seq
            [word_Assign 10 (word_Op asm_Add [word_Var 10;
               word_Const (n2w (3 * 2 EXP shift_length c))]);
             word_Assign 8 (word_Op asm_Sub [word_Var 8; word_Const ((n2w 3)
               * bytes_in_word)]);
             word_Store (word_Op asm_Add [word_Var 2; word_Const ((n2w 2) *
               bytes_in_word)]) 10;
             word_Assign 2 (word_Op asm_Add [word_Var 2; word_Const ((n2w 3)
               * bytes_in_word)]);
             word_Call NONE (SOME AppendMainLoop_location) [0; 2; 5; 6; 8;
               10] NONE]);
        // nil case
        word_Assign 1 (word_Lookup (Temp (n2w 0)));
        // arg 2 to append
        word_Assign 3 (word_Lookup (Temp (n2w 2)));
        // ret value
        word_Store (word_Op asm_Add [word_Var 2; word_Const ((n2w 2) *
          bytes_in_word)]) 1;
        word_Set NextFree (word_Op asm_Add [word_Var 2; word_Const ((n2w 3)
          * bytes_in_word)]);
        word_Return 0 [3]]:'a word_prog)`;;

let AppendLenLoop_code_def = new_definition
  `AppendLenLoop_code c =
     word_If asm_Test 2 (Imm (n2w 1))
       (data_to_word_list_Seq
         [word_Assign 1 (word_Op asm_Sub [word_Lookup TriggerGC; word_Lookup
           NextFree]);
          word_Assign 1 (word_Op asm_Add [word_Var 4; ShiftVar Lsr 1
            (backend_common_word_shift (:'a) - 2)]);
          word_Assign 4 (word_Lookup (Temp (n2w 0)));
          word_Assign 2 (word_Lookup (Temp (n2w 1)));
          AllocVar c (dimword (:'a) DIV 8 - 1) (sptree_fromList [one; one]);
          word_Call NONE (SOME Append_location) [0; 4; 2] NONE])
       (data_to_word_list_Seq
         [word_Assign 2 (word_Load (word_Op asm_Add [real_addr c 2;
           word_Const ((n2w 2) * bytes_in_word)]));
          word_Assign 4 (word_Op asm_Add [word_Var 4; word_Const ((n2w
            12):'a word)]);
          word_Call NONE (SOME AppendLenLoop_location) [0; 2; 4] NONE])`;;

let XorLoop_code_def = new_definition
  `XorLoop_code =
     (word_If asm_Lower 6 (Imm (n2w 2))
       (word_If asm_Equal 6 (Imm (n2w 0))
          (data_to_word_list_Seq [word_Assign 1 (word_Const (n2w 2));
                     word_Return 0 [1]])
          (data_to_word_list_Seq [word_Assign 5 (word_Load (word_Var 4));
                     word_Assign 3 (word_Load (word_Var 2));
                     word_Assign 7 (word_Op asm_Xor [word_Var 5; word_Var
                       3]);
                     word_Store (word_Var 2) 7;
                     word_Assign 1 (word_Const (n2w 2));
                     word_Return 0 [1]]))
       (data_to_word_list_Seq [word_Assign 5 (word_Load (word_Var 4));
                  word_Assign 3 (word_Load (word_Var 2));
                  word_Assign 9 (word_Load (word_Op asm_Add [word_Var 4;
                    word_Const bytes_in_word]));
                  word_Assign 7 (word_Load (word_Op asm_Add [word_Var 2;
                    word_Const bytes_in_word]));
                  word_Assign 6 (word_Op asm_Sub [word_Var 6; word_Const
                    (n2w 2)]);
                  word_Assign 5 (word_Op asm_Xor [word_Var 5; word_Var 3]);
                  word_Assign 9 (word_Op asm_Xor [word_Var 9; word_Var 7]);
                  word_Store (word_Var 2) 5;
                  word_Store (word_Op asm_Add [word_Var 2; word_Const
                    bytes_in_word]) 9;
                  word_Assign 4 (word_Op asm_Add [word_Var 4; word_Const
                    ((n2w 2) * bytes_in_word)]);
                  word_Assign 2 (word_Op asm_Add [word_Var 2; word_Const
                    ((n2w 2) * bytes_in_word)]);
                  word_Call NONE (SOME XorLoop_location) [0; 2; 4; 6]
                    NONE]):'a word_prog)`;;

let StringCmpLoop_code_def = new_definition
  `StringCmpLoop_code =
     (word_If asm_Equal 6 (Imm bytes_in_word)
       (word_Return 0 [8; 10])
       (data_to_word_list_Seq
          [word_Inst (asm_Mem asm_Load8 1 (Addr 2 (n2w 0)));
           word_Inst (asm_Mem asm_Load8 3 (Addr 4 (n2w 0)));
           word_If asm_NotEqual 1 (Reg 3) (word_Return 0 [1; 3]) word_Skip;
           word_Assign 2 (word_Op asm_Add [word_Var 2; word_Const (n2w 1)]);
           word_Assign 4 (word_Op asm_Add [word_Var 4; word_Const (n2w 1)]);
           word_Assign 6 (word_Op asm_Sub [word_Var 6; word_Const (n2w 1)]);
           word_Call NONE (SOME StringCmpLoop_location) [0; 2; 4; 6; 8;
             10] NONE]):'a word_prog)`;;

let data_to_word_get_names_def = define_cases
  `(data_to_word_get_names NONE = LN) /\
   (data_to_word_get_names (SOME x) = x)`;;

let LoadWord64_def = new_definition
  `LoadWord64 c i j =
     (word_Assign i (word_Load (word_Op asm_Add [real_addr c j;
       word_Const bytes_in_word])):'a word_prog)`;;

let LoadBignum_def = new_definition
  `LoadBignum c header word1' k = (data_to_word_list_Seq [
     word_Assign word1' (real_addr c k);
     word_Assign header (word_Load (word_Var word1'));
     word_Assign word1' (word_Load (word_Op asm_Add [word_Var word1';
       word_Const bytes_in_word]))]:'a word_prog)`;;

let WriteWord64_def = new_definition
  `// also works for storing bignums of length 1
   WriteWord64 c (header:'a word) dest i =
     (data_to_word_list_Seq [word_Assign 1 (word_Lookup NextFree);
               word_Store (word_Op asm_Add [word_Var 1; word_Const
                 bytes_in_word]) i;
               word_Assign 3 (word_Const header);
               word_Store (word_Var 1) 3;
               word_Set NextFree (word_Op asm_Add [word_Var 1; word_Const
                 ((n2w 2) * bytes_in_word)]);
               word_Assign (adjust_var dest)
                 (word_Op asm_Or [(\sh e n. word_Shift sh e (word_Const (n2w
                   n))) Lsl (word_Op asm_Sub [word_Var 1; word_Lookup
                   CurrHeap])
                           (shift_length c - backend_common_word_shift
                             (:'a));
                         word_Const (n2w 1)])]:'a word_prog)`;;

let WriteWord64_on_32_def = new_definition
  `WriteWord64_on_32 c (header:'a word) dest i1 i2 =
     (data_to_word_list_Seq [word_Assign 1 (word_Lookup NextFree);
               word_Store (word_Op asm_Add [word_Var 1; word_Const
                 bytes_in_word]) i2;
               word_Store (word_Op asm_Add [word_Var 1; word_Const ((n2w 2)
                 * bytes_in_word)]) i1;
               word_Assign 3 (word_Const header);
               word_Store (word_Var 1) 3;
               word_Set NextFree (word_Op asm_Add [word_Var 1; word_Const
                 ((n2w 3) * bytes_in_word)]);
               word_Assign (adjust_var dest)
                 (word_Op asm_Or [(\sh e n. word_Shift sh e (word_Const (n2w
                   n))) Lsl (word_Op asm_Sub [word_Var 1; word_Lookup
                   CurrHeap])
                           (shift_length c - backend_common_word_shift
                             (:'a));
                         word_Const (n2w 1)])]:'a word_prog)`;;

let WriteWord32_on_32_def = new_definition
  `WriteWord32_on_32 c header dest i1 =
      data_to_word_list_Seq
        [word_Assign 1 (word_Lookup NextFree);
         word_Store (word_Op asm_Add [word_Var 1; word_Const bytes_in_word])
           i1;
         word_Assign 3 (word_Const header); word_Store (word_Var 1) 3;
         word_Set NextFree (word_Op asm_Add [word_Var 1; word_Const ((n2w 2)
           * bytes_in_word)]);
         word_Assign (adjust_var dest)
           (word_Op asm_Or
              [(\sh e n. word_Shift sh e (word_Const (n2w n))) Lsl (word_Op
                asm_Sub [word_Var 1; word_Lookup CurrHeap])
                 (shift_length c - backend_common_word_shift (:'a));
                   word_Const ((n2w 1):'a word)])]`;;

let WordOp64_on_32_def = new_definition
  `WordOp64_on_32 (opw:opw) =
     match opw with backend_common_Andw -> data_to_word_list_Seq
       [word_Assign 29 (word_Const (n2w 0));
                         word_Assign 27 (word_Const (n2w 0));
                         word_Assign 33 (word_Op asm_And [word_Var 13;
                           word_Var 23]);
                         word_Assign 31 (word_Op asm_And [word_Var 11;
                           word_Var 21])]
     | backend_common_Orw -> data_to_word_list_Seq [word_Assign 29
       (word_Const (n2w 0));
                         word_Assign 27 (word_Const (n2w 0));
                         word_Assign 33 (word_Op asm_Or [word_Var 13;
                           word_Var 23]);
                         word_Assign 31 (word_Op asm_Or [word_Var 11;
                           word_Var 21])]
     | backend_common_Xor -> data_to_word_list_Seq [word_Assign 29
       (word_Const (n2w 0));
                         word_Assign 27 (word_Const (n2w 0));
                         word_Assign 33 (word_Op asm_Xor [word_Var 13;
                           word_Var 23]);
                         word_Assign 31 (word_Op asm_Xor [word_Var 11;
                           word_Var 21])]
     | backend_common_Add -> data_to_word_list_Seq [word_Assign 29
       (word_Const (n2w 0));
                         word_Assign 27 (word_Const (n2w 0));
                         word_Inst (asm_Arith (asm_AddCarry 33 13 23 29));
                         word_Inst (asm_Arith (asm_AddCarry 31 11 21 29))]
     | backend_common_Sub -> data_to_word_list_Seq [word_Assign 29
       (word_Const (n2w 1));
                         word_Assign 27 (word_Op asm_Xor [word_Const (--(n2w
                           1)); word_Var 23]);
                         word_Inst (asm_Arith (asm_AddCarry 33 13 27 29));
                         word_Assign 27 (word_Op asm_Xor [word_Const (--(n2w
                           1)); word_Var 21]);
                         word_Inst (asm_Arith (asm_AddCarry 31 11 27
                           29))]`;;

let WordShift64_on_32_def = new_definition
  `WordShift64_on_32 sh n = data_to_word_list_Seq
     (
      // inputs in 11 and 13, writes results in 31 and 33
      if sh = Ror then
       (let n = n MOD 64 in
         (if n < 32 then
            [word_Assign 33 (word_Op asm_Or [ShiftVar Lsl 11 (32 - n);
                              ShiftVar Lsr 13 n]);
             word_Assign 31 (word_Op asm_Or [ShiftVar Lsl 13 (32 - n);
                              ShiftVar Lsr 11 n])]
          else [word_Assign 33 (word_Op asm_Or [ShiftVar Lsl 13 (64 - n);
                              ShiftVar Lsr 11 (n - 32)]);
             word_Assign 31 (word_Op asm_Or [ShiftVar Lsl 11 (64 - n);
                              ShiftVar Lsr 13 (n - 32)])]))
     else if n < 32 then
         (match sh with Lsl -> [word_Assign 33 (ShiftVar sh 13 n);
                    word_Assign 31 (word_Op asm_Or [ShiftVar Lsr 13 (32 -
                      n);
                              ShiftVar sh 11 n])]
          | Lsr -> [word_Assign 33 (word_Op asm_Or [ShiftVar Lsl 11 (32 -
            n);
                              ShiftVar sh 13 n]);
                    word_Assign 31 (ShiftVar sh 11 n)]
          | Asr -> [word_Assign 33 (word_Op asm_Or [ShiftVar Lsl 11 (32 -
            n);
                              ShiftVar Lsr 13 n]);
                    word_Assign 31 (ShiftVar sh 11 n)]
          | Ror -> [])
       else (match sh with Lsl -> [word_Assign 33 (word_Const (n2w 0));
         word_Assign 31 (ShiftVar sh 13 (n - 32))]
          | Lsr -> [word_Assign 33 (ShiftVar sh 11 (n - 32)); word_Assign 31
            (word_Const (n2w 0))]
          | Asr -> [word_Assign 33 (ShiftVar sh 11 (n - 32));
                    word_Assign 31 (ShiftVar sh 11 32)]
          | Ror -> []))`;;

let smallnum_def = new_definition
  `Smallnum i =
     if i < (&0) then (n2w 0) - n2w (num_of_int ((&4) * ((&0) - i))) else
       n2w (num_of_int ((&4) * i))`;;

(* HOL4 data_to_wordScript.sml:1099: the overload FALSE_CONST, which the
   port expands *)
(* HOL4 data_to_wordScript.sml:1100: the overload TRUE_CONST, which the port
   expands *)

let MemEqList_def,MemEqList_ind = define_rec
  `(MemEqList a [] = (word_Assign 1 (word_Const (n2w 18:'a word)):'a
    word_prog)) /\
   (MemEqList a (CONS w ws) =
         ((word_Seq (word_Assign 5 (word_Load (word_Op asm_Add [word_Var 3;
             word_Const a])))
             (word_If asm_Equal 5 (Imm w) (MemEqList (a +
                 bytes_in_word) ws) word_Skip)):'a word_prog))`;;

let get_gen_size_def = define_cases
  `(get_gen_size [] = bytes_in_word * ((--(n2w 1)):'a word)) /\
   (get_gen_size (CONS x xs) =
         if w2n (bytes_in_word:'a word) * x < dimword (:'a) then
             bytes_in_word * n2w x
         else bytes_in_word * (--(n2w 1)))`;;

let fp_cmp_inst_def = define_cases
  `(fp_cmp_inst FP_Less = FPLess 3 0 1) /\
   (fp_cmp_inst FP_LessEqual = FPLessEqual 3 0 1) /\
   (fp_cmp_inst FP_Greater = FPLess 3 1 0) /\
   (fp_cmp_inst FP_GreaterEqual = FPLessEqual 3 1 0) /\
   (fp_cmp_inst FP_Equal = FPEqual 3 0 1)`;;

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
  `fp_uop_inst x1' =
   match x1' with
     fpSem_FP_Neg -> FPNeg 1 0
   | fpSem_FP_Abs -> FPAbs 1 0
   | fpSem_FP_Sqrt -> FPSqrt 1 0`;;

let arg1_def = new_definition
  `data_to_word_arg1 vs f x = match vs with [v1] -> f v1 | _ -> x`;;

let arg2_def = new_definition
  `data_to_word_arg2 vs f x = match vs with [v1; v2] -> f v1 v2 | _ -> x`;;

let arg3_def = new_definition
  `arg3 vs f x = match vs with [v1; v2; v3] -> f v1 v2 v3 | _ -> x`;;

let arg4_def = new_definition
  `arg4 vs f x = match vs with [v1; v2; v3; v4] -> f v1 v2 v3 v4 | _ -> x`;;

let arg2_pmatch = prove
 (`data_to_word_arg2 vs f x = match vs with [v1; v2] -> f v1 v2 | _ -> x`,
  CHEAT_TAC);;

let arg3_pmatch = prove
 (`arg3 vs f x = match vs with [v1; v2; v3] -> f v1 v2 v3 | _ -> x`,
  CHEAT_TAC);;

let arg4_pmatch = prove
 (`arg4 vs f x = match vs with [v1; v2; v3; v4] -> f v1 v2 v3 v4 | _ -> x`,
  CHEAT_TAC);;

(* HOL4 data_to_wordScript.sml:1176-1180: ML code, not ported *)

let assign_Const_def = new_definition
  `assign_Const i (l:num) (dest:num) =
         // bvl_to_bvi compilation ensures that all literal
         // constants fit into a machine word
         if i < (&0) then (word_Assign (adjust_var dest) (word_Const ((n2w
           0) - n2w (num_of_int ((&4) * ((&0) - i))))),l)
         else (word_Assign (adjust_var dest) (word_Const (n2w (num_of_int
           ((&4) * i)))),l):'a word_prog#num`;;

let assign_SetGlobalsPtr_def = new_definition
  `assign_SetGlobalsPtr (c:data_to_word_config) (l:num) (dest:num) v1 =
       ((word_Seq (word_Set Globals (word_Var (adjust_var v1)))
       (word_Seq (word_Set GlobReal (real_addr c (adjust_var v1)))
            (word_Assign (adjust_var dest) data_to_word_Unit)),l):'a
              word_prog#num)`;;

let assign_Global_def = new_definition
  `assign_Global (c:data_to_word_config) n (l:num) (dest:num) =
       ((word_Assign (adjust_var dest) (word_Load (word_Op asm_Add
         [word_Lookup GlobReal;
                              word_Const (bytes_in_word * n2w (n +
                                1))])),l):'a word_prog#num)`;;

let assign_SetGlobal_def = new_definition
  `assign_SetGlobal (c:data_to_word_config) n (l:num) (dest:num) v1 =
       ((word_Seq (word_Store (word_Op asm_Add [word_Lookup GlobReal;
         word_Const (bytes_in_word * n2w (n + 1))])
                   (adjust_var v1))
            (word_Assign (adjust_var dest) data_to_word_Unit),l):'a
              word_prog#num)`;;

let assign_El_def = new_definition
  `assign_El (c:data_to_word_config) (l:num) (dest:num) v1 v2 =
                          ((word_Assign (adjust_var dest)
                             (word_Load (word_Op asm_Add [real_addr c
                               (adjust_var v1);
                              real_offset c (adjust_var v2)])),l):'a
                                word_prog#num)`;;

let assign_ElemAt_def = new_definition
  `assign_ElemAt (c:data_to_word_config) n (l:num) (dest:num) v1 =
                          ((word_Assign (adjust_var dest)
                             (word_Load (word_Op asm_Add [real_addr c
                               (adjust_var v1);
                              word_Const (bytes_in_word +
                              bytes_in_word * n2w n)])),l):'a
                                word_prog#num)`;;

let assign_DerefByte_def = new_definition
  `assign_DerefByte (c:data_to_word_config) (l:num) (dest:num) v1 v2 =
          ((data_to_word_list_Seq [
             word_Assign 1 (word_Op asm_Add [real_addr c (adjust_var v1);
                              real_byte_offset (adjust_var v2)]);
             word_Inst (asm_Mem asm_Load8 3 (Addr 1 (n2w 0)));
             word_Assign (adjust_var dest) ((\sh e n. word_Shift sh e
               (word_Const (n2w n))) Lsl (word_Var 3) 2)],l):'a
               word_prog#num)`;;

let assign_Update_def = new_definition
  `assign_Update (c:data_to_word_config) (l:num) (dest:num) v1 v2 v3 =
                  ((word_Seq (word_Store (word_Op asm_Add [real_addr c
                    (adjust_var v1);
                              real_offset c (adjust_var v2)])
                              (adjust_var v3))
                       (word_Assign (adjust_var dest)
                         data_to_word_Unit),l):'a word_prog#num)`;;

let assign_UpdateThunk_def = new_definition
  `assign_UpdateThunk ev (c:data_to_word_config) (l:num) (dest:num) v1 v2 =
       ((match ev with NotEvaluated ->
            (word_Seq (word_Store (word_Op asm_Add [real_addr c (adjust_var
              v1);
                              word_Const bytes_in_word])
                        (adjust_var v2))
                 (word_Assign (adjust_var dest) data_to_word_Unit),l)
        | Evaluated ->
            (match encode_header c (8 + 6) 1 with NONE -> (GiveUp,l)
             | SOME (header:'a word) -> (data_to_word_list_Seq
                 [word_Assign 1 (real_addr c (adjust_var v1));
                  word_Assign 3 (word_Const header);
                  word_Store (word_Var 1) 3;
                  word_Store (word_Op asm_Add [word_Var 1; word_Const
                    bytes_in_word]) (adjust_var v2);
                  word_Assign (adjust_var dest)
                    data_to_word_Unit],l))):'a word_prog#num)`;;

let assign_UpdateByte_def = new_definition
  `assign_UpdateByte (c:data_to_word_config) (l:num) (dest:num) v1 v2 v3 =
       ((data_to_word_list_Seq [
           word_Assign 1 (word_Op asm_Add [real_addr c (adjust_var v1);
                             real_byte_offset (adjust_var v2)]);
           word_Assign 3 ((\sh e n. word_Shift sh e (word_Const (n2w n)))
             Lsr (word_Var (adjust_var v3)) 2);
           word_Inst (asm_Mem asm_Store8 3 (Addr 1 (n2w 0)));
           word_Assign (adjust_var dest) data_to_word_Unit],l):'a
             word_prog#num)`;;

let assign_ListAppend_def = new_definition
  `assign_ListAppend (c:data_to_word_config) (secn:num) (l:num) (dest:num)
  (names:(1 spt) option) v1 v2 =
          ((match encode_header c 0 2 with NONE -> (GiveUp,l)
           | SOME (header:'a word) ->
            ((word_MustTerminate
              (word_Call (SOME ([adjust_var dest],adjust_sets
                (data_to_word_get_names names),word_Skip,secn,l))
                 (SOME Append_location)
                    [adjust_var v2; adjust_var v1] NONE):'a word_prog),l
                      + 1)):'a word_prog#num)`;;

let assign_Cons_def = new_definition
  `assign_Cons (c:data_to_word_config) (l:num) (dest:num) tag args =
                   if LENGTH args = 0 then
                     if tag < dimword (:'a) DIV 16 then
                       (word_Assign (adjust_var dest) (word_Const (n2w (16 *
                         tag + 2))),l)
                     else (GiveUp,l)
                   else (
                      // tag is too big to be represented
                      match encode_header c (4 * tag) (LENGTH args) with
                        NONE -> (GiveUp,l)
                      | SOME (header:'a word) -> (data_to_word_list_Seq
                         [word_Assign 1 (word_Lookup NextFree);
                          word_Assign 3 (word_Const header);
                          StoreEach 1 (CONS 3 (MAP adjust_var args)) (n2w
                            0);
                          word_Assign (adjust_var dest)
                            (word_Op asm_Or [(\sh e n. word_Shift sh e
                              (word_Const (n2w n))) Lsl (word_Op asm_Sub
                              [word_Var 1; word_Lookup CurrHeap])
                              (shift_length c - backend_common_word_shift
                                (:'a));
                              word_Const ((n2w 1) ||
                              (word_bits (small_shift_length c - 1) 0)
                              (ptr_bits c tag (LENGTH args)))]);
                          word_Set NextFree (word_Op asm_Add [word_Var 1;
                            word_Const (bytes_in_word * n2w (LENGTH args
                              + 1))])],l)):'a word_prog#num`;;

let assign_MutCons_def = new_definition
  `assign_MutCons (c:data_to_word_config) (l:num) (dest:num) tag args =
     match data_to_word_config_gc_kind c with data_to_word_Generational _ ->
       (GiveUp,l)
     | _ -> (assign_Cons (c:data_to_word_config) (l:num) (dest:num) tag
       args:'a word_prog#num)`;;

let assign_ConfigGC_def = new_definition
  `assign_ConfigGC (c:data_to_word_config) (secn:num) (l:num) (dest:num)
  (names:(1 spt) option) v1 v2 =
              ((data_to_word_list_Seq [SilentFFI c 3 (adjust_sets
                (data_to_word_get_names names));
                         word_Assign 1 (word_Const (n2w 0));
                         word_Alloc 1 (adjust_sets (data_to_word_get_names
                           names));
                         // runs GC
                         SilentFFI c 3 (adjust_sets (data_to_word_get_names
                           names));
                         word_Assign (adjust_var dest) (word_Const (n2w
                           2))],l):'a word_prog#num)`;;

let getWords_def,getWords_ind = define_rec
  `(getWords [] aux = (REVERSE aux,[])) /\
   (getWords (CONS c cs) aux =
      match c with (b,word_Word w) -> getWords cs (CONS (b,w) aux)
      | _ -> (REVERSE aux,CONS c cs))`;;

(* the termination relation that HOL4 gives is
     MEASURE (\(r1,r2,r3,vs,v). LENGTH vs)
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 data_to_wordScript.sml:1349-1358: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let StoreAnyConsts_def,StoreAnyConsts_ind = define_guess_cheat
  `(StoreAnyConsts r1 r2 r3 [] v =
      word_Seq (word_Set NextFree (word_Var r2))
          (match SND v with word_Loc n _ -> word_LocValue r1 n
           | word_Word w -> word_Assign r1 (if FST v then word_Op asm_Add
               [word_Const w; word_Var r3]
                              else (word_Const w)))) /\
   (StoreAnyConsts r1 r2 r3 (CONS v vs) w =
      match ((SND v):'a word_loc) with word_Loc n _ ->
          data_to_word_list_Seq [word_LocValue r1 n;
                             word_Store (word_Var r2) r1;
                             word_Assign r2 (word_Op asm_Add [word_Var r2;
                                 word_Const bytes_in_word]);
                             StoreAnyConsts r1 r2 r3 vs w]
      | _ -> let (ws,vs1) = getWords (CONS v vs) [] in
               word_Seq (word_StoreConsts r2 r3 r2 r3 ws)
                   (StoreAnyConsts r1 r2 r3 vs1 w))`;;

let lookup_mem_def = new_definition
  `lookup_mem m a =
     match sptree_lookup a m with NONE -> (F,word_Word ((n2w 0):'a word))
     | SOME x -> x`;;

let byte_len_def = new_definition
  `byte_len (:'a) num_bytes =
     if dimindex (:'a) = 32 then num_bytes DIV 4 + 1
                            else num_bytes DIV 8 + 1`;;

let make_byte_header_def = new_definition
  `make_byte_header conf cmp_by_contents len =
   let tag = (if cmp_by_contents then (n2w 0b00111) else (n2w 0b10111)) in
     (if dimindex (:'a) = 32 then n2w (len + 4) << (dimindex (:'a) - 2 -
       data_to_word_config_len_size conf) || tag
      else n2w (len + 8) << (dimindex (:'a) - 3 -
        data_to_word_config_len_size conf) || tag):'a word`;;

let get_lowerbits_def = new_definition
  `get_lowerbits conf x2 =
     match x2 with
       word_Word w ->
        (((word_bits (small_shift_length conf - 1) 0) w) || (n2w 1))
     | _ -> (n2w 1)`;;

let make_cons_ptr_def = new_definition
  `make_cons_ptr conf nf tag len =
     word_Word (
             nf << (shift_length conf - backend_common_word_shift (:'a))
               || ((n2w 1):'a word) || get_lowerbits conf (word_Word
               (ptr_bits conf tag len)))`;;

let make_ptr_def = new_definition
  `make_ptr conf nf tag len =
     word_Word (nf << (shift_length conf - backend_common_word_shift
       (:'a)) || ((n2w 1):'a word))`;;

let write_bytes_def,write_bytes_ind = define_rec
  `(write_bytes bs [] be' = []) /\
   (write_bytes bs (CONS (w:'a word) ws) be' =
         let k = dimindex (:'a) DIV 8 in
              CONS (bytes_to_word k (n2w 0) bs w be') (write_bytes
                  (DROP k bs) ws be'))`;;

let small_int_def = new_definition
  `small_int (:'a) i <=>
     --(&(dimword (:'a) DIV 8)) <= i /\ i < (&(dimword (:'a) DIV 8):int)`;;

let part_to_words_def = define_cases
  `(part_to_words c m (clos_Int i) (offset:'a word) =
      (if small_int (:'a) i then SOME ((F,word_Word (Smallnum i)),[])
       else let (sign,ws) = i2mw i in
              match encode_header c (if sign then 7 else 3) (LENGTH ws)
                  with NONE -> NONE
              | SOME hd -> SOME ((T,(make_ptr c offset ((n2w 0):'a word)
                  (LENGTH ws))),
                              MAP (\w. (F,word_Word w)) (CONS hd ws)))) /\
   (part_to_words c m (clos_Con t ns) (offset:'a word) =
      (if NULL ns then
         if t < dimword (:'a) DIV 16 then SOME ((F,word_Word (n2w (16 * t +
             2))),[]) else NONE
       else match encode_header c (4 * t) (LENGTH ns) with NONE -> NONE
         | SOME hd -> SOME ((T,word_Word
                              (offset << (shift_length c -
                                  backend_common_word_shift (:'a)) +
                              (ptr_bits c t (LENGTH ns) || (n2w
                                  1)))),CONS (F,word_Word hd) (MAP
                                  (lookup_mem m) ns)))) /\
   (part_to_words c m (clos_W64 w) (offset:'a word) =
      (let ws = (if dimindex (:'a) < 64 then [((63 >< 32) w); ((31 >< 0)
          w)]
                 else [((63 >< 0) w):'a word]) in
         match encode_header c 3 (LENGTH ws) with NONE -> NONE
         | SOME hd -> SOME ((T,(make_ptr c offset ((n2w 0):'a word) (LENGTH
             ws))),
                            MAP (\w. (F,word_Word w)) (CONS hd ws)))) /\
   (part_to_words c m (clos_Str s) (offset:'a word) =
      (let bytes = MAP (n2w o ORD) (explode s) in
       let n = LENGTH bytes in
       let hd = make_byte_header c T n in
       let k = byte_len (:'a) n in
       let ws = write_bytes bytes (REPLICATE k (n2w 0))
           (data_to_word_config_be c) in
         if k < 2 EXP (dimindex (:'a) - 4) /\ k < 2 EXP
             data_to_word_config_len_size c then SOME ((T,(make_ptr c offset
             ((n2w 0):'a word) k)),
                    MAP (\w. (F,word_Word w)) (CONS hd ws))
         else NONE))`;;

let parts_to_words_def,parts_to_words_ind = define_rec
  `(parts_to_words c m i [] (off:'a word) = SOME (lookup_mem m (i -
    (1:num)),[])) /\
   (parts_to_words c m i (CONS x parts') (off:'a word) =
      match part_to_words c m x off with NONE -> NONE
      | SOME (w,xs) ->
        (match parts_to_words c (sptree_insert i w m) (i + 1) parts'
                 (off + bytes_in_word * n2w (LENGTH xs)) with NONE -> NONE
        | SOME (r,ys) -> SOME (r,APPEND xs ys)))`;;

let const_parts_to_words_def = new_definition
  `const_parts_to_words c parts' =
     parts_to_words c LN 0 parts' (n2w 0)`;;

let get_Word_def = new_definition
  `get_Word x1 =
   match x1 with
     word_Word w -> w
   | _ -> (n2w 0)`;;
add_simp get_Word_def;;

let assign_Build_def = new_definition
  `assign_Build (c:data_to_word_config) (secn:num) (l:num) (dest:num) (names:(1
  spt) option) ps =
     match const_parts_to_words c ps with NONE -> (GiveUp,l)
     | SOME (w,ws) ->
       ((data_to_word_list_Seq
         [word_Assign 1 (word_Lookup NextFree);
          word_Assign 3 ((\sh e n. word_Shift sh e (word_Const (n2w n))) Lsl
            (word_Op asm_Sub [word_Var 1; word_Lookup CurrHeap])
                     (shift_length c - backend_common_word_shift (:'a)));
          StoreAnyConsts (adjust_var dest) 1 3 ws w],l):'a word_prog#num)`;;

let assign_ConsExtend_def = new_definition
  `assign_ConsExtend (c:data_to_word_config) (secn:num) (l:num) (dest:num)
  (names:(1 spt) option) tag args =
         ((match args with (CONS old (CONS start' (CONS len (CONS tot
           rest)))) ->
           (match encode_header c (4 * tag) 0 with
              NONE -> (GiveUp,l)
            | SOME header ->
               let limit' = MIN (2 EXP data_to_word_config_len_size c)
                 (dimword (:'a) DIV 16) in
               let h = (\sh e n. word_Shift sh e (word_Const (n2w n))) Lsl
                 (word_Var (adjust_var tot))
                         (dimindex (:'a) - data_to_word_config_len_size c -
                           2) in
                 (data_to_word_list_Seq
                   [BignumHalt (adjust_var tot);
                    word_Assign 1 (word_Var (adjust_var tot));
                    AllocVar c limit' (list_insert args
                      (data_to_word_get_names names));
                    word_Assign 1 (word_Lookup NextFree);
                    word_Assign 5 (word_Op asm_Or [h; word_Const header]);
                    word_Assign 7 ((\sh e n. word_Shift sh e (word_Const
                      (n2w n))) Lsr (word_Var (adjust_var tot)) 2);
                    word_Assign 9 (word_Const (n2w tag));
                    StoreEach 1 (CONS 5 (MAP adjust_var rest)) (n2w 0);
                    Make_ptr_bits_code c 9 7 3;
                    word_Set NextFree (word_Op asm_Add [word_Var 1;
                      word_Const bytes_in_word;
                      (\sh e n. word_Shift sh e (word_Const (n2w n))) Lsl
                        (word_Var 7) (backend_common_word_shift (:'a))]);
                    word_Assign 15 (word_Var (adjust_var len));
                    word_Assign 13 (word_Op asm_Add [word_Var 1;
                      word_Const (bytes_in_word * n2w (LENGTH rest + 1))]);
                    word_Assign 11 (word_Op asm_Add [real_addr c (adjust_var
                      old);
                      word_Const bytes_in_word;
                      ShiftVar Lsl (adjust_var start')
                        (backend_common_word_shift (:'a) - 2)]);
                    word_If asm_Test 15 (Reg 15) (word_Assign (adjust_var
                      dest) (word_Var 3)) (data_to_word_list_Seq [
                      word_MustTerminate
                        (word_Call (SOME ([adjust_var dest],adjust_sets
                          (data_to_word_get_names names),
                              word_Skip,secn,l))
                           (SOME MemCopy_location) [15; 11; 13; 3]
                             NONE)])]),l + 1)
          | _ -> (word_Skip,l)):'a word_prog#num)`;;

let assign_Ref_def = new_definition
  `assign_Ref (c:data_to_word_config) (secn:num) (l:num) (dest:num) (names:(1
  spt) option) args =
           ((match encode_header c 2 (LENGTH args) with NONE -> (GiveUp,l)
               | SOME (header:'a word) -> (data_to_word_list_Seq
                  [word_Set TriggerGC (word_Op asm_Sub [word_Lookup
                    TriggerGC;
                      word_Const (bytes_in_word * n2w (LENGTH args + 1))]);
                   word_Assign 1 (word_Op asm_Sub [word_Lookup EndOfHeap;
                      word_Const (bytes_in_word * n2w (LENGTH args + 1))]);
                   word_Set EndOfHeap (word_Var 1);
                   word_Assign 3 (word_Const header);
                   StoreEach 1 (CONS 3 (MAP adjust_var args)) (n2w 0);
                   word_Assign (adjust_var dest)
                     (word_Op asm_Or [(\sh e n. word_Shift sh e (word_Const
                       (n2w n))) Lsl (word_Op asm_Sub [word_Var 1; word_Lookup
                       CurrHeap])
                              (shift_length c - backend_common_word_shift
                                (:'a));
                             word_Const (n2w 1)])],l)):'a word_prog#num)`;;

let assign_AllocThunk_def = new_definition
  `assign_AllocThunk (ev:thunk_mode) (c:data_to_word_config) (secn:num) (l:num)
  (dest:num) (names:(1 spt) option) arg =
           ((let tag = (match ev with Evaluated -> 8 + 6
                          | NotEvaluated -> 0 + 6) in
            match encode_header c tag 1 with NONE -> (GiveUp,l)
               | SOME (header:'a word) -> (data_to_word_list_Seq
                  [word_Set TriggerGC (word_Op asm_Sub [word_Lookup
                    TriggerGC;
                      word_Const (bytes_in_word * (n2w 2))]);
                   word_Assign 1 (word_Op asm_Sub [word_Lookup EndOfHeap;
                      word_Const (bytes_in_word * (n2w 2))]);
                   word_Set EndOfHeap (word_Var 1);
                   word_Assign 3 (word_Const header);
                   StoreEach 1 [3; adjust_var arg] (n2w 0);
                   word_Assign (adjust_var dest)
                     (word_Op asm_Or [(\sh e n. word_Shift sh e (word_Const
                       (n2w n))) Lsl (word_Op asm_Sub [word_Var 1; word_Lookup
                       CurrHeap])
                              (shift_length c - backend_common_word_shift
                                (:'a));
                             word_Const (n2w 1)])],l)):'a word_prog#num)`;;

let assign_RefByte_def = new_definition
  `assign_RefByte (c:data_to_word_config) (secn:num) (l:num) (dest:num)
  (names:(1 spt) option) immutable v1 v2 =
          ((word_Seq
            (word_Assign 1 (word_Const (if immutable then (n2w 0) else (n2w
              16))))
            (
             // n.b. this would have been better done with Set Temp
             (word_MustTerminate
              (word_Call (SOME ([adjust_var dest],adjust_sets
                (data_to_word_get_names names),word_Skip,secn,l))
                 (SOME RefByte_location)
                    [adjust_var v1; adjust_var v2; 1] NONE):'a
                      word_prog)),l + 1):'a word_prog#num)`;;

let assign_XorByte_def = new_definition
  `assign_XorByte (c:data_to_word_config) (secn:num) (l:num) (dest:num)
  (names:(1 spt) option) v1 v2 =
     ((data_to_word_list_Seq [
         word_Assign 1 (real_addr c (adjust_var v1));
         word_Assign 3 (real_addr c (adjust_var v2));
         word_Assign 5 (SmallLsr (word_Load (word_Var 3)) (dimindex (:'a) -
           data_to_word_config_len_size c));
         word_Assign 1 (word_Op asm_Add [word_Var 1; word_Const
           bytes_in_word]);
         word_Assign 3 (word_Op asm_Add [word_Var 3; word_Const
           (bytes_in_word:'a word)]);
         word_MustTerminate
           (word_Call
             (SOME ([adjust_var dest],adjust_sets (data_to_word_get_names
               names),word_Skip,secn,l))
             (SOME XorLoop_location) [1; 3; 5] NONE)],l + 1):'a
               word_prog#num)`;;

let SetBool_def = new_definition
  `SetBool dest cmp r ri =
   (word_If cmp r ri
      (word_Assign dest (word_Const (n2w 18:'a word)))
      (word_Assign dest (word_Const (n2w 2:'a word))):'a word_prog)`;;

let AssignCmp_def = define_cases
  `(AssignCmp dest (ast_Lt:opb) v1 v2 = (SetBool dest asm_Lower v1 (Reg
    v2):'a word_prog)) /\
   (AssignCmp dest (ast_Gt:opb) v1 v2 = ((SetBool dest asm_Lower v2 (Reg
    v1)):'a word_prog)) /\
   (AssignCmp dest (ast_Leq:opb) v1 v2 = ((SetBool dest asm_NotLower v2
    (Reg v1)):'a word_prog)) /\
   (AssignCmp dest (ast_Geq:opb) v1 v2 = ((SetBool dest asm_NotLower v1
    (Reg v2)):'a word_prog))`;;

let assign_StringCmp_def = new_definition
  `assign_StringCmp (c:data_to_word_config) (secn:num) (l:num) (dest:num)
  (names:(1 spt) option) (b:bool) (cmp:opb) v1 v2 =
     ((let k = (dimindex (:'a) - data_to_word_config_len_size c -
       backend_common_word_shift (:'a)) in
       data_to_word_list_Seq [
           word_Assign 1 (real_addr c (adjust_var v1));
           // address to header
           word_Assign 3 (real_addr c (adjust_var v2));
           // address to header
           word_Assign 5 ((\sh e n. word_Shift sh e (word_Const (n2w n)))
             Lsr (word_Load (word_Var 1)) k);
           // len + bytes_in_word
           word_Assign 7 ((\sh e n. word_Shift sh e (word_Const (n2w n)))
             Lsr (word_Load (word_Var 3)) k);
           (
            // len + bytes_in_word
            if b then
              word_If asm_Equal 5 (Reg 7)
                 (data_to_word_list_Seq
                  [word_Assign 11 (word_Op asm_Add [word_Var 1; word_Const
                    bytes_in_word]);
                   word_Assign 13 (word_Op asm_Add [word_Var 3; word_Const
                     bytes_in_word]);
                   word_MustTerminate
                   (word_Call (SOME ([5; 7],adjust_sets
                     (data_to_word_get_names names),word_Skip,secn,l))
                         (SOME StringCmpLoop_location) [11; 13; 7; 7; 7]
                           NONE)])
                 word_Skip
            else data_to_word_list_Seq
              [word_Assign 11 (word_Op asm_Add [word_Var 1; word_Const
                bytes_in_word]);
               word_Assign 13 (word_Op asm_Add [word_Var 3; word_Const
                 bytes_in_word]);
               word_Assign 9 (word_Var 5);
               word_If asm_Lower 7 (Reg 5) (word_Assign 9 (word_Var 7))
                 word_Skip;
               word_MustTerminate
               (word_Call (SOME ([5; 7],adjust_sets (data_to_word_get_names
                 names),word_Skip,secn,l))
                     (SOME StringCmpLoop_location) [11; 13; 9; 5; 7]
                       NONE)]);
           AssignCmp (adjust_var dest) cmp 5 7],l + 1):'a word_prog#num)`;;

let assign_CopyByte_def = new_definition
  `assign_CopyByte (c:data_to_word_config) (secn:num) (l:num) (dest:num)
  (names:(1 spt) option) args =
       ((match args with [v1; v2; v3; v4; v5] ->
            (
             // alloc_new is F
             (word_MustTerminate
              (word_Call (SOME ([adjust_var dest],adjust_sets
                (data_to_word_get_names names),word_Skip,secn,l))
                 (SOME ByteCopy_location)
                    [adjust_var v1; adjust_var v2; adjust_var v3;
                     adjust_var v4; adjust_var v5] NONE):'a word_prog),l +
                       1)
        | [v1; v2; v3] ->
            (
             // alloc_new is T
             (word_MustTerminate
              (word_Call (SOME ([adjust_var dest],adjust_sets
                (data_to_word_get_names names),word_Skip,secn,l))
                 (SOME ByteCopyNew_location)
                    [adjust_var v1; adjust_var v2;
                     adjust_var v3] NONE):'a word_prog),l + 1)
        | _ -> (word_Skip,l)):'a word_prog#num)`;;

let assign_RefArray_def = new_definition
  `assign_RefArray (c:data_to_word_config) (secn:num) (l:num) (dest:num)
  (names:(1 spt) option) v1 v2 =
       let limit' = MIN (2 EXP data_to_word_config_len_size c) (dimword
         (:'a) DIV 16) in
          (data_to_word_list_Seq
           [
           BignumHalt (adjust_var v1);
           word_Move 0 [(1,adjust_var v1)];
           AllocVar c limit' (list_insert [v1; v2] (data_to_word_get_names
             names));
           word_MustTerminate
             (word_Call (SOME ([adjust_var dest],adjust_sets
               (data_to_word_get_names names),word_Skip,secn,l))
                (SOME RefArray_location)
                   [adjust_var v1; adjust_var v2] NONE):'a word_prog],l +
                     1):'a word_prog#num`;;

let assign_FromList_def = new_definition
  `assign_FromList (c:data_to_word_config) (secn:num) (l:num) (dest:num)
  (names:(1 spt) option) tag v1 v2 =
        if encode_header c (4 * tag) 0 = (NONE:('a word) option) then
          (GiveUp,l) else (word_MustTerminate (data_to_word_list_Seq [
             word_Assign 1 (word_Const (n2w (16 * tag)));
             (word_Call (SOME ([adjust_var dest],adjust_sets
               (data_to_word_get_names names),word_Skip,secn,l))
                (SOME FromList_location)
                   [adjust_var v1; adjust_var v2; 1] NONE):'a
                     word_prog]),l + 1):'a word_prog#num`;;

let assign_LessConstSmall_def = new_definition
  `assign_LessConstSmall (l:num) (dest:num) i v1 =
                  ((word_If asm_Less (adjust_var v1) (Imm (n2w (4 * i)))
                     (word_Assign (adjust_var dest) (word_Const (n2w 18:'a
                       word)))
                     (word_Assign (adjust_var dest) (word_Const (n2w 2:'a
                       word))),l):'a word_prog#num)`;;

let assign_BoolTest_def = new_definition
  `assign_BoolTest (l:num) (dest:num) (test:test) v1 v2 =
                  ((word_If asm_Equal (adjust_var v1) (Reg (adjust_var v2))
                    (word_Assign (adjust_var dest) (word_Const (n2w 18:'a
                      word)))
                    (word_Assign (adjust_var dest) (word_Const (n2w 2:'a
                      word))),l):'a word_prog#num)`;;

let assign_BoolNot_def = new_definition
  `assign_BoolNot (l:num) (dest:num) v1 =
                  ((word_Assign (adjust_var dest)
                     (word_Op asm_Xor [word_Var (adjust_var v1);
                       word_Const (n2w 16)]),l):'a word_prog#num)`;;

let assign_WordTest_def = new_definition
  `assign_WordTest (l:num) (dest:num) (test:test) v1 v2 =
        (((match test with ast_Equal -> word_If asm_Equal (adjust_var v1)
          (Reg (adjust_var v2))
                              (word_Assign (adjust_var dest) (word_Const
                                (n2w 18:'a word)))
                              (word_Assign (adjust_var dest) (word_Const
                                (n2w 2:'a word)))
          | ast_Compare ast_Lt -> word_If asm_Lower (adjust_var v1) (Reg
            (adjust_var v2))
                              (word_Assign (adjust_var dest) (word_Const
                                (n2w 18:'a word)))
                              (word_Assign (adjust_var dest) (word_Const
                                (n2w 2:'a word)))
          | ast_Compare ast_Leq -> word_If asm_NotLower (adjust_var v2) (Reg
            (adjust_var v1))
                              (word_Assign (adjust_var dest) (word_Const
                                (n2w 18:'a word)))
                              (word_Assign (adjust_var dest) (word_Const
                                (n2w 2:'a word)))
          | _ -> word_Skip),l):'a word_prog#num)`;;

let assign_BoundsCheckByte_def = new_definition
  `assign_BoundsCheckByte (c:data_to_word_config) (secn:num) (l:num) (dest:num)
  (names:(1 spt) option) leq v1 v2 =
                    ((data_to_word_list_Seq [word_Assign 1
                              (let addr' = real_addr c (adjust_var v1) in
                              let header = word_Load addr' in
                              let extra = (if dimindex (:'a) = 32 then 2
                                else 3) in
                              let k = dimindex (:'a) -
                                data_to_word_config_len_size c - extra in
                              word_Op asm_Sub [(\sh e n. word_Shift sh e
                                (word_Const (n2w n))) Lsr header k; word_Const
                                bytes_in_word]);
                              word_Assign 3 (ShiftVar Ror (adjust_var v2)
                                2);
                              (if leq then word_If asm_NotLower 1 (Reg 3)
                                else word_If asm_Lower 3 (Reg 1))
                              (word_Assign (adjust_var dest) (word_Const
                                (n2w 18:'a word)))
                              (word_Assign (adjust_var dest) (word_Const
                                (n2w 2:'a word)))],l):'a word_prog#num)`;;

let assign_BoundsCheckArray_def = new_definition
  `assign_BoundsCheckArray (c:data_to_word_config) (secn:num) (l:num)
  (dest:num) (names:(1 spt) option) v1 v2 =
                    ((data_to_word_list_Seq [word_Assign 1
                              (let addr' = real_addr c (adjust_var v1) in
                              let header = word_Load addr' in
                              let k = dimindex (:'a) -
                                data_to_word_config_len_size c in
                              (\sh e n. word_Shift sh e (word_Const (n2w
                                n))) Lsr header k);
                              word_Assign 3 (ShiftVar Ror (adjust_var v2)
                                2);
                              word_If asm_Lower 3 (Reg 1)
                              (word_Assign (adjust_var dest) (word_Const
                                (n2w 18:'a word)))
                              (word_Assign (adjust_var dest) (word_Const
                                (n2w 2:'a word)))],l):'a word_prog#num)`;;

let assign_BoundsCheckBlock_def = new_definition
  `assign_BoundsCheckBlock (c:data_to_word_config) (secn:num) (l:num)
  (dest:num) (names:(1 spt) option) v1 v2 =
                    ((data_to_word_list_Seq [word_If asm_Test (adjust_var
                      v1) (Imm (n2w 1))
                              (word_Assign 1 (word_Const (n2w 0)))
                              (word_Assign 1
                              (let addr' = real_addr c (adjust_var v1) in
                              let header = word_Load addr' in
                              let k = dimindex (:'a) -
                                data_to_word_config_len_size c in
                              (\sh e n. word_Shift sh e (word_Const (n2w
                                n))) Lsr header k));
                              word_Assign 3 (ShiftVar Ror (adjust_var v2)
                                2);
                              word_If asm_Lower 3 (Reg 1)
                              (word_Assign (adjust_var dest) (word_Const
                                (n2w 18:'a word)))
                              (word_Assign (adjust_var dest) (word_Const
                                (n2w 2:'a word)))],l):'a word_prog#num)`;;

let assign_Equal_def = new_definition
  `assign_Equal (c:data_to_word_config) (secn:num) (l:num) (dest:num) (names:(1
  spt) option) v1 v2 =
         ((data_to_word_list_Seq [word_Assign 1 (word_Var (adjust_var v1));
                    word_Assign 3 (word_Var (adjust_var v2));
                    word_Assign 5 (word_Op asm_And [word_Var 1; word_Var
                      3]);
                    word_If asm_Test 5 (Imm (n2w 1)) word_Skip
                      (word_If asm_Equal 1 (Reg 3) word_Skip
                        (word_Seq (word_MustTerminate
                           (word_Call (SOME ([1],adjust_sets
                             (data_to_word_get_names names),word_Skip,secn,l))
                              (SOME Equal_location) [1; 3] NONE))
                           (word_Assign 3 (word_Const (n2w 1)))));
                    (word_If asm_Equal 1 (Reg 3)
                       (word_Assign (adjust_var dest) (word_Const (n2w 18:'a
                         word)))
                       (word_Assign (adjust_var dest) (word_Const (n2w
                         2:'a word))))],l + 1):'a word_prog#num)`;;

let assign_Less_def = new_definition
  `assign_Less (c:data_to_word_config) (secn:num) (l:num) (dest:num) (names:(1
  spt) option) v1 v2 =
         ((data_to_word_list_Seq [word_Assign 1 (word_Var (adjust_var v1));
                    word_Assign 3 (word_Var (adjust_var v2));
                    word_Assign 5 (word_Op asm_Or [word_Var 1; word_Var 3]);
                    word_If asm_Test 5 (Imm (n2w 1)) word_Skip
                      (word_Seq (word_MustTerminate
                           (word_Call (SOME ([1],adjust_sets
                             (data_to_word_get_names names),word_Skip,secn,l))
                              (SOME Compare_location) [1; 3] NONE))
                           (word_Assign 3 (word_Const (n2w 1))));
                    (word_If asm_Less 1 (Reg 3)
                       (word_Assign (adjust_var dest) (word_Const (n2w 18:'a
                         word)))
                       (word_Assign (adjust_var dest) (word_Const (n2w
                         2:'a word))))],l + 1):'a word_prog#num)`;;

let assign_LessEq_def = new_definition
  `assign_LessEq (c:data_to_word_config) (secn:num) (l:num) (dest:num)
  (names:(1 spt) option) v1 v2 =
         ((data_to_word_list_Seq [word_Assign 1 (word_Var (adjust_var v1));
                    word_Assign 3 (word_Var (adjust_var v2));
                    word_Assign 5 (word_Op asm_Or [word_Var 1; word_Var 3]);
                    word_If asm_Test 5 (Imm (n2w 1)) word_Skip
                      (word_Seq (word_MustTerminate
                           (word_Call (SOME ([1],adjust_sets
                             (data_to_word_get_names names),word_Skip,secn,l))
                              (SOME Compare_location) [1; 3] NONE))
                           (word_Assign 3 (word_Const (n2w 1))));
                    (word_If asm_NotLess 3 (Reg 1)
                       (word_Assign (adjust_var dest) (word_Const (n2w 18:'a
                         word)))
                       (word_Assign (adjust_var dest) (word_Const (n2w
                         2:'a word))))],l + 1):'a word_prog#num)`;;

let assign_LengthBlock_def = new_definition
  `assign_LengthBlock (c:data_to_word_config) (secn:num) (l:num) (dest:num)
  (names:(1 spt) option) v1 =
                         ((word_If asm_Test (adjust_var v1) (Imm (n2w 1))
                            (word_Assign (adjust_var dest) (word_Const (n2w
                              0)))
                            (word_Assign (adjust_var dest)
                              (let addr' = real_addr c (adjust_var v1) in
                              let header = word_Load addr' in
                              let k = dimindex (:'a) -
                                data_to_word_config_len_size c in
                              let len = (\sh e n. word_Shift sh e
                                (word_Const (n2w n))) Lsr header k in
                              ((\sh e n. word_Shift sh e (word_Const (n2w
                                n))) Lsl len 2))),l):'a word_prog#num)`;;

let assign_Length_def = new_definition
  `assign_Length (c:data_to_word_config) (secn:num) (l:num) (dest:num)
  (names:(1 spt) option) v1 =
                           ((word_Assign (adjust_var dest)
                              (let addr' = real_addr c (adjust_var v1) in
                              let header = word_Load addr' in
                              let k = dimindex (:'a) -
                                data_to_word_config_len_size c in
                              let len = (\sh e n. word_Shift sh e
                                (word_Const (n2w n))) Lsr header k in
                              ((\sh e n. word_Shift sh e (word_Const (n2w
                                n))) Lsl len 2)),l):'a word_prog#num)`;;

let assign_LengthByte_def = new_definition
  `assign_LengthByte (c:data_to_word_config) (secn:num) (l:num) (dest:num)
  (names:(1 spt) option) v1 =
             ((word_Assign (adjust_var dest)
                (let addr' = real_addr c (adjust_var v1) in
                 let header = word_Load addr' in
                 let k = dimindex (:'a) - backend_common_word_shift (:'a) -
                   data_to_word_config_len_size c in
                 let fakelen = (\sh e n. word_Shift sh e (word_Const (n2w
                   n))) Lsr header k in
                 let len = word_Op asm_Sub [fakelen; word_Const
                   bytes_in_word] in
                   ((\sh e n. word_Shift sh e (word_Const (n2w n))) Lsl
                     len 2)),l):'a word_prog#num)`;;

let assign_TagLenEq_def = new_definition
  `assign_TagLenEq (c:data_to_word_config) (secn:num) (l:num) (dest:num)
  (names:(1 spt) option) tag len v1 =
                         ((if len = 0 then
                            if tag < dimword (:'a) DIV 16 then
                              (word_If asm_Equal (adjust_var v1) (Imm (n2w
                                (16 * tag + 2)))
                              (word_Assign (adjust_var dest) (word_Const
                                (n2w 18:'a word)))
                              (word_Assign (adjust_var dest) (word_Const
                                (n2w 2:'a word))),l)
                            else (word_Assign (adjust_var dest) (word_Const
                              (n2w 2:'a word)),l)
                          else if tag < 2 EXP data_to_word_config_tag_bits c
                            - 1 /\
                              len < 2 EXP data_to_word_config_len_bits c - 1
                                then
                            (word_Seq
                              (word_Assign 1 (word_Op asm_And
                              [word_Var (adjust_var v1);
                              word_Const (all_ones
                                (data_to_word_config_len_bits c +
                                data_to_word_config_tag_bits c + 1) 0)]))
                              (word_If asm_Equal 1 (Imm (ptr_bits c tag len
                                || (n2w 1)))
                              (word_Assign (adjust_var dest) (word_Const
                                (n2w 18:'a word)))
                              (word_Assign (adjust_var dest) (word_Const
                                (n2w 2:'a word)))),l)
                          else match encode_header c (4 * tag) len with NONE
                            -> (word_Assign (adjust_var dest) (word_Const (n2w
                            2:'a word)),l)
                            | SOME h ->
                              (data_to_word_list_Seq
                              [word_Assign 1 (word_Const (n2w 0));
                              word_If asm_Test (adjust_var v1) (Imm (n2w 1))
                                word_Skip
                              (word_Assign 1 (word_Load (real_addr c
                                (adjust_var v1))));
                              word_If asm_Equal 1 (Imm h)
                              (word_Assign (adjust_var dest) (word_Const
                                (n2w 18:'a word)))
                              (word_Assign (adjust_var dest) (word_Const
                                (n2w 2:'a word)))],l)):'a word_prog#num)`;;

let assign_LenEq_def = new_definition
  `assign_LenEq (c:data_to_word_config) (secn:num) (l:num) (dest:num) (names:(1
  spt) option) len v1 =
                         ((if len = 0 then
                            (word_If asm_Test (adjust_var v1) (Imm (n2w 1))
                              (word_Assign (adjust_var dest) (word_Const
                                (n2w 18:'a word)))
                              (word_Assign (adjust_var dest) (word_Const
                                (n2w 2:'a word))),l)
                          else if len < 2 EXP data_to_word_config_len_bits c
                            - 1 then
                            (word_Seq
                              (word_Assign 1 (word_Op asm_And
                              [word_Var (adjust_var v1);
                              word_Const (all_ones
                                (data_to_word_config_len_bits c + 1) 0)]))
                              (word_If asm_Equal 1 (Imm (ptr_bits c 0 len ||
                                (n2w 1)))
                              (word_Assign (adjust_var dest) (word_Const
                                (n2w 18:'a word)))
                              (word_Assign (adjust_var dest) (word_Const
                                (n2w 2:'a word)))),l)
                          else if len < dimword (:'a) then
                            (data_to_word_list_Seq
                              [word_Assign 1 (word_Const (n2w 0));
                              word_If asm_Test (adjust_var v1) (Imm (n2w 1))
                                word_Skip
                              (word_Assign 1
                              (let addr' = real_addr c (adjust_var v1) in
                              let header = word_Load addr' in
                              let k = dimindex (:'a) -
                                data_to_word_config_len_size c in
                              let len = (\sh e n. word_Shift sh e
                                (word_Const (n2w n))) Lsr header k in
                              len));
                              word_If asm_Equal 1 (Imm (n2w len))
                              (word_Assign (adjust_var dest) (word_Const
                                (n2w 18:'a word)))
                              (word_Assign (adjust_var dest) (word_Const
                                (n2w 2:'a word)))],l)
                          else (word_Assign (adjust_var dest) (word_Const
                            (n2w 2:'a word)),l)):'a word_prog#num)`;;

let assign_TagEq_def = new_definition
  `assign_TagEq (c:data_to_word_config) (secn:num) (l:num) (dest:num) (names:(1
  spt) option) tag v1 =
                ((if tag < dimword (:'a) DIV 16 then
                  (data_to_word_list_Seq
                    [word_Assign 1 (word_Var (adjust_var v1));
                     word_If asm_Test (adjust_var v1) (Imm (n2w 1))
                       word_Skip
                       (word_Assign 1 (let v = adjust_var v1 in
                              let h = word_Load (real_addr c v) in
                              word_Op asm_And [h; word_Const (tag_mask c ||
                                (n2w 2))]));
                     word_If asm_Equal 1 (Imm (n2w (16 * tag + 2)))
                       (word_Assign (adjust_var dest) (word_Const (n2w 18:'a
                         word)))
                       (word_Assign (adjust_var dest) (word_Const (n2w 2:'a
                         word)))],l)
                 else (word_Assign (adjust_var dest) (word_Const (n2w
                   2:'a word)),l)):'a word_prog#num)`;;

let assign_Add_def = new_definition
  `assign_Add (c:data_to_word_config) (secn:num) (l:num) (dest:num) (names:(1
  spt) option) v1 v2 =
         ((data_to_word_list_Seq [
                    // perform addition
                    word_Inst (asm_Arith (asm_AddOverflow 1 (adjust_var v1)
                              (adjust_var v2) 3));
                    // or together bits of overflow flag, and the two inputs
                    word_Assign 3 (word_Op asm_Or [word_Var 3; word_Var
                      (adjust_var v1); word_Var (adjust_var v2)]);
                    // if the least significant bit is set, then bignum is needed
                    word_If asm_Test 3 (Imm (n2w 1)) word_Skip
                     (word_MustTerminate
                       (word_Call (SOME ([1],adjust_sets
                         (data_to_word_get_names names),word_Skip,secn,l))
                         (SOME Add_location) [adjust_var v1; adjust_var v2]
                           NONE));
                    word_Move 2 [(adjust_var dest,1)]],l + 1):'a
                      word_prog#num)`;;

let assign_Sub_def = new_definition
  `assign_Sub (c:data_to_word_config) (secn:num) (l:num) (dest:num) (names:(1
  spt) option) v1 v2 =
         ((data_to_word_list_Seq [
                    // perform subtraction
                    word_Inst (asm_Arith (asm_SubOverflow 1 (adjust_var v1)
                              (adjust_var v2) 3));
                    // or together bits of overflow flag, and the two inputs
                    word_Assign 3 (word_Op asm_Or [word_Var 3; word_Var
                      (adjust_var v1); word_Var (adjust_var v2)]);
                    // if the least significant bit is set, then bignum is needed
                    word_If asm_Test 3 (Imm (n2w 1)) word_Skip
                     (word_MustTerminate
                       (word_Call (SOME ([1],adjust_sets
                         (data_to_word_get_names names),word_Skip,secn,l))
                         (SOME Sub_location) [adjust_var v1; adjust_var v2]
                           NONE));
                    word_Move 2 [(adjust_var dest,1)]],l + 1):'a
                      word_prog#num)`;;

let assign_Mult_def = new_definition
  `assign_Mult (c:data_to_word_config) (secn:num) (l:num) (dest:num) (names:(1
  spt) option) v1 v2 =
         ((data_to_word_list_Seq [word_Assign 1 (ShiftVar Lsr (adjust_var
           v1) 1);
                    word_Inst (asm_Arith (asm_LongMul 3 1 1 (adjust_var
                      v2)));
                    word_Assign 3 (word_Op asm_Or [word_Var 3;
                              word_Op asm_And [word_Const (n2w 1);
                              word_Op asm_Or [word_Var (adjust_var v1);
                                word_Var (adjust_var v2)]]]);
                    word_Assign 1 (ShiftVar Lsr 1 1);
                    word_If asm_Equal 3 (Imm (n2w 0)) word_Skip
                      (word_MustTerminate
                        (word_Call (SOME ([1],adjust_sets
                          (data_to_word_get_names names),word_Skip,secn,l))
                         (SOME Mul_location) [adjust_var v1; adjust_var v2]
                           NONE));
                    word_Move 2 [(adjust_var dest,1)]],l + 1):'a
                      word_prog#num)`;;

let assign_Div_def = new_definition
  `assign_Div (c:data_to_word_config) (secn:num) (l:num) (dest:num) (names:(1
  spt) option) v1 v2 =
         ((data_to_word_list_Seq [
            word_Assign 1 (word_Op asm_Or [word_Var (adjust_var v1);
              word_Var (adjust_var v2)]);
            word_Assign 1 (word_Op asm_Or [word_Var 1; ShiftVar Lsr 1
              (dimindex (:'a) - 1)]);
            word_If asm_Test 1 (Imm ((n2w 1):'a word))
              (if data_to_word_config_has_div c then
                 data_to_word_list_Seq [word_Inst (asm_Arith (asm_Div 1
                   (adjust_var v1) (adjust_var v2)));
                           word_Assign (adjust_var dest) (ShiftVar Lsl 1 2)]
               else if data_to_word_config_has_longdiv c then
                 data_to_word_list_Seq [word_Assign 1 (word_Const (n2w 0));
                           word_Inst (asm_Arith (asm_LongDiv 1 3 1
                             (adjust_var v1) (adjust_var v2)));
                           word_Assign (adjust_var dest) (ShiftVar Lsl 1 2)]
               else data_to_word_list_Seq
                   [word_Assign 1 (word_Const (n2w 0));
                    word_MustTerminate
                     (word_Call (SOME ([1],adjust_sets
                       (data_to_word_get_names names),word_Skip,secn,l + 1))
                       (SOME LongDiv_location)
                         [1; adjust_var v1; adjust_var v2] NONE);
                    word_Assign (adjust_var dest) (ShiftVar Lsl 1 2)])
              (data_to_word_list_Seq
                 [word_MustTerminate
                    (word_Call (SOME ([1],adjust_sets
                      (data_to_word_get_names names),word_Skip,secn,l))
                       (SOME Div_location) [adjust_var v1; adjust_var v2]
                         NONE);
                  word_Move 2 [(adjust_var dest,1)]])],l + 2):'a
                    word_prog#num)`;;

let assign_Mod_def = new_definition
  `assign_Mod (c:data_to_word_config) (secn:num) (l:num) (dest:num) (names:(1
  spt) option) v1 v2 =
         ((data_to_word_list_Seq [
            word_Assign 1 (word_Op asm_Or [word_Var (adjust_var v1);
              word_Var (adjust_var v2)]);
            word_Assign 1 (word_Op asm_Or [word_Var 1; ShiftVar Lsr 1
              (dimindex (:'a) - 1)]);
            word_If asm_Test 1 (Imm ((n2w 1):'a word))
              (if data_to_word_config_has_div c then
                 data_to_word_list_Seq [word_Inst (asm_Arith (asm_Div 1
                   (adjust_var v1) (adjust_var v2)));
                           word_Inst (asm_Arith (asm_LongMul 3 1 1
                             (adjust_var v2)));
                           word_Assign (adjust_var dest)
                             (word_Op asm_Sub [word_Var (adjust_var v1);
                               word_Var 1])]
               else if data_to_word_config_has_longdiv c then
                 data_to_word_list_Seq [word_Assign 1 (word_Const (n2w 0));
                           word_Inst (asm_Arith (asm_LongDiv 1 3 1
                             (adjust_var v1) (adjust_var v2)));
                           word_Move 2 [(adjust_var dest,3)]]
               else data_to_word_list_Seq
                   [word_Assign 1 (word_Const (n2w 0));
                    word_MustTerminate
                     (word_Call (SOME ([1],adjust_sets
                       (data_to_word_get_names names),word_Skip,secn,l + 1))
                       (SOME LongDiv_location)
                         [1; adjust_var v1; adjust_var v2] NONE);
                    word_Get (adjust_var dest) (Temp (n2w 28))])
              (data_to_word_list_Seq
                 [word_MustTerminate
                    (word_Call (SOME ([1],adjust_sets
                      (data_to_word_get_names names),word_Skip,secn,l))
                       (SOME Mod_location) [adjust_var v1; adjust_var v2]
                         NONE);
                  word_Move 2 [(adjust_var dest,1)]])],l + 2):'a
                    word_prog#num)`;;

let assign_WordOpW8_def = new_definition
  `assign_WordOpW8 opw (c:data_to_word_config) (secn:num) (l:num) (dest:num)
  (names:(1 spt) option) v1 v2 =
            ((word_Assign (adjust_var dest)
             (match lookup_word_op opw with Bitwise op -> word_Op op
               [word_Var (adjust_var v1); word_Var (adjust_var v2)]
              | Carried op -> let k = dimindex (:'a) - 10 in
                (\sh e n. word_Shift sh e (word_Const (n2w n))) Lsr ((\sh e
                  n. word_Shift sh e (word_Const (n2w n))) Lsl
                  (word_Op op [word_Var (adjust_var v1); word_Var
                    (adjust_var v2)]) k) k),l):'a word_prog#num)`;;

let assign_WordOpW64_def = new_definition
  `assign_WordOpW64 opw (c:data_to_word_config) (secn:num) (l:num) (dest:num)
  (names:(1 spt) option) v1 v2 =
        ((if dimindex (:'a) = 64 then
          (match encode_header c 3 1 with NONE -> (GiveUp,l)
           | SOME (header:'a word) ->
                 (word_Seq (word_Assign 3
                   (word_Op (match opw with
                           backend_common_Andw -> asm_And
                         | backend_common_Orw -> asm_Or
                         | backend_common_Xor -> asm_Xor
                         | backend_common_Add -> asm_Add
                         | backend_common_Sub -> asm_Sub)
                          [word_Load
                             (word_Op asm_Add
                              [real_addr c (adjust_var v1);
                              word_Const bytes_in_word]);
                           word_Load
                             (word_Op asm_Add
                              [real_addr c (adjust_var v2);
                              word_Const bytes_in_word])]))
                    (WriteWord64 c header dest 3),l))
         else (match encode_header c 3 2 with NONE -> (GiveUp,l)
           | SOME header ->
             (data_to_word_list_Seq [
                word_Assign 15 (real_addr c (adjust_var v1));
                word_Assign 17 (real_addr c (adjust_var v2));
                word_Assign 11 (word_Load (word_Op asm_Add [word_Var 15;
                  word_Const bytes_in_word]));
                word_Assign 13 (word_Load (word_Op asm_Add [word_Var 15;
                  word_Const ((n2w 2) * bytes_in_word)]));
                word_Assign 21 (word_Load (word_Op asm_Add [word_Var 17;
                  word_Const bytes_in_word]));
                word_Assign 23 (word_Load (word_Op asm_Add [word_Var 17;
                  word_Const ((n2w 2) * bytes_in_word)]));
                WordOp64_on_32 opw;
                WriteWord64_on_32 c header dest 33 31],l))):'a
                  word_prog#num)`;;

let assign_WordShiftW8_def = new_definition
  `assign_WordShiftW8 sh n (c:data_to_word_config) (secn:num) (l:num)
  (dest:num) (names:(1 spt) option) v1 =
         ((word_Assign (adjust_var dest)
            (match sh with Lsl ->
               (\sh e n. word_Shift sh e (word_Const (n2w n))) Lsr
                 ((\sh e n. word_Shift sh e (word_Const (n2w n))) Lsl
                   (word_Var (adjust_var v1)) (dimindex (:'a) - 10 + (MIN n
                   8)))
                 (dimindex (:'a) - 10)
             | Lsr ->
               (\sh e n. word_Shift sh e (word_Const (n2w n))) Lsl
                 ((\sh e n. word_Shift sh e (word_Const (n2w n))) Lsr
                   (word_Var (adjust_var v1)) ((MIN n 8) + 2)) 2
             | Asr ->
               (\sh e n. word_Shift sh e (word_Const (n2w n))) Lsl
                 ((\sh e n. word_Shift sh e (word_Const (n2w n))) Lsr
                    ((\sh e n. word_Shift sh e (word_Const (n2w n))) Asr
                       ((\sh e n. word_Shift sh e (word_Const (n2w n))) Lsl
                         (word_Var (adjust_var v1)) (dimindex (:'a) - 10))
                       (MIN n 8))
                    (dimindex (:'a) - 8)) 2
             | Ror ->
               (let n = n MOD 8 in
                  word_Op asm_Or
                   [(\sh e n. word_Shift sh e (word_Const (n2w n))) Lsl
                     (ShiftVar Lsr (adjust_var v1) (n + 2)) 2;
                    (\sh e n. word_Shift sh e (word_Const (n2w n))) Lsr
                      (ShiftVar Lsl (adjust_var v1)
                      ((dimindex (:'a) - 2) - n)) (dimindex (:'a) -
                        10)])),l):'a word_prog#num)`;;

let assign_WordShiftW64_def = new_definition
  `assign_WordShiftW64 sh n (c:data_to_word_config) (secn:num) (l:num)
  (dest:num) (names:(1 spt) option) v1 =
          let len = (if dimindex (:'a) < 64 then 2 else 1) in
          (match encode_header c 3 len with NONE -> (GiveUp,l)
           | SOME (header:'a word) ->
             ((if len = 1 then
                data_to_word_list_Seq
                  [LoadWord64 c 3 (adjust_var v1);
                   word_Assign 3 (ShiftVar sh 3 n);
                   WriteWord64 c header dest 3]
              else data_to_word_list_Seq [
                  word_Assign 15 (real_addr c (adjust_var v1));
                  word_Assign 11 (word_Load (word_Op asm_Add [word_Var 15;
                    word_Const bytes_in_word]));
                  word_Assign 13 (word_Load (word_Op asm_Add [word_Var 15;
                    word_Const ((n2w 2) * bytes_in_word)]));
                  WordShift64_on_32 sh n;
                  WriteWord64_on_32 c header dest 33 31]),l)):'a
                    word_prog#num`;;

let assign_WordFromWord_def = new_definition
  `assign_WordFromWord b (c:data_to_word_config) (secn:num) (l:num) (dest:num)
  (names:(1 spt) option) v1 =
           if b then
             (data_to_word_list_Seq [word_Assign 1 (real_addr c (adjust_var
               v1));
                        word_Assign 1 (word_Load (word_Op asm_Add [word_Var
                          1;
                          word_Const (if dimindex (:'a) = 32 then (n2w 2) *
                            bytes_in_word else bytes_in_word)]));
                        word_Assign 1 (word_Op asm_And [word_Var 1;
                          word_Const (n2w 255)]);
                        word_Assign (adjust_var dest) (ShiftVar Lsl 1 2)],l)
           else (let
              len = (if dimindex (:'a) < 64 then 2 else 1) in
              match encode_header c 3 len with
                NONE -> (GiveUp,l)
              | SOME header ->
                 (if len = 1 then
                    (data_to_word_list_Seq [word_Assign 3 ((\sh e n.
                      word_Shift sh e (word_Const (n2w n))) Lsr (word_Var
                      (adjust_var v1)) 2);
                              WriteWord64 c header dest 3],l)
                  else (data_to_word_list_Seq [word_Assign 5 ((\sh e n.
                    word_Shift sh e (word_Const (n2w n))) Lsr (word_Var
                    (adjust_var v1)) 2);
                              word_Assign 3 (word_Const (n2w 0));
                              WriteWord64_on_32 c header dest 5
                                3],l))):'a word_prog#num`;;

let assign_WordFromInt_def = new_definition
  `assign_WordFromInt (c:data_to_word_config) (secn:num) (l:num) (dest:num)
  (names:(1 spt) option) v1 =
         let len = (if dimindex (:'a) < 64 then 2 else 1) in
         (match encode_header c 3 len with NONE -> (GiveUp,l)
          | SOME (header:'a word) ->
            (if len = 1 then
              word_Seq
                (
                 // put the word value into 3
                 word_If asm_Test (adjust_var v1) (Imm (n2w 1))
                     (
                      // smallnum case
                      word_Assign 3 ((\sh e n. word_Shift sh e (word_Const
                        (n2w n))) Asr (word_Var (adjust_var v1)) 2))
                    (
                     // bignum case
                     word_Seq
                      (LoadBignum c 1 3 (adjust_var v1))
                      (word_If asm_Test 1 (Imm (n2w 16)) word_Skip
                         (word_Assign 3 (word_Op asm_Sub [word_Const (n2w
                           0); word_Var 3])))))
                (WriteWord64 c header dest 3)
             else word_If asm_Test (adjust_var v1) (Imm (n2w 1))
               (data_to_word_list_Seq [
                 word_Assign 3 ((\sh e n. word_Shift sh e (word_Const (n2w
                   n))) Asr (word_Var (adjust_var v1)) 2);
                 word_Assign 5 ((\sh e n. word_Shift sh e (word_Const (n2w
                   n))) Asr (word_Var (adjust_var v1)) 31);
                 WriteWord64_on_32 c header dest 3 5])
               (data_to_word_list_Seq [
                 word_Assign 1 (real_addr c (adjust_var v1));
                 word_Assign 3 (word_Load (word_Var 1));
                 word_Assign 5 (word_Load (word_Op asm_Add [word_Var 1;
                   word_Const bytes_in_word]));
                 word_Assign 7 (ShiftVar Lsr 3 (dimindex (:'a) -
                   data_to_word_config_len_size c));
                 word_If asm_Equal 7 (Imm (n2w 1))
                   (
                    // bignum of length 1
                    word_If asm_Test 3 (Imm (n2w 16))
                     (
                      // positive case
                      word_Seq (word_Assign 9 (word_Const (n2w 0)))
                          (WriteWord64_on_32 c header dest 5 9))
                     (
                      // negative case
                      word_Seq (word_Assign 9 (word_Const (word_not (n2w
                        0))))
                     (word_Seq (word_Assign 5 (word_Op asm_Sub [word_Const
                       (n2w 0); word_Var 5]))
                          (WriteWord64_on_32 c header dest 5 9))))
                   (
                    // longer bignum
                    word_If asm_Test 3 (Imm (n2w 16))
                     (
                      // positive case
                      word_Seq (word_Assign 9 (word_Load
                            (word_Op asm_Add [word_Var 1; word_Const ((n2w
                              2) * bytes_in_word)])))
                          (WriteWord64_on_32 c header dest 5 9))
                     (
                      // negative case -- messy
                      data_to_word_list_Seq
                       [word_Assign 11 (word_Const (n2w 0));
                        word_Assign 13 (word_Const (n2w 1));
                        word_Assign 9 (word_Load
                          (word_Op asm_Add [word_Var 1; word_Const ((n2w 2)
                            * bytes_in_word)]));
                        word_Assign 5 (word_Op asm_Xor [word_Const (word_not
                          (n2w 0)); word_Var 5]);
                        word_Assign 9 (word_Op asm_Xor [word_Const (word_not
                          (n2w 0)); word_Var 9]);
                        word_Inst (asm_Arith (asm_AddCarry 15 11 5 13));
                        word_Inst (asm_Arith (asm_AddCarry 19 11 9 13));
                        WriteWord64_on_32 c header dest 15 19]))])),l):'a
                          word_prog#num`;;

let assign_WordToInt_def = new_definition
  `assign_WordToInt (c:data_to_word_config) (secn:num) (l:num) (dest:num)
  (names:(1 spt) option) v =
         let len = (if dimindex (:'a) < 64 then 2 else 1) in
         (match encode_header c 3 len with NONE -> (GiveUp,l)
            | SOME header ->
              (if len = 1 then
                (data_to_word_list_Seq [LoadWord64 c 3 (adjust_var v);
                           word_Assign 1 ((\sh e n. word_Shift sh e
                             (word_Const (n2w n))) Lsr (word_Var 3) 61);
                           word_If asm_Equal 1 (Imm (n2w 0))
                             (word_Assign (adjust_var dest) ((\sh e n.
                               word_Shift sh e (word_Const (n2w n))) Lsl
                               (word_Var 3) 2))
                             (WriteWord64 c header dest 3)],l)
              else (match encode_header c 3 1 with NONE -> (GiveUp,l)
                | SOME header1 ->
                  (data_to_word_list_Seq [
                   word_Assign 15 (real_addr c (adjust_var v));
                   word_Assign 13 (word_Load (word_Op asm_Add [word_Var 15;
                     word_Const bytes_in_word]));
                   word_Assign 11 (word_Load (word_Op asm_Add [word_Var 15;
                     word_Const ((n2w 2) * bytes_in_word)]));
                   word_If asm_NotEqual 13 (Imm (n2w 0))
                     (WriteWord64_on_32 c header dest 13 11)
                     (data_to_word_list_Seq [
                       word_Assign 1 ((\sh e n. word_Shift sh e (word_Const
                         (n2w n))) Lsr (word_Var 11) 29);
                       word_If asm_Equal 1 (Imm (n2w 0))
                         (word_Assign (adjust_var dest) ((\sh e n.
                           word_Shift sh e (word_Const (n2w n))) Lsl (word_Var
                           11) 2))
                         (WriteWord32_on_32 c header1 dest
                           11)])],l)))):'a word_prog#num`;;

let assign_FFI_def = new_definition
  `assign_FFI ffi_index (c:data_to_word_config) (secn:num) (l:num) (dest:num)
  (names:(1 spt) option) v1 v2 =
       if ~(data_to_word_config_call_empty_ffi c) /\ ffi_index = (implode
         "") then (word_Assign (adjust_var dest) data_to_word_Unit,l) else let
         addr1 = real_addr c (adjust_var v1) in
         let header1 = word_Load addr1 in
         let k = dimindex (:'a) - backend_common_word_shift (:'a) -
           data_to_word_config_len_size c in
         let fakelen1 = (\sh e n. word_Shift sh e (word_Const (n2w n))) Lsr
           header1 k in
         let addr2 = real_addr c (adjust_var v2) in
         let header2 = word_Load addr2 in
         let fakelen2 = (\sh e n. word_Shift sh e (word_Const (n2w n))) Lsr
           header2 k in
         (
         data_to_word_list_Seq [
           word_Assign 1 (word_Op asm_Add [addr1; word_Const
             bytes_in_word]);
           word_Assign 3 (word_Op asm_Sub [fakelen1; word_Const
             bytes_in_word]);
           word_Assign 5 (if ffi_index = (implode "") then word_Const (n2w
             0) else (word_Op asm_Add [addr2; word_Const bytes_in_word]));
           word_Assign 7 (if ffi_index = (implode "") then word_Const (n2w
             0) else (word_Op asm_Sub [fakelen2; word_Const bytes_in_word]));
           word_FFI ffi_index 1 3 5 7 (adjust_sets (match names with SOME
             names -> names | NONE -> LN));
           word_Assign (adjust_var dest) data_to_word_Unit],l):'a
             word_prog#num`;;

let assign_EqualConst_def = new_definition
  `assign_EqualConst p (c:data_to_word_config) (secn:num) (l:num) (dest:num)
  (names:(1 spt) option) v =
     match part_to_words c LN p (n2w 0) with SOME ((F,w),_) ->
         (word_If asm_Equal (adjust_var v) (Imm (get_Word w))
                     (word_Assign (adjust_var dest) (word_Const (n2w 18:'a
                       word)))
                     (word_Assign (adjust_var dest) (word_Const (n2w 2:'a
                       word))),l)
     | SOME (_,words) ->
         ((match p with clos_Int _ -> word_If asm_Test (adjust_var v) (Imm
           (n2w 1))
                        (word_Assign (adjust_var dest) (word_Const (n2w 2:'a
                          word)))
                        (data_to_word_list_Seq
                           [word_Assign 1 (word_Const (n2w 2:'a word));
                            word_Assign 3 (real_addr c (adjust_var v));
                            MemEqList (n2w 0) (MAP (get_Word o SND) words);
                            word_Assign (adjust_var dest) (word_Var 1)])
           | clos_W64 _ -> (data_to_word_list_Seq
                           [word_Assign 1 (word_Const (n2w 2:'a word));
                            word_Assign 3 (word_Op asm_Add [real_addr c
                              (adjust_var v);
                              word_Const bytes_in_word]);
                            MemEqList (n2w 0) (MAP (get_Word o SND) (TL
                              words));
                            word_Assign (adjust_var dest) (word_Var 1)])
           | clos_Str _ -> (data_to_word_list_Seq
                           [word_Assign 1 (word_Const (n2w 2:'a word));
                            word_Assign 3 (real_addr c (adjust_var v));
                            MemEqList (n2w 0) (MAP (get_Word o SND) words);
                            word_Assign (adjust_var dest) (word_Var 1)])
           | _ -> word_Skip),l)
     | _ -> ((word_Assign (adjust_var dest) (word_Const (n2w 2:'a
       word)),l):'a word_prog#num)`;;

let assign_Install_def = new_definition
  `assign_Install (c:data_to_word_config) (secn:num) (l:num) (dest:num)
  (names:(1 spt) option) v1 v2 v3 v4 =
         ((data_to_word_list_Seq [BignumHalt (adjust_var v3);
                    // length must be smallint
                    BignumHalt (adjust_var v4);
                    // length must be smallint
                    word_Assign 1 (word_Lookup BitmapBuffer);
                    word_Assign 3 (word_Op asm_Sub [word_Lookup
                      BitmapBufferEnd; word_Var 1]);
                    word_Assign 5 (ShiftVar Lsr (adjust_var v4) 2);
                    word_Assign 3 (ShiftVar Lsr 3 (backend_common_word_shift
                      (:'a)));
                    word_If asm_Lower 3 (Reg 5)
                            // too little data space
                            GiveUp word_Skip;
                    word_Assign 1 (word_Lookup CodeBuffer);
                    word_Assign 3 (word_Op asm_Sub [word_Lookup
                      CodeBufferEnd; word_Var 1]);
                    word_Assign 5 (ShiftVar Lsr (adjust_var v3) 2);
                    word_If asm_Lower 3 (Reg 5)
                            // too little code space
                            GiveUp word_Skip;
                    word_MustTerminate
                     (word_Call (SOME ([adjust_var dest],
                        adjust_sets (data_to_word_get_names
                          names),word_Skip,secn,l))
                     (SOME InstallCode_location)
                       [adjust_var v1; adjust_var v2; 1] NONE)],l + 1):'a
                         word_prog#num)`;;

let assign_FP_cmp_def = new_definition
  `assign_FP_cmp fpc (c:data_to_word_config) (secn:num) (l:num) (dest:num)
  (names:(1 spt) option) v1 v2 =
        ((if ~(data_to_word_config_has_fp_ops c) then (GiveUp,l) else if
          dimindex (:'a) = 64 then
            ((data_to_word_list_Seq [
                word_Assign 3 (word_Load (word_Op asm_Add
                            [real_addr c (adjust_var v1); word_Const
                              bytes_in_word]));
                word_Assign 5 (word_Load (word_Op asm_Add
                            [real_addr c (adjust_var v2); word_Const
                              bytes_in_word]));
                word_Inst (asm_FP (FPMovFromReg 0 3 3));
                word_Inst (asm_FP (FPMovFromReg 1 5 5));
                word_Inst (asm_FP (fp_cmp_inst fpc));
                word_Assign (adjust_var dest) (word_Op asm_Add [ShiftVar Lsl
                  3 4; word_Const (n2w 2)])],l))
         else ((data_to_word_list_Seq [
                word_Assign 15 (real_addr c (adjust_var v1));
                word_Assign 17 (real_addr c (adjust_var v2));
                word_Assign 11 (word_Load (word_Op asm_Add [word_Var 15;
                  word_Const bytes_in_word]));
                word_Assign 13 (word_Load (word_Op asm_Add [word_Var 15;
                  word_Const ((n2w 2) * bytes_in_word)]));
                word_Assign 21 (word_Load (word_Op asm_Add [word_Var 17;
                  word_Const bytes_in_word]));
                word_Assign 23 (word_Load (word_Op asm_Add [word_Var 17;
                  word_Const ((n2w 2) * bytes_in_word)]));
                word_Inst (asm_FP (FPMovFromReg 0 13 11));
                word_Inst (asm_FP (FPMovFromReg 1 23 21));
                word_Inst (asm_FP (fp_cmp_inst fpc));
                word_Assign (adjust_var dest) (word_Op asm_Add [ShiftVar
                  Lsl 3 4; word_Const (n2w 2)])],l))):'a word_prog#num)`;;

let assign_FP_top_def = new_definition
  `assign_FP_top fpt (c:data_to_word_config) (secn:num) (l:num) (dest:num)
  (names:(1 spt) option) v1 v2 v3 =
        ((if ~(data_to_word_config_has_fp_ops c) \/
          ~(data_to_word_config_has_fp_tern c) then (GiveUp,l) else if dimindex
          (:'a) = 64 then
          (match encode_header c 3 1 with NONE -> (GiveUp,l)
           | SOME (header:'a word) ->
             (data_to_word_list_Seq [
                word_Assign 3 (word_Load (word_Op asm_Add
                            [real_addr c (adjust_var v1); word_Const
                              bytes_in_word]));
                word_Assign 5 (word_Load (word_Op asm_Add
                            [real_addr c (adjust_var v2); word_Const
                              bytes_in_word]));
                word_Assign 7 (word_Load (word_Op asm_Add
                            [real_addr c (adjust_var v3); word_Const
                              bytes_in_word]));
                word_Inst (asm_FP (FPMovFromReg 0 3 3));
                word_Inst (asm_FP (FPMovFromReg 1 5 5));
                word_Inst (asm_FP (FPMovFromReg 2 7 7));
                word_Inst (asm_FP (fp_top_inst fpt));
                word_Inst (asm_FP (FPMovToReg 3 5 0));
                WriteWord64 c header dest 3],l))
         else (match encode_header c 3 2 with NONE -> (GiveUp,l)
           | SOME header ->
             (data_to_word_list_Seq [
                word_Assign 15 (real_addr c (adjust_var v1));
                word_Assign 17 (real_addr c (adjust_var v2));
                word_Assign 19 (real_addr c (adjust_var v3));
                word_Assign 11 (word_Load (word_Op asm_Add [word_Var 15;
                  word_Const bytes_in_word]));
                word_Assign 13 (word_Load (word_Op asm_Add [word_Var 15;
                  word_Const ((n2w 2) * bytes_in_word)]));
                word_Assign 21 (word_Load (word_Op asm_Add [word_Var 17;
                  word_Const bytes_in_word]));
                word_Assign 23 (word_Load (word_Op asm_Add [word_Var 17;
                  word_Const ((n2w 2) * bytes_in_word)]));
                word_Assign 31 (word_Load (word_Op asm_Add [word_Var 19;
                  word_Const bytes_in_word]));
                word_Assign 33 (word_Load (word_Op asm_Add [word_Var 19;
                  word_Const ((n2w 2) * bytes_in_word)]));
                word_Inst (asm_FP (FPMovFromReg 0 13 11));
                word_Inst (asm_FP (FPMovFromReg 1 23 21));
                word_Inst (asm_FP (FPMovFromReg 2 33 31));
                word_Inst (asm_FP (fp_top_inst fpt));
                word_Inst (asm_FP (FPMovToReg 5 3 0));
                WriteWord64_on_32 c header dest 5 3],l))):'a
                  word_prog#num)`;;

let assign_FP_bop_def = new_definition
  `assign_FP_bop fpb (c:data_to_word_config) (secn:num) (l:num) (dest:num)
  (names:(1 spt) option) v1 v2 =
        ((if ~(data_to_word_config_has_fp_ops c) then (GiveUp,l) else if
          dimindex (:'a) = 64 then
          (match encode_header c 3 1 with NONE -> (GiveUp,l)
           | SOME (header:'a word) ->
             (data_to_word_list_Seq [
                word_Assign 3 (word_Load (word_Op asm_Add
                            [real_addr c (adjust_var v1); word_Const
                              bytes_in_word]));
                word_Assign 5 (word_Load (word_Op asm_Add
                            [real_addr c (adjust_var v2); word_Const
                              bytes_in_word]));
                word_Inst (asm_FP (FPMovFromReg 0 3 3));
                word_Inst (asm_FP (FPMovFromReg 1 5 5));
                word_Inst (asm_FP (fp_bop_inst fpb));
                word_Inst (asm_FP (FPMovToReg 3 5 0));
                WriteWord64 c header dest 3],l))
         else (match encode_header c 3 2 with NONE -> (GiveUp,l)
           | SOME header ->
             (data_to_word_list_Seq [
                word_Assign 15 (real_addr c (adjust_var v1));
                word_Assign 17 (real_addr c (adjust_var v2));
                word_Assign 11 (word_Load (word_Op asm_Add [word_Var 15;
                  word_Const bytes_in_word]));
                word_Assign 13 (word_Load (word_Op asm_Add [word_Var 15;
                  word_Const ((n2w 2) * bytes_in_word)]));
                word_Assign 21 (word_Load (word_Op asm_Add [word_Var 17;
                  word_Const bytes_in_word]));
                word_Assign 23 (word_Load (word_Op asm_Add [word_Var 17;
                  word_Const ((n2w 2) * bytes_in_word)]));
                word_Inst (asm_FP (FPMovFromReg 0 13 11));
                word_Inst (asm_FP (FPMovFromReg 1 23 21));
                word_Inst (asm_FP (fp_bop_inst fpb));
                word_Inst (asm_FP (FPMovToReg 5 3 0));
                WriteWord64_on_32 c header dest 5 3],l))):'a
                  word_prog#num)`;;

let assign_FP_uop_def = new_definition
  `assign_FP_uop fpu (c:data_to_word_config) (secn:num) (l:num) (dest:num)
  (names:(1 spt) option) v1 =
        ((if ~(data_to_word_config_has_fp_ops c) then (GiveUp,l) else if
          dimindex (:'a) = 64 then
          (match encode_header c 3 1 with NONE -> (GiveUp,l)
           | SOME (header:'a word) ->
             (data_to_word_list_Seq [
                word_Assign 3 (word_Load (word_Op asm_Add
                            [real_addr c (adjust_var v1); word_Const
                              bytes_in_word]));
                word_Inst (asm_FP (FPMovFromReg 0 3 3));
                word_Inst (asm_FP (fp_uop_inst fpu));
                word_Inst (asm_FP (FPMovToReg 3 5 1));
                WriteWord64 c header dest 3],l))
         else (match encode_header c 3 2 with NONE -> (GiveUp,l)
           | SOME header ->
             (data_to_word_list_Seq [
                word_Assign 15 (real_addr c (adjust_var v1));
                word_Assign 11 (word_Load (word_Op asm_Add [word_Var 15;
                  word_Const bytes_in_word]));
                word_Assign 13 (word_Load (word_Op asm_Add [word_Var 15;
                  word_Const ((n2w 2) * bytes_in_word)]));
                word_Inst (asm_FP (FPMovFromReg 0 13 11));
                word_Inst (asm_FP (fp_uop_inst fpu));
                word_Inst (asm_FP (FPMovToReg 5 3 1));
                WriteWord64_on_32 c header dest 5 3],l))):'a
                  word_prog#num)`;;

let assign_FinaliseCons_def = new_definition
  `assign_FinaliseCons (l:num) (dest:num) v1 =
                  ((word_Assign (adjust_var dest) (word_Var (adjust_var
                    v1)),l):'a word_prog#num)`;;

(* HOL4 data_to_wordScript.sml:2460-2461: a theorem that HOL4 states as the
   value of an ML expression: all_assign_defs *)

let assign_def = new_definition
  `data_to_word_assign (c:data_to_word_config) (secn:num) (l:num) (dest:num)
  (op:clos_op) (args:num list) (names:(1 spt) option) =
     match op with clos_IntOp (clos_Const i) -> assign_Const i l dest
     | clos_GlobOp clos_GlobalsPtr -> (word_Assign (adjust_var dest)
       (word_Lookup Globals),l)
     | clos_GlobOp clos_SetGlobalsPtr -> data_to_word_arg1 args
       (assign_SetGlobalsPtr c l dest) (word_Skip,l)
     | clos_GlobOp (clos_SetGlobal n) -> data_to_word_arg1 args
       (assign_SetGlobal c n l dest) (word_Skip,l)
     | clos_GlobOp (clos_Global n) -> assign_Global c n l dest
     | clos_MemOp clos_El -> data_to_word_arg2 args (assign_El c l dest)
       (word_Skip,l)
     | clos_BlockOp (clos_ElemAt n) -> data_to_word_arg1 args (assign_ElemAt
       c n l dest) (word_Skip,l)
     | clos_MemOp clos_DerefByte -> data_to_word_arg2 args (assign_DerefByte
       c l dest) (word_Skip,l)
     | clos_MemOp clos_Update -> arg3 args (assign_Update c l dest)
       (word_Skip,l)
     | clos_MemOp clos_UpdateCons -> arg3 args (assign_Update c l dest)
       (word_Skip,l)
     | clos_MemOp clos_UpdateByte -> arg3 args (assign_UpdateByte c l dest)
       (word_Skip,l)
     | clos_MemOp clos_FinaliseCons -> data_to_word_arg1 args
       (assign_FinaliseCons l dest) (word_Skip,l)
     | clos_BlockOp clos_ListAppend -> data_to_word_arg2 args
       (assign_ListAppend c secn l dest names) (word_Skip,l)
     | clos_BlockOp (clos_Cons tag) -> assign_Cons c l dest tag args
     | clos_MemOp (clos_MutCons tag _) -> assign_MutCons c l dest tag args
     | clos_MemOp clos_ConfigGC -> data_to_word_arg2 args (assign_ConfigGC c
       secn l dest names) (word_Skip,l)
     | clos_BlockOp (clos_Build parts') -> assign_Build c secn l dest names
       parts'
     | clos_BlockOp (clos_ConsExtend tag) -> assign_ConsExtend c secn l dest
       names tag args
     | clos_MemOp clos_Ref -> assign_Ref c secn l dest names args
     | clos_ThunkOp (AllocThunk ev) -> data_to_word_arg1 args
       (assign_AllocThunk ev c secn l dest names) (word_Skip,l)
     | clos_ThunkOp (UpdateThunk ev) -> data_to_word_arg2 args
       (assign_UpdateThunk ev c l dest) (word_Skip,l)
     | clos_MemOp (clos_RefByte imm) -> data_to_word_arg2 args
       (assign_RefByte c secn l dest names imm) (word_Skip,l)
     | clos_MemOp clos_XorByte -> data_to_word_arg2 args (assign_XorByte c
       secn l dest names) (word_Skip,l)
     | clos_MemOp (clos_StringCmp b cmp) -> data_to_word_arg2 args
       (assign_StringCmp c secn l dest names b cmp) (word_Skip,l)
     | clos_Label n -> (word_LocValue (adjust_var dest) n,l)
     | clos_MemOp (clos_CopyByte alloc_new) -> assign_CopyByte c secn l dest
       names args
     | clos_MemOp clos_RefArray -> data_to_word_arg2 args (assign_RefArray c
       secn l dest names) (word_Skip,l)
     | clos_BlockOp (clos_BoolTest test) -> data_to_word_arg2 args
       (assign_BoolTest l dest test) (word_Skip,l)
     | clos_BlockOp clos_BoolNot -> data_to_word_arg1 args (assign_BoolNot l
       dest) (word_Skip,l)
     | clos_WordOp (WordTest ws test) -> data_to_word_arg2 args
       (assign_WordTest l dest test) (word_Skip,l)
     | clos_BlockOp (clos_FromList tag) -> data_to_word_arg2 args
       (assign_FromList c secn l dest names tag) (word_Skip,l)
     | clos_IntOp (clos_LessConstSmall i) -> data_to_word_arg1 args
       (assign_LessConstSmall l dest i) (word_Skip,l)
     | clos_MemOp (clos_BoundsCheckByte leq) ->
         data_to_word_arg2 args (assign_BoundsCheckByte c secn l dest names
           leq) (word_Skip,l)
     | clos_MemOp clos_BoundsCheckArray ->
         data_to_word_arg2 args (assign_BoundsCheckArray c secn l dest
           names) (word_Skip,l)
     | clos_BlockOp clos_BoundsCheckBlock ->
         data_to_word_arg2 args (assign_BoundsCheckBlock c secn l dest
           names) (word_Skip,l)
     | clos_BlockOp clos_Equal -> data_to_word_arg2 args (assign_Equal c
       secn l dest names) (word_Skip,l)
     | clos_IntOp clos_Less -> data_to_word_arg2 args (assign_Less c secn l
       dest names) (word_Skip,l)
     | clos_IntOp clos_LessEq -> data_to_word_arg2 args (assign_LessEq c
       secn l dest names) (word_Skip,l)
     | clos_BlockOp clos_LengthBlock -> data_to_word_arg1 args
       (assign_LengthBlock c secn l dest names) (word_Skip,l)
     | clos_MemOp clos_Length -> data_to_word_arg1 args (assign_Length c
       secn l dest names) (word_Skip,l)
     | clos_MemOp clos_LengthByte -> data_to_word_arg1 args
       (assign_LengthByte c secn l dest names) (word_Skip,l)
     | clos_BlockOp (clos_TagLenEq tag len) ->
         data_to_word_arg1 args (assign_TagLenEq c secn l dest names tag
           len) (word_Skip,l)
     | clos_BlockOp (clos_LenEq len) -> data_to_word_arg1 args (assign_LenEq
       c secn l dest names len) (word_Skip,l)
     | clos_BlockOp (clos_TagEq tag) -> data_to_word_arg1 args (assign_TagEq
       c secn l dest names tag) (word_Skip,l)
     | clos_IntOp clos_Add -> data_to_word_arg2 args (assign_Add c secn l
       dest names) (word_Skip,l)
     | clos_IntOp clos_Sub -> data_to_word_arg2 args (assign_Sub c secn l
       dest names) (word_Skip,l)
     | clos_IntOp clos_Mult -> data_to_word_arg2 args (assign_Mult c secn l
       dest names) (word_Skip,l)
     | clos_IntOp clos_Div -> data_to_word_arg2 args (assign_Div c secn l
       dest names) (word_Skip,l)
     | clos_IntOp clos_Mod -> data_to_word_arg2 args (assign_Mod c secn l
       dest names) (word_Skip,l)
     | clos_WordOp (WordOpw ast_W8 opw) -> data_to_word_arg2 args
       (assign_WordOpW8 opw c secn l dest names) (word_Skip,l)
     | clos_WordOp (WordOpw ast_W64 opw) -> data_to_word_arg2 args
       (assign_WordOpW64 opw c secn l dest names) (word_Skip,l)
     | clos_WordOp (WordShift ast_W8 sh n) -> data_to_word_arg1 args
       (assign_WordShiftW8 sh n c secn l dest names) (word_Skip,l)
     | clos_WordOp (WordShift ast_W64 sh n) -> data_to_word_arg1 args
       (assign_WordShiftW64 sh n c secn l dest names) (word_Skip,l)
     | clos_WordOp (WordFromWord b) -> data_to_word_arg1 args
       (assign_WordFromWord b c secn l dest names) (word_Skip,l)
     | clos_WordOp (WordFromInt) -> data_to_word_arg1 args
       (assign_WordFromInt c secn l dest names) (word_Skip,l)
     | clos_WordOp (WordToInt) -> data_to_word_arg1 args (assign_WordToInt c
       secn l dest names) (word_Skip,l)
     | clos_FFI ffi_index -> data_to_word_arg2 args (assign_FFI ffi_index c
       secn l dest names) (word_Skip,l)
     | clos_BlockOp (clos_EqualConst p) -> data_to_word_arg1 args
       (assign_EqualConst p c secn l dest names) (word_Skip,l)
     | clos_Install -> arg4 args (assign_Install c secn l dest names)
       (word_Skip,l)
     | clos_WordOp (FP_cmp fpc) -> data_to_word_arg2 args (assign_FP_cmp fpc
       c secn l dest names) (word_Skip,l)
     | clos_WordOp (FP_top fpt) -> arg3 args (assign_FP_top fpt c secn l
       dest names) (word_Skip,l)
     | clos_WordOp (FP_bop fpb) -> data_to_word_arg2 args (assign_FP_bop fpb
       c secn l dest names) (word_Skip,l)
     | clos_WordOp (FP_uop fpu) -> data_to_word_arg1 args (assign_FP_uop fpu
       c secn l dest names) (word_Skip,l)
     | _ -> (word_Skip,l)`;;

let force_thunk_def = new_definition
  `force_thunk (c:data_to_word_config) secn (l:num) ret loc v1 =
     ((match encode_header c (8 + 6) 1 with NONE -> (GiveUp,l)
      | SOME (header:'a word) ->
      word_If asm_Test (adjust_var v1) (Imm (n2w 1))
        (match ret with NONE -> word_Return 0 [adjust_var v1]
         | SOME (dest,_) -> word_Assign (adjust_var dest) (word_Var
           (adjust_var v1)))
        (data_to_word_list_Seq
           [word_Assign 1 (real_addr c (adjust_var v1));
            word_Assign 3 (word_Op asm_And [word_Load (word_Var 1);
              word_Const (n2w 0b111100)]);
            word_If asm_Equal 3 (Imm (n2w ((8 + 6) * 4)))
              (match ret with NONE ->
                  data_to_word_list_Seq
                    [word_Assign 1 (word_Load (word_Op asm_Add [word_Var 1;
                      word_Const bytes_in_word]));
                     word_Return 0 [1]]
               | SOME (dest,_) ->
                   word_Assign (adjust_var dest)
                          (word_Load (word_Op asm_Add [word_Var 1;
                            word_Const bytes_in_word])))
            (word_If asm_NotEqual 3 (Imm (n2w ((0 + 6) * 4)))
              (match ret with NONE -> word_Return 0 [adjust_var v1]
               | SOME (dest,_) -> word_Assign (adjust_var dest) (word_Var
                 (adjust_var v1)))
              (data_to_word_list_Seq
                 [word_Assign 5 (word_Load (word_Op asm_Add [word_Var 1;
                   word_Const bytes_in_word]));
                  (match ret with NONE -> word_Call NONE (SOME loc) [0;
                    adjust_var v1; 5] NONE
                   | SOME (r,ns) -> word_Call (SOME ([adjust_var
                     r],adjust_sets ns,word_Skip,secn,l))
                              (SOME loc) [adjust_var v1; 5] NONE)]))]),l
                                + 1):'a word_prog#num)`;;

make_size "data_prog";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let comp_def,comp_ind = define_wf
  `MEASURE (\(x0,x1,x2,x3). data_prog_size x3)`
  `data_to_word_comp c (secn:num) (l:num) (p:data_prog) =
     match p with data_Skip -> ((word_Skip:'a word_prog),l)
     | data_Tick -> (word_Tick,l)
     | data_Raise n -> (word_Raise (adjust_var n),l)
     | data_Return ns -> (word_Return 0 (MAP adjust_var ns),l)
     | data_Move n1 n2 -> (word_Move 0 [(adjust_var n1,adjust_var n2)],l)
     | data_Seq p1 p2 ->
         let (q1,l1) = data_to_word_comp c secn l p1 in
         let (q2,l2) = data_to_word_comp c secn l1 p2 in
           (word_Seq q1 q2,l2)
     | data_If n p1 p2 ->
         let (q1,l1) = data_to_word_comp c secn l p1 in
         let (q2,l2) = data_to_word_comp c secn l1 p2 in
           (word_If asm_Equal (adjust_var n) (Imm (n2w 18)) q1 q2,l2)
     | data_MakeSpace n names ->
         let k = dimindex (:'a) DIV 8 in
         let w = n2w (n * k) in
         let w = (if w2n w = n * k then w else word_not (n2w 0)) in
           (word_Seq (word_Assign 1 (word_Op asm_Sub [word_Lookup TriggerGC;
             word_Lookup NextFree]))
                (word_If asm_Lower 1 (Imm w)
                  (data_to_word_list_Seq [SilentFFI c 3 (adjust_sets names);
                             word_Assign 1 (word_Const w);
                             word_Alloc 1 (adjust_sets names);
                             SilentFFI c 3 (adjust_sets names)])
                 word_Skip),l)
     | data_Assign dest op args names -> data_to_word_assign c secn l dest
       op args names
     | data_Force ret loc v -> force_thunk c secn l ret loc v
     | data_Call ret target args handler ->
         (match ret with NONE -> (word_Call NONE target (CONS 0 (MAP
           adjust_var args)) NONE,l)
         | SOME (ns,names) ->
             (let ret = SOME (MAP adjust_var ns,adjust_sets
               names,word_Skip,secn,l) in
               match handler with NONE -> (word_Call ret target (MAP
                 adjust_var args) NONE,l + 1)
               | SOME (n,p) ->
                   let (q1,l1) = data_to_word_comp c secn (l + 2) p in
                   let handler = SOME (adjust_var n,q1,secn,l + 1) in
                     (word_Call ret target (MAP adjust_var args)
                       handler,l1)))`;;

let data_to_word_compile_part_def = new_definition
  `data_to_word_compile_part c (n,arg_count,p) = (n,arg_count + 1,FST
  (data_to_word_comp c n 2 p))`;;

let MemCopy_code_def = new_definition
  `MemCopy_code =
     (word_If asm_Test 2 (Reg 2) (word_Return 0 [8])
         (data_to_word_list_Seq [word_Assign 1 (word_Load (word_Var 4));
                    word_Assign 2 (word_Op asm_Sub [word_Var 2; word_Const
                      (n2w 4)]);
                    word_Assign 4 (word_Op asm_Add [word_Var 4; word_Const
                      bytes_in_word]);
                    word_Store (word_Var 6) 1;
                    word_Assign 6 (word_Op asm_Add [word_Var 6; word_Const
                      bytes_in_word]);
                    word_Call NONE (SOME MemCopy_location) [0; 2; 4; 6;
                      8] NONE]):'a word_prog)`;;

let ByteCopy_code_def = new_definition
  `ByteCopy_code c = (data_to_word_list_Seq
      [word_Assign 4 (ShiftVar Lsr 4 2);
       word_Assign 6 (ShiftVar Lsr 6 2);
       word_Assign 10 (ShiftVar Lsr 10 2);
       word_Assign 1 data_to_word_Unit;
       word_Assign 2 (word_Op asm_Add [real_addr c 2; word_Const
         bytes_in_word; word_Var 4]);
       word_Assign 8 (word_Op asm_Add [real_addr c 8; word_Const
         bytes_in_word; word_Var 10]);
       word_If asm_Lower 4 (Reg 10)
         (data_to_word_list_Seq [word_Assign 3 (word_Op asm_Sub [word_Var 6;
           word_Const (n2w 1)]);
                    word_Assign 2 (word_Op asm_Add [word_Var 2; word_Var
                      3]);
                    word_Assign 8 (word_Op asm_Add [word_Var 8; word_Var
                      3]);
                    word_Call NONE (SOME ByteCopySub_location) [0; 6; 2; 8;
                      1] NONE])
         (word_Call NONE (SOME ByteCopyAdd_location) [0; 6; 2; 8; 1]
           NONE)]:'a word_prog)`;;

let ByteCopyAdd_code_def = new_definition
  `ByteCopyAdd_code =
   word_If asm_Lower 2 (Imm (n2w 4))
     (
       // n <+ 4w
       word_If asm_Lower 2 (Imm (n2w 2))
       (
         // n <+ 2w
         word_If asm_Equal 2 (Imm (n2w 0)) (word_Return 0 [8])
         (
           // n = 0w
           data_to_word_list_Seq [
             word_Inst (asm_Mem asm_Load8 1 (Addr 4 (n2w 0)));
             word_Inst (asm_Mem asm_Store8 1 (Addr 6 (n2w 0)));
             word_Return 0 [8]]))
       (data_to_word_list_Seq [
         word_Inst (asm_Mem asm_Load8 1 (Addr 4 (n2w 0)));
         word_Inst (asm_Mem asm_Load8 3 (Addr 4 (n2w 1)));
         word_If asm_Equal 2 (Imm (n2w 2))
           (data_to_word_list_Seq [
             word_Inst (asm_Mem asm_Store8 1 (Addr 6 (n2w 0)));
             word_Inst (asm_Mem asm_Store8 3 (Addr 6 (n2w 1)));
             word_Return 0 [8]])
           (data_to_word_list_Seq [
             word_Inst (asm_Mem asm_Load8 5 (Addr 4 (n2w 2)));
             word_Inst (asm_Mem asm_Store8 1 (Addr 6 (n2w 0)));
             word_Inst (asm_Mem asm_Store8 3 (Addr 6 (n2w 1)));
             word_Inst (asm_Mem asm_Store8 5 (Addr 6 (n2w 2)));
             word_Return 0 [8]])]))
     (data_to_word_list_Seq [
      word_Inst (asm_Mem asm_Load8 1 (Addr 4 (n2w 0)));
      word_Inst (asm_Mem asm_Load8 3 (Addr 4 (n2w 1)));
      word_Inst (asm_Mem asm_Load8 5 (Addr 4 (n2w 2)));
      word_Inst (asm_Mem asm_Load8 7 (Addr 4 (n2w 3)));
      word_Inst (asm_Mem asm_Store8 1 (Addr 6 (n2w 0)));
      word_Inst (asm_Mem asm_Store8 3 (Addr 6 (n2w 1)));
      word_Inst (asm_Mem asm_Store8 5 (Addr 6 (n2w 2)));
      word_Inst (asm_Mem asm_Store8 7 (Addr 6 (n2w 3)));
      word_Assign 9 (word_Op asm_Sub [word_Var 2; word_Const (n2w 4)]);
      word_Assign 11 (word_Op asm_Add [word_Var 4; word_Const (n2w 4)]);
      word_Assign 13 (word_Op asm_Add [word_Var 6; word_Const (n2w 4)]);
      word_Call NONE (SOME ByteCopyAdd_location) [0; 9; 11; 13; 8] NONE])`;;

let ByteCopySub_code_def = new_definition
  `ByteCopySub_code =
   word_If asm_Lower 2 (Imm (n2w 4))
     (
       // n <+ 4w
       word_If asm_Lower 2 (Imm (n2w 2))
       (
         // n <+ 2w
         word_If asm_Equal 2 (Imm (n2w 0)) (word_Return 0 [8])
         (
           // n = 0w
           data_to_word_list_Seq [
             word_Inst (asm_Mem asm_Load8 1 (Addr 4 (n2w 0)));
             word_Inst (asm_Mem asm_Store8 1 (Addr 6 (n2w 0)));
             word_Return 0 [8]]))
       (data_to_word_list_Seq [
         word_Inst (asm_Mem asm_Load8 1 (Addr 4 (n2w 0)));
         word_Inst (asm_Mem asm_Load8 3 (Addr 4 (--(n2w 1))));
         word_If asm_Equal 2 (Imm (n2w 2))
           (data_to_word_list_Seq [
             word_Inst (asm_Mem asm_Store8 1 (Addr 6 (n2w 0)));
             word_Inst (asm_Mem asm_Store8 3 (Addr 6 (--(n2w 1))));
             word_Return 0 [8]])
           (data_to_word_list_Seq [
             word_Inst (asm_Mem asm_Load8 5 (Addr 4 (--(n2w 2))));
             word_Inst (asm_Mem asm_Store8 1 (Addr 6 (n2w 0)));
             word_Inst (asm_Mem asm_Store8 3 (Addr 6 (--(n2w 1))));
             word_Inst (asm_Mem asm_Store8 5 (Addr 6 (--(n2w 2))));
             word_Return 0 [8]])]))
     (data_to_word_list_Seq [
      word_Inst (asm_Mem asm_Load8 1 (Addr 4 (n2w 0)));
      word_Inst (asm_Mem asm_Load8 3 (Addr 4 (--(n2w 1))));
      word_Inst (asm_Mem asm_Load8 5 (Addr 4 (--(n2w 2))));
      word_Inst (asm_Mem asm_Load8 7 (Addr 4 (--(n2w 3))));
      word_Inst (asm_Mem asm_Store8 1 (Addr 6 (n2w 0)));
      word_Inst (asm_Mem asm_Store8 3 (Addr 6 (--(n2w 1))));
      word_Inst (asm_Mem asm_Store8 5 (Addr 6 (--(n2w 2))));
      word_Inst (asm_Mem asm_Store8 7 (Addr 6 (--(n2w 3))));
      word_Assign 9 (word_Op asm_Sub [word_Var 2; word_Const (n2w 4)]);
      word_Assign 11 (word_Op asm_Sub [word_Var 4; word_Const (n2w 4)]);
      word_Assign 13 (word_Op asm_Sub [word_Var 6; word_Const (n2w 4)]);
      word_Call NONE (SOME ByteCopySub_location) [0; 9; 11; 13; 8] NONE])`;;

let ByteCopyNew_code_def = new_definition
  `ByteCopyNew_code c = (word_Skip:'a word_prog)`;;

let data_to_word_stubs_def = new_definition
  `data_to_word_stubs (:'a) data_conf = APPEND [
     (FromList_location,4,((FromList_code data_conf):'a word_prog));
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
     (Unused_location,6,word_Skip);
     (
      // TODO: use next time new stub is needed
      StringCmpLoop_location,6,StringCmpLoop_code);
     (MemCopy_location,5,MemCopy_code);
     (ByteCopy_location,6,ByteCopy_code data_conf);
     (ByteCopyAdd_location,5,ByteCopyAdd_code);
     (ByteCopySub_location,5,ByteCopySub_code);
     (ByteCopyNew_location,4,ByteCopyNew_code data_conf);
     (Dummy_location,0,word_Skip)] (generated_bignum_stubs
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
 (`word_num_stubs + LENGTH (data_to_word_stubs (:'a) c) = data_num_stubs`,
  CHEAT_TAC);;

let check_LongDiv_location = prove
 (`LongDiv_location = div_location`,
  CHEAT_TAC);;

let data_to_word_compile_def = new_definition
  `data_to_word_compile data_conf word_conf asm_conf prog =
     let data_conf =
       (data_to_word_config_has_fp_tern_fupd (K (asm_config_ISA asm_conf =
         ARMv7 /\ 2 < asm_config_fp_reg_count asm_conf))
         (data_to_word_config_has_fp_ops_fupd (K (1 < asm_config_fp_reg_count
         asm_conf)) data_conf)) in
     let p = APPEND (data_to_word_stubs (:'a) data_conf) (MAP
       (data_to_word_compile_part data_conf) prog) in
       word_to_word_compile word_conf (asm_conf:'a asm_config) p`;;

let compile_0_def = new_definition
  `compile_0 data_conf (asm_conf:'a asm_config) prog =
     let data_conf = (data_to_word_config_has_fp_tern_fupd (K
       (asm_config_ISA asm_conf = ARMv7 /\
                              2 < asm_config_fp_reg_count asm_conf))
                                (data_to_word_config_has_fp_ops_fupd (K (1 <
                                asm_config_fp_reg_count asm_conf))
                                data_conf)) in APPEND (data_to_word_stubs
                                (:'a) data_conf) (MAP
                                (data_to_word_compile_part data_conf) prog)`;;

(* compute bignum call graph *)

(* HOL4 data_to_wordScript.sml:2856-2867: the ML values that the definitions
   below antiquote *)

let AnyArith_call_tree_def = new_definition
  `AnyArith_call_tree =
     full_call_graph AnyArith_location
       (fromAList (data_to_word_stubs (:1)
          (data_to_word_config_has_longdiv_fupd (K F)
             (data_to_word_config_call_empty_ffi_fupd (K F) ARB))))`;;

make_size "call_tree";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let structure_le_def,structure_le_ind = define_wf
  `MEASURE (\(x0,x1). call_tree_size x0 + call_tree_size x1)`
  `structure_le x1 x2 =
   match (x1,x2) with
     (word_depth_Leaf,_) -> T
   | (_,word_depth_Unknown) -> T
   | (word_depth_Const k1 t1,word_depth_Const k2 t2) ->
     (k1 <= k2 /\ structure_le t1 t2)
   | (word_depth_Call n1 t2,word_depth_Call m1 u2) ->
     (n1 = m1 /\ structure_le t2 u2)
   | (word_depth_Branch t1 t2,word_depth_Branch u1 u2) ->
     (structure_le t1 u1 /\ structure_le t2 u2)
   | (_,_) -> F`;;

let AnyArith_call_tree_thm = prove
 (`structure_le
     (full_call_graph AnyArith_location (fromAList (data_to_word_stubs (:'a)
       (data_conf))))
     AnyArith_call_tree`,
  CHEAT_TAC);;

(* and the interface *)
let _ = unhide_overloads ();;
