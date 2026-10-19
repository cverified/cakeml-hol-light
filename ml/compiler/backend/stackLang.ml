(* ======================================================== *)
(*  stackLang: ported from HOL4's
    compiler/backend/stackLangScript.sml
    A definition theory, with 3 definitions, 2 datatypes and 2
    theorems.  Needed by 52 files of the port.  *)
(* ======================================================== *)

(*
  The stackLang intermediate language is a structured programming
  language with function calls, while loops, if statements, etc. All
  assignments are assembly instructions and register allocation is
  assumed to have been done. This is the language within which stack
  operations get optimised and turned into normal memory accesses.
*)

needs "compiler/backend/backend_common.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "misc/misc.ml";;
(* for bytes_in_word *)


let store_name_INDUCT,store_name_RECURSION = define_datatype
  "store_name = NextFree | EndOfHeap | TriggerGC | HeapLength | \
   ProgStart | BitmapBase | CurrHeap | OtherHeap | AllocSize | \
   Globals | GlobReal | Handler | GenStart | CodeBuffer | \
   CodeBufferEnd | BitmapBuffer | BitmapBufferEnd | Temp (5 word)";;

let stackLang_prog_INDUCT,stackLang_prog_RECURSION = define_datatype
  "stackLang_prog = stackLang_Skip | stackLang_Inst ('a asm_inst) | \
   stackLang_Get (num) (store_name) | stackLang_Set (store_name) \
   (num) | stackLang_OpCurrHeap (binop) (num) (num) | stackLang_Call \
   ((stackLang_prog#num#num#num) option) (num+num) \
   ((stackLang_prog#num#num) option) \
   // target of call\n\
   | \
   // return-handler code, link reg, labels l1,l2\n\
   // handler: exception-handler code, labels l1,l2\n\
   stackLang_Seq (stackLang_prog) (stackLang_prog) | stackLang_If \
   (cmp) (num) ('a asm_reg_imm) (stackLang_prog) (stackLang_prog) | \
   stackLang_Loop (stackLang_prog) | stackLang_JumpLower (num) (num) \
   (num) \
   // reg, reg, target name\n\
   | stackLang_Alloc (num) | stackLang_StoreConsts (num) (num) (num \
   option) \
   // reg, reg, stub name to call\n\
   | stackLang_Raise (num) | stackLang_Return (num) | stackLang_Break \
   (num) | stackLang_Continue (num) | stackLang_FFI (mlstring) (num) \
   (num) (num) (num) (num) \
   // FFI index, conf_ptr, conf_len,\n\
   // array_ptr, array_len, ret_addr\n\
   | stackLang_Tick | stackLang_LocValue (num) (num) (num) \
   // assign v1 := Loc v2 v3\n\
   | stackLang_Install (num) (num) (num) (num) (num) \
   // code buffer start, length of new code,\n\
   // data buffer start, length of new data, ret_addr\n\
   | stackLang_ShMemOp (memop) (num) ('a asm_addr) \
   // share memory operation, register, addr to load/store\n\
   | stackLang_CodeBufferWrite (num) (num) \
   // code buffer address, byte to write\n\
   | stackLang_DataBufferWrite (num) (num) \
   // data buffer address, word to write\n\
   | \
   // new in stackLang, compared to wordLang, below\n\
   stackLang_RawCall (num) \
   // tail-call into body of function (past stack alloc)\n\
   | stackLang_StackAlloc (num) \
   // allocate n slots on the stack\n\
   | stackLang_StackFree (num) \
   // free n slots on the stack\n\
   | stackLang_StackStore (num) (num) \
   // offset, fast\n\
   | stackLang_StackStoreAny (num) (num) \
   // reg contains offset, slow, used by GC\n\
   | stackLang_StackLoad (num) (num) \
   // offset, fast\n\
   | stackLang_StackLoadAny (num) (num) \
   // reg contains offset, slow, used by GC\n\
   | stackLang_StackGetSize (num) \
   // used when installing exc handler\n\
   | stackLang_StackSetSize (num) \
   // used by implementation of raise\n\
   | stackLang_BitmapLoad (num) (num) \
   // load word from read-only region\n\
   | stackLang_Halt (num)";;
hol4_overload "Skip" "stackLang_Skip";;
hol4_overload "Inst" "stackLang_Inst";;
hol4_overload "Get" "stackLang_Get";;
hol4_overload "Set" "stackLang_Set";;
hol4_overload "OpCurrHeap" "stackLang_OpCurrHeap";;
hol4_overload "Call" "stackLang_Call";;
hol4_overload "Seq" "stackLang_Seq";;
hol4_overload "If" "stackLang_If";;
hol4_overload "Loop" "stackLang_Loop";;
hol4_overload "JumpLower" "stackLang_JumpLower";;
hol4_overload "Alloc" "stackLang_Alloc";;
hol4_overload "StoreConsts" "stackLang_StoreConsts";;
hol4_overload "Raise" "stackLang_Raise";;
hol4_overload "Return" "stackLang_Return";;
hol4_overload "Break" "stackLang_Break";;
hol4_overload "Continue" "stackLang_Continue";;
hol4_overload "FFI" "stackLang_FFI";;
hol4_overload "Tick" "stackLang_Tick";;
hol4_overload "LocValue" "stackLang_LocValue";;
hol4_overload "Install" "stackLang_Install";;
hol4_overload "ShMemOp" "stackLang_ShMemOp";;
hol4_overload "CodeBufferWrite" "stackLang_CodeBufferWrite";;
hol4_overload "DataBufferWrite" "stackLang_DataBufferWrite";;
hol4_overload "RawCall" "stackLang_RawCall";;
hol4_overload "StackAlloc" "stackLang_StackAlloc";;
hol4_overload "StackFree" "stackLang_StackFree";;
hol4_overload "StackStore" "stackLang_StackStore";;
hol4_overload "StackStoreAny" "stackLang_StackStoreAny";;
hol4_overload "StackLoad" "stackLang_StackLoad";;
hol4_overload "StackLoadAny" "stackLang_StackLoadAny";;
hol4_overload "StackGetSize" "stackLang_StackGetSize";;
hol4_overload "StackSetSize" "stackLang_StackSetSize";;
hol4_overload "BitmapLoad" "stackLang_BitmapLoad";;
hol4_overload "Halt" "stackLang_Halt";;

(* HOL4 stackLangScript.sml:68: the overload While, which the port
   expands *)

(* HOL4 stackLangScript.sml:70: the overload move, which the port
   expands *)
(* HOL4 stackLangScript.sml:71: the overload sub_1_inst, which the
   port expands *)
(* HOL4 stackLangScript.sml:72: the overload sub_inst, which the port
   expands *)
(* HOL4 stackLangScript.sml:73: the overload add_inst, which the port
   expands *)
(* HOL4 stackLangScript.sml:74: the overload and_inst, which the port
   expands *)
(* HOL4 stackLangScript.sml:75: the overload xor_inst, which the port
   expands *)
(* HOL4 stackLangScript.sml:76: the overload add_1_inst, which the
   port expands *)
(* HOL4 stackLangScript.sml:77: the overload or_inst, which the port
   expands *)
(* HOL4 stackLangScript.sml:78: the overload add_bytes_in_word_inst,
   which the port expands *)
(* HOL4 stackLangScript.sml:79: the overload div2_inst, which the
   port expands *)
(* HOL4 stackLangScript.sml:80: the overload left_shift_inst, which
   the port expands *)
(* HOL4 stackLangScript.sml:81: the overload right_shift_inst, which
   the port expands *)
(* HOL4 stackLangScript.sml:82: the overload const_inst, which the
   port expands *)
(* HOL4 stackLangScript.sml:83: the overload load_inst, which the
   port expands *)
(* HOL4 stackLangScript.sml:84: the overload store_inst, which the
   port expands *)

let list_Seq_def = cake_define_list
  [`stackLang_list_Seq [] = Skip`;
   `stackLang_list_Seq [x] = x`;
   `stackLang_list_Seq (x :: y :: xs) = stackLang_Seq x
  (stackLang_list_Seq (y :: xs))`];;
hol4_overload "list_Seq" "stackLang_list_Seq";;

let gc_stub_location_def = cake_define
  `gc_stub_location = stack_num_stubs - 1`;;
let store_consts_stub_location_def = cake_define
  `stackLang_store_consts_stub_location = gc_stub_location - 1`;;
hol4_overload "store_consts_stub_location"
  "stackLang_store_consts_stub_location";;
(* HOL4 stackLangScript.sml:98-99: a theorem that HOL4 states as the
   value of an ML expression: gc_stub_location_eq *)
(* HOL4 stackLangScript.sml:100-101: a theorem that HOL4 states as
   the value of an ML expression: store_consts_stub_location_eq *)
