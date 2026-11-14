(* ======================================================== *)
(*  stackLang: ported from HOL4's
    compiler/backend/stackLangScript.sml
    A definition theory, with 3 definitions, 2 datatypes and 2
    theorems.  Needed by 34 files of the port.  *)
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

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "stackLang"
  ["asm"; "backend_common"; "misc"];;


let store_name_INDUCT,store_name_RECURSION = define_datatype
  "store_name =
     NextFree
   | EndOfHeap
   | TriggerGC
   | HeapLength
   | ProgStart
   | BitmapBase
   | CurrHeap
   | OtherHeap
   | AllocSize
   | Globals
   | GlobReal
   | Handler
   | GenStart
   | CodeBuffer
   | CodeBufferEnd
   | BitmapBuffer
   | BitmapBufferEnd
   | Temp (5 word)";;

let stackLang_prog_INDUCT,stackLang_prog_RECURSION = define_datatype
  "stackLang_prog =
     stackLang_Skip
   | stackLang_Inst ('a asm_inst)
   | stackLang_Get num store_name
   | stackLang_Set store_name num
   | stackLang_OpCurrHeap binop num num
   | stackLang_Call ((stackLang_prog#num#num#num) option) (num+num)
       ((stackLang_prog#num#num) option)
     // target of call
     // return-handler code, link reg, labels l1,l2
     // handler: exception-handler code, labels l1,l2
   | stackLang_Seq stackLang_prog stackLang_prog
   | stackLang_If cmp num ('a asm_reg_imm) stackLang_prog stackLang_prog
   | stackLang_Loop stackLang_prog
   | stackLang_JumpLower num num num
     // reg, reg, target name
   | stackLang_Alloc num
   | stackLang_StoreConsts num num (num option)
     // reg, reg, stub name to call
   | stackLang_Raise num
   | stackLang_Return num
   | stackLang_Break num
   | stackLang_Continue num
   | stackLang_FFI mlstring num num num num num
     // FFI index, conf_ptr, conf_len,
     // array_ptr, array_len, ret_addr
   | stackLang_Tick
   | stackLang_LocValue num num num
     // assign v1 := Loc v2 v3
   | stackLang_Install num num num num num
     // code buffer start, length of new code,
     // data buffer start, length of new data, ret_addr
   | stackLang_ShMemOp memop num ('a asm_addr)
     // share memory operation, register, addr to load/store
   | stackLang_CodeBufferWrite num num
     // code buffer address, byte to write
   | stackLang_DataBufferWrite num num
     // data buffer address, word to write
     // new in stackLang, compared to wordLang, below
   | stackLang_RawCall num
     // tail-call into body of function (past stack alloc)
   | stackLang_StackAlloc num
     // allocate n slots on the stack
   | stackLang_StackFree num
     // free n slots on the stack
   | stackLang_StackStore num num
     // offset, fast
   | stackLang_StackStoreAny num num
     // reg contains offset, slow, used by GC
   | stackLang_StackLoad num num
     // offset, fast
   | stackLang_StackLoadAny num num
     // reg contains offset, slow, used by GC
   | stackLang_StackGetSize num
     // used when installing exc handler
   | stackLang_StackSetSize num
     // used by implementation of raise
   | stackLang_BitmapLoad num num
     // load word from read-only region
   | stackLang_Halt num";;

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

let _ = size_thms "stackLang_prog";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let list_Seq_def,list_Seq_ind = define_wf
  `MEASURE (\x0. list_size (stackLang_prog_size (\x. 0)) x0)`
  [`stackLang_list_Seq [] = stackLang_Skip`;
   `stackLang_list_Seq [x] = x`;
   `stackLang_list_Seq (CONS x (CONS y xs)) = stackLang_Seq x
    (stackLang_list_Seq (CONS y xs))`];;

let gc_stub_location_def = new_definition
  `gc_stub_location = stack_num_stubs - 1`;;
let store_consts_stub_location_def = new_definition
  `stackLang_store_consts_stub_location = gc_stub_location - 1`;;
(* HOL4 stackLangScript.sml:98-99: a theorem that HOL4 states as the
   value of an ML expression: gc_stub_location_eq *)
(* HOL4 stackLangScript.sml:100-101: a theorem that HOL4 states as
   the value of an ML expression: store_consts_stub_location_eq *)

(* and the interface *)
let _ = unhide_overloads ();;
