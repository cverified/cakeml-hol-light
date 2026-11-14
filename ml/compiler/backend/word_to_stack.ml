(* ======================================================== *)
(*  word_to_stack: ported from HOL4's
    compiler/backend/word_to_stackScript.sml
    A definition theory, with 45 definitions, 1 datatype and no
    theorems.  Needed by backend.ml, backendProof.ml,
    stack_to_lab.ml, stack_to_labProof.ml and word_to_stackProof.ml.  *)
(* ======================================================== *)

(*
  This compiler phase maps wordLang programs into stackLang
  programs. The most complicated part is the handling of spilled
  variables in conjunction with function calls. This compiler phase
  also introduces the so called bitmaps that the garbage collector
  uses to known which variables it should treat as roots in a given
  stack frame.
*)

needs "basis/pure/mlstring.ml";;
needs "compiler/backend/reg_alloc/parmove.ml";;
needs "compiler/backend/stackLang.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/backend/word_alloc.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "lib/sptree.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "word_to_stack"
  ["asm"; "mlstring"; "parmove"; "stackLang"; "wordLang";
   "word_alloc"];;

(* bitmaps_length stores the current length of the bitmaps *)
let word_to_stack_config_FIELDS = define_record "word_to_stack_config"
  ["bitmaps_length","num";
   "stack_frame_size","num spt"];;

(* -- *)

(* Here k = number of registers
    and f = size of stack frame
    and f' = number of slots in stack frame (= f - bitmap_size)
    and kf = (k,f,f') *)

let wReg1_def = new_definition
  `wReg1 r (k,f,(f':num)) =
     (let r = r DIV 2 in
       if r < k then ([],r) else ([(k,f - 1 - (r - k))],(k:num)))`;;

let wReg2_def = new_definition
  `wReg2 r (k,f,(f':num)) =
     (let r = r DIV 2 in
       if r < k then ([],r) else ([(k + 1,f - 1 - (r - k))],k +
         (1:num)))`;;

let wRegWrite1_def = new_definition
  `wRegWrite1 g r (k,f,(f':num)) =
     (let r = r DIV 2 in
       if r < k then g r else stackLang_Seq (g k)
         (stackLang_StackStore k (f - 1 - (r - k))))`;;

let wRegWrite2_def = new_definition
  `wRegWrite2 g r (k,f,(f':num)) =
     (let r = r DIV 2 in
       if r < k then g r else stackLang_Seq (g (k + 1))
         (stackLang_StackStore (k + 1) (f - 1 - (r - k))))`;;

let wStackLoad_def,wStackLoad_ind = define_rec
  [`wStackLoad [] x = x`;
   `wStackLoad (CONS (r,i) ps) x = stackLang_Seq
    (stackLang_StackLoad r i) (wStackLoad ps x)`];;

let wStackStore_def,wStackStore_ind = define_rec
  [`wStackStore [] x = x`;
   `wStackStore (CONS (r,i) ps) x = stackLang_Seq (wStackStore ps
    x) (stackLang_StackStore r i)`];;

let wMoveSingle_def = new_definition
  `wMoveSingle (x,y) (k,f,(f':num)) =
     (match (x,y) with (INL r1,INL r2) -> stackLang_Inst (asm_Arith
       (asm_Binop asm_Or r1 r2 (Reg r2))) | (INL r1,INR r2) ->
       stackLang_StackLoad r1 (f - 1 - (r2 - k)) | (INR r1,INL r2) ->
       stackLang_StackStore r2 (f - 1 - (r1 - k)) | (INR r1,INR r2) ->
       stackLang_Seq (stackLang_StackLoad k (f - 1 - (r2 - k)))
                              (stackLang_StackStore k (f - 1 - (r1
                                - k))))`;;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let wMoveAux_def,wMoveAux_ind = define_wf
  `MEASURE (\(x0,x1).      list_size      (pair_size (sum_size (\n. n)
  (\n. n)) (sum_size (\n. n) (\n. n)))      x0)`
  [`wMoveAux x1 kf =
        match x1 with
          [] -> stackLang_Skip
        | [xy] -> wMoveSingle xy kf
        | (CONS xy xys) -> stackLang_Seq (wMoveSingle xy kf)
          (wMoveAux xys kf)`];;

let format_var_def = define_cases
  [`format_var (k:num) NONE = INL (k + 1)`;
   `format_var (k:num) (SOME x) = (if x < (k:num) then INL x else
    INR x)`];;

let wMove_def = new_definition
  `wMove xs (k,(f:num),(f':num)) =
     wMoveAux (MAP (format_var k ## format_var k) (parmove (MAP
       (DIV2 ## DIV2) xs))) (k,f,f')`;;

let wInst_def = new_definition
  `wInst x1 kf =
        match x1 with
          ((asm_Const n c):'a asm_inst) ->
       wRegWrite1 (\n. stackLang_Inst (asm_Const n c)) n kf
        | (asm_Arith (asm_Binop bop n1 n2 (Imm imm))) ->
       (let (l,n2) = wReg1 n2 kf in
       wStackLoad l
         (wRegWrite1 (\n1. stackLang_Inst (asm_Arith (asm_Binop bop
           n1 n2 (Imm imm)))) n1 kf))
        | (asm_Arith (asm_Binop bop n1 n2 (Reg n3))) ->
       (let (l,n2) = wReg1 n2 kf in
       let (l',n3) = wReg2 n3 kf in
       wStackLoad (APPEND l l')
         (wRegWrite1 (\n1. stackLang_Inst (asm_Arith (asm_Binop bop
           n1 n2 (Reg n3)))) n1 kf))
        | (asm_Arith (asm_Shift sh n1 n2 (Imm imm))) ->
       (let (l,n2) = wReg1 n2 kf in
       wStackLoad l
         (wRegWrite1 (\n1. stackLang_Inst (asm_Arith (asm_Shift sh n1
           n2 (Imm imm)))) n1 kf))
        | (asm_Arith (asm_Shift sh n1 n2 (Reg n3))) ->
       (let (l,n2) = wReg1 n2 kf in
       let (l',n3) = wReg2 n3 kf in
       wStackLoad (APPEND l l')
         (wRegWrite1 (\n1. stackLang_Inst (asm_Arith (asm_Shift sh n1
           n2 (Reg n3)))) n1 kf))
        | (asm_Arith (asm_Div n1 n2 n3)) ->
       (let (l,n2) = wReg1 n2 kf in
       let (l',n3) = wReg2 n3 kf in
       wStackLoad (APPEND l l')
         (wRegWrite1 (\n1. stackLang_Inst (asm_Arith (asm_Div n1 n2
           n3))) n1 kf))
        | (asm_Arith (asm_AddCarry n1 n2 n3 n4)) ->
       (let (l,n2) = wReg1 n2 kf in
       let (l',n3) = wReg2 n3 kf in
       wStackLoad (APPEND l l')
         (wRegWrite1 (\n1. stackLang_Inst (asm_Arith (asm_AddCarry n1
           n2 n3 n4))) n1 kf))
        | (asm_Arith (asm_AddOverflow n1 n2 n3 n4)) ->
       (let (l,n2) = wReg1 n2 kf in
       let (l',n3) = wReg2 n3 kf in
       wStackLoad (APPEND l l')
         (wRegWrite1 (\n1. stackLang_Inst (asm_Arith (asm_AddOverflow
           n1 n2 n3 n4))) n1 kf))
        | (asm_Arith (asm_SubOverflow n1 n2 n3 n4)) ->
       (let (l,n2) = wReg1 n2 kf in
       let (l',n3) = wReg2 n3 kf in
       wStackLoad (APPEND l l')
         (wRegWrite1 (\n1. stackLang_Inst (asm_Arith (asm_SubOverflow
           n1 n2 n3 n4))) n1 kf))
        | (asm_Arith (asm_LongMul n1 n2 n3 n4)) ->
         (
          // n1 = 2, n2 = 0, n3 = 0, n4 = 1 no spills necessary
          stackLang_Inst (asm_Arith (asm_LongMul 3 0 0 2)))
        | (asm_Arith (asm_LongDiv n1 n2 n3 n4 n5)) ->
       // n1 = 0, n2 = 2, n3 = 2, n4 = 0 no spills necessary
       (let (l,n5) = wReg1 n5 kf in
       wStackLoad l
         (stackLang_Inst (asm_Arith (asm_LongDiv 0 3 3 0 n5))))
        | (asm_Mem asm_Load n1 (Addr n2 offset)) ->
       (let (l,n2) = wReg1 n2 kf in
       wStackLoad l
         (wRegWrite1 (\n1. stackLang_Inst (asm_Mem asm_Load n1 (Addr
           n2 offset))) n1 kf))
        | (asm_Mem asm_Store n1 (Addr n2 offset)) ->
       (let (l1,n2) = wReg1 n2 kf in
       let (l2,n1) = wReg2 n1 kf in
         wStackLoad (APPEND l1 l2)
           (stackLang_Inst (asm_Mem asm_Store n1 (Addr n2 offset))))
        | (asm_Mem asm_Load8 n1 (Addr n2 offset)) ->
       (let (l,n2) = wReg1 n2 kf in
       wStackLoad l
         (wRegWrite1 (\n1. stackLang_Inst (asm_Mem asm_Load8 n1 (Addr
           n2 offset))) n1 kf))
        | (asm_Mem asm_Store8 n1 (Addr n2 offset)) ->
       (let (l1,n2) = wReg1 n2 kf in
       let (l2,n1) = wReg2 n1 kf in
         wStackLoad (APPEND l1 l2)
           (stackLang_Inst (asm_Mem asm_Store8 n1 (Addr n2 offset))))
        | (asm_Mem asm_Load32 n1 (Addr n2 offset)) ->
       (let (l,n2) = wReg1 n2 kf in
       wStackLoad l
         (wRegWrite1 (\n1. stackLang_Inst (asm_Mem asm_Load32 n1
           (Addr n2 offset))) n1 kf))
        | (asm_Mem asm_Store32 n1 (Addr n2 offset)) ->
       (let (l1,n2) = wReg1 n2 kf in
       let (l2,n1) = wReg2 n1 kf in
         wStackLoad (APPEND l1 l2)
           (stackLang_Inst (asm_Mem asm_Store32 n1 (Addr n2
             offset))))
        | (asm_FP (FPLess r f1 f2)) ->
       wRegWrite1 (\r. stackLang_Inst (asm_FP (FPLess r f1 f2))) r kf
        | (asm_FP (FPLessEqual r f1 f2)) ->
       wRegWrite1 (\r. stackLang_Inst (asm_FP (FPLessEqual r f1 f2)))
         r kf
        | (asm_FP (FPEqual r f1 f2)) ->
       wRegWrite1 (\r. stackLang_Inst (asm_FP (FPEqual r f1 f2))) r
         kf
        | (asm_FP (FPMovToReg r1 r2 d)) ->
       (if dimindex (:'a) = 64 then
         wRegWrite1 (\r1. stackLang_Inst (asm_FP (FPMovToReg r1 0
           d))) r1 kf else
         wRegWrite2 (\r2. wRegWrite1 (\r1. stackLang_Inst (asm_FP
           (FPMovToReg r1 r2 d))) r1 kf) r2 kf)
        | (asm_FP (FPMovFromReg d r1 r2)) ->
       (let (l,n1) = wReg1 r1 kf in
       let (l',n2) =
         (if dimindex (:'a) = 64 then ([],0) else wReg2 r2 kf) in
       wStackLoad (APPEND l l')
         (stackLang_Inst (asm_FP (FPMovFromReg d n1 n2))))
        | (asm_FP f) -> stackLang_Inst (asm_FP f)
        // pass through the ones that don't use int registers
        | _1 -> stackLang_Inst asm_Skip`;;

let wShareInst_def = new_definition
  `wShareInst x1 v x3 kf =
        match (x1,x3) with
          ((asm_Load:memop),Addr ad offset) ->
       (let (l,n2) = wReg1 ad kf in
       wStackLoad l
         (wRegWrite1 (\r. stackLang_ShMemOp asm_Load r (Addr n2
           offset)) v kf))
        | (asm_Load8,(Addr ad offset)) ->
       (let (l,n2) = wReg1 ad kf in
       wStackLoad l
         (wRegWrite1 (\r. stackLang_ShMemOp asm_Load8 r (Addr n2
           offset)) v kf))
        | (asm_Load16,(Addr ad offset)) ->
       (let (l,n2) = wReg1 ad kf in
       wStackLoad l
         (wRegWrite1 (\r. stackLang_ShMemOp asm_Load16 r (Addr n2
           offset)) v kf))
        | (asm_Load32,(Addr ad offset)) ->
       (let (l,n2) = wReg1 ad kf in
       wStackLoad l
         (wRegWrite1 (\r. stackLang_ShMemOp asm_Load32 r (Addr n2
           offset)) v kf))
        | (asm_Store,(Addr ad offset)) ->
       (let (l1,n2) = wReg1 ad kf in
       let (l2,n1) = wReg2 v kf in
       wStackLoad (APPEND l1 l2)
         (stackLang_ShMemOp asm_Store n1 (Addr n2 offset)))
        | (asm_Store8,(Addr ad offset)) ->
       (let (l1,n2) = wReg1 ad kf in
       let (l2,n1) = wReg2 v kf in
       wStackLoad (APPEND l1 l2)
         (stackLang_ShMemOp asm_Store8 n1 (Addr n2 offset)))
        | (asm_Store16,(Addr ad offset)) ->
       (let (l1,n2) = wReg1 ad kf in
       let (l2,n1) = wReg2 v kf in
       wStackLoad (APPEND l1 l2)
         (stackLang_ShMemOp asm_Store16 n1 (Addr n2 offset)))
        | (asm_Store32,(Addr ad offset)) ->
       (let (l1,n2) = wReg1 ad kf in
       let (l2,n1) = wReg2 v kf in
       wStackLoad (APPEND l1 l2)
         (stackLang_ShMemOp asm_Store32 n1 (Addr n2 offset)))`;;

let bits_to_word_def,bits_to_word_ind = define_guess
  [`bits_to_word [] = (n2w 0)`;
   `bits_to_word (CONS T xs) = (bits_to_word xs << 1 || (n2w 1))`;
   `bits_to_word (CONS F xs) = (bits_to_word xs << 1)`];;

(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 word_to_stackScript.sml:235-238: the tactic that proves the
   termination *)
let word_to_stack_word_list_def,word_to_stack_word_list_ind = define_wf
  `MEASURE (LENGTH o FST)`
  [`word_to_stack_word_list (xs:bool list) d =
     (if LENGTH xs <= d \/ (d = 0) then [bits_to_word xs] else
       CONS (bits_to_word (APPEND (TAKE d xs) [T]))
       (word_to_stack_word_list (DROP d xs) d))`];;

let write_bitmap_def = new_definition
  `((write_bitmap live k f'):('a word) list) =
     (let names = MAP (\(r,y). (f' - 1) - (r DIV 2 - k)) (toAList
       live) in
       word_to_stack_word_list (APPEND (list_of_seq (\x. MEM x
         names) f') [T]) (dimindex (:'a) - 1))`;;

let insert_bitmap_def = new_definition
  `insert_bitmap ws (data,data_len) =
     (let l = LENGTH ws in
       ((misc_Append data (misc_List ws),data_len + l),data_len))`;;

let wLive_def = new_definition
  `wLive (live:1 spt#1 spt) (bitmaps:('a word) app_list#num)
  (k,(f:num),(f':num)) =
     (if f = 0 then (stackLang_Skip,bitmaps) else
       let (new_bitmaps,i) = insert_bitmap (write_bitmap (SND live) k
         f') bitmaps in
         ((stackLang_Seq (stackLang_Inst (asm_Const k (n2w (i +
           1)))) (stackLang_StackStore k 0):'a
           stackLang_prog),new_bitmaps))`;;

let SeqStackFree_def = new_definition
  `SeqStackFree n p = (if n = 0 then p else stackLang_Seq
  (stackLang_StackFree n) p)`;;

let call_dest_def = define_cases
  [`(call_dest (SOME pos) args kf = (stackLang_Skip,INL pos)) /\
   (call_dest NONE args kf =
      (if LENGTH args = 0 then (stackLang_Skip,INL
        raise_stub_location) else
        // this case can never occur, raise_stub_location is convenient
        let (x1,r) = wReg2 (LAST args) kf in
          (wStackLoad x1 stackLang_Skip,INR r)))`];;

let stack_arg_count_def = new_definition
  `stack_arg_count dest arg_count k =
     (match dest with INL _2 -> (arg_count - (k:num)) | INR _3 ->
       ((arg_count - 1) - (k:num)))`;;

let word_to_stack_stack_free_def = new_definition
  `word_to_stack_stack_free dest arg_count (k,f,(f':num)) =
     f - stack_arg_count dest arg_count k`;;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let stack_move_def,stack_move_ind = define_wf
  `MEASURE (\(x0,x1,x2,x3,x4). (\n. n) x0)`
  [`stack_move 0 start' offset i p = p`;
   `stack_move (SUC n) start' offset i p =
         stackLang_Seq (stack_move n (start' + 1) offset i p)
             (stackLang_Seq (stackLang_StackLoad i (start' +
                 offset)) (stackLang_StackStore i start'))`];;

let StackArgs_def = new_definition
  `StackArgs dest arg_count (k,f,(f':num)) =
     (let n = stack_arg_count dest arg_count k in
       stack_move n 0 f k (stackLang_StackAlloc n))`;;

(* Unverified x64 perf-mode instrumentation.

   The idea is to "simulate" CakeML's call stack by pushing the return address
   and the frame pointer to the C stack, popping it when the call returns.
   This allows ‘perf record --call-graph fp’ to walk CakeML stack traces.

   Due to the presence of exceptions, we need to additionally (re)store the
   base pointer and stack pointer (see PushHandler and raise_stub).
 *)

(* x64_config$x64_names: 14 → 4 = RSP *)
let perf_rsp_def = new_definition
  `perf_rsp = 14`;;

(* x64_config$x64_names: 15 → 5 = RBP (HOL's x64Script.sml) *)
let perf_rbp_def = new_definition
  `perf_rbp = 15`;;

let perf_call_prefix_def = new_definition
  `perf_call_prefix l1 l2 k =
     stackLang_list_Seq [
       // k := return address
       stackLang_LocValue k l1 l2;
       // Write the new frame's slots BELOW perf_rsp first; do not adjust
       // perf_rsp yet, so perf's fp-walker still sees the old (valid) frame
       // while the new one is being built. After the final Sub, the layout
       // will be (perf_rsp)=old_rbp, 8(perf_rsp)=ret_addr.
       stackLang_Inst (asm_Mem asm_Store k (Addr perf_rsp (--(n2w
         8))));
       stackLang_Inst (asm_Mem asm_Store perf_rbp (Addr perf_rsp
         (--(n2w 16))));
       // Atomically commit the new frame, then sync perf_rbp := perf_rsp.
       stackLang_Inst (asm_Arith (asm_Binop asm_Sub perf_rsp perf_rsp
         (Imm (n2w 16))));
       stackLang_Inst (asm_Arith (asm_Binop asm_Or perf_rbp
         perf_rsp (Reg perf_rsp)))]`;;

let perf_call_suffix_def = new_definition
  `perf_call_suffix =
     stackLang_list_Seq [
       // pop saved %rbp
       stackLang_Inst (asm_Mem asm_Load perf_rbp (Addr perf_rsp (n2w
         0)));
       // discard both slots (saved-rbp + ret_addr) in one atomic step
       stackLang_Inst (asm_Arith (asm_Binop asm_Add perf_rsp
         perf_rsp (Imm (n2w 16))))]`;;

let handler_slots_def = new_definition
  `handler_slots perf = (if perf then 5 else 3)`;;

let StackHandlerArgs_def = new_definition
  `StackHandlerArgs perf dest arg_count (k,f,(f':num)) =
     StackArgs dest arg_count (k,f + handler_slots perf,f' +
       handler_slots perf)`;;

let PushHandler_def = new_definition
  `PushHandler perf l1 l2 (k,f,f') =
     stackLang_Seq (stackLang_StackAlloc (handler_slots perf))
    (stackLang_Seq (stackLang_Inst (asm_Const k (n2w 1)))
    (stackLang_Seq (stackLang_StackStore k 0)
    (stackLang_Seq (stackLang_LocValue k l1 l2)
    (stackLang_Seq (stackLang_StackStore k 1)
    (stackLang_Seq (stackLang_Get k Handler)
    (stackLang_Seq (stackLang_StackStore k 2)
    (stackLang_Seq (if perf then
            stackLang_list_Seq [
              // slot 3: saved %rsp
              stackLang_Inst (asm_Arith (asm_Binop asm_Or k perf_rsp
                (Reg perf_rsp)));
              stackLang_StackStore k 3;
              // slot 4: saved %rbp
              stackLang_Inst (asm_Arith (asm_Binop asm_Or k perf_rbp
                (Reg perf_rbp)));
              stackLang_StackStore k 4] else stackLang_Skip)
    (stackLang_Seq (stackLang_StackGetSize k)
         (stackLang_Set Handler k)))))))))`;;

let PopHandler_def = new_definition
  `PopHandler perf (k,f,f') prog =
    stackLang_Seq (stackLang_StackLoad k 2)
   (stackLang_Seq (stackLang_Set Handler k)
   (stackLang_Seq (stackLang_StackFree (handler_slots perf))
   prog))`;;

let chunk_to_bits_def,chunk_to_bits_ind = define_rec
  [`chunk_to_bits ([]:(bool#'a word) list) = ((n2w 1):'a word)`;
   `chunk_to_bits (CONS (b,w) ws) =
      ((let res = (chunk_to_bits ws) << 1 in
        if b then res + (n2w 1) else res):'a word)`];;

let chunk_to_bitmap_def = new_definition
  `chunk_to_bitmap ws = CONS (chunk_to_bits ws) (MAP SND ws)`;;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let const_words_to_bitmap_def,const_words_to_bitmap_ind = define_wf
  `MEASURE (\(x0,x1). (\n. n) x1)`
  [`const_words_to_bitmap (ws:(bool#'a word) list) (ws_len:num) =
     (if ws_len < (dimindex (:'a) - 1) \/ (dimindex (:'a) - 1) = 0
       then chunk_to_bitmap ws else
       let h = TAKE (dimindex (:'a) - 1) ws in
       let t = DROP (dimindex (:'a) - 1) ws in APPEND
         (chunk_to_bitmap h) (const_words_to_bitmap t (ws_len -
         (dimindex (:'a) - 1))))`];;

(* Store a large constant in the second temporary *)

(*
0                f-1 0    ...   g-1
| ----------(---)|   |----------|----stack---|
            ^
      values returned on stack
*)

(* Stack slots used in multi-arg return *)
let num_stack_ret_def = new_definition
  `num_stack_ret k vs = (
   LENGTH vs + 1) - k`;;

(* Number of slots to free by callee *)
let skip_free_def = new_definition
  `skip_free (k,f,f') vs =
     f - num_stack_ret k vs`;;

(* Caller copying from the previous stack frame into its own *)
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let copy_ret_aux_def,copy_ret_aux_ind = define_wf
  `MEASURE (\(x0,x1,x2). (\n. n) x2)`
  [`(copy_ret_aux k f n =
     (if n = 0 then stackLang_Skip else
       let n' = n - 1 in
       stackLang_list_Seq
       [
         stackLang_StackLoad k n';
         stackLang_StackStore k (n' + f);
         copy_ret_aux k f n']))`];;

let copy_ret_def = new_definition
  `copy_ret perf is_handle (k,f,f') vs kont =
   (let n = num_stack_ret k vs in
   if n = 0 then kont else stackLang_Seq
       (copy_ret_aux k (if is_handle then f + handler_slots perf else
         f) n)
       (SeqStackFree n kont))`;;

(* Return should be 2,4,6,...,2k,2k+1,... *)
let word_to_stack_comp_def,word_to_stack_comp_ind =
  assume_definition_rec
  "termination (CHEAT_TAC)"
  [`word_to_stack_comp conf perf x3 bs kf =
        match x3 with
          (wordLang_Skip:'a wordLang_prog) -> ((stackLang_Skip:'a
            stackLang_prog),bs)
        | (wordLang_Move _4 xs) -> (wMove xs kf,bs)
        | (wordLang_Inst i) -> (wInst i kf,bs)
        | (wordLang_Return v1 vs) ->
        (let (xs,x) = wReg1 v1 kf in
          (wStackLoad xs (SeqStackFree (skip_free kf vs)
            (stackLang_Return x)),bs))
        | (wordLang_Raise v) -> (stackLang_Call NONE (INL
          raise_stub_location) NONE,bs)
        | (wordLang_OpCurrHeap b dst src) ->
        (let (xs,src_r) = wReg1 src kf in
          (wStackLoad xs (wRegWrite1 (\dst_r. stackLang_OpCurrHeap b
            dst_r src_r) dst kf),bs))
        | (wordLang_Tick) -> (stackLang_Tick,bs)
        | (wordLang_Break k) -> (stackLang_Break k,bs)
        | (wordLang_Continue k) -> (stackLang_Continue k,bs)
        | (wordLang_MustTerminate p1) -> word_to_stack_comp conf
          perf p1 bs kf
        | (wordLang_Seq p1 p2) ->
        (let (q1,bs) = word_to_stack_comp conf perf p1 bs kf in
        let (q2,bs) = word_to_stack_comp conf perf p2 bs kf in
          (stackLang_Seq q1 q2,bs))
        | (wordLang_If cmp r ri p1 p2) ->
        (let (x1,r') = wReg1 r kf in
        let (q1,bs) = word_to_stack_comp conf perf p1 bs kf in
        let (q2,bs) = word_to_stack_comp conf perf p2 bs kf in
        match ri with
          Reg r ->
            (let (x2,n) = wReg2 r kf in
             (wStackLoad (APPEND x1 x2) (stackLang_If cmp r' (Reg n)
               q1 q2),bs)) | Imm i ->
           (if asm_config_valid_imm conf (INR cmp) i then
             (wStackLoad x1 (stackLang_If cmp r' (Imm i) q1 q2),bs)
               else
             let r = FST kf + 1 in
             (stackLang_Seq
               ((\r w. stackLang_Inst (asm_Const r w)) r i)
               (wStackLoad x1 (stackLang_If cmp r' (Reg r) q1
                 q2)),bs)))
        | (wordLang_Loop _5 p1 _6) ->
        (let (q1,bs) = word_to_stack_comp conf perf p1 bs kf in
          (stackLang_Loop q1,bs))
        | (wordLang_Set name exp) ->
       (if name = BitmapBase then (stackLang_Skip,bs) else
        // Impossible
        match exp with wordLang_Var n -> (let (x1,r') = wReg1 n kf
          in (wStackLoad x1 (stackLang_Set name r'),bs)) | _7 ->
          (stackLang_Skip,bs))
        // impossible
        | (wordLang_Get n name) ->
        (wRegWrite1 (\r. stackLang_Get r name) n kf,bs)
        | (wordLang_Call ret dest args handler) ->
        (let (q0,dest) = call_dest dest args kf in
        match ret with NONE -> (stackLang_Seq q0 (SeqStackFree
          (word_to_stack_stack_free dest (LENGTH args) kf)
                    (stackLang_Call NONE dest NONE)),bs) | SOME
                      (vs,live,ret_code,l1,l2) ->
            (let (q1,bs) = wLive live bs kf in
            let (q2,bs) = word_to_stack_comp conf perf ret_code bs
              kf in
            let pre = (if perf then perf_call_prefix l1 l2 (FST kf)
              else stackLang_Skip) in
            let suf = (if perf then perf_call_suffix else
              stackLang_Skip) in
              match handler with NONE ->
                (let q3 = stackLang_Seq suf (copy_ret perf F kf vs
                  q2) in
                  (stackLang_Seq q0
                    (stackLang_Seq q1
                      (stackLang_Seq (StackArgs dest (LENGTH args +
                        1) kf)
                        (stackLang_Seq pre
                          (stackLang_Call (SOME (q3,0,l1,l2)) dest
                            NONE)))),
                   bs)) | SOME (handle_var,handle_code,h1,h2) ->
                (let q3 = stackLang_Seq suf (copy_ret perf T kf vs
                  (PopHandler perf kf q2)) in
                let (q4,bs) = word_to_stack_comp conf perf
                  handle_code bs kf in
                  (stackLang_Seq q0
                     (stackLang_Seq q1
                       (stackLang_Seq (PushHandler perf h1 h2 kf)
                         (stackLang_Seq (StackHandlerArgs perf dest
                           (LENGTH args + 1) kf)
                           (stackLang_Seq pre
                             (stackLang_Call (SOME (q3,0,l1,l2))
                               dest (SOME (q4,h1,h2))))))),
                   bs))))
        | (wordLang_Alloc r live) ->
        (let (q1,bs) = wLive live bs kf in
          (stackLang_Seq q1 (stackLang_Alloc 1),bs))
        | (wordLang_StoreConsts a b c d ws) ->
        (let (new_bs,i) = insert_bitmap (const_words_to_bitmap ws
          (LENGTH ws)) bs in
          (stackLang_Seq (stackLang_Inst (asm_Const 1 (n2w i)))
               (stackLang_StoreConsts (FST kf) (FST kf + 1) (SOME
                 stackLang_store_consts_stub_location)),new_bs))
        | (wordLang_LocValue r l1) -> (wRegWrite1 (\r.
          stackLang_LocValue r l1 0) r kf,bs)
        | (wordLang_Install r1 r2 r3 r4 live) ->
       (let (l3,r3) = wReg1 r3 kf in
       let (l4,r4) = wReg2 r4 kf in
         (wStackLoad (APPEND l3 l4) (stackLang_Install (r1 DIV 2)
           (r2 DIV 2) r3 r4 0),bs))
        | (wordLang_CodeBufferWrite r1 r2) ->
       (let (l1,r1) = wReg1 r1 kf in
       let (l2,r2) = wReg2 r2 kf in
         (wStackLoad (APPEND l1 l2) (stackLang_CodeBufferWrite r1
           r2),bs))
        | (wordLang_DataBufferWrite r1 r2) ->
       (let (l1,r1) = wReg1 r1 kf in
       let (l2,r2) = wReg2 r2 kf in
         (wStackLoad (APPEND l1 l2) (stackLang_DataBufferWrite r1
           r2),bs))
        | (wordLang_FFI i r1 r2 r3 r4 live) -> (stackLang_FFI i (r1
          DIV 2) (r2 DIV 2)
                              (r3 DIV 2) (r4 DIV 2) 0,bs)
        | (wordLang_ShareInst op v exp) ->
      (match exp_to_addr exp with
         NONE -> (stackLang_Skip,bs) | SOME addr' -> wShareInst op v
           addr' kf,bs)
        | _8 -> (stackLang_Skip,bs)`];;

let raise_stub_def = new_definition
  `raise_stub perf k =
      stackLang_Seq (stackLang_Get k Handler)
     (stackLang_Seq (stackLang_StackSetSize k)
     (stackLang_Seq (if perf then
             stackLang_list_Seq [
               // restore %rsp from slot 3
               stackLang_StackLoad k 3;
               stackLang_Inst (asm_Arith (asm_Binop asm_Or perf_rsp k
                 (Reg k)));
               // restore %rbp from slot 4
               stackLang_StackLoad k 4;
               stackLang_Inst (asm_Arith (asm_Binop asm_Or perf_rbp k
                 (Reg k)))] else stackLang_Skip)
     (stackLang_Seq (stackLang_StackLoad k 2)
     (
      // next handler
      stackLang_Seq (stackLang_Set Handler k)
     (stackLang_Seq (stackLang_StackLoad k 1)
     (
      // handler pc
      stackLang_Seq (stackLang_StackFree (handler_slots perf))
          (stackLang_Raise k)))))))`;;

let store_consts_stub_def = new_definition
  `store_consts_stub k =
     stackLang_Seq (stackLang_StoreConsts k (k + 1) NONE)
       (stackLang_Return 0)`;;

(*stack args are in wordLang vars 0,2,4,...,2*(k-1), 2*k , ...*)
(*2*k and above are "stack" variables*)
(*We always allocate enough space for the maximum stack var*)
let word_to_stack_compile_prog_def = new_definition
  `word_to_stack_compile_prog asm_conf perf (prog:'a wordLang_prog)
  arg_count reg_count bitmaps =
     (let stack_arg_count' = arg_count - reg_count in
     let stack_var_count = MAX ((max_var prog DIV 2 + 1) - reg_count)
       stack_arg_count' in
     let f = (if stack_var_count = 0 then 0 else stack_var_count + 1)
       in
     let (q1,bitmaps) = word_to_stack_comp asm_conf perf prog bitmaps
       (reg_count,f,stack_var_count) in
       (stackLang_Seq (stackLang_StackAlloc (f -
         stack_arg_count')) q1,f,bitmaps))`;;

let compile_word_to_stack_def,compile_word_to_stack_ind = define_rec
  [`compile_word_to_stack asm_conf perf k [] bitmaps =
    ([],[],bitmaps)`;
   `compile_word_to_stack asm_conf perf k (CONS (i,n,p) progs) bitmaps =
         (let (prog,f,bitmaps) = word_to_stack_compile_prog asm_conf
             perf p n k bitmaps in
         let (progs,fs,bitmaps) = compile_word_to_stack asm_conf
             perf k progs bitmaps in
           (CONS (i,prog) progs,CONS f fs,bitmaps))`];;

let word_to_stack_compile_def = new_definition
  `word_to_stack_compile asm_conf perf progs =
     (let k = asm_config_reg_count asm_conf - (5 + LENGTH
       (asm_config_avoid_regs asm_conf)) in
     // Since we increase the slots for the handler when perf=T, we need to
     // update the bitmap to ensure that GC leaves the new entries alone.
     let init_bitmaps =
         (if perf then (misc_List [(n2w 16)],1) else (misc_List [(n2w
           4)],1)) in
     let (progs,fs,bitmaps) = compile_word_to_stack asm_conf perf k
       progs init_bitmaps in
     let sfs = fromAList (MAP (\((i,_9),n). (i,n)) (ZIP progs fs)) in
       (append (FST bitmaps),
        mk_word_to_stack_config (SND bitmaps) sfs,CONS 0 fs,CONS
          (raise_stub_location,raise_stub perf k) (CONS
          (stackLang_store_consts_stub_location,store_consts_stub k)
          progs)))`;;

let word_to_stack_stub_names_def = new_definition
  `word_to_stack_stub_names one = [
     (raise_stub_location,implode "_Raise");
     (stackLang_store_consts_stub_location,implode
       "_StoreConsts")]`;;

(* and the interface *)
let _ = unhide_overloads ();;
