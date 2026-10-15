(* ======================================================== *)
(*  word_to_stack: ported from HOL4's
    compiler/backend/word_to_stackScript.sml  *)
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
needs "compiler/backend/pattern_matching/pattern_semantics.ml";;
needs "compiler/backend/reg_alloc/parmove.ml";;
needs "compiler/backend/stackLang.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/backend/word_alloc.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "lib/sptree.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;

(* bitmaps_length stores the current length of the bitmaps *)
let word_to_stack_config_FIELDS = define_record "word_to_stack_config"
  ["bitmaps_length","num";
   "stack_frame_size","num spt"];;

(* -- *)

(* Here k = number of registers
    and f = size of stack frame
    and f' = number of slots in stack frame (= f - bitmap_size)
    and kf = (k,f,f') *)

let wReg1_def = cake_define
  `wReg1 r (k,f,(f':num)) =
     (let r = r DIV 2 in
       if r < k then ([],r) else ([(k,f - 1 - (r - k))],(k:num)))`;;

let wReg2_def = cake_define
  `wReg2 r (k,f,(f':num)) =
     (let r = r DIV 2 in
       if r < k then ([],r) else ([(k + 1,f - 1 - (r - k))],k +
         (1:num)))`;;

let wRegWrite1_def = cake_define
  `wRegWrite1 g r (k,f,(f':num)) =
     (let r = r DIV 2 in
       if r < k then g r else Seq (g k) (StackStore k (f - 1 - (r
         - k))))`;;

let wRegWrite2_def = cake_define
  `wRegWrite2 g r (k,f,(f':num)) =
     (let r = r DIV 2 in
       if r < k then g r else Seq (g (k + 1)) (StackStore (k + 1)
         (f - 1 - (r - k))))`;;

let wStackLoad_def = cake_define
  `(wStackLoad [] x = x) /\
   (wStackLoad ((r,i) :: ps) x = Seq (StackLoad r i) (wStackLoad
     ps x))`;;

let wStackStore_def = cake_define
  `(wStackStore [] x = x) /\
   (wStackStore ((r,i) :: ps) x = Seq (wStackStore ps x)
     (StackStore r i))`;;

let wMoveSingle_def = cake_define
  `wMoveSingle (x,y) (k,f,(f':num)) =
     (match (x,y) with (INL r1,INL r2) -> Inst (Arith (Binop Or r1 r2
       (Reg r2))) | (INL r1,INR r2) -> StackLoad r1 (f - 1 - (r2 - k)) |
       (INR r1,INL r2) -> StackStore r2 (f - 1 - (r1 - k)) | (INR r1,INR
       r2) -> Seq (StackLoad k (f - 1 - (r2 - k)))
                              (StackStore k (f - 1 - (r1 - k))))`;;

let wMoveAux_def = cake_define
  `wMoveAux x1 kf =
        match x1 with
          [] -> Skip
        | [xy] -> wMoveSingle xy kf
        | (xy :: xys) -> Seq (wMoveSingle xy kf) (wMoveAux xys kf)`;;

let format_var_def = cake_define
  `(format_var k NONE = INL (k + 1)) /\
   (format_var k (SOME x) = (if x < (k:num) then INL x else INR
     x))`;;

let wMove_def = cake_define
  `wMove xs (k,(f:num),(f':num)) =
     wMoveAux (MAP (format_var k ## format_var k) (parmove (MAP
       (DIV2 ## DIV2) xs))) (k,f,f')`;;

let wInst_def = cake_define
  `wInst x1 kf =
        match x1 with
          ((Const n c):'a asm_inst) ->
       wRegWrite1 (\n. Inst (Const n c)) n kf
        | (Arith (Binop bop n1 n2 (Imm imm))) ->
       let (l,n2) = wReg1 n2 kf in
       wStackLoad l
         (wRegWrite1 (\n1. Inst (Arith (Binop bop n1 n2 (Imm imm))))
           n1 kf)
        | (Arith (Binop bop n1 n2 (Reg n3))) ->
       let (l,n2) = wReg1 n2 kf in
       let (l',n3) = wReg2 n3 kf in
       wStackLoad (l ++ l')
         (wRegWrite1 (\n1. Inst (Arith (Binop bop n1 n2 (Reg n3))))
           n1 kf)
        | (Arith (Shift sh n1 n2 (Imm imm))) ->
       let (l,n2) = wReg1 n2 kf in
       wStackLoad l
         (wRegWrite1 (\n1. Inst (Arith (Shift sh n1 n2 (Imm imm))))
           n1 kf)
        | (Arith (Shift sh n1 n2 (Reg n3))) ->
       let (l,n2) = wReg1 n2 kf in
       let (l',n3) = wReg2 n3 kf in
       wStackLoad (l ++ l')
         (wRegWrite1 (\n1. Inst (Arith (Shift sh n1 n2 (Reg n3)))) n1
           kf)
        | (Arith (Div n1 n2 n3)) ->
       let (l,n2) = wReg1 n2 kf in
       let (l',n3) = wReg2 n3 kf in
       wStackLoad (l ++ l')
         (wRegWrite1 (\n1. Inst (Arith (Div n1 n2 n3))) n1 kf)
        | (Arith (AddCarry n1 n2 n3 n4)) ->
       let (l,n2) = wReg1 n2 kf in
       let (l',n3) = wReg2 n3 kf in
       wStackLoad (l ++ l')
         (wRegWrite1 (\n1. Inst (Arith (AddCarry n1 n2 n3 n4))) n1
           kf)
        | (Arith (AddOverflow n1 n2 n3 n4)) ->
       let (l,n2) = wReg1 n2 kf in
       let (l',n3) = wReg2 n3 kf in
       wStackLoad (l ++ l')
         (wRegWrite1 (\n1. Inst (Arith (AddOverflow n1 n2 n3 n4))) n1
           kf)
        | (Arith (SubOverflow n1 n2 n3 n4)) ->
       let (l,n2) = wReg1 n2 kf in
       let (l',n3) = wReg2 n3 kf in
       wStackLoad (l ++ l')
         (wRegWrite1 (\n1. Inst (Arith (SubOverflow n1 n2 n3 n4))) n1
           kf)
        | (Arith (LongMul n1 n2 n3 n4)) ->
         (Inst (Arith (LongMul 3 0 0 2)))
        | (Arith (LongDiv n1 n2 n3 n4 n5)) ->
       let (l,n5) = wReg1 n5 kf in
       wStackLoad l
         (Inst (Arith (LongDiv 0 3 3 0 n5)))
        | (Mem Load n1 (Addr n2 offset)) ->
       let (l,n2) = wReg1 n2 kf in
       wStackLoad l
         (wRegWrite1 (\n1. Inst (Mem Load n1 (Addr n2 offset))) n1
           kf)
        | (Mem Store n1 (Addr n2 offset)) ->
       let (l1,n2) = wReg1 n2 kf in
       let (l2,n1) = wReg2 n1 kf in
         wStackLoad (l1 ++ l2)
           (Inst (Mem Store n1 (Addr n2 offset)))
        | (Mem Load8 n1 (Addr n2 offset)) ->
       let (l,n2) = wReg1 n2 kf in
       wStackLoad l
         (wRegWrite1 (\n1. Inst (Mem Load8 n1 (Addr n2 offset))) n1
           kf)
        | (Mem Store8 n1 (Addr n2 offset)) ->
       let (l1,n2) = wReg1 n2 kf in
       let (l2,n1) = wReg2 n1 kf in
         wStackLoad (l1 ++ l2)
           (Inst (Mem Store8 n1 (Addr n2 offset)))
        | (Mem Load32 n1 (Addr n2 offset)) ->
       let (l,n2) = wReg1 n2 kf in
       wStackLoad l
         (wRegWrite1 (\n1. Inst (Mem Load32 n1 (Addr n2 offset))) n1
           kf)
        | (Mem Store32 n1 (Addr n2 offset)) ->
       let (l1,n2) = wReg1 n2 kf in
       let (l2,n1) = wReg2 n1 kf in
         wStackLoad (l1 ++ l2)
           (Inst (Mem Store32 n1 (Addr n2 offset)))
        | (FP (FPLess r f1 f2)) ->
       wRegWrite1 (\r. Inst (FP (FPLess r f1 f2))) r kf
        | (FP (FPLessEqual r f1 f2)) ->
       wRegWrite1 (\r. Inst (FP (FPLessEqual r f1 f2))) r kf
        | (FP (FPEqual r f1 f2)) ->
       wRegWrite1 (\r. Inst (FP (FPEqual r f1 f2))) r kf
        | (FP (FPMovToReg r1 r2 d)) ->
       if dimindex (:'a) = 64 then
         wRegWrite1 (\r1. Inst (FP (FPMovToReg r1 0 d))) r1 kf else
         wRegWrite2 (\r2. wRegWrite1 (\r1. Inst (FP (FPMovToReg r1 r2
           d))) r1 kf) r2 kf
        | (FP (FPMovFromReg d r1 r2)) ->
       let (l,n1) = wReg1 r1 kf in
       let (l',n2) =
         if dimindex (:'a) = 64 then ([],0) else wReg2 r2 kf in
       wStackLoad (l ++ l')
         (Inst (FP (FPMovFromReg d n1 n2)))
        | (FP f) -> Inst (FP f)
        | _1 -> Inst Skip`;;

let wShareInst_def = cake_define
  `wShareInst x1 v x3 kf =
        match (x1,x3) with
          (Load,(Addr ad offset)) ->
       let (l,n2) = wReg1 ad kf in
       wStackLoad l
         (wRegWrite1 (\r. ShMemOp Load r (Addr n2 offset)) v kf)
        | (Load8,(Addr ad offset)) ->
       let (l,n2) = wReg1 ad kf in
       wStackLoad l
         (wRegWrite1 (\r. ShMemOp Load8 r (Addr n2 offset)) v kf)
        | (Load16,(Addr ad offset)) ->
       let (l,n2) = wReg1 ad kf in
       wStackLoad l
         (wRegWrite1 (\r. ShMemOp Load16 r (Addr n2 offset)) v kf)
        | (Load32,(Addr ad offset)) ->
       let (l,n2) = wReg1 ad kf in
       wStackLoad l
         (wRegWrite1 (\r. ShMemOp Load32 r (Addr n2 offset)) v kf)
        | (Store,(Addr ad offset)) ->
       let (l1,n2) = wReg1 ad kf in
       let (l2,n1) = wReg2 v kf in
       wStackLoad (l1 ++ l2)
         (ShMemOp Store n1 (Addr n2 offset))
        | (Store8,(Addr ad offset)) ->
       let (l1,n2) = wReg1 ad kf in
       let (l2,n1) = wReg2 v kf in
       wStackLoad (l1 ++ l2)
         (ShMemOp Store8 n1 (Addr n2 offset))
        | (Store16,(Addr ad offset)) ->
       let (l1,n2) = wReg1 ad kf in
       let (l2,n1) = wReg2 v kf in
       wStackLoad (l1 ++ l2)
         (ShMemOp Store16 n1 (Addr n2 offset))
        | (Store32,(Addr ad offset)) ->
       let (l1,n2) = wReg1 ad kf in
       let (l2,n1) = wReg2 v kf in
       wStackLoad (l1 ++ l2)
         (ShMemOp Store32 n1 (Addr n2 offset))`;;

let bits_to_word_def = cake_define
  `(bits_to_word [] = (n2w 0)) /\
   (bits_to_word (T :: xs) = (bits_to_word xs << 1 || (n2w 1))) /\
   (bits_to_word (F :: xs) = (bits_to_word xs << 1))`;;

(* HOL4 termination: \\ fs [LENGTH_DROP] \\ DECIDE_TAC *)
let word_list_def = cake_define_wf
  `MEASURE (LENGTH o FST)`
  `word_to_stack_word_list (xs:bool list) d =
     (if LENGTH xs <= d \/ (d = 0) then [bits_to_word xs] else
       bits_to_word (TAKE d xs ++ [T]) :: word_to_stack_word_list
       (DROP d xs) d)`;;
hol4_overload "word_list" "word_to_stack_word_list";;

let write_bitmap_def = cake_define
  `((write_bitmap live k f'):('a word) list) =
     (let names = MAP (\(r,y). (f' - 1) - (r DIV 2 - k)) (toAList
       live) in
       word_list (GENLIST (\x. MEM x names) f' ++ [T]) (dimindex
         (:'a) - 1))`;;

let insert_bitmap_def = cake_define
  `insert_bitmap ws (data,data_len) =
     (let l = LENGTH ws in
       ((Append data (List ws),data_len + l),data_len))`;;

let wLive_def = cake_define
  `wLive (live:1 spt#1 spt) (bitmaps:('a word) app_list#num)
  (k,(f:num),(f':num)) =
     (if f = 0 then (Skip,bitmaps) else
       let (new_bitmaps,i) = insert_bitmap (write_bitmap (SND live) k
         f') bitmaps in
         ((Seq (Inst (Const k (n2w (i + 1)))) (StackStore k 0):'a
           stackLang_prog),new_bitmaps))`;;

let SeqStackFree_def = cake_define
  `SeqStackFree n p = (if n = 0 then p else Seq (StackFree n) p)`;;

let call_dest_def = cake_define
  `(call_dest (SOME pos) args kf = (Skip,INL pos)) /\
   (call_dest NONE args kf =
      (if LENGTH args = 0 then (Skip,INL raise_stub_location) else
        let (x1,r) = wReg2 (LAST args) kf in
          (wStackLoad x1 Skip,INR r)))`;;

let stack_arg_count_def = cake_define
  `stack_arg_count dest arg_count k =
     (match dest with INL _2 -> (arg_count - (k:num)) | INR _3 ->
       ((arg_count - 1) - (k:num)))`;;

let stack_free_def = cake_define
  `word_to_stack_stack_free dest arg_count (k,f,(f':num)) =
     f - stack_arg_count dest arg_count k`;;
hol4_overload "stack_free" "word_to_stack_stack_free";;

let stack_move_def = cake_define
  `(stack_move 0 start offset i p = p) /\
   (stack_move (SUC n) start offset i p =
      Seq (stack_move n (start + 1) offset i p)
          (Seq (StackLoad i (start + offset)) (StackStore i
            start)))`;;

let StackArgs_def = cake_define
  `StackArgs dest arg_count (k,f,(f':num)) =
     (let n = stack_arg_count dest arg_count k in
       stack_move n 0 f k (StackAlloc n))`;;

(* Unverified x64 perf-mode instrumentation.

   The idea is to "simulate" CakeML's call stack by pushing the return
     address
   and the frame pointer to the C stack, popping it when the call
     returns.
   This allows ‘perf record --call-graph fp’ to walk CakeML stack
     traces.

   Due to the presence of exceptions, we need to additionally (re)store
     the
   base pointer and stack pointer (see PushHandler and raise_stub).
 *)

(* x64_config$x64_names: 14 → 4 = RSP *)
let perf_rsp_def = cake_define
  `perf_rsp = 14`;;

(* x64_config$x64_names: 15 → 5 = RBP (HOL's x64Script.sml) *)
let perf_rbp_def = cake_define
  `perf_rbp = 15`;;

let perf_call_prefix_def = cake_define
  `perf_call_prefix l1 l2 k =
     list_Seq [
       LocValue k l1 l2;
       Inst (Mem Store k (Addr perf_rsp (--(n2w 8))));
       Inst (Mem Store perf_rbp (Addr perf_rsp (--(n2w 16))));
       Inst (Arith (Binop Sub perf_rsp perf_rsp (Imm (n2w 16))));
       Inst (Arith (Binop Or perf_rbp perf_rsp (Reg perf_rsp)))]`;;

let perf_call_suffix_def = cake_define
  `perf_call_suffix =
     list_Seq [
       Inst (Mem Load perf_rbp (Addr perf_rsp (n2w 0)));
       Inst (Arith (Binop Add perf_rsp perf_rsp (Imm (n2w 16))))]`;;

let handler_slots_def = cake_define
  `handler_slots perf = (if perf then 5 else 3)`;;

let StackHandlerArgs_def = cake_define
  `StackHandlerArgs perf dest arg_count (k,f,(f':num)) =
     StackArgs dest arg_count (k,f + handler_slots perf,f' +
       handler_slots perf)`;;

let PushHandler_def = cake_define
  `PushHandler perf l1 l2 (k,f,f') =
     Seq (StackAlloc (handler_slots perf))
    (Seq (Inst (Const k (n2w 1)))
    (Seq (StackStore k 0)
    (Seq (LocValue k l1 l2)
    (Seq (StackStore k 1)
    (Seq (Get k Handler)
    (Seq (StackStore k 2)
    (Seq (if perf then
            list_Seq [
              Inst (Arith (Binop Or k perf_rsp (Reg perf_rsp)));
              StackStore k 3;
              Inst (Arith (Binop Or k perf_rbp (Reg perf_rbp)));
              StackStore k 4] else Skip)
    (Seq (StackGetSize k)
         (Set Handler k)))))))))`;;

let PopHandler_def = cake_define
  `PopHandler perf (k,f,f') prog =
    Seq (StackLoad k 2)
   (Seq (Set Handler k)
   (Seq (StackFree (handler_slots perf))
   prog))`;;

let chunk_to_bits_def = cake_define
  `chunk_to_bits ([]) = ((n2w 1):'a word) /\
   chunk_to_bits ((b,w) :: ws) =
     (let res = (chunk_to_bits ws) << 1 in
       if b then res + (n2w 1) else res)`;;

let chunk_to_bitmap_def = cake_define
  `chunk_to_bitmap ws = chunk_to_bits ws :: MAP SND ws`;;

let const_words_to_bitmap_def = cake_define
  `const_words_to_bitmap (ws) (ws_len:num) =
     (if ws_len < (dimindex (:'a) - 1) \/ (dimindex (:'a) - 1) = 0
       then chunk_to_bitmap ws else
       let h = TAKE (dimindex (:'a) - 1) ws in
       let t = DROP (dimindex (:'a) - 1) ws in
         chunk_to_bitmap h ++ const_words_to_bitmap t (ws_len -
           (dimindex (:'a) - 1)))`;;

(* Store a large constant in the second temporary *)

(*
0                f-1 0    ...   g-1
| ----------(---)|   |----------|----stack---|
            ^
      values returned on stack
*)

(* Stack slots used in multi-arg return *)
let num_stack_ret_def = cake_define
  `num_stack_ret k vs = (
   LENGTH vs + 1) - k`;;

(* Number of slots to free by callee *)
let skip_free_def = cake_define
  `skip_free (k,f,f') vs =
     f - num_stack_ret k vs`;;

(* Caller copying from the previous stack frame into its own *)
let copy_ret_aux_def = cake_define
  `(copy_ret_aux k f n =
     (if n = 0 then Skip else
       let n' = n - 1 in
       list_Seq
       [
         StackLoad k n';
         StackStore k (n' + f);
         copy_ret_aux k f n']))`;;

let copy_ret_def = cake_define
  `copy_ret perf is_handle (k,f,f') vs kont =
   (let n = num_stack_ret k vs in
   if n = 0 then kont else Seq
       (copy_ret_aux k (if is_handle then f + handler_slots perf else
         f) n)
       (SeqStackFree n kont))`;;

(* Return should be 2,4,6,...,2k,2k+1,... *)
let comp_def = cake_define
  `word_to_stack_comp conf perf x3 bs kf =
        match x3 with
          (Skip:'a wordLang_prog) -> ((Skip:'a stackLang_prog),bs)
        | (Move _4 xs) -> (wMove xs kf,bs)
        | (Inst i) -> (wInst i kf,bs)
        | (Return v1 vs) ->
        let (xs,x) = wReg1 v1 kf in
          (wStackLoad xs (SeqStackFree (skip_free kf vs) (Return
            x)),bs)
        | (Raise v) -> (Call NONE (INL raise_stub_location) NONE,bs)
        | (OpCurrHeap b dst src) ->
        let (xs,src_r) = wReg1 src kf in
          (wStackLoad xs (wRegWrite1 (\dst_r. OpCurrHeap b dst_r
            src_r) dst kf),bs)
        | (Tick) -> (Tick,bs)
        | (Break k) -> (Break k,bs)
        | (Continue k) -> (Continue k,bs)
        | (MustTerminate p1) -> word_to_stack_comp conf perf p1 bs kf
        | (Seq p1 p2) ->
        let (q1,bs) = word_to_stack_comp conf perf p1 bs kf in
        let (q2,bs) = word_to_stack_comp conf perf p2 bs kf in
          (Seq q1 q2,bs)
        | (If cmp r ri p1 p2) ->
        let (x1,r') = wReg1 r kf in
        let (q1,bs) = word_to_stack_comp conf perf p1 bs kf in
        let (q2,bs) = word_to_stack_comp conf perf p2 bs kf in
        match ri with
          Reg r ->
            (let (x2,n) = wReg2 r kf in
             (wStackLoad (x1 ++ x2) (If cmp r' (Reg n) q1 q2),bs)) |
               Imm i ->
           (if asm_config_valid_imm conf (INR cmp) i then
             (wStackLoad x1 (If cmp r' (Imm i) q1 q2),bs) else
             let r = FST kf + 1 in
             (Seq
               ((\r w. Inst (Const r w)) r i)
               (wStackLoad x1 (If cmp r' (Reg r) q1 q2)),bs))
        | (Loop _5 p1 _6) ->
        let (q1,bs) = word_to_stack_comp conf perf p1 bs kf in
          (Loop q1,bs)
        | (Set name exp) ->
       if name = BitmapBase then (Skip,bs) else
        match exp with Var n -> (let (x1,r') = wReg1 n kf in
          (wStackLoad x1 (Set name r'),bs)) | _7 -> (Skip,bs)
        | (Get n name) ->
        (wRegWrite1 (\r. Get r name) n kf,bs)
        | (Call ret dest args handler) ->
        let (q0,dest) = call_dest dest args kf in
        match ret with NONE -> (Seq q0 (SeqStackFree (stack_free dest
          (LENGTH args) kf)
                    (Call NONE dest NONE)),bs) | SOME
                      (vs,live,ret_code,l1,l2) ->
            (let (q1,bs) = wLive live bs kf in
            let (q2,bs) = word_to_stack_comp conf perf ret_code bs kf
              in
            let pre = if perf then perf_call_prefix l1 l2 (FST kf)
              else Skip in
            let suf = if perf then perf_call_suffix else Skip in
              match handler with NONE ->
                (let q3 = Seq suf (copy_ret perf F kf vs q2) in
                  (Seq q0
                    (Seq q1
                      (Seq (StackArgs dest (LENGTH args + 1) kf)
                        (Seq pre
                          (Call (SOME (q3,0,l1,l2)) dest NONE)))),
                   bs)) | SOME (handle_var,handle_code,h1,h2) ->
                (let q3 = Seq suf (copy_ret perf T kf vs (PopHandler
                  perf kf q2)) in
                let (q4,bs) = word_to_stack_comp conf perf
                  handle_code bs kf in
                  (Seq q0
                     (Seq q1
                       (Seq (PushHandler perf h1 h2 kf)
                         (Seq (StackHandlerArgs perf dest (LENGTH
                           args + 1) kf)
                           (Seq pre
                             (Call (SOME (q3,0,l1,l2)) dest (SOME
                               (q4,h1,h2))))))),
                   bs)))
        | (Alloc r live) ->
        let (q1,bs) = wLive live bs kf in
          (Seq q1 (Alloc 1),bs)
        | (StoreConsts a b c d ws) ->
        let (new_bs,i) = insert_bitmap (const_words_to_bitmap ws
          (LENGTH ws)) bs in
          (Seq (Inst (Const 1 (n2w i)))
               (StoreConsts (FST kf) (FST kf + 1) (SOME
                 store_consts_stub_location)),new_bs)
        | (LocValue r l1) -> (wRegWrite1 (\r. LocValue r l1 0) r
          kf,bs)
        | (Install r1 r2 r3 r4 live) ->
       let (l3,r3) = wReg1 r3 kf in
       let (l4,r4) = wReg2 r4 kf in
         (wStackLoad (l3 ++ l4) (Install (r1 DIV 2) (r2 DIV 2) r3 r4
           0),bs)
        | (CodeBufferWrite r1 r2) ->
       let (l1,r1) = wReg1 r1 kf in
       let (l2,r2) = wReg2 r2 kf in
         (wStackLoad (l1 ++ l2) (CodeBufferWrite r1 r2),bs)
        | (DataBufferWrite r1 r2) ->
       let (l1,r1) = wReg1 r1 kf in
       let (l2,r2) = wReg2 r2 kf in
         (wStackLoad (l1 ++ l2) (DataBufferWrite r1 r2),bs)
        | (FFI i r1 r2 r3 r4 live) -> (FFI i (r1 DIV 2) (r2 DIV 2)
                              (r3 DIV 2) (r4 DIV 2) 0,bs)
        | (ShareInst op v exp) ->
      ((match exp_to_addr exp with
         NONE -> (Skip,bs) | SOME addr -> wShareInst op v addr
           kf),bs)
        | _8 -> (Skip,bs)`;;
hol4_overload "comp" "word_to_stack_comp";;

let raise_stub_def = cake_define
  `raise_stub perf k =
      Seq (Get k Handler)
     (Seq (StackSetSize k)
     (Seq (if perf then
             list_Seq [
               StackLoad k 3;
               Inst (Arith (Binop Or perf_rsp k (Reg k)));
               StackLoad k 4;
               Inst (Arith (Binop Or perf_rbp k (Reg k)))] else Skip)
     (Seq (StackLoad k 2)
     (Seq (Set Handler k)
     (Seq (StackLoad k 1)
     (Seq (StackFree (handler_slots perf))
          (Raise k)))))))`;;

let store_consts_stub_def = cake_define
  `store_consts_stub k =
     Seq (StoreConsts k (k + 1) NONE) (Return 0)`;;

(*stack args are in wordLang vars 0,2,4,...,2*(k-1), 2*k , ...*)
(*2*k and above are "stack" variables*)
(*We always allocate enough space for the maximum stack var*)
let compile_prog_def = cake_define
  `word_to_stack_compile_prog asm_conf perf (prog:'a wordLang_prog)
  arg_count reg_count bitmaps =
     (let stack_arg_count' = arg_count - reg_count in
     let stack_var_count = MAX ((max_var prog DIV 2 + 1) - reg_count)
       stack_arg_count' in
     let f = if stack_var_count = 0 then 0 else stack_var_count + 1
       in
     let (q1,bitmaps) = comp asm_conf perf prog bitmaps
       (reg_count,f,stack_var_count) in
       (Seq (StackAlloc (f - stack_arg_count')) q1,f,bitmaps))`;;
hol4_overload "compile_prog" "word_to_stack_compile_prog";;

let compile_word_to_stack_def = cake_define
  `(compile_word_to_stack asm_conf perf k [] bitmaps = ([],[],bitmaps))
  /\
   (compile_word_to_stack asm_conf perf k ((i,n,p) :: progs) bitmaps
     =
      (let (prog,f,bitmaps) = compile_prog asm_conf perf p n k
        bitmaps in
      let (progs,fs,bitmaps) = compile_word_to_stack asm_conf perf k
        progs bitmaps in
        ((i,prog) :: progs,f :: fs,bitmaps)))`;;

let compile_def = cake_define
  `word_to_stack_compile asm_conf perf progs =
     (let k = asm_config_reg_count asm_conf - (5 + LENGTH
       (asm_config_avoid_regs asm_conf)) in
     let init_bitmaps =
         if perf then (List [(n2w 16)],1) else (List [(n2w 4)],1) in
     let (progs,fs,bitmaps) = compile_word_to_stack asm_conf perf k
       progs init_bitmaps in
     let sfs = fromAList (MAP (\((i,_9),n). (i,n)) (ZIP (progs,fs)))
       in
       (append (FST bitmaps),
        mk_word_to_stack_config (SND bitmaps) sfs,0 :: fs,
        (raise_stub_location,raise_stub perf k) ::
        (store_consts_stub_location,store_consts_stub k) ::
          progs))`;;
hol4_overload "compile" "word_to_stack_compile";;

let stub_names_def = cake_define
  `word_to_stack_stub_names one = [
     (raise_stub_location,implode "_Raise");
     (store_consts_stub_location,implode "_StoreConsts")]`;;
hol4_overload "stub_names" "word_to_stack_stub_names";;
