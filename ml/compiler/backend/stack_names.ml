(* ======================================================== *)
(*  stack_names: ported from HOL4's
    compiler/backend/stack_namesScript.sml  *)
(* ======================================================== *)

(*
  This compiler phase renames the registers to fit with the target
  architecture.
*)

needs "compiler/backend/pattern_matching/pattern_semantics.ml";;
needs "compiler/backend/stackLang.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;

(* HOL4 overload (expanded in the port):
     find_name = tlookup *)

let ri_find_name_def = cake_define
  `(ri_find_name f (Reg r) = Reg ((tlookup) f r)) /\
   (ri_find_name f (Imm w) = Imm w)`;;

let inst_find_name_def = cake_define
  `inst_find_name f i =
     (match i with Skip -> Skip | Const r w -> Const ((tlookup) f r)
       w | Arith (Binop bop d r ri) ->
         Arith (Binop bop ((tlookup) f d) ((tlookup) f r)
           (ri_find_name f ri)) | Arith (Shift sop d r ri) ->
         Arith (Shift sop ((tlookup) f d) ((tlookup) f r)
           (ri_find_name f ri)) | Arith (Div r1 r2 r3) ->
         Arith (Div ((tlookup) f r1) ((tlookup) f r2) ((tlookup) f
           r3)) | Arith (AddCarry r1 r2 r3 r4) ->
         Arith (AddCarry ((tlookup) f r1) ((tlookup) f r2) ((tlookup)
           f r3) ((tlookup) f r4)) | Arith (AddOverflow r1 r2 r3 r4) ->
         Arith (AddOverflow ((tlookup) f r1) ((tlookup) f r2)
           ((tlookup) f r3) ((tlookup) f r4)) | Arith (SubOverflow r1 r2
           r3 r4) ->
         Arith (SubOverflow ((tlookup) f r1) ((tlookup) f r2)
           ((tlookup) f r3) ((tlookup) f r4)) | Arith (LongMul r1 r2 r3
           r4) ->
         Arith (LongMul ((tlookup) f r1) ((tlookup) f r2) ((tlookup)
           f r3) ((tlookup) f r4)) | Arith (LongDiv r1 r2 r3 r4 r5) ->
         Arith (LongDiv ((tlookup) f r1) ((tlookup) f r2)
           ((tlookup) f r3) ((tlookup) f r4) ((tlookup) f r5)) | Mem
           mop r (Addr a w) -> Mem mop ((tlookup) f r) (Addr
           ((tlookup) f a) w) | FP (FPLess r f1 f2) -> FP (FPLess
           ((tlookup) f r) f1 f2) | FP (FPLessEqual r f1 f2) -> FP
           (FPLessEqual ((tlookup) f r) f1 f2) | FP (FPEqual r f1 f2)
           -> FP (FPEqual ((tlookup) f r) f1 f2) | FP (FPMovToReg r1
           r2 d) -> FP (FPMovToReg ((tlookup) f r1) ((tlookup) f r2)
           d) | FP (FPMovFromReg d r1 r2) -> FP (FPMovFromReg d
           ((tlookup) f r1) ((tlookup) f r2)) | i -> i)`;;

let dest_find_name_def = cake_define
  `dest_find_name f x =
      match x with
        (INR r) -> INR ((tlookup) f r)
      | x -> x`;;

let comp_def = cake_define
  `stack_names_comp f p =
     (match p with Halt r -> Halt ((tlookup) f r) | Raise r -> Raise
       ((tlookup) f r) | Break n -> Break n | Continue n -> Continue n |
       Return r -> Return ((tlookup) f r) | Inst i -> Inst
       (inst_find_name f i) | LocValue i l1 l2 -> LocValue ((tlookup) f
       i) l1 l2 | Seq p1 p2 -> Seq (stack_names_comp f p1)
       (stack_names_comp f p2) | If c r ri p1 p2 ->
         If c ((tlookup) f r) (ri_find_name f ri) (stack_names_comp f
           p1) (stack_names_comp f p2) | Loop p1 -> Loop
           (stack_names_comp f p1) | Call ret dest exc ->
         Call (match ret with NONE -> NONE | SOME (p1,lr,l1,l2) ->
           SOME (stack_names_comp f p1,(tlookup) f lr,l1,l2))
              (dest_find_name f dest)
              (match exc with NONE -> NONE | SOME (p2,l1,l2) -> SOME
                (stack_names_comp f p2,l1,l2)) | Install r1 r2 r3 r4 r5
                -> Install ((tlookup) f r1) ((tlookup) f r2)
       ((tlookup) f r3) ((tlookup) f r4) ((tlookup) f r5) | ShMemOp
         op r (Addr a w) -> ShMemOp op ((tlookup) f r) (Addr ((tlookup)
         f a) w) | CodeBufferWrite r1 r2 -> CodeBufferWrite ((tlookup) f
         r1) ((tlookup) f r2) | FFI i r1 r2 r3 r4 r5 -> FFI i ((tlookup)
         f r1) ((tlookup) f r2) ((tlookup) f r3)
                              ((tlookup) f r4) ((tlookup) f r5) |
                                JumpLower r1 r2 dest -> JumpLower
                                ((tlookup) f r1) ((tlookup) f r2)
                                dest | p -> p)`;;
hol4_overload "comp" "stack_names_comp";;

let prog_comp_def = cake_define
  `stack_names_prog_comp f (n,p) = (n,comp f p)`;;
hol4_overload "prog_comp" "stack_names_prog_comp";;

let compile_def = cake_define
  `stack_names_compile f prog = MAP (prog_comp f) prog`;;
hol4_overload "compile" "stack_names_compile";;

(* some defaults *)

let names_ok_def = cake_define
  `stack_names_names_ok names reg_count avoid_regs =
     (let xs = GENLIST ((tlookup) names) (reg_count - LENGTH
       avoid_regs) in
       ALL_DISTINCT xs /\
       EVERY (\x. x < reg_count /\ ~(MEM x avoid_regs)) xs)`;;
hol4_overload "names_ok" "stack_names_names_ok";;
