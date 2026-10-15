(* ======================================================== *)
(*  stack_names: ported from HOL4's
    compiler/backend/stack_namesScript.sml  *)
(* ======================================================== *)

(*
  This compiler phase renames the registers to fit with the target
  architecture.
*)

needs "compiler/backend/data_to_word.ml";;
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
       w | Arith (asm_Binop bop d r ri) ->
         Arith (asm_Binop bop ((tlookup) f d) ((tlookup) f r)
           (ri_find_name f ri)) | Arith (Shift sop d r ri) ->
         Arith (Shift sop ((tlookup) f d) ((tlookup) f r)
           (ri_find_name f ri)) | Arith (Div r1 r2 r3) ->
         Arith (Div ((tlookup) f r1) ((tlookup) f r2) ((tlookup) f
           r3)) | Arith (asm_AddCarry r1 r2 r3 r4) ->
         Arith (asm_AddCarry ((tlookup) f r1) ((tlookup) f r2)
           ((tlookup) f r3) ((tlookup) f r4)) | Arith (asm_AddOverflow
           r1 r2 r3 r4) ->
         Arith (asm_AddOverflow ((tlookup) f r1) ((tlookup) f r2)
           ((tlookup) f r3) ((tlookup) f r4)) | Arith (asm_SubOverflow
           r1 r2 r3 r4) ->
         Arith (asm_SubOverflow ((tlookup) f r1) ((tlookup) f r2)
           ((tlookup) f r3) ((tlookup) f r4)) | Arith (asm_LongMul r1 r2
           r3 r4) ->
         Arith (asm_LongMul ((tlookup) f r1) ((tlookup) f r2)
           ((tlookup) f r3) ((tlookup) f r4)) | Arith (asm_LongDiv r1 r2
           r3 r4 r5) ->
         Arith (asm_LongDiv ((tlookup) f r1) ((tlookup) f r2)
           ((tlookup) f r3) ((tlookup) f r4) ((tlookup) f r5)) |
           asm_Mem mop r (Addr a w) -> asm_Mem mop ((tlookup) f r)
           (Addr ((tlookup) f a) w) | asm_FP (FPLess r f1 f2) ->
           asm_FP (FPLess ((tlookup) f r) f1 f2) | asm_FP
           (FPLessEqual r f1 f2) -> asm_FP (FPLessEqual ((tlookup) f
           r) f1 f2) | asm_FP (FPEqual r f1 f2) -> asm_FP (FPEqual
           ((tlookup) f r) f1 f2) | asm_FP (FPMovToReg r1 r2 d) ->
           asm_FP (FPMovToReg ((tlookup) f r1) ((tlookup) f r2) d) |
           asm_FP (FPMovFromReg d r1 r2) -> asm_FP (FPMovFromReg d
           ((tlookup) f r1) ((tlookup) f r2)) | i -> i)`;;

let dest_find_name_def = cake_define
  `dest_find_name f x =
      match x with
        (INR r) -> INR ((tlookup) f r)
      | x -> x`;;

(* HOL4 ML code, not ported:
local val comp_quotation = `
  comp f p =
    case p of
    | Halt r => Halt (find_name f r)
    | Raise r => Raise (find_name f r)
    | Break n => Break n
    | Continue n => Continue n
    | Return r => Return (find_name f r)
    | Inst i => Inst (inst_find_name f i)
    | LocValue i l1 l2 => LocValue (find_name f i) l1 l2
    | Seq p1 p2 => Seq (comp f p1) (comp f p2)
    | If c r ri p1 p2 =>
        If c (find_name f r) (ri_find_name f ri) (comp f p1) (comp f p2)
    | Loop p1 => Loop (comp f p1)
    | Call ret dest exc =>
        Call (case ret of
              | NONE => NONE
              | SOME (p1,lr,l1,l2) => SOME (comp f p1,find_name f
                lr,l1,l2))
             (dest_find_name f dest)
             (case exc of
              | NONE => NONE
              | SOME (p2,l1,l2) => SOME (comp f p2,l1,l2))
    | Install r1 r2 r3 r4 r5 => Install (find_name f r1) (find_name f
      r2)
      (find_name f r3) (find_name f r4) (find_name f r5)
    | ShMemOp op r (Addr a w) => ShMemOp op (find_name f r) (Addr
      (find_name f a) w)
    | CodeBufferWrite r1 r2 => CodeBufferWrite (find_name f r1)
      (find_name f r2)
    | FFI i r1 r2 r3 r4 r5 => FFI i (find_name f r1) (find_name f r2)
      (find_name f r3)
                                    (find_name f r4) (find_name f r5)
    | JumpLower r1 r2 dest => JumpLower (find_name f r1) (find_name f
      r2) dest
    | p => p`
in
val comp_def = Define comp_quotation
*)

let prog_comp_def = cake_define
  `stack_names_prog_comp f (n,p) = (n,comp f p)`;;
hol4_overload "prog_comp" "stack_names_prog_comp";;

let compile_def = cake_define
  `stack_names_compile f prog = MAP (prog_comp f) prog`;;
hol4_overload "compile" "stack_names_compile";;

(* some defaults *)

let names_ok_def = cake_define
  `names_ok names reg_count avoid_regs =
     (let xs = GENLIST ((tlookup) names) (reg_count - LENGTH
       avoid_regs) in
       ALL_DISTINCT xs /\
       EVERY (\x. x < reg_count /\ ~(MEM x avoid_regs)) xs)`;;
