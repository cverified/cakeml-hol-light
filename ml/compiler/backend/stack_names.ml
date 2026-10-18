(* ======================================================== *)
(*  stack_names: ported from HOL4's
    compiler/backend/stack_namesScript.sml
    A definition theory, with 7 definitions and 1 theorem.  Needed
    by stackProps.ml, stack_namesProof.ml, stack_removeProof.ml,
    stack_to_lab.ml and word_to_stackProof.ml.  *)
(* ======================================================== *)

(*
  This compiler phase renames the registers to fit with the target
  architecture.
*)

needs "compiler/backend/stackLang.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;

(* HOL4 stack_namesScript.sml:14: the overload find_name, which the
   port expands *)

let ri_find_name_def = cake_define_list
  [`ri_find_name f (Reg r) = Reg (tlookup f r)`;
   `ri_find_name f (Imm w) = Imm w`];;

let inst_find_name_def = cake_define
  `inst_find_name f i =
     (match i with Skip -> Skip | asm_Const r w -> asm_Const (tlookup
       f r) w | Arith (asm_Binop bop d r ri) ->
         Arith (asm_Binop bop (tlookup f d) (tlookup f r)
           (ri_find_name f ri)) | Arith (asm_Shift sop d r ri) ->
         Arith (asm_Shift sop (tlookup f d) (tlookup f r)
           (ri_find_name f ri)) | Arith (asm_Div r1 r2 r3) ->
         Arith (asm_Div (tlookup f r1) (tlookup f r2) (tlookup f r3))
           | Arith (asm_AddCarry r1 r2 r3 r4) ->
         Arith (asm_AddCarry (tlookup f r1) (tlookup f r2) (tlookup f
           r3) (tlookup f r4)) | Arith (asm_AddOverflow r1 r2 r3 r4) ->
         Arith (asm_AddOverflow (tlookup f r1) (tlookup f r2)
           (tlookup f r3) (tlookup f r4)) | Arith (asm_SubOverflow r1 r2
           r3 r4) ->
         Arith (asm_SubOverflow (tlookup f r1) (tlookup f r2)
           (tlookup f r3) (tlookup f r4)) | Arith (asm_LongMul r1 r2 r3
           r4) ->
         Arith (asm_LongMul (tlookup f r1) (tlookup f r2) (tlookup f
           r3) (tlookup f r4)) | Arith (asm_LongDiv r1 r2 r3 r4 r5) ->
         Arith (asm_LongDiv (tlookup f r1) (tlookup f r2) (tlookup
           f r3) (tlookup f r4) (tlookup f r5)) | asm_Mem mop r (Addr
           a w) -> asm_Mem mop (tlookup f r) (Addr (tlookup f a) w) |
           asm_FP (FPLess r f1 f2) -> asm_FP (FPLess (tlookup f r) f1
           f2) | asm_FP (FPLessEqual r f1 f2) -> asm_FP (FPLessEqual
           (tlookup f r) f1 f2) | asm_FP (FPEqual r f1 f2) -> asm_FP
           (FPEqual (tlookup f r) f1 f2) | asm_FP (FPMovToReg r1 r2
           d) -> asm_FP (FPMovToReg (tlookup f r1) (tlookup f r2) d)
           | asm_FP (FPMovFromReg d r1 r2) -> asm_FP (FPMovFromReg d
           (tlookup f r1) (tlookup f r2)) | i -> i)`;;

let dest_find_name_def = cake_define
  `dest_find_name f x =
      match x with
        INR r -> INR (tlookup f r)
      | x -> x`;;

let comp_def = cake_define
  `stack_names_comp f p =
     (match p with stackLang_Halt r -> stackLang_Halt (tlookup f r) |
       Raise r -> Raise (tlookup f r) | stackLang_Break n ->
       stackLang_Break n | stackLang_Continue n -> stackLang_Continue n
       | stackLang_Return r -> stackLang_Return (tlookup f r) | Inst i
       -> Inst (inst_find_name f i) | stackLang_LocValue i l1 l2 ->
       stackLang_LocValue (tlookup f i) l1 l2 | stackLang_Seq p1 p2 ->
       stackLang_Seq (stack_names_comp f p1) (stack_names_comp f p2) |
       If c r ri p1 p2 ->
         If c (tlookup f r) (ri_find_name f ri) (stack_names_comp f
           p1) (stack_names_comp f p2) | stackLang_Loop p1 ->
           stackLang_Loop (stack_names_comp f p1) | Call ret dest exc ->
         Call (match ret with NONE -> NONE | SOME (p1,lr,l1,l2) ->
           SOME (stack_names_comp f p1,tlookup f lr,l1,l2))
              (dest_find_name f dest)
              (match exc with NONE -> NONE | SOME (p2,l1,l2) -> SOME
                (stack_names_comp f p2,l1,l2)) | stackLang_Install r1 r2
                r3 r4 r5 -> stackLang_Install (tlookup f r1) (tlookup f
                r2)
       (tlookup f r3) (tlookup f r4) (tlookup f r5) |
         stackLang_ShMemOp op r (Addr a w) -> stackLang_ShMemOp op
         (tlookup f r) (Addr (tlookup f a) w) |
         stackLang_CodeBufferWrite r1 r2 -> stackLang_CodeBufferWrite
         (tlookup f r1) (tlookup f r2) | FFI i r1 r2 r3 r4 r5 -> FFI i
         (tlookup f r1) (tlookup f r2) (tlookup f r3)
                              (tlookup f r4) (tlookup f r5) |
                                stackLang_JumpLower r1 r2 dest ->
                                stackLang_JumpLower (tlookup f r1)
                                (tlookup f r2) dest | p -> p)`;;
hol4_overload "comp" "stack_names_comp";;

(* HOL4 stack_namesScript.sml:89-99: a theorem that HOL4 states as
   the value of an ML expression: comp_pmatch *)

let prog_comp_def = cake_define
  `stack_names_prog_comp f (n,p) = (n,stack_names_comp f p)`;;
hol4_overload "prog_comp" "stack_names_prog_comp";;

let compile_def = cake_define
  `stack_names_compile f prog = MAP (stack_names_prog_comp f) prog`;;
hol4_overload "compile" "stack_names_compile";;

(* some defaults *)

let names_ok_def = cake_define
  `stack_names_names_ok names reg_count avoid_regs =
     (let xs = GENLIST (tlookup names) (reg_count - LENGTH
       avoid_regs) in
       ALL_DISTINCT xs /\
       EVERY (\x. x < reg_count /\ ~(MEM x avoid_regs)) xs)`;;
hol4_overload "names_ok" "stack_names_names_ok";;
