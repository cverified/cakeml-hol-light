(* ======================================================== *)
(*  stack_names: ported from HOL4's
    compiler/backend/stack_namesScript.sml
    A definition theory, with 7 definitions and 1 theorem.  Needed
    by stackProps.ml, stack_namesProof.ml, stack_to_lab.ml,
    to_target32Prog.ml and to_target64Prog.ml.  *)
(* ======================================================== *)

(*
  This compiler phase renames the registers to fit with the target
  architecture.
*)

needs "compiler/backend/stackLang.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "misc/misc.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "stack_names"
  ["stackLang"];;

(* HOL4 stack_namesScript.sml:14: the overload find_name, which the port
   expands *)

let ri_find_name_def = define_cases
  `(ri_find_name f (asm_Reg r) = asm_Reg (tlookup f r)) /\
   (ri_find_name f (asm_Imm w) = asm_Imm w)`;;

let inst_find_name_def = new_definition
  `inst_find_name f i =
     match i with asm_Skip -> asm_Skip
     | asm_Const r w -> asm_Const (tlookup f r) w
     | asm_Arith (asm_Binop bop d r ri) ->
         asm_Arith (asm_Binop bop (tlookup f d) (tlookup f r) (ri_find_name
           f ri))
     | asm_Arith (asm_Shift sop d r ri) ->
         asm_Arith (asm_Shift sop (tlookup f d) (tlookup f r) (ri_find_name
           f ri))
     | asm_Arith (asm_Div r1 r2 r3) ->
         asm_Arith (asm_Div (tlookup f r1) (tlookup f r2) (tlookup f r3))
     | asm_Arith (asm_AddCarry r1 r2 r3 r4) ->
         asm_Arith (asm_AddCarry (tlookup f r1) (tlookup f r2) (tlookup f
           r3) (tlookup f r4))
     | asm_Arith (asm_AddOverflow r1 r2 r3 r4) ->
         asm_Arith (asm_AddOverflow (tlookup f r1) (tlookup f r2) (tlookup f
           r3) (tlookup f r4))
     | asm_Arith (asm_SubOverflow r1 r2 r3 r4) ->
         asm_Arith (asm_SubOverflow (tlookup f r1) (tlookup f r2) (tlookup f
           r3) (tlookup f r4))
     | asm_Arith (asm_LongMul r1 r2 r3 r4) ->
         asm_Arith (asm_LongMul (tlookup f r1) (tlookup f r2) (tlookup f r3)
           (tlookup f r4))
     | asm_Arith (asm_LongDiv r1 r2 r3 r4 r5) ->
         asm_Arith (asm_LongDiv (tlookup f r1) (tlookup f r2) (tlookup f r3)
           (tlookup f r4) (tlookup f r5))
     | asm_Mem mop r (Addr a w) -> asm_Mem mop (tlookup f r) (Addr (tlookup
       f a) w)
     | asm_FP (FPLess r f1 f2) -> asm_FP (FPLess (tlookup f r) f1 f2)
     | asm_FP (FPLessEqual r f1 f2) -> asm_FP (FPLessEqual (tlookup f r) f1
       f2)
     | asm_FP (FPEqual r f1 f2) -> asm_FP (FPEqual (tlookup f r) f1 f2)
     | asm_FP (FPMovToReg r1 r2 d) -> asm_FP (FPMovToReg (tlookup f r1)
       (tlookup f r2) d)
     | asm_FP (FPMovFromReg d r1 r2) -> asm_FP (FPMovFromReg d (tlookup f
       r1) (tlookup f r2))
     | i -> i`;;

let dest_find_name_def = new_definition
  `dest_find_name f x =
   match x with
     INR r -> INR (tlookup f r)
   | x -> x`;;

make_size "stack_prog";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let stack_names_comp_def,stack_names_comp_ind = define_wf
  `MEASURE (\(x0,x1). stack_prog_size (\x. 0) x1)`
  `stack_names_comp f p =
     match p with stack_Halt r -> stack_Halt (tlookup f r)
     | stack_Raise r -> stack_Raise (tlookup f r)
     | stack_Break n -> stack_Break n
     | stack_Continue n -> stack_Continue n
     | stack_Return r -> stack_Return (tlookup f r)
     | stack_Inst i -> stack_Inst (inst_find_name f i)
     | stack_LocValue i l1 l2 -> stack_LocValue (tlookup f i) l1 l2
     | stack_Seq p1 p2 -> stack_Seq (stack_names_comp f p1)
       (stack_names_comp f p2)
     | stack_If c r ri p1 p2 ->
         stack_If c (tlookup f r) (ri_find_name f ri) (stack_names_comp f
           p1) (stack_names_comp f p2)
     | stack_Loop p1 -> stack_Loop (stack_names_comp f p1)
     | stack_Call ret dest exc ->
         stack_Call (match ret with NONE -> NONE
               | SOME (p1,lr,l1,l2) -> SOME (stack_names_comp f p1,tlookup f
                 lr,l1,l2))
              (dest_find_name f dest)
              (match exc with NONE -> NONE
               | SOME (p2,l1,l2) -> SOME (stack_names_comp f p2,l1,l2))
     | stack_Install r1 r2 r3 r4 r5 -> stack_Install (tlookup f r1) (tlookup
       f r2)
       (tlookup f r3) (tlookup f r4) (tlookup f r5)
     | stack_ShMemOp op r (Addr a w) -> stack_ShMemOp op (tlookup f r) (Addr
       (tlookup f a) w)
     | stack_CodeBufferWrite r1 r2 -> stack_CodeBufferWrite (tlookup f r1)
       (tlookup f r2)
     | stack_FFI i r1 r2 r3 r4 r5 -> stack_FFI i (tlookup f r1) (tlookup f
       r2) (tlookup f r3)
                              (tlookup f r4) (tlookup f r5)
     | stack_JumpLower r1 r2 dest -> stack_JumpLower (tlookup f r1) (tlookup
       f r2) dest
     | p -> p`;;

(* HOL4 stack_namesScript.sml:89-99: a theorem that HOL4 states as the value
   of an ML expression: comp_pmatch *)

let stack_names_prog_comp_def = new_definition
  `stack_names_prog_comp f (n,p) = (n,stack_names_comp f p)`;;

let stack_names_compile_def = new_definition
  `stack_names_compile f prog = MAP (stack_names_prog_comp f) prog`;;

(* some defaults *)

let names_ok_def = new_definition
  `stack_names_names_ok names reg_count avoid_regs =
     let xs = list_of_seq (tlookup names) (reg_count - LENGTH avoid_regs) in
       ALL_DISTINCT xs /\
       ALL (\x. x < reg_count /\ ~(MEM x avoid_regs)) xs`;;

(* and the interface *)
let _ = unhide_overloads ();;
