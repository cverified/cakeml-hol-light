(* ======================================================== *)
(*  monadic_enc: ported from HOL4's
    compiler/encoders/monadic_enc/monadic_encScript.sml
    A definition theory, with 10 definitions and no theorems.
    Needed by monadic_enc32.ml, monadic_enc64.ml, to_target32Prog.ml
    and to_target64Prog.ml.  *)
(* ======================================================== *)

(*
  Implement and prove correct monadic version of encoder
*)

needs "compiler/backend/lab_to_target.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "semantics/ast.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "monadic_enc"
  ["asm"; "lab_to_target"];;

(*
  This hash function is roughly a rolling hash
  The modulus m is a hash size parameter
*)
let hash_reg_imm_def = define_cases
  `(hash_reg_imm m (asm_Reg reg) = reg) /\
   (hash_reg_imm m (asm_Imm imm) = 67 + (w2n imm MOD m))`;;

let hash_binop_def = define_cases
  `(hash_binop asm_Add = 0) /\
   (hash_binop asm_Sub = 1) /\
   (hash_binop asm_And = 2) /\
   (hash_binop asm_Or = 3) /\
   (hash_binop asm_Xor = 4)`;;

let hash_cmp_def = define_cases
  `(hash_cmp asm_Equal = 5) /\
   (hash_cmp asm_Lower = 6) /\
   (hash_cmp asm_Less = 7) /\
   (hash_cmp asm_Test = 8) /\
   (hash_cmp asm_NotEqual = 9) /\
   (hash_cmp asm_NotLower = 10) /\
   (hash_cmp asm_NotLess = 11) /\
   (hash_cmp asm_NotTest = 12)`;;

let hash_shift_def = define_cases
  `(hash_shift Lsl = 13) /\
   (hash_shift Lsr = 14) /\
   (hash_shift Asr = 15) /\
   (hash_shift Ror = 16)`;;

let hash_memop_def = define_cases
  `(hash_memop asm_Load = 17) /\
   (hash_memop asm_Load8 = 18) /\
   (hash_memop asm_Load16 = 57) /\
   (hash_memop asm_Load32 = 56) /\
   (hash_memop asm_Store = 19) /\
   (hash_memop asm_Store8 = 20) /\
   (hash_memop asm_Store16 = 57) /\
   (hash_memop asm_Store32 = 56)`;;

let roll_hash_def,roll_hash_ind = define_guess
  `(roll_hash [] acc = acc) /\
   (roll_hash (CONS x xs) acc = roll_hash xs (31 * acc + x))`;;

(*
Roughly, roll_hash [b;c;d;e] a
gives
roll_hash [b; c; d; e] a = 31 * (31 * (31 * (31 * a + b) + c) + d) + e

Try to put largest terms at the end of the list!
*)

let hash_arith_def = define_cases
  `(hash_arith m (asm_Binop bop r1 r2 ri) =
        roll_hash [hash_binop bop; r1; r2; hash_reg_imm m ri] 21) /\
   (hash_arith m (asm_Shift sh r1 r2 ri) =
        roll_hash [hash_shift sh; r1; r2; hash_reg_imm m ri] 22) /\
   (hash_arith m (asm_Div r1 r2 r3) =
        roll_hash [r1; r2; r3] 23) /\
   (hash_arith m (asm_LongMul r1 r2 r3 r4) =
        roll_hash [r1; r2; r3; r4] 24) /\
   (hash_arith m (asm_LongDiv r1 r2 r3 r4 r5) =
        roll_hash [r1; r2; r3; r4; r5] 25) /\
   (hash_arith m (asm_AddCarry r1 r2 r3 r4) =
        roll_hash [r1; r2; r3; r4] 26) /\
   (hash_arith m (asm_AddOverflow r1 r2 r3 r4) =
        roll_hash [r1; r2; r3; r4] 27) /\
   (hash_arith m (asm_SubOverflow r1 r2 r3 r4) =
        roll_hash [r1; r2; r3; r4] 28)`;;

let hash_fp_def = define_cases
  `(hash_fp (FPLess r f1 f2) =
        roll_hash [r; f1; f2] 29) /\
   (hash_fp (FPLessEqual r f1 f2) =
        roll_hash [r; f1; f2] 30) /\
   (hash_fp (FPEqual r f1 f2) =
        roll_hash [r; f1; f2] 31) /\
   (hash_fp (FPAbs f1 f2) =
        roll_hash [f1; f2] 32) /\
   (hash_fp (FPNeg f1 f2) =
        roll_hash [f1; f2] 33) /\
   (hash_fp (FPSqrt f1 f2) =
        roll_hash [f1; f2] 34) /\
   (hash_fp (FPAdd f1 f2 f3) =
        roll_hash [f1; f2; f3] 35) /\
   (hash_fp (FPSub f1 f2 f3) =
        roll_hash [f1; f2; f3] 36) /\
   (hash_fp (FPMul f1 f2 f3) =
        roll_hash [f1; f2; f3] 37) /\
   (hash_fp (FPDiv f1 f2 f3) =
        roll_hash [f1; f2; f3] 38) /\
   (hash_fp (FPFma f1 f2 f3) =
        roll_hash [f1; f2; f3] 39) /\
   (hash_fp (FPMov f1 f2) =
        roll_hash [f1; f2] 40) /\
   (hash_fp (FPMovToReg r1 r2 f) =
        roll_hash [r1; r2; f] 41) /\
   (hash_fp (FPMovFromReg f r1 r2) =
        roll_hash [f; r1; r2] 42) /\
   (hash_fp (FPToInt f1 f2) =
        roll_hash [f1; f2] 43) /\
   (hash_fp (FPFromInt f1 f2) =
        roll_hash [f1; f2] 44)`;;

let hash_inst_def = new_definition
  `hash_inst m x2 =
     match x2 with
       asm_Skip -> 45
     | asm_Const r w ->
       roll_hash [r; w2n w MOD m] 46
     | asm_Arith a ->
       roll_hash [hash_arith m a] 47
     | asm_Mem mop r (Addr rr w) ->
       roll_hash [hash_memop mop; r; rr; w2n w MOD m] 48
     | asm_FP fp ->
       roll_hash [hash_fp fp] 49`;;

let hash_asm_def = define_cases
  `(hash_asm m (asm_Inst i) =
        roll_hash [hash_inst m i] 50) /\
   (hash_asm m (asm_Jump w) =
        roll_hash [w2n w MOD m] 51) /\
   (hash_asm m (asm_JumpCmp c r ri w) =
        roll_hash [hash_cmp c; r; hash_reg_imm m ri; w2n w MOD m] 52) /\
   (hash_asm m (asm_Call w) =
        roll_hash [w2n w MOD m] 53) /\
   (hash_asm m (asm_JumpReg r) =
        roll_hash [r] 54) /\
   (hash_asm m (asm_Loc r w) =
        roll_hash [r; w2n w MOD m] 55)`;;

(* and the interface *)
let _ = unhide_overloads ();;
