(* ======================================================== *)
(*  asmSem: ported from HOL4's
    compiler/encoders/asm/asmSemScript.sml  *)
(* ======================================================== *)

(*
  The semantics of the asm instruction description.
*)

needs "compiler/backend/pattern_matching/pattern_semantics.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "lib/binary_ieee.ml";;
needs "lib/integer_word.ml";;
needs "lib/machine_ieee.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;
(* HOL4 ancestors outside the port: (* for bytes_in_memory *) *)

(* -- semantics of ASM program -- *)

let asm_state_FIELDS = define_record "asm_state"
  ["regs","num->'a word";
   "fp_regs","num->word64";
   "mem","'a word->word8";
   "mem_domain","'a word->bool";
   "pc","'a word";
   "lr","num";
   "align","num";
   "be","bool";
   "failed","bool"];;

let upd_pc_def = cake_define
  `asmSem_upd_pc pc s = asm_state_pc_fupd (K pc) s`;;
let upd_reg_def = cake_define
  `asmSem_upd_reg r v s = asm_state_regs_fupd (K ((r =+ v)
  (asm_state_regs s))) s`;;
let upd_fp_reg_def = cake_define
  `asmSem_upd_fp_reg r v s = asm_state_fp_regs_fupd (K ((r =+ v)
  (asm_state_fp_regs s))) s`;;
let upd_mem_def = cake_define
  `asmSem_upd_mem a b s = asm_state_mem_fupd (K ((a =+ b)
  (asm_state_mem s))) s`;;
let read_reg_def = cake_define
  `asmSem_read_reg r s = asm_state_regs s r`;;
let read_fp_reg_def = cake_define
  `asmSem_read_fp_reg r s = asm_state_fp_regs s r`;;
let read_mem_def = cake_define
  `asmSem_read_mem a s = asm_state_mem s a`;;

let assert_def = cake_define
  `asmSem_assert b s = asm_state_failed_fupd (K (~b \/
  asm_state_failed s)) s`;;

let reg_imm_def = cake_define_list
  [`asmSem_reg_imm (Reg r) s = asmSem_read_reg r s`;
   `asmSem_reg_imm (Imm w) s = w`];;

let binop_upd_def = cake_define_list
  [`asmSem_binop_upd r Add w1 w2 = asmSem_upd_reg r (w1 + w2)`;
   `asmSem_binop_upd r Sub w1 w2 = asmSem_upd_reg r (w1 - w2)`;
   `asmSem_binop_upd r And w1 w2 = asmSem_upd_reg r (word_and w1 w2)`;
   `asmSem_binop_upd r Or w1 w2 = asmSem_upd_reg r (word_or w1 w2)`;
   `asmSem_binop_upd r Xor w1 w2 = asmSem_upd_reg r (word_xor w1 w2)`];;

let is_test_def = cake_define
  `is_test c <=> (c = Test) \/ (c = asm_NotTest)`;;

let word_shift_def = cake_define_list
  [`asmSem_word_shift Lsl w n = w << n`;
   `asmSem_word_shift Lsr w n = w >>> n`;
   `asmSem_word_shift Asr w n = w >> n`;
   `asmSem_word_shift Ror w n = word_ror w n`];;

let arith_upd_def = cake_define_list
  [`asmSem_arith_upd (asm_Binop b r1 r2 (ri:'a asm_reg_imm)) s =
         asmSem_binop_upd r1 b (asmSem_read_reg r2 s)
           (asmSem_reg_imm ri s) s`;
   `asmSem_arith_upd (asm_Shift l r1 r2 ri) s =
         asmSem_assert (match ri with Reg r -> w2n (asmSem_read_reg
           r s) < dimindex (:'a) | _2 -> T)
           (asmSem_upd_reg r1 (asmSem_word_shift l
             (asmSem_read_reg r2 s) (w2n (asmSem_reg_imm ri s))) s)`;
   `asmSem_arith_upd (asm_Div r1 r2 r3) s =
         (let q = asmSem_read_reg r3 s in
           asmSem_assert (~(q = (n2w 0))) (asmSem_upd_reg r1
             (asmSem_read_reg r2 s / q) s))`;
   `asmSem_arith_upd (asm_LongMul r1 r2 r3 r4) (s:'a asm_state) =
         (let r = w2n (asmSem_read_reg r3 s) * w2n (asmSem_read_reg
           r4 s) in
           asmSem_upd_reg r2 (n2w r) (asmSem_upd_reg r1 (n2w (r
             DIV dimword (:'a))) s))`;
   `asmSem_arith_upd (asm_LongDiv r1 r2 r3 r4 r5) (s:'a asm_state) =
         (let n = w2n (asmSem_read_reg r3 s) * dimword (:'a) + w2n
           (asmSem_read_reg r4 s) in
         let d = w2n (asmSem_read_reg r5 s) in
         let q = n DIV d in
           asmSem_assert (~(d = 0) /\ q < dimword (:'a))
             (asmSem_upd_reg r1 (n2w q) (asmSem_upd_reg r2 (n2w
               (n MOD d)) s)))`;
   `asmSem_arith_upd (asm_AddCarry r1 r2 r3 r4) (s:'a asm_state) =
         (let r = w2n (asmSem_read_reg r2 s) + w2n (asmSem_read_reg
           r3 s) +
                 (if asmSem_read_reg r4 s = (n2w 0) then 0 else 1)
                   in
           asmSem_upd_reg r4 (if dimword (:'a) <= r then (n2w 1)
             else (n2w 0))
             (asmSem_upd_reg r1 (n2w r) s))`;
   `asmSem_arith_upd (asm_AddOverflow r1 r2 r3 r4) (s:'a asm_state) =
         (let w2 = asmSem_read_reg r2 s in
         let w3 = asmSem_read_reg r3 s in
           asmSem_upd_reg r4 (if ~(w2i (w2 + w3) = w2i w2 + w2i w3)
             then (n2w 1) else (n2w 0))
             (asmSem_upd_reg r1 (w2 + w3) s))`;
   `asmSem_arith_upd (asm_SubOverflow r1 r2 r3 r4) (s:'a asm_state) =
         (let w2 = asmSem_read_reg r2 s in
         let w3 = asmSem_read_reg r3 s in
           asmSem_upd_reg r4 (if ~(w2i (w2 - w3) = w2i w2 - w2i w3)
             then (n2w 1) else (n2w 0))
             (asmSem_upd_reg r1 (w2 - w3) s))`];;

let fp_upd_def = cake_define_list
  [`asmSem_fp_upd (FPLess r d1 d2) s =
         asmSem_upd_reg r (if fp64_lessThan (asmSem_read_fp_reg
           d1 s) (asmSem_read_fp_reg d2 s) then (n2w 1) else (n2w 0))
           s`;
   `asmSem_fp_upd (FPLessEqual r d1 d2) s =
         asmSem_upd_reg r (if fp64_lessEqual (asmSem_read_fp_reg
           d1 s) (asmSem_read_fp_reg d2 s) then (n2w 1) else (n2w 0))
           s`;
   `asmSem_fp_upd (FPEqual r d1 d2) s =
         asmSem_upd_reg r (if fp64_equal (asmSem_read_fp_reg d1
           s) (asmSem_read_fp_reg d2 s) then (n2w 1) else (n2w 0)) s`;
   `asmSem_fp_upd (FPMov d1 d2) s = asmSem_upd_fp_reg d1
  (asmSem_read_fp_reg d2 s) s`;
   `asmSem_fp_upd (FPAbs d1 d2) s = asmSem_upd_fp_reg d1 (fp64_abs
  (asmSem_read_fp_reg d2 s)) s`;
   `asmSem_fp_upd (FPNeg d1 d2) s = asmSem_upd_fp_reg d1 (fp64_negate
  (asmSem_read_fp_reg d2 s)) s`;
   `asmSem_fp_upd (FPSqrt d1 d2) s =
         asmSem_upd_fp_reg d1 (fp64_sqrt roundTiesToEven
           (asmSem_read_fp_reg d2 s)) s`;
   `asmSem_fp_upd (FPAdd d1 d2 d3) s =
         asmSem_upd_fp_reg d1
           (fp64_add roundTiesToEven (asmSem_read_fp_reg d2 s)
             (asmSem_read_fp_reg d3 s)) s`;
   `asmSem_fp_upd (FPSub d1 d2 d3) s =
         asmSem_upd_fp_reg d1
           (fp64_sub roundTiesToEven (asmSem_read_fp_reg d2 s)
             (asmSem_read_fp_reg d3 s)) s`;
   `asmSem_fp_upd (FPMul d1 d2 d3) s =
         asmSem_upd_fp_reg d1
           (fp64_mul roundTiesToEven (asmSem_read_fp_reg d2 s)
             (asmSem_read_fp_reg d3 s)) s`;
   `asmSem_fp_upd (FPDiv d1 d2 d3) s =
         asmSem_upd_fp_reg d1
           (fp64_div roundTiesToEven (asmSem_read_fp_reg d2 s)
             (asmSem_read_fp_reg d3 s)) s`;
   `asmSem_fp_upd (FPFma d1 d2 d3) s =
         asmSem_upd_fp_reg d1
           (fp64_mul_add roundTiesToEven (asmSem_read_fp_reg d2
             s) (asmSem_read_fp_reg d3 s) (asmSem_read_fp_reg d1 s))
             s`;
   `asmSem_fp_upd (FPMovToReg r1 r2 d) (s:'a asm_state) =
         (if dimindex (:'a) = 64 then
           asmSem_upd_reg r1 (w2w (asmSem_read_fp_reg d s)) s else
             let v = asmSem_read_fp_reg d s in
           asmSem_upd_reg r2 ((63 >< 32) v) (asmSem_upd_reg r1
             ((31 >< 0) v) s))`;
   `asmSem_fp_upd (FPMovFromReg d r1 r2) (s:'a asm_state) =
         asmSem_upd_fp_reg d
           (if dimindex (:'a) = 64 then
              w2w (asmSem_read_reg r1 s) else
              asmSem_read_reg r2 s @@ asmSem_read_reg r1 s) s`;
   `asmSem_fp_upd (FPToInt d1 d2) (s:'a asm_state) =
         (match fp64_to_int roundTiesToEven (asmSem_read_fp_reg d2
           s) with
             SOME i ->
               (let w = i2w i:word32 in
                 (if dimindex (:'a) = 64 then
                    asmSem_upd_fp_reg d1 (w2w w) else let (h,l) = if
                      ODD d1 then (63,32) else (31,0) in
                         asmSem_upd_fp_reg (d1 DIV 2)
                           (bit_field_insert h l w
                             (asmSem_read_fp_reg (d1 DIV 2) s)))
                    (asmSem_assert (w2i w = i) s)) | _4 ->
                      asmSem_assert F s)`;
   `asmSem_fp_upd (FPFromInt d1 d2) (s:'a asm_state) =
         (let i = if dimindex (:'a) = 64 then
                   w2i ((31 >< 0) (asmSem_read_fp_reg d2 s):word32)
                     else let v = asmSem_read_fp_reg (d2 DIV 2) s in
                   w2i (if ODD d2 then (63 >< 32) v else (31 >< 0)
                     v:'a word) in
           asmSem_upd_fp_reg d1 (int_to_fp64 roundTiesToEven i)
             s)`];;

let addr_def = cake_define
  `asmSem_addr (Addr r offset) s = asmSem_read_reg r s + offset`;;

let read_mem_word_def = cake_define_list
  [`read_mem_word a 0 s = (((n2w 0):'a word),s)`;
   `read_mem_word a (SUC n) s =
         (let (w,s1) = read_mem_word (if asm_state_be s then a -
           (n2w 1) else a + (n2w 1)) n s in
           (word_or (w << 8) (w2w (asmSem_read_mem a s1)),
              asmSem_assert (a IN asm_state_mem_domain s1) s1))`];;

let mem_load_def = cake_define
  `asmSem_mem_load n r a s =
     (let a = asmSem_addr a s in
     let (w,s) = read_mem_word (if asm_state_be s then a + n2w (n -
       1) else a) n s in
     let s = asmSem_upd_reg r w s in
       asmSem_assert (alignment_aligned (LOG2 n) a) s)`;;

let write_mem_word_def = cake_define_list
  [`write_mem_word a 0 w s = s`;
   `write_mem_word a (SUC n) w s =
         (let s1 = write_mem_word (if asm_state_be s then a - (n2w
           1) else a + (n2w 1)) n (w >>> 8) s in
           asmSem_assert (a IN asm_state_mem_domain s1)
             (asmSem_upd_mem a (w2w w) s1))`];;

let mem_store_def = cake_define
  `asmSem_mem_store n r a s =
     (let a = asmSem_addr a s in
     let w = asmSem_read_reg r s in
     let s = write_mem_word (if asm_state_be s then a + n2w (n - 1)
       else a) n w s in
       asmSem_assert (alignment_aligned (LOG2 n) a) s)`;;

let mem_op_def = cake_define_list
  [`asmSem_mem_op asm_Load r a = asmSem_mem_load (dimindex (:'a) DIV
  8) r a`;
   `asmSem_mem_op asm_Store r a = asmSem_mem_store (dimindex (:'a)
  DIV 8) r a`;
   `asmSem_mem_op asm_Load8 r a = asmSem_mem_load 1 r a`;
   `asmSem_mem_op asm_Store8 r a = asmSem_mem_store 1 r a`;
   `asmSem_mem_op asm_Load16 r a = asmSem_mem_load 2 r a`;
   `asmSem_mem_op asm_Store16 r a = asmSem_mem_store 2 r a`;
   `asmSem_mem_op asm_Load32 r (a:'a asm_addr) = asmSem_mem_load 4 r
  a`;
   `asmSem_mem_op asm_Store32 r (a:'a asm_addr) = asmSem_mem_store 4
  r a`];;

let inst_def = cake_define_list
  [`asmSem_inst asm_Skip s = s`;
   `asmSem_inst (asm_Const r imm) s = asmSem_upd_reg r imm s`;
   `asmSem_inst (asm_Arith x) s = asmSem_arith_upd x s`;
   `asmSem_inst (asm_Mem m r a) s = asmSem_mem_op m r a s`;
   `asmSem_inst (asm_FP fp) s = asmSem_fp_upd fp s`];;

let jump_to_offset_def = cake_define
  `jump_to_offset w s = asmSem_upd_pc (asm_state_pc s + w) s`;;

let asm_def = cake_define_list
  [`asmSem_asm (asm_Inst i) pc s = asmSem_upd_pc pc (asmSem_inst i s)`;
   `asmSem_asm (asm_Jump l) pc s = jump_to_offset l s`;
   `asmSem_asm (asm_JumpCmp cmp r ri l) pc s =
         (if asm_word_cmp cmp (asmSem_read_reg r s)
           (asmSem_reg_imm ri s) then jump_to_offset l s else
           asmSem_upd_pc pc s)`;
   `asmSem_asm (asm_Call l) pc s = jump_to_offset l (asmSem_upd_reg
  (asm_state_lr s) pc s)`;
   `asmSem_asm (asm_JumpReg r) pc s =
         (let a = asmSem_read_reg r s in asmSem_upd_pc a
           (asmSem_assert (alignment_aligned (asm_state_align s) a)
           s))`;
   `asmSem_asm (asm_Loc r l) pc s = asmSem_upd_pc pc (asmSem_upd_reg
  r (asm_state_pc s + l) s)`];;

let asm_step_def = cake_define
  `asm_step c s1 i s2 <=>
     bytes_in_memory (asm_state_pc s1) (asm_config_encode c i)
       (asm_state_mem s1) (asm_state_mem_domain s1) /\
     (match asm_config_link_reg c with SOME r -> asm_state_lr s1 = r
       | NONE -> T) /\
     (asm_state_be s1 = asm_config_big_endian c) /\
     (asm_state_align s1 = asm_config_code_alignment c) /\
     (asmSem_asm i (asm_state_pc s1 + n2w (LENGTH (asm_config_encode
       c i))) s1 = s2) /\
     ~asm_state_failed s2 /\ asm_ok i c`;;
