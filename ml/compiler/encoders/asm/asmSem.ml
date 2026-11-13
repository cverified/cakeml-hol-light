(* ======================================================== *)
(*  asmSem: ported from HOL4's
    compiler/encoders/asm/asmSemScript.sml
    A definition theory, with 24 definitions, 1 datatype and no
    theorems.  Needed by 6 files of the port.  *)
(* ======================================================== *)

(*
  The semantics of the asm instruction description.
*)

needs "compiler/encoders/asm/asm.ml";;
needs "lib/binary_ieee.ml";;
needs "lib/integer_word.ml";;
needs "lib/machine_ieee.ml";;
needs "misc/misc.ml";;
(* for bytes_in_memory *)
needs "semantics/ast.ml";;

(* the theories whose names the Ancestors blocks of the source
   bring, which are the ones that its statements read: the
   overloads of every other theory come out of the interface
   while this file loads *)
let _ = hol4_ancestors "asmSem"
  ["asm"; "misc"];;

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
hol4_field_overload "regs" "asm_state_regs";;
hol4_field_overload "regs_fupd" "asm_state_regs_fupd";;
hol4_field_overload "fp_regs" "asm_state_fp_regs";;
hol4_field_overload "fp_regs_fupd" "asm_state_fp_regs_fupd";;
hol4_field_overload "mem" "asm_state_mem";;
hol4_field_overload "mem_fupd" "asm_state_mem_fupd";;
hol4_field_overload "mem_domain" "asm_state_mem_domain";;
hol4_field_overload "mem_domain_fupd" "asm_state_mem_domain_fupd";;
hol4_field_overload "pc" "asm_state_pc";;
hol4_field_overload "pc_fupd" "asm_state_pc_fupd";;
hol4_field_overload "be" "asm_state_be";;
hol4_field_overload "be_fupd" "asm_state_be_fupd";;
hol4_field_overload "failed" "asm_state_failed";;
hol4_field_overload "failed_fupd" "asm_state_failed_fupd";;

let upd_pc_def = new_definition
  `asmSem_upd_pc pc' s = asm_state_pc_fupd (K pc') s`;;
hol4_overload "upd_pc" "asmSem_upd_pc";;
let upd_reg_def = new_definition
  `asmSem_upd_reg r v s = asm_state_regs_fupd (K ((r =+ v)
  (asm_state_regs s))) s`;;
hol4_overload "upd_reg" "asmSem_upd_reg";;
let upd_fp_reg_def = new_definition
  `asmSem_upd_fp_reg r v s = asm_state_fp_regs_fupd (K ((r =+ v)
  (asm_state_fp_regs s))) s`;;
hol4_overload "upd_fp_reg" "asmSem_upd_fp_reg";;
let upd_mem_def = new_definition
  `asmSem_upd_mem a b s = asm_state_mem_fupd (K ((a =+ b)
  (asm_state_mem s))) s`;;
hol4_overload "upd_mem" "asmSem_upd_mem";;
let read_reg_def = new_definition
  `asmSem_read_reg r s = asm_state_regs s r`;;
hol4_overload "read_reg" "asmSem_read_reg";;
let read_fp_reg_def = new_definition
  `asmSem_read_fp_reg r s = asm_state_fp_regs s r`;;
hol4_overload "read_fp_reg" "asmSem_read_fp_reg";;
let read_mem_def = new_definition
  `asmSem_read_mem a s = asm_state_mem s a`;;
hol4_overload "read_mem" "asmSem_read_mem";;

let assert_def = new_definition
  `asmSem_assert b s = asm_state_failed_fupd (K (~b \/
  asm_state_failed s)) s`;;
hol4_overload "assert" "asmSem_assert";;

let reg_imm_def = define_cases
  [`asmSem_reg_imm (Reg r) s = asmSem_read_reg r s`;
   `asmSem_reg_imm (Imm w) s = w`];;
hol4_overload "reg_imm" "asmSem_reg_imm";;

let binop_upd_def = define_general
  [`asmSem_binop_upd r (Add:binop) w1 w2 = asmSem_upd_reg r (w1 + w2)`;
   `asmSem_binop_upd r (Sub:binop) w1 w2 = asmSem_upd_reg r (w1 - w2)`;
   `asmSem_binop_upd r (And:binop) w1 w2 = asmSem_upd_reg r (word_and
  w1 w2)`;
   `asmSem_binop_upd r (Or:binop) w1 w2 = asmSem_upd_reg r (word_or
  w1 w2)`;
   `asmSem_binop_upd r (Xor:binop) w1 w2 = asmSem_upd_reg r
  (word_xor w1 w2)`];;
hol4_overload "binop_upd" "asmSem_binop_upd";;

let is_test_def = new_definition
  `is_test c <=> (c = Test) \/ (c = asm_NotTest)`;;

let asmSem_word_shift_def = define_cases
  [`asmSem_word_shift Lsl w n = w << n`;
   `asmSem_word_shift Lsr w n = w >>> n`;
   `asmSem_word_shift Asr w n = w >> n`;
   `asmSem_word_shift Ror w n = word_ror w n`];;
hol4_overload "word_shift" "asmSem_word_shift";;

let arith_upd_def = define_cases
  [`asmSem_arith_upd (asm_Binop b r1 r2 (ri:'a asm_reg_imm)) (s:'a
  asm_state) =
         asmSem_binop_upd r1 b (asmSem_read_reg r2 s)
           (asmSem_reg_imm ri s) s`;
   `asmSem_arith_upd (asm_Shift l r1 r2 ri) (s:'a asm_state) =
         asmSem_assert (match ri with Reg r -> w2n (asmSem_read_reg
           r s) < dimindex (:'a) | _6 -> T)
           (asmSem_upd_reg r1 (asmSem_word_shift l
             (asmSem_read_reg r2 s) (w2n (asmSem_reg_imm ri s))) s)`;
   `asmSem_arith_upd (asm_Div r1 r2 r3) (s:'a asm_state) =
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
hol4_overload "arith_upd" "asmSem_arith_upd";;

let fp_upd_def = define_cases
  [`asmSem_fp_upd (FPLess r d1 d2) (s:'a asm_state) =
         asmSem_upd_reg r (if fp64_lessThan (asmSem_read_fp_reg
           d1 s) (asmSem_read_fp_reg d2 s) then (n2w 1) else (n2w 0))
           s`;
   `asmSem_fp_upd (FPLessEqual r d1 d2) (s:'a asm_state) =
         asmSem_upd_reg r (if fp64_lessEqual (asmSem_read_fp_reg
           d1 s) (asmSem_read_fp_reg d2 s) then (n2w 1) else (n2w 0))
           s`;
   `asmSem_fp_upd (FPEqual r d1 d2) (s:'a asm_state) =
         asmSem_upd_reg r (if fp64_equal (asmSem_read_fp_reg d1
           s) (asmSem_read_fp_reg d2 s) then (n2w 1) else (n2w 0)) s`;
   `asmSem_fp_upd (FPMov d1 d2) (s:'a asm_state) = asmSem_upd_fp_reg
  d1 (asmSem_read_fp_reg d2 s) s`;
   `asmSem_fp_upd (FPAbs d1 d2) (s:'a asm_state) = asmSem_upd_fp_reg
  d1 (fp64_abs (asmSem_read_fp_reg d2 s)) s`;
   `asmSem_fp_upd (FPNeg d1 d2) (s:'a asm_state) = asmSem_upd_fp_reg
  d1 (fp64_negate (asmSem_read_fp_reg d2 s)) s`;
   `asmSem_fp_upd (FPSqrt d1 d2) (s:'a asm_state) =
         asmSem_upd_fp_reg d1 (fp64_sqrt roundTiesToEven
           (asmSem_read_fp_reg d2 s)) s`;
   `asmSem_fp_upd (FPAdd d1 d2 d3) (s:'a asm_state) =
         asmSem_upd_fp_reg d1
           (fp64_add roundTiesToEven (asmSem_read_fp_reg d2 s)
             (asmSem_read_fp_reg d3 s)) s`;
   `asmSem_fp_upd (FPSub d1 d2 d3) (s:'a asm_state) =
         asmSem_upd_fp_reg d1
           (fp64_sub roundTiesToEven (asmSem_read_fp_reg d2 s)
             (asmSem_read_fp_reg d3 s)) s`;
   `asmSem_fp_upd (FPMul d1 d2 d3) (s:'a asm_state) =
         asmSem_upd_fp_reg d1
           (fp64_mul roundTiesToEven (asmSem_read_fp_reg d2 s)
             (asmSem_read_fp_reg d3 s)) s`;
   `asmSem_fp_upd (FPDiv d1 d2 d3) (s:'a asm_state) =
         asmSem_upd_fp_reg d1
           (fp64_div roundTiesToEven (asmSem_read_fp_reg d2 s)
             (asmSem_read_fp_reg d3 s)) s`;
   `asmSem_fp_upd (FPFma d1 d2 d3) (s:'a asm_state) =
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
               (let w = (i2w i:word32) in
                 (if dimindex (:'a) = 64 then
                    asmSem_upd_fp_reg d1 (w2w w) else let (h,l) =
                      (if ODD d1 then (63,32) else (31,0)) in
                         asmSem_upd_fp_reg (d1 DIV 2)
                           (bit_field_insert h l w
                             (asmSem_read_fp_reg (d1 DIV 2) s)))
                    (asmSem_assert (w2i w = i) s)) | _8 ->
                      asmSem_assert F s)`;
   `asmSem_fp_upd (FPFromInt d1 d2) (s:'a asm_state) =
         (let i = (if dimindex (:'a) = 64 then
                   w2i ((31 >< 0) (asmSem_read_fp_reg d2 s):word32)
                     else let v = asmSem_read_fp_reg (d2 DIV 2) s in
                   w2i (if ODD d2 then (63 >< 32) v else (31 >< 0)
                     v:'a word)) in
           asmSem_upd_fp_reg d1 (int_to_fp64 roundTiesToEven i)
             s)`];;
hol4_overload "fp_upd" "asmSem_fp_upd";;

let addr_def = define_general
  [`asmSem_addr (Addr r offset) s = asmSem_read_reg r s + offset`];;
hol4_overload "addr" "asmSem_addr";;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let read_mem_word_def,read_mem_word_ind = define_wf
  `MEASURE (\(x0,x1,x2). (\n. n) x1)`
  [`read_mem_word a 0 s = (((n2w 0):'a word),s)`;
   `read_mem_word a (SUC n) s =
         (let (w,s1) = read_mem_word (if asm_state_be s then a -
           (n2w 1) else a + (n2w 1)) n s in
           (word_or (w << 8) (w2w (asmSem_read_mem a s1)),
              asmSem_assert (a IN asm_state_mem_domain s1) s1))`];;

let mem_load_def = new_definition
  `asmSem_mem_load n r a s =
     (let a = asmSem_addr a s in
     let (w,s) = read_mem_word (if asm_state_be s then a + n2w (n -
       1) else a) n s in
     let s = asmSem_upd_reg r w s in
       asmSem_assert (alignment_aligned (LOG2 n) a) s)`;;
hol4_overload "mem_load" "asmSem_mem_load";;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let write_mem_word_def,write_mem_word_ind = define_wf
  `MEASURE (\(x0,x1,x2,x3). (\n. n) x1)`
  [`write_mem_word a 0 w s = s`;
   `write_mem_word a (SUC n) w s =
         (let s1 = write_mem_word (if asm_state_be s then a - (n2w
           1) else a + (n2w 1)) n (w >>> 8) s in
           asmSem_assert (a IN asm_state_mem_domain s1)
             (asmSem_upd_mem a (w2w w) s1))`];;

let mem_store_def = new_definition
  `asmSem_mem_store n r a s =
     (let a = asmSem_addr a s in
     let w = asmSem_read_reg r s in
     let s = write_mem_word (if asm_state_be s then a + n2w (n - 1)
       else a) n w s in
       asmSem_assert (alignment_aligned (LOG2 n) a) s)`;;
hol4_overload "mem_store" "asmSem_mem_store";;

let mem_op_def = define_general
  [`asmSem_mem_op (asm_Load:memop) r (a:'a asm_addr) =
  asmSem_mem_load (dimindex (:'a) DIV 8) r a`;
   `asmSem_mem_op (asm_Store:memop) r (a:'a asm_addr) =
  asmSem_mem_store (dimindex (:'a) DIV 8) r a`;
   `asmSem_mem_op asm_Load8 r (a:'a asm_addr) = asmSem_mem_load 1 r a`;
   `asmSem_mem_op asm_Store8 r (a:'a asm_addr) = asmSem_mem_store 1 r
  a`;
   `asmSem_mem_op asm_Load16 r (a:'a asm_addr) = asmSem_mem_load 2 r
  a`;
   `asmSem_mem_op asm_Store16 r (a:'a asm_addr) = asmSem_mem_store 2
  r a`;
   `asmSem_mem_op (asm_Load32:memop) r (a:'a asm_addr) =
  asmSem_mem_load 4 r a`;
   `asmSem_mem_op (asm_Store32:memop) r (a:'a asm_addr) =
  asmSem_mem_store 4 r a`];;
hol4_overload "mem_op" "asmSem_mem_op";;

let inst_def = define_cases
  [`asmSem_inst asm_Skip s = s`;
   `asmSem_inst (asm_Const r imm) s = asmSem_upd_reg r imm s`;
   `asmSem_inst (asm_Arith x) s = asmSem_arith_upd x s`;
   `asmSem_inst (asm_Mem m r a) s = asmSem_mem_op m r a s`;
   `asmSem_inst (asm_FP fp) s = asmSem_fp_upd fp s`];;
hol4_overload "inst" "asmSem_inst";;

let jump_to_offset_def = new_definition
  `jump_to_offset w s = asmSem_upd_pc (asm_state_pc s + w) s`;;

let asm_def = define_cases
  [`asmSem_asm (asm_Inst i) pc' s = asmSem_upd_pc pc' (asmSem_inst i
  s)`;
   `asmSem_asm (asm_Jump l) pc' s = jump_to_offset l s`;
   `asmSem_asm (asm_JumpCmp cmp r ri l) pc' s =
         (if asm_word_cmp cmp (asmSem_read_reg r s)
           (asmSem_reg_imm ri s) then jump_to_offset l s else
           asmSem_upd_pc pc' s)`;
   `asmSem_asm (asm_Call l) pc' s = jump_to_offset l (asmSem_upd_reg
  (asm_state_lr s) pc' s)`;
   `asmSem_asm (asm_JumpReg r) pc' s =
         (let a = asmSem_read_reg r s in asmSem_upd_pc a
           (asmSem_assert (alignment_aligned (asm_state_align s) a)
           s))`;
   `asmSem_asm (asm_Loc r l) pc' s = asmSem_upd_pc pc'
  (asmSem_upd_reg r (asm_state_pc s + l) s)`];;
hol4_overload "asm" "asmSem_asm";;

let asm_step_def = new_definition
  `asm_step c s1 i s2 <=>
     bytes_in_memory (asm_state_pc s1) (asm_config_encode c i)
       (asm_state_mem s1) (asm_state_mem_domain s1) /\
     (match asm_config_link_reg c with SOME r -> asm_state_lr s1 = r
       | NONE -> T) /\
     (asm_state_be s1 = asm_config_big_endian c) /\
     (asm_state_align s1 = asm_config_code_alignment c) /\
     (asmSem_asm i (asm_state_pc s1 + n2w (LENGTH (asm_config_encode
       c i))) s1 = s2) /\
     ~(asm_state_failed s2) /\ asm_ok i c`;;

(* and the overloads that this file cannot see are back in the
   interface *)
let _ = unhide_overloads ();;
