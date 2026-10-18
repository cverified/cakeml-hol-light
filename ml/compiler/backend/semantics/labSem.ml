(* ======================================================== *)
(*  labSem: ported from HOL4's
    compiler/backend/semantics/labSemScript.sml
    A definition theory, with 37 definitions, 2 datatypes and 2
    theorems.  Needed by 6 files of the port.  *)
(* ======================================================== *)

(*
  The formal semantics of labLang
*)

needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/labLang.ml";;
needs "compiler/backend/semantics/targetSem.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/backend/stackLang.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "lib/alignment.ml";;
needs "lib/binary_ieee.ml";;
needs "lib/byte.ml";;
needs "lib/integer_word.ml";;
needs "lib/lprefix_lub.ml";;
needs "lib/pegexec.ml";;
needs "lib/sptree.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/fpSem.ml";;

let word8_loc_INDUCT,word8_loc_RECURSION = define_datatype
  "word8_loc = Byte (word8) | LocByte (num) (num) (num)";;

let labSem_state_FIELDS = define_record "labSem_state"
  ["regs","num->'a word_loc";
   "fp_regs","num->word64";
   "mem","'a word->'a word_loc";
   "mem_domain","'a word->bool";
   "shared_mem_domain","'a word->bool";
   "pc","num";
   "be","bool";
   "ffi","'ffi ffi_state";
   "io_regs","num->ffiname->num->('a word) option";
   "cc_regs","num->num->('a word) option";
   "io_fp_regs","num->num->word64";
   "cc_fp_regs","num->num->word64";
   "code","('a sec) list";
   "compile","'c->('a sec) list->(word8 list#'c) option";
   "compile_oracle","num->'c#('a sec) list";
   "code_buffer","('a,8)buffer";
   "clock","num";
   "failed","bool";
   "ptr_reg","num";
   "len_reg","num";
   "ptr2_reg","num";
   "len2_reg","num";
   "link_reg","num"];;
hol4_field_overload "regs" "labSem_state_regs";;
hol4_field_overload "regs_fupd" "labSem_state_regs_fupd";;
hol4_field_overload "fp_regs" "labSem_state_fp_regs";;
hol4_field_overload "fp_regs_fupd" "labSem_state_fp_regs_fupd";;
hol4_field_overload "mem" "labSem_state_mem";;
hol4_field_overload "mem_fupd" "labSem_state_mem_fupd";;
hol4_field_overload "mem_domain" "labSem_state_mem_domain";;
hol4_field_overload "mem_domain_fupd" "labSem_state_mem_domain_fupd";;
hol4_field_overload "pc" "labSem_state_pc";;
hol4_field_overload "pc_fupd" "labSem_state_pc_fupd";;
hol4_field_overload "be" "labSem_state_be";;
hol4_field_overload "be_fupd" "labSem_state_be_fupd";;
hol4_field_overload "state_ffi" "labSem_state_ffi";;
hol4_field_overload "state_ffi_fupd" "labSem_state_ffi_fupd";;
hol4_field_overload "state_code" "labSem_state_code";;
hol4_field_overload "state_code_fupd" "labSem_state_code_fupd";;
hol4_field_overload "compile" "labSem_state_compile";;
hol4_field_overload "compile_fupd" "labSem_state_compile_fupd";;
hol4_field_overload "compile_oracle" "labSem_state_compile_oracle";;
hol4_field_overload "compile_oracle_fupd"
  "labSem_state_compile_oracle_fupd";;
hol4_field_overload "state_code_buffer" "labSem_state_code_buffer";;
hol4_field_overload "state_code_buffer_fupd"
  "labSem_state_code_buffer_fupd";;
hol4_field_overload "state_clock" "labSem_state_clock";;
hol4_field_overload "state_clock_fupd" "labSem_state_clock_fupd";;
hol4_field_overload "failed" "labSem_state_failed";;
hol4_field_overload "failed_fupd" "labSem_state_failed_fupd";;
hol4_field_overload "ptr_reg" "labSem_state_ptr_reg";;
hol4_field_overload "ptr_reg_fupd" "labSem_state_ptr_reg_fupd";;
hol4_field_overload "len_reg" "labSem_state_len_reg";;
hol4_field_overload "len_reg_fupd" "labSem_state_len_reg_fupd";;
hol4_field_overload "ptr2_reg" "labSem_state_ptr2_reg";;
hol4_field_overload "ptr2_reg_fupd" "labSem_state_ptr2_reg_fupd";;
hol4_field_overload "len2_reg" "labSem_state_len2_reg";;
hol4_field_overload "len2_reg_fupd" "labSem_state_len2_reg_fupd";;
hol4_field_overload "link_reg" "labSem_state_link_reg";;
hol4_field_overload "link_reg_fupd" "labSem_state_link_reg_fupd";;

let is_Label_def = cake_define
  `is_Label x1 =
        match x1 with
          labLang_Label _4 _5 _6 -> T
        | _7 -> F`;;

let asm_fetch_aux_def = cake_define_list
  [`asm_fetch_aux pos [] = NONE`;
   `asm_fetch_aux pos (Section k [] :: xs) = asm_fetch_aux pos xs`;
   `asm_fetch_aux pos (Section k (y :: ys) :: xs) =
         (if is_Label y then asm_fetch_aux pos ((Section k ys)
           :: xs) else if pos = (0:num) then SOME y else
           asm_fetch_aux (pos - 1) ((Section k ys) :: xs))`];;

let asm_fetch_def = cake_define
  `asm_fetch s = asm_fetch_aux (pc s) (state_code s)`;;

let upd_pc_def = cake_define
  `labSem_upd_pc pc' s = pc_fupd (K pc') s`;;
hol4_overload "upd_pc" "labSem_upd_pc";;
let upd_reg_def = cake_define
  `labSem_upd_reg r w s = regs_fupd (K ((r =+ w) (regs s))) s`;;
hol4_overload "upd_reg" "labSem_upd_reg";;
let upd_mem_def = cake_define
  `labSem_upd_mem a w s = mem_fupd (K ((a =+ w) (mem s))) s`;;
hol4_overload "upd_mem" "labSem_upd_mem";;

(* HOL4 labSemScript.sml:77: the overload read_reg, which the port
   expands *)

let assert_def = cake_define
  `labSem_assert b s = failed_fupd (K (~b \/ failed s)) s`;;
hol4_overload "assert" "labSem_assert";;

let reg_imm_def = cake_define_list
  [`labSem_reg_imm (Reg r) s = (\r s. regs s r) r s`;
   `labSem_reg_imm (Imm w) s = wordLang_Word w`];;
hol4_overload "reg_imm" "labSem_reg_imm";;

let binop_upd_def = cake_define_list
  [`labSem_binop_upd r (Add:binop) w1 w2 = upd_reg r (wordLang_Word
  (w1 + w2))`;
   `labSem_binop_upd r (Sub:binop) w1 w2 = upd_reg r (wordLang_Word
  (w1 - w2))`;
   `labSem_binop_upd r (And:binop) w1 w2 = upd_reg r (wordLang_Word
  (word_and w1 w2))`;
   `labSem_binop_upd r (Or:binop) w1 w2 = upd_reg r (wordLang_Word
  (word_or w1 w2))`;
   `labSem_binop_upd r (Xor:binop) w1 w2 = upd_reg r (wordLang_Word
  (word_xor w1 w2))`];;
hol4_overload "binop_upd" "labSem_binop_upd";;

let arith_upd_def = cake_define_list
  [`labSem_arith_upd (asm_Binop b r1 r2 (ri:'a asm_reg_imm)) s =
         (match ((\r s. regs s r) r2 s,reg_imm ri s) with
           (wordLang_Word w1,wordLang_Word w2) -> binop_upd r1 b w1
           w2 s | (x,_16) -> (if b = Or /\ ri = Reg r2 then upd_reg
           r1 x s else assert F s))`;
   `labSem_arith_upd (asm_Shift l r1 r2 ri) s =
         (match ((\r s. regs s r) r2 s,reg_imm ri s) with
           (wordLang_Word w1,wordLang_Word w2) ->
             assert (w2n w2 < dimindex (:'a)) (upd_reg r1
               (wordLang_Word (word_shift l w1 (w2n w2))) s) | _19 ->
               assert F s)`;
   `labSem_arith_upd (asm_Div r1 r2 r3) s =
         (match ((\r s. regs s r) r3 s,(\r s. regs s r) r2 s) with
           (wordLang_Word q,wordLang_Word w2) ->
           assert (~(q = (n2w 0))) (upd_reg r1 (wordLang_Word (w2
             / q)) s) | _22 -> assert F s)`;
   `labSem_arith_upd (asm_AddCarry r1 r2 r3 r4) s =
         (match ((\r s. regs s r) r2 s,(\r s. regs s r) r3 s,(\r s.
           regs s r) r4 s) with (wordLang_Word w2,wordLang_Word
           w3,wordLang_Word w4) ->
           (let r = w2n w2 + w2n w3 + (if w4 = (n2w 0) then 0 else
             1) in
             upd_reg r4 (wordLang_Word (if dimword (:'a) <= r then
               (n2w 1) else (n2w 0)))
                (upd_reg r1 (wordLang_Word (n2w r)) s)) | _25 ->
                  assert F s)`;
   `labSem_arith_upd (asm_LongMul r1 r2 r3 r4) s =
         (match ((\r s. regs s r) r3 s,(\r s. regs s r) r4 s) with
           (wordLang_Word w3,wordLang_Word w4) ->
           (let r = w2n w3 * w2n w4 in
          upd_reg r2 (wordLang_Word (n2w r))
           (upd_reg r1 (wordLang_Word (n2w (r DIV dimword
             (:'a)))) s)) | _26 -> assert F s)`;
   `labSem_arith_upd (asm_LongDiv r1 r2 r3 r4 r5) s =
         (match ((\r s. regs s r) r3 s,(\r s. regs s r) r4 s,(\r s.
           regs s r) r5 s) with (wordLang_Word w3,wordLang_Word
           w4,wordLang_Word w5) ->
           (let n = w2n w3 * dimword (:'a) + w2n w4 in
           let d = w2n w5 in
           let q = n DIV d in
           assert (~(d = 0) /\ q < dimword (:'a))
             (upd_reg r1 (wordLang_Word (n2w q)) (upd_reg r2
               (wordLang_Word (n2w (n MOD d))) s))) | _27 -> assert F
               s)`;
   `labSem_arith_upd (asm_AddOverflow r1 r2 r3 r4) s =
         (match ((\r s. regs s r) r2 s,(\r s. regs s r) r3 s) with
           (wordLang_Word w2,wordLang_Word w3) ->
             upd_reg r4 (wordLang_Word (if ~(w2i (w2 + w3) = w2i w2
               + w2i w3) then (n2w 1) else (n2w 0)))
                (upd_reg r1 (wordLang_Word (w2 + w3)) s) | _28 ->
                  assert F s)`;
   `labSem_arith_upd (asm_SubOverflow r1 r2 r3 r4) s =
         (match ((\r s. regs s r) r2 s,(\r s. regs s r) r3 s) with
           (wordLang_Word w2,wordLang_Word w3) ->
             upd_reg r4 (wordLang_Word (if ~(w2i (w2 - w3) = w2i w2
               - w2i w3) then (n2w 1) else (n2w 0)))
                (upd_reg r1 (wordLang_Word (w2 - w3)) s) | _29
                  -> assert F s)`];;
hol4_overload "arith_upd" "labSem_arith_upd";;

let upd_fp_reg_def = cake_define
  `labSem_upd_fp_reg r v s = fp_regs_fupd (K ((r =+ v) (fp_regs s)))
  s`;;
hol4_overload "upd_fp_reg" "labSem_upd_fp_reg";;
let read_fp_reg_def = cake_define
  `labSem_read_fp_reg r s = fp_regs s r`;;
hol4_overload "read_fp_reg" "labSem_read_fp_reg";;

let fp_upd_def = cake_define_list
  [`labSem_fp_upd (FPLess r d1 d2) (s:('a,'c,'ffi)labSem_state) =
         upd_reg r (wordLang_Word (if fp64_lessThan (read_fp_reg
           d1 s) (read_fp_reg d2 s) then (n2w 1) else (n2w 0))) s`;
   `labSem_fp_upd (FPLessEqual r d1 d2) (s:('a,'c,'ffi)labSem_state) =
         upd_reg r (wordLang_Word (if fp64_lessEqual (read_fp_reg
           d1 s) (read_fp_reg d2 s) then (n2w 1) else (n2w 0))) s`;
   `labSem_fp_upd (FPEqual r d1 d2) (s:('a,'c,'ffi)labSem_state) =
         upd_reg r (wordLang_Word (if fp64_equal (read_fp_reg d1
           s) (read_fp_reg d2 s) then (n2w 1) else (n2w 0))) s`;
   `labSem_fp_upd (FPMov d1 d2) (s:('a,'c,'ffi)labSem_state) =
  upd_fp_reg d1 (read_fp_reg d2 s) s`;
   `labSem_fp_upd (FPAbs d1 d2) (s:('a,'c,'ffi)labSem_state) =
  upd_fp_reg d1 (fp64_abs (read_fp_reg d2 s)) s`;
   `labSem_fp_upd (FPNeg d1 d2) (s:('a,'c,'ffi)labSem_state) =
  upd_fp_reg d1 (fp64_negate (read_fp_reg d2 s)) s`;
   `labSem_fp_upd (FPSqrt d1 d2) (s:('a,'c,'ffi)labSem_state) =
         upd_fp_reg d1 (fp64_sqrt roundTiesToEven (read_fp_reg d2
           s)) s`;
   `labSem_fp_upd (FPAdd d1 d2 d3) (s:('a,'c,'ffi)labSem_state) =
         upd_fp_reg d1
           (fp64_add roundTiesToEven (read_fp_reg d2 s)
             (read_fp_reg d3 s)) s`;
   `labSem_fp_upd (FPSub d1 d2 d3) (s:('a,'c,'ffi)labSem_state) =
         upd_fp_reg d1
           (fp64_sub roundTiesToEven (read_fp_reg d2 s)
             (read_fp_reg d3 s)) s`;
   `labSem_fp_upd (FPMul d1 d2 d3) (s:('a,'c,'ffi)labSem_state) =
         upd_fp_reg d1
           (fp64_mul roundTiesToEven (read_fp_reg d2 s)
             (read_fp_reg d3 s)) s`;
   `labSem_fp_upd (FPDiv d1 d2 d3) (s:('a,'c,'ffi)labSem_state) =
         upd_fp_reg d1
           (fp64_div roundTiesToEven (read_fp_reg d2 s)
             (read_fp_reg d3 s)) s`;
   `labSem_fp_upd (FPFma d1 d2 d3) (s:('a,'c,'ffi)labSem_state) =
         upd_fp_reg d1
           (fpfma (read_fp_reg d1 s) (read_fp_reg d2 s)
             (read_fp_reg d3 s)) s`;
   `labSem_fp_upd (FPMovToReg r1 r2 d) (s:('a,'c,'ffi)labSem_state) =
         (if dimindex (:'a) = 64 then
           upd_reg r1 (wordLang_Word (w2w (read_fp_reg d s))) s else
             let v = read_fp_reg d s in
           upd_reg r2 (wordLang_Word ((63 >< 32) v)) (upd_reg r1
             (wordLang_Word ((31 >< 0) v)) s))`;
   `labSem_fp_upd (FPMovFromReg d r1 r2) (s:('a,'c,'ffi)labSem_state) =
         (if dimindex (:'a) = 64 then
           match (\r s. regs s r) r1 s with
             wordLang_Word w1 -> upd_fp_reg d (w2w w1) s | _33 ->
               assert F s else
           match ((\r s. regs s r) r1 s,(\r s. regs s r) r2 s) with
             (wordLang_Word w1,wordLang_Word w2) -> upd_fp_reg d
               (w2 @@ w1) s | _34 -> assert F s)`;
   `labSem_fp_upd (FPToInt d1 d2) (s:('a,'c,'ffi)labSem_state) =
         (match fp64_to_int roundTiesToEven (read_fp_reg d2 s) with
             SOME i ->
               (let w = (i2w i:word32) in
                 (if dimindex (:'a) = 64 then
                    upd_fp_reg d1 (w2w w) else let (h,l) = (if ODD
                      d1 then (63,32) else (31,0)) in
                         upd_fp_reg (d1 DIV 2)
                           (bit_field_insert h l w (read_fp_reg (d1
                             DIV 2) s)))
                    (assert (w2i w = i) s)) | _35 -> assert F s)`;
   `labSem_fp_upd (FPFromInt d1 d2) (s:('a,'c,'ffi)labSem_state) =
         (let i = (if dimindex (:'a) = 64 then
                   w2i ((31 >< 0) (read_fp_reg d2 s):word32) else
                     let v = read_fp_reg (d2 DIV 2) s in
                   w2i (if ODD d2 then (63 >< 32) v else (31 >< 0)
                     v:'a word)) in
           upd_fp_reg d1 (int_to_fp64 roundTiesToEven i) s)`];;
hol4_overload "fp_upd" "labSem_fp_upd";;

let addr_def = cake_define
  `labSem_addr (Addr r offset) s =
     (match (\r s. regs s r) r s with wordLang_Word w -> SOME (w +
       offset) | _36 -> NONE)`;;
hol4_overload "addr" "labSem_addr";;

let is_Loc_def = cake_define
  `is_Loc x1 =
        match x1 with
          wordLang_Loc _39 _40 -> T
        | _41 -> F`;;

let mem_store_def = cake_define
  `labSem_mem_store r a (s:('a,'c,'ffi)labSem_state) =
     (match addr a s with NONE -> assert F s | SOME w -> assert ((w2n
       w MOD (dimindex (:'a) DIV 8) = 0) /\
                         w IN labSem_state_mem_domain s)
                   (upd_mem w ((\r s. regs s r) r s) s))`;;
hol4_overload "mem_store" "labSem_mem_store";;

let mem_load_def = cake_define
  `labSem_mem_load r a (s:('a,'c,'ffi)labSem_state) =
     (match addr a s with NONE -> assert F s | SOME w -> assert ((w2n
       w MOD (dimindex (:'a) DIV 8) = 0) /\
                         w IN labSem_state_mem_domain s)
                   (upd_reg r (labSem_state_mem s w) s))`;;
hol4_overload "mem_load" "labSem_mem_load";;

let mem_load32_def = cake_define
  `mem_load32 r a (s:('a,'c,'ffi)labSem_state) =
     (match addr a s with NONE -> assert F s | SOME w ->
         (match mem_load_32 (labSem_state_mem s)
           (labSem_state_mem_domain s) (labSem_state_be s) w with
           SOME v -> upd_reg r (wordLang_Word (w2w v)) s | NONE ->
           assert F s))`;;

let mem_store32_def = cake_define
  `mem_store32 r a (s:('a,'c,'ffi)labSem_state) =
     (match addr a s with NONE -> assert F s | SOME w ->
         (match (\r s. regs s r) r s with wordLang_Word b ->
            (match mem_store_32 (labSem_state_mem s)
              (labSem_state_mem_domain s) (labSem_state_be s) w (w2w
              b) with SOME m -> (labSem_state_mem_fupd (K m) s) |
              NONE -> assert F s) | _42 -> assert F s))`;;

let mem_load_byte_def = cake_define
  `mem_load_byte r a (s:('a,'c,'ffi)labSem_state) =
     (match addr a s with NONE -> assert F s | SOME w ->
         (match mem_load_byte_aux (labSem_state_mem s)
           (labSem_state_mem_domain s) (labSem_state_be s) w with
           SOME v -> upd_reg r (wordLang_Word (w2w v)) s | NONE ->
           assert F s))`;;

let mem_store_byte_def = cake_define
  `mem_store_byte r a (s:('a,'c,'ffi)labSem_state) =
     (match addr a s with NONE -> assert F s | SOME w ->
         (match (\r s. regs s r) r s with wordLang_Word b ->
            (match mem_store_byte_aux (labSem_state_mem s)
              (labSem_state_mem_domain s) (labSem_state_be s) w (w2w
              b) with SOME m -> (labSem_state_mem_fupd (K m) s) |
              NONE -> assert F s) | _43 -> assert F s))`;;

let mem_op_def = cake_define_list
  [`labSem_mem_op (Load:memop) r (a:'a asm_addr) = mem_load r a`;
   `labSem_mem_op (Store:memop) r (a:'a asm_addr) = mem_store r a`;
   `labSem_mem_op (asm_Load32:memop) r (a:'a asm_addr) = mem_load32 r
  a`;
   `labSem_mem_op (asm_Store32:memop) r (a:'a asm_addr) = mem_store32
  r a`;
   `labSem_mem_op asm_Load8 r (a:'a asm_addr) = mem_load_byte r a`;
   `labSem_mem_op asm_Store8 r (a:'a asm_addr) = mem_store_byte r a`;
   `labSem_mem_op asm_Load16 r (a:'a asm_addr) = assert F`;
   `labSem_mem_op asm_Store16 r (a:'a asm_addr) = assert F`];;
hol4_overload "mem_op" "labSem_mem_op";;

let asm_inst_def = cake_define_list
  [`asm_inst asm_Skip (s:('a,'c,'ffi)labSem_state) =
  (s:('a,'c,'ffi)labSem_state)`;
   `asm_inst (asm_Const r imm) (s:('a,'c,'ffi)labSem_state) =
  ((upd_reg r (wordLang_Word imm) s):('a,'c,'ffi)labSem_state)`;
   `asm_inst (asm_Arith x) (s:('a,'c,'ffi)labSem_state) = ((arith_upd
  x s):('a,'c,'ffi)labSem_state)`;
   `asm_inst (asm_Mem m r a) (s:('a,'c,'ffi)labSem_state) = ((mem_op
  m r a s):('a,'c,'ffi)labSem_state)`;
   `asm_inst (asm_FP fp) (s:('a,'c,'ffi)labSem_state) = ((fp_upd fp
  s):('a,'c,'ffi)labSem_state)`];;

let dec_clock_def = cake_define
  `labSem_dec_clock s = state_clock_fupd (K (state_clock s - 1)) s`;;
hol4_overload "dec_clock" "labSem_dec_clock";;

let inc_pc_def = cake_define
  `inc_pc s = pc_fupd (K (pc s + 1)) s`;;

(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let asm_code_length_def = cake_define_list_cheat CHEAT_TAC
  [`asm_code_length [] = 0`;
   `asm_code_length (Section k [] :: xs) = asm_code_length xs`;
   `asm_code_length (Section k (y :: ys) :: xs) =
         asm_code_length ((Section k ys) :: xs) + (if is_Label
           y then 0 else 1:num)`];;

let asm_fetch_IMP = cake_theorem "asm_fetch_IMP[local]"
  (fun () ->
    `(asm_fetch s = SOME x) ==> pc
       s < asm_code_length (state_code s)`)
  CHEAT_TAC;;

let lab_to_loc_def = cake_define
  `lab_to_loc (labLang_Lab n1 n2:lab) = Loc n1 n2`;;

(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let loc_to_pc_def = cake_define_list_cheat CHEAT_TAC
  [`loc_to_pc n1 n2 [] = NONE`;
   `loc_to_pc n1 n2 (Section k xs :: ys) =
         (if (k = n1) /\ (n2 = 0) then SOME (0:num) else
           match xs with [] -> loc_to_pc n1 n2 ys | (z :: zs) ->
             (if (?k. z = labLang_Label n1 n2 k) /\ ~(n2 = 0) then
               SOME 0 else
               if is_Label z then loc_to_pc n1 n2 ((Section k zs) ::
                 ys) else
                 match loc_to_pc n1 n2 ((Section k zs) :: ys)
                   with NONE -> NONE | SOME pos -> SOME (pos +
                   (1:num))))`];;

let asm_inst_consts = cake_theorem "asm_inst_consts"
  (fun () ->
    `(pc (asm_inst i s) = pc s) /\
     (state_code (asm_inst i s) = state_code s) /\
     (state_clock (asm_inst i s) = state_clock s) /\
     (state_ffi (asm_inst i s) = state_ffi s) /\
     (labSem_state_io_regs (asm_inst i s) = labSem_state_io_regs s)
       /\
     (labSem_state_io_fp_regs (asm_inst i s) =
       labSem_state_io_fp_regs s) /\
     (labSem_state_cc_regs (asm_inst i s) = labSem_state_cc_regs s)
       /\
     (labSem_state_cc_fp_regs (asm_inst i s) =
       labSem_state_cc_fp_regs s) /\
     (ptr_reg (asm_inst i s) = ptr_reg s) /\
     (len_reg (asm_inst i s) = len_reg s) /\
     (ptr2_reg (asm_inst i s) = ptr2_reg s) /\
     (len2_reg (asm_inst i s) = len2_reg s) /\
     (link_reg (asm_inst i s) = link_reg s)`)
  CHEAT_TAC;;

let get_pc_value_def = cake_define
  `get_pc_value lab (s:('a,'c,'ffi)labSem_state) =
     (match lab with labLang_Lab n1 n2 -> loc_to_pc n1 n2
       (labSem_state_code s))`;;

let next_label_def = cake_define
  `next_label x1 =
        match x1 with
          [] -> NONE
        | (Section k [] :: xs) -> next_label xs
        | ((Section k (labLang_Label n1 n2 _44 :: ys)) :: xs) -> SOME
          (Loc n1 n2)
        | ((Section k (y :: ys)) :: xs) -> next_label (Section k
          ys :: xs)`;;

let get_lab_after_def = cake_define_list
  [`get_lab_after pos [] = NONE`;
   `get_lab_after pos (Section k [] :: xs) = get_lab_after pos xs`;
   `get_lab_after pos (Section k (y :: ys) :: xs) =
         (if is_Label y then get_lab_after pos ((Section k ys)
           :: xs) else if pos = (0:num) then next_label ((Section k
           ys) :: xs) else get_lab_after (pos - 1) ((Section k ys)
           :: xs))`];;

let get_ret_Loc_def = cake_define
  `get_ret_Loc s = get_lab_after (pc s) (state_code s)`;;

let share_mem_load_def = cake_define
  `share_mem_load r ad (s:('a,'c,'ffi)labSem_state) n =
     (match addr ad s with NONE -> NONE | SOME v ->
         (if (if n = 0 then (
                  w2n v MOD (dimindex (:'a) DIV 8) = 0 /\ (v IN
                    labSem_state_shared_mem_domain s)) else byte_align v
                    IN labSem_state_shared_mem_domain s) then
           (match call_FFI (labSem_state_ffi s) (ffi_SharedMem
             MappedRead)
             [n2w n]
             (word_to_bytes v F) with FFI_final outcome -> SOME
               (FFI_final outcome,s) | FFI_return new_ffi new_bytes ->
               SOME (FFI_return new_ffi
                 new_bytes,labSem_state_clock_fupd (K
                 (labSem_state_clock s - 1)) (labSem_state_pc_fupd (K
                 (labSem_state_pc s + 1)) (labSem_state_regs_fupd (K ((r
                 =+ wordLang_Word (word_of_bytes F (n2w 0) new_bytes))
                 (labSem_state_regs s))) (labSem_state_ffi_fupd (K
                 new_ffi)
                 s))))) else NONE))`;;

let share_mem_store_def = cake_define
  `share_mem_store r ad (s:('a,'c,'ffi)labSem_state) n =
     (match labSem_state_regs s r with wordLang_Word w ->
       (match addr ad s with NONE -> NONE | SOME v ->
         (if (if n = 0 then (
                  w2n v MOD (dimindex (:'a) DIV 8) = 0 /\ (v IN
                    labSem_state_shared_mem_domain s)) else byte_align v
                    IN labSem_state_shared_mem_domain s) then
              (match call_FFI (labSem_state_ffi s) (ffi_SharedMem
                MappedWrite)
                [n2w n]
                ((if n = 0 then word_to_bytes w F else TAKE n
                  (word_to_bytes w F)) ++ (word_to_bytes v F)) with
                  FFI_final outcome -> SOME (FFI_final outcome,s) |
                  FFI_return new_ffi new_bytes ->
                  SOME ((FFI_return new_ffi new_bytes),
                    inc_pc (dec_clock (labSem_state_ffi_fupd (K
                      new_ffi) s)))) else NONE)) | _45 -> NONE)`;;

let share_mem_op_def = cake_define_list
  [`share_mem_op (Load:memop) r ad (s:('a,'c,'ffi)labSem_state) =
        share_mem_load r ad s 0`;
   `share_mem_op asm_Load8 r ad (s:('a,'c,'ffi)labSem_state) =
  share_mem_load r ad s 1`;
   `share_mem_op asm_Load16 r ad (s:('a,'c,'ffi)labSem_state) =
  share_mem_load r ad s 2`;
   `share_mem_op (Store:memop) r ad (s:('a,'c,'ffi)labSem_state) =
  share_mem_store r ad s 0`;
   `share_mem_op asm_Store8 r ad (s:('a,'c,'ffi)labSem_state) =
  share_mem_store r ad s 1`;
   `share_mem_op asm_Store16 r ad (s:('a,'c,'ffi)labSem_state) =
  share_mem_store r ad s 2`;
   `share_mem_op (asm_Load32:memop) r ad (s:('a,'c,'ffi)labSem_state)
  = share_mem_load r ad s 4`;
   `share_mem_op (asm_Store32:memop) r ad
  (s:('a,'c,'ffi)labSem_state) = share_mem_store r ad s 4`];;

(* HOL4 labSemScript.sml:610-617: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let evaluate_def = cake_define_try_tac (fun () ->
  `MEASURE (\s. state_clock s)`)
  CHEAT_TAC
  `labSem_evaluate (s:('a,'c,'ffi)labSem_state) =
     (if labSem_state_clock s = 0 then (TimeOut,s) else
     match asm_fetch s with SOME (labLang_Asm (Asmi a) _46 _47) ->
         (match a with Inst i ->
             (let s1 = asm_inst i s in
                if failed s1 then (Error,s) else labSem_evaluate
                  (inc_pc (dec_clock s1))) | asm_JumpReg r ->
             (match (\r s. regs s r) r s with Loc n1 n2 ->
                  (match loc_to_pc n1 n2 (labSem_state_code s) with
                    NONE -> (Error,s) | SOME p ->
                       labSem_evaluate (upd_pc p (dec_clock s))) |
                         _48 -> (Error,s)) | _49 -> (Error,s)) | SOME
                         (labLang_Asm (Cbw r1 r2) _50 _51) ->
       (match ((\r s. regs s r) r1 s,(\r s. regs s r) r2 s) with
         (wordLang_Word w1,wordLang_Word w2) ->
         (match buffer_write (labSem_state_code_buffer s) w1 (w2w w2)
           with SOME new_cb ->
           labSem_evaluate (inc_pc (dec_clock
             (labSem_state_code_buffer_fupd (K new_cb) s))) | _52 ->
             (Error,s)) | _53 -> (Error,s)) | SOME (labLang_Asm
             (ShareMem m r ad) _54 _55) ->
        (match share_mem_op m r ad s with SOME (FFI_final outcome,s')
          -> (Halt (ffi_FFI_outcome outcome),s') | SOME (FFI_return _56
          _57,s') ->
             labSem_evaluate (labSem_state_io_fp_regs_fupd (K
               (misc_shift_seq 1 (labSem_state_io_fp_regs s')))
               (labSem_state_io_regs_fupd (K (misc_shift_seq 1
               (labSem_state_io_regs s'))) s')) | NONE -> (Error,s)) |
               SOME (labLang_LabAsm labLang_Halt _58 _59 _60) ->
        (match labSem_state_regs s (labSem_state_ptr_reg s) with
          wordLang_Word (n2w 0) -> (Halt ffi_Success,s) | wordLang_Word
          _61 -> (Halt ffi_Resource_limit_hit,s) | _62 -> (Error,s)) |
          SOME (labLang_LabAsm (LocValue r lab) _63 _64 _65) ->
        (if get_pc_value lab s = NONE then (Error,s) else
           let s1 = upd_reg r (lab_to_loc lab) s in
             labSem_evaluate (inc_pc (dec_clock s1))) | SOME
               (labLang_LabAsm (Jump l) _66 _67 _68) ->
        (match get_pc_value l s with NONE -> (Error,s) | SOME p ->
          labSem_evaluate (upd_pc p (dec_clock s))) | SOME
          (labLang_LabAsm (JumpCmp c r ri l) _69 _70 _71) ->
        (match word_cmp c ((\r s. regs s r) r s) (reg_imm ri s) with
          NONE -> (Error,s) | SOME F -> labSem_evaluate (inc_pc
          (dec_clock s)) | SOME T ->
          (match get_pc_value l s with NONE -> (Error,s) | SOME p ->
            labSem_evaluate (upd_pc p (dec_clock s)))) | SOME
            (labLang_LabAsm (Call l) _72 _73 _74) ->
        (match get_pc_value l s with NONE -> (Error,s) | SOME p ->
          (match get_ret_Loc s with NONE -> (Error,s) | SOME k ->
              (let s1 = upd_reg (labSem_state_link_reg s) k s in
                labSem_evaluate (upd_pc p (dec_clock s1))))) | SOME
                  (labLang_LabAsm Install _75 _76 _77) ->
        (match (labSem_state_regs s (labSem_state_ptr_reg
          s),labSem_state_regs s (labSem_state_len_reg
          s),labSem_state_regs s (labSem_state_link_reg s)) with
          (wordLang_Word w1,wordLang_Word w2,Loc n1 n2) ->
            (match (buffer_flush (labSem_state_code_buffer s) w1
              w2,loc_to_pc n1 n2 (labSem_state_code s)) with (SOME
              (bytes,cb),SOME new_pc) ->
               (let (cfg,prog) = labSem_state_compile_oracle s 0 in
               let new_oracle = misc_shift_seq 1
                 (labSem_state_compile_oracle s) in
                 (match (labSem_state_compile s cfg prog,prog) with
                   (SOME (bytes',cfg'),Section k _78 :: _79) ->
                    (if bytes = bytes' /\ FST (new_oracle 0) = cfg'
                      then
                      labSem_evaluate
                        (labSem_state_clock_fupd (K
                          (labSem_state_clock s - 1))
                          (labSem_state_compile_oracle_fupd (K
                          new_oracle) (labSem_state_fp_regs_fupd (K (\n.
                          labSem_state_cc_fp_regs s 0 n))
                          (labSem_state_regs_fupd (K
                          ((labSem_state_ptr_reg s =+ Loc k 0)
                              (\a. get_reg_value
                                (labSem_state_cc_regs s 0 a)
                              (labSem_state_regs s a)
                                wordLang_Word)))
                                (labSem_state_cc_fp_regs_fupd (K
                                (misc_shift_seq 1
                                (labSem_state_cc_fp_regs s)))
                                (labSem_state_cc_regs_fupd (K
                                (misc_shift_seq 1 (labSem_state_cc_regs
                                s))) (labSem_state_code_fupd (K
                                (labSem_state_code s ++ prog))
                                (labSem_state_code_buffer_fupd (K cb)
                                (labSem_state_pc_fupd (K new_pc)
                                s))))))))) else
                      (Error,s)) | _80 -> (Error,s))) | _81 ->
                        (Error,s)) | _82 -> (Error,s)) | SOME
                        (labLang_LabAsm (labLang_CallFFI ffi_index) _83
                        _84 _85) ->
        (match (labSem_state_regs s (labSem_state_len_reg
          s),labSem_state_regs s (labSem_state_ptr_reg
          s),labSem_state_regs
               s (labSem_state_len2_reg s),labSem_state_regs s
                 (labSem_state_ptr2_reg s),labSem_state_regs s
                 (labSem_state_link_reg s)) with (wordLang_Word
                 w,wordLang_Word w2,wordLang_Word w3,wordLang_Word
                 w4,Loc n1 n2) ->
          (match (read_bytearray w2 (w2n w) (mem_load_byte_aux
            (labSem_state_mem s) (labSem_state_mem_domain s)
            (labSem_state_be s)),
                 read_bytearray w4 (w2n w3) (mem_load_byte_aux
                   (labSem_state_mem s) (labSem_state_mem_domain s)
                   (labSem_state_be s)),
                 loc_to_pc n1 n2 (labSem_state_code s)) with (SOME
                   bytes,SOME bytes2,SOME new_pc) ->
              (match call_FFI (labSem_state_ffi s) (ffi_ExtCall
                ffi_index) bytes bytes2 with FFI_final outcome -> (Halt
                (ffi_FFI_outcome outcome),s) | FFI_return new_ffi
                new_bytes ->
                   (let new_io_regs = misc_shift_seq 1
                     (labSem_state_io_regs s) in
                   let new_io_fp_regs = misc_shift_seq 1
                     (labSem_state_io_fp_regs s) in
                   let new_m = write_bytearray w4 new_bytes
                     (labSem_state_mem s) (labSem_state_mem_domain s)
                     (labSem_state_be s) in
                     labSem_evaluate (labSem_state_clock_fupd (K
                       (labSem_state_clock s - 1)) (labSem_state_pc_fupd
                       (K new_pc) (labSem_state_fp_regs_fupd (K (\n.
                       labSem_state_io_fp_regs s 0 n))
                       (labSem_state_regs_fupd (K (\a. get_reg_value
                       (labSem_state_io_regs s 0 (ffi_ExtCall ffi_index)
                       a)
                              (labSem_state_regs s a)
                                wordLang_Word))
                                (labSem_state_io_fp_regs_fupd (K
                                new_io_fp_regs)
                                (labSem_state_io_regs_fupd (K
                                new_io_regs) (labSem_state_ffi_fupd
                                (K new_ffi) (labSem_state_mem_fupd (K
                                new_m) s)))))))))) | _86 ->
                                (Error,s)) | _87 -> (Error,s)) | _88
                                -> (Error,s))`;;
hol4_overload "evaluate" "labSem_evaluate";;

let semantics_def = cake_define
  `labSem_semantics s =
   (if ?k. FST (evaluate (state_clock_fupd (K k) s)) = Error then
     ffi_Fail else
     match some (\res.
       ?k t outcome.
         evaluate (state_clock_fupd (K k) s) = (Halt outcome,t) /\
         res = ffi_Terminate outcome (ffi_state_io_events (state_ffi
           t))) with SOME res -> res | NONE ->
       ffi_Diverge
          (build_lprefix_lub
            (IMAGE (\k. fromList (ffi_state_io_events (state_ffi
              (SND (evaluate (state_clock_fupd (K k) s)))))) UNIV)))`;;
hol4_overload "semantics" "labSem_semantics";;
