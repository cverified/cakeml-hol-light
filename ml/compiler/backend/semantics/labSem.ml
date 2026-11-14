(* ======================================================== *)
(*  labSem: ported from HOL4's
    compiler/backend/semantics/labSemScript.sml
    A definition theory, with 37 definitions, 2 datatypes and 2
    theorems.  Needed by 6 files of the port.  *)
(* ======================================================== *)

(*
  The formal semantics of labLang
*)

needs "compiler/backend/labLang.ml";;
needs "compiler/backend/semantics/targetSem.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "lib/alignment.ml";;
needs "lib/binary_ieee.ml";;
needs "lib/byte.ml";;
needs "lib/integer_word.ml";;
needs "lib/lprefix_lub.ml";;
needs "lib/sptree.ml";;
needs "misc/misc.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/fpSem.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "labSem"
  ["labLang"; "targetSem"; "wordSem"];;

let word8_loc_INDUCT,word8_loc_RECURSION = define_datatype
  "word8_loc =
     Byte word8
   | LocByte num num num";;

let labSem_state_FIELDS = define_record "labSem_state"
  ["regs","num->'a word_loc";
   "fp_regs","num->word64";
   "mem","'a word->'a word_loc";
   "mem_domain","'a word->bool";
   "shared_mem_domain","'a word->bool";
   "pc","num";
   "be","bool";
   "ffi","'ffi ffi_state";
   (* oracle *)
   (* oracle: sequence of havoc on registers at each FFI call *)
   "io_regs","num->ffiname->num->('a word) option";
   (* seq number *)
   (* ffi name *)
   (* register *)
   "cc_regs","num->num->('a word) option";
   (* same as io_regs but for calling clear cache *)
   (* oracles: sequence of havoc on FP registers at each FFI call / clear-cache call; a SharedMem call consumes an io_fp_regs position without using it (the machine-level counter is shared with ExtCall) *)
   "io_fp_regs","num->num->word64";
   (* seq number *)
   (* FP register *)
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

let is_Label_def = new_definition
  `is_Label x1 =
        match x1 with
          labLang_Label _4 _5 _6 -> T
        | _7 -> F`;;
add_simp is_Label_def;;

let _ = size_thms "sec";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let asm_fetch_aux_def,asm_fetch_aux_ind = define_wf
  `MEASURE (\(x0,x1). list_size (sec_size (\x. 0)) x1)`
  [`asm_fetch_aux pos [] = NONE`;
   `asm_fetch_aux pos (CONS (Section k []) xs) = asm_fetch_aux pos xs`;
   `asm_fetch_aux pos (CONS (Section k (CONS y ys)) xs) =
         (if is_Label y then asm_fetch_aux pos (CONS (Section k
             ys) xs) else if pos = (0:num) then SOME y else
             asm_fetch_aux (pos - 1) (CONS (Section k ys) xs))`];;

let asm_fetch_def = new_definition
  `asm_fetch s = asm_fetch_aux (labSem_state_pc s) (labSem_state_code
  s)`;;

let labSem_upd_pc_def = new_definition
  `labSem_upd_pc pc' s = labSem_state_pc_fupd (K pc') s`;;
let labSem_upd_reg_def = new_definition
  `labSem_upd_reg r w s = labSem_state_regs_fupd (K ((r =+ w)
  (labSem_state_regs s))) s`;;
let labSem_upd_mem_def = new_definition
  `labSem_upd_mem a w s = labSem_state_mem_fupd (K ((a =+ w)
  (labSem_state_mem s))) s`;;

(* HOL4 labSemScript.sml:77: the overload read_reg, which the port
   expands *)

let labSem_assert_def = new_definition
  `labSem_assert b s = labSem_state_failed_fupd (K (~b \/
  labSem_state_failed s)) s`;;

let labSem_reg_imm_def = define_cases
  [`labSem_reg_imm (Reg r) s = (\r s. labSem_state_regs s r) r s`;
   `labSem_reg_imm (Imm w) s = wordLang_Word w`];;
add_simp labSem_reg_imm_def;;

let labSem_binop_upd_def = define_general
  [`labSem_binop_upd r (asm_Add:binop) w1 w2 = labSem_upd_reg r
    (wordLang_Word (w1 + w2))`;
   `labSem_binop_upd r (asm_Sub:binop) w1 w2 = labSem_upd_reg r
    (wordLang_Word (w1 - w2))`;
   `labSem_binop_upd r (asm_And:binop) w1 w2 = labSem_upd_reg r
    (wordLang_Word (word_and w1 w2))`;
   `labSem_binop_upd r (asm_Or:binop) w1 w2 = labSem_upd_reg r
    (wordLang_Word (word_or w1 w2))`;
   `labSem_binop_upd r (asm_Xor:binop) w1 w2 = labSem_upd_reg r
    (wordLang_Word (word_xor w1 w2))`];;

let labSem_arith_upd_def = define_cases
  [`labSem_arith_upd (asm_Binop b r1 r2 (ri:'a asm_reg_imm)) s =
         (match ((\r s. labSem_state_regs s r) r2
             s,labSem_reg_imm ri s) with (wordLang_Word
             w1,wordLang_Word w2) -> labSem_binop_upd r1 b w1 w2 s |
             (x,_16) -> (if b = asm_Or /\ ri = Reg r2 then
             labSem_upd_reg r1 x s else labSem_assert F s))`;
   `labSem_arith_upd (asm_Shift l r1 r2 ri) s =
         (match ((\r s. labSem_state_regs s r) r2 s,labSem_reg_imm
             ri s) with (wordLang_Word w1,wordLang_Word w2) ->
             labSem_assert (w2n w2 < dimindex (:'a))
                 (labSem_upd_reg r1 (wordLang_Word (asmSem_word_shift
                 l w1 (w2n w2))) s) | _19 -> labSem_assert F s)`;
   `labSem_arith_upd (asm_Div r1 r2 r3) s =
         (match ((\r s. labSem_state_regs s r) r3 s,(\r s.
             labSem_state_regs s r) r2 s) with (wordLang_Word
             q,wordLang_Word w2) ->
           labSem_assert (~(q = (n2w 0))) (labSem_upd_reg r1
               (wordLang_Word (w2 / q)) s) | _22 -> labSem_assert F
               s)`;
   `labSem_arith_upd (asm_AddCarry r1 r2 r3 r4) s =
         (match ((\r s. labSem_state_regs s r) r2 s,(\r s.
             labSem_state_regs s r) r3 s,(\r s. labSem_state_regs s r)
             r4 s) with (wordLang_Word w2,wordLang_Word w3,wordLang_Word
             w4) ->
           (let r = w2n w2 + w2n w3 + (if w4 = (n2w 0) then 0 else
               1) in
             labSem_upd_reg r4 (wordLang_Word (if dimword (:'a) <= r
                 then (n2w 1) else (n2w 0)))
                (labSem_upd_reg r1 (wordLang_Word (n2w r)) s)) |
                    _25 -> labSem_assert F s)`;
   `labSem_arith_upd (asm_LongMul r1 r2 r3 r4) s =
         (match ((\r s. labSem_state_regs s r) r3 s,(\r s.
             labSem_state_regs s r) r4 s) with (wordLang_Word
             w3,wordLang_Word w4) ->
           (let r = w2n w3 * w2n w4 in
          labSem_upd_reg r2 (wordLang_Word (n2w r))
           (labSem_upd_reg r1 (wordLang_Word (n2w (r DIV dimword
               (:'a)))) s)) | _26 -> labSem_assert F s)`;
   `labSem_arith_upd (asm_LongDiv r1 r2 r3 r4 r5) s =
         (match ((\r s. labSem_state_regs s r) r3 s,(\r s.
             labSem_state_regs s r) r4 s,(\r s. labSem_state_regs s r)
             r5 s) with (wordLang_Word w3,wordLang_Word w4,wordLang_Word
             w5) ->
           (let n = w2n w3 * dimword (:'a) + w2n w4 in
           let d = w2n w5 in
           let q = n DIV d in
           labSem_assert (~(d = 0) /\ q < dimword (:'a))
             (labSem_upd_reg r1 (wordLang_Word (n2w q))
                 (labSem_upd_reg r2 (wordLang_Word (n2w (n MOD d)))
                 s))) | _27 -> labSem_assert F s)`;
   `labSem_arith_upd (asm_AddOverflow r1 r2 r3 r4) s =
         (match ((\r s. labSem_state_regs s r) r2 s,(\r s.
             labSem_state_regs s r) r3 s) with (wordLang_Word
             w2,wordLang_Word w3) ->
             labSem_upd_reg r4 (wordLang_Word (if ~(w2i (w2 + w3) =
                 w2i w2 + w2i w3) then (n2w 1) else (n2w 0)))
                (labSem_upd_reg r1 (wordLang_Word (w2 + w3)) s) |
                    _28 -> labSem_assert F s)`;
   `labSem_arith_upd (asm_SubOverflow r1 r2 r3 r4) s =
         (match ((\r s. labSem_state_regs s r) r2 s,(\r s.
             labSem_state_regs s r) r3 s) with (wordLang_Word
             w2,wordLang_Word w3) ->
             labSem_upd_reg r4 (wordLang_Word (if ~(w2i (w2 - w3) =
                 w2i w2 - w2i w3) then (n2w 1) else (n2w 0)))
                (labSem_upd_reg r1 (wordLang_Word (w2 - w3)) s)
                    | _29 -> labSem_assert F s)`];;
add_simp labSem_arith_upd_def;;

let labSem_upd_fp_reg_def = new_definition
  `labSem_upd_fp_reg r v s = labSem_state_fp_regs_fupd (K ((r =+ v)
  (labSem_state_fp_regs s))) s`;;
let labSem_read_fp_reg_def = new_definition
  `labSem_read_fp_reg r s = labSem_state_fp_regs s r`;;

let labSem_fp_upd_def = define_cases
  [`labSem_fp_upd (FPLess r d1 d2) (s:('a,'c,'ffi)labSem_state) =
         labSem_upd_reg r (wordLang_Word (if fp64_lessThan
             (labSem_read_fp_reg d1 s) (labSem_read_fp_reg d2 s) then
             (n2w 1) else (n2w 0))) s`;
   `labSem_fp_upd (FPLessEqual r d1 d2) (s:('a,'c,'ffi)labSem_state) =
         labSem_upd_reg r (wordLang_Word (if fp64_lessEqual
             (labSem_read_fp_reg d1 s) (labSem_read_fp_reg d2 s) then
             (n2w 1) else (n2w 0))) s`;
   `labSem_fp_upd (FPEqual r d1 d2) (s:('a,'c,'ffi)labSem_state) =
         labSem_upd_reg r (wordLang_Word (if fp64_equal
             (labSem_read_fp_reg d1 s) (labSem_read_fp_reg d2 s) then
             (n2w 1) else (n2w 0))) s`;
   `labSem_fp_upd (FPMov d1 d2) (s:('a,'c,'ffi)labSem_state) =
    labSem_upd_fp_reg d1 (labSem_read_fp_reg d2 s) s`;
   `labSem_fp_upd (FPAbs d1 d2) (s:('a,'c,'ffi)labSem_state) =
    labSem_upd_fp_reg d1 (fp64_abs (labSem_read_fp_reg d2 s)) s`;
   `labSem_fp_upd (FPNeg d1 d2) (s:('a,'c,'ffi)labSem_state) =
    labSem_upd_fp_reg d1 (fp64_negate (labSem_read_fp_reg d2 s)) s`;
   `labSem_fp_upd (FPSqrt d1 d2) (s:('a,'c,'ffi)labSem_state) =
         labSem_upd_fp_reg d1 (fp64_sqrt roundTiesToEven
             (labSem_read_fp_reg d2 s)) s`;
   `labSem_fp_upd (FPAdd d1 d2 d3) (s:('a,'c,'ffi)labSem_state) =
         labSem_upd_fp_reg d1
           (fp64_add roundTiesToEven (labSem_read_fp_reg d2 s)
               (labSem_read_fp_reg d3 s)) s`;
   `labSem_fp_upd (FPSub d1 d2 d3) (s:('a,'c,'ffi)labSem_state) =
         labSem_upd_fp_reg d1
           (fp64_sub roundTiesToEven (labSem_read_fp_reg d2 s)
               (labSem_read_fp_reg d3 s)) s`;
   `labSem_fp_upd (FPMul d1 d2 d3) (s:('a,'c,'ffi)labSem_state) =
         labSem_upd_fp_reg d1
           (fp64_mul roundTiesToEven (labSem_read_fp_reg d2 s)
               (labSem_read_fp_reg d3 s)) s`;
   `labSem_fp_upd (FPDiv d1 d2 d3) (s:('a,'c,'ffi)labSem_state) =
         labSem_upd_fp_reg d1
           (fp64_div roundTiesToEven (labSem_read_fp_reg d2 s)
               (labSem_read_fp_reg d3 s)) s`;
   `labSem_fp_upd (FPFma d1 d2 d3) (s:('a,'c,'ffi)labSem_state) =
         labSem_upd_fp_reg d1
           (fpfma (labSem_read_fp_reg d1 s) (labSem_read_fp_reg
               d2 s) (labSem_read_fp_reg d3 s)) s`;
   `labSem_fp_upd (FPMovToReg r1 r2 d) (s:('a,'c,'ffi)labSem_state) =
         (if dimindex (:'a) = 64 then
           labSem_upd_reg r1 (wordLang_Word (w2w (labSem_read_fp_reg
               d s))) s else let v = labSem_read_fp_reg d s in
           labSem_upd_reg r2 (wordLang_Word ((63 >< 32) v))
               (labSem_upd_reg r1 (wordLang_Word ((31 >< 0) v)) s))`;
   `labSem_fp_upd (FPMovFromReg d r1 r2) (s:('a,'c,'ffi)labSem_state) =
         (if dimindex (:'a) = 64 then
           match (\r s. labSem_state_regs s r) r1 s with
             wordLang_Word w1 -> labSem_upd_fp_reg d (w2w w1) s |
                 _33 -> labSem_assert F s else
           match ((\r s. labSem_state_regs s r) r1 s,(\r s.
               labSem_state_regs s r) r2 s) with
             (wordLang_Word w1,wordLang_Word w2) ->
                 labSem_upd_fp_reg d (w2 @@ w1) s | _34 ->
                 labSem_assert F s)`;
   `labSem_fp_upd (FPToInt d1 d2) (s:('a,'c,'ffi)labSem_state) =
         (match fp64_to_int roundTiesToEven (labSem_read_fp_reg d2
             s) with
             SOME i ->
               (let w = (i2w i:word32) in
                 (if dimindex (:'a) = 64 then
                    labSem_upd_fp_reg d1 (w2w w) else let (h,l) =
                        (if ODD d1 then (63,32) else (31,0)) in
                         labSem_upd_fp_reg (d1 DIV 2)
                           (bit_field_insert h l w
                               (labSem_read_fp_reg (d1 DIV 2) s)))
                    (labSem_assert (w2i w = i) s)) | _35 ->
                        labSem_assert F s)`;
   `labSem_fp_upd (FPFromInt d1 d2) (s:('a,'c,'ffi)labSem_state) =
         (let i = (if dimindex (:'a) = 64 then
                   w2i ((31 >< 0) (labSem_read_fp_reg d2 s):word32)
                       else let v = labSem_read_fp_reg (d2 DIV 2) s in
                   w2i (if ODD d2 then (63 >< 32) v else (31 >< 0)
                       v:'a word)) in
           labSem_upd_fp_reg d1 (int_to_fp64 roundTiesToEven i)
               s)`];;
add_simp labSem_fp_upd_def;;

let labSem_addr_def = define_general
  [`labSem_addr (Addr r offset) s =
     (match (\r s. labSem_state_regs s r) r s with wordLang_Word
       w -> SOME (w + offset) | _36 -> NONE)`];;

let is_Loc_def = new_definition
  `is_Loc x1 =
        match x1 with
          wordLang_Loc _39 _40 -> T
        | _41 -> F`;;

let labSem_mem_store_def = new_definition
  `labSem_mem_store r a (s:('a,'c,'ffi)labSem_state) =
     (match labSem_addr a s with NONE -> labSem_assert F s | SOME w
       -> labSem_assert ((w2n w MOD (dimindex (:'a) DIV 8) = 0) /\
                         w IN labSem_state_mem_domain s)
                   (labSem_upd_mem w ((\r s. labSem_state_regs s
                     r) r s) s))`;;

let labSem_mem_load_def = new_definition
  `labSem_mem_load r a (s:('a,'c,'ffi)labSem_state) =
     (match labSem_addr a s with NONE -> labSem_assert F s | SOME w
       -> labSem_assert ((w2n w MOD (dimindex (:'a) DIV 8) = 0) /\
                         w IN labSem_state_mem_domain s)
                   (labSem_upd_reg r (labSem_state_mem s w) s))`;;

let mem_load32_def = new_definition
  `mem_load32 r a (s:('a,'c,'ffi)labSem_state) =
     (match labSem_addr a s with NONE -> labSem_assert F s | SOME w
       ->
         (match mem_load_32 (labSem_state_mem s)
           (labSem_state_mem_domain s) (labSem_state_be s) w with
           SOME v -> labSem_upd_reg r (wordLang_Word (w2w v)) s |
           NONE -> labSem_assert F s))`;;

let mem_store32_def = new_definition
  `mem_store32 r a (s:('a,'c,'ffi)labSem_state) =
     (match labSem_addr a s with NONE -> labSem_assert F s | SOME w
       ->
         (match (\r s. labSem_state_regs s r) r s with wordLang_Word
           b ->
            (match mem_store_32 (labSem_state_mem s)
              (labSem_state_mem_domain s) (labSem_state_be s) w (w2w
              b) with SOME m -> (labSem_state_mem_fupd (K m) s) |
              NONE -> labSem_assert F s) | _42 -> labSem_assert F s))`;;

let mem_load_byte_def = new_definition
  `mem_load_byte r a (s:('a,'c,'ffi)labSem_state) =
     (match labSem_addr a s with NONE -> labSem_assert F s | SOME w
       ->
         (match mem_load_byte_aux (labSem_state_mem s)
           (labSem_state_mem_domain s) (labSem_state_be s) w with
           SOME v -> labSem_upd_reg r (wordLang_Word (w2w v)) s |
           NONE -> labSem_assert F s))`;;

let mem_store_byte_def = new_definition
  `mem_store_byte r a (s:('a,'c,'ffi)labSem_state) =
     (match labSem_addr a s with NONE -> labSem_assert F s | SOME w
       ->
         (match (\r s. labSem_state_regs s r) r s with wordLang_Word
           b ->
            (match mem_store_byte_aux (labSem_state_mem s)
              (labSem_state_mem_domain s) (labSem_state_be s) w (w2w
              b) with SOME m -> (labSem_state_mem_fupd (K m) s) |
              NONE -> labSem_assert F s) | _43 -> labSem_assert F s))`;;

let labSem_mem_op_def = define_general
  [`labSem_mem_op (asm_Load:memop) r (a:'a asm_addr) =
    labSem_mem_load r a`;
   `labSem_mem_op (asm_Store:memop) r (a:'a asm_addr) =
    labSem_mem_store r a`;
   `labSem_mem_op (asm_Load32:memop) r (a:'a asm_addr) = mem_load32 r
    a`;
   `labSem_mem_op (asm_Store32:memop) r (a:'a asm_addr) = mem_store32
    r a`;
   `labSem_mem_op asm_Load8 r (a:'a asm_addr) = mem_load_byte r a`;
   `labSem_mem_op asm_Store8 r (a:'a asm_addr) = mem_store_byte r a`;
   `labSem_mem_op asm_Load16 r (a:'a asm_addr) = labSem_assert F`;
   `labSem_mem_op asm_Store16 r (a:'a asm_addr) = labSem_assert F`];;
add_simp labSem_mem_op_def;;

let asm_inst_def = define_cases
  [`asm_inst asm_Skip (s:('a,'c,'ffi)labSem_state) =
    (s:('a,'c,'ffi)labSem_state)`;
   `asm_inst (asm_Const r imm) (s:('a,'c,'ffi)labSem_state) =
    ((labSem_upd_reg r (wordLang_Word imm)
    s):('a,'c,'ffi)labSem_state)`;
   `asm_inst (asm_Arith x) (s:('a,'c,'ffi)labSem_state) =
    ((labSem_arith_upd x s):('a,'c,'ffi)labSem_state)`;
   `asm_inst (asm_Mem m r a) (s:('a,'c,'ffi)labSem_state) =
    ((labSem_mem_op m r a s):('a,'c,'ffi)labSem_state)`;
   `asm_inst (asm_FP fp) (s:('a,'c,'ffi)labSem_state) =
    ((labSem_fp_upd fp s):('a,'c,'ffi)labSem_state)`];;
add_simp asm_inst_def;;

let labSem_dec_clock_def = new_definition
  `labSem_dec_clock s = labSem_state_clock_fupd (K
  (labSem_state_clock s - 1)) s`;;

let inc_pc_def = new_definition
  `inc_pc s = labSem_state_pc_fupd (K (labSem_state_pc s + 1)) s`;;

(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let asm_code_length_def,asm_code_length_ind = define_guess_cheat
  [`asm_code_length [] = 0`;
   `asm_code_length (CONS (Section k []) xs) = asm_code_length xs`;
   `asm_code_length (CONS (Section k (CONS y ys)) xs) =
         asm_code_length (CONS (Section k ys) xs) + (if
             is_Label y then 0 else 1:num)`];;

(* [local] *)
let asm_fetch_IMP = prove
 (`(asm_fetch s = SOME x) ==> labSem_state_pc
     s < asm_code_length (labSem_state_code s)`,
  CHEAT_TAC);;

let lab_to_loc_def = define_general
  [`lab_to_loc (labLang_Lab n1 n2:lab) = wordLang_Loc n1 n2`];;

(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let loc_to_pc_def,loc_to_pc_ind = define_guess_cheat
  [`loc_to_pc n1 n2 [] = NONE`;
   `loc_to_pc n1 n2 (CONS (Section k xs) ys) =
         (if (k = n1) /\ (n2 = 0) then SOME (0:num) else
           match xs with [] -> loc_to_pc n1 n2 ys | (CONS z zs) ->
             (if (?k. z = labLang_Label n1 n2 k) /\ ~(n2 = 0) then
                 SOME 0 else
               if is_Label z then loc_to_pc n1 n2 (CONS (Section k
                   zs) ys) else
                 match loc_to_pc n1 n2 (CONS (Section k zs) ys)
                     with NONE -> NONE | SOME pos -> SOME (pos +
                     (1:num))))`];;

let asm_inst_consts = prove
 (`(labSem_state_pc (asm_inst i s) = labSem_state_pc s) /\
   (labSem_state_code (asm_inst i s) = labSem_state_code s) /\
   (labSem_state_clock (asm_inst i s) = labSem_state_clock s) /\
   (labSem_state_ffi (asm_inst i s) = labSem_state_ffi s) /\
   (labSem_state_io_regs (asm_inst i s) = labSem_state_io_regs s) /\
   (labSem_state_io_fp_regs (asm_inst i s) = labSem_state_io_fp_regs
     s) /\
   (labSem_state_cc_regs (asm_inst i s) = labSem_state_cc_regs s) /\
   (labSem_state_cc_fp_regs (asm_inst i s) = labSem_state_cc_fp_regs
     s) /\
   (labSem_state_ptr_reg (asm_inst i s) = labSem_state_ptr_reg s) /\
   (labSem_state_len_reg (asm_inst i s) = labSem_state_len_reg s) /\
   (labSem_state_ptr2_reg (asm_inst i s) = labSem_state_ptr2_reg s)
     /\
   (labSem_state_len2_reg (asm_inst i s) = labSem_state_len2_reg s)
     /\
   (labSem_state_link_reg (asm_inst i s) = labSem_state_link_reg s)`,
  CHEAT_TAC);;

let get_pc_value_def = new_definition
  `get_pc_value lab (s:('a,'c,'ffi)labSem_state) =
     (match lab with labLang_Lab n1 n2 -> loc_to_pc n1 n2
       (labSem_state_code s))`;;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let next_label_def,next_label_ind = define_wf
  `MEASURE (\x0. list_size (sec_size (\x. 0)) x0)`
  [`next_label x1 =
        match x1 with
          [] -> NONE
        | CONS (Section k []) xs -> next_label xs
        | (CONS (Section k (CONS (labLang_Label n1 n2 _44) ys)) xs)
          -> SOME (wordLang_Loc n1 n2)
        | (CONS (Section k (CONS y ys)) xs) -> next_label (CONS
          (Section k ys) xs)`];;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let get_lab_after_def,get_lab_after_ind = define_wf
  `MEASURE (\(x0,x1). list_size (sec_size (\x. 0)) x1)`
  [`get_lab_after pos [] = NONE`;
   `get_lab_after pos (CONS (Section k []) xs) = get_lab_after pos xs`;
   `get_lab_after pos (CONS (Section k (CONS y ys)) xs) =
         (if is_Label y then get_lab_after pos (CONS (Section k
             ys) xs) else if pos = (0:num) then next_label (CONS
             (Section k ys) xs) else get_lab_after (pos - 1) (CONS
             (Section k ys) xs))`];;

let get_ret_Loc_def = new_definition
  `get_ret_Loc s = get_lab_after (labSem_state_pc s)
  (labSem_state_code s)`;;

let share_mem_load_def = new_definition
  `share_mem_load r ad (s:('a,'c,'ffi)labSem_state) n =
     (match labSem_addr ad s with NONE -> NONE | SOME v ->
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

let share_mem_store_def = new_definition
  `share_mem_store r ad (s:('a,'c,'ffi)labSem_state) n =
     (match labSem_state_regs s r with wordLang_Word w ->
       (match labSem_addr ad s with NONE -> NONE | SOME v ->
         (if (if n = 0 then (
                  w2n v MOD (dimindex (:'a) DIV 8) = 0 /\ (v IN
                    labSem_state_shared_mem_domain s)) else byte_align v
                    IN labSem_state_shared_mem_domain s) then
              (match call_FFI (labSem_state_ffi s) (ffi_SharedMem
                MappedWrite)
                [n2w n]
                (APPEND (if n = 0 then word_to_bytes w F else TAKE n
                  (word_to_bytes w F)) (word_to_bytes v F)) with
                  FFI_final outcome -> SOME (FFI_final outcome,s) |
                  FFI_return new_ffi new_bytes ->
                  SOME ((FFI_return new_ffi new_bytes),
                    inc_pc (labSem_dec_clock
                      (labSem_state_ffi_fupd (K new_ffi) s)))) else
                      NONE)) | _45 -> NONE)`;;

let share_mem_op_def = define_cases
  [`share_mem_op (asm_Load:memop) r ad (s:('a,'c,'ffi)labSem_state) =
        share_mem_load r ad s 0`;
   `share_mem_op asm_Load8 r ad (s:('a,'c,'ffi)labSem_state) =
    share_mem_load r ad s 1`;
   `share_mem_op asm_Load16 r ad (s:('a,'c,'ffi)labSem_state) =
    share_mem_load r ad s 2`;
   `share_mem_op (asm_Store:memop) r ad (s:('a,'c,'ffi)labSem_state)
    = share_mem_store r ad s 0`;
   `share_mem_op asm_Store8 r ad (s:('a,'c,'ffi)labSem_state) =
    share_mem_store r ad s 1`;
   `share_mem_op asm_Store16 r ad (s:('a,'c,'ffi)labSem_state) =
    share_mem_store r ad s 2`;
   `share_mem_op (asm_Load32:memop) r ad (s:('a,'c,'ffi)labSem_state)
    = share_mem_load r ad s 4`;
   `share_mem_op (asm_Store32:memop) r ad
    (s:('a,'c,'ffi)labSem_state) = share_mem_store r ad s 4`];;

let labSem_evaluate_def,labSem_evaluate_ind = assume_definition_rec
  "termination (CHEAT_TAC)"
  [`labSem_evaluate (s:('a,'c,'ffi)labSem_state) =
     (if labSem_state_clock s = 0 then (targetSem_TimeOut,s) else
     match asm_fetch s with SOME (labLang_Asm (Asmi a) _46 _47) ->
         (match a with asm_Inst i ->
             (let s1 = asm_inst i s in
                if labSem_state_failed s1 then (targetSem_Error,s)
                  else labSem_evaluate (inc_pc (labSem_dec_clock s1)))
                  | asm_JumpReg r ->
             (match (\r s. labSem_state_regs s r) r s with
               wordLang_Loc n1 n2 ->
                  (match loc_to_pc n1 n2 (labSem_state_code s) with
                    NONE -> (targetSem_Error,s) | SOME p ->
                       labSem_evaluate (labSem_upd_pc p
                         (labSem_dec_clock s))) | _48 ->
                         (targetSem_Error,s)) | _49 ->
                         (targetSem_Error,s)) | SOME (labLang_Asm (Cbw
                         r1 r2) _50 _51) ->
       (match ((\r s. labSem_state_regs s r) r1 s,(\r s.
         labSem_state_regs s r) r2 s) with (wordLang_Word
         w1,wordLang_Word w2) ->
         (match buffer_write (labSem_state_code_buffer s) w1 (w2w
           w2) with SOME new_cb ->
           labSem_evaluate (inc_pc (labSem_dec_clock
             (labSem_state_code_buffer_fupd (K new_cb) s))) | _52 ->
             (targetSem_Error,s)) | _53 -> (targetSem_Error,s)) | SOME
             (labLang_Asm (ShareMem m r ad) _54 _55) ->
        (match share_mem_op m r ad s with SOME (FFI_final
          outcome,s') -> (targetSem_Halt (ffi_FFI_outcome outcome),s')
          | SOME (FFI_return _56 _57,s') ->
             labSem_evaluate (labSem_state_io_fp_regs_fupd (K
               (misc_shift_seq 1 (labSem_state_io_fp_regs s')))
               (labSem_state_io_regs_fupd (K (misc_shift_seq 1
               (labSem_state_io_regs s'))) s')) | NONE ->
               (targetSem_Error,s)) | SOME (labLang_LabAsm labLang_Halt
               _58 _59 _60) ->
        (match labSem_state_regs s (labSem_state_ptr_reg s) with
          wordLang_Word (n2w 0) -> (targetSem_Halt ffi_Success,s) |
          wordLang_Word _61 -> (targetSem_Halt
          ffi_Resource_limit_hit,s) | _62 -> (targetSem_Error,s)) |
          SOME (labLang_LabAsm (labLang_LocValue r lab) _63 _64 _65) ->
        (if get_pc_value lab s = NONE then (targetSem_Error,s) else
           let s1 = labSem_upd_reg r (lab_to_loc lab) s in
             labSem_evaluate (inc_pc (labSem_dec_clock s1))) | SOME
               (labLang_LabAsm (labLang_Jump l) _66 _67 _68) ->
        (match get_pc_value l s with NONE -> (targetSem_Error,s) |
          SOME p -> labSem_evaluate (labSem_upd_pc p (labSem_dec_clock
          s))) | SOME (labLang_LabAsm (labLang_JumpCmp c r ri l) _69
          _70 _71) ->
        (match wordSem_word_cmp c ((\r s. labSem_state_regs s r) r
          s) (labSem_reg_imm ri s) with NONE -> (targetSem_Error,s) |
          SOME F -> labSem_evaluate (inc_pc (labSem_dec_clock s)) |
          SOME T ->
          (match get_pc_value l s with NONE -> (targetSem_Error,s) |
            SOME p -> labSem_evaluate (labSem_upd_pc p
            (labSem_dec_clock s)))) | SOME (labLang_LabAsm
            (labLang_Call l) _72 _73 _74) ->
        (match get_pc_value l s with NONE -> (targetSem_Error,s) |
          SOME p ->
          (match get_ret_Loc s with NONE -> (targetSem_Error,s) |
            SOME k ->
              (let s1 = labSem_upd_reg (labSem_state_link_reg s) k s
                in
                labSem_evaluate (labSem_upd_pc p (labSem_dec_clock
                  s1))))) | SOME (labLang_LabAsm labLang_Install _75
                  _76 _77) ->
        (match (labSem_state_regs s (labSem_state_ptr_reg
          s),labSem_state_regs s (labSem_state_len_reg
          s),labSem_state_regs s (labSem_state_link_reg s)) with
          (wordLang_Word w1,wordLang_Word w2,wordLang_Loc n1 n2) ->
            (match (buffer_flush (labSem_state_code_buffer s) w1
              w2,loc_to_pc n1 n2 (labSem_state_code s)) with (SOME
              (bytes,cb),SOME new_pc) ->
               (let (cfg,prog) = labSem_state_compile_oracle s 0 in
               // the next oracle program
               let new_oracle = misc_shift_seq 1
                 (labSem_state_compile_oracle s) in
                 (match (labSem_state_compile s cfg prog,prog) with
                   (SOME (bytes',cfg'),CONS (Section k _78) _79) ->
                    (if bytes = bytes' /\ FST (new_oracle 0) = cfg'
                      then
                      // the oracle was correct
                      labSem_evaluate
                        (labSem_state_clock_fupd (K
                          (labSem_state_clock s - 1))
                          (labSem_state_compile_oracle_fupd (K
                          new_oracle) (labSem_state_fp_regs_fupd (K
                          (\n. labSem_state_cc_fp_regs s 0 n))
                          (labSem_state_regs_fupd (K
                          ((labSem_state_ptr_reg s =+ wordLang_Loc k 0)
                              (\a. get_reg_value
                                (labSem_state_cc_regs s 0 a)
                              (labSem_state_regs s a)
                                wordLang_Word)))
                                (labSem_state_cc_fp_regs_fupd (K
                                (misc_shift_seq 1
                                (labSem_state_cc_fp_regs s)))
                                (labSem_state_cc_regs_fupd (K
                                (misc_shift_seq 1 (labSem_state_cc_regs
                                s))) (labSem_state_code_fupd (K (APPEND
                                (labSem_state_code s) prog))
                                (labSem_state_code_buffer_fupd (K cb)
                                (labSem_state_pc_fupd (K new_pc)
                                s))))))))) else
                      (targetSem_Error,s)) | _80 ->
                        (targetSem_Error,s))) | _81 ->
                        (targetSem_Error,s)) | _82 ->
                        (targetSem_Error,s)) | SOME (labLang_LabAsm
                        (labLang_CallFFI ffi_index) _83 _84 _85) ->
        (match (labSem_state_regs s (labSem_state_len_reg
          s),labSem_state_regs s (labSem_state_ptr_reg
          s),labSem_state_regs
               s (labSem_state_len2_reg s),labSem_state_regs s
                 (labSem_state_ptr2_reg s),labSem_state_regs s
                 (labSem_state_link_reg s)) with (wordLang_Word
                 w,wordLang_Word w2,wordLang_Word w3,wordLang_Word
                 w4,wordLang_Loc n1 n2) ->
          (match (read_bytearray w2 (w2n w) (mem_load_byte_aux
            (labSem_state_mem s) (labSem_state_mem_domain s)
            (labSem_state_be s)),
                 read_bytearray w4 (w2n w3) (mem_load_byte_aux
                   (labSem_state_mem s) (labSem_state_mem_domain s)
                   (labSem_state_be s)),
                 loc_to_pc n1 n2 (labSem_state_code s)) with (SOME
                   bytes,SOME bytes2,SOME new_pc) ->
              (match call_FFI (labSem_state_ffi s) (ffi_ExtCall
                ffi_index) bytes bytes2 with FFI_final outcome ->
                (targetSem_Halt (ffi_FFI_outcome outcome),s) |
                FFI_return new_ffi new_bytes ->
                   (let new_io_regs = misc_shift_seq 1
                     (labSem_state_io_regs s) in
                   let new_io_fp_regs = misc_shift_seq 1
                     (labSem_state_io_fp_regs s) in
                   let new_m = write_bytearray w4 new_bytes
                     (labSem_state_mem s) (labSem_state_mem_domain s)
                     (labSem_state_be s) in
                     labSem_evaluate (labSem_state_clock_fupd (K
                       (labSem_state_clock s - 1))
                       (labSem_state_pc_fupd (K new_pc)
                       (labSem_state_fp_regs_fupd (K (\n.
                       labSem_state_io_fp_regs s 0 n))
                       (labSem_state_regs_fupd (K (\a. get_reg_value
                       (labSem_state_io_regs s 0 (ffi_ExtCall
                       ffi_index) a)
                              (labSem_state_regs s a)
                                wordLang_Word))
                                (labSem_state_io_fp_regs_fupd (K
                                new_io_fp_regs)
                                (labSem_state_io_regs_fupd (K
                                new_io_regs) (labSem_state_ffi_fupd
                                (K new_ffi) (labSem_state_mem_fupd
                                (K new_m) s)))))))))) | _86 ->
                                (targetSem_Error,s)) | _87 ->
                                (targetSem_Error,s)) | _88 ->
                                (targetSem_Error,s))`];;

let labSem_semantics_def = new_definition
  `labSem_semantics s =
   (if ?k. FST (labSem_evaluate (labSem_state_clock_fupd (K k) s)) =
     targetSem_Error then ffi_Fail else
     match some (\res.
       ?k t outcome.
         labSem_evaluate (labSem_state_clock_fupd (K k) s) =
           (targetSem_Halt outcome,t) /\
         res = ffi_Terminate outcome (ffi_state_io_events
           (labSem_state_ffi t))) with SOME res -> res | NONE ->
       ffi_Diverge
          (build_lprefix_lub
            (IMAGE (\k. fromList (ffi_state_io_events
              (labSem_state_ffi (SND (labSem_evaluate
              (labSem_state_clock_fupd (K k) s)))))) UNIV)))`;;

(* and the interface *)
let _ = unhide_overloads ();;
