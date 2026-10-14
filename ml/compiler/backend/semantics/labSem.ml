(* ======================================================== *)
(*  labSem: ported from HOL4's
    compiler/backend/semantics/labSemScript.sml  *)
(* ======================================================== *)

(*
  The formal semantics of labLang
*)

needs "compiler/backend/labLang.ml";;
needs "compiler/backend/semantics/targetSem.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "lib/alignment.ml";;

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
   "code","'a labLang_prog";
   "compile","'c->'a labLang_prog->(word8 list#'c) option";
   "compile_oracle","num->'c#'a labLang_prog";
   "code_buffer","('a,8)buffer";
   "clock","num";
   "failed","bool";
   "ptr_reg","num";
   "len_reg","num";
   "ptr2_reg","num";
   "len2_reg","num";
   "link_reg","num"];;

let is_Label_def = cake_define
  `is_Label x1 =
        match x1 with
          (labLang_Label _1 _2 _3) -> T
        | _4 -> F`;;

let asm_fetch_aux_def = cake_define
  `(asm_fetch_aux pos [] = NONE) /\
   (asm_fetch_aux pos ((Section k []) :: xs) = asm_fetch_aux pos xs)
     /\
   (asm_fetch_aux pos ((Section k (y :: ys)) :: xs) =
      (if is_Label y then asm_fetch_aux pos ((Section k ys) :: xs)
        else if pos = (0:num) then SOME y else asm_fetch_aux (pos -
        1) ((Section k ys) :: xs)))`;;

let asm_fetch_def = cake_define
  `asm_fetch s = asm_fetch_aux (?_pc s) (?_code s)`;;

let upd_pc_def = cake_define
  `labSem_upd_pc pc s = ?_pc_fupd (K pc) s`;;
let upd_reg_def = cake_define
  `labSem_upd_reg r w s = ?_regs_fupd (K ((r =+ w) (?_regs s))) s`;;
let upd_mem_def = cake_define
  `labSem_upd_mem a w s = ?_mem_fupd (K ((a =+ w) (?_mem s))) s`;;

(* HOL4 overload (expanded in the port):
     read_reg = λr s. s.regs r *)

let assert_def = cake_define
  `labSem_assert b s = ?_failed_fupd (K (~b \/ ?_failed s)) s`;;

let reg_imm_def = cake_define
  `(labSem_reg_imm (Reg r) s = (\r s. ?_regs s r) r s) /\
   (labSem_reg_imm (Imm w) s = wordLang_Word w)`;;

let binop_upd_def = cake_define
  `(labSem_binop_upd r asm_Add w1 w2 = labSem_upd_reg r (wordLang_Word
  (w1 + w2))) /\
   (labSem_binop_upd r asm_Sub w1 w2 = labSem_upd_reg r
     (wordLang_Word (w1 - w2))) /\
   (labSem_binop_upd r asm_And w1 w2 = labSem_upd_reg r
     (wordLang_Word (word_and w1 w2))) /\
   (labSem_binop_upd r asm_Or w1 w2 = labSem_upd_reg r (wordLang_Word
     (word_or w1 w2))) /\
   (labSem_binop_upd r asm_Xor w1 w2 = labSem_upd_reg r
     (wordLang_Word (word_xor w1 w2)))`;;

let arith_upd_def = cake_define
  `(labSem_arith_upd (asm_Binop b r1 r2 (ri:'a labSem_reg_imm)) s =
      (match ((\r s. ?_regs s r) r2 s,labSem_reg_imm ri s) with
        (wordLang_Word w1,wordLang_Word w2) -> labSem_binop_upd r1 b w1
        w2 s | (x,_5) -> (if b = asm_Or /\ ri = Reg r2 then
        labSem_upd_reg r1 x s else labSem_assert F s))) /\
   (labSem_arith_upd (wordLang_Shift l r1 r2 ri) s =
      (match ((\r s. ?_regs s r) r2 s,labSem_reg_imm ri s) with
        (wordLang_Word w1,wordLang_Word w2) ->
          labSem_assert (w2n w2 < dimindex (:'a)) (labSem_upd_reg r1
            (wordLang_Word (asmSem_word_shift l w1 (w2n w2))) s) | _6 ->
            labSem_assert F s)) /\
   (labSem_arith_upd (asm_Div r1 r2 r3) s =
      (match ((\r s. ?_regs s r) r3 s,(\r s. ?_regs s r) r2 s) with
        (wordLang_Word q,wordLang_Word w2) ->
        labSem_assert (~(q = (n2w 0))) (labSem_upd_reg r1
          (wordLang_Word (w2 / q)) s) | _7 -> labSem_assert F s)) /\
   (labSem_arith_upd (asm_AddCarry r1 r2 r3 r4) s =
      (match ((\r s. ?_regs s r) r2 s,(\r s. ?_regs s r) r3 s,(\r s.
        ?_regs s r) r4 s) with (wordLang_Word w2,wordLang_Word
        w3,wordLang_Word w4) ->
        (let r = w2n w2 + w2n w3 + (if w4 = (n2w 0) then 0 else 1) in
          labSem_upd_reg r4 (wordLang_Word (if dimword (:'a) <= r
            then (n2w 1) else (n2w 0)))
             (labSem_upd_reg r1 (wordLang_Word (n2w r)) s)) | _8 ->
               labSem_assert F s)) /\
   (labSem_arith_upd (asm_LongMul r1 r2 r3 r4) s =
      (match ((\r s. ?_regs s r) r3 s,(\r s. ?_regs s r) r4 s) with
        (wordLang_Word w3,wordLang_Word w4) ->
        (let r = w2n w3 * w2n w4 in
       labSem_upd_reg r2 (wordLang_Word (n2w r))
        (labSem_upd_reg r1 (wordLang_Word (n2w (r DIV dimword
          (:'a)))) s)) | _9 -> labSem_assert F s)) /\
   (labSem_arith_upd (asm_LongDiv r1 r2 r3 r4 r5) s =
      (match ((\r s. ?_regs s r) r3 s,(\r s. ?_regs s r) r4 s,(\r s.
        ?_regs s r) r5 s) with (wordLang_Word w3,wordLang_Word
        w4,wordLang_Word w5) ->
        (let n = w2n w3 * dimword (:'a) + w2n w4 in
        let d = w2n w5 in
        let q = n DIV d in
        labSem_assert (~(d = 0) /\ q < dimword (:'a))
          (labSem_upd_reg r1 (wordLang_Word (n2w q)) (labSem_upd_reg
            r2 (wordLang_Word (n2w (n MOD d))) s))) | _10 ->
            labSem_assert F s)) /\
   (labSem_arith_upd (asm_AddOverflow r1 r2 r3 r4) s =
      (match ((\r s. ?_regs s r) r2 s,(\r s. ?_regs s r) r3 s) with
        (wordLang_Word w2,wordLang_Word w3) ->
          labSem_upd_reg r4 (wordLang_Word (if ~(w2i (w2 + w3) = w2i
            w2 + w2i w3) then (n2w 1) else (n2w 0)))
             (labSem_upd_reg r1 (wordLang_Word (w2 + w3)) s) | _11 ->
               labSem_assert F s)) /\
   (labSem_arith_upd (asm_SubOverflow r1 r2 r3 r4) s =
      (match ((\r s. ?_regs s r) r2 s,(\r s. ?_regs s r) r3 s) with
        (wordLang_Word w2,wordLang_Word w3) ->
          labSem_upd_reg r4 (wordLang_Word (if ~(w2i (w2 - w3) = w2i
            w2 - w2i w3) then (n2w 1) else (n2w 0)))
             (labSem_upd_reg r1 (wordLang_Word (w2 - w3)) s) | _12
               -> labSem_assert F s))`;;

let upd_fp_reg_def = cake_define
  `labSem_upd_fp_reg r semanticPrimitives_v s = ?_fp_regs_fupd (K ((r
  =+ semanticPrimitives_v) (?_fp_regs s))) s`;;
let read_fp_reg_def = cake_define
  `labSem_read_fp_reg r s = ?_fp_regs s r`;;

let fp_upd_def = cake_define
  `(labSem_fp_upd (FPLess r d1 d2) (s:('a,'c,'ffi)labSem_state) =
      labSem_upd_reg r (wordLang_Word (if fp64_lessThan
        (labSem_read_fp_reg d1 s) (labSem_read_fp_reg d2 s) then (n2w 1)
        else (n2w 0))) s) /\
   (labSem_fp_upd (FPLessEqual r d1 d2) s =
      labSem_upd_reg r (wordLang_Word (if fp64_lessEqual
        (labSem_read_fp_reg d1 s) (labSem_read_fp_reg d2 s) then (n2w 1)
        else (n2w 0))) s) /\
   (labSem_fp_upd (FPEqual r d1 d2) s =
      labSem_upd_reg r (wordLang_Word (if fp64_equal
        (labSem_read_fp_reg d1 s) (labSem_read_fp_reg d2 s) then (n2w 1)
        else (n2w 0))) s) /\
   (labSem_fp_upd (FPMov d1 d2) s = labSem_upd_fp_reg d1
     (labSem_read_fp_reg d2 s) s) /\
   (labSem_fp_upd (FPAbs d1 d2) s = labSem_upd_fp_reg d1 (fp64_abs
     (labSem_read_fp_reg d2 s)) s) /\
   (labSem_fp_upd (FPNeg d1 d2) s = labSem_upd_fp_reg d1 (fp64_negate
     (labSem_read_fp_reg d2 s)) s) /\
   (labSem_fp_upd (FPSqrt d1 d2) s =
      labSem_upd_fp_reg d1 (fp64_sqrt roundTiesToEven
        (labSem_read_fp_reg d2 s)) s) /\
   (labSem_fp_upd (FPAdd d1 d2 d3) s =
      labSem_upd_fp_reg d1
        (fp64_add roundTiesToEven (labSem_read_fp_reg d2 s)
          (labSem_read_fp_reg d3 s)) s) /\
   (labSem_fp_upd (FPSub d1 d2 d3) s =
      labSem_upd_fp_reg d1
        (fp64_sub roundTiesToEven (labSem_read_fp_reg d2 s)
          (labSem_read_fp_reg d3 s)) s) /\
   (labSem_fp_upd (FPMul d1 d2 d3) s =
      labSem_upd_fp_reg d1
        (fp64_mul roundTiesToEven (labSem_read_fp_reg d2 s)
          (labSem_read_fp_reg d3 s)) s) /\
   (labSem_fp_upd (FPDiv d1 d2 d3) s =
      labSem_upd_fp_reg d1
        (fp64_div roundTiesToEven (labSem_read_fp_reg d2 s)
          (labSem_read_fp_reg d3 s)) s) /\
   (labSem_fp_upd (FPFma d1 d2 d3) s =
      labSem_upd_fp_reg d1
        (fpfma (labSem_read_fp_reg d1 s) (labSem_read_fp_reg d2 s)
          (labSem_read_fp_reg d3 s)) s) /\
   (labSem_fp_upd (FPMovToReg r1 r2 d) s =
      (if dimindex (:'a) = 64 then
        labSem_upd_reg r1 (wordLang_Word (w2w (labSem_read_fp_reg d
          s))) s else let semanticPrimitives_v = labSem_read_fp_reg d s
          in
        labSem_upd_reg r2 (wordLang_Word ((63 >< 32)
          semanticPrimitives_v)) (labSem_upd_reg r1 (wordLang_Word ((31
          >< 0) semanticPrimitives_v)) s))) /\
   (labSem_fp_upd (FPMovFromReg d r1 r2) s =
      (if dimindex (:'a) = 64 then
        match (\r s. ?_regs s r) r1 s with
          wordLang_Word w1 -> labSem_upd_fp_reg d (w2w w1) s | _13 ->
            labSem_assert F s else
        match ((\r s. ?_regs s r) r1 s,(\r s. ?_regs s r) r2 s) with
          (wordLang_Word w1,wordLang_Word w2) -> labSem_upd_fp_reg d
            (w2 @@ w1) s | _14 -> labSem_assert F s)) /\
   (labSem_fp_upd (FPToInt d1 d2) s =
      (match fp64_to_int roundTiesToEven (labSem_read_fp_reg d2 s)
        with
          SOME i ->
            (let w = i2w i:word32 in
              (if dimindex (:'a) = 64 then
                 labSem_upd_fp_reg d1 (w2w w) else let (h,l) = if ODD
                   d1 then (63,32) else (31,0) in
                      labSem_upd_fp_reg (d1 DIV 2)
                        (bit_field_insert h l w (labSem_read_fp_reg
                          (d1 DIV 2) s)))
                 (labSem_assert (w2i w = i) s)) | _15 ->
                   labSem_assert F s)) /\
   (labSem_fp_upd (FPFromInt d1 d2) s =
      (let i = if dimindex (:'a) = 64 then
                w2i ((31 >< 0) (labSem_read_fp_reg d2 s):word32) else
                  let semanticPrimitives_v = labSem_read_fp_reg (d2 DIV
                  2) s in
                w2i (if ODD d2 then (63 >< 32) semanticPrimitives_v
                  else (31 >< 0) semanticPrimitives_v:'a word) in
        labSem_upd_fp_reg d1 (int_to_fp64 roundTiesToEven i) s))`;;

let addr_def = cake_define
  `labSem_addr (Addr r offset) s =
     (match (\r s. ?_regs s r) r s with wordLang_Word w -> SOME (w
       + offset) | _16 -> NONE)`;;

let is_Loc_def = cake_define
  `is_Loc x1 =
        match x1 with
          (semanticPrimitives_Loc _17 _18) -> T
        | _19 -> F`;;

let mem_store_def = cake_define
  `labSem_mem_store r a (s:('a,'c,'ffi)labSem_state) =
     (match labSem_addr a s with NONE -> labSem_assert F s | SOME w
       -> labSem_assert ((w2n w MOD (dimindex (:'a) DIV 8) = 0) /\
                         w IN ?_mem_domain s)
                   (labSem_upd_mem w ((\r s. ?_regs s r) r s) s))`;;

let mem_load_def = cake_define
  `labSem_mem_load r a (s:('a,'c,'ffi)labSem_state) =
     (match labSem_addr a s with NONE -> labSem_assert F s | SOME w
       -> labSem_assert ((w2n w MOD (dimindex (:'a) DIV 8) = 0) /\
                         w IN ?_mem_domain s)
                   (labSem_upd_reg r (?_mem s w) s))`;;

let mem_load32_def = cake_define
  `mem_load32 r a (s:('a,'c,'ffi)labSem_state) =
     (match labSem_addr a s with NONE -> labSem_assert F s | SOME w
       ->
         (match mem_load_32 (?_mem s) (?_mem_domain s) (?_be s) w
           with SOME semanticPrimitives_v -> labSem_upd_reg r
           (wordLang_Word (w2w semanticPrimitives_v)) s | NONE ->
           labSem_assert F s))`;;

let mem_store32_def = cake_define
  `mem_store32 r a (s:('a,'c,'ffi)labSem_state) =
     (match labSem_addr a s with NONE -> labSem_assert F s | SOME w
       ->
         (match (\r s. ?_regs s r) r s with wordLang_Word b ->
            (match mem_store_32 (?_mem s) (?_mem_domain s) (?_be
              s) w (w2w b) with SOME m -> (?_mem_fupd (K m) s) | NONE
              -> labSem_assert F s) | _20 -> labSem_assert F s))`;;

let mem_load_byte_def = cake_define
  `mem_load_byte r a (s:('a,'c,'ffi)labSem_state) =
     (match labSem_addr a s with NONE -> labSem_assert F s | SOME w
       ->
         (match mem_load_byte_aux (?_mem s) (?_mem_domain s) (?_be
           s) w with SOME semanticPrimitives_v -> labSem_upd_reg r
           (wordLang_Word (w2w semanticPrimitives_v)) s | NONE ->
           labSem_assert F s))`;;

let mem_store_byte_def = cake_define
  `mem_store_byte r a (s:('a,'c,'ffi)labSem_state) =
     (match labSem_addr a s with NONE -> labSem_assert F s | SOME w
       ->
         (match (\r s. ?_regs s r) r s with wordLang_Word b ->
            (match mem_store_byte_aux (?_mem s) (?_mem_domain s)
              (?_be s) w (w2w b) with SOME m -> (?_mem_fupd (K m) s)
              | NONE -> labSem_assert F s) | _21 -> labSem_assert F
              s))`;;

let mem_op_def = cake_define
  `(labSem_mem_op wordLang_Load r a = labSem_mem_load r a) /\
   (labSem_mem_op wordLang_Store r a = labSem_mem_store r a) /\
   (labSem_mem_op asm_Load32 r a = mem_load32 r a) /\
   (labSem_mem_op asm_Store32 r a = mem_store32 r a) /\
   (labSem_mem_op asm_Load8 r a = mem_load_byte r a) /\
   (labSem_mem_op asm_Store8 r a = mem_store_byte r a) /\
   (labSem_mem_op asm_Load16 r (a:'a labSem_addr) = labSem_assert F)
     /\
   (labSem_mem_op asm_Store16 r (a:'a labSem_addr) = labSem_assert
     F)`;;

let asm_inst_def = cake_define
  `(asm_inst wordLang_Skip s = (s:('a,'c,'ffi)labSem_state)) /\
   (asm_inst (wordLang_Const r imm) s = labSem_upd_reg r
     (wordLang_Word imm) s) /\
   (asm_inst (asm_Arith x) s = labSem_arith_upd x s) /\
   (asm_inst (asm_Mem m r a) s = labSem_mem_op m r a s) /\
   (asm_inst (asm_FP fp) s = labSem_fp_upd fp s)`;;

let dec_clock_def = cake_define
  `labSem_dec_clock s = ?_clock_fupd (K (?_clock s - 1)) s`;;

let inc_pc_def = cake_define
  `inc_pc s = ?_pc_fupd (K (?_pc s + 1)) s`;;

let asm_code_length_def = cake_define
  `(asm_code_length [] = 0) /\
   (asm_code_length ((Section k []) :: xs) = asm_code_length xs) /\
   (asm_code_length ((Section k (y :: ys)) :: xs) =
      asm_code_length ((Section k ys) :: xs) + (if is_Label y then
        0 else 1:num))`;;

let lab_to_loc_def = cake_define
  `lab_to_loc (labLang_Lab n1 n2) = semanticPrimitives_Loc n1 n2`;;

let loc_to_pc_def = cake_define
  `(loc_to_pc n1 n2 [] = NONE) /\
   (loc_to_pc n1 n2 ((Section k xs) :: ys) =
      (if (k = n1) /\ (n2 = 0) then SOME (0:num) else
        match xs with [] -> loc_to_pc n1 n2 ys | (z :: zs) ->
          (if (?k. z = labLang_Label n1 n2 k) /\ ~(n2 = 0) then SOME
            0 else
            if is_Label z then loc_to_pc n1 n2 ((Section k zs) :: ys)
              else
              match loc_to_pc n1 n2 ((Section k zs) :: ys) with
                NONE -> NONE | SOME pos -> SOME (pos + (1:num)))))`;;

let get_pc_value_def = cake_define
  `get_pc_value lab (s:('a,'c,'ffi)labSem_state) =
     (match lab with labLang_Lab n1 n2 -> loc_to_pc n1 n2 (?_code
       s))`;;

let next_label_def = cake_define
  `next_label x1 =
        match x1 with
          [] -> NONE
        | ((Section k []) :: xs) -> next_label xs
        | ((Section k (labLang_Label n1 n2 _22 :: ys)) :: xs) -> SOME
          (semanticPrimitives_Loc n1 n2)
        | ((Section k (y :: ys)) :: xs) -> next_label (Section k
          ys :: xs)`;;

let get_lab_after_def = cake_define
  `(get_lab_after pos [] = NONE) /\
   (get_lab_after pos ((Section k []) :: xs) = get_lab_after pos xs)
     /\
   (get_lab_after pos ((Section k (y :: ys)) :: xs) =
      (if is_Label y then get_lab_after pos ((Section k ys) :: xs)
        else if pos = (0:num) then next_label ((Section k ys) :: xs)
        else get_lab_after (pos - 1) ((Section k ys) :: xs)))`;;

let get_ret_Loc_def = cake_define
  `get_ret_Loc s = get_lab_after (?_pc s) (?_code s)`;;

let share_mem_load_def = cake_define
  `share_mem_load r ad (s:('a,'c,'ffi)labSem_state) n =
     (match labSem_addr ad s with NONE -> NONE | SOME
       semanticPrimitives_v ->
         (if (if n = 0 then (
                  w2n semanticPrimitives_v MOD (dimindex (:'a) DIV 8)
                    = 0 /\ (semanticPrimitives_v IN
                    labSem_state_shared_mem_domain s)) else byte_align
                    semanticPrimitives_v IN
                    labSem_state_shared_mem_domain s) then
           (match call_FFI (?_ffi s) (SharedMem MappedRead)
             [n2w n]
             (word_to_bytes semanticPrimitives_v F) with FFI_final
               outcome -> SOME (FFI_final outcome,s) | FFI_return
               new_ffi new_bytes ->
               SOME (FFI_return new_ffi new_bytes,?_clock_fupd (K
                 (?_clock s - 1)) (?_pc_fupd (K (?_pc s + 1))
                 (?_regs_fupd (K ((r =+ wordLang_Word (word_of_bytes F
                 (n2w 0) new_bytes)) (?_regs s))) (?_ffi_fupd (K
                 new_ffi)
                 s))))) else NONE))`;;

let share_mem_store_def = cake_define
  `share_mem_store r ad (s:('a,'c,'ffi)labSem_state) n =
     (match ?_regs s r with wordLang_Word w ->
       (match labSem_addr ad s with NONE -> NONE | SOME
         semanticPrimitives_v ->
         (if (if n = 0 then (
                  w2n semanticPrimitives_v MOD (dimindex (:'a) DIV 8)
                    = 0 /\ (semanticPrimitives_v IN
                    labSem_state_shared_mem_domain s)) else byte_align
                    semanticPrimitives_v IN
                    labSem_state_shared_mem_domain s) then
              (match call_FFI (?_ffi s) (SharedMem MappedWrite)
                [n2w n]
                ((if n = 0 then word_to_bytes w F else TAKE n
                  (word_to_bytes w F)) ++ (word_to_bytes
                  semanticPrimitives_v F)) with FFI_final outcome ->
                  SOME (FFI_final outcome,s) | FFI_return new_ffi
                  new_bytes ->
                  SOME ((FFI_return new_ffi new_bytes),
                    inc_pc (labSem_dec_clock (?_ffi_fupd (K
                      new_ffi) s)))) else NONE)) | _23 -> NONE)`;;

let share_mem_op_def = cake_define
  `(share_mem_op wordLang_Load r ad (s:('a,'c,'ffi)labSem_state) =
     share_mem_load r ad s 0) /\
   (share_mem_op asm_Load8 r ad s = share_mem_load r ad s 1) /\
   (share_mem_op asm_Load16 r ad s = share_mem_load r ad s 2) /\
   (share_mem_op wordLang_Store r ad s = share_mem_store r ad s 0) /\
   (share_mem_op asm_Store8 r ad s = share_mem_store r ad s 1) /\
   (share_mem_op asm_Store16 r ad s = share_mem_store r ad s 2) /\
   (share_mem_op asm_Load32 r ad s = share_mem_load r ad s 4) /\
   (share_mem_op asm_Store32 r ad s = share_mem_store r ad s 4)`;;

(* HOL4 termination: \\ fs [inc_pc_def] \\ rw [] \\ IMP_RES_TAC
   asm_fetch_IMP \\
   fs[asm_inst_consts,upd_reg_def,upd_pc_def,dec_clock_def,inc_pc_def]
   \\ Cases_on `m` \\
   fs[share_mem_op_def,share_mem_load_def,share_mem_store_def] \\
   gvs[AllCaseEqs(),inc_pc_def,dec_clock_def] *)
let evaluate_def = cake_define_wf
  `MEASURE (\s. ?_clock s)`
  `labSem_evaluate (s:('a,'c,'ffi)labSem_state) =
     (if ?_clock s = 0 then (targetSem_TimeOut,s) else
     match asm_fetch s with SOME (labLang_Asm (Asmi a) _24 _25) ->
         (match a with wordLang_Inst i ->
             (let s1 = asm_inst i s in
                if ?_failed s1 then (targetSem_Error,s) else
                  labSem_evaluate (inc_pc (labSem_dec_clock s1))) |
                  asm_JumpReg r ->
             (match (\r s. ?_regs s r) r s with
               semanticPrimitives_Loc n1 n2 ->
                  (match loc_to_pc n1 n2 (?_code s) with NONE ->
                    (targetSem_Error,s) | SOME p ->
                       labSem_evaluate (labSem_upd_pc p
                         (labSem_dec_clock s))) | _26 ->
                         (targetSem_Error,s)) | _27 ->
                         (targetSem_Error,s)) | SOME (labLang_Asm (Cbw
                         r1 r2) _28 _29) ->
       (match ((\r s. ?_regs s r) r1 s,(\r s. ?_regs s r) r2 s) with
         (wordLang_Word w1,wordLang_Word w2) ->
         (match buffer_write (?_code_buffer s) w1 (w2w w2) with SOME
           new_cb ->
           labSem_evaluate (inc_pc (labSem_dec_clock
             (?_code_buffer_fupd (K new_cb) s))) | _30 ->
             (targetSem_Error,s)) | _31 -> (targetSem_Error,s)) | SOME
             (labLang_Asm (ShareMem m r ad) _32 _33) ->
        (match share_mem_op m r ad s with SOME (FFI_final outcome,s')
          -> (targetSem_Halt (ffi_FFI_outcome outcome),s') | SOME
          (FFI_return _34 _35,s') ->
             labSem_evaluate (labSem_state_io_fp_regs_fupd (K
               (shift_seq 1 (labSem_state_io_fp_regs s')))
               (labSem_state_io_regs_fupd (K (shift_seq 1
               (labSem_state_io_regs s'))) s')) | NONE ->
               (targetSem_Error,s)) | SOME (labLang_LabAsm
               targetSem_Halt _36 _37 _38) ->
        (match ?_regs s (?_ptr_reg s) with wordLang_Word (n2w 0) ->
          (targetSem_Halt ffi_Success,s) | wordLang_Word _39 ->
          (targetSem_Halt ffi_Resource_limit_hit,s) | _40 ->
          (targetSem_Error,s)) | SOME (labLang_LabAsm (labLang_LocValue
          r lab) _41 _42 _43) ->
        (if get_pc_value lab s = NONE then (targetSem_Error,s) else
           let s1 = labSem_upd_reg r (lab_to_loc lab) s in
             labSem_evaluate (inc_pc (labSem_dec_clock s1))) | SOME
               (labLang_LabAsm (labLang_Jump l) _44 _45 _46) ->
        (match get_pc_value l s with NONE -> (targetSem_Error,s) |
          SOME p -> labSem_evaluate (labSem_upd_pc p (labSem_dec_clock
          s))) | SOME (labLang_LabAsm (labLang_JumpCmp c r ri l) _47 _48
          _49) ->
        (match wordSem_word_cmp c ((\r s. ?_regs s r) r s)
          (labSem_reg_imm ri s) with NONE -> (targetSem_Error,s) | SOME
          F -> labSem_evaluate (inc_pc (labSem_dec_clock s)) | SOME T ->
          (match get_pc_value l s with NONE -> (targetSem_Error,s) |
            SOME p -> labSem_evaluate (labSem_upd_pc p (labSem_dec_clock
            s)))) | SOME (labLang_LabAsm (labLang_Call l) _50 _51 _52)
            ->
        (match get_pc_value l s with NONE -> (targetSem_Error,s) |
          SOME p ->
          (match get_ret_Loc s with NONE -> (targetSem_Error,s) |
            SOME k ->
              (let s1 = labSem_upd_reg (?_link_reg s) k s in
                labSem_evaluate (labSem_upd_pc p (labSem_dec_clock
                  s1))))) | SOME (labLang_LabAsm labLang_Install _53 _54
                  _55) ->
        (match (?_regs s (?_ptr_reg s),?_regs s (?_len_reg s),?_regs
          s (?_link_reg s)) with (wordLang_Word w1,wordLang_Word
          w2,semanticPrimitives_Loc n1 n2) ->
            (match (buffer_flush (?_code_buffer s) w1 w2,loc_to_pc n1
              n2 (?_code s)) with (SOME (bytes,cb),SOME new_pc) ->
               (let (cfg,labLang_prog) = ?_compile_oracle s 0 in
               let new_oracle = shift_seq 1 (?_compile_oracle s) in
                 (match (?_compile s cfg labLang_prog,labLang_prog)
                   with (SOME (bytes',cfg'),Section k _56 :: _57) ->
                    (if bytes = bytes' /\ FST (new_oracle 0) = cfg'
                      then
                      labSem_evaluate
                        (?_clock_fupd (K (?_clock s - 1))
                          (?_compile_oracle_fupd (K new_oracle)
                          (?_fp_regs_fupd (K (\n.
                          labSem_state_cc_fp_regs s 0 n)) (?_regs_fupd
                          (K ((?_ptr_reg s =+ semanticPrimitives_Loc k
                          0)
                              (\a. get_reg_value
                                (labSem_state_cc_regs s 0 a)
                              (?_regs s a) wordLang_Word)))
                                (labSem_state_cc_fp_regs_fupd (K
                                (shift_seq 1 (labSem_state_cc_fp_regs
                                s))) (labSem_state_cc_regs_fupd (K
                                (shift_seq 1 (labSem_state_cc_regs s)))
                                (?_code_fupd (K (?_code s ++
                                labLang_prog)) (?_code_buffer_fupd (K
                                cb) (?_pc_fupd (K new_pc) s)))))))))
                                else
                      (targetSem_Error,s)) | _58 ->
                        (targetSem_Error,s))) | _59 ->
                        (targetSem_Error,s)) | _60 ->
                        (targetSem_Error,s)) | SOME (labLang_LabAsm
                        (labLang_CallFFI ffi_index) _61 _62 _63) ->
        (match (?_regs s (?_len_reg s),?_regs s (?_ptr_reg s),?_regs
               s (?_len2_reg s),?_regs s (?_ptr2_reg s),?_regs s
                 (?_link_reg s)) with (wordLang_Word w,wordLang_Word
                 w2,wordLang_Word w3,wordLang_Word
                 w4,semanticPrimitives_Loc n1 n2) ->
          (match (read_bytearray w2 (w2n w) (mem_load_byte_aux (?_mem
            s) (?_mem_domain s) (?_be s)),
                 read_bytearray w4 (w2n w3) (mem_load_byte_aux (?_mem
                   s) (?_mem_domain s) (?_be s)),
                 loc_to_pc n1 n2 (?_code s)) with (SOME bytes,SOME
                   bytes2,SOME new_pc) ->
              (match call_FFI (?_ffi s) (ExtCall ffi_index) bytes
                bytes2 with FFI_final outcome -> (targetSem_Halt
                (ffi_FFI_outcome outcome),s) | FFI_return new_ffi
                new_bytes ->
                   (let new_io_regs = shift_seq 1
                     (labSem_state_io_regs s) in
                   let new_io_fp_regs = shift_seq 1
                     (labSem_state_io_fp_regs s) in
                   let new_m = write_bytearray w4 new_bytes (?_mem s)
                     (?_mem_domain s) (?_be s) in
                     labSem_evaluate (?_clock_fupd (K (?_clock s -
                       1)) (?_pc_fupd (K new_pc) (?_fp_regs_fupd (K (\n.
                       labSem_state_io_fp_regs s 0 n)) (?_regs_fupd (K
                       (\a. get_reg_value (labSem_state_io_regs s 0
                       (ExtCall ffi_index) a)
                              (?_regs s a) wordLang_Word))
                                (labSem_state_io_fp_regs_fupd (K
                                new_io_fp_regs)
                                (labSem_state_io_regs_fupd (K
                                new_io_regs) (?_ffi_fupd (K new_ffi)
                                (?_mem_fupd (K new_m) s)))))))))) |
                                _64 -> (targetSem_Error,s)) | _65 ->
                                (targetSem_Error,s)) | _66 ->
                                (targetSem_Error,s))`;;

let semantics_def = cake_define
  `labSem_semantics s =
   (if ?k. FST (labSem_evaluate (?_clock_fupd (K k) s)) =
     targetSem_Error then ffi_Fail else
     match some (\res.
       ?k t outcome.
         labSem_evaluate (?_clock_fupd (K k) s) = (targetSem_Halt
           outcome,t) /\
         res = ffi_Terminate outcome (ffi_state_io_events (?_ffi t)))
           with SOME res -> res | NONE ->
       ffi_Diverge
          (build_lprefix_lub
            (IMAGE (\k. fromList (ffi_state_io_events (?_ffi (SND
              (labSem_evaluate (?_clock_fupd (K k) s)))))) UNIV)))`;;
