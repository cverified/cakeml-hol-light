(* ======================================================== *)
(*  asm: ported from HOL4's
    compiler/encoders/asm/asmScript.sml  *)
(* ======================================================== *)

(* ---------------------------------------------------------------------
   ----

   This script defines the syntax of a small general-purpose machine
   instruction description (without labels).

   The intention is that each instruction can be translated
   (i.e. encoded) into one instruction in real machine languages such
   as 32-bit ARM, 64-bit x86, MIPS etc.

 * A clean, simple and reusable instruction description language

   The language is full of compromises as it attempts to be both a
   clean target language for compiler backends and, at the same time,
   translate as naturally as possible into several different real
   machine languages.

   The language attempts to be clean and simple by having:
    - register names be natural numbers,
    - the machine word size be a variable throughout,
    - the memory be flat word -> byte mapping,
    - compare-and-jump instead of status flags, and
    - immediate constants fit a full machine word.

 * Target specific configuration

   In order to be able to map the abstract assembly instructions into
   real assembly, we also provide a target-specific configuration
   which can prune (from the syntax of assembly language) instructions
   which cannot be supported by the specific target machine
   language. The target-specific configuration can e.g.
    - disallow certain instructions,
    - limit the number of registers,
    - exclude special registers,
    - limit the size of immediate constants, offsets etc.
    - force arithmetic to only use two registers (e.g. xor r8,r9,r10
        cannot be translated to a single instruction in x86-64)

   This configuration is used by the compiler implementations to
   guide code generation into the appropriate target-specific subset
   of the assembly language.

 * Encode function, decode function or both?

   We had to decide how to define the semantics of an instruction
   execution. Normally, machine languages semantics are defined using
   decode functions. In our setting, the assembler/compiler needs an
   encode function. If the assembly language semantics was defined
   using a decode function, then we'd need a theorem roughly:

     !i. asm_ok i config ==> (decode (encode i) = i)

   But that's not generally true: the encode function might encode
   instructions to the same machine instruction, e.g. some
   architectures map "mov r0,r1" and "or r0,r1,r1" to the same
   instruction.  In order to keep things as simple as possible, we
   defined the semantics just in terms of an encode function.

 * Determinism

   The assembly language must be deterministic. The current definition
   of the semantics is relational but it only allows deterministic
     behaviour.

   ---------------------------------------------------------------------
     ---- *)

needs "lib/alignment.ml";;
needs "semantics/ast.ml";;
(* HOL4 ancestors outside the port: words *)

(* -- syntax of ASM instruction -- *)

new_type_abbrev("asm_reg",`: num`);;
new_type_abbrev("fp_reg",`: num`);;
(* HOL4 type abbreviation (expanded in the port):
     imm = 'a word *)

let asm_reg_imm_INDUCT,asm_reg_imm_RECURSION = define_datatype
  "asm_reg_imm = Reg (num) | Imm ('a word)";;

let binop_INDUCT,binop_RECURSION = define_datatype
  "binop = asm_Add | asm_Sub | asm_And | asm_Or | asm_Xor";;
hol4_overload "Add" "asm_Add";;
hol4_overload "Sub" "asm_Sub";;
hol4_overload "And" "asm_And";;
hol4_overload "Or" "asm_Or";;
hol4_overload "Xor" "asm_Xor";;

let cmp_INDUCT,cmp_RECURSION = define_datatype
  "cmp = asm_Equal | asm_Lower | asm_Less | asm_Test | asm_NotEqual | \
   asm_NotLower | asm_NotLess | asm_NotTest";;
hol4_overload "Equal" "asm_Equal";;
hol4_overload "Lower" "asm_Lower";;
hol4_overload "Less" "asm_Less";;
hol4_overload "Test" "asm_Test";;
hol4_overload "NotEqual" "asm_NotEqual";;
hol4_overload "NotLower" "asm_NotLower";;
hol4_overload "NotLess" "asm_NotLess";;
hol4_overload "NotTest" "asm_NotTest";;

let asm_arith_INDUCT,asm_arith_RECURSION = define_datatype
  "asm_arith = asm_Binop (binop) (num) (num) ('a asm_reg_imm) | \
   asm_Shift (ast_shift) (num) (num) ('a asm_reg_imm) | asm_Div (num) \
   (num) (num) | asm_LongMul (num) (num) (num) (num) | asm_LongDiv \
   (num) (num) (num) (num) (num) | asm_AddCarry (num) (num) (num) \
   (num) | asm_AddOverflow (num) (num) (num) (num) | asm_SubOverflow \
   (num) (num) (num) (num)";;
hol4_overload "Binop" "asm_Binop";;
hol4_overload "Shift" "asm_Shift";;
hol4_overload "Div" "asm_Div";;
hol4_overload "LongMul" "asm_LongMul";;
hol4_overload "LongDiv" "asm_LongDiv";;
hol4_overload "AddCarry" "asm_AddCarry";;
hol4_overload "AddOverflow" "asm_AddOverflow";;
hol4_overload "SubOverflow" "asm_SubOverflow";;

let fp_INDUCT,fp_RECURSION = define_datatype
  "fp = FPLess (num) (num) (num) | FPLessEqual (num) (num) (num) | \
   FPEqual (num) (num) (num) | FPAbs (num) (num) | FPNeg (num) (num) \
   | FPSqrt (num) (num) | FPAdd (num) (num) (num) | FPSub (num) (num) \
   (num) | FPMul (num) (num) (num) | FPDiv (num) (num) (num) | FPFma \
   (num) (num) (num) | FPMov (num) (num) | FPMovToReg (num) (num) \
   (num) | FPMovFromReg (num) (num) (num) | FPToInt (num) (num) | \
   FPFromInt (num) (num)";;

let asm_addr_INDUCT,asm_addr_RECURSION = define_datatype
  "asm_addr = Addr (num) ('a word)";;

let memop_INDUCT,memop_RECURSION = define_datatype
  "memop = asm_Load | asm_Load8 | asm_Load16 | asm_Load32 | asm_Store \
   | asm_Store8 | asm_Store16 | asm_Store32";;
hol4_overload "Load" "asm_Load";;
hol4_overload "Load8" "asm_Load8";;
hol4_overload "Load16" "asm_Load16";;
hol4_overload "Load32" "asm_Load32";;
hol4_overload "Store" "asm_Store";;
hol4_overload "Store8" "asm_Store8";;
hol4_overload "Store16" "asm_Store16";;
hol4_overload "Store32" "asm_Store32";;

let asm_inst_INDUCT,asm_inst_RECURSION = define_datatype
  "asm_inst = asm_Skip | asm_Const (num) ('a word) | asm_Arith ('a \
   asm_arith) | asm_Mem (memop) (num) ('a asm_addr) | asm_FP (fp)";;
hol4_overload "Skip" "asm_Skip";;
hol4_overload "Const" "asm_Const";;
hol4_overload "Arith" "asm_Arith";;
hol4_overload "Mem" "asm_Mem";;
hol4_overload "FP" "asm_FP";;

let asm_INDUCT,asm_RECURSION = define_datatype
  "asm = asm_Inst ('a asm_inst) | asm_Jump ('a word) | asm_JumpCmp \
   (cmp) (num) ('a asm_reg_imm) ('a word) | asm_Call ('a word) | \
   asm_JumpReg (num) | asm_Loc (num) ('a word)";;
hol4_overload "Inst" "asm_Inst";;
hol4_overload "Jump" "asm_Jump";;
hol4_overload "JumpCmp" "asm_JumpCmp";;
hol4_overload "Call" "asm_Call";;
hol4_overload "JumpReg" "asm_JumpReg";;
hol4_overload "Loc" "asm_Loc";;

(* -- ASM target-specific configuration -- *)

let architecture_INDUCT,architecture_RECURSION = define_datatype
  "architecture = ARMv7 | ARMv8 | MIPS | RISC_V | Ag32 | x86_64";;

let asm_config_FIELDS = define_record "asm_config"
  ["ISA","architecture";
   "encode","'a asm->word8 list";
   "big_endian","bool";
   "code_alignment","num";
   "link_reg","num option";
   "avoid_regs","num list";
   "reg_count","num";
   "fp_reg_count","num";
   "two_reg_arith","bool";
   "valid_imm","binop+cmp->'a word->bool";
   "addr_offset","'a word#'a word";
   "hw_offset","'a word#'a word";
   "byte_offset","'a word#'a word";
   "jump_offset","'a word#'a word";
   "cjump_offset","'a word#'a word";
   "loc_offset","'a word#'a word"];;
hol4_overload "link_reg" "asm_config_link_reg";;
hol4_overload "link_reg_fupd" "asm_config_link_reg_fupd";;

let reg_ok_def = cake_define
  `reg_ok r c <=> r < asm_config_reg_count c /\ ~MEM r
  (asm_config_avoid_regs c)`;;

let fp_reg_ok_def = cake_define
  `fp_reg_ok d c <=> d < asm_config_fp_reg_count c`;;

let reg_imm_ok_def = cake_define_list
  [`reg_imm_ok b (Reg r) c = reg_ok r c`;
   `reg_imm_ok b (Imm w) c =
         ((b = INL Xor) /\ (w = --(n2w 1)) \/
           asm_config_valid_imm c b w)`];;


(* Requires register inequality for some architectures *)
let arith_ok_def = cake_define_list
  [`arith_ok (asm_Binop b r1 r2 ri) (c:'a asm_config) <=>
         (asm_config_two_reg_arith c ==> (r1 = r2) \/ (b = Or) /\
           (ri = Reg r2)) /\
         reg_ok r1 c /\ reg_ok r2 c /\ reg_imm_ok (INL b) ri c`;
   `arith_ok (asm_Shift l r1 r2 ri) (c:'a asm_config) <=>
         (asm_config_two_reg_arith c ==> (r1 = r2)) /\
         reg_ok r1 c /\ reg_ok r2 c /\
         (match ri with Imm i -> (((i = (n2w 0)) ==> (l = Lsl)) /\
           w2n i < dimindex (:'a)) | Reg r ->
            reg_ok r c /\
            (asm_config_ISA c = x86_64 ==> r = 1))`;
   `arith_ok (asm_Div r1 r2 r3) (c:'a asm_config) <=>
         reg_ok r1 c /\ reg_ok r2 c /\ reg_ok r3 c /\ asm_config_ISA
         c IN {ARMv8,MIPS,RISC_V}`;
   `arith_ok (asm_LongMul r1 r2 r3 r4) (c:'a asm_config) <=>
         reg_ok r1 c /\ reg_ok r2 c /\ reg_ok r3 c /\ reg_ok r4 c /\
         ((asm_config_ISA c = x86_64) ==> (r1 = 2) /\ (r2 = 0) /\
           (r3 = 0)) /\
         ((asm_config_ISA c = ARMv7) ==> ~(r1 = r2)) /\
         (asm_config_ISA c IN {ARMv8,RISC_V,Ag32} ==> ~(r1 = r3)
           /\ ~(r1 = r4))`;
   `arith_ok (asm_LongDiv r1 r2 r3 r4 r5) (c:'a asm_config) <=>
         (asm_config_ISA c = x86_64) /\ (r1 = 0) /\ (r2 = 2) /\ (r3
           = 2) /\ (r4 = 0) /\
         reg_ok r5 c`;
   `arith_ok (asm_AddCarry r1 r2 r3 r4) (c:'a asm_config) <=>
         (asm_config_two_reg_arith c ==> (r1 = r2)) /\
         reg_ok r1 c /\ reg_ok r2 c /\ reg_ok r3 c /\ reg_ok r4 c /\
         (((asm_config_ISA c = MIPS) \/ (asm_config_ISA c =
           RISC_V)) ==> ~(r1 = r3) /\ ~(r1 = r4))`;
   `arith_ok (asm_AddOverflow r1 r2 r3 r4) (c:'a asm_config) <=>
         (asm_config_two_reg_arith c ==> (r1 = r2)) /\
         reg_ok r1 c /\ reg_ok r2 c /\ reg_ok r3 c /\ reg_ok r4 c /\
         (((asm_config_ISA c = MIPS) \/ (asm_config_ISA c =
           RISC_V)) ==> ~(r1 = r3))`;
   `arith_ok (asm_SubOverflow r1 r2 r3 r4) (c:'a asm_config) <=>
         (asm_config_two_reg_arith c ==> (r1 = r2)) /\
         reg_ok r1 c /\ reg_ok r2 c /\ reg_ok r3 c /\ reg_ok r4 c /\
         (((asm_config_ISA c = MIPS) \/ (asm_config_ISA c =
           RISC_V)) ==> ~(r1 = r3))`];;

let fp_ok_def = cake_define_list
  [`fp_ok (FPLess r d1 d2) (c:'a asm_config) <=>
          reg_ok r c /\ fp_reg_ok d1 c /\ fp_reg_ok d2 c`;
   `fp_ok (FPLessEqual r d1 d2) (c:'a asm_config) <=>
          reg_ok r c /\ fp_reg_ok d1 c /\ fp_reg_ok d2 c`;
   `fp_ok (FPEqual r d1 d2) (c:'a asm_config) <=>
          reg_ok r c /\ fp_reg_ok d1 c /\ fp_reg_ok d2 c`;
   `fp_ok (FPAbs d1 d2) (c:'a asm_config) <=>
          (asm_config_two_reg_arith c ==> (~(d1 = d2))) /\
            fp_reg_ok d1 c /\ fp_reg_ok d2 c`;
   `fp_ok (FPNeg d1 d2) (c:'a asm_config) <=>
          (asm_config_two_reg_arith c ==> (~(d1 = d2))) /\
            fp_reg_ok d1 c /\ fp_reg_ok d2 c`;
   `fp_ok (FPSqrt d1 d2) (c:'a asm_config) <=> fp_reg_ok d1 c /\
  fp_reg_ok d2 c`;
   `fp_ok (FPAdd d1 d2 d3) (c:'a asm_config) <=>
          (asm_config_two_reg_arith c ==> (d1 = d2)) /\
          fp_reg_ok d1 c /\ fp_reg_ok d2 c /\ fp_reg_ok d3 c`;
   `fp_ok (FPSub d1 d2 d3) (c:'a asm_config) <=>
          (asm_config_two_reg_arith c ==> (d1 = d2)) /\
          fp_reg_ok d1 c /\ fp_reg_ok d2 c /\ fp_reg_ok d3 c`;
   `fp_ok (FPMul d1 d2 d3) (c:'a asm_config) <=>
          (asm_config_two_reg_arith c ==> (d1 = d2)) /\
          fp_reg_ok d1 c /\ fp_reg_ok d2 c /\ fp_reg_ok d3 c`;
   `fp_ok (FPDiv d1 d2 d3) (c:'a asm_config) <=>
          (asm_config_two_reg_arith c ==> (d1 = d2)) /\
          fp_reg_ok d1 c /\ fp_reg_ok d2 c /\ fp_reg_ok d3 c`;
   `fp_ok (FPFma d1 d2 d3) (c:'a asm_config) <=>
          (asm_config_ISA c = ARMv7) /\
          2 < asm_config_fp_reg_count c /\
          fp_reg_ok d1 c /\ fp_reg_ok d2 c /\ fp_reg_ok d3 c`;
   `fp_ok (FPMov d1 d2) (c:'a asm_config) <=> fp_reg_ok d1 c /\
  fp_reg_ok d2 c`;
   `fp_ok (FPMovToReg r1 r2 d) (c:'a asm_config) <=>
          reg_ok r1 c /\ ((dimindex (:'a) = 32) ==> ~(r1 = r2) /\
            reg_ok r2 c) /\
          fp_reg_ok d c`;
   `fp_ok (FPMovFromReg d r1 r2) (c:'a asm_config) <=>
          reg_ok r1 c /\ ((dimindex (:'a) = 32) ==> ~(r1 = r2) /\
            reg_ok r2 c) /\
          fp_reg_ok d c`;
   `fp_ok (FPToInt r d) (c:'a asm_config) <=> fp_reg_ok r c /\
  fp_reg_ok d c`;
   `fp_ok (FPFromInt d r) (c:'a asm_config) <=> fp_reg_ok r c /\
  fp_reg_ok d c`];;

let cmp_ok_def = cake_define
  `cmp_ok (cmp:cmp) r ri c <=> reg_ok r c /\ reg_imm_ok (INR cmp) ri
  c`;;

let offset_ok_def = cake_define
  `asm_offset_ok a offset w =
   (let (min',max') = offset in min' <= w /\ w <= max' /\
     alignment_aligned a w)`;;
hol4_overload "offset_ok" "asm_offset_ok";;

(* HOL4 overload (expanded in the port):
     addr_offset_ok = λc. offset_ok 0 c.addr_offset *)
(* HOL4 overload (expanded in the port):
     hw_offset_ok = λc. offset_ok 0 c.hw_offset *)
(* HOL4 overload (expanded in the port):
     byte_offset_ok = λc. offset_ok 0 c.byte_offset *)
(* HOL4 overload (expanded in the port):
     jump_offset_ok = λc. offset_ok c.code_alignment c.jump_offset *)
(* HOL4 overload (expanded in the port):
     cjump_offset_ok = λc. offset_ok c.code_alignment c.cjump_offset *)
(* HOL4 overload (expanded in the port):
     loc_offset_ok = λc. offset_ok c.code_alignment c.loc_offset *)

let inst_ok_def = cake_define
  `inst_ok x1 c =
        match x1 with
          asm_Skip -> T
        | (asm_Const r w) -> reg_ok r c
        | (Arith x) -> arith_ok x c
        | (asm_FP x) -> fp_ok x c
        | (asm_Mem m r1 (Addr r2 w):'a asm_inst) ->
        reg_ok r1 c /\ reg_ok r2 c /\
        (if m IN {asm_Load,asm_Store,asm_Load32,asm_Store32} then
           (\c. asm_offset_ok 0 (asm_config_addr_offset c)) c w else
             if m IN {asm_Load16,asm_Store16} then
           (\c. asm_offset_ok 0 (asm_config_hw_offset c)) c w /\
             ~(asm_config_ISA c = Ag32) else
           (\c. asm_offset_ok 0 (asm_config_byte_offset c)) c w)`;;

let asm_ok_def = cake_define_list
  [`asm_ok (asm_Inst i) c <=> inst_ok i c`;
   `asm_ok (asm_Jump w) c <=> (\c. asm_offset_ok
  (asm_config_code_alignment c) (asm_config_jump_offset c)) c w`;
   `asm_ok (asm_JumpCmp cmp r ri w) c <=>
         (\c. asm_offset_ok (asm_config_code_alignment c)
           (asm_config_cjump_offset c)) c w /\ cmp_ok cmp r ri c`;
   `asm_ok (asm_Call w) c <=>
         (match asm_config_link_reg c with SOME r -> reg_ok r c |
           NONE -> F) /\
         (\c. asm_offset_ok (asm_config_code_alignment c)
           (asm_config_jump_offset c)) c w`;
   `asm_ok (asm_JumpReg r) c <=> reg_ok r c`;
   `asm_ok (asm_Loc r w) c <=> reg_ok r c /\ (\c. asm_offset_ok
  (asm_config_code_alignment c) (asm_config_loc_offset c)) c w`];;

let word_cmp_def = cake_define_list
  [`asm_word_cmp (Equal:cmp) w1 w2 = (w1 = w2)`;
   `asm_word_cmp (Less:cmp) w1 w2 = (w1 < w2)`;
   `asm_word_cmp asm_Lower w1 w2 = (w1 <+ w2)`;
   `asm_word_cmp (Test:cmp) w1 w2 = ((w1 && w2) = (n2w 0))`;
   `asm_word_cmp asm_NotEqual w1 w2 = (~(w1 = w2))`;
   `asm_word_cmp asm_NotLess w1 w2 = ~(w1 < w2)`;
   `asm_word_cmp asm_NotLower w1 w2 = ~(w1 <+ w2)`;
   `asm_word_cmp asm_NotTest w1 w2 = (~((w1 && w2) = (n2w 0)))`];;
hol4_overload "word_cmp" "asm_word_cmp";;

let is_load_def = cake_define
  `is_load x1 =
        match x1 with
          (asm_Load:memop) -> T
        | asm_Load8 -> T
        | asm_Load16 -> T
        | asm_Load32 -> T
        | _1 -> F`;;
