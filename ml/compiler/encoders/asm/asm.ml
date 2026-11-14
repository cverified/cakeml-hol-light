(* ======================================================== *)
(*  asm: ported from HOL4's
    compiler/encoders/asm/asmScript.sml
    A definition theory, with 11 definitions, 11 datatypes and no
    theorems.  Needed by 55 files of the port.  *)
(* ======================================================== *)

(* -------------------------------------------------------------------------

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
   of the semantics is relational but it only allows deterministic behaviour.

   ------------------------------------------------------------------------- *)

needs "lib/alignment.ml";;
needs "semantics/ast.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "asm"
  ["ast"];;
(* HOL4 ancestors outside the port: words *)

(* -- syntax of ASM instruction -- *)

new_type_abbrev("asm_reg",`:num`);;
new_type_abbrev("fp_reg",`:num`);;
(* HOL4 asmScript.sml:72: the type abbreviation imm, which the port
   expands *)

let asm_reg_imm_INDUCT,asm_reg_imm_RECURSION = define_datatype
  "asm_reg_imm =
     Reg asm_reg
   | Imm ('a word)";;

let binop_INDUCT,binop_RECURSION = define_datatype
  "binop =
     asm_Add
   | asm_Sub
   | asm_And
   | asm_Or
   | asm_Xor";;

let cmp_INDUCT,cmp_RECURSION = define_datatype
  "cmp =
     asm_Equal
   | asm_Lower
   | asm_Less
   | asm_Test
   | asm_NotEqual
   | asm_NotLower
   | asm_NotLess
   | asm_NotTest";;

let asm_arith_INDUCT,asm_arith_RECURSION = define_datatype
  "asm_arith =
     asm_Binop binop asm_reg asm_reg ('a asm_reg_imm)
   | asm_Shift ast_shift asm_reg asm_reg ('a asm_reg_imm)
   | asm_Div asm_reg asm_reg asm_reg
   | asm_LongMul asm_reg asm_reg asm_reg asm_reg
   | asm_LongDiv asm_reg asm_reg asm_reg asm_reg asm_reg
   | asm_AddCarry asm_reg asm_reg asm_reg asm_reg
   | asm_AddOverflow asm_reg asm_reg asm_reg asm_reg
   | asm_SubOverflow asm_reg asm_reg asm_reg asm_reg";;

let fp_INDUCT,fp_RECURSION = define_datatype
  "fp =
     // orderings
     FPLess asm_reg fp_reg fp_reg
   | FPLessEqual asm_reg fp_reg fp_reg
   | FPEqual asm_reg fp_reg fp_reg
     // unary ops
   | FPAbs fp_reg fp_reg
     // IEEE754:2008
   | FPNeg fp_reg fp_reg
     // IEEE754:2008
   | FPSqrt fp_reg fp_reg
     // binary ops
   | FPAdd fp_reg fp_reg fp_reg
   | FPSub fp_reg fp_reg fp_reg
   | FPMul fp_reg fp_reg fp_reg
   | FPDiv fp_reg fp_reg fp_reg
     // Ternary ops
   | FPFma fp_reg fp_reg fp_reg
     // moves and converts
   | FPMov fp_reg fp_reg
   | FPMovToReg asm_reg asm_reg fp_reg
   | FPMovFromReg fp_reg asm_reg asm_reg
   | FPToInt fp_reg fp_reg
   | FPFromInt fp_reg fp_reg";;

let asm_addr_INDUCT,asm_addr_RECURSION = define_datatype
  "asm_addr =
     Addr asm_reg ('a word)";;

let memop_INDUCT,memop_RECURSION = define_datatype
  "memop =
     asm_Load
   | asm_Load8
   | asm_Load16
   | asm_Load32
   | asm_Store
   | asm_Store8
   | asm_Store16
   | asm_Store32";;

let asm_inst_INDUCT,asm_inst_RECURSION = define_datatype
  "asm_inst =
     asm_Skip
   | asm_Const asm_reg ('a word)
   | asm_Arith ('a asm_arith)
   | asm_Mem memop asm_reg ('a asm_addr)
   | asm_FP fp";;

let asm_INDUCT,asm_RECURSION = define_datatype
  "asm =
     asm_Inst ('a asm_inst)
   | asm_Jump ('a word)
   | asm_JumpCmp cmp asm_reg ('a asm_reg_imm) ('a word)
   | asm_Call ('a word)
   | asm_JumpReg asm_reg
   | asm_Loc asm_reg ('a word)";;

(* -- ASM target-specific configuration -- *)

let architecture_INDUCT,architecture_RECURSION = define_datatype
  "architecture =
     ARMv7
   | ARMv8
   | MIPS
   | RISC_V
   | Ag32
   | x86_64";;

let asm_config_FIELDS = define_record "asm_config"
  ["ISA","architecture";
   "encode","'a asm->word8 list";
   "big_endian","bool";
   "code_alignment","num";
   "link_reg","num option";
   "avoid_regs","num list";
   "reg_count","num";
   "fp_reg_count","num";
   (* set to 0 if float not available *)
   "two_reg_arith","bool";
   "valid_imm","binop+cmp->'a word->bool";
   "addr_offset","'a word#'a word";
   "hw_offset","'a word#'a word";
   "byte_offset","'a word#'a word";
   "jump_offset","'a word#'a word";
   "cjump_offset","'a word#'a word";
   "loc_offset","'a word#'a word"];;

let reg_ok_def = new_definition
  `reg_ok r c <=> r < asm_config_reg_count c /\ ~(MEM r
  (asm_config_avoid_regs c))`;;

let fp_reg_ok_def = new_definition
  `fp_reg_ok d c <=> d < asm_config_fp_reg_count c`;;

let reg_imm_ok_def = define_cases
  [`reg_imm_ok b (Reg r) c = reg_ok r c`;
   `reg_imm_ok b (Imm w) c =
         ((
           // Always permit Xor by -1 in order to provide 1's complement
           b = INL asm_Xor) /\ (w = --(n2w 1)) \/
               asm_config_valid_imm c b w)`];;


(* Requires register inequality for some architectures *)
let arith_ok_def = define_cases
  [`arith_ok (asm_Binop b r1 r2 ri) (c:'a asm_config) <=>
         (asm_config_two_reg_arith
          // note: register to register moves can be implmented with
          // "Or" on "two_reg_arith" architectures.
          c ==> (r1 = r2) \/ (b = asm_Or) /\ (ri = Reg r2)) /\
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

let fp_ok_def = define_cases
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

let cmp_ok_def = new_definition
  `cmp_ok (cmp:cmp) r ri c <=> reg_ok r c /\ reg_imm_ok (INR cmp) ri
  c`;;

let offset_ok_def = new_definition
  `asm_offset_ok a offset w =
   (let (min',max') = offset in min' <= w /\ w <= max' /\
     alignment_aligned a w)`;;

(* HOL4 asmScript.sml:279: the overload addr_offset_ok, which the
   port expands *)
(* HOL4 asmScript.sml:280: the overload hw_offset_ok, which the port
   expands *)
(* HOL4 asmScript.sml:281: the overload byte_offset_ok, which the
   port expands *)
(* HOL4 asmScript.sml:282: the overload jump_offset_ok, which the
   port expands *)
(* HOL4 asmScript.sml:283: the overload cjump_offset_ok, which the
   port expands *)
(* HOL4 asmScript.sml:284: the overload loc_offset_ok, which the port
   expands *)

let inst_ok_def = new_definition
  `inst_ok x1 c =
        match x1 with
          asm_Skip -> T
        | (asm_Const r w) -> reg_ok r c
        | (asm_Arith x) -> arith_ok x c
        | (asm_FP x) -> fp_ok x c
        | (asm_Mem m r1 (Addr r2 w):'a asm_inst) ->
        reg_ok r1 c /\ reg_ok r2 c /\
        (if m IN {asm_Load,asm_Store,asm_Load32,asm_Store32} then
           (\c. asm_offset_ok 0 (asm_config_addr_offset c)) c w else
             if m IN {asm_Load16,asm_Store16} then
           (\c. asm_offset_ok 0 (asm_config_hw_offset c)) c w /\
             ~(asm_config_ISA c = Ag32) else
           (\c. asm_offset_ok 0 (asm_config_byte_offset c)) c w)`;;

let asm_ok_def = define_cases
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

let word_cmp_def = define_cases
  [`(asm_word_cmp (asm_Equal:cmp) w1 w2 = (w1 = w2)) /\
   (asm_word_cmp asm_Less w1 w2 = (w1 < w2)) /\
   (asm_word_cmp asm_Lower w1 w2 = (w1 <+ w2)) /\
   (asm_word_cmp asm_Test w1 w2 = ((w1 && w2) = (n2w 0))) /\
   (asm_word_cmp asm_NotEqual w1 w2 = (~(w1 = w2))) /\
   (asm_word_cmp asm_NotLess w1 w2 = ~(w1 < w2)) /\
   (asm_word_cmp asm_NotLower w1 w2 = ~(w1 <+ w2)) /\
   (asm_word_cmp asm_NotTest w1 w2 = (~((w1 && w2) = (n2w 0))))`];;

let is_load_def = new_definition
  `is_load x1 =
        match x1 with
          (asm_Load:memop) -> T
        | asm_Load8 -> T
        | asm_Load16 -> T
        | asm_Load32 -> T
        | _1 -> F`;;
add_simp is_load_def;;

(* and the interface *)
let _ = unhide_overloads ();;
