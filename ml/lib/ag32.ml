(* ==================================================================== *)
(*  ag32: the Silver instruction set.                                   *)
(*                                                                      *)
(*  HOL4's compiler/encoders/ag32/ag32Script.sml is a file that L3       *)
(*  generated: it builds its types and its 29 definitions by calling    *)
(*  the ML of HOL4's Import library, which a source level port cannot   *)
(*  follow, so the theory is outside the port (tools/excluded.txt).     *)
(*                                                                      *)
(*  Seven files of the load order use the model all the same -- the     *)
(*  memory layout of the Silver machine and the proofs about it -- and  *)
(*  what they use of it is data and four names.  This is that much of   *)
(*  it: the four datatypes (ag32Script.sml:6-38), the record of the     *)
(*  machine state (:40-45), and Encode, Decode, Run and Next, whose     *)
(*  value is the generated ML and which are declared without one, as    *)
(*  the encoders of the six targets are (PENDING.md).                   *)
(*                                                                      *)
(*  The names are the ones tools/overrides.py gives the theory          *)
(*  (EXTRA_DATATYPES, EXTRA_RECORDS, EXTRA_DEFS), so that what the      *)
(*  port writes and what this file makes are the same constants.        *)
(* ==================================================================== *)

let funcT_INDUCT,funcT_RECURSION = define_datatype
  "funcT =
     fAdd
   | fAddWithCarry
   | fSub
   | fCarry
   | fOverflow
   | fInc
   | fDec
   | fMul
   | fMulHU
   | fAnd
   | fOr
   | fXor
   | fEqual
   | fLess
   | fLower
   | fSnd";;

let shiftT_INDUCT,shiftT_RECURSION = define_datatype
  "shiftT =
     shiftLL
   | shiftLR
   | shiftAR
   | shiftRor";;

let reg_immT_INDUCT,reg_immT_RECURSION = define_datatype
  "reg_immT =
     ag32_Imm ((6)word)
   | ag32_Reg ((6)word)";;

(* every constructor of the instructions takes one tuple, as L3
   makes them *)

let instruction_INDUCT,instruction_RECURSION = define_datatype
  "instruction =
     ag32_Accelerator ((6)word#reg_immT)
   | ag32_In ((6)word)
   | ag32_Interrupt
   | ag32_Jump (funcT#(6)word#reg_immT)
   | ag32_JumpIfNotZero (funcT#reg_immT#reg_immT#reg_immT)
   | ag32_JumpIfZero (funcT#reg_immT#reg_immT#reg_immT)
   | ag32_LoadConstant ((6)word#bool#(23)word)
   | ag32_LoadMEM ((6)word#reg_immT)
   | ag32_LoadMEMByte ((6)word#reg_immT)
   | ag32_LoadUpperConstant ((6)word#(9)word)
   | ag32_Normal (funcT#(6)word#reg_immT#reg_immT)
   | ag32_Out (funcT#(6)word#reg_immT#reg_immT)
   | ag32_ReservedInstr
   | ag32_Shift (shiftT#(6)word#reg_immT#reg_immT)
   | ag32_StoreMEM (reg_immT#reg_immT)
   | ag32_StoreMEMByte (reg_immT#reg_immT)";;

let ag32_state_FIELDS = define_record "ag32_state"
  ["CarryFlag","bool";
   "MEM","(32)word->(8)word";
   "OverflowFlag","bool";
   "PC","(32)word";
   "R","(6)word->(32)word";
   "data_in","(2)word";
   "data_out","(10)word";
   "io_events","((32)word->(8)word)list"];;

(* the four functions of the model that the sources of the port
   name.  Their value is the ML that L3 generated, which the port
   does not have, so they are declared and not defined -- four
   constants with no value, as PENDING.md counts them *)

(* the step function of each instruction, which the proofs of the
   memory layout state a theorem about.  Each takes the arguments
   of its constructor as one tuple and the state, and gives the
   state (ag32Script.sml:147-511) *)

cake_declare "dfn'Accelerator"
  `:((6)word#reg_immT)->ag32_state->ag32_state`;;

cake_declare "dfn'In" `:(6)word->ag32_state->ag32_state`;;

cake_declare "dfn'Interrupt" `:ag32_state->ag32_state`;;

cake_declare "dfn'Jump"
  `:(funcT#(6)word#reg_immT)->ag32_state->ag32_state`;;

cake_declare "dfn'JumpIfNotZero"
  `:(funcT#reg_immT#reg_immT#reg_immT)->ag32_state->ag32_state`;;

cake_declare "dfn'JumpIfZero"
  `:(funcT#reg_immT#reg_immT#reg_immT)->ag32_state->ag32_state`;;

cake_declare "dfn'LoadConstant"
  `:((6)word#bool#(23)word)->ag32_state->ag32_state`;;

cake_declare "dfn'LoadMEM"
  `:((6)word#reg_immT)->ag32_state->ag32_state`;;

cake_declare "dfn'LoadMEMByte"
  `:((6)word#reg_immT)->ag32_state->ag32_state`;;

cake_declare "dfn'LoadUpperConstant"
  `:((6)word#(9)word)->ag32_state->ag32_state`;;

cake_declare "dfn'Normal"
  `:(funcT#(6)word#reg_immT#reg_immT)->ag32_state->ag32_state`;;

cake_declare "dfn'Out"
  `:(funcT#(6)word#reg_immT#reg_immT)->ag32_state->ag32_state`;;

cake_declare "dfn'Shift"
  `:(shiftT#(6)word#reg_immT#reg_immT)->ag32_state->ag32_state`;;

cake_declare "dfn'StoreMEM"
  `:(reg_immT#reg_immT)->ag32_state->ag32_state`;;

cake_declare "dfn'StoreMEMByte"
  `:(reg_immT#reg_immT)->ag32_state->ag32_state`;;

(* and the four that read or run a whole instruction *)

cake_declare "Encode" `:instruction->(32)word`;;

cake_declare "Decode" `:(32)word->instruction`;;

cake_declare "Run" `:instruction->ag32_state->ag32_state`;;

cake_declare "Next" `:ag32_state->ag32_state`;;
