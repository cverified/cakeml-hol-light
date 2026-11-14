(* ======================================================== *)
(*  labLang: ported from HOL4's
    compiler/backend/labLangScript.sml
    A definition theory, with 2 definitions, 5 datatypes and no
    theorems.  Needed by 13 files of the port.  *)
(* ======================================================== *)

(*
  The labLang intermediate language is a target-neutral assembly
  language at the bottom end of the compiler backend.
*)

needs "compiler/encoders/asm/asm.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "labLang"
  ["asm"];;

new_type_abbrev("labLang_reg",`:num`);;

(* A label refers to either a section name or a local label definition
   within the current section. *)

let lab_INDUCT,lab_RECURSION = define_datatype
  "lab =
     labLang_Lab num num";;

(* Each line of a section consists of either a label, an assembly
   instruction (without a label) or some labelled asm instruction. *)

let asm_with_lab_INDUCT,asm_with_lab_RECURSION = define_datatype
  "asm_with_lab =
     labLang_Jump lab
   | labLang_JumpCmp cmp labLang_reg ('a asm_reg_imm) lab
   | labLang_Call lab
   | labLang_LocValue labLang_reg lab
     // following have no label, but have similar semantics
   | labLang_CallFFI mlstring
   | labLang_Install
   | labLang_Halt";;

let asm_or_cbw_INDUCT,asm_or_cbw_RECURSION = define_datatype
  "asm_or_cbw =
     Asmi ('a asm)
   | Cbw labLang_reg labLang_reg
   | ShareMem memop labLang_reg ('a asm_addr)";;
 (* Either an asm inst/jumpreg or code-buffer-write *)

let line_INDUCT,line_RECURSION = define_datatype
  "line =
     labLang_Label num num num
     // section number, label number, length
   | labLang_Asm ('a asm_or_cbw) (word8 list) num
     // instruction, encoded instruction, length
   | labLang_LabAsm ('a asm_with_lab) ('a word) (word8 list) num";;
                                  (* position, encoded instruction, length *)

(* A section consists a name (num) and a list of assembly lines. *)

let sec_INDUCT,sec_RECURSION = define_datatype
  "sec =
     Section num (('a line) list)";;

let section_num_def = define_general
  [`Section_num (Section k _1) = k`];;
add_simp section_num_def;;
let section_lines_def = define_general
  [`Section_lines (Section _2 lines) = lines`];;
add_simp section_lines_def;;

(* A full assembly program consists of a list of sections. *)

(* HOL4 labLangScript.sml:61: the type abbreviation prog, which the
   port expands *)
