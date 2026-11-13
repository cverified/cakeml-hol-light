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

(* the theories whose names the Ancestors blocks of the source
   bring, which are the ones that its statements read: the
   overloads of every other theory come out of the interface
   while this file loads *)
let _ = hol4_ancestors "labLang"
  ["asm"];;

new_type_abbrev("labLang_reg",`: num`);;

(* A label refers to either a section name or a local label definition
   within the current section. *)

let lab_INDUCT,lab_RECURSION = define_datatype
  "lab = labLang_Lab (num) (num)";;
hol4_overload "Lab" "labLang_Lab";;

(* Each line of a section consists of either a label, an assembly
   instruction (without a label) or some labelled asm instruction. *)

let asm_with_lab_INDUCT,asm_with_lab_RECURSION = define_datatype
  "asm_with_lab = labLang_Jump (lab) | labLang_JumpCmp (cmp) (num) \
   ('a asm_reg_imm) (lab) | labLang_Call (lab) | labLang_LocValue \
   (num) (lab) | \
   // following have no label, but have similar semantics\n\
   labLang_CallFFI (mlstring) | labLang_Install | labLang_Halt";;
hol4_overload "Jump" "labLang_Jump";;
hol4_overload "JumpCmp" "labLang_JumpCmp";;
hol4_overload "Call" "labLang_Call";;
hol4_overload "LocValue" "labLang_LocValue";;
hol4_overload "CallFFI" "labLang_CallFFI";;
hol4_overload "Install" "labLang_Install";;
hol4_overload "Halt" "labLang_Halt";;

let asm_or_cbw_INDUCT,asm_or_cbw_RECURSION = define_datatype
  "asm_or_cbw = Asmi ('a asm) | Cbw (num) (num) | ShareMem (memop) \
   (num) ('a asm_addr)";;
 (* Either an asm inst/jumpreg or code-buffer-write *)

let line_INDUCT,line_RECURSION = define_datatype
  "line = labLang_Label (num) (num) (num) \
   // section number, label number, length\n\
   | labLang_Asm ('a asm_or_cbw) (word8 list) (num) \
   // instruction, encoded instruction, length\n\
   | labLang_LabAsm ('a asm_with_lab) ('a word) (word8 list) (num)";;
hol4_overload "Label" "labLang_Label";;
hol4_overload "Asm" "labLang_Asm";;
hol4_overload "LabAsm" "labLang_LabAsm";;
                                  (* position, encoded instruction, length *)

(* A section consists a name (num) and a list of assembly lines. *)

let sec_INDUCT,sec_RECURSION = define_datatype
  "sec = Section (num) (('a line) list)";;

let section_num_def = cake_define
  `Section_num (Section k _1) = k`;;
let section_lines_def = cake_define
  `Section_lines (Section _2 lines) = lines`;;

(* A full assembly program consists of a list of sections. *)

(* HOL4 labLangScript.sml:61: the type abbreviation prog, which the
   port expands *)

(* and the overloads that this file cannot see are back in the
   interface *)
let _ = unhide_overloads ();;
