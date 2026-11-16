(* ======================================================== *)
(*  dataLang: ported from HOL4's
    compiler/backend/dataLangScript.sml
    A definition theory, with 3 definitions, 1 datatype and no
    theorems.  Needed by 11 files of the port.  *)
(* ======================================================== *)

(*
  The dataLang intermediate language is the last language with a
  functional-programming-style data abstraction.

  dataLang is the next step from BVL/BVI: (1) dataLang is an
  imperative version of BVL/BVI, i.e. operations update state; (2)
  there is a new state component (called space) and an explicit
  MakeSpace operation that increases space. Space is consumed by Ref
  and Cons, and space is reset by Add, Sub, etc.

  The idea is that the MakeSpace calls can be moved around and lumped
  together. This optimisation reduces the number of calls to the
  allocator and, thus, simplifies the program.  The MakeSpace function
  can, unfortunately, not be moved across function calls or bignum
  operations, which can internally call the allocator.

  The MakeSpace command has an optional variable name list. If this
  list is provided, i.e. SOME var_names, then only these variables can
  survive the execution of the MakeSpace command. The idea is that one
  generates MakeSpace X NONE when compiling into dataLang. Then
  optimisations move around and combine MakeSpace commands. Then
  liveness analysis annotates each MakeSpace command with a SOME. The
  translation from dataLang into more concete forms must implement a
  GC that only looks at the variables in the SOME annotations.
*)

needs "compiler/backend/closLang.ml";;
(* for op *)
needs "misc/misc.ml";;
(* for num_set *)

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "dataLang"
  ["closLang"; "misc"];;


(* --- Syntax of dataLang --- *)
let op_space_reset_def = new_definition
  `op_space_reset x1 =
     match x1 with
       clos_IntOp clos_Add -> T
     | clos_IntOp clos_Sub -> T
     | clos_IntOp clos_Mult -> T
     | clos_IntOp clos_Div -> T
     | clos_IntOp clos_Mod -> T
     | clos_IntOp clos_Less -> T
     | clos_IntOp clos_LessEq -> T
     | clos_IntOp clos_Greater -> T
     | clos_IntOp clos_GreaterEq -> T
     | clos_BlockOp clos_Equal -> T
     | clos_BlockOp clos_ListAppend -> T
     | clos_BlockOp (clos_FromList _) -> T
     | clos_MemOp clos_RefArray -> T
     | clos_MemOp (clos_RefByte _) -> T
     | clos_BlockOp (clos_ConsExtend _) -> T
     | clos_MemOp (clos_CopyByte new_flag) -> new_flag
     | clos_MemOp clos_ConfigGC -> T
     | clos_FFI _ -> T
     | _ -> F`;;

let op_requires_names_def = new_definition
  `op_requires_names op = (op_space_reset op \/ (?n. op = clos_FFI n) \/
                          (?new_flag. op = (clos_MemOp (clos_CopyByte
                            new_flag))) \/
                          (op = clos_MemOp clos_XorByte) \/
                          (?b cmp. op = clos_MemOp (clos_StringCmp b cmp))
                            \/
                          (op = clos_Install))`;;

let data_prog_INDUCT,data_prog_RECURSION = define_datatype
  "data_prog =
     data_Skip
   | data_Move num num
   | data_Call ((num list#misc_num_set) option) (num option) (num list)
       ((num#data_prog) option)
     // return var, cut-set
     // target of call
     // arguments
     // handler: varname, handler code
   | data_Assign num clos_op (num list) (misc_num_set option)
   | data_Seq data_prog data_prog
   | data_If num data_prog data_prog
   | data_MakeSpace num misc_num_set
   | data_Raise num
   | data_Return (num list)
   | data_Tick
   | data_Force ((num#misc_num_set) option) num num";;

let mk_ticks_def = new_definition
  `mk_ticks n e = ITER n (data_Seq data_Tick) e`;;

(* and the interface *)
let _ = unhide_overloads ();;
