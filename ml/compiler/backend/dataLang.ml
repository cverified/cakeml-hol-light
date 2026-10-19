(* ======================================================== *)
(*  dataLang: ported from HOL4's
    compiler/backend/dataLangScript.sml
    A definition theory, with 3 definitions, 1 datatype and no
    theorems.  Needed by 20 files of the port.  *)
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
needs "lib/comparison.ml";;
needs "misc/misc.ml";;
(* for num_set *)
needs "semantics/ast.ml";;


(* --- Syntax of dataLang --- *)
let op_space_reset_def = cake_define
  `op_space_reset x1 =
        match x1 with
          closLang_IntOp closLang_Add -> T
        | (closLang_IntOp closLang_Sub) -> T
        | (closLang_IntOp closLang_Mult) -> T
        | (closLang_IntOp closLang_Div) -> T
        | (closLang_IntOp closLang_Mod) -> T
        | (closLang_IntOp closLang_Less) -> T
        | (closLang_IntOp closLang_LessEq) -> T
        | (closLang_IntOp Greater) -> T
        | (closLang_IntOp closLang_GreaterEq) -> T
        | (closLang_BlockOp closLang_Equal) -> T
        | (closLang_BlockOp ListAppend) -> T
        | (closLang_BlockOp (closLang_FromList _1)) -> T
        | (closLang_MemOp closLang_RefArray) -> T
        | (closLang_MemOp (closLang_RefByte _2)) -> T
        | (closLang_BlockOp (closLang_ConsExtend _3)) -> T
        | (closLang_MemOp (closLang_CopyByte new_flag)) -> new_flag
        | (closLang_MemOp ConfigGC) -> T
        | (FFI _4) -> T
        | _5 -> F`;;

let op_requires_names_def = cake_define
  `op_requires_names op = (op_space_reset op \/ (?n. op = FFI n) \/
                          (?new_flag. op = (closLang_MemOp
                            (closLang_CopyByte new_flag))) \/
                          (op = closLang_MemOp closLang_XorByte) \/
                          (?b cmp. op = closLang_MemOp
                            (closLang_StringCmp b cmp)) \/
                          (op = closLang_Install))`;;

let dataLang_prog_INDUCT,dataLang_prog_RECURSION = define_datatype
  "dataLang_prog = dataLang_Skip | dataLang_Move (num) (num) | \
   dataLang_Call ((num list#1 spt) option) (num option) (num list) \
   ((num#dataLang_prog) option) \
   // return var, cut-set\n\
   // target of call\n\
   // arguments\n\
   // handler: varname, handler code\n\
   | dataLang_Assign (num) (closLang_op) (num list) ((1 spt) option) \
   | dataLang_Seq (dataLang_prog) (dataLang_prog) | dataLang_If (num) \
   (dataLang_prog) (dataLang_prog) | dataLang_MakeSpace (num) (1 spt) \
   | dataLang_Raise (num) | dataLang_Return (num list) | \
   dataLang_Tick | dataLang_Force ((num#1 spt) option) (num) (num)";;
hol4_overload "Skip" "dataLang_Skip";;
hol4_overload "Move" "dataLang_Move";;
hol4_overload "Call" "dataLang_Call";;
hol4_overload "Assign" "dataLang_Assign";;
hol4_overload "Seq" "dataLang_Seq";;
hol4_overload "If" "dataLang_If";;
hol4_overload "MakeSpace" "dataLang_MakeSpace";;
hol4_overload "Raise" "dataLang_Raise";;
hol4_overload "Return" "dataLang_Return";;
hol4_overload "Tick" "dataLang_Tick";;
hol4_overload "Force" "dataLang_Force";;

let mk_ticks_def = cake_define
  `mk_ticks n e = FUNPOW (dataLang_Seq dataLang_Tick) n e`;;
