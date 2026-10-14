(* ======================================================== *)
(*  dataLang: ported from HOL4's
    compiler/backend/dataLangScript.sml  *)
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
needs "lib/ternaryComparisons.ml";;
needs "misc/misc.ml";;
(* HOL4 ancestors outside the port: (* for op *) (* for num_set *) *)


(* --- Syntax of dataLang --- *)
let op_space_reset_def = cake_define
  `op_space_reset x1 =
        match x1 with
          (closLang_IntOp closLang_Add) -> T
        | (closLang_IntOp closLang_Sub) -> T
        | (closLang_IntOp closLang_Mult) -> T
        | (closLang_IntOp closLang_Div) -> T
        | (closLang_IntOp closLang_Mod) -> T
        | (closLang_IntOp (LESS)) -> T
        | (closLang_IntOp closLang_LessEq) -> T
        | (closLang_IntOp (GREATER)) -> T
        | (closLang_IntOp closLang_GreaterEq) -> T
        | (closLang_BlockOp (EQUAL)) -> T
        | (closLang_BlockOp closLang_ListAppend) -> T
        | (closLang_BlockOp (closLang_FromList _1)) -> T
        | (closLang_MemOp closLang_RefArray) -> T
        | (closLang_MemOp (closLang_RefByte _2)) -> T
        | (closLang_BlockOp (closLang_ConsExtend _3)) -> T
        | (closLang_MemOp (closLang_CopyByte new_flag)) -> new_flag
        | (closLang_MemOp closLang_ConfigGC) -> T
        | (closLang_FFI _4) -> T
        | _5 -> F`;;

let op_requires_names_def = cake_define
  `op_requires_names closLang_op = (op_space_reset closLang_op \/ (?n.
  closLang_op = closLang_FFI n) \/
                          (?new_flag. closLang_op = (closLang_MemOp
                            (closLang_CopyByte new_flag))) \/
                          (closLang_op = closLang_MemOp
                            closLang_XorByte) \/
                          (?b cmp. closLang_op = closLang_MemOp
                            (closLang_StringCmp b cmp)) \/
                          (closLang_op = closLang_Install))`;;

let dataLang_prog_INDUCT,dataLang_prog_RECURSION = define_datatype
  "dataLang_prog = dataLang_Skip | dataLang_Move (num) (num) | \
   dataLang_Call ((num list#one spt) option) (num option) (num list) \
   ((num#dataLang_prog) option) | dataLang_Assign (num) (closLang_op) \
   (num list) ((one spt) option) | dataLang_Seq (dataLang_prog) \
   (dataLang_prog) | dataLang_If (num) (dataLang_prog) \
   (dataLang_prog) | dataLang_MakeSpace (num) (one spt) | \
   dataLang_Raise (num) | dataLang_Return (num list) | dataLang_Tick \
   | dataLang_Force ((num#one spt) option) (num) (num)";;

let mk_ticks_def = cake_define
  `mk_ticks n e = FUNPOW (dataLang_Seq dataLang_Tick) n e`;;
