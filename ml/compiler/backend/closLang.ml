(* ======================================================== *)
(*  closLang: ported from HOL4's
    compiler/backend/closLangScript.sml
    A definition theory, with 4 definitions, 9 datatypes and 1
    theorem.  Needed by 49 files of the port.  *)
(* ======================================================== *)

(*
  The closLang intermediate language. This language is the last
  intermediate language that has closure values. This language is
  designed for optimisation of function calls.
*)

needs "basis/pure/mlstring.ml";;
needs "compiler/backend/backend_common.ml";;
needs "semantics/ast.ml";;
needs "semantics/fpSem.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "closLang"
  ["ast"; "backend_common"; "fpSem"; "mlstring"];;

(* compilation from this language removes closures *)

let const_INDUCT,const_RECURSION = define_datatype
  "const =
     ConstCons num (const list)
   | ConstInt int
   | ConstStr mlstring
   | ConstWord64 word64";;

let const_part_INDUCT,const_part_RECURSION = define_datatype
  "const_part =
     clos_Con num (num list)
   | clos_Int int
   | clos_Str mlstring
   | clos_W64 word64";;

let clos_int_op_INDUCT,clos_int_op_RECURSION = define_datatype
  "clos_int_op =
     clos_Const int
     // integer
   | clos_Add
     // + over the integers
   | clos_Sub
     // - over the integers
   | clos_Mult
     // * over the integers
   | clos_Div
     // div over the integers
   | clos_Mod
     // mod over the integers
   | clos_Less
     // < over the integers
   | clos_LessEq
     // <= over the integers
   | clos_Greater
     // > over the integers
   | clos_GreaterEq
     // >= over the integers
   | clos_LessConstSmall num
     // checks < const for small ints
  ";;

let clos_word_op_INDUCT,clos_word_op_RECURSION = define_datatype
  "clos_word_op =
     WordOpw word_size opw
   | WordShift word_size ast_shift num
   | WordTest word_size test
   | WordFromInt
   | WordToInt
   | WordFromWord bool
   | FP_cmp fp_cmp
   | FP_uop fp_uop
   | FP_bop fp_bop
   | FP_top fp_top";;

let block_op_INDUCT,block_op_RECURSION = define_datatype
  "block_op =
     clos_Cons num
     // construct a Block with given tag
   | clos_ElemAt num
     // same as El but for constant index
   | clos_TagLenEq num num
     // check Block's tag and length
   | clos_LenEq num
     // check Block's length
   | clos_TagEq num
     // check Block's tag
   | clos_LengthBlock
     // get length of Block
   | clos_BoolTest test
     // tests for bools
   | clos_BoolNot
     // boolean not
   | clos_BoundsCheckBlock
     // check that vector index is within bounds
   | clos_ConsExtend num
     // construct a Block with given tag. The first three
     // arguments should be a block followed by two numbers
     // indicating the first element, and how many, should be
     // copied into the end of the new block. The fourth
     // argument is the total size of the new block.
   | clos_FromList num
     // convert list to packed Block
   | clos_ListAppend
     // appends two lists
   | clos_Constant const
     // produces a constant value
   | clos_Equal
     // structural equality
   | clos_EqualConst const_part
     // equal to integer/string/word constant
   | clos_Build (const_part list)
     // implementation of Constant above
  ";;

let glob_op_INDUCT,glob_op_RECURSION = define_datatype
  "glob_op =
     clos_Global num
     // load global var with index
   | clos_SetGlobal num
     // assign a value to a global
   | clos_AllocGlobal
     // make space for a new global
   | clos_GlobalsPtr
     // get pointer to globals array
   | clos_SetGlobalsPtr
     // set pointer to globals array
  ";;

let clos_mem_op_INDUCT,clos_mem_op_RECURSION = define_datatype
  "clos_mem_op =
     clos_Ref
     // makes a reference/array
   | clos_Update
     // updates a reference/array
   | clos_El
     // read index from block of reference/array
   | clos_Length
     // get length of reference
   | clos_LengthByte
     // get length of byte array
   | clos_RefByte bool
     // makes a byte array, T = immutable/compare-by-contents
   | clos_RefArray
     // makes an array by replicating a value
   | clos_DerefByte
     // loads a byte from a byte array
   | clos_UpdateByte
     // updates a byte array
   | clos_ConcatByteVec
     // concatenate list of byte vectors
   | clos_CopyByte bool
     // copy a slice of a byte array, T means target should be allocated
   | clos_FromListByte
     // convert list of chars to ByteVector
   | clos_ToListByte
     // convert ByteVector to list of chars
   | clos_LengthByteVec
     // get length of ByteVector
   | clos_DerefByteVec
     // load a byte from a ByteVector
   | clos_StringCmp bool opb
     // string comparisons
   | clos_XorByte
     // xor a btye vector into a byte array
   | clos_BoundsCheckArray
   | clos_BoundsCheckByte bool
     // T = loose (<=) bound
   | clos_MutCons num num
     // allocate a cons with a mutable hole, tag, index of hole
   | clos_UpdateCons
     // mutate the hole in a MutCons
   | clos_FinaliseCons
     // turns a stack of MutCons into Cons
   | clos_ConfigGC";;

let clos_op_INDUCT,clos_op_RECURSION = define_datatype
  "clos_op =
     clos_Label num
     // constructs a CodePtr
   | clos_FFI mlstring
     // calls the FFI
   | clos_IntOp clos_int_op
   | clos_WordOp clos_word_op
   | clos_BlockOp block_op
   | clos_GlobOp glob_op
   | clos_MemOp clos_mem_op
   | clos_Install
     // installs new code at runtime
   | clos_ThunkOp ast_thunk_op";;

let clos_exp_INDUCT,clos_exp_RECURSION = define_datatype
  "clos_exp =
     clos_Var tra num
   | clos_If tra clos_exp clos_exp clos_exp
   | clos_Let tra (clos_exp list) clos_exp
   | clos_Raise tra clos_exp
   | clos_Handle tra clos_exp clos_exp
   | clos_Tick tra clos_exp
   | clos_Call tra num num (clos_exp list)
     // ticks
     // loc
     // args
   | clos_App tra (num option) clos_exp (clos_exp list)
   | clos_Fn mlstring (num option) ((num list) option) num clos_exp
   | clos_Letrec (mlstring list) (num option) ((num list) option)
       ((num#clos_exp) list) clos_exp
   | clos_Op tra clos_op (clos_exp list)";;

(* HOL4 closLangScript.sml:143: ML code, not ported *)

(* the termination relation that HOL4 gives is
     MEASURE (\x. match x with INL e -> clos_exp_size e
                                   | INR es -> list_size clos_exp_size es)
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 closLangScript.sml:159-168: the tactic that proves the termination *)
let has_install_def,has_install_ind = define_shaped_rec
  "nested"
  `(has_install ((clos_Var t n):clos_exp) = F) /\
   (has_install (clos_If t e1 e2 e3) = (has_install e1 \/ has_install e2 \/
    has_install e3)) /\
   (has_install (clos_Let t es e) = (has_install e \/ has_install_list es)) /\
   (has_install (clos_Op t p es) = (p = clos_Install \/ has_install_list
    es)) /\
   (has_install (clos_Raise t e) = has_install e) /\
   (has_install (clos_Tick t e) = has_install e) /\
   (has_install (clos_Fn _ _ _ _ e) = has_install e) /\
   (has_install (clos_Handle t e1 e2) = (has_install e1 \/ has_install e2)) /\
   (has_install (clos_Call _ _ _ es) = has_install_list es) /\
   (has_install (clos_App _ _ e es) = (has_install e \/ has_install_list
    es)) /\
   (has_install (clos_Letrec _ _ _ fns e) = (has_install_list (MAP SND fns)
    \/ has_install e)) /\
   (has_install_list [] = F) /\
   (has_install_list (CONS x xs) = (has_install x \/ has_install_list xs))`;;

let exp1_size_lemma = prove
 (`!fns n x. MEM (n,x) fns ==> clos_exp_size x < list_size (pair_size (\x. x)
  clos_exp_size) fns`,
  CHEAT_TAC);;

let pure_op_def = new_definition
  `clos_pure_op op <=>
     (match op with
       clos_FFI _ -> F
     | clos_GlobOp (clos_SetGlobal _) -> F
     | clos_GlobOp clos_AllocGlobal -> F
     | clos_MemOp (clos_RefByte _) -> F
     | clos_MemOp clos_RefArray -> F
     | clos_MemOp clos_UpdateByte -> F
     | clos_MemOp (clos_CopyByte F) -> F
     | clos_MemOp clos_XorByte -> F
     | clos_MemOp clos_Ref -> F
     | clos_MemOp clos_Update -> F
     | clos_Install -> F
     | clos_ThunkOp _ -> F
     | _ -> T)`;;

(* pure e means e can neither raise an exception nor side-effect the state *)
let pure_def,pure_ind = define_shaped_rec
  "nested"
  `(pure (clos_Var _ _) <=> T) /\
   (pure (clos_If _ e1 e2 e3) <=> pure e1 /\ pure e2 /\ pure e3) /\
   (pure (clos_Let _ es e2) <=> ALL pure es /\ pure e2) /\
   (pure (clos_Raise _ _) <=> F) /\
   (pure (clos_Handle _ e1 e2) <=> pure e1) /\
   (pure (clos_Tick _ _) <=> F) /\
   (pure (clos_Call _ _ _ _) <=> F) /\
   (pure (clos_App _ _ _ _) <=> F) /\
   (pure (clos_Fn _ _ _ _ _) <=> T) /\
   (pure (clos_Letrec _ _ _ _ x) <=> pure x) /\
   (pure (clos_Op _ opn es) <=> ALL pure es /\ clos_pure_op opn)`;;

(* used in proofs about closLang, BVL, BVI and dataLang *)
let assign_get_code_label_def = new_definition
  `assign_get_code_label x =
     match x with
       clos_Label x -> {x}
     | x -> {}`;;

new_type_abbrev("clos_prog",`:clos_exp list#(num#num#clos_exp) list`);;

(* HOL4 closLangScript.sml:228: the type abbreviation clos_cc, which the
   port expands *)

(* and the interface *)
let _ = unhide_overloads ();;
