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
     closLang_Con num (num list)
   | closLang_Int int
   | closLang_Str mlstring
   | closLang_W64 word64";;

let closLang_int_op_INDUCT,closLang_int_op_RECURSION = define_datatype
  "closLang_int_op =
     closLang_Const int
     // integer
   | closLang_Add
     // + over the integers
   | closLang_Sub
     // - over the integers
   | closLang_Mult
     // * over the integers
   | closLang_Div
     // div over the integers
   | closLang_Mod
     // mod over the integers
   | closLang_Less
     // < over the integers
   | closLang_LessEq
     // <= over the integers
   | closLang_Greater
     // > over the integers
   | closLang_GreaterEq
     // >= over the integers
   | closLang_LessConstSmall num
     // checks < const for small ints
  ";;

let closLang_word_op_INDUCT,closLang_word_op_RECURSION = define_datatype
  "closLang_word_op =
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
     closLang_Cons num
     // construct a Block with given tag
   | closLang_ElemAt num
     // same as El but for constant index
   | closLang_TagLenEq num num
     // check Block's tag and length
   | closLang_LenEq num
     // check Block's length
   | closLang_TagEq num
     // check Block's tag
   | closLang_LengthBlock
     // get length of Block
   | closLang_BoolTest test
     // tests for bools
   | closLang_BoolNot
     // boolean not
   | closLang_BoundsCheckBlock
     // check that vector index is within bounds
   | closLang_ConsExtend num
     // construct a Block with given tag. The first three
     // arguments should be a block followed by two numbers
     // indicating the first element, and how many, should be
     // copied into the end of the new block. The fourth
     // argument is the total size of the new block.
   | closLang_FromList num
     // convert list to packed Block
   | closLang_ListAppend
     // appends two lists
   | closLang_Constant const
     // produces a constant value
   | closLang_Equal
     // structural equality
   | closLang_EqualConst const_part
     // equal to integer/string/word constant
   | closLang_Build (const_part list)
     // implementation of Constant above
  ";;

let glob_op_INDUCT,glob_op_RECURSION = define_datatype
  "glob_op =
     closLang_Global num
     // load global var with index
   | closLang_SetGlobal num
     // assign a value to a global
   | closLang_AllocGlobal
     // make space for a new global
   | closLang_GlobalsPtr
     // get pointer to globals array
   | closLang_SetGlobalsPtr
     // set pointer to globals array
  ";;

let closLang_mem_op_INDUCT,closLang_mem_op_RECURSION = define_datatype
  "closLang_mem_op =
     closLang_Ref
     // makes a reference/array
   | closLang_Update
     // updates a reference/array
   | closLang_El
     // read index from block of reference/array
   | closLang_Length
     // get length of reference
   | closLang_LengthByte
     // get length of byte array
   | closLang_RefByte bool
     // makes a byte array, T = immutable/compare-by-contents
   | closLang_RefArray
     // makes an array by replicating a value
   | closLang_DerefByte
     // loads a byte from a byte array
   | closLang_UpdateByte
     // updates a byte array
   | closLang_ConcatByteVec
     // concatenate list of byte vectors
   | closLang_CopyByte bool
     // copy a slice of a byte array, T means target should be allocated
   | closLang_FromListByte
     // convert list of chars to ByteVector
   | closLang_ToListByte
     // convert ByteVector to list of chars
   | closLang_LengthByteVec
     // get length of ByteVector
   | closLang_DerefByteVec
     // load a byte from a ByteVector
   | closLang_StringCmp bool opb
     // string comparisons
   | closLang_XorByte
     // xor a btye vector into a byte array
   | closLang_BoundsCheckArray
   | closLang_BoundsCheckByte bool
     // T = loose (<=) bound
   | closLang_MutCons num num
     // allocate a cons with a mutable hole, tag, index of hole
   | closLang_UpdateCons
     // mutate the hole in a MutCons
   | closLang_FinaliseCons
     // turns a stack of MutCons into Cons
   | closLang_ConfigGC";;

let closLang_op_INDUCT,closLang_op_RECURSION = define_datatype
  "closLang_op =
     closLang_Label num
     // constructs a CodePtr
   | closLang_FFI mlstring
     // calls the FFI
   | closLang_IntOp closLang_int_op
   | closLang_WordOp closLang_word_op
   | closLang_BlockOp block_op
   | closLang_GlobOp glob_op
   | closLang_MemOp closLang_mem_op
   | closLang_Install
     // installs new code at runtime
   | closLang_ThunkOp ast_thunk_op";;

let closLang_exp_INDUCT,closLang_exp_RECURSION = define_datatype
  "closLang_exp =
     closLang_Var tra num
   | closLang_If tra closLang_exp closLang_exp closLang_exp
   | closLang_Let tra (closLang_exp list) closLang_exp
   | closLang_Raise tra closLang_exp
   | closLang_Handle tra closLang_exp closLang_exp
   | closLang_Tick tra closLang_exp
   | closLang_Call tra num num (closLang_exp list)
     // ticks
     // loc
     // args
   | closLang_App tra (num option) closLang_exp (closLang_exp list)
   | closLang_Fn mlstring (num option) ((num list) option) num
       closLang_exp
   | closLang_Letrec (mlstring list) (num option) ((num list) option)
       ((num#closLang_exp) list) closLang_exp
   | closLang_Op tra closLang_op (closLang_exp list)";;

(* HOL4 closLangScript.sml:143: ML code, not ported *)

(* the termination relation that HOL4 gives is
     MEASURE (\x. match x with INL e -> closLang_exp_size e | INR es ->
       list_size closLang_exp_size es)
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 closLangScript.sml:159-168: the tactic that proves the
   termination *)
let has_install_def,has_install_ind = define_shaped_rec
  "nested"
  [`has_install ((closLang_Var t n):closLang_exp) = F`;
   `has_install (closLang_If t e1 e2 e3:closLang_exp) = (has_install
    e1 \/ has_install e2 \/ has_install e3)`;
   `has_install (closLang_Let t es e:closLang_exp) = (has_install e
    \/ has_install_list es)`;
   `has_install (closLang_Op t p es:closLang_exp) = (p =
    closLang_Install \/ has_install_list es)`;
   `has_install (closLang_Raise t e:closLang_exp) = has_install e`;
   `has_install (closLang_Tick t e:closLang_exp) = has_install e`;
   `has_install (closLang_Fn _1 _2 _3 _4 e) = has_install e`;
   `has_install (closLang_Handle t e1 e2:closLang_exp) = (has_install
    e1 \/ has_install e2)`;
   `has_install (closLang_Call _8 _9 _10 es:closLang_exp) =
    has_install_list es`;
   `has_install (closLang_App _13 _14 e es:closLang_exp) =
    (has_install e \/ has_install_list es)`;
   `has_install (closLang_Letrec _18 _19 _20 fns e:closLang_exp) =
    (has_install_list (MAP SND fns) \/ has_install e)`;
   `has_install_list [] = F`;
   `has_install_list (CONS x xs) = (has_install x \/
    has_install_list xs)`];;

let exp1_size_lemma = prove
 (`!fns n x. MEM (n,x) fns ==> closLang_exp_size x < list_size
  (pair_size (\x. x) closLang_exp_size) fns`,
  CHEAT_TAC);;

let pure_op_def = new_definition
  `closLang_pure_op op <=>
     (match op with
       closLang_FFI _21 -> F | closLang_GlobOp (closLang_SetGlobal
         _22) -> F | closLang_GlobOp closLang_AllocGlobal -> F |
         closLang_MemOp (closLang_RefByte _23) -> F | closLang_MemOp
         closLang_RefArray -> F | closLang_MemOp closLang_UpdateByte
         -> F | closLang_MemOp (closLang_CopyByte F) -> F |
         closLang_MemOp closLang_XorByte -> F | closLang_MemOp
         closLang_Ref -> F | closLang_MemOp closLang_Update -> F |
         closLang_Install -> F | closLang_ThunkOp _24 -> F | _25 ->
         T)`;;

(* pure e means e can neither raise an exception nor side-effect the state *)
let pure_def,pure_ind = define_shaped_rec
  "nested"
  [`pure (closLang_Var _28 _29:closLang_exp) <=> T`;
   `pure (closLang_If _31 e1 e2 e3:closLang_exp) <=> pure e1 /\ pure
    e2 /\ pure e3`;
   `pure (closLang_Let _33 es e2:closLang_exp) <=> ALL pure es /\
    pure e2`;
   `pure (closLang_Raise _36 _37:closLang_exp) <=> F`;
   `pure (closLang_Handle _39 e1 e2:closLang_exp) <=> pure e1`;
   `pure (closLang_Tick _42 _43:closLang_exp) <=> F`;
   `pure (closLang_Call _48 _49 _50 _51:closLang_exp) <=> F`;
   `pure (closLang_App _56 _57 _58 _59:closLang_exp) <=> F`;
   `pure (closLang_Fn _60 _61 _62 _63 _64) <=> T`;
   `pure (closLang_Letrec _69 _70 _71 _72 x:closLang_exp) <=> pure x`;
   `pure (closLang_Op _74 opn es:closLang_exp) <=> ALL pure es /\
    closLang_pure_op opn`];;

(* used in proofs about closLang, BVL, BVI and dataLang *)
let assign_get_code_label_def = new_definition
  `assign_get_code_label x =
        match x with
          closLang_Label x -> {x}
        | x -> {}`;;

new_type_abbrev("clos_prog",`:closLang_exp
   list#(num#num#closLang_exp) list`);;

(* HOL4 closLangScript.sml:228: the type abbreviation clos_cc, which
   the port expands *)

(* and the interface *)
let _ = unhide_overloads ();;
