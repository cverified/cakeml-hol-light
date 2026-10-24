(* ======================================================== *)
(*  closLang: ported from HOL4's
    compiler/backend/closLangScript.sml
    A definition theory, with 4 definitions, 9 datatypes and 1
    theorem.  Needed by 73 files of the port.  *)
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

(* compilation from this language removes closures *)

let const_INDUCT,const_RECURSION = define_datatype
  "const = ConstCons (num) (const list) | ConstInt (int) | ConstStr \
   (mlstring) | ConstWord64 (word64)";;

let const_part_INDUCT,const_part_RECURSION = define_datatype
  "const_part = closLang_Con (num) (num list) | closLang_Int (int) | \
   closLang_Str (mlstring) | closLang_W64 (word64)";;
hol4_overload "Con" "closLang_Con";;
hol4_overload "Int" "closLang_Int";;
hol4_overload "Str" "closLang_Str";;
hol4_overload "W64" "closLang_W64";;

let closLang_int_op_INDUCT,closLang_int_op_RECURSION = define_datatype
  "closLang_int_op = closLang_Const (int) \
   // integer\n\
   | closLang_Add \
   // + over the integers\n\
   | closLang_Sub \
   // - over the integers\n\
   | closLang_Mult \
   // * over the integers\n\
   | closLang_Div \
   // div over the integers\n\
   | closLang_Mod \
   // mod over the integers\n\
   | closLang_Less \
   // < over the integers\n\
   | closLang_LessEq \
   // <= over the integers\n\
   | closLang_Greater \
   // > over the integers\n\
   | closLang_GreaterEq \
   // >= over the integers\n\
   | closLang_LessConstSmall (num) \
   // checks < const for small ints";;
hol4_overload "Const" "closLang_Const";;
hol4_overload "Add" "closLang_Add";;
hol4_overload "Sub" "closLang_Sub";;
hol4_overload "Mult" "closLang_Mult";;
hol4_overload "Div" "closLang_Div";;
hol4_overload "Mod" "closLang_Mod";;
hol4_overload "Less" "closLang_Less";;
hol4_overload "LessEq" "closLang_LessEq";;
hol4_overload "Greater" "closLang_Greater";;
hol4_overload "GreaterEq" "closLang_GreaterEq";;
hol4_overload "LessConstSmall" "closLang_LessConstSmall";;

let closLang_word_op_INDUCT,closLang_word_op_RECURSION = define_datatype
  "closLang_word_op = WordOpw (word_size) (opw) | WordShift \
   (word_size) (ast_shift) (num) | WordTest (word_size) (test) | \
   WordFromInt | WordToInt | WordFromWord (bool) | FP_cmp (fp_cmp) | \
   FP_uop (fp_uop) | FP_bop (fp_bop) | FP_top (fp_top)";;

let block_op_INDUCT,block_op_RECURSION = define_datatype
  "block_op = closLang_Cons (num) \
   // construct a Block with given tag\n\
   | closLang_ElemAt (num) \
   // same as El but for constant index\n\
   | closLang_TagLenEq (num) (num) \
   // check Block's tag and length\n\
   | closLang_LenEq (num) \
   // check Block's length\n\
   | closLang_TagEq (num) \
   // check Block's tag\n\
   | closLang_LengthBlock \
   // get length of Block\n\
   | closLang_BoolTest (test) \
   // tests for bools\n\
   | closLang_BoolNot \
   // boolean not\n\
   | closLang_BoundsCheckBlock \
   // check that vector index is within bounds\n\
   | closLang_ConsExtend (num) \
   // construct a Block with given tag. The first three\n\
   // arguments should be a block followed by two numbers\n\
   // indicating the first element, and how many, should be\n\
   // copied into the end of the new block. The fourth\n\
   // argument is the total size of the new block.\n\
   | closLang_FromList (num) \
   // convert list to packed Block\n\
   | closLang_ListAppend \
   // appends two lists\n\
   | closLang_Constant (const) \
   // produces a constant value\n\
   | closLang_Equal \
   // structural equality\n\
   | closLang_EqualConst (const_part) \
   // equal to integer/string/word constant\n\
   | closLang_Build (const_part list) \
   // implementation of Constant above";;
hol4_overload "Cons" "closLang_Cons";;
hol4_overload "ElemAt" "closLang_ElemAt";;
hol4_overload "TagLenEq" "closLang_TagLenEq";;
hol4_overload "LenEq" "closLang_LenEq";;
hol4_overload "TagEq" "closLang_TagEq";;
hol4_overload "LengthBlock" "closLang_LengthBlock";;
hol4_overload "BoolTest" "closLang_BoolTest";;
hol4_overload "BoolNot" "closLang_BoolNot";;
hol4_overload "BoundsCheckBlock" "closLang_BoundsCheckBlock";;
hol4_overload "ConsExtend" "closLang_ConsExtend";;
hol4_overload "FromList" "closLang_FromList";;
hol4_overload "ListAppend" "closLang_ListAppend";;
hol4_overload "Constant" "closLang_Constant";;
hol4_overload "Equal" "closLang_Equal";;
hol4_overload "EqualConst" "closLang_EqualConst";;
hol4_overload "Build" "closLang_Build";;

let glob_op_INDUCT,glob_op_RECURSION = define_datatype
  "glob_op = closLang_Global (num) \
   // load global var with index\n\
   | closLang_SetGlobal (num) \
   // assign a value to a global\n\
   | closLang_AllocGlobal \
   // make space for a new global\n\
   | closLang_GlobalsPtr \
   // get pointer to globals array\n\
   | closLang_SetGlobalsPtr \
   // set pointer to globals array";;
hol4_overload "Global" "closLang_Global";;
hol4_overload "SetGlobal" "closLang_SetGlobal";;
hol4_overload "AllocGlobal" "closLang_AllocGlobal";;
hol4_overload "GlobalsPtr" "closLang_GlobalsPtr";;
hol4_overload "SetGlobalsPtr" "closLang_SetGlobalsPtr";;

let closLang_mem_op_INDUCT,closLang_mem_op_RECURSION = define_datatype
  "closLang_mem_op = closLang_Ref \
   // makes a reference/array\n\
   | closLang_Update \
   // updates a reference/array\n\
   | closLang_El \
   // read index from block of reference/array\n\
   | closLang_Length \
   // get length of reference\n\
   | closLang_LengthByte \
   // get length of byte array\n\
   | closLang_RefByte (bool) \
   // makes a byte array, T = immutable/compare-by-contents\n\
   | closLang_RefArray \
   // makes an array by replicating a value\n\
   | closLang_DerefByte \
   // loads a byte from a byte array\n\
   | closLang_UpdateByte \
   // updates a byte array\n\
   | closLang_ConcatByteVec \
   // concatenate list of byte vectors\n\
   | closLang_CopyByte (bool) \
   // copy a slice of a byte array, T means target should be allocated\n\
   | closLang_FromListByte \
   // convert list of chars to ByteVector\n\
   | closLang_ToListByte \
   // convert ByteVector to list of chars\n\
   | closLang_LengthByteVec \
   // get length of ByteVector\n\
   | closLang_DerefByteVec \
   // load a byte from a ByteVector\n\
   | closLang_StringCmp (bool) (opb) \
   // string comparisons\n\
   | closLang_XorByte \
   // xor a btye vector into a byte array\n\
   | closLang_BoundsCheckArray | closLang_BoundsCheckByte (bool) \
   // T = loose (<=) bound\n\
   | closLang_MutCons (num) (num) \
   // allocate a cons with a mutable hole, tag, index of hole\n\
   | closLang_UpdateCons \
   // mutate the hole in a MutCons\n\
   | closLang_FinaliseCons \
   // turns a stack of MutCons into Cons\n\
   | closLang_ConfigGC";;
hol4_overload "Ref" "closLang_Ref";;
hol4_overload "Update" "closLang_Update";;
hol4_overload "El" "closLang_El";;
hol4_overload "Length" "closLang_Length";;
hol4_overload "LengthByte" "closLang_LengthByte";;
hol4_overload "RefByte" "closLang_RefByte";;
hol4_overload "RefArray" "closLang_RefArray";;
hol4_overload "DerefByte" "closLang_DerefByte";;
hol4_overload "UpdateByte" "closLang_UpdateByte";;
hol4_overload "ConcatByteVec" "closLang_ConcatByteVec";;
hol4_overload "CopyByte" "closLang_CopyByte";;
hol4_overload "FromListByte" "closLang_FromListByte";;
hol4_overload "ToListByte" "closLang_ToListByte";;
hol4_overload "LengthByteVec" "closLang_LengthByteVec";;
hol4_overload "DerefByteVec" "closLang_DerefByteVec";;
hol4_overload "StringCmp" "closLang_StringCmp";;
hol4_overload "XorByte" "closLang_XorByte";;
hol4_overload "BoundsCheckArray" "closLang_BoundsCheckArray";;
hol4_overload "BoundsCheckByte" "closLang_BoundsCheckByte";;
hol4_overload "MutCons" "closLang_MutCons";;
hol4_overload "UpdateCons" "closLang_UpdateCons";;
hol4_overload "FinaliseCons" "closLang_FinaliseCons";;
hol4_overload "ConfigGC" "closLang_ConfigGC";;

let closLang_op_INDUCT,closLang_op_RECURSION = define_datatype
  "closLang_op = closLang_Label (num) \
   // constructs a CodePtr\n\
   | closLang_FFI (mlstring) \
   // calls the FFI\n\
   | closLang_IntOp (closLang_int_op) | closLang_WordOp \
   (closLang_word_op) | closLang_BlockOp (block_op) | closLang_GlobOp \
   (glob_op) | closLang_MemOp (closLang_mem_op) | closLang_Install \
   // installs new code at runtime\n\
   | closLang_ThunkOp (ast_thunk_op)";;
hol4_overload "Label" "closLang_Label";;
hol4_overload "FFI" "closLang_FFI";;
hol4_overload "IntOp" "closLang_IntOp";;
hol4_overload "WordOp" "closLang_WordOp";;
hol4_overload "BlockOp" "closLang_BlockOp";;
hol4_overload "GlobOp" "closLang_GlobOp";;
hol4_overload "MemOp" "closLang_MemOp";;
hol4_overload "Install" "closLang_Install";;
hol4_overload "ThunkOp" "closLang_ThunkOp";;

let closLang_exp_INDUCT,closLang_exp_RECURSION = define_datatype
  "closLang_exp = closLang_Var (tra) (num) | closLang_If (tra) \
   (closLang_exp) (closLang_exp) (closLang_exp) | closLang_Let (tra) \
   (closLang_exp list) (closLang_exp) | closLang_Raise (tra) \
   (closLang_exp) | closLang_Handle (tra) (closLang_exp) \
   (closLang_exp) | closLang_Tick (tra) (closLang_exp) | \
   closLang_Call (tra) (num) (num) (closLang_exp list) \
   // ticks\n\
   // loc\n\
   // args\n\
   | closLang_App (tra) (num option) (closLang_exp) (closLang_exp \
   list) | closLang_Fn (mlstring) (num option) ((num list) option) \
   (num) (closLang_exp) | closLang_Letrec (mlstring list) (num \
   option) ((num list) option) ((num#closLang_exp) list) \
   (closLang_exp) | closLang_Op (tra) (closLang_op) (closLang_exp \
   list)";;
hol4_overload "Var" "closLang_Var";;
hol4_overload "If" "closLang_If";;
hol4_overload "Let" "closLang_Let";;
hol4_overload "Raise" "closLang_Raise";;
hol4_overload "Handle" "closLang_Handle";;
hol4_overload "Tick" "closLang_Tick";;
hol4_overload "Call" "closLang_Call";;
hol4_overload "App" "closLang_App";;
hol4_overload "Fn" "closLang_Fn";;
hol4_overload "Letrec" "closLang_Letrec";;
hol4_overload "Op" "closLang_Op";;

(* HOL4 closLangScript.sml:143: ML code, not ported *)

let _ = size_thms "closLang_exp";;
(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 closLangScript.sml:159-168: the tactic that proves the
   termination *)
let has_install_def = cake_define_list_try (fun () ->
  `MEASURE (\x. match x with INL e -> closLang_exp_size e | INR es ->
     list_size closLang_exp_size es)`)
  [`has_install ((Var t n):closLang_exp) = F`;
   `has_install (If t e1 e2 e3:closLang_exp) = (has_install e1 \/
  has_install e2 \/ has_install e3)`;
   `has_install (Let t es e:closLang_exp) = (has_install e \/
  has_install_list es)`;
   `has_install (closLang_Op t p es:closLang_exp) = (p =
  closLang_Install \/ has_install_list es)`;
   `has_install (Raise t e:closLang_exp) = has_install e`;
   `has_install (closLang_Tick t e:closLang_exp) = has_install e`;
   `has_install (closLang_Fn _1 _2 _3 _4 e) = has_install e`;
   `has_install (Handle t e1 e2:closLang_exp) = (has_install e1 \/
  has_install e2)`;
   `has_install (closLang_Call _8 _9 _10 es:closLang_exp) =
  has_install_list es`;
   `has_install (App _13 _14 e es:closLang_exp) = (has_install e \/
  has_install_list es)`;
   `has_install (Letrec _18 _19 _20 fns e:closLang_exp) =
  (has_install_list (MAP SND fns) \/ has_install e)`;
   `has_install_list [] = F`;
   `has_install_list (x :: xs) = (has_install x \/ has_install_list
  xs)`];;

(* HOL4 closLangScript.sml:170-175: a theorem whose statement the
   port cannot state yet: exp1_size_lemma *)

let pure_op_def = cake_define
  `closLang_pure_op op <=>
     (match op with
       FFI _21 -> F | closLang_GlobOp (closLang_SetGlobal _22) ->
         F | closLang_GlobOp closLang_AllocGlobal -> F |
         closLang_MemOp (closLang_RefByte _23) -> F | closLang_MemOp
         closLang_RefArray -> F | closLang_MemOp closLang_UpdateByte
         -> F | closLang_MemOp (closLang_CopyByte F) -> F |
         closLang_MemOp closLang_XorByte -> F | closLang_MemOp
         closLang_Ref -> F | closLang_MemOp closLang_Update -> F |
         closLang_Install -> F | ThunkOp _24 -> F | _25 -> T)`;;
hol4_overload "pure_op" "closLang_pure_op";;

(* pure e means e can neither raise an exception nor side-effect the state *)
let pure_def = cake_define_list
  [`pure (Var _28 _29:closLang_exp) <=> T`;
   `pure (If _31 e1 e2 e3:closLang_exp) <=> pure e1 /\ pure e2 /\
  pure e3`;
   `pure (Let _33 es e2:closLang_exp) <=> EVERY pure es /\ pure e2`;
   `pure (Raise _36 _37:closLang_exp) <=> F`;
   `pure (Handle _39 e1 e2:closLang_exp) <=> pure e1`;
   `pure (closLang_Tick _42 _43:closLang_exp) <=> F`;
   `pure (closLang_Call _48 _49 _50 _51:closLang_exp) <=> F`;
   `pure (App _56 _57 _58 _59:closLang_exp) <=> F`;
   `pure (closLang_Fn _60 _61 _62 _63 _64) <=> T`;
   `pure (Letrec _69 _70 _71 _72 x:closLang_exp) <=> pure x`;
   `pure (closLang_Op _74 opn es:closLang_exp) <=> EVERY pure es /\
  closLang_pure_op opn`];;

(* used in proofs about closLang, BVL, BVI and dataLang *)
let assign_get_code_label_def = cake_define
  `assign_get_code_label x =
        match x with
          closLang_Label x -> {x}
        | x -> {}`;;

new_type_abbrev("clos_prog",`: closLang_exp
   list#(num#num#closLang_exp) list`);;

(* HOL4 closLangScript.sml:228: the type abbreviation clos_cc, which
   the port expands *)
