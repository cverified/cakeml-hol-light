(* ======================================================== *)
(*  closLang: ported from HOL4's
    compiler/backend/closLangScript.sml  *)
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
hol4_overload "W64" "closLang_W64";;

let closLang_int_op_INDUCT,closLang_int_op_RECURSION = define_datatype
  "closLang_int_op = closLang_Const (int) | closLang_Add | \
   closLang_Sub | closLang_Mult | closLang_Div | closLang_Mod | \
   closLang_Less | closLang_LessEq | closLang_Greater | \
   closLang_GreaterEq | closLang_LessConstSmall (num)";;
hol4_overload "Add" "closLang_Add";;
hol4_overload "Sub" "closLang_Sub";;
hol4_overload "Div" "closLang_Div";;
hol4_overload "Mod" "closLang_Mod";;
hol4_overload "Less" "closLang_Less";;
hol4_overload "Greater" "closLang_Greater";;

let closLang_word_op_INDUCT,closLang_word_op_RECURSION = define_datatype
  "closLang_word_op = WordOpw (word_size) (opw) | WordShift \
   (word_size) (ast_shift) (num) | WordTest (word_size) (test) | \
   WordFromInt | WordToInt | WordFromWord (bool) | FP_cmp (fp_cmp) | \
   FP_uop (fp_uop) | FP_bop (fp_bop) | FP_top (fp_top)";;

let block_op_INDUCT,block_op_RECURSION = define_datatype
  "block_op = closLang_Cons (num) | closLang_ElemAt (num) | \
   closLang_TagLenEq (num) (num) | closLang_LenEq (num) | \
   closLang_TagEq (num) | closLang_LengthBlock | closLang_BoolTest \
   (test) | closLang_BoolNot | closLang_BoundsCheckBlock | \
   closLang_ConsExtend (num) | closLang_FromList (num) | \
   closLang_ListAppend | closLang_Constant (const) | closLang_Equal | \
   closLang_EqualConst (const_part) | closLang_Build (const_part \
   list)";;
hol4_overload "Cons" "closLang_Cons";;
hol4_overload "ListAppend" "closLang_ListAppend";;
hol4_overload "Equal" "closLang_Equal";;

let glob_op_INDUCT,glob_op_RECURSION = define_datatype
  "glob_op = Global (num) | SetGlobal (num) | AllocGlobal | \
   GlobalsPtr | SetGlobalsPtr";;

let closLang_mem_op_INDUCT,closLang_mem_op_RECURSION = define_datatype
  "closLang_mem_op = closLang_Ref | closLang_Update | closLang_El | \
   closLang_Length | closLang_LengthByte | closLang_RefByte (bool) | \
   closLang_RefArray | closLang_DerefByte | closLang_UpdateByte | \
   closLang_ConcatByteVec | closLang_CopyByte (bool) | \
   closLang_FromListByte | closLang_ToListByte | \
   closLang_LengthByteVec | closLang_DerefByteVec | \
   closLang_StringCmp (bool) (opb) | closLang_XorByte | \
   closLang_BoundsCheckArray | closLang_BoundsCheckByte (bool) | \
   closLang_MutCons (num) (num) | closLang_UpdateCons | \
   closLang_FinaliseCons | closLang_ConfigGC";;
hol4_overload "ConfigGC" "closLang_ConfigGC";;

let closLang_op_INDUCT,closLang_op_RECURSION = define_datatype
  "closLang_op = closLang_Label (num) | closLang_FFI (mlstring) | \
   closLang_IntOp (closLang_int_op) | closLang_WordOp \
   (closLang_word_op) | closLang_BlockOp (block_op) | closLang_GlobOp \
   (glob_op) | closLang_MemOp (closLang_mem_op) | closLang_Install | \
   closLang_ThunkOp (ast_thunk_op)";;
hol4_overload "FFI" "closLang_FFI";;
hol4_overload "ThunkOp" "closLang_ThunkOp";;

let closLang_exp_INDUCT,closLang_exp_RECURSION = define_datatype
  "closLang_exp = closLang_Var (tra) (num) | closLang_If (tra) \
   (closLang_exp) (closLang_exp) (closLang_exp) | closLang_Let (tra) \
   (closLang_exp list) (closLang_exp) | closLang_Raise (tra) \
   (closLang_exp) | closLang_Handle (tra) (closLang_exp) \
   (closLang_exp) | closLang_Tick (tra) (closLang_exp) | \
   closLang_Call (tra) (num) (num) (closLang_exp list) | closLang_App \
   (tra) (num option) (closLang_exp) (closLang_exp list) | \
   closLang_Fn (mlstring) (num option) ((num list) option) (num) \
   (closLang_exp) | closLang_Letrec (mlstring list) (num option) \
   ((num list) option) ((num#closLang_exp) list) (closLang_exp) | \
   closLang_Op (tra) (closLang_op) (closLang_exp list)";;
hol4_overload "Var" "closLang_Var";;
hol4_overload "If" "closLang_If";;
hol4_overload "Let" "closLang_Let";;
hol4_overload "Raise" "closLang_Raise";;
hol4_overload "Handle" "closLang_Handle";;
hol4_overload "App" "closLang_App";;
hol4_overload "Letrec" "closLang_Letrec";;

(* HOL4 ML code, not ported:
val exp_size_def = definition"exp_size_def";
*)

let has_install_def = cake_define_list
  [`has_install ((Var t n):closLang_exp) = F`;
   `has_install (If t e1 e2 e3:closLang_exp) = (has_install e1 \/
  has_install e2 \/ has_install e3)`;
   `has_install (Let t es e:closLang_exp) = (has_install e \/
  has_install_list es)`;
   `has_install (closLang_Op t p es) = (p = closLang_Install \/
  has_install_list es)`;
   `has_install (Raise t e:closLang_exp) = has_install e`;
   `has_install (closLang_Tick t e) = has_install e`;
   `has_install (closLang_Fn _1 _2 _3 _4 e) = has_install e`;
   `has_install (Handle t e1 e2:closLang_exp) = (has_install e1 \/
  has_install e2)`;
   `has_install (closLang_Call _5 _6 _7 es) = has_install_list es`;
   `has_install (App _8 _9 e es:closLang_exp) = (has_install e \/
  has_install_list es)`;
   `has_install (Letrec _10 _11 _12 fns e:closLang_exp) =
  (has_install_list (MAP SND fns) \/ has_install e)`;
   `has_install_list [] = F`;
   `has_install_list (x :: xs) = (has_install x \/ has_install_list
  xs)`];;

let pure_op_def = cake_define
  `closLang_pure_op op <=>
     (match op with
       FFI _13 -> F | closLang_GlobOp (SetGlobal _14) -> F |
         closLang_GlobOp AllocGlobal -> F | closLang_MemOp
         (closLang_RefByte _15) -> F | closLang_MemOp
         closLang_RefArray -> F | closLang_MemOp closLang_UpdateByte
         -> F | closLang_MemOp (closLang_CopyByte F) -> F |
         closLang_MemOp closLang_XorByte -> F | closLang_MemOp
         closLang_Ref -> F | closLang_MemOp closLang_Update -> F |
         closLang_Install -> F | ThunkOp _16 -> F | _17 -> T)`;;

(* pure e means e can neither raise an exception nor side-effect the
   state *)
let pure_def = cake_define_list
  [`pure (Var _18 _19:closLang_exp) <=> T`;
   `pure (If _20 e1 e2 e3:closLang_exp) <=> pure e1 /\ pure e2 /\
  pure e3`;
   `pure (Let _21 es e2:closLang_exp) <=> EVERY pure es /\ pure e2`;
   `pure (Raise _22 _23:closLang_exp) <=> F`;
   `pure (Handle _24 e1 e2:closLang_exp) <=> pure e1`;
   `pure (closLang_Tick _25 _26) <=> F`;
   `pure (closLang_Call _27 _28 _29 _30) <=> F`;
   `pure (App _31 _32 _33 _34:closLang_exp) <=> F`;
   `pure (closLang_Fn _35 _36 _37 _38 _39) <=> T`;
   `pure (Letrec _40 _41 _42 _43 x:closLang_exp) <=> pure x`;
   `pure (closLang_Op _44 opn es) <=> EVERY pure es /\
  closLang_pure_op opn`];;

(* used in proofs about closLang, BVL, BVI and dataLang *)
let assign_get_code_label_def = cake_define
  `assign_get_code_label x =
        match x with
          closLang_Label x -> {x}
        | x -> {}`;;

new_type_abbrev("clos_prog",`: closLang_exp
   list#(num#num#closLang_exp) list`);;

(* HOL4 type abbreviation (expanded in the port):
     clos_cc = 'c -> clos_prog -> (word8 list # word64 list # 'c) option
       *)
