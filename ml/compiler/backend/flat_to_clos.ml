(* ======================================================== *)
(*  flat_to_clos: ported from HOL4's
    compiler/backend/flat_to_closScript.sml  *)
(* ======================================================== *)

(*
  Compilation from flatLang to closLang. This compiler phase converts
  explicit variable names of flatLang to de Bruijn indexing of
  closLang. It also makes all division-by-zero and out-of-bounds
  exceptions raised explicitly.
*)

needs "basis/pure/mlstring.ml";;
needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/clos_interp.ml";;
needs "compiler/backend/flatLang.ml";;
needs "compiler/backend/reg_alloc/reg_alloc.ml";;
needs "lib/ternaryComparisons.ml";;
needs "semantics/ast.ml";;
needs "semantics/fpSem.ml";;
needs "semantics/semanticPrimitives.ml";;

let dest_pat_def = cake_define
  `dest_pat x1 =
      match x1 with
        [(flatLang_Pvar v,h)] -> SOME ((v:mlstring),h)
      | _1 -> NONE`;;

let compile_lit_def = cake_define
  `compile_lit t l =
     closLang_Op t
      (match l with ast_IntLit i -> closLang_IntOp (closLang_Const
        i) | ast_Char c -> closLang_IntOp (closLang_Const (&(ORD c)))
        | ast_StrLit s -> closLang_BlockOp (closLang_Constant
        (ConstStr s)) | ast_Word8 b -> closLang_IntOp (closLang_Const
        (&(w2n b))) | ast_Word64 w -> closLang_BlockOp
        (closLang_Constant (ConstWord64 w)) | ast_Float64 w ->
        closLang_BlockOp (closLang_Constant (ConstWord64 w))) []`;;

let arg1_def = cake_define
  `flat_to_clos_arg1 xs f =
     (match xs with [x] -> f x | _2 -> closLang_Let
       backend_common_None xs (closLang_Var backend_common_None 0))`;;

let arg2_def = cake_define
  `flat_to_clos_arg2 xs f =
     (match xs with [x; y] -> f x y | _3 -> closLang_Let
       backend_common_None xs (closLang_Var backend_common_None 0))`;;

(* HOL4 ML code, not ported:
fun var_fun m n = ``closLang$Var t ^(numSyntax.term_of_int(m-n))``;
*)

(* HOL4 ML code, not ported:
fun check1 tm var =
``(If t (Op t (IntOp Less) [Op t (IntOp (Const 0)) []; ^(var 2)]) (Raise
  t (Op t (BlockOp (Cons subscript_tag)) []))
  (If t (Op t (IntOp Less) [Op t (IntOp (Const 0)) []; ^(var 1)]) (Raise
    t (Op t (BlockOp (Cons subscript_tag)) []))
  (If t (Op t (MemOp (BoundsCheckByte T)) [Op t (IntOp Add) [^(var 2);
    ^(var 1)]; ^(var 0)]) ^tm
  (Raise t (Op t (BlockOp (Cons subscript_tag)) [])))))``;
*)

(* HOL4 ML code, not ported:
val checkT = check1
  ``(closLang$Op t (MemOp (CopyByte T)) [Var t 0; Var t 1; Var t 2])``
    (var_fun 2);
*)

(* HOL4 ML code, not ported:
val checkF = check1
``(If t (Op t (IntOp Less) [Op t (IntOp (Const 0)) []; Var t 0]) (Raise
  t (Op t (BlockOp (Cons subscript_tag)) []))
  (If t (Op t (MemOp (BoundsCheckByte T)) [Op t (IntOp Add) [Var t 2;
    Var t 0]; Var t 1])
     (Op t (MemOp (CopyByte F)) [Var t 0; Var t 1; Var t 2; Var t 3; Var
       t 4])
     (Raise t (Op t (BlockOp (Cons subscript_tag)) []))))`` (var_fun 4);
*)

let CopyByteStr_def = cake_define
  `CopyByteStr t = checkT`;;

let CopyByteAw8_def = cake_define
  `CopyByteAw8 t = checkF`;;

let compile_arith_def = cake_define
  `compile_arith t (a:ast_arith) ty xs =
     (match ty with ast_IntT -> (match a with closLang_Add ->
       closLang_Op t (closLang_IntOp closLang_Add) xs | closLang_Sub ->
       closLang_Op t (closLang_IntOp closLang_Sub) xs | ast_Mul ->
       closLang_Op t (closLang_IntOp closLang_Mult) xs | closLang_Div ->
       flatLang_Let t xs (flatLang_If t (closLang_Op t (closLang_BlockOp
       (EQUAL)) [closLang_Var t 0; closLang_Op t (closLang_IntOp
       (closLang_Const 0)) []])
                              (flatLang_Raise t (closLang_Op t
                                (closLang_BlockOp (closLang_Cons
                                div_tag)) []))
                              (closLang_Op t (closLang_IntOp
                                closLang_Div) [closLang_Var t 0;
                                closLang_Var t 1])) | closLang_Mod ->
                                flatLang_Let t xs (flatLang_If t
                                (closLang_Op t (closLang_BlockOp
                                (EQUAL)) [closLang_Var t 0; closLang_Op
                                t (closLang_IntOp (closLang_Const 0))
                                []])
                              (flatLang_Raise t (closLang_Op t
                                (closLang_BlockOp (closLang_Cons
                                div_tag)) []))
                              (closLang_Op t (closLang_IntOp
                                closLang_Mod) [closLang_Var t 0;
                                closLang_Var t 1])) | _4 ->
                                flatLang_Let backend_common_None xs
                                (closLang_Var backend_common_None 0))
                                | ast_Float64T -> (match a with
                                ast_Abs -> closLang_Op t
                                (closLang_WordOp (FP_uop
                                fpSem_FP_Abs)) xs | ast_Neg ->
                                closLang_Op t (closLang_WordOp
                                (FP_uop fpSem_FP_Neg)) xs | ast_Sqrt
                                -> closLang_Op t (closLang_WordOp
                                (FP_uop fpSem_FP_Sqrt)) xs |
                                closLang_Add -> closLang_Op t
                                (closLang_WordOp (FP_bop
                                fpSem_FP_Add)) xs | closLang_Sub ->
                                closLang_Op t (closLang_WordOp
                                (FP_bop fpSem_FP_Sub)) xs | ast_Mul
                                -> closLang_Op t (closLang_WordOp
                                (FP_bop fpSem_FP_Mul)) xs |
                                closLang_Div -> closLang_Op t
                                (closLang_WordOp (FP_bop
                                fpSem_FP_Div)) xs | ast_FMA ->
                                closLang_Op t (closLang_WordOp
                                (FP_top FP_Fma)) xs | _5 ->
                                flatLang_Let backend_common_None xs
                                (closLang_Var backend_common_None 0))
                                | ast_WordT ws -> (match a with
                                closLang_Add -> closLang_Op t
                                (closLang_WordOp (WordOpw ws
                                closLang_Add)) xs | closLang_Sub ->
                                closLang_Op t (closLang_WordOp
                                (WordOpw ws closLang_Sub)) xs |
                                ast_And -> closLang_Op t
                                (closLang_WordOp (WordOpw ws
                                backend_common_Andw)) xs | ast_Or ->
                                closLang_Op t (closLang_WordOp
                                (WordOpw ws backend_common_Orw)) xs |
                                backend_common_Xor -> closLang_Op t
                                (closLang_WordOp (WordOpw ws
                                backend_common_Xor)) xs | _6 ->
                                flatLang_Let backend_common_None xs
                                (closLang_Var backend_common_None 0))
                                | ast_BoolT -> closLang_Op t
                                (closLang_BlockOp closLang_BoolNot)
                                xs | _7 -> flatLang_Let
                                backend_common_None xs (closLang_Var
                                backend_common_None 0))`;;

let compile_op_def = cake_define
  `flat_to_clos_compile_op t flatLang_op xs =
     (match flatLang_op with flatLang_TagLenEq tag n -> closLang_Op t
       (closLang_BlockOp (flatLang_TagLenEq tag n)) xs | flatLang_LenEq
       n -> closLang_Op t (closLang_BlockOp (flatLang_LenEq n)) xs |
       flatLang_El n -> flat_to_clos_arg1 xs (\x. closLang_Op t
       (closLang_MemOp flatLang_El) [closLang_Op backend_common_None
       (closLang_IntOp (closLang_Const (&n))) []; x]) |
       flatLang_GlobalVarAlloc n -> flatLang_Let t xs (closLang_Op t
       (closLang_GlobOp AllocGlobal) [closLang_Op t (closLang_IntOp
       (closLang_Const (&n))) []]) | flatLang_GlobalVarInit n ->
       closLang_Op t (closLang_GlobOp (SetGlobal (n + 1))) xs |
       flatLang_GlobalVarLookup n -> closLang_Op t (closLang_GlobOp
       (Global (n + 1))) xs | flatLang_Id -> flat_to_clos_arg1 xs (\x.
       x) | flatLang_Src ast_Opapp -> flat_to_clos_arg2 xs (\x f.
       closLang_App t NONE f [x]) | flatLang_Src ast_Opassign ->
       flat_to_clos_arg2 xs (\x y. closLang_Op t (closLang_MemOp
       closLang_Update) [x; closLang_Op backend_common_None
       (closLang_IntOp (closLang_Const 0)) []; y]) | flatLang_Src
       ast_Opref -> closLang_Op t (closLang_MemOp closLang_Ref) xs |
       flatLang_Src closLang_ConfigGC -> closLang_Op t (closLang_MemOp
       closLang_ConfigGC) xs | flatLang_Src ast_Equality -> closLang_Op
       t (closLang_BlockOp (EQUAL)) xs | flatLang_Src (closLang_FFI n)
       -> closLang_Op t (closLang_FFI n) xs | flatLang_Src
       closLang_ListAppend -> closLang_Op t (closLang_BlockOp
       closLang_ListAppend) xs | flatLang_Src ast_Vlength -> closLang_Op
       t (closLang_BlockOp closLang_LengthBlock) xs | flatLang_Src
       ast_Alength -> closLang_Op t (closLang_MemOp closLang_Length) xs
       | flatLang_Src ast_Implode -> closLang_Op t (closLang_MemOp
       closLang_FromListByte) xs | flatLang_Src ast_Explode ->
       closLang_Op t (closLang_MemOp closLang_ToListByte) xs |
       flatLang_Src ast_Strlen -> closLang_Op t (closLang_MemOp
       closLang_LengthByteVec) xs | flatLang_Src ast_Strcat ->
       closLang_Op t (closLang_MemOp closLang_ConcatByteVec) xs |
       flatLang_Src ast_CopyStrStr -> flatLang_Let t xs (CopyByteStr t)
       | flatLang_Src ast_CopyStrAw8 -> flatLang_Let t xs (CopyByteAw8
       t) | flatLang_Src ast_CopyAw8Str -> flatLang_Let t xs
       (CopyByteStr t) | flatLang_Src ast_CopyAw8Aw8 -> flatLang_Let t
       xs (CopyByteAw8 t) | flatLang_Src ast_XorAw8Str_unsafe ->
       closLang_Op t (closLang_MemOp closLang_XorByte) xs | flatLang_Src
       ast_VfromList -> closLang_Op t (closLang_BlockOp
       (closLang_FromList 0)) xs | flatLang_Src (ast_Test test test_ty)
       ->
          (match test_ty with ast_BoolT -> closLang_Op t
            (closLang_BlockOp (closLang_BoolTest test)) xs | ast_CharT
            -> closLang_Op t (closLang_WordOp (WordTest ast_W8 test)) xs
            | ast_WordT ast_W8 -> closLang_Op t (closLang_WordOp
            (WordTest ast_W8 test)) xs | ast_IntT -> (match test with
            ast_Compare ast_Lt -> closLang_Op t (closLang_IntOp (LESS))
            xs | ast_Compare ast_Leq -> closLang_Op t (closLang_IntOp
            closLang_LessEq) xs | ast_Compare ast_Gt -> closLang_Op t
            (closLang_IntOp (GREATER)) xs | ast_Compare ast_Geq ->
            closLang_Op t (closLang_IntOp closLang_GreaterEq) xs | _8 ->
            closLang_Op t (closLang_BlockOp (EQUAL)) xs) | ast_Float64T
            -> (match test with ast_Compare ast_Lt -> closLang_Op t
            (closLang_WordOp (FP_cmp FP_Less)) xs | ast_Compare ast_Leq
            -> closLang_Op t (closLang_WordOp (FP_cmp FP_LessEqual)) xs
            | ast_Compare ast_Gt -> closLang_Op t (closLang_WordOp
            (FP_cmp FP_Greater)) xs | ast_Compare ast_Geq -> closLang_Op
            t (closLang_WordOp (FP_cmp FP_GreaterEqual)) xs | _9 ->
            closLang_Op t (closLang_WordOp (FP_cmp FP_Equal)) xs) |
            ast_StrT -> (match test with ast_Compare opb -> closLang_Op
            t (closLang_MemOp (closLang_StringCmp F opb)) xs |
            ast_AltCompare opb -> closLang_Op t (closLang_MemOp
            (closLang_StringCmp T opb)) xs | _10 -> closLang_Op t
            (closLang_BlockOp (EQUAL)) xs) | _11 -> closLang_Op t
            (closLang_BlockOp (EQUAL)) xs) | flatLang_Src ast_Aw8length
            -> closLang_Op t (closLang_MemOp closLang_LengthByte) xs |
            flatLang_Src ast_AallocFixed -> closLang_Op t
            (closLang_MemOp closLang_Ref) xs | flatLang_Src ast_Aalloc
            -> flatLang_Let t xs (flatLang_If t (closLang_Op t
            (closLang_IntOp (LESS)) [closLang_Op t (closLang_IntOp
            (closLang_Const 0)) []; closLang_Var t 1])
                              (flatLang_Raise t (closLang_Op t
                                (closLang_BlockOp (closLang_Cons
                                subscript_tag)) []))
                              (closLang_Op t (closLang_MemOp
                                closLang_RefArray) [closLang_Var t 0;
                                closLang_Var t 1])) | flatLang_Src
                                ast_Aw8alloc -> flatLang_Let t xs
                                (flatLang_If t (closLang_Op t
                                (closLang_IntOp (LESS)) [closLang_Op t
                                (closLang_IntOp (closLang_Const 0)) [];
                                closLang_Var t 1])
                              (flatLang_Raise t (closLang_Op t
                                (closLang_BlockOp (closLang_Cons
                                subscript_tag)) []))
                              (closLang_Op t (closLang_MemOp
                                (closLang_RefByte F)) [closLang_Var t 0;
                                closLang_Var t 1])) | flatLang_Src
                                ast_Vsub -> flatLang_Let t xs
                                (flatLang_If t (closLang_Op t
                                (closLang_BlockOp
                                closLang_BoundsCheckBlock) [closLang_Var
                                t 0; closLang_Var t 1])
                              (closLang_Op t (closLang_MemOp
                                flatLang_El) [closLang_Var t 0;
                                closLang_Var t 1])
                              (flatLang_Raise t (closLang_Op t
                                (closLang_BlockOp (closLang_Cons
                                subscript_tag)) []))) | flatLang_Src
                                ast_Vsub_unsafe -> closLang_Op t
                                (closLang_MemOp flatLang_El) xs |
                                flatLang_Src ast_Asub -> flatLang_Let t
                                xs (flatLang_If t (closLang_Op t
                                (closLang_MemOp
                                closLang_BoundsCheckArray) [closLang_Var
                                t 0; closLang_Var t 1])
                              (closLang_Op t (closLang_MemOp
                                flatLang_El) [closLang_Var t 0;
                                closLang_Var t 1])
                              (flatLang_Raise t (closLang_Op t
                                (closLang_BlockOp (closLang_Cons
                                subscript_tag)) []))) | flatLang_Src
                                ast_Asub_unsafe -> closLang_Op t
                                (closLang_MemOp flatLang_El) xs |
                                flatLang_Src ast_Aupdate -> flatLang_Let
                                t xs (flatLang_If t (closLang_Op t
                                (closLang_MemOp
                                closLang_BoundsCheckArray) [closLang_Var
                                t 1; closLang_Var t 2])
                              (closLang_Op t (closLang_MemOp
                                closLang_Update) [closLang_Var t 0;
                                closLang_Var t 1; closLang_Var t 2])
                              (flatLang_Raise t (closLang_Op t
                                (closLang_BlockOp (closLang_Cons
                                subscript_tag)) []))) | flatLang_Src
                                ast_Aupdate_unsafe -> closLang_Op t
                                (closLang_MemOp closLang_Update) xs |
                                flatLang_Src ast_Aw8sub -> flatLang_Let
                                t xs (flatLang_If t (closLang_Op t
                                (closLang_MemOp
                                (closLang_BoundsCheckByte F))
                                [closLang_Var t 0; closLang_Var t 1])
                              (closLang_Op t (closLang_MemOp
                                closLang_DerefByte) [closLang_Var t 0;
                                closLang_Var t 1])
                              (flatLang_Raise t (closLang_Op t
                                (closLang_BlockOp (closLang_Cons
                                subscript_tag)) []))) | flatLang_Src
                                ast_Aw8sub_unsafe -> closLang_Op t
                                (closLang_MemOp closLang_DerefByte) xs |
                                flatLang_Src ast_Aw8update ->
                                flatLang_Let t xs (flatLang_If t
                                (closLang_Op t (closLang_MemOp
                                (closLang_BoundsCheckByte F))
                                [closLang_Var t 1; closLang_Var t 2])
                              (closLang_Op t (closLang_MemOp
                                closLang_UpdateByte) [closLang_Var t 0;
                                closLang_Var t 1; closLang_Var t 2])
                              (flatLang_Raise t (closLang_Op t
                                (closLang_BlockOp (closLang_Cons
                                subscript_tag)) []))) | flatLang_Src
                                ast_Aw8update_unsafe -> closLang_Op t
                                (closLang_MemOp closLang_UpdateByte) xs
                                | flatLang_Src ast_Strsub ->
                                flatLang_Let t xs (flatLang_If t
                                (closLang_Op t (closLang_MemOp
                                (closLang_BoundsCheckByte F))
                                [closLang_Var t 0; closLang_Var t 1])
                              (closLang_Op t (closLang_MemOp
                                closLang_DerefByteVec) [closLang_Var t
                                0; closLang_Var t 1])
                              (flatLang_Raise t (closLang_Op t
                                (closLang_BlockOp (closLang_Cons
                                subscript_tag)) []))) | flatLang_Src
                                (ast_Shift x1 x2 x3) -> closLang_Op t
                                (closLang_WordOp (WordShift x1 x2 x3))
                                xs | flatLang_Src ast_Eval ->
                                closLang_Op t closLang_Install xs |
                                flatLang_Src (closLang_ThunkOp
                                flatLang_op) -> closLang_Op t
                                (closLang_ThunkOp flatLang_op) xs |
                                flatLang_Src (ast_Arith a ty) ->
                                compile_arith t a ty xs | flatLang_Src
                                (ast_FromTo (ast_WordT ast_W8) ast_IntT)
                                -> flat_to_clos_arg1 xs (\x. x) |
                                flatLang_Src (ast_FromTo (ast_WordT
                                closLang_W64) ast_IntT) -> closLang_Op t
                                (closLang_WordOp WordToInt) xs |
                                flatLang_Src (ast_FromTo ast_IntT
                                (ast_WordT ast_W8)) -> flat_to_clos_arg1
                                xs (\x. closLang_Op t (closLang_IntOp
                                closLang_Mod) [closLang_Op t
                                (closLang_IntOp (closLang_Const 256))
                                []; x]) | flatLang_Src (ast_FromTo
                                ast_IntT (ast_WordT closLang_W64)) ->
                                closLang_Op t (closLang_WordOp
                                WordFromInt) xs | flatLang_Src
                                (ast_FromTo ast_IntT ast_CharT) ->
                                flatLang_Let t xs (flatLang_If t
                                (closLang_Op t (closLang_IntOp (LESS))
                                [closLang_Op backend_common_None
                                (closLang_IntOp (closLang_Const 0)) [];
                                closLang_Var t 0])
                         (flatLang_Raise t (closLang_Op t
                           (closLang_BlockOp (closLang_Cons chr_tag))
                           []))
                         (flatLang_If t (closLang_Op t
                           (closLang_IntOp (LESS)) [closLang_Var t 0;
                           closLang_Op backend_common_None
                           (closLang_IntOp (closLang_Const 255)) []])
                           (flatLang_Raise t (closLang_Op t
                             (closLang_BlockOp (closLang_Cons chr_tag))
                             []))
                           (closLang_Var t 0))) | flatLang_Src
                             (ast_FromTo ast_Float64T (ast_WordT
                             closLang_W64)) -> flatLang_Let
                             backend_common_None xs (closLang_Var
                             backend_common_None 0) | flatLang_Src
                             (ast_FromTo (ast_WordT closLang_W64)
                             ast_Float64T) -> flatLang_Let
                             backend_common_None xs (closLang_Var
                             backend_common_None 0) | flatLang_Src
                             _12 -> flatLang_Let backend_common_None
                             xs (closLang_Var backend_common_None 0))`;;

let join_strings_def = cake_define
  `join_strings (x:mlstring) y =
     (if strlen x = 0 then y else mlstring_concat [x; implode "_";
       y])`;;

let dest_nop_def = cake_define
  `dest_nop flatLang_op e =
     (if flatLang_op = flatLang_Src (ast_FromTo ast_IntT (ast_WordT
       ast_W8)) then
       (match e with [flatLang_App _13 op1 [x]] -> (if op1 =
         flatLang_Src (ast_FromTo ast_CharT ast_IntT) then SOME x else
         NONE) | _14 -> NONE) else if flatLang_op = flatLang_Src
         (ast_FromTo ast_IntT ast_CharT) then
       (match e with [flatLang_App _15 op1 [x]] -> (if op1 =
         flatLang_Src (ast_FromTo (ast_WordT ast_W8) ast_IntT) then
         SOME x else NONE) | _16 -> NONE) else NONE)`;;

let dest_Constant_def = cake_define
  `flat_to_clos_dest_Constant x1 =
      match x1 with
        (closLang_Op t (closLang_BlockOp (closLang_Constant c)) [])
          -> SOME c
      | (closLang_Op t (closLang_IntOp (closLang_Const i)) []) ->
        SOME (ConstInt i)
      | (closLang_Op t (closLang_BlockOp (closLang_Cons n)) []) ->
        SOME (ConstCons n [])
      | _17 -> NONE`;;

let dest_Constants_def = cake_define
  `dest_Constants [] = SOME [] /\
   dest_Constants (c :: cs) =
     (match flat_to_clos_dest_Constant c with NONE -> NONE | SOME
       x -> (match dest_Constants cs with NONE -> NONE | SOME xs ->
       SOME (x :: xs)))`;;

let SmartCons_def = cake_define
  `SmartCons t tag xs =
     (if NULL xs then closLang_Op t (closLang_BlockOp (closLang_Cons
       tag)) [] else
     match dest_Constants xs with NONE -> closLang_Op t
       (closLang_BlockOp (closLang_Cons tag)) xs | SOME cs ->
       closLang_Op t (closLang_BlockOp (closLang_Constant (ConstCons
       tag (REVERSE cs)))) [])`;;

(* HOL4 termination: \\ rw [] \\ `!funs f v x. MEM (f,v,x) funs ==>
   exp_size x < flatLang$exp1_size funs` by (Induct \\ fs [] \\ rw []
   \\ fs [flatLangTheory.exp_size_def] \\ res_tac \\ fs []) \\
   res_tac \\ fs [dest_pat_thm] \\ fs [flatLangTheory.exp_size_def]
   \\ gvs [dest_nop_thm] \\ fs [flatLangTheory.exp_size_def] *)
let compile_def = cake_define_wf
  `MEASURE (exp6_size o SND)`
  `(flat_to_clos_compile m [] = []) /\
   (flat_to_clos_compile m (x :: y :: xs) = flat_to_clos_compile m
     [x] ++ flat_to_clos_compile m (y :: xs)) /\
   (flat_to_clos_compile m [flatLang_Raise t e] = [closLang_Raise t
     (HD (flat_to_clos_compile m [e]))]) /\
   (flat_to_clos_compile m [flatLang_Lit t l] = [compile_lit t l]) /\
   (flat_to_clos_compile m [flatLang_Var_local t v] = [closLang_Var t
     (indexedLists_findi (SOME v) m)]) /\
   (flat_to_clos_compile m [flatLang_Con t n es] =
      (let tag = (match n with SOME (t,_18) -> t | _19 -> 0) in
        [SmartCons t tag (flat_to_clos_compile m (REVERSE es))])) /\
   (flat_to_clos_compile m [flatLang_App t flatLang_op es] =
      (match dest_nop flatLang_op es with SOME e ->
        flat_to_clos_compile m [e] | NONE -> [flat_to_clos_compile_op t
        flatLang_op (flat_to_clos_compile m (REVERSE es))])) /\
   (flat_to_clos_compile m [flatLang_Fun t v e] =
      [closLang_Fn t NONE NONE 1 (HD (flat_to_clos_compile (SOME v ::
        m) [e]))]) /\
   (flat_to_clos_compile m [flatLang_If t x1 x2 x3] =
      [flatLang_If t (HD (flat_to_clos_compile m [x1]))
            (HD (flat_to_clos_compile m [x2]))
            (HD (flat_to_clos_compile m [x3]))]) /\
   (flat_to_clos_compile m [flatLang_Let t vo e1 e2] =
      [flatLang_Let t (flat_to_clos_compile m [e1]) (HD
        (flat_to_clos_compile (vo :: m) [e2]))]) /\
   (flat_to_clos_compile m [flatLang_Mat t e pes] = [closLang_Op t
     (closLang_IntOp (closLang_Const 0)) []]) /\
   (flat_to_clos_compile m [flatLang_Handle t e pes] =
      (match dest_pat pes with SOME (v,h) -> [flatLang_Handle t (HD
        (flat_to_clos_compile m [e])) (HD (flat_to_clos_compile (SOME v
        :: m) [h]))] | _20 -> flat_to_clos_compile m [e])) /\
   (flat_to_clos_compile m [flatLang_Letrec t funs e] =
      (let new_m = MAP (\n. SOME (FST n)) funs ++ m in
        [flatLang_Letrec (MAP (\n. join_strings t (FST n)) funs) NONE
          NONE
           (MAP (\(f,v,x). (1,HD (flat_to_clos_compile (SOME v ::
             new_m) [x]))) funs)
           (HD (flat_to_clos_compile new_m [e]))]))`;;

let compile_decs_def = cake_define
  `flat_to_clos_compile_decs [] = [] /\
   flat_to_clos_compile_decs (e :: xs) = flat_to_clos_compile []
     [e] ++ flat_to_clos_compile_decs xs`;;

let compile_prog_def = cake_define
  `flat_to_clos_compile_prog xs =
     attach_interpreter (flat_to_clos_compile_decs xs)`;;

let inc_compile_decs_def = cake_define
  `inc_compile_decs decs =
     (let xs = flat_to_clos_compile_decs decs ++
       flat_to_clos_compile_decs [flatLang_Con backend_common_None NONE
       []] in
       (insert_interp xs,[]))`;;
