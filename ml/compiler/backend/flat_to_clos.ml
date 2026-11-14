(* ======================================================== *)
(*  flat_to_clos: ported from HOL4's
    compiler/backend/flat_to_closScript.sml
    A definition theory, with 17 definitions and 9 theorems.  Needed
    by backend.ml, backendProof.ml, flat_to_closProof.ml and
    source_evalProof.ml.  *)
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
needs "semantics/fpSem.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "flat_to_clos"
  ["backend_common"; "closLang"; "clos_interp"; "flatLang"];;

let _ = do_list hide_constant ["pmatch"];;

let dest_pat_def = new_definition
  `dest_pat x1 =
      match x1 with
        [(flatLang_Pvar v:flatLang_pat),h] -> SOME ((v:mlstring),h)
      | _1 -> NONE`;;

let dest_pat_pmatch = prove
 (`dest_pat x =
     (match x with [(flatLang_Pvar v,h)] -> SOME ((v:mlstring),h) |
       _2 -> NONE)`,
  CHEAT_TAC);;

let dest_pat_thm = prove
 (`dest_pat pes = SOME (p_1,p_2) <=> pes = [(flatLang_Pvar p_1,p_2)]`,
  CHEAT_TAC);;

let compile_lit_def = new_definition
  `compile_lit t l =
     closLang_Op t
      (match l with ast_IntLit i -> closLang_IntOp (closLang_Const
        i) | ast_Char c -> closLang_IntOp (closLang_Const (&(ORD c)))
        | ast_StrLit s -> closLang_BlockOp (closLang_Constant
        (ConstStr s)) | ast_Word8 b -> closLang_IntOp (closLang_Const
        (&(w2n b))) | ast_Word64 w -> closLang_BlockOp
        (closLang_Constant (ConstWord64 w)) | ast_Float64 w ->
        closLang_BlockOp (closLang_Constant (ConstWord64 w))) []`;;

let flat_to_clos_arg1_def = new_definition
  `flat_to_clos_arg1 xs f =
     (match xs with [x] -> f x | _3 -> closLang_Let
       backend_common_None xs (closLang_Var backend_common_None 0))`;;

let arg1_pmatch = prove
 (`flat_to_clos_arg1 xs f =
     (match xs with [x] -> f x | _4 -> closLang_Let
       backend_common_None xs (closLang_Var backend_common_None 0))`,
  CHEAT_TAC);;

let flat_to_clos_arg2_def = new_definition
  `flat_to_clos_arg2 xs f =
     (match xs with [x; y] -> f x y | _5 -> closLang_Let
       backend_common_None xs (closLang_Var backend_common_None 0))`;;

(* arg2_pmatch *)
let flat_to_clos_arg2_pmatch = prove
 (`flat_to_clos_arg2 xs f =
     (match xs with [x; y] -> f x y | _6 -> closLang_Let
       backend_common_None xs (closLang_Var backend_common_None 0))`,
  CHEAT_TAC);;

let var_fun m n =
  list_mk_icomb "closLang_Var" [`t:tra`; mk_small_numeral (m - n)];;

let check1 tm var =
  vsubst [var 2,`v2:closLang_exp`; var 1,`v1:closLang_exp`;
          var 0,`v0:closLang_exp`; tm,`tm:closLang_exp`]
  `closLang_If t
     (closLang_Op t (closLang_IntOp closLang_Less)
        [closLang_Op t (closLang_IntOp (closLang_Const (&0))) [];
         v2])
     (closLang_Raise t (closLang_Op t
        (closLang_BlockOp (closLang_Cons subscript_tag)) []))
     (closLang_If t
       (closLang_Op t (closLang_IntOp closLang_Less)
          [closLang_Op t (closLang_IntOp (closLang_Const (&0))) [];
           v1])
       (closLang_Raise t (closLang_Op t
          (closLang_BlockOp (closLang_Cons subscript_tag)) []))
       (closLang_If t
         (closLang_Op t (closLang_MemOp (closLang_BoundsCheckByte T))
            [closLang_Op t (closLang_IntOp closLang_Add) [v2; v1];
             v0])
         tm
         (closLang_Raise t (closLang_Op t
            (closLang_BlockOp (closLang_Cons subscript_tag))
            []))))`;;

let checkT =
  check1 `closLang_Op t (closLang_MemOp (closLang_CopyByte T))
            [closLang_Var t 0; closLang_Var t 1; closLang_Var t 2]`
         (var_fun 2);;

let checkF =
  check1
  `closLang_If t
     (closLang_Op t (closLang_IntOp closLang_Less)
        [closLang_Op t (closLang_IntOp (closLang_Const (&0))) [];
         closLang_Var t 0])
     (closLang_Raise t (closLang_Op t
        (closLang_BlockOp (closLang_Cons subscript_tag)) []))
     (closLang_If t
       (closLang_Op t (closLang_MemOp (closLang_BoundsCheckByte T))
          [closLang_Op t (closLang_IntOp closLang_Add)
             [closLang_Var t 2; closLang_Var t 0];
           closLang_Var t 1])
       (closLang_Op t (closLang_MemOp (closLang_CopyByte F))
          [closLang_Var t 0; closLang_Var t 1; closLang_Var t 2;
           closLang_Var t 3; closLang_Var t 4])
       (closLang_Raise t (closLang_Op t
          (closLang_BlockOp (closLang_Cons subscript_tag)) [])))`
  (var_fun 4);;

let CopyByteStr_def = new_definition
  (mk_eq (`(CopyByteStr (t:tra)):closLang_exp`,checkT));;

let CopyByteAw8_def = new_definition
  (mk_eq (`(CopyByteAw8 (t:tra)):closLang_exp`,checkF));;

let compile_arith_def = new_definition
  `compile_arith t (a:ast_arith) ty xs =
     (match ty with ast_IntT -> (match a with ast_Add -> closLang_Op
       t (closLang_IntOp closLang_Add) xs | ast_Sub -> closLang_Op t
       (closLang_IntOp closLang_Sub) xs | ast_Mul -> closLang_Op t
       (closLang_IntOp closLang_Mult) xs | ast_Div -> closLang_Let t xs
       (closLang_If t (closLang_Op t (closLang_BlockOp closLang_Equal)
       [closLang_Var t 0; closLang_Op t (closLang_IntOp (closLang_Const
       (&0))) []])
                              (closLang_Raise t (closLang_Op t
                                (closLang_BlockOp (closLang_Cons
                                div_tag)) []))
                              (closLang_Op t (closLang_IntOp
                                closLang_Div) [closLang_Var t 0;
                                closLang_Var t 1])) | ast_Mod ->
                                closLang_Let t xs (closLang_If t
                                (closLang_Op t (closLang_BlockOp
                                closLang_Equal) [closLang_Var t 0;
                                closLang_Op t (closLang_IntOp
                                (closLang_Const (&0))) []])
                              (closLang_Raise t (closLang_Op t
                                (closLang_BlockOp (closLang_Cons
                                div_tag)) []))
                              (closLang_Op t (closLang_IntOp
                                closLang_Mod) [closLang_Var t 0;
                                closLang_Var t 1])) | _7 ->
                                closLang_Let backend_common_None xs
                                (closLang_Var backend_common_None 0))
                                | ast_Float64T -> (match a with
                                ast_Abs -> closLang_Op t
                                (closLang_WordOp (FP_uop
                                fpSem_FP_Abs)) xs | ast_Neg ->
                                closLang_Op t (closLang_WordOp
                                (FP_uop fpSem_FP_Neg)) xs | ast_Sqrt
                                -> closLang_Op t (closLang_WordOp
                                (FP_uop fpSem_FP_Sqrt)) xs | ast_Add
                                -> closLang_Op t (closLang_WordOp
                                (FP_bop fpSem_FP_Add)) xs | ast_Sub
                                -> closLang_Op t (closLang_WordOp
                                (FP_bop fpSem_FP_Sub)) xs | ast_Mul
                                -> closLang_Op t (closLang_WordOp
                                (FP_bop fpSem_FP_Mul)) xs | ast_Div
                                -> closLang_Op t (closLang_WordOp
                                (FP_bop fpSem_FP_Div)) xs | ast_FMA
                                -> closLang_Op t (closLang_WordOp
                                (FP_top FP_Fma)) xs | _8 ->
                                closLang_Let backend_common_None xs
                                (closLang_Var backend_common_None 0))
                                | ast_WordT ws -> (match a with
                                ast_Add -> closLang_Op t
                                (closLang_WordOp (WordOpw ws
                                backend_common_Add)) xs | ast_Sub ->
                                closLang_Op t (closLang_WordOp
                                (WordOpw ws backend_common_Sub)) xs |
                                ast_And -> closLang_Op t
                                (closLang_WordOp (WordOpw ws
                                backend_common_Andw)) xs | ast_Or ->
                                closLang_Op t (closLang_WordOp
                                (WordOpw ws backend_common_Orw)) xs |
                                ast_Xor -> closLang_Op t
                                (closLang_WordOp (WordOpw ws
                                backend_common_Xor)) xs | _9 ->
                                closLang_Let backend_common_None xs
                                (closLang_Var backend_common_None 0))
                                | ast_BoolT -> closLang_Op t
                                (closLang_BlockOp closLang_BoolNot)
                                xs | _10 -> closLang_Let
                                backend_common_None xs (closLang_Var
                                backend_common_None 0))`;;

let flat_to_clos_compile_op_def = new_definition
  `flat_to_clos_compile_op t op xs =
     (match op with flatLang_TagLenEq tag n -> closLang_Op t
       (closLang_BlockOp (closLang_TagLenEq tag n)) xs | flatLang_LenEq
       n -> closLang_Op t (closLang_BlockOp (closLang_LenEq n)) xs |
       flatLang_El n -> flat_to_clos_arg1 xs (\x. closLang_Op t
       (closLang_MemOp closLang_El) [closLang_Op backend_common_None
       (closLang_IntOp (closLang_Const (&n))) []; x]) |
       flatLang_GlobalVarAlloc n -> closLang_Let t xs (closLang_Op t
       (closLang_GlobOp closLang_AllocGlobal) [closLang_Op t
       (closLang_IntOp (closLang_Const (&n))) []]) |
       flatLang_GlobalVarInit n -> closLang_Op t (closLang_GlobOp
       (closLang_SetGlobal (n + 1))) xs | flatLang_GlobalVarLookup n ->
       closLang_Op t (closLang_GlobOp (closLang_Global (n + 1))) xs |
       flatLang_Id -> flat_to_clos_arg1 xs (\x. x) | flatLang_Src
       ast_Opapp -> flat_to_clos_arg2 xs (\x f. closLang_App t NONE f
       [x]) | flatLang_Src ast_Opassign -> flat_to_clos_arg2 xs (\x y.
       closLang_Op t (closLang_MemOp closLang_Update) [x; closLang_Op
       backend_common_None (closLang_IntOp (closLang_Const (&0))) [];
       y]) | flatLang_Src ast_Opref -> closLang_Op t (closLang_MemOp
       closLang_Ref) xs | flatLang_Src ast_ConfigGC -> closLang_Op t
       (closLang_MemOp closLang_ConfigGC) xs | flatLang_Src ast_Equality
       -> closLang_Op t (closLang_BlockOp closLang_Equal) xs |
       flatLang_Src (ast_FFI n) -> closLang_Op t (closLang_FFI n) xs |
       flatLang_Src ast_ListAppend -> closLang_Op t (closLang_BlockOp
       closLang_ListAppend) xs | flatLang_Src ast_Vlength -> closLang_Op
       t (closLang_BlockOp closLang_LengthBlock) xs | flatLang_Src
       ast_Alength -> closLang_Op t (closLang_MemOp closLang_Length) xs
       | flatLang_Src ast_Implode -> closLang_Op t (closLang_MemOp
       closLang_FromListByte) xs | flatLang_Src ast_Explode ->
       closLang_Op t (closLang_MemOp closLang_ToListByte) xs |
       flatLang_Src ast_Strlen -> closLang_Op t (closLang_MemOp
       closLang_LengthByteVec) xs | flatLang_Src ast_Strcat ->
       closLang_Op t (closLang_MemOp closLang_ConcatByteVec) xs |
       flatLang_Src ast_CopyStrStr -> closLang_Let t xs (CopyByteStr t)
       | flatLang_Src ast_CopyStrAw8 -> closLang_Let t xs (CopyByteAw8
       t) | flatLang_Src ast_CopyAw8Str -> closLang_Let t xs
       (CopyByteStr t) | flatLang_Src ast_CopyAw8Aw8 -> closLang_Let t
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
            ast_Compare ast_Lt -> closLang_Op t (closLang_IntOp
            closLang_Less) xs | ast_Compare ast_Leq -> closLang_Op t
            (closLang_IntOp closLang_LessEq) xs | ast_Compare ast_Gt ->
            closLang_Op t (closLang_IntOp closLang_Greater) xs |
            ast_Compare ast_Geq -> closLang_Op t (closLang_IntOp
            closLang_GreaterEq) xs | _11 -> closLang_Op t
            (closLang_BlockOp closLang_Equal) xs) | ast_Float64T ->
            (match test with ast_Compare ast_Lt -> closLang_Op t
            (closLang_WordOp (FP_cmp FP_Less)) xs | ast_Compare ast_Leq
            -> closLang_Op t (closLang_WordOp (FP_cmp FP_LessEqual)) xs
            | ast_Compare ast_Gt -> closLang_Op t (closLang_WordOp
            (FP_cmp FP_Greater)) xs | ast_Compare ast_Geq -> closLang_Op
            t (closLang_WordOp (FP_cmp FP_GreaterEqual)) xs | _12 ->
            closLang_Op t (closLang_WordOp (FP_cmp FP_Equal)) xs) |
            ast_StrT -> (match test with ast_Compare opb -> closLang_Op
            t (closLang_MemOp (closLang_StringCmp F opb)) xs |
            ast_AltCompare opb -> closLang_Op t (closLang_MemOp
            (closLang_StringCmp T opb)) xs | _13 -> closLang_Op t
            (closLang_BlockOp closLang_Equal) xs) | _14 -> closLang_Op t
            (closLang_BlockOp closLang_Equal) xs) | flatLang_Src
            ast_Aw8length -> closLang_Op t (closLang_MemOp
            closLang_LengthByte) xs | flatLang_Src ast_AallocFixed ->
            closLang_Op t (closLang_MemOp closLang_Ref) xs |
            flatLang_Src ast_Aalloc -> closLang_Let t xs (closLang_If t
            (closLang_Op t (closLang_IntOp closLang_Less) [closLang_Op t
            (closLang_IntOp (closLang_Const (&0))) []; closLang_Var t
            1])
                              (closLang_Raise t (closLang_Op t
                                (closLang_BlockOp (closLang_Cons
                                subscript_tag)) []))
                              (closLang_Op t (closLang_MemOp
                                closLang_RefArray) [closLang_Var t 0;
                                closLang_Var t 1])) | flatLang_Src
                                ast_Aw8alloc -> closLang_Let t xs
                                (closLang_If t (closLang_Op t
                                (closLang_IntOp closLang_Less)
                                [closLang_Op t (closLang_IntOp
                                (closLang_Const (&0))) []; closLang_Var
                                t 1])
                              (closLang_Raise t (closLang_Op t
                                (closLang_BlockOp (closLang_Cons
                                subscript_tag)) []))
                              (closLang_Op t (closLang_MemOp
                                (closLang_RefByte F)) [closLang_Var t 0;
                                closLang_Var t 1])) | flatLang_Src
                                ast_Vsub -> closLang_Let t xs
                                (closLang_If t (closLang_Op t
                                (closLang_BlockOp
                                closLang_BoundsCheckBlock) [closLang_Var
                                t 0; closLang_Var t 1])
                              (closLang_Op t (closLang_MemOp
                                closLang_El) [closLang_Var t 0;
                                closLang_Var t 1])
                              (closLang_Raise t (closLang_Op t
                                (closLang_BlockOp (closLang_Cons
                                subscript_tag)) []))) | flatLang_Src
                                ast_Vsub_unsafe -> closLang_Op t
                                (closLang_MemOp closLang_El) xs |
                                flatLang_Src ast_Asub -> closLang_Let t
                                xs (closLang_If t (closLang_Op t
                                (closLang_MemOp
                                closLang_BoundsCheckArray) [closLang_Var
                                t 0; closLang_Var t 1])
                              (closLang_Op t (closLang_MemOp
                                closLang_El) [closLang_Var t 0;
                                closLang_Var t 1])
                              (closLang_Raise t (closLang_Op t
                                (closLang_BlockOp (closLang_Cons
                                subscript_tag)) []))) | flatLang_Src
                                ast_Asub_unsafe -> closLang_Op t
                                (closLang_MemOp closLang_El) xs |
                                flatLang_Src ast_Aupdate -> closLang_Let
                                t xs (closLang_If t (closLang_Op t
                                (closLang_MemOp
                                closLang_BoundsCheckArray) [closLang_Var
                                t 1; closLang_Var t 2])
                              (closLang_Op t (closLang_MemOp
                                closLang_Update) [closLang_Var t 0;
                                closLang_Var t 1; closLang_Var t 2])
                              (closLang_Raise t (closLang_Op t
                                (closLang_BlockOp (closLang_Cons
                                subscript_tag)) []))) | flatLang_Src
                                ast_Aupdate_unsafe -> closLang_Op t
                                (closLang_MemOp closLang_Update) xs |
                                flatLang_Src ast_Aw8sub -> closLang_Let
                                t xs (closLang_If t (closLang_Op t
                                (closLang_MemOp
                                (closLang_BoundsCheckByte F))
                                [closLang_Var t 0; closLang_Var t 1])
                              (closLang_Op t (closLang_MemOp
                                closLang_DerefByte) [closLang_Var t 0;
                                closLang_Var t 1])
                              (closLang_Raise t (closLang_Op t
                                (closLang_BlockOp (closLang_Cons
                                subscript_tag)) []))) | flatLang_Src
                                ast_Aw8sub_unsafe -> closLang_Op t
                                (closLang_MemOp closLang_DerefByte) xs |
                                flatLang_Src ast_Aw8update ->
                                closLang_Let t xs (closLang_If t
                                (closLang_Op t (closLang_MemOp
                                (closLang_BoundsCheckByte F))
                                [closLang_Var t 1; closLang_Var t 2])
                              (closLang_Op t (closLang_MemOp
                                closLang_UpdateByte) [closLang_Var t 0;
                                closLang_Var t 1; closLang_Var t 2])
                              (closLang_Raise t (closLang_Op t
                                (closLang_BlockOp (closLang_Cons
                                subscript_tag)) []))) | flatLang_Src
                                ast_Aw8update_unsafe -> closLang_Op t
                                (closLang_MemOp closLang_UpdateByte) xs
                                | flatLang_Src ast_Strsub ->
                                closLang_Let t xs (closLang_If t
                                (closLang_Op t (closLang_MemOp
                                (closLang_BoundsCheckByte F))
                                [closLang_Var t 0; closLang_Var t 1])
                              (closLang_Op t (closLang_MemOp
                                closLang_DerefByteVec) [closLang_Var t
                                0; closLang_Var t 1])
                              (closLang_Raise t (closLang_Op t
                                (closLang_BlockOp (closLang_Cons
                                subscript_tag)) []))) | flatLang_Src
                                (ast_Shift x1 x2 x3) -> closLang_Op t
                                (closLang_WordOp (WordShift x1 x2 x3))
                                xs | flatLang_Src ast_Eval ->
                                closLang_Op t closLang_Install xs |
                                flatLang_Src (ast_ThunkOp op) ->
                                closLang_Op t (closLang_ThunkOp op) xs |
                                flatLang_Src (ast_Arith a ty) ->
                                compile_arith t a ty xs | flatLang_Src
                                (ast_FromTo (ast_WordT ast_W8) ast_IntT)
                                -> flat_to_clos_arg1 xs (\x. x) |
                                flatLang_Src (ast_FromTo (ast_WordT
                                ast_W64) ast_IntT) -> closLang_Op t
                                (closLang_WordOp WordToInt) xs |
                                flatLang_Src (ast_FromTo ast_IntT
                                (ast_WordT ast_W8)) -> flat_to_clos_arg1
                                xs (\x. closLang_Op t (closLang_IntOp
                                closLang_Mod) [closLang_Op t
                                (closLang_IntOp (closLang_Const (&256)))
                                []; x]) | flatLang_Src (ast_FromTo
                                ast_IntT (ast_WordT ast_W64)) ->
                                closLang_Op t (closLang_WordOp
                                WordFromInt) xs | flatLang_Src
                                (ast_FromTo ast_IntT ast_CharT) ->
                                closLang_Let t xs (closLang_If t
                                (closLang_Op t (closLang_IntOp
                                closLang_Less) [closLang_Op
                                backend_common_None (closLang_IntOp
                                (closLang_Const (&0))) []; closLang_Var
                                t 0])
                         (closLang_Raise t (closLang_Op t
                           (closLang_BlockOp (closLang_Cons chr_tag))
                           []))
                         (closLang_If t (closLang_Op t
                           (closLang_IntOp closLang_Less) [closLang_Var
                           t 0; closLang_Op backend_common_None
                           (closLang_IntOp (closLang_Const (&255))) []])
                           (closLang_Raise t (closLang_Op t
                             (closLang_BlockOp (closLang_Cons chr_tag))
                             []))
                           (closLang_Var t 0))) | flatLang_Src
                             (ast_FromTo ast_Float64T (ast_WordT
                             ast_W64)) -> closLang_Let
                             backend_common_None xs (closLang_Var
                             backend_common_None 0) | flatLang_Src
                             (ast_FromTo (ast_WordT ast_W64)
                             ast_Float64T) -> closLang_Let
                             backend_common_None xs (closLang_Var
                             backend_common_None 0) | flatLang_Src
                             _15 -> closLang_Let backend_common_None
                             xs (closLang_Var backend_common_None 0))`;;

let join_strings_def = new_definition
  `join_strings (x:mlstring) y =
     (if strlen x = 0 then y else mlstring_concat [x; implode "_";
       y])`;;

let dest_nop_def = new_definition
  `dest_nop op e =
     (if op = flatLang_Src (ast_FromTo ast_IntT (ast_WordT ast_W8))
       then
       (match e with [flatLang_App _16 op1 [x]] -> (if op1 =
         flatLang_Src (ast_FromTo ast_CharT ast_IntT) then SOME x else
         NONE) | _17 -> NONE) else if op = flatLang_Src (ast_FromTo
         ast_IntT ast_CharT) then
       (match e with [flatLang_App _18 op1 [x]] -> (if op1 =
         flatLang_Src (ast_FromTo (ast_WordT ast_W8) ast_IntT) then
         SOME x else NONE) | _19 -> NONE) else NONE)`;;

let dest_nop_thm = prove
 (`dest_nop op es = SOME x <=>
     (?t. op = flatLang_Src (ast_FromTo ast_IntT (ast_WordT ast_W8))
       /\ es = [flatLang_App t (flatLang_Src (ast_FromTo ast_CharT
       ast_IntT)) [x]]) \/
     (?t. op = flatLang_Src (ast_FromTo ast_IntT ast_CharT) /\ es =
       [flatLang_App t (flatLang_Src (ast_FromTo (ast_WordT ast_W8)
       ast_IntT)) [x]])`,
  CHEAT_TAC);;

let flat_to_clos_dest_Constant_def = new_definition
  `flat_to_clos_dest_Constant x1 =
      match x1 with
        (closLang_Op t (closLang_BlockOp (closLang_Constant c))
          []:closLang_exp) -> SOME c
      | (closLang_Op t (closLang_IntOp (closLang_Const i)) []) ->
        SOME (ConstInt i)
      | (closLang_Op t (closLang_BlockOp (closLang_Cons n)) []) ->
        SOME (ConstCons n [])
      | _20 -> NONE`;;

(* dest_Constant_pmatch *)
let flat_to_clos_dest_Constant_pmatch = prove
 (`flat_to_clos_dest_Constant xs =
     (match xs with closLang_Op t (closLang_BlockOp
       (closLang_Constant x)) [] -> SOME x | closLang_Op t
       (closLang_IntOp (closLang_Const i)) [] -> SOME (ConstInt i) |
       closLang_Op t (closLang_BlockOp (closLang_Cons n)) [] -> SOME
       (ConstCons n []) | _21 -> NONE)`,
  CHEAT_TAC);;

let dest_Constants_def,dest_Constants_ind = define_rec
  [`dest_Constants [] = SOME []`;
   `dest_Constants (CONS c cs) =
      (match flat_to_clos_dest_Constant c with NONE -> NONE |
          SOME x -> (match dest_Constants cs with NONE -> NONE |
          SOME xs -> SOME (CONS x xs)))`];;

let SmartCons_def = new_definition
  `SmartCons t tag xs =
     (if NULL xs then closLang_Op t (closLang_BlockOp (closLang_Cons
       tag)) [] else
     match dest_Constants xs with NONE -> closLang_Op t
       (closLang_BlockOp (closLang_Cons tag)) xs | SOME cs ->
       closLang_Op t (closLang_BlockOp (closLang_Constant (ConstCons
       tag (REVERSE cs)))) [])`;;

let _ = size_thms "flatLang_exp";;
let flat_to_clos_compile_def,flat_to_clos_compile_ind =
  assume_definition_rec
  "termination (CHEAT_TAC)"
  [`flat_to_clos_compile m [] = []`;
   `flat_to_clos_compile m (CONS x (CONS y xs)) = APPEND
    (flat_to_clos_compile m [x]) (flat_to_clos_compile m (CONS y xs))`;
   `flat_to_clos_compile m [flatLang_Raise t e] = [closLang_Raise t
    (HD (flat_to_clos_compile m [e]))]`;
   `flat_to_clos_compile m [(flatLang_Lit t l:flatLang_exp)] =
    [compile_lit t l]`;
   `flat_to_clos_compile m [flatLang_Var_local t v] = [closLang_Var t
    (indexedLists_findi (SOME v) m)]`;
   `flat_to_clos_compile m [(flatLang_Con t n es:flatLang_exp)] =
         (let tag = (match n with SOME (t,_28) -> t | _29 -> 0) in
           [SmartCons t tag (flat_to_clos_compile m (REVERSE
               es))])`;
   `flat_to_clos_compile m [(flatLang_App t op es:flatLang_exp)] =
         (match dest_nop op es with SOME e ->
             flat_to_clos_compile m [e] | NONE ->
             [flat_to_clos_compile_op t op (flat_to_clos_compile m
             (REVERSE es))])`;
   `flat_to_clos_compile m [(flatLang_Fun t v e:flatLang_exp)] =
         [closLang_Fn t NONE NONE 1 (HD (flat_to_clos_compile
             (CONS (SOME v) m) [e]))]`;
   `flat_to_clos_compile m [(flatLang_If t x1 x2 x3:flatLang_exp)] =
         [closLang_If t (HD (flat_to_clos_compile m [x1]))
               (HD (flat_to_clos_compile m [x2]))
               (HD (flat_to_clos_compile m [x3]))]`;
   `flat_to_clos_compile m [(flatLang_Let t vo e1 e2:flatLang_exp)] =
         [closLang_Let t (flat_to_clos_compile m [e1]) (HD
             (flat_to_clos_compile (CONS vo m) [e2]))]`;
   `flat_to_clos_compile m [(flatLang_Mat t e pes:flatLang_exp)] =
    [closLang_Op t (closLang_IntOp (closLang_Const (&0))) []]`;
   `flat_to_clos_compile m [(flatLang_Handle t e pes:flatLang_exp)] =
         (match dest_pat pes with SOME (v,h) -> [closLang_Handle
             t (HD (flat_to_clos_compile m [e])) (HD
             (flat_to_clos_compile (CONS (SOME v) m) [h]))] | _32 ->
             flat_to_clos_compile m [e])`;
   `flat_to_clos_compile m [(flatLang_Letrec t funs e:flatLang_exp)] =
         (let new_m = APPEND (MAP (\n. SOME (FST n)) funs) m in
           [closLang_Letrec (MAP (\n. join_strings t (FST n)) funs)
               NONE NONE
              (MAP (\(f,v,x). (1,HD (flat_to_clos_compile (CONS
                  (SOME v) new_m) [x]))) funs)
              (HD (flat_to_clos_compile new_m [e]))])`];;

let compile_decs_def,compile_decs_ind = define_rec
  [`flat_to_clos_compile_decs [] = []`;
   `flat_to_clos_compile_decs (CONS e xs) = APPEND
    (flat_to_clos_compile [] [e]) (flat_to_clos_compile_decs xs)`];;

let flat_to_clos_compile_prog_def = new_definition
  `flat_to_clos_compile_prog xs =
     attach_interpreter (flat_to_clos_compile_decs xs)`;;

let inc_compile_decs_def = new_definition
  `inc_compile_decs decs =
     (let xs = APPEND (flat_to_clos_compile_decs decs)
       (flat_to_clos_compile_decs [flatLang_Con backend_common_None NONE
       []]) in
       (insert_interp xs,[]))`;;

let LENGTH_compile = prove
 (`!m xs. LENGTH (flat_to_clos_compile m xs) = LENGTH xs`,
  CHEAT_TAC);;

let compile_NOT_NIL = prove
 (`~(flat_to_clos_compile m (CONS x xs) = [])`,
  CHEAT_TAC);;
add_simp compile_NOT_NIL;;

let HD_compile = prove
 (`[HD (flat_to_clos_compile m [x])] = flat_to_clos_compile m [x]`,
  CHEAT_TAC);;
add_simp HD_compile;;

(* and the names it reads as variables are constants again *)
let _ = do_list unhide_constant
  ["pmatch"];;

(* and the interface *)
let _ = unhide_overloads ();;
