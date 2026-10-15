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
needs "lib/binary_ieee.ml";;
needs "lib/comparison.ml";;
needs "semantics/ast.ml";;
needs "semantics/fpSem.ml";;

let dest_pat_def = cake_define
  `dest_pat x1 =
      match x1 with
        [(Pvar v:flatLang_pat),h] -> SOME ((v:mlstring),h)
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
       backend_common_None xs (Var backend_common_None 0))`;;
hol4_overload "arg1" "flat_to_clos_arg1";;

let arg2_def = cake_define
  `flat_to_clos_arg2 xs f =
     (match xs with [x; y] -> f x y | _3 -> closLang_Let
       backend_common_None xs (Var backend_common_None 0))`;;
hol4_overload "arg2" "flat_to_clos_arg2";;

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
     (match ty with ast_IntT -> (match a with Add -> closLang_Op t
       (closLang_IntOp Add) xs | Sub -> closLang_Op t (closLang_IntOp
       Sub) xs | ast_Mul -> closLang_Op t (closLang_IntOp closLang_Mult)
       xs | Div -> Let t xs (If t (closLang_Op t (closLang_BlockOp
       Equal) [Var t 0; closLang_Op t (closLang_IntOp (closLang_Const
       (&0))) []])
                              (Raise t (closLang_Op t
                                (closLang_BlockOp (Cons div_tag)) []))
                              (closLang_Op t (closLang_IntOp
                                closLang_Div) [Var t 0; Var t 1])) | Mod
                                -> Let t xs (If t (closLang_Op t
                                (closLang_BlockOp Equal) [Var t 0;
                                closLang_Op t (closLang_IntOp
                                (closLang_Const (&0))) []])
                              (Raise t (closLang_Op t
                                (closLang_BlockOp (Cons div_tag)) []))
                              (closLang_Op t (closLang_IntOp
                                closLang_Mod) [Var t 0; Var t 1])) |
                                _4 -> Let backend_common_None xs (Var
                                backend_common_None 0)) |
                                ast_Float64T -> (match a with ast_Abs
                                -> closLang_Op t (closLang_WordOp
                                (FP_uop fpSem_FP_Abs)) xs | ast_Neg
                                -> closLang_Op t (closLang_WordOp
                                (FP_uop fpSem_FP_Neg)) xs | ast_Sqrt
                                -> closLang_Op t (closLang_WordOp
                                (FP_uop FP_Sqrt)) xs | Add ->
                                closLang_Op t (closLang_WordOp
                                (FP_bop FP_Add)) xs | Sub ->
                                closLang_Op t (closLang_WordOp
                                (FP_bop FP_Sub)) xs | ast_Mul ->
                                closLang_Op t (closLang_WordOp
                                (FP_bop FP_Mul)) xs | Div ->
                                closLang_Op t (closLang_WordOp
                                (FP_bop FP_Div)) xs | ast_FMA ->
                                closLang_Op t (closLang_WordOp
                                (FP_top FP_Fma)) xs | _5 -> Let
                                backend_common_None xs (Var
                                backend_common_None 0)) | ast_WordT
                                ws -> (match a with Add ->
                                closLang_Op t (closLang_WordOp
                                (WordOpw ws Add)) xs | Sub ->
                                closLang_Op t (closLang_WordOp
                                (WordOpw ws Sub)) xs | ast_And ->
                                closLang_Op t (closLang_WordOp
                                (WordOpw ws backend_common_Andw)) xs
                                | ast_Or -> closLang_Op t
                                (closLang_WordOp (WordOpw ws
                                backend_common_Orw)) xs | Xor ->
                                closLang_Op t (closLang_WordOp
                                (WordOpw ws Xor)) xs | _6 -> Let
                                backend_common_None xs (Var
                                backend_common_None 0)) | ast_BoolT
                                -> closLang_Op t (closLang_BlockOp
                                closLang_BoolNot) xs | _7 -> Let
                                backend_common_None xs (Var
                                backend_common_None 0))`;;

let compile_op_def = cake_define
  `flat_to_clos_compile_op t op xs =
     (match op with TagLenEq tag n -> closLang_Op t (closLang_BlockOp
       (TagLenEq tag n)) xs | LenEq n -> closLang_Op t (closLang_BlockOp
       (LenEq n)) xs | El n -> flat_to_clos_arg1 xs (\x. closLang_Op t
       (closLang_MemOp El) [closLang_Op backend_common_None
       (closLang_IntOp (closLang_Const (&n))) []; x]) |
       flatLang_GlobalVarAlloc n -> Let t xs (closLang_Op t
       (closLang_GlobOp AllocGlobal) [closLang_Op t (closLang_IntOp
       (closLang_Const (&n))) []]) | flatLang_GlobalVarInit n ->
       closLang_Op t (closLang_GlobOp (SetGlobal (n + 1))) xs |
       flatLang_GlobalVarLookup n -> closLang_Op t (closLang_GlobOp
       (Global (n + 1))) xs | flatLang_Id -> flat_to_clos_arg1 xs (\x.
       x) | flatLang_Src ast_Opapp -> flat_to_clos_arg2 xs (\x f.
       closLang_App t NONE f [x]) | flatLang_Src ast_Opassign ->
       flat_to_clos_arg2 xs (\x y. closLang_Op t (closLang_MemOp
       closLang_Update) [x; closLang_Op backend_common_None
       (closLang_IntOp (closLang_Const (&0))) []; y]) | flatLang_Src
       ast_Opref -> closLang_Op t (closLang_MemOp closLang_Ref) xs |
       flatLang_Src ConfigGC -> closLang_Op t (closLang_MemOp ConfigGC)
       xs | flatLang_Src ast_Equality -> closLang_Op t (closLang_BlockOp
       Equal) xs | flatLang_Src (FFI n) -> closLang_Op t (FFI n) xs |
       flatLang_Src ListAppend -> closLang_Op t (closLang_BlockOp
       ListAppend) xs | flatLang_Src ast_Vlength -> closLang_Op t
       (closLang_BlockOp closLang_LengthBlock) xs | flatLang_Src
       ast_Alength -> closLang_Op t (closLang_MemOp closLang_Length) xs
       | flatLang_Src ast_Implode -> closLang_Op t (closLang_MemOp
       closLang_FromListByte) xs | flatLang_Src ast_Explode ->
       closLang_Op t (closLang_MemOp closLang_ToListByte) xs |
       flatLang_Src ast_Strlen -> closLang_Op t (closLang_MemOp
       closLang_LengthByteVec) xs | flatLang_Src ast_Strcat ->
       closLang_Op t (closLang_MemOp closLang_ConcatByteVec) xs |
       flatLang_Src ast_CopyStrStr -> Let t xs (CopyByteStr t) |
       flatLang_Src ast_CopyStrAw8 -> Let t xs (CopyByteAw8 t) |
       flatLang_Src ast_CopyAw8Str -> Let t xs (CopyByteStr t) |
       flatLang_Src ast_CopyAw8Aw8 -> Let t xs (CopyByteAw8 t) |
       flatLang_Src ast_XorAw8Str_unsafe -> closLang_Op t
       (closLang_MemOp closLang_XorByte) xs | flatLang_Src ast_VfromList
       -> closLang_Op t (closLang_BlockOp (closLang_FromList 0)) xs |
       flatLang_Src (ast_Test test test_ty) ->
          (match test_ty with ast_BoolT -> closLang_Op t
            (closLang_BlockOp (closLang_BoolTest test)) xs | ast_CharT
            -> closLang_Op t (closLang_WordOp (WordTest ast_W8 test)) xs
            | ast_WordT ast_W8 -> closLang_Op t (closLang_WordOp
            (WordTest ast_W8 test)) xs | ast_IntT -> (match test with
            ast_Compare ast_Lt -> closLang_Op t (closLang_IntOp Less) xs
            | ast_Compare ast_Leq -> closLang_Op t (closLang_IntOp
            closLang_LessEq) xs | ast_Compare ast_Gt -> closLang_Op t
            (closLang_IntOp Greater) xs | ast_Compare ast_Geq ->
            closLang_Op t (closLang_IntOp closLang_GreaterEq) xs | _8 ->
            closLang_Op t (closLang_BlockOp Equal) xs) | ast_Float64T ->
            (match test with ast_Compare ast_Lt -> closLang_Op t
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
            (closLang_BlockOp Equal) xs) | _11 -> closLang_Op t
            (closLang_BlockOp Equal) xs) | flatLang_Src ast_Aw8length ->
            closLang_Op t (closLang_MemOp closLang_LengthByte) xs |
            flatLang_Src ast_AallocFixed -> closLang_Op t
            (closLang_MemOp closLang_Ref) xs | flatLang_Src ast_Aalloc
            -> Let t xs (If t (closLang_Op t (closLang_IntOp Less)
            [closLang_Op t (closLang_IntOp (closLang_Const (&0))) [];
            Var t 1])
                              (Raise t (closLang_Op t
                                (closLang_BlockOp (Cons subscript_tag))
                                []))
                              (closLang_Op t (closLang_MemOp
                                closLang_RefArray) [Var t 0; Var t 1]))
                                | flatLang_Src ast_Aw8alloc -> Let t xs
                                (If t (closLang_Op t (closLang_IntOp
                                Less) [closLang_Op t (closLang_IntOp
                                (closLang_Const (&0))) []; Var t 1])
                              (Raise t (closLang_Op t
                                (closLang_BlockOp (Cons subscript_tag))
                                []))
                              (closLang_Op t (closLang_MemOp
                                (closLang_RefByte F)) [Var t 0; Var t
                                1])) | flatLang_Src ast_Vsub -> Let t xs
                                (If t (closLang_Op t (closLang_BlockOp
                                closLang_BoundsCheckBlock) [Var t 0; Var
                                t 1])
                              (closLang_Op t (closLang_MemOp El) [Var
                                t 0; Var t 1])
                              (Raise t (closLang_Op t
                                (closLang_BlockOp (Cons subscript_tag))
                                []))) | flatLang_Src ast_Vsub_unsafe ->
                                closLang_Op t (closLang_MemOp El) xs |
                                flatLang_Src ast_Asub -> Let t xs (If t
                                (closLang_Op t (closLang_MemOp
                                closLang_BoundsCheckArray) [Var t 0; Var
                                t 1])
                              (closLang_Op t (closLang_MemOp El) [Var
                                t 0; Var t 1])
                              (Raise t (closLang_Op t
                                (closLang_BlockOp (Cons subscript_tag))
                                []))) | flatLang_Src ast_Asub_unsafe ->
                                closLang_Op t (closLang_MemOp El) xs |
                                flatLang_Src ast_Aupdate -> Let t xs (If
                                t (closLang_Op t (closLang_MemOp
                                closLang_BoundsCheckArray) [Var t 1; Var
                                t 2])
                              (closLang_Op t (closLang_MemOp
                                closLang_Update) [Var t 0; Var t 1; Var
                                t 2])
                              (Raise t (closLang_Op t
                                (closLang_BlockOp (Cons subscript_tag))
                                []))) | flatLang_Src ast_Aupdate_unsafe
                                -> closLang_Op t (closLang_MemOp
                                closLang_Update) xs | flatLang_Src
                                ast_Aw8sub -> Let t xs (If t
                                (closLang_Op t (closLang_MemOp
                                (closLang_BoundsCheckByte F)) [Var t 0;
                                Var t 1])
                              (closLang_Op t (closLang_MemOp
                                closLang_DerefByte) [Var t 0; Var t 1])
                              (Raise t (closLang_Op t
                                (closLang_BlockOp (Cons subscript_tag))
                                []))) | flatLang_Src ast_Aw8sub_unsafe
                                -> closLang_Op t (closLang_MemOp
                                closLang_DerefByte) xs | flatLang_Src
                                ast_Aw8update -> Let t xs (If t
                                (closLang_Op t (closLang_MemOp
                                (closLang_BoundsCheckByte F)) [Var t 1;
                                Var t 2])
                              (closLang_Op t (closLang_MemOp
                                closLang_UpdateByte) [Var t 0; Var t 1;
                                Var t 2])
                              (Raise t (closLang_Op t
                                (closLang_BlockOp (Cons subscript_tag))
                                []))) | flatLang_Src
                                ast_Aw8update_unsafe -> closLang_Op t
                                (closLang_MemOp closLang_UpdateByte) xs
                                | flatLang_Src ast_Strsub -> Let t xs
                                (If t (closLang_Op t (closLang_MemOp
                                (closLang_BoundsCheckByte F)) [Var t 0;
                                Var t 1])
                              (closLang_Op t (closLang_MemOp
                                closLang_DerefByteVec) [Var t 0; Var t
                                1])
                              (Raise t (closLang_Op t
                                (closLang_BlockOp (Cons subscript_tag))
                                []))) | flatLang_Src (ast_Shift x1 x2
                                x3) -> closLang_Op t (closLang_WordOp
                                (WordShift x1 x2 x3)) xs | flatLang_Src
                                ast_Eval -> closLang_Op t
                                closLang_Install xs | flatLang_Src
                                (ThunkOp op) -> closLang_Op t (ThunkOp
                                op) xs | flatLang_Src (ast_Arith a ty)
                                -> compile_arith t a ty xs |
                                flatLang_Src (ast_FromTo (ast_WordT
                                ast_W8) ast_IntT) -> flat_to_clos_arg1
                                xs (\x. x) | flatLang_Src (ast_FromTo
                                (ast_WordT W64) ast_IntT) -> closLang_Op
                                t (closLang_WordOp WordToInt) xs |
                                flatLang_Src (ast_FromTo ast_IntT
                                (ast_WordT ast_W8)) -> flat_to_clos_arg1
                                xs (\x. closLang_Op t (closLang_IntOp
                                Mod) [closLang_Op t (closLang_IntOp
                                (closLang_Const (&256))) []; x]) |
                                flatLang_Src (ast_FromTo ast_IntT
                                (ast_WordT W64)) -> closLang_Op t
                                (closLang_WordOp WordFromInt) xs |
                                flatLang_Src (ast_FromTo ast_IntT
                                ast_CharT) -> Let t xs (If t
                                (closLang_Op t (closLang_IntOp Less)
                                [closLang_Op backend_common_None
                                (closLang_IntOp (closLang_Const (&0)))
                                []; Var t 0])
                         (Raise t (closLang_Op t (closLang_BlockOp
                           (Cons chr_tag)) []))
                         (If t (closLang_Op t (closLang_IntOp Less)
                           [Var t 0; closLang_Op backend_common_None
                           (closLang_IntOp (closLang_Const (&255))) []])
                           (Raise t (closLang_Op t (closLang_BlockOp
                             (Cons chr_tag)) []))
                           (Var t 0))) | flatLang_Src (ast_FromTo
                             ast_Float64T (ast_WordT W64)) -> Let
                             backend_common_None xs (Var
                             backend_common_None 0) | flatLang_Src
                             (ast_FromTo (ast_WordT W64)
                             ast_Float64T) -> Let backend_common_None
                             xs (Var backend_common_None 0) |
                             flatLang_Src _12 -> Let
                             backend_common_None xs (Var
                             backend_common_None 0))`;;
hol4_overload "compile_op" "flat_to_clos_compile_op";;

let join_strings_def = cake_define
  `join_strings (x:mlstring) y =
     (if strlen x = 0 then y else mlstring_concat [x; implode "_";
       y])`;;

let dest_nop_def = cake_define
  `dest_nop op e =
     (if op = flatLang_Src (ast_FromTo ast_IntT (ast_WordT ast_W8))
       then
       (match e with [App _13 op1 [x]] -> (if op1 = flatLang_Src
         (ast_FromTo ast_CharT ast_IntT) then SOME x else NONE) | _14 ->
         NONE) else if op = flatLang_Src (ast_FromTo ast_IntT ast_CharT)
         then
       (match e with [App _15 op1 [x]] -> (if op1 = flatLang_Src
         (ast_FromTo (ast_WordT ast_W8) ast_IntT) then SOME x else
         NONE) | _16 -> NONE) else NONE)`;;

let dest_Constant_def = cake_define
  `flat_to_clos_dest_Constant x1 =
      match x1 with
        closLang_Op t (closLang_BlockOp (closLang_Constant c)) [] ->
          SOME c
      | (closLang_Op t (closLang_IntOp (closLang_Const i)) []) ->
        SOME (ConstInt i)
      | (closLang_Op t (closLang_BlockOp (Cons n)) []) -> SOME
        (ConstCons n [])
      | _17 -> NONE`;;
hol4_overload "dest_Constant" "flat_to_clos_dest_Constant";;

let dest_Constants_def = cake_define_list
  [`dest_Constants [] = SOME []`;
   `dest_Constants (c :: cs) =
      (match flat_to_clos_dest_Constant c with NONE -> NONE |
        SOME x -> (match dest_Constants cs with NONE -> NONE | SOME
        xs -> SOME (x :: xs)))`];;

let SmartCons_def = cake_define
  `SmartCons t tag xs =
     (if NULL xs then closLang_Op t (closLang_BlockOp (Cons tag)) []
       else
     match dest_Constants xs with NONE -> closLang_Op t
       (closLang_BlockOp (Cons tag)) xs | SOME cs -> closLang_Op t
       (closLang_BlockOp (closLang_Constant (ConstCons tag (REVERSE
       cs)))) [])`;;

let compile_def = cake_define_list
  [`flat_to_clos_compile m [] = []`;
   `flat_to_clos_compile m (x :: y :: xs) = flat_to_clos_compile m
  [x] ++ flat_to_clos_compile m (y :: xs)`;
   `flat_to_clos_compile m [flatLang_Raise t e] = [closLang_Raise t
  (HD (flat_to_clos_compile m [e]))]`;
   `flat_to_clos_compile m [(Lit t l:flatLang_exp)] = [compile_lit t
  l]`;
   `flat_to_clos_compile m [flatLang_Var_local t v] = [Var t
  (indexedLists_findi (SOME v) m)]`;
   `flat_to_clos_compile m [(Con t n es:flatLang_exp)] =
         (let tag = (match n with SOME (t,_21) -> t | _22 -> 0) in
           [SmartCons t tag (flat_to_clos_compile m (REVERSE
             es))])`;
   `flat_to_clos_compile m [(App t op es:flatLang_exp)] =
         (match dest_nop op es with SOME e ->
           flat_to_clos_compile m [e] | NONE ->
           [flat_to_clos_compile_op t op (flat_to_clos_compile m
           (REVERSE es))])`;
   `flat_to_clos_compile m [(Fun t v e:flatLang_exp)] =
         [closLang_Fn t NONE NONE 1 (HD (flat_to_clos_compile
           (SOME v :: m) [e]))]`;
   `flat_to_clos_compile m [(If t x1 x2 x3:flatLang_exp)] =
         [If t (HD (flat_to_clos_compile m [x1]))
               (HD (flat_to_clos_compile m [x2]))
               (HD (flat_to_clos_compile m [x3]))]`;
   `flat_to_clos_compile m [(Let t vo e1 e2:flatLang_exp)] =
         [Let t (flat_to_clos_compile m [e1]) (HD
           (flat_to_clos_compile (vo :: m) [e2]))]`;
   `flat_to_clos_compile m [(Mat t e pes:flatLang_exp)] =
  [closLang_Op t (closLang_IntOp (closLang_Const (&0))) []]`;
   `flat_to_clos_compile m [(Handle t e pes:flatLang_exp)] =
         (match dest_pat pes with SOME (v,h) -> [Handle t (HD
           (flat_to_clos_compile m [e])) (HD (flat_to_clos_compile
           (SOME v :: m) [h]))] | _24 -> flat_to_clos_compile m [e])`;
   `flat_to_clos_compile m [(Letrec t funs e:flatLang_exp)] =
         (let new_m = MAP (\n. SOME (FST n)) funs ++ m in
           [Letrec (MAP (\n. join_strings t (FST n)) funs) NONE NONE
              (MAP (\(f,v,x). (1,HD (flat_to_clos_compile (SOME v ::
                new_m) [x]))) funs)
              (HD (flat_to_clos_compile new_m [e]))])`];;
hol4_overload "compile" "flat_to_clos_compile";;

let compile_decs_def = cake_define_list
  [`flat_to_clos_compile_decs [] = []`;
   `flat_to_clos_compile_decs (e :: xs) = flat_to_clos_compile []
  [e] ++ flat_to_clos_compile_decs xs`];;
hol4_overload "compile_decs" "flat_to_clos_compile_decs";;

let compile_prog_def = cake_define
  `flat_to_clos_compile_prog xs =
     attach_interpreter (flat_to_clos_compile_decs xs)`;;
hol4_overload "compile_prog" "flat_to_clos_compile_prog";;

let inc_compile_decs_def = cake_define
  `inc_compile_decs decs =
     (let xs = flat_to_clos_compile_decs decs ++
       flat_to_clos_compile_decs [Con backend_common_None NONE []] in
       (insert_interp xs,[]))`;;
