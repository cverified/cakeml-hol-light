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
needs "compiler/backend/clos_op.ml";;
needs "compiler/backend/clos_to_bvl.ml";;
needs "compiler/backend/data_live.ml";;
needs "compiler/backend/data_to_word.ml";;
needs "compiler/backend/flatLang.ml";;
needs "compiler/backend/reg_alloc/reg_alloc.ml";;
needs "lib/binary_ieee.ml";;
needs "lib/indexedLists.ml";;
needs "lib/ternaryComparisons.ml";;
needs "semantics/ast.ml";;
needs "semantics/fpSem.ml";;
needs "semantics/semanticPrimitives.ml";;

let dest_pat_def = cake_define
  `dest_pat x1 =
      match x1 with
        [(Pvar v,h)] -> SOME ((v:mlstring),h)
      | _1 -> NONE`;;

let compile_lit_def = cake_define
  `compile_lit t l =
     closLang_Op t
      (match l with ast_IntLit i -> closLang_IntOp (Const i) |
        ast_Char c -> closLang_IntOp (Const (&(ORD c))) | ast_StrLit
        s -> closLang_BlockOp (closLang_Constant (ConstStr s)) |
        ast_Word8 b -> closLang_IntOp (Const (&(w2n b))) | Word64 w
        -> closLang_BlockOp (closLang_Constant (ConstWord64 w)) |
        ast_Float64 w -> closLang_BlockOp (closLang_Constant
        (ConstWord64 w))) []`;;

let arg1_def = cake_define
  `flat_to_clos_arg1 xs f =
     (match xs with [x] -> f x | _2 -> closLang_Let None xs (Var
       None 0))`;;
hol4_overload "arg1" "flat_to_clos_arg1";;

let arg2_def = cake_define
  `flat_to_clos_arg2 xs f =
     (match xs with [x; y] -> f x y | _3 -> closLang_Let None xs
       (Var None 0))`;;
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
     (match ty with IntT -> (match a with Add -> Op t (closLang_IntOp
       Add) xs | Sub -> Op t (closLang_IntOp Sub) xs | Mul -> Op t
       (closLang_IntOp closLang_Mult) xs | Div -> Let t xs (If t (Op t
       (closLang_BlockOp (EQUAL)) [Var t 0; Op t (closLang_IntOp (Const
       0)) []])
                              (Raise t (Op t (closLang_BlockOp (Cons
                                div_tag)) []))
                              (Op t (closLang_IntOp closLang_Div)
                                [Var t 0; Var t 1])) | Mod -> Let t xs
                                (If t (Op t (closLang_BlockOp (EQUAL))
                                [Var t 0; Op t (closLang_IntOp (Const
                                0)) []])
                              (Raise t (Op t (closLang_BlockOp (Cons
                                div_tag)) []))
                              (Op t (closLang_IntOp closLang_Mod)
                                [Var t 0; Var t 1])) | _4 -> Let None
                                xs (Var None 0)) | ast_Float64T ->
                                (match a with ast_Abs -> Op t
                                (closLang_WordOp (FP_uop
                                fpSem_FP_Abs)) xs | ast_Neg -> Op t
                                (closLang_WordOp (FP_uop
                                fpSem_FP_Neg)) xs | ast_Sqrt -> Op t
                                (closLang_WordOp (FP_uop FP_Sqrt)) xs
                                | Add -> Op t (closLang_WordOp
                                (FP_bop FP_Add)) xs | Sub -> Op t
                                (closLang_WordOp (FP_bop FP_Sub)) xs
                                | Mul -> Op t (closLang_WordOp
                                (FP_bop FP_Mul)) xs | Div -> Op t
                                (closLang_WordOp (FP_bop FP_Div)) xs
                                | ast_FMA -> Op t (closLang_WordOp
                                (FP_top FP_Fma)) xs | _5 -> Let None
                                xs (Var None 0)) | WordT ws -> (match
                                a with Add -> Op t (closLang_WordOp
                                (WordOpw ws Add)) xs | Sub -> Op t
                                (closLang_WordOp (WordOpw ws Sub)) xs
                                | And -> Op t (closLang_WordOp
                                (WordOpw ws backend_common_Andw)) xs
                                | Or -> Op t (closLang_WordOp
                                (WordOpw ws backend_common_Orw)) xs |
                                Xor -> Op t (closLang_WordOp (WordOpw
                                ws Xor)) xs | _6 -> Let None xs (Var
                                None 0)) | ast_BoolT -> Op t
                                (closLang_BlockOp closLang_BoolNot)
                                xs | _7 -> Let None xs (Var None 0))`;;

let compile_op_def = cake_define
  `flat_to_clos_compile_op t op xs =
     (match op with TagLenEq tag n -> closLang_Op t (closLang_BlockOp
       (TagLenEq tag n)) xs | LenEq n -> closLang_Op t (closLang_BlockOp
       (LenEq n)) xs | El n -> arg1 xs (\x. Op t (closLang_MemOp El) [Op
       None (closLang_IntOp (Const (&n))) []; x]) |
       flatLang_GlobalVarAlloc n -> Let t xs (Op t (closLang_GlobOp
       AllocGlobal) [Op t (closLang_IntOp (Const (&n))) []]) |
       flatLang_GlobalVarInit n -> Op t (closLang_GlobOp (SetGlobal (n +
       1))) xs | flatLang_GlobalVarLookup n -> Op t (closLang_GlobOp
       (Global (n + 1))) xs | flatLang_Id -> arg1 xs (\x. x) |
       flatLang_Src ast_Opapp -> arg2 xs (\x f. closLang_App t NONE f
       [x]) | flatLang_Src ast_Opassign -> arg2 xs (\x y. Op t
       (closLang_MemOp closLang_Update) [x; Op None (closLang_IntOp
       (Const 0)) []; y]) | flatLang_Src ast_Opref -> Op t
       (closLang_MemOp Ref) xs | flatLang_Src ConfigGC -> Op t
       (closLang_MemOp ConfigGC) xs | flatLang_Src ast_Equality -> Op t
       (closLang_BlockOp (EQUAL)) xs | flatLang_Src (FFI n) -> Op t (FFI
       n) xs | flatLang_Src ListAppend -> Op t (closLang_BlockOp
       ListAppend) xs | flatLang_Src ast_Vlength -> Op t
       (closLang_BlockOp closLang_LengthBlock) xs | flatLang_Src
       ast_Alength -> Op t (closLang_MemOp closLang_Length) xs |
       flatLang_Src ast_Implode -> Op t (closLang_MemOp
       closLang_FromListByte) xs | flatLang_Src ast_Explode -> Op t
       (closLang_MemOp closLang_ToListByte) xs | flatLang_Src ast_Strlen
       -> Op t (closLang_MemOp closLang_LengthByteVec) xs | flatLang_Src
       ast_Strcat -> Op t (closLang_MemOp closLang_ConcatByteVec) xs |
       flatLang_Src ast_CopyStrStr -> Let t xs (CopyByteStr t) |
       flatLang_Src ast_CopyStrAw8 -> Let t xs (CopyByteAw8 t) |
       flatLang_Src ast_CopyAw8Str -> Let t xs (CopyByteStr t) |
       flatLang_Src ast_CopyAw8Aw8 -> Let t xs (CopyByteAw8 t) |
       flatLang_Src ast_XorAw8Str_unsafe -> Op t (closLang_MemOp
       closLang_XorByte) xs | flatLang_Src ast_VfromList -> Op t
       (closLang_BlockOp (closLang_FromList 0)) xs | flatLang_Src (Test
       test test_ty) ->
          (match test_ty with ast_BoolT -> Op t (closLang_BlockOp
            (closLang_BoolTest test)) xs | CharT -> Op t
            (closLang_WordOp (WordTest ast_W8 test)) xs | WordT ast_W8
            -> Op t (closLang_WordOp (WordTest ast_W8 test)) xs | IntT
            -> (match test with ast_Compare Lt -> Op t (closLang_IntOp
            (LESS)) xs | ast_Compare ast_Leq -> Op t (closLang_IntOp
            closLang_LessEq) xs | ast_Compare ast_Gt -> Op t
            (closLang_IntOp (GREATER)) xs | ast_Compare ast_Geq -> Op t
            (closLang_IntOp closLang_GreaterEq) xs | _8 -> Op t
            (closLang_BlockOp (EQUAL)) xs) | ast_Float64T -> (match test
            with ast_Compare Lt -> Op t (closLang_WordOp (FP_cmp
            FP_Less)) xs | ast_Compare ast_Leq -> Op t (closLang_WordOp
            (FP_cmp FP_LessEqual)) xs | ast_Compare ast_Gt -> Op t
            (closLang_WordOp (FP_cmp FP_Greater)) xs | ast_Compare
            ast_Geq -> Op t (closLang_WordOp (FP_cmp FP_GreaterEqual))
            xs | _9 -> Op t (closLang_WordOp (FP_cmp FP_Equal)) xs) |
            ast_StrT -> (match test with ast_Compare opb -> Op t
            (closLang_MemOp (closLang_StringCmp F opb)) xs |
            ast_AltCompare opb -> Op t (closLang_MemOp
            (closLang_StringCmp T opb)) xs | _10 -> Op t
            (closLang_BlockOp (EQUAL)) xs) | _11 -> Op t
            (closLang_BlockOp (EQUAL)) xs) | flatLang_Src ast_Aw8length
            -> Op t (closLang_MemOp closLang_LengthByte) xs |
            flatLang_Src ast_AallocFixed -> Op t (closLang_MemOp Ref) xs
            | flatLang_Src ast_Aalloc -> Let t xs (If t (Op t
            (closLang_IntOp (LESS)) [Op t (closLang_IntOp (Const 0)) [];
            Var t 1])
                              (Raise t (Op t (closLang_BlockOp (Cons
                                subscript_tag)) []))
                              (Op t (closLang_MemOp
                                closLang_RefArray) [Var t 0; Var t 1]))
                                | flatLang_Src ast_Aw8alloc -> Let t xs
                                (If t (Op t (closLang_IntOp (LESS)) [Op
                                t (closLang_IntOp (Const 0)) []; Var t
                                1])
                              (Raise t (Op t (closLang_BlockOp (Cons
                                subscript_tag)) []))
                              (Op t (closLang_MemOp (closLang_RefByte
                                F)) [Var t 0; Var t 1])) | flatLang_Src
                                ast_Vsub -> Let t xs (If t (Op t
                                (closLang_BlockOp
                                closLang_BoundsCheckBlock) [Var t 0; Var
                                t 1])
                              (Op t (closLang_MemOp El) [Var t 0; Var
                                t 1])
                              (Raise t (Op t (closLang_BlockOp (Cons
                                subscript_tag)) []))) | flatLang_Src
                                ast_Vsub_unsafe -> Op t (closLang_MemOp
                                El) xs | flatLang_Src ast_Asub -> Let t
                                xs (If t (Op t (closLang_MemOp
                                closLang_BoundsCheckArray) [Var t 0; Var
                                t 1])
                              (Op t (closLang_MemOp El) [Var t 0; Var
                                t 1])
                              (Raise t (Op t (closLang_BlockOp (Cons
                                subscript_tag)) []))) | flatLang_Src
                                ast_Asub_unsafe -> Op t (closLang_MemOp
                                El) xs | flatLang_Src ast_Aupdate -> Let
                                t xs (If t (Op t (closLang_MemOp
                                closLang_BoundsCheckArray) [Var t 1; Var
                                t 2])
                              (Op t (closLang_MemOp closLang_Update)
                                [Var t 0; Var t 1; Var t 2])
                              (Raise t (Op t (closLang_BlockOp (Cons
                                subscript_tag)) []))) | flatLang_Src
                                ast_Aupdate_unsafe -> Op t
                                (closLang_MemOp closLang_Update) xs |
                                flatLang_Src ast_Aw8sub -> Let t xs (If
                                t (Op t (closLang_MemOp
                                (closLang_BoundsCheckByte F)) [Var t 0;
                                Var t 1])
                              (Op t (closLang_MemOp
                                closLang_DerefByte) [Var t 0; Var t 1])
                              (Raise t (Op t (closLang_BlockOp (Cons
                                subscript_tag)) []))) | flatLang_Src
                                ast_Aw8sub_unsafe -> Op t
                                (closLang_MemOp closLang_DerefByte) xs |
                                flatLang_Src ast_Aw8update -> Let t xs
                                (If t (Op t (closLang_MemOp
                                (closLang_BoundsCheckByte F)) [Var t 1;
                                Var t 2])
                              (Op t (closLang_MemOp
                                closLang_UpdateByte) [Var t 0; Var t 1;
                                Var t 2])
                              (Raise t (Op t (closLang_BlockOp (Cons
                                subscript_tag)) []))) | flatLang_Src
                                ast_Aw8update_unsafe -> Op t
                                (closLang_MemOp closLang_UpdateByte) xs
                                | flatLang_Src ast_Strsub -> Let t xs
                                (If t (Op t (closLang_MemOp
                                (closLang_BoundsCheckByte F)) [Var t 0;
                                Var t 1])
                              (Op t (closLang_MemOp
                                closLang_DerefByteVec) [Var t 0; Var t
                                1])
                              (Raise t (Op t (closLang_BlockOp (Cons
                                subscript_tag)) []))) | flatLang_Src
                                (Shift x1 x2 x3) -> Op t
                                (closLang_WordOp (WordShift x1 x2 x3))
                                xs | flatLang_Src ast_Eval -> Op t
                                Install xs | flatLang_Src (ThunkOp op)
                                -> Op t (ThunkOp op) xs | flatLang_Src
                                (Arith a ty) -> compile_arith t a ty xs
                                | flatLang_Src (ast_FromTo (WordT
                                ast_W8) IntT) -> arg1 xs (\x. x) |
                                flatLang_Src (ast_FromTo (WordT W64)
                                IntT) -> Op t (closLang_WordOp
                                WordToInt) xs | flatLang_Src (ast_FromTo
                                IntT (WordT ast_W8)) -> arg1 xs (\x. Op
                                t (closLang_IntOp Mod) [Op t
                                (closLang_IntOp (Const 256)) []; x]) |
                                flatLang_Src (ast_FromTo IntT (WordT
                                W64)) -> Op t (closLang_WordOp
                                WordFromInt) xs | flatLang_Src
                                (ast_FromTo IntT CharT) -> Let t xs (If
                                t (Op t (closLang_IntOp (LESS)) [Op None
                                (closLang_IntOp (Const 0)) []; Var t 0])
                         (Raise t (Op t (closLang_BlockOp (Cons
                           chr_tag)) []))
                         (If t (Op t (closLang_IntOp (LESS)) [Var t
                           0; Op None (closLang_IntOp (Const 255)) []])
                           (Raise t (Op t (closLang_BlockOp (Cons
                             chr_tag)) []))
                           (Var t 0))) | flatLang_Src (ast_FromTo
                             ast_Float64T (WordT W64)) -> Let None xs
                             (Var None 0) | flatLang_Src (ast_FromTo
                             (WordT W64) ast_Float64T) -> Let None xs
                             (Var None 0) | flatLang_Src _12 -> Let
                             None xs (Var None 0))`;;
hol4_overload "compile_op" "flat_to_clos_compile_op";;

let join_strings_def = cake_define
  `join_strings (x:mlstring) y =
     (if strlen x = 0 then y else mlstring_concat [x; implode "_";
       y])`;;

let dest_nop_def = cake_define
  `dest_nop op e =
     (if op = flatLang_Src (ast_FromTo IntT (WordT ast_W8)) then
       (match e with [App _13 op1 [x]] -> (if op1 = flatLang_Src
         (ast_FromTo CharT IntT) then SOME x else NONE) | _14 -> NONE)
         else if op = flatLang_Src (ast_FromTo IntT CharT) then
       (match e with [App _15 op1 [x]] -> (if op1 = flatLang_Src
         (ast_FromTo (WordT ast_W8) IntT) then SOME x else NONE) |
         _16 -> NONE) else NONE)`;;

let dest_Constant_def = cake_define
  `flat_to_clos_dest_Constant x1 =
      match x1 with
        (Op t (closLang_BlockOp (closLang_Constant c)) []) -> SOME c
      | (Op t (closLang_IntOp (Const i)) []) -> SOME (ConstInt i)
      | (Op t (closLang_BlockOp (Cons n)) []) -> SOME (ConstCons n
        [])
      | _17 -> NONE`;;
hol4_overload "dest_Constant" "flat_to_clos_dest_Constant";;

let dest_Constants_def = cake_define
  `dest_Constants [] = SOME [] /\
   dest_Constants (c :: cs) =
     (match dest_Constant c with NONE -> NONE | SOME x -> (match
       dest_Constants cs with NONE -> NONE | SOME xs -> SOME (x ::
       xs)))`;;

let SmartCons_def = cake_define
  `SmartCons t tag xs =
     (if NULL xs then Op t (closLang_BlockOp (Cons tag)) [] else
     match dest_Constants xs with NONE -> Op t (closLang_BlockOp
       (Cons tag)) xs | SOME cs -> Op t (closLang_BlockOp
       (closLang_Constant (ConstCons tag (REVERSE cs)))) [])`;;

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
   (flat_to_clos_compile m [Lit t l] = [compile_lit t l]) /\
   (flat_to_clos_compile m [flatLang_Var_local t v] = [Var t (findi
     (SOME v) m)]) /\
   (flat_to_clos_compile m [Con t n es] =
      (let tag = (match n with SOME (t,_18) -> t | _19 -> 0) in
        [SmartCons t tag (flat_to_clos_compile m (REVERSE es))])) /\
   (flat_to_clos_compile m [App t op es] =
      (match dest_nop op es with SOME e -> flat_to_clos_compile m [e]
        | NONE -> [compile_op t op (flat_to_clos_compile m (REVERSE
        es))])) /\
   (flat_to_clos_compile m [Fun t v e] =
      [closLang_Fn t NONE NONE 1 (HD (flat_to_clos_compile (SOME v ::
        m) [e]))]) /\
   (flat_to_clos_compile m [If t x1 x2 x3] =
      [If t (HD (flat_to_clos_compile m [x1]))
            (HD (flat_to_clos_compile m [x2]))
            (HD (flat_to_clos_compile m [x3]))]) /\
   (flat_to_clos_compile m [Let t vo e1 e2] =
      [Let t (flat_to_clos_compile m [e1]) (HD (flat_to_clos_compile
        (vo :: m) [e2]))]) /\
   (flat_to_clos_compile m [Mat t e pes] = [Op t (closLang_IntOp
     (Const 0)) []]) /\
   (flat_to_clos_compile m [Handle t e pes] =
      (match dest_pat pes with SOME (v,h) -> [Handle t (HD
        (flat_to_clos_compile m [e])) (HD (flat_to_clos_compile (SOME v
        :: m) [h]))] | _20 -> flat_to_clos_compile m [e])) /\
   (flat_to_clos_compile m [Letrec t funs e] =
      (let new_m = MAP (\n. SOME (FST n)) funs ++ m in
        [Letrec (MAP (\n. join_strings t (FST n)) funs) NONE NONE
           (MAP (\(f,v,x). (1,HD (flat_to_clos_compile (SOME v ::
             new_m) [x]))) funs)
           (HD (flat_to_clos_compile new_m [e]))]))`;;
hol4_overload "compile" "flat_to_clos_compile";;

let compile_decs_def = cake_define
  `flat_to_clos_compile_decs [] = [] /\
   flat_to_clos_compile_decs (e :: xs) = compile [] [e] ++
     flat_to_clos_compile_decs xs`;;
hol4_overload "compile_decs" "flat_to_clos_compile_decs";;

let compile_prog_def = cake_define
  `flat_to_clos_compile_prog xs =
     attach_interpreter (compile_decs xs)`;;
hol4_overload "compile_prog" "flat_to_clos_compile_prog";;

let inc_compile_decs_def = cake_define
  `inc_compile_decs decs =
     (let xs = compile_decs decs ++ compile_decs [Con None NONE []]
       in
       (insert_interp xs,[]))`;;
