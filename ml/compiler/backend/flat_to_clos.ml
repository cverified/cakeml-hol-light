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
needs "lib/indexedLists.ml";;
needs "lib/ternaryComparisons.ml";;
needs "semantics/ast.ml";;
needs "semantics/fpSem.ml";;

let dest_pat_def = cake_define
  `dest_pat x1 =
      match x1 with
        [(Pvar v,h)] -> SOME ((v:mlstring),h)
      | _1 -> NONE`;;

let compile_lit_def = cake_define
  `compile_lit t l =
     closLang_Op t
      (match l with IntLit i -> IntOp (Const i) | Char c -> IntOp
        (Const (&(ORD c))) | StrLit s -> BlockOp (Constant (ConstStr
        s)) | Word8 b -> IntOp (Const (&(w2n b))) | Word64 w ->
        BlockOp (Constant (ConstWord64 w)) | Float64 w -> BlockOp
        (Constant (ConstWord64 w))) []`;;

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
     (match ty with IntT -> (match a with Add -> Op t (IntOp Add) xs
       | Sub -> Op t (IntOp Sub) xs | Mul -> Op t (IntOp Mult) xs | Div
       -> Let t xs (If t (Op t (BlockOp (EQUAL)) [Var t 0; Op t (IntOp
       (Const 0)) []])
                              (Raise t (Op t (BlockOp (Cons div_tag))
                                []))
                              (Op t (IntOp closLang_Div) [Var t 0;
                                Var t 1])) | Mod -> Let t xs (If t (Op t
                                (BlockOp (EQUAL)) [Var t 0; Op t (IntOp
                                (Const 0)) []])
                              (Raise t (Op t (BlockOp (Cons div_tag))
                                []))
                              (Op t (IntOp closLang_Mod) [Var t 0;
                                Var t 1])) | _4 -> Let None xs (Var
                                None 0)) | Float64T -> (match a with
                                Abs -> Op t (WordOp (FP_uop FP_Abs))
                                xs | Neg -> Op t (WordOp (FP_uop
                                FP_Neg)) xs | Sqrt -> Op t (WordOp
                                (FP_uop FP_Sqrt)) xs | Add -> Op t
                                (WordOp (FP_bop FP_Add)) xs | Sub ->
                                Op t (WordOp (FP_bop FP_Sub)) xs |
                                Mul -> Op t (WordOp (FP_bop FP_Mul))
                                xs | Div -> Op t (WordOp (FP_bop
                                FP_Div)) xs | FMA -> Op t (WordOp
                                (FP_top FP_Fma)) xs | _5 -> Let None
                                xs (Var None 0)) | WordT ws -> (match
                                a with Add -> Op t (WordOp (WordOpw
                                ws Add)) xs | Sub -> Op t (WordOp
                                (WordOpw ws Sub)) xs | And -> Op t
                                (WordOp (WordOpw ws Andw)) xs | Or ->
                                Op t (WordOp (WordOpw ws Orw)) xs |
                                Xor -> Op t (WordOp (WordOpw ws Xor))
                                xs | _6 -> Let None xs (Var None 0))
                                | BoolT -> Op t (BlockOp BoolNot) xs
                                | _7 -> Let None xs (Var None 0))`;;

let compile_op_def = cake_define
  `flat_to_clos_compile_op t op xs =
     (match op with TagLenEq tag n -> closLang_Op t (BlockOp
       (TagLenEq tag n)) xs | LenEq n -> closLang_Op t (BlockOp (LenEq
       n)) xs | El n -> arg1 xs (\x. Op t (MemOp El) [Op None (IntOp
       (Const (&n))) []; x]) | GlobalVarAlloc n -> Let t xs (Op t
       (GlobOp AllocGlobal) [Op t (IntOp (Const (&n))) []]) |
       GlobalVarInit n -> Op t (GlobOp (SetGlobal (n + 1))) xs |
       GlobalVarLookup n -> Op t (GlobOp (Global (n + 1))) xs | Id ->
       arg1 xs (\x. x) | Src Opapp -> arg2 xs (\x f. closLang_App t NONE
       f [x]) | Src Opassign -> arg2 xs (\x y. Op t (MemOp Update) [x;
       Op None (IntOp (Const 0)) []; y]) | Src Opref -> Op t (MemOp Ref)
       xs | Src ConfigGC -> Op t (MemOp ConfigGC) xs | Src Equality ->
       Op t (BlockOp (EQUAL)) xs | Src (FFI n) -> Op t (FFI n) xs | Src
       ListAppend -> Op t (BlockOp ListAppend) xs | Src Vlength -> Op t
       (BlockOp LengthBlock) xs | Src Alength -> Op t (MemOp Length) xs
       | Src Implode -> Op t (MemOp FromListByte) xs | Src Explode -> Op
       t (MemOp ToListByte) xs | Src Strlen -> Op t (MemOp
       LengthByteVec) xs | Src Strcat -> Op t (MemOp ConcatByteVec) xs |
       Src CopyStrStr -> Let t xs (CopyByteStr t) | Src CopyStrAw8 ->
       Let t xs (CopyByteAw8 t) | Src CopyAw8Str -> Let t xs
       (CopyByteStr t) | Src CopyAw8Aw8 -> Let t xs (CopyByteAw8 t) |
       Src XorAw8Str_unsafe -> Op t (MemOp XorByte) xs | Src VfromList
       -> Op t (BlockOp (FromList 0)) xs | Src (Test test test_ty) ->
          (match test_ty with BoolT -> Op t (BlockOp (BoolTest test))
            xs | CharT -> Op t (WordOp (WordTest W8 test)) xs | WordT W8
            -> Op t (WordOp (WordTest W8 test)) xs | IntT -> (match test
            with Compare Lt -> Op t (IntOp (LESS)) xs | Compare Leq ->
            Op t (IntOp LessEq) xs | Compare Gt -> Op t (IntOp
            (GREATER)) xs | Compare Geq -> Op t (IntOp GreaterEq) xs |
            _8 -> Op t (BlockOp (EQUAL)) xs) | Float64T -> (match test
            with Compare Lt -> Op t (WordOp (FP_cmp FP_Less)) xs |
            Compare Leq -> Op t (WordOp (FP_cmp FP_LessEqual)) xs |
            Compare Gt -> Op t (WordOp (FP_cmp FP_Greater)) xs | Compare
            Geq -> Op t (WordOp (FP_cmp FP_GreaterEqual)) xs | _9 -> Op
            t (WordOp (FP_cmp FP_Equal)) xs) | StrT -> (match test with
            Compare opb -> Op t (MemOp (StringCmp F opb)) xs |
            AltCompare opb -> Op t (MemOp (StringCmp T opb)) xs | _10 ->
            Op t (BlockOp (EQUAL)) xs) | _11 -> Op t (BlockOp (EQUAL))
            xs) | Src Aw8length -> Op t (MemOp LengthByte) xs | Src
            AallocFixed -> Op t (MemOp Ref) xs | Src Aalloc -> Let t xs
            (If t (Op t (IntOp (LESS)) [Op t (IntOp (Const 0)) []; Var t
            1])
                              (Raise t (Op t (BlockOp (Cons
                                subscript_tag)) []))
                              (Op t (MemOp RefArray) [Var t 0; Var t
                                1])) | Src Aw8alloc -> Let t xs (If t
                                (Op t (IntOp (LESS)) [Op t (IntOp (Const
                                0)) []; Var t 1])
                              (Raise t (Op t (BlockOp (Cons
                                subscript_tag)) []))
                              (Op t (MemOp (RefByte F)) [Var t 0; Var
                                t 1])) | Src Vsub -> Let t xs (If t (Op
                                t (BlockOp BoundsCheckBlock) [Var t 0;
                                Var t 1])
                              (Op t (MemOp El) [Var t 0; Var t 1])
                              (Raise t (Op t (BlockOp (Cons
                                subscript_tag)) []))) | Src Vsub_unsafe
                                -> Op t (MemOp El) xs | Src Asub -> Let
                                t xs (If t (Op t (MemOp
                                BoundsCheckArray) [Var t 0; Var t 1])
                              (Op t (MemOp El) [Var t 0; Var t 1])
                              (Raise t (Op t (BlockOp (Cons
                                subscript_tag)) []))) | Src Asub_unsafe
                                -> Op t (MemOp El) xs | Src Aupdate ->
                                Let t xs (If t (Op t (MemOp
                                BoundsCheckArray) [Var t 1; Var t 2])
                              (Op t (MemOp Update) [Var t 0; Var t 1;
                                Var t 2])
                              (Raise t (Op t (BlockOp (Cons
                                subscript_tag)) []))) | Src
                                Aupdate_unsafe -> Op t (MemOp Update) xs
                                | Src Aw8sub -> Let t xs (If t (Op t
                                (MemOp (BoundsCheckByte F)) [Var t 0;
                                Var t 1])
                              (Op t (MemOp DerefByte) [Var t 0; Var t
                                1])
                              (Raise t (Op t (BlockOp (Cons
                                subscript_tag)) []))) | Src
                                Aw8sub_unsafe -> Op t (MemOp DerefByte)
                                xs | Src Aw8update -> Let t xs (If t (Op
                                t (MemOp (BoundsCheckByte F)) [Var t 1;
                                Var t 2])
                              (Op t (MemOp UpdateByte) [Var t 0; Var
                                t 1; Var t 2])
                              (Raise t (Op t (BlockOp (Cons
                                subscript_tag)) []))) | Src
                                Aw8update_unsafe -> Op t (MemOp
                                UpdateByte) xs | Src Strsub -> Let t xs
                                (If t (Op t (MemOp (BoundsCheckByte F))
                                [Var t 0; Var t 1])
                              (Op t (MemOp DerefByteVec) [Var t 0;
                                Var t 1])
                              (Raise t (Op t (BlockOp (Cons
                                subscript_tag)) []))) | Src (Shift x1 x2
                                x3) -> Op t (WordOp (WordShift x1 x2
                                x3)) xs | Src Eval -> Op t Install xs |
                                Src (ThunkOp op) -> Op t (ThunkOp op) xs
                                | Src (Arith a ty) -> compile_arith t a
                                ty xs | Src (FromTo (WordT W8) IntT) ->
                                arg1 xs (\x. x) | Src (FromTo (WordT
                                W64) IntT) -> Op t (WordOp WordToInt) xs
                                | Src (FromTo IntT (WordT W8)) -> arg1
                                xs (\x. Op t (IntOp Mod) [Op t (IntOp
                                (Const 256)) []; x]) | Src (FromTo IntT
                                (WordT W64)) -> Op t (WordOp
                                WordFromInt) xs | Src (FromTo IntT
                                CharT) -> Let t xs (If t (Op t (IntOp
                                (LESS)) [Op None (IntOp (Const 0)) [];
                                Var t 0])
                         (Raise t (Op t (BlockOp (Cons chr_tag)) []))
                         (If t (Op t (IntOp (LESS)) [Var t 0; Op None
                           (IntOp (Const 255)) []])
                           (Raise t (Op t (BlockOp (Cons chr_tag))
                             []))
                           (Var t 0))) | Src (FromTo Float64T
                             (WordT W64)) -> Let None xs (Var None 0)
                             | Src (FromTo (WordT W64) Float64T) ->
                             Let None xs (Var None 0) | Src _12 ->
                             Let None xs (Var None 0))`;;
hol4_overload "compile_op" "flat_to_clos_compile_op";;

let join_strings_def = cake_define
  `join_strings (x:mlstring) y =
     (if strlen x = 0 then y else mlstring_concat [x; implode "_";
       y])`;;

let dest_nop_def = cake_define
  `dest_nop op e =
     (if op = Src (FromTo IntT (WordT W8)) then
       (match e with [App _13 op1 [x]] -> (if op1 = Src (FromTo CharT
         IntT) then SOME x else NONE) | _14 -> NONE) else if op = Src
         (FromTo IntT CharT) then
       (match e with [App _15 op1 [x]] -> (if op1 = Src (FromTo
         (WordT W8) IntT) then SOME x else NONE) | _16 -> NONE) else
         NONE)`;;

let dest_Constant_def = cake_define
  `flat_to_clos_dest_Constant x1 =
      match x1 with
        (Op t (BlockOp (Constant c)) []) -> SOME c
      | (Op t (IntOp (Const i)) []) -> SOME (ConstInt i)
      | (Op t (BlockOp (Cons n)) []) -> SOME (ConstCons n [])
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
     (if NULL xs then Op t (BlockOp (Cons tag)) [] else
     match dest_Constants xs with NONE -> Op t (BlockOp (Cons
       tag)) xs | SOME cs -> Op t (BlockOp (Constant (ConstCons tag
       (REVERSE cs)))) [])`;;

let _ = size_thms "exp6";;
(* HOL4 termination: \\ rw [] \\ `!funs f v x. MEM (f,v,x) funs ==>
   exp_size x < flatLang$exp1_size funs` by (Induct \\ fs [] \\ rw []
   \\ fs [flatLangTheory.exp_size_def] \\ res_tac \\ fs []) \\
   res_tac \\ fs [dest_pat_thm] \\ fs [flatLangTheory.exp_size_def]
   \\ gvs [dest_nop_thm] \\ fs [flatLangTheory.exp_size_def] *)
let compile_def = cake_define_wf
  `MEASURE (exp6_size o SND)`
  `flat_to_clos_compile m x2 =
        match x2 with
          [] -> []
        | (x :: y :: xs) -> flat_to_clos_compile m [x] ++
          flat_to_clos_compile m (y :: xs)
        | [flatLang_Raise t e] -> [closLang_Raise t (HD
          (flat_to_clos_compile m [e]))]
        | [Lit t l] -> [compile_lit t l]
        | [Var_local t v] -> [Var t (findi (SOME v) m)]
        | [Con t n es] ->
        let tag = (match n with SOME (t,_21) -> t | _22 -> 0) in
          [SmartCons t tag (flat_to_clos_compile m (REVERSE es))]
        | [App t op es] ->
        match dest_nop op es with SOME e -> flat_to_clos_compile m
          [e] | NONE -> [compile_op t op (flat_to_clos_compile m
          (REVERSE es))]
        | [Fun t v e] ->
        [Fn t NONE NONE 1 (HD (flat_to_clos_compile (SOME v :: m)
          [e]))]
        | [If t x1 x2 x3] ->
        [If t (HD (flat_to_clos_compile m [x1]))
              (HD (flat_to_clos_compile m [x2]))
              (HD (flat_to_clos_compile m [x3]))]
        | [Let t vo e1 e2] ->
        [Let t (flat_to_clos_compile m [e1]) (HD
          (flat_to_clos_compile (vo :: m) [e2]))]
        | [Mat t e pes] -> [Op t (IntOp (Const 0)) []]
        | [Handle t e pes] ->
        match dest_pat pes with SOME (v,h) -> [Handle t (HD
          (flat_to_clos_compile m [e])) (HD (flat_to_clos_compile (SOME
          v :: m) [h]))] | _23 -> flat_to_clos_compile m [e]
        | [Letrec t funs e] ->
        let new_m = MAP (\n. SOME (FST n)) funs ++ m in
          [Letrec (MAP (\n. join_strings t (FST n)) funs) NONE NONE
             (MAP (\(f,v,x). (1,HD (flat_to_clos_compile (SOME v ::
               new_m) [x]))) funs)
             (HD (flat_to_clos_compile new_m [e]))]`;;
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
