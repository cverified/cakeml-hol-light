(* ======================================================== *)
(*  flat_to_clos: ported from HOL4's
    compiler/backend/flat_to_closScript.sml
    A definition theory, with 17 definitions and 9 theorems.  Needed
    by backend.ml, backendProof.ml, flat_to_closProof.ml,
    source_evalProof.ml, to_closProg.ml and to_data_cv.ml.  *)
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
     [flat_Pvar v,h] -> SOME ((v:mlstring),h)
   | _ -> NONE`;;

let dest_pat_pmatch = prove
 (`dest_pat x =
     match x with [(flat_Pvar v,h)] -> SOME ((v:mlstring),h) | _ -> NONE`,
  CHEAT_TAC);;

let dest_pat_thm = prove
 (`dest_pat pes = SOME (p_1,p_2) <=> pes = [(flat_Pvar p_1,p_2)]`,
  CHEAT_TAC);;

let compile_lit_def = new_definition
  `compile_lit t l =
     clos_Op t
      (match l with ast_IntLit i -> clos_IntOp (clos_Const i)
       | ast_Char c -> clos_IntOp (clos_Const (&(ORD c)))
       | ast_StrLit s -> clos_BlockOp (clos_Constant (ConstStr s))
       | ast_Word8 b -> clos_IntOp (clos_Const (&(w2n b)))
       | ast_Word64 w -> clos_BlockOp (clos_Constant (ConstWord64 w))
       | ast_Float64 w -> clos_BlockOp (clos_Constant (ConstWord64 w)))
         []`;;

let flat_to_clos_arg1_def = new_definition
  `flat_to_clos_arg1 xs f =
     match xs with [x] -> f x | _ -> clos_Let backend_common_None xs
       (clos_Var backend_common_None 0)`;;

let arg1_pmatch = prove
 (`flat_to_clos_arg1 xs f =
     match xs with [x] -> f x | _ -> clos_Let backend_common_None xs
       (clos_Var backend_common_None 0)`,
  CHEAT_TAC);;

let flat_to_clos_arg2_def = new_definition
  `flat_to_clos_arg2 xs f =
     match xs with [x; y] -> f x y | _ -> clos_Let backend_common_None xs
       (clos_Var backend_common_None 0)`;;

(* arg2_pmatch *)
let flat_to_clos_arg2_pmatch = prove
 (`flat_to_clos_arg2 xs f =
     match xs with [x; y] -> f x y | _ -> clos_Let backend_common_None xs
       (clos_Var backend_common_None 0)`,
  CHEAT_TAC);;

let var_fun m n =
  list_mk_icomb "clos_Var" [`t:tra`; mk_small_numeral (m - n)];;

let check1 tm var =
  vsubst [var 2,`v2:clos_exp`; var 1,`v1:clos_exp`;
          var 0,`v0:clos_exp`; tm,`tm:clos_exp`]
  `clos_If t
     (clos_Op t (clos_IntOp clos_Less)
        [clos_Op t (clos_IntOp (clos_Const (&0))) [];
         v2])
     (clos_Raise t (clos_Op t
        (clos_BlockOp (clos_Cons subscript_tag)) []))
     (clos_If t
       (clos_Op t (clos_IntOp clos_Less)
          [clos_Op t (clos_IntOp (clos_Const (&0))) [];
           v1])
       (clos_Raise t (clos_Op t
          (clos_BlockOp (clos_Cons subscript_tag)) []))
       (clos_If t
         (clos_Op t (clos_MemOp (clos_BoundsCheckByte T))
            [clos_Op t (clos_IntOp clos_Add) [v2; v1];
             v0])
         tm
         (clos_Raise t (clos_Op t
            (clos_BlockOp (clos_Cons subscript_tag))
            []))))`;;

let checkT =
  check1 `clos_Op t (clos_MemOp (clos_CopyByte T))
            [clos_Var t 0; clos_Var t 1; clos_Var t 2]`
         (var_fun 2);;

let checkF =
  check1
  `clos_If t
     (clos_Op t (clos_IntOp clos_Less)
        [clos_Op t (clos_IntOp (clos_Const (&0))) [];
         clos_Var t 0])
     (clos_Raise t (clos_Op t
        (clos_BlockOp (clos_Cons subscript_tag)) []))
     (clos_If t
       (clos_Op t (clos_MemOp (clos_BoundsCheckByte T))
          [clos_Op t (clos_IntOp clos_Add)
             [clos_Var t 2; clos_Var t 0];
           clos_Var t 1])
       (clos_Op t (clos_MemOp (clos_CopyByte F))
          [clos_Var t 0; clos_Var t 1; clos_Var t 2;
           clos_Var t 3; clos_Var t 4])
       (clos_Raise t (clos_Op t
          (clos_BlockOp (clos_Cons subscript_tag)) [])))`
  (var_fun 4);;

let CopyByteStr_def = new_definition
  (mk_eq (`(CopyByteStr (t:tra)):clos_exp`,checkT));;

let CopyByteAw8_def = new_definition
  (mk_eq (`(CopyByteAw8 (t:tra)):clos_exp`,checkF));;

let compile_arith_def = new_definition
  `compile_arith t (a:ast_arith) ty xs =
     match ty with ast_IntT -> (match a with ast_Add -> clos_Op t
       (clos_IntOp clos_Add) xs
                | ast_Sub -> clos_Op t (clos_IntOp clos_Sub) xs
                | ast_Mul -> clos_Op t (clos_IntOp clos_Mult) xs
                | ast_Div -> clos_Let t xs (clos_If t (clos_Op t
                  (clos_BlockOp clos_Equal) [clos_Var t 0; clos_Op t
                  (clos_IntOp (clos_Const (&0))) []])
                              (clos_Raise t (clos_Op t (clos_BlockOp
                                (clos_Cons div_tag)) []))
                              (clos_Op t (clos_IntOp clos_Div) [clos_Var t
                                0; clos_Var t 1]))
                | ast_Mod -> clos_Let t xs (clos_If t (clos_Op t
                  (clos_BlockOp clos_Equal) [clos_Var t 0; clos_Op t
                  (clos_IntOp (clos_Const (&0))) []])
                              (clos_Raise t (clos_Op t (clos_BlockOp
                                (clos_Cons div_tag)) []))
                              (clos_Op t (clos_IntOp clos_Mod) [clos_Var t
                                0; clos_Var t 1]))
                | _ -> clos_Let backend_common_None xs (clos_Var
                  backend_common_None 0))
     | ast_Float64T -> (match a with ast_Abs -> clos_Op t (clos_WordOp
       (FP_uop fpSem_FP_Abs)) xs
                    | ast_Neg -> clos_Op t (clos_WordOp (FP_uop
                      fpSem_FP_Neg)) xs
                    | ast_Sqrt -> clos_Op t (clos_WordOp (FP_uop
                      fpSem_FP_Sqrt)) xs
                    | ast_Add -> clos_Op t (clos_WordOp (FP_bop
                      fpSem_FP_Add)) xs
                    | ast_Sub -> clos_Op t (clos_WordOp (FP_bop
                      fpSem_FP_Sub)) xs
                    | ast_Mul -> clos_Op t (clos_WordOp (FP_bop
                      fpSem_FP_Mul)) xs
                    | ast_Div -> clos_Op t (clos_WordOp (FP_bop
                      fpSem_FP_Div)) xs
                    | ast_FMA -> clos_Op t (clos_WordOp (FP_top FP_Fma)) xs
                    | _ -> clos_Let backend_common_None xs (clos_Var
                      backend_common_None 0))
     | ast_WordT ws -> (match a with ast_Add -> clos_Op t (clos_WordOp
       (WordOpw ws backend_common_Add)) xs
                    | ast_Sub -> clos_Op t (clos_WordOp (WordOpw ws
                      backend_common_Sub)) xs
                    | ast_And -> clos_Op t (clos_WordOp (WordOpw ws
                      backend_common_Andw)) xs
                    | ast_Or -> clos_Op t (clos_WordOp (WordOpw ws
                      backend_common_Orw)) xs
                    | ast_Xor -> clos_Op t (clos_WordOp (WordOpw ws
                      backend_common_Xor)) xs
                    | _ -> clos_Let backend_common_None xs (clos_Var
                      backend_common_None 0))
     | ast_BoolT -> clos_Op t (clos_BlockOp clos_BoolNot) xs
     | _ -> clos_Let backend_common_None xs (clos_Var backend_common_None
       0)`;;

let flat_to_clos_compile_op_def = new_definition
  `flat_to_clos_compile_op t op xs =
     match op with flat_TagLenEq tag n -> clos_Op t (clos_BlockOp
       (clos_TagLenEq tag n)) xs
     | flat_LenEq n -> clos_Op t (clos_BlockOp (clos_LenEq n)) xs
     | flat_El n -> flat_to_clos_arg1 xs (\x. clos_Op t (clos_MemOp clos_El)
       [clos_Op backend_common_None (clos_IntOp (clos_Const (&n))) []; x])
     | flat_GlobalVarAlloc n -> clos_Let t xs (clos_Op t (clos_GlobOp
       clos_AllocGlobal) [clos_Op t (clos_IntOp (clos_Const (&n))) []])
     | flat_GlobalVarInit n -> clos_Op t (clos_GlobOp (clos_SetGlobal (n +
       1))) xs
     | flat_GlobalVarLookup n -> clos_Op t (clos_GlobOp (clos_Global (n +
       1))) xs
     | flat_Id -> flat_to_clos_arg1 xs (\x. x)
     | flat_Src ast_Opapp -> flat_to_clos_arg2 xs (\x f. clos_App t NONE f
       [x])
     | flat_Src ast_Opassign -> flat_to_clos_arg2 xs (\x y. clos_Op t
       (clos_MemOp clos_Update) [x; clos_Op backend_common_None (clos_IntOp
       (clos_Const (&0))) []; y])
     | flat_Src ast_Opref -> clos_Op t (clos_MemOp clos_Ref) xs
     | flat_Src ast_ConfigGC -> clos_Op t (clos_MemOp clos_ConfigGC) xs
     | flat_Src ast_Equality -> clos_Op t (clos_BlockOp clos_Equal) xs
     | flat_Src (ast_FFI n) -> clos_Op t (clos_FFI n) xs
     | flat_Src ast_ListAppend -> clos_Op t (clos_BlockOp clos_ListAppend)
       xs
     | flat_Src ast_Vlength -> clos_Op t (clos_BlockOp clos_LengthBlock) xs
     | flat_Src ast_Alength -> clos_Op t (clos_MemOp clos_Length) xs
     | flat_Src ast_Implode -> clos_Op t (clos_MemOp clos_FromListByte) xs
     | flat_Src ast_Explode -> clos_Op t (clos_MemOp clos_ToListByte) xs
     | flat_Src ast_Strlen -> clos_Op t (clos_MemOp clos_LengthByteVec) xs
     | flat_Src ast_Strcat -> clos_Op t (clos_MemOp clos_ConcatByteVec) xs
     | flat_Src ast_CopyStrStr -> clos_Let t xs (CopyByteStr t)
     | flat_Src ast_CopyStrAw8 -> clos_Let t xs (CopyByteAw8 t)
     | flat_Src ast_CopyAw8Str -> clos_Let t xs (CopyByteStr t)
     | flat_Src ast_CopyAw8Aw8 -> clos_Let t xs (CopyByteAw8 t)
     | flat_Src ast_XorAw8Str_unsafe -> clos_Op t (clos_MemOp clos_XorByte)
       xs
     | flat_Src ast_VfromList -> clos_Op t (clos_BlockOp (clos_FromList 0))
       xs
     | flat_Src (ast_Test test test_ty) ->
          (match test_ty with ast_BoolT -> clos_Op t (clos_BlockOp
            (clos_BoolTest test)) xs
           | ast_CharT -> clos_Op t (clos_WordOp (WordTest ast_W8 test)) xs
           | ast_WordT ast_W8 -> clos_Op t (clos_WordOp (WordTest ast_W8
             test)) xs
           | ast_IntT -> (match test with ast_Compare ast_Lt -> clos_Op t
             (clos_IntOp clos_Less) xs
                           | ast_Compare ast_Leq -> clos_Op t (clos_IntOp
                             clos_LessEq) xs
                           | ast_Compare ast_Gt -> clos_Op t (clos_IntOp
                             clos_Greater) xs
                           | ast_Compare ast_Geq -> clos_Op t (clos_IntOp
                             clos_GreaterEq) xs
                           | _ -> clos_Op t (clos_BlockOp clos_Equal) xs)
           | ast_Float64T -> (match test with ast_Compare ast_Lt -> clos_Op
             t (clos_WordOp (FP_cmp FP_Less)) xs
                           | ast_Compare ast_Leq -> clos_Op t (clos_WordOp
                             (FP_cmp FP_LessEqual)) xs
                           | ast_Compare ast_Gt -> clos_Op t (clos_WordOp
                             (FP_cmp FP_Greater)) xs
                           | ast_Compare ast_Geq -> clos_Op t (clos_WordOp
                             (FP_cmp FP_GreaterEqual)) xs
                           | _ -> clos_Op t (clos_WordOp (FP_cmp FP_Equal))
                             xs)
           | ast_StrT -> (match test with ast_Compare opb -> clos_Op t
             (clos_MemOp (clos_StringCmp F opb)) xs
                           | ast_AltCompare opb -> clos_Op t (clos_MemOp
                             (clos_StringCmp T opb)) xs
                           | _ -> clos_Op t (clos_BlockOp clos_Equal) xs)
           | _ -> clos_Op t (clos_BlockOp clos_Equal) xs)
     | flat_Src ast_Aw8length -> clos_Op t (clos_MemOp clos_LengthByte) xs
     | flat_Src ast_AallocFixed -> clos_Op t (clos_MemOp clos_Ref) xs
     | flat_Src ast_Aalloc -> clos_Let t xs (clos_If t (clos_Op t
       (clos_IntOp clos_Less) [clos_Op t (clos_IntOp (clos_Const (&0))) [];
       clos_Var t 1])
                              (clos_Raise t (clos_Op t (clos_BlockOp
                                (clos_Cons subscript_tag)) []))
                              (clos_Op t (clos_MemOp clos_RefArray)
                                [clos_Var t 0; clos_Var t 1]))
     | flat_Src ast_Aw8alloc -> clos_Let t xs (clos_If t (clos_Op t
       (clos_IntOp clos_Less) [clos_Op t (clos_IntOp (clos_Const (&0))) [];
       clos_Var t 1])
                              (clos_Raise t (clos_Op t (clos_BlockOp
                                (clos_Cons subscript_tag)) []))
                              (clos_Op t (clos_MemOp (clos_RefByte F))
                                [clos_Var t 0; clos_Var t 1]))
     | flat_Src ast_Vsub -> clos_Let t xs (clos_If t (clos_Op t
       (clos_BlockOp clos_BoundsCheckBlock) [clos_Var t 0; clos_Var t 1])
                              (clos_Op t (clos_MemOp clos_El) [clos_Var t 0;
                                clos_Var t 1])
                              (clos_Raise t (clos_Op t (clos_BlockOp
                                (clos_Cons subscript_tag)) [])))
     | flat_Src ast_Vsub_unsafe -> clos_Op t (clos_MemOp clos_El) xs
     | flat_Src ast_Asub -> clos_Let t xs (clos_If t (clos_Op t (clos_MemOp
       clos_BoundsCheckArray) [clos_Var t 0; clos_Var t 1])
                              (clos_Op t (clos_MemOp clos_El) [clos_Var t 0;
                                clos_Var t 1])
                              (clos_Raise t (clos_Op t (clos_BlockOp
                                (clos_Cons subscript_tag)) [])))
     | flat_Src ast_Asub_unsafe -> clos_Op t (clos_MemOp clos_El) xs
     | flat_Src ast_Aupdate -> clos_Let t xs (clos_If t (clos_Op t
       (clos_MemOp clos_BoundsCheckArray) [clos_Var t 1; clos_Var t 2])
                              (clos_Op t (clos_MemOp clos_Update) [clos_Var
                                t 0; clos_Var t 1; clos_Var t 2])
                              (clos_Raise t (clos_Op t (clos_BlockOp
                                (clos_Cons subscript_tag)) [])))
     | flat_Src ast_Aupdate_unsafe -> clos_Op t (clos_MemOp clos_Update) xs
     | flat_Src ast_Aw8sub -> clos_Let t xs (clos_If t (clos_Op t
       (clos_MemOp (clos_BoundsCheckByte F)) [clos_Var t 0; clos_Var t 1])
                              (clos_Op t (clos_MemOp clos_DerefByte)
                                [clos_Var t 0; clos_Var t 1])
                              (clos_Raise t (clos_Op t (clos_BlockOp
                                (clos_Cons subscript_tag)) [])))
     | flat_Src ast_Aw8sub_unsafe -> clos_Op t (clos_MemOp clos_DerefByte)
       xs
     | flat_Src ast_Aw8update -> clos_Let t xs (clos_If t (clos_Op t
       (clos_MemOp (clos_BoundsCheckByte F)) [clos_Var t 1; clos_Var t 2])
                              (clos_Op t (clos_MemOp clos_UpdateByte)
                                [clos_Var t 0; clos_Var t 1; clos_Var t 2])
                              (clos_Raise t (clos_Op t (clos_BlockOp
                                (clos_Cons subscript_tag)) [])))
     | flat_Src ast_Aw8update_unsafe -> clos_Op t (clos_MemOp
       clos_UpdateByte) xs
     | flat_Src ast_Strsub -> clos_Let t xs (clos_If t (clos_Op t
       (clos_MemOp (clos_BoundsCheckByte F)) [clos_Var t 0; clos_Var t 1])
                              (clos_Op t (clos_MemOp clos_DerefByteVec)
                                [clos_Var t 0; clos_Var t 1])
                              (clos_Raise t (clos_Op t (clos_BlockOp
                                (clos_Cons subscript_tag)) [])))
     | flat_Src (ast_Shift x1 x2 x3) -> clos_Op t (clos_WordOp (WordShift x1
       x2 x3)) xs
     | flat_Src ast_Eval -> clos_Op t clos_Install xs
     | flat_Src (ast_ThunkOp op) -> clos_Op t (clos_ThunkOp op) xs
     | flat_Src (ast_Arith a ty) -> compile_arith t a ty xs
     | flat_Src (ast_FromTo (ast_WordT ast_W8) ast_IntT) ->
       flat_to_clos_arg1 xs (\x. x)
     | flat_Src (ast_FromTo (ast_WordT ast_W64) ast_IntT) -> clos_Op t
       (clos_WordOp WordToInt) xs
     | flat_Src (ast_FromTo ast_IntT (ast_WordT ast_W8)) ->
       flat_to_clos_arg1 xs (\x. clos_Op t (clos_IntOp clos_Mod) [clos_Op t
       (clos_IntOp (clos_Const (&256))) []; x])
     | flat_Src (ast_FromTo ast_IntT (ast_WordT ast_W64)) -> clos_Op t
       (clos_WordOp WordFromInt) xs
     | flat_Src (ast_FromTo ast_IntT ast_CharT) -> clos_Let t xs (clos_If t
       (clos_Op t (clos_IntOp clos_Less) [clos_Op backend_common_None
       (clos_IntOp (clos_Const (&0))) []; clos_Var t 0])
                         (clos_Raise t (clos_Op t (clos_BlockOp (clos_Cons
                           chr_tag)) []))
                         (clos_If t (clos_Op t (clos_IntOp clos_Less)
                           [clos_Var t 0; clos_Op backend_common_None
                           (clos_IntOp (clos_Const (&255))) []])
                           (clos_Raise t (clos_Op t (clos_BlockOp (clos_Cons
                             chr_tag)) []))
                           (clos_Var t 0)))
     | flat_Src (ast_FromTo ast_Float64T (ast_WordT ast_W64)) -> clos_Let
       backend_common_None xs (clos_Var backend_common_None 0)
     | flat_Src (ast_FromTo (ast_WordT ast_W64) ast_Float64T) -> clos_Let
       backend_common_None xs (clos_Var backend_common_None 0)
     | flat_Src _ -> clos_Let backend_common_None xs (clos_Var
       backend_common_None 0)`;;

let join_strings_def = new_definition
  `join_strings (x:mlstring) y =
     if strlen x = 0 then y
     else mlstring_concat [x; implode "_"; y]`;;

let dest_nop_def = new_definition
  `dest_nop op e =
     if op = flat_Src (ast_FromTo ast_IntT (ast_WordT ast_W8)) then
       (match e with [flat_App _ op1 [x]] -> (if op1 = flat_Src (ast_FromTo
         ast_CharT ast_IntT) then SOME x else NONE)
        | _ -> NONE)
     else if op = flat_Src (ast_FromTo ast_IntT ast_CharT) then
       (match e with [flat_App _ op1 [x]] -> (if op1 = flat_Src (ast_FromTo
         (ast_WordT ast_W8) ast_IntT) then SOME x else NONE)
        | _ -> NONE)
     else NONE`;;

let dest_nop_thm = prove
 (`dest_nop op es = SOME x <=>
     (?t. op = flat_Src (ast_FromTo ast_IntT (ast_WordT ast_W8)) /\ es =
       [flat_App t (flat_Src (ast_FromTo ast_CharT ast_IntT)) [x]]) \/
     (?t. op = flat_Src (ast_FromTo ast_IntT ast_CharT) /\ es = [flat_App
       t (flat_Src (ast_FromTo (ast_WordT ast_W8) ast_IntT)) [x]])`,
  CHEAT_TAC);;

let flat_to_clos_dest_Constant_def = new_definition
  `flat_to_clos_dest_Constant x1' =
   match x1' with
     clos_Op t (clos_BlockOp (clos_Constant c)) [] -> SOME c
   | clos_Op t (clos_IntOp (clos_Const i)) [] -> SOME (ConstInt i)
   | clos_Op t (clos_BlockOp (clos_Cons n)) [] -> SOME (ConstCons n [])
   | _ -> NONE`;;

(* dest_Constant_pmatch *)
let flat_to_clos_dest_Constant_pmatch = prove
 (`flat_to_clos_dest_Constant xs =
     match xs with clos_Op t (clos_BlockOp (clos_Constant x)) [] -> SOME x
     | clos_Op t (clos_IntOp (clos_Const i)) [] -> SOME (ConstInt i)
     | clos_Op t (clos_BlockOp (clos_Cons n)) [] -> SOME (ConstCons n [])
     | _ -> NONE`,
  CHEAT_TAC);;

let dest_Constants_def,dest_Constants_ind = define_rec
  `(dest_Constants [] = SOME []) /\
   (dest_Constants (CONS c cs) =
      match flat_to_clos_dest_Constant c with NONE -> NONE
      | SOME x -> (match dest_Constants cs with NONE -> NONE
                  | SOME xs -> SOME (CONS x xs)))`;;

let SmartCons_def = new_definition
  `SmartCons t tag xs =
     if NULL xs then clos_Op t (clos_BlockOp (clos_Cons tag)) [] else match
       dest_Constants xs with NONE -> clos_Op t (clos_BlockOp (clos_Cons tag))
       xs
     | SOME cs -> clos_Op t (clos_BlockOp (clos_Constant (ConstCons tag
       (REVERSE cs)))) []`;;

make_size "flat_exp";;
(* the clauses in two quotations: funs is ((varN # varN # exp) list) and
   (_#_#_)list; t is tra and varN, which one quotation cannot typecheck *)
let flat_to_clos_compile_def,flat_to_clos_compile_ind =
  assume_definition_rec_clauses
  "termination (CHEAT_TAC)"
  [`(flat_to_clos_compile m [] = []) /\
    (flat_to_clos_compile m (CONS x (CONS y xs)) = APPEND
    (flat_to_clos_compile m [x]) (flat_to_clos_compile m (CONS y xs))) /\
    (flat_to_clos_compile m [flat_Raise t e] = [clos_Raise t (HD
    (flat_to_clos_compile m [e]))]) /\
    (flat_to_clos_compile m [flat_Lit t l] = [compile_lit t l]) /\
    (flat_to_clos_compile m [flat_Var_local t v] = [clos_Var t
    (indexedLists_findi (SOME v) m)]) /\
    (flat_to_clos_compile m [flat_Con t n es] =
         let tag = (match n with SOME (t,_) -> t | _ -> 0) in
           [SmartCons t tag (flat_to_clos_compile m (REVERSE es))]) /\
    (flat_to_clos_compile m [flat_App t op es] =
         match dest_nop op es with SOME e -> flat_to_clos_compile m [e]
         | NONE -> [flat_to_clos_compile_op t op (flat_to_clos_compile
             m (REVERSE es))]) /\
    (flat_to_clos_compile m [flat_If t x1 x2 x3] =
         [clos_If t (HD (flat_to_clos_compile m [x1]))
               (HD (flat_to_clos_compile m [x2]))
               (HD (flat_to_clos_compile m [x3]))]) /\
    (flat_to_clos_compile m [flat_Let t vo e1 e2] =
         [clos_Let t (flat_to_clos_compile m [e1]) (HD
             (flat_to_clos_compile (CONS vo m) [e2]))]) /\
    (flat_to_clos_compile m [flat_Mat t e pes] = [clos_Op t (clos_IntOp
    (clos_Const (&0))) []]) /\
    (flat_to_clos_compile m [flat_Handle t e pes] =
         match dest_pat pes with SOME (v,h) -> [clos_Handle t (HD
             (flat_to_clos_compile m [e])) (HD (flat_to_clos_compile (CONS
             (SOME v) m) [h]))]
         | _ -> flat_to_clos_compile m [e])`;
   `(flat_to_clos_compile m [flat_Fun t v e] =
         [clos_Fn t NONE NONE 1 (HD (flat_to_clos_compile (CONS (SOME
             v) m) [e]))]) /\
    (flat_to_clos_compile m [flat_Letrec t funs e] =
         let new_m = APPEND (MAP (\n. SOME (FST n)) funs) m in
           [clos_Letrec (MAP (\n. join_strings t (FST n)) funs) NONE NONE
              (MAP (\(f,v,x). (1,HD (flat_to_clos_compile (CONS (SOME v)
                  new_m) [x]))) funs)
              (HD (flat_to_clos_compile new_m [e]))])`];;

let compile_decs_def,compile_decs_ind = define_rec
  `(flat_to_clos_compile_decs [] = []) /\
   (flat_to_clos_compile_decs (CONS e xs) = APPEND (flat_to_clos_compile
    [] [e]) (flat_to_clos_compile_decs xs))`;;

let flat_to_clos_compile_prog_def = new_definition
  `flat_to_clos_compile_prog xs =
     attach_interpreter (flat_to_clos_compile_decs xs)`;;

let inc_compile_decs_def = new_definition
  `inc_compile_decs decs =
     let xs = APPEND (flat_to_clos_compile_decs decs)
       (flat_to_clos_compile_decs [flat_Con backend_common_None NONE []]) in
       (insert_interp xs,[])`;;

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
