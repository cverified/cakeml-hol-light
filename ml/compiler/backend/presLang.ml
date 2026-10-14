(* ======================================================== *)
(*  presLang: ported from HOL4's
    compiler/backend/presLangScript.sml  *)
(* ======================================================== *)

(*
  Functions for converting various intermediate languages
  into displayLang representations.
*)

needs "basis/pure/mlint.ml";;
needs "basis/pure/mloption.ml";;
needs "compiler/backend/bvi.ml";;
needs "compiler/backend/bvl.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/clos_to_bvl.ml";;
needs "compiler/backend/dataLang.ml";;
needs "compiler/backend/displayLang.ml";;
needs "compiler/backend/flatLang.ml";;
needs "compiler/backend/labLang.ml";;
needs "compiler/backend/source_to_flat.ml";;
needs "compiler/backend/stackLang.ml";;
needs "compiler/backend/wordLang.ml";;
needs "semantics/ast.ml";;

(* basics *)

let empty_item_def = cake_define
  `empty_item name = displayLang_String name`;;

let num_to_display_def = cake_define
  `num_to_display (n:num) = displayLang_String ((num_to_str) n)`;;

let int_to_display_def = cake_define
  `int_to_display (i:int) = displayLang_String ((num_to_str) i)`;;

let string_imp_def = cake_define
  `string_imp s = displayLang_String s`;;

let item_with_num_def = cake_define
  `item_with_num name n = displayLang_Item NONE name [num_to_display
  n]`;;

let item_with_nums_def = cake_define
  `item_with_nums name ns = displayLang_Item NONE name (MAP
  num_to_display ns)`;;

let bool_to_display_def = cake_define
  `bool_to_display b = empty_item (if b then (strlit "True") else
  (strlit "False"))`;;

let num_to_hex_def = cake_define
  `num_to_hex n =
     (if n < 16 then [] else num_to_hex (n DIV 16)) ++
     num_to_hex_digit (n MOD 16)`;;

let separate_lines_def = cake_define
  `separate_lines name xs = displayLang_List (displayLang_String name
  :: xs)`;;

(* num_to_hex "implements" words$word_to_hex_string in a
   simple way that the translator can handle. these lemmas
   check that is true. *)

let num_to_hex_mlstring_def = cake_define
  `num_to_hex_mlstring n = implode ("0x" ++ num_to_hex n)`;;

let word_to_display_def = cake_define
  `word_to_display w = empty_item (num_to_hex_mlstring (w2n w))`;;

let item_with_word_def = cake_define
  `item_with_word name w = displayLang_Item NONE name
  [word_to_display w]`;;

let lit_to_display_def = cake_define
  `(lit_to_display (ast_IntLit i) =
     displayLang_Item NONE (strlit "IntLit") [empty_item
       ((num_to_str) i)]) /\
   (lit_to_display (ast_Char c) =
     displayLang_Item NONE (strlit "Char") [empty_item (implode
       ("#\"" ++ [c] ++ "\""))]) /\
   (lit_to_display (ast_StrLit s) =
     displayLang_Item NONE (strlit "StrLit") [string_imp s]) /\
   (lit_to_display (ast_Word8 w) =
     displayLang_Item NONE (strlit "Word8") [word_to_display w]) /\
   (lit_to_display (ast_Word64 w) =
     displayLang_Item NONE (strlit "Word64") [word_to_display w]) /\
   (lit_to_display (ast_Float64 w) =
     displayLang_Item NONE (strlit "Float64") [word_to_display w])`;;

(* HOL4 overload (expanded in the port):
     list_to_display = λf xs. displayLang$Tuple (MAP f xs) *)

(* HOL4 overload (expanded in the port):
     option_to_display = λf opt. case opt of
          | NONE => empty_item «none»
          | SOME opt' => Item NONE «some» [f opt'] *)
(* source *)

let fp_cmp_to_display_def = cake_define
  `fp_cmp_to_display cmp = (match cmp with FP_Less -> empty_item
  (strlit "FP_Less") | FP_LessEqual -> empty_item (strlit
  "FP_LessEqual") | FP_Greater -> empty_item (strlit "FP_Greater") |
  FP_GreaterEqual -> empty_item (strlit "FP_GreaterEqual") | FP_Equal
  -> empty_item (strlit "FP_Equal"))`;;

let fp_uop_to_display_def = cake_define
  `fp_uop_to_display flatLang_op = (match flatLang_op with
  fpSem_FP_Abs -> empty_item (strlit "FP_Abs") | fpSem_FP_Neg ->
  empty_item (strlit "FP_Neg") | fpSem_FP_Sqrt -> empty_item (strlit
  "FP_Sqrt"))`;;

let fp_bop_to_display_def = cake_define
  `fp_bop_to_display flatLang_op = (match flatLang_op with
  fpSem_FP_Add -> empty_item (strlit "FP_Add") | fpSem_FP_Sub ->
  empty_item (strlit "FP_Sub") | fpSem_FP_Mul -> empty_item (strlit
  "FP_Mul") | fpSem_FP_Div -> empty_item (strlit "FP_Div"))`;;

let fp_top_to_display_def = cake_define
  `fp_top_to_display flatLang_op =
     (match flatLang_op with FP_Fma -> empty_item (strlit
       "FP_Fma"))`;;

let word_size_to_display_def = cake_define
  `(word_size_to_display ast_W8 = empty_item (strlit "W8")) /\
   (word_size_to_display closLang_W64 = empty_item (strlit "W64"))`;;

let opb_to_display_def = cake_define
  `(opb_to_display ast_Lt = empty_item (strlit "Lt")) /\
   (opb_to_display ast_Gt = empty_item (strlit "Gt")) /\
   (opb_to_display ast_Leq = empty_item (strlit "Leq")) /\
   (opb_to_display ast_Geq = empty_item (strlit "Geq"))`;;

let opw_to_display_def = cake_define
  `(opw_to_display backend_common_Andw = empty_item (strlit "Andw")) /\
   (opw_to_display backend_common_Orw = empty_item (strlit "Orw")) /\
   (opw_to_display asm_Xor = empty_item (strlit "Xor")) /\
   (opw_to_display asm_Add = empty_item (strlit "Add")) /\
   (opw_to_display asm_Sub = empty_item (strlit "Sub"))`;;

let shift_to_display_def = cake_define
  `(shift_to_display Lsl = empty_item (strlit "Lsl")) /\
   (shift_to_display Lsr = empty_item (strlit "Lsr")) /\
   (shift_to_display Asr = empty_item (strlit "Asr")) /\
   (shift_to_display Ror = empty_item (strlit "Ror"))`;;

let thunk_mode_to_display_def = cake_define
  `(thunk_mode_to_display Evaluated = empty_item (strlit "Evaluated"))
  /\
   (thunk_mode_to_display NotEvaluated = empty_item (strlit
     "NotEvaluated"))`;;

let thunk_op_to_display_def = cake_define
  `(thunk_op_to_display (AllocThunk m) =
     displayLang_Item NONE (strlit "AllocThunk")
       [thunk_mode_to_display m]) /\
   (thunk_op_to_display (UpdateThunk m) =
     displayLang_Item NONE (strlit "UpdateThunk")
       [thunk_mode_to_display m]) /\
   (thunk_op_to_display ForceThunk = empty_item (strlit
     "ForceThunk"))`;;

let test_to_display_def = cake_define
  `test_to_display (EQUAL) = empty_item (strlit "Equal") /\
   test_to_display (ast_Compare cmp) = displayLang_Item NONE (strlit
     "Compare") [opb_to_display cmp] /\
   test_to_display (ast_AltCompare cmp) = displayLang_Item NONE
     (strlit "AltCompare") [opb_to_display cmp]`;;

let arith_to_display_def = cake_define
  `arith_to_display asm_Add = empty_item (strlit "Add") /\
   arith_to_display asm_Sub = empty_item (strlit "Sub") /\
   arith_to_display ast_Mul = empty_item (strlit "Mul") /\
   arith_to_display asm_Div = empty_item (strlit "Div") /\
   arith_to_display closLang_Mod = empty_item (strlit "Mod") /\
   arith_to_display asm_And = empty_item (strlit "And") /\
   arith_to_display asm_Xor = empty_item (strlit "Xor") /\
   arith_to_display pattern_semantics_Or = empty_item (strlit "Or")
     /\
   arith_to_display ast_Neg = empty_item (strlit "Neg") /\
   arith_to_display pattern_semantics_Not = empty_item (strlit "Not")
     /\
   arith_to_display ast_Abs = empty_item (strlit "Abs") /\
   arith_to_display ast_Sqrt = empty_item (strlit "Sqrt") /\
   arith_to_display ast_FMA = empty_item (strlit "FMA")`;;

let prim_type_to_display_def = cake_define
  `prim_type_to_display ast_BoolT = empty_item (strlit "BoolT") /\
   prim_type_to_display ast_IntT = empty_item (strlit "IntT") /\
   prim_type_to_display ast_CharT = empty_item (strlit "CharT") /\
   prim_type_to_display ast_StrT = empty_item (strlit "StrT") /\
   prim_type_to_display ast_Float64T = empty_item (strlit "Float64T")
     /\
   prim_type_to_display (ast_WordT ast_W8) = empty_item (strlit
     "WordT_W8") /\
   prim_type_to_display (ast_WordT closLang_W64) = empty_item
     (strlit "WordT_W64")`;;

let lop_to_display_def = cake_define
  `lop_to_display Andalso = empty_item (strlit "Andalso") /\
   lop_to_display Orelse = empty_item (strlit "Orelse")`;;

let op_to_display_def = cake_define
  `op_to_display (p:ast_op) =
   (match p with wordLang_Shift ws sh num' -> displayLang_Item NONE
     (strlit "Shift")
                             [word_size_to_display ws;
                              shift_to_display sh;
                              num_to_display num'] | asm_Arith a ty
                                -> displayLang_Item NONE (strlit
                                "Arith")
                          [arith_to_display a;
                           prim_type_to_display ty] | ast_FromTo ty1
                             ty2 -> displayLang_Item NONE (strlit
                             "FromTo")
                          [prim_type_to_display ty1;
                           prim_type_to_display ty2] | asm_Test test
                             ty -> displayLang_Item NONE (strlit "Test")
                          [test_to_display test;
                           prim_type_to_display ty] | ast_Equality
                             -> empty_item (strlit "Equality") |
                             ast_Opapp -> empty_item (strlit "Opapp")
                             | ast_Opassign -> empty_item (strlit
                             "Opassign") | ast_Opref -> empty_item
                             (strlit "Opref") | ast_Opderef ->
                             empty_item (strlit "Opderef") |
                             ast_Aw8alloc -> empty_item (strlit
                             "Aw8alloc") | ast_Aw8sub -> empty_item
                             (strlit "Aw8sub") | ast_Aw8length ->
                             empty_item (strlit "Aw8length") |
                             ast_Aw8update -> empty_item (strlit
                             "Aw8update") | ast_CopyStrStr ->
                             empty_item (strlit "CopyStrStr") |
                             ast_CopyStrAw8 -> empty_item (strlit
                             "CopyStrAw8") | ast_CopyAw8Str ->
                             empty_item (strlit "CopyAw8Str") |
                             ast_CopyAw8Aw8 -> empty_item (strlit
                             "CopyAw8Aw8") | ast_Implode ->
                             empty_item (strlit "Implode") |
                             ast_Explode -> empty_item (strlit
                             "Explode") | ast_Strsub -> empty_item
                             (strlit "Strsub") | ast_Strlen ->
                             empty_item (strlit "Strlen") |
                             ast_Strcat -> empty_item (strlit
                             "Strcat") | ast_VfromList -> empty_item
                             (strlit "VfromList") | ast_Vsub ->
                             empty_item (strlit "Vsub") |
                             ast_Vsub_unsafe -> empty_item (strlit
                             "Vsub_unsafe") | ast_Vlength ->
                             empty_item (strlit "Vlength") |
                             ast_Aalloc -> empty_item (strlit
                             "Aalloc") | ast_AallocEmpty ->
                             empty_item (strlit "AallocEmpty") |
                             ast_AallocFixed -> empty_item (strlit
                             "AallocFixed") | ast_Asub -> empty_item
                             (strlit "Asub") | ast_Alength ->
                             empty_item (strlit "Alength") |
                             ast_Aupdate -> empty_item (strlit
                             "Aupdate") | ast_Asub_unsafe ->
                             empty_item (strlit "Asub_unsafe") |
                             ast_Aupdate_unsafe -> empty_item (strlit
                             "Aupdate_unsafe") | ast_Aw8sub_unsafe ->
                             empty_item (strlit "Aw8sub_unsafe") |
                             ast_Aw8update_unsafe -> empty_item
                             (strlit "Aw8update_unsafe") |
                             ast_XorAw8Str_unsafe -> empty_item
                             (strlit "XorAw8Str_unsafe") |
                             closLang_ListAppend -> empty_item
                             (strlit "ListAppend") |
                             closLang_ConfigGC -> empty_item (strlit
                             "ConfigGC") | wordLang_FFI v35 ->
                             empty_item (strlit "FFI v35") | ast_Eval
                             -> empty_item (strlit "Eval") |
                             ast_Env_id -> empty_item (strlit
                             "Env_id") | closLang_ThunkOp t ->
                             thunk_op_to_display t)`;;

let id_to_display_def = cake_define
  `id_to_display (Short n) =
     displayLang_Item NONE (strlit "Short") [displayLang_String n] /\
   id_to_display (Long n i) =
     displayLang_Item NONE (strlit "Long") [displayLang_String n;
       id_to_display i]`;;

(* HOL4 termination: *)
let ast_t_to_display_def = cake_define_wf
  `MEASURE (\x. match x with INL semanticPrimitives_v -> ast_t_size
  semanticPrimitives_v | INR semanticPrimitives_v -> list_size
  ast_t_size semanticPrimitives_v)`
  `ast_t_to_display c =
        match c with
          c ->
     match c with Atvar n -> displayLang_Item NONE (strlit "Atvar")
       [displayLang_String n] | Atfun t1 t2 -> displayLang_Item NONE
       (strlit "Atfun") [ast_t_to_display t1; ast_t_to_display t2] |
       Attup ts -> displayLang_Item NONE (strlit "Attup")
       [displayLang_Tuple (ast_t_to_display_list ts)] | Atapp ts id ->
       displayLang_Item NONE (strlit "Attup") [displayLang_Tuple
       (ast_t_to_display_list ts);
                              id_to_display id]
        | [] -> []
        | (x :: xs) ->
       ast_t_to_display x :: ast_t_to_display_list xs`;;

(* HOL4 termination: *)
let pat_to_display_def = cake_define_wf
  `MEASURE (\x. match x with INL semanticPrimitives_v -> pat_size
  semanticPrimitives_v | INR semanticPrimitives_v -> list_size pat_size
  semanticPrimitives_v)`
  `pat_to_display x1 =
        match x1 with
          (c:ast_pat) ->
     match c with flatLang_Pany -> displayLang_Item NONE (strlit
       "Pany") [] | flatLang_Pvar semanticPrimitives_v ->
       displayLang_Item NONE (strlit "Pvar") [displayLang_String
       semanticPrimitives_v] | flatLang_Plit l -> displayLang_Item NONE
       (strlit "Plit") [lit_to_display l] | flatLang_Pcon opt_id pats ->
         displayLang_Item NONE (strlit "Pcon") [(\f' opt. match opt
           with NONE -> empty_item (strlit "none") | SOME opt' ->
           displayLang_Item NONE (strlit "some") [f' opt'])
           id_to_display opt_id;
                           displayLang_Tuple (pat_to_display_list
                             pats)] | flatLang_Pas t
                             semanticPrimitives_v -> displayLang_Item
                             NONE (strlit "Pas") [pat_to_display t;
                             displayLang_String semanticPrimitives_v] |
                             flatLang_Pref t -> displayLang_Item NONE
                             (strlit "Pref") [pat_to_display t] |
                             ast_Ptannot x y -> displayLang_Item NONE
                             (strlit "Ptannot") [pat_to_display x;
                             ast_t_to_display y]
        | [] -> []
        | (x :: xs) ->
       pat_to_display x :: pat_to_display_list xs`;;

let exp_to_display_def = cake_define
  `exp_to_display x1 =
        match x1 with
          (c:ast_exp) ->
     match c with pattern_semantics_Lit l -> displayLang_Item NONE
       (strlit "Lit") [lit_to_display l] | flatLang_Raise e ->
       displayLang_Item NONE (strlit "Raise") [exp_to_display e] |
       flatLang_Con opt_id es -> displayLang_Item NONE (strlit "Con")
       [(\f' opt. match opt with NONE -> empty_item (strlit "none") |
       SOME opt' -> displayLang_Item NONE (strlit "some") [f' opt'])
       id_to_display opt_id;
                              displayLang_Tuple (exp_to_display_list
                                es)] | wordLang_Var id ->
                                displayLang_Item NONE (strlit "Var")
                                [id_to_display id] | flatLang_Fun n e ->
                                displayLang_Item NONE (strlit "Fun")
                                [displayLang_String n; exp_to_display e]
                                | flatLang_App flatLang_op es ->
                                displayLang_Item NONE (strlit "App")
                                (op_to_display flatLang_op ::
                              exp_to_display_list es) | ast_Log lop
                                e1 e2 -> displayLang_Item NONE (strlit
                                "Log") [lop_to_display lop;
                              exp_to_display e1;
                              exp_to_display e2] |
                                pattern_semantics_If e1 e2 e3 ->
                                displayLang_Item NONE (strlit "If")
                                [exp_to_display e1;
                              exp_to_display e2;
                              exp_to_display e3] | flatLang_Let n_opt
                                e1 e2 -> displayLang_Item NONE (strlit
                                "Let")
         [(\f' opt. match opt with NONE -> empty_item (strlit "none")
           | SOME opt' -> displayLang_Item NONE (strlit "some") [f'
           opt']) displayLang_String n_opt;
          exp_to_display e1;
          exp_to_display e2] | flatLang_Mat e pats ->
         displayLang_Item NONE (strlit "Mat")
         [exp_to_display e;
          displayLang_Tuple (pat_exp_to_display_list pats)] |
            flatLang_Handle e pats ->
         displayLang_Item NONE (strlit "Handle")
         [exp_to_display e;
          displayLang_Tuple (pat_exp_to_display_list pats)] |
            flatLang_Letrec fns e ->
         displayLang_Item NONE (strlit "Letrec")
         [displayLang_Tuple (fun_to_display_list fns);
          exp_to_display e] | ast_Tannot e _1 -> displayLang_Item
            NONE (strlit "Tannot") [exp_to_display e] | ast_Lannot e _2
            -> displayLang_Item NONE (strlit "Lannot") [exp_to_display
            e]
        | [] -> []
        | (x :: xs) ->
       exp_to_display x :: exp_to_display_list xs
        | [] -> []
        | ((p,e) :: xs) ->
       displayLang_Tuple [pat_to_display p; exp_to_display e] ::
       pat_exp_to_display_list xs
        | [] -> []
        | ((m,n,e) :: xs) ->
       displayLang_Tuple [displayLang_String m;
              displayLang_String n;
              exp_to_display e] ::
       fun_to_display_list xs`;;

(* HOL4 termination: *)
let source_to_display_dec_def = cake_define_wf
  `MEASURE (\x. match x with INL semanticPrimitives_v -> dec_size
  semanticPrimitives_v | INR semanticPrimitives_v -> list_size dec_size
  semanticPrimitives_v)`
  `source_to_display_dec x1 =
        match x1 with
          (d:dec) ->
     match d with Dlet _3 pattern_semantics_pat e -> displayLang_Item
       NONE (strlit "Dlet") [pat_to_display pattern_semantics_pat;
       exp_to_display e] | Dletrec _4 fns -> displayLang_Item NONE
       (strlit "Dletrec")
                             (MAP (\(m,n,e). displayLang_Tuple
                               [displayLang_String m;
                              displayLang_String n;
                              exp_to_display e]) fns) | Dtype _5 ts
                                -> displayLang_Item NONE (strlit
                                "Dtype") (MAP (\(ns,n,z).
                       displayLang_Tuple [displayLang_Tuple (MAP
                         displayLang_String ns);
                              displayLang_String n;
                              displayLang_Tuple (MAP (\(n,tys).
                                displayLang_Tuple [displayLang_String n;
                              displayLang_Tuple (MAP ast_t_to_display
                                tys)]) z)]) ts) | Dtabbrev _6 ns n ty ->
         displayLang_Item NONE (strlit "Dtabbrev") [displayLang_Tuple
           (MAP displayLang_String ns);
                              displayLang_String n;
                              ast_t_to_display ty] | Dexn _7 n tys ->
                                displayLang_Item NONE (strlit "Dexn")
                                [displayLang_String n;
                              displayLang_Tuple (MAP ast_t_to_display
                                tys)] | Dmod n ds -> displayLang_Item
                                NONE (strlit "Dmod") [displayLang_String
                                n;
                              displayLang_Tuple
                                (source_to_display_dec_list ds)] |
                                Dlocal xs ys -> displayLang_Item NONE
                                (strlit "Dlocal") [displayLang_Tuple
                                (source_to_display_dec_list xs);
                              displayLang_Tuple
                                (source_to_display_dec_list ys)] | Denv
                                n -> displayLang_Item NONE (strlit
                                "Denv") [displayLang_String n]
        | [] -> []
        | (x :: xs) ->
       source_to_display_dec x :: source_to_display_dec_list xs`;;

(* flatLang *)

let opt_con_to_display_def = cake_define
  `opt_con_to_display ocon = (match ocon with NONE -> empty_item
  (strlit "ConIdNone") | SOME (c,NONE) -> item_with_num (strlit
  "ConIdUntyped") c | SOME (c,SOME t) -> item_with_nums (strlit
  "ConIdTyped") [c; t])`;;

(* HOL4 termination: *)
let flat_pat_to_display_def = cake_define_wf
  `MEASURE (\x. match x with INL semanticPrimitives_v -> pat_size
  semanticPrimitives_v | INR semanticPrimitives_v -> list_size pat_size
  semanticPrimitives_v)`
  `flat_pat_to_display p =
        match p with
          p ->
       match p with flatLang_Pvar varN -> displayLang_Item NONE
         (strlit "Pvar") [string_imp varN] | flatLang_Pany -> empty_item
         (strlit "Pany") | flatLang_Plit lit -> displayLang_Item NONE
         (strlit "Plit") [lit_to_display lit] | flatLang_Pcon id pats ->
         displayLang_Item NONE (strlit "Pcon")
               (flat_pat_to_display_list pats) | flatLang_Pas
                 pattern_semantics_pat varN -> displayLang_Item NONE
                 (strlit "Pas") [flat_pat_to_display
                 pattern_semantics_pat;
                              string_imp varN] | flatLang_Pref
                                pattern_semantics_pat ->
                                displayLang_Item NONE (strlit "Pref")
                                [flat_pat_to_display
                                pattern_semantics_pat]
        | [] -> []
        | (x :: xs) ->
       flat_pat_to_display x :: flat_pat_to_display_list xs`;;

let flat_op_to_display_def = cake_define
  `flat_op_to_display flatLang_op = (match flatLang_op with
  flatLang_Src ast_op -> op_to_display ast_op |
  flatLang_GlobalVarAlloc n -> item_with_num (strlit
  "GlobalVarAlloc") n | flatLang_GlobalVarInit n -> item_with_num
  (strlit "GlobalVarInit") n | flatLang_GlobalVarLookup n ->
  item_with_num (strlit "GlobalVarLookup") n |
  pattern_semantics_TagLenEq n1 n2 -> item_with_nums (strlit
  "TagLenEq") [n1; n2] | flatLang_LenEq n1 -> item_with_nums (strlit
  "LenEq") [n1] | flatLang_El n -> item_with_num (strlit "El") n |
  flatLang_Id -> empty_item (strlit "Id"))`;;

let add_name_hint_def = cake_define
  `add_name_hint prefix name_hint =
     mlstring_concat [prefix; (strlit "<"); name_hint; (strlit
       ">")]`;;

let flat_to_display_def = cake_define
  `flat_to_display x1 =
        match x1 with
          (flatLang_Raise tra flatLang_exp) ->
       displayLang_Item (SOME tra) (strlit "raise") [flat_to_display
         flatLang_exp]
        | (flatLang_Handle tra flatLang_exp pes) ->
       displayLang_Item (SOME tra) (strlit "handle") (
           flat_to_display flatLang_exp :: pat_flat_to_display_list
             pes)
        | (pattern_semantics_Lit tra lit) -> displayLang_Item (SOME
          tra) (strlit "lit") []
        | (flatLang_Con tra id_opt exps) ->
       displayLang_Item (SOME tra) (strlit "con") (
           opt_con_to_display id_opt :: flat_to_display_list exps)
        | (flatLang_Var_local tra varN) ->
       displayLang_Item (SOME tra) (strlit "var_local") [string_imp
         varN]
        | (flatLang_Fun name_hint varN flatLang_exp) ->
       displayLang_Item (SOME backend_common_None) (add_name_hint
         (strlit "fun") name_hint)
         [string_imp varN; flat_to_display flatLang_exp]
        | (flatLang_App tra flatLang_op exps) ->
       displayLang_Item (SOME tra) (strlit "app") (flat_op_to_display
         flatLang_op :: flat_to_display_list exps)
        | (pattern_semantics_If tra exp1 exp2 exp3) ->
       displayLang_Item (SOME tra) (strlit "if") [flat_to_display
         exp1; flat_to_display exp2;
           flat_to_display exp3]
        | (flatLang_Mat tra flatLang_exp pes) ->
       displayLang_Item (SOME tra) (strlit "mat") (
           flat_to_display flatLang_exp :: pat_flat_to_display_list
             pes)
        | (flatLang_Let tra varN_opt exp1 exp2) ->
       displayLang_Item (SOME tra) (strlit "let") [(\f' opt. match
         opt with NONE -> empty_item (strlit "none") | SOME opt' ->
         displayLang_Item NONE (strlit "some") [f' opt']) string_imp
         varN_opt;
           flat_to_display exp1; flat_to_display exp2]
        | (flatLang_Letrec name_hint funs flatLang_exp) ->
       displayLang_Item (SOME backend_common_None) (add_name_hint
         (strlit "letrec") name_hint)
           [displayLang_Tuple (fun_flat_to_display_list funs);
             flat_to_display flatLang_exp]
        | [] -> []
        | (x :: xs) ->
       flat_to_display x :: flat_to_display_list xs
        | [] -> []
        | ((pattern_semantics_pat,flatLang_exp) :: xs) ->
       displayLang_Tuple [flat_pat_to_display pattern_semantics_pat;
         flat_to_display flatLang_exp] :: pat_flat_to_display_list xs
        | [] -> []
        | ((v1,v2,e) :: xs) ->
        displayLang_Tuple [string_imp v1; string_imp v2;
          flat_to_display e] ::
           fun_flat_to_display_list xs`;;

(* clos to displayLang *)

(* HOL4 termination: \\ rw [] \\ fs [DIV_LT_X] *)
let num_to_varn_aux_def = cake_define_wf
  `MEASURE I`
  `num_to_varn_aux n =
     (if n < 26 then [CHR (97 + n)] else (num_to_varn_aux ((n DIV
       26) - 1)) ++ ([CHR (97 + (n MOD 26))]))`;;

let num_to_varn_def = cake_define
  `num_to_varn n = implode (num_to_varn_aux n)`;;

let display_num_as_varn_def = cake_define
  `display_num_as_varn n = string_imp (num_to_varn n)`;;

let num_to_varn_list_def = cake_define
  `num_to_varn_list h n =
     (if n = 0 then [] else
       num_to_varn (h + n) :: num_to_varn_list h (n - 1))`;;

let attach_name_def = cake_define
  `attach_name ns NONE = (strlit "none") /\
   attach_name ns (SOME d) =
     (match sptree_lookup d ns with NONE -> (num_to_str) d | SOME
       name -> mlstring_concat [name; (strlit "@"); (num_to_str) d])`;;

let const_part_to_display_def = cake_define
  `const_part_to_display (jsonLang_Int i:const_part) =
     displayLang_Item NONE (strlit "Int") [int_to_display i] /\
   const_part_to_display (flatLang_Con t vs) =
     displayLang_Item NONE (strlit "Con") [num_to_display t;
       displayLang_Tuple (MAP num_to_display vs)] /\
   const_part_to_display (mlsexp_Str s) =
     displayLang_Item NONE (strlit "Str") [displayLang_String
       (mlstring_concat [(implode) "\""; s; (implode) "\""])] /\
   const_part_to_display (closLang_W64 w) =
     displayLang_Item NONE (strlit "W64") [word_to_display w]`;;

(* HOL4 termination: *)
let const_to_display_def = cake_define_wf
  `MEASURE (\x. match x with INL semanticPrimitives_v -> const_size
  semanticPrimitives_v | INR semanticPrimitives_v -> list_size
  const_size semanticPrimitives_v)`
  `const_to_display (ConstInt i:const) =
     displayLang_Item NONE (strlit "ConstInt") [int_to_display i] /\
   const_to_display (ConstCons t vs) =
     displayLang_Item NONE (strlit "ConstCons") [num_to_display t;
       displayLang_Tuple (const_to_display_list vs)] /\
   const_to_display (ConstStr s) =
     displayLang_Item NONE (strlit "ConstStr") [displayLang_String
       (mlstring_concat [(implode) "\""; s; (implode) "\""])] /\
   const_to_display (ConstWord64 w) =
     displayLang_Item NONE (strlit "ConstWord64") [word_to_display w]
       /\
   (const_to_display_list [] = []) /\
   (const_to_display_list (x :: xs) =
     const_to_display x :: const_to_display_list xs)`;;

let clos_op_to_display_def = cake_define
  `clos_op_to_display ns flatLang_op = (match flatLang_op with
  closLang_GlobOp (Global num') -> item_with_num (strlit "Global") num'
  | closLang_GlobOp (SetGlobal num') -> item_with_num (strlit
  "SetGlobal") num' | closLang_GlobOp AllocGlobal -> displayLang_String
  (strlit "AllocGlobal") | closLang_GlobOp GlobalsPtr ->
  displayLang_String (strlit "GlobalsPtr") | closLang_GlobOp
  SetGlobalsPtr -> displayLang_String (strlit "SetGlobalsPtr") |
  closLang_BlockOp (pattern_semantics_Cons num') -> item_with_num
  (strlit "Cons") num' | closLang_BlockOp (closLang_ElemAt num') ->
  item_with_num (strlit "ElemAt") num' | closLang_BlockOp
  (pattern_semantics_TagLenEq n1 n2) -> item_with_nums (strlit
  "TagLenEq") [n1; n2] | closLang_BlockOp (closLang_BoolTest test) ->
  displayLang_Item NONE (strlit "BoolTest") [test_to_display test] |
  closLang_BlockOp closLang_BoolNot -> displayLang_String (strlit
  "BoolNot") | closLang_BlockOp (flatLang_LenEq num') -> item_with_num
  (strlit "LenEq") num' | closLang_BlockOp (closLang_TagEq num') ->
  item_with_num (strlit "TagEq") num' | closLang_BlockOp
  closLang_LengthBlock -> displayLang_String (strlit "LengthBlock") |
  closLang_BlockOp closLang_BoundsCheckBlock -> displayLang_String
  (strlit "BoundsCheckBlock") | closLang_BlockOp (closLang_ConsExtend
  num') -> item_with_num (strlit "ConsExtend") num' | closLang_BlockOp
  (closLang_FromList num') -> item_with_num (strlit "FromList") num' |
  closLang_BlockOp closLang_ListAppend -> displayLang_String (strlit
  "ListAppend") | closLang_BlockOp (closLang_Constant c) ->
  displayLang_Item NONE (strlit "Constant") [const_to_display c] |
  closLang_BlockOp (EQUAL) -> displayLang_String (strlit "Equal") |
  closLang_BlockOp (closLang_EqualConst c) -> displayLang_Item NONE
  (strlit "EqualConst") [const_part_to_display c] | closLang_BlockOp
  (closLang_Build bs) -> displayLang_Item NONE (strlit "Build") (MAP
  const_part_to_display bs) | closLang_MemOp pattern_semantics_Ref ->
  displayLang_String (strlit "Ref") | closLang_MemOp closLang_Update ->
  displayLang_String (strlit "Update") | closLang_MemOp flatLang_El ->
  displayLang_String (strlit "El") | closLang_MemOp closLang_Length ->
  displayLang_String (strlit "Length") | closLang_MemOp
  closLang_LengthByte -> displayLang_String (strlit "LengthByte") |
  closLang_MemOp (closLang_RefByte b) -> displayLang_Item NONE (strlit
  "RefByte") [bool_to_display b] | closLang_MemOp closLang_RefArray ->
  displayLang_String (strlit "RefArray") | closLang_MemOp
  closLang_DerefByte -> displayLang_String (strlit "DerefByte") |
  closLang_MemOp closLang_UpdateByte -> displayLang_String (strlit
  "UpdateByte") | closLang_MemOp closLang_ConcatByteVec ->
  displayLang_String (strlit "ConcatByteVec") | closLang_MemOp
  (closLang_CopyByte b) -> displayLang_Item NONE (strlit "CopyByte")
  [bool_to_display b] | closLang_MemOp closLang_FromListByte ->
  displayLang_String (strlit "FromListByte") | closLang_MemOp
  closLang_ToListByte -> displayLang_String (strlit "ToListByte") |
  closLang_MemOp closLang_LengthByteVec -> displayLang_String (strlit
  "LengthByteVec") | closLang_MemOp closLang_DerefByteVec ->
  displayLang_String (strlit "DerefByteVec") | closLang_MemOp
  closLang_BoundsCheckArray -> displayLang_String (strlit
  "BoundsCheckArray") | closLang_MemOp (closLang_BoundsCheckByte b) ->
  displayLang_Item NONE (strlit "BoundsCheckByte") [bool_to_display b] |
  closLang_MemOp closLang_ConfigGC -> displayLang_String (strlit
  "ConfigGC") | closLang_MemOp (closLang_StringCmp b opb) ->
  displayLang_Item NONE (strlit "StringCmp") [bool_to_display b;
                              opb_to_display opb] | closLang_MemOp
                                closLang_XorByte -> displayLang_String
                                (strlit "XorByte") | closLang_MemOp
                                (closLang_MutCons pattern_semantics_tag
                                i) -> item_with_nums (strlit "MutCons")
                                [pattern_semantics_tag; i] |
                                closLang_MemOp closLang_UpdateCons ->
                                displayLang_String (strlit "UpdateCons")
                                | closLang_MemOp closLang_FinaliseCons
                                -> displayLang_String (strlit
                                "FinaliseCons") | labLang_Label num' ->
                                displayLang_Item NONE (strlit "Label")
                                [displayLang_String (attach_name ns
                                (SOME num'))] | wordLang_FFI s ->
                                displayLang_Item NONE (strlit "FFI")
                                [string_imp s] | closLang_IntOp
                                (wordLang_Const i) -> displayLang_Item
                                NONE (strlit "Const") [int_to_display i]
                                | closLang_IntOp asm_Add ->
                                displayLang_String (strlit "Add") |
                                closLang_IntOp asm_Sub ->
                                displayLang_String (strlit "Sub") |
                                closLang_IntOp closLang_Mult ->
                                displayLang_String (strlit "Mult") |
                                closLang_IntOp asm_Div ->
                                displayLang_String (strlit "Div") |
                                closLang_IntOp closLang_Mod ->
                                displayLang_String (strlit "Mod") |
                                closLang_IntOp (LESS) ->
                                displayLang_String (strlit "Less") |
                                closLang_IntOp closLang_LessEq ->
                                displayLang_String (strlit "LessEq") |
                                closLang_IntOp (GREATER) ->
                                displayLang_String (strlit "Greater") |
                                closLang_IntOp closLang_GreaterEq ->
                                displayLang_String (strlit "GreaterEq")
                                | closLang_IntOp
                                (closLang_LessConstSmall num') ->
                                item_with_num (strlit "LessConstSmall")
                                num' | closLang_WordOp (WordOpw ws
                                flatLang_op) -> displayLang_Item NONE
                                (strlit "WordOp")
                              [word_size_to_display ws;
                              opw_to_display flatLang_op] |
                                closLang_WordOp (WordShift ws sh num')
                                -> displayLang_Item NONE (strlit
                                "WordShift")
                              [word_size_to_display ws;
                              shift_to_display sh;
                              num_to_display num'] | closLang_WordOp
                                (WordTest ws test) -> displayLang_Item
                                NONE (strlit "WordTest")
                              [word_size_to_display ws;
                              test_to_display test] |
                                closLang_WordOp WordFromInt ->
                                displayLang_String (strlit
                                "WordFromInt") | closLang_WordOp
                                WordToInt -> displayLang_String
                                (strlit "WordToInt") |
                                closLang_WordOp (WordFromWord b) ->
                                displayLang_Item NONE (strlit
                                "WordFromWord") [bool_to_display b] |
                                closLang_WordOp (FP_cmp cmp) ->
                                fp_cmp_to_display cmp |
                                closLang_WordOp (FP_uop flatLang_op)
                                -> fp_uop_to_display flatLang_op |
                                closLang_WordOp (FP_bop flatLang_op)
                                -> fp_bop_to_display flatLang_op |
                                closLang_WordOp (FP_top flatLang_op)
                                -> fp_top_to_display flatLang_op |
                                labLang_Install -> displayLang_String
                                (strlit "Install") | closLang_ThunkOp
                                t -> thunk_op_to_display t)`;;

let commas_def = cake_define
  `presLang_commas x1 =
      match x1 with
        [] -> (strlit "")
      | [x] -> x
      | (x :: xs) -> ^ (^ x (strlit ",")) (presLang_commas xs)`;;

(* The clos_to_display ns function uses the same approach to de bruijn
   indices as the pat_to_display function *)
(* HOL4 termination: >> rw[list_size_pair_size_MAP_FST_SND] *)
let clos_to_display_def = cake_define_wf
  `MEASURE (\x. match x with INL (_8,_9,e) -> exp_size e | INR (INL
  (_10,_11,e)) -> list_size exp_size e | INR (INR (INL
  (_12,_13,_14,es))) -> list_size exp_size es | INR (INR (INR
  (_15,_16,_17,_18,es))) -> list_size (pair_size I exp_size) es)`
  `(clos_to_display ns h (wordLang_Var t n) =
     displayLang_Item (SOME t) (strlit "var") [display_num_as_varn (h
       - n - 1)]) /\
   (clos_to_display ns h (pattern_semantics_If t x1 x2 x3) =
     displayLang_Item (SOME t) (strlit "if") [clos_to_display ns h
       x1; clos_to_display ns h x2;
         clos_to_display ns h x3]) /\
   (clos_to_display ns h (closLang_Let t xs x) =
     separate_lines (strlit "let")
         [displayLang_Tuple (clos_to_display_lets ns h (LENGTH xs -
           1) xs);
             clos_to_display ns (h + LENGTH xs) x]) /\
   (clos_to_display ns h (flatLang_Raise t x) =
     displayLang_Item (SOME t) (strlit "raise") [clos_to_display ns h
       x]) /\
   (clos_to_display ns h (wordLang_Tick t x) =
     displayLang_Item (SOME t) (strlit "tick") [clos_to_display ns h
       x]) /\
   (clos_to_display ns h (flatLang_Handle t x y) =
     displayLang_Item (SOME t) (strlit "handle")
         [clos_to_display ns h x; display_num_as_varn h;
             clos_to_display ns (h + 1) y]) /\
   (clos_to_display ns h (labLang_Call t ticks dest xs) =
     displayLang_Item (SOME t) (strlit "call")
       ([num_to_display ticks; displayLang_String (attach_name ns
         (SOME dest))] ++
        (clos_to_display_list ns h xs))) /\
   (clos_to_display ns h (flatLang_App t opt_n x xs) =
     displayLang_Item (SOME t) (strlit "app")
         ([(\f' opt. match opt with NONE -> empty_item (strlit
           "none") | SOME opt' -> displayLang_Item NONE (strlit "some")
           [f' opt']) num_to_display opt_n;
           clos_to_display ns h x] ++ (clos_to_display_list ns h
             xs))) /\
   (clos_to_display ns h (closLang_Fn name_hint n1 n2 vn x) =
     displayLang_Item (SOME backend_common_None) (add_name_hint
       (strlit "fn") name_hint)
         [(\f' opt. match opt with NONE -> empty_item (strlit "none")
           | SOME opt' -> displayLang_Item NONE (strlit "some") [f'
           opt']) num_to_display n1;
          (\f' opt. match opt with NONE -> empty_item (strlit "none")
            | SOME opt' -> displayLang_Item NONE (strlit "some") [f'
            opt']) ((\f' xs. displayLang_Tuple (MAP f' xs))
            num_to_display) n2;
          (\f' xs. displayLang_Tuple (MAP f' xs)) string_imp
            (num_to_varn_list h vn);
          clos_to_display ns h x]) /\
   (clos_to_display ns h (closLang_Letrec name_hint n1 n2 es e) =
     displayLang_Item (SOME backend_common_None) (add_name_hint
       (strlit "letrec") (presLang_commas name_hint))
         [(\f' opt. match opt with NONE -> empty_item (strlit "none")
           | SOME opt' -> displayLang_Item NONE (strlit "some") [f'
           opt']) num_to_display n1;
          (\f' opt. match opt with NONE -> empty_item (strlit "none")
            | SOME opt' -> displayLang_Item NONE (strlit "some") [f'
            opt']) ((\f' xs. displayLang_Tuple (MAP f' xs))
            num_to_display) n2;
          displayLang_Tuple (clos_to_display_letrecs ns h (LENGTH es
            - 1) (LENGTH es) es);
          clos_to_display ns h e]) /\
   (clos_to_display ns h (wordLang_Op t flatLang_op xs) =
     displayLang_Item (SOME t) (strlit "op") (clos_op_to_display LN
       flatLang_op ::
         (clos_to_display_list ns h xs))) /\
   (clos_to_display_list ns h [] = []) /\
   (clos_to_display_list ns h (x :: xs) =
     clos_to_display ns h x :: clos_to_display_list ns h xs) /\
   (clos_to_display_lets ns h i [] = []) /\
   (clos_to_display_lets ns h i (x :: xs) =
     displayLang_Tuple [display_num_as_varn (h + i);
       displayLang_String (strlit "<-"); clos_to_display ns h x] ::
       clos_to_display_lets ns h (i - 1) xs) /\
   (clos_to_display_letrecs ns h i len [] = []) /\
   (clos_to_display_letrecs ns h i len ((vn,e) :: es) =
     displayLang_Tuple [display_num_as_varn (h + i);
         (\f' xs. displayLang_Tuple (MAP f' xs)) string_imp
           (num_to_varn_list ((h + len) - 1) vn);
         clos_to_display ns (h + len + vn) e] ::
           clos_to_display_letrecs ns h (i - 1) len es)`;;

let clos_fun_to_display_def = cake_define
  `clos_fun_to_display names (n,argc,body) =
     displayLang_Tuple [displayLang_String (strlit "func");
            displayLang_String (attach_name names (SOME n));
            displayLang_Tuple (REVERSE (GENLIST display_num_as_varn
              argc));
            clos_to_display names argc body]`;;

let clos_dec_to_display_def = cake_define
  `clos_dec_to_display names dec =
     displayLang_Tuple [displayLang_String (strlit "dec");
            clos_to_display names 0 dec]`;;

(* bvl to displayLang *)

(* HOL4 termination: *)
let bvl_to_display_def = cake_define_wf
  `MEASURE (\x.
     match x with
       INL (ns,h,x) -> exp_size x | INR (INL (ns,h,xs)) -> list_size
         exp_size xs | INR (INR (ns,h,i,xs)) -> list_size exp_size xs)`
  `(bvl_to_display ns h (wordLang_Var n) =
     displayLang_Item NONE (strlit "var") [display_num_as_varn (h - n
       - 1)]) /\
   (bvl_to_display ns h (pattern_semantics_If x1 x2 x3) =
     displayLang_Item NONE (strlit "if") [bvl_to_display ns h x1;
       bvl_to_display ns h x2;
         bvl_to_display ns h x3]) /\
   (bvl_to_display ns h (bvl_Let xs x) =
     separate_lines (strlit "let")
         (bvl_to_display_lets ns h (LENGTH xs - 1) xs ++
             [bvl_to_display ns (h + LENGTH xs) x])) /\
   (bvl_to_display ns h (flatLang_Raise x) =
     displayLang_Item NONE (strlit "raise") [bvl_to_display ns h x])
       /\
   (bvl_to_display ns h (wordLang_Tick x) =
     displayLang_Item NONE (strlit "tick") [bvl_to_display ns h x])
       /\
   (bvl_to_display ns h (flatLang_Handle x y) =
     displayLang_Item NONE (strlit "handle")
         [bvl_to_display ns h x; display_num_as_varn h;
             bvl_to_display ns (h + 1) y]) /\
   (bvl_to_display ns h (labLang_Call ticks dest xs) =
     displayLang_Item NONE (strlit "call")
          (displayLang_String (attach_name ns dest) ::
           (bvl_to_display_list ns h xs))) /\
   (bvl_to_display ns h (bvl_Force loc n) =
     displayLang_Item NONE (strlit "force")
          [display_num_as_varn (h - n - 1); displayLang_String
            (attach_name ns (SOME loc))]) /\
   (bvl_to_display ns h (wordLang_Op flatLang_op xs) =
     displayLang_Item NONE (strlit "op") (clos_op_to_display ns
       flatLang_op ::
                              (bvl_to_display_list ns h xs))) /\
   (bvl_to_display_list ns h [] = []) /\
   (bvl_to_display_list ns h (x :: xs) =
     bvl_to_display ns h x :: bvl_to_display_list ns h xs) /\
   (bvl_to_display_lets ns h i [] = []) /\
   (bvl_to_display_lets ns h i (x :: xs) =
     displayLang_Tuple [display_num_as_varn (h + i);
       displayLang_String (strlit "<-"); bvl_to_display ns h x] ::
       bvl_to_display_lets ns h (i - 1) xs)`;;

let bvl_fun_to_display_def = cake_define
  `bvl_fun_to_display names (n,argc,body) =
     displayLang_Tuple [displayLang_String (strlit "func");
            displayLang_String (attach_name names (SOME n));
            displayLang_Tuple (REVERSE (GENLIST display_num_as_varn
              argc));
            bvl_to_display names argc body]`;;

(* bvi to displayLang *)

(* HOL4 termination: *)
let bvi_to_display_def = cake_define_wf
  `MEASURE (\x.
     match x with
       INL (ns,h,x) -> exp_size x | INR (INL (ns,h,xs)) -> list_size
         exp_size xs | INR (INR (ns,h,i,xs)) -> list_size exp_size xs)`
  `(bvi_to_display ns h (wordLang_Var n) =
     displayLang_Item NONE (strlit "var") [display_num_as_varn (h - n
       - 1)]) /\
   (bvi_to_display ns h (pattern_semantics_If x1 x2 x3) =
     displayLang_Item NONE (strlit "if") [bvi_to_display ns h x1;
       bvi_to_display ns h x2;
         bvi_to_display ns h x3]) /\
   (bvi_to_display ns h (bvi_Let xs x) =
     separate_lines (strlit "let")
         (bvi_to_display_lets ns h (LENGTH xs - 1) xs ++
             [bvi_to_display ns (h + LENGTH xs) x])) /\
   (bvi_to_display ns h (flatLang_Raise x) =
     displayLang_Item NONE (strlit "raise") [bvi_to_display ns h x])
       /\
   (bvi_to_display ns h (wordLang_Tick x) =
     displayLang_Item NONE (strlit "tick") [bvi_to_display ns h x])
       /\
   (bvi_to_display ns h (labLang_Call ticks dest xs handler) =
     displayLang_Item NONE (strlit "call")
          ((displayLang_String (attach_name ns dest) ::
           (bvi_to_display_list ns h xs)) ++
           (match handler with NONE -> [] | SOME e ->
             [displayLang_Item NONE (strlit "handler")
             [display_num_as_varn h;
                              empty_item (strlit "->");
                              bvi_to_display ns (h + 1) e]]))) /\
   (bvi_to_display ns h (bvl_Force loc n) =
     displayLang_Item NONE (strlit "force")
          [display_num_as_varn (h - n - 1); displayLang_String
            (attach_name ns (SOME loc))]) /\
   (bvi_to_display ns h (wordLang_Op flatLang_op xs) =
     displayLang_Item NONE (strlit "op") (clos_op_to_display ns
       flatLang_op ::
                              (bvi_to_display_list ns h xs))) /\
   (bvi_to_display ns h (wordLang_Return xs) =
     displayLang_Item NONE (strlit "return") (bvi_to_display_list ns
       h xs)) /\
   (bvi_to_display ns h (bvi_LetCall rets ticks dest xs y) =
     separate_lines (strlit "letcall")
         [displayLang_Item NONE (strlit "call")
            (displayLang_String (attach_name ns (SOME dest)) ::
              bvi_to_display_list ns h xs);
          displayLang_Tuple (REVERSE (GENLIST (\i.
            display_num_as_varn (h + i)) rets));
          bvi_to_display ns (h + rets) y]) /\
   (bvi_to_display_list ns h [] = []) /\
   (bvi_to_display_list ns h (x :: xs) =
     bvi_to_display ns h x :: bvi_to_display_list ns h xs) /\
   (bvi_to_display_lets ns h i [] = []) /\
   (bvi_to_display_lets ns h i (x :: xs) =
     displayLang_Tuple [display_num_as_varn (h + i);
       displayLang_String (strlit "<-"); bvi_to_display ns h x] ::
       bvi_to_display_lets ns h (i - 1) xs)`;;

let bvi_fun_to_display_def = cake_define
  `bvi_fun_to_display names (n,argc,body) =
     displayLang_Tuple [displayLang_String (strlit "func");
            displayLang_String (attach_name names (SOME n));
            displayLang_Tuple (REVERSE (GENLIST display_num_as_varn
              argc));
            bvi_to_display names argc body]`;;

(* dataLang *)

let num_set_to_display_def = cake_define
  `num_set_to_display ns =
     displayLang_String (mlstring_concat [(strlit "{");
                      presLang_commas (MAP (num_to_str) (MAP FST
                        (toSortedAList ns)));
                      (strlit "}")])`;;

let data_seqs_def = cake_define
  `data_seqs z =
     (match z with dataLang_Seq x y -> mlsexp_Append (data_seqs x)
       (data_seqs y) | _19 -> displayLang_List [z])`;;

(* HOL4 termination: *)
let data_prog_to_display_def = cake_define_wf
  `MEASURE (\x.
     match x with
       INL (k,_20,_21) -> k | INR (k,_22,_23) -> k)`
  `data_prog_to_display k ns prog =
        match (k,prog) with
          (0,labLang_prog) -> empty_item (strlit "...")
        | ((SUC k),labLang_prog) ->
         match labLang_prog with dataLang_Skip -> empty_item (strlit
           "skip") | dataLang_Move x y -> displayLang_Tuple
           [num_to_display x; displayLang_String (strlit ":=");
             num_to_display y] | labLang_Call rets target args NONE ->
             displayLang_Item NONE (strlit "call")
           [(\f' opt. match opt with NONE -> empty_item (strlit
             "none") | SOME opt' -> displayLang_Item NONE (strlit
             "some") [f' opt']) (\(x,y). displayLang_Tuple
                   [(\f' xs. displayLang_Tuple (MAP f' xs))
                     num_to_display x;
                    num_set_to_display y]) rets;
               displayLang_String (attach_name ns target);
               (\f' xs. displayLang_Tuple (MAP f' xs)) num_to_display
                 args;
               empty_item (strlit "none")] | labLang_Call rets target
                 args (SOME (semanticPrimitives_v,handler)) ->
                 displayLang_Item NONE (strlit "call")
           [(\f' opt. match opt with NONE -> empty_item (strlit
             "none") | SOME opt' -> displayLang_Item NONE (strlit
             "some") [f' opt']) (\(x,y). displayLang_Tuple
                   [(\f' xs. displayLang_Tuple (MAP f' xs))
                     num_to_display x;
                    num_set_to_display y]) rets;
               displayLang_String (attach_name ns target);
               (\f' xs. displayLang_Tuple (MAP f' xs)) num_to_display
                 args;
               displayLang_Item NONE (strlit "some")
                 [displayLang_Tuple [num_to_display
                 semanticPrimitives_v;
                   data_prog_to_display k ns handler]]] | bvl_Force
                     ret loc src -> displayLang_Item NONE (strlit
                     "force")
           [(\f' opt. match opt with NONE -> empty_item (strlit
             "none") | SOME opt' -> displayLang_Item NONE (strlit
             "some") [f' opt']) (\(x,y). displayLang_Tuple
                   [num_to_display x; num_set_to_display y]) ret;
            num_to_display loc;
            num_to_display src] | wordLang_Assign n flatLang_op args
              n_set -> displayLang_Tuple
           [num_to_display n;
            displayLang_String (strlit ":=");
            clos_op_to_display ns flatLang_op;
               (\f' xs. displayLang_Tuple (MAP f' xs)) num_to_display
                 args;
               (\f' opt. match opt with NONE -> empty_item (strlit
                 "none") | SOME opt' -> displayLang_Item NONE (strlit
                 "some") [f' opt']) num_set_to_display n_set] |
                 wordLang_Seq x y ->
           (let xs = append (mlsexp_Append (data_seqs x) (data_seqs
             y)) in
              separate_lines (strlit "seq")
                (data_prog_to_display_list k ns xs)) |
                pattern_semantics_If n x y -> displayLang_Item NONE
                (strlit "if")
           [num_to_display n; data_prog_to_display k ns x;
             data_prog_to_display k ns y] | dataLang_MakeSpace n ns ->
             displayLang_Item NONE (strlit "make_space")
           [num_to_display n; num_set_to_display ns] | flatLang_Raise
             n -> displayLang_Item NONE (strlit "raise") [num_to_display
             n] | wordLang_Return ns -> displayLang_Item NONE (strlit
             "return") [(\f' xs. displayLang_Tuple (MAP f' xs))
             num_to_display ns] | wordLang_Tick -> empty_item (strlit
             "tick")
        | (k,[]) -> []
        | (k,(x :: xs)) ->
       match k with
         0 -> [] | SUC k ->
       data_prog_to_display k ns x :: data_prog_to_display_list k
         ns xs`;;

let data_fun_to_display_def = cake_define
  `data_fun_to_display names (n,argc,body) =
     displayLang_Tuple [displayLang_String (strlit "func");
            displayLang_String (attach_name names (SOME n));
            displayLang_Tuple (GENLIST num_to_display argc);
            data_prog_to_display 1000000000 names body]`;;

(* asm *)

let asm_binop_to_display_def = cake_define
  `asm_binop_to_display flatLang_op = (match flatLang_op with asm_Add
  -> empty_item (strlit "Add") | asm_Sub -> empty_item (strlit "Sub")
  | asm_And -> empty_item (strlit "And") | pattern_semantics_Or ->
  empty_item (strlit "Or") | asm_Xor -> empty_item (strlit "Xor"))`;;

let asm_reg_imm_to_display_def = cake_define
  `asm_reg_imm_to_display reg_imm' = (match reg_imm' with Reg
  labLang_reg -> item_with_num (strlit "Reg") labLang_reg | Imm imm
  -> item_with_word (strlit "Imm") imm)`;;

let asm_arith_to_display_def = cake_define
  `asm_arith_to_display flatLang_op = (match flatLang_op with asm_Binop
  bop n1 n2 reg_imm' -> displayLang_Item NONE (strlit "Binop")
         [asm_binop_to_display bop; num_to_display n1; num_to_display
           n2;
             asm_reg_imm_to_display reg_imm'] | asm_Shift sh n1 n2 n3
               -> displayLang_Item NONE (strlit "Shift")
         [shift_to_display sh;
          num_to_display n1;
          num_to_display n2;
          asm_reg_imm_to_display n3] | asm_Div n1 n2 n3 ->
            item_with_nums (strlit "Div") [n1; n2; n3] | asm_LongMul
            n1 n2 n3 n4 -> item_with_nums (strlit "LongMul") [n1; n2;
            n3; n4] | asm_LongDiv n1 n2 n3 n4 n5 -> item_with_nums
            (strlit "LongDiv") [n1; n2; n3; n4; n5] | asm_AddCarry n1
            n2 n3 n4 -> item_with_nums (strlit "AddCarry") [n1; n2;
            n3; n4] | asm_AddOverflow n1 n2 n3 n4 -> item_with_nums
            (strlit "AddOverflow") [n1; n2; n3; n4] | asm_SubOverflow
            n1 n2 n3 n4 -> item_with_nums (strlit "SubOverflow") [n1;
            n2; n3; n4])`;;

let asm_addr_to_display_def = cake_define
  `asm_addr_to_display addr' = (match addr' with Addr labLang_reg w ->
  displayLang_Item NONE (strlit "Addr")
                          [num_to_display labLang_reg;
                            word_to_display w])`;;

let asm_memop_to_display_def = cake_define
  `asm_memop_to_display flatLang_op = (match flatLang_op with
  wordLang_Load -> empty_item (strlit "Load") | asm_Load8 ->
  empty_item (strlit "Load8") | asm_Load16 -> empty_item (strlit
  "Load16") | asm_Load32 -> empty_item (strlit "Load32") |
  wordLang_Store -> empty_item (strlit "Store") | asm_Store8 ->
  empty_item (strlit "Store8") | asm_Store16 -> empty_item (strlit
  "Store16") | asm_Store32 -> empty_item (strlit "Store32"))`;;

let asm_cmp_to_display_def = cake_define
  `asm_cmp_to_display flatLang_op = (match flatLang_op with (EQUAL)
  -> empty_item (strlit "Equal") | asm_Lower -> empty_item (strlit
  "Lower") | (LESS) -> empty_item (strlit "Less") | asm_Test ->
  empty_item (strlit "Test") | asm_NotEqual -> empty_item (strlit
  "NotEqual") | asm_NotLower -> empty_item (strlit "NotLower") |
  asm_NotLess -> empty_item (strlit "NotLess") | asm_NotTest ->
  empty_item (strlit "NotTest"))`;;

let asm_fp_to_display_def = cake_define
  `asm_fp_to_display flatLang_op = (match flatLang_op with FPLess n1
  n2 n3 -> item_with_nums (strlit "FPLess") [n1; n2; n3] |
  FPLessEqual n1 n2 n3 -> item_with_nums (strlit "FPLessEqual") [n1;
  n2; n3] | FPEqual n1 n2 n3 -> item_with_nums (strlit "FPEqual")
  [n1; n2; n3] | FPAbs n1 n2 -> item_with_nums (strlit "FPAbs") [n1;
  n2] | FPNeg n1 n2 -> item_with_nums (strlit "FPNeg") [n1; n2] |
  FPSqrt n1 n2 -> item_with_nums (strlit "FPSqrt") [n1; n2] | FPAdd
  n1 n2 n3 -> item_with_nums (strlit "FPAdd") [n1; n2; n3] | FPSub n1
  n2 n3 -> item_with_nums (strlit "FPSub") [n1; n2; n3] | FPMul n1 n2
  n3 -> item_with_nums (strlit "FPMul") [n1; n2; n3] | FPDiv n1 n2 n3
  -> item_with_nums (strlit "FPDiv") [n1; n2; n3] | FPFma n1 n2 n3 ->
  item_with_nums (strlit "FPFma") [n1; n2; n3] | FPMov n1 n2 ->
  item_with_nums (strlit "FPMov") [n1; n2] | FPMovToReg n1 n2 n3 ->
  item_with_nums (strlit "FPMovToReg") [n1; n2; n3] | FPMovFromReg n1
  n2 n3 -> item_with_nums (strlit "FPMovFromReg") [n1; n2; n3] |
  FPToInt n1 n2 -> item_with_nums (strlit "FPToInt") [n1; n2] |
  FPFromInt n1 n2 -> item_with_nums (strlit "FPFromInt") [n1; n2])`;;

let asm_inst_to_display_def = cake_define
  `asm_inst_to_display inst' = (match inst' with asm_Skip -> empty_item
  (strlit "Skip") | wordLang_Const labLang_reg w -> displayLang_Item
  NONE (strlit "Const") [num_to_display labLang_reg;
                              word_to_display w] | asm_Arith a ->
                                displayLang_Item NONE (strlit "Arith")
                                [asm_arith_to_display a] | asm_Mem mop r
                                addr' -> displayLang_Item NONE (strlit
                                "Mem") [asm_memop_to_display mop;
         num_to_display r; asm_addr_to_display addr'] | asm_FP fp
           -> displayLang_Item NONE (strlit "FP") [asm_fp_to_display
           fp])`;;

let asm_asm_to_display_def = cake_define
  `asm_asm_to_display inst' = (match inst' with wordLang_Inst i ->
  asm_inst_to_display i | bvl_jump_Jump w -> item_with_word (strlit
  "Jump") w | labLang_JumpCmp c r to w -> displayLang_Item NONE (strlit
  "JumpCmp")
       [asm_cmp_to_display c; num_to_display r;
         asm_reg_imm_to_display to;
        word_to_display w] | labLang_Call w -> item_with_word
          (strlit "Call") w | asm_JumpReg r -> item_with_num (strlit
          "JumpReg>") r | semanticPrimitives_Loc r w ->
          displayLang_Item NONE (strlit "Loc") [num_to_display r;
          word_to_display w])`;;

(* stackLang *)

let store_name_to_display_def = cake_define
  `store_name_to_display st = (match st with NextFree -> empty_item
  (strlit "NextFree") | EndOfHeap -> empty_item (strlit "EndOfHeap")
  | TriggerGC -> empty_item (strlit "TriggerGC") | HeapLength ->
  empty_item (strlit "HeapLength") | ProgStart -> empty_item (strlit
  "ProgStart") | BitmapBase -> empty_item (strlit "BitmapBase") |
  CurrHeap -> empty_item (strlit "CurrHeap") | OtherHeap ->
  empty_item (strlit "OtherHeap") | AllocSize -> empty_item (strlit
  "AllocSize") | Globals -> empty_item (strlit "Globals") | GlobReal
  -> empty_item (strlit "GlobReal") | Handler -> empty_item (strlit
  "Handler") | GenStart -> empty_item (strlit "GenStart") |
  CodeBuffer -> empty_item (strlit "CodeBuffer") | CodeBufferEnd ->
  empty_item (strlit "CodeBufferEnd") | BitmapBuffer -> empty_item
  (strlit "BitmapBuffer") | BitmapBufferEnd -> empty_item (strlit
  "BitmapBufferEnd") | Temp w -> item_with_word (strlit "Temp") w)`;;

let stack_seqs_def = cake_define
  `stack_seqs z =
     (match z with stackLang_Seq x y -> mlsexp_Append (stack_seqs
       x) (stack_seqs y) | _24 -> displayLang_List [z])`;;

(* HOL4 termination: *)
let stack_prog_to_display_def = cake_define_wf
  `MEASURE (\x.
     match x with
       INL (k,_26,_27) -> k | INR (k,_28,_29) -> k)`
  `stack_prog_to_display k ns prog =
      match (k,prog) with
        (0,labLang_prog) -> empty_item (strlit "...")
      | ((SUC k),stackLang_Skip) -> empty_item (strlit "skip")
      | ((SUC k),(wordLang_Inst i)) -> asm_inst_to_display i
      | ((SUC k),(wordLang_Get n sn)) -> displayLang_Tuple
     [num_to_display n; displayLang_String (strlit "<-");
       store_name_to_display sn]
      | ((SUC k),(wordLang_Set sn n)) -> displayLang_Tuple
     [store_name_to_display sn; displayLang_String (strlit "<-");
       num_to_display n]
      | ((SUC k),(wordLang_OpCurrHeap b n1 n2)) -> displayLang_Tuple
     [num_to_display n1; displayLang_String (strlit ":=");
       displayLang_String (strlit "CurrHeap");
      asm_binop_to_display b; num_to_display n2]
      | ((SUC k),(labLang_Call rh tgt eh)) ->
     displayLang_Item NONE (strlit "call")
          [(match rh with NONE -> empty_item (strlit "tail") | SOME
            (p,lr,l1,l2) ->
                displayLang_Item NONE (strlit "returning")
                     [num_to_display lr;
                      displayLang_String (attach_name ns (SOME l1));
                      num_to_display l2;
                      stack_prog_to_display k ns p]);
          (match tgt with INL l -> displayLang_Item NONE (strlit
            "direct") [displayLang_String (attach_name ns (SOME l))] |
            INR r -> item_with_num (strlit "reg") r);
          (match eh with NONE -> empty_item (strlit "no_handler") |
            SOME (p,l1,l2) ->
               displayLang_Item NONE (strlit "handler")
                    [displayLang_String (attach_name ns (SOME l1));
                     num_to_display l2;
                     stack_prog_to_display k ns p])]
      | ((SUC k),(wordLang_Seq x y)) ->
         (let xs = append (mlsexp_Append (stack_seqs x) (stack_seqs
           y)) in
            separate_lines (strlit "seq") (stack_prog_to_display_list
              k ns xs))
      | ((SUC k),(pattern_semantics_If c n to x y)) ->
        displayLang_Item NONE (strlit "if")
         [displayLang_Tuple [asm_cmp_to_display c; num_to_display n;
           asm_reg_imm_to_display to];
          stack_prog_to_display k ns x;
          stack_prog_to_display k ns y]
      | ((SUC k),(wordLang_Loop x)) -> displayLang_Item NONE (strlit
        "loop")
         [stack_prog_to_display k ns x]
      | ((SUC k),(stackLang_JumpLower n1 n2 n3)) ->
      item_with_nums (strlit "jump_lower") [n1; n2; n3]
      | ((SUC k),(wordLang_Alloc n)) -> item_with_num (strlit
        "alloc") n
      | ((SUC k),(wordLang_StoreConsts n1 n2 _25)) -> item_with_nums
        (strlit "store_consts") [n1; n2]
      | ((SUC k),(flatLang_Raise n)) -> item_with_num (strlit
        "raise") n
      | ((SUC k),(wordLang_Return n)) -> item_with_num (strlit
        "return") n
      | ((SUC k),(wordLang_Break n)) -> item_with_num (strlit
        "break") n
      | ((SUC k),(wordLang_Continue n)) -> item_with_num (strlit
        "continue") n
      | ((SUC k),(wordLang_FFI nm cp cl ap al ra)) ->
        displayLang_Item NONE (strlit "ffi")
         (string_imp nm :: MAP num_to_display [cp; cl; ap; al; ra])
      | ((SUC k),(wordLang_Tick)) -> empty_item (strlit "tick")
      | ((SUC k),(labLang_LocValue n1 n2 n3)) ->
      displayLang_Item NONE (strlit "loc_value") [num_to_display n1;
                             displayLang_String (attach_name ns (SOME
                               n2));
                             num_to_display n3]
      | ((SUC k),(labLang_Install n1 n2 n3 n4 n5)) ->
      item_with_nums (strlit "install") [n1; n2; n3; n4; n5]
      | ((SUC k),(stackLang_ShMemOp mop r a)) ->
      displayLang_Item NONE (strlit "sh_mem") [asm_memop_to_display
        mop;
                              num_to_display r; asm_addr_to_display
                                a]
      | ((SUC k),(wordLang_CodeBufferWrite n1 n2)) ->
      item_with_nums (strlit "code_buffer_write") [n1; n2]
      | ((SUC k),(wordLang_DataBufferWrite n1 n2)) ->
      item_with_nums (strlit "data_buffer_write") [n1; n2]
      | ((SUC k),(stackLang_RawCall n)) ->
      displayLang_Item NONE (strlit "raw_call") [displayLang_String
        (attach_name ns (SOME n))]
      | ((SUC k),(stackLang_StackAlloc n)) -> item_with_num (strlit
        "stack_alloc") n
      | ((SUC k),(stackLang_StackFree n)) -> item_with_num (strlit
        "stack_free") n
      | ((SUC k),(stackLang_StackStore n m)) ->
      displayLang_Tuple [displayLang_String (^ (^ (^ (strlit
        "stack[") (num_to_hex_mlstring n)) (strlit "] := "))
        ((num_to_str) m))]
      | ((SUC k),(stackLang_StackStoreAny n m)) ->
      displayLang_Tuple [displayLang_String (^ (^ (^ (strlit
        "stack[var ") ((num_to_str) n)) (strlit "] := ")) ((num_to_str)
        m))]
      | ((SUC k),(stackLang_StackLoad n m)) ->
      displayLang_Tuple [displayLang_String (mlstring_concat
        [(num_to_str) n;
                             (strlit " := stack[");
                             num_to_hex_mlstring m; (strlit "]")])]
      | ((SUC k),(stackLang_StackLoadAny n m)) ->
      displayLang_Tuple [displayLang_String (mlstring_concat
        [(num_to_str) n;
                             (strlit " := stack[var ");
                             (num_to_str) m; (strlit "]")])]
      | ((SUC k),(stackLang_StackGetSize n)) -> item_with_num (strlit
        "stack_get_size") n
      | ((SUC k),(stackLang_StackSetSize n)) -> item_with_num (strlit
        "stack_set_size") n
      | ((SUC k),(stackLang_BitmapLoad n m)) ->
      displayLang_Tuple [displayLang_String (mlstring_concat
        [(num_to_str) n;
                             (strlit " := bitmap[");
                             num_to_hex_mlstring m;
                             (strlit "]")])]
      | ((SUC k),(labLang_Halt n)) -> item_with_num (strlit "halt") n
      | (k,[]) -> []
      | (k,(x :: xs)) ->
     match k with 0 -> [] | SUC k ->
     stack_prog_to_display k ns x :: stack_prog_to_display_list k
       ns xs`;;

let stack_fun_to_display_def = cake_define
  `stack_fun_to_display names (n,body) =
     displayLang_Tuple [displayLang_String (strlit "func");
            displayLang_String (attach_name names (SOME n));
            stack_prog_to_display 1000000000 names body]`;;

(* labLang *)

let lab_asm_to_display_def = cake_define
  `lab_asm_to_display ns la = (match la with labLang_Jump (labLang_Lab s
  n) ->
         displayLang_Item NONE (strlit "jump")
           [displayLang_String (attach_name ns (SOME s));
             num_to_display n] | labLang_JumpCmp c r ri (labLang_Lab s
             n) ->
         displayLang_Item NONE (strlit "jump_cmp")
           [displayLang_Tuple [asm_cmp_to_display c; num_to_display
             r;
                   asm_reg_imm_to_display ri];
            displayLang_String (attach_name ns (SOME s));
              num_to_display n] | labLang_Call (labLang_Lab s n) ->
         displayLang_Item NONE (strlit "call")
           [displayLang_String (attach_name ns (SOME s));
             num_to_display n] | labLang_LocValue r (labLang_Lab s n) ->
         displayLang_Item NONE (strlit "loc_value")
           [num_to_display r; displayLang_String (attach_name ns
             (SOME s)); num_to_display n] | labLang_CallFFI name ->
             displayLang_Item NONE (strlit "call_FFI") [string_imp
             name] | labLang_Install -> empty_item (strlit "install")
             | labLang_Halt -> empty_item (strlit "halt"))`;;

let lab_line_to_display_def = cake_define
  `lab_line_to_display ns line = (match line with labLang_Label s n le
  ->
         displayLang_Item NONE (strlit "label") [displayLang_String
           (attach_name ns (SOME s)); num_to_display n] | labLang_Asm
           aoc enc len -> (match aoc with Asmi i -> displayLang_Item
           NONE (strlit "asm") [asm_asm_to_display i] | Cbw r1 r2 ->
           item_with_nums (strlit "cbw") [r1; r2] | ShareMem mop r a ->
           displayLang_Item NONE (strlit "share_mem")
           [asm_memop_to_display mop;
                              num_to_display r;
                              asm_addr_to_display a]) |
                                labLang_LabAsm la pos enc len ->
                                lab_asm_to_display ns la)`;;

let lab_fun_to_display_def = cake_define
  `lab_fun_to_display names (Section n lines) =
     displayLang_List (
            displayLang_String (attach_name names (SOME n)) :: MAP
              (lab_line_to_display names) lines)`;;

(* wordLang *)

let word_seqs_def = cake_define
  `word_seqs z =
     (match z with wordLang_Seq x y -> mlsexp_Append (word_seqs x)
       (word_seqs y) | _30 -> displayLang_List [z])`;;

(* HOL4 termination: *)
let word_exp_to_display_def = cake_define_wf
  `MEASURE (\x. match x with INL semanticPrimitives_v -> exp_size ARB
  semanticPrimitives_v | INR semanticPrimitives_v -> list_size exp_size
  ARB semanticPrimitives_v)`
  `(
     word_exp_to_display (wordLang_Const semanticPrimitives_v) =
       item_with_word (strlit "Const") semanticPrimitives_v) /\
   (
     word_exp_to_display (wordLang_Var n) = item_with_num (strlit
       "Var") n) /\
   (
     word_exp_to_display (wordLang_Lookup st) = displayLang_Item NONE
       (strlit "Lookup") [store_name_to_display st]) /\
   (
     word_exp_to_display (wordLang_Load exp2) = displayLang_Item NONE
       (strlit "MemLoad") [word_exp_to_display exp2]) /\
   (
     word_exp_to_display (wordLang_Op bop exs) = displayLang_Item
       NONE (strlit "Op") (
         asm_binop_to_display bop :: word_exp_to_display_list exs))
           /\
   (
     word_exp_to_display (wordLang_Shift sh flatLang_exp exp1) =
       displayLang_Item NONE (strlit "Shift") [
       shift_to_display sh;
       word_exp_to_display flatLang_exp;
       word_exp_to_display exp1]) /\
   (word_exp_to_display_list [] = []) /\
   (word_exp_to_display_list (x :: xs) =
     word_exp_to_display x :: word_exp_to_display_list xs)`;;

let ws_to_display_def = cake_define
  `ws_to_display [] = [] /\
   ws_to_display ((b,x) :: xs) =
     displayLang_Tuple [bool_to_display b; word_to_display x] ::
       ws_to_display xs`;;

let num_sets_to_display_def = cake_define
  `num_sets_to_display (l,r) =
     displayLang_Tuple [num_set_to_display l;
            num_set_to_display r]`;;

(* HOL4 termination: *)
let word_prog_to_display_def = cake_define_wf
  `MEASURE (\x. match x with INL (k,_31) -> k | INR (INL (k,_32)) -> k
  | INR (INR (INL (k,_33))) -> k | INR (INR (INR (k,_34))) -> k)`
  `word_prog_to_display k ns x =
        match (k,x) with
          (0,x) -> empty_item (strlit "...")
        | ((SUC k),wordLang_Skip) -> empty_item (strlit "skip")
        | ((SUC k),(wordLang_Move n mvs)) -> displayLang_Item NONE
          (strlit "move")
       [num_to_display n; displayLang_Tuple (MAP (\(n1,n2).
         displayLang_Tuple
           [num_to_display n1;
            displayLang_String (strlit ":=");
            num_to_display n2]) mvs)]
        | ((SUC k),(wordLang_Inst i)) ->
       displayLang_Item NONE (strlit "inst") [asm_inst_to_display i]
        | ((SUC k),(wordLang_Assign n flatLang_exp)) ->
        displayLang_Tuple [num_to_display n;
               displayLang_String (strlit ":=");
               word_exp_to_display flatLang_exp]
        | ((SUC k),(wordLang_Get n sn)) -> displayLang_Tuple
       [num_to_display n; displayLang_String (strlit "<-");
         store_name_to_display sn]
        | ((SUC k),(wordLang_Set sn flatLang_exp)) ->
          displayLang_Tuple
       [store_name_to_display sn; displayLang_String (strlit "<-");
         word_exp_to_display flatLang_exp]
        | ((SUC k),(wordLang_Store flatLang_exp n)) ->
          displayLang_Tuple
       [displayLang_String (strlit "mem"); word_exp_to_display
         flatLang_exp;
        displayLang_String (strlit ":="); num_to_display n]
        | ((SUC k),(wordLang_ShareInst mop n flatLang_exp)) ->
          displayLang_Tuple
       [displayLang_String (strlit "share_mem"); asm_memop_to_display
         mop;
        num_to_display n; word_exp_to_display flatLang_exp]
        | ((SUC k),(wordLang_MustTerminate labLang_prog)) ->
          displayLang_Item NONE (strlit "must_terminate")
       [word_prog_to_display k ns labLang_prog]
        | ((SUC k),(labLang_Call a b c d)) -> displayLang_Item NONE
          (strlit "call")
       [word_prog_to_display_ret k ns a;
        (\f' opt. match opt with NONE -> empty_item (strlit "none") |
          SOME opt' -> displayLang_Item NONE (strlit "some") [f' opt'])
          (\n. displayLang_String (attach_name ns (SOME n))) b;
        (\f' xs. displayLang_Tuple (MAP f' xs)) num_to_display c;
        word_prog_to_display_handler k ns d]
        | ((SUC k),(wordLang_OpCurrHeap b n1 n2)) ->
          displayLang_Tuple
       [num_to_display n1; displayLang_String (strlit ":=");
         displayLang_String (strlit "CurrHeap");
        asm_binop_to_display b; num_to_display n2]
        | ((SUC k),(wordLang_Seq prog1 prog2)) ->
       (let xs = append (mlsexp_Append (word_seqs prog1) (word_seqs
         prog2)) in
          separate_lines (strlit "seq") (word_prog_to_display_list k
            ns xs))
        | ((SUC k),(pattern_semantics_If cmp n labLang_reg p1 p2)) ->
       displayLang_Item NONE (strlit "if")
         [displayLang_Tuple [asm_cmp_to_display cmp;
                 num_to_display n;
                 asm_reg_imm_to_display labLang_reg];
          word_prog_to_display k ns p1; word_prog_to_display k ns p2]
        | ((SUC k),(wordLang_Loop ns1 p ns2)) ->
       displayLang_Item NONE (strlit "Loop")
         [num_set_to_display ns1;
          word_prog_to_display k ns p;
          num_set_to_display ns2]
        | ((SUC k),(wordLang_Alloc n ms)) -> displayLang_Item NONE
          (strlit "alloc")
       [num_to_display n; num_sets_to_display ms]
        | ((SUC k),(wordLang_StoreConsts a b c d ws)) ->
          displayLang_Item NONE (strlit "store_consts")
       [num_to_display a;
        num_to_display b;
        num_to_display c;
        num_to_display d;
        displayLang_Tuple (ws_to_display ws)]
        | ((SUC k),(flatLang_Raise n)) -> item_with_num (strlit
          "raise") n
        | ((SUC k),(wordLang_Break n)) -> item_with_num (strlit
          "break") n
        | ((SUC k),(wordLang_Continue n)) -> item_with_num (strlit
          "continue") n
        | ((SUC k),(wordLang_Return n vs)) ->
        displayLang_Item NONE (strlit "return")
          [num_to_display n;
           displayLang_Tuple (MAP num_to_display vs)]
        | ((SUC k),wordLang_Tick) -> empty_item (strlit "tick")
        | ((SUC k),(labLang_LocValue n1 n2)) ->
       displayLang_Item NONE (strlit "loc_value") [displayLang_String
         (attach_name ns (SOME n1)); num_to_display n2]
        | ((SUC k),(labLang_Install n1 n2 n3 n4 ms)) ->
       displayLang_Item NONE (strlit "install") (
           MAP num_to_display [n1; n2; n3; n4] ++
             [num_sets_to_display ms])
        | ((SUC k),(wordLang_CodeBufferWrite n1 n2)) ->
       item_with_nums (strlit "code_buffer_write") [n1; n2]
        | ((SUC k),(wordLang_DataBufferWrite n1 n2)) ->
       item_with_nums (strlit "data_buffer_write") [n1; n2]
        | ((SUC k),(wordLang_FFI nm n1 n2 n3 n4 ms)) ->
       displayLang_Item NONE (strlit "ffi") (
           (string_imp nm :: MAP num_to_display [n1; n2; n3; n4]) ++
             [num_sets_to_display ms])
        | (k,[]) -> []
        | (k,(x :: xs)) ->
       match k with 0 -> [] | SUC k ->
       word_prog_to_display k ns x :: word_prog_to_display_list k ns
         xs
        | (k,NONE) -> empty_item (strlit "tail")
        | (k,(SOME (vs,ms,labLang_prog,n2,n3))) ->
       match k with 0 -> empty_item (strlit "...") | SUC k ->
       displayLang_Item NONE (strlit "returning") [displayLang_Tuple
         [displayLang_Tuple (MAP num_to_display vs); num_sets_to_display
         ms;
           word_prog_to_display k ns labLang_prog;
           displayLang_String (attach_name ns (SOME n2));
           num_to_display n3]]
        | (k,NONE) -> empty_item (strlit "no_handler")
        | (k,(SOME (n1,labLang_prog,n2,n3))) ->
       match k with 0 -> empty_item (strlit "...") | SUC k ->
       displayLang_Item NONE (strlit "handler") [displayLang_Tuple
         [num_to_display n1;
           word_prog_to_display k ns labLang_prog;
           displayLang_String (attach_name ns (SOME n2));
           num_to_display n3]]`;;

let word_fun_to_display_def = cake_define
  `word_fun_to_display names (n,argc,body) =
     displayLang_Tuple [displayLang_String (strlit "func");
            displayLang_String (attach_name names (SOME n));
            displayLang_Tuple (GENLIST (\n. num_to_display (2 * n))
              argc);
            word_prog_to_display 1000000000 names body]`;;

(* tap configuration *)

let tap_config_FIELDS = define_record "tap_config"
  ["explore_flag","bool"];;

let default_tap_config_def = cake_define
  `default_tap_config = mk_tap_config F`;;

(* ------------------------- *)

let map_to_append_def = cake_define
  `map_to_append f' [] = misc_Nil /\
   map_to_append f' (x :: xs) = mlsexp_Append (displayLang_List
     (f' x)) (map_to_append f' xs)`;;

let source_to_strs_def = cake_define
  `source_to_strs decs =
     map_to_append (str_tree_to_strs (strlit "\n\n") o
                    display_to_str_tree o
                    source_to_display_dec) decs`;;

let flat_to_strs_def = cake_define
  `flat_to_strs (decs:flatLang_exp list) =
     map_to_append (str_tree_to_strs (strlit "\n\n") o
                    display_to_str_tree o
                    flat_to_display) decs`;;

let clos_to_strs_def = cake_define
  `clos_to_strs (decs,funs) =
     (let names = get_src_names (decs ++ MAP (SND o SND) funs) LN in
       mlsexp_Append (map_to_append (str_tree_to_strs (strlit "\n\n")
         o
                              display_to_str_tree o
                              clos_dec_to_display names) decs)
              (map_to_append (str_tree_to_strs (strlit "\n\n") o
                              display_to_str_tree o
                              clos_fun_to_display names) funs))`;;

let bvl_to_strs_def = cake_define
  `bvl_to_strs names xs =
     map_to_append (str_tree_to_strs (strlit "\n\n") o
                    display_to_str_tree o
                    bvl_fun_to_display names) xs`;;

(* HOL4 ML code, not ported:
val bvl_test =
  “concat $ append $ bvl_to_strs
     (insert 50 «foo» (insert 60 «bar» LN))
     [(50,2,Let [Var 0; Var 1]
              $ Op (IntOp Add) [Var 0; Var 1; Var 2; Var 3]);
      (60,2,Let [Var 0; Var 1]
              $ Call 0 (SOME 50) [Var 2; Var 0])]”
  |> EVAL |> concl |> rand |> rand |> stringSyntax.fromHOLstring
  |> (fn t => (print "\n\n"; print t; print "\n"))
*)

let bvi_to_strs_def = cake_define
  `bvi_to_strs names xs =
     map_to_append (str_tree_to_strs (strlit "\n\n") o
                    display_to_str_tree o
                    bvi_fun_to_display names) xs`;;

(* HOL4 ML code, not ported:
val bvi_test =
  “concat $ append $ bvi_to_strs
     (insert 50 «foo» (insert 60 «bar» LN))
     [(50,2,Let [Var 0]
              $ Op (IntOp Add) [Var 0; Var 1; Var 2; Var 3]);
      (60,2,Let [Var 0; Var 1]
              $ Call 0 (SOME 50) [Var 2; Var 0] (SOME (Var 0)))]”
  |> EVAL |> concl |> rand |> rand |> stringSyntax.fromHOLstring
  |> (fn t => (print "\n\n"; print t; print "\n"))
*)

let data_to_strs_def = cake_define
  `data_to_strs names xs =
     map_to_append (str_tree_to_strs (strlit "\n\n") o
                    display_to_str_tree o
                    data_fun_to_display names) xs`;;

(* HOL4 ML code, not ported:
val data_test =
  “concat $ append $ data_to_strs
     (insert 50 «foo» (insert 60 «bar» LN))
     [(50,2,Seq (Move 5 1) $
            Seq (Assign 3 (IntOp Add) [0;1] NONE) $
            Seq (Assign 6 (IntOp Sub) [5;3] NONE) $ Return [6]);
      (60,2,Skip)]”
  |> EVAL |> concl |> rand |> rand |> stringSyntax.fromHOLstring
  |> (fn t => (print "\n\n"; print t; print "\n"));
*)

let word_to_strs_def = cake_define
  `word_to_strs names xs =
     map_to_append (str_tree_to_strs (strlit "\n\n") o
                    display_to_str_tree o
                    word_fun_to_display names) xs`;;

let stack_to_strs_def = cake_define
  `stack_to_strs names xs =
     map_to_append (str_tree_to_strs (strlit "\n\n") o
                    display_to_str_tree o
                    stack_fun_to_display names) xs`;;

let lab_to_strs_def = cake_define
  `lab_to_strs names xs =
     map_to_append (str_tree_to_strs (strlit "\n\n") o
                    display_to_str_tree o
                    lab_fun_to_display names) xs`;;

(* HOL4 ML code, not ported:
val lab_test =
  “concat $ append $ lab_to_strs
     (insert 50 «foo» (insert 60 «bar» LN))
     [Section 50 [Label 50 1 0;
                  Asm (Asmi (Inst (Const 5 (70w:word32)))) [] 0;
                  Label 50 2 0];
      Section 60 [Label 50 5 0]]”
  |> EVAL |> concl |> rand |> rand |> stringSyntax.fromHOLstring
  |> (fn t => (print "\n\n"; print t; print "\n"));
*)

(*

val names_tm = “(insert 50 «foo» (insert 60 «bar» LN))”

val data_prog_tm =
    “[(50,2,Seq (Move 5 1) $
            Seq (Assign 3 Add [0;1] NONE) $
            Seq (Assign 6 Sub [5;3] NONE) $ Return 6);
      (60n,2n,Skip)]”

val _ = data_to_strs data_prog_tm names_tm |> print_strs

*)
