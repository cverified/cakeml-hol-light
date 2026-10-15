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
needs "basis/pure/mlsexp.ml";;
needs "basis/pure/mlstring.ml";;
needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/bvi.ml";;
needs "compiler/backend/bvl.ml";;
needs "compiler/backend/bvl_jump.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/clos_known.ml";;
needs "compiler/backend/clos_to_bvl.ml";;
needs "compiler/backend/dataLang.ml";;
needs "compiler/backend/displayLang.ml";;
needs "compiler/backend/flatLang.ml";;
needs "compiler/backend/jsonLang.ml";;
needs "compiler/backend/labLang.ml";;
needs "compiler/backend/pattern_matching/pattern_semantics.ml";;
needs "compiler/backend/source_to_flat.ml";;
needs "compiler/backend/stackLang.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/backend/word_bignum.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "lib/binary_ieee.ml";;
needs "lib/comparison.ml";;
needs "lib/integer_word.ml";;
needs "lib/peg.ml";;
needs "lib/sptree.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/fpSem.ml";;
needs "semantics/namespace.ml";;

(* basics *)

let empty_item_def = cake_define
  `empty_item name = String name`;;

let num_to_display_def = cake_define
  `num_to_display (n:num) = String (toString n)`;;

let int_to_display_def = cake_define
  `int_to_display (i:int) = String (toString i)`;;

let string_imp_def = cake_define
  `string_imp s = String s`;;

let item_with_num_def = cake_define
  `item_with_num name n = displayLang_Item NONE name [num_to_display
  n]`;;

let item_with_nums_def = cake_define
  `item_with_nums name ns = displayLang_Item NONE name (MAP
  num_to_display ns)`;;

let bool_to_display_def = cake_define
  `bool_to_display b = empty_item (if b then (implode "True") else
  (implode "False"))`;;

let num_to_hex_def = cake_define
  `num_to_hex n =
     (if n < 16 then [] else num_to_hex (n DIV 16)) ++
     num_to_hex_digit (n MOD 16)`;;

let separate_lines_def = cake_define
  `separate_lines name xs = List (String name :: xs)`;;

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

let lit_to_display_def = cake_define_list
  [`lit_to_display (ast_IntLit i) =
        displayLang_Item NONE (implode "IntLit") [empty_item
          (toString i)]`;
   `lit_to_display (ast_Char c) =
        displayLang_Item NONE (implode "Char") [empty_item
          (implode ("#\"" ++ [c] ++ "\""))]`;
   `lit_to_display (ast_StrLit s) =
        displayLang_Item NONE (implode "StrLit") [string_imp s]`;
   `lit_to_display (ast_Word8 w) =
        displayLang_Item NONE (implode "Word8") [word_to_display
          w]`;
   `lit_to_display (ast_Word64 w) =
        displayLang_Item NONE (implode "Word64") [word_to_display
          w]`;
   `lit_to_display (ast_Float64 w) =
        displayLang_Item NONE (implode "Float64")
          [word_to_display w]`];;

(* HOL4 overload (expanded in the port):
     list_to_display = λf xs. displayLang$Tuple (MAP f xs) *)

(* HOL4 overload (expanded in the port):
     option_to_display = λf opt. case opt of
          | NONE => empty_item «none»
          | SOME opt' => Item NONE «some» [f opt'] *)
(* source *)

let fp_cmp_to_display_def = cake_define
  `fp_cmp_to_display cmp = (match cmp with FP_Less -> empty_item
  (implode "FP_Less") | FP_LessEqual -> empty_item (implode
  "FP_LessEqual") | FP_Greater -> empty_item (implode "FP_Greater") |
  FP_GreaterEqual -> empty_item (implode "FP_GreaterEqual") |
  FP_Equal -> empty_item (implode "FP_Equal"))`;;

let fp_uop_to_display_def = cake_define
  `fp_uop_to_display op = (match op with fpSem_FP_Abs -> empty_item
  (implode "FP_Abs") | fpSem_FP_Neg -> empty_item (implode "FP_Neg")
  | FP_Sqrt -> empty_item (implode "FP_Sqrt"))`;;

let fp_bop_to_display_def = cake_define
  `fp_bop_to_display op = (match op with FP_Add -> empty_item
  (implode "FP_Add") | FP_Sub -> empty_item (implode "FP_Sub") |
  FP_Mul -> empty_item (implode "FP_Mul") | FP_Div -> empty_item
  (implode "FP_Div"))`;;

let fp_top_to_display_def = cake_define
  `fp_top_to_display op =
     (match op with FP_Fma -> empty_item (implode "FP_Fma"))`;;

let word_size_to_display_def = cake_define_list
  [`word_size_to_display ast_W8 = empty_item (implode "W8")`;
   `word_size_to_display W64 = empty_item (implode "W64")`];;

let opb_to_display_def = cake_define_list
  [`opb_to_display ast_Lt = empty_item (implode "Lt")`;
   `opb_to_display ast_Gt = empty_item (implode "Gt")`;
   `opb_to_display ast_Leq = empty_item (implode "Leq")`;
   `opb_to_display ast_Geq = empty_item (implode "Geq")`];;

let opw_to_display_def = cake_define_list
  [`opw_to_display backend_common_Andw = empty_item (implode "Andw")`;
   `opw_to_display backend_common_Orw = empty_item (implode "Orw")`;
   `opw_to_display Xor = empty_item (implode "Xor")`;
   `opw_to_display Add = empty_item (implode "Add")`;
   `opw_to_display Sub = empty_item (implode "Sub")`];;

let shift_to_display_def = cake_define_list
  [`shift_to_display Lsl = empty_item (implode "Lsl")`;
   `shift_to_display Lsr = empty_item (implode "Lsr")`;
   `shift_to_display Asr = empty_item (implode "Asr")`;
   `shift_to_display Ror = empty_item (implode "Ror")`];;

let thunk_mode_to_display_def = cake_define_list
  [`thunk_mode_to_display Evaluated = empty_item (implode
  "Evaluated")`;
   `thunk_mode_to_display NotEvaluated = empty_item (implode
  "NotEvaluated")`];;

let thunk_op_to_display_def = cake_define_list
  [`thunk_op_to_display (AllocThunk m) =
        displayLang_Item NONE (implode "AllocThunk")
          [thunk_mode_to_display m]`;
   `thunk_op_to_display (UpdateThunk m) =
        displayLang_Item NONE (implode "UpdateThunk")
          [thunk_mode_to_display m]`;
   `thunk_op_to_display ForceThunk = empty_item (implode
  "ForceThunk")`];;

let test_to_display_def = cake_define_list
  [`test_to_display Equal = empty_item (implode "Equal")`;
   `test_to_display (ast_Compare cmp) = displayLang_Item NONE
  (implode "Compare") [opb_to_display cmp]`;
   `test_to_display (ast_AltCompare cmp) = displayLang_Item NONE
  (implode "AltCompare") [opb_to_display cmp]`];;

let arith_to_display_def = cake_define_list
  [`arith_to_display Add = empty_item (implode "Add")`;
   `arith_to_display Sub = empty_item (implode "Sub")`;
   `arith_to_display ast_Mul = empty_item (implode "Mul")`;
   `arith_to_display Div = empty_item (implode "Div")`;
   `arith_to_display Mod = empty_item (implode "Mod")`;
   `arith_to_display And = empty_item (implode "And")`;
   `arith_to_display Xor = empty_item (implode "Xor")`;
   `arith_to_display Or = empty_item (implode "Or")`;
   `arith_to_display ast_Neg = empty_item (implode "Neg")`;
   `arith_to_display Not = empty_item (implode "Not")`;
   `arith_to_display ast_Abs = empty_item (implode "Abs")`;
   `arith_to_display ast_Sqrt = empty_item (implode "Sqrt")`;
   `arith_to_display ast_FMA = empty_item (implode "FMA")`];;

let prim_type_to_display_def = cake_define
  `prim_type_to_display x1 =
      match x1 with
        ast_BoolT -> empty_item (implode "BoolT")
      | ast_IntT -> empty_item (implode "IntT")
      | ast_CharT -> empty_item (implode "CharT")
      | ast_StrT -> empty_item (implode "StrT")
      | ast_Float64T -> empty_item (implode "Float64T")
      | (ast_WordT ast_W8) -> empty_item (implode "WordT_W8")
      | (ast_WordT W64) -> empty_item (implode "WordT_W64")`;;

let lop_to_display_def = cake_define_list
  [`lop_to_display Andalso = empty_item (implode "Andalso")`;
   `lop_to_display Orelse = empty_item (implode "Orelse")`];;

let op_to_display_def = cake_define
  `op_to_display (p:ast_op) =
   (match p with Shift ws sh num' -> displayLang_Item NONE (implode
     "Shift")
                             [word_size_to_display ws;
                              shift_to_display sh;
                              num_to_display num'] | Arith a ty ->
                                displayLang_Item NONE (implode "Arith")
                          [arith_to_display a;
                           prim_type_to_display ty] | ast_FromTo ty1
                             ty2 -> displayLang_Item NONE (implode
                             "FromTo")
                          [prim_type_to_display ty1;
                           prim_type_to_display ty2] | Test test ty
                             -> displayLang_Item NONE (implode "Test")
                          [test_to_display test;
                           prim_type_to_display ty] | ast_Equality
                             -> empty_item (implode "Equality") |
                             ast_Opapp -> empty_item (implode
                             "Opapp") | ast_Opassign -> empty_item
                             (implode "Opassign") | ast_Opref ->
                             empty_item (implode "Opref") |
                             ast_Opderef -> empty_item (implode
                             "Opderef") | ast_Aw8alloc -> empty_item
                             (implode "Aw8alloc") | ast_Aw8sub ->
                             empty_item (implode "Aw8sub") |
                             ast_Aw8length -> empty_item (implode
                             "Aw8length") | ast_Aw8update ->
                             empty_item (implode "Aw8update") |
                             ast_CopyStrStr -> empty_item (implode
                             "CopyStrStr") | ast_CopyStrAw8 ->
                             empty_item (implode "CopyStrAw8") |
                             ast_CopyAw8Str -> empty_item (implode
                             "CopyAw8Str") | ast_CopyAw8Aw8 ->
                             empty_item (implode "CopyAw8Aw8") |
                             ast_Implode -> empty_item (implode
                             "Implode") | ast_Explode -> empty_item
                             (implode "Explode") | ast_Strsub ->
                             empty_item (implode "Strsub") |
                             ast_Strlen -> empty_item (implode
                             "Strlen") | ast_Strcat -> empty_item
                             (implode "Strcat") | ast_VfromList ->
                             empty_item (implode "VfromList") |
                             ast_Vsub -> empty_item (implode "Vsub")
                             | ast_Vsub_unsafe -> empty_item (implode
                             "Vsub_unsafe") | ast_Vlength ->
                             empty_item (implode "Vlength") |
                             ast_Aalloc -> empty_item (implode
                             "Aalloc") | ast_AallocEmpty ->
                             empty_item (implode "AallocEmpty") |
                             ast_AallocFixed -> empty_item (implode
                             "AallocFixed") | ast_Asub -> empty_item
                             (implode "Asub") | ast_Alength ->
                             empty_item (implode "Alength") |
                             ast_Aupdate -> empty_item (implode
                             "Aupdate") | ast_Asub_unsafe ->
                             empty_item (implode "Asub_unsafe") |
                             ast_Aupdate_unsafe -> empty_item
                             (implode "Aupdate_unsafe") |
                             ast_Aw8sub_unsafe -> empty_item (implode
                             "Aw8sub_unsafe") | ast_Aw8update_unsafe
                             -> empty_item (implode
                             "Aw8update_unsafe") |
                             ast_XorAw8Str_unsafe -> empty_item
                             (implode "XorAw8Str_unsafe") |
                             ListAppend -> empty_item (implode
                             "ListAppend") | ConfigGC -> empty_item
                             (implode "ConfigGC") | FFI v35 ->
                             empty_item (implode "FFI v35") |
                             ast_Eval -> empty_item (implode "Eval")
                             | ast_Env_id -> empty_item (implode
                             "Env_id") | ThunkOp t ->
                             thunk_op_to_display t)`;;

let id_to_display_def = cake_define_list
  [`id_to_display (Short n) =
      displayLang_Item NONE (implode "Short") [String n]`;
   `id_to_display (Long n i) =
      displayLang_Item NONE (implode "Long") [String n;
        id_to_display i]`];;

let ast_t_to_display_def = cake_define_list
  [`ast_t_to_display c =
      (match c with Atvar n -> displayLang_Item NONE (implode
        "Atvar") [String n] | Atfun t1 t2 -> displayLang_Item NONE
        (implode "Atfun") [ast_t_to_display t1; ast_t_to_display t2] |
        Attup ts -> displayLang_Item NONE (implode "Attup") [Tuple
        (ast_t_to_display_list ts)] | Atapp ts id' -> displayLang_Item
        NONE (implode "Attup") [Tuple (ast_t_to_display_list ts);
                              id_to_display id'])`;
   `ast_t_to_display_list [] = []`;
   `ast_t_to_display_list (x :: xs) =
        ast_t_to_display x :: ast_t_to_display_list xs`];;

let pat_to_display_def = cake_define_list
  [`pat_to_display (c:ast_pat) =
      (match c with Pany -> displayLang_Item NONE (implode "Pany")
        [] | Pvar v -> displayLang_Item NONE (implode "Pvar") [String v]
        | Plit l -> displayLang_Item NONE (implode "Plit")
        [lit_to_display l] | Pcon opt_id pats ->
          displayLang_Item NONE (implode "Pcon") [(\f opt. match opt
            with NONE -> empty_item (implode "none") | SOME opt' ->
            displayLang_Item NONE (implode "some") [f opt'])
            id_to_display opt_id;
                            Tuple (pat_to_display_list pats)] |
                              Pas t v -> displayLang_Item NONE
                              (implode "Pas") [pat_to_display t;
                              String v] | Pref t -> displayLang_Item
                              NONE (implode "Pref") [pat_to_display
                              t] | ast_Ptannot x y ->
                              displayLang_Item NONE (implode
                              "Ptannot") [pat_to_display x;
                              ast_t_to_display y])`;
   `pat_to_display_list [] = []`;
   `pat_to_display_list (x :: xs) =
        pat_to_display x :: pat_to_display_list xs`];;

let exp_to_display_def = cake_define_list
  [`exp_to_display (c:ast_exp) =
      (match c with Lit l -> displayLang_Item NONE (implode "Lit")
        [lit_to_display l] | Raise e -> displayLang_Item NONE (implode
        "Raise") [exp_to_display e] | Con opt_id es -> displayLang_Item
        NONE (implode "Con") [(\f opt. match opt with NONE -> empty_item
        (implode "none") | SOME opt' -> displayLang_Item NONE (implode
        "some") [f opt']) id_to_display opt_id;
                              Tuple (exp_to_display_list es)] | Var
                                id' -> displayLang_Item NONE (implode
                                "Var") [id_to_display id'] | Fun n e ->
                                displayLang_Item NONE (implode "Fun")
                                [String n; exp_to_display e] | App op es
                                -> displayLang_Item NONE (implode "App")
                                (op_to_display op ::
                              exp_to_display_list es) | ast_Log lop
                                e1 e2 -> displayLang_Item NONE (implode
                                "Log") [lop_to_display lop;
                              exp_to_display e1;
                              exp_to_display e2] | If e1 e2 e3 ->
                                displayLang_Item NONE (implode "If")
                                [exp_to_display e1;
                              exp_to_display e2;
                              exp_to_display e3] | Let n_opt e1 e2
                                -> displayLang_Item NONE (implode "Let")
          [(\f opt. match opt with NONE -> empty_item (implode
            "none") | SOME opt' -> displayLang_Item NONE (implode
            "some") [f opt']) String n_opt;
           exp_to_display e1;
           exp_to_display e2] | Mat e pats ->
          displayLang_Item NONE (implode "Mat")
          [exp_to_display e;
           Tuple (pat_exp_to_display_list pats)] | Handle e pats ->
          displayLang_Item NONE (implode "Handle")
          [exp_to_display e;
           Tuple (pat_exp_to_display_list pats)] | Letrec fns e ->
          displayLang_Item NONE (implode "Letrec")
          [Tuple (fun_to_display_list fns);
           exp_to_display e] | ast_Tannot e _1 ->
             displayLang_Item NONE (implode "Tannot") [exp_to_display
             e] | ast_Lannot e _2 -> displayLang_Item NONE (implode
             "Lannot") [exp_to_display e])`;
   `exp_to_display_list [] = []`;
   `exp_to_display_list (x :: xs) =
        exp_to_display x :: exp_to_display_list xs`;
   `pat_exp_to_display_list [] = []`;
   `pat_exp_to_display_list ((p,e) :: xs) =
        Tuple [pat_to_display p; exp_to_display e] ::
        pat_exp_to_display_list xs`;
   `fun_to_display_list [] = []`;
   `fun_to_display_list ((m,n,e) :: xs) =
        Tuple [String m;
               String n;
               exp_to_display e] ::
        fun_to_display_list xs`];;

let source_to_display_dec_def = cake_define_list
  [`source_to_display_dec (d:dec) =
      (match d with Dlet _3 pat e -> displayLang_Item NONE (implode
        "Dlet") [pat_to_display pat; exp_to_display e] | Dletrec _4 fns
        -> displayLang_Item NONE (implode "Dletrec")
                              (MAP (\(m,n,e). Tuple [String m;
                              String n;
                              exp_to_display e]) fns) | Dtype _5 ts
                                -> displayLang_Item NONE (implode
                                "Dtype") (MAP (\(ns,n,z).
                        Tuple [Tuple (MAP String ns);
                              String n;
                              Tuple (MAP (\(n,tys). Tuple [String n;
                              Tuple (MAP ast_t_to_display tys)])
                                z)]) ts) | Dtabbrev _6 ns n ty ->
          displayLang_Item NONE (implode "Dtabbrev") [Tuple (MAP
            String ns);
                              String n;
                              ast_t_to_display ty] | Dexn _7 n tys
                                -> displayLang_Item NONE (implode
                                "Dexn") [String n;
                              Tuple (MAP ast_t_to_display tys)] |
                                Dmod n ds -> displayLang_Item NONE
                                (implode "Dmod") [String n;
                              Tuple (source_to_display_dec_list ds)]
                                | Dlocal xs ys -> displayLang_Item NONE
                                (implode "Dlocal") [Tuple
                                (source_to_display_dec_list xs);
                              Tuple (source_to_display_dec_list
                                ys)] | Denv n -> displayLang_Item
                                NONE (implode "Denv") [String n])`;
   `source_to_display_dec_list [] = []`;
   `source_to_display_dec_list (x :: xs) =
        source_to_display_dec x :: source_to_display_dec_list xs`];;

(* flatLang *)

let opt_con_to_display_def = cake_define
  `opt_con_to_display ocon = (match ocon with NONE -> empty_item
  (implode "ConIdNone") | SOME (c,NONE) -> item_with_num (implode
  "ConIdUntyped") c | SOME (c,SOME t) -> item_with_nums (implode
  "ConIdTyped") [c; t])`;;

let flat_pat_to_display_def = cake_define_list
  [`flat_pat_to_display p =
        (match p with flatLang_Pvar varN -> displayLang_Item NONE
          (implode "Pvar") [string_imp varN] | Pany -> empty_item
          (implode "Pany") | Plit lit -> displayLang_Item NONE (implode
          "Plit") [lit_to_display lit] | flatLang_Pcon id' pats ->
          displayLang_Item NONE (implode "Pcon")
                (flat_pat_to_display_list pats) | Pas pat varN ->
                  displayLang_Item NONE (implode "Pas")
                  [flat_pat_to_display pat;
                              string_imp varN] | Pref pat ->
                                displayLang_Item NONE (implode
                                "Pref") [flat_pat_to_display pat])`;
   `flat_pat_to_display_list [] = []`;
   `flat_pat_to_display_list (x :: xs) =
        flat_pat_to_display x :: flat_pat_to_display_list xs`];;

let flat_op_to_display_def = cake_define
  `flat_op_to_display op = (match op with flatLang_Src ast_op ->
  op_to_display ast_op | flatLang_GlobalVarAlloc n -> item_with_num
  (implode "GlobalVarAlloc") n | flatLang_GlobalVarInit n ->
  item_with_num (implode "GlobalVarInit") n |
  flatLang_GlobalVarLookup n -> item_with_num (implode
  "GlobalVarLookup") n | TagLenEq n1 n2 -> item_with_nums (implode
  "TagLenEq") [n1; n2] | LenEq n1 -> item_with_nums (implode "LenEq")
  [n1] | El n -> item_with_num (implode "El") n | flatLang_Id ->
  empty_item (implode "Id"))`;;

let add_name_hint_def = cake_define
  `add_name_hint prefix name_hint =
     mlstring_concat [prefix; (implode "<"); name_hint; (implode
       ">")]`;;

let flat_to_display_def = cake_define_list
  [`flat_to_display (flatLang_Raise tra exp) =
        displayLang_Item (SOME tra) (implode "raise")
          [flat_to_display exp]`;
   `flat_to_display (Handle tra exp pes:flatLang_exp) =
        displayLang_Item (SOME tra) (implode "handle") (
            flat_to_display exp :: pat_flat_to_display_list pes)`;
   `flat_to_display (Lit tra lit:flatLang_exp) = displayLang_Item
  (SOME tra) (implode "lit") []`;
   `flat_to_display (flatLang_Con tra id_opt exps) =
        displayLang_Item (SOME tra) (implode "con") (
            opt_con_to_display id_opt :: flat_to_display_list
              exps)`;
   `flat_to_display (flatLang_Var_local tra varN) =
        displayLang_Item (SOME tra) (implode "var_local")
          [string_imp varN]`;
   `flat_to_display (Fun name_hint varN exp:flatLang_exp) =
        displayLang_Item (SOME backend_common_None) (add_name_hint
          (implode "fun") name_hint)
          [string_imp varN; flat_to_display exp]`;
   `flat_to_display (App tra op exps:flatLang_exp) =
        displayLang_Item (SOME tra) (implode "app")
          (flat_op_to_display op :: flat_to_display_list exps)`;
   `flat_to_display (If tra exp1 exp2 exp3:flatLang_exp) =
        displayLang_Item (SOME tra) (implode "if") [flat_to_display
          exp1; flat_to_display exp2;
            flat_to_display exp3]`;
   `flat_to_display (Mat tra exp pes:flatLang_exp) =
        displayLang_Item (SOME tra) (implode "mat") (
            flat_to_display exp :: pat_flat_to_display_list pes)`;
   `flat_to_display (Let tra varN_opt exp1 exp2:flatLang_exp) =
        displayLang_Item (SOME tra) (implode "let") [(\f opt. match
          opt with NONE -> empty_item (implode "none") | SOME opt' ->
          displayLang_Item NONE (implode "some") [f opt']) string_imp
          varN_opt;
            flat_to_display exp1; flat_to_display exp2]`;
   `flat_to_display (Letrec name_hint funs exp:flatLang_exp) =
        displayLang_Item (SOME backend_common_None) (add_name_hint
          (implode "letrec") name_hint)
            [Tuple (fun_flat_to_display_list funs);
              flat_to_display exp]`;
   `flat_to_display_list [] = []`;
   `flat_to_display_list (x :: xs) =
        flat_to_display x :: flat_to_display_list xs`;
   `pat_flat_to_display_list [] = []`;
   `pat_flat_to_display_list ((pat,exp) :: xs) =
        displayLang_Tuple [flat_pat_to_display pat;
          flat_to_display exp] :: pat_flat_to_display_list xs`;
   `fun_flat_to_display_list [] = []`;
   `fun_flat_to_display_list ((v1,v2,e) :: xs) =
         Tuple [string_imp v1; string_imp v2; flat_to_display e] ::
            fun_flat_to_display_list xs`];;

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

let attach_name_def = cake_define_list
  [`attach_name ns NONE = (implode "none")`;
   `attach_name ns (SOME d) =
      (match sptree_lookup d ns with NONE -> toString d | SOME
        name -> mlstring_concat [name; (implode "@"); toString d])`];;

let const_part_to_display_def = cake_define_list
  [`const_part_to_display (Int i:const_part) =
      displayLang_Item NONE (implode "Int") [int_to_display i]`;
   `const_part_to_display (Con t vs:const_part) =
      displayLang_Item NONE (implode "Con") [num_to_display t;
        Tuple (MAP num_to_display vs)]`;
   `const_part_to_display (Str s:const_part) =
      displayLang_Item NONE (implode "Str") [String
        (mlstring_concat [implode "\""; s; implode "\""])]`;
   `const_part_to_display (W64 w:const_part) =
      displayLang_Item NONE (implode "W64") [word_to_display w]`];;

let const_to_display_def = cake_define_list
  [`const_to_display (ConstInt i:const) =
      displayLang_Item NONE (implode "ConstInt") [int_to_display
        i]`;
   `const_to_display (ConstCons t vs) =
      displayLang_Item NONE (implode "ConstCons") [num_to_display
        t; Tuple (const_to_display_list vs)]`;
   `const_to_display (ConstStr s) =
      displayLang_Item NONE (implode "ConstStr") [String
        (mlstring_concat [implode "\""; s; implode "\""])]`;
   `const_to_display (ConstWord64 w) =
      displayLang_Item NONE (implode "ConstWord64")
        [word_to_display w]`;
   `const_to_display_list [] = []`;
   `const_to_display_list (x :: xs) =
        const_to_display x :: const_to_display_list xs`];;

let clos_op_to_display_def = cake_define
  `clos_op_to_display ns op = (match op with closLang_GlobOp (Global
  num') -> item_with_num (implode "Global") num' | closLang_GlobOp
  (SetGlobal num') -> item_with_num (implode "SetGlobal") num' |
  closLang_GlobOp AllocGlobal -> String (implode "AllocGlobal") |
  closLang_GlobOp GlobalsPtr -> String (implode "GlobalsPtr") |
  closLang_GlobOp SetGlobalsPtr -> String (implode "SetGlobalsPtr") |
  closLang_BlockOp (Cons num') -> item_with_num (implode "Cons") num' |
  closLang_BlockOp (closLang_ElemAt num') -> item_with_num (implode
  "ElemAt") num' | closLang_BlockOp (TagLenEq n1 n2) -> item_with_nums
  (implode "TagLenEq") [n1; n2] | closLang_BlockOp (closLang_BoolTest
  test) -> displayLang_Item NONE (implode "BoolTest") [test_to_display
  test] | closLang_BlockOp closLang_BoolNot -> String (implode
  "BoolNot") | closLang_BlockOp (LenEq num') -> item_with_num (implode
  "LenEq") num' | closLang_BlockOp (closLang_TagEq num') ->
  item_with_num (implode "TagEq") num' | closLang_BlockOp
  closLang_LengthBlock -> String (implode "LengthBlock") |
  closLang_BlockOp closLang_BoundsCheckBlock -> String (implode
  "BoundsCheckBlock") | closLang_BlockOp (closLang_ConsExtend num') ->
  item_with_num (implode "ConsExtend") num' | closLang_BlockOp
  (closLang_FromList num') -> item_with_num (implode "FromList") num' |
  closLang_BlockOp ListAppend -> String (implode "ListAppend") |
  closLang_BlockOp (closLang_Constant c) -> displayLang_Item NONE
  (implode "Constant") [const_to_display c] | closLang_BlockOp Equal ->
  String (implode "Equal") | closLang_BlockOp (closLang_EqualConst c) ->
  displayLang_Item NONE (implode "EqualConst") [const_part_to_display c]
  | closLang_BlockOp (closLang_Build bs) -> displayLang_Item NONE
  (implode "Build") (MAP const_part_to_display bs) | closLang_MemOp Ref
  -> String (implode "Ref") | closLang_MemOp closLang_Update -> String
  (implode "Update") | closLang_MemOp El -> String (implode "El") |
  closLang_MemOp closLang_Length -> String (implode "Length") |
  closLang_MemOp closLang_LengthByte -> String (implode "LengthByte") |
  closLang_MemOp (closLang_RefByte b) -> displayLang_Item NONE (implode
  "RefByte") [bool_to_display b] | closLang_MemOp closLang_RefArray ->
  String (implode "RefArray") | closLang_MemOp closLang_DerefByte ->
  String (implode "DerefByte") | closLang_MemOp closLang_UpdateByte ->
  String (implode "UpdateByte") | closLang_MemOp closLang_ConcatByteVec
  -> String (implode "ConcatByteVec") | closLang_MemOp
  (closLang_CopyByte b) -> displayLang_Item NONE (implode "CopyByte")
  [bool_to_display b] | closLang_MemOp closLang_FromListByte -> String
  (implode "FromListByte") | closLang_MemOp closLang_ToListByte ->
  String (implode "ToListByte") | closLang_MemOp closLang_LengthByteVec
  -> String (implode "LengthByteVec") | closLang_MemOp
  closLang_DerefByteVec -> String (implode "DerefByteVec") |
  closLang_MemOp closLang_BoundsCheckArray -> String (implode
  "BoundsCheckArray") | closLang_MemOp (closLang_BoundsCheckByte b) ->
  displayLang_Item NONE (implode "BoundsCheckByte") [bool_to_display b]
  | closLang_MemOp closLang_ConfigGC -> String (implode "ConfigGC") |
  closLang_MemOp (closLang_StringCmp b opb) -> displayLang_Item NONE
  (implode "StringCmp") [bool_to_display b;
                              opb_to_display opb] | closLang_MemOp
                                closLang_XorByte -> String (implode
                                "XorByte") | closLang_MemOp
                                (closLang_MutCons tag i) ->
                                item_with_nums (implode "MutCons") [tag;
                                i] | closLang_MemOp closLang_UpdateCons
                                -> String (implode "UpdateCons") |
                                closLang_MemOp closLang_FinaliseCons ->
                                String (implode "FinaliseCons") | Label
                                num' -> displayLang_Item NONE (implode
                                "Label") [String (attach_name ns (SOME
                                num'))] | FFI s -> displayLang_Item NONE
                                (implode "FFI") [string_imp s] |
                                closLang_IntOp (Const i) ->
                                displayLang_Item NONE (implode "Const")
                                [int_to_display i] | closLang_IntOp Add
                                -> String (implode "Add") |
                                closLang_IntOp Sub -> String (implode
                                "Sub") | closLang_IntOp closLang_Mult ->
                                String (implode "Mult") | closLang_IntOp
                                Div -> String (implode "Div") |
                                closLang_IntOp Mod -> String (implode
                                "Mod") | closLang_IntOp Less -> String
                                (implode "Less") | closLang_IntOp
                                closLang_LessEq -> String (implode
                                "LessEq") | closLang_IntOp Greater ->
                                String (implode "Greater") |
                                closLang_IntOp closLang_GreaterEq ->
                                String (implode "GreaterEq") |
                                closLang_IntOp (closLang_LessConstSmall
                                num') -> item_with_num (implode
                                "LessConstSmall") num' | closLang_WordOp
                                (WordOpw ws op) -> displayLang_Item NONE
                                (implode "WordOp")
                              [word_size_to_display ws;
                              opw_to_display op] | closLang_WordOp
                                (WordShift ws sh num') ->
                                displayLang_Item NONE (implode
                                "WordShift")
                              [word_size_to_display ws;
                              shift_to_display sh;
                              num_to_display num'] | closLang_WordOp
                                (WordTest ws test) -> displayLang_Item
                                NONE (implode "WordTest")
                              [word_size_to_display ws;
                              test_to_display test] |
                                closLang_WordOp WordFromInt -> String
                                (implode "WordFromInt") |
                                closLang_WordOp WordToInt -> String
                                (implode "WordToInt") |
                                closLang_WordOp (WordFromWord b) ->
                                displayLang_Item NONE (implode
                                "WordFromWord") [bool_to_display b] |
                                closLang_WordOp (FP_cmp cmp) ->
                                fp_cmp_to_display cmp |
                                closLang_WordOp (FP_uop op) ->
                                fp_uop_to_display op |
                                closLang_WordOp (FP_bop op) ->
                                fp_bop_to_display op |
                                closLang_WordOp (FP_top op) ->
                                fp_top_to_display op | Install ->
                                String (implode "Install") | ThunkOp
                                t -> thunk_op_to_display t)`;;

let commas_def = cake_define
  `presLang_commas x1 =
      match x1 with
        [] -> (implode "")
      | [x] -> x
      | (x :: xs) -> (\x y. strcat x y) ((\x y. strcat x y) x
        (implode ",")) (presLang_commas xs)`;;
hol4_overload "commas" "presLang_commas";;

(* The clos_to_display ns function uses the same approach to de bruijn
   indices as the pat_to_display function *)
let clos_to_display_def = cake_define_list
  [`clos_to_display ns h (Var t n:flatLang_exp) =
        displayLang_Item (SOME t) (implode "var")
          [display_num_as_varn (h - n - 1)]`;
   `clos_to_display ns h (If t x1 x2 x3:flatLang_exp) =
        displayLang_Item (SOME t) (implode "if") [clos_to_display ns
          h x1; clos_to_display ns h x2;
            clos_to_display ns h x3]`;
   `clos_to_display ns h (closLang_Let t xs x) =
        separate_lines (implode "let")
            [Tuple (clos_to_display_lets ns h (LENGTH xs - 1) xs);
                clos_to_display ns (h + LENGTH xs) x]`;
   `clos_to_display ns h (Raise t x:flatLang_exp) =
        displayLang_Item (SOME t) (implode "raise")
          [clos_to_display ns h x]`;
   `clos_to_display ns h (Tick t x:flatLang_exp) =
        displayLang_Item (SOME t) (implode "tick")
          [clos_to_display ns h x]`;
   `clos_to_display ns h (Handle t x y:flatLang_exp) =
        displayLang_Item (SOME t) (implode "handle")
            [clos_to_display ns h x; display_num_as_varn h;
                clos_to_display ns (h + 1) y]`;
   `clos_to_display ns h (Call t ticks dest xs:flatLang_exp) =
        displayLang_Item (SOME t) (implode "call")
          ([num_to_display ticks; String (attach_name ns (SOME
            dest))] ++
           (clos_to_display_list ns h xs))`;
   `clos_to_display ns h (App t opt_n x xs:flatLang_exp) =
        displayLang_Item (SOME t) (implode "app")
            ([(\f opt. match opt with NONE -> empty_item (implode
              "none") | SOME opt' -> displayLang_Item NONE (implode
              "some") [f opt']) num_to_display opt_n;
              clos_to_display ns h x] ++ (clos_to_display_list ns
                h xs))`;
   `clos_to_display ns h (closLang_Fn name_hint n1 n2 vn x) =
        displayLang_Item (SOME backend_common_None) (add_name_hint
          (implode "fn") name_hint)
            [(\f opt. match opt with NONE -> empty_item (implode
              "none") | SOME opt' -> displayLang_Item NONE (implode
              "some") [f opt']) num_to_display n1;
             (\f opt. match opt with NONE -> empty_item (implode
               "none") | SOME opt' -> displayLang_Item NONE (implode
               "some") [f opt']) ((\f xs. displayLang_Tuple (MAP f xs))
               num_to_display) n2;
             (\f xs. displayLang_Tuple (MAP f xs)) string_imp
               (num_to_varn_list h vn);
             clos_to_display ns h x]`;
   `clos_to_display ns h (closLang_Letrec name_hint n1 n2 es e) =
        displayLang_Item (SOME backend_common_None) (add_name_hint
          (implode "letrec") (presLang_commas name_hint))
            [(\f opt. match opt with NONE -> empty_item (implode
              "none") | SOME opt' -> displayLang_Item NONE (implode
              "some") [f opt']) num_to_display n1;
             (\f opt. match opt with NONE -> empty_item (implode
               "none") | SOME opt' -> displayLang_Item NONE (implode
               "some") [f opt']) ((\f xs. displayLang_Tuple (MAP f xs))
               num_to_display) n2;
             Tuple (clos_to_display_letrecs ns h (LENGTH es - 1)
               (LENGTH es) es);
             clos_to_display ns h e]`;
   `clos_to_display ns h (Op t op xs:flatLang_exp) =
        displayLang_Item (SOME t) (implode "op") (clos_op_to_display
          LN op ::
            (clos_to_display_list ns h xs))`;
   `clos_to_display_list ns h [] = []`;
   `clos_to_display_list ns h (x :: xs) =
        clos_to_display ns h x :: clos_to_display_list ns h xs`;
   `clos_to_display_lets ns h i [] = []`;
   `clos_to_display_lets ns h i (x :: xs) =
        Tuple [display_num_as_varn (h + i); String (implode
          "<-"); clos_to_display ns h x] :: clos_to_display_lets ns h
          (i - 1) xs`;
   `clos_to_display_letrecs ns h i len [] = []`;
   `clos_to_display_letrecs ns h i len ((vn,e) :: es) =
        Tuple [display_num_as_varn (h + i);
            (\f xs. displayLang_Tuple (MAP f xs)) string_imp
              (num_to_varn_list ((h + len) - 1) vn);
            clos_to_display ns (h + len + vn) e] ::
              clos_to_display_letrecs ns h (i - 1) len es`];;

let clos_fun_to_display_def = cake_define
  `clos_fun_to_display names (n,argc,body) =
     Tuple [String (implode "func");
            String (attach_name names (SOME n));
            Tuple (REVERSE (GENLIST display_num_as_varn argc));
            clos_to_display names argc body]`;;

let clos_dec_to_display_def = cake_define
  `clos_dec_to_display names dec =
     Tuple [String (implode "dec");
            clos_to_display names 0 dec]`;;

(* bvl to displayLang *)

let bvl_to_display_def = cake_define_list
  [`bvl_to_display ns h (Var n:flatLang_exp) =
        displayLang_Item NONE (implode "var")
          [display_num_as_varn (h - n - 1)]`;
   `bvl_to_display ns h (If x1 x2 x3:flatLang_exp) =
        displayLang_Item NONE (implode "if") [bvl_to_display ns h
          x1; bvl_to_display ns h x2;
            bvl_to_display ns h x3]`;
   `bvl_to_display ns h (bvl_Let xs x) =
        separate_lines (implode "let")
            (bvl_to_display_lets ns h (LENGTH xs - 1) xs ++
                [bvl_to_display ns (h + LENGTH xs) x])`;
   `bvl_to_display ns h (Raise x:flatLang_exp) =
        displayLang_Item NONE (implode "raise") [bvl_to_display
          ns h x]`;
   `bvl_to_display ns h (Tick x:flatLang_exp) =
        displayLang_Item NONE (implode "tick") [bvl_to_display ns
          h x]`;
   `bvl_to_display ns h (Handle x y:flatLang_exp) =
        displayLang_Item NONE (implode "handle")
            [bvl_to_display ns h x; display_num_as_varn h;
                bvl_to_display ns (h + 1) y]`;
   `bvl_to_display ns h (Call ticks dest xs:flatLang_exp) =
        displayLang_Item NONE (implode "call")
             (String (attach_name ns dest) ::
              (bvl_to_display_list ns h xs))`;
   `bvl_to_display ns h (Force loc n:flatLang_exp) =
        displayLang_Item NONE (implode "force")
             [display_num_as_varn (h - n - 1); String
               (attach_name ns (SOME loc))]`;
   `bvl_to_display ns h (Op op xs:flatLang_exp) =
        displayLang_Item NONE (implode "op") (clos_op_to_display ns
          op ::
                              (bvl_to_display_list ns h xs))`;
   `bvl_to_display_list ns h [] = []`;
   `bvl_to_display_list ns h (x :: xs) =
        bvl_to_display ns h x :: bvl_to_display_list ns h xs`;
   `bvl_to_display_lets ns h i [] = []`;
   `bvl_to_display_lets ns h i (x :: xs) =
        Tuple [display_num_as_varn (h + i); String (implode
          "<-"); bvl_to_display ns h x] :: bvl_to_display_lets ns h
          (i - 1) xs`];;

let bvl_fun_to_display_def = cake_define
  `bvl_fun_to_display names (n,argc,body) =
     Tuple [String (implode "func");
            String (attach_name names (SOME n));
            Tuple (REVERSE (GENLIST display_num_as_varn argc));
            bvl_to_display names argc body]`;;

(* bvi to displayLang *)

let bvi_to_display_def = cake_define_list
  [`bvi_to_display ns h (Var n:flatLang_exp) =
        displayLang_Item NONE (implode "var")
          [display_num_as_varn (h - n - 1)]`;
   `bvi_to_display ns h (If x1 x2 x3:flatLang_exp) =
        displayLang_Item NONE (implode "if") [bvi_to_display ns h
          x1; bvi_to_display ns h x2;
            bvi_to_display ns h x3]`;
   `bvi_to_display ns h (bvi_Let xs x) =
        separate_lines (implode "let")
            (bvi_to_display_lets ns h (LENGTH xs - 1) xs ++
                [bvi_to_display ns (h + LENGTH xs) x])`;
   `bvi_to_display ns h (Raise x:flatLang_exp) =
        displayLang_Item NONE (implode "raise") [bvi_to_display
          ns h x]`;
   `bvi_to_display ns h (Tick x:flatLang_exp) =
        displayLang_Item NONE (implode "tick") [bvi_to_display ns
          h x]`;
   `bvi_to_display ns h (Call ticks dest xs handler:flatLang_exp) =
        displayLang_Item NONE (implode "call")
             ((String (attach_name ns dest) ::
              (bvi_to_display_list ns h xs)) ++
              (match handler with NONE -> [] | SOME e ->
                [displayLang_Item NONE (implode "handler")
                [display_num_as_varn h;
                              empty_item (implode "->");
                              bvi_to_display ns (h + 1) e]]))`;
   `bvi_to_display ns h (Force loc n:flatLang_exp) =
        displayLang_Item NONE (implode "force")
             [display_num_as_varn (h - n - 1); String
               (attach_name ns (SOME loc))]`;
   `bvi_to_display ns h (Op op xs:flatLang_exp) =
        displayLang_Item NONE (implode "op") (clos_op_to_display ns
          op ::
                              (bvi_to_display_list ns h xs))`;
   `bvi_to_display ns h (Return xs:flatLang_exp) =
        displayLang_Item NONE (implode "return")
          (bvi_to_display_list ns h xs)`;
   `bvi_to_display ns h (bvi_LetCall rets ticks dest xs y) =
        separate_lines (implode "letcall")
            [displayLang_Item NONE (implode "call")
               (String (attach_name ns (SOME dest)) ::
                 bvi_to_display_list ns h xs);
             Tuple (REVERSE (GENLIST (\i. display_num_as_varn (h +
               i)) rets));
             bvi_to_display ns (h + rets) y]`;
   `bvi_to_display_list ns h [] = []`;
   `bvi_to_display_list ns h (x :: xs) =
        bvi_to_display ns h x :: bvi_to_display_list ns h xs`;
   `bvi_to_display_lets ns h i [] = []`;
   `bvi_to_display_lets ns h i (x :: xs) =
        Tuple [display_num_as_varn (h + i); String (implode
          "<-"); bvi_to_display ns h x] :: bvi_to_display_lets ns h
          (i - 1) xs`];;

let bvi_fun_to_display_def = cake_define
  `bvi_fun_to_display names (n,argc,body) =
     Tuple [String (implode "func");
            String (attach_name names (SOME n));
            Tuple (REVERSE (GENLIST display_num_as_varn argc));
            bvi_to_display names argc body]`;;

(* dataLang *)

let num_set_to_display_def = cake_define
  `num_set_to_display ns =
     String (mlstring_concat [(implode "{");
                      presLang_commas (MAP toString (MAP FST
                        (toSortedAList ns)));
                      (implode "}")])`;;

let data_seqs_def = cake_define
  `data_seqs z =
     (match z with dataLang_Seq x y -> Append (data_seqs x)
       (data_seqs y) | _8 -> List [z])`;;

let data_prog_to_display_def = cake_define_list
  [`data_prog_to_display 0 ns prog = empty_item (implode "...")`;
   `data_prog_to_display (SUC k) ns prog =
          (match prog with dataLang_Skip -> empty_item (implode
            "skip") | dataLang_Move x y -> Tuple
            [num_to_display x; String (implode ":="); num_to_display
              y] | Call rets target args NONE -> displayLang_Item NONE
              (implode "call")
            [(\f opt. match opt with NONE -> empty_item (implode
              "none") | SOME opt' -> displayLang_Item NONE (implode
              "some") [f opt']) (\(x,y). Tuple
                    [(\f xs. displayLang_Tuple (MAP f xs))
                      num_to_display x;
                     num_set_to_display y]) rets;
                String (attach_name ns target);
                (\f xs. displayLang_Tuple (MAP f xs)) num_to_display
                  args;
                empty_item (implode "none")] | Call rets target args
                  (SOME (v,handler)) -> displayLang_Item NONE (implode
                  "call")
            [(\f opt. match opt with NONE -> empty_item (implode
              "none") | SOME opt' -> displayLang_Item NONE (implode
              "some") [f opt']) (\(x,y). Tuple
                    [(\f xs. displayLang_Tuple (MAP f xs))
                      num_to_display x;
                     num_set_to_display y]) rets;
                String (attach_name ns target);
                (\f xs. displayLang_Tuple (MAP f xs)) num_to_display
                  args;
                displayLang_Item NONE (implode "some") [Tuple
                  [num_to_display v;
                    data_prog_to_display k ns handler]]] | Force ret
                      loc src -> displayLang_Item NONE (implode "force")
            [(\f opt. match opt with NONE -> empty_item (implode
              "none") | SOME opt' -> displayLang_Item NONE (implode
              "some") [f opt']) (\(x,y). Tuple
                    [num_to_display x; num_set_to_display y]) ret;
             num_to_display loc;
             num_to_display src] | Assign n op args n_set -> Tuple
            [num_to_display n;
             String (implode ":=");
             clos_op_to_display ns op;
                (\f xs. displayLang_Tuple (MAP f xs)) num_to_display
                  args;
                (\f opt. match opt with NONE -> empty_item (implode
                  "none") | SOME opt' -> displayLang_Item NONE (implode
                  "some") [f opt']) num_set_to_display n_set] | Seq x y
                  ->
            (let xs = append (Append (data_seqs x) (data_seqs y)) in
               separate_lines (implode "seq")
                 (data_prog_to_display_list k ns xs)) | If n x y ->
                 displayLang_Item NONE (implode "if")
            [num_to_display n; data_prog_to_display k ns x;
              data_prog_to_display k ns y] | dataLang_MakeSpace n ns ->
              displayLang_Item NONE (implode "make_space")
            [num_to_display n; num_set_to_display ns] | Raise n
              -> displayLang_Item NONE (implode "raise")
              [num_to_display n] | Return ns -> displayLang_Item NONE
              (implode "return") [(\f xs. displayLang_Tuple (MAP f
              xs)) num_to_display ns] | Tick -> empty_item (implode
              "tick"))`;
   `data_prog_to_display_list k ns [] = []`;
   `data_prog_to_display_list k ns (x :: xs) =
        (match k with
          0 -> [] | SUC k ->
        data_prog_to_display k ns x :: data_prog_to_display_list
          k ns xs)`];;

let data_fun_to_display_def = cake_define
  `data_fun_to_display names (n,argc,body) =
     Tuple [String (implode "func");
            String (attach_name names (SOME n));
            Tuple (GENLIST num_to_display argc);
            data_prog_to_display 1000000000 names body]`;;

(* asm *)

let asm_binop_to_display_def = cake_define
  `asm_binop_to_display op = (match op with asm_Add -> empty_item
  (implode "Add") | Sub -> empty_item (implode "Sub") | And ->
  empty_item (implode "And") | Or -> empty_item (implode "Or") | Xor
  -> empty_item (implode "Xor"))`;;

let asm_reg_imm_to_display_def = cake_define
  `asm_reg_imm_to_display reg_imm' = (match reg_imm' with Reg reg ->
  item_with_num (implode "Reg") reg | Imm imm -> item_with_word
  (implode "Imm") imm)`;;

let asm_arith_to_display_def = cake_define
  `asm_arith_to_display op = (match op with asm_Binop bop n1 n2 reg_imm'
  -> displayLang_Item NONE (implode "Binop")
         [asm_binop_to_display bop; num_to_display n1; num_to_display
           n2;
             asm_reg_imm_to_display reg_imm'] | asm_Shift sh n1 n2 n3
               -> displayLang_Item NONE (implode "Shift")
         [shift_to_display sh;
          num_to_display n1;
          num_to_display n2;
          asm_reg_imm_to_display n3] | Div n1 n2 n3 ->
            item_with_nums (implode "Div") [n1; n2; n3] | asm_LongMul
            n1 n2 n3 n4 -> item_with_nums (implode "LongMul") [n1;
            n2; n3; n4] | asm_LongDiv n1 n2 n3 n4 n5 ->
            item_with_nums (implode "LongDiv") [n1; n2; n3; n4; n5] |
            asm_AddCarry n1 n2 n3 n4 -> item_with_nums (implode
            "AddCarry") [n1; n2; n3; n4] | asm_AddOverflow n1 n2 n3
            n4 -> item_with_nums (implode "AddOverflow") [n1; n2; n3;
            n4] | asm_SubOverflow n1 n2 n3 n4 -> item_with_nums
            (implode "SubOverflow") [n1; n2; n3; n4])`;;

let asm_addr_to_display_def = cake_define
  `asm_addr_to_display addr' = (match addr' with Addr reg w ->
  displayLang_Item NONE (implode "Addr")
                          [num_to_display reg; word_to_display w])`;;

let asm_memop_to_display_def = cake_define
  `asm_memop_to_display op = (match op with Load -> empty_item
  (implode "Load") | asm_Load8 -> empty_item (implode "Load8") |
  asm_Load16 -> empty_item (implode "Load16") | asm_Load32 ->
  empty_item (implode "Load32") | Store -> empty_item (implode
  "Store") | asm_Store8 -> empty_item (implode "Store8") |
  asm_Store16 -> empty_item (implode "Store16") | asm_Store32 ->
  empty_item (implode "Store32"))`;;

let asm_cmp_to_display_def = cake_define
  `asm_cmp_to_display op = (match op with Equal -> empty_item
  (implode "Equal") | asm_Lower -> empty_item (implode "Lower") |
  Less -> empty_item (implode "Less") | Test -> empty_item (implode
  "Test") | asm_NotEqual -> empty_item (implode "NotEqual") |
  asm_NotLower -> empty_item (implode "NotLower") | asm_NotLess ->
  empty_item (implode "NotLess") | asm_NotTest -> empty_item (implode
  "NotTest"))`;;

let asm_fp_to_display_def = cake_define
  `asm_fp_to_display op = (match op with FPLess n1 n2 n3 ->
  item_with_nums (implode "FPLess") [n1; n2; n3] | FPLessEqual n1 n2
  n3 -> item_with_nums (implode "FPLessEqual") [n1; n2; n3] | FPEqual
  n1 n2 n3 -> item_with_nums (implode "FPEqual") [n1; n2; n3] | FPAbs
  n1 n2 -> item_with_nums (implode "FPAbs") [n1; n2] | FPNeg n1 n2 ->
  item_with_nums (implode "FPNeg") [n1; n2] | FPSqrt n1 n2 ->
  item_with_nums (implode "FPSqrt") [n1; n2] | FPAdd n1 n2 n3 ->
  item_with_nums (implode "FPAdd") [n1; n2; n3] | FPSub n1 n2 n3 ->
  item_with_nums (implode "FPSub") [n1; n2; n3] | FPMul n1 n2 n3 ->
  item_with_nums (implode "FPMul") [n1; n2; n3] | FPDiv n1 n2 n3 ->
  item_with_nums (implode "FPDiv") [n1; n2; n3] | FPFma n1 n2 n3 ->
  item_with_nums (implode "FPFma") [n1; n2; n3] | FPMov n1 n2 ->
  item_with_nums (implode "FPMov") [n1; n2] | FPMovToReg n1 n2 n3 ->
  item_with_nums (implode "FPMovToReg") [n1; n2; n3] | FPMovFromReg
  n1 n2 n3 -> item_with_nums (implode "FPMovFromReg") [n1; n2; n3] |
  FPToInt n1 n2 -> item_with_nums (implode "FPToInt") [n1; n2] |
  FPFromInt n1 n2 -> item_with_nums (implode "FPFromInt") [n1; n2])`;;

let asm_inst_to_display_def = cake_define
  `asm_inst_to_display inst' = (match inst' with asm_Skip -> empty_item
  (implode "Skip") | Const reg w -> displayLang_Item NONE (implode
  "Const") [num_to_display reg;
                              word_to_display w] | Arith a ->
                                displayLang_Item NONE (implode "Arith")
                                [asm_arith_to_display a] | asm_Mem mop r
                                addr' -> displayLang_Item NONE (implode
                                "Mem") [asm_memop_to_display mop;
         num_to_display r; asm_addr_to_display addr'] | asm_FP fp
           -> displayLang_Item NONE (implode "FP") [asm_fp_to_display
           fp])`;;

let asm_asm_to_display_def = cake_define
  `asm_asm_to_display inst' = (match inst' with Inst i ->
  asm_inst_to_display i | Jump w -> item_with_word (implode "Jump") w |
  JumpCmp c r to w -> displayLang_Item NONE (implode "JumpCmp")
       [asm_cmp_to_display c; num_to_display r;
         asm_reg_imm_to_display to;
        word_to_display w] | Call w -> item_with_word (implode
          "Call") w | asm_JumpReg r -> item_with_num (implode
          "JumpReg>") r | Loc r w -> displayLang_Item NONE (implode
          "Loc") [num_to_display r; word_to_display w])`;;

(* stackLang *)

let store_name_to_display_def = cake_define
  `store_name_to_display st = (match st with NextFree -> empty_item
  (implode "NextFree") | EndOfHeap -> empty_item (implode
  "EndOfHeap") | TriggerGC -> empty_item (implode "TriggerGC") |
  HeapLength -> empty_item (implode "HeapLength") | ProgStart ->
  empty_item (implode "ProgStart") | BitmapBase -> empty_item
  (implode "BitmapBase") | CurrHeap -> empty_item (implode
  "CurrHeap") | OtherHeap -> empty_item (implode "OtherHeap") |
  AllocSize -> empty_item (implode "AllocSize") | Globals ->
  empty_item (implode "Globals") | GlobReal -> empty_item (implode
  "GlobReal") | Handler -> empty_item (implode "Handler") | GenStart
  -> empty_item (implode "GenStart") | CodeBuffer -> empty_item
  (implode "CodeBuffer") | CodeBufferEnd -> empty_item (implode
  "CodeBufferEnd") | BitmapBuffer -> empty_item (implode
  "BitmapBuffer") | BitmapBufferEnd -> empty_item (implode
  "BitmapBufferEnd") | Temp w -> item_with_word (implode "Temp") w)`;;

let stack_seqs_def = cake_define
  `stack_seqs z =
     (match z with stackLang_Seq x y -> Append (stack_seqs x)
       (stack_seqs y) | _9 -> List [z])`;;

let stack_prog_to_display_def = cake_define_list
  [`stack_prog_to_display 0 ns prog = empty_item (implode "...")`;
   `stack_prog_to_display (SUC k) ns stackLang_Skip = empty_item
  (implode "skip")`;
   `stack_prog_to_display (SUC k) ns (Inst i:labLang_prog) =
  asm_inst_to_display i`;
   `stack_prog_to_display (SUC k) ns (Get n sn:labLang_prog) = Tuple
      [num_to_display n; String (implode "<-");
        store_name_to_display sn]`;
   `stack_prog_to_display (SUC k) ns (Set sn n:labLang_prog) = Tuple
      [store_name_to_display sn; String (implode "<-");
        num_to_display n]`;
   `stack_prog_to_display (SUC k) ns (OpCurrHeap b n1 n2:labLang_prog) =
  Tuple
      [num_to_display n1; String (implode ":="); String (implode
        "CurrHeap");
       asm_binop_to_display b; num_to_display n2]`;
   `stack_prog_to_display (SUC k) ns (Call rh tgt eh:labLang_prog) =
      displayLang_Item NONE (implode "call")
           [(match rh with NONE -> empty_item (implode "tail") |
             SOME (p,lr,l1,l2) ->
                 displayLang_Item NONE (implode "returning")
                      [num_to_display lr;
                       String (attach_name ns (SOME l1));
                       num_to_display l2;
                       stack_prog_to_display k ns p]);
           (match tgt with INL l -> displayLang_Item NONE (implode
             "direct") [String (attach_name ns (SOME l))] | INR r ->
             item_with_num (implode "reg") r);
           (match eh with NONE -> empty_item (implode "no_handler")
             | SOME (p,l1,l2) ->
                displayLang_Item NONE (implode "handler")
                     [String (attach_name ns (SOME l1));
                      num_to_display l2;
                      stack_prog_to_display k ns p])]`;
   `stack_prog_to_display (SUC k) ns (Seq x y:labLang_prog) =
         (let xs = append (Append (stack_seqs x) (stack_seqs y)) in
            separate_lines (implode "seq")
              (stack_prog_to_display_list k ns xs))`;
   `stack_prog_to_display (SUC k) ns (If c n to x y:labLang_prog) =
  displayLang_Item NONE (implode "if")
         [Tuple [asm_cmp_to_display c; num_to_display n;
           asm_reg_imm_to_display to];
          stack_prog_to_display k ns x;
          stack_prog_to_display k ns y]`;
   `stack_prog_to_display (SUC k) ns (Loop x:labLang_prog) =
  displayLang_Item NONE (implode "loop")
         [stack_prog_to_display k ns x]`;
   `stack_prog_to_display (SUC k) ns (stackLang_JumpLower n1 n2 n3) =
      item_with_nums (implode "jump_lower") [n1; n2; n3]`;
   `stack_prog_to_display (SUC k) ns (Alloc n:labLang_prog) =
  item_with_num (implode "alloc") n`;
   `stack_prog_to_display (SUC k) ns (StoreConsts n1 n2
  _10:labLang_prog) = item_with_nums (implode "store_consts") [n1;
  n2]`;
   `stack_prog_to_display (SUC k) ns (Raise n:labLang_prog) =
  item_with_num (implode "raise") n`;
   `stack_prog_to_display (SUC k) ns (Return n:labLang_prog) =
  item_with_num (implode "return") n`;
   `stack_prog_to_display (SUC k) ns (Break n:labLang_prog) =
  item_with_num (implode "break") n`;
   `stack_prog_to_display (SUC k) ns (Continue n:labLang_prog) =
  item_with_num (implode "continue") n`;
   `stack_prog_to_display (SUC k) ns (FFI nm cp cl ap al
  ra:labLang_prog) = displayLang_Item NONE (implode "ffi")
         (string_imp nm :: MAP num_to_display [cp; cl; ap; al;
           ra])`;
   `stack_prog_to_display (SUC k) ns Tick = empty_item (implode
  "tick")`;
   `stack_prog_to_display (SUC k) ns (LocValue n1 n2 n3:labLang_prog) =
      displayLang_Item NONE (implode "loc_value") [num_to_display
        n1;
                             String (attach_name ns (SOME n2));
                             num_to_display n3]`;
   `stack_prog_to_display (SUC k) ns (Install n1 n2 n3 n4
  n5:labLang_prog) =
      item_with_nums (implode "install") [n1; n2; n3; n4; n5]`;
   `stack_prog_to_display (SUC k) ns (stackLang_ShMemOp mop r a) =
      displayLang_Item NONE (implode "sh_mem") [asm_memop_to_display
        mop;
                              num_to_display r;
                                asm_addr_to_display a]`;
   `stack_prog_to_display (SUC k) ns (CodeBufferWrite n1
  n2:labLang_prog) =
      item_with_nums (implode "code_buffer_write") [n1; n2]`;
   `stack_prog_to_display (SUC k) ns (DataBufferWrite n1
  n2:labLang_prog) =
      item_with_nums (implode "data_buffer_write") [n1; n2]`;
   `stack_prog_to_display (SUC k) ns (stackLang_RawCall n) =
      displayLang_Item NONE (implode "raw_call") [String
        (attach_name ns (SOME n))]`;
   `stack_prog_to_display (SUC k) ns (stackLang_StackAlloc n) =
  item_with_num (implode "stack_alloc") n`;
   `stack_prog_to_display (SUC k) ns (stackLang_StackFree n) =
  item_with_num (implode "stack_free") n`;
   `stack_prog_to_display (SUC k) ns (stackLang_StackStore n m) =
      Tuple [String ((\x y. strcat x y) ((\x y. strcat x y) ((\x
        y. strcat x y) (implode "stack[") (num_to_hex_mlstring n))
        (implode "] := ")) (toString m))]`;
   `stack_prog_to_display (SUC k) ns (stackLang_StackStoreAny n m) =
      Tuple [String ((\x y. strcat x y) ((\x y. strcat x y) ((\x
        y. strcat x y) (implode "stack[var ") (toString n)) (implode
        "] := ")) (toString m))]`;
   `stack_prog_to_display (SUC k) ns (stackLang_StackLoad n m) =
      Tuple [String (mlstring_concat [toString n;
                             (implode " := stack[");
                             num_to_hex_mlstring m; (implode
                               "]")])]`;
   `stack_prog_to_display (SUC k) ns (stackLang_StackLoadAny n m) =
      Tuple [String (mlstring_concat [toString n;
                             (implode " := stack[var ");
                             toString m; (implode "]")])]`;
   `stack_prog_to_display (SUC k) ns (stackLang_StackGetSize n) =
  item_with_num (implode "stack_get_size") n`;
   `stack_prog_to_display (SUC k) ns (stackLang_StackSetSize n) =
  item_with_num (implode "stack_set_size") n`;
   `stack_prog_to_display (SUC k) ns (stackLang_BitmapLoad n m) =
      Tuple [String (mlstring_concat [toString n;
                             (implode " := bitmap[");
                             num_to_hex_mlstring m;
                             (implode "]")])]`;
   `stack_prog_to_display (SUC k) ns (Halt n:labLang_prog) =
  item_with_num (implode "halt") n`;
   `stack_prog_to_display_list k ns [] = []`;
   `stack_prog_to_display_list k ns (x :: xs) =
        (match k with 0 -> [] | SUC k ->
        stack_prog_to_display k ns x ::
          stack_prog_to_display_list k ns xs)`];;

let stack_fun_to_display_def = cake_define
  `stack_fun_to_display names (n,body) =
     Tuple [String (implode "func");
            String (attach_name names (SOME n));
            stack_prog_to_display 1000000000 names body]`;;

(* labLang *)

let lab_asm_to_display_def = cake_define
  `lab_asm_to_display ns la = (match la with labLang_Jump (labLang_Lab s
  n) ->
         displayLang_Item NONE (implode "jump")
           [String (attach_name ns (SOME s)); num_to_display n] |
             JumpCmp c r ri (labLang_Lab s n) ->
         displayLang_Item NONE (implode "jump_cmp")
           [Tuple [asm_cmp_to_display c; num_to_display r;
                   asm_reg_imm_to_display ri];
            String (attach_name ns (SOME s)); num_to_display n] |
              Call (labLang_Lab s n) ->
         displayLang_Item NONE (implode "call")
           [String (attach_name ns (SOME s)); num_to_display n] |
             LocValue r (labLang_Lab s n) ->
         displayLang_Item NONE (implode "loc_value")
           [num_to_display r; String (attach_name ns (SOME s));
             num_to_display n] | labLang_CallFFI name ->
             displayLang_Item NONE (implode "call_FFI") [string_imp
             name] | Install -> empty_item (implode "install") | Halt
             -> empty_item (implode "halt"))`;;

let lab_line_to_display_def = cake_define
  `lab_line_to_display ns line = (match line with Label s n le ->
         displayLang_Item NONE (implode "label") [String (attach_name
           ns (SOME s)); num_to_display n] | labLang_Asm aoc enc len ->
           (match aoc with Asmi i -> displayLang_Item NONE (implode
           "asm") [asm_asm_to_display i] | Cbw r1 r2 -> item_with_nums
           (implode "cbw") [r1; r2] | ShareMem mop r a ->
           displayLang_Item NONE (implode "share_mem")
           [asm_memop_to_display mop;
                              num_to_display r;
                              asm_addr_to_display a]) |
                                labLang_LabAsm la pos enc len ->
                                lab_asm_to_display ns la)`;;

let lab_fun_to_display_def = cake_define
  `lab_fun_to_display names (Section n lines) =
     List (
            String (attach_name names (SOME n)) :: MAP
              (lab_line_to_display names) lines)`;;

(* wordLang *)

let word_seqs_def = cake_define
  `word_seqs z =
     (match z with wordLang_Seq x y -> Append (word_seqs x)
       (word_seqs y) | _11 -> List [z])`;;

let word_exp_to_display_def = cake_define_list
  [`word_exp_to_display (wordLang_Const v) = item_with_word (implode
  "Const") v`;
   `word_exp_to_display (Var n:flatLang_exp) = item_with_num (implode
  "Var") n`;
   `word_exp_to_display (wordLang_Lookup st) = displayLang_Item NONE
  (implode "Lookup") [store_name_to_display st]`;
   `word_exp_to_display (Load exp2:flatLang_exp) = displayLang_Item
  NONE (implode "MemLoad") [word_exp_to_display exp2]`;
   `word_exp_to_display (Op bop exs:flatLang_exp) = displayLang_Item
  NONE (implode "Op") (
        asm_binop_to_display bop :: word_exp_to_display_list exs)`;
   `word_exp_to_display (Shift sh exp exp1:flatLang_exp) =
  displayLang_Item NONE (implode "Shift") [
      shift_to_display sh;
      word_exp_to_display exp;
      word_exp_to_display exp1]`;
   `word_exp_to_display_list [] = []`;
   `word_exp_to_display_list (x :: xs) =
        word_exp_to_display x :: word_exp_to_display_list xs`];;

let ws_to_display_def = cake_define_list
  [`ws_to_display [] = []`;
   `ws_to_display ((b,x) :: xs) =
      Tuple [bool_to_display b; word_to_display x] ::
        ws_to_display xs`];;

let num_sets_to_display_def = cake_define
  `num_sets_to_display (l,r) =
     Tuple [num_set_to_display l;
            num_set_to_display r]`;;

let word_prog_to_display_def = cake_define_list
  [`word_prog_to_display 0 ns x = empty_item (implode "...")`;
   `word_prog_to_display (SUC k) ns Skip = empty_item (implode
  "skip")`;
   `word_prog_to_display (SUC k) ns (Move n mvs:labLang_prog) =
  displayLang_Item NONE (implode "move")
        [num_to_display n; displayLang_Tuple (MAP (\(n1,n2). Tuple
            [num_to_display n1;
             String (implode ":=");
             num_to_display n2]) mvs)]`;
   `word_prog_to_display (SUC k) ns (Inst i:labLang_prog) =
        displayLang_Item NONE (implode "inst")
          [asm_inst_to_display i]`;
   `word_prog_to_display (SUC k) ns (Assign n exp:labLang_prog) =
         Tuple [num_to_display n;
                String (implode ":=");
                word_exp_to_display exp]`;
   `word_prog_to_display (SUC k) ns (Get n sn:labLang_prog) = Tuple
        [num_to_display n; String (implode "<-");
          store_name_to_display sn]`;
   `word_prog_to_display (SUC k) ns (Set sn exp:labLang_prog) = Tuple
        [store_name_to_display sn; String (implode "<-");
          word_exp_to_display exp]`;
   `word_prog_to_display (SUC k) ns (Store exp n:labLang_prog) = Tuple
        [String (implode "mem"); word_exp_to_display exp;
         String (implode ":="); num_to_display n]`;
   `word_prog_to_display (SUC k) ns (wordLang_ShareInst mop n exp) =
  Tuple
        [String (implode "share_mem"); asm_memop_to_display mop;
         num_to_display n; word_exp_to_display exp]`;
   `word_prog_to_display (SUC k) ns (wordLang_MustTerminate prog) =
  displayLang_Item NONE (implode "must_terminate")
        [word_prog_to_display k ns prog]`;
   `word_prog_to_display (SUC k) ns (Call a b c d:labLang_prog) =
  displayLang_Item NONE (implode "call")
        [word_prog_to_display_ret k ns a;
         (\f opt. match opt with NONE -> empty_item (implode "none")
           | SOME opt' -> displayLang_Item NONE (implode "some") [f
           opt']) (\n. String (attach_name ns (SOME n))) b;
         (\f xs. displayLang_Tuple (MAP f xs)) num_to_display c;
         word_prog_to_display_handler k ns d]`;
   `word_prog_to_display (SUC k) ns (OpCurrHeap b n1 n2:labLang_prog) =
  Tuple
        [num_to_display n1; String (implode ":="); String (implode
          "CurrHeap");
         asm_binop_to_display b; num_to_display n2]`;
   `word_prog_to_display (SUC k) ns (Seq prog1 prog2:labLang_prog) =
        (let xs = append (Append (word_seqs prog1) (word_seqs
          prog2)) in
           separate_lines (implode "seq")
             (word_prog_to_display_list k ns xs))`;
   `word_prog_to_display (SUC k) ns (If cmp n reg p1 p2:labLang_prog) =
        displayLang_Item NONE (implode "if")
          [Tuple [asm_cmp_to_display cmp;
                  num_to_display n;
                  asm_reg_imm_to_display reg];
           word_prog_to_display k ns p1; word_prog_to_display k
             ns p2]`;
   `word_prog_to_display (SUC k) ns (Loop ns1 p ns2:labLang_prog) =
        displayLang_Item NONE (implode "Loop")
          [num_set_to_display ns1;
           word_prog_to_display k ns p;
           num_set_to_display ns2]`;
   `word_prog_to_display (SUC k) ns (Alloc n ms:labLang_prog) =
  displayLang_Item NONE (implode "alloc")
        [num_to_display n; num_sets_to_display ms]`;
   `word_prog_to_display (SUC k) ns (StoreConsts a b c d
  ws:labLang_prog) = displayLang_Item NONE (implode "store_consts")
        [num_to_display a;
         num_to_display b;
         num_to_display c;
         num_to_display d;
         Tuple (ws_to_display ws)]`;
   `word_prog_to_display (SUC k) ns (Raise n:labLang_prog) =
  item_with_num (implode "raise") n`;
   `word_prog_to_display (SUC k) ns (Break n:labLang_prog) =
  item_with_num (implode "break") n`;
   `word_prog_to_display (SUC k) ns (Continue n:labLang_prog) =
  item_with_num (implode "continue") n`;
   `word_prog_to_display (SUC k) ns (Return n vs:labLang_prog) =
         displayLang_Item NONE (implode "return")
           [num_to_display n;
            Tuple (MAP num_to_display vs)]`;
   `word_prog_to_display (SUC k) ns Tick = empty_item (implode
  "tick")`;
   `word_prog_to_display (SUC k) ns (LocValue n1 n2:labLang_prog) =
        displayLang_Item NONE (implode "loc_value") [String
          (attach_name ns (SOME n1)); num_to_display n2]`;
   `word_prog_to_display (SUC k) ns (Install n1 n2 n3 n4
  ms:labLang_prog) =
        displayLang_Item NONE (implode "install") (
            MAP num_to_display [n1; n2; n3; n4] ++
              [num_sets_to_display ms])`;
   `word_prog_to_display (SUC k) ns (CodeBufferWrite n1 n2:labLang_prog)
  =
        item_with_nums (implode "code_buffer_write") [n1; n2]`;
   `word_prog_to_display (SUC k) ns (DataBufferWrite n1 n2:labLang_prog)
  =
        item_with_nums (implode "data_buffer_write") [n1; n2]`;
   `word_prog_to_display (SUC k) ns (FFI nm n1 n2 n3 n4 ms:labLang_prog)
  =
        displayLang_Item NONE (implode "ffi") (
            (string_imp nm :: MAP num_to_display [n1; n2; n3;
              n4]) ++ [num_sets_to_display ms])`;
   `word_prog_to_display_list k ns [] = []`;
   `word_prog_to_display_list k ns (x :: xs) =
        (match k with 0 -> [] | SUC k ->
        word_prog_to_display k ns x :: word_prog_to_display_list
          k ns xs)`;
   `word_prog_to_display_ret k ns NONE = empty_item (implode "tail")`;
   `word_prog_to_display_ret k ns (SOME (vs,ms,prog,n2,n3)) =
        (match k with 0 -> empty_item (implode "...") | SUC k ->
        displayLang_Item NONE (implode "returning") [Tuple [Tuple
          (MAP num_to_display vs); num_sets_to_display ms;
            word_prog_to_display k ns prog;
            String (attach_name ns (SOME n2));
            num_to_display n3]])`;
   `word_prog_to_display_handler k ns NONE = empty_item (implode
  "no_handler")`;
   `word_prog_to_display_handler k ns (SOME (n1,prog,n2,n3)) =
        (match k with 0 -> empty_item (implode "...") | SUC k ->
        displayLang_Item NONE (implode "handler") [Tuple
          [num_to_display n1;
            word_prog_to_display k ns prog;
            String (attach_name ns (SOME n2));
            num_to_display n3]])`];;

let word_fun_to_display_def = cake_define
  `word_fun_to_display names (n,argc,body) =
     Tuple [String (implode "func");
            String (attach_name names (SOME n));
            Tuple (GENLIST (\n. num_to_display (2 * n)) argc);
            word_prog_to_display 1000000000 names body]`;;

(* tap configuration *)

let tap_config_FIELDS = define_record "tap_config"
  ["explore_flag","bool"];;

let default_tap_config_def = cake_define
  `default_tap_config = mk_tap_config F`;;

(* ------------------------- *)

let map_to_append_def = cake_define_list
  [`map_to_append f [] = misc_Nil`;
   `map_to_append f (x :: xs) = Append (List (f x)) (map_to_append f
  xs)`];;

let source_to_strs_def = cake_define
  `source_to_strs decs =
     map_to_append (str_tree_to_strs (implode "\n\n") o
                    display_to_str_tree o
                    source_to_display_dec) decs`;;

let flat_to_strs_def = cake_define
  `flat_to_strs (decs:flatLang_exp list) =
     map_to_append (str_tree_to_strs (implode "\n\n") o
                    display_to_str_tree o
                    flat_to_display) decs`;;

let clos_to_strs_def = cake_define
  `clos_to_strs (decs,funs) =
     (let names = get_src_names (decs ++ MAP (SND o SND) funs) LN in
       Append (map_to_append (str_tree_to_strs (implode "\n\n") o
                              display_to_str_tree o
                              clos_dec_to_display names) decs)
              (map_to_append (str_tree_to_strs (implode "\n\n") o
                              display_to_str_tree o
                              clos_fun_to_display names) funs))`;;

let bvl_to_strs_def = cake_define
  `bvl_to_strs names xs =
     map_to_append (str_tree_to_strs (implode "\n\n") o
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
     map_to_append (str_tree_to_strs (implode "\n\n") o
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
     map_to_append (str_tree_to_strs (implode "\n\n") o
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
     map_to_append (str_tree_to_strs (implode "\n\n") o
                    display_to_str_tree o
                    word_fun_to_display names) xs`;;

let stack_to_strs_def = cake_define
  `stack_to_strs names xs =
     map_to_append (str_tree_to_strs (implode "\n\n") o
                    display_to_str_tree o
                    stack_fun_to_display names) xs`;;

let lab_to_strs_def = cake_define
  `lab_to_strs names xs =
     map_to_append (str_tree_to_strs (implode "\n\n") o
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
