(* ======================================================== *)
(*  presLang: ported from HOL4's
    compiler/backend/presLangScript.sml
    A definition theory, with 91 definitions, 1 datatype and 15
    theorems.  Needed by 8 files of the port.  *)
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
needs "lib/ASCIInumbers.ml";;
needs "lib/binary_ieee.ml";;
needs "lib/comparison.ml";;
needs "lib/errorMonad.ml";;
needs "lib/peg.ml";;
needs "lib/sptree.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/fpSem.ml";;
needs "semantics/namespace.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "presLang"
  ["ast"; "bvi"; "bvl"; "closLang"; "clos_to_bvl"; "dataLang";
   "displayLang"; "flatLang"; "labLang"; "mlint"; "mloption";
   "source_to_flat"; "stackLang"; "wordLang"];;

(* basics *)

let empty_item_def = new_definition
  `empty_item name = displayLang_String name`;;

let num_to_display_def = new_definition
  `num_to_display (n:num) = displayLang_String (mlint_toString n)`;;

let int_to_display_def = new_definition
  `int_to_display (i:int) = displayLang_String (mlint_toString i)`;;

let string_imp_def = new_definition
  `string_imp s = displayLang_String s`;;

let item_with_num_def = new_definition
  `item_with_num name n = displayLang_Item NONE name [num_to_display
  n]`;;

let item_with_nums_def = new_definition
  `item_with_nums name ns = displayLang_Item NONE name (MAP
  num_to_display ns)`;;

let bool_to_display_def = new_definition
  `bool_to_display b = empty_item (if b then (implode "True") else
  (implode "False"))`;;

let num_to_hex_def,num_to_hex_ind = assume_definition_rec
  "termination (CHEAT_TAC)"
  [`num_to_hex n = APPEND (if n < 16 then [] else num_to_hex (n DIV 16))
     (num_to_hex_digit (n MOD 16))`];;

let separate_lines_def = new_definition
  `separate_lines name xs = displayLang_List (CONS
  (displayLang_String name) xs)`;;

(* num_to_hex "implements" words$word_to_hex_string in a
   simple way that the translator can handle. these lemmas
   check that is true. *)
let num_to_hex_digit_eq = prove
 (`!i. i < 16 ==> num_to_hex_digit i = [HEX i]`,
  CHEAT_TAC);;

let num_to_hex_eq = prove
 (`num_to_hex (w2n w) = word_to_hex_string w`,
  CHEAT_TAC);;

let num_to_hex_mlstring_def = new_definition
  `num_to_hex_mlstring n = implode (APPEND "0x" (num_to_hex n))`;;

let word_to_display_def = new_definition
  `word_to_display w = empty_item (num_to_hex_mlstring (w2n w))`;;

let item_with_word_def = new_definition
  `item_with_word name w = displayLang_Item NONE name
  [word_to_display w]`;;

let lit_to_display_def = define_cases
  [`lit_to_display (ast_IntLit i) =
        displayLang_Item NONE (implode "IntLit") [empty_item
            (mlint_toString i)]`;
   `lit_to_display (ast_Char c) =
        displayLang_Item NONE (implode "Char") [empty_item
            (implode (APPEND (APPEND "#\"" [c]) "\""))]`;
   `lit_to_display (ast_StrLit s) =
        displayLang_Item NONE (implode "StrLit") [string_imp s]`;
   `lit_to_display (ast_Word8 w) =
        displayLang_Item NONE (implode "Word8") [word_to_display
            w]`;
   `lit_to_display (ast_Word64 w:lit) =
        displayLang_Item NONE (implode "Word64") [word_to_display
            w]`;
   `lit_to_display (ast_Float64 w) =
        displayLang_Item NONE (implode "Float64")
            [word_to_display w]`];;

(* HOL4 presLangScript.sml:105: the overload list_to_display, which
   the port expands *)

(* HOL4 presLangScript.sml:107-110: the overload option_to_display,
   which the port expands *)
(* source *)

let fp_cmp_to_display_def = new_definition
  `fp_cmp_to_display cmp = (match cmp with FP_Less -> empty_item
  (implode "FP_Less") | FP_LessEqual -> empty_item (implode
  "FP_LessEqual") | FP_Greater -> empty_item (implode "FP_Greater") |
  FP_GreaterEqual -> empty_item (implode "FP_GreaterEqual") |
  FP_Equal -> empty_item (implode "FP_Equal"))`;;

let fp_uop_to_display_def = new_definition
  `fp_uop_to_display op = (match op with fpSem_FP_Abs -> empty_item
  (implode "FP_Abs") | fpSem_FP_Neg -> empty_item (implode "FP_Neg")
  | fpSem_FP_Sqrt -> empty_item (implode "FP_Sqrt"))`;;

let fp_bop_to_display_def = new_definition
  `fp_bop_to_display op = (match op with fpSem_FP_Add -> empty_item
  (implode "FP_Add") | fpSem_FP_Sub -> empty_item (implode "FP_Sub")
  | fpSem_FP_Mul -> empty_item (implode "FP_Mul") | fpSem_FP_Div ->
  empty_item (implode "FP_Div"))`;;

let fp_top_to_display_def = new_definition
  `fp_top_to_display op =
     (match op with FP_Fma -> empty_item (implode "FP_Fma"))`;;

let word_size_to_display_def = define_cases
  [`word_size_to_display ast_W8 = empty_item (implode "W8")`;
   `word_size_to_display (ast_W64:word_size) = empty_item (implode
    "W64")`];;

let opb_to_display_def = define_cases
  [`opb_to_display (ast_Lt:opb) = empty_item (implode "Lt")`;
   `opb_to_display ast_Gt = empty_item (implode "Gt")`;
   `opb_to_display ast_Leq = empty_item (implode "Leq")`;
   `opb_to_display ast_Geq = empty_item (implode "Geq")`];;

let opw_to_display_def = define_cases
  [`opw_to_display backend_common_Andw = empty_item (implode "Andw")`;
   `opw_to_display backend_common_Orw = empty_item (implode "Orw")`;
   `opw_to_display (backend_common_Xor:opw) = empty_item (implode
    "Xor")`;
   `opw_to_display (backend_common_Add:opw) = empty_item (implode
    "Add")`;
   `opw_to_display (backend_common_Sub:opw) = empty_item (implode
    "Sub")`];;

let shift_to_display_def = define_cases
  [`shift_to_display Lsl = empty_item (implode "Lsl")`;
   `shift_to_display Lsr = empty_item (implode "Lsr")`;
   `shift_to_display Asr = empty_item (implode "Asr")`;
   `shift_to_display Ror = empty_item (implode "Ror")`];;

let thunk_mode_to_display_def = define_cases
  [`thunk_mode_to_display Evaluated = empty_item (implode
    "Evaluated")`;
   `thunk_mode_to_display NotEvaluated = empty_item (implode
    "NotEvaluated")`];;

let thunk_op_to_display_def = define_cases
  [`thunk_op_to_display (AllocThunk m) =
        displayLang_Item NONE (implode "AllocThunk")
            [thunk_mode_to_display m]`;
   `thunk_op_to_display (UpdateThunk m) =
        displayLang_Item NONE (implode "UpdateThunk")
            [thunk_mode_to_display m]`;
   `thunk_op_to_display ForceThunk = empty_item (implode
    "ForceThunk")`];;

let test_to_display_def = define_cases
  [`test_to_display (ast_Equal:test) = empty_item (implode "Equal")`;
   `test_to_display (ast_Compare cmp) = displayLang_Item NONE
    (implode "Compare") [opb_to_display cmp]`;
   `test_to_display (ast_AltCompare cmp) = displayLang_Item NONE
    (implode "AltCompare") [opb_to_display cmp]`];;

let arith_to_display_def = define_cases
  [`arith_to_display (ast_Add:ast_arith) = empty_item (implode "Add")`;
   `arith_to_display (ast_Sub:ast_arith) = empty_item (implode "Sub")`;
   `arith_to_display (ast_Mul:ast_arith) = empty_item (implode "Mul")`;
   `arith_to_display (ast_Div:ast_arith) = empty_item (implode "Div")`;
   `arith_to_display (ast_Mod:ast_arith) = empty_item (implode "Mod")`;
   `arith_to_display (ast_And:ast_arith) = empty_item (implode "And")`;
   `arith_to_display (ast_Xor:ast_arith) = empty_item (implode "Xor")`;
   `arith_to_display (ast_Or:ast_arith) = empty_item (implode "Or")`;
   `arith_to_display ast_Neg = empty_item (implode "Neg")`;
   `arith_to_display (ast_Not:ast_arith) = empty_item (implode "Not")`;
   `arith_to_display ast_Abs = empty_item (implode "Abs")`;
   `arith_to_display ast_Sqrt = empty_item (implode "Sqrt")`;
   `arith_to_display ast_FMA = empty_item (implode "FMA")`];;

let prim_type_to_display_def = new_definition
  `prim_type_to_display x1 =
      match x1 with
        ast_BoolT -> empty_item (implode "BoolT")
      | ast_IntT -> empty_item (implode "IntT")
      | ast_CharT -> empty_item (implode "CharT")
      | ast_StrT -> empty_item (implode "StrT")
      | ast_Float64T -> empty_item (implode "Float64T")
      | (ast_WordT ast_W8) -> empty_item (implode "WordT_W8")
      | (ast_WordT ast_W64) -> empty_item (implode "WordT_W64")`;;

let lop_to_display_def = define_cases
  [`lop_to_display Andalso = empty_item (implode "Andalso")`;
   `lop_to_display Orelse = empty_item (implode "Orelse")`];;

let op_to_display_def = new_definition
  `op_to_display (p:ast_op) =
   (match p with ast_Shift ws sh num' -> displayLang_Item NONE
     (implode "Shift")
                             [word_size_to_display ws;
                              shift_to_display sh;
                              num_to_display num'] | ast_Arith a ty
                                -> displayLang_Item NONE (implode
                                "Arith")
                          [arith_to_display a;
                           prim_type_to_display ty] | ast_FromTo ty1
                             ty2 -> displayLang_Item NONE (implode
                             "FromTo")
                          [prim_type_to_display ty1;
                           prim_type_to_display ty2] | ast_Test test
                             ty -> displayLang_Item NONE (implode
                             "Test")
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
                             ast_ListAppend -> empty_item (implode
                             "ListAppend") | ast_ConfigGC ->
                             empty_item (implode "ConfigGC") |
                             ast_FFI v35 -> empty_item (implode
                             "FFI v35") | ast_Eval -> empty_item
                             (implode "Eval") | ast_Env_id ->
                             empty_item (implode "Env_id") |
                             ast_ThunkOp t -> thunk_op_to_display t)`;;

let id_to_display_def,id_to_display_ind = define_rec
  [`id_to_display (Short n) =
      displayLang_Item NONE (implode "Short") [displayLang_String
          n]`;
   `id_to_display (Long n i) =
      displayLang_Item NONE (implode "Long")
          [displayLang_String n; id_to_display i]`];;

let ast_t_to_display_def,ast_t_to_display_ind = assume_definition_rec
  "termination (CHEAT_TAC)"
  [`ast_t_to_display c =
      (match c with Atvar n -> displayLang_Item NONE (implode
          "Atvar") [displayLang_String n] | Atfun t1 t2 ->
          displayLang_Item NONE (implode "Atfun") [ast_t_to_display t1;
          ast_t_to_display t2] | Attup ts -> displayLang_Item NONE
          (implode "Attup") [displayLang_Tuple (ast_t_to_display_list
          ts)] | Atapp ts id' -> displayLang_Item NONE (implode "Attup")
          [displayLang_Tuple (ast_t_to_display_list ts);
                              id_to_display id'])`;
   `ast_t_to_display_list [] = []`;
   `ast_t_to_display_list (CONS x xs) = CONS (ast_t_to_display x)
    (ast_t_to_display_list xs)`];;

let pat_to_display_def,pat_to_display_ind = assume_definition_rec
  "termination (CHEAT_TAC)"
  [`pat_to_display (c:ast_pat) =
      (match c with flatLang_Pany -> displayLang_Item NONE (implode
          "Pany") [] | flatLang_Pvar v -> displayLang_Item NONE (implode
          "Pvar") [displayLang_String v] | flatLang_Plit l ->
          displayLang_Item NONE (implode "Plit") [lit_to_display l] |
          flatLang_Pcon opt_id pats ->
          displayLang_Item NONE (implode "Pcon") [(\f opt. match opt
              with NONE -> empty_item (implode "none") | SOME opt' ->
              displayLang_Item NONE (implode "some") [f opt'])
              id_to_display opt_id;
                            displayLang_Tuple
                                (pat_to_display_list pats)] |
                                flatLang_Pas t v -> displayLang_Item
                                NONE (implode "Pas") [pat_to_display
                                t; displayLang_String v] |
                                flatLang_Pref t -> displayLang_Item
                                NONE (implode "Pref") [pat_to_display
                                t] | ast_Ptannot x y ->
                                displayLang_Item NONE (implode
                                "Ptannot") [pat_to_display x;
                                ast_t_to_display y])`;
   `pat_to_display_list [] = []`;
   `pat_to_display_list (CONS x xs) = CONS (pat_to_display x)
    (pat_to_display_list xs)`];;

let exp_to_display_def,exp_to_display_ind = assume_definition_rec
  "termination (CHEAT_TAC)"
  [`exp_to_display (c:ast_exp) =
      (match c with pattern_semantics_Lit l -> displayLang_Item NONE
          (implode "Lit") [lit_to_display l] | wordLang_Raise e ->
          displayLang_Item NONE (implode "Raise") [exp_to_display e] |
          closLang_Con opt_id es -> displayLang_Item NONE (implode
          "Con") [(\f opt. match opt with NONE -> empty_item (implode
          "none") | SOME opt' -> displayLang_Item NONE (implode "some")
          [f opt']) id_to_display opt_id;
                              displayLang_Tuple (exp_to_display_list
                                  es)] | db_vars_Var id' ->
                                  displayLang_Item NONE (implode "Var")
                                  [id_to_display id'] | ast_Fun n e ->
                                  displayLang_Item NONE (implode "Fun")
                                  [displayLang_String n; exp_to_display
                                  e] | ast_App op es -> displayLang_Item
                                  NONE (implode "App") (CONS
                                  (op_to_display op)
                              (exp_to_display_list es)) | ast_Log
                                  lop e1 e2 -> displayLang_Item NONE
                                  (implode "Log") [lop_to_display lop;
                              exp_to_display e1;
                              exp_to_display e2] |
                                  pattern_semantics_If e1 e2 e3 ->
                                  displayLang_Item NONE (implode "If")
                                  [exp_to_display e1;
                              exp_to_display e2;
                              exp_to_display e3] | closLang_Let
                                  n_opt e1 e2 -> displayLang_Item NONE
                                  (implode "Let")
          [(\f opt. match opt with NONE -> empty_item (implode
              "none") | SOME opt' -> displayLang_Item NONE (implode
              "some") [f opt']) displayLang_String n_opt;
           exp_to_display e1;
           exp_to_display e2] | ast_Mat e pats ->
          displayLang_Item NONE (implode "Mat")
          [exp_to_display e;
           displayLang_Tuple (pat_exp_to_display_list pats)] |
               bvl_Handle e pats ->
          displayLang_Item NONE (implode "Handle")
          [exp_to_display e;
           displayLang_Tuple (pat_exp_to_display_list pats)] |
               ast_Letrec fns e ->
          displayLang_Item NONE (implode "Letrec")
          [displayLang_Tuple (fun_to_display_list fns);
           exp_to_display e] | ast_Tannot e _1 ->
               displayLang_Item NONE (implode "Tannot")
               [exp_to_display e] | ast_Lannot e _2 ->
               displayLang_Item NONE (implode "Lannot")
               [exp_to_display e])`;
   `exp_to_display_list [] = []`;
   `exp_to_display_list (CONS x xs) = CONS (exp_to_display x)
    (exp_to_display_list xs)`;
   `pat_exp_to_display_list [] = []`;
   `pat_exp_to_display_list (CONS (p,e) xs) = CONS (displayLang_Tuple
    [pat_to_display p; exp_to_display e])
        (pat_exp_to_display_list xs)`;
   `fun_to_display_list [] = []`;
   `fun_to_display_list (CONS (m,n,e) xs) = CONS (displayLang_Tuple
    [displayLang_String m;
               displayLang_String n;
               exp_to_display e])
        (fun_to_display_list xs)`];;

let source_to_display_dec_def,source_to_display_dec_ind =
  assume_definition_rec
  "termination (CHEAT_TAC)"
  [`source_to_display_dec (d:dec) =
      (match d with Dlet _3 pat e -> displayLang_Item NONE (implode
          "Dlet") [pat_to_display pat; exp_to_display e] | Dletrec _4
          fns -> displayLang_Item NONE (implode "Dletrec")
                              (MAP (\(m,n,e). displayLang_Tuple
                                  [displayLang_String m;
                              displayLang_String n;
                              exp_to_display e]) fns) | Dtype _5 ts
                                  -> displayLang_Item NONE (implode
                                  "Dtype") (MAP (\(ns,n,z).
                        displayLang_Tuple [displayLang_Tuple (MAP
                            displayLang_String ns);
                              displayLang_String n;
                              displayLang_Tuple (MAP (\(n,tys).
                                  displayLang_Tuple [displayLang_String
                                  n;
                              displayLang_Tuple (MAP
                                  ast_t_to_display tys)]) z)]) ts) |
                                  Dtabbrev _6 ns n ty ->
          displayLang_Item NONE (implode "Dtabbrev")
              [displayLang_Tuple (MAP displayLang_String ns);
                              displayLang_String n;
                              ast_t_to_display ty] | Dexn _7 n tys
                                  -> displayLang_Item NONE (implode
                                  "Dexn") [displayLang_String n;
                              displayLang_Tuple (MAP
                                  ast_t_to_display tys)] | Dmod n ds ->
                                  displayLang_Item NONE (implode "Dmod")
                                  [displayLang_String n;
                              displayLang_Tuple
                                  (source_to_display_dec_list ds)] |
                                  Dlocal xs ys -> displayLang_Item NONE
                                  (implode "Dlocal") [displayLang_Tuple
                                  (source_to_display_dec_list xs);
                              displayLang_Tuple
                                  (source_to_display_dec_list ys)] |
                                  Denv n -> displayLang_Item NONE
                                  (implode "Denv")
                                  [displayLang_String n])`;
   `source_to_display_dec_list [] = []`;
   `source_to_display_dec_list (CONS x xs) = CONS
    (source_to_display_dec x) (source_to_display_dec_list xs)`];;

(* flatLang *)

(* HOL4 presLangScript.sml:414-418: a theorem whose statement the
   port cannot state yet: MEM_pat_size *)

let opt_con_to_display_def = new_definition
  `opt_con_to_display ocon = (match ocon with NONE -> empty_item
  (implode "ConIdNone") | SOME (c,NONE) -> item_with_num (implode
  "ConIdUntyped") c | SOME (c,SOME t) -> item_with_nums (implode
  "ConIdTyped") [c; t])`;;

let flat_pat_to_display_def,flat_pat_to_display_ind =
  assume_definition_rec
  "termination (CHEAT_TAC)"
  [`flat_pat_to_display p =
        (match p with flatLang_Pvar varN -> displayLang_Item NONE
            (implode "Pvar") [string_imp varN] | flatLang_Pany ->
            empty_item (implode "Pany") | flatLang_Plit lit ->
            displayLang_Item NONE (implode "Plit") [lit_to_display lit]
            | flatLang_Pcon id' pats -> displayLang_Item NONE (implode
            "Pcon")
                (flat_pat_to_display_list pats) | flatLang_Pas pat
                    varN -> displayLang_Item NONE (implode "Pas")
                    [flat_pat_to_display pat;
                              string_imp varN] | flatLang_Pref
                                  pat -> displayLang_Item NONE
                                  (implode "Pref")
                                  [flat_pat_to_display pat])`;
   `flat_pat_to_display_list [] = []`;
   `flat_pat_to_display_list (CONS x xs) = CONS
    (flat_pat_to_display x) (flat_pat_to_display_list xs)`];;

let flat_op_to_display_def = new_definition
  `flat_op_to_display op = (match op with flatLang_Src ast_op ->
  op_to_display ast_op | flatLang_GlobalVarAlloc n -> item_with_num
  (implode "GlobalVarAlloc") n | flatLang_GlobalVarInit n ->
  item_with_num (implode "GlobalVarInit") n |
  flatLang_GlobalVarLookup n -> item_with_num (implode
  "GlobalVarLookup") n | flatLang_TagLenEq n1 n2 -> item_with_nums
  (implode "TagLenEq") [n1; n2] | flatLang_LenEq n1 -> item_with_nums
  (implode "LenEq") [n1] | flatLang_El n -> item_with_num (implode
  "El") n | flatLang_Id -> empty_item (implode "Id"))`;;

(* HOL4 presLangScript.sml:457-462: a theorem whose statement the
   port cannot state yet: MEM_funs_size *)

(* HOL4 presLangScript.sml:464-469: a theorem whose statement the
   port cannot state yet: MEM_exps_size *)

(* HOL4 presLangScript.sml:471-476: a theorem whose statement the
   port cannot state yet: MEM_pats_size *)

let add_name_hint_def = new_definition
  `add_name_hint prefix name_hint =
     mlstring_concat [prefix; (implode "<"); name_hint; (implode
       ">")]`;;

let flat_to_display_def,flat_to_display_ind = define_shaped_rec
  "maplist>maplist>maplist>nested"
  [`flat_to_display (flatLang_Raise tra exp) =
        displayLang_Item (SOME tra) (implode "raise")
            [flat_to_display exp]`;
   `flat_to_display (flatLang_Handle tra exp pes:flatLang_exp) =
        displayLang_Item (SOME tra) (implode "handle") (
            CONS (flat_to_display exp) (pat_flat_to_display_list
                pes))`;
   `flat_to_display (flatLang_Lit tra lit:flatLang_exp) =
    displayLang_Item (SOME tra) (implode "lit") []`;
   `flat_to_display (flatLang_Con tra id_opt exps) =
        displayLang_Item (SOME tra) (implode "con") (
            CONS (opt_con_to_display id_opt)
                (flat_to_display_list exps))`;
   `flat_to_display (flatLang_Var_local tra varN) =
        displayLang_Item (SOME tra) (implode "var_local")
            [string_imp varN]`;
   `flat_to_display (flatLang_Fun name_hint varN exp:flatLang_exp) =
        displayLang_Item (SOME backend_common_None) (add_name_hint
            (implode "fun") name_hint)
          [string_imp varN; flat_to_display exp]`;
   `flat_to_display (flatLang_App tra op exps:flatLang_exp) =
        displayLang_Item (SOME tra) (implode "app") (CONS
            (flat_op_to_display op) (flat_to_display_list exps))`;
   `flat_to_display (flatLang_If tra exp1 exp2 exp3:flatLang_exp) =
        displayLang_Item (SOME tra) (implode "if") [flat_to_display
            exp1; flat_to_display exp2;
            flat_to_display exp3]`;
   `flat_to_display (flatLang_Mat tra exp pes:flatLang_exp) =
        displayLang_Item (SOME tra) (implode "mat") (
            CONS (flat_to_display exp) (pat_flat_to_display_list
                pes))`;
   `flat_to_display (flatLang_Let tra varN_opt exp1 exp2:flatLang_exp) =
        displayLang_Item (SOME tra) (implode "let") [(\f opt. match
            opt with NONE -> empty_item (implode "none") | SOME opt' ->
            displayLang_Item NONE (implode "some") [f opt']) string_imp
            varN_opt;
            flat_to_display exp1; flat_to_display exp2]`;
   `flat_to_display (flatLang_Letrec name_hint funs exp:flatLang_exp) =
        displayLang_Item (SOME backend_common_None) (add_name_hint
            (implode "letrec") name_hint)
            [displayLang_Tuple (fun_flat_to_display_list funs);
                flat_to_display exp]`;
   `flat_to_display_list [] = []`;
   `flat_to_display_list (CONS x xs) = CONS (flat_to_display x)
    (flat_to_display_list xs)`;
   `pat_flat_to_display_list [] = []`;
   `pat_flat_to_display_list (CONS (pat,exp) xs) = CONS
    (displayLang_Tuple [flat_pat_to_display pat; flat_to_display
    exp]) (pat_flat_to_display_list xs)`;
   `fun_flat_to_display_list [] = []`;
   `fun_flat_to_display_list (CONS (v1,v2,e) xs) = CONS
    (displayLang_Tuple [string_imp v1; string_imp v2; flat_to_display
    e])
            (fun_flat_to_display_list xs)`];;

(* clos to displayLang *)

(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 presLangScript.sml:541-543: the tactic that proves the
   termination *)
let num_to_varn_aux_def,num_to_varn_aux_ind = define_wf
  `MEASURE I`
  [`num_to_varn_aux n =
     (if n < 26 then [CHR (97 + n)] else APPEND (num_to_varn_aux
       ((n DIV 26) - 1)) ([CHR (97 + (n MOD 26))]))`];;

let num_to_varn_def = new_definition
  `num_to_varn n = implode (num_to_varn_aux n)`;;

let display_num_as_varn_def = new_definition
  `display_num_as_varn n = string_imp (num_to_varn n)`;;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let num_to_varn_list_def,num_to_varn_list_ind = define_wf
  `MEASURE (\(x0,x1). (\n. n) x1)`
  [`num_to_varn_list h n =
     (if n = 0 then [] else CONS (num_to_varn (h + n))
       (num_to_varn_list h (n - 1)))`];;

let attach_name_def = define_cases
  [`attach_name ns NONE = (implode "none")`;
   `attach_name ns (SOME d) =
      (match sptree_lookup d ns with NONE -> mlint_toString d |
          SOME name -> mlstring_concat [name; (implode "@");
          mlint_toString d])`];;

let const_part_to_display_def = define_cases
  [`const_part_to_display (closLang_Int i:const_part) =
      displayLang_Item NONE (implode "Int") [int_to_display i]`;
   `const_part_to_display (closLang_Con t vs:const_part) =
      displayLang_Item NONE (implode "Con") [num_to_display t;
          displayLang_Tuple (MAP num_to_display vs)]`;
   `const_part_to_display (closLang_Str s:const_part) =
      displayLang_Item NONE (implode "Str") [displayLang_String
          (mlstring_concat [implode "\""; s; implode "\""])]`;
   `const_part_to_display (closLang_W64 w:const_part) =
      displayLang_Item NONE (implode "W64") [word_to_display w]`];;

(* the termination relation that HOL4 gives is
     MEASURE (\x. match x with INL v -> const_size v | INR v -> list_size
       const_size v)
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
let const_to_display_def,const_to_display_ind = define_rec
  [`const_to_display (ConstInt i:const) =
      displayLang_Item NONE (implode "ConstInt") [int_to_display
          i]`;
   `const_to_display (ConstCons t vs) =
      displayLang_Item NONE (implode "ConstCons") [num_to_display
          t; displayLang_Tuple (const_to_display_list vs)]`;
   `const_to_display (ConstStr s) =
      displayLang_Item NONE (implode "ConstStr")
          [displayLang_String (mlstring_concat [implode "\""; s;
          implode "\""])]`;
   `const_to_display (ConstWord64 w) =
      displayLang_Item NONE (implode "ConstWord64")
          [word_to_display w]`;
   `const_to_display_list [] = []`;
   `const_to_display_list (CONS x xs) = CONS (const_to_display x)
    (const_to_display_list xs)`];;

let clos_op_to_display_def = new_definition
  `clos_op_to_display ns op = (match op with closLang_GlobOp
  (closLang_Global num') -> item_with_num (implode "Global") num' |
  closLang_GlobOp (closLang_SetGlobal num') -> item_with_num (implode
  "SetGlobal") num' | closLang_GlobOp closLang_AllocGlobal ->
  displayLang_String (implode "AllocGlobal") | closLang_GlobOp
  closLang_GlobalsPtr -> displayLang_String (implode "GlobalsPtr") |
  closLang_GlobOp closLang_SetGlobalsPtr -> displayLang_String (implode
  "SetGlobalsPtr") | closLang_BlockOp (closLang_Cons num') ->
  item_with_num (implode "Cons") num' | closLang_BlockOp
  (closLang_ElemAt num') -> item_with_num (implode "ElemAt") num' |
  closLang_BlockOp (closLang_TagLenEq n1 n2) -> item_with_nums (implode
  "TagLenEq") [n1; n2] | closLang_BlockOp (closLang_BoolTest test) ->
  displayLang_Item NONE (implode "BoolTest") [test_to_display test] |
  closLang_BlockOp closLang_BoolNot -> displayLang_String (implode
  "BoolNot") | closLang_BlockOp (closLang_LenEq num') -> item_with_num
  (implode "LenEq") num' | closLang_BlockOp (closLang_TagEq num') ->
  item_with_num (implode "TagEq") num' | closLang_BlockOp
  closLang_LengthBlock -> displayLang_String (implode "LengthBlock") |
  closLang_BlockOp closLang_BoundsCheckBlock -> displayLang_String
  (implode "BoundsCheckBlock") | closLang_BlockOp (closLang_ConsExtend
  num') -> item_with_num (implode "ConsExtend") num' | closLang_BlockOp
  (closLang_FromList num') -> item_with_num (implode "FromList") num' |
  closLang_BlockOp closLang_ListAppend -> displayLang_String (implode
  "ListAppend") | closLang_BlockOp (closLang_Constant c) ->
  displayLang_Item NONE (implode "Constant") [const_to_display c] |
  closLang_BlockOp closLang_Equal -> displayLang_String (implode
  "Equal") | closLang_BlockOp (closLang_EqualConst c) ->
  displayLang_Item NONE (implode "EqualConst") [const_part_to_display c]
  | closLang_BlockOp (closLang_Build bs) -> displayLang_Item NONE
  (implode "Build") (MAP const_part_to_display bs) | closLang_MemOp
  closLang_Ref -> displayLang_String (implode "Ref") | closLang_MemOp
  closLang_Update -> displayLang_String (implode "Update") |
  closLang_MemOp closLang_El -> displayLang_String (implode "El") |
  closLang_MemOp closLang_Length -> displayLang_String (implode
  "Length") | closLang_MemOp closLang_LengthByte -> displayLang_String
  (implode "LengthByte") | closLang_MemOp (closLang_RefByte b) ->
  displayLang_Item NONE (implode "RefByte") [bool_to_display b] |
  closLang_MemOp closLang_RefArray -> displayLang_String (implode
  "RefArray") | closLang_MemOp closLang_DerefByte -> displayLang_String
  (implode "DerefByte") | closLang_MemOp closLang_UpdateByte ->
  displayLang_String (implode "UpdateByte") | closLang_MemOp
  closLang_ConcatByteVec -> displayLang_String (implode "ConcatByteVec")
  | closLang_MemOp (closLang_CopyByte b) -> displayLang_Item NONE
  (implode "CopyByte") [bool_to_display b] | closLang_MemOp
  closLang_FromListByte -> displayLang_String (implode "FromListByte") |
  closLang_MemOp closLang_ToListByte -> displayLang_String (implode
  "ToListByte") | closLang_MemOp closLang_LengthByteVec ->
  displayLang_String (implode "LengthByteVec") | closLang_MemOp
  closLang_DerefByteVec -> displayLang_String (implode "DerefByteVec") |
  closLang_MemOp closLang_BoundsCheckArray -> displayLang_String
  (implode "BoundsCheckArray") | closLang_MemOp
  (closLang_BoundsCheckByte b) -> displayLang_Item NONE (implode
  "BoundsCheckByte") [bool_to_display b] | closLang_MemOp
  closLang_ConfigGC -> displayLang_String (implode "ConfigGC") |
  closLang_MemOp (closLang_StringCmp b opb) -> displayLang_Item NONE
  (implode "StringCmp") [bool_to_display b;
                              opb_to_display opb] | closLang_MemOp
                                closLang_XorByte -> displayLang_String
                                (implode "XorByte") | closLang_MemOp
                                (closLang_MutCons tag i) ->
                                item_with_nums (implode "MutCons") [tag;
                                i] | closLang_MemOp closLang_UpdateCons
                                -> displayLang_String (implode
                                "UpdateCons") | closLang_MemOp
                                closLang_FinaliseCons ->
                                displayLang_String (implode
                                "FinaliseCons") | closLang_Label num' ->
                                displayLang_Item NONE (implode "Label")
                                [displayLang_String (attach_name ns
                                (SOME num'))] | closLang_FFI s ->
                                displayLang_Item NONE (implode "FFI")
                                [string_imp s] | closLang_IntOp
                                (closLang_Const i) -> displayLang_Item
                                NONE (implode "Const") [int_to_display
                                i] | closLang_IntOp closLang_Add ->
                                displayLang_String (implode "Add") |
                                closLang_IntOp closLang_Sub ->
                                displayLang_String (implode "Sub") |
                                closLang_IntOp closLang_Mult ->
                                displayLang_String (implode "Mult") |
                                closLang_IntOp closLang_Div ->
                                displayLang_String (implode "Div") |
                                closLang_IntOp closLang_Mod ->
                                displayLang_String (implode "Mod") |
                                closLang_IntOp closLang_Less ->
                                displayLang_String (implode "Less") |
                                closLang_IntOp closLang_LessEq ->
                                displayLang_String (implode "LessEq") |
                                closLang_IntOp closLang_Greater ->
                                displayLang_String (implode "Greater") |
                                closLang_IntOp closLang_GreaterEq ->
                                displayLang_String (implode "GreaterEq")
                                | closLang_IntOp
                                (closLang_LessConstSmall num') ->
                                item_with_num (implode "LessConstSmall")
                                num' | closLang_WordOp (WordOpw ws op)
                                -> displayLang_Item NONE (implode
                                "WordOp")
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
                                closLang_WordOp WordFromInt ->
                                displayLang_String (implode
                                "WordFromInt") | closLang_WordOp
                                WordToInt -> displayLang_String
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
                                fp_top_to_display op |
                                closLang_Install ->
                                displayLang_String (implode
                                "Install") | closLang_ThunkOp t ->
                                thunk_op_to_display t)`;;

(* HOL4 presLangScript.sml:675-680: a theorem whose statement the
   port cannot state yet: MEM_clos_exps_size *)

let _ = size_thms "mlstring";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let commas_def,commas_ind = define_wf
  `MEASURE (\x0. list_size mlstring_size x0)`
  [`presLang_commas x1 =
      match x1 with
        [] -> (implode "")
      | [x] -> x
      | (CONS x xs) -> (\x y. strcat x y) ((\x y. strcat x y) x
        (implode ",")) (presLang_commas xs)`];;

(* The clos_to_display ns function uses the same approach to de bruijn
   indices as the pat_to_display function *)
let clos_to_display_def,clos_to_display_ind = assume_definition_rec
  "termination (CHEAT_TAC)"
  [`clos_to_display ns h (closLang_Var t n:closLang_exp) =
        displayLang_Item (SOME t) (implode "var")
            [display_num_as_varn (h - n - 1)]`;
   `clos_to_display ns h (closLang_If t x1 x2 x3:closLang_exp) =
        displayLang_Item (SOME t) (implode "if") [clos_to_display ns
            h x1; clos_to_display ns h x2;
            clos_to_display ns h x3]`;
   `clos_to_display ns h (closLang_Let t xs x) =
        separate_lines (implode "let")
            [displayLang_Tuple (clos_to_display_lets ns h (LENGTH xs
                - 1) xs);
                clos_to_display ns (h + LENGTH xs) x]`;
   `clos_to_display ns h (closLang_Raise t x:closLang_exp) =
        displayLang_Item (SOME t) (implode "raise")
            [clos_to_display ns h x]`;
   `clos_to_display ns h (closLang_Tick t x:closLang_exp) =
        displayLang_Item (SOME t) (implode "tick")
            [clos_to_display ns h x]`;
   `clos_to_display ns h (closLang_Handle t x y:closLang_exp) =
        displayLang_Item (SOME t) (implode "handle")
            [clos_to_display ns h x; display_num_as_varn h;
                clos_to_display ns (h + 1) y]`;
   `clos_to_display ns h (closLang_Call t ticks dest xs:closLang_exp) =
        displayLang_Item (SOME t) (implode "call")
          (APPEND [num_to_display ticks; displayLang_String
              (attach_name ns (SOME dest))]
           (clos_to_display_list ns h xs))`;
   `clos_to_display ns h (closLang_App t opt_n x xs:closLang_exp) =
        displayLang_Item (SOME t) (implode "app")
            (APPEND [(\f opt. match opt with NONE -> empty_item
                (implode "none") | SOME opt' -> displayLang_Item NONE
                (implode "some") [f opt']) num_to_display opt_n;
              clos_to_display ns h x] (clos_to_display_list ns h
                  xs))`;
   `clos_to_display ns h (closLang_Fn name_hint n1 n2 vn x) =
        displayLang_Item (SOME backend_common_None) (add_name_hint
            (implode "fn") name_hint)
            [(\f opt. match opt with NONE -> empty_item (implode
                "none") | SOME opt' -> displayLang_Item NONE (implode
                "some") [f opt']) num_to_display n1;
             (\f opt. match opt with NONE -> empty_item (implode
                 "none") | SOME opt' -> displayLang_Item NONE (implode
                 "some") [f opt']) ((\f xs. displayLang_Tuple (MAP f
                 xs)) num_to_display) n2;
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
                 "some") [f opt']) ((\f xs. displayLang_Tuple (MAP f
                 xs)) num_to_display) n2;
             displayLang_Tuple (clos_to_display_letrecs ns h (LENGTH
                 es - 1) (LENGTH es) es);
             clos_to_display ns h e]`;
   `clos_to_display ns h (closLang_Op t op xs:closLang_exp) =
        displayLang_Item (SOME t) (implode "op") (CONS
            (clos_op_to_display LN op)
            (clos_to_display_list ns h xs))`;
   `clos_to_display_list ns h [] = []`;
   `clos_to_display_list ns h (CONS x xs) = CONS (clos_to_display ns
    h x) (clos_to_display_list ns h xs)`;
   `clos_to_display_lets ns h i [] = []`;
   `clos_to_display_lets ns h i (CONS x xs) =
          CONS (displayLang_Tuple [display_num_as_varn (h + i);
              displayLang_String (implode "<-"); clos_to_display ns h
              x]) (clos_to_display_lets ns h (i - 1) xs)`;
   `clos_to_display_letrecs ns h i len [] = []`;
   `clos_to_display_letrecs ns h i len (CONS (vn,e) es) =
        CONS (displayLang_Tuple [display_num_as_varn (h + i);
            (\f xs. displayLang_Tuple (MAP f xs)) string_imp
                (num_to_varn_list ((h + len) - 1) vn);
            clos_to_display ns (h + len + vn) e])
                (clos_to_display_letrecs ns h (i - 1) len es)`];;

let clos_fun_to_display_def = new_definition
  `clos_fun_to_display names (n,argc,body) =
     displayLang_Tuple [displayLang_String (implode "func");
            displayLang_String (attach_name names (SOME n));
            displayLang_Tuple (REVERSE (list_of_seq
              display_num_as_varn argc));
            clos_to_display names argc body]`;;

let clos_dec_to_display_def = new_definition
  `clos_dec_to_display names dec =
     displayLang_Tuple [displayLang_String (implode "dec");
            clos_to_display names 0 dec]`;;

(* bvl to displayLang *)

(* HOL4 presLangScript.sml:769-774: a theorem whose statement the
   port cannot state yet: MEM_bvl_exps_size *)

let _ = size_thms "bvl_exp";;
(* the termination relation that HOL4 gives is
     MEASURE (\x.
          match x with
            INL (ns,h,x) -> flatLang_exp_size x | INR (INL (ns,h,xs)) ->
              list_size flatLang_exp_size xs | INR (INR (ns,h,i,xs)) ->
              list_size flatLang_exp_size xs)
   which is not one that HOL Light takes here; the one
   below is what the port found for it *)
let bvl_to_display_def,bvl_to_display_ind = define_shaped_wf
  "maplist>measure"
  `MEASURE (sum_measure (\(x0,x1,x2). bvl_exp_size x2) (\(x0,x1,x2,x3).
  bvl_exp_size1 x3))`
  [`bvl_to_display ns h (bvl_Var n:bvl_exp) =
        displayLang_Item NONE (implode "var")
            [display_num_as_varn (h - n - 1)]`;
   `bvl_to_display ns h (bvl_If x1 x2 x3:bvl_exp) =
        displayLang_Item NONE (implode "if") [bvl_to_display ns h
            x1; bvl_to_display ns h x2;
            bvl_to_display ns h x3]`;
   `bvl_to_display ns h (bvl_Let xs x) =
        separate_lines (implode "let")
            (APPEND (bvl_to_display_lets ns h (LENGTH xs - 1) xs)
                [bvl_to_display ns (h + LENGTH xs) x])`;
   `bvl_to_display ns h (bvl_Raise x:bvl_exp) =
        displayLang_Item NONE (implode "raise") [bvl_to_display
            ns h x]`;
   `bvl_to_display ns h (bvl_Tick x:bvl_exp) =
        displayLang_Item NONE (implode "tick") [bvl_to_display ns
            h x]`;
   `bvl_to_display ns h (bvl_Handle x y:bvl_exp) =
        displayLang_Item NONE (implode "handle")
            [bvl_to_display ns h x; display_num_as_varn h;
                bvl_to_display ns (h + 1) y]`;
   `bvl_to_display ns h (bvl_Call ticks dest xs:bvl_exp) =
        displayLang_Item NONE (implode "call")
             (CONS (displayLang_String (attach_name ns dest))
              (bvl_to_display_list ns h xs))`;
   `bvl_to_display ns h (bvl_Force loc n:bvl_exp) =
        displayLang_Item NONE (implode "force")
             [display_num_as_varn (h - n - 1); displayLang_String
                 (attach_name ns (SOME loc))]`;
   `bvl_to_display ns h (bvl_Op op xs:bvl_exp) =
        displayLang_Item NONE (implode "op") (CONS
            (clos_op_to_display ns op)
                              (bvl_to_display_list ns h xs))`;
   `bvl_to_display_list ns h [] = []`;
   `bvl_to_display_list ns h (CONS x xs) = CONS (bvl_to_display ns h
    x) (bvl_to_display_list ns h xs)`;
   `bvl_to_display_lets ns h i [] = []`;
   `bvl_to_display_lets ns h i (CONS x xs) =
        CONS (displayLang_Tuple [display_num_as_varn (h + i);
            displayLang_String (implode "<-"); bvl_to_display ns h
            x]) (bvl_to_display_lets ns h (i - 1) xs)`];;

let bvl_fun_to_display_def = new_definition
  `bvl_fun_to_display names (n,argc,body) =
     displayLang_Tuple [displayLang_String (implode "func");
            displayLang_String (attach_name names (SOME n));
            displayLang_Tuple (REVERSE (list_of_seq
              display_num_as_varn argc));
            bvl_to_display names argc body]`;;

(* bvi to displayLang *)

(* HOL4 presLangScript.sml:829-834: a theorem whose statement the
   port cannot state yet: MEM_bvi_exps_size *)

let bvi_to_display_def,bvi_to_display_ind = assume_definition_rec
  "termination (CHEAT_TAC)"
  [`bvi_to_display ns h (bvi_Var n:bvi_exp) =
        displayLang_Item NONE (implode "var")
            [display_num_as_varn (h - n - 1)]`;
   `bvi_to_display ns h (bvi_If x1 x2 x3:bvi_exp) =
        displayLang_Item NONE (implode "if") [bvi_to_display ns h
            x1; bvi_to_display ns h x2;
            bvi_to_display ns h x3]`;
   `bvi_to_display ns h (bvi_Let xs x) =
        separate_lines (implode "let")
            (APPEND (bvi_to_display_lets ns h (LENGTH xs - 1) xs)
                [bvi_to_display ns (h + LENGTH xs) x])`;
   `bvi_to_display ns h (bvi_Raise x:bvi_exp) =
        displayLang_Item NONE (implode "raise") [bvi_to_display
            ns h x]`;
   `bvi_to_display ns h (bvi_Tick x:bvi_exp) =
        displayLang_Item NONE (implode "tick") [bvi_to_display ns
            h x]`;
   `bvi_to_display ns h (bvi_Call ticks dest xs handler:bvi_exp) =
        displayLang_Item NONE (implode "call")
             (APPEND (CONS (displayLang_String (attach_name ns
                 dest))
              (bvi_to_display_list ns h xs))
              (match handler with NONE -> [] | SOME e ->
                  [displayLang_Item NONE (implode "handler")
                  [display_num_as_varn h;
                              empty_item (implode "->");
                              bvi_to_display ns (h + 1) e]]))`;
   `bvi_to_display ns h (bvi_Force loc n:bvi_exp) =
        displayLang_Item NONE (implode "force")
             [display_num_as_varn (h - n - 1); displayLang_String
                 (attach_name ns (SOME loc))]`;
   `bvi_to_display ns h (bvi_Op op xs:bvi_exp) =
        displayLang_Item NONE (implode "op") (CONS
            (clos_op_to_display ns op)
                              (bvi_to_display_list ns h xs))`;
   `bvi_to_display ns h (bvi_Return xs:bvi_exp) =
        displayLang_Item NONE (implode "return")
            (bvi_to_display_list ns h xs)`;
   `bvi_to_display ns h (bvi_LetCall rets ticks dest xs y) =
        separate_lines (implode "letcall")
            [displayLang_Item NONE (implode "call")
               (CONS (displayLang_String (attach_name ns (SOME
                   dest))) (bvi_to_display_list ns h xs));
             displayLang_Tuple (REVERSE (list_of_seq (\i.
                 display_num_as_varn (h + i)) rets));
             bvi_to_display ns (h + rets) y]`;
   `bvi_to_display_list ns h [] = []`;
   `bvi_to_display_list ns h (CONS x xs) = CONS (bvi_to_display ns h
    x) (bvi_to_display_list ns h xs)`;
   `bvi_to_display_lets ns h i [] = []`;
   `bvi_to_display_lets ns h i (CONS x xs) =
        CONS (displayLang_Tuple [display_num_as_varn (h + i);
            displayLang_String (implode "<-"); bvi_to_display ns h
            x]) (bvi_to_display_lets ns h (i - 1) xs)`];;

let bvi_fun_to_display_def = new_definition
  `bvi_fun_to_display names (n,argc,body) =
     displayLang_Tuple [displayLang_String (implode "func");
            displayLang_String (attach_name names (SOME n));
            displayLang_Tuple (REVERSE (list_of_seq
              display_num_as_varn argc));
            bvi_to_display names argc body]`;;

(* dataLang *)

let num_set_to_display_def = new_definition
  `num_set_to_display ns =
     displayLang_String (mlstring_concat [(implode "{");
                      presLang_commas (MAP mlint_toString (MAP FST
                        (toSortedAList ns)));
                      (implode "}")])`;;

let _ = size_thms "dataLang_prog";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let data_seqs_def,data_seqs_ind = define_wf
  `MEASURE (\x0. dataLang_prog_size x0)`
  [`data_seqs z =
     (match z with dataLang_Seq x y -> misc_Append (data_seqs x)
       (data_seqs y) | _19 -> displayLang_List [z])`];;

(* [local] *)
let MEM_append_data_seqs = prove
 (`!x. MEM a (append (data_seqs x)) ==> labLang_prog_size a <=
  labLang_prog_size x`,
  CHEAT_TAC);;

(* [local] *)
let list_size_append_data_seqs = prove
 (`!x.
   list_size labLang_prog_size (append (data_seqs x)) =
   labLang_prog_size x + 1`,
  CHEAT_TAC);;

(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
let data_prog_to_display_def,data_prog_to_display_ind = define_wf
  `MEASURE (\x. match x with INL (k,_20,_21) -> k | INR (k,_22,_23) ->
  k)`
  [`data_prog_to_display 0 ns prog = empty_item (implode "...")`;
   `data_prog_to_display (SUC k) ns prog =
          (match prog with dataLang_Skip -> empty_item (implode
              "skip") | dataLang_Move x y -> displayLang_Tuple
            [num_to_display x; displayLang_String (implode ":=");
                num_to_display y] | wordLang_Call rets target args NONE
                -> displayLang_Item NONE (implode "call")
            [(\f opt. match opt with NONE -> empty_item (implode
                "none") | SOME opt' -> displayLang_Item NONE (implode
                "some") [f opt']) (\(x,y). displayLang_Tuple
                    [(\f xs. displayLang_Tuple (MAP f xs))
                        num_to_display x;
                     num_set_to_display y]) rets;
                displayLang_String (attach_name ns target);
                (\f xs. displayLang_Tuple (MAP f xs)) num_to_display
                    args;
                empty_item (implode "none")] | wordLang_Call rets
                    target args (SOME (v,handler)) -> displayLang_Item
                    NONE (implode "call")
            [(\f opt. match opt with NONE -> empty_item (implode
                "none") | SOME opt' -> displayLang_Item NONE (implode
                "some") [f opt']) (\(x,y). displayLang_Tuple
                    [(\f xs. displayLang_Tuple (MAP f xs))
                        num_to_display x;
                     num_set_to_display y]) rets;
                displayLang_String (attach_name ns target);
                (\f xs. displayLang_Tuple (MAP f xs)) num_to_display
                    args;
                displayLang_Item NONE (implode "some")
                    [displayLang_Tuple [num_to_display v;
                    data_prog_to_display k ns handler]]] |
                        dataLang_Force ret loc src -> displayLang_Item
                        NONE (implode "force")
            [(\f opt. match opt with NONE -> empty_item (implode
                "none") | SOME opt' -> displayLang_Item NONE (implode
                "some") [f opt']) (\(x,y). displayLang_Tuple
                    [num_to_display x; num_set_to_display y]) ret;
             num_to_display loc;
             num_to_display src] | dataLang_Assign n op args n_set
                 -> displayLang_Tuple
            [num_to_display n;
             displayLang_String (implode ":=");
             clos_op_to_display ns op;
                (\f xs. displayLang_Tuple (MAP f xs)) num_to_display
                    args;
                (\f opt. match opt with NONE -> empty_item (implode
                    "none") | SOME opt' -> displayLang_Item NONE
                    (implode "some") [f opt']) num_set_to_display n_set]
                    | wordLang_Seq x y ->
            (let xs = append (misc_Append (data_seqs x) (data_seqs
                y)) in
               separate_lines (implode "seq")
                   (data_prog_to_display_list k ns xs)) |
                   pattern_semantics_If n x y -> displayLang_Item NONE
                   (implode "if")
            [num_to_display n; data_prog_to_display k ns x;
                data_prog_to_display k ns y] | dataLang_MakeSpace n ns
                -> displayLang_Item NONE (implode "make_space")
            [num_to_display n; num_set_to_display ns] |
                wordLang_Raise n -> displayLang_Item NONE (implode
                "raise") [num_to_display n] | stackLang_Return ns ->
                displayLang_Item NONE (implode "return") [(\f xs.
                displayLang_Tuple (MAP f xs)) num_to_display ns] |
                wordLang_Tick -> empty_item (implode "tick"))`;
   `data_prog_to_display_list k ns [] = []`;
   `data_prog_to_display_list k ns (CONS x xs) =
        (match k with
          0 -> [] | SUC k -> CONS (data_prog_to_display k ns x)
              (data_prog_to_display_list k ns xs))`];;

let data_fun_to_display_def = new_definition
  `data_fun_to_display names (n,argc,body) =
     displayLang_Tuple [displayLang_String (implode "func");
            displayLang_String (attach_name names (SOME n));
            displayLang_Tuple (list_of_seq num_to_display argc);
            data_prog_to_display 1000000000 names body]`;;

(* asm *)

let asm_binop_to_display_def = new_definition
  `asm_binop_to_display op = (match op with asm_Add -> empty_item
  (implode "Add") | closLang_Sub -> empty_item (implode "Sub") |
  asm_And -> empty_item (implode "And") | asm_Or -> empty_item
  (implode "Or") | asm_Xor -> empty_item (implode "Xor"))`;;

let asm_reg_imm_to_display_def = new_definition
  `asm_reg_imm_to_display reg_imm' = (match reg_imm' with Reg reg ->
  item_with_num (implode "Reg") reg | Imm imm -> item_with_word
  (implode "Imm") imm)`;;

let asm_arith_to_display_def = new_definition
  `asm_arith_to_display op = (match op with asm_Binop bop n1 n2 reg_imm'
  -> displayLang_Item NONE (implode "Binop")
         [asm_binop_to_display bop; num_to_display n1; num_to_display
           n2;
             asm_reg_imm_to_display reg_imm'] | asm_Shift sh n1 n2 n3
               -> displayLang_Item NONE (implode "Shift")
         [shift_to_display sh;
          num_to_display n1;
          num_to_display n2;
          asm_reg_imm_to_display n3] | asm_Div n1 n2 n3 ->
            item_with_nums (implode "Div") [n1; n2; n3] | asm_LongMul
            n1 n2 n3 n4 -> item_with_nums (implode "LongMul") [n1;
            n2; n3; n4] | asm_LongDiv n1 n2 n3 n4 n5 ->
            item_with_nums (implode "LongDiv") [n1; n2; n3; n4; n5] |
            asm_AddCarry n1 n2 n3 n4 -> item_with_nums (implode
            "AddCarry") [n1; n2; n3; n4] | asm_AddOverflow n1 n2 n3
            n4 -> item_with_nums (implode "AddOverflow") [n1; n2; n3;
            n4] | asm_SubOverflow n1 n2 n3 n4 -> item_with_nums
            (implode "SubOverflow") [n1; n2; n3; n4])`;;

let asm_addr_to_display_def = new_definition
  `asm_addr_to_display addr' = (match addr' with Addr reg w ->
  displayLang_Item NONE (implode "Addr")
                          [num_to_display reg; word_to_display w])`;;

let asm_memop_to_display_def = new_definition
  `asm_memop_to_display op = (match op with asm_Load -> empty_item
  (implode "Load") | asm_Load8 -> empty_item (implode "Load8") |
  asm_Load16 -> empty_item (implode "Load16") | asm_Load32 ->
  empty_item (implode "Load32") | asm_Store -> empty_item (implode
  "Store") | asm_Store8 -> empty_item (implode "Store8") |
  asm_Store16 -> empty_item (implode "Store16") | asm_Store32 ->
  empty_item (implode "Store32"))`;;

let asm_cmp_to_display_def = new_definition
  `asm_cmp_to_display op = (match op with closLang_Equal ->
  empty_item (implode "Equal") | asm_Lower -> empty_item (implode
  "Lower") | closLang_Less -> empty_item (implode "Less") | asm_Test
  -> empty_item (implode "Test") | asm_NotEqual -> empty_item
  (implode "NotEqual") | asm_NotLower -> empty_item (implode
  "NotLower") | asm_NotLess -> empty_item (implode "NotLess") |
  asm_NotTest -> empty_item (implode "NotTest"))`;;

let asm_fp_to_display_def = new_definition
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

let asm_inst_to_display_def = new_definition
  `asm_inst_to_display inst' = (match inst' with asm_Skip -> empty_item
  (implode "Skip") | asm_Const reg w -> displayLang_Item NONE (implode
  "Const") [num_to_display reg;
                              word_to_display w] | asm_Arith a ->
                                displayLang_Item NONE (implode "Arith")
                                [asm_arith_to_display a] | asm_Mem mop r
                                addr' -> displayLang_Item NONE (implode
                                "Mem") [asm_memop_to_display mop;
         num_to_display r; asm_addr_to_display addr'] | asm_FP fp
           -> displayLang_Item NONE (implode "FP") [asm_fp_to_display
           fp])`;;

let asm_asm_to_display_def = new_definition
  `asm_asm_to_display inst' = (match inst' with asm_Inst i ->
  asm_inst_to_display i | labLang_Jump w -> item_with_word (implode
  "Jump") w | labLang_JumpCmp c r to w -> displayLang_Item NONE (implode
  "JumpCmp")
       [asm_cmp_to_display c; num_to_display r;
         asm_reg_imm_to_display to;
        word_to_display w] | labLang_Call w -> item_with_word
          (implode "Call") w | asm_JumpReg r -> item_with_num
          (implode "JumpReg>") r | wordLang_Loc r w ->
          displayLang_Item NONE (implode "Loc") [num_to_display r;
          word_to_display w])`;;

(* stackLang *)

let store_name_to_display_def = new_definition
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

let _ = size_thms "stackLang_prog";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let stack_seqs_def,stack_seqs_ind = define_wf
  `MEASURE (\x0. stackLang_prog_size (\x. 0) x0)`
  [`stack_seqs z =
     (match z with stackLang_Seq x y -> misc_Append (stack_seqs
       x) (stack_seqs y) | _24 -> displayLang_List [z])`];;

(* [local] *)
let MEM_append_stack_seqs = prove
 (`!x. MEM a (append (stack_seqs x)) ==> labLang_prog_size ARB a <=
  labLang_prog_size ARB x`,
  CHEAT_TAC);;

(* [local] *)
let list_size_append_stack_seqs = prove
 (`!x.
   list_size (labLang_prog_size ARB) (append (stack_seqs x)) =
   labLang_prog_size ARB x + 1`,
  CHEAT_TAC);;

let stack_prog_to_display_def,stack_prog_to_display_ind =
  assume_definition_rec
  "termination (CHEAT_TAC)"
  [`stack_prog_to_display 0 ns prog = empty_item (implode "...")`;
   `stack_prog_to_display (SUC k) ns stackLang_Skip = empty_item
    (implode "skip")`;
   `stack_prog_to_display (SUC k) ns (stackLang_Inst i) =
    asm_inst_to_display i`;
   `stack_prog_to_display (SUC k) ns (stackLang_Get n sn) =
    displayLang_Tuple
      [num_to_display n; displayLang_String (implode "<-");
          store_name_to_display sn]`;
   `stack_prog_to_display (SUC k) ns (stackLang_Set sn n) =
    displayLang_Tuple
      [store_name_to_display sn; displayLang_String (implode
          "<-"); num_to_display n]`;
   `stack_prog_to_display (SUC k) ns (stackLang_OpCurrHeap b n1 n2) =
    displayLang_Tuple
      [num_to_display n1; displayLang_String (implode ":=");
          displayLang_String (implode "CurrHeap");
       asm_binop_to_display b; num_to_display n2]`;
   `stack_prog_to_display (SUC k) ns (stackLang_Call rh tgt eh) =
      displayLang_Item NONE (implode "call")
           [(match rh with NONE -> empty_item (implode "tail") |
               SOME (p,lr,l1,l2) ->
                 displayLang_Item NONE (implode "returning")
                      [num_to_display lr;
                       displayLang_String (attach_name ns (SOME
                           l1));
                       num_to_display l2;
                       stack_prog_to_display k ns p]);
           (match tgt with INL l -> displayLang_Item NONE (implode
               "direct") [displayLang_String (attach_name ns (SOME l))]
               | INR r -> item_with_num (implode "reg") r);
           (match eh with NONE -> empty_item (implode "no_handler")
               | SOME (p,l1,l2) ->
                displayLang_Item NONE (implode "handler")
                     [displayLang_String (attach_name ns (SOME l1));
                      num_to_display l2;
                      stack_prog_to_display k ns p])]`;
   `stack_prog_to_display (SUC k) ns (stackLang_Seq x y) =
         (let xs = append (misc_Append (stack_seqs x) (stack_seqs
             y)) in
            separate_lines (implode "seq")
                (stack_prog_to_display_list k ns xs))`;
   `stack_prog_to_display (SUC k) ns (stackLang_If c n to x y) =
    displayLang_Item NONE (implode "if")
         [displayLang_Tuple [asm_cmp_to_display c; num_to_display n;
             asm_reg_imm_to_display to];
          stack_prog_to_display k ns x;
          stack_prog_to_display k ns y]`;
   `stack_prog_to_display (SUC k) ns (stackLang_Loop x) =
    displayLang_Item NONE (implode "loop")
         [stack_prog_to_display k ns x]`;
   `stack_prog_to_display (SUC k) ns (stackLang_JumpLower n1 n2 n3) =
      item_with_nums (implode "jump_lower") [n1; n2; n3]`;
   `stack_prog_to_display (SUC k) ns (stackLang_Alloc n) =
    item_with_num (implode "alloc") n`;
   `stack_prog_to_display (SUC k) ns (stackLang_StoreConsts n1 n2
    _26) = item_with_nums (implode "store_consts") [n1; n2]`;
   `stack_prog_to_display (SUC k) ns (stackLang_Raise n) =
    item_with_num (implode "raise") n`;
   `stack_prog_to_display (SUC k) ns (stackLang_Return n) =
    item_with_num (implode "return") n`;
   `stack_prog_to_display (SUC k) ns (stackLang_Break n) =
    item_with_num (implode "break") n`;
   `stack_prog_to_display (SUC k) ns (stackLang_Continue n) =
    item_with_num (implode "continue") n`;
   `stack_prog_to_display (SUC k) ns (stackLang_FFI nm cp cl ap al ra) =
    displayLang_Item NONE (implode "ffi")
         (CONS (string_imp nm) (MAP num_to_display [cp; cl; ap;
             al; ra]))`;
   `stack_prog_to_display (SUC k) ns stackLang_Tick = empty_item
    (implode "tick")`;
   `stack_prog_to_display (SUC k) ns (stackLang_LocValue n1 n2 n3) =
      displayLang_Item NONE (implode "loc_value") [num_to_display
          n1;
                             displayLang_String (attach_name ns
                                 (SOME n2));
                             num_to_display n3]`;
   `stack_prog_to_display (SUC k) ns (stackLang_Install n1 n2 n3 n4 n5)
    =
      item_with_nums (implode "install") [n1; n2; n3; n4; n5]`;
   `stack_prog_to_display (SUC k) ns (stackLang_ShMemOp mop r a) =
      displayLang_Item NONE (implode "sh_mem") [asm_memop_to_display
          mop;
                              num_to_display r;
                                  asm_addr_to_display a]`;
   `stack_prog_to_display (SUC k) ns (stackLang_CodeBufferWrite n1 n2) =
      item_with_nums (implode "code_buffer_write") [n1; n2]`;
   `stack_prog_to_display (SUC k) ns (stackLang_DataBufferWrite n1 n2) =
      item_with_nums (implode "data_buffer_write") [n1; n2]`;
   `stack_prog_to_display (SUC k) ns (stackLang_RawCall n) =
      displayLang_Item NONE (implode "raw_call")
          [displayLang_String (attach_name ns (SOME n))]`;
   `stack_prog_to_display (SUC k) ns (stackLang_StackAlloc n) =
    item_with_num (implode "stack_alloc") n`;
   `stack_prog_to_display (SUC k) ns (stackLang_StackFree n) =
    item_with_num (implode "stack_free") n`;
   `stack_prog_to_display (SUC k) ns (stackLang_StackStore n m) =
      displayLang_Tuple [displayLang_String ((\x y. strcat x y)
          ((\x y. strcat x y) ((\x y. strcat x y) (implode "stack[")
          (num_to_hex_mlstring n)) (implode "] := ")) (mlint_toString
          m))]`;
   `stack_prog_to_display (SUC k) ns (stackLang_StackStoreAny n m) =
      displayLang_Tuple [displayLang_String ((\x y. strcat x y)
          ((\x y. strcat x y) ((\x y. strcat x y) (implode
          "stack[var ") (mlint_toString n)) (implode "] := "))
          (mlint_toString m))]`;
   `stack_prog_to_display (SUC k) ns (stackLang_StackLoad n m) =
      displayLang_Tuple [displayLang_String (mlstring_concat
          [mlint_toString n;
                             (implode " := stack[");
                             num_to_hex_mlstring m; (implode
                                 "]")])]`;
   `stack_prog_to_display (SUC k) ns (stackLang_StackLoadAny n m) =
      displayLang_Tuple [displayLang_String (mlstring_concat
          [mlint_toString n;
                             (implode " := stack[var ");
                             mlint_toString m; (implode "]")])]`;
   `stack_prog_to_display (SUC k) ns (stackLang_StackGetSize n) =
    item_with_num (implode "stack_get_size") n`;
   `stack_prog_to_display (SUC k) ns (stackLang_StackSetSize n) =
    item_with_num (implode "stack_set_size") n`;
   `stack_prog_to_display (SUC k) ns (stackLang_BitmapLoad n m) =
      displayLang_Tuple [displayLang_String (mlstring_concat
          [mlint_toString n;
                             (implode " := bitmap[");
                             num_to_hex_mlstring m;
                             (implode "]")])]`;
   `stack_prog_to_display (SUC k) ns (stackLang_Halt n) =
    item_with_num (implode "halt") n`;
   `stack_prog_to_display_list k ns [] = []`;
   `stack_prog_to_display_list k ns (CONS x xs) =
        (match k with 0 -> [] | SUC k -> CONS
            (stack_prog_to_display k ns x)
            (stack_prog_to_display_list k ns xs))`];;

let stack_fun_to_display_def = new_definition
  `stack_fun_to_display names (n,body) =
     displayLang_Tuple [displayLang_String (implode "func");
            displayLang_String (attach_name names (SOME n));
            stack_prog_to_display 1000000000 names body]`;;

(* labLang *)

let lab_asm_to_display_def = new_definition
  `lab_asm_to_display ns la = (match la with labLang_Jump (labLang_Lab s
  n) ->
         displayLang_Item NONE (implode "jump")
           [displayLang_String (attach_name ns (SOME s));
             num_to_display n] | labLang_JumpCmp c r ri (labLang_Lab s
             n) ->
         displayLang_Item NONE (implode "jump_cmp")
           [displayLang_Tuple [asm_cmp_to_display c; num_to_display
             r;
                   asm_reg_imm_to_display ri];
            displayLang_String (attach_name ns (SOME s));
              num_to_display n] | labLang_Call (labLang_Lab s n) ->
         displayLang_Item NONE (implode "call")
           [displayLang_String (attach_name ns (SOME s));
             num_to_display n] | labLang_LocValue r (labLang_Lab s n) ->
         displayLang_Item NONE (implode "loc_value")
           [num_to_display r; displayLang_String (attach_name ns
             (SOME s)); num_to_display n] | labLang_CallFFI name ->
             displayLang_Item NONE (implode "call_FFI") [string_imp
             name] | stackLang_Install -> empty_item (implode
             "install") | stackLang_Halt -> empty_item (implode
             "halt"))`;;

let lab_line_to_display_def = new_definition
  `lab_line_to_display ns line = (match line with labLang_Label s n le
  ->
         displayLang_Item NONE (implode "label") [displayLang_String
           (attach_name ns (SOME s)); num_to_display n] | labLang_Asm
           aoc enc len -> (match aoc with Asmi i -> displayLang_Item
           NONE (implode "asm") [asm_asm_to_display i] | Cbw r1 r2 ->
           item_with_nums (implode "cbw") [r1; r2] | ShareMem mop r a ->
           displayLang_Item NONE (implode "share_mem")
           [asm_memop_to_display mop;
                              num_to_display r;
                              asm_addr_to_display a]) |
                                labLang_LabAsm la pos enc len ->
                                lab_asm_to_display ns la)`;;

let lab_fun_to_display_def = define_general
  [`lab_fun_to_display names (Section n lines) =
     displayLang_List (
            CONS (displayLang_String (attach_name names (SOME
              n))) (MAP (lab_line_to_display names) lines))`];;

(* wordLang *)

let _ = size_thms "wordLang_prog";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let word_seqs_def,word_seqs_ind = define_wf
  `MEASURE (\x0. wordLang_prog_size (\x. 0) x0)`
  [`word_seqs z =
     (match z with wordLang_Seq x y -> misc_Append (word_seqs x)
       (word_seqs y) | _31 -> displayLang_List [z])`];;

(* [local] *)
let MEM_append_word_seqs = prove
 (`!x. MEM a (append (word_seqs x)) ==> labLang_prog_size ARB a <=
  labLang_prog_size ARB x`,
  CHEAT_TAC);;

(* HOL4 presLangScript.sml:1311-1312: a theorem that HOL4 states as
   the value of an ML expression: MEM_word_exps_size_ARB *)

(* the termination relation that HOL4 gives is
     MEASURE (\x. match x with INL v -> wordLang_exp_size ARB v | INR v
       -> list_size wordLang_exp_size ARB v)
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
let word_exp_to_display_def,word_exp_to_display_ind = define_rec
  [`word_exp_to_display (wordLang_Const v) = item_with_word (implode
    "Const") v`;
   `word_exp_to_display (wordLang_Var n) = item_with_num (implode
    "Var") n`;
   `word_exp_to_display (wordLang_Lookup st) = displayLang_Item NONE
    (implode "Lookup") [store_name_to_display st]`;
   `word_exp_to_display (wordLang_Load exp2) = displayLang_Item NONE
    (implode "MemLoad") [word_exp_to_display exp2]`;
   `word_exp_to_display (wordLang_Op bop exs) = displayLang_Item NONE
    (implode "Op") (
        CONS (asm_binop_to_display bop) (word_exp_to_display_list
            exs))`;
   `word_exp_to_display (wordLang_Shift sh exp exp1) = displayLang_Item
    NONE (implode "Shift") [
      shift_to_display sh;
      word_exp_to_display exp;
      word_exp_to_display exp1]`;
   `word_exp_to_display_list [] = []`;
   `word_exp_to_display_list (CONS x xs) = CONS
    (word_exp_to_display x) (word_exp_to_display_list xs)`];;

let ws_to_display_def,ws_to_display_ind = define_rec
  [`ws_to_display [] = []`;
   `ws_to_display (CONS (b,x) xs) = CONS (displayLang_Tuple
    [bool_to_display b; word_to_display x]) (ws_to_display xs)`];;

let num_sets_to_display_def = new_definition
  `num_sets_to_display (l,r) =
     displayLang_Tuple [num_set_to_display l;
            num_set_to_display r]`;;

let word_prog_to_display_def,word_prog_to_display_ind =
  assume_definition_rec
  "termination (CHEAT_TAC)"
  [`word_prog_to_display 0 ns x = empty_item (implode "...")`;
   `word_prog_to_display (SUC k) ns wordLang_Skip = empty_item
    (implode "skip")`;
   `word_prog_to_display (SUC k) ns (wordLang_Move n mvs) =
    displayLang_Item NONE (implode "move")
        [num_to_display n; displayLang_Tuple (MAP (\(n1,n2).
            displayLang_Tuple
            [num_to_display n1;
             displayLang_String (implode ":=");
             num_to_display n2]) mvs)]`;
   `word_prog_to_display (SUC k) ns (wordLang_Inst i) =
        displayLang_Item NONE (implode "inst")
            [asm_inst_to_display i]`;
   `word_prog_to_display (SUC k) ns (wordLang_Assign n exp) =
         displayLang_Tuple [num_to_display n;
                displayLang_String (implode ":=");
                word_exp_to_display exp]`;
   `word_prog_to_display (SUC k) ns (wordLang_Get n sn) =
    displayLang_Tuple
        [num_to_display n; displayLang_String (implode "<-");
            store_name_to_display sn]`;
   `word_prog_to_display (SUC k) ns (wordLang_Set sn exp) =
    displayLang_Tuple
        [store_name_to_display sn; displayLang_String (implode
            "<-"); word_exp_to_display exp]`;
   `word_prog_to_display (SUC k) ns (wordLang_Store exp n) =
    displayLang_Tuple
        [displayLang_String (implode "mem"); word_exp_to_display
            exp;
         displayLang_String (implode ":="); num_to_display n]`;
   `word_prog_to_display (SUC k) ns (wordLang_ShareInst mop n exp) =
    displayLang_Tuple
        [displayLang_String (implode "share_mem");
            asm_memop_to_display mop;
         num_to_display n; word_exp_to_display exp]`;
   `word_prog_to_display (SUC k) ns (wordLang_MustTerminate prog) =
    displayLang_Item NONE (implode "must_terminate")
        [word_prog_to_display k ns prog]`;
   `word_prog_to_display (SUC k) ns (wordLang_Call a b c d) =
    displayLang_Item NONE (implode "call")
        [word_prog_to_display_ret k ns a;
         (\f opt. match opt with NONE -> empty_item (implode "none")
             | SOME opt' -> displayLang_Item NONE (implode "some") [f
             opt']) (\n. displayLang_String (attach_name ns (SOME n)))
             b;
         (\f xs. displayLang_Tuple (MAP f xs)) num_to_display c;
         word_prog_to_display_handler k ns d]`;
   `word_prog_to_display (SUC k) ns (wordLang_OpCurrHeap b n1 n2) =
    displayLang_Tuple
        [num_to_display n1; displayLang_String (implode ":=");
            displayLang_String (implode "CurrHeap");
         asm_binop_to_display b; num_to_display n2]`;
   `word_prog_to_display (SUC k) ns (wordLang_Seq prog1 prog2) =
        (let xs = append (misc_Append (word_seqs prog1) (word_seqs
            prog2)) in
           separate_lines (implode "seq")
               (word_prog_to_display_list k ns xs))`;
   `word_prog_to_display (SUC k) ns (wordLang_If cmp n reg p1 p2) =
        displayLang_Item NONE (implode "if")
          [displayLang_Tuple [asm_cmp_to_display cmp;
                  num_to_display n;
                  asm_reg_imm_to_display reg];
           word_prog_to_display k ns p1; word_prog_to_display k
               ns p2]`;
   `word_prog_to_display (SUC k) ns (wordLang_Loop ns1 p ns2) =
        displayLang_Item NONE (implode "Loop")
          [num_set_to_display ns1;
           word_prog_to_display k ns p;
           num_set_to_display ns2]`;
   `word_prog_to_display (SUC k) ns (wordLang_Alloc n ms) =
    displayLang_Item NONE (implode "alloc")
        [num_to_display n; num_sets_to_display ms]`;
   `word_prog_to_display (SUC k) ns (wordLang_StoreConsts a b c d ws) =
    displayLang_Item NONE (implode "store_consts")
        [num_to_display a;
         num_to_display b;
         num_to_display c;
         num_to_display d;
         displayLang_Tuple (ws_to_display ws)]`;
   `word_prog_to_display (SUC k) ns (wordLang_Raise n) =
    item_with_num (implode "raise") n`;
   `word_prog_to_display (SUC k) ns (wordLang_Break n) =
    item_with_num (implode "break") n`;
   `word_prog_to_display (SUC k) ns (wordLang_Continue n) =
    item_with_num (implode "continue") n`;
   `word_prog_to_display (SUC k) ns (wordLang_Return n vs) =
         displayLang_Item NONE (implode "return")
           [num_to_display n;
            displayLang_Tuple (MAP num_to_display vs)]`;
   `word_prog_to_display (SUC k) ns wordLang_Tick = empty_item
    (implode "tick")`;
   `word_prog_to_display (SUC k) ns (wordLang_LocValue n1 n2) =
        displayLang_Item NONE (implode "loc_value")
            [displayLang_String (attach_name ns (SOME n1));
            num_to_display n2]`;
   `word_prog_to_display (SUC k) ns (wordLang_Install n1 n2 n3 n4 ms) =
        displayLang_Item NONE (implode "install") (
            APPEND (MAP num_to_display [n1; n2; n3; n4])
                [num_sets_to_display ms])`;
   `word_prog_to_display (SUC k) ns (wordLang_CodeBufferWrite n1 n2) =
        item_with_nums (implode "code_buffer_write") [n1; n2]`;
   `word_prog_to_display (SUC k) ns (wordLang_DataBufferWrite n1 n2) =
        item_with_nums (implode "data_buffer_write") [n1; n2]`;
   `word_prog_to_display (SUC k) ns (wordLang_FFI nm n1 n2 n3 n4 ms) =
        displayLang_Item NONE (implode "ffi") (
            APPEND (CONS (string_imp nm) (MAP num_to_display [n1;
                n2; n3; n4])) [num_sets_to_display ms])`;
   `word_prog_to_display_list k ns [] = []`;
   `word_prog_to_display_list k ns (CONS x xs) =
        (match k with 0 -> [] | SUC k -> CONS
            (word_prog_to_display k ns x) (word_prog_to_display_list
            k ns xs))`;
   `word_prog_to_display_ret k ns NONE = empty_item (implode "tail")`;
   `word_prog_to_display_ret k ns (SOME (vs,ms,prog,n2,n3)) =
        (match k with 0 -> empty_item (implode "...") | SUC k ->
        displayLang_Item NONE (implode "returning")
            [displayLang_Tuple [displayLang_Tuple (MAP num_to_display
            vs); num_sets_to_display ms;
            word_prog_to_display k ns prog;
            displayLang_String (attach_name ns (SOME n2));
            num_to_display n3]])`;
   `word_prog_to_display_handler k ns NONE = empty_item (implode
    "no_handler")`;
   `word_prog_to_display_handler k ns (SOME (n1,prog,n2,n3)) =
        (match k with 0 -> empty_item (implode "...") | SUC k ->
        displayLang_Item NONE (implode "handler") [displayLang_Tuple
            [num_to_display n1;
            word_prog_to_display k ns prog;
            displayLang_String (attach_name ns (SOME n2));
            num_to_display n3]])`];;

let word_fun_to_display_def = new_definition
  `word_fun_to_display names (n,argc,body) =
     displayLang_Tuple [displayLang_String (implode "func");
            displayLang_String (attach_name names (SOME n));
            displayLang_Tuple (list_of_seq (\n. num_to_display (2 *
              n)) argc);
            word_prog_to_display 1000000000 names body]`;;

(* tap configuration *)

let tap_config_FIELDS = define_record "tap_config"
  ["explore_flag","bool"];;

let default_tap_config_def = new_definition
  `default_tap_config = mk_tap_config F`;;

(* ------------------------- *)

let map_to_append_def,map_to_append_ind = define_rec
  [`map_to_append f [] = misc_Nil`;
   `map_to_append f (CONS x xs) = misc_Append (misc_List (f x))
    (map_to_append f xs)`];;

let source_to_strs_def = new_definition
  `source_to_strs decs =
     map_to_append (str_tree_to_strs (implode "\n\n") o
                    display_to_str_tree o
                    source_to_display_dec) decs`;;

let flat_to_strs_def = new_definition
  `flat_to_strs (decs:flatLang_exp list) =
     map_to_append (str_tree_to_strs (implode "\n\n") o
                    display_to_str_tree o
                    flat_to_display) decs`;;

let clos_to_strs_def = new_definition
  `clos_to_strs (decs,funs) =
     (let names = get_src_names (APPEND decs (MAP (SND o SND) funs))
       LN in
       misc_Append (map_to_append (str_tree_to_strs (implode "\n\n")
         o
                              display_to_str_tree o
                              clos_dec_to_display names) decs)
              (map_to_append (str_tree_to_strs (implode "\n\n") o
                              display_to_str_tree o
                              clos_fun_to_display names) funs))`;;

let bvl_to_strs_def = new_definition
  `bvl_to_strs names xs =
     map_to_append (str_tree_to_strs (implode "\n\n") o
                    display_to_str_tree o
                    bvl_fun_to_display names) xs`;;

(* HOL4 presLangScript.sml:1513-1521: the ML values that the
   definitions below antiquote *)

let bvi_to_strs_def = new_definition
  `bvi_to_strs names xs =
     map_to_append (str_tree_to_strs (implode "\n\n") o
                    display_to_str_tree o
                    bvi_fun_to_display names) xs`;;

(* HOL4 presLangScript.sml:1530-1538: the ML values that the
   definitions below antiquote *)

let data_to_strs_def = new_definition
  `data_to_strs names xs =
     map_to_append (str_tree_to_strs (implode "\n\n") o
                    display_to_str_tree o
                    data_fun_to_display names) xs`;;

(* HOL4 presLangScript.sml:1547-1555: the ML values that the
   definitions below antiquote *)

let word_to_strs_def = new_definition
  `word_to_strs names xs =
     map_to_append (str_tree_to_strs (implode "\n\n") o
                    display_to_str_tree o
                    word_fun_to_display names) xs`;;

let stack_to_strs_def = new_definition
  `stack_to_strs names xs =
     map_to_append (str_tree_to_strs (implode "\n\n") o
                    display_to_str_tree o
                    stack_fun_to_display names) xs`;;

let lab_to_strs_def = new_definition
  `lab_to_strs names xs =
     map_to_append (str_tree_to_strs (implode "\n\n") o
                    display_to_str_tree o
                    lab_fun_to_display names) xs`;;

(* HOL4 presLangScript.sml:1578-1586: the ML values that the
   definitions below antiquote *)

(*

val names_tm = “(insert 50 «foo» (insert 60 «bar» LN))”

val data_prog_tm =
    “[(50,2,Seq (Move 5 1) $
            Seq (Assign 3 Add [0;1] NONE) $
            Seq (Assign 6 Sub [5;3] NONE) $ Return 6);
      (60n,2n,Skip)]”

val _ = data_to_strs data_prog_tm names_tm |> print_strs

*)
