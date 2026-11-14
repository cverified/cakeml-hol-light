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
  ["ast"; "bvi"; "bvl"; "closLang"; "clos_to_bvl"; "dataLang"; "displayLang";
   "flatLang"; "labLang"; "mlint"; "mloption"; "source_to_flat"; "stackLang";
   "wordLang"];;

(* basics *)

let empty_item_def = new_definition
  `empty_item name = display_String name`;;

let num_to_display_def = new_definition
  `num_to_display (n:num) = display_String (num_to_str n)`;;

let int_to_display_def = new_definition
  `int_to_display (i:int) = display_String (mlint_toString i)`;;

let string_imp_def = new_definition
  `string_imp s = display_String s`;;

let item_with_num_def = new_definition
  `item_with_num name n = display_Item NONE name [num_to_display n]`;;

let item_with_nums_def = new_definition
  `item_with_nums name ns = display_Item NONE name (MAP num_to_display ns)`;;

let bool_to_display_def = new_definition
  `bool_to_display b = empty_item (if b then (implode "True") else (implode
  "False"))`;;

let num_to_hex_def,num_to_hex_ind = assume_definition_rec
  "termination (CHEAT_TAC)"
  `num_to_hex n = APPEND (if n < 16 then [] else num_to_hex (n DIV 16))
     (num_to_hex_digit (n MOD 16))`;;

let separate_lines_def = new_definition
  `separate_lines name xs = display_List (CONS (display_String name) xs)`;;

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
  `item_with_word name w = display_Item NONE name [word_to_display w]`;;

(* the clauses in two quotations: w is word8 and word64, which one quotation
   cannot typecheck *)
let lit_to_display_def = define_cases_clauses
  [`(lit_to_display (ast_IntLit i) =
        display_Item NONE (implode "IntLit") [empty_item
            (mlint_toString i)]) /\
    (lit_to_display (ast_Char c) =
        display_Item NONE (implode "Char") [empty_item (implode (APPEND
            (APPEND "#\"" [c]) "\""))]) /\
    (lit_to_display (ast_StrLit s) =
        display_Item NONE (implode "StrLit") [string_imp s]) /\
    (lit_to_display (ast_Word8 w) =
        display_Item NONE (implode "Word8") [word_to_display w])`;
   `(lit_to_display (ast_Word64 w) =
        display_Item NONE (implode "Word64") [word_to_display w]) /\
    (lit_to_display (ast_Float64 w) =
        display_Item NONE (implode "Float64") [word_to_display w])`];;

(* HOL4 presLangScript.sml:105: the overload list_to_display, which the port
   expands *)

(* HOL4 presLangScript.sml:107-110: the overload option_to_display, which
   the port expands *)
(* source *)

let fp_cmp_to_display_def = new_definition
  `fp_cmp_to_display cmp = match cmp with FP_Less -> empty_item (implode
  "FP_Less")
     | FP_LessEqual -> empty_item (implode "FP_LessEqual")
     | FP_Greater -> empty_item (implode "FP_Greater")
     | FP_GreaterEqual -> empty_item (implode "FP_GreaterEqual")
     | FP_Equal -> empty_item (implode "FP_Equal")`;;

let fp_uop_to_display_def = new_definition
  `fp_uop_to_display op = match op with fpSem_FP_Abs -> empty_item (implode
  "FP_Abs")
     | fpSem_FP_Neg -> empty_item (implode "FP_Neg")
     | fpSem_FP_Sqrt -> empty_item (implode "FP_Sqrt")`;;

let fp_bop_to_display_def = new_definition
  `fp_bop_to_display op = match op with fpSem_FP_Add -> empty_item (implode
  "FP_Add")
     | fpSem_FP_Sub -> empty_item (implode "FP_Sub")
     | fpSem_FP_Mul -> empty_item (implode "FP_Mul")
     | fpSem_FP_Div -> empty_item (implode "FP_Div")`;;

let fp_top_to_display_def = new_definition
  `fp_top_to_display op =
     match op with FP_Fma -> empty_item (implode "FP_Fma")`;;

let word_size_to_display_def = define_cases
  `(word_size_to_display ast_W8 = empty_item (implode "W8")) /\
   (word_size_to_display ast_W64 = empty_item (implode "W64"))`;;

let opb_to_display_def = define_cases
  `(opb_to_display ast_Lt = empty_item (implode "Lt")) /\
   (opb_to_display ast_Gt = empty_item (implode "Gt")) /\
   (opb_to_display ast_Leq = empty_item (implode "Leq")) /\
   (opb_to_display ast_Geq = empty_item (implode "Geq"))`;;

let opw_to_display_def = define_cases
  `(opw_to_display backend_common_Andw = empty_item (implode "Andw")) /\
   (opw_to_display backend_common_Orw = empty_item (implode "Orw")) /\
   (opw_to_display backend_common_Xor = empty_item (implode "Xor")) /\
   (opw_to_display backend_common_Add = empty_item (implode "Add")) /\
   (opw_to_display backend_common_Sub = empty_item (implode "Sub"))`;;

let shift_to_display_def = define_cases
  `(shift_to_display Lsl = empty_item (implode "Lsl")) /\
   (shift_to_display Lsr = empty_item (implode "Lsr")) /\
   (shift_to_display Asr = empty_item (implode "Asr")) /\
   (shift_to_display Ror = empty_item (implode "Ror"))`;;

let thunk_mode_to_display_def = define_cases
  `(thunk_mode_to_display Evaluated = empty_item (implode "Evaluated")) /\
   (thunk_mode_to_display NotEvaluated = empty_item (implode
    "NotEvaluated"))`;;

let thunk_op_to_display_def = define_cases
  `(thunk_op_to_display (AllocThunk m) =
        display_Item NONE (implode "AllocThunk") [thunk_mode_to_display
            m]) /\
   (thunk_op_to_display (UpdateThunk m) =
        display_Item NONE (implode "UpdateThunk")
            [thunk_mode_to_display m]) /\
   (thunk_op_to_display ForceThunk = empty_item (implode "ForceThunk"))`;;

let test_to_display_def = define_cases
  `(test_to_display ast_Equal = empty_item (implode "Equal")) /\
   (test_to_display (ast_Compare cmp) = display_Item NONE (implode
    "Compare") [opb_to_display cmp]) /\
   (test_to_display (ast_AltCompare cmp) = display_Item NONE (implode
    "AltCompare") [opb_to_display cmp])`;;

let arith_to_display_def = define_cases
  `(arith_to_display ast_Add = empty_item (implode "Add")) /\
   (arith_to_display ast_Sub = empty_item (implode "Sub")) /\
   (arith_to_display ast_Mul = empty_item (implode "Mul")) /\
   (arith_to_display ast_Div = empty_item (implode "Div")) /\
   (arith_to_display ast_Mod = empty_item (implode "Mod")) /\
   (arith_to_display ast_And = empty_item (implode "And")) /\
   (arith_to_display ast_Xor = empty_item (implode "Xor")) /\
   (arith_to_display ast_Or = empty_item (implode "Or")) /\
   (arith_to_display ast_Neg = empty_item (implode "Neg")) /\
   (arith_to_display ast_Not = empty_item (implode "Not")) /\
   (arith_to_display ast_Abs = empty_item (implode "Abs")) /\
   (arith_to_display ast_Sqrt = empty_item (implode "Sqrt")) /\
   (arith_to_display ast_FMA = empty_item (implode "FMA"))`;;

let prim_type_to_display_def = new_definition
  `prim_type_to_display x1 =
   match x1 with
     ast_BoolT -> empty_item (implode "BoolT")
   | ast_IntT -> empty_item (implode "IntT")
   | ast_CharT -> empty_item (implode "CharT")
   | ast_StrT -> empty_item (implode "StrT")
   | ast_Float64T -> empty_item (implode "Float64T")
   | ast_WordT ast_W8 -> empty_item (implode "WordT_W8")
   | ast_WordT ast_W64 -> empty_item (implode "WordT_W64")`;;

let lop_to_display_def = define_cases
  `(lop_to_display Andalso = empty_item (implode "Andalso")) /\
   (lop_to_display Orelse = empty_item (implode "Orelse"))`;;

let op_to_display_def = new_definition
  `op_to_display (p:ast_op) =
   match p with ast_Shift ws sh num' -> display_Item NONE (implode "Shift")
                             [word_size_to_display ws;
                              shift_to_display sh;
                              num_to_display num']
   | ast_Arith a ty -> display_Item NONE (implode "Arith")
                          [arith_to_display a;
                           prim_type_to_display ty]
   | ast_FromTo ty1 ty2 -> display_Item NONE (implode "FromTo")
                          [prim_type_to_display ty1;
                           prim_type_to_display ty2]
   | ast_Test test ty -> display_Item NONE (implode "Test")
                          [test_to_display test;
                           prim_type_to_display ty]
   | ast_Equality -> empty_item (implode "Equality")
   | ast_Opapp -> empty_item (implode "Opapp")
   | ast_Opassign -> empty_item (implode "Opassign")
   | ast_Opref -> empty_item (implode "Opref")
   | ast_Opderef -> empty_item (implode "Opderef")
   | ast_Aw8alloc -> empty_item (implode "Aw8alloc")
   | ast_Aw8sub -> empty_item (implode "Aw8sub")
   | ast_Aw8length -> empty_item (implode "Aw8length")
   | ast_Aw8update -> empty_item (implode "Aw8update")
   | ast_CopyStrStr -> empty_item (implode "CopyStrStr")
   | ast_CopyStrAw8 -> empty_item (implode "CopyStrAw8")
   | ast_CopyAw8Str -> empty_item (implode "CopyAw8Str")
   | ast_CopyAw8Aw8 -> empty_item (implode "CopyAw8Aw8")
   | ast_Implode -> empty_item (implode "Implode")
   | ast_Explode -> empty_item (implode "Explode")
   | ast_Strsub -> empty_item (implode "Strsub")
   | ast_Strlen -> empty_item (implode "Strlen")
   | ast_Strcat -> empty_item (implode "Strcat")
   | ast_VfromList -> empty_item (implode "VfromList")
   | ast_Vsub -> empty_item (implode "Vsub")
   | ast_Vsub_unsafe -> empty_item (implode "Vsub_unsafe")
   | ast_Vlength -> empty_item (implode "Vlength")
   | ast_Aalloc -> empty_item (implode "Aalloc")
   | ast_AallocEmpty -> empty_item (implode "AallocEmpty")
   | ast_AallocFixed -> empty_item (implode "AallocFixed")
   | ast_Asub -> empty_item (implode "Asub")
   | ast_Alength -> empty_item (implode "Alength")
   | ast_Aupdate -> empty_item (implode "Aupdate")
   | ast_Asub_unsafe -> empty_item (implode "Asub_unsafe")
   | ast_Aupdate_unsafe -> empty_item (implode "Aupdate_unsafe")
   | ast_Aw8sub_unsafe -> empty_item (implode "Aw8sub_unsafe")
   | ast_Aw8update_unsafe -> empty_item (implode "Aw8update_unsafe")
   | ast_XorAw8Str_unsafe -> empty_item (implode "XorAw8Str_unsafe")
   | ast_ListAppend -> empty_item (implode "ListAppend")
   | ast_ConfigGC -> empty_item (implode "ConfigGC")
   | ast_FFI v35 -> empty_item (implode "FFI v35")
   | ast_Eval -> empty_item (implode "Eval")
   | ast_Env_id -> empty_item (implode "Env_id")
   | ast_ThunkOp t -> thunk_op_to_display t`;;

(* the clauses in two quotations: n is 'n and 'm, which one quotation cannot
   typecheck *)
let id_to_display_def,id_to_display_ind = define_rec_clauses
  [`id_to_display (Short n) =
      display_Item NONE (implode "Short") [display_String n]`;
   `id_to_display (Long n i) =
      display_Item NONE (implode "Long") [display_String n;
          id_to_display i]`];;

let ast_t_to_display_def,ast_t_to_display_ind = assume_definition_rec
  "termination (CHEAT_TAC)"
  `(ast_t_to_display c =
      match c with Atvar n -> display_Item NONE (implode "Atvar")
          [display_String n]
      | Atfun t1 t2 -> display_Item NONE (implode "Atfun")
          [ast_t_to_display t1; ast_t_to_display t2]
      | Attup ts -> display_Item NONE (implode "Attup") [display_Tuple
          (ast_t_to_display_list ts)]
      | Atapp ts id' -> display_Item NONE (implode "Attup") [display_Tuple
          (ast_t_to_display_list ts);
                              id_to_display id']) /\
   (ast_t_to_display_list [] = []) /\
   (ast_t_to_display_list (CONS x xs) = CONS (ast_t_to_display x)
    (ast_t_to_display_list xs))`;;

let pat_to_display_def,pat_to_display_ind = assume_definition_rec
  "termination (CHEAT_TAC)"
  `(pat_to_display (c:ast_pat) =
      match c with ast_Pany -> display_Item NONE (implode "Pany") []
      | ast_Pvar v -> display_Item NONE (implode "Pvar") [display_String v]
      | ast_Plit l -> display_Item NONE (implode "Plit") [lit_to_display l]
      | ast_Pcon opt_id pats ->
          display_Item NONE (implode "Pcon") [(\f opt. match opt with NONE
              -> empty_item (implode "none")
              | SOME opt' -> display_Item NONE (implode "some") [f opt'])
                  id_to_display opt_id;
                            display_Tuple (pat_to_display_list pats)]
      | ast_Pas t v -> display_Item NONE (implode "Pas") [pat_to_display t;
          display_String v]
      | ast_Pref t -> display_Item NONE (implode "Pref") [pat_to_display t]
      | ast_Ptannot x y -> display_Item NONE (implode "Ptannot")
          [pat_to_display x; ast_t_to_display y]) /\
   (pat_to_display_list [] = []) /\
   (pat_to_display_list (CONS x xs) = CONS (pat_to_display x)
    (pat_to_display_list xs))`;;

let exp_to_display_def,exp_to_display_ind = assume_definition_rec_clauses
  "termination (CHEAT_TAC)"
  [`exp_to_display (c:ast_exp) =
      match c with ast_Lit l -> display_Item NONE (implode "Lit")
          [lit_to_display l]
      | ast_Raise e -> display_Item NONE (implode "Raise") [exp_to_display
          e]
      | ast_Con opt_id es -> display_Item NONE (implode "Con") [(\f opt.
          match opt with NONE -> empty_item (implode "none")
              | SOME opt' -> display_Item NONE (implode "some") [f opt'])
                  id_to_display opt_id;
                              display_Tuple (exp_to_display_list es)]
      | ast_Var id' -> display_Item NONE (implode "Var") [id_to_display
          id']
      | ast_Fun n e -> display_Item NONE (implode "Fun") [display_String n;
          exp_to_display e]
      | ast_App op es -> display_Item NONE (implode "App") (CONS
          (op_to_display op)
                              (exp_to_display_list es))
      | ast_Log lop e1 e2 -> display_Item NONE (implode "Log")
          [lop_to_display lop;
                              exp_to_display e1;
                              exp_to_display e2]
      | ast_If e1 e2 e3 -> display_Item NONE (implode "If") [exp_to_display
          e1;
                              exp_to_display e2;
                              exp_to_display e3]
      | ast_Let n_opt e1 e2 -> display_Item NONE (implode "Let")
          [(\f opt. match opt with NONE -> empty_item (implode "none")
              | SOME opt' -> display_Item NONE (implode "some") [f opt'])
                  display_String n_opt;
           exp_to_display e1;
           exp_to_display e2]
      | ast_Mat e pats ->
          display_Item NONE (implode "Mat")
          [exp_to_display e;
           display_Tuple (pat_exp_to_display_list pats)]
      | ast_Handle e pats ->
          display_Item NONE (implode "Handle")
          [exp_to_display e;
           display_Tuple (pat_exp_to_display_list pats)]
      | ast_Letrec fns e ->
          display_Item NONE (implode "Letrec")
          [display_Tuple (fun_to_display_list fns);
           exp_to_display e]
      | ast_Tannot e _ -> display_Item NONE (implode "Tannot")
          [exp_to_display e]
      | ast_Lannot e _ -> display_Item NONE (implode "Lannot")
          [exp_to_display e]`;
   `exp_to_display_list [] = []`;
   `exp_to_display_list (CONS x xs) = CONS (exp_to_display x)
    (exp_to_display_list xs)`;
   `pat_exp_to_display_list [] = []`;
   `pat_exp_to_display_list (CONS (p,e) xs) = CONS (display_Tuple
    [pat_to_display p; exp_to_display e])
        (pat_exp_to_display_list xs)`;
   `fun_to_display_list [] = []`;
   `fun_to_display_list (CONS (m,n,e) xs) = CONS (display_Tuple [display_String
    m;
               display_String n;
               exp_to_display e])
        (fun_to_display_list xs)`];;

let source_to_display_dec_def,source_to_display_dec_ind = assume_definition_rec
  "termination (CHEAT_TAC)"
  `(source_to_display_dec (d:dec) =
      match d with Dlet _ pat e -> display_Item NONE (implode "Dlet")
          [pat_to_display pat; exp_to_display e]
      | Dletrec _ fns -> display_Item NONE (implode "Dletrec")
                              (MAP (\(m,n,e). display_Tuple [display_String
                                  m;
                              display_String n;
                              exp_to_display e]) fns)
      | Dtype _ ts -> display_Item NONE (implode "Dtype") (MAP (\(ns,n,z).
                        display_Tuple [display_Tuple (MAP display_String
                            ns);
                              display_String n;
                              display_Tuple (MAP (\(n,tys). display_Tuple
                                  [display_String n;
                              display_Tuple (MAP ast_t_to_display tys)])
                                  z)]) ts)
      | Dtabbrev _ ns n ty ->
          display_Item NONE (implode "Dtabbrev") [display_Tuple (MAP
              display_String ns);
                              display_String n;
                              ast_t_to_display ty]
      | Dexn _ n tys -> display_Item NONE (implode "Dexn") [display_String
          n;
                              display_Tuple (MAP ast_t_to_display tys)]
      | Dmod n ds -> display_Item NONE (implode "Dmod") [display_String n;
                              display_Tuple (source_to_display_dec_list
                                  ds)]
      | Dlocal xs ys -> display_Item NONE (implode "Dlocal") [display_Tuple
          (source_to_display_dec_list xs);
                              display_Tuple (source_to_display_dec_list
                                  ys)]
      | Denv n -> display_Item NONE (implode "Denv") [display_String n]) /\
   (source_to_display_dec_list [] = []) /\
   (source_to_display_dec_list (CONS x xs) = CONS (source_to_display_dec
    x) (source_to_display_dec_list xs))`;;

(* flatLang *)

(* [local] *)
let MEM_pat_size = prove
 (`!pats a. MEM a (pats:flat_pat list) ==> pattern_semantics_pat_size a <
  list_size flat_pat_size pats`,
  CHEAT_TAC);;

let opt_con_to_display_def = new_definition
  `opt_con_to_display ocon = match ocon with NONE -> empty_item (implode
  "ConIdNone")
     | SOME (c,NONE) -> item_with_num (implode "ConIdUntyped") c
     | SOME (c,SOME t) -> item_with_nums (implode "ConIdTyped") [c; t]`;;

let flat_pat_to_display_def,flat_pat_to_display_ind = assume_definition_rec
  "termination (CHEAT_TAC)"
  `(flat_pat_to_display p =
        match p with flat_Pvar varN -> display_Item NONE (implode "Pvar")
            [string_imp varN]
           | flat_Pany -> empty_item (implode "Pany")
           | flat_Plit lit -> display_Item NONE (implode "Plit")
               [lit_to_display lit]
           | flat_Pcon id' pats -> display_Item NONE (implode "Pcon")
                (flat_pat_to_display_list pats)
           | flat_Pas pat varN -> display_Item NONE (implode "Pas")
               [flat_pat_to_display pat;
                              string_imp varN]
           | flat_Pref pat -> display_Item NONE (implode "Pref")
               [flat_pat_to_display pat]) /\
   (flat_pat_to_display_list [] = []) /\
   (flat_pat_to_display_list (CONS x xs) = CONS (flat_pat_to_display x)
    (flat_pat_to_display_list xs))`;;

let flat_op_to_display_def = new_definition
  `flat_op_to_display op = match op with flat_Src ast_op -> op_to_display
  ast_op
     | flat_GlobalVarAlloc n -> item_with_num (implode "GlobalVarAlloc") n
     | flat_GlobalVarInit n -> item_with_num (implode "GlobalVarInit") n
     | flat_GlobalVarLookup n -> item_with_num (implode "GlobalVarLookup") n
     | flat_TagLenEq n1 n2 -> item_with_nums (implode "TagLenEq") [n1; n2]
     | flat_LenEq n1 -> item_with_nums (implode "LenEq") [n1]
     | flat_El n -> item_with_num (implode "El") n
     | flat_Id -> empty_item (implode "Id")`;;

(* [local] *)
let MEM_funs_size = prove
 (`!fs v1 v2 e. MEM (v1,v2,e) fs ==> flat_exp_size e < list_size (pair_size
  mlstring_size (pair_size mlstring_size flat_exp_size)) fs`,
  CHEAT_TAC);;

(* [local] *)
let MEM_exps_size = prove
 (`!exps e. MEM e exps ==> flat_exp_size e < list_size flat_exp_size exps`,
  CHEAT_TAC);;

(* [local] *)
let MEM_pats_size = prove
 (`!pats p e. MEM (p,e) pats ==> flat_exp_size e < list_size (pair_size
  flat_pat_size flat_exp_size) pats`,
  CHEAT_TAC);;

let add_name_hint_def = new_definition
  `add_name_hint prefix name_hint =
     mlstring_concat [prefix; (implode "<"); name_hint; (implode ">")]`;;

let flat_to_display_def,flat_to_display_ind = define_shaped_rec_clauses
  "maplist>maplist>maplist>nested"
  [`flat_to_display (flat_Raise tra exp) =
        display_Item (SOME tra) (implode "raise") [flat_to_display exp]`;
   `flat_to_display (flat_Handle tra exp pes) =
        display_Item (SOME tra) (implode "handle") (
            CONS (flat_to_display exp) (pat_flat_to_display_list pes))`;
   `flat_to_display (flat_Lit tra lit) = display_Item (SOME tra) (implode
    "lit") []`;
   `flat_to_display (flat_Con tra id_opt exps) =
        display_Item (SOME tra) (implode "con") (
            CONS (opt_con_to_display id_opt) (flat_to_display_list
                exps))`;
   `flat_to_display (flat_Var_local tra varN) =
        display_Item (SOME tra) (implode "var_local") [string_imp varN]`;
   `flat_to_display (flat_Fun name_hint varN exp) =
        display_Item (SOME backend_common_None) (add_name_hint (implode
            "fun") name_hint)
          [string_imp varN; flat_to_display exp]`;
   `flat_to_display (flat_App tra op exps) =
        display_Item (SOME tra) (implode "app") (CONS
            (flat_op_to_display op) (flat_to_display_list exps))`;
   `flat_to_display (flat_If tra exp1 exp2 exp3) =
        display_Item (SOME tra) (implode "if") [flat_to_display exp1;
            flat_to_display exp2;
            flat_to_display exp3]`;
   `flat_to_display (flat_Mat tra exp pes) =
        display_Item (SOME tra) (implode "mat") (
            CONS (flat_to_display exp) (pat_flat_to_display_list pes))`;
   `flat_to_display (flat_Let tra varN_opt exp1 exp2) =
        display_Item (SOME tra) (implode "let") [(\f opt. match opt with
            NONE -> empty_item (implode "none")
              | SOME opt' -> display_Item NONE (implode "some") [f opt'])
                  string_imp varN_opt;
            flat_to_display exp1; flat_to_display exp2]`;
   `flat_to_display (flat_Letrec name_hint funs exp) =
        display_Item (SOME backend_common_None) (add_name_hint (implode
            "letrec") name_hint)
            [display_Tuple (fun_flat_to_display_list funs);
                flat_to_display exp]`;
   `flat_to_display_list [] = []`;
   `flat_to_display_list (CONS x xs) = CONS (flat_to_display x)
    (flat_to_display_list xs)`;
   `pat_flat_to_display_list [] = []`;
   `pat_flat_to_display_list (CONS (pat,exp) xs) = CONS (display_Tuple
    [flat_pat_to_display pat; flat_to_display exp])
    (pat_flat_to_display_list xs)`;
   `fun_flat_to_display_list [] = []`;
   `fun_flat_to_display_list (CONS (v1,v2,e) xs) = CONS (display_Tuple
    [string_imp v1; string_imp v2; flat_to_display e])
            (fun_flat_to_display_list xs)`];;

(* clos to displayLang *)

(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 presLangScript.sml:541-543: the tactic that proves the termination *)
let num_to_varn_aux_def,num_to_varn_aux_ind = define_wf
  `MEASURE I`
  `num_to_varn_aux n =
     if n < 26 then [CHR (97 + n)]
     else APPEND (num_to_varn_aux ((n DIV 26) - 1)) ([CHR (97 + (n MOD
       26))])`;;

let num_to_varn_def = new_definition
  `num_to_varn n = implode (num_to_varn_aux n)`;;

let display_num_as_varn_def = new_definition
  `display_num_as_varn n = string_imp (num_to_varn n)`;;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let num_to_varn_list_def,num_to_varn_list_ind = define_wf
  `MEASURE (\(x0,x1). (\n. n) x1)`
  `num_to_varn_list h n =
     if n = 0 then [] else CONS (num_to_varn (h + n)) (num_to_varn_list
       h (n - 1))`;;

let attach_name_def = define_cases
  `(attach_name ns NONE = (implode "none")) /\
   (attach_name ns (SOME d) =
      match sptree_lookup d ns with NONE -> num_to_str d
      | SOME name -> mlstring_concat [name; (implode "@"); num_to_str
          d])`;;

let const_part_to_display_def = define_cases
  `(const_part_to_display (clos_Int i:const_part) =
      display_Item NONE (implode "Int") [int_to_display i]) /\
   (const_part_to_display (clos_Con t vs) =
      display_Item NONE (implode "Con") [num_to_display t;
          display_Tuple (MAP num_to_display vs)]) /\
   (const_part_to_display (clos_Str s) =
      display_Item NONE (implode "Str") [display_String
          (mlstring_concat [implode "\""; s; implode "\""])]) /\
   (const_part_to_display (clos_W64 w) =
      display_Item NONE (implode "W64") [word_to_display w])`;;

(* the termination relation that HOL4 gives is
     MEASURE (\x. match x with INL v -> const_size v | INR v -> list_size
       const_size v)
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
let const_to_display_def,const_to_display_ind = define_rec
  `(const_to_display (ConstInt i:const) =
      display_Item NONE (implode "ConstInt") [int_to_display i]) /\
   (const_to_display (ConstCons t vs) =
      display_Item NONE (implode "ConstCons") [num_to_display t;
          display_Tuple (const_to_display_list vs)]) /\
   (const_to_display (ConstStr s) =
      display_Item NONE (implode "ConstStr") [display_String
          (mlstring_concat [implode "\""; s; implode "\""])]) /\
   (const_to_display (ConstWord64 w) =
      display_Item NONE (implode "ConstWord64") [word_to_display w]) /\
   (const_to_display_list [] = []) /\
   (const_to_display_list (CONS x xs) = CONS (const_to_display x)
    (const_to_display_list xs))`;;

let clos_op_to_display_def = new_definition
  `clos_op_to_display ns op = match op with clos_GlobOp (clos_Global num') ->
  item_with_num (implode "Global") num'
     | clos_GlobOp (clos_SetGlobal num') -> item_with_num (implode
       "SetGlobal") num'
     | clos_GlobOp clos_AllocGlobal -> display_String (implode
       "AllocGlobal")
     | clos_GlobOp clos_GlobalsPtr -> display_String (implode "GlobalsPtr")
     | clos_GlobOp clos_SetGlobalsPtr -> display_String (implode
       "SetGlobalsPtr")
     | clos_BlockOp (clos_Cons num') -> item_with_num (implode "Cons") num'
     | clos_BlockOp (clos_ElemAt num') -> item_with_num (implode "ElemAt")
       num'
     | clos_BlockOp (clos_TagLenEq n1 n2) -> item_with_nums (implode
       "TagLenEq") [n1; n2]
     | clos_BlockOp (clos_BoolTest test) -> display_Item NONE (implode
       "BoolTest") [test_to_display test]
     | clos_BlockOp clos_BoolNot -> display_String (implode "BoolNot")
     | clos_BlockOp (clos_LenEq num') -> item_with_num (implode "LenEq")
       num'
     | clos_BlockOp (clos_TagEq num') -> item_with_num (implode "TagEq")
       num'
     | clos_BlockOp clos_LengthBlock -> display_String (implode
       "LengthBlock")
     | clos_BlockOp clos_BoundsCheckBlock -> display_String (implode
       "BoundsCheckBlock")
     | clos_BlockOp (clos_ConsExtend num') -> item_with_num (implode
       "ConsExtend") num'
     | clos_BlockOp (clos_FromList num') -> item_with_num (implode
       "FromList") num'
     | clos_BlockOp clos_ListAppend -> display_String (implode "ListAppend")
     | clos_BlockOp (clos_Constant c) -> display_Item NONE (implode
       "Constant") [const_to_display c]
     | clos_BlockOp clos_Equal -> display_String (implode "Equal")
     | clos_BlockOp (clos_EqualConst c) -> display_Item NONE (implode
       "EqualConst") [const_part_to_display c]
     | clos_BlockOp (clos_Build bs) -> display_Item NONE (implode "Build")
       (MAP const_part_to_display bs)
     | clos_MemOp clos_Ref -> display_String (implode "Ref")
     | clos_MemOp clos_Update -> display_String (implode "Update")
     | clos_MemOp clos_El -> display_String (implode "El")
     | clos_MemOp clos_Length -> display_String (implode "Length")
     | clos_MemOp clos_LengthByte -> display_String (implode "LengthByte")
     | clos_MemOp (clos_RefByte b) -> display_Item NONE (implode "RefByte")
       [bool_to_display b]
     | clos_MemOp clos_RefArray -> display_String (implode "RefArray")
     | clos_MemOp clos_DerefByte -> display_String (implode "DerefByte")
     | clos_MemOp clos_UpdateByte -> display_String (implode "UpdateByte")
     | clos_MemOp clos_ConcatByteVec -> display_String (implode
       "ConcatByteVec")
     | clos_MemOp (clos_CopyByte b) -> display_Item NONE (implode
       "CopyByte") [bool_to_display b]
     | clos_MemOp clos_FromListByte -> display_String (implode
       "FromListByte")
     | clos_MemOp clos_ToListByte -> display_String (implode "ToListByte")
     | clos_MemOp clos_LengthByteVec -> display_String (implode
       "LengthByteVec")
     | clos_MemOp clos_DerefByteVec -> display_String (implode
       "DerefByteVec")
     | clos_MemOp clos_BoundsCheckArray -> display_String (implode
       "BoundsCheckArray")
     | clos_MemOp (clos_BoundsCheckByte b) -> display_Item NONE (implode
       "BoundsCheckByte") [bool_to_display b]
     | clos_MemOp clos_ConfigGC -> display_String (implode "ConfigGC")
     | clos_MemOp (clos_StringCmp b opb) -> display_Item NONE (implode
       "StringCmp") [bool_to_display b;
                              opb_to_display opb]
     | clos_MemOp clos_XorByte -> display_String (implode "XorByte")
     | clos_MemOp (clos_MutCons tag i) -> item_with_nums (implode "MutCons")
       [tag; i]
     | clos_MemOp clos_UpdateCons -> display_String (implode "UpdateCons")
     | clos_MemOp clos_FinaliseCons -> display_String (implode
       "FinaliseCons")
     | clos_Label num' -> display_Item NONE (implode "Label")
       [display_String (attach_name ns (SOME num'))]
     | clos_FFI s -> display_Item NONE (implode "FFI") [string_imp s]
     | clos_IntOp (clos_Const i) -> display_Item NONE (implode "Const")
       [int_to_display i]
     | clos_IntOp clos_Add -> display_String (implode "Add")
     | clos_IntOp clos_Sub -> display_String (implode "Sub")
     | clos_IntOp clos_Mult -> display_String (implode "Mult")
     | clos_IntOp clos_Div -> display_String (implode "Div")
     | clos_IntOp clos_Mod -> display_String (implode "Mod")
     | clos_IntOp clos_Less -> display_String (implode "Less")
     | clos_IntOp clos_LessEq -> display_String (implode "LessEq")
     | clos_IntOp clos_Greater -> display_String (implode "Greater")
     | clos_IntOp clos_GreaterEq -> display_String (implode "GreaterEq")
     | clos_IntOp (clos_LessConstSmall num') -> item_with_num (implode
       "LessConstSmall") num'
     | clos_WordOp (WordOpw ws op) -> display_Item NONE (implode "WordOp")
                              [word_size_to_display ws;
                              opw_to_display op]
     | clos_WordOp (WordShift ws sh num') -> display_Item NONE (implode
       "WordShift")
                              [word_size_to_display ws;
                              shift_to_display sh;
                              num_to_display num']
     | clos_WordOp (WordTest ws test) -> display_Item NONE (implode
       "WordTest")
                              [word_size_to_display ws;
                              test_to_display test]
     | clos_WordOp WordFromInt -> display_String (implode "WordFromInt")
     | clos_WordOp WordToInt -> display_String (implode "WordToInt")
     | clos_WordOp (WordFromWord b) -> display_Item NONE (implode
       "WordFromWord") [bool_to_display b]
     | clos_WordOp (FP_cmp cmp) -> fp_cmp_to_display cmp
     | clos_WordOp (FP_uop op) -> fp_uop_to_display op
     | clos_WordOp (FP_bop op) -> fp_bop_to_display op
     | clos_WordOp (FP_top op) -> fp_top_to_display op
     | clos_Install -> display_String (implode "Install")
     | clos_ThunkOp t -> thunk_op_to_display t`;;

(* [local] *)
let MEM_clos_exps_size = prove
 (`!exps e. MEM e exps ==> clos_exp_size e < list_size clos_exp_size exps`,
  CHEAT_TAC);;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let commas_def,commas_ind = define_wf
  `MEASURE (\x0. list_size mlstring_size x0)`
  `pres_commas x1 =
   match x1 with
     [] -> (implode "")
   | [x] -> x
   | CONS x xs -> strcat (strcat x (implode ",")) (pres_commas xs)`;;

(* The clos_to_display ns function uses the same approach to de bruijn
   indices as the pat_to_display function *)
(* the clauses in two quotations: es is ((num # exp) list), (_)list and
   (_#_)list; name_hint is mlstring and (mlstring list); xs is (exp list) and
   (_)list, which one quotation cannot typecheck *)
let clos_to_display_def,clos_to_display_ind = assume_definition_rec_clauses
  "termination (CHEAT_TAC)"
  [`(clos_to_display ns h (clos_Var t n) =
        display_Item (SOME t) (implode "var") [display_num_as_varn (h -
            n - 1)]) /\
    (clos_to_display ns h (clos_If t x1 x2 x3) =
        display_Item (SOME t) (implode "if") [clos_to_display ns h x1;
            clos_to_display ns h x2;
            clos_to_display ns h x3]) /\
    (clos_to_display ns h (clos_Let t xs x) =
        separate_lines (implode "let")
            [display_Tuple (clos_to_display_lets ns h (LENGTH xs - 1) xs);
                clos_to_display ns (h + LENGTH xs) x]) /\
    (clos_to_display ns h (clos_Raise t x) =
        display_Item (SOME t) (implode "raise") [clos_to_display ns h
            x]) /\
    (clos_to_display ns h (clos_Tick t x) =
        display_Item (SOME t) (implode "tick") [clos_to_display ns h x]) /\
    (clos_to_display ns h (clos_Handle t x y) =
        display_Item (SOME t) (implode "handle")
            [clos_to_display ns h x; display_num_as_varn h;
                clos_to_display ns (h + 1) y]) /\
    (clos_to_display ns h (clos_Call t ticks dest xs) =
        display_Item (SOME t) (implode "call")
          (APPEND [num_to_display ticks; display_String (attach_name ns
              (SOME dest))]
           (clos_to_display_list ns h xs))) /\
    (clos_to_display ns h (clos_App t opt_n x xs) =
        display_Item (SOME t) (implode "app")
            (APPEND [(\f opt. match opt with NONE -> empty_item (implode
                "none")
              | SOME opt' -> display_Item NONE (implode "some") [f opt'])
                  num_to_display opt_n;
              clos_to_display ns h x] (clos_to_display_list ns h xs))) /\
    (clos_to_display ns h (clos_Fn name_hint n1 n2 vn x) =
        display_Item (SOME backend_common_None) (add_name_hint (implode
            "fn") name_hint)
            [(\f opt. match opt with NONE -> empty_item (implode "none")
              | SOME opt' -> display_Item NONE (implode "some") [f opt'])
                  num_to_display n1;
             (\f opt. match opt with NONE -> empty_item (implode "none")
              | SOME opt' -> display_Item NONE (implode "some") [f opt'])
                  ((\f xs. display_Tuple (MAP f xs)) num_to_display) n2;
             (\f xs. display_Tuple (MAP f xs)) string_imp (num_to_varn_list
                 h vn);
             clos_to_display ns h x]) /\
    (clos_to_display ns h (clos_Op t op xs) =
        display_Item (SOME t) (implode "op") (CONS (clos_op_to_display LN
            op)
            (clos_to_display_list ns h xs))) /\
    (clos_to_display_list ns h [] = []) /\
    (clos_to_display_list ns h (CONS x xs) = CONS (clos_to_display ns h x)
    (clos_to_display_list ns h xs)) /\
    (clos_to_display_lets ns h i [] = []) /\
    (clos_to_display_lets ns h i (CONS x xs) =
          CONS (display_Tuple [display_num_as_varn (h + i);
              display_String (implode "<-"); clos_to_display ns h x])
              (clos_to_display_lets ns h (i - 1) xs)) /\
    (clos_to_display_letrecs ns h i len [] = [])`;
   `(clos_to_display ns h (clos_Letrec name_hint n1 n2 es e) =
        display_Item (SOME backend_common_None) (add_name_hint (implode
            "letrec") (pres_commas name_hint))
            [(\f opt. match opt with NONE -> empty_item (implode "none")
              | SOME opt' -> display_Item NONE (implode "some") [f opt'])
                  num_to_display n1;
             (\f opt. match opt with NONE -> empty_item (implode "none")
              | SOME opt' -> display_Item NONE (implode "some") [f opt'])
                  ((\f xs. display_Tuple (MAP f xs)) num_to_display) n2;
             display_Tuple (clos_to_display_letrecs ns h (LENGTH es - 1)
                 (LENGTH es) es);
             clos_to_display ns h e]) /\
    (clos_to_display_letrecs ns h i len (CONS (vn,e) es) =
        CONS (display_Tuple [display_num_as_varn (h + i);
            (\f xs. display_Tuple (MAP f xs)) string_imp (num_to_varn_list
                ((h + len) - 1) vn);
            clos_to_display ns (h + len + vn) e])
                (clos_to_display_letrecs ns h (i - 1) len es))`];;

let clos_fun_to_display_def = new_definition
  `clos_fun_to_display names (n,argc,body) =
     display_Tuple [display_String (implode "func");
            display_String (attach_name names (SOME n));
            display_Tuple (REVERSE (list_of_seq display_num_as_varn argc));
            clos_to_display names argc body]`;;

let clos_dec_to_display_def = new_definition
  `clos_dec_to_display names dec =
     display_Tuple [display_String (implode "dec");
            clos_to_display names 0 dec]`;;

(* bvl to displayLang *)

(* [local] *)
let MEM_bvl_exps_size = prove
 (`!exps e. MEM e exps ==> bvl_exp_size e < list_size bvl_exp_size exps`,
  CHEAT_TAC);;

(* the termination relation that HOL4 gives is
     MEASURE (\x.
          match x with
            INL (ns,h,x) -> flat_exp_size x
          | INR (INL (ns,h,xs)) -> list_size flat_exp_size xs
          | INR (INR (ns,h,i,xs)) -> list_size flat_exp_size xs)
   which is not one that HOL Light takes here; the one
   below is what the port found for it *)
let bvl_to_display_def,bvl_to_display_ind = define_shaped_wf
  "maplist>measure"
  `MEASURE (sum_measure (\(x0,x1,x2). bvl_exp_size x2) (\(x0,x1,x2,x3).
  bvl_exp_size1 x3))`
  `(bvl_to_display ns h (bvl_Var n) =
        display_Item NONE (implode "var") [display_num_as_varn (h - n -
            1)]) /\
   (bvl_to_display ns h (bvl_If x1 x2 x3) =
        display_Item NONE (implode "if") [bvl_to_display ns h x1;
            bvl_to_display ns h x2;
            bvl_to_display ns h x3]) /\
   (bvl_to_display ns h (bvl_Let xs x) =
        separate_lines (implode "let")
            (APPEND (bvl_to_display_lets ns h (LENGTH xs - 1) xs)
                [bvl_to_display ns (h + LENGTH xs) x])) /\
   (bvl_to_display ns h (bvl_Raise x) =
        display_Item NONE (implode "raise") [bvl_to_display ns h x]) /\
   (bvl_to_display ns h (bvl_Tick x) =
        display_Item NONE (implode "tick") [bvl_to_display ns h x]) /\
   (bvl_to_display ns h (bvl_Handle x y) =
        display_Item NONE (implode "handle")
            [bvl_to_display ns h x; display_num_as_varn h;
                bvl_to_display ns (h + 1) y]) /\
   (bvl_to_display ns h (bvl_Call ticks dest xs) =
        display_Item NONE (implode "call")
             (CONS (display_String (attach_name ns dest))
              (bvl_to_display_list ns h xs))) /\
   (bvl_to_display ns h (bvl_Force loc n) =
        display_Item NONE (implode "force")
             [display_num_as_varn (h - n - 1); display_String
                 (attach_name ns (SOME loc))]) /\
   (bvl_to_display ns h (bvl_Op op xs) =
        display_Item NONE (implode "op") (CONS (clos_op_to_display ns op)
                              (bvl_to_display_list ns h xs))) /\
   (bvl_to_display_list ns h [] = []) /\
   (bvl_to_display_list ns h (CONS x xs) = CONS (bvl_to_display ns h x)
    (bvl_to_display_list ns h xs)) /\
   (bvl_to_display_lets ns h i [] = []) /\
   (bvl_to_display_lets ns h i (CONS x xs) =
        CONS (display_Tuple [display_num_as_varn (h + i);
            display_String (implode "<-"); bvl_to_display ns h x])
            (bvl_to_display_lets ns h (i - 1) xs))`;;

let bvl_fun_to_display_def = new_definition
  `bvl_fun_to_display names (n,argc,body) =
     display_Tuple [display_String (implode "func");
            display_String (attach_name names (SOME n));
            display_Tuple (REVERSE (list_of_seq display_num_as_varn argc));
            bvl_to_display names argc body]`;;

(* bvi to displayLang *)

(* [local] *)
let MEM_bvi_exps_size = prove
 (`!exps e. MEM e exps ==> bvi_exp_size e < list_size bvi_exp_size exps`,
  CHEAT_TAC);;

(* the clauses in two quotations: dest is (num option) and num; xs is (exp
   list) and (_)list, which one quotation cannot typecheck *)
let bvi_to_display_def,bvi_to_display_ind = assume_definition_rec_clauses
  "termination (CHEAT_TAC)"
  [`(bvi_to_display ns h (bvi_Var n) =
        display_Item NONE (implode "var") [display_num_as_varn (h - n -
            1)]) /\
    (bvi_to_display ns h (bvi_If x1 x2 x3) =
        display_Item NONE (implode "if") [bvi_to_display ns h x1;
            bvi_to_display ns h x2;
            bvi_to_display ns h x3]) /\
    (bvi_to_display ns h (bvi_Let xs x) =
        separate_lines (implode "let")
            (APPEND (bvi_to_display_lets ns h (LENGTH xs - 1) xs)
                [bvi_to_display ns (h + LENGTH xs) x])) /\
    (bvi_to_display ns h (bvi_Raise x) =
        display_Item NONE (implode "raise") [bvi_to_display ns h x]) /\
    (bvi_to_display ns h (bvi_Tick x) =
        display_Item NONE (implode "tick") [bvi_to_display ns h x]) /\
    (bvi_to_display ns h (bvi_Call ticks dest xs handler) =
        display_Item NONE (implode "call")
             (APPEND (CONS (display_String (attach_name ns dest))
              (bvi_to_display_list ns h xs))
              (match handler with NONE -> []
               | SOME e -> [display_Item NONE (implode "handler")
                   [display_num_as_varn h;
                              empty_item (implode "->");
                              bvi_to_display ns (h + 1) e]]))) /\
    (bvi_to_display ns h (bvi_Force loc n) =
        display_Item NONE (implode "force")
             [display_num_as_varn (h - n - 1); display_String
                 (attach_name ns (SOME loc))]) /\
    (bvi_to_display ns h (bvi_Op op xs) =
        display_Item NONE (implode "op") (CONS (clos_op_to_display ns op)
                              (bvi_to_display_list ns h xs))) /\
    (bvi_to_display ns h (bvi_Return xs) =
        display_Item NONE (implode "return") (bvi_to_display_list ns h
            xs)) /\
    (bvi_to_display_list ns h [] = []) /\
    (bvi_to_display_list ns h (CONS x xs) = CONS (bvi_to_display ns h x)
    (bvi_to_display_list ns h xs)) /\
    (bvi_to_display_lets ns h i [] = []) /\
    (bvi_to_display_lets ns h i (CONS x xs) =
        CONS (display_Tuple [display_num_as_varn (h + i);
            display_String (implode "<-"); bvi_to_display ns h x])
            (bvi_to_display_lets ns h (i - 1) xs))`;
   `bvi_to_display ns h (bvi_LetCall rets ticks dest xs y) =
        separate_lines (implode "letcall")
            [display_Item NONE (implode "call")
               (CONS (display_String (attach_name ns (SOME dest)))
                   (bvi_to_display_list ns h xs));
             display_Tuple (REVERSE (list_of_seq (\i. display_num_as_varn
                 (h + i)) rets));
             bvi_to_display ns (h + rets) y]`];;

let bvi_fun_to_display_def = new_definition
  `bvi_fun_to_display names (n,argc,body) =
     display_Tuple [display_String (implode "func");
            display_String (attach_name names (SOME n));
            display_Tuple (REVERSE (list_of_seq display_num_as_varn argc));
            bvi_to_display names argc body]`;;

(* dataLang *)

let num_set_to_display_def = new_definition
  `num_set_to_display ns =
     display_String (mlstring_concat [(implode "{");
                      pres_commas (MAP num_to_str (MAP FST (toSortedAList
                        ns)));
                      (implode "}")])`;;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let data_seqs_def,data_seqs_ind = define_wf
  `MEASURE (\x0. data_prog_size x0)`
  `data_seqs z =
     match z with data_Seq x y -> misc_Append (data_seqs x) (data_seqs y)
     | _ -> misc_List [z]`;;

(* [local] *)
let MEM_append_data_seqs = prove
 (`!x. MEM a (append (data_seqs x)) ==> data_prog_size a <= data_prog_size x`,
  CHEAT_TAC);;

(* [local] *)
let list_size_append_data_seqs = prove
 (`!x.
   list_size data_prog_size (append (data_seqs x)) =
   data_prog_size x + 1`,
  CHEAT_TAC);;

(* the termination relation that HOL4 gives is
     MEASURE (\x.
          match x with
            INL (k,_,_) -> k
          | INR (k,_,_) -> k)
   which is not one that HOL Light takes here; the one
   below is what the port found for it *)
let data_prog_to_display_def,data_prog_to_display_ind = define_wf
  `MEASURE (\x. match x with INL (k,_20,_21) -> k | INR (k,_22,_23) -> k)`
  `(data_prog_to_display 0 ns prog = empty_item (implode "...")) /\
   (data_prog_to_display (SUC k) ns prog =
          match prog with data_Skip -> empty_item (implode "skip")
        | data_Move x y -> display_Tuple
            [num_to_display x; display_String (implode ":=");
                num_to_display y]
        | data_Call rets target args NONE -> display_Item NONE (implode
            "call")
            [(\f opt. match opt with NONE -> empty_item (implode "none")
              | SOME opt' -> display_Item NONE (implode "some") [f opt'])
                  (\(x,y). display_Tuple
                    [(\f xs. display_Tuple (MAP f xs)) num_to_display x;
                     num_set_to_display y]) rets;
                display_String (attach_name ns target);
                (\f xs. display_Tuple (MAP f xs)) num_to_display args;
                empty_item (implode "none")]
         | data_Call rets target args (SOME (v,handler)) -> display_Item
             NONE (implode "call")
            [(\f opt. match opt with NONE -> empty_item (implode "none")
              | SOME opt' -> display_Item NONE (implode "some") [f opt'])
                  (\(x,y). display_Tuple
                    [(\f xs. display_Tuple (MAP f xs)) num_to_display x;
                     num_set_to_display y]) rets;
                display_String (attach_name ns target);
                (\f xs. display_Tuple (MAP f xs)) num_to_display args;
                display_Item NONE (implode "some") [display_Tuple
                    [num_to_display v;
                    data_prog_to_display k ns handler]]]
        | data_Force ret loc src -> display_Item NONE (implode "force")
            [(\f opt. match opt with NONE -> empty_item (implode "none")
              | SOME opt' -> display_Item NONE (implode "some") [f opt'])
                  (\(x,y). display_Tuple
                    [num_to_display x; num_set_to_display y]) ret;
             num_to_display loc;
             num_to_display src]
        | data_Assign n op args n_set -> display_Tuple
            [num_to_display n;
             display_String (implode ":=");
             clos_op_to_display ns op;
                (\f xs. display_Tuple (MAP f xs)) num_to_display args;
                (\f opt. match opt with NONE -> empty_item (implode "none")
              | SOME opt' -> display_Item NONE (implode "some") [f opt'])
                  num_set_to_display n_set]
        | data_Seq x y ->
            (let xs = append (misc_Append (data_seqs x) (data_seqs y)) in
               separate_lines (implode "seq") (data_prog_to_display_list k
                   ns xs))
        | data_If n x y -> display_Item NONE (implode "if")
            [num_to_display n; data_prog_to_display k ns x;
                data_prog_to_display k ns y]
        | data_MakeSpace n ns -> display_Item NONE (implode "make_space")
            [num_to_display n; num_set_to_display ns]
        | data_Raise n -> display_Item NONE (implode "raise")
            [num_to_display n]
        | data_Return ns -> display_Item NONE (implode "return") [(\f xs.
            display_Tuple (MAP f xs)) num_to_display ns]
        | data_Tick -> empty_item (implode "tick")) /\
   (data_prog_to_display_list k ns [] = []) /\
   (data_prog_to_display_list k ns (CONS x xs) =
        match k with
          0 -> []
        | SUC k -> CONS (data_prog_to_display k ns x)
            (data_prog_to_display_list k ns xs))`;;

let data_fun_to_display_def = new_definition
  `data_fun_to_display names (n,argc,body) =
     display_Tuple [display_String (implode "func");
            display_String (attach_name names (SOME n));
            display_Tuple (list_of_seq num_to_display argc);
            data_prog_to_display 1000000000 names body]`;;

(* asm *)

let asm_binop_to_display_def = new_definition
  `asm_binop_to_display op = match op with asm_Add -> empty_item (implode
  "Add")
     | asm_Sub -> empty_item (implode "Sub")
     | asm_And -> empty_item (implode "And")
     | asm_Or -> empty_item (implode "Or")
     | asm_Xor -> empty_item (implode "Xor")`;;

let asm_reg_imm_to_display_def = new_definition
  `asm_reg_imm_to_display reg_imm' = match reg_imm' with Reg reg ->
  item_with_num (implode "Reg") reg
     | Imm imm -> item_with_word (implode "Imm") imm`;;

let asm_arith_to_display_def = new_definition
  `asm_arith_to_display op = match op with asm_Binop bop n1 n2 reg_imm' ->
  display_Item NONE (implode "Binop")
         [asm_binop_to_display bop; num_to_display n1; num_to_display n2;
             asm_reg_imm_to_display reg_imm']
     | asm_Shift sh n1 n2 n3 -> display_Item NONE (implode "Shift")
         [shift_to_display sh;
          num_to_display n1;
          num_to_display n2;
          asm_reg_imm_to_display n3]
     | asm_Div n1 n2 n3 -> item_with_nums (implode "Div") [n1; n2; n3]
     | asm_LongMul n1 n2 n3 n4 -> item_with_nums (implode "LongMul") [n1;
       n2; n3; n4]
     | asm_LongDiv n1 n2 n3 n4 n5 -> item_with_nums (implode "LongDiv") [n1;
       n2; n3; n4; n5]
     | asm_AddCarry n1 n2 n3 n4 -> item_with_nums (implode "AddCarry") [n1;
       n2; n3; n4]
     | asm_AddOverflow n1 n2 n3 n4 -> item_with_nums (implode "AddOverflow")
       [n1; n2; n3; n4]
     | asm_SubOverflow n1 n2 n3 n4 -> item_with_nums (implode
       "SubOverflow") [n1; n2; n3; n4]`;;

let asm_addr_to_display_def = new_definition
  `asm_addr_to_display addr' = match addr' with Addr reg w -> display_Item NONE
  (implode "Addr")
                          [num_to_display reg; word_to_display w]`;;

let asm_memop_to_display_def = new_definition
  `asm_memop_to_display op = match op with asm_Load -> empty_item (implode
  "Load")
     | asm_Load8 -> empty_item (implode "Load8")
     | asm_Load16 -> empty_item (implode "Load16")
     | asm_Load32 -> empty_item (implode "Load32")
     | asm_Store -> empty_item (implode "Store")
     | asm_Store8 -> empty_item (implode "Store8")
     | asm_Store16 -> empty_item (implode "Store16")
     | asm_Store32 -> empty_item (implode "Store32")`;;

let asm_cmp_to_display_def = new_definition
  `asm_cmp_to_display op = match op with asm_Equal -> empty_item (implode
  "Equal")
     | asm_Lower -> empty_item (implode "Lower")
     | asm_Less -> empty_item (implode "Less")
     | asm_Test -> empty_item (implode "Test")
     | asm_NotEqual -> empty_item (implode "NotEqual")
     | asm_NotLower -> empty_item (implode "NotLower")
     | asm_NotLess -> empty_item (implode "NotLess")
     | asm_NotTest -> empty_item (implode "NotTest")`;;

let asm_fp_to_display_def = new_definition
  `asm_fp_to_display op = match op with FPLess n1 n2 n3 -> item_with_nums
  (implode "FPLess") [n1; n2; n3]
     | FPLessEqual n1 n2 n3 -> item_with_nums (implode "FPLessEqual") [n1;
       n2; n3]
     | FPEqual n1 n2 n3 -> item_with_nums (implode "FPEqual") [n1; n2; n3]
     | FPAbs n1 n2 -> item_with_nums (implode "FPAbs") [n1; n2]
     | FPNeg n1 n2 -> item_with_nums (implode "FPNeg") [n1; n2]
     | FPSqrt n1 n2 -> item_with_nums (implode "FPSqrt") [n1; n2]
     | FPAdd n1 n2 n3 -> item_with_nums (implode "FPAdd") [n1; n2; n3]
     | FPSub n1 n2 n3 -> item_with_nums (implode "FPSub") [n1; n2; n3]
     | FPMul n1 n2 n3 -> item_with_nums (implode "FPMul") [n1; n2; n3]
     | FPDiv n1 n2 n3 -> item_with_nums (implode "FPDiv") [n1; n2; n3]
     | FPFma n1 n2 n3 -> item_with_nums (implode "FPFma") [n1; n2; n3]
     | FPMov n1 n2 -> item_with_nums (implode "FPMov") [n1; n2]
     | FPMovToReg n1 n2 n3 -> item_with_nums (implode "FPMovToReg") [n1; n2;
       n3]
     | FPMovFromReg n1 n2 n3 -> item_with_nums (implode "FPMovFromReg") [n1;
       n2; n3]
     | FPToInt n1 n2 -> item_with_nums (implode "FPToInt") [n1; n2]
     | FPFromInt n1 n2 -> item_with_nums (implode "FPFromInt") [n1; n2]`;;

let asm_inst_to_display_def = new_definition
  `asm_inst_to_display inst' = match inst' with asm_Skip -> empty_item (implode
  "Skip")
     | asm_Const reg w -> display_Item NONE (implode "Const")
       [num_to_display reg;
                              word_to_display w]
     | asm_Arith a -> display_Item NONE (implode "Arith")
       [asm_arith_to_display a]
     | asm_Mem mop r addr' -> display_Item NONE (implode "Mem")
       [asm_memop_to_display mop;
         num_to_display r; asm_addr_to_display addr']
     | asm_FP fp -> display_Item NONE (implode "FP") [asm_fp_to_display
       fp]`;;

let asm_asm_to_display_def = new_definition
  `asm_asm_to_display inst' = match inst' with asm_Inst i ->
  asm_inst_to_display i
     | asm_Jump w -> item_with_word (implode "Jump") w
     | asm_JumpCmp c r to w -> display_Item NONE (implode "JumpCmp")
       [asm_cmp_to_display c; num_to_display r; asm_reg_imm_to_display to;
        word_to_display w]
     | asm_Call w -> item_with_word (implode "Call") w
     | asm_JumpReg r -> item_with_num (implode "JumpReg>") r
     | asm_Loc r w -> display_Item NONE (implode "Loc") [num_to_display
       r; word_to_display w]`;;

(* stackLang *)

let store_name_to_display_def = new_definition
  `store_name_to_display st = match st with NextFree -> empty_item (implode
  "NextFree")
     | EndOfHeap -> empty_item (implode "EndOfHeap")
     | TriggerGC -> empty_item (implode "TriggerGC")
     | HeapLength -> empty_item (implode "HeapLength")
     | ProgStart -> empty_item (implode "ProgStart")
     | BitmapBase -> empty_item (implode "BitmapBase")
     | CurrHeap -> empty_item (implode "CurrHeap")
     | OtherHeap -> empty_item (implode "OtherHeap")
     | AllocSize -> empty_item (implode "AllocSize")
     | Globals -> empty_item (implode "Globals")
     | GlobReal -> empty_item (implode "GlobReal")
     | Handler -> empty_item (implode "Handler")
     | GenStart -> empty_item (implode "GenStart")
     | CodeBuffer -> empty_item (implode "CodeBuffer")
     | CodeBufferEnd -> empty_item (implode "CodeBufferEnd")
     | BitmapBuffer -> empty_item (implode "BitmapBuffer")
     | BitmapBufferEnd -> empty_item (implode "BitmapBufferEnd")
     | Temp w -> item_with_word (implode "Temp") w`;;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let stack_seqs_def,stack_seqs_ind = define_wf
  `MEASURE (\x0. stack_prog_size (\x. 0) x0)`
  `stack_seqs z =
     match z with stack_Seq x y -> misc_Append (stack_seqs x) (stack_seqs y)
     | _ -> misc_List [z]`;;

(* [local] *)
let MEM_append_stack_seqs = prove
 (`!x. MEM a (append (stack_seqs x)) ==> stack_prog_size ARB a <=
  stack_prog_size ARB x`,
  CHEAT_TAC);;

(* [local] *)
let list_size_append_stack_seqs = prove
 (`!x.
   list_size (stack_prog_size ARB) (append (stack_seqs x)) =
   stack_prog_size ARB x + 1`,
  CHEAT_TAC);;

(* the clauses in 4 quotations: x is stackLang$prog and prog; y is
   stackLang$prog and prog, which one quotation cannot typecheck *)
let stack_prog_to_display_def,stack_prog_to_display_ind =
  assume_definition_rec_clauses
  "termination (CHEAT_TAC)"
  [`(stack_prog_to_display 0 ns prog = empty_item (implode "...")) /\
    (stack_prog_to_display (SUC k) ns stack_Skip = empty_item (implode
    "skip")) /\
    (stack_prog_to_display (SUC k) ns (stack_Inst i) = asm_inst_to_display i)
      /\
    (stack_prog_to_display (SUC k) ns (stack_Get n sn) = display_Tuple
      [num_to_display n; display_String (implode "<-");
          store_name_to_display sn]) /\
    (stack_prog_to_display (SUC k) ns (stack_Set sn n) = display_Tuple
      [store_name_to_display sn; display_String (implode "<-");
          num_to_display n]) /\
    (stack_prog_to_display (SUC k) ns (stack_OpCurrHeap b n1 n2) =
      display_Tuple
      [num_to_display n1; display_String (implode ":="); display_String
          (implode "CurrHeap");
       asm_binop_to_display b; num_to_display n2]) /\
    (stack_prog_to_display (SUC k) ns (stack_Call rh tgt eh) =
      display_Item NONE (implode "call")
           [(match rh with NONE -> empty_item (implode "tail")
             | SOME (p,lr,l1,l2) ->
                 display_Item NONE (implode "returning")
                      [num_to_display lr;
                       display_String (attach_name ns (SOME l1));
                       num_to_display l2;
                       stack_prog_to_display k ns p]);
           (match tgt with INL l -> display_Item NONE (implode "direct")
               [display_String (attach_name ns (SOME l))]
            | INR r -> item_with_num (implode "reg") r);
           (match eh with NONE -> empty_item (implode "no_handler")
            | SOME (p,l1,l2) ->
                display_Item NONE (implode "handler")
                     [display_String (attach_name ns (SOME l1));
                      num_to_display l2;
                      stack_prog_to_display k ns p])]) /\
    (stack_prog_to_display (SUC k) ns (stack_Seq x y) =
         (let xs = append (misc_Append (stack_seqs x) (stack_seqs y)) in
            separate_lines (implode "seq") (stack_prog_to_display_list
                k ns xs))) /\
    (stack_prog_to_display (SUC k) ns (stack_JumpLower n1 n2 n3) =
      item_with_nums (implode "jump_lower") [n1; n2; n3]) /\
    (stack_prog_to_display (SUC k) ns (stack_Alloc n) = item_with_num
    (implode "alloc") n) /\
    (stack_prog_to_display (SUC k) ns (stack_StoreConsts n1 n2 _) =
    item_with_nums (implode "store_consts") [n1; n2]) /\
    (stack_prog_to_display (SUC k) ns (stack_Raise n) = item_with_num
    (implode "raise") n) /\
    (stack_prog_to_display (SUC k) ns (stack_Return n) = item_with_num
    (implode "return") n) /\
    (stack_prog_to_display (SUC k) ns (stack_Break n) = item_with_num
    (implode "break") n) /\
    (stack_prog_to_display (SUC k) ns (stack_Continue n) = item_with_num
    (implode "continue") n) /\
    (stack_prog_to_display (SUC k) ns (stack_FFI nm cp cl ap al ra) =
    display_Item NONE (implode "ffi")
         (CONS (string_imp nm) (MAP num_to_display [cp; cl; ap; al;
             ra]))) /\
    (stack_prog_to_display (SUC k) ns stack_Tick = empty_item (implode
    "tick")) /\
    (stack_prog_to_display (SUC k) ns (stack_LocValue n1 n2 n3) =
      display_Item NONE (implode "loc_value") [num_to_display n1;
                             display_String (attach_name ns (SOME n2));
                             num_to_display n3]) /\
    (stack_prog_to_display (SUC k) ns (stack_Install n1 n2 n3 n4 n5) =
      item_with_nums (implode "install") [n1; n2; n3; n4; n5]) /\
    (stack_prog_to_display (SUC k) ns (stack_ShMemOp mop r a) =
      display_Item NONE (implode "sh_mem") [asm_memop_to_display mop;
                              num_to_display r; asm_addr_to_display a]) /\
    (stack_prog_to_display (SUC k) ns (stack_CodeBufferWrite n1 n2) =
      item_with_nums (implode "code_buffer_write") [n1; n2]) /\
    (stack_prog_to_display (SUC k) ns (stack_DataBufferWrite n1 n2) =
      item_with_nums (implode "data_buffer_write") [n1; n2]) /\
    (stack_prog_to_display (SUC k) ns (stack_RawCall n) =
      display_Item NONE (implode "raw_call") [display_String
          (attach_name ns (SOME n))]) /\
    (stack_prog_to_display (SUC k) ns (stack_StackAlloc n) = item_with_num
    (implode "stack_alloc") n) /\
    (stack_prog_to_display (SUC k) ns (stack_StackFree n) = item_with_num
    (implode "stack_free") n) /\
    (stack_prog_to_display (SUC k) ns (stack_StackStore n m) =
      display_Tuple [display_String (strcat (strcat (strcat (implode
          "stack[") (num_to_hex_mlstring n)) (implode "] := ")) (num_to_str
          m))]) /\
    (stack_prog_to_display (SUC k) ns (stack_StackStoreAny n m) =
      display_Tuple [display_String (strcat (strcat (strcat (implode
          "stack[var ") (num_to_str n)) (implode "] := ")) (num_to_str m))]) /\
    (stack_prog_to_display (SUC k) ns (stack_StackLoad n m) =
      display_Tuple [display_String (mlstring_concat [num_to_str n;
                             (implode " := stack[");
                             num_to_hex_mlstring m; (implode "]")])]) /\
    (stack_prog_to_display (SUC k) ns (stack_StackLoadAny n m) =
      display_Tuple [display_String (mlstring_concat [num_to_str n;
                             (implode " := stack[var ");
                             num_to_str m; (implode "]")])]) /\
    (stack_prog_to_display (SUC k) ns (stack_StackGetSize n) = item_with_num
    (implode "stack_get_size") n) /\
    (stack_prog_to_display (SUC k) ns (stack_StackSetSize n) = item_with_num
    (implode "stack_set_size") n) /\
    (stack_prog_to_display (SUC k) ns (stack_BitmapLoad n m) =
      display_Tuple [display_String (mlstring_concat [num_to_str n;
                             (implode " := bitmap[");
                             num_to_hex_mlstring m;
                             (implode "]")])]) /\
    (stack_prog_to_display (SUC k) ns (stack_Halt n) = item_with_num
    (implode "halt") n) /\
    (stack_prog_to_display_list k ns [] = [])`;
   `stack_prog_to_display (SUC k) ns (stack_If c n to x y) = display_Item NONE
    (implode "if")
         [display_Tuple [asm_cmp_to_display c; num_to_display n;
             asm_reg_imm_to_display to];
          stack_prog_to_display k ns x;
          stack_prog_to_display k ns y]`;
   `stack_prog_to_display (SUC k) ns (stack_Loop x) = display_Item NONE
    (implode "loop")
         [stack_prog_to_display k ns x]`;
   `stack_prog_to_display_list k ns (CONS x xs) =
        match k with 0 -> []
        | SUC k -> CONS (stack_prog_to_display k ns x)
            (stack_prog_to_display_list k ns xs)`];;

let stack_fun_to_display_def = new_definition
  `stack_fun_to_display names (n,body) =
     display_Tuple [display_String (implode "func");
            display_String (attach_name names (SOME n));
            stack_prog_to_display 1000000000 names body]`;;

(* labLang *)

let lab_asm_to_display_def = new_definition
  `lab_asm_to_display ns la = match la with lab_Jump (lab_Lab s n) ->
         display_Item NONE (implode "jump")
           [display_String (attach_name ns (SOME s)); num_to_display n]
     | lab_JumpCmp c r ri (lab_Lab s n) ->
         display_Item NONE (implode "jump_cmp")
           [display_Tuple [asm_cmp_to_display c; num_to_display r;
                   asm_reg_imm_to_display ri];
            display_String (attach_name ns (SOME s)); num_to_display n]
     | lab_Call (lab_Lab s n) ->
         display_Item NONE (implode "call")
           [display_String (attach_name ns (SOME s)); num_to_display n]
     | lab_LocValue r (lab_Lab s n) ->
         display_Item NONE (implode "loc_value")
           [num_to_display r; display_String (attach_name ns (SOME s));
             num_to_display n]
     | lab_CallFFI name -> display_Item NONE (implode "call_FFI")
       [string_imp name]
     | lab_Install -> empty_item (implode "install")
     | lab_Halt -> empty_item (implode "halt")`;;

let lab_line_to_display_def = new_definition
  `lab_line_to_display ns line = match line with lab_Label s n le ->
         display_Item NONE (implode "label") [display_String (attach_name ns
           (SOME s)); num_to_display n]
     | lab_Asm aoc enc len -> (match aoc with Asmi i -> display_Item NONE
       (implode "asm") [asm_asm_to_display i]
       | Cbw r1 r2 -> item_with_nums (implode "cbw") [r1; r2]
       | ShareMem mop r a -> display_Item NONE (implode "share_mem")
         [asm_memop_to_display mop;
                              num_to_display r;
                              asm_addr_to_display a])
     | lab_LabAsm la pos enc len -> lab_asm_to_display ns la`;;

let lab_fun_to_display_def = define_general
  `lab_fun_to_display names (Section n lines) =
     display_List (
            CONS (display_String (attach_name names (SOME n))) (MAP
              (lab_line_to_display names) lines))`;;

(* wordLang *)

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let word_seqs_def,word_seqs_ind = define_wf
  `MEASURE (\x0. word_prog_size (\x. 0) x0)`
  `word_seqs z =
     match z with word_Seq x y -> misc_Append (word_seqs x) (word_seqs y)
     | _ -> misc_List [z]`;;

(* [local] *)
let MEM_append_word_seqs = prove
 (`!x. MEM a (append (word_seqs x)) ==> word_prog_size ARB a <=
  word_prog_size ARB x`,
  CHEAT_TAC);;

(* HOL4 presLangScript.sml:1311-1312: a theorem that HOL4 states as the
   value of an ML expression: MEM_word_exps_size_ARB *)

(* the termination relation that HOL4 gives is
     MEASURE (\x. match x with INL v -> word_exp_size ARB v | INR v ->
       list_size
       word_exp_size ARB v)
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
let word_exp_to_display_def,word_exp_to_display_ind = define_rec
  `(word_exp_to_display (word_Const v) = item_with_word (implode "Const") v) /\
   (word_exp_to_display (word_Var n) = item_with_num (implode "Var") n) /\
   (word_exp_to_display (word_Lookup st) = display_Item NONE (implode
    "Lookup") [store_name_to_display st]) /\
   (word_exp_to_display (word_Load exp2) = display_Item NONE (implode
    "MemLoad") [word_exp_to_display exp2]) /\
   (word_exp_to_display (word_Op bop exs) = display_Item NONE (implode "Op") (
        CONS (asm_binop_to_display bop) (word_exp_to_display_list exs))) /\
   (word_exp_to_display (word_Shift sh exp exp1) = display_Item NONE (implode
    "Shift") [
      shift_to_display sh;
      word_exp_to_display exp;
      word_exp_to_display exp1]) /\
   (word_exp_to_display_list [] = []) /\
   (word_exp_to_display_list (CONS x xs) = CONS (word_exp_to_display x)
    (word_exp_to_display_list xs))`;;

let ws_to_display_def,ws_to_display_ind = define_rec
  `(ws_to_display [] = []) /\
   (ws_to_display (CONS (b,x) xs) = CONS (display_Tuple [bool_to_display
    b; word_to_display x]) (ws_to_display xs))`;;

let num_sets_to_display_def = new_definition
  `num_sets_to_display (l,r) =
     display_Tuple [num_set_to_display l;
            num_set_to_display r]`;;

(* the clauses in 6 quotations: a is ((num list # cutsets # wordLang$prog #
   num # num) option) and num; b is (num option), binop and num; c is (num
   list) and num; d is ((num # wordLang$prog # num # num) option) and num;
   mvs is ((num # num) list) and (_#_)list; p is wordLang$prog and prog; p1
   is wordLang$prog and prog; p2 is wordLang$prog and prog; prog is prog and
   wordLang$prog, which one quotation cannot typecheck *)
let word_prog_to_display_def,word_prog_to_display_ind =
  assume_definition_rec_clauses
  "termination (CHEAT_TAC)"
  [`(word_prog_to_display 0 ns x = empty_item (implode "...")) /\
    (word_prog_to_display (SUC k) ns word_Skip = empty_item (implode "skip"))
      /\
    (word_prog_to_display (SUC k) ns (word_Move n mvs) = display_Item NONE
    (implode "move")
        [num_to_display n; display_Tuple (MAP (\(n1,n2). display_Tuple
            [num_to_display n1;
             display_String (implode ":=");
             num_to_display n2]) mvs)]) /\
    (word_prog_to_display (SUC k) ns (word_Inst i) =
        display_Item NONE (implode "inst") [asm_inst_to_display i]) /\
    (word_prog_to_display (SUC k) ns (word_Assign n exp) =
         display_Tuple [num_to_display n;
                display_String (implode ":=");
                word_exp_to_display exp]) /\
    (word_prog_to_display (SUC k) ns (word_Get n sn) = display_Tuple
        [num_to_display n; display_String (implode "<-");
            store_name_to_display sn]) /\
    (word_prog_to_display (SUC k) ns (word_Set sn exp) = display_Tuple
        [store_name_to_display sn; display_String (implode "<-");
            word_exp_to_display exp]) /\
    (word_prog_to_display (SUC k) ns (word_Store exp n) = display_Tuple
        [display_String (implode "mem"); word_exp_to_display exp;
         display_String (implode ":="); num_to_display n]) /\
    (word_prog_to_display (SUC k) ns (word_ShareInst mop n exp) = display_Tuple
        [display_String (implode "share_mem"); asm_memop_to_display mop;
         num_to_display n; word_exp_to_display exp]) /\
    (word_prog_to_display (SUC k) ns (word_Call a b c d) = display_Item NONE
    (implode "call")
        [word_prog_to_display_ret k ns a;
         (\f opt. match opt with NONE -> empty_item (implode "none")
              | SOME opt' -> display_Item NONE (implode "some") [f opt'])
                  (\n. display_String (attach_name ns (SOME n))) b;
         (\f xs. display_Tuple (MAP f xs)) num_to_display c;
         word_prog_to_display_handler k ns d]) /\
    (word_prog_to_display (SUC k) ns (word_Seq prog1 prog2) =
        (let xs = append (misc_Append (word_seqs prog1) (word_seqs prog2))
            in
           separate_lines (implode "seq") (word_prog_to_display_list k
               ns xs))) /\
    (word_prog_to_display (SUC k) ns (word_Alloc n ms) = display_Item NONE
    (implode "alloc")
        [num_to_display n; num_sets_to_display ms]) /\
    (word_prog_to_display (SUC k) ns (word_Raise n) = item_with_num (implode
    "raise") n) /\
    (word_prog_to_display (SUC k) ns (word_Break n) = item_with_num (implode
    "break") n) /\
    (word_prog_to_display (SUC k) ns (word_Continue n) = item_with_num
    (implode "continue") n) /\
    (word_prog_to_display (SUC k) ns (word_Return n vs) =
         display_Item NONE (implode "return")
           [num_to_display n;
            display_Tuple (MAP num_to_display vs)]) /\
    (word_prog_to_display (SUC k) ns word_Tick = empty_item (implode "tick"))
      /\
    (word_prog_to_display (SUC k) ns (word_LocValue n1 n2) =
        display_Item NONE (implode "loc_value") [display_String
            (attach_name ns (SOME n1)); num_to_display n2]) /\
    (word_prog_to_display (SUC k) ns (word_Install n1 n2 n3 n4 ms) =
        display_Item NONE (implode "install") (
            APPEND (MAP num_to_display [n1; n2; n3; n4])
                [num_sets_to_display ms])) /\
    (word_prog_to_display (SUC k) ns (word_CodeBufferWrite n1 n2) =
        item_with_nums (implode "code_buffer_write") [n1; n2]) /\
    (word_prog_to_display (SUC k) ns (word_DataBufferWrite n1 n2) =
        item_with_nums (implode "data_buffer_write") [n1; n2]) /\
    (word_prog_to_display (SUC k) ns (word_FFI nm n1 n2 n3 n4 ms) =
        display_Item NONE (implode "ffi") (
            APPEND (CONS (string_imp nm) (MAP num_to_display [n1; n2;
                n3; n4])) [num_sets_to_display ms])) /\
    (word_prog_to_display_list k ns [] = []) /\
    (word_prog_to_display_list k ns (CONS x xs) =
        match k with 0 -> []
        | SUC k -> CONS (word_prog_to_display k ns x)
            (word_prog_to_display_list k ns xs)) /\
    (word_prog_to_display_ret k ns NONE = empty_item (implode "tail")) /\
    (word_prog_to_display_ret k ns (SOME (vs,ms,prog,n2,n3)) =
        match k with 0 -> empty_item (implode "...")
        | SUC k ->
        display_Item NONE (implode "returning") [display_Tuple
            [display_Tuple (MAP num_to_display vs); num_sets_to_display ms;
            word_prog_to_display k ns prog;
            display_String (attach_name ns (SOME n2));
            num_to_display n3]]) /\
    (word_prog_to_display_handler k ns NONE = empty_item (implode
    "no_handler")) /\
    (word_prog_to_display_handler k ns (SOME (n1,prog,n2,n3)) =
        match k with 0 -> empty_item (implode "...")
        | SUC k ->
        display_Item NONE (implode "handler") [display_Tuple
            [num_to_display n1;
            word_prog_to_display k ns prog;
            display_String (attach_name ns (SOME n2));
            num_to_display n3]])`;
   `word_prog_to_display (SUC k) ns (word_MustTerminate prog) = display_Item
    NONE (implode "must_terminate")
        [word_prog_to_display k ns prog]`;
   `word_prog_to_display (SUC k) ns (word_OpCurrHeap b n1 n2) = display_Tuple
        [num_to_display n1; display_String (implode ":="); display_String
            (implode "CurrHeap");
         asm_binop_to_display b; num_to_display n2]`;
   `word_prog_to_display (SUC k) ns (word_If cmp n reg p1 p2) =
        display_Item NONE (implode "if")
          [display_Tuple [asm_cmp_to_display cmp;
                  num_to_display n;
                  asm_reg_imm_to_display reg];
           word_prog_to_display k ns p1; word_prog_to_display k ns p2]`;
   `word_prog_to_display (SUC k) ns (word_Loop ns1 p ns2) =
        display_Item NONE (implode "Loop")
          [num_set_to_display ns1;
           word_prog_to_display k ns p;
           num_set_to_display ns2]`;
   `word_prog_to_display (SUC k) ns (word_StoreConsts a b c d ws) =
    display_Item NONE (implode "store_consts")
        [num_to_display a;
         num_to_display b;
         num_to_display c;
         num_to_display d;
         display_Tuple (ws_to_display ws)]`];;

let word_fun_to_display_def = new_definition
  `word_fun_to_display names (n,argc,body) =
     display_Tuple [display_String (implode "func");
            display_String (attach_name names (SOME n));
            display_Tuple (list_of_seq (\n. num_to_display (2 * n)) argc);
            word_prog_to_display 1000000000 names body]`;;

(* tap configuration *)

let tap_config_FIELDS = define_record "tap_config"
  ["explore_flag","bool"];;

let default_tap_config_def = new_definition
  `default_tap_config = mk_tap_config F`;;

(* ------------------------- *)

let map_to_append_def,map_to_append_ind = define_rec
  `(map_to_append f [] = misc_Nil) /\
   (map_to_append f (CONS x xs) = misc_Append (misc_List (f x))
    (map_to_append f xs))`;;

let source_to_strs_def = new_definition
  `source_to_strs decs =
     map_to_append (str_tree_to_strs (implode "\n\n") o
                    display_to_str_tree o
                    source_to_display_dec) decs`;;

let flat_to_strs_def = new_definition
  `flat_to_strs (decs:flat_exp list) =
     map_to_append (str_tree_to_strs (implode "\n\n") o
                    display_to_str_tree o
                    flat_to_display) decs`;;

let clos_to_strs_def = new_definition
  `clos_to_strs (decs,funs) =
     let names = get_src_names (APPEND decs (MAP (SND o SND) funs)) LN in
       misc_Append (map_to_append (str_tree_to_strs (implode "\n\n") o
                              display_to_str_tree o
                              clos_dec_to_display names) decs)
              (map_to_append (str_tree_to_strs (implode "\n\n") o
                              display_to_str_tree o
                              clos_fun_to_display names) funs)`;;

let bvl_to_strs_def = new_definition
  `bvl_to_strs names xs =
     map_to_append (str_tree_to_strs (implode "\n\n") o
                    display_to_str_tree o
                    bvl_fun_to_display names) xs`;;

(* HOL4 presLangScript.sml:1513-1521: the ML values that the definitions
   below antiquote *)

let bvi_to_strs_def = new_definition
  `bvi_to_strs names xs =
     map_to_append (str_tree_to_strs (implode "\n\n") o
                    display_to_str_tree o
                    bvi_fun_to_display names) xs`;;

(* HOL4 presLangScript.sml:1530-1538: the ML values that the definitions
   below antiquote *)

let data_to_strs_def = new_definition
  `data_to_strs names xs =
     map_to_append (str_tree_to_strs (implode "\n\n") o
                    display_to_str_tree o
                    data_fun_to_display names) xs`;;

(* HOL4 presLangScript.sml:1547-1555: the ML values that the definitions
   below antiquote *)

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

(* HOL4 presLangScript.sml:1578-1586: the ML values that the definitions
   below antiquote *)

(*

val names_tm = “(insert 50 «foo» (insert 60 «bar» LN))”

val data_prog_tm =
    “[(50,2,Seq (Move 5 1) $
            Seq (Assign 3 Add [0;1] NONE) $
            Seq (Assign 6 Sub [5;3] NONE) $ Return 6);
      (60n,2n,Skip)]”

val _ = data_to_strs data_prog_tm names_tm |> print_strs

*)

(* and the interface *)
let _ = unhide_overloads ();;
