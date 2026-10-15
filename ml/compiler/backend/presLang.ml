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
  `item_with_num name n = Item NONE name [num_to_display n]`;;

let item_with_nums_def = cake_define
  `item_with_nums name ns = Item NONE name (MAP num_to_display ns)`;;

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
  `item_with_word name w = Item NONE name [word_to_display w]`;;

let lit_to_display_def = cake_define_list
  [`lit_to_display (IntLit i) =
        Item NONE (implode "IntLit") [empty_item (toString i)]`;
   `lit_to_display (Char c) =
        Item NONE (implode "Char") [empty_item (implode ("#\"" ++
          [c] ++ "\""))]`;
   `lit_to_display (StrLit s) =
        Item NONE (implode "StrLit") [string_imp s]`;
   `lit_to_display (Word8 w) =
        Item NONE (implode "Word8") [word_to_display w]`;
   `lit_to_display (Word64 w) =
        Item NONE (implode "Word64") [word_to_display w]`;
   `lit_to_display (Float64 w) =
        Item NONE (implode "Float64") [word_to_display w]`];;

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
  `fp_uop_to_display op = (match op with FP_Abs -> empty_item
  (implode "FP_Abs") | FP_Neg -> empty_item (implode "FP_Neg") |
  FP_Sqrt -> empty_item (implode "FP_Sqrt"))`;;

let fp_bop_to_display_def = cake_define
  `fp_bop_to_display op = (match op with FP_Add -> empty_item
  (implode "FP_Add") | FP_Sub -> empty_item (implode "FP_Sub") |
  FP_Mul -> empty_item (implode "FP_Mul") | FP_Div -> empty_item
  (implode "FP_Div"))`;;

let fp_top_to_display_def = cake_define
  `fp_top_to_display op =
     (match op with FP_Fma -> empty_item (implode "FP_Fma"))`;;

let word_size_to_display_def = cake_define
  `(word_size_to_display W8 = empty_item (implode "W8")) /\
   (word_size_to_display W64 = empty_item (implode "W64"))`;;

let opb_to_display_def = cake_define
  `(opb_to_display Lt = empty_item (implode "Lt")) /\
   (opb_to_display Gt = empty_item (implode "Gt")) /\
   (opb_to_display Leq = empty_item (implode "Leq")) /\
   (opb_to_display Geq = empty_item (implode "Geq"))`;;

let opw_to_display_def = cake_define
  `(opw_to_display Andw = empty_item (implode "Andw")) /\
   (opw_to_display Orw = empty_item (implode "Orw")) /\
   (opw_to_display Xor = empty_item (implode "Xor")) /\
   (opw_to_display Add = empty_item (implode "Add")) /\
   (opw_to_display Sub = empty_item (implode "Sub"))`;;

let shift_to_display_def = cake_define
  `(shift_to_display Lsl = empty_item (implode "Lsl")) /\
   (shift_to_display Lsr = empty_item (implode "Lsr")) /\
   (shift_to_display Asr = empty_item (implode "Asr")) /\
   (shift_to_display Ror = empty_item (implode "Ror"))`;;

let thunk_mode_to_display_def = cake_define
  `(thunk_mode_to_display Evaluated = empty_item (implode "Evaluated"))
  /\
   (thunk_mode_to_display NotEvaluated = empty_item (implode
     "NotEvaluated"))`;;

let thunk_op_to_display_def = cake_define
  `(thunk_op_to_display (AllocThunk m) =
     Item NONE (implode "AllocThunk") [thunk_mode_to_display m]) /\
   (thunk_op_to_display (UpdateThunk m) =
     Item NONE (implode "UpdateThunk") [thunk_mode_to_display m]) /\
   (thunk_op_to_display ForceThunk = empty_item (implode
     "ForceThunk"))`;;

let test_to_display_def = cake_define
  `test_to_display Equal = empty_item (implode "Equal") /\
   test_to_display (Compare cmp) = Item NONE (implode "Compare")
     [opb_to_display cmp] /\
   test_to_display (AltCompare cmp) = Item NONE (implode
     "AltCompare") [opb_to_display cmp]`;;

let arith_to_display_def = cake_define
  `arith_to_display Add = empty_item (implode "Add") /\
   arith_to_display Sub = empty_item (implode "Sub") /\
   arith_to_display Mul = empty_item (implode "Mul") /\
   arith_to_display Div = empty_item (implode "Div") /\
   arith_to_display Mod = empty_item (implode "Mod") /\
   arith_to_display And = empty_item (implode "And") /\
   arith_to_display Xor = empty_item (implode "Xor") /\
   arith_to_display Or = empty_item (implode "Or") /\
   arith_to_display Neg = empty_item (implode "Neg") /\
   arith_to_display Not = empty_item (implode "Not") /\
   arith_to_display Abs = empty_item (implode "Abs") /\
   arith_to_display Sqrt = empty_item (implode "Sqrt") /\
   arith_to_display FMA = empty_item (implode "FMA")`;;

let prim_type_to_display_def = cake_define
  `prim_type_to_display x1 =
      match x1 with
        BoolT -> empty_item (implode "BoolT")
      | IntT -> empty_item (implode "IntT")
      | CharT -> empty_item (implode "CharT")
      | StrT -> empty_item (implode "StrT")
      | Float64T -> empty_item (implode "Float64T")
      | (WordT W8) -> empty_item (implode "WordT_W8")
      | (WordT W64) -> empty_item (implode "WordT_W64")`;;

let lop_to_display_def = cake_define
  `lop_to_display Andalso = empty_item (implode "Andalso") /\
   lop_to_display Orelse = empty_item (implode "Orelse")`;;

let op_to_display_def = cake_define
  `op_to_display (p:ast_op) =
   (match p with Shift ws sh num' -> Item NONE (implode "Shift")
                             [word_size_to_display ws;
                              shift_to_display sh;
                              num_to_display num'] | Arith a ty ->
                                Item NONE (implode "Arith")
                          [arith_to_display a;
                           prim_type_to_display ty] | FromTo ty1 ty2
                             -> Item NONE (implode "FromTo")
                          [prim_type_to_display ty1;
                           prim_type_to_display ty2] | Test test ty
                             -> Item NONE (implode "Test")
                          [test_to_display test;
                           prim_type_to_display ty] | Equality ->
                             empty_item (implode "Equality") | Opapp
                             -> empty_item (implode "Opapp") |
                             Opassign -> empty_item (implode
                             "Opassign") | Opref -> empty_item
                             (implode "Opref") | Opderef ->
                             empty_item (implode "Opderef") |
                             Aw8alloc -> empty_item (implode
                             "Aw8alloc") | Aw8sub -> empty_item
                             (implode "Aw8sub") | Aw8length ->
                             empty_item (implode "Aw8length") |
                             Aw8update -> empty_item (implode
                             "Aw8update") | CopyStrStr -> empty_item
                             (implode "CopyStrStr") | CopyStrAw8 ->
                             empty_item (implode "CopyStrAw8") |
                             CopyAw8Str -> empty_item (implode
                             "CopyAw8Str") | CopyAw8Aw8 -> empty_item
                             (implode "CopyAw8Aw8") | Implode ->
                             empty_item (implode "Implode") | Explode
                             -> empty_item (implode "Explode") |
                             Strsub -> empty_item (implode "Strsub")
                             | Strlen -> empty_item (implode
                             "Strlen") | Strcat -> empty_item
                             (implode "Strcat") | VfromList ->
                             empty_item (implode "VfromList") | Vsub
                             -> empty_item (implode "Vsub") |
                             Vsub_unsafe -> empty_item (implode
                             "Vsub_unsafe") | Vlength -> empty_item
                             (implode "Vlength") | Aalloc ->
                             empty_item (implode "Aalloc") |
                             AallocEmpty -> empty_item (implode
                             "AallocEmpty") | AallocFixed ->
                             empty_item (implode "AallocFixed") |
                             Asub -> empty_item (implode "Asub") |
                             Alength -> empty_item (implode
                             "Alength") | Aupdate -> empty_item
                             (implode "Aupdate") | Asub_unsafe ->
                             empty_item (implode "Asub_unsafe") |
                             Aupdate_unsafe -> empty_item (implode
                             "Aupdate_unsafe") | Aw8sub_unsafe ->
                             empty_item (implode "Aw8sub_unsafe") |
                             Aw8update_unsafe -> empty_item (implode
                             "Aw8update_unsafe") | XorAw8Str_unsafe
                             -> empty_item (implode
                             "XorAw8Str_unsafe") | ListAppend ->
                             empty_item (implode "ListAppend") |
                             ConfigGC -> empty_item (implode
                             "ConfigGC") | FFI v35 -> empty_item
                             (implode "FFI v35") | Eval -> empty_item
                             (implode "Eval") | Env_id -> empty_item
                             (implode "Env_id") | ThunkOp t ->
                             thunk_op_to_display t)`;;

let id_to_display_def = cake_define_list
  [`id_to_display (Short n) =
      Item NONE (implode "Short") [String n]`;
   `id_to_display (Long n i) =
      Item NONE (implode "Long") [String n; id_to_display i]`];;

let _ = size_thms "ast_t";;
let _ = size_thms "list";;
(* HOL4 termination: *)
let ast_t_to_display_def = cake_define_wf
  `MEASURE (\x. match x with INL v -> ast_t_size v | INR v -> list_size
  ast_t_size v)`
  `ast_t_to_display c =
        match c with
          c ->
     match c with Atvar n -> Item NONE (implode "Atvar") [String n] |
       Atfun t1 t2 -> Item NONE (implode "Atfun") [ast_t_to_display t1;
       ast_t_to_display t2] | Attup ts -> Item NONE (implode "Attup")
       [Tuple (ast_t_to_display_list ts)] | Atapp ts id -> Item NONE
       (implode "Attup") [Tuple (ast_t_to_display_list ts);
                              id_to_display id]
        | [] -> []
        | (x :: xs) ->
       ast_t_to_display x :: ast_t_to_display_list xs`;;

let _ = size_thms "list";;
let _ = size_thms "pat";;
(* HOL4 termination: *)
let pat_to_display_def = cake_define_wf
  `MEASURE (\x. match x with INL v -> pat_size v | INR v -> list_size
  pat_size v)`
  `pat_to_display x1 =
        match x1 with
          (c:ast_pat) ->
     match c with Pany -> Item NONE (implode "Pany") [] | Pvar v ->
       Item NONE (implode "Pvar") [String v] | Plit l -> Item NONE
       (implode "Plit") [lit_to_display l] | Pcon opt_id pats ->
         Item NONE (implode "Pcon") [(\f opt. match opt with NONE ->
           empty_item (implode "none") | SOME opt' -> Item NONE (implode
           "some") [f opt']) id_to_display opt_id;
                           Tuple (pat_to_display_list pats)] | Pas t
                             v -> Item NONE (implode "Pas")
                             [pat_to_display t; String v] | Pref t ->
                             Item NONE (implode "Pref") [pat_to_display
                             t] | Ptannot x y -> Item NONE (implode
                             "Ptannot") [pat_to_display x;
                             ast_t_to_display y]
        | [] -> []
        | (x :: xs) ->
       pat_to_display x :: pat_to_display_list xs`;;

let exp_to_display_def = cake_define
  `exp_to_display x1 =
        match x1 with
          (c:ast_exp) ->
     match c with Lit l -> Item NONE (implode "Lit") [lit_to_display
       l] | Raise e -> Item NONE (implode "Raise") [exp_to_display e] |
       Con opt_id es -> Item NONE (implode "Con") [(\f opt. match opt
       with NONE -> empty_item (implode "none") | SOME opt' -> Item NONE
       (implode "some") [f opt']) id_to_display opt_id;
                              Tuple (exp_to_display_list es)] | Var
                                id -> Item NONE (implode "Var")
                                [id_to_display id] | Fun n e -> Item
                                NONE (implode "Fun") [String n;
                                exp_to_display e] | App op es -> Item
                                NONE (implode "App") (op_to_display op
                                ::
                              exp_to_display_list es) | Log lop e1 e2
                                -> Item NONE (implode "Log")
                                [lop_to_display lop;
                              exp_to_display e1;
                              exp_to_display e2] | If e1 e2 e3 ->
                                Item NONE (implode "If") [exp_to_display
                                e1;
                              exp_to_display e2;
                              exp_to_display e3] | Let n_opt e1 e2 ->
                                Item NONE (implode "Let")
         [(\f opt. match opt with NONE -> empty_item (implode "none")
           | SOME opt' -> Item NONE (implode "some") [f opt']) String
           n_opt;
          exp_to_display e1;
          exp_to_display e2] | Mat e pats ->
         Item NONE (implode "Mat")
         [exp_to_display e;
          Tuple (pat_exp_to_display_list pats)] | Handle e pats ->
         Item NONE (implode "Handle")
         [exp_to_display e;
          Tuple (pat_exp_to_display_list pats)] | Letrec fns e ->
         Item NONE (implode "Letrec")
         [Tuple (fun_to_display_list fns);
          exp_to_display e] | Tannot e _1 -> Item NONE (implode
            "Tannot") [exp_to_display e] | Lannot e _2 -> Item NONE
            (implode "Lannot") [exp_to_display e]
        | [] -> []
        | (x :: xs) ->
       exp_to_display x :: exp_to_display_list xs
        | [] -> []
        | ((p,e) :: xs) ->
       Tuple [pat_to_display p; exp_to_display e] ::
       pat_exp_to_display_list xs
        | [] -> []
        | ((m,n,e) :: xs) ->
       Tuple [String m;
              String n;
              exp_to_display e] ::
       fun_to_display_list xs`;;

let _ = size_thms "dec";;
let _ = size_thms "list";;
(* HOL4 termination: *)
let source_to_display_dec_def = cake_define_wf
  `MEASURE (\x. match x with INL v -> dec_size v | INR v -> list_size
  dec_size v)`
  `source_to_display_dec x1 =
        match x1 with
          (d:dec) ->
     match d with Dlet _3 pat e -> Item NONE (implode "Dlet")
       [pat_to_display pat; exp_to_display e] | Dletrec _4 fns -> Item
       NONE (implode "Dletrec")
                             (MAP (\(m,n,e). Tuple [String m;
                              String n;
                              exp_to_display e]) fns) | Dtype _5 ts
                                -> Item NONE (implode "Dtype") (MAP
                                (\(ns,n,z).
                       Tuple [Tuple (MAP String ns);
                              String n;
                              Tuple (MAP (\(n,tys). Tuple [String n;
                              Tuple (MAP ast_t_to_display tys)]) z)])
                                ts) | Dtabbrev _6 ns n ty ->
         Item NONE (implode "Dtabbrev") [Tuple (MAP String ns);
                              String n;
                              ast_t_to_display ty] | Dexn _7 n tys ->
                                Item NONE (implode "Dexn") [String n;
                              Tuple (MAP ast_t_to_display tys)] |
                                Dmod n ds -> Item NONE (implode "Dmod")
                                [String n;
                              Tuple (source_to_display_dec_list ds)]
                                | Dlocal xs ys -> Item NONE (implode
                                "Dlocal") [Tuple
                                (source_to_display_dec_list xs);
                              Tuple (source_to_display_dec_list ys)]
                                | Denv n -> Item NONE (implode "Denv")
                                [String n]
        | [] -> []
        | (x :: xs) ->
       source_to_display_dec x :: source_to_display_dec_list xs`;;

(* flatLang *)

let opt_con_to_display_def = cake_define
  `opt_con_to_display ocon = (match ocon with NONE -> empty_item
  (implode "ConIdNone") | SOME (c,NONE) -> item_with_num (implode
  "ConIdUntyped") c | SOME (c,SOME t) -> item_with_nums (implode
  "ConIdTyped") [c; t])`;;

let _ = size_thms "list";;
let _ = size_thms "pat";;
(* HOL4 termination: *)
let flat_pat_to_display_def = cake_define_wf
  `MEASURE (\x. match x with INL v -> pat_size v | INR v -> list_size
  pat_size v)`
  `flat_pat_to_display p =
        match p with
          p ->
       match p with flatLang_Pvar varN -> Item NONE (implode "Pvar")
         [string_imp varN] | Pany -> empty_item (implode "Pany") | Plit
         lit -> Item NONE (implode "Plit") [lit_to_display lit] |
         flatLang_Pcon id pats -> Item NONE (implode "Pcon")
               (flat_pat_to_display_list pats) | Pas pat varN -> Item
                 NONE (implode "Pas") [flat_pat_to_display pat;
                              string_imp varN] | Pref pat -> Item
                                NONE (implode "Pref")
                                [flat_pat_to_display pat]
        | [] -> []
        | (x :: xs) ->
       flat_pat_to_display x :: flat_pat_to_display_list xs`;;

let flat_op_to_display_def = cake_define
  `flat_op_to_display op = (match op with Src ast_op -> op_to_display
  ast_op | GlobalVarAlloc n -> item_with_num (implode
  "GlobalVarAlloc") n | GlobalVarInit n -> item_with_num (implode
  "GlobalVarInit") n | GlobalVarLookup n -> item_with_num (implode
  "GlobalVarLookup") n | TagLenEq n1 n2 -> item_with_nums (implode
  "TagLenEq") [n1; n2] | LenEq n1 -> item_with_nums (implode "LenEq")
  [n1] | El n -> item_with_num (implode "El") n | Id -> empty_item
  (implode "Id"))`;;

let add_name_hint_def = cake_define
  `add_name_hint prefix name_hint =
     concat [prefix; (implode "<"); name_hint; (implode ">")]`;;

let flat_to_display_def = cake_define
  `flat_to_display x1 =
        match x1 with
          (flatLang_Raise tra exp) ->
       Item (SOME tra) (implode "raise") [flat_to_display exp]
        | (Handle tra exp pes) ->
       Item (SOME tra) (implode "handle") (
           flat_to_display exp :: pat_flat_to_display_list pes)
        | (Lit tra lit) -> Item (SOME tra) (implode "lit") []
        | (flatLang_Con tra id_opt exps) ->
       Item (SOME tra) (implode "con") (
           opt_con_to_display id_opt :: flat_to_display_list exps)
        | (Var_local tra varN) ->
       Item (SOME tra) (implode "var_local") [string_imp varN]
        | (Fun name_hint varN exp) ->
       Item (SOME None) (add_name_hint (implode "fun") name_hint)
         [string_imp varN; flat_to_display exp]
        | (App tra op exps) ->
       Item (SOME tra) (implode "app") (flat_op_to_display op ::
         flat_to_display_list exps)
        | (If tra exp1 exp2 exp3) ->
       Item (SOME tra) (implode "if") [flat_to_display exp1;
         flat_to_display exp2;
           flat_to_display exp3]
        | (Mat tra exp pes) ->
       Item (SOME tra) (implode "mat") (
           flat_to_display exp :: pat_flat_to_display_list pes)
        | (Let tra varN_opt exp1 exp2) ->
       Item (SOME tra) (implode "let") [(\f opt. match opt with NONE
         -> empty_item (implode "none") | SOME opt' -> Item NONE
         (implode "some") [f opt']) string_imp varN_opt;
           flat_to_display exp1; flat_to_display exp2]
        | (Letrec name_hint funs exp) ->
       Item (SOME None) (add_name_hint (implode "letrec") name_hint)
           [Tuple (fun_flat_to_display_list funs); flat_to_display
             exp]
        | [] -> []
        | (x :: xs) ->
       flat_to_display x :: flat_to_display_list xs
        | [] -> []
        | ((pat,exp) :: xs) ->
       displayLang_Tuple [flat_pat_to_display pat; flat_to_display
         exp] :: pat_flat_to_display_list xs
        | [] -> []
        | ((v1,v2,e) :: xs) ->
        Tuple [string_imp v1; string_imp v2; flat_to_display e] ::
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
  `attach_name ns NONE = (implode "none") /\
   attach_name ns (SOME d) =
     (match lookup d ns with NONE -> toString d | SOME name ->
       concat [name; (implode "@"); toString d])`;;

let const_part_to_display_def = cake_define
  `const_part_to_display (Int i:const_part) =
     Item NONE (implode "Int") [int_to_display i] /\
   const_part_to_display (Con t vs) =
     Item NONE (implode "Con") [num_to_display t; Tuple (MAP
       num_to_display vs)] /\
   const_part_to_display (Str s) =
     Item NONE (implode "Str") [String (concat [(implode) "\""; s;
       (implode) "\""])] /\
   const_part_to_display (W64 w) =
     Item NONE (implode "W64") [word_to_display w]`;;

let _ = size_thms "const";;
let _ = size_thms "list";;
(* HOL4 termination: *)
let const_to_display_def = cake_define_wf
  `MEASURE (\x. match x with INL v -> const_size v | INR v -> list_size
  const_size v)`
  `const_to_display (ConstInt i:const) =
     Item NONE (implode "ConstInt") [int_to_display i] /\
   const_to_display (ConstCons t vs) =
     Item NONE (implode "ConstCons") [num_to_display t; Tuple
       (const_to_display_list vs)] /\
   const_to_display (ConstStr s) =
     Item NONE (implode "ConstStr") [String (concat [(implode) "\"";
       s; (implode) "\""])] /\
   const_to_display (ConstWord64 w) =
     Item NONE (implode "ConstWord64") [word_to_display w] /\
   (const_to_display_list [] = []) /\
   (const_to_display_list (x :: xs) =
     const_to_display x :: const_to_display_list xs)`;;

let clos_op_to_display_def = cake_define
  `clos_op_to_display ns op = (match op with GlobOp (Global num') ->
  item_with_num (implode "Global") num' | GlobOp (SetGlobal num') ->
  item_with_num (implode "SetGlobal") num' | GlobOp AllocGlobal ->
  String (implode "AllocGlobal") | GlobOp GlobalsPtr -> String (implode
  "GlobalsPtr") | GlobOp SetGlobalsPtr -> String (implode
  "SetGlobalsPtr") | BlockOp (Cons num') -> item_with_num (implode
  "Cons") num' | BlockOp (ElemAt num') -> item_with_num (implode
  "ElemAt") num' | BlockOp (TagLenEq n1 n2) -> item_with_nums (implode
  "TagLenEq") [n1; n2] | BlockOp (BoolTest test) -> Item NONE (implode
  "BoolTest") [test_to_display test] | BlockOp BoolNot -> String
  (implode "BoolNot") | BlockOp (LenEq num') -> item_with_num (implode
  "LenEq") num' | BlockOp (TagEq num') -> item_with_num (implode
  "TagEq") num' | BlockOp LengthBlock -> String (implode "LengthBlock")
  | BlockOp BoundsCheckBlock -> String (implode "BoundsCheckBlock") |
  BlockOp (ConsExtend num') -> item_with_num (implode "ConsExtend") num'
  | BlockOp (FromList num') -> item_with_num (implode "FromList") num' |
  BlockOp ListAppend -> String (implode "ListAppend") | BlockOp
  (Constant c) -> Item NONE (implode "Constant") [const_to_display c] |
  BlockOp Equal -> String (implode "Equal") | BlockOp (EqualConst c) ->
  Item NONE (implode "EqualConst") [const_part_to_display c] | BlockOp
  (Build bs) -> Item NONE (implode "Build") (MAP const_part_to_display
  bs) | MemOp Ref -> String (implode "Ref") | MemOp Update -> String
  (implode "Update") | MemOp El -> String (implode "El") | MemOp Length
  -> String (implode "Length") | MemOp LengthByte -> String (implode
  "LengthByte") | MemOp (RefByte b) -> Item NONE (implode "RefByte")
  [bool_to_display b] | MemOp RefArray -> String (implode "RefArray") |
  MemOp DerefByte -> String (implode "DerefByte") | MemOp UpdateByte ->
  String (implode "UpdateByte") | MemOp ConcatByteVec -> String (implode
  "ConcatByteVec") | MemOp (CopyByte b) -> Item NONE (implode
  "CopyByte") [bool_to_display b] | MemOp FromListByte -> String
  (implode "FromListByte") | MemOp ToListByte -> String (implode
  "ToListByte") | MemOp LengthByteVec -> String (implode
  "LengthByteVec") | MemOp DerefByteVec -> String (implode
  "DerefByteVec") | MemOp BoundsCheckArray -> String (implode
  "BoundsCheckArray") | MemOp (BoundsCheckByte b) -> Item NONE (implode
  "BoundsCheckByte") [bool_to_display b] | MemOp closLang_ConfigGC ->
  String (implode "ConfigGC") | MemOp (StringCmp b opb) -> Item NONE
  (implode "StringCmp") [bool_to_display b;
                              opb_to_display opb] | MemOp XorByte ->
                                String (implode "XorByte") | MemOp
                                (MutCons tag i) -> item_with_nums
                                (implode "MutCons") [tag; i] | MemOp
                                UpdateCons -> String (implode
                                "UpdateCons") | MemOp FinaliseCons ->
                                String (implode "FinaliseCons") | Label
                                num' -> Item NONE (implode "Label")
                                [String (attach_name ns (SOME num'))] |
                                FFI s -> Item NONE (implode "FFI")
                                [string_imp s] | IntOp (Const i) -> Item
                                NONE (implode "Const") [int_to_display
                                i] | IntOp Add -> String (implode "Add")
                                | IntOp Sub -> String (implode "Sub") |
                                IntOp Mult -> String (implode "Mult") |
                                IntOp Div -> String (implode "Div") |
                                IntOp Mod -> String (implode "Mod") |
                                IntOp Less -> String (implode "Less") |
                                IntOp LessEq -> String (implode
                                "LessEq") | IntOp Greater -> String
                                (implode "Greater") | IntOp GreaterEq ->
                                String (implode "GreaterEq") | IntOp
                                (LessConstSmall num') -> item_with_num
                                (implode "LessConstSmall") num' | WordOp
                                (WordOpw ws op) -> Item NONE (implode
                                "WordOp")
                              [word_size_to_display ws;
                              opw_to_display op] | WordOp (WordShift
                                ws sh num') -> Item NONE (implode
                                "WordShift")
                              [word_size_to_display ws;
                              shift_to_display sh;
                              num_to_display num'] | WordOp (WordTest
                                ws test) -> Item NONE (implode
                                "WordTest")
                              [word_size_to_display ws;
                              test_to_display test] | WordOp
                                WordFromInt -> String (implode
                                "WordFromInt") | WordOp WordToInt ->
                                String (implode "WordToInt") | WordOp
                                (WordFromWord b) -> Item NONE
                                (implode "WordFromWord")
                                [bool_to_display b] | WordOp (FP_cmp
                                cmp) -> fp_cmp_to_display cmp |
                                WordOp (FP_uop op) ->
                                fp_uop_to_display op | WordOp (FP_bop
                                op) -> fp_bop_to_display op | WordOp
                                (FP_top op) -> fp_top_to_display op |
                                Install -> String (implode "Install")
                                | ThunkOp t -> thunk_op_to_display t)`;;

let commas_def = cake_define
  `presLang_commas x1 =
      match x1 with
        [] -> (implode "")
      | [x] -> x
      | (x :: xs) -> ^ (^ x (implode ",")) (presLang_commas xs)`;;
hol4_overload "commas" "presLang_commas";;

(* The clos_to_display ns function uses the same approach to de bruijn
   indices as the pat_to_display function *)
let _ = size_thms "exp";;
let _ = size_thms "list";;
let _ = size_thms "pair";;
(* HOL4 termination: >> rw[list_size_pair_size_MAP_FST_SND] *)
let clos_to_display_def = cake_define_wf
  `MEASURE (\x. match x with INL (_8,_9,e) -> exp_size e | INR (INL
  (_10,_11,e)) -> list_size exp_size e | INR (INR (INL
  (_12,_13,_14,es))) -> list_size exp_size es | INR (INR (INR
  (_15,_16,_17,_18,es))) -> list_size (pair_size I exp_size) es)`
  `(clos_to_display ns h (Var t n) =
     Item (SOME t) (implode "var") [display_num_as_varn (h - n - 1)])
       /\
   (clos_to_display ns h (If t x1 x2 x3) =
     Item (SOME t) (implode "if") [clos_to_display ns h x1;
       clos_to_display ns h x2;
         clos_to_display ns h x3]) /\
   (clos_to_display ns h (closLang_Let t xs x) =
     separate_lines (implode "let")
         [Tuple (clos_to_display_lets ns h (LENGTH xs - 1) xs);
             clos_to_display ns (h + LENGTH xs) x]) /\
   (clos_to_display ns h (Raise t x) =
     Item (SOME t) (implode "raise") [clos_to_display ns h x]) /\
   (clos_to_display ns h (Tick t x) =
     Item (SOME t) (implode "tick") [clos_to_display ns h x]) /\
   (clos_to_display ns h (Handle t x y) =
     Item (SOME t) (implode "handle")
         [clos_to_display ns h x; display_num_as_varn h;
             clos_to_display ns (h + 1) y]) /\
   (clos_to_display ns h (Call t ticks dest xs) =
     Item (SOME t) (implode "call")
       ([num_to_display ticks; String (attach_name ns (SOME dest))]
         ++
        (clos_to_display_list ns h xs))) /\
   (clos_to_display ns h (App t opt_n x xs) =
     Item (SOME t) (implode "app")
         ([(\f opt. match opt with NONE -> empty_item (implode
           "none") | SOME opt' -> Item NONE (implode "some") [f opt'])
           num_to_display opt_n;
           clos_to_display ns h x] ++ (clos_to_display_list ns h
             xs))) /\
   (clos_to_display ns h (Fn name_hint n1 n2 vn x) =
     Item (SOME None) (add_name_hint (implode "fn") name_hint)
         [(\f opt. match opt with NONE -> empty_item (implode "none")
           | SOME opt' -> Item NONE (implode "some") [f opt'])
           num_to_display n1;
          (\f opt. match opt with NONE -> empty_item (implode "none")
            | SOME opt' -> Item NONE (implode "some") [f opt']) ((\f xs.
            displayLang_Tuple (MAP f xs)) num_to_display) n2;
          (\f xs. displayLang_Tuple (MAP f xs)) string_imp
            (num_to_varn_list h vn);
          clos_to_display ns h x]) /\
   (clos_to_display ns h (closLang_Letrec name_hint n1 n2 es e) =
     Item (SOME None) (add_name_hint (implode "letrec") (commas
       name_hint))
         [(\f opt. match opt with NONE -> empty_item (implode "none")
           | SOME opt' -> Item NONE (implode "some") [f opt'])
           num_to_display n1;
          (\f opt. match opt with NONE -> empty_item (implode "none")
            | SOME opt' -> Item NONE (implode "some") [f opt']) ((\f xs.
            displayLang_Tuple (MAP f xs)) num_to_display) n2;
          Tuple (clos_to_display_letrecs ns h (LENGTH es - 1) (LENGTH
            es) es);
          clos_to_display ns h e]) /\
   (clos_to_display ns h (Op t op xs) =
     Item (SOME t) (implode "op") (clos_op_to_display LN op ::
         (clos_to_display_list ns h xs))) /\
   (clos_to_display_list ns h [] = []) /\
   (clos_to_display_list ns h (x :: xs) =
     clos_to_display ns h x :: clos_to_display_list ns h xs) /\
   (clos_to_display_lets ns h i [] = []) /\
   (clos_to_display_lets ns h i (x :: xs) =
     Tuple [display_num_as_varn (h + i); String (implode "<-");
       clos_to_display ns h x] :: clos_to_display_lets ns h (i - 1) xs)
       /\
   (clos_to_display_letrecs ns h i len [] = []) /\
   (clos_to_display_letrecs ns h i len ((vn,e) :: es) =
     Tuple [display_num_as_varn (h + i);
         (\f xs. displayLang_Tuple (MAP f xs)) string_imp
           (num_to_varn_list ((h + len) - 1) vn);
         clos_to_display ns (h + len + vn) e] ::
           clos_to_display_letrecs ns h (i - 1) len es)`;;

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

let _ = size_thms "exp";;
let _ = size_thms "list";;
(* HOL4 termination: *)
let bvl_to_display_def = cake_define_wf
  `MEASURE (\x.
     match x with
       INL (ns,h,x) -> exp_size x | INR (INL (ns,h,xs)) -> list_size
         exp_size xs | INR (INR (ns,h,i,xs)) -> list_size exp_size xs)`
  `(bvl_to_display ns h (Var n) =
     Item NONE (implode "var") [display_num_as_varn (h - n - 1)]) /\
   (bvl_to_display ns h (If x1 x2 x3) =
     Item NONE (implode "if") [bvl_to_display ns h x1; bvl_to_display
       ns h x2;
         bvl_to_display ns h x3]) /\
   (bvl_to_display ns h (bvl_Let xs x) =
     separate_lines (implode "let")
         (bvl_to_display_lets ns h (LENGTH xs - 1) xs ++
             [bvl_to_display ns (h + LENGTH xs) x])) /\
   (bvl_to_display ns h (Raise x) =
     Item NONE (implode "raise") [bvl_to_display ns h x]) /\
   (bvl_to_display ns h (Tick x) =
     Item NONE (implode "tick") [bvl_to_display ns h x]) /\
   (bvl_to_display ns h (Handle x y) =
     Item NONE (implode "handle")
         [bvl_to_display ns h x; display_num_as_varn h;
             bvl_to_display ns (h + 1) y]) /\
   (bvl_to_display ns h (Call ticks dest xs) =
     Item NONE (implode "call")
          (String (attach_name ns dest) ::
           (bvl_to_display_list ns h xs))) /\
   (bvl_to_display ns h (Force loc n) =
     Item NONE (implode "force")
          [display_num_as_varn (h - n - 1); String (attach_name ns
            (SOME loc))]) /\
   (bvl_to_display ns h (Op op xs) =
     Item NONE (implode "op") (clos_op_to_display ns op ::
                              (bvl_to_display_list ns h xs))) /\
   (bvl_to_display_list ns h [] = []) /\
   (bvl_to_display_list ns h (x :: xs) =
     bvl_to_display ns h x :: bvl_to_display_list ns h xs) /\
   (bvl_to_display_lets ns h i [] = []) /\
   (bvl_to_display_lets ns h i (x :: xs) =
     Tuple [display_num_as_varn (h + i); String (implode "<-");
       bvl_to_display ns h x] :: bvl_to_display_lets ns h (i - 1) xs)`;;

let bvl_fun_to_display_def = cake_define
  `bvl_fun_to_display names (n,argc,body) =
     Tuple [String (implode "func");
            String (attach_name names (SOME n));
            Tuple (REVERSE (GENLIST display_num_as_varn argc));
            bvl_to_display names argc body]`;;

(* bvi to displayLang *)

let _ = size_thms "exp";;
let _ = size_thms "list";;
(* HOL4 termination: *)
let bvi_to_display_def = cake_define_wf
  `MEASURE (\x.
     match x with
       INL (ns,h,x) -> exp_size x | INR (INL (ns,h,xs)) -> list_size
         exp_size xs | INR (INR (ns,h,i,xs)) -> list_size exp_size xs)`
  `(bvi_to_display ns h (Var n) =
     Item NONE (implode "var") [display_num_as_varn (h - n - 1)]) /\
   (bvi_to_display ns h (If x1 x2 x3) =
     Item NONE (implode "if") [bvi_to_display ns h x1; bvi_to_display
       ns h x2;
         bvi_to_display ns h x3]) /\
   (bvi_to_display ns h (bvi_Let xs x) =
     separate_lines (implode "let")
         (bvi_to_display_lets ns h (LENGTH xs - 1) xs ++
             [bvi_to_display ns (h + LENGTH xs) x])) /\
   (bvi_to_display ns h (Raise x) =
     Item NONE (implode "raise") [bvi_to_display ns h x]) /\
   (bvi_to_display ns h (Tick x) =
     Item NONE (implode "tick") [bvi_to_display ns h x]) /\
   (bvi_to_display ns h (Call ticks dest xs handler) =
     Item NONE (implode "call")
          ((String (attach_name ns dest) ::
           (bvi_to_display_list ns h xs)) ++
           (match handler with NONE -> [] | SOME e -> [Item NONE
             (implode "handler") [display_num_as_varn h;
                              empty_item (implode "->");
                              bvi_to_display ns (h + 1) e]]))) /\
   (bvi_to_display ns h (Force loc n) =
     Item NONE (implode "force")
          [display_num_as_varn (h - n - 1); String (attach_name ns
            (SOME loc))]) /\
   (bvi_to_display ns h (Op op xs) =
     Item NONE (implode "op") (clos_op_to_display ns op ::
                              (bvi_to_display_list ns h xs))) /\
   (bvi_to_display ns h (Return xs) =
     Item NONE (implode "return") (bvi_to_display_list ns h xs)) /\
   (bvi_to_display ns h (LetCall rets ticks dest xs y) =
     separate_lines (implode "letcall")
         [Item NONE (implode "call")
            (String (attach_name ns (SOME dest)) ::
              bvi_to_display_list ns h xs);
          Tuple (REVERSE (GENLIST (\i. display_num_as_varn (h + i))
            rets));
          bvi_to_display ns (h + rets) y]) /\
   (bvi_to_display_list ns h [] = []) /\
   (bvi_to_display_list ns h (x :: xs) =
     bvi_to_display ns h x :: bvi_to_display_list ns h xs) /\
   (bvi_to_display_lets ns h i [] = []) /\
   (bvi_to_display_lets ns h i (x :: xs) =
     Tuple [display_num_as_varn (h + i); String (implode "<-");
       bvi_to_display ns h x] :: bvi_to_display_lets ns h (i - 1) xs)`;;

let bvi_fun_to_display_def = cake_define
  `bvi_fun_to_display names (n,argc,body) =
     Tuple [String (implode "func");
            String (attach_name names (SOME n));
            Tuple (REVERSE (GENLIST display_num_as_varn argc));
            bvi_to_display names argc body]`;;

(* dataLang *)

let num_set_to_display_def = cake_define
  `num_set_to_display ns =
     String (concat [(implode "{");
                      commas (MAP toString (MAP FST (toSortedAList
                        ns)));
                      (implode "}")])`;;

let data_seqs_def = cake_define
  `data_seqs z =
     (match z with dataLang_Seq x y -> Append (data_seqs x)
       (data_seqs y) | _19 -> List [z])`;;

(* HOL4 termination: *)
let data_prog_to_display_def = cake_define_wf
  `MEASURE (\x.
     match x with
       INL (k,_20,_21) -> k | INR (k,_22,_23) -> k)`
  `data_prog_to_display k ns prog =
        match (k,prog) with
          (0,prog) -> empty_item (implode "...")
        | ((SUC k),prog) ->
         match prog with dataLang_Skip -> empty_item (implode "skip")
           | dataLang_Move x y -> Tuple
           [num_to_display x; String (implode ":="); num_to_display
             y] | Call rets target args NONE -> Item NONE (implode
             "call")
           [(\f opt. match opt with NONE -> empty_item (implode
             "none") | SOME opt' -> Item NONE (implode "some") [f opt'])
             (\(x,y). Tuple
                   [(\f xs. displayLang_Tuple (MAP f xs))
                     num_to_display x;
                    num_set_to_display y]) rets;
               String (attach_name ns target);
               (\f xs. displayLang_Tuple (MAP f xs)) num_to_display
                 args;
               empty_item (implode "none")] | Call rets target args
                 (SOME (v,handler)) -> Item NONE (implode "call")
           [(\f opt. match opt with NONE -> empty_item (implode
             "none") | SOME opt' -> Item NONE (implode "some") [f opt'])
             (\(x,y). Tuple
                   [(\f xs. displayLang_Tuple (MAP f xs))
                     num_to_display x;
                    num_set_to_display y]) rets;
               String (attach_name ns target);
               (\f xs. displayLang_Tuple (MAP f xs)) num_to_display
                 args;
               Item NONE (implode "some") [Tuple [num_to_display v;
                   data_prog_to_display k ns handler]]] | Force ret
                     loc src -> Item NONE (implode "force")
           [(\f opt. match opt with NONE -> empty_item (implode
             "none") | SOME opt' -> Item NONE (implode "some") [f opt'])
             (\(x,y). Tuple
                   [num_to_display x; num_set_to_display y]) ret;
            num_to_display loc;
            num_to_display src] | Assign n op args n_set -> Tuple
           [num_to_display n;
            String (implode ":=");
            clos_op_to_display ns op;
               (\f xs. displayLang_Tuple (MAP f xs)) num_to_display
                 args;
               (\f opt. match opt with NONE -> empty_item (implode
                 "none") | SOME opt' -> Item NONE (implode "some") [f
                 opt']) num_set_to_display n_set] | Seq x y ->
           (let xs = append (Append (data_seqs x) (data_seqs y)) in
              separate_lines (implode "seq")
                (data_prog_to_display_list k ns xs)) | If n x y -> Item
                NONE (implode "if")
           [num_to_display n; data_prog_to_display k ns x;
             data_prog_to_display k ns y] | MakeSpace n ns -> Item NONE
             (implode "make_space")
           [num_to_display n; num_set_to_display ns] | Raise n ->
             Item NONE (implode "raise") [num_to_display n] | Return ns
             -> Item NONE (implode "return") [(\f xs. displayLang_Tuple
             (MAP f xs)) num_to_display ns] | Tick -> empty_item
             (implode "tick")
        | (k,[]) -> []
        | (k,(x :: xs)) ->
       match k with
         0 -> [] | SUC k ->
       data_prog_to_display k ns x :: data_prog_to_display_list k
         ns xs`;;

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
  -> Item NONE (implode "Binop")
         [asm_binop_to_display bop; num_to_display n1; num_to_display
           n2;
             asm_reg_imm_to_display reg_imm'] | asm_Shift sh n1 n2 n3
               -> Item NONE (implode "Shift")
         [shift_to_display sh;
          num_to_display n1;
          num_to_display n2;
          asm_reg_imm_to_display n3] | Div n1 n2 n3 ->
            item_with_nums (implode "Div") [n1; n2; n3] | LongMul n1
            n2 n3 n4 -> item_with_nums (implode "LongMul") [n1; n2;
            n3; n4] | LongDiv n1 n2 n3 n4 n5 -> item_with_nums
            (implode "LongDiv") [n1; n2; n3; n4; n5] | AddCarry n1 n2
            n3 n4 -> item_with_nums (implode "AddCarry") [n1; n2; n3;
            n4] | AddOverflow n1 n2 n3 n4 -> item_with_nums (implode
            "AddOverflow") [n1; n2; n3; n4] | SubOverflow n1 n2 n3 n4
            -> item_with_nums (implode "SubOverflow") [n1; n2; n3;
            n4])`;;

let asm_addr_to_display_def = cake_define
  `asm_addr_to_display addr' = (match addr' with Addr reg w -> Item NONE
  (implode "Addr")
                          [num_to_display reg; word_to_display w])`;;

let asm_memop_to_display_def = cake_define
  `asm_memop_to_display op = (match op with Load -> empty_item
  (implode "Load") | Load8 -> empty_item (implode "Load8") | Load16
  -> empty_item (implode "Load16") | Load32 -> empty_item (implode
  "Load32") | Store -> empty_item (implode "Store") | Store8 ->
  empty_item (implode "Store8") | Store16 -> empty_item (implode
  "Store16") | Store32 -> empty_item (implode "Store32"))`;;

let asm_cmp_to_display_def = cake_define
  `asm_cmp_to_display op = (match op with Equal -> empty_item
  (implode "Equal") | Lower -> empty_item (implode "Lower") | Less ->
  empty_item (implode "Less") | Test -> empty_item (implode "Test") |
  NotEqual -> empty_item (implode "NotEqual") | NotLower ->
  empty_item (implode "NotLower") | NotLess -> empty_item (implode
  "NotLess") | NotTest -> empty_item (implode "NotTest"))`;;

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
  (implode "Skip") | Const reg w -> Item NONE (implode "Const")
  [num_to_display reg;
                              word_to_display w] | Arith a -> Item
                                NONE (implode "Arith")
                                [asm_arith_to_display a] | Mem mop r
                                addr' -> Item NONE (implode "Mem")
                                [asm_memop_to_display mop;
         num_to_display r; asm_addr_to_display addr'] | FP fp ->
           Item NONE (implode "FP") [asm_fp_to_display fp])`;;

let asm_asm_to_display_def = cake_define
  `asm_asm_to_display inst' = (match inst' with Inst i ->
  asm_inst_to_display i | Jump w -> item_with_word (implode "Jump") w |
  JumpCmp c r to w -> Item NONE (implode "JumpCmp")
       [asm_cmp_to_display c; num_to_display r;
         asm_reg_imm_to_display to;
        word_to_display w] | Call w -> item_with_word (implode
          "Call") w | JumpReg r -> item_with_num (implode "JumpReg>")
          r | Loc r w -> Item NONE (implode "Loc") [num_to_display r;
          word_to_display w])`;;

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
       (stack_seqs y) | _24 -> List [z])`;;

(* HOL4 termination: *)
let stack_prog_to_display_def = cake_define_wf
  `MEASURE (\x.
     match x with
       INL (k,_26,_27) -> k | INR (k,_28,_29) -> k)`
  `stack_prog_to_display k ns prog =
      match (k,prog) with
        (0,prog) -> empty_item (implode "...")
      | ((SUC k),stackLang_Skip) -> empty_item (implode "skip")
      | ((SUC k),(Inst i)) -> asm_inst_to_display i
      | ((SUC k),(Get n sn)) -> Tuple
     [num_to_display n; String (implode "<-"); store_name_to_display
       sn]
      | ((SUC k),(Set sn n)) -> Tuple
     [store_name_to_display sn; String (implode "<-"); num_to_display
       n]
      | ((SUC k),(OpCurrHeap b n1 n2)) -> Tuple
     [num_to_display n1; String (implode ":="); String (implode
       "CurrHeap");
      asm_binop_to_display b; num_to_display n2]
      | ((SUC k),(Call rh tgt eh)) ->
     Item NONE (implode "call")
          [(match rh with NONE -> empty_item (implode "tail") | SOME
            (p,lr,l1,l2) ->
                Item NONE (implode "returning")
                     [num_to_display lr;
                      String (attach_name ns (SOME l1));
                      num_to_display l2;
                      stack_prog_to_display k ns p]);
          (match tgt with INL l -> Item NONE (implode "direct")
            [String (attach_name ns (SOME l))] | INR r -> item_with_num
            (implode "reg") r);
          (match eh with NONE -> empty_item (implode "no_handler") |
            SOME (p,l1,l2) ->
               Item NONE (implode "handler")
                    [String (attach_name ns (SOME l1));
                     num_to_display l2;
                     stack_prog_to_display k ns p])]
      | ((SUC k),(Seq x y)) ->
         (let xs = append (Append (stack_seqs x) (stack_seqs y)) in
            separate_lines (implode "seq")
              (stack_prog_to_display_list k ns xs))
      | ((SUC k),(If c n to x y)) -> Item NONE (implode "if")
         [Tuple [asm_cmp_to_display c; num_to_display n;
           asm_reg_imm_to_display to];
          stack_prog_to_display k ns x;
          stack_prog_to_display k ns y]
      | ((SUC k),(Loop x)) -> Item NONE (implode "loop")
         [stack_prog_to_display k ns x]
      | ((SUC k),(JumpLower n1 n2 n3)) ->
      item_with_nums (implode "jump_lower") [n1; n2; n3]
      | ((SUC k),(Alloc n)) -> item_with_num (implode "alloc") n
      | ((SUC k),(StoreConsts n1 n2 _25)) -> item_with_nums (implode
        "store_consts") [n1; n2]
      | ((SUC k),(Raise n)) -> item_with_num (implode "raise") n
      | ((SUC k),(Return n)) -> item_with_num (implode "return") n
      | ((SUC k),(Break n)) -> item_with_num (implode "break") n
      | ((SUC k),(Continue n)) -> item_with_num (implode "continue")
        n
      | ((SUC k),(FFI nm cp cl ap al ra)) -> Item NONE (implode
        "ffi")
         (string_imp nm :: MAP num_to_display [cp; cl; ap; al; ra])
      | ((SUC k),(Tick)) -> empty_item (implode "tick")
      | ((SUC k),(LocValue n1 n2 n3)) ->
      Item NONE (implode "loc_value") [num_to_display n1;
                             String (attach_name ns (SOME n2));
                             num_to_display n3]
      | ((SUC k),(Install n1 n2 n3 n4 n5)) ->
      item_with_nums (implode "install") [n1; n2; n3; n4; n5]
      | ((SUC k),(ShMemOp mop r a)) ->
      Item NONE (implode "sh_mem") [asm_memop_to_display mop;
                              num_to_display r; asm_addr_to_display
                                a]
      | ((SUC k),(CodeBufferWrite n1 n2)) ->
      item_with_nums (implode "code_buffer_write") [n1; n2]
      | ((SUC k),(DataBufferWrite n1 n2)) ->
      item_with_nums (implode "data_buffer_write") [n1; n2]
      | ((SUC k),(RawCall n)) ->
      Item NONE (implode "raw_call") [String (attach_name ns (SOME
        n))]
      | ((SUC k),(StackAlloc n)) -> item_with_num (implode
        "stack_alloc") n
      | ((SUC k),(StackFree n)) -> item_with_num (implode
        "stack_free") n
      | ((SUC k),(StackStore n m)) ->
      Tuple [String (^ (^ (^ (implode "stack[") (num_to_hex_mlstring
        n)) (implode "] := ")) (toString m))]
      | ((SUC k),(StackStoreAny n m)) ->
      Tuple [String (^ (^ (^ (implode "stack[var ") (toString n))
        (implode "] := ")) (toString m))]
      | ((SUC k),(StackLoad n m)) ->
      Tuple [String (concat [toString n;
                             (implode " := stack[");
                             num_to_hex_mlstring m; (implode "]")])]
      | ((SUC k),(StackLoadAny n m)) ->
      Tuple [String (concat [toString n;
                             (implode " := stack[var ");
                             toString m; (implode "]")])]
      | ((SUC k),(StackGetSize n)) -> item_with_num (implode
        "stack_get_size") n
      | ((SUC k),(StackSetSize n)) -> item_with_num (implode
        "stack_set_size") n
      | ((SUC k),(BitmapLoad n m)) ->
      Tuple [String (concat [toString n;
                             (implode " := bitmap[");
                             num_to_hex_mlstring m;
                             (implode "]")])]
      | ((SUC k),(Halt n)) -> item_with_num (implode "halt") n
      | (k,[]) -> []
      | (k,(x :: xs)) ->
     match k with 0 -> [] | SUC k ->
     stack_prog_to_display k ns x :: stack_prog_to_display_list k
       ns xs`;;

let stack_fun_to_display_def = cake_define
  `stack_fun_to_display names (n,body) =
     Tuple [String (implode "func");
            String (attach_name names (SOME n));
            stack_prog_to_display 1000000000 names body]`;;

(* labLang *)

let lab_asm_to_display_def = cake_define
  `lab_asm_to_display ns la = (match la with labLang_Jump (Lab s n) ->
         Item NONE (implode "jump")
           [String (attach_name ns (SOME s)); num_to_display n] |
             JumpCmp c r ri (Lab s n) ->
         Item NONE (implode "jump_cmp")
           [Tuple [asm_cmp_to_display c; num_to_display r;
                   asm_reg_imm_to_display ri];
            String (attach_name ns (SOME s)); num_to_display n] |
              Call (Lab s n) ->
         Item NONE (implode "call")
           [String (attach_name ns (SOME s)); num_to_display n] |
             LocValue r (Lab s n) ->
         Item NONE (implode "loc_value")
           [num_to_display r; String (attach_name ns (SOME s));
             num_to_display n] | CallFFI name -> Item NONE (implode
             "call_FFI") [string_imp name] | Install -> empty_item
             (implode "install") | Halt -> empty_item (implode
             "halt"))`;;

let lab_line_to_display_def = cake_define
  `lab_line_to_display ns line = (match line with Label s n le ->
         Item NONE (implode "label") [String (attach_name ns (SOME
           s)); num_to_display n] | Asm aoc enc len -> (match aoc with
           Asmi i -> Item NONE (implode "asm") [asm_asm_to_display i] |
           Cbw r1 r2 -> item_with_nums (implode "cbw") [r1; r2] |
           ShareMem mop r a -> Item NONE (implode "share_mem")
           [asm_memop_to_display mop;
                              num_to_display r;
                              asm_addr_to_display a]) | LabAsm la
                                pos enc len -> lab_asm_to_display ns
                                la)`;;

let lab_fun_to_display_def = cake_define
  `lab_fun_to_display names (Section n lines) =
     List (
            String (attach_name names (SOME n)) :: MAP
              (lab_line_to_display names) lines)`;;

(* wordLang *)

let word_seqs_def = cake_define
  `word_seqs z =
     (match z with wordLang_Seq x y -> Append (word_seqs x)
       (word_seqs y) | _30 -> List [z])`;;

let _ = size_thms "exp";;
let _ = size_thms "list";;
(* HOL4 termination: *)
let word_exp_to_display_def = cake_define_wf
  `MEASURE (\x. match x with INL v -> exp_size ARB v | INR v ->
  list_size exp_size ARB v)`
  `(
     word_exp_to_display (wordLang_Const v) = item_with_word (implode
       "Const") v) /\
   (
     word_exp_to_display (Var n) = item_with_num (implode "Var") n)
       /\
   (
     word_exp_to_display (Lookup st) = Item NONE (implode "Lookup")
       [store_name_to_display st]) /\
   (
     word_exp_to_display (Load exp2) = Item NONE (implode "MemLoad")
       [word_exp_to_display exp2]) /\
   (
     word_exp_to_display (Op bop exs) = Item NONE (implode "Op") (
         asm_binop_to_display bop :: word_exp_to_display_list exs))
           /\
   (
     word_exp_to_display (Shift sh exp exp1) = Item NONE (implode
       "Shift") [
       shift_to_display sh;
       word_exp_to_display exp;
       word_exp_to_display exp1]) /\
   (word_exp_to_display_list [] = []) /\
   (word_exp_to_display_list (x :: xs) =
     word_exp_to_display x :: word_exp_to_display_list xs)`;;

let ws_to_display_def = cake_define
  `ws_to_display [] = [] /\
   ws_to_display ((b,x) :: xs) =
     Tuple [bool_to_display b; word_to_display x] :: ws_to_display
       xs`;;

let num_sets_to_display_def = cake_define
  `num_sets_to_display (l,r) =
     Tuple [num_set_to_display l;
            num_set_to_display r]`;;

(* HOL4 termination: *)
let word_prog_to_display_def = cake_define_wf
  `MEASURE (\x. match x with INL (k,_31) -> k | INR (INL (k,_32)) -> k
  | INR (INR (INL (k,_33))) -> k | INR (INR (INR (k,_34))) -> k)`
  `word_prog_to_display k ns x =
        match (k,x) with
          (0,x) -> empty_item (implode "...")
        | ((SUC k),Skip) -> empty_item (implode "skip")
        | ((SUC k),(Move n mvs)) -> Item NONE (implode "move")
       [num_to_display n; displayLang_Tuple (MAP (\(n1,n2). Tuple
           [num_to_display n1;
            String (implode ":=");
            num_to_display n2]) mvs)]
        | ((SUC k),(Inst i)) ->
       Item NONE (implode "inst") [asm_inst_to_display i]
        | ((SUC k),(Assign n exp)) ->
        Tuple [num_to_display n;
               String (implode ":=");
               word_exp_to_display exp]
        | ((SUC k),(Get n sn)) -> Tuple
       [num_to_display n; String (implode "<-");
         store_name_to_display sn]
        | ((SUC k),(Set sn exp)) -> Tuple
       [store_name_to_display sn; String (implode "<-");
         word_exp_to_display exp]
        | ((SUC k),(Store exp n)) -> Tuple
       [String (implode "mem"); word_exp_to_display exp;
        String (implode ":="); num_to_display n]
        | ((SUC k),(ShareInst mop n exp)) -> Tuple
       [String (implode "share_mem"); asm_memop_to_display mop;
        num_to_display n; word_exp_to_display exp]
        | ((SUC k),(MustTerminate prog)) -> Item NONE (implode
          "must_terminate")
       [word_prog_to_display k ns prog]
        | ((SUC k),(Call a b c d)) -> Item NONE (implode "call")
       [word_prog_to_display_ret k ns a;
        (\f opt. match opt with NONE -> empty_item (implode "none") |
          SOME opt' -> Item NONE (implode "some") [f opt']) (\n. String
          (attach_name ns (SOME n))) b;
        (\f xs. displayLang_Tuple (MAP f xs)) num_to_display c;
        word_prog_to_display_handler k ns d]
        | ((SUC k),(OpCurrHeap b n1 n2)) -> Tuple
       [num_to_display n1; String (implode ":="); String (implode
         "CurrHeap");
        asm_binop_to_display b; num_to_display n2]
        | ((SUC k),(Seq prog1 prog2)) ->
       (let xs = append (Append (word_seqs prog1) (word_seqs prog2))
         in
          separate_lines (implode "seq") (word_prog_to_display_list k
            ns xs))
        | ((SUC k),(If cmp n reg p1 p2)) ->
       Item NONE (implode "if")
         [Tuple [asm_cmp_to_display cmp;
                 num_to_display n;
                 asm_reg_imm_to_display reg];
          word_prog_to_display k ns p1; word_prog_to_display k ns p2]
        | ((SUC k),(Loop ns1 p ns2)) ->
       Item NONE (implode "Loop")
         [num_set_to_display ns1;
          word_prog_to_display k ns p;
          num_set_to_display ns2]
        | ((SUC k),(Alloc n ms)) -> Item NONE (implode "alloc")
       [num_to_display n; num_sets_to_display ms]
        | ((SUC k),(StoreConsts a b c d ws)) -> Item NONE (implode
          "store_consts")
       [num_to_display a;
        num_to_display b;
        num_to_display c;
        num_to_display d;
        Tuple (ws_to_display ws)]
        | ((SUC k),(Raise n)) -> item_with_num (implode "raise") n
        | ((SUC k),(Break n)) -> item_with_num (implode "break") n
        | ((SUC k),(Continue n)) -> item_with_num (implode
          "continue") n
        | ((SUC k),(Return n vs)) ->
        Item NONE (implode "return")
          [num_to_display n;
           Tuple (MAP num_to_display vs)]
        | ((SUC k),Tick) -> empty_item (implode "tick")
        | ((SUC k),(LocValue n1 n2)) ->
       Item NONE (implode "loc_value") [String (attach_name ns (SOME
         n1)); num_to_display n2]
        | ((SUC k),(Install n1 n2 n3 n4 ms)) ->
       Item NONE (implode "install") (
           MAP num_to_display [n1; n2; n3; n4] ++
             [num_sets_to_display ms])
        | ((SUC k),(CodeBufferWrite n1 n2)) ->
       item_with_nums (implode "code_buffer_write") [n1; n2]
        | ((SUC k),(DataBufferWrite n1 n2)) ->
       item_with_nums (implode "data_buffer_write") [n1; n2]
        | ((SUC k),(FFI nm n1 n2 n3 n4 ms)) ->
       Item NONE (implode "ffi") (
           (string_imp nm :: MAP num_to_display [n1; n2; n3; n4]) ++
             [num_sets_to_display ms])
        | (k,[]) -> []
        | (k,(x :: xs)) ->
       match k with 0 -> [] | SUC k ->
       word_prog_to_display k ns x :: word_prog_to_display_list k ns
         xs
        | (k,NONE) -> empty_item (implode "tail")
        | (k,(SOME (vs,ms,prog,n2,n3))) ->
       match k with 0 -> empty_item (implode "...") | SUC k ->
       Item NONE (implode "returning") [Tuple [Tuple (MAP
         num_to_display vs); num_sets_to_display ms;
           word_prog_to_display k ns prog;
           String (attach_name ns (SOME n2));
           num_to_display n3]]
        | (k,NONE) -> empty_item (implode "no_handler")
        | (k,(SOME (n1,prog,n2,n3))) ->
       match k with 0 -> empty_item (implode "...") | SUC k ->
       Item NONE (implode "handler") [Tuple [num_to_display n1;
           word_prog_to_display k ns prog;
           String (attach_name ns (SOME n2));
           num_to_display n3]]`;;

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

let map_to_append_def = cake_define
  `map_to_append f [] = Nil /\
   map_to_append f (x :: xs) = Append (List (f x)) (map_to_append
     f xs)`;;

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
