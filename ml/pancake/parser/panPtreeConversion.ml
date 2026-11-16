(* ======================================================== *)
(*  panPtreeConversion: ported from HOL4's
    pancake/parser/panPtreeConversionScript.sml
    A definition theory, with 50 definitions and 5 theorems.  Needed
    by compiler.ml, from_pancake32Prog.ml and from_pancake64Prog.ml.  *)
(* ======================================================== *)

(**
 * Theory for translating the Pancake parse tree into the Pancake AST.
 *)

(*
 * We take some inspiration from the existing conversion theory
 * for CakeML.
 *
 * Created by Craig McLaughlin on 6/5/2022.
 *)

needs "basis/pure/mlint.ml";;
needs "basis/pure/mlmap.ml";;
needs "basis/pure/mlstring.ml";;
needs "lib/grammar.ml";;
needs "lib/integer_word.ml";;
needs "lib/location.ml";;
needs "lib/peg.ml";;
needs "lib/pegexec.ml";;
needs "lib/simpleSexpParse.ml";;
needs "pancake/panLang.ml";;
needs "pancake/parser/panLexer.ml";;
needs "pancake/parser/panPEG.ml";;
needs "semantics/ast.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "panPtreeConversion"
  ["mlint"; "mlmap"; "mlstring"; "panLang"; "panLexer"; "panPEG"];;
(* HOL4 ancestors outside the port: arithmetic combin *)

(** Set HOL to parse operations in following definition
  * for Option monad. *)

(* HOL4 panPtreeConversionScript.sml:21: the overload lift, which the port
   expands *)

(** Copied from tokenUtilsTheory: prevent a conflict between
  * panLexer$token and token$token. *)
let panPtreeConversion_destLf_def = new_definition
  `panPtreeConversion_destLf x1 =
     match x1 with
       Lf (x,_) -> SOME x
     | _ -> NONE`;;
add_simp panPtreeConversion_destLf_def;;

let panPtreeConversion_destTOK_def = new_definition
  `panPtreeConversion_destTOK x1' =
     match x1' with
       grammar_TOK t -> SOME t
     | _ -> NONE`;;
add_simp panPtreeConversion_destTOK_def;;
(** End copy *)

(** Copied from cmlptreeconversion *)
(* HOL4 panPtreeConversionScript.sml:35: the overload ', which the port
   expands *)

(* HOL4 panPtreeConversionScript.sml:37: the overload ptree_size, which the
   port expands *)
(* HOL4 panPtreeConversionScript.sml:38: the overload ptree1_size, which the
   port expands *)

let panPtreeConversion_tokcheck_def = new_definition
  `panPtreeConversion_tokcheck pt expected =
     match ((\f a. OPTION_BIND a f) panPtreeConversion_destTOK
       (panPtreeConversion_destLf pt)) with
       SOME actual -> actual = expected
     | NONE -> F`;;
(** End copy **)

let dest_annot_tok_def = new_definition
  `dest_annot_tok pt = match (OPTION_BIND (panPtreeConversion_destLf pt)
  panPtreeConversion_destTOK) with
       SOME (panLexer_AnnotCommentT c) -> SOME c
     | _ -> NONE`;;

let kw_def = new_definition
  `kw k = panLexer_KeywordT k`;;

let isNT_def = new_definition
  `isNT nodeNT ntm <=> FST nodeNT = INL ntm`;;

let argsNT_def = define_cases
  `(argsNT (Lf _) _ = NONE) /\
   (argsNT (Nd nodeNT args) ntm =
      if FST nodeNT = INL ntm then SOME args else NONE)`;;

let is_add_with_carry_def = new_definition
  `is_add_with_carry s <=> s = (implode "__add_with_carry__")`;;

let conv_int_def = new_definition
  `conv_int tree =
     match (\f a. OPTION_BIND a f) panPtreeConversion_destTOK
       (panPtreeConversion_destLf tree) with
       SOME (panLexer_IntT n) -> SOME n
     | _ -> NONE`;;

let conv_nat_def = new_definition
  `conv_nat tree =
     match conv_int tree with
       SOME n -> if n >= (&0) then SOME (num_of_int n) else NONE
     | _ -> NONE`;;

let conv_const_def = new_definition
  `conv_const t = OPTION_MAP (pan_Const o i2w) (conv_int t)`;;

let conv_ident_def = new_definition
  `conv_ident tree =
     match (\f a. OPTION_BIND a f) panPtreeConversion_destTOK
       (panPtreeConversion_destLf tree) with
       SOME (panLexer_IdentT s) -> SOME (implode s)
     | _ -> NONE`;;

let conv_ffi_ident_def = new_definition
  `conv_ffi_ident tree =
     match (\f a. OPTION_BIND a f) panPtreeConversion_destTOK
       (panPtreeConversion_destLf tree) with
       SOME (panLexer_ForeignIdent s) -> SOME (implode s)
     | _ -> NONE`;;

let conv_var_def = new_definition
  `conv_var t = OPTION_MAP (ast_Var pan_Global) (conv_ident t)`;;

(** Collection of binop expression nodes, n >= 2 *)
let binaryExps_def = new_definition
  `binaryExps = [EOrNT; EXorNT; EAndNT; EAddNT]`;;

let panExps_def = new_definition
  `panExps = [EMulNT]`;;

(** Subtraction must apply to only two subexpressions.
  * See the pancake semantics script. *)
let isSubOp_def = new_definition
  `isSubOp x1 =
   match x1 with
     pan_Op asm_Sub [e1; e2] -> T
   | _ -> F`;;

(* Convert a binary operator into its AST representation. *)
let conv_binop_def,conv_binop_ind = define_guess
  `conv_binop leaf =
     match leaf with
       Nd nodeNT args ->
        if isNT nodeNT AddOpsNT then
          match args with
            [leaf] -> conv_binop leaf
          | _ -> NONE
        else NONE
     | leaf ->
      if panPtreeConversion_tokcheck leaf panLexer_PlusT then SOME asm_Add
      else if panPtreeConversion_tokcheck leaf panLexer_MinusT then SOME
        asm_Sub
      else if panPtreeConversion_tokcheck leaf panLexer_AndT then SOME
        asm_And
      else if panPtreeConversion_tokcheck leaf panLexer_OrT then SOME asm_Or
      else if panPtreeConversion_tokcheck leaf panLexer_XorT then SOME
        asm_Xor
      else NONE`;;

let conv_panop_def,conv_panop_ind = define_guess
  `conv_panop leaf =
     match leaf with
       Nd nodeNT args ->
        if isNT nodeNT MulOpsNT then
          match args with
            [leaf] -> conv_panop leaf
          | _ -> NONE
        else NONE
     | leaf ->
      if panPtreeConversion_tokcheck leaf panLexer_StarT then SOME pan_Mul
      else NONE`;;

let conv_shift_def,conv_shift_ind = define_guess
  `conv_shift leaf =
     match leaf with
       Nd nodeNT args ->
      if isNT nodeNT ShiftOpsNT then
        match args with
          [leaf] -> conv_shift leaf
        | _ -> NONE
      else NONE
     | leaf ->
     if panPtreeConversion_tokcheck leaf panLexer_LslT then SOME Lsl
     else if panPtreeConversion_tokcheck leaf panLexer_LsrT then SOME Lsr
     else if panPtreeConversion_tokcheck leaf panLexer_AsrT then SOME Asr
     else if panPtreeConversion_tokcheck leaf panLexer_RorT then SOME Ror
     else NONE`;;

let conv_cmp_def,conv_cmp_ind = define_guess
  `conv_cmp leaf =
     match leaf with
       Nd nodeNT args ->
      if isNT nodeNT CmpOpsNT \/ isNT nodeNT EqOpsNT then
        match args with
          [leaf] -> conv_cmp leaf
        | _ -> NONE
      else NONE
     | leaf ->
     if panPtreeConversion_tokcheck leaf panLexer_EqT then SOME
       (asm_Equal,F)
     else if panPtreeConversion_tokcheck leaf panLexer_NeqT then SOME
       (asm_NotEqual,F)
     else if panPtreeConversion_tokcheck leaf panLexer_LessT then SOME
       (asm_Less,F)
     else if panPtreeConversion_tokcheck leaf panLexer_GeqT then SOME
       (asm_NotLess,F)
     else if panPtreeConversion_tokcheck leaf panLexer_GreaterT then SOME
       (asm_Less,T)
     else if panPtreeConversion_tokcheck leaf panLexer_LeqT then SOME
       (asm_NotLess,T)
     else if panPtreeConversion_tokcheck leaf panLexer_LowerT then SOME
       (asm_Lower,F)
     else if panPtreeConversion_tokcheck leaf panLexer_HigherT then SOME
       (asm_Lower,T)
     else if panPtreeConversion_tokcheck leaf panLexer_HigheqT then SOME
       (asm_NotLower,F)
     else if panPtreeConversion_tokcheck leaf panLexer_LoweqT then SOME
       (asm_NotLower,T)
     else NONE`;;

let conv_default_shape_def = new_definition
  `conv_default_shape tree =
     match (\f a. OPTION_BIND a f) panPtreeConversion_destTOK
       (panPtreeConversion_destLf tree) with SOME (panLexer_DefaultShT) -> SOME
       pan_One
         | _ -> NONE`;;

(** A single tree is smaller than the forest. *)
(* the termination relation that HOL4 gives is
     MEASURE (parsetree_size (K 0) (K 0) (K 0))
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 panPtreeConversionScript.sml:215-222: the tactic that proves the
   termination *)
let conv_Shape_def,conv_Shape_ind = define_guess
  `conv_Shape tree =
     match conv_default_shape tree with SOME s -> SOME s
     | _ ->
       (match conv_int tree with
         SOME n ->
           if n < (&1) then NONE
           else if n = (&1) then SOME pan_One
           else SOME (pan_Comb (REPLICATE (num_of_int n) pan_One))
       | NONE ->
           (match conv_ident tree with
             SOME id -> SOME (pan_Named id)
           | NONE ->
               (match argsNT tree ShapeCombNT with
                 SOME ts -> OPTION_MAP pan_Comb (OPT_MMAP conv_Shape ts)
               | _ -> NONE)))`;;

let conv_params_def,conv_params_ind = define_guess
  `conv_params as =
   match as with
     (CONS s (CONS t ps)) ->
       (match (conv_Shape s) with
          SOME sh ->
            (match (conv_ident t) with
               SOME v -> (OPTION_MAP (CONS (v,sh))) (conv_params ps)
             | _ -> NONE)
        | _ -> NONE)
   | [] -> SOME []
   | _ -> NONE`;;

(** Convert a expression parse tree into the corresponding AST.
  *
  * The definition is slightly complicated by the requirement that
  * subtraction must have exactly two children. All the other 'binop'
  * operations can have ≥ 2 arguments. See the Pancake semantics script
  * for precise details. *)
(* the clauses in 4 quotations: e is parsetree and exp; op is binop, panop
   and shift, which one quotation cannot typecheck *)
(* the termination relation that HOL4 gives is
     MEASURE (\x. match x with INL x -> (parsetree_size (K 0) (K 0) (K 0)) x
                                   | INR (INL x) -> (parsetree_size (K 0) (K 0)
                                     (K 0)) x
                                   | INR (INR (INL x)) -> (parsetree_size (K 0)
                                     (K 0) (K 0)) x
                                   | INR (INR (INR (INL x))) -> (parsetree_size
                                     (K 0) (K 0) (K 0)) x
                                   | INR (INR (INR (INR (INL x)))) -> list_size
                                     (parsetree_size (K 0) (K 0) (K 0)) (FST x)
                                   | INR (INR (INR (INR (INR (INL x))))) ->
                                     list_size (parsetree_size (K 0) (K 0) (K
                                       0))
                                     (FST x)
                                   | INR (INR (INR (INR (INR (INR x))))) ->
                                     list_size (parsetree_size (K 0) (K 0) (K
                                       0))
                                     (FST x))
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 panPtreeConversionScript.sml:377-400: the tactic that proves the
   termination *)
let conv_Exp_def,conv_Exp_ind = define_guess_clauses
  [`(conv_ArgList tree =
       if panPtreeConversion_tokcheck tree panLexer_NotT then SOME []
       else match argsNT tree ArgListNT with
           SOME (CONS t ts) -> OPT_MMAP conv_Exp (CONS t ts)
         | _ -> NONE) /\
    (conv_FieldList tree =
        match argsNT tree NmdFieldListNT with
          SOME (CONS t ts) -> OPT_MMAP conv_Field (CONS t ts)
        | _ -> NONE) /\
    (conv_Field tree =
        match argsNT tree NmdFieldNT with
          SOME [t1; t2] -> OPTION_BIND (conv_ident t1) (\fld. OPTION_BIND
              (conv_Exp t2) (\exp.
                             SOME (fld,exp)))
        | _ -> NONE) /\
    (conv_Exp (Nd nodeNT args) =
        if isNT nodeNT EFieldNT then
          match args with
            [] -> NONE
          | [t] -> conv_Exp t
          | CONS t ts -> FOLDL (\e t.
                            match conv_nat t with
                              SOME n -> OPTION_MAP2 pan_RField (SOME n) e
                            | NONE -> (match conv_ident t with
                              SOME i -> OPTION_MAP2 pan_NField (SOME i) e
                              | NONE -> NONE)) (conv_Exp t) ts
        else if isNT nodeNT RawStructNT then
          match args with
            [ts] -> OPTION_BIND (conv_ArgList ts) (\es.
                       SOME (pan_RStruct es))
          | _ -> NONE
        else if isNT nodeNT NmdStructNT then
          match args with
            [t1; t2] -> OPTION_BIND (conv_ident t1) (\nm. OPTION_BIND
                (conv_FieldList t2) (\flds.
                          SOME (pan_NStruct nm flds)))
          | _ -> NONE
        else if isNT nodeNT ENotNT then
          match args with
            [t] -> conv_Exp t
          | [_; t] -> OPTION_MAP (pan_Cmp asm_Equal (pan_Const (n2w 0)))
              (conv_Exp t)
          | _ -> NONE
        else if isNT nodeNT ELoadByteNT then
          match args with
            [t] -> OPTION_MAP pan_LoadByte (conv_Exp t)
          | _ -> NONE
        else if isNT nodeNT ELoad32NT then
          match args with
            [t] -> OPTION_MAP pan_Load32 (conv_Exp t)
          | _ -> NONE
        else if isNT nodeNT ELoadNT then
          match args with
            [t1; t2] -> OPTION_BIND (conv_Shape t1) (\s. OPTION_BIND
                (conv_Exp t2) (\e.
                           SOME (pan_Load s e)))
          | _ -> NONE
        else if isNT nodeNT ECmpNT \/ isNT nodeNT EEqNT then
          match args with
            [e] -> conv_Exp e
          | [e1; op; e2] -> OPTION_BIND (conv_Exp e1) (\e1'. OPTION_BIND
              (conv_cmp op) (\(op',b). OPTION_BIND (conv_Exp e2) (\e2'.
                              SOME (if b then pan_Cmp op' e2' e1'
                              else pan_Cmp op' e1' e2'))))
          | _ -> NONE
        else if isNT nodeNT ExpNT then
          // boolean or
          match args with
            [e] -> conv_Exp e
          | CONS e1 args' -> OPTION_BIND (OPT_MMAP conv_Exp (CONS e1
              args')) (\es.
                            SOME (pan_Cmp asm_NotEqual (pan_Const (n2w 0))
                                (pan_Op asm_Or es)))
          | _ -> NONE
        else if isNT nodeNT EBoolAndNT then
          match args with
            [e] -> conv_Exp e
          | CONS e1 args' -> OPTION_BIND (OPT_MMAP conv_Exp (CONS e1
              args')) (\es.
                            SOME (pan_Op asm_And (MAP (\e. pan_Cmp
                                asm_NotEqual (pan_Const (n2w 0)) e) es)))
          | _ -> NONE
        else if isNT nodeNT EShiftNT then
          match args with CONS e es -> (\f a. OPTION_BIND a f) (conv_shifts
              es) (conv_Exp e)
          | _ -> NONE
        else if EX (isNT nodeNT) binaryExps then
          match args with
            [] -> NONE
          | (CONS e es) -> (\f a. OPTION_BIND a f) (conv_binaryExps es)
              (conv_Exp e)
        else if EX (isNT nodeNT) panExps then
          match args with
            [] -> NONE
          | (CONS e es) -> (\f a. OPTION_BIND a f) (conv_panops es)
              (conv_Exp e)
        else NONE) /\
    (conv_Exp leaf = if panPtreeConversion_tokcheck leaf (kw BaseK) then SOME
    pan_BaseAddr
                       else if panPtreeConversion_tokcheck leaf (kw TopK)
                           then SOME pan_TopAddr
                       else if panPtreeConversion_tokcheck leaf (kw BiwK)
                           then SOME pan_BytesInWord
                       else if panPtreeConversion_tokcheck leaf (kw TrueK)
                           then SOME (pan_Const (n2w 1))
                       else if panPtreeConversion_tokcheck leaf (kw FalseK)
                           then SOME (pan_Const (n2w 0))
                       else APPEND (conv_const leaf) (conv_var leaf)) /\
    (conv_binaryExps [] e = SOME e) /\
    (conv_binaryExps _ _ = NONE) /\
    // Impossible: ruled out by grammar.
    (conv_panops [] e = SOME e) /\
    (conv_panops _ _ = NONE) /\
    // Impossible: ruled out by grammar.
    (conv_shifts [] e = SOME e) /\
    (conv_shifts _ _ = NONE)`;
   `conv_binaryExps (CONS t1 (CONS t2 ts)) res =
        OPTION_BIND (conv_binop t1) (\op. OPTION_BIND (conv_Exp t2) (\e.
           match res with
             pan_Op bop es -> if ~(bop = op) \/ isSubOp res then
                            conv_binaryExps ts (pan_Op op [res; e])
                          else conv_binaryExps ts (pan_Op bop (APPEND es
                              [e]))
           | e' -> conv_binaryExps ts (pan_Op op [e'; e])))`;
   `conv_panops (CONS t1 (CONS t2 ts)) res =
        OPTION_BIND (conv_panop t1) (\op. OPTION_BIND (conv_Exp t2) (\e.
           match res with
             pan_Panop bop es -> conv_panops ts (pan_Panop op [res; e])
           | e' -> conv_panops ts (pan_Panop op [e'; e])))`;
   `conv_shifts (CONS t1 (CONS t2 ts)) res =
        OPTION_BIND (conv_shift t1) (\op. OPTION_BIND (conv_Exp t2) (\e.
           conv_shifts ts (pan_Shift op res e)))`];;

(** Handles all statements which cannot contain
  * Prog nodes as children. *)
let conv_NonRecStmt_def = new_definition
  `conv_NonRecStmt leaf =
     match leaf with
       Nd nodeNT args ->
       if isNT nodeNT AssignNT then
         match args with
           [dst; src] -> OPTION_MAP2 (pan_Assign pan_Global) (conv_ident
             dst) (conv_Exp src)
         | _ -> NONE
       else if isNT nodeNT StoreNT then
         match args with
           [dst; src] -> OPTION_MAP2 pan_Store (conv_Exp dst) (conv_Exp src)
         | _ -> NONE
       else if isNT nodeNT StoreByteNT then
         match args with
           [dst; src] -> OPTION_MAP2 pan_StoreByte (conv_Exp dst) (conv_Exp
             src)
         | _ -> NONE
       else if isNT nodeNT Store32NT then
         match args with
           [dst; src] -> OPTION_MAP2 pan_Store32 (conv_Exp dst) (conv_Exp
             src)
         | _ -> NONE
       else if isNT nodeNT SharedLoadNT then
         match args with
           [v; e] -> OPTION_MAP2 (pan_ShMemLoad OpW pan_Global) (conv_ident
             v) (conv_Exp e)
         | _ -> NONE
       else if isNT nodeNT SharedLoadByteNT then
         match args with
           [v; e] -> OPTION_MAP2 (pan_ShMemLoad Op8 pan_Global) (conv_ident
             v) (conv_Exp e)
         | _ -> NONE
       else if isNT nodeNT SharedLoad16NT then
         match args with
           [v; e] -> OPTION_MAP2 (pan_ShMemLoad Op16 pan_Global) (conv_ident
             v) (conv_Exp e)
         | _ -> NONE
       else if isNT nodeNT SharedLoad32NT then
         match args with
           [v; e] -> OPTION_MAP2 (pan_ShMemLoad Op32 pan_Global) (conv_ident
             v) (conv_Exp e)
         | _ -> NONE
       else if isNT nodeNT SharedStoreNT then
         match args with
           [v; e] -> OPTION_MAP2 (pan_ShMemStore OpW) (conv_Exp v) (conv_Exp
             e)
         | _ -> NONE
       else if isNT nodeNT SharedStoreByteNT then
         match args with
           [v; e] -> OPTION_MAP2 (pan_ShMemStore Op8) (conv_Exp v) (conv_Exp
             e)
         | _ -> NONE
       else if isNT nodeNT SharedStore16NT then
         match args with
           [v; e] -> OPTION_MAP2 (pan_ShMemStore Op16) (conv_Exp v)
             (conv_Exp e)
         | _ -> NONE
       else if isNT nodeNT SharedStore32NT then
         match args with
           [v; e] -> OPTION_MAP2 (pan_ShMemStore Op32) (conv_Exp v)
             (conv_Exp e)
         | _ -> NONE
       else if isNT nodeNT ExtCallNT then
         match args with
           [name; ptr; clen; array; alen] ->
             OPTION_BIND (conv_ffi_ident name) (\name'. OPTION_BIND
               (conv_Exp ptr) (\ptr'. OPTION_BIND (conv_Exp clen) (\clen'.
               OPTION_BIND (conv_Exp array) (\array'. OPTION_BIND (conv_Exp
               alen) (\alen'.
                SOME (pan_ExtCall name' ptr' clen' array' alen'))))))
         | _ -> NONE
       else if isNT nodeNT ThrowNT then
         match args with
           [id; e] -> OPTION_BIND (conv_ident id) (\eid. OPTION_BIND
             (conv_Exp e) (\e'.
                         SOME (pan_Raise eid e')))
         | _ -> NONE
       else if isNT nodeNT ReturnNT then
         match args with
           [e] -> OPTION_MAP pan_Return (conv_Exp e)
         | _ -> NONE
       else NONE
     | leaf ->
       (if panPtreeConversion_tokcheck leaf (kw SkipK) then SOME pan_Skip
       else if panPtreeConversion_tokcheck leaf (kw BrK) then SOME pan_Break
       else if panPtreeConversion_tokcheck leaf (kw ContK) then SOME
         pan_Continue
       else if panPtreeConversion_tokcheck leaf (kw TicK) then SOME pan_Tick
       else (match dest_annot_tok leaf with SOME c -> SOME (pan_Annot
         (implode "@") (implode c))
         | NONE -> NONE))`;;

let butlast_def,butlast_ind = define_guess
  `(butlast [] = []) /\
   (butlast (CONS x xs) = (if xs = [] then [] else CONS x (butlast xs)))`;;

let butlast_length = prove
 (`!xs. LENGTH (butlast xs) = LENGTH xs - 1`,
  CHEAT_TAC);;

let butlast_tl = prove
 (`!xs. butlast (TL xs) = TL (butlast xs)`,
  CHEAT_TAC);;
add_simp butlast_tl;;

let butlast_append = prove
 (`!xs ys. butlast (APPEND xs ys) = (if ys = [] then butlast xs else APPEND
  xs (butlast ys))`,
  CHEAT_TAC);;
add_simp butlast_append;;

let list_size_butlast = prove
 (`!xs f. list_size f (butlast xs) <= list_size f xs`,
  CHEAT_TAC);;

let list_size_MEM = prove
 (`!xs x. MEM x xs ==> f x <= list_size f xs`,
  CHEAT_TAC);;

let parsetree_locs_def = new_definition
  `parsetree_locs tree = (match tree with Nd (_,Locs p1 p2) _ -> (p1,p2)
     | Lf (_,Locs p1 p2) -> (p1,p2))`;;

let posn_string_def = define_cases
  `(posn_string (POSN lnum cnum) = (strcat (strcat (mlint_toString lnum)
    (implode ":")) (mlint_toString cnum))) /\
   (posn_string EOFpt = (implode "EOF")) /\
   (posn_string UNKNOWNpt = (implode "UNKNOWN"))`;;

let locs_comment_def = new_definition
  `locs_comment (p1,p2) =
   mlstring_concat [(implode "(");
     posn_string p1;
     (implode " ");
     posn_string p2;
     (implode ")")]`;;

let add_locs_annot_def = new_definition
  `add_locs_annot ptree prog = pan_Seq (pan_Annot (implode "location")
  (locs_comment (parsetree_locs ptree))) prog`;;

(* HOL4 panPtreeConversionScript.sml:553: the ML values that the definitions
   below antiquote *)

let conv_Dec_def = new_definition
  `conv_Dec x1 =
     match x1 with
       (Nd:(pancakeNT+num)#locs->((panLexer_token,pancakeNT,locs)parsetree)
         list->(panLexer_token,pancakeNT,locs)parsetree) nodeNT args ->
      if isNT nodeNT DecNT then
        match args with
          [sh; id; e] ->
            OPTION_BIND (conv_Shape sh) (\sh. OPTION_BIND (conv_ident id)
              (\v. OPTION_BIND (conv_Exp e) (\e'.
               SOME (sh,v,e'))))
        | _ -> NONE
      else NONE
     | _ -> NONE`;;

let conv_GlobalDec_def = new_definition
  `conv_GlobalDec x1' =
     match x1' with
       (Nd:(pancakeNT+num)#locs->((panLexer_token,pancakeNT,locs)parsetree)
         list->(panLexer_token,pancakeNT,locs)parsetree) nodeNT args ->
      if isNT nodeNT GlobalDecNT then
        match args with
          [sh; id; e] ->
            OPTION_BIND (conv_Shape sh) (\sh. OPTION_BIND (conv_ident id)
              (\v. OPTION_BIND (conv_Exp e) (\e'.
               SOME (sh,v,e'))))
        | _ -> NONE
      else NONE
     | _ -> NONE`;;

let conv_ExnDec_def = new_definition
  `conv_ExnDec tree =
     match argsNT tree ExnDecNT with
       SOME [id; sh] ->
         OPTION_BIND (conv_ident id) (\eid. OPTION_BIND (conv_Shape sh)
           (\sh'.
            SOME (eid,sh')))
     | _ -> NONE`;;

let conv_DecCall_def = new_definition
  `conv_DecCall x1'' =
     match x1'' with
       (Nd:(pancakeNT+num)#locs->((panLexer_token,pancakeNT,locs)parsetree)
         list->(panLexer_token,pancakeNT,locs)parsetree) nodeNT args ->
      if isNT nodeNT DecCallNT then
        match args with CONS s (CONS i (CONS e ts)) ->
            OPTION_BIND (conv_Shape s) (\s'. OPTION_BIND (conv_ident i)
              (\i'. OPTION_BIND (conv_ident e) (\e'. OPTION_BIND (match ts with
              [] -> SOME [] | CONS args _ -> conv_ArgList args) (\args'.
               SOME (s',i',e',(args':('a pan_exp) list))))))
        | _ -> NONE
      else NONE
     | _ -> NONE`;;

let conv_Ret_def = new_definition
  `conv_Ret tree =
   if panPtreeConversion_tokcheck tree (kw RetK) then
     SOME NONE
   else if panPtreeConversion_tokcheck tree panLexer_NotT then
     SOME (SOME NONE)
   else match argsNT tree RetNT with SOME [id] -> OPTION_BIND (conv_ident
     id) (\var.
                       SOME (SOME (SOME (pan_Global,var))))
     | _ -> NONE`;;

(* the termination relation that HOL4 gives is
     MEASURE (parsetree_size (K 0) (K 0) (K 0))
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 panPtreeConversionScript.sml:706-722: the tactic that proves the
   termination *)
let conv_Prog_def,conv_Prog_ind = define_guess
  `conv_Prog leaf =
     match leaf with
       Nd nodeNT args ->
        let nd = Nd nodeNT args in
        if isNT nodeNT DecNT then
          match args with
            [d; p] -> OPTION_BIND (conv_Dec d) (\(sh,v,e'). OPTION_BIND
              (conv_Prog p) (\p'.
                         SOME (add_locs_annot nd (pan_Dec v sh e' p'))))
          | _ -> NONE
        else if isNT nodeNT IfNT then
          match args with [e; p1; p2] -> OPTION_BIND (conv_Exp e) (\e'.
            OPTION_BIND (conv_Prog p1) (\p1'. OPTION_BIND (conv_Prog p2) (\p2'.
                              SOME (add_locs_annot nd (pan_If e' p1'
                                p2')))))
          | _ -> NONE
        else if isNT nodeNT WhileNT then
          match args with
            [e; p] -> OPTION_BIND (conv_Exp e) (\e'. OPTION_BIND (conv_Prog
              p) (\p'.
                         SOME (add_locs_annot nd (pan_While e' p'))))
          | _ -> NONE
        else if isNT nodeNT DecCallNT then
          match args with
            [dec; p] ->
              OPTION_BIND (conv_DecCall dec) (\(s',i',e',args'). OPTION_BIND
                (conv_Prog p) (\p'.
                  if is_add_with_carry e' then SOME (add_locs_annot nd
                            (pan_Dec i' s' (shape_val s')
                              (pan_Seq (pan_Primitive i' pan_AddCarry args')
                                p')))
                  else SOME (add_locs_annot nd
                            (pan_DecCall i' s' e' args' p'))))
          | _ -> NONE
        else if isNT nodeNT HandleNT then
          match args with [ret; f; ts; eid; id; p] ->
              OPTION_BIND (conv_Ret ret) (\r'. OPTION_BIND r' (\r''.
                OPTION_BIND (conv_ident f) (\fname. OPTION_BIND (conv_ArgList
                ts) (\args. OPTION_BIND (conv_ident eid) (\ename. OPTION_BIND
                (conv_ident id) (\evar. OPTION_BIND (conv_Prog p) (\prog.
                 SOME (add_locs_annot nd (pan_Call (SOME (r'',SOME
                   (ename,evar,prog))) fname args)))))))))
          | _ -> NONE
        else if isNT nodeNT CallNT then
          match args with [r; e; args] ->
              OPTION_BIND (conv_Ret r) (\r'. OPTION_BIND (conv_ident e)
                (\e'. OPTION_BIND (conv_ArgList args) (\args'.
                 if is_add_with_carry e' then
                   (match r' with SOME (SOME (_,vn)) ->
                        SOME (add_locs_annot nd
                             (pan_Primitive vn pan_AddCarry args'))
                    | _ -> NONE)
                 else SOME (add_locs_annot nd
                        (pan_Call (OPTION_MAP (\x. (x,NONE)) r') e'
                          args')))))
          | _ -> NONE
        else if isNT nodeNT ProgNT then
          match args with CONS t ts -> if ~(ts = []) then ITLIST (\t' p.
            OPTION_MAP2 pan_Seq t' p)
                              (MAP conv_Prog (CONS t (butlast ts)))
                                (conv_Prog (LAST ts))
                     else conv_Prog t
          | _ -> NONE
        else OPTION_MAP (add_locs_annot nd) (conv_NonRecStmt (Nd nodeNT
          args))
     | leaf -> OPTION_MAP (add_locs_annot leaf) (conv_NonRecStmt leaf)`;;

let conv_inline_def = new_definition
  `conv_inline tree =
     match (\f a. OPTION_BIND a f) panPtreeConversion_destTOK
       (panPtreeConversion_destLf tree) with
       SOME (panLexer_KeywordT InlineK) -> SOME T
     | SOME (panLexer_NoinlineT) -> SOME F
     | _ -> NONE`;;

let conv_export_def = new_definition
  `conv_export tree =
     match (\f a. OPTION_BIND a f) panPtreeConversion_destTOK
       (panPtreeConversion_destLf tree) with
       SOME (panLexer_KeywordT ExportK) -> SOME T
     | SOME (panLexer_StaticT) -> SOME F
     | _ -> NONE`;;

let conv_FieldNameList_def = new_definition
  `(conv_FieldNameList tree =
     match argsNT tree FieldNameListNT with
       SOME args -> conv_params args
     | _ -> NONE)`;;

let conv_StructName_def = new_definition
  `conv_StructName x1''' =
     match x1''' with
       (Nd:(pancakeNT+num)#locs->((panLexer_token,pancakeNT,locs)parsetree)
         list->(panLexer_token,pancakeNT,locs)parsetree) nodeNT args ->
       if isNT nodeNT StructNameNT then
         match args with
           [id; flds] ->
             OPTION_BIND (conv_ident id) (\nm. OPTION_BIND
               (conv_FieldNameList flds) (\flds'.
                SOME (nm,flds')))
         | _ -> NONE
       else NONE
     | _ -> NONE`;;

let conv_TopDec_def = new_definition
  `conv_TopDec tree =
   match argsNT tree FunNT with SOME [i; e; sh; n; ps; c] ->
       (match (argsNT ps ParamListNT) with
          SOME args ->
            (OPTION_BIND (conv_params args) (\ps'. OPTION_BIND (conv_Prog c)
              (\body. OPTION_BIND (conv_ident n) (\n'. OPTION_BIND (conv_inline
              i) (\i'. OPTION_BIND (conv_export e) (\e'. OPTION_BIND
              (conv_Shape sh) (\sh'.
                SOME (Function (mk_fun_decl n' i' e' ps' body sh')))))))))
        | _ -> NONE)
   | _ ->
       (match conv_GlobalDec tree with SOME (sh,v,e) -> SOME (Decl sh v e)
        | _ -> (match conv_StructName tree with SOME (nm,flds) -> SOME (Name
          nm flds)
                | _ ->
                    (match conv_ExnDec tree with
                       SOME (eid,sh) -> SOME (ExnDecl eid sh)
                     | NONE -> NONE)))`;;

(* the termination relation that HOL4 gives is
     MEASURE (parsetree_size (K 0) (K 0) (K 0))
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 panPtreeConversionScript.sml:803-807: the tactic that proves the
   termination *)
let conv_TopDecList_def,conv_TopDecList_ind = define_guess
  `conv_TopDecList tree =
    match argsNT tree TopDecListNT with
      SOME [] -> SOME []
    | SOME [f; tree'] ->
        (match dest_annot_tok f with
          NONE ->
            (match conv_TopDec f with SOME f ->
                 (match conv_TopDecList tree' with
                   NONE -> NONE
                  | SOME fs -> SOME (CONS f fs))
             | NONE -> NONE)
        | SOME _ -> conv_TopDecList tree')
    | _ -> NONE`;;

let parse_to_ast_def = new_definition
  `parse_to_ast s =
     match parse_statement (pancake_lex s) with
       SOME e -> conv_Prog e
     | _ -> NONE`;;

let collect_globals_def,collect_globals_ind = define_guess
  `(collect_globals [] = peg_empty mlstring_compare) /\
   (collect_globals (CONS d ds) =
    match d with
      Decl _ v _ -> mlmap_insert (collect_globals ds) v one
    | _ -> collect_globals ds)`;;

let localise_exp_def,localise_exp_ind = define_guess
  `(localise_exp ls (pan_Var varkind varname) =
       match mlmap_lookup ls varname with
         NONE -> pan_Var varkind varname
       | SOME _ -> pan_Var pan_Local varname) /\
   (localise_exp ls (pan_RStruct exps) = pan_RStruct (localise_exps ls
    exps)) /\
   (localise_exp ls (pan_RField index exp) = pan_RField index (localise_exp
    ls exp)) /\
   (localise_exp ls (pan_NStruct nm flds) = pan_NStruct nm (MAP (\(fld,e).
    (fld,localise_exp ls e)) flds)) /\
   (localise_exp ls (pan_NField fld exp) = pan_NField fld (localise_exp ls
    exp)) /\
   (localise_exp ls (pan_Load shape exp) = pan_Load shape (localise_exp ls
    exp)) /\
   (localise_exp ls (pan_LoadByte exp) = pan_LoadByte (localise_exp ls exp)) /\
   (localise_exp ls (pan_Op binop exps) = pan_Op binop (localise_exps ls
    exps)) /\
   (localise_exp ls (pan_Panop panop exps) = pan_Panop panop (localise_exps
    ls exps)) /\
   (localise_exp ls (pan_Cmp cmp exp1 exp2) = pan_Cmp cmp (localise_exp ls
    exp1) (localise_exp ls exp2)) /\
   (localise_exp ls (pan_Shift shift exp1 exp2) = pan_Shift shift
    (localise_exp ls exp1) (localise_exp ls exp2)) /\
   (localise_exp ls e = e) /\
   (localise_exps ls [] = []) /\
   (localise_exps ls (CONS e es) = CONS (localise_exp ls e) (localise_exps
    ls es))`;;

let localise_prog_def,localise_prog_ind = define_guess
  `localise_prog ls p =
   match p with
     pan_Dec varname shape exp prog ->
   pan_Dec varname shape
       (localise_exp ls exp)
       (localise_prog (mlmap_insert ls varname one) prog)
   | pan_Assign varkind varname exp ->
   pan_Assign (match mlmap_lookup ls varname with NONE -> varkind | SOME _
     -> pan_Local)
          varname (localise_exp ls exp)
   | pan_Primitive varname pop exps ->
   pan_Primitive varname pop (MAP (localise_exp ls) exps)
   | pan_Store exp1 exp2 ->
   pan_Store (localise_exp ls exp1)
         (localise_exp ls exp2)
   | pan_StoreByte exp1 exp2 ->
   pan_StoreByte (localise_exp ls exp1)
             (localise_exp ls exp2)
   | pan_Seq prog1 prog2 ->
   pan_Seq (localise_prog ls prog1)
       (localise_prog ls prog2)
   | pan_If exp prog1 prog2 ->
   pan_If (localise_exp ls exp)
      (localise_prog ls prog1)
      (localise_prog ls prog2)
   | pan_While exp prog ->
   pan_While (localise_exp ls exp)
         (localise_prog ls prog)
   | pan_Call call name exps ->
   pan_Call (OPTION_MAP
           (\(x,y).
              (OPTION_MAP (\(varkind,varname). ((match mlmap_lookup ls
                varname with NONE -> varkind | SOME _ -> pan_Local),varname))
                x,
               OPTION_MAP (\(x,y,z). (x,y,localise_prog (mlmap_insert ls y
                 one) z)) y))
           call)
        name
        (MAP (localise_exp ls) exps)
   | pan_DecCall varname shape fname exps prog ->
   pan_DecCall varname shape
           fname
           (MAP (localise_exp ls) exps)
           (localise_prog (mlmap_insert ls varname one) prog)
   | pan_ExtCall funname exp1 exp2 exp3 exp4 ->
   pan_ExtCall funname
           (localise_exp ls exp1) (localise_exp ls exp2)
           (localise_exp ls exp3) (localise_exp ls exp4)
   | pan_Raise eid exp ->
   pan_Raise eid (localise_exp ls exp)
   | pan_Return exp ->
   pan_Return (localise_exp ls exp)
   | pan_ShMemLoad opsize varkind varname exp ->
   pan_ShMemLoad opsize
             (match mlmap_lookup ls varname with NONE -> varkind | SOME _ ->
               pan_Local)
             varname
             (localise_exp ls exp)
   | pan_ShMemStore opsize exp1 exp2 ->
   pan_ShMemStore opsize (localise_exp ls exp1) (localise_exp ls exp2)
   | p -> p`;;

(* the clauses in two quotations: nm is stcname and eid, which one quotation
   cannot typecheck *)
let localise_topdec_def = define_cases_clauses
  [`(localise_topdec ls (Decl sh v e) = Decl sh v e) /\
    (localise_topdec ls (Name nm fld) = Name nm fld) /\
    (localise_topdec ls (Function fi) =
    Function (fun_decl_body_fupd (K (localise_prog (FOLDL (\m p.
        mlmap_insert m p one) ls (MAP FST (fun_decl_params fi)))
        (fun_decl_body fi))) fi))`;
   `localise_topdec ls (ExnDecl nm sh) = ExnDecl nm sh`];;

let localise_topdecs_def = new_definition
  `localise_topdecs decs = MAP (localise_topdec (peg_empty
  mlstring_compare)) decs`;;

let parse_topdecs_to_ast_def = assume_definition
  "declared (no value)"
  `parse_topdecs_to_ast s =
     (match safe_pancake_lex s with INL toks ->
         (match panPEG_parse toks with INL e ->
              (match conv_TopDecList e with SOME funs -> INL
                (localise_topdecs funs)
               | NONE -> INR [((implode
                 "Parse tree conversion failed"),unknown_loc)])
            | INR err -> INR err)
      | INR err -> INR err)`;;

(* and the interface *)
let _ = unhide_overloads ();;
