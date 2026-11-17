(* ======================================================== *)
(*  caml_lex: ported from HOL4's
    compiler/parsing/ocaml/caml_lexScript.sml
    A definition theory, with 40 definitions, 2 datatypes and 35
    theorems.  Needed by camlPEG.ml, camlPtreeConversion.ml,
    caml_lexProg.ml and caml_parser.ml.  *)
(* ======================================================== *)

(*
  Lexer for the OCaml frontend.
 *)

needs "basis/pure/mlstring.ml";;
needs "candle/standard/syntax/holSyntax.ml";;
needs "compiler/encoders/asm/asmSem.ml";;
needs "compiler/parsing/lexer_impl.ml";;
needs "lib/ASCIInumbers.ml";;
needs "lib/errorMonad.ml";;
needs "lib/location.ml";;
needs "lib/pegexec.ml";;
needs "misc/misc.ml";;
needs "semantics/lexer_fun.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "caml_lex"
  ["lexer_fun"; "lexer_impl"; "misc"];;

let _ = do_list hide_constant ["pmatch"];;

(* -------------------------------------------------------------------------
 * Tokens
 * ------------------------------------------------------------------------- *)

let caml_lex_token_INDUCT,caml_lex_token_RECURSION = define_datatype
  "caml_lex_token =
     // keywords:
     caml_lex_AndT
   | caml_lex_AsT
   | caml_lex_AssertT
   | caml_lex_AsrT
   | caml_lex_BeginT
   | caml_lex_ClassT
   | caml_lex_ConstraintT
   | caml_lex_DoT
   | caml_lex_DoneT
   | caml_lex_DowntoT
   | caml_lex_ElseT
   | caml_lex_EndT
   | caml_lex_ExceptionT
   | caml_lex_ExternalT
   | caml_lex_FalseT
   | caml_lex_ForT
   | caml_lex_FunT
   | caml_lex_FunctionT
   | caml_lex_FunctorT
   | caml_lex_IfT
   | caml_lex_InT
   | caml_lex_IncludeT
   | caml_lex_InheritT
   | caml_lex_InitializerT
   | caml_lex_LandT
   | caml_lex_LazyT
   | caml_lex_LetT
   | caml_lex_LorT
   | caml_lex_LslT
   | caml_lex_LsrT
   | caml_lex_LxorT
   | caml_lex_MatchT
   | caml_lex_MethodT
   | caml_lex_ModT
   | caml_lex_ModuleT
   | caml_lex_MutableT
   | caml_lex_NewT
   | caml_lex_NonrecT
   | caml_lex_ObjectT
   | caml_lex_OfT
   | caml_lex_OpenT
   | caml_lex_OrT
   | caml_lex_PrivateT
   | caml_lex_RecT
   | caml_lex_SigT
   | caml_lex_StructT
   | caml_lex_ThenT
   | caml_lex_ToT
   | caml_lex_TrueT
   | caml_lex_TryT
   | caml_lex_TypeT
   | caml_lex_ValT
   | caml_lex_VirtualT
   | caml_lex_WhenT
   | caml_lex_WhileT
   | caml_lex_WithT
     // symbol keywords:
   | caml_lex_EqualT
   | caml_lex_TickT
   | caml_lex_LparT
   | caml_lex_RparT
   | caml_lex_HashT
   | caml_lex_StarT
   | caml_lex_PlusT
   | caml_lex_CommaT
   | caml_lex_MinusT
   | caml_lex_LessT
   | caml_lex_GreaterT
   | caml_lex_LbrackT
   | caml_lex_RbrackT
   | caml_lex_LbraceT
   | caml_lex_RbraceT
   | caml_lex_QuestionT
   | caml_lex_SemiT
   | caml_lex_SemisT
   | caml_lex_BarT
   | caml_lex_OrelseT
   | caml_lex_AmpT
   | caml_lex_AndalsoT
   | caml_lex_NeqT
   | caml_lex_MinusFT
   | caml_lex_RarrowT
   | caml_lex_LarrowT
   | caml_lex_DotT
   | caml_lex_DotsT
   | caml_lex_EscapeT
   | caml_lex_ColonT
   | caml_lex_ColonsT
   | caml_lex_UpdateT
   | caml_lex_SealT
   | caml_lex_AnyT
   | caml_lex_BtickT
   | caml_lex_TildeT
   | caml_lex_LqbraceT
   | caml_lex_RqbraceT
   | caml_lex_LqbrackT
   | caml_lex_RqbrackT
   | caml_lex_RrbrackT
   | caml_lex_LlbrackT
   | caml_lex_RlbrackT
     // special HOL Light tokens (all infixes):
   | caml_lex_FuncompT
   | caml_lex_F_FT
   | caml_lex_THEN_T
   | caml_lex_THENC_T
   | caml_lex_THENL_T
   | caml_lex_THEN_TCL_T
   | caml_lex_ORELSE_T
   | caml_lex_ORELSEC_T
   | caml_lex_ORELSE_TCL_T
     // CakeML pragma
   | caml_lex_PragmaT mlstring
     // literals and identifiers:
   | caml_lex_IntT int
   | caml_lex_FloatT mlstring
   | caml_lex_CharT char
   | caml_lex_StringT mlstring
   | caml_lex_IdentT mlstring
   | caml_lex_SymbolT mlstring
     // symbols
   | caml_lex_LexErrorT";;

let caml_lex_isInt_def = new_definition
  `caml_lex_isInt x1 =
   match x1 with
     caml_lex_IntT i -> T
   | _ -> F`;;

let destInt_def = new_definition
  `destInt x1' =
   match x1' with
     caml_lex_IntT i -> SOME i
   | _ -> NONE`;;
add_simp destInt_def;;

let isInt_thm = prove
 (`caml_lex_isInt x <=> (?y. x = caml_lex_IntT y)`,
  CHEAT_TAC);;

let isFloat_def = new_definition
  `isFloat x1'' =
   match x1'' with
     caml_lex_FloatT s -> T
   | _ -> F`;;

let destFloat_def = new_definition
  `destFloat x1''' =
   match x1''' with
     caml_lex_FloatT s -> SOME s
   | _ -> NONE`;;
add_simp destFloat_def;;

let isFloat_thm = prove
 (`isFloat x <=> (?y. x = caml_lex_FloatT y)`,
  CHEAT_TAC);;

let isChar_def = new_definition
  `isChar x1'''' =
   match x1'''' with
     caml_lex_CharT c -> T
   | _ -> F`;;

let destChar_def = new_definition
  `destChar x1''''' =
   match x1''''' with
     caml_lex_CharT c -> SOME c
   | _ -> NONE`;;
add_simp destChar_def;;

let isChar_thm = prove
 (`isChar x <=> (?y. x = caml_lex_CharT y)`,
  CHEAT_TAC);;

let caml_lex_isString_def = new_definition
  `caml_lex_isString x1'''''' =
   match x1'''''' with
     caml_lex_StringT s -> T
   | _ -> F`;;

let destString_def = new_definition
  `destString x1''''''' =
   match x1''''''' with
     caml_lex_StringT s -> SOME s
   | _ -> NONE`;;
add_simp destString_def;;

let isString_thm = prove
 (`caml_lex_isString x <=> (?y. x = caml_lex_StringT y)`,
  CHEAT_TAC);;

let caml_lex_isSymbol_def = new_definition
  `caml_lex_isSymbol x1'''''''' =
   match x1'''''''' with
     caml_lex_SymbolT s -> T
   | _ -> F`;;

let destSymbol_def = new_definition
  `destSymbol x1''''''''' =
   match x1''''''''' with
     caml_lex_SymbolT s -> SOME s
   | _ -> NONE`;;
add_simp destSymbol_def;;

let isSymbol_thm = prove
 (`caml_lex_isSymbol x <=> (?y. x = caml_lex_SymbolT y)`,
  CHEAT_TAC);;

let isIdent_def = new_definition
  `isIdent x1'''''''''' =
   match x1'''''''''' with
     caml_lex_IdentT s -> T
   | _ -> F`;;

let destIdent_def = new_definition
  `destIdent x1''''''''''' =
   match x1''''''''''' with
     caml_lex_IdentT s -> SOME s
   | _ -> NONE`;;
add_simp destIdent_def;;

let isIdent_thm = prove
 (`isIdent x <=> (?y. x = caml_lex_IdentT y)`,
  CHEAT_TAC);;

let isPragma_def = new_definition
  `isPragma x1'''''''''''' =
   match x1'''''''''''' with
     caml_lex_PragmaT s -> T
   | _ -> F`;;

let destPragma_def = new_definition
  `destPragma x1''''''''''''' =
   match x1''''''''''''' with
     caml_lex_PragmaT s -> SOME s
   | _ -> NONE`;;
add_simp destPragma_def;;

let isPragma_thm = prove
 (`isPragma x <=> (?y. x = caml_lex_PragmaT y)`,
  CHEAT_TAC);;

(* -------------------------------------------------------------------------
 * Pre-tokens
 * ------------------------------------------------------------------------- *)

let caml_lex_symbol_INDUCT,caml_lex_symbol_RECURSION = define_datatype
  "caml_lex_symbol =
     caml_lex_NumberS int
   | caml_lex_FloatS string
   | caml_lex_StringS string
   | caml_lex_CharS char
   | caml_lex_OtherS string
   | caml_lex_PragmaS string
   | caml_lex_ErrorS";;

(* INTEGERS
 *
 *   int-lit ::= [-]? [0-9] [0-9_]*
 *             | [-]? ("0x"|"0X") [0-9a-fA-F] [0-9a-fA-F_]*
 *             | [-]? ("0o"|"0O") [0-7] [0-7_]*
 *             | [-]? ("0b"|"0B") [0-1] [0-1_]*
 *
 *   int32-lit ::= int-lit "l"
 *   int64-lit ::= int-lit "L"
 *   intn-lit  ::= int-lit "n"
 *)

let isOctDigit_def = new_definition
  `isOctDigit c <=> 48 <= ORD c /\ ORD c <= 55`;;

let isBinDigit_def = new_definition
  `isBinDigit c <=> 48 <= ORD c /\ ORD c <= 49`;;

let oct2num_def = new_definition
  `oct2num = s2n 8 lexer_impl_unhex_alt`;;

let hex2num_def = new_definition
  `hex2num = s2n 16 lexer_impl_unhex_alt`;;

let bin2num_def = new_definition
  `bin2num = s2n 2 lexer_impl_unhex_alt`;;

let dec2num_def = new_definition
  `dec2num = s2n 10 lexer_impl_unhex_alt`;;

let take_while_aux_def,take_while_aux_ind = define_guess
  `take_while_aux acc p xs =
     match xs with
       [] -> (REVERSE acc,xs)
     | CONS x xs ->
         if p x then take_while_aux (CONS x acc) p xs
         else (REVERSE acc,CONS x xs)`;;

(* [local] *)
let take_while_aux_thm = prove
 (`!acc p xs ys zs.
     take_while_aux acc p xs = (ys,zs) ==>
       LENGTH xs + LENGTH acc = LENGTH ys + LENGTH zs`,
  CHEAT_TAC);;

let take_while_def = new_definition
  `take_while = take_while_aux []`;;

let take_while_thm = prove
 (`take_while p xs = (ys,zs) ==> LENGTH xs = LENGTH ys + LENGTH zs`,
  CHEAT_TAC);;

let caml_lex_skip_comment_def,caml_lex_skip_comment_ind = define_guess
  `caml_lex_skip_comment cs d loc =
     match cs with CONS x (CONS y xs) ->
         if x = (CHR 40) /\ y = (CHR 42) then
           caml_lex_skip_comment xs (d + 1) (lexer_fun_next_loc 2 loc)
         else if x = (CHR 42) /\ y = (CHR 41) then
           let loc' = lexer_fun_next_loc 2 loc in
             if d = 0 then SOME (xs,loc') else caml_lex_skip_comment xs (d -
               1) loc'
         else if x = (CHR 10) then
           caml_lex_skip_comment (CONS y xs) d (lexer_fun_next_line loc)
         else caml_lex_skip_comment (CONS y xs) d (lexer_fun_next_loc 1 loc)
     | _ -> NONE`;;

(* skip_comment_thm *)
let caml_lex_skip_comment_thm = prove
 (`!xs d loc.
     caml_lex_skip_comment xs d loc = SOME (ys,loc') ==>
       LENGTH ys <= LENGTH xs`,
  CHEAT_TAC);;

(* ESCAPE SEQUENCE
 *
 *  esc-seq  ::= "\" [\\"'ntr\s]
 *             | "\" [0-9][0-9][0-9]
 *             | "\x" [0-9][0-9]
 *             | "\o" [0-3][0-7][0-7]
 *  char-lit ::= "'" (<char> | esc-seq) "'"
 *)

let scan_escseq_def = new_definition
  `scan_escseq s loc =
     match s with CONS (CHR 92) cs ->
         (match cs with CONS (CHR 92) rest ->
              SOME ((CHR 92),rest,lexer_fun_next_loc 2 loc)
          | CONS (CHR 34) rest ->
              SOME ((CHR 34),rest,lexer_fun_next_loc 2 loc)
          | CONS (CHR 39) rest ->
              SOME ((CHR 39),rest,lexer_fun_next_loc 2 loc)
          | CONS (CHR 110) rest ->
              SOME ((CHR 10),rest,lexer_fun_next_loc 2 loc)
          | CONS (CHR 114) rest ->
              SOME ((CHR 13),rest,lexer_fun_next_loc 2 loc)
          | CONS (CHR 116) rest ->
              SOME ((CHR 9),rest,lexer_fun_next_loc 2 loc)
          | CONS (CHR 98) rest ->
              SOME ((CHR 8),rest,lexer_fun_next_loc 2 loc)
          | CONS (CHR 32) rest ->
              SOME ((CHR 32),rest,lexer_fun_next_loc 2 loc)
          | CONS (CHR 120) (CONS d1 (CONS d2 rest)) ->
              if isHexDigit d1 /\ isHexDigit d2 then
                let n = hex2num [d1; d2] in
                  SOME (CHR n,rest,lexer_fun_next_loc 4 loc)
              else NONE
          | CONS (CHR 111) (CONS d1 (CONS d2 (CONS d3 rest))) ->
             if 48 <= ORD d1 /\ ORD d1 <= 51 /\ isOctDigit d2 /\ isOctDigit
               d3 then
               let n = oct2num [d1; d2; d3] in
                SOME (CHR n,rest,lexer_fun_next_loc 5 loc)
              else NONE
          | CONS d1 (CONS d2 (CONS d3 rest)) ->
              if ALL isDigit [d1; d2; d3] then
                let n = dec2num [d1; d2; d3] in
                  if n <= 255 then
                    SOME (CHR n,rest,lexer_fun_next_loc 4 loc)
                  else NONE
              else NONE
          | _ -> NONE)
     | _ -> NONE`;;

let scan_escseq_thm = prove
 (`!xs loc c ys loc'.
     scan_escseq xs loc = SOME (c,ys,loc') ==> LENGTH ys < LENGTH xs`,
  CHEAT_TAC);;

(* the termination relation that HOL4 gives is
     MEASURE (LENGTH o FST o SND)
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 caml_lexScript.sml:351-354: the tactic that proves the termination *)
let scan_strlit_def,scan_strlit_ind = define_guess
  `scan_strlit acc cs loc =
     match cs with
       [] -> SOME (caml_lex_ErrorS,Locs loc loc,cs)
     | CONS (CHR 34) cs ->
         SOME (caml_lex_StringS (REVERSE acc),Locs loc loc,cs)
     | CONS (CHR 10) cs ->
         scan_strlit (CONS (CHR 10) acc) cs (lexer_fun_next_line loc)
     | CONS (CHR 92) _ ->
         (match scan_escseq cs loc with
            NONE -> SOME (caml_lex_ErrorS,Locs loc loc,cs)
          | SOME (c,cs',loc') -> scan_strlit (CONS c acc) cs' loc')
     | CONS c cs -> scan_strlit (CONS c acc) cs (lexer_fun_next_loc 1
       loc)`;;

let scan_strlit_thm = prove
 (`!acc cs loc sym locs ds.
     scan_strlit acc cs loc = SOME (sym,locs,ds) ==>
       LENGTH ds <= LENGTH cs + LENGTH acc`,
  CHEAT_TAC);;

let scan_charlit_def = new_definition
  `scan_charlit cs loc =
     if cs = "" then
       SOME (caml_lex_ErrorS,Locs loc loc,cs)
     else if HD cs = (CHR 92) then
       match scan_escseq cs loc with
         SOME (c,cs',loc') ->
           if ~(cs' = "") /\ HD cs' = (CHR 39) then
             SOME (caml_lex_CharS c,Locs loc loc',TL cs')
           else SOME (caml_lex_ErrorS,Locs loc loc',cs')
       | NONE ->
           SOME (caml_lex_ErrorS,Locs loc loc,cs)
     else match cs with CONS c (CONS (CHR 39) rest) ->
           SOME (caml_lex_CharS c,Locs loc (lexer_fun_next_loc 1 loc),rest)
       | _ ->
           SOME (caml_lex_ErrorS,Locs loc loc,cs)`;;

let scan_charlit_thm = prove
 (`scan_charlit cs loc = SOME (sym,locs,ds) ==> LENGTH ds <= LENGTH cs`,
  CHEAT_TAC);;

let scan_number_def = new_definition
  `scan_number ok_digit to_int' offset cs loc =
     if cs = "" then
       SOME (caml_lex_ErrorS,Locs loc loc,cs)
     else if ~(ok_digit (HD cs)) then
       SOME (caml_lex_ErrorS,Locs loc loc,cs)
     else let (cs',rest) = take_while (\c. c = (CHR 95) \/ ok_digit c) cs in
       let n = FILTER ((\x y. ~(x = y)) (CHR 95)) cs' in
       let (t,rest) = (if ~(rest = "") /\ MEM (HD rest) "lLn" then (1,TL
         rest)
                       else (0,rest)) in
         SOME (caml_lex_NumberS (to_int' n),
               Locs loc (lexer_fun_next_loc ((LENGTH cs' + offset + t) - 1)
                 loc),
               rest)`;;

(* FLOATS
 *
 *   float-lit ::= [0-9] [0-9_]* ("." [0-9_]* )? ([eE] [+-]? [0-9_]* )?
 *
 *)

(* [0-9] [0-9_]* *)
let scan_float1_def = new_definition
  `scan_float1 cs =
     if cs = "" \/ ~(isDigit (HD cs)) then NONE else let (cs',rest) =
       take_while (\c. c = (CHR 95) \/ isDigit c) cs in
       let n = FILTER ((\x y. ~(x = y)) (CHR 95)) cs' in
         SOME (n,LENGTH cs',rest)`;;

(* "." [0-9_]* *)
let scan_float2_def = new_definition
  `scan_float2 cs =
     if cs = "" \/ ~(HD cs = (CHR 46)) then NONE else let (cs',rest) =
       take_while (\c. c = (CHR 95) \/ isDigit c) (TL cs) in
       let n = FILTER ((\x y. ~(x = y)) (CHR 95)) cs' in
         SOME (CONS (CHR 46) n,LENGTH cs' + 1,rest)`;;

(* [eE] [+-]? *)
let scan_float3_def = new_definition
  `scan_float3 cs =
     match cs with CONS x (CONS y rest) ->
         if ~(MEM x "eE") then NONE
         else if MEM y "+-" then
           if rest = "" \/ ~(isDigit (HD rest)) then NONE else let
             (cs',rest') = take_while (\c. c = (CHR 95) \/ isDigit c) rest in
             let n = FILTER ((\x y. ~(x = y)) (CHR 95)) cs' in
               SOME (CONS x (CONS y n),2 + LENGTH cs',rest')
         else if ~(isDigit y) then NONE
         else let (cs',rest') = take_while (\c. c = (CHR 95) \/ isDigit c)
           rest in
           let n = FILTER ((\x y. ~(x = y)) (CHR 95)) cs' in
             SOME (CONS x (CONS y n),2 + LENGTH cs',rest')
     | _ -> NONE`;;

(* At least one of scan_float2 or scan_float3 must succeed. If they fail,
 * try to scan an integer instead.
 *)
let scan_float_or_int_def = new_definition
  `scan_float_or_int cs loc =
     match scan_float1 cs with
       NONE -> SOME (caml_lex_ErrorS,Locs loc loc,cs)
     | SOME (s1,n1,cs1) ->
         (match scan_float2 cs1 with
           NONE ->
             (
              // try scan_float3
              match scan_float3 cs1 with
               NONE -> scan_number isDigit (\s. &(dec2num s)) 0 cs loc
             | SOME (s2,n2,cs2) -> SOME (caml_lex_FloatS (APPEND s1 s2),
                              Locs loc (lexer_fun_next_loc (n1 + n2) loc),
                              cs2))
         | SOME (s2,n2,cs2) ->
             (match scan_float3 cs2 with
               NONE -> SOME (caml_lex_FloatS (APPEND s1 s2),
                             Locs loc (lexer_fun_next_loc (n1 + n2) loc),
                             cs2)
             | SOME (s3,n3,cs3) ->
                 SOME (caml_lex_FloatS (APPEND (APPEND s1 s2) s3),
                       Locs loc (lexer_fun_next_loc (n1 + n2 + n3) loc),
                       cs3)))`;;

let scan_pragma_def,scan_pragma_ind = define_guess
  `scan_pragma (level:num) (n:num) cs loc =
   match cs with CONS x (CONS y xs) ->
       if x = (CHR 40) /\ y = (CHR 42) then
         scan_pragma (level + 1) (n + 2) xs (lexer_fun_next_loc 2 loc)
       else if x = (CHR 42) /\ y = (CHR 41) then
         let loc' = lexer_fun_next_loc 2 loc in
           if level = 0 then
             SOME (n,lexer_fun_next_loc 2 loc,xs)
           else scan_pragma (level - 1) (n + 2) xs loc'
       else if x = (CHR 10) then
         scan_pragma level (n + 1) (CONS y xs) (lexer_fun_next_line loc)
       else scan_pragma level (n + 1) (CONS y xs) (lexer_fun_next_loc 1 loc)
   | _ -> NONE`;;

let scan_pragma_thm = prove
 (`!l n cs loc m loc' rest.
     scan_pragma l n cs loc = SOME (m,loc',rest) ==>
       LENGTH rest <= LENGTH cs /\
       n <= m`,
  CHEAT_TAC);;

let scan_number_thm = prove
 (`scan_number f g off cs loc = SOME (sym,locs,ds) ==>
     LENGTH ds <= LENGTH cs`,
  CHEAT_TAC);;

let scan_float_or_int_thm = prove
 (`scan_float_or_int cs loc = SOME (sym,locs,ds) ==> LENGTH ds <= LENGTH cs`,
  CHEAT_TAC);;

let isSym_def = new_definition
  `isSym c <=> MEM c "#$&*+-/=>@^|~!?%<:.;"`;;

let isDelim_def = new_definition
  `isDelim c <=> MEM c "()[]{},"`;;

(* the termination relation that HOL4 gives is
     MEASURE (LENGTH o FST)
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 caml_lexScript.sml:597-602: the tactic that proves the termination *)
let caml_lex_next_sym_def,caml_lex_next_sym_ind = define_guess
  `(caml_lex_next_sym [] loc = NONE) /\
   (caml_lex_next_sym (CONS c cs) loc =
      if c = (CHR 10) then
        caml_lex_next_sym cs (lexer_fun_next_line loc)
      else if isSpace c then
        caml_lex_next_sym cs (lexer_fun_next_loc 1 loc)
      else if isDigit c then
        if c = (CHR 48) /\ ~(cs = "") then
          if HD cs = (CHR 120) \/ HD cs = (CHR 88) then
            scan_number isHexDigit (\s. &(hex2num s)) 2 (TL cs) loc
          else if HD cs = (CHR 111) \/ HD cs = (CHR 79) then
            scan_number isOctDigit (\s. &(oct2num s)) 2 (TL cs) loc
          else if HD cs = (CHR 98) \/ HD cs = (CHR 66) then
            scan_number isBinDigit (\s. &(bin2num s)) 2 (TL cs) loc
          else scan_float_or_int (CONS c cs) loc
        else scan_float_or_int (CONS c cs) loc
      else if c = (CHR 34) then
        scan_strlit [] cs (lexer_fun_next_loc 1 loc)
      else if c = (CHR 39) then
        match scan_charlit cs (lexer_fun_next_loc 1 loc) with NONE -> SOME
            (caml_lex_OtherS [c],Locs loc loc,cs)
        | SOME res ->
            if FST res = caml_lex_ErrorS then SOME (caml_lex_OtherS
                [c],Locs loc loc,cs)
            else SOME res
      else if isPREFIX "*)" (CONS c cs) then
        SOME (caml_lex_ErrorS,Locs loc (lexer_fun_next_loc 2 loc),TL cs)
      else if isPREFIX (CONS (CHR 40) (CONS (CHR 42) "CML")) (CONS c cs)
          then
        match scan_pragma 0 0 (DROP 4 cs) loc with NONE -> SOME
            (caml_lex_ErrorS,Locs loc loc,"")
        | SOME (n,loc',rest) ->
            SOME (caml_lex_PragmaS (TAKE n (DROP 4 cs)),
                  Locs loc loc',
                  rest)
      else if isPREFIX [(CHR 40); (CHR 42)] (CONS c cs) then
        match caml_lex_skip_comment (TL cs) 0 (lexer_fun_next_loc 2 loc)
            with NONE -> SOME (caml_lex_ErrorS,Locs loc (lexer_fun_next_loc 2
            loc),"")
        | SOME (rest,loc') -> caml_lex_next_sym rest loc'
      else if isDelim c then
        SOME (caml_lex_OtherS [c],Locs loc loc,cs)
      else if isSym c then
        let (n,rest) = take_while isSym (CONS c cs) in
          SOME (caml_lex_OtherS n,
                Locs loc (lexer_fun_next_loc (LENGTH n - 1) loc),
                rest)
      else if isAlpha c \/ c = (CHR 95) then
        let (n,rest) = take_while (\c. isAlphaNum c \/ MEM c "'_") (CONS c
            cs) in
          SOME (caml_lex_OtherS n,
                Locs loc (lexer_fun_next_loc (LENGTH n - 1) loc),
                rest)
      else SOME (caml_lex_ErrorS,Locs loc loc,cs))`;;

(* [local] *)
let take_while_lemma = prove
 (`!acc p xs ys zs. ~(xs = "") /\
     p (HD xs) /\
     take_while_aux acc p xs = (ys,zs) ==>
       0 < LENGTH ys`,
  CHEAT_TAC);;

(* [local] *)
let scan_float2_thm = prove
 (`scan_float2 cs = SOME (s,n,ds) ==>
     0 < n /\
     LENGTH cs = n + LENGTH ds`,
  CHEAT_TAC);;

(* [local] *)
let scan_float3_thm = prove
 (`scan_float3 cs = SOME (s,n,ds) ==>
     0 < n /\
     LENGTH cs = n + LENGTH ds`,
  CHEAT_TAC);;

let next_sym_thm = prove
 (`!cs loc sym locs ds.
     caml_lex_next_sym cs loc = SOME (sym,locs,ds) ==>
       LENGTH ds < LENGTH cs`,
  CHEAT_TAC);;

(*
EVAL “next_sym "(*CML (* foo *) bar *)" loc”

EVAL “next_sym "'foo'" loc”
EVAL “next_sym "-0X2f" loc”
EVAL “next_sym "0x2f" loc”
EVAL “next_sym "0b10n" loc”
EVAL “next_sym "0o77_3" loc”
EVAL “next_sym "-1_000_099L" loc”
EVAL “next_sym "' '" loc”
EVAL “next_sym "'\\033'" loc”
EVAL “next_sym (STRCAT "'\\" "x1f'") loc”
EVAL “next_sym "'\\o015'" loc”
EVAL “next_sym "(* foo (* bar *) baz 33 \n *) -4_4_n_rest" loc”
EVAL “next_sym ("\"foo " ++ #"\\" :: #"\\" :: " f\"") loc”
EVAL “next_sym "(* foo *)\"\\nfoo foofo\"" loc”
EVAL “scan_escseq [#"\\"; #"n"] loc”

EVAL “next_sym "foo39_'2 = bar" loc”
EVAL “next_sym "= bar" loc”

EVAL “next_sym "(= bar)" loc”
EVAL “next_sym "=<! bar" loc”

EVAL “next_sym "*" loc”

EVAL “next_sym "123.456e+33" loc”
EVAL “next_sym "123.456E33" loc”
EVAL “next_sym "123." loc”
EVAL “next_sym "0.3e" loc”

 *)

let caml_lex_get_token_def = new_definition
  `caml_lex_get_token s =
     if s = "" then caml_lex_LexErrorT else if s = "=" then caml_lex_EqualT
       else if s = "'" then caml_lex_TickT else if s = "(" then caml_lex_LparT
       else if s = ")" then caml_lex_RparT else if s = "#" then caml_lex_HashT
       else if s = "*" then caml_lex_StarT else if s = "+" then caml_lex_PlusT
       else if s = "," then caml_lex_CommaT else if s = "-" then
       caml_lex_MinusT else if s = "<" then caml_lex_LessT else if s = ">" then
       caml_lex_GreaterT else if s = "[" then caml_lex_LbrackT else if s = "]"
       then caml_lex_RbrackT else if s = "{" then caml_lex_LbraceT else if s =
       "}" then caml_lex_RbraceT else if s = "?" then caml_lex_QuestionT else
       if s = ";" then caml_lex_SemiT else if s = ";;" then caml_lex_SemisT
       else if s = "|" then caml_lex_BarT else if s = "||" then
       caml_lex_OrelseT else if s = "&" then caml_lex_AmpT else if s = "&&"
       then caml_lex_AndalsoT else if s = "!=" then caml_lex_NeqT else if s =
       "-." then caml_lex_MinusFT else if s = "->" then caml_lex_RarrowT else
       if s = "<-" then caml_lex_LarrowT else if s = "." then caml_lex_DotT
       else if s = ".." then caml_lex_DotsT else if s = ".~" then
       caml_lex_EscapeT else if s = ":" then caml_lex_ColonT else if s = "::"
       then caml_lex_ColonsT else if s = ":=" then caml_lex_UpdateT else if s =
       ":>" then caml_lex_SealT else if s = "_" then caml_lex_AnyT else if s =
       "\096" then caml_lex_BtickT else if s = "~" then caml_lex_TildeT else if
       s = "{<" then caml_lex_LqbraceT else if s = ">}" then caml_lex_RqbraceT
       else if s = "[<" then caml_lex_LqbrackT else if s = ">]" then
       caml_lex_RqbrackT else if s = "[>" then caml_lex_RrbrackT else if s =
       "[|" then caml_lex_LlbrackT else if s = "|]" then caml_lex_RlbrackT else
       if s = "and" then caml_lex_AndT else if s = "as" then caml_lex_AsT else
       if s = "assert" then caml_lex_AssertT else if s = "asr" then
       caml_lex_AsrT else if s = "begin" then caml_lex_BeginT else if s =
       "class" then caml_lex_ClassT else if s = "constraint" then
       caml_lex_ConstraintT else if s = "do" then caml_lex_DoT else if s =
       "done" then caml_lex_DoneT else if s = "downto" then caml_lex_DowntoT
       else if s = "else" then caml_lex_ElseT else if s = "end" then
       caml_lex_EndT else if s = "exception" then caml_lex_ExceptionT else if s
       = "external" then caml_lex_ExternalT else if s = "false" then
       caml_lex_FalseT else if s = "for" then caml_lex_ForT else if s = "fun"
       then caml_lex_FunT else if s = "function" then caml_lex_FunctionT else
       if s = "functor" then caml_lex_FunctorT else if s = "if" then
       caml_lex_IfT else if s = "in" then caml_lex_InT else if s = "include"
       then caml_lex_IncludeT else if s = "inherit" then caml_lex_InheritT else
       if s = "initializer" then caml_lex_InitializerT else if s = "land" then
       caml_lex_LandT else if s = "lazy" then caml_lex_LazyT else if s = "let"
       then caml_lex_LetT else if s = "lor" then caml_lex_LorT else if s =
       "lsl" then caml_lex_LslT else if s = "lsr" then caml_lex_LsrT else if s
       = "lxor" then caml_lex_LxorT else if s = "match" then caml_lex_MatchT
       else if s = "method" then caml_lex_MethodT else if s = "mod" then
       caml_lex_ModT else if s = "module" then caml_lex_ModuleT else if s =
       "mutable" then caml_lex_MutableT else if s = "new" then caml_lex_NewT
       else if s = "nonrec" then caml_lex_NonrecT else if s = "object" then
       caml_lex_ObjectT else if s = "of" then caml_lex_OfT else if s = "open"
       then caml_lex_OpenT else if s = "or" then caml_lex_OrT else if s =
       "private" then caml_lex_PrivateT else if s = "rec" then caml_lex_RecT
       else if s = "sig" then caml_lex_SigT else if s = "struct" then
       caml_lex_StructT else if s = "then" then caml_lex_ThenT else if s = "to"
       then caml_lex_ToT else if s = "true" then caml_lex_TrueT else if s =
       "try" then caml_lex_TryT else if s = "type" then caml_lex_TypeT else if
       s = "val" then caml_lex_ValT else if s = "virtual" then
       caml_lex_VirtualT else if s = "when" then caml_lex_WhenT else if s =
       "while" then caml_lex_WhileT else if s = "with" then caml_lex_WithT else
     // HOL Light:
     if s = "o" then caml_lex_FuncompT else if s = "F_F" then caml_lex_F_FT
       else if s = "THEN" then caml_lex_THEN_T else if s = "THENC" then
       caml_lex_THENC_T else if s = "THENL" then caml_lex_THENL_T else if s =
       "THEN_TCL" then caml_lex_THEN_TCL_T else if s = "ORELSE" then
       caml_lex_ORELSE_T else if s = "ORELSEC" then caml_lex_ORELSEC_T else if
       s = "ORELSE_TCL" then caml_lex_ORELSE_TCL_T else
       // identifiers or symbols
       let c = HD s in
         if isAlpha c \/ c = (CHR 95) then caml_lex_IdentT (implode s)
           else caml_lex_SymbolT (implode s)`;;

let sym2token_def = new_definition
  `sym2token s =
     match s with
       caml_lex_NumberS i -> caml_lex_IntT i
     | caml_lex_FloatS s -> caml_lex_FloatT (implode s)
     | caml_lex_StringS s -> caml_lex_StringT (implode s)
     | caml_lex_CharS c -> caml_lex_CharT c
     | caml_lex_ErrorS -> caml_lex_LexErrorT
     | caml_lex_PragmaS s -> caml_lex_PragmaT (implode s)
     | caml_lex_OtherS s -> caml_lex_get_token s`;;

let caml_lex_next_token_def = new_definition
  `caml_lex_next_token inp loc =
     match caml_lex_next_sym inp loc with
       NONE -> NONE
     | SOME (sym,locs,rest) -> SOME (sym2token sym,locs,rest)`;;

let next_token_thm = prove
 (`caml_lex_next_token inp loc = SOME (sym,locs,rest) ==>
     LENGTH rest < LENGTH inp`,
  CHEAT_TAC);;

(*
EVAL “next_token "let foo = 3;; (* bar *)" loc”
EVAL “next_token "-33 + 44" loc”
EVAL “next_token "* /" loc”
EVAL “next_token "**" loc”
EVAL “next_token "(*CML (* foo bar *) baz\n\nasdf*)" loc”
EVAL “next_token "(* CML (* foo bar *) baz\n\nasdf*)" loc” (* = NONE *)
EVAL “next_token "(*CL (* foo bar *) baz\n\nasdf*)" loc” (* = NONE *)
 *)

(* the termination relation that HOL4 gives is
     MEASURE (LENGTH o FST)
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 caml_lexScript.sml:880-883: the tactic that proves the termination *)
let caml_lex_lexer_fun_aux_def,caml_lex_lexer_fun_aux_ind = define_guess
  `caml_lex_lexer_fun_aux inp loc =
     match caml_lex_next_token inp loc with
       NONE -> []
     | SOME (tok,Locs loc1 loc2,rest) -> CONS (tok,Locs loc1 loc2)
           (caml_lex_lexer_fun_aux rest (lexer_fun_next_loc 1 loc2))`;;

let caml_lex_lexer_fun_def = new_definition
  `caml_lex_lexer_fun inp = caml_lex_lexer_fun_aux inp lexer_fun_init_loc`;;

(*
EVAL “lexer_fun "true"”
EVAL “lexer_fun "false"”
EVAL “lexer_fun "()"”
EVAL “lexer_fun "begin end"”
EVAL “lexer_fun "( )"”
EVAL “lexer_fun "X.x"”
EVAL “lexer_fun "x"”
EVAL “lexer_fun "3 <+> 5 FOO"”
EVAL “lexer_fun "4;;\n(*CML code *)"”
 *)

(* -------------------------------------------------------------------------
 * PMATCH
 * ------------------------------------------------------------------------- *)

(* HOL4 caml_lexScript.sml:905: ML code, not ported *)

let isInt_PMATCH = prove
 (`!x. caml_lex_isInt x =
         match x with
           caml_lex_IntT i -> T
         | _ -> F`,
  CHEAT_TAC);;

let destInt_PMATCH = prove
 (`!x. destInt x =
         match x with
           caml_lex_IntT i -> SOME i
         | _ -> NONE`,
  CHEAT_TAC);;

let isFloat_PMATCH = prove
 (`!x. isFloat x =
         match x with
           caml_lex_FloatT i -> T
         | _ -> F`,
  CHEAT_TAC);;

let destFloat_PMATCH = prove
 (`!x. destFloat x =
         match x with
           caml_lex_FloatT i -> SOME i
         | _ -> NONE`,
  CHEAT_TAC);;

let isChar_PMATCH = prove
 (`!x. isChar x =
         match x with
           caml_lex_CharT c -> T
         | _ -> F`,
  CHEAT_TAC);;

let destChar_PMATCH = prove
 (`!x. destChar x =
         match x with
           caml_lex_CharT c -> SOME c
         | _ -> NONE`,
  CHEAT_TAC);;

let isString_PMATCH = prove
 (`!x. caml_lex_isString x =
         match x with
           caml_lex_StringT s -> T
         | _ -> F`,
  CHEAT_TAC);;

let destString_PMATCH = prove
 (`!x. destString x =
         match x with
           caml_lex_StringT s -> SOME s
         | _ -> NONE`,
  CHEAT_TAC);;

let isSymbol_PMATCH = prove
 (`!x. caml_lex_isSymbol x =
         match x with
           caml_lex_SymbolT s -> T
         | _ -> F`,
  CHEAT_TAC);;

let destSymbol_PMATCH = prove
 (`!x. destSymbol x =
         match x with
           caml_lex_SymbolT s -> SOME s
         | _ -> NONE`,
  CHEAT_TAC);;

let isIdent_PMATCH = prove
 (`!x. isIdent x =
         match x with
           caml_lex_IdentT s -> T
         | _ -> F`,
  CHEAT_TAC);;

let destIdent_PMATCH = prove
 (`!x. destIdent x =
         match x with
           caml_lex_IdentT s -> SOME s
         | _ -> NONE`,
  CHEAT_TAC);;

let isPragma_PMATCH = prove
 (`!x. isPragma x =
         match x with
           caml_lex_PragmaT s -> T
         | _ -> F`,
  CHEAT_TAC);;

let destPragma_PMATCH = prove
 (`!x. destPragma x =
         match x with
           caml_lex_PragmaT s -> SOME s
         | _ -> NONE`,
  CHEAT_TAC);;

(* and the names it reads as variables are constants again *)
let _ = do_list unhide_constant
  ["pmatch"];;

(* and the interface *)
let _ = unhide_overloads ();;
