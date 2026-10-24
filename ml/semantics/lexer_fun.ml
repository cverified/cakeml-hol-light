(* ======================================================== *)
(*  lexer_fun: ported from HOL4's
    semantics/lexer_funScript.sml
    A definition theory, with 25 definitions, 1 datatype and 14
    theorems.  Needed by compiler.ml, compilerProof.ml,
    lexer_impl.ml and semantics.ml.  *)
(* ======================================================== *)

(*
  A functional specification of lexing from strings to token lists.
*)

needs "basis/pure/mlstring.ml";;
needs "lib/ASCIInumbers.ml";;
needs "lib/location.ml";;
needs "semantics/tokens.ml";;
(* HOL4 ancestors outside the port: string list *)

(* This script defines the functional spec for the assembly
   implementation of the lexer. This lexer specification consists of
   two phases. The first phase reads a string and returns a list of
   symbols. The second phase converts the symbol list into a list of
   tokens. The implementation merges these two phases. *)

(* intermediate symbols *)

let lexer_fun_symbol_INDUCT,lexer_fun_symbol_RECURSION = define_datatype
  "lexer_fun_symbol = StringS (string) | CharS (char) | NumberS (int) \
   | WordS (num) | LongS (string list) (string) \
   // [\"Foo\";\"Bar\"] \"<\" is Foo.Bar.<\n\
   | FFIS (string) | OtherS (string) | ErrorS";;

(* helper functions *)
let mkCharS_def = cake_define
  `mkCharS x1 =
        match x1 with
          StringS s -> (if LENGTH s = 1 then CharS (HD s) else
            ErrorS)
        | _1 -> ErrorS`;;

let read_while_def = cake_define
  `read_while P x2 s =
        match x2 with
          "" -> (IMPLODE (REVERSE s),"")
        | (STRING c cs) ->
        (if P c then read_while P cs (c :: s) else (IMPLODE
          (REVERSE s),STRING c cs))`;;

let read_while_thm = prove
 (`!cs s cs' s'.
       (read_while P cs s = (s',cs')) ==> STRLEN cs' <= STRLEN cs`,
  CHEAT_TAC);;

let is_single_char_symbol_def = cake_define
  `is_single_char_symbol c = MEM c "()[]{},;"`;;

let isSymbol_def = cake_define
  `isSymbol c = MEM c (CHR 96 ::
                // backquote
                "!%&$#+-/:<=>?@\\~^|*")`;;

let next_loc_def = cake_define
  `next_loc n x =
      match x with
        POSN r c -> POSN r (c + n)
      | x -> x`;;

let next_line_def = cake_define
  `next_line x =
      match x with
        POSN r c -> POSN (r + 1) 0
      | x -> x`;;

let read_char_as_3digits_def = cake_define
  `read_char_as_3digits str =
   (let ds = TAKE 3 str in let
       rest = DROP 3 str in
     if LENGTH ds < 3 then NONE else
       match FOLDL (\A d. match A with
                           NONE -> NONE | SOME A0 -> (if isDigit d
                             then
                              SOME (10 * A0 + (ORD d - 48)) else
                                NONE))
                  (SOME 0) ds with
         NONE -> NONE | SOME ci ->
           (if ci < 256 then SOME (CHR ci,rest) else NONE))`;;

let read_char_as_3digits_reduces = prove
 (`!str0 c str.
     read_char_as_3digits str0 = SOME (c,str) ==>
     LENGTH str0 = LENGTH str + 3`,
  CHEAT_TAC);;

(* HOL4 lexer_funScript.sml:122-126: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let lexer_fun_read_string_def = cake_define_try_tac (fun () ->
  `MEASURE (LENGTH o FST)`)
  CHEAT_TAC
  `lexer_fun_read_string str s (loc:locn) =
     (if str = "" then (ErrorS,loc,"") else
     if HD str = (CHR 34) then (StringS s,loc,TL str) else
     if HD str = (CHR 10) then (ErrorS,next_line loc,TL str) else
     if ~(HD str = (CHR 92)) then
       lexer_fun_read_string (TL str) (s ++ [HD str]) (next_loc 1
         loc) else
       match TL str with (CHR 92) :: cs -> lexer_fun_read_string cs
         (s ++ "\\") (next_loc 2 loc) | (CHR 34) :: cs ->
         lexer_fun_read_string cs (s ++ "\"") (next_loc 2 loc) | (CHR
         97) :: cs -> lexer_fun_read_string cs (s ++ [CHR 7]) (next_loc
         2 loc) | (CHR 98) :: cs -> lexer_fun_read_string cs (s ++ [CHR
         8]) (next_loc 2 loc) | (CHR 116) :: cs -> lexer_fun_read_string
         cs (s ++ [CHR 9]) (next_loc 2 loc) | (CHR 110) :: cs ->
         lexer_fun_read_string cs (s ++ [CHR 10]) (next_loc 2 loc) |
         (CHR 118) :: cs -> lexer_fun_read_string cs (s ++ [CHR 11])
         (next_loc 2 loc) | (CHR 102) :: cs -> lexer_fun_read_string cs
         (s ++ [CHR 12]) (next_loc 2 loc) | (CHR 114) :: cs ->
         lexer_fun_read_string cs (s ++ [CHR 13]) (next_loc 2 loc) | c
         :: cs -> (if isDigit c then
                    match read_char_as_3digits (c :: cs) with
                      NONE -> (ErrorS,loc,c :: cs) | SOME (c,cs') ->
                        lexer_fun_read_string cs' (s ++ [c])
                              (next_loc 4 loc) else (ErrorS,loc,TL
                                str)) | _2 -> (ErrorS,loc,TL str))`;;
hol4_overload "read_string" "lexer_fun_read_string";;

let read_string_thm = prove
 (`!s t l l' x1 x2. (lexer_fun_read_string s t l = (x1,l',x2)) ==>
                    (LENGTH x2 <= LENGTH s + LENGTH t)`,
  CHEAT_TAC);;

let skip_comment_def = cake_define_list
  [`skip_comment "" d _3 = NONE`;
   `skip_comment [x] d _4 = NONE`;
   `skip_comment (x :: y :: xs) d loc =
        (if [x; y] = "(*" then
          skip_comment xs (d + (1:num)) (next_loc 2 loc) else if [x;
            y] = "*)" then
          (if d = 0 then SOME (xs,next_loc 2 loc) else skip_comment
            xs (d - 1) (next_loc 2 loc)) else if ORD x = 10 then
          skip_comment (y :: xs) d (next_line loc) else
            skip_comment (y :: xs) d (next_loc 1 loc))`];;

let skip_comment_thm = prove
 (`!xs d l l' str. (skip_comment xs d l = SOME (str,l')) ==> LENGTH
  str <= LENGTH xs`,
  CHEAT_TAC);;

let read_FFIcall_def = cake_define_list
  [`read_FFIcall "" acc loc = (ErrorS,loc,"")`;
   `read_FFIcall (c :: s0) acc loc =
          (if c = (CHR 41) then
            (FFIS (REVERSE acc),next_loc 2 loc,s0) else if c = (CHR
              10) then (ErrorS,loc,s0) else if isSpace c then
            read_FFIcall s0 acc (next_loc 1 loc) else
            read_FFIcall s0 (c :: acc) (next_loc 1 loc))`];;

let read_FFIcall_reduces_input = prove
 (`!s0 a l0 t l s.
     read_FFIcall s0 a l0 = (t,l,s) ==> LENGTH s < LENGTH s0 + 1`,
  CHEAT_TAC);;

let read_REPLcommand_def = cake_define_list
  [`read_REPLcommand "" acc loc = (ErrorS,loc,"")`;
   `read_REPLcommand (c :: s0) acc loc =
          (if c = (CHR 125) then
            (FFIS (REVERSE acc),locn_colupdate ((+) 2) loc,s0) else
              if c = (CHR 10) then (ErrorS,loc,s0) else if isSpace c
              then
            read_REPLcommand s0 acc (locn_colupdate ((+) 1) loc)
              else
            read_REPLcommand s0 (c :: acc) (locn_colupdate ((+)
              1) loc))`];;

let read_REPLcommand_reduces_input = prove
 (`!s0 a l0 t l s.
     read_REPLcommand s0 a l0 = (t,l,s) ==> LENGTH s < LENGTH s0 +
       1`,
  CHEAT_TAC);;

let isAlphaNumPrime_def = cake_define
  `isAlphaNumPrime c <=> isAlphaNum c \/ (c = (CHR 39)) \/ (c = (CHR
  95))`;;

let read_Ident_ret_def = cake_define
  `read_Ident_ret acc n new_loc rest =
     (if NULL acc then
       (OtherS n,new_loc,rest) else
       (LongS (REVERSE acc) n,new_loc,rest))`;;

(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 lexer_funScript.sml:247-251: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let read_Ident_def = cake_define_list_try_tac (fun () ->
  `MEASURE (LENGTH o FST)`)
  CHEAT_TAC
  [`read_Ident [] loc acc = (ErrorS,loc,[])`;
   `read_Ident (c :: str) loc acc =
      (if is_single_char_symbol c then
        // single character tokens, i.e. delimiters
        if NULL acc then
          (OtherS [c],next_loc 1 loc,str) else
          (ErrorS,loc,str) else if isSymbol c then
        let (n,rest) = read_while isSymbol str [c] in
        let new_loc = next_loc (LENGTH n) loc in
          read_Ident_ret acc n new_loc rest else if isAlpha c then
        let (n,rest) = read_while isAlphaNumPrime str [c] in
        let new_loc = next_loc (LENGTH n) loc in
          match rest with [] -> read_Ident_ret acc n new_loc rest |
            c1 :: rest1 ->
            (if c1 = (CHR 46) then read_Ident rest1 new_loc (n ::
              acc) else read_Ident_ret acc n new_loc rest) else
        (
         // input not recognised
         ErrorS,loc,str))`];;

(* next_sym reads the next symbol from a string, returning NONE if at eof *)
(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 lexer_funScript.sml:314-320: the tactic that proves the
   termination *)
let next_sym_def = cake_define_list_try (fun () ->
  `MEASURE (LENGTH o FST)`)
  [`next_sym "" _5 = NONE`;
   `next_sym (c :: str) loc =
         (if c = (CHR 10) then
            // skip new line
            next_sym str (next_line loc) else if isSpace c then
           // skip blank space
           next_sym str (next_loc 1 loc) else if isDigit c then
           // read number
           if ~(str = "") /\ c = (CHR 48) /\ HD str = (CHR 119) then
             if TL str = "" then SOME (ErrorS,Locs loc loc,"") else
               if isDigit (HD (TL str)) then
               let (n,rest) = read_while isDigit (TL str) [] in
                 SOME (WordS (num_from_dec_string n),
                       Locs loc (next_loc (LENGTH n + 1) loc),
                       rest) else if HD (TL str) = (CHR 120) then
               let (n,rest) = read_while isHexDigit (TL (TL str)) []
                 in
                 SOME (WordS (num_from_hex_string n),
                       Locs loc (next_loc (LENGTH n + 2) loc),
                       rest) else SOME (ErrorS,Locs loc loc,TL str)
                         else
             if ~(str = "") /\ c = (CHR 48) /\ HD str = (CHR 120)
               then
               let (n,rest) = read_while isHexDigit (TL str) [] in
                 SOME (NumberS (&(num_from_hex_string n)),
                       Locs loc (next_loc (LENGTH n) loc),
                       rest) else
               let (n,rest) = read_while isDigit str [] in
                 SOME (NumberS (&(num_from_dec_string (c :: n))),
                       Locs loc (next_loc (LENGTH n) loc),
                       rest) else if c = (CHR 126) /\ ~(str = "") /\
                         isDigit (HD str) then
           // read negative number
           let (n,rest) = read_while isDigit str [] in
             SOME (NumberS ((&0) - &(num_from_dec_string n)),
                   Locs loc (next_loc (LENGTH n + 1) loc),
                   rest) else if c = (CHR 39) then
           // read type variable
           let (n,rest) = read_while isAlphaNumPrime str [c] in
             SOME (OtherS n,Locs loc (next_loc (LENGTH n - 1) loc),
                   rest) else if c = (CHR 34) then
           // read string
           let (t,loc',rest) = lexer_fun_read_string str ""
             (next_loc 1 loc) in
             SOME (t,Locs loc loc',rest) else if isPREFIX "*)" (c ::
               str) then
           SOME (ErrorS,Locs loc (next_loc 2 loc),TL str) else if
             isPREFIX "#\"" (c :: str) then
           let (t,loc',rest) = lexer_fun_read_string (TL str) ""
             (next_loc 2 loc) in
             SOME (mkCharS t,Locs loc loc',rest) else if isPREFIX
               "#(" (c :: str) then
           let (t,loc',rest) = read_FFIcall (TL str) "" (next_loc 2
             loc) in
             SOME (t,Locs loc loc',rest) else if isPREFIX "(*" (c ::
               str) then
           match skip_comment (TL str) 0 (next_loc 2 loc) with NONE
             -> SOME (ErrorS,Locs loc (next_loc 2 loc),"") | SOME
             (rest,loc') -> next_sym rest loc' else if c = (CHR 95) then
             SOME (OtherS "_",Locs loc loc,str) else
           let (tok',end_loc,rest) = read_Ident (c :: str) loc [] in
             SOME (tok',Locs loc end_loc,rest))`];;

(* EVAL “next_sym "  Foo.Bar.<  " (POSN 0 0)” *)

(* [local] *)
let lem1 = prove
 (`((let (x,y) = z a in f x y) = P a) = (let (x,y) = z a in (f x y = P
  a))`,
  CHEAT_TAC);;

(* [local] *)
let lem2 = prove
 (`((let (x,y) = z a in f x y) ==> P a) = (let (x,y) = z a in (f x y
  ==> P a))`,
  CHEAT_TAC);;

(* HOL4 lexer_funScript.sml:342: a theorem that HOL4 states as the
   value of an ML expression: read_while_EMPTY *)

(* [local] *)
let NOT_NIL_EXISTS_CONS = prove
 (`(~(n = []) <=> (?h t. n = h :: t)) /\
   (list_CASE n F P <=> (?h t. n = h :: t /\ P h t))`,
  CHEAT_TAC);;

(* HOL4 lexer_funScript.sml:350-351: ML code, not ported *)

let read_Ident_LESS = prove
 (`!xs l acc s loc rest.
     read_Ident xs l acc = (s,loc,rest) ==>
     (if xs = [] then rest = [] else LENGTH rest < LENGTH xs)`,
  CHEAT_TAC);;

let next_sym_LESS = prove
 (`!input l s l' rest.
     next_sym input l = SOME (s,l',rest) ==>
     LENGTH rest < LENGTH input`,
  CHEAT_TAC);;

let init_loc_def = cake_define
  `init_loc = POSN 0 0`;;

(*

  EVAL ``next_sym " (* hi (* there \" *) *)\n  ~4 \" (* *)\" <= ;; " init_loc ``
  EVAL ``next_sym "0w10 +" init_loc``;
  EVAL ``next_sym "0wx1A +" init_loc``;

*)

(* next_token reads the next token from a string *)

let processIdent_def = cake_define
  `processIdent s =
     (match s with "" -> tokens_LexErrorT | c :: s ->
            (if isAlpha c then
              tokens_AlphaT (implode (c :: s)) else
              tokens_SymbolT (implode (c :: s))))`;;

let get_token_def = cake_define
  `get_token s =
     (if s = "#" then tokens_HashT else
     if s = "(" then tokens_LparT else
     if s = ")" then tokens_RparT else
     if s = "*" then tokens_StarT else
     if s = "," then tokens_CommaT else
     if s = "->" then tokens_ArrowT else
     if s = "..." then tokens_DotsT else
     if s = ":" then tokens_ColonT else
     if s = ":>" then tokens_SealT else
     if s = ";" then tokens_SemicolonT else
     if s = "=" then tokens_EqualsT else
     if s = "=>" then tokens_DarrowT else
     if s = "[" then tokens_LbrackT else
     if s = "]" then tokens_RbrackT else
     if s = "_" then tokens_UnderbarT else
     if s = "{" then tokens_LbraceT else
     if s = "}" then tokens_RbraceT else
     if s = "|" then tokens_BarT else
     if s = "and" then tokens_AndT else
     if s = "andalso" then tokens_AndalsoT else
     if s = "as" then tokens_AsT else
     if s = "case" then tokens_CaseT else
     if s = "datatype" then tokens_DatatypeT else
     if s = "else" then tokens_ElseT else
     if s = "end" then tokens_EndT else
     if s = "eqtype" then tokens_EqtypeT else
     if s = "exception" then tokens_ExceptionT else
     if s = "fn" then tokens_FnT else
     if s = "fun" then tokens_FunT else
     if s = "handle" then tokens_HandleT else
     if s = "if" then tokens_IfT else
     if s = "in" then tokens_InT else
     if s = "include" then tokens_IncludeT else
     if s = "let" then tokens_LetT else
     if s = "local" then tokens_LocalT else
     if s = "of" then tokens_OfT else
     if s = "op" then tokens_OpT else
     if s = "open" then tokens_OpenT else
     if s = "orelse" then tokens_OrelseT else
     if s = "raise" then tokens_RaiseT else
     if s = "rec" then tokens_RecT else
     if s = "sharing" then tokens_SharingT else
     if s = "sig" then tokens_SigT else
     if s = "signature" then tokens_SignatureT else
     if s = "struct" then tokens_StructT else
     if s = "structure" then tokens_StructureT else
     if s = "then" then tokens_ThenT else
     if s = "type" then tokens_TypeT else
     if s = "val" then tokens_ValT else
     if s = "where" then tokens_WhereT else
     if s = "with" then tokens_WithT else
     if s = "withtype" then tokens_WithtypeT else
     if ~(s = "") /\ HD s = (CHR 39) then tokens_TyvarT (implode s)
       else
     processIdent s)`;;

let to_path_def = cake_define_list
  [`to_path [] = tokens_End`;
   `to_path (x :: xs) = tokens_Mod x (to_path xs)`];;

let token_of_sym_def = cake_define
  `token_of_sym s =
     (match s with ErrorS -> tokens_LexErrorT | StringS s ->
       tokens_StringT (implode s) | CharS c -> tokens_CharT c |
       NumberS i -> tokens_IntT i | WordS n -> tokens_WordT n | LongS
       xs s -> tokens_LongidT (to_path (MAP implode xs)) (implode s)
       | FFIS s -> tokens_FFIT (implode s) | OtherS s -> get_token s)`;;

let next_token_def = cake_define
  `next_token input loc =
     (match next_sym input loc with NONE -> NONE | SOME
       (sym,locs,rest_of_input) ->
         SOME (token_of_sym sym,locs,rest_of_input))`;;

let next_token_LESS = prove
 (`!s l l' rest input. (next_token input l = SOME (s,l',rest)) ==>
                   LENGTH rest < LENGTH input`,
  CHEAT_TAC);;

(* top-level lexer specification *)

(* HOL4 lexer_funScript.sml:516-518: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let lexer_fun_aux_def = cake_define_try_tac (fun () ->
  `MEASURE (LENGTH o FST)`)
  CHEAT_TAC
  `lexer_fun_aux input loc =
     (match next_token input loc with NONE -> [] | SOME (token,Locs
       loc' loc'',rest_of_input) ->
         (token,Locs loc' loc'') ::
             lexer_fun_aux rest_of_input (next_loc 1 loc''))`;;

let lexer_fun_def = cake_define
  `lexer_fun input = lexer_fun_aux input init_loc`;;

(*

  A few tests:

    EVAL ``lexer_fun "3 (* hi (* there \" *) *) ~4 \" (* *)\" <= ;; "``;
    EVAL ``lexer_fun "3 (* hi (* there  *) *) ~4 \" (* *)\" <= ;; "``;
    EVAL ``lexer_fun "a b cd c2 c3'"``;
    EVAL ``lexer_fun "'a 'b '2"``;
    EVAL ``lexer_fun "'"``;
    EVAL ``lexer_fun "0w10 + 0wxAa3F"``;
    EVAL ``lexer_fun "0w"`;

*)

(* split a list of tokens at top-level semicolons *)

let toplevel_semi_dex_def = cake_define_list
  [`toplevel_semi_dex (i:num) (d:num) [] = NONE`;
   `toplevel_semi_dex (i:num) (d:num) ((h,l) :: t) =
        (if h = tokens_SemicolonT /\ (d = 0) then SOME (i + 1)
          else if h = tokens_LetT then toplevel_semi_dex (i + 1) (d
          + 1) t else if h = tokens_StructT then toplevel_semi_dex
          (i + 1) (d + 1) t else if h = tokens_SigT then
          toplevel_semi_dex (i + 1) (d + 1) t else if h =
          tokens_LparT then toplevel_semi_dex (i + 1) (d + 1) t
          else if h = tokens_EndT then toplevel_semi_dex (i + 1) (d
          - 1) t else if h = tokens_RparT then toplevel_semi_dex (i
          + 1) (d - 1) t else toplevel_semi_dex (i + 1) d t)`];;

(* [local] *)
let toplevel_semi_dex_non0 = prove
 (`!i d toks j. (toplevel_semi_dex i d toks = SOME j) ==> 0 < j`,
  CHEAT_TAC);;

(* HOL4 lexer_funScript.sml:570-578: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let split_top_level_semi_def = cake_define_try_tac (fun () ->
  `MEASURE LENGTH`)
  CHEAT_TAC
  `(split_top_level_semi toks =
    (match toplevel_semi_dex 0 0 toks with NONE -> [] | SOME i ->
        TAKE i toks :: split_top_level_semi (DROP i toks)))`;;
