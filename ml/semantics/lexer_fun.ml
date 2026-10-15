(* ======================================================== *)
(*  lexer_fun: ported from HOL4's
    semantics/lexer_funScript.sml  *)
(* ======================================================== *)

(*
  A functional specification of lexing from strings to token lists.
*)

needs "basis/pure/mlstring.ml";;
needs "compiler/backend/pattern_matching/pattern_semantics.ml";;
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
   | WordS (num) | LongS (string list) (string) | FFIS (string) | \
   OtherS (string) | ErrorS";;

(* helper functions *)
let mkCharS_def = cake_define
  `mkCharS x1 =
        match x1 with
          (StringS s) -> (if LENGTH s = 1 then CharS (HD s) else
            ErrorS)
        | _1 -> ErrorS`;;

let read_while_def = cake_define
  `read_while P x2 s =
        match x2 with
          "" -> (IMPLODE (REVERSE s),"")
        | (STRING c cs) ->
        (if P c then read_while P cs (c :: s) else (IMPLODE
          (REVERSE s),STRING c cs))`;;

let is_single_char_symbol_def = cake_define
  `is_single_char_symbol c = MEM c "()[]{},;"`;;

let isSymbol_def = cake_define
  `isSymbol c = MEM c (CHR 96 :: "!%&$#+-/:<=>?@\\~^|*")`;;

let next_loc_def = cake_define
  `next_loc n x =
      match x with
        (POSN r c) -> POSN r (c + n)
      | x -> x`;;

let next_line_def = cake_define
  `next_line x =
      match x with
        (POSN r c) -> POSN (r + 1) 0
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

(* HOL4 termination: THEN REPEAT STRIP_TAC THEN Cases_on `str` THEN
   FULL_SIMP_TAC (srw_ss()) [] THEN imp_res_tac
   read_char_as_3digits_reduces >> gs[] *)
let read_string_def = cake_define_wf
  `MEASURE (LENGTH o FST)`
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

let skip_comment_def = cake_define
  `(skip_comment "" d _3 = NONE) /\
   (skip_comment [x] d _4 = NONE) /\
   (skip_comment (x :: y :: xs) d loc =
     (if [x; y] = "(*" then
       skip_comment xs (d + (1:num)) (next_loc 2 loc) else if [x; y]
         = "*)" then
       (if d = 0 then SOME (xs,next_loc 2 loc) else skip_comment xs
         (d - 1) (next_loc 2 loc)) else if ORD x = 10 then
       skip_comment (y :: xs) d (next_line loc) else skip_comment
         (y :: xs) d (next_loc 1 loc)))`;;

let read_FFIcall_def = cake_define
  `(read_FFIcall "" acc loc = (ErrorS,loc,"")) /\
   (read_FFIcall (c :: s0) acc loc =
       (if c = (CHR 41) then
         (FFIS (REVERSE acc),next_loc 2 loc,s0) else if c = (CHR 10)
           then (ErrorS,loc,s0) else if isSpace c then
         read_FFIcall s0 acc (next_loc 1 loc) else
         read_FFIcall s0 (c :: acc) (next_loc 1 loc)))`;;

let read_REPLcommand_def = cake_define
  `(read_REPLcommand "" acc loc = (ErrorS,loc,"")) /\
   (read_REPLcommand (c :: s0) acc loc =
       (if c = (CHR 125) then
         (FFIS (REVERSE acc),?_col_fupd ((+) 2) loc,s0) else if c =
           (CHR 10) then (ErrorS,loc,s0) else if isSpace c then
         read_REPLcommand s0 acc (?_col_fupd ((+) 1) loc) else
         read_REPLcommand s0 (c :: acc) (?_col_fupd ((+) 1) loc)))`;;

let isAlphaNumPrime_def = cake_define
  `isAlphaNumPrime c <=> isAlphaNum c \/ (c = (CHR 39)) \/ (c = (CHR
  95))`;;

let read_Ident_ret_def = cake_define
  `read_Ident_ret acc n new_loc rest =
     (if NULL acc then
       (OtherS n,new_loc,rest) else
       (LongS (REVERSE acc) n,new_loc,rest))`;;

(* TERMINATION: wf_rel_tac ‘measure (LENGTH o FST)’ \\ rw []
  \\ imp_res_tac (GSYM read_while_thm)
  \\ Cases_on ‘str’ \\ gvs [] *)
let read_Ident_def = cake_define
  `read_Ident [] loc acc = (ErrorS,loc,[]) /\
   read_Ident (c :: str) loc acc =
     (if is_single_char_symbol c then
       if NULL acc then
         (OtherS [c],next_loc 1 loc,str) else
         (ErrorS,loc,str) else if isSymbol c then
       let (n,rest) = read_while isSymbol str [c] in
       let new_loc = next_loc (LENGTH n) loc in
         read_Ident_ret acc n new_loc rest else if isAlpha c then
       let (n,rest) = read_while isAlphaNumPrime str [c] in
       let new_loc = next_loc (LENGTH n) loc in
         match rest with [] -> read_Ident_ret acc n new_loc rest | c1
           :: rest1 ->
           (if c1 = (CHR 46) then read_Ident rest1 new_loc (n :: acc)
             else read_Ident_ret acc n new_loc rest) else
       (ErrorS,loc,str))`;;

(* next_sym reads the next symbol from a string, returning NONE if at
   eof *)
(* TERMINATION: wf_rel_tac ‘measure (LENGTH o FST)’ \\ rw []
  \\ imp_res_tac (GSYM read_while_thm)
  \\ imp_res_tac (GSYM read_string_thm)
  \\ Cases_on ‘str’ \\ gvs []
  \\ imp_res_tac skip_comment_thm \\ gvs [] *)
let next_sym_def = cake_define
  `(next_sym "" _5 = NONE) /\
   (next_sym (c :: str) loc =
      (if c = (CHR 10) then
         next_sym str (next_line loc) else if isSpace c then
        next_sym str (next_loc 1 loc) else if isDigit c then
        if ~(str = "") /\ c = (CHR 48) /\ HD str = (CHR 119) then
          if TL str = "" then SOME (ErrorS,Locs loc loc,"") else if
            isDigit (HD (TL str)) then
            let (n,rest) = read_while isDigit (TL str) [] in
              SOME (WordS (num_from_dec_string n),
                    Locs loc (next_loc (LENGTH n + 1) loc),
                    rest) else if HD (TL str) = (CHR 120) then
            let (n,rest) = read_while isHexDigit (TL (TL str)) [] in
              SOME (WordS (num_from_hex_string n),
                    Locs loc (next_loc (LENGTH n + 2) loc),
                    rest) else SOME (ErrorS,Locs loc loc,TL str) else
          if ~(str = "") /\ c = (CHR 48) /\ HD str = (CHR 120) then
            let (n,rest) = read_while isHexDigit (TL str) [] in
              SOME (NumberS (&(num_from_hex_string n)),
                    Locs loc (next_loc (LENGTH n) loc),
                    rest) else
            let (n,rest) = read_while isDigit str [] in
              SOME (NumberS (&(num_from_dec_string (c :: n))),
                    Locs loc (next_loc (LENGTH n) loc),
                    rest) else if c = (CHR 126) /\ ~(str = "") /\
                      isDigit (HD str) then
        let (n,rest) = read_while isDigit str [] in
          SOME (NumberS ((&0) - &(num_from_dec_string n)),
                Locs loc (next_loc (LENGTH n + 1) loc),
                rest) else if c = (CHR 39) then
        let (n,rest) = read_while isAlphaNumPrime str [c] in
          SOME (OtherS n,Locs loc (next_loc (LENGTH n - 1) loc),
                rest) else if c = (CHR 34) then
        let (t,loc',rest) = read_string str "" (next_loc 1 loc) in
          SOME (t,Locs loc loc',rest) else if isPREFIX "*)" (c ::
            str) then
        SOME (ErrorS,Locs loc (next_loc 2 loc),TL str) else if
          isPREFIX "#\"" (c :: str) then
        let (t,loc',rest) = read_string (TL str) "" (next_loc 2 loc)
          in
          SOME (mkCharS t,Locs loc loc',rest) else if isPREFIX "#("
            (c :: str) then
        let (t,loc',rest) = read_FFIcall (TL str) "" (next_loc 2 loc)
          in
          SOME (t,Locs loc loc',rest) else if isPREFIX "(*" (c ::
            str) then
        match skip_comment (TL str) 0 (next_loc 2 loc) with NONE ->
          SOME (ErrorS,Locs loc (next_loc 2 loc),"") | SOME (rest,loc')
          -> next_sym rest loc' else if c = (CHR 95) then SOME (OtherS
          "_",Locs loc loc,str) else
        let (tok',end_loc,rest) = read_Ident (c :: str) loc [] in
          SOME (tok',Locs loc end_loc,rest)))`;;

(* EVAL “next_sym "  Foo.Bar.<  " (POSN 0 0)” *)

(* HOL4 ML code, not ported:
val listeq = CaseEq "list"
val optioneq = CaseEq "option"
*)

let init_loc_def = cake_define
  `init_loc = POSN 0 0`;;

(*

  EVAL ``next_sym " (* hi (* there \" *) *)\n  ~4 \" (* *)\" <= ;; "
    init_loc ``
  EVAL ``next_sym "0w10 +" init_loc``;
  EVAL ``next_sym "0wx1A +" init_loc``;

*)

(* next_token reads the next token from a string *)

let processIdent_def = cake_define
  `processIdent s =
     (match s with "" -> LexErrorT | c :: s ->
            (if isAlpha c then
              AlphaT (implode (c :: s)) else
              SymbolT (implode (c :: s))))`;;

let get_token_def = cake_define
  `get_token s =
     (if s = "#" then HashT else
     if s = "(" then LparT else
     if s = ")" then RparT else
     if s = "*" then StarT else
     if s = "," then CommaT else
     if s = "->" then ArrowT else
     if s = "..." then DotsT else
     if s = ":" then ColonT else
     if s = ":>" then SealT else
     if s = ";" then SemicolonT else
     if s = "=" then EqualsT else
     if s = "=>" then DarrowT else
     if s = "[" then LbrackT else
     if s = "]" then RbrackT else
     if s = "_" then UnderbarT else
     if s = "{" then LbraceT else
     if s = "}" then RbraceT else
     if s = "|" then BarT else
     if s = "and" then AndT else
     if s = "andalso" then AndalsoT else
     if s = "as" then AsT else
     if s = "case" then CaseT else
     if s = "datatype" then DatatypeT else
     if s = "else" then ElseT else
     if s = "end" then EndT else
     if s = "eqtype" then EqtypeT else
     if s = "exception" then ExceptionT else
     if s = "fn" then FnT else
     if s = "fun" then FunT else
     if s = "handle" then HandleT else
     if s = "if" then IfT else
     if s = "in" then InT else
     if s = "include" then IncludeT else
     if s = "let" then LetT else
     if s = "local" then LocalT else
     if s = "of" then OfT else
     if s = "op" then OpT else
     if s = "open" then OpenT else
     if s = "orelse" then OrelseT else
     if s = "raise" then RaiseT else
     if s = "rec" then RecT else
     if s = "sharing" then SharingT else
     if s = "sig" then SigT else
     if s = "signature" then SignatureT else
     if s = "struct" then StructT else
     if s = "structure" then StructureT else
     if s = "then" then ThenT else
     if s = "type" then TypeT else
     if s = "val" then ValT else
     if s = "where" then WhereT else
     if s = "with" then WithT else
     if s = "withtype" then WithtypeT else
     if ~(s = "") /\ HD s = (CHR 39) then TyvarT (implode s) else
     processIdent s)`;;

let to_path_def = cake_define
  `to_path [] = End /\
   to_path (x :: xs) = Mod x (to_path xs)`;;

let token_of_sym_def = cake_define
  `token_of_sym s =
     (match s with ErrorS -> LexErrorT | StringS s -> StringT
       (implode s) | CharS c -> CharT c | NumberS i -> IntT i | WordS
       n -> WordT n | LongS xs s -> LongidT (to_path (MAP implode
       xs)) (implode s) | FFIS s -> FFIT (implode s) | OtherS s ->
       get_token s)`;;

let next_token_def = cake_define
  `next_token input loc =
     (match next_sym input loc with NONE -> NONE | SOME
       (sym,locs,rest_of_input) ->
         SOME (token_of_sym sym,locs,rest_of_input))`;;

(* top-level lexer specification *)

(* HOL4 termination: >> rw[] >> imp_res_tac next_token_LESS *)
let lexer_fun_aux_def = cake_define_wf
  `MEASURE (LENGTH o FST)`
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

let toplevel_semi_dex_def = cake_define
  `(toplevel_semi_dex (i:num) (d:num) [] = NONE) /\
   (toplevel_semi_dex i d ((h,l) :: t) =
     (if h = SemicolonT /\ (d = 0) then SOME (i + 1) else if h =
       LetT then toplevel_semi_dex (i + 1) (d + 1) t else if h =
       StructT then toplevel_semi_dex (i + 1) (d + 1) t else if h =
       SigT then toplevel_semi_dex (i + 1) (d + 1) t else if h =
       LparT then toplevel_semi_dex (i + 1) (d + 1) t else if h =
       EndT then toplevel_semi_dex (i + 1) (d - 1) t else if h =
       RparT then toplevel_semi_dex (i + 1) (d - 1) t else
       toplevel_semi_dex (i + 1) d t))`;;

(* TERMINATION: wf_rel_tac `measure LENGTH` >>
  rw [] >>
  cases_on `toks` >>
  fs [toplevel_semi_dex_def] >>
  cases_on `h` >>
  fs [] >>
  metis_tac [toplevel_semi_dex_non0, DECIDE ``0 < 1:num``, DECIDE
    ``∀x:num. 0 < x + 1``] *)
let split_top_level_semi_def = cake_define
  `(split_top_level_semi toks =
    (match toplevel_semi_dex 0 0 toks with NONE -> [] | SOME i ->
        TAKE i toks :: split_top_level_semi (DROP i toks)))`;;
