(* ======================================================== *)
(*  panLexer: ported from HOL4's
    pancake/parser/panLexerScript.sml
    A definition theory, with 23 definitions, 3 datatypes and 3
    theorems.  Needed by panPEG.ml, panPtreeConversion.ml and
    pancake_lexProg.ml.  *)
(* ======================================================== *)

(**
 * A lexer for the Pancake language.
 *)

(**
 * We take significant inspiration from the Spark ADA development.
 *
 * Author: Craig McLaughlin
 * Date: March--April 2022
 *)

needs "basis/pure/mlstring.ml";;
needs "lib/ASCIInumbers.ml";;
needs "lib/errorMonad.ml";;
needs "lib/location.ml";;
needs "lib/peg.ml";;
needs "misc/misc.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "panLexer"
  ["mlstring"];;
(* HOL4 ancestors outside the port: arithmetic string list *)


let keyword_INDUCT,keyword_RECURSION = define_datatype
  "keyword =
     SkipK
   | StK
   | StwK
   | St8K
   | St16K
   | St32K
   | IfK
   | ElseK
   | WhileK
   | BrK
   | ContK
   | ThrowK
   | RetK
   | TicK
   | VarK
   | TryK
   | CatchK
   | BiwK
   | NamedK
   | LdsK
   | Ld8K
   | LdwK
   | Ld16K
   | Ld32K
   | BaseK
   | TopK
   | InK
   | FunK
   | ExportK
   | TrueK
   | FalseK
   | InlineK
   | ExceptionK";;

let panLexer_token_INDUCT,panLexer_token_RECURSION = define_datatype
  "panLexer_token =
     panLexer_AndT
   | panLexer_OrT
   | panLexer_BoolAndT
   | panLexer_BoolOrT
   | panLexer_XorT
   | panLexer_NotT
   | panLexer_ArrowT
   | panLexer_EqT
   | panLexer_NeqT
   | panLexer_LessT
   | panLexer_GreaterT
   | panLexer_GeqT
   | panLexer_LeqT
   | panLexer_LowerT
   | panLexer_HigherT
   | panLexer_HigheqT
   | panLexer_LoweqT
   | panLexer_PlusT
   | panLexer_MinusT
   | panLexer_DotT
   | panLexer_StarT
   | panLexer_LslT
   | panLexer_LsrT
   | panLexer_AsrT
   | panLexer_RorT
   | panLexer_IntT int
   | panLexer_IdentT string
   | panLexer_ForeignIdent string
     // @ffi_str except @base, @biw, @top
   | panLexer_LParT
   | panLexer_RParT
   | panLexer_CommaT
   | panLexer_SemiT
   | panLexer_ColonT
   | panLexer_AddrT
   | panLexer_LBrakT
   | panLexer_RBrakT
   | panLexer_LCurT
   | panLexer_RCurT
   | panLexer_AssignT
   | panLexer_StaticT
   | panLexer_NoinlineT
   | panLexer_DefaultShT
   | panLexer_KeywordT keyword
   | panLexer_AnnotCommentT string
   | panLexer_LexErrorT mlstring";;

let panLexer_atom_INDUCT,panLexer_atom_RECURSION = define_datatype
  "panLexer_atom =
     NumberA int
   | WordA string
   | SymA string
   | ErrA mlstring
   | AnnotCommentA string";;

let isAtom_singleton_def = new_definition
  `isAtom_singleton c = MEM c "+-^*().,;:[]{}"`;;

let isAtom_begin_group_def,isAtom_begin_group_ind = define_guess
  `// # is for only for RorT,
   // * and should remove it to avoid collision with
   // * C-preprocessor later
   isAtom_begin_group c = MEM c "#=><!&|"`;;

let isAtom_in_group_def = new_definition
  `isAtom_in_group c = MEM c "=<>|&+"`;;

let isAlphaNumOrWild_def = new_definition
  `isAlphaNumOrWild c <=> isAlphaNum c \/ c = (CHR 95)`;;

(* HOL4 panLexerScript.sml:65-68: the definition *)

let dest_lexErrorT_def = new_definition
  `destLexErrorT x1 =
     match x1 with
       panLexer_LexErrorT msg -> SOME msg
     | _ -> NONE`;;

let panLexer_get_token_def = new_definition
  `panLexer_get_token s =
   if s = "&&" then panLexer_BoolAndT else if s = "||" then
     panLexer_BoolOrT else if s = "&" then panLexer_AndT else if s = "|"
     then panLexer_OrT else if s = "^" then panLexer_XorT else if s = "=="
     then panLexer_EqT else if s = "=>" then panLexer_ArrowT else if s =
     "!=" then panLexer_NeqT else if s = "<" then panLexer_LessT else if s =
     ">" then panLexer_GreaterT else if s = ">=" then panLexer_GeqT else if
     s = "<=" then panLexer_LeqT else if s = "<+" then panLexer_LowerT else
     if s = ">+" then panLexer_HigherT else if s = ">=+" then
     panLexer_HigheqT else if s = "<=+" then panLexer_LoweqT else if s = "!"
     then panLexer_NotT else if s = "+" then panLexer_PlusT else if s = "-"
     then panLexer_MinusT else if s = "*" then panLexer_StarT else if s =
     "." then panLexer_DotT else if s = "<<" then panLexer_LslT else if s =
     ">>>" then panLexer_LsrT else if s = ">>" then panLexer_AsrT else if s
     = "#>>" then panLexer_RorT else if s = "(" then panLexer_LParT else if
     s = ")" then panLexer_RParT else if s = "," then panLexer_CommaT else
     if s = ";" then panLexer_SemiT else if s = ":" then panLexer_ColonT
     else if s = "[" then panLexer_LBrakT else if s = "]" then
     panLexer_RBrakT else if s = "{" then panLexer_LCurT else if s = "}"
     then panLexer_RCurT else if s = "=" then panLexer_AssignT else
     panLexer_LexErrorT (mlstring_concat [(implode
     "Unrecognised symbolic token: "); implode s])`;;

let get_keyword_def = new_definition
  `get_keyword s =
   if s = "skip" then (panLexer_KeywordT SkipK) else if s = "st" then
     (panLexer_KeywordT StK) else if s = "stw" then (panLexer_KeywordT StwK)
     else if s = "st8" then (panLexer_KeywordT St8K) else if s = "st16" then
     (panLexer_KeywordT St16K) else if s = "st32" then (panLexer_KeywordT
     St32K) else if s = "if" then (panLexer_KeywordT IfK) else if s = "else"
     then (panLexer_KeywordT ElseK) else if s = "while" then (panLexer_KeywordT
     WhileK) else if s = "break" then (panLexer_KeywordT BrK) else if s =
     "continue" then (panLexer_KeywordT ContK) else if s = "throw" then
     (panLexer_KeywordT ThrowK) else if s = "return" then (panLexer_KeywordT
     RetK) else if s = "tick" then (panLexer_KeywordT TicK) else if s = "var"
     then (panLexer_KeywordT VarK) else if s = "in" then (panLexer_KeywordT
     InK) else if s = "try" then (panLexer_KeywordT TryK) else if s = "catch"
     then (panLexer_KeywordT CatchK) else if s = "lds" then (panLexer_KeywordT
     LdsK) else if s = "ldw" then (panLexer_KeywordT LdwK) else if s = "ld8"
     then (panLexer_KeywordT Ld8K) else if s = "ld16" then (panLexer_KeywordT
     Ld16K) else if s = "ld32" then (panLexer_KeywordT Ld32K) else if s =
     "@base" then (panLexer_KeywordT BaseK) else if s = "@top" then
     (panLexer_KeywordT BaseK) else if s = "@biw" then (panLexer_KeywordT BiwK)
     else if s = "true" then (panLexer_KeywordT TrueK) else if s = "false" then
     (panLexer_KeywordT FalseK) else if s = "fun" then (panLexer_KeywordT FunK)
     else if s = "export" then (panLexer_KeywordT ExportK) else if s = "inline"
     then (panLexer_KeywordT InlineK) else if s = "exception" then
     (panLexer_KeywordT ExceptionK) else if s = "struct" then
     (panLexer_KeywordT NamedK) else if s = "" then panLexer_LexErrorT (implode
     "Expected keyword, found empty string") else if 2 <= LENGTH s /\ EL 0 s =
     (CHR 64) then panLexer_ForeignIdent (DROP 1 s)
   else panLexer_IdentT s`;;

let token_of_atom_def = new_definition
  `token_of_atom a =
   match a with NumberA i -> panLexer_IntT i
   | WordA s -> get_keyword s
   | SymA s -> panLexer_get_token s
   | ErrA s -> panLexer_LexErrorT s
   | AnnotCommentA s -> panLexer_AnnotCommentT s`;;

let panLexer_read_while_def,panLexer_read_while_ind = define_guess
  `panLexer_read_while P x2 s =
     match x2 with
       "" -> (IMPLODE (REVERSE s),"")
     | CONS c cs ->
      if P c then panLexer_read_while P cs (CONS c s)
      else (IMPLODE (REVERSE s),CONS c cs)`;;

(* read_while_thm *)
let panLexer_read_while_thm = prove
 (`!P input s s' rest.
      panLexer_read_while P input s = (s',rest) ==> LENGTH rest <= LENGTH
        input`,
  CHEAT_TAC);;

let panLexer_next_loc_def = new_definition
  `panLexer_next_loc n x =
   match x with
     POSN r c -> POSN r (c + n)
   | x -> x`;;

let panLexer_next_line_def = new_definition
  `panLexer_next_line x =
   match x with
     POSN r c -> POSN (r + 1) 0
   | x -> x`;;

let loc_row_def = new_definition
  `loc_row n = POSN n 1`;;

let panLexer_skip_comment_def,panLexer_skip_comment_ind = define_guess
  `(panLexer_skip_comment "" _ _ = NONE) /\
   (panLexer_skip_comment (CONS x xs) loc i =
    (match x with (CHR 10) -> SOME (panLexer_next_line loc,i + 1)
     | _ -> panLexer_skip_comment xs (panLexer_next_loc 1 loc) (i +
         1)))`;;

(* return SOME (loc, i, j) -> i characters in comment, DROP j characters to
   continue parsing (after the closing '*/') at loc *)
let skip_block_comment_def,skip_block_comment_ind = define_guess
  `(skip_block_comment "" _ _ = NONE) /\
   (skip_block_comment [_] _ _ = NONE) /\
   (skip_block_comment (CONS x (CONS y xs)) loc i =
    if (x = (CHR 42) /\ y = (CHR 47)) \/ (x = (CHR 64) /\ y = (CHR 47))
        then
      SOME (panLexer_next_loc 2 loc,i,i + 2)
    else if x = (CHR 10) then
      skip_block_comment (CONS y xs) (panLexer_next_line loc) (i + 1)
    else skip_block_comment (CONS y xs) (panLexer_next_loc 1 loc) (i +
        1))`;;

let panLexer_unhex_alt_def = new_definition
  `panLexer_unhex_alt x = if isHexDigit x then UNHEX x else 0`;;

let panLexer_num_from_dec_string_alt_def = new_definition
  `panLexer_num_from_dec_string_alt = s2n 10 panLexer_unhex_alt`;;

(* the termination relation that HOL4 gives is
     MEASURE (LENGTH o FST)
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 panLexerScript.sml:265-268: the tactic that proves the termination *)
let next_atom_def,next_atom_ind = define_guess
  `(next_atom "" _ = NONE) /\
   (next_atom (CONS c cs) loc =
      if c = (CHR 10) then
        // Skip Newline
        next_atom cs (panLexer_next_line loc)
      else if isSpace c then
        next_atom cs (panLexer_next_loc 1 loc)
      else if isDigit c then
        let (n,cs') = panLexer_read_while isDigit cs [c] in
          SOME (NumberA (&(panLexer_num_from_dec_string_alt n)),
                Locs loc (panLexer_next_loc (LENGTH n) loc),
                cs')
      else if c = (CHR 45) /\ ~(cs = "") /\ isDigit (HD cs) then
        let (n,rest) = panLexer_read_while isDigit cs [] in
        SOME (NumberA ((&0) - &(panLexer_num_from_dec_string_alt n)),
              Locs loc (panLexer_next_loc (LENGTH n) loc),
              rest)
      else if isPREFIX "//" (CONS c cs) then
        (
         // comment
         match (panLexer_skip_comment (TL cs) (panLexer_next_loc 2 loc) 0)
             with NONE -> SOME (ErrA (implode "Malformed comment"),Locs loc
             (panLexer_next_loc 2 loc),"")
         | SOME (loc',len) -> next_atom (DROP (len + 1) cs) loc')
      else if isPREFIX "/@" (CONS c cs) then
        (
         // annotation block comment
         match (skip_block_comment (TL cs) (panLexer_next_loc 3 loc) 0)
             with NONE -> SOME (ErrA (implode "Malformed comment"),Locs loc
             (panLexer_next_loc 3 loc),"")
         | SOME (loc',i,len) -> SOME (AnnotCommentA (TAKE i (TL cs)),
              Locs loc loc',DROP (len + 1) cs))
      else if isPREFIX "/*" (CONS c cs) then
        (
         // block comment
         match (skip_block_comment (TL cs) (panLexer_next_loc 2 loc) 0)
             with NONE -> SOME (ErrA (implode "Malformed comment"),Locs loc
             (panLexer_next_loc 2 loc),"")
         | SOME (loc',_,len) -> next_atom (DROP (len + 1) cs) loc')
      else if isAtom_singleton c then
        SOME (SymA (CONS c []),Locs loc loc,cs)
      else if isAtom_begin_group c then
        let (n,rest) = panLexer_read_while isAtom_in_group cs [c] in
        SOME (SymA n,Locs loc (panLexer_next_loc (LENGTH n - 1) loc),rest)
      else if isAlpha c \/ c = (CHR 64) \/ c = (CHR 95) then
        // read identifier
        let (n,rest) = panLexer_read_while isAlphaNumOrWild cs [c] in
        SOME (WordA n,Locs loc (panLexer_next_loc (LENGTH n) loc),rest)
      else
        // input not recognised
        SOME (ErrA (mlstring_concat [(implode
            "Unrecognised symbol: "); integer_word_toString c]),Locs loc
            loc,cs))`;;

let next_atom_LESS = prove
 (`!input l s l' rest.
     next_atom input l = SOME (s,l',rest) ==> LENGTH rest < LENGTH input`,
  CHEAT_TAC);;

let panLexer_next_token_def = new_definition
  `panLexer_next_token input loc =
   match next_atom input loc with NONE -> NONE
    | SOME (atom,locs,rest) ->
        SOME (token_of_atom atom,locs,rest)`;;

(* next_token_LESS *)
let panLexer_next_token_LESS = prove
 (`!s l l' rest input. (panLexer_next_token input l = SOME (s,l',rest)) ==>
                              LENGTH rest < LENGTH input`,
  CHEAT_TAC);;

let panLexer_init_loc_def = new_definition
  `panLexer_init_loc = POSN 1 1`;;

(* the termination relation that HOL4 gives is
     MEASURE (LENGTH o FST)
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 panLexerScript.sml:309-312: the tactic that proves the termination *)
let pancake_lex_aux_def,pancake_lex_aux_ind = define_guess
  `pancake_lex_aux input loc =
   (match panLexer_next_token input loc with NONE -> []
    | SOME (token,Locs locB locE,rest) -> CONS (token,Locs locB locE)
      (pancake_lex_aux rest locE))`;;

let pancake_lex_def = new_definition
  `pancake_lex input = pancake_lex_aux input panLexer_init_loc`;;

let safe_pancake_lex_def = new_definition
  `safe_pancake_lex input =
   (let output = pancake_lex input in
       match FILTER (isLexErrorT o FST) output with
         [] -> INL output
       | xs -> INR (MAP ((the (implode "") o destLexErrorT) ## I) xs))`;;

(* Tests :
   EVAL ``pancake_lex "x + 1 --Then check y\n && y - 2 <= -3 || !z"``;
*)

(* and the interface *)
let _ = unhide_overloads ();;
