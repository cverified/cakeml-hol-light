(* ======================================================== *)
(*  simpleSexp: ported from HOL4's
    examples/formal-languages/context-free/simpleSexpScript.sml
    A HOL4 library theory, of which the port has the definitions
    that CakeML needs.  Needed by bvi_tailrec.ml, data_to_word.ml,
    fromSexp.ml, simpleSexpPEG.ml and simpleSexpParse.ml.  *)
(* ======================================================== *)

needs "lib/peg.ml";;
(* HOL4 ancestors outside the port: string *)

hol4_overload "++" "OPTION_CHOICE";;

let simpleSexp_sexp_INDUCT,simpleSexp_sexp_RECURSION = define_datatype
  "simpleSexp_sexp = SX_CONS (simpleSexp_sexp) (simpleSexp_sexp) | \
   SX_SYM (string) | SX_NUM (num) | SX_STR (string)";;

hol4_numeral_form "SX_NUM";;
(* HOL4 simpleSexpScript.sml:23-34: the overload nil, which the port
   expands *)

let valid_first_symchar_def = cake_define
  `valid_first_symchar c <=>
     isGraph c /\ ~(c IN {(CHR 39),(CHR 40),(CHR 41),(CHR 46),(CHR
       34)}) /\ ~(isDigit c)`;;

let valid_symchar_def = cake_define
  `valid_symchar c <=> isGraph c /\ ~(c IN {(CHR 39),(CHR 40),(CHR
  41)})`;;

let valid_symbol_def = cake_define_list
  [`valid_symbol "" <=> F`;
   `valid_symbol (c :: cs) <=> valid_first_symchar c /\ EVERY
  valid_symchar cs`];;

let valid_sexp_def = cake_define
  `valid_sexp s =
        match s with
          SX_SYM s -> valid_symbol s
        | (SX_CONS s1 s2) -> valid_sexp s1 /\ valid_sexp s2
        | (SX_STR s) -> EVERY isPrint s
        | s -> T`;;

let arb_sexp_def = cake_define
  `arb_sexp = SX_NUM 0`;;

let destSXNUM_def = cake_define
  `destSXNUM x1 =
      match x1 with
        SX_NUM n -> n
      | _1 -> 0`;;

let destSXSYM_def = cake_define
  `destSXSYM x1 =
      match x1 with
        SX_SYM s -> s
      | _2 -> ""`;;

let destSXCONS_def = cake_define
  `destSXCONS x1 =
      match x1 with
        SX_CONS a d -> (a,d)
      | _3 -> (arb_sexp,arb_sexp)`;;

let strip_sxcons_def = cake_define
  `strip_sxcons s =
     (match s with
         SX_CONS h t -> OPTION_MAP (CONS h) (strip_sxcons t) |
           SX_SYM s -> (if s = "nil" then SOME [] else NONE) | _4 ->
           NONE)`;;

let sxMEM_def = cake_define
  `sxMEM e s <=> (?l. strip_sxcons s = SOME l /\ MEM e l)`;;

let dstrip_sexp_def = cake_define
  `dstrip_sexp x1 =
        match x1 with
          SX_CONS sym args ->
        (match sym with
            SX_SYM s -> OPTION_MAP (\t. (s,t)) (strip_sxcons args) |
              _5 -> NONE)
        | _6 -> NONE`;;


(* HOL4 makes the datatype of the nonterminals and the
   grammar itself with the ML code of grammarLib
   (mk_grammar_def); the port writes out what it makes *)

let sexpNT_INDUCT,sexpNT_RECURSION = define_datatype
  "sexpNT = sxnt_symchars | sxnt_symchar | sxnt_strcontents | \
   sxnt_strchar | sxnt_sexpsym | sxnt_sexpstr | sxnt_sexpseq | \
   sxnt_sexpnum | sxnt_sexp0 | sxnt_sexp | sxnt_normstrchar | \
   sxnt_grabWS | sxnt_first_symchar | sxnt_escapedstrchar | \
   sxnt_escapablechar | sxnt_digit | sxnt_WSsexp | sxnt_WS";;

let sexpG_def = cake_define
  `sexpG = mk_grammar (INL sxnt_sexp) (FEMPTY |+ (INL
  sxnt_sexp,{[grammar_NT (INL sxnt_WSsexp); grammar_NT (INL
  sxnt_grabWS)]}) |+ (INL sxnt_WSsexp,{[grammar_NT (INL sxnt_grabWS);
  grammar_NT (INL sxnt_sexp0)]}) |+ (INL sxnt_grabWS,({[grammar_NT
  (INL sxnt_WS); grammar_NT (INL sxnt_grabWS)]} UNION {[]})) |+ (INL
  sxnt_WS,{[grammar_TOK (c)] | isSpace c}) |+ (INL
  sxnt_sexp0,((((({[grammar_NT (INL sxnt_sexpsym)]} UNION
  {[grammar_NT (INL sxnt_sexpnum)]}) UNION {[grammar_NT (INL
  sxnt_sexpstr)]}) UNION {[grammar_TOK ((CHR 40)); grammar_NT (INL
  sxnt_sexpseq); grammar_NT (INL sxnt_grabWS); grammar_TOK ((CHR
  41))]}) UNION {[grammar_TOK ((CHR 40)); grammar_NT (INL sxnt_sexp);
  grammar_TOK ((CHR 46)); grammar_NT (INL sxnt_sexp); grammar_TOK
  ((CHR 41))]}) UNION {[grammar_TOK ((CHR 39)); grammar_NT (INL
  sxnt_WSsexp)]})) |+ (INL sxnt_sexpseq,({[grammar_NT (INL
  sxnt_WSsexp); grammar_NT (INL sxnt_sexpseq)]} UNION {[]})) |+ (INL
  sxnt_sexpnum,({[grammar_NT (INL sxnt_sexpnum); grammar_NT (INL
  sxnt_digit)]} UNION {[grammar_NT (INL sxnt_digit)]})) |+ (INL
  sxnt_digit,{[grammar_TOK (c)] | isDigit c}) |+ (INL
  sxnt_sexpstr,{[grammar_TOK ((CHR 34)); grammar_NT (INL
  sxnt_strcontents); grammar_TOK ((CHR 34))]}) |+ (INL
  sxnt_strcontents,({[]} UNION {[grammar_NT (INL sxnt_strchar);
  grammar_NT (INL sxnt_strcontents)]})) |+ (INL
  sxnt_strchar,({[grammar_NT (INL sxnt_normstrchar)]} UNION
  {[grammar_NT (INL sxnt_escapedstrchar)]})) |+ (INL
  sxnt_normstrchar,{[grammar_TOK (c)] | isPrint c /\ ~(c = (CHR 92))
  /\ ~(c = (CHR 34))}) |+ (INL sxnt_escapedstrchar,{[grammar_TOK
  ((CHR 92)); grammar_NT (INL sxnt_escapablechar)]}) |+ (INL
  sxnt_escapablechar,({[grammar_TOK ((CHR 92))]} UNION {[grammar_TOK
  ((CHR 34))]})) |+ (INL sxnt_sexpsym,{[grammar_NT (INL
  sxnt_first_symchar); grammar_NT (INL sxnt_symchars)]}) |+ (INL
  sxnt_first_symchar,{[grammar_TOK (c)] | valid_first_symchar c}) |+
  (INL sxnt_symchars,({[grammar_NT (INL sxnt_symchar); grammar_NT
  (INL sxnt_symchars)]} UNION {[]})) |+ (INL
  sxnt_symchar,{[grammar_TOK (c)] | valid_symchar c}))`;;

hol4_only "++" "APPEND";;
