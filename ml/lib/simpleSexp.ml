(* ======================================================== *)
(*  simpleSexp: ported from HOL4's
    examples/formal-languages/context-free/simpleSexpScript.sml  *)
(*  Of this HOL4 library theory only the definitions that the
    CakeML port needs are ported.  *)
(* ======================================================== *)

needs "lib/peg.ml";;
(* HOL4 ancestors outside the port: string *)

hol4_overload "++" "OPTION_CHOICE";;

let simpleSexp_sexp_INDUCT,simpleSexp_sexp_RECURSION = define_datatype
  "simpleSexp_sexp = SX_CONS (simpleSexp_sexp) (simpleSexp_sexp) | \
   SX_SYM (string) | SX_NUM (num) | SX_STR (string)";;
(* HOL4 overload (expanded in the port):
     nil = SX_SYM "nil" *)

let valid_first_symchar_def = cake_define
  `valid_first_symchar c <=>
     isGraph c /\ ~(c IN {(CHR 39),(CHR 40),(CHR 41),(CHR 46),(CHR
       34)}) /\ ~isDigit c`;;

let valid_symchar_def = cake_define
  `valid_symchar c <=> isGraph c /\ ~(c IN {(CHR 39),(CHR 40),(CHR
  41)})`;;

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

let dstrip_sexp_def = cake_define
  `dstrip_sexp x1 =
        match x1 with
          SX_CONS sym args ->
        (match sym with
            SX_SYM s -> OPTION_MAP (\t. (s,t)) (strip_sxcons args) |
              _5 -> NONE)
        | _6 -> NONE`;;

hol4_only "++" "APPEND";;
