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

let strip_sxcons_def = cake_define
  `strip_sxcons s =
     (match s with
         SX_CONS h t -> OPTION_MAP (CONS h) (strip_sxcons t) |
           SX_SYM s -> (if s = "nil" then SOME [] else NONE) | _1 ->
           NONE)`;;

let dstrip_sexp_def = cake_define
  `dstrip_sexp x1 =
        match x1 with
          SX_CONS sym args ->
        (match sym with
            SX_SYM s -> OPTION_MAP (\t. (s,t)) (strip_sxcons args) |
              _2 -> NONE)
        | _3 -> NONE`;;

hol4_only "++" "APPEND";;
