(* ======================================================== *)
(*  simpleSexpParse: ported from HOL4's
    examples/formal-languages/context-free/simpleSexpParseScript.sml
    A HOL4 library theory, of which the port has the definitions
    that CakeML needs.  Needed by cmlPEG.ml, cmlParse.ml and
    compiler.ml.  *)
(* ======================================================== *)

needs "lib/ASCIInumbers.ml";;
needs "lib/peg.ml";;
needs "lib/pegexec.ml";;
needs "lib/simpleSexp.ml";;
needs "lib/simpleSexpPEG.ml";;

(* this file is of no theory of the port: the overloads it
   registers are in the scope of every file *)
let _ = hol4_lib ();;
(* HOL4 ancestors outside the port: list pair string *)

let parse_sexp_def = new_definition
  `parse_sexp s =
     OPTION_BIND (pegparse sexpPEG s)
       (\(rest,sx). OPTION_IGNORE_BIND (OPTION_GUARD (rest = []))
         (SOME (FST sx)))`;;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let escape_string_def,escape_string_ind = define_wf
  `MEASURE (\x0. list_size char_size x0)`
  [`escape_string s =
     (match s with "" -> "" | CONS (CHR 92) s -> APPEND "\\\\"
       (escape_string s) | CONS (CHR 34) s -> APPEND "\\\""
       (escape_string s) | CONS c s -> CONS c (escape_string s))`];;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let print_space_separated_def,print_space_separated_ind = define_wf
  `MEASURE (\x0. list_size (list_size char_size) x0)`
  [`print_space_separated x1 =
        match x1 with
          [] -> ""
        | [x] -> x
        | (CONS x xs) -> APPEND (APPEND x " ")
          (print_space_separated xs)`];;

let strip_dot_def,strip_dot_ind = define_rec
  [`strip_dot (SX_NUM n) = ([],SOME (SX_NUM n))`;
   `strip_dot (SX_STR s) = ([],SOME (SX_STR s))`;
   `strip_dot (SX_SYM s) =
      (if s = "nil" then ([],NONE) else ([],SOME (SX_SYM s)))`;
   `strip_dot (SX_CONS a d) = (let (ls,n) = strip_dot d in (CONS a
  ls,n))`];;

(* the termination relation that HOL4 gives is
     MEASURE simpleSexp_sexp_size
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 simpleSexpParseScript.sml:260-268: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let print_sexp_def,print_sexp_ind = define_guess_cheat
  [`print_sexp s =
        match s with
          SX_SYM s -> s
        | (SX_NUM n) -> num_to_dec_string n
        | (SX_STR s) -> APPEND (APPEND "\"" (escape_string s)) "\""
        | s ->
      (let (ls,n) = strip_dot s in
      match n with NONE ->
        (if LENGTH ls = 2 /\ HD ls = SX_SYM "quote" then APPEND "'"
          (print_sexp (EL 1 ls)) else APPEND (APPEND "("
          (print_space_separated (MAP print_sexp ls))) ")") | SOME last
          -> APPEND (APPEND (APPEND (APPEND "(" (print_space_separated
          (MAP print_sexp ls))) " . ")
          (print_sexp last)) ")")`];;
