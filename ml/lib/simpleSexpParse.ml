(* ======================================================== *)
(*  simpleSexpParse: ported from HOL4's
    examples/formal-languages/context-free/simpleSexpParseScript.sml  *)
(*  Of this HOL4 library theory only the definitions that the
    CakeML port needs are ported.  *)
(* ======================================================== *)

needs "lib/ASCIInumbers.ml";;
needs "lib/peg.ml";;
needs "lib/pegexec.ml";;
needs "lib/simpleSexp.ml";;
needs "lib/simpleSexpPEG.ml";;
(* HOL4 ancestors outside the port: list pair string *)

let parse_sexp_def = cake_define
  `parse_sexp s =
     OPTION_BIND (pegparse sexpPEG s)
       (\(rest,sx). OPTION_IGNORE_BIND (OPTION_GUARD (rest = []))
         (SOME (FST sx)))`;;

let escape_string_def = cake_define
  `escape_string s =
     (match s with "" -> "" | (CHR 92) :: s -> "\\\\" ++
       escape_string s | (CHR 34) :: s -> "\\\"" ++ escape_string s |
       c :: s -> c :: (escape_string s))`;;

let print_space_separated_def = cake_define
  `print_space_separated x1 =
        match x1 with
          [] -> ""
        | [x] -> x
        | (x :: xs) -> x ++ " " ++ print_space_separated xs`;;

let strip_dot_def = cake_define_list
  [`strip_dot (SX_NUM n) = ([],SOME (SX_NUM n))`;
   `strip_dot (SX_STR s) = ([],SOME (SX_STR s))`;
   `strip_dot (SX_SYM s) =
      (if s = "nil" then ([],NONE) else ([],SOME (SX_SYM s)))`;
   `strip_dot (SX_CONS a d) = (let (ls,n) = strip_dot d in (a ::
  ls,n))`];;

let _ = size_thms "simpleSexp_sexp";;
(* HOL4 simpleSexpParseScript.sml:260-268: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let print_sexp_def = cake_define_try_tac (fun () ->
  `MEASURE simpleSexp_sexp_size`)
  CHEAT_TAC
  `print_sexp s =
        match s with
          SX_SYM s -> s
        | (SX_NUM n) -> num_to_dec_string n
        | (SX_STR s) -> "\"" ++ escape_string s ++ "\""
        | s ->
      (let (ls,n) = strip_dot s in
      match n with NONE ->
        (if LENGTH ls = 2 /\ HD ls = SX_SYM "quote" then "'" ++
          print_sexp (EL 1 ls) else "(" ++ print_space_separated (MAP
          print_sexp ls) ++ ")") | SOME last ->
          "(" ++ print_space_separated (MAP print_sexp ls) ++ " . "
            ++
          print_sexp last ++ ")")`;;
