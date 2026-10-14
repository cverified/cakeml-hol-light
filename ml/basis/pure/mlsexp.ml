(* ======================================================== *)
(*  mlsexp: ported from HOL4's
    basis/pure/mlsexpScript.sml  *)
(* ======================================================== *)

(*
  Definition of a simple mlstring-based s-expression, includes
  parsing and pretty printing for these s-expressions.
*)

needs "basis/pure/mlstring.ml";;
needs "misc/misc.ml";;
needs "semantics/semanticPrimitives.ml";;

(*--------------------------------------------------------------*
   Definition of s-expression
 *--------------------------------------------------------------*)

let sexp_INDUCT,sexp_RECURSION = define_datatype
  "sexp = Atom (mlstring) | Expr (sexp list)";;

(*--------------------------------------------------------------*
   Lexing + parsing
 *--------------------------------------------------------------*)

let mlsexp_token_INDUCT,mlsexp_token_RECURSION = define_datatype
  "mlsexp_token = OPEN | CLOSE | SYMBOL (mlstring)";;

(* Functions may not consume the entire input (string), so they always
   return
   the rest of the string, independent of success or failure. *)
(* HOL4 type abbreviation (expanded in the port):
     result = (α # string) + (β # string) *)

let read_string_aux_def = cake_define
  `read_string_aux [] acc =
     INL ((strlit "read_string_aux: unterminated string literal"),[])
       /\
   read_string_aux (c :: rest) acc =
     (if c = (CHR 34) then INR (implode (REVERSE acc),rest) else
     if c = (CHR 92) then
       (match rest with [] -> read_string_aux rest acc | (e :: rest)
         ->
            (if e = (CHR 92) then read_string_aux rest ((CHR 92) ::
              acc) else
             if e = (CHR 34) then read_string_aux rest ((CHR 34) ::
               acc) else
             if e = (CHR 48) then read_string_aux rest ((CHR 0) ::
               acc) else
             if e = (CHR 110) then read_string_aux rest ((CHR 10) ::
               acc) else
             if e = (CHR 114) then read_string_aux rest ((CHR 13) ::
               acc) else
             if e = (CHR 116) then read_string_aux rest ((CHR 9) ::
               acc) else
               INL ((strlit
                 "read_string_aux: unrecognised escape"),rest))) else
       read_string_aux rest (c :: acc))`;;

(* Returns the string until a closing quote, and the rest of the input.
   Fails with an error message if closing quotes are missing or an
   unrecognised escape sequence occurs. *)
let read_string_def = cake_define
  `(mlsexp_read_string (input:string):mlstring#string+mlstring#string) =
     read_string_aux input []`;;

(* Returns the string until a closing parenthesis or whitespace, and the
   rest of the input.

   See usage in lex_aux as to why a "non-aux function" is exposing an
   accumulator. *)
let read_symbol_def = cake_define
  `read_symbol [] acc =
     (implode (REVERSE acc),[]) /\
   read_symbol (c :: cs) acc =
     (if c = (CHR 41) \/ isSpace c then (implode (REVERSE acc),(c
       :: cs)) else read_symbol cs (c :: acc))`;;

(* By tracking the depth, we can ensure we only lex one S-expression at
   a
   time. *)
(* TERMINATION: wf_rel_tac ‘measure $ (λ(_, input, _). LENGTH input)’ \\
   rw[]
  \\ imp_res_tac read_string_length \\ fs[]
  \\ fs[Once read_symbol_def]
  \\ gvs [AllCaseEqs()]
  \\ imp_res_tac read_symbol_length \\ fs[] *)
let lex_aux_def = cake_define
  `(mlsexp_lex_aux depth [] acc:mlstring#string+mlsexp_token
  list#string) =
     (if depth = (0:num) then INR (acc,[]) else INL ((strlit
       "lex_aux: missing closing parenthesis"),[])) /\
   mlsexp_lex_aux depth (c :: cs) acc =
     (if isSpace c then mlsexp_lex_aux depth cs acc else if c = (CHR
       40) then mlsexp_lex_aux (depth + 1) cs (OPEN :: acc) else if c =
       (CHR 41) then
       (if depth = 0 then INL ((strlit
         "lex_aux: too many closing parenthesis"),cs) else if depth = 1
         then INR (CLOSE :: acc,cs) else mlsexp_lex_aux (depth - 1) cs
         (CLOSE :: acc)) else if c = (CHR 34) then
       match mlsexp_read_string cs with INL (msg,rest) -> INL
         (msg,rest) | INR (s,rest) ->
           (if depth = 0 then INR ([SYMBOL s],rest) else
             mlsexp_lex_aux depth rest ((SYMBOL s) :: acc)) else
       match read_symbol cs [c] with (s,rest) ->
           (if depth = 0 then INR ([SYMBOL s],rest) else
             mlsexp_lex_aux depth rest ((SYMBOL s) :: acc)))`;;

(* Tokenizes (at most) one S-expression, and returns the rest of the
   input.
   Fails with an error message if parentheses are unbalanced or
   read_string fails on a string literal. *)
let lex_def = cake_define
  `(lex (input:string):mlstring#string+mlsexp_token list#string) =
     mlsexp_lex_aux 0 input []`;;

let parse_aux_def = cake_define
  `parse_aux [] xs s = xs /\
   parse_aux (CLOSE :: rest) xs s = parse_aux rest [] (xs :: s) /\
   parse_aux (OPEN :: rest) xs s =
     (match s with [] -> parse_aux rest xs s | (y :: ys) -> parse_aux
       rest ((Expr xs) :: y) ys) /\
   parse_aux ((SYMBOL sy) :: rest) xs s = parse_aux rest ((Atom
     sy) :: xs) s`;;

(* Parses (at most) one S-expression, and returns the rest of the input.
   Fails exactly when lexing fails. *)
let parse_def = cake_define
  `(mlsexp_parse (input:string):mlstring#string+sexp#string) =
     (match lex input with INL (msg,rest) -> INL (msg,rest) | INR
       (rev_toks,rest) ->
         (match parse_aux rev_toks [] [] with [] -> INL ((strlit
           "parse: empty input"),rest) | (v :: _1) -> INR (v,rest)))`;;

(* Function for parsing in the style of the Standard ML basis library.
   *)
let fromString_def = cake_define
  `(mlsexp_fromString (input:mlstring):sexp option) =
     (match mlsexp_parse (explode input) with INL _2 -> NONE | INR
       (se,_3) -> SOME se)`;;

(*--------------------------------------------------------------*
   Pretty printing of str_tree
 *--------------------------------------------------------------*)

let str_tree_INDUCT,str_tree_RECURSION = define_datatype
  "str_tree = mlsexp_Str (mlstring) | mlsexp_Trees (str_tree list) | \
   mlsexp_GrabLine (str_tree)";;

let pretty_INDUCT,pretty_RECURSION = define_datatype
  "pretty = mlsexp_Parenthesis (pretty) | mlsexp_String (mlstring) | \
   mlsexp_Append (pretty) (bool) (pretty) | mlsexp_Size (num) \
   (pretty)";;

let newlines_def = cake_define
  `newlines x1 =
      match x1 with
        [] -> mlsexp_String (strlit "")
      | [x] -> x
      | (x :: xs) -> mlsexp_Append x T (newlines xs)`;;

let v2pretty_def = cake_define
  `v2pretty v =
        match  with
           ->
        match v with mlsexp_Str s -> mlsexp_String s |
          mlsexp_GrabLine w -> mlsexp_Size 100000 (v2pretty w) |
          mlsexp_Trees l -> mlsexp_Parenthesis (newlines (vs2pretty l))
        |  ->
        match v with [] -> [] | (v :: v) -> v2pretty v ::
          vs2pretty v`;;

let get_size_def = cake_define
  `mlsexp_get_size x1 =
      match x1 with
        (mlsexp_Size n x) -> n
      | (mlsexp_Append x _4 y) -> mlsexp_get_size x + mlsexp_get_size
        y + 1
      | (mlsexp_Parenthesis x) -> mlsexp_get_size x + 2
      | _5 -> 0`;;

let get_next_size_def = cake_define
  `get_next_size x1 =
      match x1 with
        (mlsexp_Size n x) -> n
      | (mlsexp_Append x _6 y) -> get_next_size x
      | (mlsexp_Parenthesis x) -> get_next_size x + 2
      | _7 -> 0`;;

let annotate_def = cake_define
  `mlsexp_annotate (mlsexp_String s) = mlsexp_Size (strlen s)
  (mlsexp_String s) /\
   mlsexp_annotate (mlsexp_Parenthesis b) =
     (let b = mlsexp_annotate b in
        mlsexp_Size (mlsexp_get_size b + 2) (mlsexp_Parenthesis b))
          /\
   mlsexp_annotate (mlsexp_Append b1 n b2) =
     (let b1 = mlsexp_annotate b1 in
      let b2 = mlsexp_annotate b2 in
         (mlsexp_Append b1 n b2)) /\
   mlsexp_annotate (mlsexp_Size n b) = mlsexp_Size n
     (mlsexp_annotate b)`;;

let remove_all_def = cake_define
  `remove_all (mlsexp_Parenthesis v) = mlsexp_Parenthesis (remove_all v)
  /\
   remove_all (mlsexp_String v1) = mlsexp_String v1 /\
   remove_all (mlsexp_Append v2 _8 v3) = mlsexp_Append (remove_all
     v2) F (remove_all v3) /\
   remove_all (mlsexp_Size v4 v5) = remove_all v5`;;

let smart_remove_def = cake_define
  `smart_remove i k (mlsexp_Size n b) =
     (if k + n < 70 then remove_all b else smart_remove i k b) /\
   smart_remove i k (mlsexp_Parenthesis v) = mlsexp_Parenthesis
     (smart_remove (i + 1) (k + 1) v) /\
   smart_remove i k (mlsexp_String v1) = mlsexp_String v1 /\
   smart_remove i k (mlsexp_Append v2 b v3) =
     (let n2 = mlsexp_get_size v2 in
     let n3 = get_next_size v3 in
       if k + n2 + n3 < 50 then
         mlsexp_Append (smart_remove i k v2) F (smart_remove i (k +
           n2) v3) else
         mlsexp_Append (smart_remove i k v2) T (smart_remove i i
           v3))`;;

let flatten_def = cake_define
  `flatten indent (mlsexp_Size n p) s = flatten indent p s /\
   flatten indent (mlsexp_Parenthesis p) s =
     (strlit "(") :: flatten (mlstring_concat [indent; (strlit
       "   ")]) p ((strlit ")") :: s) /\
   flatten indent (mlsexp_String t) s = t :: s /\
   flatten indent (mlsexp_Append p1 b p2) s =
     flatten indent p1 ((if b then indent else (strlit " ")) ::
       flatten indent p2 s)`;;

let str_tree_to_strs_def = cake_define
  `str_tree_to_strs end v = flatten (strlit "\n") (smart_remove 0 0
  (mlsexp_annotate (v2pretty v))) [end]`;;

(*--------------------------------------------------------------*
   Pretty printing of sexp
 *--------------------------------------------------------------*)

let is_safe_char_def = cake_define
  `is_safe_char c <=> ~MEM c "()\"\000" /\ ~isSpace c`;;

let str_every_def = cake_define
  `str_every p n s =
     (if n = 0 then T else
       p (strsub s (n - 1)) /\ str_every p (n - (1:num)) s)`;;

let make_str_safe_def = cake_define
  `make_str_safe s =
     (if s = (strlit "") then (implode) "\"\"" else
     if str_every is_safe_char (strlen s) s then s else escape_str
       s)`;;

let sexp2tree_def = cake_define
  `sexp2tree (Atom s) = mlsexp_Str (make_str_safe s) /\
   sexp2tree (Expr l) = mlsexp_Trees (sexp2trees l) /\
   sexp2trees [] = [] /\
   sexp2trees (v :: vs) = sexp2tree v :: sexp2trees vs`;;

let sexp_to_app_list_def = cake_define
  `sexp_to_app_list (Atom s) = misc_List [make_str_safe s] /\
   sexp_to_app_list (Expr l) =
     mlsexp_Append (misc_List [(strlit "(")])
            (mlsexp_Append (sexps_to_app_list l) (misc_List [(strlit
              ")")])) /\
   sexps_to_app_list [] = misc_List [] /\
   sexps_to_app_list (v :: vs) =
     (if NULL vs then sexp_to_app_list v else mlsexp_Append
       (sexp_to_app_list v)
                 (mlsexp_Append (misc_List [(strlit " ")])
                   (sexps_to_app_list vs)))`;;

let sexp_to_string_def = cake_define
  `sexp_to_string s = mlstring_concat (append (sexp_to_app_list s))`;;

let sexp_to_pretty_string_def = cake_define
  `sexp_to_pretty_string s = mlstring_concat (str_tree_to_strs
  (strlit "\n") (sexp2tree s))`;;

(*--------------------------------------------------------------*
   Proofs relating parsing with pretty prniting
 *--------------------------------------------------------------*)

let to_tokens_def = cake_define
  `to_tokens (Atom a) = [SYMBOL a] /\
   to_tokens (Expr xs) = [OPEN] ++ FLAT (MAP (\x. to_tokens x) xs)
     ++ [CLOSE]`;;
