(* ======================================================== *)
(*  mlsexp: ported from HOL4's
    basis/pure/mlsexpScript.sml
    A definition theory, with 25 definitions, 4 datatypes and 25
    theorems.  Needed by compiler.ml, compilerProof.ml,
    displayLang.ml and presLang.ml.  *)
(* ======================================================== *)

(*
  Definition of a simple mlstring-based s-expression, includes
  parsing and pretty printing for these s-expressions.
*)

needs "basis/pure/mlstring.ml";;
needs "lib/peg.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;

(* the theories whose names the Ancestors blocks of the source
   bring, which are the ones that its statements read: the
   overloads of every other theory come out of the interface
   while this file loads *)
let _ = hol4_ancestors "mlsexp"
  ["mlstring"];;

(*--------------------------------------------------------------*
   Definition of s-expression
 *--------------------------------------------------------------*)

let mlsexp_sexp_INDUCT,mlsexp_sexp_RECURSION = define_datatype
  "mlsexp_sexp = Atom (mlstring) | Expr (mlsexp_sexp list)";;

(*--------------------------------------------------------------*
   Lexing + parsing
 *--------------------------------------------------------------*)

let mlsexp_token_INDUCT,mlsexp_token_RECURSION = define_datatype
  "mlsexp_token = OPEN | CLOSE | SYMBOL (mlstring)";;

(* Functions may not consume the entire input (string), so they always return
   the rest of the string, independent of success or failure. *)
(* HOL4 mlsexpScript.sml:29: the type abbreviation result, which the
   port expands *)

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let read_string_aux_def,read_string_aux_ind = define_wf
  `MEASURE (\(x0,x1). list_size char_size x0)`
  [`read_string_aux [] acc =
      INL ((implode
        "read_string_aux: unterminated string literal"),[])`;
   `read_string_aux (c :: rest) acc =
      (if c = (CHR 34) then INR (implode (REVERSE acc),rest) else
      if c = (CHR 92) then
        (match rest with [] -> read_string_aux rest acc | (
            // causes error: unterminated string
            e :: rest) ->
             (if e = (CHR 92) then read_string_aux rest ((CHR 92) ::
               acc) else
              if e = (CHR 34) then read_string_aux rest ((CHR 34) ::
                acc) else
              if e = (CHR 48) then read_string_aux rest ((CHR 0) ::
                acc) else
              if e = (CHR 110) then read_string_aux rest ((CHR 10)
                :: acc) else
              if e = (CHR 114) then read_string_aux rest ((CHR 13)
                :: acc) else
              if e = (CHR 116) then read_string_aux rest ((CHR 9) ::
                acc) else
                INL ((implode
                  "read_string_aux: unrecognised escape"),rest))) else
        read_string_aux rest (c :: acc))`];;

(* Returns the string until a closing quote, and the rest of the input.
   Fails with an error message if closing quotes are missing or an
   unrecognised escape sequence occurs. *)
let read_string_def = new_definition
  `(mlsexp_read_string (input:string):mlstring#string+mlstring#string) =
     read_string_aux input []`;;
hol4_overload "read_string" "mlsexp_read_string";;

let read_string_aux_length = prove
 (`!input acc.
     read_string_aux input acc = INR (s,rest) ==> LENGTH rest <=
       LENGTH input`,
  CHEAT_TAC);;

let read_string_length = prove
 (`mlsexp_read_string input = INR (s,rest) ==> LENGTH rest <= LENGTH
  input`,
  CHEAT_TAC);;

(* Returns the string until a closing parenthesis or whitespace, and the
   rest of the input.

   See usage in lex_aux as to why a "non-aux function" is exposing an
   accumulator. *)
let read_symbol_def,read_symbol_ind = define_rec
  [`read_symbol [] acc =
      (implode (REVERSE acc),[])`;
   `read_symbol (c :: cs) acc =
      (if c = (CHR 41) \/ isSpace c then (implode (REVERSE
        acc),(c :: cs)) else read_symbol cs (c :: acc))`];;

let read_symbol_length = prove
 (`!input acc.
     read_symbol input acc = (s,rest) ==> LENGTH rest <= LENGTH
       input`,
  CHEAT_TAC);;

(* By tracking the depth, we can ensure we only lex one S-expression at a
   time. *)
(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 mlsexpScript.sml:131-137: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let lex_aux_def,lex_aux_ind = define_wf_cheat
  `MEASURE (\(_1,input,_2). LENGTH input)`
  [`(mlsexp_lex_aux depth [] acc:mlstring#string+mlsexp_token
  list#string) =
      (if depth = (0:num) then INR (acc,[]) else INL ((implode
        "lex_aux: missing closing parenthesis"),[]))`;
   `mlsexp_lex_aux depth (c :: cs) acc =
      (if isSpace c then mlsexp_lex_aux depth cs acc else if c =
        (CHR 40) then mlsexp_lex_aux (depth + 1) cs (OPEN :: acc) else
        if c = (CHR 41) then
        (if depth = 0 then INL ((implode
          "lex_aux: too many closing parenthesis"),cs) else if depth = 1
          then INR (CLOSE :: acc,cs) else mlsexp_lex_aux (depth - 1) cs
          (CLOSE :: acc)) else if c = (CHR 34) then
        match mlsexp_read_string cs with INL (msg,rest) -> INL
          (msg,rest) | INR (s,rest) ->
            (if depth = 0 then INR ([SYMBOL s],rest) else
              mlsexp_lex_aux depth rest ((SYMBOL s) :: acc)) else
        // We know that c is not a closing parenthesis or a space, so read_symbol
        // (c::cs) [] is equivalent to read_symbol cs [c].
        //
        // The choice is an implementation detail relevant in the context of
        // streams: If we interpret the input string as a stream and use the
        // latter version of the call, the case split can be seen as consuming the
        // first character.  If we insist on the former version, the case split
        // can only peek at (not consume) c, and we must add calls to consume c in
        // the other branches.
        match read_symbol cs [c] with (s,rest) ->
            (if depth = 0 then INR ([SYMBOL s],rest) else
              mlsexp_lex_aux depth rest ((SYMBOL s) :: acc)))`];;
hol4_overload "lex_aux" "mlsexp_lex_aux";;

let lex_aux_length = prove
 (`!depth input acc e rest.
     mlsexp_lex_aux depth input acc = INR (e,rest) ==> LENGTH rest
       <= LENGTH input`,
  CHEAT_TAC);;

(* Tokenizes (at most) one S-expression, and returns the rest of the input.
   Fails with an error message if parentheses are unbalanced or
   read_string fails on a string literal. *)
let lex_def = new_definition
  `(lex (input:string):mlstring#string+mlsexp_token list#string) =
     mlsexp_lex_aux 0 input []`;;

let lex_IMP_LENGTH_LESS = prove
 (`!input x rest. lex input = INR (x,rest) ==> LENGTH rest < LENGTH
  input \/ x = []`,
  CHEAT_TAC);;

(* [local] *)
let test_lex = prove
 (`lex " 1 2   3 " = INR ([SYMBOL (implode "1")]," 2   3 ") /\
   lex "\"\n \" 2" = INR ([SYMBOL (implode "\n ")]," 2") /\
   lex " (1 2) 3 " = INR ([CLOSE; SYMBOL (implode "2"); SYMBOL
     (implode "1"); OPEN]," 3 ") /\
   lex " (1 2) ) " = INR ([CLOSE; SYMBOL (implode "2"); SYMBOL
     (implode "1"); OPEN]," ) ") /\
   lex " (1 2    " = INL ((implode
     "lex_aux: missing closing parenthesis"),"") /\
   lex " ) (1 2) " = INL ((implode
     "lex_aux: too many closing parenthesis")," (1 2) ")`,
  CHEAT_TAC);;

let _ = size_thms "mlsexp_token";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let parse_aux_def,parse_aux_ind = define_wf
  `MEASURE (\(x0,x1,x2). list_size mlsexp_token_size x0)`
  [`parse_aux [] xs s = xs`;
   `parse_aux (CLOSE :: rest) xs s = parse_aux rest [] (xs :: s)`;
   `parse_aux (OPEN :: rest) xs s =
      (match s with [] -> parse_aux rest xs s | (y :: ys) ->
        parse_aux rest ((Expr xs) :: y) ys)`;
   `parse_aux (SYMBOL sy :: rest) xs s = parse_aux rest ((Atom sy)
  :: xs) s`];;

(* Parses (at most) one S-expression, and returns the rest of the input.
   Fails exactly when lexing fails. *)
let parse_def = new_definition
  `(mlsexp_parse (input:string):mlstring#string+mlsexp_sexp#string) =
     (match lex input with INL (msg,rest) -> INL (msg,rest) | INR
       (rev_toks,rest) ->
         (match parse_aux rev_toks [] [] with [] -> INL ((implode
           "parse: empty input"),rest) | (v :: _3) -> INR (v,rest)))`;;
hol4_overload "parse" "mlsexp_parse";;

let parse_IMP_LENGTH_LESS = prove
 (`!input x rest. mlsexp_parse input = INR (x,rest) ==> LENGTH rest <
  LENGTH input`,
  CHEAT_TAC);;

let parse_space = prove
 (`mlsexp_parse ((CHR 10) :: xs) = mlsexp_parse xs`,
  CHEAT_TAC);;

(* [local] *)
let test_parse = prove
 (`mlsexp_parse " 1 2 3 " = INR (Atom (implode "1")," 2 3 ") /\
   mlsexp_parse "(1 2 3)" = INR (Expr [Atom (implode "1"); Atom
     (implode "2"); Atom (implode "3")],"") /\
   mlsexp_parse "(()) ()" = INR (Expr [Expr []]," ()")`,
  CHEAT_TAC);;

(* Function for parsing in the style of the Standard ML basis library. *)
let mlsexp_fromString_def = new_definition
  `(mlsexp_fromString (input:mlstring):mlsexp_sexp option) =
     (match mlsexp_parse (explode input) with INL _4 -> NONE | INR
       (se,_5) -> SOME se)`;;
hol4_overload "fromString" "mlsexp_fromString";;

(*--------------------------------------------------------------*
   Pretty printing of str_tree
 *--------------------------------------------------------------*)

let str_tree_INDUCT,str_tree_RECURSION = define_datatype
  "str_tree = mlsexp_Str (mlstring) | mlsexp_Trees (str_tree list) | \
   mlsexp_GrabLine (str_tree)";;
hol4_overload "Str" "mlsexp_Str";;
hol4_overload "Trees" "mlsexp_Trees";;
hol4_overload "GrabLine" "mlsexp_GrabLine";;

let pretty_INDUCT,pretty_RECURSION = define_datatype
  "pretty = mlsexp_Parenthesis (pretty) | mlsexp_String (mlstring) | \
   mlsexp_Append (pretty) (bool) (pretty) | mlsexp_Size (num) \
   (pretty)";;
hol4_overload "Parenthesis" "mlsexp_Parenthesis";;
hol4_overload "String" "mlsexp_String";;
hol4_overload "Append" "mlsexp_Append";;
hol4_overload "Size" "mlsexp_Size";;

let _ = size_thms "pretty";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let newlines_def,newlines_ind = define_wf
  `MEASURE (\x0. list_size pretty_size x0)`
  [`newlines x1 =
      match x1 with
        [] -> mlsexp_String (implode "")
      | [x] -> x
      | (x :: xs) -> Append x T (newlines xs)`];;

let _ = size_thms "str_tree";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let v2pretty_def = define_mutual_wf
  `MEASURE (sum_measure (\x0. str_tree_size x0) (\x0. str_tree_size1
  x0))`
  [`v2pretty v =
         (match v with mlsexp_Str s -> mlsexp_String s |
           mlsexp_GrabLine w -> mlsexp_Size 100000 (v2pretty w) |
           mlsexp_Trees l -> mlsexp_Parenthesis (newlines (vs2pretty
           l)))`;
   `vs2pretty vs =
         (match vs with [] -> [] | (v :: vs) -> v2pretty v ::
           vs2pretty vs)`];;

let mlsexp_get_size_def,mlsexp_get_size_ind = define_shaped_rec
  "match"
  [`mlsexp_get_size x1 =
      match x1 with
        mlsexp_Size n x -> n
      | (Append x _6 y) -> mlsexp_get_size x + mlsexp_get_size y + 1
      | (mlsexp_Parenthesis x) -> mlsexp_get_size x + 2
      | _7 -> 0`];;
hol4_overload "get_size" "mlsexp_get_size";;

let get_next_size_def,get_next_size_ind = define_shaped_rec
  "match"
  [`get_next_size x1 =
      match x1 with
        mlsexp_Size n x -> n
      | (Append x _8 y) -> get_next_size x
      | (mlsexp_Parenthesis x) -> get_next_size x + 2
      | _9 -> 0`];;

let mlsexp_annotate_def,mlsexp_annotate_ind = define_rec
  [`mlsexp_annotate (mlsexp_String s:pretty) = mlsexp_Size (strlen s)
  (mlsexp_String s)`;
   `mlsexp_annotate (mlsexp_Parenthesis b) =
      (let b = mlsexp_annotate b in
         mlsexp_Size (mlsexp_get_size b + 2) (mlsexp_Parenthesis
           b))`;
   `mlsexp_annotate (Append b1 n b2:pretty) =
      (let b1 = mlsexp_annotate b1 in
       let b2 = mlsexp_annotate b2 in
          (
           // Size (get_size b1 + get_size b2 + 1)
           Append b1 n b2))`;
   `mlsexp_annotate (mlsexp_Size n b) = mlsexp_Size n
  (mlsexp_annotate b)`];;
hol4_overload "annotate" "mlsexp_annotate";;

let remove_all_def,remove_all_ind = define_rec
  [`remove_all (mlsexp_Parenthesis v) = mlsexp_Parenthesis
  (remove_all v)`;
   `remove_all (mlsexp_String v1:pretty) = (mlsexp_String v1:pretty)`;
   `remove_all (Append v2 _11 v3:pretty) = Append (remove_all v2) F
  (remove_all v3)`;
   `remove_all (mlsexp_Size v4 v5) = remove_all v5`];;

let smart_remove_def,smart_remove_ind = define_rec
  [`smart_remove i k (mlsexp_Size n b) =
      (if k + n < 70 then remove_all b else smart_remove i k b)`;
   `smart_remove i k (mlsexp_Parenthesis v) = mlsexp_Parenthesis
  (smart_remove (i + 1) (k + 1) v)`;
   `smart_remove i k (mlsexp_String v1:pretty) = (mlsexp_String
  v1:pretty)`;
   `smart_remove i k (Append v2 b v3:pretty) =
      (let n2 = mlsexp_get_size v2 in
      let n3 = get_next_size v3 in
        if k + n2 + n3 < 50 then
          Append (smart_remove i k v2) F (smart_remove i (k + n2)
            v3) else
          Append (smart_remove i k v2) T (smart_remove i i v3))`];;

let flatten_def,flatten_ind = define_rec
  [`mlsexp_flatten indent (mlsexp_Size n p) s = mlsexp_flatten indent
  p s`;
   `mlsexp_flatten indent (mlsexp_Parenthesis p) s =
      (implode "(") :: mlsexp_flatten (mlstring_concat [indent;
        (implode "   ")]) p ((implode ")") :: s)`;
   `mlsexp_flatten indent (mlsexp_String t:pretty) s = t :: s`;
   `mlsexp_flatten indent (Append p1 b p2:pretty) s =
      mlsexp_flatten indent p1 ((if b then indent else (implode
        " ")) :: mlsexp_flatten indent p2 s)`];;
hol4_overload "flatten" "mlsexp_flatten";;

let str_tree_to_strs_def = new_definition
  `str_tree_to_strs end v = mlsexp_flatten (implode "\n")
  (smart_remove 0 0 (mlsexp_annotate (v2pretty v))) [end]`;;

(* [local] *)
let test1_str_tree_to_strs = prove
 (`mlstring_concat (str_tree_to_strs (implode "")
                            (mlsexp_Trees [mlsexp_Str (implode
                              "hello");
                              mlsexp_Str (implode "there")])) =
   (implode "(hello there)")`,
  CHEAT_TAC);;

(* [local] *)
let test2_str_tree_to_strs = prove
 (`mlstring_concat (str_tree_to_strs (implode "")
                            (mlsexp_Trees [mlsexp_Str (implode
                              "test");
                              mlsexp_GrabLine (mlsexp_Str (implode
                                "hi"));
                              mlsexp_GrabLine (mlsexp_Str (implode
                                "there"))])) =
   (implode "(test\n   hi\n   there)")`,
  CHEAT_TAC);;

(*--------------------------------------------------------------*
   Pretty printing of sexp
 *--------------------------------------------------------------*)

let is_safe_char_def = new_definition
  `is_safe_char c <=> ~(MEM c "()\"\000") /\ ~(isSpace c)`;;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let str_every_def,str_every_ind = define_wf
  `MEASURE (\(x0,x1,x2). (\n. n) x1)`
  [`str_every p n s =
     (if n = 0 then T else
       p (strsub s (n - 1)) /\ str_every p (n - (1:num)) s)`];;

let make_str_safe_def = new_definition
  `make_str_safe s =
     (if s = (implode "") then implode "\"\"" else
     if str_every is_safe_char (strlen s) s then s else escape_str
       s)`;;

let sexp2tree_def = define_mutual_rec
  [`sexp2tree (Atom s) = mlsexp_Str (make_str_safe s)`;
   `sexp2tree (Expr l) = mlsexp_Trees (sexp2trees l)`;
   `sexp2trees [] = []`;
   `sexp2trees (v :: vs) = sexp2tree v :: sexp2trees vs`];;

let sexp_to_app_list_def = define_mutual_rec
  [`sexp_to_app_list (Atom s) = misc_List [make_str_safe s]`;
   `sexp_to_app_list (Expr l) =
      Append (misc_List [(implode "(")])
             (misc_Append (sexps_to_app_list l) (misc_List
               [(implode ")")]))`;
   `sexps_to_app_list [] = misc_List []`;
   `sexps_to_app_list (v :: vs) =
      (if NULL vs then sexp_to_app_list v else Append
        (sexp_to_app_list v)
                  (misc_Append (misc_List [(implode " ")])
                    (sexps_to_app_list vs)))`];;

let sexp_to_string_def = new_definition
  `sexp_to_string s = mlstring_concat (append (sexp_to_app_list s))`;;

let sexp_to_pretty_string_def = new_definition
  `sexp_to_pretty_string s = mlstring_concat (str_tree_to_strs
  (implode "\n") (sexp2tree s))`;;

(*--------------------------------------------------------------*
   Proofs relating parsing with pretty prniting
 *--------------------------------------------------------------*)

let to_tokens_def,to_tokens_ind = define_shaped_rec
  "nested"
  [`to_tokens (Atom a) = [SYMBOL a]`;
   `to_tokens (Expr xs) = [OPEN] ++ FLAT (MAP (\x. to_tokens x) xs)
  ++ [CLOSE]`];;

(* [local] *)
let parse_aux_to_tokens_lemma = prove
 (`!x xs s rest.
     parse_aux (REVERSE (to_tokens x) ++ rest) xs s =
     parse_aux rest (x :: xs) s`,
  CHEAT_TAC);;

let parse_aux_to_tokens_thm = prove
 (`parse_aux (REVERSE (to_tokens x)) [] [] = [x]`,
  CHEAT_TAC);;

let str_every_thm = prove
 (`!P i m. str_every P i m /\ i <= strlen m ==> (!k. k < i ==> P (EL k
  (explode m)))`,
  CHEAT_TAC);;

let read_symbol_thm = prove
 (`!t s acc.
     EVERY is_safe_char t /\ (~(s = "") ==> isSpace (HD s) \/ HD s =
       (CHR 41)) ==>
     read_symbol (t ++ s) acc = (implode (REVERSE acc ++ t),s)`,
  CHEAT_TAC);;

let read_string_aux_thm = prove
 (`!xs s acc.
     read_string_aux (STRCAT (STRCAT (CONCAT (MAP char_escaped xs))
       "\"") s) acc =
     INR (implode (REVERSE acc ++ xs),s)`,
  CHEAT_TAC);;

let lex_aux_make_str_safe = prove
 (`!m s ts depth.
     (~(s = "") ==> isSpace (HD s) \/ HD s = (CHR 41)) /\
     (depth = 0 ==> ts = []) ==>
     mlsexp_lex_aux depth (STRCAT (match make_str_safe m with implode
       x -> x) s) ts =
     (if depth = 0 then INR (SYMBOL m :: ts,s) else mlsexp_lex_aux
       depth s (SYMBOL m :: ts))`,
  CHEAT_TAC);;

let flatten_acc = prove
 (`!x indent s. mlsexp_flatten indent x s = mlsexp_flatten indent x []
  ++ s`,
  CHEAT_TAC);;

let lex_aux_spaces = prove
 (`!t rest ts depth.
     EVERY isSpace t ==>
     mlsexp_lex_aux depth (t ++ rest) ts = mlsexp_lex_aux depth
       rest ts`,
  CHEAT_TAC);;

let lex_aux_sexp2tree = prove
 (`(!x s ts depth m n indent.
      (~(s = "") ==> isSpace (HD s) \/ HD s = (CHR 41)) /\
      (depth = 0 ==> ts = []) /\ ~(indent = (implode "")) /\ EVERY
        isSpace (explode indent) ==>
      mlsexp_lex_aux depth
              (STRCAT
               (explode
                (mlstring_concat
                 (mlsexp_flatten indent
                          (smart_remove m n (mlsexp_annotate
                            (v2pretty (sexp2tree x))))
                          []))) s) ts =
      (if depth = 0 then INR (REVERSE (to_tokens x) ++ ts,s) else
        mlsexp_lex_aux depth s (REVERSE (to_tokens x) ++ ts)) /\
      mlsexp_lex_aux depth
              (STRCAT
               (explode
                (mlstring_concat
                 (mlsexp_flatten indent
                          (remove_all (mlsexp_annotate (v2pretty
                            (sexp2tree x))))
                          []))) s) ts =
      (if depth = 0 then INR (REVERSE (to_tokens x) ++ ts,s) else
        mlsexp_lex_aux depth s (REVERSE (to_tokens x) ++ ts))) /\
   (!xs s ts depth indent m n.
      (~(s = "") ==> isSpace (HD s) \/ HD s = (CHR 41)) /\ ~(depth =
        0) /\ ~(indent = (implode "")) /\ EVERY isSpace (explode indent)
        ==>
      mlsexp_lex_aux depth
              (STRCAT
               (explode
                (mlstring_concat
                 (mlsexp_flatten indent
                   (smart_remove m n (mlsexp_annotate (newlines
                     (vs2pretty (sexp2trees xs)))))
                   []))) s) ts =
      (mlsexp_lex_aux depth s (REVERSE (FLAT (MAP to_tokens xs)) ++
        ts)) /\
      mlsexp_lex_aux depth
              (STRCAT
               (explode
                (mlstring_concat
                 (mlsexp_flatten indent
                   (remove_all (mlsexp_annotate (newlines (vs2pretty
                     (sexp2trees xs)))))
                   []))) s) ts =
      (mlsexp_lex_aux depth s (REVERSE (FLAT (MAP to_tokens xs)) ++
        ts)))`,
  CHEAT_TAC);;

let lex_aux_sexp_to_list = prove
 (`(!x s ts depth.
      (~(s = "") ==> isSpace (HD s) \/ HD s = (CHR 41)) /\
      (depth = 0 ==> ts = []) ==>
      mlsexp_lex_aux depth (explode (mlstring_concat (append
        (sexp_to_app_list x))) ++ s) ts =
      (if depth = 0 then
        INR (REVERSE (to_tokens x) ++ ts,s) else
        mlsexp_lex_aux depth s (REVERSE (to_tokens x) ++ ts))) /\
   (!xs s ts depth.
      (~(s = "") ==> isSpace (HD s) \/ HD s = (CHR 41)) /\ ~(depth =
        0) ==>
      mlsexp_lex_aux depth (explode (mlstring_concat (append
        (sexps_to_app_list xs))) ++ s) ts =
      mlsexp_lex_aux depth s (REVERSE (FLAT (MAP (\x. to_tokens x)
        xs)) ++ ts))`,
  CHEAT_TAC);;

let parse_sexp_to_string = prove
 (`!s x.
     (~(s = "") ==> isSpace (HD s)) ==>
     mlsexp_parse (explode (sexp_to_string x) ++ s) = INR (x,s)`,
  CHEAT_TAC);;

let parse_sexp_to_pretty_string = prove
 (`!s x.
     mlsexp_parse (explode (sexp_to_pretty_string x) ++ s) = INR
       (x,"\n" ++ s)`,
  CHEAT_TAC);;

let fromString_sexp_to_string = prove
 (`fromString (sexp_to_string x) = SOME x`,
  CHEAT_TAC);;

let fromString_sexp_to_pretty_string = prove
 (`fromString (sexp_to_pretty_string x) = SOME x`,
  CHEAT_TAC);;

(* and the overloads that this file cannot see are back in the
   interface *)
let _ = unhide_overloads ();;
