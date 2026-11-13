(* ======================================================== *)
(*  lexer_impl: ported from HOL4's
    compiler/parsing/lexer_implScript.sml
    A definition theory, with 13 definitions and 23 theorems.
    Needed by compiler.ml.  *)
(* ======================================================== *)

(*
  Definition of the lexer: code for consuming tokens until a top-level
  semicolon is found (semicolons can be hidden in `let`-`in`-`end` blocks,
  structures, signatures, and between parentheses).
*)

needs "basis/pure/mlstring.ml";;
needs "lib/ASCIInumbers.ml";;
needs "lib/location.ml";;
needs "misc/misc.ml";;
needs "semantics/lexer_fun.ml";;
needs "semantics/tokens.ml";;

(* the theories whose names the Ancestors blocks of the source
   bring, which are the ones that its statements read: the
   overloads of every other theory come out of the interface
   while this file loads *)
let _ = hol4_ancestors "lexer_impl"
  ["lexer_fun"; "misc"; "tokens"];;

let _ = do_list hide_constant ["val"];;
(* HOL4 ancestors outside the port: rich_list *)

(* HOL4 lexer_implScript.sml:16-20: a proof *)

let get_token_eqn = prove
 (`!s.
    get_token s =
      (match s with
           [] -> tokens_LexErrorT | [c] ->
             (if c <= (CHR 59) then
               if c <= (CHR 41) then
                 if c <= (CHR 39) then
                   if c = (CHR 35) then tokens_HashT else
                   if c = (CHR 39) then tokens_TyvarT (implode s)
                     else
                   tokens_SymbolT (implode s) else
                   if c = (CHR 40) then tokens_LparT else
                   if c = (CHR 41) then tokens_RparT else
                   tokens_SymbolT (implode s) else
                 if c <= (CHR 44) then
                   if c = (CHR 42) then tokens_StarT else
                   if c = (CHR 44) then tokens_CommaT else
                   tokens_SymbolT (implode s) else
                   if c = (CHR 58) then tokens_ColonT else
                   if c = (CHR 59) then tokens_SemicolonT else
                   tokens_SymbolT (implode s) else
               if c <= (CHR 93) then
                 if c <= (CHR 90) then
                   if (CHR 65) <= c /\ c <= (CHR 90) then
                     tokens_AlphaT (implode s) else
                   if c = (CHR 61) then tokens_EqualsT else
                   tokens_SymbolT (implode s) else
                   if c = (CHR 91) then tokens_LbrackT else
                   if c = (CHR 93) then tokens_RbrackT else
                   tokens_SymbolT (implode s) else
                 if c <= (CHR 123) then
                   if c = (CHR 95) then tokens_UnderbarT else
                   if (CHR 97) <= c /\ c <= (CHR 122) then
                     tokens_AlphaT (implode s) else
                   if c = (CHR 123) then tokens_LbraceT else
                   tokens_SymbolT (implode s) else
                   if c = (CHR 124) then tokens_BarT else
                   if c = (CHR 125) then tokens_RbraceT else
                   tokens_SymbolT (implode s)) | c :: s' ->
             (if c < (CHR 97) then
               if c <= (CHR 46) then
                 if c = (CHR 39) then tokens_TyvarT (implode s) else
                 if s = "->" then tokens_ArrowT else
                 if s = "..." then tokens_DotsT else
                 tokens_SymbolT (implode s) else
                 if s = ":>" then tokens_SealT else
                 if s = "=>" then tokens_DarrowT else
                 if (CHR 65) <= c /\ c <= (CHR 90) then tokens_AlphaT
                   (implode s) else
                 tokens_SymbolT (implode s) else if c <= (CHR 122)
                   then
               if c <= (CHR 105) then
                 if c <= (CHR 101) then
                   if c < (CHR 101) then
                     if s = "and" then tokens_AndT else
                     if s = "andalso" then tokens_AndalsoT else
                     if s = "as" then tokens_AsT else
                     if s = "case" then tokens_CaseT else
                     if s = "datatype" then tokens_DatatypeT else
                     tokens_AlphaT (implode s) else
                     if s = "else" then tokens_ElseT else
                     if s = "end" then tokens_EndT else
                     if s = "eqtype" then tokens_EqtypeT else
                     if s = "exception" then tokens_ExceptionT else
                     tokens_AlphaT (implode s) else
                   if c <= (CHR 104) then
                     if s = "fn" then tokens_FnT else
                     if s = "fun" then tokens_FunT else
                     if s = "handle" then tokens_HandleT else
                     tokens_AlphaT (implode s) else
                     if s = "if" then tokens_IfT else
                     if s = "in" then tokens_InT else
                     if s = "include" then tokens_IncludeT else
                     tokens_AlphaT (implode s) else
                 if c <= (CHR 114) then
                   if c = (CHR 108) then
                     if s = "let" then tokens_LetT else
                     if s = "local" then tokens_LocalT else
                     tokens_AlphaT (implode s) else if c = (CHR 111)
                       then
                     if s = "of" then tokens_OfT else
                     if s = "op" then tokens_OpT else
                     if s = "open" then tokens_OpenT else
                     if s = "orelse" then tokens_OrelseT else
                     tokens_AlphaT (implode s) else
                     if s = "raise" then tokens_RaiseT else
                     if s = "rec" then tokens_RecT else
                     tokens_AlphaT (implode s) else
                   if c = (CHR 115) then
                     if s = "sharing" then tokens_SharingT else
                     if s = "sig" then tokens_SigT else
                     if s = "signature" then tokens_SignatureT else
                     if s = "struct" then tokens_StructT else
                     if s = "structure" then tokens_StructureT else
                     tokens_AlphaT (implode s) else if c < (CHR 119)
                       then
                     if s = "then" then tokens_ThenT else
                     if s = "type" then tokens_TypeT else
                     if s = "val" then tokens_ValT else
                     tokens_AlphaT (implode s) else
                     if s = "where" then tokens_WhereT else
                     if s = "with" then tokens_WithT else
                     if s = "withtype" then tokens_WithtypeT else
                     tokens_AlphaT (implode s) else
               tokens_SymbolT (implode s)))`,
  CHEAT_TAC);;

let unhex_alt_def = new_definition
  `unhex_alt x = (if isHexDigit x then UNHEX x else 0)`;;

let num_from_dec_string_alt_def = new_definition
  `num_from_dec_string_alt = s2n 10 unhex_alt`;;
let num_from_hex_string_alt_def = new_definition
  `num_from_hex_string_alt = s2n 16 unhex_alt`;;

(* the termination relation that HOL4 gives is
     MEASURE (LENGTH o FST)
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 lexer_implScript.sml:239-245: the tactic that proves the
   termination *)
let next_sym_alt_def,next_sym_alt_ind = define_guess
  [`next_sym_alt "" _1 = NONE`;
   `next_sym_alt (c :: str) loc =
         (if c = (CHR 10) then
            // skip new line
            next_sym_alt str (next_line loc) else if isSpace c then
           // skip blank space
           next_sym_alt str (next_loc 1 loc) else if isDigit c then
           // read number
           if ~(str = "") /\ c = (CHR 48) /\ HD str = (CHR 119) then
             if TL str = "" then SOME (ErrorS,Locs loc loc,"") else
               if isDigit (HD (TL str)) then
               let (n,rest) = read_while isDigit (TL str) [] in
                 SOME (WordS (num_from_dec_string_alt n),
                       Locs loc (next_loc (LENGTH n + 1) loc),
                       rest) else if HD (TL str) = (CHR 120) then
               let (n,rest) = read_while isHexDigit (TL (TL str)) []
                 in
                 SOME (WordS (num_from_hex_string_alt n),
                       Locs loc (next_loc (LENGTH n + 2) loc),
                       rest) else SOME (ErrorS,Locs loc loc,TL str)
                         else
             if ~(str = "") /\ c = (CHR 48) /\ HD str = (CHR 120)
               then
               let (n,rest) = read_while isHexDigit (TL str) [] in
                 SOME (NumberS (&(num_from_hex_string_alt n)),
                       Locs loc (next_loc (LENGTH n) loc),
                       rest) else
               let (n,rest) = read_while isDigit str [] in
                 SOME (NumberS (&(num_from_dec_string_alt (c ::
                   n))),
                       Locs loc (next_loc (LENGTH n) loc),
                       rest) else if c = (CHR 126) /\ ~(str = "") /\
                         isDigit (HD str) then
           // read negative number
           let (n,rest) = read_while isDigit str [] in
             SOME (NumberS ((&0) - &(num_from_dec_string_alt n)),
                   Locs loc (next_loc (LENGTH n + 1) loc),
                   rest) else if c = (CHR 39) then
           // read type variable
           let (n,rest) = read_while isAlphaNumPrime str [c] in
             SOME (OtherS n,
                   Locs loc (next_loc (LENGTH n - 1) loc),
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
           let (t,loc',rest) =
                 read_FFIcall (TL str) "" (next_loc 2 loc) in
             SOME (t,Locs loc loc',rest) else if isPREFIX "(*" (c ::
               str) then
           match skip_comment (TL str) (0:num) (next_loc 2 loc) with
             NONE -> SOME (ErrorS,Locs loc (next_loc 2 loc),"") | SOME
             (rest,loc') -> next_sym_alt rest loc' else if c = (CHR 95)
             then SOME (OtherS "_",Locs loc loc,str) else
           let (tok',end_loc,rest) = read_Ident (STRING c str) loc
             [] in
             SOME (tok',Locs loc end_loc,rest))`];;

(* [local] *)
let EVERY_isDigit_imp = prove
 (`EVERY isDigit x ==>
   MAP UNHEX x = MAP unhex_alt x`,
  CHEAT_TAC);;

(* [local] *)
let toNum_rw = prove
 (`!x. EVERY isDigit x ==>
   num_from_dec_string x = num_from_dec_string_alt x`,
  CHEAT_TAC);;

(* [local] *)
let EVERY_isHexDigit_imp = prove
 (`EVERY isHexDigit x ==>
   MAP UNHEX x = MAP unhex_alt x`,
  CHEAT_TAC);;

(* [local] *)
let num_from_hex_string_rw = prove
 (`!x. EVERY isHexDigit x ==>
       num_from_hex_string x = num_from_hex_string_alt x`,
  CHEAT_TAC);;

(* [local] *)
let EVERY_IMPLODE = prove
 (`!ls P.
     EVERY P (IMPLODE ls) <=> EVERY P ls`,
  CHEAT_TAC);;

(* [local] *)
let read_while_P_lem = prove
 (`!ls rest P x y.
     EVERY P rest /\
     read_while P ls rest = (x,y) ==>
     EVERY P x`,
  CHEAT_TAC);;

(* [local] *)
let read_while_P = prove
 (`!ls P x y. read_while P ls "" = (x,y) ==> EVERY P x`,
  CHEAT_TAC);;

let next_sym_eq = prove
 (`!x l. next_sym x l = next_sym_alt x l`,
  CHEAT_TAC);;

(* lex_until_toplevel_semicolon *)

(* the termination relation that HOL4 gives is
     MEASURE (LENGTH o FST o SND o SND)
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 lexer_implScript.sml:344-347: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let lexer_impl_lex_aux_def,lexer_impl_lex_aux_ind = define_guess_cheat
  [`lexer_impl_lex_aux acc (d:num) input loc =
     (match next_token input loc with
       // case: end of input
       NONE -> NONE |
       // case: token found
       SOME (token,Locs loc' loc'',rest) ->
         (let new_acc = ((token,Locs loc' loc'') :: acc) in
         let newloc = next_loc 1 loc'' in
           if token = tokens_SemicolonT /\ (d = 0) then SOME
             (REVERSE new_acc,newloc,rest) else
             if token = tokens_LetT then lexer_impl_lex_aux
               new_acc (d + 1) rest newloc else if token =
               tokens_StructT then lexer_impl_lex_aux new_acc (d +
               1) rest newloc else if token = tokens_SigT then
               lexer_impl_lex_aux new_acc (d + 1) rest newloc else
               if token = tokens_LparT then lexer_impl_lex_aux
               new_acc (d + 1) rest newloc else if token =
               tokens_EndT then lexer_impl_lex_aux new_acc (d - 1)
               rest newloc else if token = tokens_RparT then
               lexer_impl_lex_aux new_acc (d - 1) rest newloc else
               lexer_impl_lex_aux new_acc d rest newloc))`];;
hol4_overload "lex_aux" "lexer_impl_lex_aux";;

let lex_until_toplevel_semicolon_def = new_definition
  `lex_until_toplevel_semicolon input = lexer_impl_lex_aux [] 0 input`;;

(* [local] *)
let lex_aux_LESS = prove
 (`!acc d input l.
       (lexer_impl_lex_aux acc d input l = SOME (ts,l',rest)) ==>
       (if acc = [] then LENGTH rest < LENGTH input else LENGTH
         rest <= LENGTH input)`,
  CHEAT_TAC);;

let lex_until_toplevel_semicolon_LESS = prove
 (`(lex_until_toplevel_semicolon input l = SOME (ts,l',rest)) ==>
    LENGTH rest < LENGTH input`,
  CHEAT_TAC);;

(* lex_until_toplevel_semicolon_alt *)

(* the termination relation that HOL4 gives is
     MEASURE (LENGTH o FST o SND o SND)
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 lexer_implScript.sml:402-405: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let lex_aux_alt_def,lex_aux_alt_ind = define_guess_cheat
  [`lex_aux_alt acc (d:num) input l =
     (match next_sym input l with
       // case: end of input
       NONE -> NONE |
       // case: token found
       SOME (token,Locs loc' loc'',rest) ->
         (let new_acc = ((token,Locs loc' loc'') :: acc) in
         let newloc = next_loc 1 loc'' in
           if (token = OtherS ";") /\ (d = 0) then SOME (REVERSE
             new_acc,newloc,rest) else if MEM token [OtherS "let";
             OtherS "struct";
                              OtherS "sig"; OtherS "("] then
             lex_aux_alt new_acc (d + 1) rest newloc else if MEM
               token [OtherS ")"; OtherS "end"] then
             lex_aux_alt new_acc (d - 1) rest newloc else
               lex_aux_alt new_acc d rest newloc))`];;

let lex_until_top_semicolon_alt_def = new_definition
  `lex_until_top_semicolon_alt input = lex_aux_alt [] 0 input`;;

(* [local] *)
let lex_aux_alt_LESS = prove
 (`!acc d input l.
       (lex_aux_alt acc d input l = SOME (ts,l',rest)) ==>
       (if acc = [] then LENGTH rest < LENGTH input else LENGTH
         rest <= LENGTH input)`,
  CHEAT_TAC);;

let lex_until_top_semicolon_alt_LESS = prove
 (`(lex_until_top_semicolon_alt input l = SOME (ts,l',rest)) ==>
    LENGTH rest < LENGTH input`,
  CHEAT_TAC);;

(* [local] *)
let token_of_sym_EQ_LEMMA = prove
 (`((token_of_sym q = tokens_LetT) = (q = OtherS "let")) /\
   ((token_of_sym q = tokens_EndT) = (q = OtherS "end")) /\
   ((token_of_sym q = tokens_SigT) = (q = OtherS "sig")) /\
   ((token_of_sym q = tokens_StructT) = (q = OtherS "struct")) /\
   ((token_of_sym q = tokens_SemicolonT) = (q = OtherS ";")) /\
   ((token_of_sym q = tokens_RparT) = (q = OtherS ")")) /\
   ((token_of_sym q = tokens_LparT) = (q = OtherS "("))`,
  CHEAT_TAC);;


let token_of_sym_loc_def = new_definition
  `token_of_sym_loc (t,l) = (token_of_sym t,l)`;;

(* HOL4 lexer_implScript.sml:460-474: a theorem that HOL4 states as
   the value of an ML expression: lex_aux_alt_thm *)

let lex_until_top_semicolon_alt_thm = prove
 (`match lex_until_top_semicolon_alt input l with NONE ->
  (lex_until_toplevel_semicolon input l = NONE) | SOME (ts,rest) ->
        (lex_until_toplevel_semicolon input l = SOME (MAP
          token_of_sym_loc ts,rest))`,
  CHEAT_TAC);;

(* lex_impl_all *)

(* the termination relation that HOL4 gives is
     MEASURE (LENGTH o FST)
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 lexer_implScript.sml:493-497: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let lex_impl_all_def,lex_impl_all_ind = define_guess_cheat
  [`lex_impl_all input l =
     (match lex_until_toplevel_semicolon input l with NONE -> []
       | SOME (t,loc,input') -> t :: lex_impl_all input' loc)`];;

let lex_aux_tokens_def,lex_aux_tokens_ind = define_shaped_rec
  "match"
  [`lex_aux_tokens acc (d:num) input =
      (match input with
        [] -> NONE | (token,locs) :: rest ->
          (let new_acc = (token,locs) :: acc in
            if token = tokens_SemicolonT /\ (d = 0) then
              SOME (REVERSE (new_acc),rest) else
              if token = tokens_LetT then
                lex_aux_tokens new_acc (d + 1) rest else if token =
                  tokens_StructT then
                lex_aux_tokens new_acc (d + 1) rest else if token =
                  tokens_SigT then
                lex_aux_tokens new_acc (d + 1) rest else if token =
                  tokens_LparT then
                lex_aux_tokens new_acc (d + 1) rest else if token =
                  tokens_EndT then
                lex_aux_tokens new_acc (d - 1) rest else if token =
                  tokens_RparT then
                lex_aux_tokens new_acc (d - 1) rest else
                  lex_aux_tokens new_acc d rest))`];;

let lex_until_toplevel_semicolon_tokens_def = new_definition
  `lex_until_toplevel_semicolon_tokens input = lex_aux_tokens [] 0
  input`;;

(* [local] *)
let lex_aux_tokens_LESS = prove
 (`!acc d input.
       (lex_aux_tokens acc d input = SOME (t,rest)) ==>
       (if acc = [] then LENGTH rest < LENGTH input else LENGTH
         rest <= LENGTH input)`,
  CHEAT_TAC);;

(* the termination relation that HOL4 gives is
     MEASURE LENGTH
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 lexer_implScript.sml:549-553: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let lex_impl_all_tokens_def,lex_impl_all_tokens_ind = define_guess_cheat
  [`lex_impl_all_tokens input =
      (match lex_until_toplevel_semicolon_tokens input with
        NONE -> [] | SOME (t,input) -> t :: lex_impl_all_tokens
          input)`];;

(* [local] *)
let lex_aux_tokens_thm_1 = prove
 (`!input l acc d res1 res2.
       (lex_aux_tokens acc d (lexer_fun_aux input l) = res1) /\
       (lexer_impl_lex_aux acc d input l = res2) ==>
       (match res2 with NONE -> (res1 = NONE) | SOME (ts,l',rest) ->
               (res1 = SOME (ts,lexer_fun_aux rest l')))`,
  CHEAT_TAC);;

(* HOL4 lexer_implScript.sml:578: a theorem that HOL4 states as the
   value of an ML expression: lex_aux_tokens_thm *)

(* [local] *)
let lex_impl_all_tokens_thm = prove
 (`!input l. lex_impl_all input l =
             lex_impl_all_tokens (lexer_fun_aux input l)`,
  CHEAT_TAC);;

(* lex_aux_tokens_thm_1[local] *)
let lexer_impl_lex_aux_tokens_thm_1 = prove
 (`!input d acc.
       match lex_aux_tokens acc d input with
         NONE -> (toplevel_semi_dex (LENGTH acc) d input = NONE) |
           SOME (toks,rest) ->
           (toplevel_semi_dex (LENGTH acc) d input = SOME (LENGTH
             toks)) /\
           (REVERSE acc ++ input = toks ++ rest)`,
  CHEAT_TAC);;

(* HOL4 lexer_implScript.sml:614-615: a theorem that HOL4 states as
   the value of an ML expression: lex_aux_tokens_thm *)

(* [local] *)
let split_top_level_semi_thm = prove
 (`!input. split_top_level_semi input = lex_impl_all_tokens input`,
  CHEAT_TAC);;

let lexer_correct = prove
 (`!input. split_top_level_semi (lexer_fun_aux input l) = lex_impl_all
  input l`,
  CHEAT_TAC);;

(* and the names that this file reads as variables are constants again *)
let _ = do_list unhide_constant
  ["val"];;

(* and the overloads that this file cannot see are back in the
   interface *)
let _ = unhide_overloads ();;
