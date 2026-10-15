(* ======================================================== *)
(*  lexer_impl: ported from HOL4's
    compiler/parsing/lexer_implScript.sml  *)
(* ======================================================== *)

(*
  Definition of the lexer: code for consuming tokens until a top-level
  semicolon is found (semicolons can be hidden in `let`-`in`-`end`
    blocks,
  structures, signatures, and between parentheses).
*)

needs "compiler/backend/pattern_matching/pattern_semantics.ml";;
needs "lib/ASCIInumbers.ml";;
needs "lib/location.ml";;
needs "misc/misc.ml";;
needs "semantics/lexer_fun.ml";;
needs "semantics/tokens.ml";;
(* HOL4 ancestors outside the port: rich_list *)

(* HOL4 ML code, not ported:
val tac =
 full_simp_tac (srw_ss()) [char_le_def, char_lt_def] >>
 Cases_on `t` >>
 rw [get_token_def, processIdent_def, isAlphaNum_def, isAlpha_def,
   isDigit_def,
     isLower_def, isUpper_def];
*)

let unhex_alt_def = cake_define
  `unhex_alt x = (if isHexDigit x then UNHEX x else 0)`;;

let num_from_dec_string_alt_def = cake_define
  `num_from_dec_string_alt = s2n 10 unhex_alt`;;
let num_from_hex_string_alt_def = cake_define
  `num_from_hex_string_alt = s2n 16 unhex_alt`;;

(* HOL4 termination: THEN REPEAT STRIP_TAC THEN IMP_RES_TAC (GSYM
   read_while_thm) THEN IMP_RES_TAC (GSYM read_string_thm) THEN
   IMP_RES_TAC skip_comment_thm THEN Cases_on `str` THEN
   FULL_SIMP_TAC (srw_ss()) [LENGTH] THEN DECIDE_TAC *)
let next_sym_alt_def = cake_define_wf
  `MEASURE (LENGTH o FST)`
  `(next_sym_alt "" _1 = NONE) /\
   (next_sym_alt (c :: str) loc =
      (if c = (CHR 10) then
         next_sym_alt str (next_line loc) else if isSpace c then
        next_sym_alt str (next_loc 1 loc) else if isDigit c then
        if ~(str = "") /\ c = (CHR 48) /\ HD str = (CHR 119) then
          if TL str = "" then SOME (ErrorS,Locs loc loc,"") else if
            isDigit (HD (TL str)) then
            let (n,rest) = read_while isDigit (TL str) [] in
              SOME (WordS (num_from_dec_string_alt n),
                    Locs loc (next_loc (LENGTH n + 1) loc),
                    rest) else if HD (TL str) = (CHR 120) then
            let (n,rest) = read_while isHexDigit (TL (TL str)) [] in
              SOME (WordS (num_from_hex_string_alt n),
                    Locs loc (next_loc (LENGTH n + 2) loc),
                    rest) else SOME (ErrorS,Locs loc loc,TL str) else
          if ~(str = "") /\ c = (CHR 48) /\ HD str = (CHR 120) then
            let (n,rest) = read_while isHexDigit (TL str) [] in
              SOME (NumberS (&num_from_hex_string_alt n),
                    Locs loc (next_loc (LENGTH n) loc),
                    rest) else
            let (n,rest) = read_while isDigit str [] in
              SOME (NumberS (&(num_from_dec_string_alt (c :: n))),
                    Locs loc (next_loc (LENGTH n) loc),
                    rest) else if c = (CHR 126) /\ ~(str = "") /\
                      isDigit (HD str) then
        let (n,rest) = read_while isDigit str [] in
          SOME (NumberS (0 - &(num_from_dec_string_alt n)),
                Locs loc (next_loc (LENGTH n + 1) loc),
                rest) else if c = (CHR 39) then
        let (n,rest) = read_while isAlphaNumPrime str [c] in
          SOME (OtherS n,
                Locs loc (next_loc (LENGTH n - 1) loc),
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
        let (t,loc',rest) =
              read_FFIcall (TL str) "" (next_loc 2 loc) in
          SOME (t,Locs loc loc',rest) else if isPREFIX "(*" (c ::
            str) then
        match skip_comment (TL str) (0:num) (next_loc 2 loc) with
          NONE -> SOME (ErrorS,Locs loc (next_loc 2 loc),"") | SOME
          (rest,loc') -> next_sym_alt rest loc' else if c = (CHR 95)
          then SOME (OtherS "_",Locs loc loc,str) else
        let (tok',end_loc,rest) = read_Ident (STRING c str) loc [] in
          SOME (tok',Locs loc end_loc,rest)))`;;

(* lex_until_toplevel_semicolon *)

(* HOL4 termination: >> rw[] >> imp_res_tac next_token_LESS *)
let lex_aux_def = cake_define_wf
  `MEASURE (LENGTH o FST o SND o SND)`
  `lexer_impl_lex_aux acc (d:num) input loc =
     (match next_token input loc with
       NONE -> NONE |
       SOME (token,Locs loc' loc'',rest) ->
         (let new_acc = ((token,Locs loc' loc'') :: acc) in
         let newloc = next_loc 1 loc'' in
           if token = tokens_SemicolonT /\ (d = 0) then SOME (REVERSE
             new_acc,newloc,rest) else
             if token = tokens_LetT then lexer_impl_lex_aux
               new_acc (d + 1) rest newloc else if token =
               tokens_StructT then lexer_impl_lex_aux new_acc (d + 1)
               rest newloc else if token = tokens_SigT then
               lexer_impl_lex_aux new_acc (d + 1) rest newloc else if
               token = tokens_LparT then lexer_impl_lex_aux new_acc
               (d + 1) rest newloc else if token = tokens_EndT then
               lexer_impl_lex_aux new_acc (d - 1) rest newloc else if
               token = tokens_RparT then lexer_impl_lex_aux new_acc
               (d - 1) rest newloc else lexer_impl_lex_aux new_acc d
               rest newloc))`;;
hol4_overload "lex_aux" "lexer_impl_lex_aux";;

let lex_until_toplevel_semicolon_def = cake_define
  `lex_until_toplevel_semicolon input = lex_aux [] 0 input`;;

(* lex_until_toplevel_semicolon_alt *)

(* HOL4 termination: >> rw[] >> imp_res_tac next_sym_LESS *)
let lex_aux_alt_def = cake_define_wf
  `MEASURE (LENGTH o FST o SND o SND)`
  `lex_aux_alt acc (d:num) input l =
     (match next_sym input l with
       NONE -> NONE |
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
               lex_aux_alt new_acc d rest newloc))`;;

let lex_until_top_semicolon_alt_def = cake_define
  `lex_until_top_semicolon_alt input = lex_aux_alt [] 0 input`;;


let token_of_sym_loc_def = cake_define
  `token_of_sym_loc (t,l) = (token_of_sym t,l)`;;

(* HOL4 ML code, not ported:
val lex_aux_alt_thm = Q.prove(
  `!acc d input l.
      case lex_aux_alt acc d input l of
      | NONE => (lex_aux (MAP token_of_sym_loc acc) d input l = NONE)
      | SOME (ts, rest) => (lex_aux (MAP token_of_sym_loc acc) d input l
        =
                           SOME (MAP token_of_sym_loc ts,rest))`,
  HO_MATCH_MP_TAC (fetch "-" "lex_aux_alt_ind") THEN REPEAT STRIP_TAC
  THEN ONCE_REWRITE_TAC [lex_aux_alt_def,lex_aux_def]
  THEN SIMP_TAC std_ss [next_token_def]
  THEN Cases_on `next_sym input l` THEN1 EVAL_TAC
  THEN every_case_tac THEN FULL_SIMP_TAC (srw_ss()) [LET_DEF]
  THEN FULL_SIMP_TAC std_ss [token_of_sym_EQ_LEMMA]
  THEN SRW_TAC [] [] THEN FULL_SIMP_TAC (srw_ss())
    [rich_listTheory.MAP_REVERSE]
  THEN FULL_SIMP_TAC (srw_ss())
    [token_of_sym_loc_def,token_of_sym_def,get_token_def])
  |> Q.SPECL [`[]`,`0`] |> SIMP_RULE std_ss [MAP] ;
*)

(* lex_impl_all *)

(* HOL4 termination: >> rw [] >> metis_tac
   [lex_until_toplevel_semicolon_LESS] *)
let lex_impl_all_def = cake_define_wf
  `MEASURE (LENGTH o FST)`
  `lex_impl_all input l =
     (match lex_until_toplevel_semicolon input l with NONE -> [] |
       SOME (t,loc,input') -> t :: lex_impl_all input' loc)`;;

let lex_aux_tokens_def = cake_define
  `lex_aux_tokens acc (d:num) input =
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
                  lex_aux_tokens new_acc d rest))`;;

let lex_until_toplevel_semicolon_tokens_def = cake_define
  `lex_until_toplevel_semicolon_tokens input = lex_aux_tokens [] 0
  input`;;

(* HOL4 termination: >> SIMP_TAC std_ss
   [lex_until_toplevel_semicolon_tokens_def] >> METIS_TAC
   [lex_aux_tokens_LESS] *)
let lex_impl_all_tokens_def = cake_define_wf
  `MEASURE LENGTH`
  `lex_impl_all_tokens input =
      (match lex_until_toplevel_semicolon_tokens input with
        NONE -> [] | SOME (t,input) -> t :: lex_impl_all_tokens
          input)`;;
