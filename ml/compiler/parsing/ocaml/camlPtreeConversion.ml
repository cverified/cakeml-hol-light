(* ======================================================== *)
(*  camlPtreeConversion: ported from HOL4's
    compiler/parsing/ocaml/camlPtreeConversionScript.sml
    A definition theory, with 109 definitions, 3 datatypes and 6
    theorems.  Needed by caml_parser.ml and caml_parserProg.ml.  *)
(* ======================================================== *)

(*
  A theory for converting OCaml parse trees to abstract syntax.
 *)

needs "basis/pure/mllist.ml";;
needs "basis/pure/mlprettyprinter.ml";;
needs "basis/pure/mlstring.ml";;
needs "basis/pure/mlvector.ml";;
needs "candle/standard/monadic/holKernel.ml";;
needs "candle/standard/syntax/holBoolSyntax.ml";;
needs "candle/standard/syntax/holSyntax.ml";;
needs "characteristic/cfApp.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/clos_known.ml";;
needs "compiler/backend/db_vars.ml";;
needs "compiler/backend/jsonLang.ml";;
needs "compiler/backend/pattern_matching/pattern_semantics.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/parsing/cmlPEG.ml";;
needs "compiler/parsing/cmlParse.ml";;
needs "compiler/parsing/lexer_impl.ml";;
needs "compiler/parsing/ocaml/camlPEG.ml";;
needs "compiler/parsing/ocaml/caml_lex.ml";;
needs "lib/binary_ieee.ml";;
needs "lib/grammar.ml";;
needs "lib/location.ml";;
needs "lib/peg.ml";;
needs "lib/pegexec.ml";;
needs "lib/precparser.ml";;
needs "lib/sorting.ml";;
needs "lib/sum.ml";;
needs "lib/term.ml";;
needs "misc/misc.ml";;
needs "pancake/panLang.ml";;
needs "semantics/ast.ml";;
needs "semantics/cmlPtreeConversion.ml";;
needs "semantics/gram.ml";;
needs "semantics/lexer_fun.ml";;
needs "semantics/namespace.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "camlPtreeConversion"
  ["ast"; "camlPEG"; "caml_lex"; "cmlParse"; "lexer_impl"; "misc"; "mllist"];;

let _ = do_list hide_constant ["id"; "pmatch"];;

(* HOL4 camlPtreeConversionScript.sml:12-13: an overload that the source
   brings to the front: destResult, written out as pegexec_destResult *)

(* -------------------------------------------------------------------------
 * Sum monad syntax
 * ------------------------------------------------------------------------- *)

let camlPtreeConversion_bind_def = define_cases
  `(camlPtreeConversion_bind (sum_INL e) f = sum_INL e) /\
   (camlPtreeConversion_bind (sum_INR x) f = f x)`;;
add_simp camlPtreeConversion_bind_def;;

let ignore_bind_def = new_definition
  `ignore_bind m1 m2 = camlPtreeConversion_bind m1 (\u. m2)`;;
add_simp ignore_bind_def;;

let choice_def = define_cases
  `(camlPtreeConversion_choice (sum_INL e) b = b) /\
   (camlPtreeConversion_choice (sum_INR x) b = sum_INR x)`;;
add_simp choice_def;;

let camlPtreeConversion_return_def = new_definition
  `camlPtreeConversion_return = sum_INR`;;
add_simp camlPtreeConversion_return_def;;

let camlPtreeConversion_fail_def = new_definition
  `NONE = sum_INL`;;
add_simp camlPtreeConversion_fail_def;;

(* HOL4 camlPtreeConversionScript.sml:43-50: ML code, not ported *)

let mapM_def,mapM_ind = define_guess
  `(camlPtreeConversion_mapM f [] = (camlPtreeConversion_return []:'a+'b
    list)) /\
   (camlPtreeConversion_mapM f (CONS x xs) =
      (((OPTION_BIND) (f x) (\y. (OPTION_BIND) (camlPtreeConversion_mapM f
          xs) (\ys.
        camlPtreeConversion_return (CONS y ys)))):'a+'b list))`;;

(* [defncong] *)
let mapM_cong = prove
 (`!xs ys f g.
     xs = ys /\
     (!x. MEM x xs ==> f x = g x) ==>
       (camlPtreeConversion_mapM f xs:'a+'b list) =
         camlPtreeConversion_mapM g ys`,
  CHEAT_TAC);;

let option_def = define_cases
  `(camlPtreeConversion_option NONE = sum_INL (unknown_loc,(implode
    "option"))) /\
   (camlPtreeConversion_option (SOME x) = sum_INR x)`;;
add_simp option_def;;

let fmap_def = define_cases
  `(camlPtreeConversion_fmap f (sum_INR x) = sum_INR (f x)) /\
   (camlPtreeConversion_fmap f (sum_INL err) = sum_INL err)`;;
add_simp fmap_def;;

(* Builds the n-ary cartesian product of n lists (of any lengths).
 *)

let list_cart_prod_def,list_cart_prod_ind = define_guess
  `(list_cart_prod [] = [[]]) /\
   (list_cart_prod (CONS xs xss) =
      FLAT (MAP (\x. MAP (\y. CONS x y) (list_cart_prod xss)) xs))`;;

(* -------------------------------------------------------------------------
 * Compatibility layer
 * ------------------------------------------------------------------------- *)

(* Resolving precedences and lifting or-patterns to the top at the same time
 * is just too annoying. Until the CakeML syntax supports the latter, we can
 * use this pre-pattern type.
 *
 * Pp_prod and Pp_as correspond to Pp_con NONE and Pp_alias, and are used to
 * trick the precparser into producing n-ary tuples and suffixes (i.e. the
 * as-patterns).
 *)

let ppat_INDUCT,ppat_RECURSION = define_datatype
  "ppat =
     Pp_any
   | Pp_var varN
   | Pp_lit lit
   | Pp_con (((modN,conN)namespace_id) option) (ppat list)
   | Pp_record ((modN,conN)namespace_id) (varN list)
   | Pp_prod (ppat list)
   | Pp_or ppat ppat
   | Pp_tannot ppat ast_t
   | Pp_alias ppat (varN list)
   | Pp_as ppat varN";;

make_size "mlstring";;
make_size "ppat";;
(* the clauses in 6 quotations: a is varN and lit; x is ((modN , conN) id
   option), ((modN , conN) id) and ppat; xs is (ppat list) and (varN list); y
   is ppat, ast_t, (varN list) and varN, which one quotation cannot typecheck
   *)
let ppat_size'_def = define_cases_clauses
  [`(ppat_size' Pp_any = 0) /\
    (ppat_size' (Pp_var a) = 1) /\
    (ppat_size' (Pp_con x xs) = (1 + list_size ppat_size' xs)) /\
    (ppat_size' (Pp_prod xs) = (1 + list_size ppat_size' xs))`;
   `(ppat_size' (Pp_lit a) = 1) /\
    (ppat_size' (Pp_record x xs) = (1 + list_size mlstring_size xs))`;
   `ppat_size' (Pp_or x y) = (1 + ppat_size' x + ppat_size' y)`;
   `ppat_size' (Pp_tannot x y) = (1 + ppat_size' x)`;
   `ppat_size' (Pp_alias x y) = (1 + ppat_size' x)`;
   `ppat_size' (Pp_as x y) = (1 + ppat_size' x)`];;

(* Convert ppat patterns to CakeML patterns by distributing or-patterns at the
 * top-level (returning a list of patterns).
 *
 * Record patterns don't fit this very well, as there is no syntax for them. To
 * make things simple, we only allow them at the top-level, and this function
 * will bail out if it finds one.
 *)

(* the clauses in two quotations: id is ((modN , conN) id option) and ((modN
   , conN) id); pps is (ppat list) and (_)list, which one quotation cannot
   typecheck *)
(* the termination relation that HOL4 gives is
     MEASURE sum_size ppat_size (list_size ppat_size)
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
let ppat_to_pat_def,ppat_to_pat_ind = define_guess_clauses
  [`(ppat_to_pat Pp_any =
      camlPtreeConversion_return [ast_Pany]) /\
    (ppat_to_pat (Pp_var v) =
      camlPtreeConversion_return [ast_Pvar v]) /\
    (ppat_to_pat (Pp_lit l) =
      camlPtreeConversion_return [ast_Plit l]) /\
    (ppat_to_pat (Pp_tannot pp t) =
      camlPtreeConversion_fmap (MAP (\p. ast_Ptannot p t)) (ppat_to_pat
          pp)) /\
    (ppat_to_pat (Pp_con id pps) =
      (OPTION_BIND) (ppat_to_pats pps) (\qs.
        camlPtreeConversion_return (MAP (\ps. ast_Pcon id ps)
            (list_cart_prod qs)))) /\
    (ppat_to_pat (Pp_prod pps) =
      (OPTION_BIND) (ppat_to_pats pps) (\qs.
        camlPtreeConversion_return (MAP (\ps. ast_Pcon NONE ps)
            (list_cart_prod qs)))) /\
    (ppat_to_pat (Pp_alias pp ns) =
      camlPtreeConversion_fmap (MAP (\p. FOLDL ast_Pas p ns))
          (ppat_to_pat pp)) /\
    (ppat_to_pat (Pp_as pp n) =
      camlPtreeConversion_fmap (MAP (\p. ast_Pas p n)) (ppat_to_pat pp)) /\
    (ppat_to_pat (Pp_or p1 p2) =
      (OPTION_BIND) (ppat_to_pat p1) (\ps1. (OPTION_BIND) (ppat_to_pat p2)
          (\ps2.
        camlPtreeConversion_return (APPEND ps1 ps2)))) /\
    (ppat_to_pats [] = camlPtreeConversion_return []) /\
    (ppat_to_pats (CONS p ps) =
      (OPTION_BIND) (ppat_to_pat p) (\p1. (OPTION_BIND) (ppat_to_pats ps)
          (\ps1.
        camlPtreeConversion_return (CONS p1 ps1))))`;
   `ppat_to_pat (Pp_record id fs) =
      NONE (unknown_loc,(implode ""))`];;

(* Fix some constructor applications that needs to be in CakeML's curried
 * style. These are things from basis and Candle; all new constructors will
 * get tupled arguments.
 *)

let compatCurryP_def = new_definition
  `compatCurryP id pat =
     match id with
       Long mn vn ->
         if mn = (implode "PrettyPrinter") /\ vn = Short (implode "PP_Data")
           then
           match pat with
             Pp_con NONE ps -> Pp_con (SOME id) ps
           | _ -> Pp_con (SOME id) [pat]
         else Pp_con (SOME id) [pat]
     | Short nm ->
         if nm = (implode "Abs") \/ nm = (implode "Var") \/ nm = (implode
           "Const") \/ nm = (implode "Comb") \/
            nm = (implode "Tyapp") \/ nm = (implode "Sequent") \/ nm =
              (implode "Append") then
           match pat with Pp_any -> Pp_con (SOME id) [Pp_any; Pp_any]
           | Pp_con NONE ps -> Pp_con (SOME id) ps
           | _ -> Pp_con (SOME id) [pat]
         else Pp_con (SOME id) [pat]`;;

let compatCurryE_def = new_definition
  `compatCurryE id exp =
     match id with
       Long mn vn ->
         if mn = (implode "PrettyPrinter") /\ vn = Short (implode "PP_Data")
           then
           match exp with
             ast_Con NONE xs -> ast_Con (SOME id) xs
           | _ -> ast_Con (SOME id) [exp]
         else ast_Con (SOME id) [exp]
     | Short nm ->
         if nm = (implode "Abs") \/ nm = (implode "Var") \/ nm = (implode
           "Const") \/ nm = (implode "Comb") \/
            nm = (implode "Tyapp") \/ nm = (implode "Sequent") \/ nm =
              (implode "Append") then
           match exp with
             ast_Con NONE xs -> ast_Con (SOME id) xs
           | _ -> ast_Con (SOME id) [exp]
         else if nm = (implode "Ref") then
           ast_App ast_Opref [exp]
         else ast_Con (SOME id) [exp]`;;

(* Rename some constructors from basis that Candle needs (but otherwise cannot
 * parse).
 *)

let compatCons_def = new_definition
  `compatCons cn =
     if cn = (implode "Bad_file_name") then (implode "BadFileName")
     else if cn = (implode "Pp_data") then (implode "PP_Data")
     else cn`;;

(* Rename some module names from basis that Candle needs (but otherwise cannot
 * parse).
 *)

let compatModName_def = new_definition
  `compatModName mn =
     if mn = (implode "Text_io") then (implode "TextIO")
     else if mn = (implode "Pretty_printer") then (implode "PrettyPrinter")
     else if mn = (implode "Command_line") then (implode "CommandLine")
     else if mn = (implode "Word8_array") then (implode "Word8Array")
     else mn`;;

(* -------------------------------------------------------------------------
 * Parse tree conversion
 * ------------------------------------------------------------------------- *)

(* HOL4 camlPtreeConversionScript.sml:264: the overload psize, which the
   port expands *)

(* HOL4 camlPtreeConversionScript.sml:266: the overload p1size, which the
   port expands *)

make_size "parsetree";;
(* [local] *)
let parsetree_size_lemma = prove
 (`p1size = list_size (parsetree_size (K 0) (K 0) (K 0))`,
  CHEAT_TAC);;

let camlPtreeConversion_destLf_def = define_cases
  `(camlPtreeConversion_destLf (Lf x) = camlPtreeConversion_return x) /\
   (camlPtreeConversion_destLf (Nd (nterm,locs) _) = NONE (locs,(implode
    "destLf")))`;;

let expect_tok_def = new_definition
  `expect_tok symb (token:caml_lex_token) =
     (OPTION_BIND) (camlPtreeConversion_destLf symb) (\lf. (OPTION_BIND)
       (camlPtreeConversion_option (tokenUtils_destTOK lf)) (\tk.
       if tk = token then
         camlPtreeConversion_return tk
       else NONE (SND lf,(implode "Unexpected token"))))`;;

let path_to_ns_def,path_to_ns_ind = define_guess
  `path_to_ns locs x2 =
   match x2 with
     [] -> NONE (locs,(implode "Empty path"))
   | [i] -> camlPtreeConversion_return (Short i)
   | CONS m ms ->
     (OPTION_BIND) (path_to_ns locs ms) (\id.
       camlPtreeConversion_return (Long m id))`;;

let ptree_Ident_def = define_cases
  `(ptree_Ident (Lf (_,locs)) = NONE (locs,(implode
    "Expected ident non-terminal"))) /\
   (ptree_Ident (Nd (nterm,locs) args) =
      if nterm = sum_INL camlPEG_nIdent then
        match args with
          [arg] ->
            (OPTION_BIND) (camlPtreeConversion_destLf arg) (\lf.
                (OPTION_BIND) (camlPtreeConversion_option (tokenUtils_destTOK
                lf)) (\tk.
              camlPtreeConversion_option (destIdent tk)))
        | _ -> NONE (locs,(implode "Impossible: nIdent"))
      else NONE (locs,(implode "Expected ident non-terminal")))`;;

(* Returns a (function) name corresponding to the operator.
 *)

let camlPtreeConversion_ptree_Op_def = define_cases
  `(camlPtreeConversion_ptree_Op (Lf (_,locs)) =
      NONE (locs,(implode "Expected operator non-terminal"))) /\
   (camlPtreeConversion_ptree_Op (Nd (nterm,locs) args) =
      match args with
        [arg] ->
          (OPTION_BIND) (camlPtreeConversion_destLf arg) (\lf.
              (OPTION_BIND) (camlPtreeConversion_option (tokenUtils_destTOK
              lf)) (\tk.
            if nterm = sum_INL camlPEG_nShiftOp then
              if tk = caml_lex_LslT then
                camlPtreeConversion_return (implode "lsl")
              else if tk = caml_lex_LsrT then
                camlPtreeConversion_return (implode "lsr")
              else if tk = caml_lex_AsrT then
                camlPtreeConversion_return (implode "asr")
              else if caml_lex_isSymbol tk then
                let s = THE (destSymbol tk) in
                  camlPtreeConversion_return s
              else NONE (locs,(implode "Impossible: nShiftOp"))
            else if nterm = sum_INL camlPEG_nMultOp then
              if tk = caml_lex_StarT then
                camlPtreeConversion_return (implode "*")
              else if tk = caml_lex_ModT then
                camlPtreeConversion_return (implode "mod")
              else if tk = caml_lex_LandT then
                camlPtreeConversion_return (implode "land")
              else if tk = caml_lex_LorT then
                camlPtreeConversion_return (implode "lor")
              else if tk = caml_lex_LxorT then
                camlPtreeConversion_return (implode "lxor")
              else if caml_lex_isSymbol tk then
                let s = THE (destSymbol tk) in
                  camlPtreeConversion_return s
              else NONE (locs,(implode "Impossible: nMultOp"))
            else if nterm = sum_INL camlPEG_nAddOp then
              if tk = caml_lex_PlusT then
                camlPtreeConversion_return (implode "+")
              else if tk = caml_lex_MinusT then
                camlPtreeConversion_return (implode "-")
              else if tk = caml_lex_MinusFT then
                camlPtreeConversion_return (implode "-.")
              else if caml_lex_isSymbol tk then
                let s = THE (destSymbol tk) in
                  camlPtreeConversion_return s
              else NONE (locs,(implode "Impossible: nAddOp"))
            else if nterm = sum_INL camlPEG_nRelOp then
              if tk = caml_lex_LessT then
                camlPtreeConversion_return (implode "<")
              else if tk = caml_lex_GreaterT then
                camlPtreeConversion_return (implode ">")
              else if tk = caml_lex_EqualT then
                camlPtreeConversion_return (implode "=")
              else if caml_lex_isSymbol tk then
                let s = THE (destSymbol tk) in
                  camlPtreeConversion_return s
              else NONE (locs,(implode "Impossible: nRelOp"))
            else if nterm = sum_INL camlPEG_nAndOp then
              if tk = caml_lex_AndalsoT then
                camlPtreeConversion_return (implode "&&")
              else if tk = caml_lex_AmpT then
                camlPtreeConversion_return (implode "&")
              else if caml_lex_isSymbol tk then
                let s = THE (destSymbol tk) in
                  camlPtreeConversion_return s
              else NONE (locs,(implode "Impossible: nAndOp"))
            else if nterm = sum_INL camlPEG_nOrOp then
              if tk = caml_lex_OrelseT then
                camlPtreeConversion_return (implode "||")
              else if tk = caml_lex_OrT then
                camlPtreeConversion_return (implode "|")
              else if caml_lex_isSymbol tk then
                let s = THE (destSymbol tk) in
                  camlPtreeConversion_return s
              else NONE (locs,(implode "Impossible: nOrOp"))
            else if nterm = sum_INL camlPEG_nHolInfixOp then
              if tk = caml_lex_FuncompT then
                camlPtreeConversion_return (implode "o")
              else if tk = caml_lex_F_FT then
                camlPtreeConversion_return (implode "F_F")
              else if tk = caml_lex_THEN_T then
                camlPtreeConversion_return (implode "THEN")
              else if tk = caml_lex_THENC_T then
                camlPtreeConversion_return (implode "THENC")
              else if tk = caml_lex_THENL_T then
                camlPtreeConversion_return (implode "THENL")
              else if tk = caml_lex_THEN_TCL_T then
                camlPtreeConversion_return (implode "THEN_TCL")
              else if tk = caml_lex_ORELSE_T then
                camlPtreeConversion_return (implode "ORELSE")
              else if tk = caml_lex_ORELSEC_T then
                camlPtreeConversion_return (implode "ORELSEC")
              else if tk = caml_lex_ORELSE_TCL_T then
                camlPtreeConversion_return (implode "ORELSE_TCL")
              else NONE (locs,(implode "Impossible: nHolInfixOp"))
            else if nterm = sum_INL camlPEG_nCatOp then
              if caml_lex_isSymbol tk then
                let s = THE (destSymbol tk) in
                  camlPtreeConversion_return s
              else NONE (locs,(implode "Impossible: nCatOp"))
            else if nterm = sum_INL camlPEG_nPrefixOp then
              if caml_lex_isSymbol tk then
                let s = THE (destSymbol tk) in
                  camlPtreeConversion_return s
              else NONE (locs,(implode "Impossible: nPrefixOp"))
            else if nterm = sum_INL camlPEG_nAssignOp then
              if tk = caml_lex_LarrowT then
                camlPtreeConversion_return (implode "<-")
              else if tk = caml_lex_UpdateT then
                camlPtreeConversion_return (implode ":=")
              else NONE (locs,(implode "Impossible: nAssignOp"))
            else NONE (locs,(implode "Expected operator non-terminal"))))
      | _ -> NONE (locs,(implode "Expected operator non-terminal")))`;;

let ptree_OperatorName_def = define_cases
  `(ptree_OperatorName (Lf (_,locs)) =
      NONE (locs,(implode "Expected operator-name non-terminal"))) /\
   (ptree_OperatorName (Nd (nterm,locs) args) =
      if nterm = sum_INL camlPEG_nOperatorName then
        match args with
          [arg] -> camlPtreeConversion_ptree_Op arg
        | _ -> NONE (locs,(implode "Impossible: nOperatorName"))
      else NONE (locs,(implode "Expected operator-name non-terminal")))`;;

let ptree_ValueName_def = define_cases
  `(ptree_ValueName (Lf (_,locs)) =
      NONE (locs,(implode "Expected value-name non-terminal"))) /\
   (ptree_ValueName (Nd (nterm,locs) args) =
      if nterm = sum_INL camlPEG_nValueName then
        match args with
          [arg] ->
            (OPTION_BIND) (camlPtreeConversion_destLf arg) (\lf.
                (OPTION_BIND) (camlPtreeConversion_option (tokenUtils_destTOK
                lf)) (\tk.
              camlPtreeConversion_option (destIdent tk)))
        | [lpar; opn; rpar] ->
              monad_ignore_bind (expect_tok lpar caml_lex_LparT) (
              monad_ignore_bind (expect_tok rpar caml_lex_RparT) (
              ptree_OperatorName opn))
        | _ -> NONE (locs,(implode "Impossible: nValueName"))
      else NONE (locs,(implode "Expected value-name non-terminal")))`;;

let ptree_ConstrName_def = define_cases
  `(ptree_ConstrName (Lf (_,locs)) =
      NONE (locs,(implode "Expected constr-name non-terminal"))) /\
   (ptree_ConstrName (Nd (nterm,locs) args) =
      if nterm = sum_INL camlPEG_nConstrName then
        match args with
          [arg] ->
            (OPTION_BIND) (camlPtreeConversion_destLf arg) (\lf.
                (OPTION_BIND) (camlPtreeConversion_option (tokenUtils_destTOK
                lf)) (\tk.
              camlPtreeConversion_fmap compatCons
                  (camlPtreeConversion_option (destIdent tk))))
        | _ -> NONE (locs,(implode "Impossible: nConstrName"))
      else NONE (locs,(implode "Expected constr-name non-terminal")))`;;

let ptree_TypeConstrName_def = define_cases
  `(ptree_TypeConstrName (Lf (_,locs)) =
      NONE (locs,(implode "Expected typeconstr-name non-terminal"))) /\
   (ptree_TypeConstrName (Nd (nterm,locs) args) =
      if nterm = sum_INL camlPEG_nTypeConstrName then
        match args with
          [arg] ->
            (OPTION_BIND) (camlPtreeConversion_destLf arg) (\lf.
                (OPTION_BIND) (camlPtreeConversion_option (tokenUtils_destTOK
                lf)) (\tk.
              camlPtreeConversion_option (destIdent tk)))
        | _ -> NONE (locs,(implode "Impossible: nTypeConstrName"))
      else NONE (locs,(implode
          "Expected typeconstr-name non-terminal")))`;;

let ptree_FieldName_def = define_cases
  `(ptree_FieldName (Lf (_,locs)) =
      NONE (locs,(implode "Expected fieldname non-terminal"))) /\
   (ptree_FieldName (Nd (nterm,locs) args) =
      if nterm = sum_INL camlPEG_nFieldName then
        match args with
          [arg] ->
            (OPTION_BIND) (camlPtreeConversion_destLf arg) (\lf.
                (OPTION_BIND) (camlPtreeConversion_option (tokenUtils_destTOK
                lf)) (\tk.
              camlPtreeConversion_option (destIdent tk)))
        | _ -> NONE (locs,(implode "Impossible: nFieldName"))
      else NONE (locs,(implode "Expected fieldname non-terminal")))`;;

let ptree_ModuleName_def = define_cases
  `(ptree_ModuleName (Lf (_,locs)) =
      NONE (locs,(implode "Expected modulename non-terminal"))) /\
   (ptree_ModuleName (Nd (nterm,locs) args) =
      if nterm = sum_INL camlPEG_nModuleName then
        match args with
          [arg] ->
            (OPTION_BIND) (camlPtreeConversion_destLf arg) (\lf.
                (OPTION_BIND) (camlPtreeConversion_option (tokenUtils_destTOK
                lf)) (\tk.
              camlPtreeConversion_fmap compatModName
                  (camlPtreeConversion_option (destIdent tk))))
        | _ -> NONE (locs,(implode "Impossible: nModuleName"))
      else NONE (locs,(implode "Expected modulename non-terminal")))`;;

let ptree_ModTypeName_def = define_cases
  `(ptree_ModTypeName (Lf (_,locs)) =
      NONE (locs,(implode "Expected modtypename non-terminal"))) /\
   (ptree_ModTypeName (Nd (nterm,locs) args) =
      if nterm = sum_INL camlPEG_nModTypeName then
        match args with
          [arg] ->
            (OPTION_BIND) (camlPtreeConversion_destLf arg) (\lf.
                (OPTION_BIND) (camlPtreeConversion_option (tokenUtils_destTOK
                lf)) (\tk.
              camlPtreeConversion_option (destIdent tk)))
        | _ -> NONE (locs,(implode "Impossible: nModTypeName"))
      else NONE (locs,(implode "Expected modtypename non-terminal")))`;;

let ptree_ModulePath_def,ptree_ModulePath_ind = define_guess
  `(ptree_ModulePath (Lf (_,locs)) =
      NONE (locs,(implode "Expected module-path non-terminal"))) /\
   (ptree_ModulePath (Nd (nterm,locs) args) =
      if nterm = sum_INL camlPEG_nModulePath then
        match args with
          [arg] -> camlPtreeConversion_fmap (\x. [x]) (ptree_ModuleName
              arg)
        | [arg; dot; path] ->
              monad_ignore_bind (expect_tok dot caml_lex_DotT)
                  ((OPTION_BIND) (ptree_ModulePath path) (\vp. (OPTION_BIND)
                  (ptree_ModuleName arg) (\vn.
              camlPtreeConversion_return (CONS vn vp))))
        | _ -> NONE (locs,(implode "Impossible: nModulePath"))
      else NONE (locs,(implode "Expected module-path non-terminal")))`;;

let ptree_ValuePath_def = define_cases
  `(ptree_ValuePath (Lf (_,locs)) =
      NONE (locs,(implode "Expected value-path non-terminal"))) /\
   (ptree_ValuePath (Nd (nterm,locs) args) =
      if nterm = sum_INL camlPEG_nValuePath then
        match args with
          [arg] -> camlPtreeConversion_fmap (\x. [x]) (ptree_ValueName arg)
        | [path; dot; arg] ->
              monad_ignore_bind (expect_tok dot caml_lex_DotT)
                  ((OPTION_BIND) (ptree_ModulePath path) (\vp. (OPTION_BIND)
                  (ptree_ValueName arg) (\vn.
              camlPtreeConversion_return (APPEND vp [vn]))))
        | _ -> NONE (locs,(implode "Impossible: nValuePath"))
      else NONE (locs,(implode "Expected value-path non-terminal")))`;;

let ptree_Constr_def,ptree_Constr_ind = define_guess
  `(ptree_Constr (Lf (_,locs)) = NONE (locs,(implode
    "Expected constr non-terminal"))) /\
   (ptree_Constr (Nd (nterm,locs) args) =
      if nterm = sum_INL camlPEG_nConstr then
        match args with
          [arg] -> camlPtreeConversion_fmap (\x. [x]) (ptree_ConstrName
              arg)
        | [name; dot; rest] ->
              monad_ignore_bind (expect_tok dot caml_lex_DotT)
                  ((OPTION_BIND) (ptree_ModuleName name) (\vp. (OPTION_BIND)
                  (ptree_Constr rest) (\vn.
              camlPtreeConversion_return (CONS vp vn))))
        | _ -> NONE (locs,(implode "Impossible: nConstr"))
      else NONE (locs,(implode "Expected constr non-terminal")))`;;

let ptree_TypeConstr_def = define_cases
  `(ptree_TypeConstr (Lf (_,locs)) =
      NONE (locs,(implode "Expected typeconstr non-terminal"))) /\
   (ptree_TypeConstr (Nd (nterm,locs) args) =
      if nterm = sum_INL camlPEG_nTypeConstr then
        match args with
          [arg] -> camlPtreeConversion_fmap (\x. [x]) (ptree_TypeConstrName
              arg)
        | [path; dot; arg] ->
              monad_ignore_bind (expect_tok dot caml_lex_DotT)
                  ((OPTION_BIND) (ptree_ModulePath path) (\vp. (OPTION_BIND)
                  (ptree_TypeConstrName arg) (\vn.
              camlPtreeConversion_return (APPEND vp [vn]))))
        | _ -> NONE (locs,(implode "Impossible: nTypeConstr"))
      else NONE (locs,(implode "Expected typeconstr non-terminal")))`;;

let ptree_ModTypePath_def,ptree_ModTypePath_ind = define_guess
  `(ptree_ModTypePath (Lf (_,locs)) =
      NONE (locs,(implode "Expected modtypepath non-terminal"))) /\
   (ptree_ModTypePath (Nd (nterm,locs) args) =
      if nterm = sum_INL camlPEG_nModTypePath then
        match args with
          [arg] -> camlPtreeConversion_fmap (\vn. [vn]) (ptree_ModTypeName
              arg)
        | [name; dot; rest] ->
              monad_ignore_bind (expect_tok dot caml_lex_DotT)
                  ((OPTION_BIND) (ptree_ModuleName name) (\vm. (OPTION_BIND)
                  (ptree_ModTypePath rest) (\vp.
              camlPtreeConversion_return (CONS vm vp))))
        | _ -> NONE (locs,(implode "Impossible: nModTypePath"))
      else NONE (locs,(implode "Expected typeconstr non-terminal")))`;;

let ptree_TVar_def = define_cases
  `(ptree_TVar (Lf (_,locs)) =
      NONE (locs,(implode "Expected type variable non-terminal"))) /\
   (ptree_TVar (Nd (nterm,locs) args) =
      if nterm = sum_INL camlPEG_nTVar then
        match args with
          [tick; id] ->
              monad_ignore_bind (expect_tok tick caml_lex_TickT)
                  ((OPTION_BIND) (ptree_Ident id) (\nm.
              camlPtreeConversion_return (Atvar nm)))
        | _ -> NONE (locs,(implode "Impossible: nTVar"))
      else NONE (locs,(implode "Expected type variable non-terminal")))`;;

(* the clauses in two quotations: args is (parsetree list) and parsetree,
   which one quotation cannot typecheck *)
(* the termination relation that HOL4 gives is
     MEASURE (sum_size (parsetree_size (K 0) (K 0) (K 0))
                                (sum_size (parsetree_size (K 0) (K 0) (K 0))
                                  (list_size (parsetree_size (K 0) (K 0) (K
                                    0)))))
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 camlPtreeConversionScript.sml:784-788: the tactic that proves the
   termination *)
let camlPtreeConversion_ptree_Type_def,camlPtreeConversion_ptree_Type_ind =
  define_guess_clauses
  [`(camlPtreeConversion_ptree_Type (Lf (_,locs)) =
        NONE (locs,(implode "Expected a type non-terminal"))) /\
    (ptree_TypeList (Lf (_,locs)) =
        NONE (locs,(implode "Expected a type list non-terminal"))) /\
    (ptree_TypeList (Nd (nterm,locs) args) =
        if nterm = sum_INL camlPEG_nTypeList then
          match args with
            [typ; comma; tlist] ->
              (OPTION_BIND) (camlPtreeConversion_ptree_Type typ) (\t.
                monad_ignore_bind (expect_tok comma caml_lex_CommaT)
                    ((OPTION_BIND) (ptree_TypeList tlist) (\ts.
                camlPtreeConversion_return (CONS t ts))))
          | _ -> NONE (locs,(implode "Impossible: nTypeList"))
        else if nterm = sum_INL camlPEG_nTypeLists then
          match args with
            [typ; comma; tlist] ->
              (OPTION_BIND) (camlPtreeConversion_ptree_Type typ) (\t.
                monad_ignore_bind (expect_tok comma caml_lex_CommaT)
                    ((OPTION_BIND) (ptree_TypeList tlist) (\ts.
                camlPtreeConversion_return (CONS t ts))))
          | [typ] -> camlPtreeConversion_fmap (\t. [t])
              (camlPtreeConversion_ptree_Type typ)
          | _ -> NONE (locs,(implode "Impossible: nTypeLists"))
        else NONE (locs,(implode "Expected a type list non-terminal"))) /\
    (ptree_StarTypes [] = camlPtreeConversion_return []) /\
    (ptree_StarTypes (CONS x xs) = APPEND (
          monad_ignore_bind (expect_tok x caml_lex_StarT) (
          ptree_StarTypes xs))
        ((OPTION_BIND) (camlPtreeConversion_ptree_Type x) (\t.
            (OPTION_BIND) (ptree_StarTypes xs) (\ts.
          camlPtreeConversion_return (CONS t ts)))))`;
   `camlPtreeConversion_ptree_Type (Nd (nterm,locs) args) =
        if nterm = sum_INL camlPEG_nType then
          match args with
            [ty] -> camlPtreeConversion_ptree_Type ty
          | _ -> NONE (locs,(implode "Impossible: nType"))
        else if nterm = sum_INL camlPEG_nTBase then
          match args with
            [lpar; args; rpar; ctor] ->
                monad_ignore_bind (expect_tok lpar caml_lex_LparT) (
                monad_ignore_bind (expect_tok rpar caml_lex_RparT)
                    ((OPTION_BIND) (ptree_TypeList args) (\ts. (OPTION_BIND)
                    (ptree_TypeConstr ctor) (\nm. (OPTION_BIND) (path_to_ns
                    locs nm) (\ns.
                camlPtreeConversion_return (Atapp ts ns))))))
          | [lpar; arg; rpar] ->
                monad_ignore_bind (expect_tok lpar caml_lex_LparT) (
                monad_ignore_bind (expect_tok rpar caml_lex_RparT) (
                camlPtreeConversion_ptree_Type arg))
          | [arg] ->
              ptree_TVar arg
          | _ -> NONE (locs,(implode "Impossible: nTBase"))
        else if nterm = sum_INL camlPEG_nTConstr then
          match args with CONS arg rest -> APPEND ((OPTION_BIND)
              (camlPtreeConversion_ptree_Type arg) (\ty. (OPTION_BIND)
              (camlPtreeConversion_mapM ptree_TypeConstr rest) (\ids.
              (OPTION_BIND) (camlPtreeConversion_mapM (path_to_ns locs) ids)
              (\cns.
                camlPtreeConversion_return (FOLDL (\t id. Atapp [t] id) ty
                    cns)))))
              ((OPTION_BIND) (ptree_TypeConstr arg) (\id. (OPTION_BIND)
                  (path_to_ns locs id) (\cn. (OPTION_BIND)
                  (camlPtreeConversion_mapM ptree_TypeConstr rest) (\ids.
                  (OPTION_BIND) (camlPtreeConversion_mapM (path_to_ns locs)
                  ids) (\cns.
                camlPtreeConversion_return (FOLDL (\t id. Atapp [t] id)
                    (Atapp [] cn) cns))))))
          | _ -> NONE (locs,(implode "Impossible: nTConstr"))
        else if nterm = sum_INL camlPEG_nTProd then
          match args with
            [arg] -> camlPtreeConversion_ptree_Type arg
          | CONS arg rest ->
              (OPTION_BIND) (camlPtreeConversion_ptree_Type arg) (\ty.
                  (OPTION_BIND) (ptree_StarTypes rest) (\ts.
                camlPtreeConversion_return (Attup (CONS ty ts))))
          | _ -> NONE (locs,(implode "Impossible: nTProd"))
        else if nterm = sum_INL camlPEG_nTFun then
          match args with
            [arg] -> camlPtreeConversion_ptree_Type arg
          | [arg; rarrow; fun'] ->
                monad_ignore_bind (expect_tok rarrow caml_lex_RarrowT)
                    ((OPTION_BIND) (camlPtreeConversion_ptree_Type arg) (\ty1.
                    (OPTION_BIND) (camlPtreeConversion_ptree_Type fun') (\ty2.
                camlPtreeConversion_return (Atfun ty1 ty2))))
          | _ -> NONE (locs,(implode "Impossible: nTFun"))
        else NONE (locs,(implode "Expected type non-terminal"))`];;

let ptree_Literal_def = define_cases
  `(ptree_Literal (Lf (_,locs)) =
      NONE (locs,(implode "Expected a literal non-terminal"))) /\
   (ptree_Literal (Nd (nterm,locs) args) =
      if nterm = sum_INL camlPEG_nLiteral then
        match args with
          [arg] ->
            (OPTION_BIND) (camlPtreeConversion_destLf arg) (\lf.
                (OPTION_BIND) (camlPtreeConversion_option (tokenUtils_destTOK
                lf)) (\tk.
              if caml_lex_isInt tk then
                camlPtreeConversion_return (ast_IntLit (THE (destInt tk)))
              else if isChar tk then
                camlPtreeConversion_return (ast_Char (THE (destChar tk)))
              else if caml_lex_isString tk then
                camlPtreeConversion_return (ast_StrLit (THE (destString
                    tk)))
              else NONE (locs,(implode "Impossible: nLiteral"))))
        | _ -> NONE (locs,(implode "Impossible: nLiteral"))
      else NONE (locs,(implode "Expected a literal non-terminal")))`;;

let bool2id_def = new_definition
  `bool2id b = Short (if b then (implode "True") else (implode "False"))`;;

let ptree_Bool_def = define_cases
  `(ptree_Bool (Lf (_,locs)) =
      NONE (locs,(implode "Expected a boolean literal non-terminal"))) /\
   (ptree_Bool (Nd (nterm,locs) args) =
      if nterm = sum_INL camlPEG_nLiteral then
        match args with
          [arg] ->
            (OPTION_BIND) (camlPtreeConversion_destLf arg) (\lf.
                (OPTION_BIND) (camlPtreeConversion_option (tokenUtils_destTOK
                lf)) (\tk.
              if tk = caml_lex_TrueT \/ tk = caml_lex_FalseT then
                camlPtreeConversion_return (bool2id (tk = caml_lex_TrueT))
              else NONE (locs,(implode "not a boolean literal"))))
        | _ -> NONE (locs,(implode "Impossible: nLiteral (bool)"))
      else NONE (locs,(implode
          "Expected a boolean literal non-terminal")))`;;

let ptree_Double_def = define_cases
  `(ptree_Double (Lf (_,locs)) =
      NONE (locs,(implode "Expected a float literal non-terminal"))) /\
   (ptree_Double (Nd (nterm,locs) args) =
      if nterm = sum_INL camlPEG_nLiteral then
        match args with
          [arg] ->
            (OPTION_BIND) (camlPtreeConversion_destLf arg) (\lf.
                (OPTION_BIND) (camlPtreeConversion_option (tokenUtils_destTOK
                lf)) (\tk.
              if isFloat tk then
                camlPtreeConversion_return (ast_Lit (ast_StrLit (THE
                    (destFloat tk))))
              else NONE (locs,(implode "not a float literal"))))
        | _ -> NONE (locs,(implode "Impossible: nLiteral (float)"))
      else NONE (locs,(implode
          "Expected a float literal non-terminal")))`;;

let nterm_of_def,nterm_of_ind = define_guess
  `(nterm_of (Lf (_,locs)) = NONE (locs,(implode
    "nterm_of: Not a parsetree node"))) /\
   (nterm_of (Nd (nterm,_) args) = camlPtreeConversion_return nterm)`;;

(* This code was adapted from the following parser code in the pure repository:
 * github.com/CakeML/pure/blob/master/compiler/parsing/cst_to_astScript.sml
 *)

(* HOL4 camlPtreeConversionScript.sml:867: ML code, not ported *)

let prec_INDUCT,prec_RECURSION = define_datatype
  "prec =
     Left
   | Right
   | NonAssoc";;

let pp_op_INDUCT,pp_op_RECURSION = define_datatype
  "pp_op =
     po_cons
   | po_prod
   | po_or
   | po_alias";;

let tokprec_def = new_definition
  `(tokprec op:(num#prec) option) = SOME
     (match op with
       po_cons -> (3,Right)
     | po_prod -> (2,Left)
     | po_or -> (1,Left)
     | po_alias -> (0,NonAssoc))`;;

let tok_action_def = new_definition
  `tok_action x1 =
   match x1 with
     sum_INL stktok,sum_INL inptok ->
     OPTION_BIND (tokprec stktok) (\(stkprec,stka). OPTION_BIND (tokprec
       inptok) (\(inpprec,inpa).
       if stka = NonAssoc then SOME precparser_Reduce
       else
        // only po_alias
        if inpprec < stkprec then SOME precparser_Reduce
       else if stkprec < inpprec then SOME ast_Shift
       else if ~(stka = inpa) \/ stka = NonAssoc then NONE
       else if stka = Left then SOME precparser_Reduce
       else SOME ast_Shift))
   | _ -> NONE`;;

(* HOL4 camlPtreeConversionScript.sml:901: ML code, not ported *)

(* Alias-patterns collapse into a pattern, an operator, and an identifier list.
 *)

let dest_alias_def = new_definition
  `dest_alias pp =
     match pp with
       Pp_alias pp ns -> SOME (pp,ns)
     | _ -> NONE`;;

let tok2ppo = new_definition
  `tok2ppo pt =
     OPTION_BIND (camlPtreeConversion_destLf pt) (\lf. OPTION_BIND
       (camlPtreeConversion_option (tokenUtils_destTOK lf)) (\tk.
       if tk = caml_lex_ColonsT then
         SOME po_cons
       else if tk = caml_lex_CommaT then
         SOME po_prod
       else if tk = caml_lex_BarT then
         SOME po_or
       else NONE (unknown_loc,(implode "ppatOp: impossible"))))`;;

(* tok: pp_op + (ppat + varN list)
 * trm: ppat + varN list
 *)

let ppat_close_def = new_definition
  `ppat_close pps =
   match pps with
     Pp_prod pps -> Pp_con NONE pps
   | Pp_alias pp vs -> FOLDL Pp_as pp vs
   | pps -> pps`;;

let ppat_reduce_def = new_definition
  `ppat_reduce a op b =
     match op with
       sum_INL po_or ->
         (match (a,b) with
            (sum_INL x,sum_INL y) -> SOME (sum_INL (Pp_or (ppat_close x) y))
          | _ -> NONE)
     | sum_INL po_prod ->
         (match (a,b) with
            (sum_INL (Pp_prod ps),sum_INL y) -> SOME (sum_INL (Pp_prod
              (APPEND ps [y])))
          | (sum_INL x,sum_INL y) -> SOME (sum_INL (Pp_prod [x; y]))
          | _ -> NONE)
     | sum_INL po_cons ->
         (match (a,b) with
            (sum_INL x,sum_INL y) ->
              SOME (sum_INL (Pp_con (SOME (Short (implode "::")))
                [ppat_close x; y]))
          | _ -> NONE)
     | sum_INL po_alias ->
         (match (a,b) with
            (sum_INL x,sum_INR y) -> SOME (sum_INL (Pp_alias (ppat_close x)
              y))
          | _ -> NONE)
     | _ -> NONE`;;

let resolve_precs_def,resolve_precs_ind = define_guess
  `resolve_precs xs =
     match precparse (mk_pMachine (\x. tok_action x) (\x op y. ppat_reduce x
       op y) (\x. match x with sum_INR y -> y | _ -> sum_INR []) (\x. ISL x)
       (\x y. NONE)) ([],xs) with
       SOME (sum_INL ppat) -> SOME (ppat_close ppat)
     | _ -> NONE (unknown_loc,(implode "resolve_precs"))
   // All x's should be INR's`;;

let ptree_AsIds_def,ptree_AsIds_ind = define_guess
  `(ptree_AsIds [] = SOME []) /\
   (ptree_AsIds [_] = NONE (unknown_loc,(implode
    "Impossible: ptree_AsIds"))) /\
   (ptree_AsIds (CONS x (CONS y xs)) =
        OPTION_IGNORE_BIND (expect_tok x caml_lex_AsT) (OPTION_BIND
            (ptree_Ident y) (\n. OPTION_BIND (ptree_AsIds xs) (\ns.
        SOME (CONS n ns)))))`;;

(* Turns a list literal pattern “[x; y; z]” into the
 * constructor pattern “x::y::z::[]”.
 *)

let build_list_ppat_def = new_definition
  `build_list_ppat =
     FOLDR (\t p. Pp_con (SOME (Short (implode "::"))) [t; p])
           (Pp_con (SOME (Short (implode "[]"))) [])`;;

let ptree_FieldsList_def,ptree_FieldsList_ind = define_guess
  `ptree_FieldsList x1 =
     match x1 with
       [rbrace] ->
         OPTION_IGNORE_BIND (expect_tok rbrace caml_lex_RbraceT) (
         SOME [])
     | [semi; rbrace] ->
         OPTION_IGNORE_BIND (expect_tok semi caml_lex_SemiT) (
         OPTION_IGNORE_BIND (expect_tok rbrace caml_lex_RbraceT) (
         SOME []))
     | CONS semi (CONS fname fs) ->
         OPTION_IGNORE_BIND (expect_tok semi caml_lex_SemiT) (OPTION_BIND
           (ptree_FieldName fname) (\fn. OPTION_BIND (ptree_FieldsList fs)
           (\fns.
         SOME (CONS fn fns))))
     | [] -> NONE (unknown_loc,(implode "Impossible: ptree_FieldsList"))`;;

let ptree_PRecFields_def = define_cases
  `(ptree_PRecFields (Lf (_,locs)) =
        NONE (locs,(implode
            "Expected a pattern record fields non-terminal"))) /\
   (ptree_PRecFields (Nd (nterm,locs) args) =
        if nterm = sum_INL camlPEG_nPRecFields then
          match args with CONS lbrace (CONS fname rest) ->
                OPTION_IGNORE_BIND (expect_tok lbrace caml_lex_LbraceT)
                    (OPTION_BIND (ptree_FieldName fname) (\fn. OPTION_BIND
                    (ptree_FieldsList rest) (\fns.
                SOME (CONS fn fns))))
          | _ -> NONE (locs,(implode "Impossible: nPRecFields"))
        else NONE (locs,(implode
            "Expected a pattern record fields non-terminal")))`;;

(* the termination relation that HOL4 gives is
     MEASURE
                              (sum_size (parsetree_size (K 0) (K 0) (K 0))
                              (sum_size (list_size (parsetree_size (K 0) (K 0)
                                (K 0))) (pair_size ((K 0)) (list_size
                                (parsetree_size (K 0) (K 0) (K 0))))))
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 camlPtreeConversionScript.sml:1201-1206: the tactic that proves the
   termination *)
let ptree_PPattern_def,ptree_PPattern_ind = define_guess
  `(ptree_PPattern (Lf (_,locs)) =
        NONE (locs,(implode "Expected a pattern non-terminal"))) /\
   (ptree_PPattern (Nd (nterm,locs) args) =
        if nterm = sum_INL camlPEG_nPAny then
          match args with
            [arg] ->
                OPTION_IGNORE_BIND (expect_tok arg caml_lex_AnyT) (
                SOME Pp_any)
          | _ -> NONE (locs,(implode "Impossible: nPAny"))
        else if nterm = sum_INL camlPEG_nPList then
          match args with CONS lbrack rest ->
                OPTION_IGNORE_BIND (expect_tok lbrack caml_lex_LbrackT)
                    (OPTION_BIND (ptree_PPatternList rest) (\ps.
                SOME (build_list_ppat ps)))
          | _ -> NONE (locs,(implode "Impossible: nPList"))
        else if nterm = sum_INL camlPEG_nPPar then
          match args with
            [l; r] ->
                OPTION_IGNORE_BIND (expect_tok l caml_lex_LparT) (
                OPTION_IGNORE_BIND (expect_tok r caml_lex_RparT) (
                SOME (Pp_con NONE [])))
          | [l; p; r] ->
                OPTION_IGNORE_BIND (expect_tok l caml_lex_LparT) (
                OPTION_IGNORE_BIND (expect_tok r caml_lex_RparT) (
                ptree_PPattern p))
          | [lpar; pat; colon; typ; rpar] ->
                OPTION_IGNORE_BIND (expect_tok lpar caml_lex_LparT) (
                OPTION_IGNORE_BIND (expect_tok rpar caml_lex_RparT) (
                OPTION_IGNORE_BIND (expect_tok colon caml_lex_ColonT)
                    (OPTION_BIND (ptree_PPattern pat) (\p. OPTION_BIND
                    (camlPtreeConversion_ptree_Type typ) (\ty.
                SOME (Pp_tannot p ty))))))
          | _ -> NONE (locs,(implode "Impossible: nPPar"))
        else if nterm = sum_INL camlPEG_nPatLiteral then
          match args with
            [arg] -> APPEND (camlPtreeConversion_fmap Pp_lit (ptree_Literal
                arg))
              (camlPtreeConversion_fmap (\b. Pp_con (SOME b) [])
                  (ptree_Bool arg))
          | [minus'; arg] ->
                OPTION_IGNORE_BIND (expect_tok minus' caml_lex_MinusT)
                    (OPTION_BIND (camlPtreeConversion_destLf arg) (\lf.
                    OPTION_BIND (camlPtreeConversion_option (tokenUtils_destTOK
                    lf)) (\tk.
                if caml_lex_isInt tk then
                  SOME (Pp_lit (ast_IntLit (--(THE (destInt tk)))))
                else NONE (locs,(implode "Impossible: nPatLiteral")))))
          | _ -> NONE (locs,(implode "Impossible: nPatLiteral"))
        else if nterm = sum_INL camlPEG_nPBase then
          match args with
            [arg] ->
              OPTION_BIND (nterm_of arg) (\n.
                if n = sum_INL camlPEG_nValueName then
                  camlPtreeConversion_fmap Pp_var (ptree_ValueName arg)
                else if n = sum_INL camlPEG_nConstr then
                  OPTION_BIND (ptree_Constr arg) (\cns. OPTION_BIND
                      (path_to_ns locs cns) (\id.
                    SOME (Pp_con (SOME id) [])))
                else if n = sum_INL camlPEG_nPatLiteral \/ n = sum_INL
                    camlPEG_nPAny \/ n = sum_INL camlPEG_nPList \/
                        n = sum_INL camlPEG_nPPar then
                  ptree_PPattern arg
                else NONE (locs,(implode "Impossible: nPBase")))
          | _ -> NONE (locs,(implode "Impossible: nPBase"))
        else if nterm = sum_INL camlPEG_nPCons then
          match args with
            [cn] -> APPEND (OPTION_BIND (ptree_Constr cn) (\cns.
                OPTION_BIND (path_to_ns locs cns) (\id.
                SOME (Pp_con (SOME id) [])))) (ptree_PPattern cn)
          | [cn; arg] -> APPEND (OPTION_BIND (ptree_Constr cn) (\cns.
              OPTION_BIND (path_to_ns locs cns) (\id. OPTION_BIND
              (ptree_PRecFields arg) (\fs.
                SOME (Pp_record id fs)))))
              (OPTION_BIND (ptree_Constr cn) (\cns. OPTION_BIND (path_to_ns
                  locs cns) (\id. OPTION_BIND (ptree_PPattern arg) (\p.
                SOME (compatCurryP id p)))))
          | _ -> NONE (locs,(implode "Impossible: nPCons"))
        else if nterm = sum_INL camlPEG_nPAs then
          match args with CONS pat asids ->
              OPTION_BIND (ptree_PPattern pat) (\p. OPTION_BIND
                  (ptree_AsIds asids) (\nms.
                match nms with
                  [] -> SOME p
                | _ -> SOME (Pp_alias p nms)))
          | _ -> NONE (locs,(implode "Impossible: nPAs"))
        else if nterm = sum_INL camlPEG_nPOps then
          match args with
            [] -> NONE (locs,(implode "Impossible: nPOps"))
          | CONS pat rest ->
              OPTION_BIND (ptree_PPattern pat) (\p. OPTION_IGNORE_BIND (
                start << --(match dest_alias p with
                            NONE -> [sum_INR (sum_INL p)]
                          | SOME (pp,ns) ->
                              [sum_INR (sum_INR ns); sum_INL po_alias;
                                  sum_INR (sum_INL pp)])) (OPTION_BIND
                                  (grabPairs start rest) (\precs.
                resolve_precs precs)))
        else if nterm = sum_INL camlPEG_nPattern then
          match args with
            [pat] -> ptree_PPattern pat
          | _ -> NONE (locs,(implode "Impossible: nPattern"))
        else NONE (locs,(implode "Expected a pattern non-terminal"))) /\
   (ptree_PPatternList [] =
        NONE (unknown_loc,(implode "Pattern lists cannot be empty"))) /\
   (ptree_PPatternList [t] =
           OPTION_IGNORE_BIND (expect_tok t caml_lex_RbrackT) (
           SOME [])) /\
   (ptree_PPatternList (CONS p ps) = APPEND (
           OPTION_IGNORE_BIND (expect_tok p caml_lex_SemiT) (
           ptree_PPatternList ps))
         (OPTION_BIND (ptree_PPattern p) (\q. OPTION_BIND
             (ptree_PPatternList ps) (\qs.
           SOME (CONS q qs))))) /\
   (grabPairs A [] = SOME (REVERSE A)) /\
   (grabPairs A [_] = NONE (unknown_loc,(implode "grabPairs"))) /\
   (grabPairs A (CONS pt1 (CONS pt2 rest)) =
        OPTION_BIND (tok2ppo pt1) (\opv. OPTION_BIND (ptree_PPattern pt2)
            (\v.
          match dest_alias v with
            SOME (pp,ns) ->
              grabPairs (CONS (sum_INR (sum_INR ns)) (CONS (sum_INL
                  po_alias) (CONS (sum_INR (sum_INL pp)) (CONS (sum_INL opv)
                  A))))
                        rest
          | _ -> grabPairs (CONS (sum_INR (sum_INL v)) (CONS (sum_INL
              opv) A)) rest)))`;;

(* HOL4 camlPtreeConversionScript.sml:1208-1209: a theorem that HOL4 states
   as the value of an ML expression: ptree_PPattern_ind *)

(* The pattern parser functions return INL for record patterns, and INR for
 * real patterns. Record patterns do not have a counterpart in the :pat type,
 * so we perform some bookkeeping here.
 *
 * To simplify matters, we don't accept record patterns anywhere but at the
 * top-level. The function ppat_to_pat fails if it encounters a record pattern.
 * We convert record patterns directly in this function instead.
 *)

let camlPtreeConversion_ptree_Pattern_def = new_definition
  `camlPtreeConversion_ptree_Pattern p =
     OPTION_BIND (ptree_PPattern p) (\pp.
       match pp with
         Pp_record id fs -> SOME [sum_INL (id,fs)]
       |
         // record
         _ -> APPEND (OPTION_BIND (ppat_to_pat pp) (\ps.
           SOME (MAP sum_INR ps)))
         (NONE (unknown_loc,(implode
           "Record patterns may only appear at the top level"))))`;;

let ptree_Patterns_def,ptree_Patterns_ind = define_guess
  `(ptree_Patterns (Lf (_,locs)) =
      NONE (locs,(implode "Expected pattern list non-terminal"))) /\
   (ptree_Patterns (Nd (nterm,locs) args) =
      if nterm = sum_INL camlPEG_nPatterns then
        match args with
          [pat] -> camlPtreeConversion_fmap (\p. [p])
              (camlPtreeConversion_ptree_Pattern pat)
        | [pat; rest] ->
            OPTION_BIND (camlPtreeConversion_ptree_Pattern pat) (\p.
                OPTION_BIND (ptree_Patterns rest) (\ps.
              SOME (CONS p ps)))
        | _ -> NONE (locs,(implode "Impossible: nPatterns"))
      else NONE (locs,(implode "Expected pattern list non-terminal")))`;;

(* Builds a binary operation based on the output from “ptree_Op”.
 *)

let build_binop_def = new_definition
  `build_binop symb x y =
     if symb = (implode "&&") then
       ast_Log Andalso x y
     else if symb = (implode "||") then
       ast_Log Orelse x y
     else ast_App ast_Opapp [ast_App ast_Opapp [ast_Var (Short symb); x];
       y]`;;

(* Turns a list literal expression “[x; y; z]” into the
 * constructor application “x::y::z::[]”.
 *)

let build_list_exp_def = new_definition
  `build_list_exp =
     FOLDR (\t e. ast_Con (SOME (Short (implode "::"))) [t; e])
           (ast_Con (SOME (Short (implode "[]"))) [])`;;

let build_funapp_def = new_definition
  `build_funapp f xs =
     FOLDL (\a b.
       match a with
         ast_Var (Short id) ->
           if id = (implode "raise") then
             ast_Raise b
           else ast_App ast_Opapp [a; b]
       | _ -> ast_App ast_Opapp [a; b]) f xs`;;

(* Functions for records.
 * TODO Make it so that the names include the constructor function, so that we
 *      can have the same record field name defined for different record types.
 *)

let mk_record_update_name_def = new_definition
  `mk_record_update_name field' cons =
     mlstring_concat [strcat (strcat (strcat (strcat (implode
       "{record_update(") cons) (implode ".")) field') (implode ")}")]`;;

let id_map_def,id_map_ind = define_guess
  `(id_map f (Long mn id) = Long mn (id_map f id)) /\
   (id_map f (Short nm) = Short (f nm))`;;

let build_record_upd_def = new_definition
  `build_record_upd cons b (f,x) =
     ast_App ast_Opapp [ast_App ast_Opapp [ast_Var (id_map
       (mk_record_update_name f) cons); b]; x]`;;

let mk_record_proj_name_def = new_definition
  `mk_record_proj_name field' cons =
     mlstring_concat [strcat (strcat (strcat (strcat (implode
       "{record_projection(") cons) (implode ".")) field') (implode ")}")]`;;

let build_record_proj_def = new_definition
  `build_record_proj cons f x =
     ast_App ast_Opapp [ast_Var (id_map (mk_record_proj_name f) cons); x]`;;

let mk_record_constr_name_def = new_definition
  `mk_record_constr_name constr fields' =
     mlstring_concat (APPEND (APPEND [(implode "{record_constructor(");
       constr; (implode ")")]
             (MAP (\fn. strcat (strcat (implode "(") fn) (implode ")"))
               fields')) [(implode "}")])`;;

let build_record_cons_id_def,build_record_cons_id_ind = define_guess
  `build_record_cons_id fns x2 =
   match x2 with
     [] ->
     NONE (unknown_loc,(implode "build_record_cons_id: empty path"))
   | [cn] ->
     SOME (Short (mk_record_constr_name cn fns))
   | CONS c cs ->
     OPTION_BIND (build_record_cons_id fns cs) (\id.
       SOME (Long c id))`;;

let build_record_cons_def = new_definition
  `build_record_cons path upds =
     let (names,exprs) = UNZIP (sort (\(f,_) (g,_). mlstring_lt f g) upds)
       in
       OPTION_BIND (build_record_cons_id names path) (\id.
         SOME (build_funapp (ast_Var id) exprs))`;;

(* Pattern match on a record: first pattern match on the constructor (with
 * a wildcard for the pattern that would otherwise contain the argument tuple)
 * and then generate a let-binding for each field name matched on. Example:
 *
 *   type a = Foo of { a: int; b: bool; c: string };;
 *   match x with
 *   | Foo { a, b } -> f a b
 *
 * becomes
 *
 *   type a = Foo of int * bool * string;;
 *   match x with
 *   | Foo _ -> let a = <build_record_proj(Foo,a)>(x) in
 *              let b = <build_record_proj(Foo,a)>(x) in
 *                f a b
 *)

let mk_record_match_aux_def,mk_record_match_aux_ind = define_guess
  `(mk_record_match_aux recv constr body [] = body) /\
   (mk_record_match_aux recv constr body (CONS f fs) =
      ast_Let (SOME f) (build_record_proj constr f (ast_Var (Short recv)))
                   (mk_record_match_aux recv constr body fs))`;;

let mk_record_match_def = new_definition
  `mk_record_match constr fs recv body =
     ast_Mat (ast_Var (Short recv))
         [ast_Pcon (SOME constr) [ast_Pany],mk_record_match_aux recv
           constr body fs]`;;

(* Turns a curried lambda with patterns, e.g. “fun a [3;4] c -> e”
 * into a sequence of lambdas, possibly with pattern matches:
 * “fun a -> fun fresh -> match fresh with [3;4] -> fun c -> e”.
 *)

let build_fun_lam_def = new_definition
  `build_fun_lam body pats =
       ITLIST (\p b. match p with
                      sum_INL (c,fs) -> ast_Fun (implode "")
                        (mk_record_match c fs (implode "") b)
                    | sum_INR (ast_Pvar x) -> ast_Fun x b
                    | sum_INR p -> ast_Fun (implode "") (ast_Mat (ast_Var
                      (Short (implode ""))) [p,b])) pats
             body`;;

(*
 * build_letrec is given a list of entries consisting of:
 * - a function name
 * - a list of patterns
 * - a body expression.
 *
 * A letrec in the CakeML AST is made from a function name, a variable name, and
 * a body expression. If there is no pattern in the list given to build_letrec,
 * then we use the empty variable name ("") and apply the body expression to
 * this variable (like eta expansion). This enables us to write things like:
 *   let rec f = function ... -> ...
 * or
 *   let rec f x y = ...
 *   and g = ...
 *
 * As a consequence, the parser will turn this:
 *   let rec f x = ...
 *   and y = 5
 * into this:
 *   let rec f x = ...
 *   and y x = 5 x
 * which is different from what OCaml generates (it correctly binds the value 5
 * to y with a let).
 *
 * Patterns are turned into variables using pattern match expressions:
 * - If the first pattern is not a variable, invent a variable name and
 *   match on it using the first pattern.
 * - If the first pattern is a variable, create a lambda.
 *)

let build_letrec_def = new_definition
  `build_letrec =
     MAP (\(f,ps,x).
            match ps with
              [] ->
                (f,(implode ""),ast_App ast_Opapp [x; ast_Var (Short
                  (implode ""))])
            | CONS (sum_INL (c,fs)) ps ->
                (f,(implode ""),mk_record_match c fs (implode "")
                  (build_fun_lam x ps))
            | CONS (sum_INR (ast_Pvar v)) ps ->
                (f,v,build_fun_lam x ps)
            | CONS (sum_INR p) ps ->
                (f,(implode ""),ast_Mat (ast_Var (Short (implode "")))
                  [(p,build_fun_lam x ps)]))`;;

(* Builds a sequence of lets out of a list of let bindings.
 *
 * N.B. The sum type determines whether we're building a regular let (INL), or
 * a let rec (INR).
 *)

let build_lets_def = new_definition
  `build_lets binds body =
     ITLIST (\camlPtreeConversion_bind rest.
              match camlPtreeConversion_bind with
                sum_INL (sum_INL (c,fs),x) ->
                  ast_Let (SOME (implode " r")) x (mk_record_match c fs
                    (implode " r") rest)
              | sum_INL (sum_INR (ast_Pvar v),x) ->
                  ast_Let (SOME v) x rest
              | sum_INL (sum_INR ast_Pany,x) ->
                  ast_Let NONE x rest
              | sum_INL (sum_INR p,x) ->
                  ast_Mat x [p,rest]
              | sum_INR (f,ps,bd) ->
                  ast_Let (SOME f) (build_fun_lam bd ps) rest) body
           binds`;;

(* N.B. The match-building functions do not accept mixing value definitions
 * (i.e., with no function arguments) with recursive definitions (let rec y =
 * ...). For example, the parser won't accept this:
 *
 *   let rec f x = y
 *   and z = 5;;
 *)

(* Build pattern match rows from lists of patterns that contain record matches.
 *)

let build_match_row_def = define_cases
  `(build_match_row mvar (sum_INL (c,fs),x) =
       (ast_Pcon (SOME c) [ast_Pany],mk_record_match c fs mvar x)) /\
   (build_match_row y (sum_INR p,x) =
       (p,x))`;;

(* I don't remember what was smart about this? *)

let SmartMat_def = new_definition
  `SmartMat mvar rows =
   match rows with
     [sum_INR ast_Pany,y] -> y
   | rows ->
     ast_Mat (ast_Var (Short mvar)) (MAP (build_match_row mvar) rows)`;;

(* Builds a pattern match expression that allocates a closure each time a guard
 * expression is encountered. N.B. this expects a call with pattern rows in
 * reverse order.
 *)

let build_pmatch_def,build_pmatch_ind = define_guess
  `(build_pmatch mvar acc [] =
      SmartMat mvar acc) /\
   (build_pmatch mvar acc (CONS (pat,exp,NONE) ps) =
      build_pmatch mvar (CONS (pat,exp) acc) ps) /\
   (build_pmatch mvar acc (CONS (pat,exp,SOME guard) ps) =
      let mexp = SmartMat mvar acc in
      let clos = ast_Let (SOME (implode " p")) (ast_Fun (implode " u")
          mexp) in
      let call = ast_App ast_Opapp [ast_Var (Short (implode " p")); ast_Con
          NONE []] in
      let mat = SmartMat mvar [(pat,ast_If guard exp call); (sum_INR
          ast_Pany,call)] in
        build_pmatch mvar [sum_INR ast_Pany,clos mat] ps)`;;

let build_match_def = new_definition
  `build_match x rows =
     let mvar = (implode " m") in
     ast_Let (SOME mvar) x
       (if EX (\(p,x,g). match g with SOME _ -> T | _ -> F) rows then
          build_pmatch mvar [] (REVERSE rows)
        else (ast_Mat (ast_Var (Short mvar))
               (MAP (\(p,x,g). build_match_row mvar (p,x)) rows)))`;;

let build_handle_def = new_definition
  `build_handle x rows =
     // Save the handled exception in a variable by first matching with Handle
     // * on a single variable, and then applying Mat to the variable. Reraise the
     // * exception in case of no match.
     // *
     // * This trickery is used to support pattern guards and fake records.
     let mvar = (implode " e") in
     let rows' = CONS (sum_INR ast_Pany,ast_Raise (ast_Var (Short
       mvar)),NONE) (REVERSE rows) in
     ast_Handle x [ast_Pvar mvar,build_pmatch mvar [] rows']`;;

let build_function_def = new_definition
  `build_function rows =
     ast_Fun (implode "") (build_pmatch (implode "") [] (REVERSE rows))`;;

(* Flatten the row-alternatives in a pattern-match.
 *)

let flatten_pmatch_def = new_definition
  `flatten_pmatch pss = FLAT (MAP (\(ps,x,w). MAP (\p. (p,x,w)) ps) pss)`;;

(* the termination relation that HOL4 gives is
     MEASURE
                              (sum_size (pair_size camlNT_size (parsetree_size
                                (K
                                0) (K 0) (K 0)))
                              (sum_size (parsetree_size (K 0) (K 0) (K 0))
                              (sum_size (parsetree_size (K 0) (K 0) (K 0))
                              (sum_size (parsetree_size (K 0) (K 0) (K 0))
                              (sum_size (parsetree_size (K 0) (K 0) (K 0))
                              (sum_size (parsetree_size (K 0) (K 0) (K 0))
                              (sum_size (parsetree_size (K 0) (K 0) (K 0))
                              (sum_size (SUC o list_size (parsetree_size (K 0)
                                (K
                                0) (K 0)))
                              (sum_size (SUC o list_size (parsetree_size (K 0)
                                (K
                                0) (K 0)))
                              (sum_size (parsetree_size (K 0) (K 0) (K 0))
                                (sum_size (parsetree_size (K 0) (K 0) (K 0))
                                (parsetree_size (K 0) (K 0) (K 0)))))))))))))
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 camlPtreeConversionScript.sml:2343-2356: the tactic that proves the
   termination *)
let camlPtreeConversion_ptree_Expr_def,camlPtreeConversion_ptree_Expr_ind =
  define_guess
  `(camlPtreeConversion_ptree_Expr et (Lf (_,locs)) =
        NONE (locs,(implode "Expected an expression non-terminal"))) /\
   (camlPtreeConversion_ptree_Expr et (Nd (nterm,locs) args) =
        if ~(sum_INL et = nterm) then
          NONE (locs,(implode "ptree_Expr"))
        else if nterm = sum_INL camlPEG_nExpr then
          match args with
            [arg] -> camlPtreeConversion_ptree_Expr camlPEG_nESeq arg
          | _ -> NONE (locs,(implode "Impossible: nExpr"))
        else if nterm = sum_INL camlPEG_nEUnclosed then
          match args with
            [arg] ->
              OPTION_BIND (nterm_of arg) (\n.
                if n = sum_INL camlPEG_nELet then
                  camlPtreeConversion_ptree_Expr camlPEG_nELet arg
                else if n = sum_INL camlPEG_nELetRec then
                  camlPtreeConversion_ptree_Expr camlPEG_nELetRec arg
                else if n = sum_INL camlPEG_nEMatch then
                  camlPtreeConversion_ptree_Expr camlPEG_nEMatch arg
                else if n = sum_INL camlPEG_nEFun then
                  camlPtreeConversion_ptree_Expr camlPEG_nEFun arg
                else if n = sum_INL camlPEG_nEFunction then
                  camlPtreeConversion_ptree_Expr camlPEG_nEFunction arg
                else if n = sum_INL camlPEG_nETry then
                  camlPtreeConversion_ptree_Expr camlPEG_nETry arg
                else if n = sum_INL camlPEG_nEWhile then
                  camlPtreeConversion_ptree_Expr camlPEG_nEWhile arg
                else if n = sum_INL camlPEG_nEFor then
                  camlPtreeConversion_ptree_Expr camlPEG_nEFor arg
                else if n = sum_INL camlPEG_nEApp then
                  camlPtreeConversion_ptree_Expr camlPEG_nEApp arg
                else NONE (locs,(implode
                    "Expected an expression non-terminal")))
          | _ -> NONE (locs,(implode "Impossible: nEUnclosed"))
        else if nterm = sum_INL camlPEG_nEList then
          match args with CONS lbrack rest ->
                OPTION_IGNORE_BIND (expect_tok lbrack caml_lex_LbrackT)
                    (OPTION_BIND (ptree_ExprList rest) (\exps.
                SOME (build_list_exp exps)))
          | _ -> NONE (locs,(implode "Impossible: nEList"))
        else if nterm = sum_INL camlPEG_nEBase then
          match args with
            [lpar; rpar] -> APPEND (
                OPTION_IGNORE_BIND (expect_tok lpar caml_lex_LparT) (
                OPTION_IGNORE_BIND (expect_tok rpar caml_lex_RparT) (
                SOME (ast_Con NONE []))))
              (
                OPTION_IGNORE_BIND (expect_tok lpar caml_lex_BeginT) (
                OPTION_IGNORE_BIND (expect_tok rpar caml_lex_EndT) (
                SOME (ast_Con NONE []))))
          | [lpar; expr; rpar] -> APPEND (
                OPTION_IGNORE_BIND (expect_tok lpar caml_lex_LparT) (
                OPTION_IGNORE_BIND (expect_tok rpar caml_lex_RparT) (
                camlPtreeConversion_ptree_Expr camlPEG_nExpr expr)))
              (
                OPTION_IGNORE_BIND (expect_tok lpar caml_lex_BeginT) (
                OPTION_IGNORE_BIND (expect_tok rpar caml_lex_EndT) (
                camlPtreeConversion_ptree_Expr camlPEG_nExpr expr)))
          | [lpar; expr; colon; typ; rpar] ->
                OPTION_IGNORE_BIND (expect_tok lpar caml_lex_LparT) (
                OPTION_IGNORE_BIND (expect_tok rpar caml_lex_RparT) (
                OPTION_IGNORE_BIND (expect_tok colon caml_lex_ColonT)
                    (OPTION_BIND (camlPtreeConversion_ptree_Type typ) (\ty.
                    OPTION_BIND (camlPtreeConversion_ptree_Expr camlPEG_nExpr
                    expr) (\x.
                SOME (ast_Tannot x ty))))))
          | [arg] ->
              OPTION_BIND (nterm_of arg) (\n.
                if n = sum_INL camlPEG_nERecUpdate then
                  camlPtreeConversion_ptree_Expr camlPEG_nERecUpdate arg
                else if n = sum_INL camlPEG_nLiteral then APPEND
                    (camlPtreeConversion_fmap (\id. ast_Con (SOME id) [])
                    (ptree_Bool arg))
                  (camlPtreeConversion_fmap ast_Lit (ptree_Literal arg))
                else if n = sum_INL camlPEG_nValuePath then
                  OPTION_BIND (ptree_ValuePath arg) (\cns. OPTION_BIND
                      (path_to_ns locs cns) (\ns.
                    SOME (ast_Var ns)))
                else if n = sum_INL camlPEG_nConstr then
                  OPTION_BIND (ptree_Constr arg) (\cns. OPTION_BIND
                      (path_to_ns locs cns) (\ns.
                    SOME (ast_Con (SOME ns) [])))
                else if n = sum_INL camlPEG_nEList then
                  camlPtreeConversion_ptree_Expr camlPEG_nEList arg
                else NONE (locs,(implode "Impossible: nEBase")))
          | _ -> NONE (locs,(implode "Impossible: nEBase"))
        else if nterm = sum_INL camlPEG_nERecUpdate then
          match args with
            [arg; lb; x; witht; upds; semi; rb] ->
                OPTION_IGNORE_BIND (expect_tok lb caml_lex_LbraceT) (
                OPTION_IGNORE_BIND (expect_tok witht caml_lex_WithT) (
                OPTION_IGNORE_BIND (expect_tok semi caml_lex_SemiT) (
                OPTION_IGNORE_BIND (expect_tok rb caml_lex_RbraceT)
                    (OPTION_BIND (camlPtreeConversion_ptree_Expr camlPEG_nExpr
                    x) (\e. OPTION_BIND (ptree_Updates upds) (\us. OPTION_BIND
                    (ptree_Constr arg) (\cns. OPTION_BIND (path_to_ns locs cns)
                    (\ns.
                SOME (FOLDL (build_record_upd ns) e us)))))))))
          | [arg; lb; x; witht; upds; rb] ->
                OPTION_IGNORE_BIND (expect_tok lb caml_lex_LbraceT) (
                OPTION_IGNORE_BIND (expect_tok witht caml_lex_WithT) (
                OPTION_IGNORE_BIND (expect_tok rb caml_lex_RbraceT)
                    (OPTION_BIND (camlPtreeConversion_ptree_Expr camlPEG_nExpr
                    x) (\e. OPTION_BIND (ptree_Updates upds) (\us. OPTION_BIND
                    (ptree_Constr arg) (\cns. OPTION_BIND (path_to_ns locs cns)
                    (\ns.
                SOME (FOLDL (build_record_upd ns) e us))))))))
          | _ -> NONE (locs,(implode "Impossible: nERecUpdate"))
        else if nterm = sum_INL camlPEG_nEIndex then
          match args with
            [arg] -> camlPtreeConversion_ptree_Expr camlPEG_nEPrefix arg
          | [arg; idx] ->
              OPTION_BIND (camlPtreeConversion_ptree_Expr camlPEG_nEPrefix
                  arg) (\pfx. OPTION_BIND (ptree_Index idx) (\idx_expr.
                match idx_expr with
                  sum_INL str_idx ->
                    SOME (build_funapp (ast_Var (Long (implode "String")
                        (Short (implode "get"))))
                              [pfx; str_idx])
                | sum_INR arr_idx ->
                    SOME (build_funapp (ast_Var (Long (implode "Array")
                        (Short (implode "get"))))
                              [pfx; arr_idx])))
          | _ -> NONE (locs,(implode "Impossible: nEIndex"))
        else if nterm = sum_INL camlPEG_nERecProj then
          match args with
            [arg] -> camlPtreeConversion_ptree_Expr camlPEG_nEIndex arg
          | [arg; dot1; cons; dot2; fn] ->
                OPTION_IGNORE_BIND (expect_tok dot1 caml_lex_DotT) (
                OPTION_IGNORE_BIND (expect_tok dot2 caml_lex_DotT)
                    (OPTION_BIND (camlPtreeConversion_ptree_Expr
                    camlPEG_nEIndex arg) (\x. OPTION_BIND (ptree_FieldName fn)
                    (\f. OPTION_BIND (ptree_Constr cons) (\cns. OPTION_BIND
                    (path_to_ns locs cns) (\ns.
                SOME (build_record_proj ns f x)))))))
          | _ -> NONE (locs,(implode "Impossible: nERecProj"))
        else if nterm = sum_INL camlPEG_nERecCons then
          match args with
            [cons; lb; upds; semi; rb] ->
                OPTION_IGNORE_BIND (expect_tok lb caml_lex_LbraceT) (
                OPTION_IGNORE_BIND (expect_tok semi caml_lex_SemiT) (
                OPTION_IGNORE_BIND (expect_tok rb caml_lex_RbraceT)
                    (OPTION_BIND (ptree_Constr cons) (\path. OPTION_BIND
                    (ptree_Updates upds) (\us.
                build_record_cons path us)))))
          | [cons; lb; upds; rb] ->
                OPTION_IGNORE_BIND (expect_tok lb caml_lex_LbraceT) (
                OPTION_IGNORE_BIND (expect_tok rb caml_lex_RbraceT)
                    (OPTION_BIND (ptree_Constr cons) (\path. OPTION_BIND
                    (ptree_Updates upds) (\us.
                build_record_cons path us))))
          | _ -> NONE (locs,(implode "Impossible: nERecCons"))
        else if nterm = sum_INL camlPEG_nEAssert then
          match args with
            [assr; expr] ->
                OPTION_IGNORE_BIND (expect_tok assr caml_lex_AssertT)
                    (OPTION_BIND (camlPtreeConversion_ptree_Expr
                    camlPEG_nERecProj expr) (\x.
                SOME (ast_App ast_Opapp [ast_Var (Short (implode
                    "assert")); x])))
          | _ -> NONE (locs,(implode "Impossible: nEAssert"))
        else if nterm = sum_INL camlPEG_nELazy then
          match args with
            [lazy; expr] ->
                OPTION_IGNORE_BIND (expect_tok lazy caml_lex_LazyT)
                    (OPTION_BIND (camlPtreeConversion_ptree_Expr
                    camlPEG_nERecProj expr) (\x.
                SOME (ast_App ast_Opapp [ast_Var (Short (implode "lazy"));
                    x])))
          | _ -> NONE (locs,(implode "Impossible: nELazy"))
        else if nterm = sum_INL camlPEG_nEConstr then
          match args with
            [consid; expr] ->
              OPTION_BIND (ptree_Constr consid) (\cns. OPTION_BIND
                  (path_to_ns locs cns) (\id. OPTION_BIND
                  (camlPtreeConversion_ptree_Expr camlPEG_nERecProj expr) (\x.
                SOME (compatCurryE id x))))
          | _ -> NONE (locs,(implode "Impossible: nEConstr"))
        else if nterm = sum_INL camlPEG_nEFunapp then
          match args with
            [exp] -> camlPtreeConversion_ptree_Expr camlPEG_nERecProj exp
          | [fexp; aexp] ->
              OPTION_BIND (camlPtreeConversion_ptree_Expr camlPEG_nEFunapp
                  fexp) (\f. OPTION_BIND (camlPtreeConversion_ptree_Expr
                  camlPEG_nERecProj aexp) (\x.
                SOME (build_funapp f [x])))
          | _ -> NONE (locs,(implode "Impossible: nEFunapp"))
        else if nterm = sum_INL camlPEG_nEApp then
          match args with
            [arg] ->
              OPTION_BIND (nterm_of arg) (\n.
                if n = sum_INL camlPEG_nELazy then
                  camlPtreeConversion_ptree_Expr camlPEG_nELazy arg
                else if n = sum_INL camlPEG_nEAssert then
                  camlPtreeConversion_ptree_Expr camlPEG_nEAssert arg
                else if n = sum_INL camlPEG_nEConstr then
                  camlPtreeConversion_ptree_Expr camlPEG_nEConstr arg
                else if n = sum_INL camlPEG_nEFunapp then
                  camlPtreeConversion_ptree_Expr camlPEG_nEFunapp arg
                else if n = sum_INL camlPEG_nERecCons then
                  camlPtreeConversion_ptree_Expr camlPEG_nERecCons arg
                else if n = sum_INL camlPEG_nERecProj then
                  camlPtreeConversion_ptree_Expr camlPEG_nERecProj arg
                else NONE (locs,(implode "Impolssible: nEApp")))
          | _ -> NONE (locs,(implode "Impossible: nEApp"))
        else if nterm = sum_INL camlPEG_nEPrefix then
          match args with
            [opn; expr] ->
              OPTION_BIND (camlPtreeConversion_ptree_Op opn) (\op.
                  OPTION_BIND (camlPtreeConversion_ptree_Expr camlPEG_nEBase
                  expr) (\x.
                SOME (ast_App ast_Opapp [ast_Var (Short op); x])))
          | [arg] -> camlPtreeConversion_ptree_Expr camlPEG_nEBase arg
          | _ -> NONE (locs,(implode "Impossible: nEPrefix"))
        else if nterm = sum_INL camlPEG_nENeg then
          match args with
            [pref; expr] ->
              OPTION_BIND (camlPtreeConversion_destLf pref) (\lf.
                  OPTION_BIND (camlPtreeConversion_option (tokenUtils_destTOK
                  lf)) (\tk. OPTION_BIND (camlPtreeConversion_ptree_Expr
                  camlPEG_nEUnclosed expr) (\x.
                if tk = caml_lex_MinusT then
                  SOME (ast_App ast_Opapp [ast_Var (Short (implode "~-"));
                      x])
                else if tk = caml_lex_MinusFT then
                  SOME (ast_App ast_Opapp [ast_Var (Short (implode "~-."));
                      x])
                else if caml_lex_isSymbol tk then
                  let s = THE (destSymbol tk) in
                    SOME (ast_App ast_Opapp [ast_Var (Short s); x])
                else NONE (locs,(implode "Impossible: nEPrefix")))))
          | [arg] -> camlPtreeConversion_ptree_Expr camlPEG_nEUnclosed arg
          | _ -> NONE (locs,(implode "Impossible: nEPrefix"))
        else if nterm = sum_INL camlPEG_nEShift then
          match args with
            [exp] -> camlPtreeConversion_ptree_Expr camlPEG_nENeg exp
          | [lhs; opn; rhs] ->
              OPTION_BIND (camlPtreeConversion_ptree_Expr camlPEG_nENeg
                  lhs) (\x. OPTION_BIND (camlPtreeConversion_ptree_Expr
                  camlPEG_nEShift rhs) (\y. OPTION_BIND
                  (camlPtreeConversion_ptree_Op opn) (\op.
                SOME (build_binop op x y))))
          | _ -> NONE (locs,(implode "Impossible: nEShift"))
        else if nterm = sum_INL camlPEG_nEMult then
          match args with
            [exp] -> camlPtreeConversion_ptree_Expr camlPEG_nEShift exp
          | [lhs; opn; rhs] ->
              OPTION_BIND (camlPtreeConversion_ptree_Expr camlPEG_nEMult
                  lhs) (\x. OPTION_BIND (camlPtreeConversion_ptree_Expr
                  camlPEG_nEShift rhs) (\y. OPTION_BIND
                  (camlPtreeConversion_ptree_Op opn) (\op.
                SOME (build_binop op x y))))
          | _ -> NONE (locs,(implode "Impossible: nMult"))
        else if nterm = sum_INL camlPEG_nEAdd then
          match args with
            [exp] -> camlPtreeConversion_ptree_Expr camlPEG_nEMult exp
          | [lhs; opn; rhs] ->
              OPTION_BIND (camlPtreeConversion_ptree_Expr camlPEG_nEAdd
                  lhs) (\x. OPTION_BIND (camlPtreeConversion_ptree_Expr
                  camlPEG_nEMult rhs) (\y. OPTION_BIND
                  (camlPtreeConversion_ptree_Op opn) (\op.
                SOME (build_binop op x y))))
          | _ -> NONE (locs,(implode "Impossible: nEAdd"))
        else if nterm = sum_INL camlPEG_nECons then
          match args with
            [exp] -> camlPtreeConversion_ptree_Expr camlPEG_nEAdd exp
          | [lhs; colons; rhs] ->
                OPTION_IGNORE_BIND (expect_tok colons caml_lex_ColonsT)
                    (OPTION_BIND (camlPtreeConversion_ptree_Expr camlPEG_nEAdd
                    lhs) (\x. OPTION_BIND (camlPtreeConversion_ptree_Expr
                    camlPEG_nECons rhs) (\y.
                SOME (ast_Con (SOME (Short (implode "::"))) [x; y]))))
          | _ -> NONE (locs,(implode "Impossible: nECons"))
        else if nterm = sum_INL camlPEG_nECat then
          match args with
            [exp] -> camlPtreeConversion_ptree_Expr camlPEG_nECons exp
          | [lhs; opn; rhs] ->
              OPTION_BIND (camlPtreeConversion_ptree_Expr camlPEG_nECons
                  lhs) (\x. OPTION_BIND (camlPtreeConversion_ptree_Expr
                  camlPEG_nECat rhs) (\y. OPTION_BIND
                  (camlPtreeConversion_ptree_Op opn) (\op.
                SOME (build_binop op x y))))
          | _ -> NONE (locs,(implode "Impossible: nECat"))
        else if nterm = sum_INL camlPEG_nERel then
          match args with
            [exp] -> camlPtreeConversion_ptree_Expr camlPEG_nECat exp
          | [lhs; opn; rhs] ->
              OPTION_BIND (camlPtreeConversion_ptree_Expr camlPEG_nERel
                  lhs) (\x. OPTION_BIND (camlPtreeConversion_ptree_Expr
                  camlPEG_nECat rhs) (\y. OPTION_BIND
                  (camlPtreeConversion_ptree_Op opn) (\op.
                SOME (build_binop op x y))))
          | _ -> NONE (locs,(implode "Impossible: nERel"))
        else if nterm = sum_INL camlPEG_nEAnd then
          match args with
            [exp] -> camlPtreeConversion_ptree_Expr camlPEG_nERel exp
          | [lhs; opn; rhs] ->
              OPTION_BIND (camlPtreeConversion_ptree_Expr camlPEG_nERel
                  lhs) (\x. OPTION_BIND (camlPtreeConversion_ptree_Expr
                  camlPEG_nEAnd rhs) (\y. OPTION_BIND
                  (camlPtreeConversion_ptree_Op opn) (\op.
                SOME (build_binop op x y))))
          | _ -> NONE (locs,(implode "Impossible: nEAnd"))
        else if nterm = sum_INL camlPEG_nEOr then
          match args with
            [exp] -> camlPtreeConversion_ptree_Expr camlPEG_nEAnd exp
          | [lhs; opn; rhs] ->
              OPTION_BIND (camlPtreeConversion_ptree_Expr camlPEG_nEAnd
                  lhs) (\x. OPTION_BIND (camlPtreeConversion_ptree_Expr
                  camlPEG_nEOr rhs) (\y. OPTION_BIND
                  (camlPtreeConversion_ptree_Op opn) (\op.
                SOME (build_binop op x y))))
          | _ -> NONE (locs,(implode "Impossible: nEOr"))
        else if nterm = sum_INL camlPEG_nEHolInfix then
          match args with
            [exp] -> camlPtreeConversion_ptree_Expr camlPEG_nEOr exp
          | [lhs; opn; rhs] ->
              OPTION_BIND (camlPtreeConversion_ptree_Expr
                  camlPEG_nEHolInfix lhs) (\x. OPTION_BIND
                  (camlPtreeConversion_ptree_Expr camlPEG_nEOr rhs) (\y.
                  OPTION_BIND (camlPtreeConversion_ptree_Op opn) (\op.
                SOME (build_binop op x y))))
          | _ -> NONE (locs,(implode "Impossible: nEHolInfix"))
        else if nterm = sum_INL camlPEG_nEProd then
          match args with
            [exp] -> camlPtreeConversion_ptree_Expr camlPEG_nEHolInfix exp
          | CONS exp exps ->
              OPTION_BIND (camlPtreeConversion_ptree_Expr
                  camlPEG_nEHolInfix exp) (\x. OPTION_BIND (ptree_ExprCommas
                  exps) (\xs.
                SOME (ast_Con NONE (CONS x xs))))
          | _ -> NONE (locs,(implode "Impossible: nEProd"))
        else if nterm = sum_INL camlPEG_nEAssign then
          match args with
            [exp] -> camlPtreeConversion_ptree_Expr camlPEG_nEProd exp
          | [lhs; opn; rhs] ->
              OPTION_BIND (camlPtreeConversion_ptree_Expr camlPEG_nEProd
                  lhs) (\x. OPTION_BIND (camlPtreeConversion_ptree_Expr
                  camlPEG_nEAssign rhs) (\y. OPTION_BIND
                  (camlPtreeConversion_ptree_Op opn) (\op.
                SOME (build_binop op x y))))
          | _ -> NONE (locs,(implode "Impossible: nEAssign"))
        else if nterm = sum_INL camlPEG_nEIf then
          match args with
            [ift; x; thent; y; elset; z] ->
                OPTION_IGNORE_BIND (expect_tok ift caml_lex_IfT) (
                OPTION_IGNORE_BIND (expect_tok thent caml_lex_ThenT) (
                OPTION_IGNORE_BIND (expect_tok elset caml_lex_ElseT)
                    (OPTION_BIND (camlPtreeConversion_ptree_Expr camlPEG_nExpr
                    x) (\x1. OPTION_BIND (camlPtreeConversion_ptree_Expr
                    camlPEG_nEIf y) (\y1. OPTION_BIND
                    (camlPtreeConversion_ptree_Expr camlPEG_nEIf z) (\z1.
                SOME (ast_If x1 y1 z1)))))))
          | [ift; x; thent; y] ->
                OPTION_IGNORE_BIND (expect_tok ift caml_lex_IfT) (
                OPTION_IGNORE_BIND (expect_tok thent caml_lex_ThenT)
                    (OPTION_BIND (camlPtreeConversion_ptree_Expr camlPEG_nExpr
                    x) (\x1. OPTION_BIND (camlPtreeConversion_ptree_Expr
                    camlPEG_nEIf y) (\y1.
                SOME (ast_If x1 y1 (ast_Con NONE []))))))
          | [exp] -> camlPtreeConversion_ptree_Expr camlPEG_nEAssign exp
          | _ -> NONE (locs,(implode "Impossible: nEIf"))
        else if nterm = sum_INL camlPEG_nESeq then
          match args with
            [x; semi; y] ->
                OPTION_IGNORE_BIND (expect_tok semi caml_lex_SemiT)
                    (OPTION_BIND (camlPtreeConversion_ptree_Expr camlPEG_nEIf
                    x) (\x1. OPTION_BIND (camlPtreeConversion_ptree_Expr
                    camlPEG_nExpr y) (\y1.
                SOME (ast_Let NONE x1 y1))))
          | [x] -> camlPtreeConversion_ptree_Expr camlPEG_nEIf x
          | _ -> NONE (locs,(implode "Impossible: nESeq"))
        else if nterm = sum_INL camlPEG_nELetRec then
          match args with
            [lett; rec; binds; int'; expr] ->
                OPTION_IGNORE_BIND (expect_tok lett caml_lex_LetT) (
                OPTION_IGNORE_BIND (expect_tok rec caml_lex_RecT) (
                OPTION_IGNORE_BIND (expect_tok int' caml_lex_InT)
                    (OPTION_BIND (ptree_LetRecBindings binds) (\binds.
                    OPTION_BIND (camlPtreeConversion_ptree_Expr camlPEG_nExpr
                    expr) (\body.
                SOME (ast_Letrec (build_letrec binds) body))))))
          | _ -> NONE (locs,(implode "Impossible: nELetRec"))
        else if nterm = sum_INL camlPEG_nELet then
          match args with
            [lett; binds; int'; expr] ->
                OPTION_IGNORE_BIND (expect_tok lett caml_lex_LetT) (
                OPTION_IGNORE_BIND (expect_tok int' caml_lex_InT)
                    (OPTION_BIND (ptree_LetBindings binds) (\binds. OPTION_BIND
                    (camlPtreeConversion_ptree_Expr camlPEG_nExpr expr) (\body.
                SOME (build_lets body binds)))))
          | _ -> NONE (locs,(implode "Impossible: nELet"))
        else if nterm = sum_INL camlPEG_nEMatch then
          match args with
            [match'; expr; witht; pm] ->
                OPTION_IGNORE_BIND (expect_tok match' caml_lex_MatchT) (
                OPTION_IGNORE_BIND (expect_tok witht caml_lex_WithT)
                    (OPTION_BIND (camlPtreeConversion_ptree_Expr camlPEG_nExpr
                    expr) (\x. OPTION_BIND (ptree_PatternMatch pm) (\ps.
                SOME (build_match x (flatten_pmatch ps))))))
          | _ -> NONE (locs,(implode "Impossible: nEMatch"))
        else if nterm = sum_INL camlPEG_nEFun then
          match args with
            [funt; params'; rarrow; expr] ->
                OPTION_IGNORE_BIND (expect_tok funt caml_lex_FunT) (
                OPTION_IGNORE_BIND (expect_tok rarrow caml_lex_RarrowT)
                    (OPTION_BIND (ptree_Patterns params') (\ps. OPTION_BIND
                    (camlPtreeConversion_ptree_Expr camlPEG_nExpr expr) (\x.
                OPTION_IGNORE_BIND (if ALL (\p. match p with [_] -> T | _
                    -> F) ps then SOME one else NONE (locs,(implode
                    "Or-patterns are not allowed in fun expressions"))) (
                SOME (build_fun_lam x (FLAT ps)))))))
          | [funt; params'; colon; typ; rarrow; expr] ->
                OPTION_IGNORE_BIND (expect_tok funt caml_lex_FunT) (
                OPTION_IGNORE_BIND (expect_tok rarrow caml_lex_RarrowT)
                    (OPTION_BIND (ptree_Patterns params') (\ps. OPTION_BIND
                    (camlPtreeConversion_ptree_Expr camlPEG_nExpr expr) (\x.
                    OPTION_BIND (camlPtreeConversion_ptree_Type typ) (\ty.
                OPTION_IGNORE_BIND (if ALL (\p. match p with [_] -> T | _
                    -> F) ps then SOME one else NONE (locs,(implode
                    "Or-patterns are not allowed in fun expressions"))) (
                SOME (ast_Tannot (build_fun_lam x (FLAT ps)) ty)))))))
          | _ -> NONE (locs,(implode "Impossible: nEFun"))
        else if nterm = sum_INL camlPEG_nEFunction then
          match args with
            [funct; pm] ->
                OPTION_IGNORE_BIND (expect_tok funct caml_lex_FunctionT)
                    (OPTION_BIND (ptree_PatternMatch pm) (\ps.
                SOME (build_function (flatten_pmatch ps))))
          | _ -> NONE (locs,(implode "Impossible: nEFunction"))
        else if nterm = sum_INL camlPEG_nETry then
          match args with
            [tryt; expr; witht; pm] ->
                OPTION_IGNORE_BIND (expect_tok tryt caml_lex_TryT) (
                OPTION_IGNORE_BIND (expect_tok witht caml_lex_WithT)
                    (OPTION_BIND (camlPtreeConversion_ptree_Expr camlPEG_nExpr
                    expr) (\x. OPTION_BIND (ptree_PatternMatch pm) (\ps.
                SOME (build_handle x (flatten_pmatch ps))))))
          | _ -> NONE (locs,(implode "Impossible: nETry"))
        else if nterm = sum_INL camlPEG_nEWhile then
          match args with
            [while; expr; dot; body; donet] ->
                OPTION_IGNORE_BIND (expect_tok while caml_lex_WhileT) (
                OPTION_IGNORE_BIND (expect_tok dot caml_lex_DoT) (
                OPTION_IGNORE_BIND (expect_tok donet caml_lex_DoneT)
                    (OPTION_BIND (camlPtreeConversion_ptree_Expr camlPEG_nExpr
                    expr) (\x. OPTION_BIND (camlPtreeConversion_ptree_Expr
                    camlPEG_nExpr body) (\b.
                SOME (build_funapp (ast_Var (Short (implode "while"))) [x;
                    b]))))))
          | _ -> NONE (locs,(implode "Impossible: nEWhile"))
        else if nterm = sum_INL camlPEG_nEFor then
          match args with
            [for; ident; eq; ubd; updown; lbd; dot; body; donet] ->
                OPTION_IGNORE_BIND (expect_tok for caml_lex_ForT) (
                OPTION_IGNORE_BIND (expect_tok eq caml_lex_EqualT) (
                OPTION_IGNORE_BIND (expect_tok dot caml_lex_DoT)
                    (OPTION_BIND (camlPtreeConversion_destLf updown) (\lf.
                    OPTION_BIND (camlPtreeConversion_option (tokenUtils_destTOK
                    lf)) (\tk.
                OPTION_IGNORE_BIND (if tk = caml_lex_ToT \/ tk =
                    caml_lex_DowntoT then SOME one else NONE (locs,(implode
                    "Expected 'to' or 'downto'"))) (OPTION_BIND
                    (ptree_ValueName ident) (\id. OPTION_BIND
                    (camlPtreeConversion_ptree_Expr camlPEG_nExpr ubd) (\u.
                    OPTION_BIND (camlPtreeConversion_ptree_Expr camlPEG_nExpr
                    lbd) (\l. OPTION_BIND (camlPtreeConversion_ptree_Expr
                    camlPEG_nExpr body) (\b.
                SOME (build_funapp (ast_Var (Short (implode "for")))
                              [ast_Con (SOME (bool2id (tk = caml_lex_ToT)))
                                  [];
                              ast_Var (Short id); u; l; b])))))))))))
          | _ -> NONE (locs,(implode "Impossible: nEFor"))
        else NONE (locs,(implode "ptree_Expr"))) /\
   (ptree_LetRecBinding (Lf (_,locs)) =
        NONE (locs,(implode "Expected a let rec binding non-terminal"))) /\
   (ptree_LetRecBinding (Nd (nterm,locs) args) =
        if nterm = sum_INL camlPEG_nLetRecBinding then
          match args with
            [id; pats; colon; type; eq; expr] ->
                OPTION_IGNORE_BIND (expect_tok colon caml_lex_ColonT) (
                OPTION_IGNORE_BIND (expect_tok eq caml_lex_EqualT)
                    (OPTION_BIND (ptree_ValueName id) (\nm. OPTION_BIND
                    (ptree_Patterns pats) (\ps. OPTION_BIND
                    (camlPtreeConversion_ptree_Type type) (\ty. OPTION_BIND
                    (camlPtreeConversion_ptree_Expr camlPEG_nExpr expr) (\bd.
                OPTION_IGNORE_BIND (if ALL (\p. match p with [_] -> T | _
                    -> F) ps then SOME one else NONE (locs,(implode
                    "Or-patterns are not allowed in let (rec) bindings"))) (
                SOME (nm,FLAT ps,ast_Tannot bd ty))))))))
          | [id; pats; eq; expr] ->
                OPTION_IGNORE_BIND (expect_tok eq caml_lex_EqualT)
                    (OPTION_BIND (ptree_ValueName id) (\nm. OPTION_BIND
                    (ptree_Patterns pats) (\ps. OPTION_BIND
                    (camlPtreeConversion_ptree_Expr camlPEG_nExpr expr) (\bd.
                OPTION_IGNORE_BIND (if ALL (\p. match p with [_] -> T | _
                    -> F) ps then SOME one else NONE (locs,(implode
                    "Or-patterns are not allowed in let (rec) bindings"))) (
                SOME (nm,FLAT ps,bd))))))
          | [id; colon; type; eq; expr] ->
                OPTION_IGNORE_BIND (expect_tok eq caml_lex_EqualT) (
                OPTION_IGNORE_BIND (expect_tok colon caml_lex_ColonT)
                    (OPTION_BIND (ptree_ValueName id) (\nm. OPTION_BIND
                    (camlPtreeConversion_ptree_Type type) (\ty. OPTION_BIND
                    (camlPtreeConversion_ptree_Expr camlPEG_nExpr expr) (\bd.
                SOME (nm,[],ast_Tannot bd ty))))))
          | [id; eq; expr] ->
                OPTION_IGNORE_BIND (expect_tok eq caml_lex_EqualT)
                    (OPTION_BIND (ptree_ValueName id) (\nm. OPTION_BIND
                    (camlPtreeConversion_ptree_Expr camlPEG_nExpr expr) (\bd.
                SOME (nm,[],bd))))
          | _ -> NONE (locs,(implode "Impossible: nLetRecBinding"))
        else NONE (locs,(implode
            "Expected a let rec binding non-terminal"))) /\
   (ptree_LetRecBindings (Lf (_,locs)) =
          NONE (locs,(implode
              "Expected a list of let rec bindings non-terminal"))) /\
   (ptree_LetRecBindings (Nd (nterm,locs) args) =
        if nterm = sum_INL camlPEG_nLetRecBindings then
          match args with
            [rec] ->
              camlPtreeConversion_fmap (\r. [r]) (ptree_LetRecBinding rec)
          | [rec; andt; recs] ->
                OPTION_IGNORE_BIND (expect_tok andt caml_lex_AndT)
                    (OPTION_BIND (ptree_LetRecBinding rec) (\r. OPTION_BIND
                    (ptree_LetRecBindings recs) (\rs.
                SOME (CONS r rs))))
          | _ -> NONE (locs,(implode "Impossible: nLetRecBindings"))
        else NONE (locs,(implode
            "Expected a list of let rec bindings non-terminal"))) /\
   (ptree_LetBinding (Lf (_,locs)) =
        NONE (locs,(implode "Expected a let binding non-terminal"))) /\
   (ptree_LetBinding (Nd (nterm,locs) args) =
        if nterm = sum_INL camlPEG_nLetBinding then
          match args with
            [pat; eq; bod] ->
                OPTION_IGNORE_BIND (expect_tok eq caml_lex_EqualT)
                    (OPTION_BIND (camlPtreeConversion_ptree_Pattern pat) (\ps.
                    OPTION_BIND (camlPtreeConversion_ptree_Expr camlPEG_nExpr
                    bod) (\bd.
                match ps with
                  [p] -> SOME (sum_INL (p,bd))
                | _ ->
                  NONE (locs,(implode
                      "Or-patterns are not allowed in let (rec) bindings")))))
          | [id; pats; eq; bod] ->
                OPTION_IGNORE_BIND (expect_tok eq caml_lex_EqualT)
                    (OPTION_BIND (ptree_ValueName id) (\nm. OPTION_BIND
                    (ptree_Patterns pats) (\ps. OPTION_BIND
                    (camlPtreeConversion_ptree_Expr camlPEG_nExpr bod) (\bd.
                OPTION_IGNORE_BIND (if ALL (\p. match p with [_] -> T | _
                    -> F) ps then SOME one else NONE (locs,(implode
                    "Or-patterns are not allowed in let (rec) bindings"))) (
                SOME (sum_INR (nm,FLAT ps,bd)))))))
          | [id; colon; type; eq; bod] ->
                OPTION_IGNORE_BIND (expect_tok eq caml_lex_EqualT) (
                OPTION_IGNORE_BIND (expect_tok colon caml_lex_ColonT)
                    (OPTION_BIND (ptree_ValueName id) (\nm. OPTION_BIND
                    (camlPtreeConversion_ptree_Type type) (\ty. OPTION_BIND
                    (camlPtreeConversion_ptree_Expr camlPEG_nExpr bod) (\bd.
                SOME (sum_INL (sum_INR (ast_Pvar nm),ast_Tannot bd
                    ty)))))))
          | [id; pats; colon; type; eq; bod] ->
                OPTION_IGNORE_BIND (expect_tok eq caml_lex_EqualT) (
                OPTION_IGNORE_BIND (expect_tok colon caml_lex_ColonT)
                    (OPTION_BIND (ptree_ValueName id) (\nm. OPTION_BIND
                    (ptree_Patterns pats) (\ps. OPTION_BIND
                    (camlPtreeConversion_ptree_Type type) (\ty. OPTION_BIND
                    (camlPtreeConversion_ptree_Expr camlPEG_nExpr bod) (\bd.
                OPTION_IGNORE_BIND (if ALL (\p. match p with [_] -> T | _
                    -> F) ps then SOME one else NONE (locs,(implode
                    "Or-patterns are not allowed in let (rec) bindings"))) (
                SOME (sum_INR (nm,FLAT ps,ast_Tannot bd ty)))))))))
          | _ -> NONE (locs,(implode "Impossible: nLetBinding"))
        else NONE (locs,(implode
            "Expected a let binding non-terminal"))) /\
   (ptree_LetBindings (Lf (_,locs)) =
         NONE (locs,(implode
             "Expected a list of let bindings non-terminal"))) /\
   (ptree_LetBindings (Nd (nterm,locs) args) =
        if nterm = sum_INL camlPEG_nLetBindings then
          match args with
            [letb] ->
              camlPtreeConversion_fmap (\l. [l]) (ptree_LetBinding letb)
          | [letb; andt; lets] ->
                OPTION_IGNORE_BIND (expect_tok andt caml_lex_AndT)
                    (OPTION_BIND (ptree_LetBinding letb) (\r. OPTION_BIND
                    (ptree_LetBindings lets) (\rs.
                SOME (CONS r rs))))
          | _ -> NONE (locs,(implode "Impossible: nLetBindings"))
        else NONE (locs,(implode
            "Expected a list of let bindings non-terminal"))) /\
   (ptree_PatternMatches (Lf (_,locs)) =
        NONE (locs,(implode "Expected a pattern-matches non-terminal"))) /\
   (ptree_PatternMatches (Nd (nterm,locs) args) =
        if nterm = sum_INL camlPEG_nPatternMatches then
          match args with
            [
             // urk: these cases overlap
             a; b; c; d; e] ->
              let pat = a in let whent = b in let whenx = c in let rarrow =
                  d in let body = e in APPEND (
                  OPTION_IGNORE_BIND (expect_tok rarrow caml_lex_RarrowT) (
                  OPTION_IGNORE_BIND (expect_tok whent caml_lex_WhenT)
                      (OPTION_BIND (camlPtreeConversion_ptree_Pattern pat) (\p.
                      OPTION_BIND (camlPtreeConversion_ptree_Expr camlPEG_nExpr
                      body) (\x. OPTION_BIND (camlPtreeConversion_ptree_Expr
                      camlPEG_nExpr whenx) (\w.
                  SOME [p,x,SOME w]))))))
              (let pat = a in let rarrow = b in let body = c in let bar = d
                  in let pms = e in
                  OPTION_IGNORE_BIND (expect_tok rarrow caml_lex_RarrowT) (
                  OPTION_IGNORE_BIND (expect_tok bar caml_lex_BarT)
                      (OPTION_BIND (camlPtreeConversion_ptree_Pattern pat) (\p.
                      OPTION_BIND (camlPtreeConversion_ptree_Expr camlPEG_nExpr
                      body) (\x. OPTION_BIND (ptree_PatternMatches pms) (\ps.
                  SOME (CONS (p,x,NONE) ps)))))))
          | [pat; whent; whenx; rarrow; body; bar; pms] ->
                OPTION_IGNORE_BIND (expect_tok rarrow caml_lex_RarrowT) (
                OPTION_IGNORE_BIND (expect_tok whent caml_lex_WhenT)
                    (OPTION_BIND (camlPtreeConversion_ptree_Pattern pat) (\p.
                    OPTION_BIND (camlPtreeConversion_ptree_Expr camlPEG_nExpr
                    body) (\x. OPTION_BIND (camlPtreeConversion_ptree_Expr
                    camlPEG_nExpr whenx) (\w.
                OPTION_IGNORE_BIND (expect_tok bar caml_lex_BarT)
                    (OPTION_BIND (ptree_PatternMatches pms) (\ps.
                SOME (CONS (p,x,SOME w) ps))))))))
          | [pat; rarrow; body] ->
                OPTION_IGNORE_BIND (expect_tok rarrow caml_lex_RarrowT)
                    (OPTION_BIND (camlPtreeConversion_ptree_Pattern pat) (\p.
                    OPTION_BIND (camlPtreeConversion_ptree_Expr camlPEG_nExpr
                    body) (\x.
                SOME [p,x,NONE])))
          | _ -> NONE (locs,(implode "Impossible: nPatternMatches"))
        else NONE (locs,(implode
            "Expected a pattern-matches non-terminal"))) /\
   (ptree_PatternMatch (Lf (_,locs)) =
        NONE (locs,(implode "Expected a pattern-match non-terminal"))) /\
   (ptree_PatternMatch (Nd (nterm,locs) args) =
        if nterm = sum_INL camlPEG_nPatternMatch then
          match args with
            [bar; pms] ->
                OPTION_IGNORE_BIND (expect_tok bar caml_lex_BarT) (
                ptree_PatternMatches pms)
          | [pms] -> ptree_PatternMatches pms
          | _ -> NONE (locs,(implode "Impossible: nPatternMatch"))
        else NONE (locs,(implode
            "Expected a pattern-match non-terminal"))) /\
   (ptree_ExprList [] =
        NONE (unknown_loc,(implode "Expression lists cannot be empty"))) /\
   (ptree_ExprList [t] =
           OPTION_IGNORE_BIND (expect_tok t caml_lex_RbrackT) (
           SOME [])) /\
   (ptree_ExprList (CONS x xs) = APPEND (
           OPTION_IGNORE_BIND (expect_tok x caml_lex_SemiT) (
           ptree_ExprList xs))
         (OPTION_BIND (camlPtreeConversion_ptree_Expr camlPEG_nEIf x) (\y.
             OPTION_BIND (ptree_ExprList xs) (\ys.
           SOME (CONS y ys))))) /\
   (ptree_ExprCommas [] = SOME []) /\
   (ptree_ExprCommas (CONS x xs) = APPEND (
          OPTION_IGNORE_BIND (expect_tok x caml_lex_CommaT) (
          ptree_ExprCommas xs))
        (OPTION_BIND (camlPtreeConversion_ptree_Expr camlPEG_nEHolInfix x)
            (\y. OPTION_BIND (ptree_ExprCommas xs) (\ys.
          SOME (CONS y ys))))) /\
   (ptree_Update (Lf (_,locs)) =
        NONE (locs,(implode "Expected an update non-terminal"))) /\
   (ptree_Update (Nd (nterm,locs) args) =
         if nterm = sum_INL camlPEG_nUpdate then
           match args with
             [fd; eq; expr] ->
                 OPTION_IGNORE_BIND (expect_tok eq caml_lex_EqualT)
                     (OPTION_BIND (ptree_FieldName fd) (\f. OPTION_BIND
                     (camlPtreeConversion_ptree_Expr camlPEG_nEIf expr) (\x.
                 SOME (f,x))))
           | _ -> NONE (locs,(implode "Impossible: nUpdate"))
         else NONE (locs,(implode "Expected an update non-terminal"))) /\
   (ptree_Updates (Lf (_,locs)) =
        NONE (locs,(implode "Expected an updates non-terminal"))) /\
   (ptree_Updates (Nd (nterm,locs) args) =
         if nterm = sum_INL camlPEG_nUpdates then
           match args with
             [upd] -> camlPtreeConversion_fmap (\u. [u]) (ptree_Update upd)
           | [upd; semi; upds] ->
                 OPTION_IGNORE_BIND (expect_tok semi caml_lex_SemiT)
                     (OPTION_BIND (ptree_Update upd) (\u. OPTION_BIND
                     (ptree_Updates upds) (\us.
                 SOME (CONS u us))))
           | _ -> NONE (locs,(implode "Impossible: nUpdates"))
         else NONE (locs,(implode "Expected an updates non-terminal"))) /\
   (ptree_Index (Lf (_,locs)) =
        NONE (locs,(implode "Expected an index non-terminal"))) /\
   (ptree_Index (Nd (nterm,locs) args) =
         if nterm = sum_INL camlPEG_nArrIdx then
           match args with
             [dott; lpar; expr; rpar] ->
                 OPTION_IGNORE_BIND (expect_tok dott caml_lex_DotT) (
                 OPTION_IGNORE_BIND (expect_tok lpar caml_lex_LparT) (
                 OPTION_IGNORE_BIND (expect_tok rpar caml_lex_RparT) (
                 camlPtreeConversion_fmap sum_INR
                     (camlPtreeConversion_ptree_Expr camlPEG_nExpr expr))))
           | _ -> NONE (locs,(implode "Impossible: nArrIdx"))
         else if nterm = sum_INL camlPEG_nStrIdx then
           match args with
             [dott; lbrack; expr; rbrack] ->
                 OPTION_IGNORE_BIND (expect_tok dott caml_lex_DotT) (
                 OPTION_IGNORE_BIND (expect_tok lbrack caml_lex_LbrackT) (
                 OPTION_IGNORE_BIND (expect_tok rbrack caml_lex_RbrackT) (
                 camlPtreeConversion_fmap sum_INL
                     (camlPtreeConversion_ptree_Expr camlPEG_nExpr expr))))
           | _ -> NONE (locs,(implode "Impossible: nStrIdx"))
         else NONE (locs,(implode "Expected an index non-terminal")))`;;

(* Tidy up the list bits of the induction theorem.
 *)

(* HOL4 camlPtreeConversionScript.sml:2361-2362: a theorem that HOL4 states
   as the value of an ML expression: ptree_Expr_ind *)

let ptree_FieldDec_def = define_cases
  `(ptree_FieldDec (Lf (_,locs)) =
      NONE (locs,(implode "Expected a field declaration non-terminal"))) /\
   (ptree_FieldDec (Nd (nterm,locs) args) =
      if nterm = sum_INL camlPEG_nFieldDec then
        match args with
          [fn; colon; ty] ->
              OPTION_IGNORE_BIND (expect_tok colon caml_lex_ColonT)
                  (OPTION_BIND (ptree_FieldName fn) (\f. OPTION_BIND
                  (camlPtreeConversion_ptree_Type ty) (\t.
              SOME (f,t))))
        | _ -> NONE (locs,(implode "Impossible: nFieldDec"))
      else NONE (locs,(implode
          "Expected a field declaration non-terminal")))`;;

let ptree_FieldDecs_def,ptree_FieldDecs_ind = define_guess
  `(ptree_FieldDecs (Lf (_,locs)) =
      NONE (locs,(implode "Expected a field decls non-terminal"))) /\
   (ptree_FieldDecs (Nd (nterm,locs) args) =
      if nterm = sum_INL camlPEG_nFieldDecs then
        match args with
          [fdec] -> camlPtreeConversion_fmap (\fd. [fd]) (ptree_FieldDec
              fdec)
        | [fdec; semi; fdecs] ->
              OPTION_IGNORE_BIND (expect_tok semi caml_lex_SemiT)
                  (OPTION_BIND (ptree_FieldDec fdec) (\f. OPTION_BIND
                  (ptree_FieldDecs fdecs) (\fs.
              SOME (CONS f fs))))
        | _ -> NONE (locs,(implode "Impossible: nFieldDecs"))
      else NONE (locs,(implode
          "Expected a field declaration non-terminal")))`;;

(*
 * Record definitions return a list of (field_name,type) pairs.
 *)

let ptree_Record_def = define_cases
  `(ptree_Record (Lf (_,locs)) =
      NONE (locs,(implode "Expected a record constructor"))) /\
   (ptree_Record (Nd (nterm,locs) args) =
      if nterm = sum_INL camlPEG_nRecord then
        match args with
          [lb; fds; semi; rb] ->
              OPTION_IGNORE_BIND (expect_tok lb caml_lex_LbraceT) (
              OPTION_IGNORE_BIND (expect_tok semi caml_lex_SemiT) (
              OPTION_IGNORE_BIND (expect_tok rb caml_lex_RbraceT) (
              ptree_FieldDecs fds)))
        | [lb; fds; rb] ->
              OPTION_IGNORE_BIND (expect_tok lb caml_lex_LbraceT) (
              OPTION_IGNORE_BIND (expect_tok rb caml_lex_RbraceT) (
              ptree_FieldDecs fds))
        | _ -> NONE (locs,(implode "Impossible: nRecord"))
      else NONE (locs,(implode "Expected a record constructor")))`;;

(*
 * Vanilla constructor definitions return a list of types.
 *)

let ptree_ConstrArgs_def = define_cases
  `(ptree_ConstrArgs (Lf (_,locs)) =
      NONE (locs,(implode
          "Expected a constructor arguments non-terminal"))) /\
   (ptree_ConstrArgs (Nd (nterm,locs) args) =
      if nterm = sum_INL camlPEG_nConstrArgs then
        match args with CONS ty rest ->
            OPTION_BIND (camlPtreeConversion_ptree_Type ty) (\t.
                OPTION_BIND (ptree_StarTypes rest) (\ts.
              SOME (CONS t ts)))
        | _ -> NONE (locs,(implode "Impossible: nConstrArgs"))
      else NONE (locs,(implode
          "Expected a constructor arguments non-terminal")))`;;

(*
 * A constructor declaration returns one of:
 * - a name and a list of types (a regular constructor)
 * - a name and a list of (name*type) pairs (record constructor)
 * The latter causes a bunch of definitions to be generated.
 *)

let ptree_ConstrDecl_def = define_cases
  `(ptree_ConstrDecl (Lf (_,locs)) =
      NONE (locs,(implode
          "Expected a constructor declaration non-terminal"))) /\
   (ptree_ConstrDecl (Nd (nterm,locs) args) =
      if nterm = sum_INL camlPEG_nConstrDecl then
        match args with
          [name] ->
            camlPtreeConversion_fmap (\nm. sum_INL (nm,[]))
                (ptree_ConstrName name)
        | [name; oft; args] ->
              OPTION_IGNORE_BIND (expect_tok oft caml_lex_OfT) (OPTION_BIND
                  (ptree_ConstrName name) (\nm. OPTION_BIND (nterm_of args)
                  (\peg_nt.
              if peg_nt = sum_INL camlPEG_nRecord then
                OPTION_BIND (ptree_Record args) (\ts.
                  SOME (sum_INR (nm,ts)))
              else if peg_nt = sum_INL camlPEG_nConstrArgs then
                OPTION_BIND (ptree_ConstrArgs args) (\ts.
                  SOME (sum_INL (nm,ts)))
              else NONE (locs,(implode "Impossible: nConstrDecl")))))
        | _ -> NONE (locs,(implode "Impossible: nConstrDecl"))
      else NONE (locs,(implode
          "Expected a constructor declaration non-terminal")))`;;

let ptree_ExcType_def = define_cases
  `(ptree_ExcType (Lf (_,locs)) =
      NONE (locs,(implode (APPEND
          "Expected an exception type declaration non-termina" "l")))) /\
   (ptree_ExcType (Nd (nterm,locs) args) =
      if nterm = sum_INL camlPEG_nExcType then
        match args with
          [exnt; cdecl] ->
              OPTION_IGNORE_BIND (expect_tok exnt caml_lex_ExceptionT)
                  (OPTION_BIND (ptree_ConstrDecl cdecl) (\res.
              match res with sum_INR _ -> NONE (locs,(implode
                  "Record type exceptions are forbidden"))
              | sum_INL (nm,args) -> SOME one))
        | _ ->
            NONE (locs,(implode "Impossible: nExcType"))
      else NONE (locs,(implode (APPEND
          "Expected an exception type declaration non-termina" "l"))))
   // No types in the CakeML ast`;;

(* Ensure types get 0 or 1 arguments by wrapping >1 arguments in a tuple. *)

let ctor_tup_def = new_definition
  `ctor_tup tys =
     match tys with CONS _ (CONS _ _) -> [Attup tys]
     | _ -> tys`;;

let ptree_ExcDefinition_def = define_cases
  `(ptree_ExcDefinition (Lf (_,locs)) =
      NONE (locs,(implode
          "Expected an exception definition non-terminal"))) /\
   (ptree_ExcDefinition (Nd (nterm,locs) args) =
      if nterm = sum_INL camlPEG_nExcDefinition then
        match args with
          [exnt; cdecl] ->
              OPTION_IGNORE_BIND (expect_tok exnt caml_lex_ExceptionT)
                  (OPTION_BIND (ptree_ConstrDecl cdecl) (\res.
              match res with sum_INR _ -> NONE (locs,(implode
                  "Record type exceptions are forbidden"))
              | sum_INL (nm,args) -> SOME (Dexn locs nm (ctor_tup args))))
        | [exnt; lhsid; eq; rhsid] ->
            NONE (locs,(implode "Exception abbreviation is not supported"))
        | _ -> NONE (locs,(implode "Impossible: nExcDefinition"))
      else NONE (locs,(implode
          "Expected an exception definition non-terminal")))`;;

(* ptree_TypeRepr takes apart the rows in a datatype declaration
 * and returns a list where each element is one of:
 * - a name and a list of types (a regular constructor)
 * - a name and a list of (name*type) pairs (record constructor)
 *)

let ptree_TypeRepr_def,ptree_TypeRepr_ind = define_guess
  `(ptree_TypeRepr (Lf (_,locs)) =
      NONE (locs,(implode "Expected a type-repr non-terminal"))) /\
   (ptree_TypeRepr (Nd (nterm,locs) args) =
      if nterm = sum_INL camlPEG_nTypeRepr then
        match args with
          [bart; cdecl; reprs] ->
              OPTION_IGNORE_BIND (expect_tok bart caml_lex_BarT)
                  (OPTION_BIND (ptree_ConstrDecl cdecl) (\tr. OPTION_BIND
                  (ptree_TypeRepr reprs) (\trs.
              SOME (CONS tr trs))))
        | [a; b] -> APPEND (
              OPTION_IGNORE_BIND (expect_tok a caml_lex_BarT) (OPTION_BIND
                  (ptree_ConstrDecl b) (\tr.
              SOME [tr])))
            (OPTION_BIND (ptree_ConstrDecl a) (\tr. OPTION_BIND
                (ptree_TypeRepr b) (\trs.
              SOME (CONS tr trs))))
        | [cdecl] ->
            OPTION_BIND (ptree_ConstrDecl cdecl) (\tr.
              SOME [tr])
        | _ -> NONE (locs,(implode "Impossible: nTypeRepr"))
      else if nterm = sum_INL camlPEG_nTypeReprs then
        match args with
          [bart; cdecl] ->
              OPTION_IGNORE_BIND (expect_tok bart caml_lex_BarT)
                  (OPTION_BIND (ptree_ConstrDecl cdecl) (\ts.
              SOME [ts]))
        | [bart; cdecl; tyreps] ->
              OPTION_IGNORE_BIND (expect_tok bart caml_lex_BarT)
                  (OPTION_BIND (ptree_ConstrDecl cdecl) (\ts. OPTION_BIND
                  (ptree_TypeRepr tyreps) (\trs.
              SOME (CONS ts trs))))
        | _ -> NONE (locs,(implode "Impossible: nTypeReprs"))
      else NONE (locs,(implode "Expected a type-repr non-terminal")))`;;

let ptree_TypeInfo_def = define_cases
  `(ptree_TypeInfo (Lf (_,locs)) =
      NONE (locs,(implode "Expected a type-info non-terminal"))) /\
   (ptree_TypeInfo (Nd (nterm,locs) args) =
      if nterm = sum_INL camlPEG_nTypeInfo then
        match args with
          [eqt; arg] ->
              OPTION_IGNORE_BIND (expect_tok eqt caml_lex_EqualT)
                  (OPTION_BIND (nterm_of arg) (\n.
              if n = sum_INL camlPEG_nType then
                camlPtreeConversion_fmap sum_INL
                    (camlPtreeConversion_ptree_Type arg)
              else if n = sum_INL camlPEG_nTypeRepr then
                camlPtreeConversion_fmap sum_INR (ptree_TypeRepr arg)
              else NONE (locs,(implode "Impossible: nTypeInfo"))))
        | _ -> NONE (locs,(implode "Impossible: nTypeInfo"))
      else NONE (locs,(implode "Expected a type-info non-terminal")))`;;

let camlPtreeConversion_ptree_TypeName_def = define_cases
  `(camlPtreeConversion_ptree_TypeName (Lf (_,locs)) =
      NONE (locs,(implode "Expected type variable non-terminal"))) /\
   (camlPtreeConversion_ptree_TypeName (Nd (nterm,locs) args) =
      if nterm = sum_INL camlPEG_nTVar then
        match args with
          [tick; id] ->
              OPTION_IGNORE_BIND (expect_tok tick caml_lex_TickT) (
              ptree_Ident id)
        | _ -> NONE (locs,(implode "Impossible: nTVar"))
      else NONE (locs,(implode "Expected type variable non-terminal")))`;;

let ptree_TypeParamList_def,ptree_TypeParamList_ind = define_guess
  `ptree_TypeParamList x1 =
   match x1 with
     [] ->
     NONE (unknown_loc,(implode "Empty type parameters are not supported"))
   | [t] ->
       OPTION_IGNORE_BIND (expect_tok t caml_lex_RparT) (
       SOME [])
   | CONS p ps -> APPEND (
       OPTION_IGNORE_BIND (expect_tok p caml_lex_CommaT) (
       ptree_TypeParamList ps))
     (OPTION_BIND (camlPtreeConversion_ptree_TypeName p) (\t. OPTION_BIND
       (ptree_TypeParamList ps) (\ts.
       SOME (CONS t ts))))`;;

let ptree_TypeParams_def = define_cases
  `(ptree_TypeParams (Lf (_,locs)) =
      NONE (locs,(implode "Expected a type-parameters non-terminal"))) /\
   (ptree_TypeParams (Nd (nterm,locs) args) =
      if nterm = sum_INL camlPEG_nTypeParams then
        match args with
          [tv] ->
            camlPtreeConversion_fmap (\t. [t])
                (camlPtreeConversion_ptree_TypeName tv)
        | CONS lpar (CONS tv rest) ->
              OPTION_IGNORE_BIND (expect_tok lpar caml_lex_LparT)
                  (OPTION_BIND (camlPtreeConversion_ptree_TypeName tv) (\tn.
                  OPTION_BIND (ptree_TypeParamList rest) (\ts.
              SOME (CONS tn ts))))
        | _ -> NONE (locs,(implode "Impossible: nTypeParams"))
      else NONE (locs,(implode
          "Expected a type-parameters non-terminal")))`;;

let ptree_TypeDef_def = define_cases
  `(ptree_TypeDef (Lf (_,locs)) =
      NONE (locs,(implode "Expected a typedef non-terminal"))) /\
   (ptree_TypeDef (Nd (nterm,locs) args) =
      if nterm = sum_INL camlPEG_nTypeDef then
        match args with
          [tps; id; info] ->
            OPTION_BIND (ptree_TypeParams tps) (\tys. OPTION_BIND
                (ptree_TypeConstrName id) (\nm. OPTION_BIND (ptree_TypeInfo
                info) (\trs.
              SOME (locs,tys,nm,trs))))
        | [id; info] -> APPEND (OPTION_BIND (ptree_TypeConstrName id) (\nm.
            OPTION_BIND (ptree_TypeInfo info) (\trs.
              SOME (locs,[],nm,trs))))
            (OPTION_BIND (ptree_TypeParams id) (\tys. OPTION_BIND
                (ptree_TypeConstrName info) (\nm.
              SOME (locs,tys,nm,sum_INR []))))
        | [id] ->
            OPTION_BIND (ptree_TypeConstrName id) (\nm.
              SOME (locs,[],nm,sum_INR []))
        | _ -> NONE (locs,(implode "Impossible: nTypeDef"))
      else NONE (locs,(implode "Expected a typedef non-terminal")))`;;

let ptree_TypeDefs_def,ptree_TypeDefs_ind = define_guess
  `(ptree_TypeDefs (Lf (_,locs)) =
      NONE (locs,(implode "Expected a typedef:s non-terminal"))) /\
   (ptree_TypeDefs (Nd (nterm,locs) args) =
      if nterm = sum_INL camlPEG_nTypeDefs then
        match args with
          [td] ->
            camlPtreeConversion_fmap (\t. [t]) (ptree_TypeDef td)
        | [td; andt; tds] ->
              OPTION_IGNORE_BIND (expect_tok andt caml_lex_AndT)
                  (OPTION_BIND (ptree_TypeDef td) (\t. OPTION_BIND
                  (ptree_TypeDefs tds) (\ts.
              SOME (CONS t ts))))
        | _ -> NONE (locs,(implode "Impossible: nTypeDefs"))
      else NONE (locs,(implode "Expected a typedef:s non-terminal")))`;;

(* Builds the constructor, projection, and update functions for a record
 * datatype constructor.
 *
 * TODO It would be possible to build a pretty-printing function for the
 *      datatype, too.
 *)

let build_rec_funs_def = new_definition
  `build_rec_funs (locs,cname,fds) =
     let vars' = MAP (ast_Var o Short) fds in
     let rhs = ast_Con (SOME (Short cname))
                   (match vars' with CONS _ (CONS _ _) -> [ast_Con NONE
                     vars']
                    | _ -> vars') in
     let constr = Dlet locs (ast_Pvar (mk_record_constr_name cname fds))
                       (ITLIST (\f x. ast_Fun f x) fds rhs) in
     let pvars = MAP ast_Pvar fds in
     let pat = ast_Pcon (SOME (Short cname))
                    (match pvars with CONS _ (CONS _ _) -> [ast_Pcon NONE
                      pvars]
                     | _ -> pvars) in
     let projs = MAP (\f.
                   Dlet locs (ast_Pvar (mk_record_proj_name f cname))
                     (ast_Fun (implode "") (ast_Mat (ast_Var (Short (implode
                       "")))
                         [(pat,ast_Var (Short f))]))) fds in
     let upds = MAP (\f.
                   Dlet locs (ast_Pvar (mk_record_update_name f cname))
                     (ast_Fun (implode "") (ast_Mat (ast_Var (Short (implode
                       "")))
                         [(pat,ast_Fun f rhs)]))) fds in APPEND (CONS
                           constr projs) upds`;;

(* This function attempts to make sense of different type declarations. It has
 * grown quite convoluted. ptree_TypeDefs returns a list of tuples:
 *
 *   (locs * (tvarN list) * name * (ast_t + ast_t list + (name * ast_t) list))
 *
 * The sum type chooses between the three kinds of type declarations:
 * - type abbreviations:                  (ast_t)
 *   "type foo = bar"
 * - datatype declarations:               (ast_t list)
 *   "type foo = C of args | D | ..."
 * - record datatype declarations:        ((name # ast_t) list)
 *   "type foo = C { arg1 : type1; ...}"
 *
 * The latter two can be mixed within one declaration. Type declarations can
 * also be mutually recursive, but the type abbreviation cannot be put into
 * mutual recursion with the datatype declarations.
 *
 * A record constructor is turned into a datatype constructor and a set of
 * function definitions for projection, update and construction of values of the
 * record datatype.
 *)

let partition_types_def = new_definition
  `partition_types tdefs =
     let (abbrevs,datas) = PARTITION (\(_,_,_,trs). ISL trs) tdefs in
     let abbrevs = MAP (\(l,tvs,cn,trs). (l,tvs,cn,OUTL trs)) abbrevs in
     let datas = MAP (\(l,tvs,cn,trs). (l,tvs,cn,OUTR trs)) datas in
       (abbrevs,datas)`;;

let sort_records_def = new_definition
  `sort_records (locs,tvs,tn,tds) =
     (locs,tvs,tn,
      MAP (\tdef.
        match tdef with sum_INL (cn,tys) -> sum_INL (cn,tys)
        | sum_INR (cn,fds) -> sum_INR (cn,sort (\(l,_) (r,_). mlstring_lt
          l r) fds)) tds)`;;

let MAP_OUTR_def,MAP_OUTR_ind = define_guess
  `(MAP_OUTR f [] = []) /\
   (MAP_OUTR f (CONS (sum_INR x) xs) = CONS (f x) (MAP_OUTR f xs)) /\
   (MAP_OUTR f (CONS (sum_INL x) xs) = MAP_OUTR f xs)`;;

let extract_record_defns_def = new_definition
  `extract_record_defns (locs,tvs,tn,tds) =
     MAP_OUTR (\(cn,fds). (locs,cn,MAP FST fds)) tds`;;

(* Flattens records into regular datatype constructors. Multi-argument
 * constructors are turned into single argument constructors with tuple
 * arguments.
 *)

let strip_record_fields_def = new_definition
  `strip_record_fields (locs,tvs,cn,trs) =
     (locs,tvs,cn,MAP (\tr. match tr with sum_INL (n,tys) -> (n,ctor_tup
       tys)
                            | sum_INR (n,fds) -> (n,ctor_tup (MAP SND
                              fds))) trs)`;;

let ptree_TypeDefinition_def = define_cases
  `(ptree_TypeDefinition (Lf (_,locs)) =
      NONE (locs,(implode "Expected a type definition non-terminal"))) /\
   (ptree_TypeDefinition (Nd (nterm,locs) args) =
      if nterm = sum_INL camlPEG_nTypeDefinition then
        match args with
          [typet; nrec; tds] ->
              OPTION_IGNORE_BIND (expect_tok typet caml_lex_TypeT) (
              OPTION_IGNORE_BIND (expect_tok nrec caml_lex_NonrecT) (
              NONE (locs,(implode
                  "nonrec type definitions are not supported"))))
        | [typet; tds] ->
              OPTION_IGNORE_BIND (expect_tok typet caml_lex_TypeT)
                  (OPTION_BIND (camlPtreeConversion_fmap REVERSE
                  (ptree_TypeDefs tds)) (\tdefs. OPTION_IGNORE_BIND (
              (abbrevs,datas) << --(partition_types tdefs)) (
              OPTION_IGNORE_BIND (if ~(abbrevs = []) /\ ~(datas = []) then
                NONE (locs,mlstring_concat [
                      (implode
                          "datatypes and type abbreviations cannot be made ");
                      (implode "mutually recursive")]) else SOME one)
                          (OPTION_IGNORE_BIND (
              abbrevs << --(MAP (\(locs,tys,nm,trs). Dtabbrev locs tys nm
                  trs) abbrevs)) (
              match datas with [] -> SOME abbrevs
              | _ ->
                OPTION_IGNORE_BIND (
                  defs << --(MAP sort_records datas)) (OPTION_IGNORE_BIND
                      ((
                  recs << --FLAT) (MAP extract_record_defns defs)) (
                  OPTION_IGNORE_BIND (if ~(ALL (ALL_DISTINCT o SND o SND)
                      recs) then
                    NONE (locs,(implode
                        "record field names must be distinct"))
                  else SOME one) (OPTION_IGNORE_BIND ((
                  recfuns << --FLAT) (MAP build_rec_funs recs))
                      (OPTION_IGNORE_BIND (
                  defs << --(MAP strip_record_fields defs))
                      (OPTION_IGNORE_BIND (
                  // Datatype constructors for everything:
                  datas << --(Dtype locs (MAP SND defs))) (
                  // Record-related function definitions:
                  SOME (APPEND (CONS datas abbrevs) recfuns))))))))))))
        | _ -> NONE (locs,(implode "Impossible: nTypeDefinition"))
      else NONE (locs,(implode
          "Expected a type definition non-terminal")))`;;

(* Builds a top-level let out of a list of let bindings.
 *)

let build_dlet_def = new_definition
  `build_dlet locs binds =
     MAP (\camlPtreeConversion_bind.
            match camlPtreeConversion_bind with
              sum_INL (sum_INL (c,fs),x) ->
                let v = (implode " c") in
                Dlocal
                  [Dlet locs (ast_Pvar v) x]
                  (MAP (\f. Dlet locs (ast_Pvar f)
                              (build_record_proj c f (ast_Var (Short v))))
                                fs)
            | sum_INL (sum_INR p,x) ->
                Dlet locs p x
            | sum_INR (f,ps,bd) ->
                Dlet locs (ast_Pvar f) (build_fun_lam bd ps))
         binds`;;

let ptree_Semis_def,ptree_Semis_ind = define_guess
  `(ptree_Semis (Lf (_,locs)) =
      NONE (locs,(implode "Expected a semicolons-list non-terminal"))) /\
   (ptree_Semis (Nd (nterm,locs) args) =
      if nterm = sum_INL camlPEG_nSemis then
        match args with
          [s] -> expect_tok s caml_lex_SemisT
        | [s; r] ->
              OPTION_IGNORE_BIND (expect_tok s caml_lex_SemisT) (
              ptree_Semis r)
        | _ -> NONE (locs,(implode "Impossible: nSemis"))
      else NONE (locs,(implode
          "Expected a semicolons-list non-terminal")))`;;

(* Turns "expr;;" into "let it = expr;;". (The results of evaluating the
 * expression must end up somewhere and its strange to put in a variable with
 * no name.
 *)

let ptree_ExprDec_def = new_definition
  `ptree_ExprDec locs pt =
     camlPtreeConversion_fmap (\x. [Dlet locs (ast_Pvar (implode "it")) x])
          (camlPtreeConversion_ptree_Expr camlPEG_nExpr pt)`;;

let ptree_ValType_def = define_cases
  `(ptree_ValType (Lf (_,locs)) =
      NONE (locs,(implode
          "Expected a val-type declaration non-terminal"))) /\
   (ptree_ValType (Nd (nterm,locs) args) =
      if nterm = sum_INL camlPEG_nValType then
        match args with
          [valt; valn; colont; typ] ->
              OPTION_IGNORE_BIND (expect_tok valt caml_lex_ValT) (
              OPTION_IGNORE_BIND (expect_tok colont caml_lex_ColonT)
                  (OPTION_BIND (ptree_ValueName valn) (\nm. OPTION_BIND
                  (camlPtreeConversion_ptree_Type typ) (\ty.
              SOME one))))
        | _ -> NONE (locs,(implode "Impossible: nValType"))
      else NONE (locs,(implode
          "Expected a val-type declaration non-terminal")))`;;

let ptree_OpenMod_def = define_cases
  `(ptree_OpenMod (Lf (_,locs)) =
      NONE (locs,(implode "Expected a module-open non-terminal"))) /\
   (ptree_OpenMod (Nd (nterm,locs) args) =
      if nterm = sum_INL camlPEG_nOpenMod then
        match args with
          [opent; modpath] ->
              OPTION_IGNORE_BIND (expect_tok opent caml_lex_OpenT)
                  (OPTION_BIND (ptree_ModulePath modpath) (\ps.
              SOME one))
        | _ -> NONE (locs,(implode "Impossible: nOpenMod"))
      else NONE (locs,(implode "Expected a module-open non-terminal")))`;;

let ptree_IncludeMod_def = define_cases
  `(ptree_IncludeMod (Lf (_,locs)) =
      NONE (locs,(implode "Expected a module-open non-terminal"))) /\
   (ptree_IncludeMod (Nd (nterm,locs) args) =
      if nterm = sum_INL camlPEG_nIncludeMod then
        match args with
          [opent; modpath] ->
              OPTION_IGNORE_BIND (expect_tok opent caml_lex_IncludeT)
                  (OPTION_BIND (ptree_ModulePath modpath) (\ps.
              SOME one))
        | _ -> NONE (locs,(implode "Impossible: nIncludeMod"))
      else NONE (locs,(implode "Expected a module-open non-terminal")))`;;

(* This is currently a no-op since there are no module types. It will report
   an error if someone uses something like a functor or anything like that,
   though.
 *)
let ptree_ModuleType_def,ptree_ModuleType_ind = define_guess
  `(ptree_ModuleType (Lf (_,locs)) =
        NONE (locs,(implode
            "Expected a module-type declaration non-terminal"))) /\
   (ptree_ModuleType (Nd (nterm,locs) args) =
        if nterm = sum_INL camlPEG_nModuleType then
          match args with
            [arg] ->
              OPTION_BIND (nterm_of arg) (\peg_nt.
                if peg_nt = sum_INL camlPEG_nModTypePath then
                    OPTION_IGNORE_BIND (ptree_ModTypePath arg) (
                    SOME one)
                else if peg_nt = sum_INL camlPEG_nSigSpec then
                    OPTION_IGNORE_BIND (ptree_SigSpec arg) (
                    SOME one)
                else NONE (locs,(implode "Impossible: nModuleType")))
          | [lpar; modtype; rpar] ->
                OPTION_IGNORE_BIND (expect_tok lpar caml_lex_LparT) (
                OPTION_IGNORE_BIND (expect_tok rpar caml_lex_RparT)
                    (OPTION_BIND (ptree_ModuleType modtype) (\ty.
                SOME one)))
          | _ -> NONE (locs,(implode "Impossible: nModuleType"))
        else NONE (locs,(implode
            "Expected a module-type declaration non-terminal"))) /\
   (ptree_SigSpec (Lf (_,locs)) =
        NONE (locs,(implode "Expected a signature spec non-terminal"))) /\
   (ptree_SigSpec (Nd (nterm,locs) args) =
        if nterm = sum_INL camlPEG_nSigSpec then
          match args with
            [sigt; sigits; endt] ->
                OPTION_IGNORE_BIND (expect_tok sigt caml_lex_SigT) (
                OPTION_IGNORE_BIND (expect_tok endt caml_lex_EndT) (
                OPTION_IGNORE_BIND (ptree_SigItems sigits) (
                SOME one)))
          | [sigt; endt] ->
                OPTION_IGNORE_BIND (expect_tok sigt caml_lex_SigT) (
                OPTION_IGNORE_BIND (expect_tok endt caml_lex_EndT) (
                SOME one))
          | _ -> NONE (locs,(implode "Impossible: nSigSpec"))
        else NONE (locs,(implode
            "Expected a signature spec non-terminal"))) /\
   (ptree_SigItems (Lf (_,locs)) =
        NONE (locs,(implode
            "Expected a signature item list non-terminal"))) /\
   (ptree_SigItems (Nd (nterm,locs) args) =
        if nterm = sum_INL camlPEG_nSigItems then
          match args with
            [sigit; semis; sigits] ->
                OPTION_IGNORE_BIND (ptree_Semis semis) (OPTION_BIND
                    (ptree_SigItem sigit) (\x. OPTION_BIND (ptree_SigItems
                    sigits) (\xs.
                SOME (CONS x xs))))
          | [sigit; rest] -> APPEND (
                OPTION_IGNORE_BIND (ptree_Semis rest) (OPTION_BIND
                    (ptree_SigItem sigit) (\x.
                SOME [x])))
              (OPTION_BIND (ptree_SigItem sigit) (\x. OPTION_BIND
                  (ptree_SigItems rest) (\xs.
                SOME (CONS x xs))))
          | [sigit] -> APPEND (
                OPTION_IGNORE_BIND (ptree_Semis sigit) (
                SOME []))
              (OPTION_BIND (ptree_SigItem sigit) (\x.
                SOME [x]))
          | _ -> NONE (locs,(implode "Impossible: nSigItems"))
        else NONE (locs,(implode
            "Expected a signature item list non-terminal"))) /\
   (ptree_SigItem (Lf (_,locs)) =
        NONE (locs,(implode "Expected a signature item non-terminal"))) /\
   (ptree_SigItem (Nd (nterm,locs) args) =
        if nterm = sum_INL camlPEG_nSigItem then
          match args with
            [arg] ->
              OPTION_BIND (nterm_of arg) (\peg_nt.
                if peg_nt = sum_INL camlPEG_nTypeDefinition then
                    OPTION_IGNORE_BIND (ptree_TypeDefinition arg) (
                    SOME one)
                else if peg_nt = sum_INL camlPEG_nExcType then
                    OPTION_IGNORE_BIND (ptree_ExcType arg) (
                    SOME one)
                else if peg_nt = sum_INL camlPEG_nValType then
                    OPTION_IGNORE_BIND (ptree_ValType arg) (
                    SOME one)
                else if peg_nt = sum_INL camlPEG_nModTypeAsc then
                    OPTION_IGNORE_BIND (ptree_ModTypeAsc arg) (
                    SOME one)
                else if peg_nt = sum_INL camlPEG_nModTypeAssign then
                    OPTION_IGNORE_BIND (ptree_ModTypeAssign arg) (
                    SOME one)
                else if peg_nt = sum_INL camlPEG_nOpenMod then
                    OPTION_IGNORE_BIND (ptree_OpenMod arg) (
                    SOME one)
                else if peg_nt = sum_INL camlPEG_nIncludeMod then
                    OPTION_IGNORE_BIND (ptree_IncludeMod arg) (
                    SOME one)
                else NONE (locs,(implode "Impossible: nSigItem")))
          | _ -> NONE (locs,(implode "Impossible: nSigItem"))
        else NONE (locs,(implode
            "Expected a signature item non-terminal"))) /\
   (ptree_ModTypeAssign (Lf (_,locs)) =
        NONE (locs,(implode
            "Expected a signature assignment non-terminal"))) /\
   (ptree_ModTypeAssign (Nd (nterm,locs) args) =
        if nterm = sum_INL camlPEG_nModTypeAssign then
          match args with
            [modt; typet; name] ->
                OPTION_IGNORE_BIND (expect_tok modt caml_lex_ModuleT) (
                OPTION_IGNORE_BIND (expect_tok typet caml_lex_TypeT)
                    (OPTION_BIND (ptree_ModTypeName name) (\nm.
                SOME one)))
          | [modt; typet; name; eqt; typ] ->
                OPTION_IGNORE_BIND (expect_tok modt caml_lex_ModuleT) (
                OPTION_IGNORE_BIND (expect_tok typet caml_lex_TypeT) (
                OPTION_IGNORE_BIND (expect_tok eqt caml_lex_EqualT)
                    (OPTION_BIND (ptree_ModTypeName name) (\nm. OPTION_BIND
                    (ptree_ModuleType typ) (\ty.
                SOME one)))))
          | _ -> NONE (locs,(implode "Impossible: nModTypeAssign"))
        else NONE (locs,(implode
            "Expected a signature assignment non-terminal"))) /\
   (ptree_ModTypeAsc (Lf (_,locs)) =
        NONE (locs,(implode
            "Expected a signature ascription non-terminal"))) /\
   (ptree_ModTypeAsc (Nd (nterm,locs) args) =
        if nterm = sum_INL camlPEG_nModTypeAsc then
          match args with
            [modt; typet; modname; apps; colont; typ] ->
              NONE (locs,mlstring_concat [(implode
                  "Functor syntax is not supported");
                              (implode
                                  " (you attempted to apply a functor type)")])
          | [modt; typet; modname; colont; typ] ->
                OPTION_IGNORE_BIND (expect_tok modt caml_lex_ModuleT) (
                OPTION_IGNORE_BIND (expect_tok typet caml_lex_TypeT) (
                OPTION_IGNORE_BIND (expect_tok colont caml_lex_ColonT)
                    (OPTION_BIND (ptree_ModuleName modname) (\nm. OPTION_BIND
                    (ptree_ModuleType typ) (\ty.
                SOME one)))))
          | _ -> NONE (locs,(implode "Impossible: nModTypeAsc"))
        else NONE (locs,(implode
            "Expected a module ascription non-terminal")))
   // This is for converting functor syntax if someone ever gets around to
   // implementing that:
   // ∧
   // (ptree_ModAscApps (Lf (_, locs)) =
   // fail (locs, «Expected a moduletype-ascription list non-terminal»)) ∧
   // (ptree_ModAscApps (Nd (nterm, locs) args) =
   // if nterm = INL nModAscApps then
   // case args of
   // [arg] => fmap (λx. [x]) $ ptree_ModAscApp arg
   // | [arg; rest] =>
   // do
   // x <- ptree_ModAscApp arg;
   // xs <- ptree_ModAscApps rest;
   // return (x::xs)
   // od
   // | _ => fail (locs, «Impossible: nModAscApps»)
   // else
   // fail (locs, «Expected a moduletype-ascription list non-terminal»)) ∧
   // (ptree_ModAscApp (Lf (_, locs)) =
   // fail (locs, «Expected a moduletype-ascription non-terminal»)) ∧
   // (ptree_ModAscApp (Nd (nterm, locs) args) =
   // if nterm = INL nModAscApp then
   // case args of
   // [lpar; modname; colont; typ; rpar] =>
   // do
   // expect_tok lpar LparT;
   // expect_tok colont ColonT;
   // expect_tok rpar RparT;
   // nm <- ptree_ModuleName modname;
   // ty <- ptree_ModuleType ty;
   // return ()
   // od
   // | _ => fail (locs, «Impossible: nModAscApp»)
   // else
   // fail (locs, «Expected a moduletype-ascription non-terminal»))`;;

let peg_def = define_cases
  `(camlPtreeConversion_peg (peg_Failure locn err) = NONE (locn,implode
    err)) /\
   (camlPtreeConversion_peg (peg_Success (_:(tokens_token#locs) list) x _)
    = SOME x)`;;

(* HOL4 camlPtreeConversionScript.sml:3193-3194: the overload cmlpegexec,
   which the port expands *)

let ptree_Definition_def,ptree_Definition_ind = define_guess
  `(ptree_Definition (Lf (_,locs)) =
        NONE (locs,(implode
            "Expected a top-level definition non-terminal"))) /\
   (ptree_Definition (Nd (nterm,locs) args) =
        if nterm = sum_INL camlPEG_nDefinition then
          match args with
            [arg] -> ptree_Definition arg
          | _ -> NONE (locs,(implode "Impossible: nDefinition"))
        else if nterm = sum_INL camlPEG_nCakeMLPragma then
          match args with
            [arg] ->
              OPTION_BIND (camlPtreeConversion_destLf arg) (\lf.
                  OPTION_BIND (camlPtreeConversion_option (tokenUtils_destTOK
                  lf)) (\tk. OPTION_BIND (camlPtreeConversion_option
                  (destPragma tk)) (\str. OPTION_IGNORE_BIND (
                toks << --(lexer_fun (explode str))) (
                if EX (\t. FST t = caml_lex_LexErrorT) toks then
                  NONE (locs,(implode "The CakeML lexer failed"))
                else APPEND (OPTION_BIND (camlPtreeConversion_peg
                    (pegexec_destResult ((\n t. peg_exec cmlPEG (cmlPEG_pnt n)
                    t [] NONE [] pegexec_done pegexec_failed)
                    gram_nTopLevelDecs toks))) (\pts. OPTION_BIND
                    (camlPtreeConversion_option (oHD pts)) (\pt.
                    camlPtreeConversion_option (ptree_TopLevelDecs pt))))
                        (NONE (locs,(implode "The CakeML parser failed")))))))
          | _ -> NONE (locs,(implode "Impossible: nCakeMLPragma"))
        else if nterm = sum_INL camlPEG_nTopLet then
          match args with
            [lett; lbs] ->
                OPTION_IGNORE_BIND (expect_tok lett caml_lex_LetT)
                    (OPTION_BIND (ptree_LetBindings lbs) (\binds.
                SOME (build_dlet locs binds)))
          | _ -> NONE (locs,(implode "Impossible: nTopLet"))
        else if nterm = sum_INL camlPEG_nTopLetRec then
          match args with
            [lett; rect; lbs] ->
                OPTION_IGNORE_BIND (expect_tok lett caml_lex_LetT) (
                OPTION_IGNORE_BIND (expect_tok rect caml_lex_RecT)
                    (OPTION_BIND (ptree_LetRecBindings lbs) (\binds.
                SOME [Dletrec locs (build_letrec binds)])))
          | _ -> NONE (locs,(implode "Impossible: nTopLetRec"))
        else if nterm = sum_INL camlPEG_nTypeDefinition then
          ptree_TypeDefinition (Nd (nterm,locs) args)
        else if nterm = sum_INL camlPEG_nExcDefinition then
          camlPtreeConversion_fmap (\d. [d]) (ptree_ExcDefinition (Nd
              (nterm,locs) args))
        else if nterm = sum_INL camlPEG_nOpen then
          NONE (locs,(implode "open-declarations are not supported (yet)"))
        else if nterm = sum_INL camlPEG_nModuleTypeDef then
          match args with
            [modt; typet; name; eqt; typ] ->
                OPTION_IGNORE_BIND (expect_tok modt caml_lex_ModuleT) (
                OPTION_IGNORE_BIND (expect_tok typet caml_lex_TypeT) (
                OPTION_IGNORE_BIND (expect_tok eqt caml_lex_EqualT)
                    (OPTION_BIND (ptree_ModTypeName name) (\nm. OPTION_BIND
                    (ptree_ModuleType typ) (\ty.
                SOME [])))))
          | _ -> NONE (locs,(implode "Impossible: nModuleTypeDef"))
        else if nterm = sum_INL camlPEG_nModuleDef then
          match args with
            [modt; modid; eq; mexpr] ->
                OPTION_IGNORE_BIND (expect_tok modt caml_lex_ModuleT) (
                OPTION_IGNORE_BIND (expect_tok eq caml_lex_EqualT)
                    (OPTION_BIND (ptree_ModuleName modid) (\nm. OPTION_BIND
                    (ptree_ModExpr mexpr) (\mx.
                match mx with
                  sum_INL name ->
                    NONE (locs,(implode
                        "Structure assignment is not supported (yet?)"))
                | sum_INR decs ->
                    SOME [Dmod nm decs]))))
          | [modt; modid; colon; modty; eq; mexpr] ->
                OPTION_IGNORE_BIND (expect_tok modt caml_lex_ModuleT) (
                OPTION_IGNORE_BIND (expect_tok eq caml_lex_EqualT) (
                OPTION_IGNORE_BIND (expect_tok colon caml_lex_ColonT) (
                OPTION_IGNORE_BIND (ptree_ModuleType modty) (OPTION_BIND
                    (ptree_ModuleName modid) (\nm. OPTION_BIND (ptree_ModExpr
                    mexpr) (\mx.
                match mx with
                  sum_INL name ->
                    NONE (locs,(implode
                        "Structure assignment is not supported (yet?)"))
                | sum_INR decs ->
                    SOME [Dmod nm decs]))))))
          | _ -> NONE (locs,(implode "Impossible: nModuleDef"))
        else NONE (locs,(implode
            "Expected a top-level definition non-terminal"))) /\
   (ptree_ModExpr (Lf (_,locs)) =
        NONE (locs,(implode
            "Expected a module expression non-terminal"))) /\
   (ptree_ModExpr (Nd (nterm,locs) args) =
        if nterm = sum_INL camlPEG_nModExpr then
          match args with
            [path] -> camlPtreeConversion_fmap sum_INL (ptree_ModulePath
                path)
          | [struct; endt] ->
                OPTION_IGNORE_BIND (expect_tok struct caml_lex_StructT) (
                OPTION_IGNORE_BIND (expect_tok endt caml_lex_EndT) (
                SOME (sum_INR [])))
          | [struct; its; endt] ->
                OPTION_IGNORE_BIND (expect_tok struct caml_lex_StructT) (
                OPTION_IGNORE_BIND (expect_tok endt caml_lex_EndT)
                    (OPTION_BIND (ptree_ModuleItems its) (\is.
                SOME (sum_INR is))))
          | _ -> NONE (locs,(implode "Impossible: nModExpr"))
        else NONE (locs,(implode
            "Expected a module expression non-terminal"))) /\
   (ptree_ModuleItems (Lf (_,locs)) =
        NONE (locs,(implode
            "Expected a module item list non-terminal"))) /\
   (ptree_ModuleItems (Nd (nterm,locs) args) =
        if nterm = sum_INL camlPEG_nModuleItems then
          match args with
            [eord] -> ptree_ExprOrDefn eord
          | [eord; mit] ->
              OPTION_BIND (ptree_ExprOrDefn eord) (\d. APPEND (OPTION_BIND
                  (ptree_ModuleItem mit) (\ds.
                  SOME (APPEND d ds)))
                (
                  OPTION_IGNORE_BIND (ptree_Semis mit) (
                  SOME d)))
          | [eord; mit; semis] ->
              OPTION_BIND (ptree_ExprOrDefn eord) (\d. OPTION_BIND
                  (ptree_ModuleItem mit) (\ds.
                OPTION_IGNORE_BIND (ptree_Semis semis) (
                SOME (APPEND d ds))))
          | _ -> NONE (locs,(implode "Impossible: nModuleItems"))
        else NONE (locs,(implode
            "Expected a module item list non-terminal"))) /\
   (ptree_ModuleItem (Lf (_,locs)) =
        NONE (locs,(implode "Expected a module item non-terminal"))) /\
   (ptree_ModuleItem (Nd (nterm,locs) args) =
        if nterm = sum_INL camlPEG_nModuleItem then
          match args with
            [eord] -> ptree_ExprOrDefn eord
          | [eord; mit] ->
              OPTION_BIND (ptree_ExprOrDefn eord) (\d. OPTION_BIND
                  (ptree_ModuleItem mit) (\ds.
                SOME (APPEND d ds)))
          | _ -> NONE (locs,(implode "Impossible: nModuleItem"))
        else NONE (locs,(implode
            "Expected a module item non-terminal"))) /\
   (ptree_ExprOrDefn (Lf (_,locs)) =
        NONE (locs,(implode (APPEND
            "Expected a top-level expression/definition non-ter" "minal")))) /\
   (ptree_ExprOrDefn (Nd (nterm,locs) args) =
        if nterm = sum_INL camlPEG_nExprItems then
          match args with
            [expr] -> ptree_ExprDec locs expr
          | [semis; expr] ->
                OPTION_IGNORE_BIND (ptree_Semis semis) (
                ptree_ExprDec locs expr)
          | _ -> NONE (locs,(implode "Impossible: nExprItems"))
        else if nterm = sum_INL camlPEG_nExprItem then
          match args with [semis; expr] ->
                OPTION_IGNORE_BIND (ptree_Semis semis) (
                ptree_ExprDec locs expr)
          | _ -> NONE (locs,(implode "Impossible: nExprItem"))
        else if nterm = sum_INL camlPEG_nDefItem then
          match args with
            [defn] -> ptree_Definition defn
          | [semis; defn] ->
                OPTION_IGNORE_BIND (ptree_Semis semis) (
                ptree_Definition defn)
          | _ -> NONE (locs,(implode "Impossible: nExprItem"))
        else NONE (locs,(implode (APPEND
            "Expected a top-level expression/definition non-ter"
            "minal"))))`;;

let ptree_Start_def = define_cases
  `(ptree_Start (Lf (_,locs)) =
      NONE (locs,(implode "Expected the start non-terminal"))) /\
   (ptree_Start (Nd (nterm,locs) args) =
      if nterm = sum_INL camlPEG_nStart then
        match args with
          [] -> SOME []
        | [modits] -> ptree_ModuleItems modits
        | _ -> NONE (locs,(implode "Impossible: nStart"))
      else NONE (locs,(implode "Expected the start non-terminal")))`;;

let SmartMat_PMATCH = prove
 (`!mvar rows.
     SmartMat mvar rows =
       match rows with
         [sum_INR ast_Pany,y] -> y
       | _ -> ast_Mat (ast_Var (Short mvar)) (MAP (build_match_row mvar)
         rows)`,
  CHEAT_TAC);;

let ptree_Pattern_PMATCH = prove
 (`!p.
     camlPtreeConversion_ptree_Pattern p =
       OPTION_BIND (ptree_PPattern p) (\pp.
         match pp with
           Pp_record id fs -> SOME [sum_INL (id,fs)]
         |
           // record
           _ -> APPEND (OPTION_BIND (ppat_to_pat pp) (\ps.
             SOME (MAP sum_INR ps)))
           (NONE (unknown_loc,(implode
             "Record patterns may only appear at the top level"))))`,
  CHEAT_TAC);;

(* and the names it reads as variables are constants again *)
let _ = do_list unhide_constant
  ["id";
   "pmatch"];;

(* and the interface *)
let _ = unhide_overloads ();;
