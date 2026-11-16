(* ======================================================== *)
(*  mlprettyprinter: ported from HOL4's
    basis/pure/mlprettyprinterScript.sml
    A definition theory, with 33 definitions, 2 datatypes and 4
    theorems.  Needed by PrettyPrinterProg.ml, RatProg.ml,
    addPrintVals.ml, camlPtreeConversion.ml and typeDecToPP.ml.  *)
(* ======================================================== *)

(*
  Types and pure functions for pretty printing

  Most of these functions are translated in the first phase of the basis
  setup so that default pretty-printing (c.f. typeDecToPP) will
  work from then on.
*)

needs "basis/pure/mlint.ml";;
needs "basis/pure/mlstring.ml";;
needs "basis/pure/mlvector.ml";;
needs "compiler/backend/jsonLang.ml";;
needs "compiler/backend/pattern_matching/pattern_semantics.ml";;
needs "lib/integer_word.ml";;
needs "lib/peg.ml";;
needs "lib/regexp_compiler.ml";;
needs "lib/sptree.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "mlprettyprinter"
  ["mlint"; "mlstring"; "mlvector"];;
(* HOL4 ancestors outside the port: words *)

(* Data for pretty-printing. The bool indicates if this data needs to be
   wrapped in parens, if this data is given as an argument to an application.
*)
let pp_data_INDUCT,pp_data_RECURSION = define_datatype
  "pp_data =
     PP_Data bool (mlstring app_list)";;

let pp_token_def = new_definition
  `pp_token s = PP_Data F (misc_List [s])`;;

let pp_fun_def = new_definition
  `pp_fun = pp_token (implode "<fun>")`;;

let pp_unprintable_def = new_definition
  `pp_unprintable s = PP_Data F (misc_List [(implode
  "<val of unprintable type "); s; (implode ">")])`;;

(* there is a plan to replace this with an impure extensible implementation *)
let pp_exn_def = new_definition
  `pp_exn e = pp_token (implode "<exn>")`;;

let app_intersperse_def,app_intersperse_ind = define_guess
  `(app_intersperse c [] = misc_Nil) /\
   (app_intersperse c [x] = x) /\
   (app_intersperse c (CONS x (CONS y zs)) = misc_Append (misc_Append x
    (misc_List [c])) (app_intersperse c (CONS y zs)))`;;

let pp_contents_def = new_definition
  `pp_contents (PP_Data _ xs) = xs`;;

let pp_no_parens_def = new_definition
  `pp_no_parens pp = PP_Data F (pp_contents pp)`;;

let app_list_wrap_def = new_definition
  `app_list_wrap l xs r = misc_Append (misc_List [l]) (misc_Append xs
  (misc_List [r]))`;;

let pp_paren_contents_def = new_definition
  `pp_paren_contents x1 =
   match x1 with
     PP_Data F xs -> xs
   | PP_Data T xs -> app_list_wrap (implode "(") xs (implode ")")`;;

let pp_paren_tuple_def = new_definition
  `pp_paren_tuple pps = PP_Data F (app_list_wrap (implode "(")
     (app_intersperse (implode ", ") (MAP pp_contents pps))
     (implode ")"))`;;

let pp_spaced_block_def = new_definition
  `pp_spaced_block xs = PP_Data (LENGTH xs > 1)
     (app_intersperse (implode " ") (MAP pp_paren_contents xs))`;;

let pp_app_block_def = new_definition
  `pp_app_block nm xs = pp_spaced_block (CONS (pp_token nm) xs)`;;

let pp_val_eq_def = new_definition
  `pp_val_eq nm pp_f v ty = PP_Data F (misc_Append
     (misc_List [(implode "val "); nm; (implode " = ")])
     (misc_Append (pp_contents (pp_f v)) (misc_List [(implode ": "); ty;
       (implode "\n")])))`;;

let pp_val_hidden_type_def = new_definition
  `pp_val_hidden_type nm ty = PP_Data F
     (misc_List [(implode "val "); nm; (implode " <not printable> : ");
       ty; (implode "\n")])`;;

let pp_failure_message_def = new_definition
  `pp_failure_message s = PP_Data F
     (misc_List [(implode "<failure: "); s; (implode ">\n")])`;;

let pp_list_def = new_definition
  `pp_list f xs = PP_Data F (app_list_wrap (implode "[")
     (app_intersperse (implode "; ") (MAP (\x. pp_contents (f x)) xs))
     (implode "]"))`;;

let pp_unit_def = new_definition
  `pp_unit u = pp_token (implode "()")`;;

(* the termination relation that HOL4 gives is
     MEASURE (\(i,s). strlen s - i)
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 mlprettyprinterScript.sml:110-115: the tactic that proves the
   termination *)
let escape_str_app_list_def,escape_str_app_list_ind = define_guess
  `escape_str_app_list i s = match str_findi (\c. IS_SOME (char_escape_seq c))
  i s with
     NONE -> misc_List [substring s i (strlen s - i)]
   | SOME j -> misc_Append (misc_List [substring s i (j - i);
         match char_escape_seq (strsub s j) with NONE -> (implode "") | SOME
           s -> s])
     (escape_str_app_list (j + 1) s)`;;

(* [local] *)
let findi_map_escape = prove
 (`!P i s. P = IS_SOME o char_escape_seq ==>
   FLAT (MAP char_escaped (DROP i (explode s))) =
   (match str_findi P i s with
     NONE -> DROP i (explode s)
   | SOME j ->
     APPEND (APPEND (TAKE (j - i) (DROP i (explode s))) (match
       char_escape_seq (strsub s j) with NONE -> "" | SOME s -> explode s))
       (FLAT (MAP char_escaped (DROP (j + 1) (explode s)))))`,
  CHEAT_TAC);;

let escape_str_app_list_thm = prove
 (`!i s. mlvector_concat (append (escape_str_app_list i s)) =
   implode (FLAT (MAP char_escaped (DROP i (explode s))))`,
  CHEAT_TAC);;

let pp_string_def = new_definition
  `pp_string s = PP_Data F (app_list_wrap (implode "\"")
  (escape_str_app_list 0 s) (implode "\""))`;;

let pp_string_thm = prove
 (`mlvector_concat (append (pp_contents (pp_string s))) = escape_str s`,
  CHEAT_TAC);;

let pp_bool_def = new_definition
  `pp_bool b = PP_Data F (misc_List [if b then (implode "True") else
  (implode "False")])`;;

(* pretty-printers for the pretty-printer types *)
let pp_app_list_def,pp_app_list_ind = define_guess
  `(pp_app_list f (misc_List xs) = pp_app_block (implode "List")
      [pp_list f xs]) /\
   (pp_app_list f misc_Nil = pp_token (implode "Nil")) /\
   (pp_app_list f (misc_Append x y) = pp_app_block (implode "Append")
      [pp_app_list f x; pp_app_list f y])`;;

let pp_pp_data_def = new_definition
  `pp_pp_data (PP_Data b d) = pp_app_block (implode "PP_Data")
     [pp_bool b; pp_app_list pp_string d]`;;

let pp_char_def = new_definition
  `pp_char c = PP_Data F (misc_List [implode "#\""; match char_escape_seq c
  with NONE -> implode [c]
     | SOME s -> s; implode "\""])`;;

let pp_char_thm = prove
 (`mlvector_concat (append (pp_contents (pp_char c))) = escape_char c`,
  CHEAT_TAC);;

let pp_int_def = new_definition
  `pp_int (i:int) = pp_token (mlint_toString i)`;;

let pp_word8_def = new_definition
  `pp_word8 (w:8 word) = pp_app_block (implode "Word8.fromInt") [pp_int (w2i
  w)]`;;

let pp_word64_def = new_definition
  `pp_word64 (w:64 word) = pp_app_block (implode "Word64.fromInt") [pp_int
  (w2i w)]`;;

(* these initial pure and useless pps might be replaced later *)
let pp_array_def = new_definition
  `pp_array f arr = pp_token (implode "<array>")`;;

let pp_ref_def = new_definition
  `pp_ref f r = pp_token (implode "<ref>")`;;

let pp_word8array_def = new_definition
  `pp_word8array arr = pp_token (implode "<w8array>")`;;

let pp_vector_def = new_definition
  `pp_vector f v = pp_app_block (implode "Vector.fromList")
     [pp_list f (mlvector_toList v)]`;;

(* values of this type should never appear in programs.
   it is used to monomorphise some expressions so they
   can be printed safely. *)
let default_type_INDUCT,default_type_RECURSION = define_datatype
  "default_type =
     Default_Type";;

let pp_default_type_def = new_definition
  `pp_default_type v = match v with Default_Type ->
     pp_token (implode
       "<val of default type: this should be impossible>")`;;

let fromRat_def = new_definition
  `fromRat ((n:int),(d:num)) =
   if d = 1 then misc_List [mlint_toString n]
   else misc_List [mlint_toString n; (implode "/"); mlint_toString (&d)]`;;

let fromOption_def = new_definition
  `fromOption f opt =
   match opt with
       NONE -> misc_List [(implode "NONE")]
     | SOME x -> misc_Append (misc_List [(implode "SOME ")]) (f x)`;;

(* and the interface *)
let _ = unhide_overloads ();;
