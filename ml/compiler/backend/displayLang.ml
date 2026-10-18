(* ======================================================== *)
(*  displayLang: ported from HOL4's
    compiler/backend/displayLangScript.sml
    A definition theory, with 3 definitions, 1 datatype and 1
    theorem.  Needed by presLang.ml.  *)
(* ======================================================== *)

(*
  displayLang is a stepping stone before pretty printing any of
  the compiler's intermediate languages for inspection by humans. The
  design of displayLang is intentionally very simple. The language
  supports Tuples, Items (e.g. datatype constructors), and Lists.
*)

needs "basis/pure/mlint.ml";;
needs "basis/pure/mlsexp.ml";;
needs "basis/pure/mlstring.ml";;
needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/jsonLang.ml";;
needs "lib/integer_word.ml";;
(* HOL4 ancestors outside the port: (* for str_tree *) *)

let sExp_INDUCT,sExp_RECURSION = define_datatype
  "sExp = displayLang_Item (tra option) (mlstring) (sExp list) | \
   displayLang_String (mlstring) | displayLang_Tuple (sExp list) | \
   displayLang_List (sExp list)";;
hol4_overload "Item" "displayLang_Item";;
hol4_overload "String" "displayLang_String";;
hol4_overload "Tuple" "displayLang_Tuple";;
hol4_overload "List" "displayLang_List";;

(* HOL4 displayLangScript.sml:21: ML code, not ported *)

(* display_to_json *)
let trace_to_json_def = cake_define_list
  [`trace_to_json (backend_common_Cons tra num') =
        jsonLang_Object [((implode "name"),String (implode "Cons"));
          ((implode "num"),String (toString num'));
          ((implode "trace"),trace_to_json tra)]`;
   `trace_to_json (backend_common_Union tra1 tra2:tra) =
        jsonLang_Object [((implode "name"),String (implode
          "Union"));
          ((implode "trace1"),trace_to_json tra1);
          ((implode "trace2"),trace_to_json tra2)]`;
   `trace_to_json (backend_common_SourceLoc sr scc er ec) =
        (let arr = MAP jsonLang_Int (MAP (&) [sr; scc; er; ec]) in
          jsonLang_Object [((implode "name"),String (implode
            "SourcePos"));
            ((implode "pos"),jsonLang_Array arr)])`;
   `trace_to_json (backend_common_None:tra) = jsonLang_Null`];;

let MEM_sExp_size = cake_theorem "MEM_sExp_size"
  (fun () ->
    `!es a. MEM a es ==> sExp_size a < sExp1_size es`)
  CHEAT_TAC;;

(* Converts a display expression to JSON *)
let display_to_json_def = cake_define
  `(display_to_json (displayLang_Item tra name es) =
     (let es' = MAP display_to_json es in
     let props = [((implode "name"),String name); ((implode
       "args"),jsonLang_Array es')] in
     let props' = (match tra with NONE -> props | SOME t -> ((implode
       "trace"),trace_to_json t) :: props) in
       jsonLang_Object props')) /\
   (display_to_json (String s:sExp) = String s) /\
   (display_to_json (displayLang_Tuple es) =
     (let es' = MAP display_to_json es in
       jsonLang_Object [((implode "isTuple"),jsonLang_Bool T);
         ((implode "elements"),jsonLang_Array es')])) /\
    (display_to_json (List es) = jsonLang_Array (MAP
      display_to_json es))`;;

let display_to_str_tree_def = cake_define_list
  [`display_to_str_tree (displayLang_Item tra name es) =
         mlsexp_Trees (mlsexp_Str name ::
           display_to_str_tree_list es)`;
   `display_to_str_tree (String s:sExp) = mlsexp_Str s`;
   `display_to_str_tree (displayLang_Tuple es:sExp) =
         (if NULL es then mlsexp_Str (implode "()") else
           mlsexp_Trees (display_to_str_tree_list es))`;
   `display_to_str_tree (List es:sExp) =
         (if NULL es then mlsexp_Str (implode "()") else
           mlsexp_Trees (MAP mlsexp_GrabLine
           (display_to_str_tree_list es)))`;
   `display_to_str_tree_list [] = []`;
   `display_to_str_tree_list (x :: xs) =
        display_to_str_tree x :: display_to_str_tree_list xs`];;
