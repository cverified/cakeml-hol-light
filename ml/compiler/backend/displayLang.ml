(* ======================================================== *)
(*  displayLang: ported from HOL4's
    compiler/backend/displayLangScript.sml  *)
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

(* HOL4 ML code, not ported:
val sExp_size_def = fetch "-" "sExp_size_def";
*)

(* display_to_json *)
let trace_to_json_def = cake_define
  `(trace_to_json (backend_common_Cons tra num') =
     Object [((implode "name"),String (implode "Cons"));
       ((implode "num"),String (toString num'));
       ((implode "trace"),trace_to_json tra)]) /\
   (trace_to_json (Union tra1 tra2) =
     Object [((implode "name"),String (implode "Union"));
       ((implode "trace1"),trace_to_json tra1);
       ((implode "trace2"),trace_to_json tra2)]) /\
   (trace_to_json (SourceLoc sr scc er ec) =
     (let arr = MAP Int (MAP (&) [sr; scc; er; ec]) in
       Object [((implode "name"),String (implode "SourcePos"));
         ((implode "pos"),Array arr)])) /\
   (trace_to_json None = Null)`;;

(* Converts a display expression to JSON *)
let display_to_json_def = cake_define
  `(display_to_json (Item tra name es) =
     (let es' = MAP display_to_json es in
     let props = [((implode "name"),String name); ((implode
       "args"),Array es')] in
     let props' = match tra with NONE -> props | SOME t -> ((implode
       "trace"),trace_to_json t) :: props in
       Object props')) /\
   (display_to_json (String s:sExp) = String s) /\
   (display_to_json (Tuple es) =
     (let es' = MAP display_to_json es in
       Object [((implode "isTuple"),Bool T); ((implode
         "elements"),Array es')])) /\
    (display_to_json (List es) = Array (MAP display_to_json es))`;;

let display_to_str_tree_def = cake_define
  `(display_to_str_tree (Item tra name es) =
      Trees (Str name :: display_to_str_tree_list es)) /\
   (display_to_str_tree (String s:sExp) = Str s) /\
   (display_to_str_tree (Tuple es) =
      (if NULL es then Str (implode "()") else Trees
        (display_to_str_tree_list es))) /\
   (display_to_str_tree (List es) =
      (if NULL es then Str (implode "()") else Trees (MAP GrabLine
        (display_to_str_tree_list es)))) /\
   (display_to_str_tree_list [] = []) /\
   (display_to_str_tree_list (x :: xs) =
     display_to_str_tree x :: display_to_str_tree_list xs)`;;
