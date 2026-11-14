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
(* for str_tree *)
needs "basis/pure/mlstring.ml";;
needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/jsonLang.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "displayLang"
  ["backend_common"; "jsonLang"; "mlint"; "mlsexp"];;

let sExp_INDUCT,sExp_RECURSION = define_datatype
  "sExp =
     display_Item (tra option) mlstring (sExp list)
   | display_String mlstring
   | display_Tuple (sExp list)
   | display_List (sExp list)";;

(* HOL4 displayLangScript.sml:21: ML code, not ported *)

(* display_to_json *)
let trace_to_json_def,trace_to_json_ind = define_rec
  `(trace_to_json (backend_common_Cons tra num') =
        json_Object [((implode "name"),json_String (implode "Cons"));
          ((implode "num"),json_String (num_to_str num'));
          ((implode "trace"),trace_to_json tra)]) /\
   (trace_to_json (backend_common_Union tra1 tra2) =
        json_Object [((implode "name"),json_String (implode "Union"));
          ((implode "trace1"),trace_to_json tra1);
          ((implode "trace2"),trace_to_json tra2)]) /\
   (trace_to_json (backend_common_SourceLoc sr scc er ec) =
        let arr = MAP json_Int (MAP (&) [sr; scc; er; ec]) in
          json_Object [((implode "name"),json_String (implode
              "SourcePos"));
            ((implode "pos"),json_Array arr)]) /\
   // TODO: cancel entire trace when None, or verify that None will always be at
   // * the top level of a trace.
   (trace_to_json backend_common_None = json_Null)`;;

make_size "sExp";;
let MEM_sExp_size = prove
 (`!es a. MEM a es ==> sExp_size a < list_size sExp_size es`,
  CHEAT_TAC);;

(* Converts a display expression to JSON *)
let display_to_json_def,display_to_json_ind = define_shaped_rec
  "nested"
  `(display_to_json (display_Item tra name es) =
        let es' = MAP display_to_json es in
        let props = [((implode "name"),json_String name); ((implode
            "args"),json_Array es')] in
        let props' = (match tra with NONE -> props
                       | SOME t -> CONS ((implode "trace"),trace_to_json t)
                           props) in
          json_Object props') /\
   (display_to_json (display_String s:sExp) = json_String s) /\
   (display_to_json (display_Tuple es) =
        let es' = MAP display_to_json es in
          json_Object [((implode "isTuple"),json_Bool T); ((implode
              "elements"),json_Array es')]) /\
   (display_to_json (display_List es) = json_Array (MAP display_to_json
    es))`;;

let display_to_str_tree_def,display_to_str_tree_ind = define_rec
  `(display_to_str_tree (display_Item tra name es) =
         mlsexp_Trees (CONS (mlsexp_Str name) (display_to_str_tree_list
             es))) /\
   (display_to_str_tree (display_String s:sExp) = mlsexp_Str s) /\
   (display_to_str_tree (display_Tuple es) =
         if NULL es then mlsexp_Str (implode "()")
         else mlsexp_Trees (display_to_str_tree_list es)) /\
   (display_to_str_tree (display_List es) =
         if NULL es then mlsexp_Str (implode "()")
         else mlsexp_Trees (MAP mlsexp_GrabLine
             (display_to_str_tree_list es))) /\
   (display_to_str_tree_list [] = []) /\
   (display_to_str_tree_list (CONS x xs) = CONS (display_to_str_tree x)
    (display_to_str_tree_list xs))`;;

(* and the interface *)
let _ = unhide_overloads ();;
