(* ======================================================== *)
(*  jsonLang: ported from HOL4's
    compiler/backend/jsonLangScript.sml
    A definition theory, with 6 definitions, 1 datatype and no
    theorems.  Needed by backend.ml, data_to_word_memoryProof.ml,
    displayLang.ml, infer_t.ml and presLang.ml.  *)
(* ======================================================== *)

(*
  This module contains a datatype for representing JSON objects, and
  related functions. A JSON object can be an array of objects, a
  string, an int, a bool or null, or it can be an object enclosed
  in {}, in which case it can be viewed as a key-value store of names
  (strings) and JSON objects.
*)

needs "basis/pure/mlint.ml";;
needs "basis/pure/mlstring.ml";;
needs "lib/balanced_map.ml";;

(* the theories whose names the Ancestors blocks of the source
   bring, which are the ones that its statements read: the
   overloads of every other theory come out of the interface
   while this file loads *)
let _ = hol4_ancestors "jsonLang"
  ["mlint"; "mlstring"];;

let obj_INDUCT,obj_RECURSION = define_datatype
  "obj = jsonLang_Object ((mlstring#obj) list) | jsonLang_Array (obj \
   list) | jsonLang_String (mlstring) | jsonLang_Int (int) | \
   jsonLang_Bool (bool) | jsonLang_Null";;

(* HOL4 jsonLangScript.sml:24: the overload ++, which the port writes
   as an application of misc_Append *)

let _ = size_thms "app_list";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let concat_with_def,concat_with_ind = define_wf
  `MEASURE (\(x0,x1). list_size (app_list_size (\x. 0)) x0)`
  [`concat_with x1 c =
        match x1 with
          [] -> misc_List []
        | [s] -> s
        | (CONS s ss) -> misc_Append s (misc_Append c
          (concat_with ss c))`];;

let printable_def = new_definition
  `printable c <=> ORD c >= 32 /\ ORD c < 127 /\ ~(c = (CHR 34)) /\
  ~(c = (CHR 92))`;;

let num_to_hex_digit_def = new_definition
  `num_to_hex_digit n =
     (if n < 10 then [CHR (48 + n)] else
     if n < 16 then [CHR (55 + n)] else [])`;;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let n_rev_hex_digs,n_rev_hex_digs_ind = define_wf
  `MEASURE (\(x0,x1). (\n. n) x0)`
  [`n_rev_hex_digs 0 x = []`;
   `n_rev_hex_digs (SUC n) x = (APPEND (num_to_hex_digit (x MOD 16))
      (n_rev_hex_digs n (x DIV 16)))`];;

let encode_str_def = new_definition
  `encode_str unicode s =
   (let s2 = explode s in
   if ALL printable s2 then s else mlstring_concat (MAP (\c. if
     printable c then implode [c] else if unicode then implode
     (APPEND "\\u" (REVERSE (n_rev_hex_digs 4 (ORD c)))) else
     mlstring_concat [(implode "\\"); mlint_toString (ORD c)]) s2))`;;

let _ = size_thms "obj";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let json_to_mlstring_def,json_to_mlstring_ind = define_mutual_wf
  `MEASURE (sum_measure (\x0. obj_size x0) (\x0. obj_size3 x0))`
  [`json_to_mlstring obj =
        (match obj with jsonLang_Object mems -> misc_Append
          (misc_Append (misc_List [(implode "{")])
                    (concat_with (MAP mem_to_string mems) (misc_List
                      [(implode ",")])))
                    (misc_List [(implode "}")]) | jsonLang_Array obs
                      -> misc_Append (misc_Append (misc_List [(implode
                      "[")])
                    (concat_with (MAP json_to_mlstring obs)
                      (misc_List [(implode ",")])))
                    (misc_List [(implode "]")]) | jsonLang_String
                      s -> misc_List ([implode "\""; encode_str T s;
                      implode "\""]) | jsonLang_Int i -> misc_List
                      [mlint_toString i] | jsonLang_Bool b -> (if b
                      then misc_List [(implode "true")] else
                      misc_List [(implode "false")]) | jsonLang_Null
                      -> misc_List [(implode "null")])`;
   `mem_to_string n_obj = (let (n,obj) = n_obj in misc_Append
  (misc_List [implode "\""; n; implode "\":"]) (json_to_mlstring
  obj))`];;

(* and the overloads that this file cannot see are back in the
   interface *)
let _ = unhide_overloads ();;
