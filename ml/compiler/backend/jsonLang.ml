(* ======================================================== *)
(*  jsonLang: ported from HOL4's
    compiler/backend/jsonLangScript.sml
    A definition theory, with 6 definitions, 1 datatype and no
    theorems.  Needed by backend.ml, displayLang.ml, infer_t.ml and
    presLang.ml.  *)
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
needs "lib/integer_word.ml";;

let obj_INDUCT,obj_RECURSION = define_datatype
  "obj = jsonLang_Object ((mlstring#obj) list) | jsonLang_Array (obj \
   list) | jsonLang_String (mlstring) | jsonLang_Int (int) | \
   jsonLang_Bool (bool) | jsonLang_Null";;
hol4_overload "Object" "jsonLang_Object";;
hol4_overload "Array" "jsonLang_Array";;
hol4_overload "String" "jsonLang_String";;
hol4_overload "Int" "jsonLang_Int";;
hol4_overload "Bool" "jsonLang_Bool";;
hol4_overload "Null" "jsonLang_Null";;

hol4_overload "++" "misc_Append";;

let concat_with_def = cake_define
  `concat_with x1 c =
        match x1 with
          [] -> misc_List []
        | [s] -> s
        | (s :: ss) -> s ++ (c ++ concat_with ss c)`;;

let printable_def = cake_define
  `printable c <=> ORD c >= 32 /\ ORD c < 127 /\ ~(c = (CHR 34)) /\
  ~(c = (CHR 92))`;;

let num_to_hex_digit_def = cake_define
  `num_to_hex_digit n =
     (if n < 10 then [CHR (48 + n)] else
     if n < 16 then [CHR (55 + n)] else [])`;;

let n_rev_hex_digs = cake_define_list
  [`n_rev_hex_digs 0 x = []`;
   `n_rev_hex_digs (SUC n) x = (num_to_hex_digit (x MOD 16) ++
      n_rev_hex_digs n (x DIV 16))`];;

let encode_str_def = cake_define
  `encode_str unicode s =
   (let s2 = explode s in
   if EVERY printable s2 then s else mlstring_concat (MAP (\c. if
     printable c then implode [c] else if unicode then implode ("\\u"
     ++ REVERSE (n_rev_hex_digs 4 (ORD c))) else mlstring_concat
     [(implode "\\"); toString (ORD c)]) s2))`;;

let json_to_mlstring_def = cake_define_list
  [`json_to_mlstring obj =
        (match obj with jsonLang_Object mems -> misc_List [(implode
          "{")] ++
                    concat_with (MAP mem_to_string mems) (misc_List
                      [(implode ",")]) ++
                    misc_List [(implode "}")] | jsonLang_Array obs
                      -> misc_List [(implode "[")] ++
                    concat_with (MAP json_to_mlstring obs)
                      (misc_List [(implode ",")]) ++
                    misc_List [(implode "]")] | jsonLang_String s
                      -> misc_List ([implode "\""; encode_str T s;
                      implode "\""]) | jsonLang_Int i -> misc_List
                      [toString i] | jsonLang_Bool b -> (if b then
                      misc_List [(implode "true")] else misc_List
                      [(implode "false")]) | jsonLang_Null ->
                      misc_List [(implode "null")])`;
   `mem_to_string n_obj = (let (n,obj) = n_obj in
            misc_List [implode "\""; n; implode "\":"] ++
              json_to_mlstring obj)`];;

hol4_only "++" "APPEND";;
