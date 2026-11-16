(* ======================================================== *)
(*  cfFFIType: ported from HOL4's
    characteristic/cfFFITypeScript.sml
    A definition theory, with 9 definitions, 2 datatypes and 16
    theorems.  Needed by 83 files of the port.  *)
(* ======================================================== *)

(*
  Defines a type that can be used for embedding different FFI models
  for parts of the FFI state.
*)

needs "basis/pure/mlstring.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "cfFFIType"
  ["mlstring"];;

(*

This file defines a type that behaves like the following one:

  ffi = Str mlstring
      | Num num
      | Cons ffi ffi
      | List (ffi list)
      | Stream (num llist)
      | Fun (ffi_inner -> ffi)
      | Inner ffi_inner

  ffi_inner = iStr mlstring
            | iNum num
            | iCons ffi_inner ffi_inner
            | iList (ffi_inner list)
            | iStream (num llist)

The ffi type is missing an nchotomy thm and an induction thm, but the
important injectivity (suffix: "_11") are here.

*)

let ffi_inner_INDUCT,ffi_inner_RECURSION = define_datatype
  "ffi_inner =
     iStr mlstring
   | iNum num
   | iCons ffi_inner ffi_inner
   | iList (ffi_inner list)
   | iStream (num llist)";;

let ffi_INDUCT,ffi_RECURSION = define_datatype
  "ffi =
     FFI_TYPE (ffi_inner->ffi_inner)";;

let ffi_app_def = new_definition
  `ffi_app x n = match x with FFI_TYPE f -> f n`;;

(* constructors *)

let num_def = new_definition
  `((num_of_int i):ffi) =
     FFI_TYPE (\n. if n = iNum 0 then iNum 0 else iNum i)`;;

let str_def = new_definition
  `((cfFFIType_Str i):ffi) =
     FFI_TYPE (\n. if n = iNum 0 then iNum 1 else iStr i)`;;

let cons_def = new_definition
  `((cfFFIType_Cons (x:ffi) (y:ffi)):ffi) =
     FFI_TYPE (\n. if n = iNum 0 then iNum 2 else match n with iCons (iNum
       0) m -> ffi_app x m
                     | iCons (iNum 1) m -> ffi_app y m
                     | _ -> iNum 0)`;;

let list_def = new_definition
  `((cfFFIType_List (xs:ffi list)):ffi) =
     FFI_TYPE (\n. if n = iNum 0 then iNum 3 else if n = iNum 1 then iNum
       (LENGTH xs) else match n with iCons (iNum k) m -> ffi_app (EL k xs) m
                     | _ -> iNum 0)`;;

let stream_def = new_definition
  `((Stream i):ffi) =
     FFI_TYPE (\n. if n = iNum 0 then iNum 4 else iStream i)`;;

let fun_def = new_definition
  `((cfFFIType_Fun (f:ffi_inner->ffi)):ffi) =
     FFI_TYPE (\n. if n = iNum 0 then iNum 5 else match n with iCons x y ->
       ffi_app (f x) y
                     | _ -> iNum 0)`;;

let inner_def = new_definition
  `((Inner i):ffi) =
     FFI_TYPE (\n. if n = iNum 0 then iNum 6 else i)`;;

(* injectivity *)

(* Num_11 *)
let num_11 = prove
 (`!n1 n2. num_of_int n1 = num_of_int n2 <=> n1 = n2`,
  CHEAT_TAC);;
add_simp num_11;;

(* Str_11 *)
let str_11 = prove
 (`!n1 n2. cfFFIType_Str n1 = cfFFIType_Str n2 <=> n1 = n2`,
  CHEAT_TAC);;
add_simp str_11;;

(* Cons_11 *)
let cons_11 = prove
 (`!x1 x2 y1 y2. cfFFIType_Cons x1 x2 = cfFFIType_Cons y1 y2 <=> x1 = y1
  /\ x2 = y2`,
  CHEAT_TAC);;
add_simp cons_11;;

(* List_11 *)
let list_11 = prove
 (`!xs ys. misc_List xs = misc_List ys <=> xs = ys`,
  CHEAT_TAC);;
add_simp list_11;;

(* Stream_11 *)
let stream_11 = prove
 (`!n1 n2. Stream n1 = Stream n2 <=> n1 = n2`,
  CHEAT_TAC);;
add_simp stream_11;;

(* Fun_11 *)
let fun_11 = prove
 (`cfFFIType_Fun f1 = cfFFIType_Fun f2 <=> f1 = f2`,
  CHEAT_TAC);;
add_simp fun_11;;

(* Inner_11 *)
let inner_11 = prove
 (`!n1 n2. Inner n1 = Inner n2 <=> n1 = n2`,
  CHEAT_TAC);;
add_simp inner_11;;

(* distinctness *)

(* HOL4 cfFFITypeScript.sml:162-167: a theorem that HOL4 states as the value
   of an ML expression: ffi_distinct *)

(* destructors *)
(* [local] *)
let destNum_exists = prove
 (`?destNum.
     (!n. destNum (num_of_int n) = SOME n) /\
     (!s. destNum (cfFFIType_Str s) = NONE) /\
     (!x y. destNum (cfFFIType_Cons x y) = NONE) /\
     (!l. destNum (misc_List l) = NONE) /\
     (!ll. destNum (Stream ll) = NONE) /\
     (!f. destNum (cfFFIType_Fun f) = NONE) /\
     (!i. destNum (Inner i) = NONE)`,
  CHEAT_TAC);;
(* HOL4 cfFFITypeScript.sml:185-188: ML code, not ported *)

(* [local] *)
let destStr_exists = prove
 (`?destStr.
     (!n. destStr (num_of_int n) = NONE) /\
     (!s. destStr (cfFFIType_Str s) = SOME s) /\
     (!x y. destStr (cfFFIType_Cons x y) = NONE) /\
     (!l. destStr (misc_List l) = NONE) /\
     (!ll. destStr (Stream ll) = NONE) /\
     (!f. destStr (cfFFIType_Fun f) = NONE) /\
     (!i. destStr (Inner i) = NONE)`,
  CHEAT_TAC);;
(* HOL4 cfFFITypeScript.sml:205-208: ML code, not ported *)

let destStr_o_Str = prove
 (`destStr o cfFFIType_Str = SOME`,
  CHEAT_TAC);;
add_simp destStr_o_Str;;

(* [local] *)
let destCons_exists = prove
 (`?destCons.
     (!n. destCons (num_of_int n) = NONE) /\
     (!s. destCons (cfFFIType_Str s) = NONE) /\
     (!x y. destCons (cfFFIType_Cons x y) = SOME (x,y)) /\
     (!l. destCons (misc_List l) = NONE) /\
     (!ll. destCons (Stream ll) = NONE) /\
     (!f. destCons (cfFFIType_Fun f) = NONE) /\
     (!i. destCons (Inner i) = NONE)`,
  CHEAT_TAC);;
(* HOL4 cfFFITypeScript.sml:233-236: ML code, not ported *)

(* [local] *)
let destList_exists = prove
 (`?destList.
     (!n. destList (num_of_int n) = NONE) /\
     (!s. destList (cfFFIType_Str s) = NONE) /\
     (!x y. destList (cfFFIType_Cons x y) = NONE) /\
     (!l. destList (misc_List l) = SOME l) /\
     (!ll. destList (Stream ll) = NONE) /\
     (!f. destList (cfFFIType_Fun f) = NONE) /\
     (!i. destList (Inner i) = NONE)`,
  CHEAT_TAC);;
(* HOL4 cfFFITypeScript.sml:253-256: ML code, not ported *)

(* [local] *)
let destStream_exists = prove
 (`?destStream.
     (!n. destStream (num_of_int n) = NONE) /\
     (!s. destStream (cfFFIType_Str s) = NONE) /\
     (!x y. destStream (cfFFIType_Cons x y) = NONE) /\
     (!l. destStream (misc_List l) = NONE) /\
     (!ll. destStream (Stream ll) = SOME ll) /\
     (!f. destStream (cfFFIType_Fun f) = NONE) /\
     (!i. destStream (Inner i) = NONE)`,
  CHEAT_TAC);;
(* HOL4 cfFFITypeScript.sml:273-276: ML code, not ported *)

(* [local] *)
let destFun_exists = prove
 (`?destFun.
     (!n. destFun (num_of_int n) = NONE) /\
     (!s. destFun (cfFFIType_Str s) = NONE) /\
     (!x y. destFun (cfFFIType_Cons x y) = NONE) /\
     (!l. destFun (misc_List l) = NONE) /\
     (!ll. destFun (Stream ll) = NONE) /\
     (!f. destFun (cfFFIType_Fun f) = SOME f) /\
     (!i. destFun (Inner i) = NONE)`,
  CHEAT_TAC);;
(* HOL4 cfFFITypeScript.sml:293-296: ML code, not ported *)

(* [local] *)
let destInner_exists = prove
 (`?destInner.
     (!n. destInner (num_of_int n) = NONE) /\
     (!s. destInner (cfFFIType_Str s) = NONE) /\
     (!x y. destInner (cfFFIType_Cons x y) = NONE) /\
     (!l. destInner (misc_List l) = NONE) /\
     (!ll. destInner (Stream ll) = NONE) /\
     (!f. destInner (cfFFIType_Fun f) = NONE) /\
     (!i. destInner (Inner i) = SOME i)`,
  CHEAT_TAC);;
(* HOL4 cfFFITypeScript.sml:313-316: ML code, not ported *)

let dest_iStr_def = new_definition
  `dest_iStr (iStr s) = s`;;
add_simp dest_iStr_def;;

(* clean up *)

(* HOL4 cfFFITypeScript.sml:324-325: ML code, not ported *)

(* HOL4 cfFFITypeScript.sml:327: ML code, not ported *)

(* and the interface *)
let _ = unhide_overloads ();;
