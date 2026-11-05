(* ======================================================== *)
(*  mlvector: ported from HOL4's
    basis/pure/mlvectorScript.sml
    A definition theory, with 26 definitions and 29 theorems.
    Needed by bvi_tailrecProof.ml, bvi_tmcProof.ml,
    data_to_word_memoryProof.ml and export.ml.  *)
(* ======================================================== *)

(*
  Pure functions for the Vector module.
*)

needs "basis/pure/mllist.ml";;
needs "lib/indexedLists.ml";;
needs "lib/regexp_compiler.ml";;
needs "lib/sptree.ml";;
needs "lib/ternaryComparisons.ml";;
needs "misc/misc.ml";;

(* the theories whose names the Ancestors blocks of the source
   bring, which are the ones that its statements read: the
   overloads of every other theory come out of the interface
   while this file loads *)
let _ = hol4_ancestors "mlvector"
  ["misc"; "mllist"];;

let _ = do_list hide_constant ["Equal"; "Greater"; "Less"];;

(* HOL4 mlvectorScript.sml:10-11: a theorem that HOL4 states as the
   value of an ML expression: vector_nchotomy *)

(* HOL4 mlvectorScript.sml:13-14: a theorem that HOL4 states as the
   value of an ML expression: sub_def *)

let sub_unsafe_def = cake_define
  `// same as sub_def, but translator targets Vsub_unsafe
   sub_unsafe (Vector l) n = EL n l`;;

(* HOL4 mlvectorScript.sml:20-21: a theorem that HOL4 states as the
   value of an ML expression: length_def *)

let mlvector_tabulate_def = cake_define
  `mlvector_tabulate n f = Vector (GENLIST f n)`;;
hol4_overload "tabulate" "mlvector_tabulate";;

(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
let toList_aux_def = cake_define_wf
  `MEASURE (\(vec,n). length vec - n)`
  `toList_aux vec n =
   (if length (vec) <= n then [] else sub vec n :: toList_aux vec
     (n + 1))`;;

(* HOL4 mlvectorScript.sml:36: ML code, not ported *)

let mlvector_toList_def = cake_define
  `mlvector_toList vec = toList_aux vec 0`;;
hol4_overload "toList" "mlvector_toList";;

(* [local] *)
let toList_aux_thm = prove
 (`!vec n. toList_aux vec n = (match vec with Vector vs -> DROP n vs)`,
  CHEAT_TAC);;

let toList_thm = prove
 (`!ls. toList (Vector ls) = ls`,
  CHEAT_TAC);;

let length_toList = prove
 (`LENGTH (toList vec) = length vec`,
  CHEAT_TAC);;

(* [simp] *)
let toList_11 = prove
 (`(toList l = toList l') = (l = l')`,
  CHEAT_TAC);;

let EL_toList = prove
 (`EL n (toList l) = sub l n`,
  CHEAT_TAC);;

(* [simp] *)
let toList_fromList = prove
 (`(toList (fromList l) = l) /\ (fromList (toList v) = v)`,
  CHEAT_TAC);;

let update_def = cake_define
  `update vec i x = Vector (LUPDATE x i (toList (vec)))`;;

let update_thm = prove
 (`!vec i x. sub (update vec i x) i = (if i < length vec then x else
  sub vec i)`,
  CHEAT_TAC);;


let mlvector_concat_def = cake_define
  `mlvector_concat l = Vector (FLAT (MAP toList l))`;;
hol4_overload "concat" "mlvector_concat";;

let mlvector_map_def = cake_define
  `mlvector_map vec f = Vector (MAP f (toList vec))`;;
hol4_overload "map" "mlvector_map";;

let mlvector_mapi_def = cake_define
  `mlvector_mapi vec f = Vector (MAPi f (toList vec))`;;
hol4_overload "mapi" "mlvector_mapi";;


(* [local] *)
let less_than_length_thm = prove
 (`!xs n. (n < LENGTH xs) ==> (?ys z zs. (xs = ys ++ (z :: zs)) /\
  (LENGTH ys = n))`,
  CHEAT_TAC);;

let mlvector_foldli_aux_def = cake_define_list
  [`mlvector_foldli_aux f e vec n 0 = e`;
   `mlvector_foldli_aux f e vec n (SUC len) = mlvector_foldli_aux f
  (f n (sub vec n) e) vec (n + 1) len`];;
hol4_overload "foldli_aux" "mlvector_foldli_aux";;

let mlvector_foldli_def = cake_define
  `mlvector_foldli f e vec = foldli_aux f e vec 0 (length vec)`;;
hol4_overload "foldli" "mlvector_foldli";;

(* foldli_aux_thm[local] *)
let mlvector_foldli_aux_thm = prove
 (`!f e vec n len. (n + len = length vec) ==>
     (foldli_aux f e vec n len = mllist_foldli_aux f e n (DROP n
       (toList vec)))`,
  CHEAT_TAC);;

(* foldli_thm *)
let mlvector_foldli_thm = prove
 (`!f e vec. foldli f e vec = mllist_foldli f e (toList vec)`,
  CHEAT_TAC);;

let foldl_aux_def = cake_define_list
  [`foldl_aux f e vec n 0 = e`;
   `foldl_aux f e vec n (SUC len) = foldl_aux f (f e (sub vec n))
  vec (n + 1) len`];;

let mlvector_foldl_def = cake_define
  `mlvector_foldl f e vec = foldl_aux f e vec 0 (length vec)`;;
hol4_overload "foldl" "mlvector_foldl";;

(* [local] *)
let foldl_aux_thm = prove
 (`!f e vec x len. (x + len = length vec) ==>
     (foldl_aux f e vec x len = FOLDL f e (DROP x (toList vec)))`,
  CHEAT_TAC);;

let foldl_thm = prove
 (`!f e vec. foldl f e vec = FOLDL f e (toList vec)`,
  CHEAT_TAC);;


let foldri_aux_def = cake_define_list
  [`foldri_aux f e vec 0 = e`;
   `foldri_aux f e vec (SUC len) = foldri_aux f (f len (sub vec
  len) e) vec len`];;

let foldri_def = cake_define
  `foldri f e vec = foldri_aux f e vec (length vec)`;;


(* [local] *)
let foldri_aux_thm = prove
 (`!f e vec len. len <= length vec ==>
     (foldri_aux f e vec len = FOLDRi f e (TAKE len (toList vec)))`,
  CHEAT_TAC);;

let foldri_thm = prove
 (`!f e vec. foldri f e vec = FOLDRi f e (toList vec)`,
  CHEAT_TAC);;


let foldr_aux_def = cake_define_list
  [`foldr_aux f e vec 0 = e`;
   `foldr_aux f e vec (SUC len) = foldr_aux f (f (sub vec len) e)
  vec len`];;

let foldr_def = cake_define
  `foldr f e vec = foldr_aux f e vec (length vec)`;;

(* [local] *)
let foldr_aux_thm = prove
 (`!f e vec len. len <= length vec ==>
     (foldr_aux f e vec len = ITLIST f (TAKE len (toList vec)) e)`,
  CHEAT_TAC);;

let foldr_thm = prove
 (`!f e vec. foldr f e vec = ITLIST f (toList vec) e`,
  CHEAT_TAC);;


let findi_aux_def = cake_define_list
  [`findi_aux f vec n 0 = NONE`;
   `findi_aux f vec n (SUC len) =
      (if f n (sub vec n) then SOME (n,(sub vec n)) else
        findi_aux f vec (n + 1) len)`];;

let mlvector_findi_def = cake_define
  `mlvector_findi f vec = findi_aux f vec 0 (length vec)`;;
hol4_overload "findi" "mlvector_findi";;


let find_aux_def = cake_define_list
  [`find_aux f vec n 0 = NONE`;
   `find_aux f vec n (SUC len) =
      (if f (sub vec n) then SOME (sub vec n) else find_aux f
        vec (n + 1) len)`];;

let find_def = cake_define
  `find f vec = find_aux f vec 0 (length vec)`;;

(* [local] *)
let find_aux_thm = prove
 (`!f vec n len. (n + len = length vec) ==> (find_aux f vec n len =
  FIND f (DROP n (toList vec)))`,
  CHEAT_TAC);;

let find_thm = prove
 (`!f vec. find f vec = FIND f (toList vec)`,
  CHEAT_TAC);;


let exists_aux_def = cake_define_list
  [`exists_aux f vec n 0 = F`;
   `exists_aux f vec n (SUC len) =
        (if f (sub vec n) then T else exists_aux f vec (n + 1)
          len)`];;

let mlvector_exists_def = cake_define
  `mlvector_exists f vec = exists_aux f vec 0 (length vec)`;;

(* [local] *)
let exists_aux_thm = prove
 (`!f vec n len.
     n + len = length vec ==>
     exists_aux f vec n len = EXISTS f (DROP n (toList vec))`,
  CHEAT_TAC);;

let exists_thm = prove
 (`!f vec. mlvector_exists f vec = EXISTS f (toList vec)`,
  CHEAT_TAC);;

let all_aux_def = cake_define_list
  [`all_aux f vec n 0 = T`;
   `all_aux f vec n (SUC len) =
        (if f (sub vec n) then all_aux f vec (n + 1) len else
          F)`];;

let all_def = cake_define
  `all f vec = all_aux f vec 0 (length vec)`;;

(* [local] *)
let all_aux_thm = prove
 (`!f vec n len.
     n + len = length vec ==>
     all_aux f vec n len = EVERY f (DROP n (toList vec))`,
  CHEAT_TAC);;

let all_thm = prove
 (`!f vec. all f vec = EVERY f (toList vec)`,
  CHEAT_TAC);;

let mlvector_collate_aux_def = cake_define_list
  [`mlvector_collate_aux f vec1 vec2 n ord 0 = ord`;
   `mlvector_collate_aux f vec1 vec2 n ord (SUC len) =
        (if f (sub vec1 n) (sub vec2 n) = EQUAL then
          mlvector_collate_aux f vec1 vec2 (n + 1) ord len else f
          (sub vec1 n) (sub vec2 n))`];;
hol4_overload "collate_aux" "mlvector_collate_aux";;

let mlvector_collate_def = cake_define
  `mlvector_collate f vec1 vec2 =
   (if (length vec1) < (length vec2) then mlvector_collate_aux f
     vec1 vec2 0 LESS (length vec1) else if (length vec2) < (length
     vec1) then mlvector_collate_aux f vec1 vec2 0 GREATER (length
     vec2) else mlvector_collate_aux f vec1 vec2 0 EQUAL (length
     vec2))`;;
hol4_overload "collate" "mlvector_collate";;

(* collate_aux_less_thm[local] *)
let mlvector_collate_aux_less_thm = prove
 (`!f vec1 vec2 n len.
     n + len = length vec1 /\ length vec1 < length vec2 ==>
     mlvector_collate_aux f vec1 vec2 n LESS len =
     mllist_collate f (DROP n (toList vec1)) (DROP n (toList vec2))`,
  CHEAT_TAC);;

(* collate_aux_equal_thm[local] *)
let mlvector_collate_aux_equal_thm = prove
 (`!f vec1 vec2 n len.
     n + len = length vec2 /\ length vec1 = length vec2 ==>
     mlvector_collate_aux f vec1 vec2 n EQUAL len =
     mllist_collate f (DROP n (toList vec1)) (DROP n (toList vec2))`,
  CHEAT_TAC);;

(* collate_aux_greater_thm[local] *)
let mlvector_collate_aux_greater_thm = prove
 (`!f vec1 vec2 n len.
     n + len = length vec2 /\ length vec2 < length vec1 ==>
     mlvector_collate_aux f vec1 vec2 n GREATER len =
       mllist_collate f (DROP n (toList vec1)) (DROP n (toList
         vec2))`,
  CHEAT_TAC);;

(* collate_thm *)
let mlvector_collate_thm = prove
 (`!f vec1 vec2.
     collate f vec1 vec2 = mllist_collate f (toList vec1) (toList
       vec2)`,
  CHEAT_TAC);;

(* and the names that this file reads as variables are constants again *)
let _ = do_list unhide_constant
  ["Equal";
   "Greater";
   "Less"];;

(* and the overloads that this file cannot see are back in the
   interface *)
let _ = unhide_overloads ();;
