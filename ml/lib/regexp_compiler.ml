(* ======================================================== *)
(*  regexp_compiler: ported from HOL4's
    examples/formal-languages/regular/regexp_compilerScript.sml
    A HOL4 library theory, of which the port has the definitions
    that CakeML needs.  Needed by export.ml, export_x64.ml,
    infer_t.ml, mlvector.ml, pegComplete.ml and word_bignum.ml.  *)
(* ======================================================== *)

needs "lib/balanced_map.ml";;
needs "lib/comparison.ml";;
needs "lib/mergesort.ml";;
needs "lib/sorting.ml";;
(* HOL4 ancestors outside the port: option pair relation arithmetic
   pred_set bag container list rich_list string regexp_map oset
   finite_map vec_map charset regexp *)

let regexp_compiler_vector_INDUCT,regexp_compiler_vector_RECURSION =
  define_datatype
  "regexp_compiler_vector = Vector ('a list)";;

let sub_def = cake_define
  `sub (Vector l) n = EL n l`;;

let length_def = cake_define
  `length (Vector l) = LENGTH l`;;
