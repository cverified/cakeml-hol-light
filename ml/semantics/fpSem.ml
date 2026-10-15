(* ======================================================== *)
(*  fpSem: ported from HOL4's
    semantics/fpSemScript.sml  *)
(* ======================================================== *)

(*
  Definitions of the floating point operations used in CakeML.
*)

needs "lib/binary_ieee.ml";;
needs "lib/machine_ieee.ml";;
needs "semantics/ast.ml";;
(* HOL4 ancestors outside the port: (* order important because of
   FP_Add in & *) *)

let fp_cmp_INDUCT,fp_cmp_RECURSION = define_datatype
  "fp_cmp = FP_Less | FP_LessEqual | FP_Greater | FP_GreaterEqual | \
   FP_Equal";;

let fp_uop_INDUCT,fp_uop_RECURSION = define_datatype
  "fp_uop = fpSem_FP_Abs | fpSem_FP_Neg | fpSem_FP_Sqrt";;
hol4_overload "FP_Abs" "fpSem_FP_Abs";;
hol4_overload "FP_Neg" "fpSem_FP_Neg";;
hol4_overload "FP_Sqrt" "fpSem_FP_Sqrt";;

let fp_bop_INDUCT,fp_bop_RECURSION = define_datatype
  "fp_bop = fpSem_FP_Add | fpSem_FP_Sub | fpSem_FP_Mul | fpSem_FP_Div";;
hol4_overload "FP_Add" "fpSem_FP_Add";;
hol4_overload "FP_Sub" "fpSem_FP_Sub";;
hol4_overload "FP_Mul" "fpSem_FP_Mul";;
hol4_overload "FP_Div" "fpSem_FP_Div";;

let fp_top_INDUCT,fp_top_RECURSION = define_datatype
  "fp_top = FP_Fma";;

let fp_cmp_def = cake_define
  `fp_cmp cmp =
   (match cmp with ast_Lt -> fp64_lessThan | ast_Leq ->
     fp64_lessEqual | ast_Gt -> fp64_greaterThan | ast_Geq ->
     fp64_greaterEqual)`;;

let fp_cmp_comp_def = cake_define
  `fp_cmp_comp fop =
   (match fop with
     FP_Less -> fp64_lessThan | FP_LessEqual -> fp64_lessEqual |
       FP_Greater -> fp64_greaterThan | FP_GreaterEqual ->
       fp64_greaterEqual | FP_Equal -> fp64_equal)`;;

let fp_uop_comp_def = cake_define
  `fp_uop_comp fop =
   (match fop with
     fpSem_FP_Abs -> fp64_abs | fpSem_FP_Neg -> fp64_negate |
       FP_Sqrt -> fp64_sqrt roundTiesToEven)`;;

let fp_bop_comp_def = cake_define
  `fp_bop_comp fop =
   (match fop with FP_Add -> fp64_add roundTiesToEven | FP_Sub ->
     fp64_sub roundTiesToEven | FP_Mul -> fp64_mul roundTiesToEven |
     FP_Div -> fp64_div roundTiesToEven)`;;

let fpfma_def = cake_define
  `fpfma v1 v2 v3 = fp64_mul_add roundTiesToEven v2 v3 v1`;;

let fp_top_comp_def = cake_define
  `fp_top_comp fop = fpfma`;;
