(* ======================================================== *)
(*  multiword: ported from HOL4's
    examples/machine-code/multiword/multiwordScript.sml  *)
(*  Of this HOL4 library theory only the definitions that the
    CakeML port needs are ported.  *)
(* ======================================================== *)

needs "lib/ASCIInumbers.ml";;
(* HOL4 ancestors outside the port: pred_set res_quan arithmetic words bit pair list rich_list relation pair integer fcp *)
let i2mw_def = cake_define
  `i2mw i = ((i < 0),n2mw (num_of_int (abs i)))`;;
let mw_op_INDUCT,mw_op_RECURSION = define_datatype
  "mw_op = multiword_Add | multiword_Sub | multiword_Mul | multiword_Div | multiword_Mod | multiword_Lt | multiword_Eq | multiword_Dec";;
