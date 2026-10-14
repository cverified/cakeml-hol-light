(* ======================================================== *)
(*  multiword: ported from HOL4's
    examples/machine-code/multiword/multiwordScript.sml  *)
(*  Of this HOL4 library theory only the definitions that the
    CakeML port needs are ported.  *)
(* ======================================================== *)

needs "lib/ASCIInumbers.ml";;
(* HOL4 ancestors outside the port: pred_set res_quan arithmetic
   words bit pair list rich_list relation pair integer fcp *)
(* HOL4 termination: \\ SIMP_TAC std_ss [MATCH_MP DIV_LT_X
   ZERO_LT_dimword,ONE_LT_dimword] \\ DECIDE_TAC *)
let n2mw_def = cake_define_wf
  `MEASURE I`
  `n2mw n = (if n = 0 then []:('a word) list else
              n2w (n MOD dimword (:'a)) :: n2mw (n DIV dimword
                (:'a)))`;;
let i2mw_def = cake_define
  `i2mw i = ((i < (&0)),n2mw (num_of_int (abs i)))`;;
let mw_op_INDUCT,mw_op_RECURSION = define_datatype
  "mw_op = multiword_Add | multiword_Sub | multiword_Mul | \
   multiword_Div | multiword_Mod | multiword_Lt | multiword_Eq | \
   multiword_Dec";;
let int_op_def = cake_define
  `(multiword_int_op multiword_Add i j = i + j) /\
   (multiword_int_op multiword_Sub i j = i - j) /\
   (multiword_int_op multiword_Mul i j = i * j) /\
   (multiword_int_op multiword_Div i j = i / j) /\
   (multiword_int_op multiword_Mod i j = i % j) /\
   (multiword_int_op multiword_Lt i j = (if i < j then (&1) else
     (&0))) /\
   (multiword_int_op multiword_Eq i j = (if i = j then (&1) else
     (&0):int)) /\
   (multiword_int_op multiword_Dec i j = (&0))`;;
