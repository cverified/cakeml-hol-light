(* ======================================================== *)
(*  multiword: ported from HOL4's
    examples/machine-code/multiword/multiwordScript.sml
    A HOL4 library theory, of which the port has the definitions
    that CakeML needs.  Needed by 13 files of the port.  *)
(* ======================================================== *)

needs "lib/ASCIInumbers.ml";;
(* HOL4 ancestors outside the port: pred_set res_quan arithmetic
   words bit pair list rich_list relation pair integer fcp *)

let b2n_def = cake_define_list
  [`b2n T = ((1):num)`;
   `b2n F = (0:num)`];;
let b2w_def = cake_define
  `b2w c = n2w (b2n c)`;;

(* HOL4 multiwordScript.sml:69-74: the tactic that proves the
   termination *)
let n2mw_def = cake_define_wf
  `MEASURE I`
  `n2mw n = (if n = 0 then []:('a word) list else
              n2w (n MOD dimword (:'a)) :: n2mw (n DIV dimword
                (:'a)))`;;

let i2mw_def = cake_define
  `i2mw i = ((i < (&0)),n2mw (num_of_int (abs i)))`;;

let single_add_def = cake_define
  `single_add (x:'a word) (y:'a word) c =
     (x + y + b2w c,(dimword (:'a) <= w2n x + w2n y + b2n c))`;;

let single_sub_def = cake_define
  `single_sub (x:'a word) (y:'a word) c =
     single_add x (word_1comp y) c`;;

let single_mul_def = cake_define
  `single_mul (x:'a word) (y:'a word) (c:'a word) =
     (x * y + c,(n2w ((w2n x * w2n y + w2n c) DIV dimword
       (:'a)):'a word))`;;

let single_div_def = cake_define
  `(single_div (x1:'a word) (x2:'a word) (y:'a word) =
   ((n2w ((w2n x1 * dimword (:'a) + w2n x2) DIV w2n y):'a word),
    (n2w ((w2n x1 * dimword (:'a) + w2n x2) MOD w2n y):'a word)))`;;

let mw_op_INDUCT,mw_op_RECURSION = define_datatype
  "mw_op = multiword_Add | multiword_Sub | multiword_Mul | \
   multiword_Div | multiword_Mod | multiword_Lt | multiword_Eq | \
   multiword_Dec";;
hol4_overload "Add" "multiword_Add";;
hol4_overload "Sub" "multiword_Sub";;
hol4_overload "Mul" "multiword_Mul";;
hol4_overload "Div" "multiword_Div";;
hol4_overload "Mod" "multiword_Mod";;
hol4_overload "Lt" "multiword_Lt";;
hol4_overload "Eq" "multiword_Eq";;
hol4_overload "Dec" "multiword_Dec";;

let int_op_def = cake_define_list
  [`multiword_int_op (multiword_Add:mw_op) (i:int) (j:int) = ((i +
  j):int)`;
   `multiword_int_op (multiword_Sub:mw_op) (i:int) (j:int) = ((i -
  j):int)`;
   `multiword_int_op (multiword_Mul:mw_op) (i:int) (j:int) = ((i *
  j):int)`;
   `multiword_int_op (multiword_Div:mw_op) (i:int) (j:int) = ((i /
  j):int)`;
   `multiword_int_op (multiword_Mod:mw_op) (i:int) (j:int) = ((i %
  j):int)`;
   `multiword_int_op (multiword_Lt:mw_op) (i:int) (j:int) = ((if i <
  j then (&1) else (&0)):int)`;
   `multiword_int_op multiword_Eq (i:int) (j:int) = ((if i = j then
  (&1) else (&0):int):int)`;
   `multiword_int_op (multiword_Dec:mw_op) (i:int) (j:int) =
  ((&0):int)`];;
hol4_overload "int_op" "multiword_int_op";;
