(* ======================================================== *)
(*  multiword: ported from HOL4's
    examples/machine-code/multiword/multiwordScript.sml
    A HOL4 library theory, of which the port has the definitions
    that CakeML needs.  Needed by 14 files of the port.  *)
(* ======================================================== *)

needs "lib/ASCIInumbers.ml";;

(* this file is of no theory of the port: the overloads it
   registers are in the scope of every file *)
let _ = hol4_lib ();;
(* HOL4 ancestors outside the port: pred_set res_quan arithmetic
   words bit pair list rich_list relation pair integer fcp *)

let b2n_def = define_general
  [`b2n T = ((1):num)`;
   `b2n F = (0:num)`];;
let b2w_def = new_definition
  `b2w c = n2w (b2n c)`;;

let mw2n_def,mw2n_ind = define_rec
  [`mw2n [] = 0`;
   `mw2n (CONS x xs) = w2n (x:'a word) + dimword (:'a) * mw2n xs`];;

(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 multiwordScript.sml:69-74: the tactic that proves the
   termination *)
let n2mw_def,n2mw_ind = define_wf
  `MEASURE I`
  [`n2mw n = (if n = 0 then []:('a word) list else CONS (n2w (n MOD
  dimword (:'a))) (n2mw (n DIV dimword (:'a))))`];;

let i2mw_def = new_definition
  `i2mw i = ((i < (&0)),n2mw (num_of_int (abs i)))`;;

let mw_ok_def = new_definition
  `mw_ok xs = (~(xs = []) ==> ~(LAST xs = (n2w 0)))`;;

let single_add_def = new_definition
  `single_add (x:'a word) (y:'a word) c =
     (x + y + b2w c,(dimword (:'a) <= w2n x + w2n y + b2n c))`;;

let single_sub_def = new_definition
  `single_sub (x:'a word) (y:'a word) c =
     single_add x (word_1comp y) c`;;

let mw_sub_def,mw_sub_ind = define_guess
  [`mw_sub [] ys c = ([],c)`;
   `mw_sub (CONS x xs) [] c =
        (let (z,c1) = single_sub x (n2w 0) c in
        let (zs,c2) = mw_sub xs [] c1 in (CONS z zs,c2))`;
   `mw_sub (CONS x xs) (CONS y ys) c =
        (let (z,c1) = single_sub x y c in
        let (zs,c2) = mw_sub xs ys c1 in (CONS z zs,c2))`];;

let single_mul_def = new_definition
  `single_mul (x:'a word) (y:'a word) (c:'a word) =
     (x * y + c,(n2w ((w2n x * w2n y + w2n c) DIV dimword
       (:'a)):'a word))`;;

let mw_shift_def,mw_shift_ind = assume_definition_rec
  "termination (CHEAT_TAC)"
  [`mw_shift [] = []`;
   `mw_shift [w] = [w >>> 1]`;
   `mw_shift (CONS (w:'a word) (CONS x xs)) = CONS (w >>> 1 || x <<
  (dimindex (:'a) - 1)) (mw_shift (CONS x xs))`];;

(* the termination relation that HOL4 gives is
     MEASURE (LENGTH o FST)
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 multiwordScript.sml:1070-1076: the tactic that proves the
   termination *)
let mw_cmp_def,mw_cmp_ind = define_guess
  [`mw_cmp xs ys = (if xs = [] then NONE else
                  if LAST xs = LAST ys then
                    mw_cmp (BUTLAST xs) (BUTLAST ys) else SOME
                      (LAST xs <+ LAST ys))`];;

let single_div_def = new_definition
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

let int_op_def = define_cases
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

let single_div_loop_def,single_div_loop_ind = define_guess
  [`single_div_loop ((k:'a word),(ns:('a word) list),(m:'a word),(is:('a
  word) list)) =
     (if k = (n2w 0) then (m,is) else
       let ns = mw_shift ns in
       let m = m << 1 in
         if mw_cmp is ns = SOME T then
           single_div_loop (k - (n2w 1),ns,m,is) else
           let m = m + (n2w 1) in
           let (is,_1) = mw_sub is ns T in
             single_div_loop (k - (n2w 1),ns,m,is))`];;

let single_div_full_def = new_definition
  `single_div_full m2 (m1:'a word) n =
     (let (m,is) = single_div_loop (n2w (dimindex (:'a)),[(n2w 0);
       n],(n2w 0),[m1; m2]) in
       (m,HD is))`;;
