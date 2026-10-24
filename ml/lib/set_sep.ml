(* ======================================================== *)
(*  set_sep: ported from HOL4's
    examples/machine-code/hoare-triple/set_sepScript.sml
    A HOL4 library theory, of which the port has the definitions
    that CakeML needs.  Needed by 16 files of the port.  *)
(* ======================================================== *)

(* this file needs nothing of the port *)
(* HOL4 ancestors outside the port: pred_set pair words *)

let one_def = cake_define
  `set_sep_one x = (\s. (s = {x}))`;;
let emp_def = cake_define
  `emp = (\s. (s = {}))`;;
let cond_def = cake_define
  `cond c = (\s. (s = {}) /\ c)`;;
let SEP_T_def = cake_define
  `SEP_T s = T`;;
let SPLIT_def = cake_define
  `SPLIT (s:'a->bool) (u,v) <=> (u UNION v = s) /\ DISJOINT u v`;;
let STAR_def = cake_define
  `STAR p q = (\s. ?u v. SPLIT s (u,v) /\ p u /\ q v)`;;

overload_interface("*",
  `STAR:((A->bool)->bool)->((A->bool)->bool)->(A->bool)->bool`);;

let SEP_EXISTS = cake_define
  `(SEP_EXISTS) = (\f (s:'a->bool). (?) (\y. f y s))`;;

let fun2set_def = cake_define
  `fun2set ((f:'b->'a),d) = {(a,f a) | a IN d}`;;
