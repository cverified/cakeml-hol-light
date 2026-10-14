(* ======================================================== *)
(*  set_sep: ported from HOL4's
    examples/machine-code/hoare-triple/set_sepScript.sml  *)
(*  Of this HOL4 library theory only the definitions that the
    CakeML port needs are ported.  *)
(* ======================================================== *)

(* HOL4 ancestors outside the port: pred_set pair words *)
let one_def = cake_define
  `set_sep_one x = (\s. (s = {x}))`;;
let emp_def = cake_define
  `emp = (\s. (s = {}))`;;
let cond_def = cake_define
  `cond c = (\s. (s = {}) /\ c)`;;
let fun2set_def = cake_define
  `fun2set ((f:'b->'a),d) = {(a,f a) | a IN d}`;;
