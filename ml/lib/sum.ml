(* ======================================================== *)
(*  sum: ported from HOL4's
    src/coretypes/sumScript.sml
    A HOL4 library theory, of which the port has the definitions
    that CakeML needs.  Needed by 9 files of the port.  *)
(* ======================================================== *)

(* this file needs nothing of the port *)

(* of no theory of the port: what it registers is in the scope of every file *)
let _ = cake_library ();;
(* HOL4 ancestors outside the port: sat *)
let INL_def = new_definition
  `!e. (sum_INL:'a->'a+'b) e = ABS_sum (\b x (y:'b). (x = e) /\ b)`;;
let INR_def = new_definition
  `!e. (sum_INR:'b->'a+'b) e = ABS_sum (\b (x:'a) y. (y = e) /\ ~b)`;;
(* HOL4 sumScript.sml:236: the overload case, which the port expands *)
