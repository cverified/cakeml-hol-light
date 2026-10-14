(* ======================================================== *)
(*  numposrep[bare]: ported from HOL4's
    src/list/src/numposrepScript.sml  *)
(*  Of this HOL4 library theory only the definitions that the
    CakeML port needs are ported.  *)
(* ======================================================== *)

(* HOL4 ancestors outside the port: list rich_list logroot arithmetic
   bit *)
let l2n_def = cake_define
  `(l2n b [] = 0) /\
   (l2n b (h :: t) = h MOD b + b * l2n b t)`;;
let n2l_def = cake_define
  `n2l b n = (if n < b \/ b < 2 then [n MOD b] else n MOD b :: n2l b
  (n DIV b))`;;
