(* ======================================================== *)
(*  numposrep: ported from HOL4's
    src/list/src/numposrepScript.sml
    A HOL4 library theory, of which the port has the definitions
    that CakeML needs.  Needed by ASCIInumbers.ml, bitstring.ml,
    fromSexp.ml and misc.ml.  *)
(* ======================================================== *)

(* this file needs nothing of the port *)
(* HOL4 ancestors outside the port: list rich_list logroot arithmetic
   bit *)

let l2n_def = cake_define_list
  [`l2n b [] = 0`;
   `l2n b (h :: t) = h MOD b + b * l2n b t`];;

let n2l_def = cake_define
  `n2l b n = (if n < b \/ b < 2 then [n MOD b] else n MOD b :: n2l b
  (n DIV b))`;;
