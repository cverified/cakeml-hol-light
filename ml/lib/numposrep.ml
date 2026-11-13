(* ======================================================== *)
(*  numposrep: ported from HOL4's
    src/list/src/numposrepScript.sml
    A HOL4 library theory, of which the port has the definitions
    that CakeML needs.  Needed by ASCIInumbers.ml, bitstring.ml,
    fromSexp.ml and misc.ml.  *)
(* ======================================================== *)

(* this file needs nothing of the port *)

(* this file is of no theory of the port: the overloads it
   registers are in the scope of every file *)
let _ = hol4_lib ();;
(* HOL4 ancestors outside the port: list rich_list logroot arithmetic
   bit *)

let l2n_def,l2n_ind = define_rec
  [`l2n b [] = 0`;
   `l2n b (h :: t) = h MOD b + b * l2n b t`];;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let n2l_def,n2l_ind = define_wf
  `MEASURE (\(x0,x1). (\n. n) x1)`
  [`n2l b n = (if n < b \/ b < 2 then [n MOD b] else n MOD b :: n2l
  b (n DIV b))`];;

let num_from_bin_list_def = new_definition
  `num_from_bin_list = l2n 2 o REVERSE`;;
