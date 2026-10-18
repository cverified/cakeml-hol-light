(* ======================================================== *)
(*  term: ported from HOL4's
    examples/algorithms/unification/triangular/first-order/
      termScript.sml
    A HOL4 library theory, of which the port has the definitions
    that CakeML needs.  Needed by 8 files of the port.  *)
(* ======================================================== *)

(* this file needs nothing of the port *)
(* HOL4 ancestors outside the port: string bag commonUnif *)

let term_INDUCT,term_RECURSION = define_datatype
  "term = term_Var (num) | term_Pair (term) (term) | term_Const ('a)";;
hol4_overload "Var" "term_Var";;
hol4_overload "Pair" "term_Pair";;
hol4_overload "Const" "term_Const";;

let pair_count_def = cake_define_list
  [`pair_count (term_Var v) = 0`;
   `pair_count (term_Const c) = 0`;
   `pair_count (term_Pair t1 t2) = 1 + pair_count t1 + pair_count
  t2`];;

let vars_def = cake_define_list
  [`vars (term_Var x) = {x}`;
   `vars (term_Pair t1 t2) = vars t1 UNION vars t2`;
   `vars (term_Const _2) = {}`];;

let varb_def = cake_define_list
  [`varb (term_Var s) = BAG_INSERT s (EMPTY_BAG)`;
   `varb (term_Pair t1 t2) = (BAG_UNION) (varb t1) (varb t2)`;
   `varb (term_Const c) = EMPTY_BAG`];;
