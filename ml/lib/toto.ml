(* ======================================================== *)
(*  toto: ported from HOL4's
    src/finite_maps/totoScript.sml  *)
(*  Of this HOL4 library theory only the definitions that the
    CakeML port needs are ported.  *)
(* ======================================================== *)

(* HOL4 ancestors outside the port: pred_set relation pair arithmetic numeral string list ternaryComparisons[qualified] set_relation[qualified] *)
let lexTO = cake_define
  `(R:'a toto_comp) lexTO (V:'b toto_comp) = TO_of_LinearOrder (
     StrongLinearOrder_of_TO R LEX StrongLinearOrder_of_TO V)`;;
let lextoto = cake_define
  `(c:'a toto) lextoto (v:'b toto) = TO (apto c lexTO apto v)`;;
