(* ======================================================== *)
(*  cardinal: ported from HOL4's
    src/pred_set/src/cardinalScript.sml
    A HOL4 library theory, of which the port has the definitions
    that CakeML needs.  Needed by setSpec.ml.  *)
(* ======================================================== *)

needs "lib/sum.ml";;

(* of no theory of the port: what it registers is in the scope of every file *)
let _ = cake_library ();;
(* HOL4 ancestors outside the port: cardinalityCore pred_set pair option
   wellorder set_relation *)
