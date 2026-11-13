(* ======================================================== *)
(*  integer_word: ported from HOL4's
    src/integer/integer_wordScript.sml  *)
(* ======================================================== *)

needs "lib/ASCIInumbers.ml";;

(* this file is of no theory of the port: the overloads it
   registers are in the scope of every file *)
let _ = hol4_lib ();;
(* HOL4 ancestors outside the port: arithmetic bit words integer *)
