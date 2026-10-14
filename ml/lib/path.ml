(* ======================================================== *)
(*  path: ported from HOL4's
    src/coalgebras/pathScript.sml  *)
(*  Of this HOL4 library theory only the definitions that the
    CakeML port needs are ported.  *)
(* ======================================================== *)

needs "lib/llist.ml";;
(* HOL4 ancestors outside the port: fixedPoint[qualified] rich_list[qualified] *)
let first_def = cake_define
  `first (p:('a, 'b) path) = FST (fromPath p)`;;
let finite_def = cake_define
  `finite (sigma:('a, 'b) path) = LFINITE (SND (fromPath sigma))`;;
let length_def = cake_define
  `length p = (if finite p then
                       SOME (LENGTH (THE (toList (SND (fromPath p))))
                         + 1) else NONE)`;;
let el_def = cake_define
  `(el 0 p = first p) /\ (el (SUC n) p = el n (tail p))`;;
let PL_def = cake_define
  `PL p = {i | finite p ==> i < THE (length p)}`;;
let firstP_at_def = cake_define
  `firstP_at P p i <=> i IN PL p /\ P (el i p) /\ (!j. j < i ==> ~P (el
  j p))`;;
let exists_def = cake_define
  `path_exists P p = (?i. firstP_at P p i)`;;
