(* ======================================================== *)
(*  tailrec: ported from HOL4's
    examples/machine-code/hoare-triple/tailrecScript.sml  *)
(*  Of this HOL4 library theory only the definitions that the
    CakeML port needs are ported.  *)
(* ======================================================== *)

(* this file needs nothing of the port *)
(* HOL4 ancestors outside the port: pred_set arithmetic While sum *)

let TAILREC_PRE_def = cake_define
  `TAILREC_PRE f1 guard' precondition' (x:'a) <=>
     (!k. (!m. m < k ==> guard' (FUNPOW f1 m x)) ==> precondition'
       (FUNPOW f1 k x)) /\
     (?n. ~guard' (FUNPOW f1 n x))`;;

let TAILREC_def = cake_define
  `tailrec_TAILREC f1 (f2:'a->'b) g x = f2 (WHILE g f1 x)`;;

let SHORT_TAILREC_def = cake_define
  `SHORT_TAILREC (f:'a->('a+'b)#bool) =
     tailrec_TAILREC (OUTL o FST o f) (OUTR o FST o f) (ISL o FST
       o f)`;;

let SHORT_TAILREC_PRE_def = cake_define
  `SHORT_TAILREC_PRE (f:'a->('a+'b)#bool) =
     TAILREC_PRE (OUTL o FST o f) (ISL o FST o f) (SND o f)`;;
