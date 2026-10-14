(* ======================================================== *)
(*  location: ported from HOL4's
    examples/formal-languages/context-free/locationScript.sml  *)
(*  Of this HOL4 library theory only the definitions that the
    CakeML port needs are ported.  *)
(* ======================================================== *)

let locn_INDUCT,locn_RECURSION = define_datatype
  "locn = UNKNOWNpt | EOFpt | POSN (num) (num)";;
let locs_INDUCT,locs_RECURSION = define_datatype
  "locs = Locs (locn) (locn)";;
(* HOL4 overload (expanded in the port):
     unknown_locn = UNKNOWNpt *)
let unknown_loc_def = cake_define
  `unknown_loc = Locs (UNKNOWNpt) (UNKNOWNpt)`;;
