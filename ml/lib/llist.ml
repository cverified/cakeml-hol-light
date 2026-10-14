(* ======================================================== *)
(*  llist: ported from HOL4's
    src/coalgebras/llistScript.sml  *)
(*  Of this HOL4 library theory only the definitions that the
    CakeML port needs are ported.  *)
(* ======================================================== *)

(* HOL4 ancestors outside the port: option combin option pair num arithmetic prim_rec list rich_list While pair pred_set set_relation arithmetic *)
let LNIL = cake_define
  `LNIL = llist_abs (\n. NONE)`;;
let LCONS = cake_define
  `LCONS h t = llist_abs (\n. if n = 0 then SOME h else llist_rep t (n -
  1))`;;
let LHD = cake_define
  `LHD ll = llist_rep ll 0`;;
let LTL = cake_define
  `LTL ll = (match LHD ll with
                NONE -> NONE | SOME _1 -> SOME (llist_abs (\n.
                  llist_rep ll (n + 1))))`;;
let LTAKE = cake_define
  `(LTAKE 0 ll = SOME []) /\
   (LTAKE (SUC n) ll =
      (match LHD ll with
          NONE -> NONE | SOME hd ->
          match LTAKE n (THE (LTL ll)) with
              NONE -> NONE | SOME tl -> SOME (hd :: tl)))`;;
let LLENGTH = cake_define
  `LLENGTH ll = (if LFINITE ll then SOME (@n. llength_rel ll n) else
  NONE)`;;
let toList = cake_define
  `llist_toList ll = (if LFINITE ll then LTAKE (THE (LLENGTH ll)) ll
  else NONE)`;;
let fromList_def = cake_define
  `(llist_fromList [] = LNIL) /\ (llist_fromList (h :: t) = LCONS h
  (llist_fromList t))`;;
