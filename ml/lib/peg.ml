(* ======================================================== *)
(*  peg: ported from HOL4's
    examples/formal-languages/context-free/pegScript.sml  *)
(*  Of this HOL4 library theory only the definitions that the
    CakeML port needs are ported.  *)
(* ======================================================== *)

needs "lib/grammar.ml";;
needs "lib/location.ml";;
(* HOL4 ancestors outside the port: finite_map list rich_list *)

let pegsym_INDUCT,pegsym_RECURSION = define_datatype
  "pegsym = peg_empty ('c) | peg_any ('a#locs->'c) | peg_tok \
   ('a->bool) ('a#locs->'c) | peg_nt ('b+num) ('c->'c) | peg_seq \
   (pegsym) (pegsym) ('c->'c->'c) | peg_choice (pegsym) (pegsym) \
   ('c+'c->'c) | peg_rpt (pegsym) ('c list->'c) | peg_not (pegsym) \
   ('c) | peg_error ('e)";;

let peg_FIELDS = define_record "peg"
  ["start","('a,'b,'c,'e)pegsym";
   "anyEOF","'e";
   "tokFALSE","'e";
   "tokEOF","'e";
   "notFAIL","'e";
   "rules","('b+num,('a,'b,'c,'e)pegsym)fmap"];;

let pegresult_INDUCT,pegresult_RECURSION = define_datatype
  "pegresult = peg_Success ('a) ('c) ((locs#'e) option) | peg_Failure \
   (locs) ('e)";;

let MAXerr_def = cake_define
  `MAXerr (fl1,fe1) (fl2,fe2) =
   (if locsle fl1 fl2 then (fl2,fe2) else (fl1,fe1))`;;

let optmax_def = cake_define
  `optmax f' NONE NONE = NONE /\
   optmax f' NONE (SOME x) = SOME x /\
   optmax f' (SOME x) NONE = SOME x /\
   optmax f' (SOME x) (SOME y) = SOME (f' x y)`;;

(* HOL4 overload (expanded in the port):
     EOF = Locs EOFpt EOFpt *)
let sloc_def = cake_define
  `sloc [] = (Locs EOFpt EOFpt) /\
   sloc (h :: t) = SND h`;;
let pegf_def = cake_define
  `peg_pegf sym f' = peg_seq sym (peg_empty ARB) (\l1 l2. f' l1)`;;

let choicel_def = cake_define
  `(peg_choicel [] = peg_not (peg_empty ARB) ARB) /\
   (peg_choicel (h :: t) = peg_choice h (peg_choicel t) (\s.
     sum_CASE s I I))`;;
