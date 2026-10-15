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
hol4_overload "empty" "peg_empty";;
hol4_overload "any" "peg_any";;
hol4_overload "tok" "peg_tok";;
hol4_overload "nt" "peg_nt";;
hol4_overload "seq" "peg_seq";;
hol4_overload "choice" "peg_choice";;
hol4_overload "rpt" "peg_rpt";;
hol4_overload "not" "peg_not";;
hol4_overload "error" "peg_error";;

let peg_FIELDS = define_record "peg"
  ["start","('a,'b,'c,'e)pegsym";
   "anyEOF","'e";
   "tokFALSE","'e";
   "tokEOF","'e";
   "notFAIL","'e";
   "rules","('b+num,('a,'b,'c,'e)pegsym)fmap"];;
hol4_overload "start" "peg_start";;
hol4_overload "start_fupd" "peg_start_fupd";;
hol4_overload "rules" "peg_rules";;
hol4_overload "rules_fupd" "peg_rules_fupd";;

let pegresult_INDUCT,pegresult_RECURSION = define_datatype
  "pegresult = peg_Success ('a) ('c) ((locs#'e) option) | peg_Failure \
   (locs) ('e)";;
hol4_overload "Success" "peg_Success";;
hol4_overload "Failure" "peg_Failure";;

let MAXerr_def = cake_define
  `MAXerr (fl1,fe1) (fl2,fe2) =
   (if locsle fl1 fl2 then (fl2,fe2) else (fl1,fe1))`;;

let optmax_def = cake_define
  `optmax f x2 x3 =
      match (x2,x3) with
        (NONE,NONE) -> NONE
      | (NONE,(SOME x)) -> SOME x
      | ((SOME x),NONE) -> SOME x
      | ((SOME x),(SOME y)) -> SOME (f x y)`;;

(* HOL4 overload (expanded in the port):
     EOF = Locs EOFpt EOFpt *)
let sloc_def = cake_define_list
  [`sloc [] = (Locs EOFpt EOFpt)`;
   `sloc (h :: t) = SND h`];;
let pegf_def = cake_define
  `peg_pegf sym f = peg_seq sym (peg_empty ARB) (\l1 l2. f l1)`;;
hol4_overload "pegf" "peg_pegf";;

let choicel_def = cake_define_list
  [`peg_choicel [] = peg_not (peg_empty ARB) ARB`;
   `peg_choicel (h :: t) = peg_choice h (peg_choicel t) (\s.
  sum_CASE s I I)`];;
hol4_overload "choicel" "peg_choicel";;
