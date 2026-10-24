(* ======================================================== *)
(*  peg: ported from HOL4's
    examples/formal-languages/context-free/pegScript.sml
    A HOL4 library theory, of which the port has the definitions
    that CakeML needs.  Needed by 25 files of the port.  *)
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
hol4_field_overload "start" "peg_start";;
hol4_field_overload "start_fupd" "peg_start_fupd";;
hol4_field_overload "rules" "peg_rules";;
hol4_field_overload "rules_fupd" "peg_rules_fupd";;

let pegresult_INDUCT,pegresult_RECURSION = define_datatype
  "pegresult = peg_Success ('a) ('c) ((locs#'e) option) | peg_Failure \
   (locs) ('e)";;
hol4_overload "Success" "peg_Success";;
hol4_overload "Failure" "peg_Failure";;
let isSuccess_def = cake_define_list
  [`isSuccess (peg_Success _4 _5 _6) = T`;
   `isSuccess (peg_Failure _7 _8) = F`];;
let isFailure_def = cake_define_list
  [`isFailure (peg_Success _12 _13 _14) = F`;
   `isFailure (peg_Failure _15 _16) = T`];;

let resultmap_def = cake_define_list
  [`resultmap f (peg_Success a c eo) = peg_Success a (f c) eo`;
   `resultmap f (peg_Failure fl fe) = peg_Failure fl fe`];;

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

(* HOL4 pegScript.sml:84: the overload EOF, which the port expands *)
let sloc_def = cake_define_list
  [`sloc [] = (Locs EOFpt EOFpt)`;
   `sloc (h :: t) = SND h`];;
let peg_eval = cake_inductive
  `((!s c. peg_eval G (s,peg_empty c) (peg_Success s c NONE))) /\
   ((!n s f res.
          n IN FDOM (peg_rules G) /\ peg_eval G (s,FAPPLY (peg_rules
            G) n) res ==>
          peg_eval G (s,peg_nt n f) (resultmap f res))) /\
   ((!h t f. peg_eval G (h :: t,peg_any f) (peg_Success t (f h)
     NONE))) /\
   ((!f. peg_eval G ([],peg_any f) (peg_Failure (Locs EOFpt EOFpt)
     (peg_anyEOF G)))) /\
   ((!e t P f.
        P (FST e) ==> peg_eval G (e :: t,peg_tok P f) (peg_Success t
          (f e) NONE))) /\
   ((!h t P f.
        ~(P (FST h)) ==>
        peg_eval G (h :: t,peg_tok P f) (peg_Failure (SND h)
          (peg_tokFALSE G)))) /\
   ((!P f. peg_eval G ([],peg_tok P f) (peg_Failure (Locs EOFpt
     EOFpt) (peg_tokEOF G)))) /\
   ((!e s c fr.
        peg_eval G (s,e) fr /\ isFailure fr ==>
        peg_eval G (s,peg_not e c) (peg_Success s c NONE))) /\
   ((!e s r c.
        peg_eval G (s,e) r /\ isSuccess r ==>
        peg_eval G (s,peg_not e c) (peg_Failure (sloc s) (peg_notFAIL
          G)))) /\
   ((!e1 e2 s f fl fe.
        peg_eval G (s,e1) (peg_Failure fl fe) ==>
        peg_eval G (s,peg_seq e1 e2 f) (peg_Failure fl fe))) /\
   ((!e1 e2 f s0 eo s1 c1 fl fe.
        peg_eval G (s0,e1) (peg_Success s1 c1 eo) /\
        peg_eval G (s1,e2) (peg_Failure fl fe) ==>
        peg_eval G (s0,peg_seq e1 e2 f) (peg_Failure fl fe))) /\
   ((!e1 e2 s0 s1 s2 c1 c2 f eo1 eo2.
        peg_eval G (s0,e1) (peg_Success s1 c1 eo1) /\
        peg_eval G (s1,e2) (peg_Success s2 c2 eo2) ==>
        peg_eval G (s0,peg_seq e1 e2 f) (peg_Success s2 (f c1 c2)
          eo2))) /\
   ((!e1 e2 s f fl1 fe1 fl2 fe2.
        peg_eval G (s,e1) (peg_Failure fl1 fe1) /\
        peg_eval G (s,e2) (peg_Failure fl2 fe2) ==>
        peg_eval G (s,peg_choice e1 e2 f)
                 (UNCURRY peg_Failure (MAXerr (fl1,fe1) (fl2,fe2)))))
                   /\
   ((!e1 e2 s0 f s r eo.
        peg_eval G (s0,e1) (peg_Success s r eo) ==>
        peg_eval G (s0,peg_choice e1 e2 f) (peg_Success s (f (INL r))
          eo))) /\
   ((!e1 e2 s0 s r eo f fl fe.
        peg_eval G (s0,e1) (peg_Failure fl fe) /\
        peg_eval G (s0,e2) (peg_Success s r eo) ==>
        peg_eval G (s0,peg_choice e1 e2 f)
                 (peg_Success s (f (INR r)) (optmax MAXerr (SOME
                   (fl,fe)) eo)))) /\
   ((!e s. peg_eval G (s,peg_error e) (peg_Failure (sloc s) e))) /\
   ((!e f s s1 list' err.
        peg_eval_list G (s,e) (s1,list',err) ==>
        peg_eval G (s,peg_rpt e f) (peg_Success s1 (f list') (SOME
          err)))) /\
   ((!e s fl fe. peg_eval G (s,e) (peg_Failure fl fe) ==>
                  peg_eval_list G (s,e) (s,[],(fl,fe)))) /\
   ((!e eo0 eo s0 s1 s2 c cs.
        peg_eval G (s0,e) (peg_Success s1 c eo0) /\
        peg_eval_list G (s1,e) (s2,cs,eo) ==>
        peg_eval_list G (s0,e) (s2,c :: cs,eo)))`;;

let peg0 = cake_inductive
  `(!c. peg0 G (peg_empty c)) /\
   (
    // any
    !f. peggt0 G (peg_any f)) /\
   (!f. pegfail G (peg_any f)) /\
   (
    // tok
    !t f. peggt0 G (peg_tok t f)) /\
   (!t f. pegfail G (peg_tok t f)) /\
   (
    // rpt
    !e f. pegfail G e ==> peg0 G (peg_rpt e f)) /\
   (!e f. peggt0 G e ==> peggt0 G (peg_rpt e f)) /\
   (
    // nt rules
    !n f. n IN FDOM (peg_rules G) /\ peg0 G (FAPPLY (peg_rules G) n)
      ==>
          peg0 G (peg_nt n f)) /\
   (!n f. n IN FDOM (peg_rules G) /\ peggt0 G (FAPPLY (peg_rules G)
     n) ==>
          peggt0 G (peg_nt n f)) /\
   (!n f. n IN FDOM (peg_rules G) /\ pegfail G (FAPPLY (peg_rules G)
     n) ==>
          pegfail G (peg_nt n f)) /\
   (
    // seq rules
    !e1 e2 f. pegfail G e1 \/ (peg0 G e1 /\ pegfail G e2) \/
              (peggt0 G e1 /\ pegfail G e2) ==>
              pegfail G (peg_seq e1 e2 f)) /\
   (!e1 e2 f. peggt0 G e1 /\ (peg0 G e2 \/ peggt0 G e2) \/
              (peg0 G e1 \/ peggt0 G e1) /\ peggt0 G e2 ==>
              peggt0 G (peg_seq e1 e2 f)) /\
   (!e1 e2 f. peg0 G e1 /\ peg0 G e2 ==> peg0 G (peg_seq e1 e2 f)) /\
   (
    // choice rules
    !e1 e2 f. peg0 G e1 \/ (pegfail G e1 /\ peg0 G e2) ==>
              peg0 G (peg_choice e1 e2 f)) /\
   (!e1 e2 f. pegfail G e1 /\ pegfail G e2 ==> pegfail G (peg_choice
     e1 e2 f)) /\
   (!e1 e2 f. peggt0 G e1 \/ (pegfail G e1 /\ peggt0 G e2) ==>
              peggt0 G (peg_choice e1 e2 f)) /\
   (
    // not
    !e c. pegfail G e ==> peg0 G (peg_not e c)) /\
   (!e c. peg0 G e \/ peggt0 G e ==> pegfail G (peg_not e c)) /\
   (
    // error
    !e. pegfail G (peg_error e))`;;

let wfpeg = cake_inductive
  `((!n f. n IN FDOM (peg_rules G) /\ wfpeg G (FAPPLY (peg_rules G) n)
  ==> wfpeg G (peg_nt n f))) /\
   ((!c. wfpeg G (peg_empty c))) /\
   ((!f. wfpeg G (peg_any f))) /\
   ((!t f. wfpeg G (peg_tok t f))) /\
   ((!e. wfpeg G (peg_error e)) /\
     (!e c. wfpeg G e ==> wfpeg G (peg_not e c)) /\
     (!e1 e2 f. wfpeg G e1 /\ (peg0 G e1 ==> wfpeg G e2) ==>
                wfpeg G (peg_seq e1 e2 f)) /\
     (!e1 e2 f. wfpeg G e1 /\ wfpeg G e2 ==> wfpeg G (peg_choice e1
       e2 f)) /\
     (!e f. wfpeg G e /\ ~(peg0 G e) ==> wfpeg G (peg_rpt e f)))`;;

let subexprs_def = cake_define_list
  [`subexprs (peg_any f1) = {peg_any f1}`;
   `subexprs (peg_empty c) = {peg_empty c}`;
   `subexprs (peg_tok t f2) = {peg_tok t f2}`;
   `subexprs (peg_error e) = {(peg_error e:('a,'b,'c,'e)pegsym)}`;
   `subexprs (peg_nt s f) = {peg_nt s f}`;
   `subexprs (peg_not e c) = peg_not e c INSERT subexprs e`;
   `subexprs (peg_seq e1 e2 f3) = peg_seq e1 e2 f3 INSERT (subexprs
  e1 UNION subexprs e2)`;
   `subexprs (peg_choice e1 e2 f4) =
        peg_choice e1 e2 f4 INSERT (subexprs e1 UNION subexprs
          e2)`;
   `subexprs (peg_rpt e f5) = peg_rpt e f5 INSERT subexprs e`];;

let gexprs_def = cake_define
  `Gexprs G = BIGUNION (IMAGE subexprs (start G INSERT FRANGE
  (peg_rules G)))`;;

let wfG_def = cake_define
  `wfG G <=> (!e. e IN Gexprs G ==> wfpeg G e)`;;
let pegf_def = cake_define
  `peg_pegf sym f = peg_seq sym (peg_empty ARB) (\l1 l2. f l1)`;;
hol4_overload "pegf" "peg_pegf";;

let ignoreL_def = cake_define
  `ignoreL s1 s2 = peg_seq s1 s2 (\a b. b)`;;

let ignoreR_def = cake_define
  `ignoreR s1 s2 = peg_seq s1 s2 (\a b. a)`;;

let choicel_def = cake_define_list
  [`peg_choicel [] = peg_not (peg_empty ARB) ARB`;
   `peg_choicel (h :: t) = peg_choice h (peg_choicel t) (\s.
  sum_CASE s I I)`];;
hol4_overload "choicel" "peg_choicel";;
