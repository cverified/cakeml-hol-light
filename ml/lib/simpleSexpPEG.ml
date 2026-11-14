(* ======================================================== *)
(*  simpleSexpPEG: ported from HOL4's
    examples/formal-languages/context-free/simpleSexpPEGScript.sml
    A HOL4 library theory, of which the port has the definitions
    that CakeML needs.  Needed by simpleSexpParse.ml.  *)
(* ======================================================== *)

needs "lib/peg.ml";;
needs "lib/simpleSexp.ml";;

(* this file is of no theory of the port: the overloads it
   registers are in the scope of every file *)
let _ = hol4_lib ();;

let tokeq_def = new_definition
  `simpleSexpPEG_tokeq t = peg_tok ((=) t) (K (SX_SYM [t]))`;;
let grabWS_def = new_definition
  `grabWS s = ignoreL (peg_rpt (peg_tok isSpace (K arb_sexp)) (K
  arb_sexp)) s`;;

let pnt_def = new_definition
  `simpleSexpPEG_pnt ntsym = peg_nt (INL ntsym) I`;;

let replace_nil_def,replace_nil_ind = define_shaped_rec
  "match"
  [`replace_nil x z =
        match x with
          SX_SYM s -> (if s = "nil" then z else SX_SYM s)
        | (SX_CONS x y) -> SX_CONS x (replace_nil y z)
        | x -> x`];;

let sumID_def = define_cases
  [`simpleSexpPEG_sumID (INL x) = x`;
   `simpleSexpPEG_sumID (INR y) = y`];;
let simpleSexpPEG_choicel_def,simpleSexpPEG_choicel_ind = define_rec
  [`simpleSexpPEG_choicel [] = peg_not (peg_empty arb_sexp) arb_sexp`;
   `simpleSexpPEG_choicel (CONS h t) = peg_choice h
  (simpleSexpPEG_choicel t) simpleSexpPEG_sumID`];;

let simpleSexpPEG_pegf_def = new_definition
  `simpleSexpPEG_pegf sym f = peg_seq sym (peg_empty arb_sexp) (\l1
  l2. f l1)`;;

let sexpPEG_def = new_definition
  `(sexpPEG:(char,sexpNT,simpleSexp_sexp,string)peg) =
   mk_peg (simpleSexpPEG_pnt sxnt_sexp) "Unexpected EOF (any)"
     "Failed to see expected token"
     "Failed to see expected token because of EOF"
     "Failed to fail in a not rule" (
     FEMPTY |++
            [(INL sxnt_sexp,ignoreR (simpleSexpPEG_pnt sxnt_WSsexp)
              (peg_seq (peg_rpt (peg_tok isSpace (K arb_sexp)) (K
                arb_sexp))
                  (peg_not (peg_any (K arb_sexp)) arb_sexp)
                  (K (K arb_sexp))));
             (INL sxnt_sexp0,
              simpleSexpPEG_choicel [
                  simpleSexpPEG_pnt sxnt_sexpnum; ignoreL
                    (simpleSexpPEG_tokeq (CHR 40)) (simpleSexpPEG_pnt
                    sxnt_sexpseq);
                   ignoreR (ignoreL (simpleSexpPEG_tokeq (CHR 34))
                      (simpleSexpPEG_pnt sxnt_strcontents))
                        (peg_choice (simpleSexpPEG_tokeq (CHR 34))
                        (peg_error "Expected \"") simpleSexpPEG_sumID);
                  simpleSexpPEG_pegf (ignoreL (simpleSexpPEG_tokeq
                    (CHR 39)) (grabWS (simpleSexpPEG_pnt sxnt_sexp0)))
                       (\s. (SX_CONS (SX_SYM "quote") (SX_CONS (s)
                         (SX_SYM "nil"))));
                  simpleSexpPEG_pnt sxnt_sexpsym]);
             (INL sxnt_sexpseq,
              simpleSexpPEG_choicel [
                  simpleSexpPEG_pegf (grabWS (simpleSexpPEG_tokeq
                    (CHR 41))) (K (SX_SYM "nil"));
                  peg_seq (grabWS (simpleSexpPEG_pnt sxnt_sexp0))
                      (peg_seq
                       (peg_rpt (grabWS (simpleSexpPEG_pnt
                         sxnt_sexp0))
                        (FOLDR SX_CONS (SX_SYM "nil")))
                       (simpleSexpPEG_choicel [
                           simpleSexpPEG_pegf (grabWS
                             (simpleSexpPEG_tokeq (CHR 41))) (K (SX_SYM
                             "nil"));
                              ignoreR (ignoreL (grabWS
                                (simpleSexpPEG_tokeq (CHR 46)))
                              (grabWS (simpleSexpPEG_pnt
                                sxnt_sexp0))) (grabWS
                                (simpleSexpPEG_tokeq (CHR 41)))])
                       replace_nil)
                      SX_CONS]);
             (INL sxnt_WSsexp,ignoreL (peg_rpt (peg_tok isSpace (K
               arb_sexp)) (K arb_sexp)) (simpleSexpPEG_pnt sxnt_sexp0));
             (INL sxnt_sexpnum,
              peg_seq (simpleSexpPEG_pnt sxnt_digit)
                  (peg_rpt (simpleSexpPEG_pnt sxnt_digit)
                   (UNCURRY SX_CONS o (SX_NUM ## SX_NUM) o
                    FOLDL (\(l,n) d. (10 * l,10 * n + destSXNUM d))
                      (1,0)))
                  (\s1.
                        (\(l,n). SX_NUM (destSXNUM s1 * l + n)) o
                          (destSXNUM ## destSXNUM) o destSXCONS));
             (INL sxnt_digit,peg_tok isDigit (\(c,l). SX_NUM (ORD c -
               ORD (CHR 48))));
             (INL sxnt_sexpsym,
              peg_seq (peg_tok valid_first_symchar (\(c,l). SX_SYM
                [c]))
                  (peg_rpt (peg_tok valid_symchar (\(c,l). SX_SYM
                    [c]))
                   (SX_SYM o FOLDR (\s a. APPEND (destSXSYM s) a)
                     []))
                  (\s1 s2. SX_SYM (APPEND (destSXSYM s1) (destSXSYM
                    s2))));
             (INL sxnt_strcontents,
              peg_rpt (simpleSexpPEG_pnt sxnt_strchar)
                  (SX_STR o FOLDR (\s a. APPEND (destSXSYM s) a)
                    []));
             (INL sxnt_strchar,
              simpleSexpPEG_choicel [ignoreL (simpleSexpPEG_tokeq
                (CHR 92)) (simpleSexpPEG_pnt sxnt_escapedstrchar);
                  simpleSexpPEG_pnt sxnt_normstrchar]);
             (INL sxnt_escapedstrchar,
              simpleSexpPEG_choicel [simpleSexpPEG_tokeq (CHR 92);
                simpleSexpPEG_tokeq (CHR 34); peg_error
                "Illegal string-escape"]);
             (INL sxnt_normstrchar,
              peg_tok (\c. isPrint c /\ ~(c = (CHR 34)) /\ ~(c =
                (CHR 92))) (\(c,l). SX_SYM [c]))])`;;
