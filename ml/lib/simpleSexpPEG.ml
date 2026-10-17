(* ======================================================== *)
(*  simpleSexpPEG: ported from HOL4's
    examples/formal-languages/context-free/simpleSexpPEGScript.sml  *)
(*  Of this HOL4 library theory only the definitions that the
    CakeML port needs are ported.  *)
(* ======================================================== *)

needs "lib/peg.ml";;
needs "lib/simpleSexp.ml";;

let tokeq_def = cake_define
  `simpleSexpPEG_tokeq t = peg_tok ((=) t) (K (SX_SYM [t]))`;;
hol4_overload "tokeq" "simpleSexpPEG_tokeq";;
(* PORT FAILED: Definition grabWS_def: parse_atom: sym:'>' at 59
Definition grabWS_def:
  grabWS s = rpt (tok isSpace (K arb_sexp)) (K arb_sexp) ~> s
End
*)

let pnt_def = cake_define
  `simpleSexpPEG_pnt ntsym = peg_nt (mkNT ntsym) I`;;
hol4_overload "pnt" "simpleSexpPEG_pnt";;

let replace_nil_def = cake_define
  `replace_nil x z =
        match x with
          SX_SYM s -> (if s = "nil" then z else SX_SYM s)
        | (SX_CONS x y) -> SX_CONS x (replace_nil y z)
        | x -> x`;;

let sumID_def = cake_define_list
  [`simpleSexpPEG_sumID (INL x) = x`;
   `simpleSexpPEG_sumID (INR y) = y`];;
hol4_overload "sumID" "simpleSexpPEG_sumID";;
let choicel_def = cake_define_list
  [`simpleSexpPEG_choicel [] = peg_not (peg_empty arb_sexp) arb_sexp`;
   `simpleSexpPEG_choicel (h :: t) = peg_choice h
  (simpleSexpPEG_choicel t) simpleSexpPEG_sumID`];;
hol4_overload "choicel" "simpleSexpPEG_choicel";;

let pegf_def = cake_define
  `simpleSexpPEG_pegf sym f = peg_seq sym (peg_empty arb_sexp) (\l1
  l2. f l1)`;;
hol4_overload "pegf" "simpleSexpPEG_pegf";;

(* PORT FAILED: Definition sexpPEG_def: parse_atom: sym:'>' at 633
Definition sexpPEG_def[nocompute]:
  sexpPEG : (char, sexpNT, sexp, string) peg =
  <|
    start := pnt sxnt_sexp ;
    anyEOF := "Unexpected EOF (any)";
    tokFALSE := "Failed to see expected token";
    tokEOF := "Failed to see expected token because of EOF";
    notFAIL := "Failed to fail in a not rule";
    rules :=
    FEMPTY |++
           [(mkNT sxnt_sexp,
             pnt sxnt_WSsexp <~
             seq (rpt (tok isSpace (K arb_sexp)) (K arb_sexp))
                 (not (any (K arb_sexp)) arb_sexp)
                 (K (K arb_sexp)));
            (mkNT sxnt_sexp0,
             choicel [
                 pnt sxnt_sexpnum ;
                 tokeq #"(" ~> pnt sxnt_sexpseq ;
                 tokeq #"\"" ~>
                     pnt sxnt_strcontents
                  <~ choice (tokeq #"\"") (error "Expected \"") sumID;
                 pegf (tokeq #"'" ~> grabWS (pnt sxnt_sexp0))
                      (λs. ⟪ SX_SYM "quote"; s⟫) ;
                 pnt sxnt_sexpsym
               ]);
            (mkNT sxnt_sexpseq,
             choicel [
                 pegf (grabWS (tokeq #")")) (K (SX_SYM "nil"));
                 seq (grabWS (pnt sxnt_sexp0))
                     (seq
                      (rpt (grabWS (pnt sxnt_sexp0))
                       (FOLDR SX_CONS (SX_SYM "nil")))
                      (choicel [
                          pegf (grabWS (tokeq #")")) (K (SX_SYM "nil"));
                          grabWS (tokeq #".") ~>
                                 grabWS (pnt sxnt_sexp0)
                                 <~ grabWS (tokeq #")")
                        ])
                      replace_nil)
                     SX_CONS
               ]);
            (mkNT sxnt_WSsexp,
             rpt (tok isSpace (K arb_sexp)) (K arb_sexp) ~> pnt sxnt_sexp0);
            (mkNT sxnt_sexpnum,
             seq (pnt sxnt_digit)
                 (rpt (pnt sxnt_digit)
                  (UNCURRY SX_CONS o (SX_NUM ## SX_NUM) o
                   FOLDL (λ(l,n) d. (10*l, 10*n + destSXNUM d)) (1,0)))
                 (λs1. (λ(l,n). SX_NUM (destSXNUM s1 * l + n))
                       o (destSXNUM ## destSXNUM) o destSXCONS)) ;
            (mkNT sxnt_digit, tok isDigit (λ(c,l). SX_NUM (ORD c - ORD #"0"))) ;
            (mkNT sxnt_sexpsym,
             seq (tok valid_first_symchar (λ(c,l). SX_SYM [c]))
                 (rpt (tok valid_symchar (λ(c,l). SX_SYM [c]))
                  (SX_SYM o FOLDR (λs a. destSXSYM s ++ a) []))
                 (λs1 s2. SX_SYM (destSXSYM s1 ++ destSXSYM s2)));
            (mkNT sxnt_strcontents,
             rpt (pnt sxnt_strchar)
                 (SX_STR o FOLDR (λs a. destSXSYM s ++ a) []));
            (mkNT sxnt_strchar,
             choicel [
                 tokeq #"\\" ~> pnt sxnt_escapedstrchar ;
                 pnt sxnt_normstrchar
               ]);
            (mkNT sxnt_escapedstrchar,
             choicel [tokeq #"\\"; tokeq #"\""; error "Illegal string-escape"]);
            (mkNT sxnt_normstrchar,
             tok (λc. isPrint c ∧ c ≠ #"\"" ∧ c ≠ #"\\") (λ(c,l). SX_SYM [c]))
           ]
  |>
End
*)
