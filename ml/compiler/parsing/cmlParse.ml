(* ======================================================== *)
(*  cmlParse: ported from HOL4's
    compiler/parsing/cmlParseScript.sml  *)
(* ======================================================== *)

(*
  Definition of the overall parsing functions that go from tokens to
    abstract
  syntax trees. In other words, these include calls to the functions in
  `../semantics/cmlPtreeConversion`.
*)

needs "compiler/backend/pattern_matching/pattern_semantics.ml";;
needs "compiler/parsing/cmlPEG.ml";;
needs "lib/location.ml";;
needs "lib/peg.ml";;
needs "lib/pegexec.ml";;
needs "semantics/cmlPtreeConversion.ml";;
needs "semantics/typeSystem.ml";;

(* HOL4 overload (expanded in the port):
     cmlpegexec = λn t. peg_exec cmlPEG (pnt n) t [] NONE [] done failed
       *)

let destResult_def = cake_define
  `cmlParse_destResult x1 =
      match x1 with
        (Result (Success [] x eo)) -> Success [] x eo
      | (Result (Success ((_1,l) :: _2) _3 _4)) ->
   Failure l "Expected to be at EOF"
      | (Result (Failure fl fe)) -> Failure fl fe
      | _5 -> Failure unknown_loc
        "Something catastrophic happened"`;;
hol4_overload "destResult" "cmlParse_destResult";;

(* HOL4 type abbreviation (expanded in the port):
     M = (token # locs) list -> ((token # locs) list, α, string)
       pegresult *)
let pegresult_bind_def = cake_define
  `pegresult_bind (f) (g) =
   (\toks.
     match f toks with
       Success toks' x eo -> g x toks' | Failure fl fe -> Failure
         fl fe)`;;

let pegresult_choice_def = cake_define
  `pegresult_choice (f) (g) =
   (\toks.
     match f toks with
       Success toks' x eo -> Success toks' x eo | _6 -> g toks)`;;

let toks_to_loc_def = cake_define
  `toks_to_loc [] = unknown_loc /\
   toks_to_loc ((h,L) :: _7) = L`;;

let pegresult_guard_def = cake_define
  `(pegresult_guard b:(tokens_token#locs) list->((tokens_token#locs)
  list,1,string)pegresult) =
   (\toks. if b then Success toks one NONE else Failure
     (toks_to_loc toks) "Assert failure")`;;

let optlift_def = cake_define
  `optlift NONE = (\toks. Failure (toks_to_loc toks) "Option = NONE") /\
   optlift (SOME a) = (\toks. Success toks a NONE)`;;

let cmlParseExpr_def = cake_define
  `cmlParseExpr = monad_bind (destResult o (\n t. peg_exec cmlPEG (pnt
  n) t [] NONE [] done failed) nE) (\
     pts. monad_bind (optlift (oHD pts)) (\
     pt. monad_bind (optlift (ptree_Expr nE pt)) (\
     ast.
     return ast)))`;;

let parse_prog_def = cake_define
  `parse_prog =
     monad_bind (destResult o (\n t. peg_exec cmlPEG (pnt n) t []
       NONE [] done failed) nTopLevelDecs) (\
       pts. monad_bind (optlift (oHD pts)) (\
       pt.
       optlift (ptree_TopLevelDecs pt)))`;;
