(* ======================================================== *)
(*  cmlParse: ported from HOL4's
    compiler/parsing/cmlParseScript.sml
    A definition theory, with 8 definitions and no theorems.  Needed
    by compiler.ml and compilerProof.ml.  *)
(* ======================================================== *)

(*
  Definition of the overall parsing functions that go from tokens to abstract
  syntax trees. In other words, these include calls to the functions in
  `../semantics/cmlPtreeConversion`.
*)

needs "compiler/parsing/cmlPEG.ml";;
needs "lib/location.ml";;
needs "lib/peg.ml";;
needs "lib/pegexec.ml";;
needs "lib/simpleSexpParse.ml";;
needs "semantics/cmlPtreeConversion.ml";;
needs "semantics/gram.ml";;
needs "semantics/typeSystem.ml";;

(* the theories whose names the Ancestors blocks of the source
   bring, which are the ones that its statements read: the
   overloads of every other theory come out of the interface
   while this file loads *)
let _ = hol4_ancestors "cmlParse"
  ["cmlPEG"; "cmlPtreeConversion"];;

(* HOL4 cmlParseScript.sml:13: the overload cmlpegexec, which the
   port expands *)

let cmlParse_destResult_def = cake_define
  `cmlParse_destResult x1 =
      match x1 with
        pegexec_Result (peg_Success [] x eo) -> peg_Success [] x eo
      | (pegexec_Result (peg_Success ((_1,l) :: _2) _3 _4)) ->
   peg_Failure l "Expected to be at EOF"
      | (pegexec_Result (peg_Failure fl fe)) -> peg_Failure fl fe
      | _5 -> peg_Failure unknown_loc
        "Something catastrophic happened"`;;
hol4_overload "destResult" "cmlParse_destResult";;

(* HOL4 cmlParseScript.sml:23: the type abbreviation M, which the
   port expands *)
let pegresult_bind_def = cake_define
  `(pegresult_bind (f:(tokens_token#locs) list->((tokens_token#locs)
  list,'a,string)pegresult) (g:'a->(tokens_token#locs)
  list->((tokens_token#locs)
  list,'b,string)pegresult):(tokens_token#locs)
  list->((tokens_token#locs) list,'b,string)pegresult) =
   (\toks.
     match f toks with
       peg_Success toks' x eo -> g x toks' | peg_Failure fl fe ->
         peg_Failure fl fe)`;;

let pegresult_choice_def = cake_define
  `(pegresult_choice (f:(tokens_token#locs) list->((tokens_token#locs)
  list,'a,string)pegresult) (g:(tokens_token#locs)
  list->((tokens_token#locs)
  list,'a,string)pegresult):(tokens_token#locs)
  list->((tokens_token#locs) list,'a,string)pegresult) =
   (\toks.
     match f toks with
       peg_Success toks' x eo -> peg_Success toks' x eo | _6 -> g
         toks)`;;

let toks_to_loc_def = cake_define_list
  [`toks_to_loc [] = unknown_loc`;
   `toks_to_loc ((h,L) :: _7) = L`];;

let pegresult_guard_def = cake_define
  `(pegresult_guard b:(tokens_token#locs) list->((tokens_token#locs)
  list,1,string)pegresult) =
   (\toks. if b then peg_Success toks one NONE else peg_Failure
     (toks_to_loc toks) "Assert failure")`;;

hol4_overload "++" "pegresult_choice";;

let optlift_def = cake_define_list
  [`(optlift NONE:(tokens_token#locs) list->((tokens_token#locs)
  list,'a,string)pegresult) = (\toks. peg_Failure (toks_to_loc toks)
  "Option = NONE")`;
   `optlift (SOME a) = (\toks. peg_Success toks a NONE)`];;

let cmlParseExpr_def = cake_define
  `cmlParseExpr = pegresult_bind (destResult o (\n t. peg_exec cmlPEG
  (cmlPEG_pnt n) t [] NONE [] pegexec_done pegexec_failed) nE) (\
     pts. pegresult_bind (optlift (oHD pts)) (\
     pt. pegresult_bind (optlift (ptree_Expr nE pt)) (\
     ast.
     (\a inp. peg_Success inp a NONE) ast)))`;;

let parse_prog_def = cake_define
  `parse_prog =
     pegresult_bind (destResult o (\n t. peg_exec cmlPEG (cmlPEG_pnt
       n) t [] NONE [] pegexec_done pegexec_failed) nTopLevelDecs) (\
       pts. pegresult_bind (optlift (oHD pts)) (\
       pt.
       optlift (ptree_TopLevelDecs pt)))`;;

hol4_only "++" "APPEND";;

(* and the overloads that this file cannot see are back in the
   interface *)
let _ = unhide_overloads ();;
