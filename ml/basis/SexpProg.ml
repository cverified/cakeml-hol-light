(* ======================================================== *)
(*  SexpProg: ported from HOL4's
    basis/SexpProgScript.sml
    A definition theory, with 2 definitions and 9 theorems.  Needed
    by basisProg.ml.  *)
(* ======================================================== *)

(*
  Module for parsing and pretty-printing s-expressions.
*)

needs "basis/TextIOProg.ml";;
needs "basis/TextIOProof.ml";;
needs "basis/fsFFIProps.ml";;
(* forwardFD_o *)
needs "basis/mlbasicsProg.ml";;
(* Fail_exn *)
needs "basis/pure/mlsexp.ml";;
needs "basis/pure/mlstring.ml";;
needs "characteristic/cfApp.ml";;
needs "characteristic/cfFFIType.ml";;
needs "characteristic/cfHeapsBase.ml";;
needs "lib/set_sep.ml";;
needs "translator/ml_translator.ml";;
needs "translator/std_prelude.ml";;
(* OPTION_TYPE *)

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "SexpProg"
  ["TextIOProg"; "TextIOProof"; "cf"; "fsFFIProps"; "ml_prog";
   "ml_translator"; "mlbasicsProg"; "mlsexp"; "std_prelude"];;

(*--------------------------------------------------------------*
   Translation
 *--------------------------------------------------------------*)

(* HOL4 SexpProgScript.sml:24: ML code, not ported *)

(* HOL4 SexpProgScript.sml:26: ML code, not ported *)

(* Temporarily disable full type names to avoid mlsexp_sexp as the exported type name *)
(* HOL4 SexpProgScript.sml:29-30: ML code, not ported *)

(* Pretty printing function for s-expressions used by the REPL *)
(* HOL4 SexpProgScript.sml:33-41: ML code, not ported *)

(* We will define two functions to generate s-expressions:
   1. fromString, which is
       - simple,
       - fails with None (in the style of the SML basis)
       - translated from mlsexp.
   2. inputSexp, which is
       - efficient (buffered input),
       - fails with exceptions,
       - written in CakeML, proved equivalent to definitions in mlsexp using
         characteristic formulae (cf).

   OPT If needed, fromString can be made more efficient by using mlstring
     instead of a char list.
 *)

(* HOL4 SexpProgScript.sml:58: ML code, not ported *)

(* Shared, but private, helpers and types *)
(* HOL4 SexpProgScript.sml:61-62: ML code, not ported *)

(* Private helpers for fromString *)
(* HOL4 SexpProgScript.sml:65-67: ML code, not ported *)

(* HOL4 SexpProgScript.sml:69: ML code, not ported *)

(* [local] *)
let lex_aux_ind = prove
 (`lex_aux_ind`,
  CHEAT_TAC);;

(* HOL4 SexpProgScript.sml:84: ML code, not ported *)

(* HOL4 SexpProgScript.sml:86-87: ML code, not ported *)

(* Private helpers for inputSexp *)
(* HOL4 SexpProgScript.sml:90-109: ML code, not ported *)

(* HOL4 SexpProgScript.sml:111-113: ML code, not ported *)

(* HOL4 SexpProgScript.sml:115-125: ML code, not ported *)

(* HOL4 SexpProgScript.sml:127-147: ML code, not ported *)

(* HOL4 SexpProgScript.sml:149-151: ML code, not ported *)

(* HOL4 SexpProgScript.sml:153: ML code, not ported *)

(* Exported functions *)
(* HOL4 SexpProgScript.sml:156-157: ML code, not ported *)

(* If we were 100% consistent, we should call this parse_imp. Since it isn't a
   neat name, and parse is already taken by the translated pure version, we
   use inputSexp. *)
(* HOL4 SexpProgScript.sml:162-167: ML code, not ported *)


(* HOL4 SexpProgScript.sml:170: ML code, not ported *)

(* HOL4 SexpProgScript.sml:172-182: ML code, not ported *)

let str_every_side = prove
 (`!x n P. n <= strlen x ==> str_every_side P n x`,
  CHEAT_TAC);;

(* [local] *)
let make_str_safe_side = prove
 (`!x. make_str_safe_side x = T`,
  CHEAT_TAC);;

(* HOL4 SexpProgScript.sml:198: ML code, not ported *)

(* HOL4 SexpProgScript.sml:200-201: ML code, not ported *)

(* HOL4 SexpProgScript.sml:203: ML code, not ported *)

(* HOL4 SexpProgScript.sml:205-206: ML code, not ported *)

(* HOL4 SexpProgScript.sml:208-211: ML code, not ported *)

(* HOL4 SexpProgScript.sml:213-214: ML code, not ported *)

(*--------------------------------------------------------------*
   Prove equivalence to mlsexp
 *--------------------------------------------------------------*)

(* HOL4 SexpProgScript.sml:220: ML code, not ported *)

let read_string_aux_imp_post_def = new_definition
  `read_string_aux_imp_post s acc fs is fd' =
     (match read_string_aux s acc with INL (msg,rest) ->
          POSTe (?_SEP_EXISTS exn) (?_INSTREAM_STR k) fd' is rest (forwardFD
            fs fd' k) *
            &(Fail_exn msg exn)
      | INR (slit,rest) ->
          POSTv (?_SEP_EXISTS slitv) (?_STDIO k) (forwardFD fs fd' k) *
            INSTREAM_STR fd' is rest (forwardFD fs fd' k) *
            &(STRING_TYPE slit slitv))`;;

(* Can be used in read_string_aux_imp_spec to finish proofs about base cases.
 * k indicates how much we moved forward (passed to forwardFD) *)
(* HOL4 SexpProgScript.sml:238-240: a proof *)

(* Useful when finishing up recursive cases. Takes care of instantiating k in
 * forward fs fd k. *)
(* HOL4 SexpProgScript.sml:244-248: a proof *)

(* [local] *)
let read_string_aux_imp_spec = prove
 (`!s acc accv p is fs fd'.
     LIST_TYPE CHAR acc accv ==>
     app (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
       list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list)
       Sexp_read_string_aux_imp_v [is; accv]
       (STDIO fs * INSTREAM_STR fd' is s fs)
       (read_string_aux_imp_post s acc fs is fd')`,
  CHEAT_TAC);;

let read_string_imp_spec = prove
 (`app (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
  list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list)
  Sexp_read_string_imp_v [is]
     (STDIO fs * INSTREAM_STR fd is s fs)
     (match mlsexp_read_string s with INL (msg,rest) ->
          POSTe (?_SEP_EXISTS exn) (?_INSTREAM_STR k) fd is rest (forwardFD
            fs fd k) *
            &(Fail_exn msg exn)
      | INR (slit,rest) ->
          POSTv (?_SEP_EXISTS slitv) (?_STDIO k) (forwardFD fs fd k) *
            INSTREAM_STR fd is rest (forwardFD fs fd k) *
            &(STRING_TYPE slit slitv))`,
  CHEAT_TAC);;

(* [local] *)
let read_symbol_imp_spec = prove
 (`!s acc accv p is fs fd'.
     LIST_TYPE CHAR acc accv ==>
     app (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
       list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list)
       Sexp_read_symbol_imp_v [is; accv]
       (STDIO fs * INSTREAM_STR fd' is s fs)
       (match read_symbol s acc with (slit,rest) ->
            POSTv (?_SEP_EXISTS slitv) (?_STDIO k) (forwardFD fs fd' k) *
              INSTREAM_STR fd' is rest (forwardFD fs fd' k) *
              &(STRING_TYPE slit slitv))`,
  CHEAT_TAC);;

let lex_aux_imp_post_def = new_definition
  `lex_aux_imp_post depth s acc fs is fd' =
     (match mlsexp_lex_aux depth s acc with INL (msg,rest) ->
          POSTe (?_SEP_EXISTS exn) (?_INSTREAM_STR k) fd' is rest (forwardFD
            fs fd' k) *
            &(Fail_exn msg exn)
      | INR (toks,rest) ->
          POSTv (?_SEP_EXISTS tokvs) (?_STDIO k) (forwardFD fs fd' k) *
            INSTREAM_STR fd' is rest (forwardFD fs fd' k) *
            &(LIST_TYPE MLSEXP_TOKEN_TYPE toks tokvs))`;;

(* HOL4 SexpProgScript.sml:440: ML code, not ported *)

(* Analogous to read_string_aux_imp_base_tac *)
(* HOL4 SexpProgScript.sml:443-446: a proof *)

let lex_aux_imp_spec = prove
 (`!depth s acc depthv accv p is fs fd'.
     NUM depth depthv /\ LIST_TYPE MLSEXP_TOKEN_TYPE acc accv ==>
     app (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
       list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list)
       Sexp_lex_aux_imp_v [depthv; is; accv]
       (STDIO fs * INSTREAM_STR fd' is s fs)
       (lex_aux_imp_post depth s acc fs is fd')`,
  CHEAT_TAC);;

let lex_imp_spec = prove
 (`app (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
  list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list)
  Sexp_lex_imp_v [is]
     (STDIO fs * INSTREAM_STR fd is s fs)
     (match lex s with INL (msg,rest) ->
        POSTe (?_SEP_EXISTS exn) (?_INSTREAM_STR k) fd is rest (forwardFD fs
          fd k) *
          &(Fail_exn msg exn)
      | INR (toks,rest) ->
        POSTv (?_SEP_EXISTS tokvs) (?_STDIO k) (forwardFD fs fd k) *
          INSTREAM_STR fd is rest (forwardFD fs fd k) *
          &(LIST_TYPE MLSEXP_TOKEN_TYPE toks tokvs))`,
  CHEAT_TAC);;

let inputSexp_spec = prove
 (`app (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
  list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list)
  Sexp_inputSexp_v [is]
     (STDIO fs * INSTREAM_STR fd is s fs)
     (match mlsexp_parse s with INL (msg,rest) ->
        POSTe (?_SEP_EXISTS exn) (?_INSTREAM_STR k) fd is rest (forwardFD fs
          fd k) *
          &(Fail_exn msg exn)
      | INR (se,rest) ->
        POSTv (?_SEP_EXISTS sev) (?_STDIO k) (forwardFD fs fd k) *
          INSTREAM_STR fd is rest (forwardFD fs fd k) *
          &(SEXP_TYPE se sev))`,
  CHEAT_TAC);;

(* and the interface *)
let _ = unhide_overloads ();;
