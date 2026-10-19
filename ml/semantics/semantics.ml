(* ======================================================== *)
(*  semantics: ported from HOL4's
    semantics/semanticsScript.sml
    A definition theory, with 6 definitions, 2 datatypes and no
    theorems.  Needed by 16 files of the port.  *)
(* ======================================================== *)

(*
  The top-level semantics of CakeML programs.
*)

needs "lib/grammar.ml";;
needs "lib/lprefix_lub.ml";;
needs "lib/sptree.ml";;
needs "semantics/cmlPtreeConversion.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/gram.ml";;
needs "semantics/lexer_fun.ml";;
needs "semantics/primTypes.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "semantics/typeSystem.ml";;

let parse_def = cake_define
  `semantics_parse toks =
     (match some (\pt. valid_lptree cmlG pt /\ ptree_head pt =
       grammar_NT ((INL:MMLnonT->MMLnonT+num) nTopLevelDecs) /\
                   real_fringe pt = MAP (grammar_TOK ## I) toks)
                     with NONE -> NONE | SOME p -> ptree_TopLevelDecs
                     p)`;;
hol4_overload "parse" "semantics_parse";;

let semantics_state_FIELDS = define_record "semantics_state"
  ["tenv","type_env";
   "type_ids","num->bool";
   (* Semantics state *)
   "sem_st","'ffi semanticPrimitives_state";
   "sem_env","semanticPrimitives_v sem_env"];;

let can_type_prog_def = cake_define
  `can_type_prog state prog <=>
     (?new_tids new_tenv.
       DISJOINT (semantics_state_type_ids state) new_tids /\
       type_ds T (semantics_state_tenv state) prog new_tids
         new_tenv)`;;

let evaluate_prog_with_clock_def = cake_define
  `evaluate_prog_with_clock st env k prog =
     (let (st',r) =
       evaluate_evaluate_decs (semanticPrimitives_state_clock_fupd
         (K k) st) env prog in (semanticPrimitives_state_ffi st',r))`;;

let semantics_prog_def = cake_define_list
  [`semantics_prog st env prog (ffi_Terminate outcome io_list) <=>
        (
         // there is a clock for which evaluation terminates, either internally or via
         // FFI, and the accumulated io events match the given io_list
         ?k ffi r.
          evaluate_prog_with_clock st env k prog = (ffi,r) /\
          (match r with Rerr (Rabort (Rffi_error outcome')) ->
             outcome = ffi_FFI_outcome (outcome') | r -> ~(r = Rerr
               (Rabort Rtimeout_error)) /\ outcome = ffi_Success) /\
          (io_list = ffi_state_io_events ffi) /\
          (~(r = Rerr (Rabort Rtype_error))))`;
   `semantics_prog st env prog (ffi_Diverge io_trace) <=>
        (
         // for all clocks, evaluation times out
         !k. ?ffi.
          (evaluate_prog_with_clock st env k prog =
              (ffi,Rerr (Rabort Rtimeout_error)))) /\
         // the io_trace is the least upper bound of the set of traces
         // produced for each clock
         lprefix_lub
           (IMAGE
             (\k. fromList (ffi_state_io_events (FST
               (evaluate_prog_with_clock st env k prog))))
             UNIV)
           io_trace`;
   `semantics_prog st env prog (ffi_Fail:behaviour) <=>
        // there is a clock for which evaluation produces a runtime type error
        (?k.
          SND (evaluate_prog_with_clock st env k prog) = Rerr
            (Rabort Rtype_error))`];;

let semantics_INDUCT,semantics_RECURSION = define_datatype
  "semantics = CannotParse | IllTyped | Execute (behaviour->bool)";;

let semantics_def = cake_define
  `semantics_semantics state prelude input =
     (match semantics_parse (lexer_fun input) with NONE ->
       CannotParse | SOME prog ->
       (if can_type_prog state (prelude ++ prog) then Execute
         (semantics_prog (semantics_state_sem_st state)
         (semantics_state_sem_env state) (prelude ++ prog)) else
         IllTyped))`;;
hol4_overload "semantics" "semantics_semantics";;

let semantics_init_def = cake_define
  `semantics_init ffi =
     semantics_semantics (mk_semantics_state prim_tenv
       prim_type_ids (FST (THE (prim_sem_env ffi))) (SND (THE
       (prim_sem_env ffi))))`;;
