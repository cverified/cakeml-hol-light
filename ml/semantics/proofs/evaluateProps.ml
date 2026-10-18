(* ======================================================== *)
(*  evaluateProps: ported from HOL4's
    semantics/proofs/evaluatePropsScript.sml  *)
(* ======================================================== *)

(*
  Properties of the operational semantics.
*)

needs "semantics/ast.ml";;
needs "semantics/evaluate.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/namespace.ml";;
needs "semantics/proofs/namespaceProps.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;
needs "semantics/semanticPrimitives.ml";;

let call_FFI_rel_def = cake_define
  `call_FFI_rel s1 s2 <=> (?n conf bytes t. call_FFI s1 n conf bytes
  = FFI_return s2 t)`;;

let dest_IO_event_def = cake_define
  `dest_IO_event (IO_event s c b) = (s,c,b)`;;

let io_events_mono_def = cake_define
  `io_events_mono s1 s2 <=> ffi_state_io_events
     s1 <<= ffi_state_io_events s2 /\
     (ffi_state_io_events s2 = ffi_state_io_events s1 ==> s2 = s1)`;;

let is_clock_io_mono_def = cake_define
  `is_clock_io_mono f s = (match f s with (s',r) ->
         io_events_mono (semanticPrimitives_state_ffi s)
           (semanticPrimitives_state_ffi s') /\
         semanticPrimitives_state_clock s' <=
           semanticPrimitives_state_clock s /\
         semanticPrimitives_state_next_type_stamp s <=
           semanticPrimitives_state_next_type_stamp s' /\
         semanticPrimitives_state_next_exn_stamp s <=
           semanticPrimitives_state_next_exn_stamp s' /\
         LENGTH (semanticPrimitives_state_refs s) <= LENGTH
           (semanticPrimitives_state_refs s') /\ (!clk. match f
           (semanticPrimitives_state_clock_fupd (K clk) s) with (s'',r')
           ->
             (
                 ~(r' = Rerr (Rabort Rtimeout_error)) ==>
                 ~(r = Rerr (Rabort Rtimeout_error)) ==>
                     r' = r /\ s'' =
                       (semanticPrimitives_state_clock_fupd (K (clk -
                       (semanticPrimitives_state_clock s -
                       semanticPrimitives_state_clock s'))) s')) /\
             (
                 ~(r = Rerr (Rabort Rtimeout_error)) ==> (
                     clk >= semanticPrimitives_state_clock s -
                       semanticPrimitives_state_clock s' <=> ~(r' = Rerr
                       (Rabort Rtimeout_error)))) /\
             (
                 ~(r' = Rerr (Rabort Rtimeout_error)) ==>
                 clk <= semanticPrimitives_state_clock s ==> ~(r =
                   Rerr (Rabort Rtimeout_error))) /\ (clk <=
                   semanticPrimitives_state_clock s ==>
                   io_events_mono (semanticPrimitives_state_ffi s'')
                   (semanticPrimitives_state_ffi s'))))`;;

let adj_clock_def = cake_define
  `adj_clock inc dec s = (semanticPrimitives_state_clock_fupd (K
  ((semanticPrimitives_state_clock s + inc) - dec)) s)`;;

(* HOL4 evaluatePropsScript.sml:321-326: ML code, not ported *)

(* HOL4 evaluatePropsScript.sml:407-411: ML code, not ported *)

(* HOL4 evaluatePropsScript.sml:586-588: ML code, not ported *)

(* HOL4 evaluatePropsScript.sml:693-712: code that the source has in
   a comment *)

(* HOL4 evaluatePropsScript.sml:899-902: ML code, not ported *)

(* HOL4 evaluatePropsScript.sml:937-938: ML code, not ported *)
