(* ======================================================== *)
(*  ffi: ported from HOL4's
    semantics/ffi/ffiScript.sml  *)
(* ======================================================== *)

(*
  Definition of the FFI type
*)

needs "basis/pure/mlstring.ml";;
needs "misc/misc.ml";;

(*
  An oracle says how to perform an FFI call based on its internal
  state, represented by the type variable 'ffi.
*)

let ffi_outcome_INDUCT,ffi_outcome_RECURSION = define_datatype
  "ffi_outcome = FFI_failed | FFI_diverged";;

let oracle_result_INDUCT,oracle_result_RECURSION = define_datatype
  "oracle_result = Oracle_return ('ffi) (word8 list) | Oracle_final \
   (ffi_outcome)";;

let shmem_op_INDUCT,shmem_op_RECURSION = define_datatype
  "shmem_op = MappedRead | MappedWrite";;

let ffiname_INDUCT,ffiname_RECURSION = define_datatype
  "ffiname = ffi_ExtCall (mlstring) | ffi_SharedMem (shmem_op)";;
hol4_overload "ExtCall" "ffi_ExtCall";;
hol4_overload "SharedMem" "ffi_SharedMem";;

(* HOL4 type abbreviation (expanded in the port):
     oracle_function = 'ffi -> word8 list -> word8 list -> 'ffi
       oracle_result *)
(* HOL4 type abbreviation (expanded in the port):
     oracle = ffiname -> 'ffi oracle_function *)

(* An I/O event, IO_event s bytes bytes2, represents the call of FFI
   function s with
 * immutable input bytes and mutable input map fst bytes2,
 * returning map snd bytes2 in the mutable array. *)

let io_event_INDUCT,io_event_RECURSION = define_datatype
  "io_event = IO_event (ffiname) (word8 list) ((word8#word8) list)";;

let final_event_INDUCT,final_event_RECURSION = define_datatype
  "final_event = Final_event (ffiname) (word8 list) (word8 list) \
   (ffi_outcome)";;

let ffi_state_FIELDS = define_record "ffi_state"
  ["oracle","ffiname->'ffi->word8 list->word8 list->'ffi oracle_result";
   "ffi_state","'ffi";
   "io_events","io_event list"];;
hol4_overload "oracle" "ffi_state_oracle";;
hol4_overload "oracle_fupd" "ffi_state_oracle_fupd";;

let initial_ffi_state_def = cake_define
  `initial_ffi_state oc' (ffi:'ffi) =
     mk_ffi_state oc' ffi []`;;

let ffi_result_INDUCT,ffi_result_RECURSION = define_datatype
  "ffi_result = FFI_return ('ffi ffi_state) (word8 list) | FFI_final \
   (final_event)";;

let call_FFI_def = cake_define
  `call_FFI (st:'ffi ffi_state) s conf bytes =
     (if ~(s = ffi_ExtCall (implode "")) then
       match ffi_state_oracle st s (ffi_state_ffi_state st) conf
         bytes with
         Oracle_return ffi' bytes' ->
           (if LENGTH bytes' = LENGTH bytes then
             FFI_return
               (ffi_state_io_events_fupd (K (ffi_state_io_events
                    st ++ [IO_event s conf (ZIP bytes bytes')]))
                      (ffi_state_ffi_state_fupd (K ffi') st))
               bytes' else FFI_final (Final_event s conf bytes
                 FFI_failed)) | Oracle_final outcome ->
         FFI_final (Final_event s conf bytes outcome) else
           FFI_return st bytes)`;;

let outcome_INDUCT,outcome_RECURSION = define_datatype
  "outcome = ffi_Success | ffi_Resource_limit_hit | ffi_FFI_outcome \
   (final_event)";;
hol4_overload "Success" "ffi_Success";;
hol4_overload "Resource_limit_hit" "ffi_Resource_limit_hit";;
hol4_overload "FFI_outcome" "ffi_FFI_outcome";;

(* A program can Diverge, Terminate, or Fail. We prove that Fail is
   avoided. For Diverge and Terminate, we keep track of what I/O
   events are valid I/O events for this behaviour. *)
let behaviour_INDUCT,behaviour_RECURSION = define_datatype
  "behaviour = ffi_Diverge (io_event llist) | ffi_Terminate (outcome) \
   (io_event list) | ffi_Fail";;
hol4_overload "Diverge" "ffi_Diverge";;
hol4_overload "Terminate" "ffi_Terminate";;
hol4_overload "Fail" "ffi_Fail";;

(* trace-based semantics can be recovered as an instance of oracle-based
 * semantics as follows. *)

let trace_oracle_def = cake_define
  `trace_oracle s io_trace conf input =
     (match LHD io_trace with NONE -> Oracle_final FFI_failed | SOME
       (IO_event s' conf' bytes2) ->
       (if s = s' /\ MAP FST bytes2 = input /\ conf = conf' then
         Oracle_return (THE (LTL io_trace)) (MAP SND bytes2) else
           Oracle_final FFI_failed))`;;
