(* ======================================================== *)
(*  ffi: ported from HOL4's
    semantics/ffi/ffiScript.sml
    A definition theory, with 3 definitions, 10 datatypes and no
    theorems.  Needed by 48 files of the port.  *)
(* ======================================================== *)

(*
  Definition of the FFI type
*)

needs "basis/pure/mlstring.ml";;
needs "misc/misc.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "ffi"
  ["misc"; "mlstring"];;

(*
  An oracle says how to perform an FFI call based on its internal
  state, represented by the type variable 'ffi.
*)

let ffi_outcome_INDUCT,ffi_outcome_RECURSION = define_datatype
  "ffi_outcome =
     FFI_failed
   | FFI_diverged";;

let oracle_result_INDUCT,oracle_result_RECURSION = define_datatype
  "oracle_result =
     Oracle_return ('ffi) (word8 list)
   | Oracle_final ffi_outcome";;

let shmem_op_INDUCT,shmem_op_RECURSION = define_datatype
  "shmem_op =
     MappedRead
   | MappedWrite";;

let ffiname_INDUCT,ffiname_RECURSION = define_datatype
  "ffiname =
     ffi_ExtCall mlstring
   | ffi_SharedMem shmem_op";;

(* HOL4 ffiScript.sml:31: the type abbreviation oracle_function,
   which the port expands *)
(* HOL4 ffiScript.sml:32: the type abbreviation oracle, which the
   port expands *)

(* An I/O event, IO_event s bytes bytes2, represents the call of FFI function s with
 * immutable input bytes and mutable input map fst bytes2,
 * returning map snd bytes2 in the mutable array. *)

let io_event_INDUCT,io_event_RECURSION = define_datatype
  "io_event =
     IO_event ffiname (word8 list) ((word8#word8) list)";;

let final_event_INDUCT,final_event_RECURSION = define_datatype
  "final_event =
     Final_event ffiname (word8 list) (word8 list) ffi_outcome";;

let ffi_state_FIELDS = define_record "ffi_state"
  ["oracle","ffiname->'ffi->word8 list->word8 list->'ffi oracle_result";
   "ffi_state","'ffi";
   "io_events","io_event list"];;

let initial_ffi_state_def = new_definition
  `initial_ffi_state oc' (ffi:'ffi) =
     mk_ffi_state oc' ffi []`;;

let ffi_result_INDUCT,ffi_result_RECURSION = define_datatype
  "ffi_result =
     FFI_return ('ffi ffi_state) (word8 list)
   | FFI_final final_event";;

let call_FFI_def = new_definition
  `call_FFI (st:'ffi ffi_state) s conf bytes =
     (if ~(s = ffi_ExtCall (implode "")) then
       match ffi_state_oracle st s (ffi_state_ffi_state st) conf
         bytes with
         Oracle_return ffi' bytes' ->
           (if LENGTH bytes' = LENGTH bytes then
             FFI_return
               (ffi_state_io_events_fupd (K (APPEND
                 (ffi_state_io_events
                    st) [IO_event s conf (ZIP bytes bytes')]))
                      (ffi_state_ffi_state_fupd (K ffi') st))
               bytes' else FFI_final (Final_event s conf bytes
                 FFI_failed)) | Oracle_final outcome ->
         FFI_final (Final_event s conf bytes outcome) else
           FFI_return st bytes)`;;

let outcome_INDUCT,outcome_RECURSION = define_datatype
  "outcome =
     ffi_Success
   | ffi_Resource_limit_hit
   | ffi_FFI_outcome final_event";;

(* A program can Diverge, Terminate, or Fail. We prove that Fail is
   avoided. For Diverge and Terminate, we keep track of what I/O
   events are valid I/O events for this behaviour. *)
let behaviour_INDUCT,behaviour_RECURSION = define_datatype
  "behaviour =
     // There cannot be any non-returning FFI calls in a diverging
     // exeuction. The list of I/O events can be finite or infinite,
     // hence the llist (lazy list) type.
     ffi_Diverge (io_event llist)
     // Terminating executions can only perform a finite number of
     // FFI calls. The execution can be terminated by a non-returning
     // FFI call.
   | ffi_Terminate outcome (io_event list)
     // Failure is a behaviour which we prove cannot occur for any
     // well-typed program.
   | ffi_Fail";;

(* trace-based semantics can be recovered as an instance of oracle-based
 * semantics as follows. *)

let trace_oracle_def = new_definition
  `trace_oracle s io_trace conf input =
     (match LHD io_trace with NONE -> Oracle_final FFI_failed | SOME
       (IO_event s' conf' bytes2) ->
       (if s = s' /\ MAP FST bytes2 = input /\ conf = conf' then
         Oracle_return (THE (LTL io_trace)) (MAP SND bytes2) else
           Oracle_final FFI_failed))`;;
