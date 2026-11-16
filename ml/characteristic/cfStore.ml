(* ======================================================== *)
(*  cfStore: ported from HOL4's
    characteristic/cfStoreScript.sml
    A definition theory, with 6 definitions and 15 theorems.  Needed
    by 14 files of the port.  *)
(* ======================================================== *)

(*
  Conversion from semantic stores to heaps.
*)

needs "basis/pure/mlstring.ml";;
needs "characteristic/cfFFIType.ml";;
needs "characteristic/cfHeaps.ml";;
needs "characteristic/cfHeapsBase.ml";;
needs "lib/set_sep.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "translator/ml_translator.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "cfStore"
  ["cfHeaps"; "cfHeapsBase"; "ml_translator"; "semanticPrimitives"];;

(* Definitions *)

let store2heap_aux_def,store2heap_aux_ind = define_guess
  `(store2heap_aux n [] = ({}:heap_part->bool)) /\
   (store2heap_aux n (CONS v t) = (((cfHeapsBase_Mem n v) INSERT
    (store2heap_aux (n + (1:num)) t)):heap_part->bool))`;;

(* store2heap: v store -> heap *)
let store2heap_def = new_definition
  `store2heap l = store2heap_aux (0:num) l`;;

let ffi_has_index_in_def = new_definition
  `ffi_has_index_in ns x2 =
   match x2 with
     IO_event (ffi_ExtCall i) conf ws -> (MEM i ns)
   | _ -> F`;;

let parts_ok_def = new_definition
  `parts_ok st ((proj,parts'):('ffi->(mlstring,ffi)fmap)#(mlstring
  list#(mlstring->word8 list->word8 list->ffi->(ffi cfHeapsBase_ffi_result)
  option)) list) <=>
     ALL_DISTINCT (FLAT (MAP FST parts')) /\
     ALL (ffi_has_index_in (FLAT (MAP FST parts'))) (ffi_state_io_events st)
       /\
     (!ns u.
        MEM (ns,u) parts' ==>
        (?s. !n. MEM n ns ==> FLOOKUP (proj (ffi_state_ffi_state st)) n =
          SOME s)) /\
     (!x conf bytes m ns u.
        MEM (ns,u) parts' /\ MEM m ns /\
        u m conf bytes (FAPPLY (proj x) m) = SOME FFIdiverge ==>
          ffi_state_oracle
         st (ffi_ExtCall m) x conf bytes = Oracle_final (FFI_diverged)) /\
     (!x conf bytes w new_bytes m ns u.
       MEM (ns,u) parts' /\ MEM m ns /\
       u m conf bytes (FAPPLY (proj x) m) = SOME (FFIreturn new_bytes w) ==>
       LENGTH new_bytes = LENGTH bytes /\
       (?y. ffi_state_oracle
         st (ffi_ExtCall m) x conf bytes = Oracle_return y new_bytes /\
         proj x |++ (MAP (\n. (n,w)) ns) = proj y))`;;

let ffi2heap_def = new_definition
  `ffi2heap ((proj,parts'):('ffi->(mlstring,ffi)fmap)#(mlstring
  list#(mlstring->word8 list->word8 list->ffi->(ffi cfHeapsBase_ffi_result)
  option)) list) st =
     (if parts_ok st (proj,parts') then
       cfHeapsBase_FFI_split INSERT
       {cfHeapsBase_FFI_part s u ns ts |
         MEM (ns,u) parts' /\ ~(ns = []) /\
         ts = FILTER (ffi_has_index_in ns) (ffi_state_io_events st) /\
         (!n. MEM n ns ==> FLOOKUP (proj (ffi_state_ffi_state st)) n = SOME
           s)}
     else {cfHeapsBase_FFI_full (ffi_state_io_events st)})`;;

(* st2heap: 'ffi state -> heap *)
let st2heap_def = new_definition
  `st2heap (f:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
  list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list) (st:'ffi
  semanticPrimitives_state) =
     store2heap (semanticPrimitives_state_refs st) UNION ffi2heap f
       (semanticPrimitives_state_ffi st)`;;

(* Lemmas *)

let store2heap_aux_append = prove
 (`!s n x.
      store2heap_aux n (APPEND s [x]) =
      (cfHeapsBase_Mem (LENGTH s + n) x) INSERT store2heap_aux n s`,
  CHEAT_TAC);;

let store2heap_append = prove
 (`!s x. store2heap (APPEND s [x]) = cfHeapsBase_Mem (LENGTH s) x INSERT
  store2heap s`,
  CHEAT_TAC);;

let store2heap_aux_suc = prove
 (`!s n u v.
      (cfHeapsBase_Mem u v IN store2heap_aux n s) =
      (cfHeapsBase_Mem (SUC u) v IN store2heap_aux (SUC n) s)`,
  CHEAT_TAC);;

let store2heap_aux_IN_bound = prove
 (`!s n u v. cfHeapsBase_Mem u v IN store2heap_aux n s ==> (u >= n)`,
  CHEAT_TAC);;

let store2heap_alloc_disjoint = prove
 (`!s x. ~(cfHeapsBase_Mem (LENGTH s) x IN (store2heap s))`,
  CHEAT_TAC);;

let store2heap_IN_LENGTH = prove
 (`!s r x. cfHeapsBase_Mem r x IN (store2heap s) ==> r < LENGTH s`,
  CHEAT_TAC);;

(* HOL4 cfStoreScript.sml:128-134: a proof *)

let store2heap_IN_EL = prove
 (`!s r x. cfHeapsBase_Mem r x IN (store2heap s) ==> EL r s = x`,
  CHEAT_TAC);;

let store2heap_IN_unique_key = prove
 (`!s r x.
      cfHeapsBase_Mem r x IN (store2heap s) ==>
      (!x'. cfHeapsBase_Mem r x' IN (store2heap s) ==> x = x')`,
  CHEAT_TAC);;

let Mem_NOT_IN_ffi2heap = prove
 (`~(cfHeapsBase_Mem rv x IN ffi2heap (p:('ffi->(mlstring,ffi)fmap)#(mlstring
  list#(mlstring->word8 list->word8 list->ffi->(ffi cfHeapsBase_ffi_result)
  option)) list) f)`,
  CHEAT_TAC);;

let FFI_split_NOT_IN_store2heap_aux = prove
 (`!n s. ~(cfHeapsBase_FFI_split IN store2heap_aux n s)`,
  CHEAT_TAC);;

let FFI_part_NOT_IN_store2heap_aux = prove
 (`!n s. ~(cfHeapsBase_FFI_part x1 x2 x3 x4 IN store2heap_aux n s)`,
  CHEAT_TAC);;

let FFI_full_NOT_IN_store2heap_aux = prove
 (`!n s. ~(cfHeapsBase_FFI_full x1 IN store2heap_aux n s)`,
  CHEAT_TAC);;

let FFI_part_NOT_IN_store2heap = prove
 (`!s. ~(cfHeapsBase_FFI_split IN store2heap s) /\
        ~(cfHeapsBase_FFI_part x1 x2 x3 x4 IN store2heap s) /\
        ~(cfHeapsBase_FFI_full y2 IN store2heap s)`,
  CHEAT_TAC);;

let store2heap_LUPDATE = prove
 (`!s r x y.
      cfHeapsBase_Mem r y IN (store2heap s) ==>
      store2heap (LUPDATE x r s) = cfHeapsBase_Mem r x INSERT ((store2heap
        s) DELETE cfHeapsBase_Mem r y)`,
  CHEAT_TAC);;

let st2heap_clock = prove
 (`!st ck. st2heap (p:('ffi->(mlstring,ffi)fmap)#(mlstring
  list#(mlstring->word8 list->word8 list->ffi->(ffi cfHeapsBase_ffi_result)
  option)) list) (semanticPrimitives_state_clock_fupd (K ck) st) = st2heap p
  st`,
  CHEAT_TAC);;

(* and the interface *)
let _ = unhide_overloads ();;
