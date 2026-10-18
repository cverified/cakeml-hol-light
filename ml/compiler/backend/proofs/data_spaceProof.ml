(* ======================================================== *)
(*  data_spaceProof: ported from HOL4's
    compiler/backend/proofs/data_spaceProofScript.sml
    A proof theory about data_space.ml, with no definitions and 9
    theorems.  Needed by bvi_to_dataProof.ml.  *)
(* ======================================================== *)

(*
  Correctness proof for data_space
*)

needs "compiler/backend/data_live.ml";;
needs "compiler/backend/data_space.ml";;
needs "compiler/backend/semantics/dataProps.ml";;
needs "compiler/backend/semantics/dataSem.ml";;
needs "lib/sptree.ml";;
needs "semantics/evaluate.ml";;
needs "semantics/semanticPrimitives.ml";;

let IMP_sptree_eq = cake_theorem "IMP_sptree_eq[local]"
  (fun () ->
    `sptree_wf x /\ sptree_wf y /\ (!a. lookup a x = lookup a y) ==>
  (x = y)`)
  CHEAT_TAC;;

let mk_wf_inter = cake_theorem "mk_wf_inter[local]"
  (fun () ->
    `!t1 t2. inter t1 t2 = mk_wf (inter t1 t2)`)
  CHEAT_TAC;;

let get_vars_IMP_LENGTH = cake_theorem "get_vars_IMP_LENGTH"
  (fun () ->
    `!xs s l. dataSem_get_vars xs s = SOME l ==> (LENGTH l = LENGTH
  xs)`)
  CHEAT_TAC;;

let do_stack_with_space = cake_theorem "do_stack_with_space"
  (fun () ->
    `!op vs s z. do_stack op vs (dataSem_state_space_fupd (K z) s) =
  dataSem_state_space_fupd (K z) (do_stack op vs s)`)
  CHEAT_TAC;;

let do_stack_with_locals = cake_theorem "do_stack_with_locals"
  (fun () ->
    `!op vs s l. do_stack op vs (dataSem_state_locals_fupd (K l) s) =
  dataSem_state_locals_fupd (K l) (do_stack op vs s)`)
  CHEAT_TAC;;

let data_spaceProof_evaluate_compile =
  cake_theorem "evaluate_compile[local]"
  (fun () ->
    `!c s res s2 vars' l. ~(
        res = SOME (Rerr (Rabort Rtype_error))) /\ (evaluate (c,s)
          = (res,s2)) /\
        locals_ok (dataSem_state_locals s) l ==>
        (?w safe peak smx.
         (evaluate (compile c,dataSem_state_locals_fupd (K l) s) =
            (res,(if res = NONE then dataSem_state_stack_max_fupd
              (K smx) (dataSem_state_peak_heap_length_fupd (K peak)
              (dataSem_state_safe_for_space_fupd (K safe)
              (dataSem_state_locals_fupd (K w) s2))) else
              dataSem_state_stack_max_fupd (K smx)
              (dataSem_state_peak_heap_length_fupd (K peak)
              (dataSem_state_safe_for_space_fupd (K safe) s2))))) /\
            locals_ok (dataSem_state_locals s2) w)`)
  CHEAT_TAC;;

(* HOL4 data_spaceProofScript.sml:81-85: a proof *)

(* HOL4 data_spaceProofScript.sml:87-94: a proof *)

(* HOL4 data_spaceProofScript.sml:96-131: a proof *)

(* HOL4 data_spaceProofScript.sml:133-139: a proof *)

(* HOL4 data_spaceProofScript.sml:141-146: a proof *)

(* HOL4 data_spaceProofScript.sml:148-161: a proof *)

(* HOL4 data_spaceProofScript.sml:163-169: a proof *)

(* HOL4 data_spaceProofScript.sml:171-465: a proof *)

(* HOL4 data_spaceProofScript.sml:467-471: a proof *)

(* HOL4 data_spaceProofScript.sml:473-498: a proof *)

(* HOL4 data_spaceProofScript.sml:500-546: a proof *)

(* HOL4 data_spaceProofScript.sml:548: a proof *)


let data_spaceProof_compile_correct = cake_theorem "compile_correct"
  (fun () ->
    `!c s. ~(
        FST (evaluate (c,s)) = NONE) /\ ~(
        FST (evaluate (c,s)) = SOME (Rerr (Rabort Rtype_error)))
          ==>
        (?safe peak smx. evaluate (compile c,s) =
                        (I ## (\s. dataSem_state_stack_max_fupd (K
                          smx) (dataSem_state_peak_heap_length_fupd (K
                          peak) (dataSem_state_safe_for_space_fupd (K
                          safe) s))))
                        (evaluate (c,s)))`)
  CHEAT_TAC;;

let get_code_labels_space = cake_theorem "get_code_labels_space"
  (fun () ->
    `!x y y0 y1 y2.
     (space x = INL y ==> dataProps_get_code_labels y =
       dataProps_get_code_labels x) /\
     (space x = INR (y0,y1,y2) ==> dataProps_get_code_labels y2 =
       dataProps_get_code_labels x)`)
  CHEAT_TAC;;

let data_spaceProof_get_code_labels_compile =
  cake_theorem "get_code_labels_compile[simp]"
  (fun () ->
    `!x. dataProps_get_code_labels (data_space_compile x) =
  dataProps_get_code_labels x`)
  CHEAT_TAC;;
