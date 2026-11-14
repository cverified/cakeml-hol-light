(* ======================================================== *)
(*  data_spaceProof: ported from HOL4's
    compiler/backend/proofs/data_spaceProofScript.sml
    A proof theory about data_space.ml, with no definitions and 9
    theorems.  Needed by bvi_to_dataProof.ml.  *)
(* ======================================================== *)

(*
  Correctness proof for data_space
*)

needs "compiler/backend/data_space.ml";;
needs "compiler/backend/semantics/dataProps.ml";;
needs "compiler/backend/semantics/dataSem.ml";;
needs "lib/sptree.ml";;
needs "semantics/semanticPrimitives.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "data_spaceProof"
  ["dataProps"; "dataSem"; "data_space"];;

let _ = do_list hide_constant ["vars"];;

(* HOL4 data_spaceProofScript.sml:12-17: an overload that the source
   brings to the front: get_vars, written out as dataSem_get_vars *)
(* HOL4 data_spaceProofScript.sml:12-17: an overload that the source
   brings to the front: cut_env, written out as dataSem_cut_env *)
(* HOL4 data_spaceProofScript.sml:12-17: an overload that the source
   brings to the front: evaluate, written out as dataSem_evaluate *)
(* HOL4 data_spaceProofScript.sml:12-17: an overload that the source
   brings to the front: lookup, written out as sptree_lookup *)
(* HOL4 data_spaceProofScript.sml:12-17: an overload that the source
   brings to the front: insert, written out as sptree_insert *)
(* HOL4 data_spaceProofScript.sml:12-17: an overload that the source
   brings to the front: wf, written out as sptree_wf *)

(* [local] *)
let IMP_sptree_eq = prove
 (`sptree_wf x /\ sptree_wf y /\ (!a. sptree_lookup a x =
  sptree_lookup a y) ==> (x = y)`,
  CHEAT_TAC);;

(* [local] *)
let mk_wf_inter = prove
 (`!t1 t2. inter t1 t2 = mk_wf (inter t1 t2)`,
  CHEAT_TAC);;

let get_vars_IMP_LENGTH = prove
 (`!xs s l. dataSem_get_vars xs s = SOME l ==> (LENGTH l = LENGTH xs)`,
  CHEAT_TAC);;

let do_stack_with_space = prove
 (`!op vs s z. do_stack op vs (dataSem_state_space_fupd (K z) s) =
  dataSem_state_space_fupd (K z) (do_stack op vs s)`,
  CHEAT_TAC);;

let do_stack_with_locals = prove
 (`!op vs s l. do_stack op vs (dataSem_state_locals_fupd (K l) s) =
  dataSem_state_locals_fupd (K l) (do_stack op vs s)`,
  CHEAT_TAC);;

(* evaluate_compile[local] *)
let data_spaceProof_evaluate_compile = prove
 (`!c s res s2 vars' l. ~(res = SOME (Rerr (Rabort Rtype_error))) /\
  (dataSem_evaluate (c,s) = (res,s2)) /\
      locals_ok (dataSem_state_locals s) l ==>
      (?w safe peak smx.
       (dataSem_evaluate (data_space_compile
         c,dataSem_state_locals_fupd (K l) s) =
          (res,(if res = NONE then dataSem_state_stack_max_fupd (K
            smx) (dataSem_state_peak_heap_length_fupd (K peak)
            (dataSem_state_safe_for_space_fupd (K safe)
            (dataSem_state_locals_fupd (K w) s2))) else
            dataSem_state_stack_max_fupd (K smx)
            (dataSem_state_peak_heap_length_fupd (K peak)
            (dataSem_state_safe_for_space_fupd (K safe) s2))))) /\
          locals_ok (dataSem_state_locals s2) w)`,
  CHEAT_TAC);;

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


(* compile_correct *)
let data_spaceProof_compile_correct = prove
 (`!c s. ~(FST (dataSem_evaluate (c,s)) = NONE) /\ ~(FST
  (dataSem_evaluate (c,s)) = SOME (Rerr (Rabort Rtype_error))) ==>
      (?safe peak smx. dataSem_evaluate (data_space_compile c,s) =
                      (I ## (\s. dataSem_state_stack_max_fupd (K smx)
                        (dataSem_state_peak_heap_length_fupd (K peak)
                        (dataSem_state_safe_for_space_fupd (K safe)
                        s))))
                      (dataSem_evaluate (c,s)))`,
  CHEAT_TAC);;

let get_code_labels_space = prove
 (`!x y y0 y1 y2.
   (space x = INL y ==> dataProps_get_code_labels y =
     dataProps_get_code_labels x) /\
   (space x = INR (y0,y1,y2) ==> dataProps_get_code_labels y2 =
     dataProps_get_code_labels x)`,
  CHEAT_TAC);;

(* get_code_labels_compile *)
let data_spaceProof_get_code_labels_compile = prove
 (`!x. dataProps_get_code_labels (data_space_compile x) =
  dataProps_get_code_labels x`,
  CHEAT_TAC);;
add_simp data_spaceProof_get_code_labels_compile;;

(* and the names it reads as variables are constants again *)
let _ = do_list unhide_constant
  ["vars"];;
