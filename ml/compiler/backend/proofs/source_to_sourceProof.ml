(* ======================================================== *)
(*  source_to_sourceProof: ported from HOL4's
    compiler/backend/proofs/source_to_sourceProofScript.sml
    A proof theory about source_to_source.ml, with no definitions
    and 2 theorems.  Needed by backendProof.ml.  *)
(* ======================================================== *)

(*
  Proof of correctness for source_to_source.
 *)

needs "compiler/backend/proofs/source_evalProof.ml";;
needs "compiler/backend/proofs/source_letProof.ml";;
needs "compiler/backend/source_to_source.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "semantics/evaluate.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/proofs/evaluateProps.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "semantics/semantics.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "source_to_sourceProof"
  ["ast"; "evaluate"; "evaluateProps"; "misc"; "semanticPrimitives";
   "semanticPrimitivesProps"; "semantics"; "source_evalProof";
   "source_letProof"; "source_to_source"];;


(* compile_semantics *)
(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let source_to_sourceProof_compile_semantics = prove
 (cake_as_vars (fun () ->
    `~(semantics_prog s env prog ffi_Fail) /\
     semantics_prog s env prog outcome ==>
       semantics_prog s env (source_to_source_compile prog)
         outcome`),
  CHEAT_TAC);;

(* compile_semantics_oracle *)
let source_to_sourceProof_compile_semantics_oracle = prove
 (`!f.
   is_insert_oracle ci f (semanticPrimitives_state_eval_state s) /\
   ~(semantics_prog s env prog ffi_Fail) /\
   semantics_prog s env prog outcome ==>
   semantics_prog (semanticPrimitives_state_eval_state_fupd
             (adjust_oracle ci (source_to_source_compile o f)) s)
         env prog outcome`,
  CHEAT_TAC);;

(* and the interface *)
let _ = unhide_overloads ();;
