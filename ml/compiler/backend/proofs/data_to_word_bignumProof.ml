(* ======================================================== *)
(*  data_to_word_bignumProof: ported from HOL4's
    compiler/backend/proofs/data_to_word_bignumProofScript.sml  *)
(* ======================================================== *)

(*
  Part of the correctness proof for data_to_word
*)

needs "basis/pure/mllist.ml";;
needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/dataLang.ml";;
needs "compiler/backend/data_to_word.ml";;
needs "compiler/backend/gc/copying_gc.ml";;
needs "compiler/backend/gc/gc_shared.ml";;
needs "compiler/backend/gc/gen_gc.ml";;
needs "compiler/backend/gc/gen_gc_partial.ml";;
needs "compiler/backend/proofs/data_to_word_gcProof.ml";;
needs "compiler/backend/proofs/data_to_word_memoryProof.ml";;
needs "compiler/backend/proofs/word_bignumProof.ml";;
needs "compiler/backend/proofs/word_depthProof.ml";;
needs "compiler/backend/proofs/word_gcFunctions.ml";;
needs "compiler/backend/semantics/dataProps.ml";;
needs "compiler/backend/semantics/dataSem.ml";;
needs "compiler/backend/semantics/wordProps.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/backend/word_bignum.ml";;
needs "lib/alignment.ml";;
needs "lib/set_sep.ml";;
needs "semantics/proofs/semanticsProps.ml";;
(* HOL4 ancestors outside the port: int_bitwise finite_map *)

(* HOL4 data_to_word_bignumProofScript.sml:26-27: a proof *)

(* HOL4 data_to_word_bignumProofScript.sml:29-30: ML code, not ported *)

(* HOL4 data_to_word_bignumProofScript.sml:32-36: a proof *)

let get_iop_def = cake_define
  `get_iop (n:num) =
     (if n = 0 then multiword_Add else
     if n = 1 then multiword_Sub else
     if n = 4 then multiword_Mul else
     if n = 5 then multiword_Div else
                   multiword_Mod)`;;

let int_op_def = cake_define
  `data_to_word_bignumProof_int_op op_index (i:int) (j:int) =
     (if op_index = 0 then SOME (i + j) else
     if op_index = 1 then SOME (i - j) else
     if op_index = 4 then SOME (i * j) else
     if op_index = 5 /\ ~(j = (&0)) then SOME (i / j) else
     if op_index = 6 /\ ~(j = (&0)) then SOME (i % j) else NONE)`;;
hol4_overload "int_op" "data_to_word_bignumProof_int_op";;

let arith_location_def = cake_define
  `Arith_location index =
     (if index = 0 then Add_location else
     if index = 1 then Sub_location else
     if index = 4 then Mul_location else
     if index = 5 then Div_location else
     if index = 6 then Mod_location else ARB)`;;

let arith_code_def = cake_define
  `Arith_code index =
     Seq (Assign 6 (wordLang_Const (n2w (4 * index))))
       (Call NONE (SOME AnyArith_location) [0; 2; 4; 6] NONE)`;;

(* HOL4 data_to_word_bignumProofScript.sml:1145: the ML values that
   the definitions below antiquote *)

(* HOL4 data_to_word_bignumProofScript.sml:1147: ML code, not ported *)

(* HOL4 data_to_word_bignumProofScript.sml:1149-1152: ML code, not
   ported *)

(* HOL4 data_to_word_bignumProofScript.sml:2128: ML code, not ported *)
