(* ======================================================== *)
(*  data_to_wordProof: ported from HOL4's
    compiler/backend/proofs/data_to_wordProofScript.sml  *)
(* ======================================================== *)

(*
  Correctness proof for data_to_word
*)

needs "compiler/backend/backend.ml";;
needs "compiler/backend/dataLang.ml";;
needs "compiler/backend/data_to_word.ml";;
needs "compiler/backend/gc/copying_gc.ml";;
needs "compiler/backend/gc/gc_shared.ml";;
needs "compiler/backend/gc/gen_gc.ml";;
needs "compiler/backend/gc/gen_gc_partial.ml";;
needs "compiler/backend/proofs/data_to_word_assignProof.ml";;
needs "compiler/backend/proofs/data_to_word_bignumProof.ml";;
needs "compiler/backend/proofs/data_to_word_gcProof.ml";;
needs "compiler/backend/proofs/data_to_word_memoryProof.ml";;
needs "compiler/backend/proofs/wordConvsProof.ml";;
needs "compiler/backend/proofs/word_bignumProof.ml";;
needs "compiler/backend/proofs/word_to_wordProof.ml";;
needs "compiler/backend/semantics/dataProps.ml";;
needs "compiler/backend/semantics/dataSem.ml";;
needs "compiler/backend/semantics/wordConvs.ml";;
needs "compiler/backend/semantics/wordProps.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/backend/stackLang.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/backend/word_bignum.ml";;
needs "compiler/backend/word_to_word.ml";;
needs "lib/alignment.ml";;
needs "lib/set_sep.ml";;
needs "lib/sptree.ml";;
needs "semantics/proofs/semanticsProps.ml";;
(* HOL4 ancestors outside the port: int_bitwise finite_map While *)

(* HOL4 data_to_wordProofScript.sml:23-24: a proof *)

(* HOL4 data_to_wordProofScript.sml:26-27: ML code, not ported *)

(* HOL4 data_to_wordProofScript.sml:29-35: ML code, not ported *)

(* shared conjunct tail for the two popped-frame cases (Env / Exc) of
   state_rel_pop_env_set_vars_IMP below. *)
(* HOL4 data_to_wordProofScript.sml:179-252: a proof *)

(* multi-value generalisation of state_rel_pop_env_set_var_IMP
   (gcProof): the
   returning-Call reconstruction places the whole result list via
     set_vars. *)

(* HOL4 data_to_wordProofScript.sml:283-285: a proof *)

(* HOL4 data_to_wordProofScript.sml:287-289: a proof *)

(* HOL4 data_to_wordProofScript.sml:291: a proof *)

(* HOL4 data_to_wordProofScript.sml:348-351: a proof *)

(* HOL4 data_to_wordProofScript.sml:353-365: a proof *)

(* HOL4 data_to_wordProofScript.sml:367-389: a proof *)

(* HOL4 data_to_wordProofScript.sml:391-741: a proof *)

(* HOL4 data_to_wordProofScript.sml:743-751: a proof *)

(* HOL4 data_to_wordProofScript.sml:753-832: a proof *)

(* HOL4 data_to_wordProofScript.sml:834-843: a proof *)

(* HOL4 data_to_wordProofScript.sml:845-868: a proof *)

(* HOL4 data_to_wordProofScript.sml:870-907: a proof *)

(* HOL4 data_to_wordProofScript.sml:909-932: a proof *)

(* HOL4 data_to_wordProofScript.sml:934-970: a proof *)
  (* dataSem now has the up-front `ALL_DISTINCT q` guard (matching
     wordSem), so
     `res <> Rtype_error` forces `ALL_DISTINCT q`. *)
(* HOL4 data_to_wordProofScript.sml:973-1152: a proof *)

(* HOL4 data_to_wordProofScript.sml:1154: a proof *)

let state_rel_ext_def = cake_define
  `state_rel_ext c l1 l2 s u <=>
     (?t l.
       state_rel c l1 l2 s t NONE [] /\
       domain (wordSem_state_code t) = domain l /\
         wordSem_state_termdep
       t > 1 /\
       (?tt kk aa co. wordSem_state_compile_oracle
          u =
            (I ## MAP (\p. full_compile_single tt kk aa co (p,NONE)))
              o wordSem_state_compile_oracle
              t /\ wordSem_state_compile
          t = (\conf progs. wordSem_state_compile u conf
            (MAP (\p. full_compile_single tt kk aa co (p,NONE))
              progs))) /\
       (!n v. lookup n (wordSem_state_code t) = SOME v ==>
              (?t' k' a' c' col.
              lookup n l = SOME (SND (full_compile_single t' k' a' c'
                ((n,v),col))))) /\
       u = wordSem_state_compile_oracle_fupd (K
         (wordSem_state_compile_oracle u))
         (wordSem_state_compile_fupd (K (wordSem_state_compile u))
         (wordSem_state_termdep_fupd (K 0) (wordSem_state_code_fupd
         (K l) t))))`;;

(* observational semantics preservation *)

let get_limits_def = cake_define
  `get_limits c (t:('a,'c,'ffi)wordSem_state) =
     mk_limits (w2n (theWord (FAPPLY (wordSem_state_store t)
       HeapLength)) DIV (dimindex (:'a) DIV 8))
       (data_to_word_config_len_size c) (wordSem_state_stack_limit t)
       (dimindex (:'a) = 64) (has_fp_ops c)
       (data_to_word_config_has_fp_tern c)`;;

(* HOL4 data_to_wordProofScript.sml:1917: ML code, not ported *)

(* HOL4 data_to_wordProofScript.sml:1919: ML code, not ported *)

(* TODO: goes away on inlineenc branch *)

(* HOL4 data_to_wordProofScript.sml:1987-1989: ML code, not ported *)

(* no ShareInst in the compiled program *)

(***)

(* HOL4 data_to_wordProofScript.sml:2294-2296: ML code, not ported *)

(*
inst_ok_less_def
*)

(* HOL4 data_to_wordProofScript.sml:2482: the overload
   data_get_code_labels, which the port expands *)
(* HOL4 data_to_wordProofScript.sml:2483: the overload
   data_good_code_labels, which the port expands *)

(* semi-slow... *)

(* slow... *)

(* HOL4 data_to_wordProofScript.sml:2750: the ML values that the
   definitions below antiquote *)

(* TODO: move somewhere better *)
let stubs_fst_def = cake_define
  `stubs_fst = MAP FST (data_to_word_stubs (:1)
                 (ARB:data_to_word_config))`;;

(* The incremental version ONLY does data_to_word
  TODO: MAP FST stubs is independent of the data conf,
  not sure if generality is needed
*)
