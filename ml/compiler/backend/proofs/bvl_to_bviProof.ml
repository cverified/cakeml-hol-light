(* ======================================================== *)
(*  bvl_to_bviProof: ported from HOL4's
    compiler/backend/proofs/bvl_to_bviProofScript.sml
    A proof theory about bvl_to_bvi.ml, with 9 definitions and 123
    theorems.  Needed by backendProof.ml.  *)
(* ======================================================== *)

(*
  Correctness proof for bvl_to_bvi
*)

needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/bvi_inline.ml";;
needs "compiler/backend/bvi_let.ml";;
needs "compiler/backend/bvl_to_bvi.ml";;
needs "compiler/backend/proofs/bvi_inlineProof.ml";;
needs "compiler/backend/proofs/bvi_letProof.ml";;
needs "compiler/backend/proofs/bvi_tailrecProof.ml";;
needs "compiler/backend/proofs/bvi_tmcProof.ml";;
needs "compiler/backend/proofs/bvl_constProof.ml";;
needs "compiler/backend/proofs/bvl_handleProof.ml";;
needs "compiler/backend/proofs/bvl_inlineProof.ml";;
needs "compiler/backend/semantics/backendProps.ml";;
needs "compiler/backend/semantics/bviProps.ml";;
needs "compiler/backend/semantics/bviSem.ml";;
needs "compiler/backend/semantics/bvlProps.ml";;
needs "compiler/backend/semantics/bvlSem.ml";;
needs "compiler/backend/semantics/closSem.ml";;
needs "lib/sptree.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/semanticPrimitives.ml";;

(* HOL4 bvl_to_bviProofScript.sml:22: ML code, not ported *)

(* value relation *)
(* HOL4 bvl_to_bviProofScript.sml:25: the overload num_stubs, which
   the port expands *)
(* HOL4 bvl_to_bviProofScript.sml:26: the overload nss, which the
   port expands *)

let _ = size_thms "bvlSem_v";;
(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 bvl_to_bviProofScript.sml:34-38: the tactic that proves the
   termination *)
let adjust_bv_def = cake_define_list_try (fun () ->
  `MEASURE (bvlSem_v_size o SND)`)
  [`adjust_bv b (Number i:bvlSem_v) = bvlSem_Number i`;
   `adjust_bv b (Word64 w:bvlSem_v) = bvlSem_Word64 w`;
   `adjust_bv b (RefPtr l r:bvlSem_v) = bvlSem_RefPtr l (b r)`;
   `adjust_bv b (bvlSem_CodePtr c:bvlSem_v) = bvlSem_CodePtr
  (bvl_num_stubs + bvl_to_bvi_namespaces * c)`;
   `adjust_bv b (Block tag vs:bvlSem_v) = bvlSem_Block tag (MAP
  (adjust_bv b) vs)`];;

(* HOL4 bvl_to_bviProofScript.sml:40: ML code, not ported *)

let aux_code_installed_def = cake_define_list
  [`aux_code_installed [] t <=> T`;
   `aux_code_installed ((name,arg_count,body) :: rest) t <=>
         (sptree_lookup name t = SOME (arg_count,body)) /\
         aux_code_installed rest t`];;

(* HOL4 bvl_to_bviProofScript.sml:78: the overload in_ns_0, which the
   port expands *)
(* HOL4 bvl_to_bviProofScript.sml:79: the overload in_ns_1, which the
   port expands *)

let names_ok_def = cake_define
  `bvl_to_bviProof_names_ok s_code t_code s_oracle <=>
     (!n k prog. s_oracle n = (k,prog) ==>
                 EVERY (\(name,arity,exp). handle_ok [exp]) prog) /\
     (let next' = FST (FST (s_oracle 0)) in
       (!n. n IN domain t_code /\ bvl_num_stubs <= n ==>
            (if (\n. n MOD bvl_to_bvi_namespaces = 1) n then n <
              bvl_num_stubs + bvl_to_bvi_namespaces * next' else (\n. n
              MOD bvl_to_bvi_namespaces = 0) n /\
                 (n - bvl_num_stubs) DIV bvl_to_bvi_namespaces IN
                   domain s_code)))`;;
hol4_overload "names_ok" "bvl_to_bviProof_names_ok";;

let state_rel_def = cake_define
  `bvl_to_bviProof_state_rel (b:num->num) s (t:('c,'ffi)bviSem_state)
  <=>
     INJ b (FDOM (state_refs s)) (FDOM (state_refs t)) /\
     (!k. match FLOOKUP (state_refs s) k with NONE -> T | SOME
       (ValueArray vs) ->
              (FLOOKUP (state_refs t) (b k) = SOME (ValueArray (MAP
                (adjust_bv b) vs))) | SOME (Thunk m v) ->
              (FLOOKUP (state_refs t) (b k) = SOME (Thunk m
                (adjust_bv b v))) | SOME res -> (FLOOKUP (state_refs t)
                (b k) = SOME res)) /\
     (state_ffi s = state_ffi t) /\
     (!p. bviSem_state_global t = SOME p ==> ~(
            p IN IMAGE b (FDOM (state_refs s))) /\
            (?z. FLOOKUP (state_refs t) p =
                  SOME (ValueArray
                    ((Number (&(SUC (LENGTH (state_globals s))))) ::
                     (MAP (the (Number (&0)) o OPTION_MAP (adjust_bv
                       b)) (state_globals s) ++
                     REPLICATE (z - (SUC (LENGTH (state_globals s))))
                       (Number (&0))))) /\
                SUC (LENGTH (state_globals s)) <= z)) /\
     (state_clock s = state_clock t) /\ compile_oracle
     t = state_co compile_inc (compile_oracle s) /\ compile
     s = state_cc compile_inc (compile t) /\
     (sptree_lookup AllocGlobal_location (state_code t) = SOME
       AllocGlobal_code) /\
     (sptree_lookup CopyGlobals_location (state_code t) = SOME
       CopyGlobals_code) /\
     (sptree_lookup ListLength_location (state_code t) = SOME
       ListLength_code) /\
     (sptree_lookup FromListByte_location (state_code t) = SOME
       FromListByte_code) /\
     (sptree_lookup ToListByte_location (state_code t) = SOME
       ToListByte_code) /\
     (sptree_lookup SumListLength_location (state_code t) = SOME
       SumListLength_code) /\
     (sptree_lookup ConcatByte_location (state_code t) = SOME
       ConcatByte_code) /\
     bvl_to_bviProof_names_ok (state_code s) (state_code t)
       (compile_oracle s) /\
     (!name arity exp.
        (sptree_lookup name (state_code s) = SOME (arity,exp)) ==>
        (?n. let (c1,aux1,n1) = compile_exps n [exp] in
              (sptree_lookup (bvl_num_stubs + bvl_to_bvi_namespaces *
                name) (state_code t) =
                 SOME (arity,bvi_let_compile_exp (HD c1))) /\
              aux_code_installed (append aux1) (state_code t) /\
              handle_ok [exp]))`;;
hol4_overload "state_rel" "bvl_to_bviProof_state_rel";;

let _ = size_thms "bvlSem_v";;
(* HOL4 bvl_to_bviProofScript.sml:172-176: the tactic that proves the
   termination *)
let bv_ok_def = cake_define_wf
  `MEASURE (bvlSem_v_size o SND)`
  `bv_ok refs x2 =
        match (refs,x2) with
          ((refs:(num,bvlSem_v bvlSem_ref)fmap),(RefPtr l
            r:bvlSem_v)) -> r IN FDOM refs
        | (refs,(Block tag vs)) -> EVERY (bv_ok refs) vs
        | (refs,_1) -> T`;;

(* HOL4 bvl_to_bviProofScript.sml:178: ML code, not ported *)

let state_ok_def = cake_define
  `bvl_to_bviProof_state_ok (s:('c,'ffi)bvlSem_state) <=>
     EVERY (\x. match x with NONE -> T | SOME v -> bv_ok (state_refs
       s) v) (state_globals s) /\
     (!k. match FLOOKUP (state_refs s) k with SOME (ValueArray vs)
       -> EVERY (bv_ok (state_refs s)) vs | SOME (Thunk _2 v) ->
       bv_ok (state_refs s) v | _3 -> T)`;;
hol4_overload "state_ok" "bvl_to_bviProof_state_ok";;

(* evaluate preserves state_ok *)

(* HOL4 bvl_to_bviProofScript.sml:264-276: code that the source has
   in a comment *)

(* HOL4 bvl_to_bviProofScript.sml:318-319: ML code, not ported *)
(* HOL4 bvl_to_bviProofScript.sml:596: ML code, not ported *)

(* semantics lemmas *)

(* HOL4 bvl_to_bviProofScript.sml:680-694: a proof *)

(* HOL4 bvl_to_bviProofScript.sml:696-707: a proof *)

(* HOL4 bvl_to_bviProofScript.sml:727: ML code, not ported *)

(* correctness of stubs *)

(* HOL4 bvl_to_bviProofScript.sml:731-732: ML code, not ported *)
(* HOL4 bvl_to_bviProofScript.sml:782-783: ML code, not ported *)

(* compiler correctness *)

(* HOL4 bvl_to_bviProofScript.sml:1086-1087: ML code, not ported *)

(* HOL4 bvl_to_bviProofScript.sml:1105-1136: a proof *)

(* HOL4 bvl_to_bviProofScript.sml:1921-1923: ML code, not ported *)

let in_ns_def = cake_define
  `in_ns k n <=> n MOD bvl_to_bvi_namespaces = k`;;

(* HOL4 bvl_to_bviProofScript.sml:2007: the ML values that the
   definitions below antiquote *)

(* the compiled bvi Call handler post-processes its result, rejecting an
   escaping Ret; a mapped bvl handler result (raised values lifted through Exn)
   never raises a Ret, so the post-processing is the identity *)

(* HOL4 bvl_to_bviProofScript.sml:2182: ML code, not ported *)

(* HOL4 bvl_to_bviProofScript.sml:2184-2199: the ML values that the
   definitions below antiquote *)

(* HOL4 bvl_to_bviProofScript.sml:2232-3504: a proof *)
    (* the ops reserved for bvi_tmc are the remaining ones compile_op does not
       leave alone; each is ruled out by bvlSem$do_app being Error on it *)
(* HOL4 bvl_to_bviProofScript.sml:3507-3519: a proof *)

(* HOL4 bvl_to_bviProofScript.sml:3521-3527: a proof *)

(* HOL4 bvl_to_bviProofScript.sml:3529-3585: a proof *)

(* HOL4 bvl_to_bviProofScript.sml:3587-3595: a proof *)

(* HOL4 bvl_to_bviProofScript.sml:3597-3665: a proof *)

(* HOL4 bvl_to_bviProofScript.sml:3667-3785: a proof *)

(* HOL4 bvl_to_bviProofScript.sml:3787-3808: a proof *)

(* HOL4 bvl_to_bviProofScript.sml:3810-3965: a proof *)

(* HOL4 bvl_to_bviProofScript.sml:3967-4026: a proof *)

(* HOL4 bvl_to_bviProofScript.sml:4028-4054: a proof *)

(* HOL4 bvl_to_bviProofScript.sml:4056-4171: a proof *)

(* HOL4 bvl_to_bviProofScript.sml:4173: a proof *)

(* composed compiler correctness *)

let full_cc_def = cake_define
  `full_cc c cc =
     (let limit' = bvl_to_bvi_config_inline_size_limit c in
     let split = bvl_to_bvi_config_split_main_at_seq c in
     let cut = bvl_to_bvi_config_exp_cut c in
       state_cc (compile_inc limit' split cut) (state_cc compile_inc
         (state_cc (bvi_tailrec_compile_prog
           (bvl_to_bvi_config_do_tailrec c))
           (state_cc (bvi_tmc_compile_prog (bvl_to_bvi_config_do_tmc
             c))
             (state_cc bvi_inline_compile_inc cc)))))`;;

let full_co_def = cake_define
  `full_co c co =
     (let limit' = bvl_to_bvi_config_inline_size_limit c in
     let split = bvl_to_bvi_config_split_main_at_seq c in
     let cut = bvl_to_bvi_config_exp_cut c in
       state_co bvi_inline_compile_inc
         (state_co (bvi_tmc_compile_prog (bvl_to_bvi_config_do_tmc
           c))
           (state_co (bvi_tailrec_compile_prog
             (bvl_to_bvi_config_do_tailrec c))
             (state_co compile_inc
               (state_co (compile_inc limit' split cut) co)))))`;;

(* --- no_mutcons: syntactic absence of MutCons operations ---

   The bvi_tmc pass requires its input to be free of MutCons operations
   (the no_mutcons conjunct of bvi_tmc's input_condition).  This holds
   unconditionally: compile_op compiles out the mem_ops reserved for
   bvi_tmc (bvlSem$do_app is Error on them), so no bvi code produced by
   bvl_to_bvi contains them.  The lemmas below carry the property
   through bvi_let and bvi_tailrec to the two input_condition
   obligations in compile_semantics below. *)

(* no_mutcons preservation: bvi_let *)

(* no_mutcons preservation: bvl_to_bvi compile *)

(* no_mutcons preservation: bvi_tailrec *)

(* A name outside namespace 2 cannot be one of bvi_tailrec's fresh names,
   which are all congruent to num_stubs + 2 modulo the namespace count. *)
(* NB free_names must be qualified: bvi_tmcProof defines an identically
   printing (and identically stated) constant of the same name. *)

(* The code-label containment for the whole pass boundary, composing all four
   stages of [compile]: bvl_inline, compile_prog, bvi_tailrec and bvi_inline.
   The last two only ever shrink the label set relative to the names they keep,
   so the shape matches compile_prog_get_code_labels above, widened by the
   fresh names bvi_tailrec allocates. *)
