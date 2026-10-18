(* ======================================================== *)
(*  bvi_to_dataProof: ported from HOL4's
    compiler/backend/proofs/bvi_to_dataProofScript.sml
    A proof theory about bvi_to_data.ml, with 5 definitions and 55
    theorems.  Needed by backendProof.ml.  *)
(* ======================================================== *)

(*
  Correctness proof for bvi_to_data
*)

needs "compiler/backend/bvi_to_data.ml";;
needs "compiler/backend/data_live.ml";;
needs "compiler/backend/proofs/data_liveProof.ml";;
needs "compiler/backend/proofs/data_simpProof.ml";;
needs "compiler/backend/proofs/data_spaceProof.ml";;
needs "compiler/backend/semantics/bviProps.ml";;
needs "compiler/backend/semantics/bviSem.ml";;
needs "compiler/backend/semantics/bvlSem.ml";;
needs "compiler/backend/semantics/closSem.ml";;
needs "compiler/backend/semantics/dataProps.ml";;
needs "compiler/backend/semantics/dataSem.ml";;
needs "lib/sptree.ml";;
needs "semantics/ast.ml";;
needs "semantics/semanticPrimitives.ml";;

(* value relation *)

let code_rel_def = cake_define
  `bvi_to_dataProof_code_rel (bvi_code:(num#bvi_exp) spt)
  (data_code:(num#dataLang_prog) spt) <=>
     sptree_wf bvi_code /\ sptree_wf data_code /\
     (domain bvi_code = domain data_code) /\
     (!n exp arg_count.
       (lookup n bvi_code = SOME (arg_count,exp)) ==>
       (lookup n data_code = SOME (arg_count,compile_exp arg_count
         exp)))`;;
hol4_overload "code_rel" "bvi_to_dataProof_code_rel";;

(* Projection from `dataSem$v` into `bvlSem$v` that basically gets rid of
   timestamp information (note this make the function non-injective)
*)

let _ = size_thms "dataSem_v";;
(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 bvi_to_dataProofScript.sml:36-48: the tactic that proves the
   termination *)
let data_to_bvi_v_def = cake_define_list_try (fun () ->
  `MEASURE dataSem_v_size`)
  [`data_to_bvi_v (Number i:dataSem_v) = bvlSem_Number i`;
   `data_to_bvi_v (Word64 w:dataSem_v) = bvlSem_Word64 w`;
   `data_to_bvi_v (CodePtr p:dataSem_v) = bvlSem_CodePtr p`;
   `data_to_bvi_v (RefPtr b r:dataSem_v) = bvlSem_RefPtr b r`;
   `data_to_bvi_v (Block _2 tag l:dataSem_v) = bvlSem_Block tag
  (MAP data_to_bvi_v l)`];;

(* Projection for Unit constant *)

(* Projection for Boolv constant *)

(* Projection for references, non-injective for value arrays *)
let data_to_bvi_ref_def = cake_define_list
  [`data_to_bvi_ref (bvlSem_ValueArray l) = ValueArray (MAP
  data_to_bvi_v l)`;
   `data_to_bvi_ref (bvlSem_ByteArray b bl) = (ByteArray b bl:'a
  bvlSem_ref)`;
   `data_to_bvi_ref (bvlSem_Thunk m v) = Thunk m (data_to_bvi_v v)`;
   `data_to_bvi_ref (bvlSem_MutBlock tg fin ls c rs) =
        bvlSem_MutBlock tg fin (MAP data_to_bvi_v ls)
          (data_to_bvi_v c) (MAP data_to_bvi_v rs)`];;

(* State relation *)
let state_rel_def = cake_define
  `bvi_to_dataProof_state_rel (s:('c,'ffi)bviSem_state)
  (t:('c,'ffi)dataSem_state) <=>
     (state_clock s = state_clock t) /\
     bvi_to_dataProof_code_rel (state_code s) (state_code t) /\
     (compile_oracle t = ((I ## bvi_to_data_compile_prog) o
       compile_oracle s)) /\
     (compile s = (\cfg prog. compile t cfg (bvi_to_data_compile_prog
       prog))) /\
     (!n. FLOOKUP (state_refs s) n = lookup n (map data_to_bvi_ref
       (state_refs t))) /\
     (state_ffi s = state_ffi t) /\
     (state_global s = state_global t)`;;
hol4_overload "state_rel" "bvi_to_dataProof_state_rel";;

(* semantics lemmas *)

(* HOL4 bvi_to_dataProofScript.sml:156: the overload isException,
   which the port expands *)
(* HOL4 bvi_to_dataProofScript.sml:157: the overload isReturn, which
   the port expands *)
(* HOL4 bvi_to_dataProofScript.sml:158: the overload isResult, which
   the port expands *)

(* HOL4 bvi_to_dataProofScript.sml:160: the ML values that the
   definitions below antiquote *)

(* HOL4 bvi_to_dataProofScript.sml:162: ML code, not ported *)

(* Projection for results, injective upto `dataSem$v` *)
let data_to_bvi_result_def = cake_define
  `data_to_bvi_result x1 =
      match x1 with
        Rval vs -> Rval (MAP data_to_bvi_v vs)
      | (Rerr (Rraise v)) -> Rerr (Rraise (Exn (data_to_bvi_v v)))
      | (Rerr (Rabort err)) -> Rerr (Rabort err)`;;

(* All the `dataSem$v` values project to `bvlSem$Boolv b` satisfy `isBool` *)

(* Lifting `data_to_bvi_v` projection to work over `bvlSem$v list` *)

(* Special bijection for `data_to_bvi_v` with `dataSem$Number` + `MAP` *)

(* Special bijection for `data_to_bvi_v` with `dataSem$Word64` + `MAP` *)

(* Bijection of `data_to_bvi_v (Number n)` over multiple maps *)

(* Bijection of `data_to_bvi_v (Word64 n)` over multiple maps *)

(* `data_to_bvi_v_def` is idempotent over `v_to_bytes` *)

(* `data_to_bvi_v_def` is idempotent over `v_to_words` *)

(* isBool simplifications *)

(* HOL4 bvi_to_dataProofScript.sml:272-273: ML code, not ported *)

(* A variable correspondece (`var_corr`) over projecte values in `t2`
   implies all values in `a` are projections of values in `t2`
 *)

(* `data_to_bvi_v` preserves `var_corr` *)

(* Construction of the pre-image of `data_to_bvi_v`,
   wich in all cases except `Block` is bijective
 *)
(*flip LHS equalities*)

(* HOL4 bvi_to_dataProofScript.sml:355-361: ML code, not ported *)

(* HOL4 bvi_to_dataProofScript.sml:381-385: ML code, not ported *)

(* Construction of the pre-image of `data_to_bvi_result` *)

(* `data_to_bvi_v` preservers `do_eq` *)

(* HOL4 bvi_to_dataProofScript.sml:445-452: code that the source has
   in a comment *)

(* bviSem$finalise_cons is simulated by dataSem$finalise_cons: the extra
   time stamps taken by the dataLang version are invisible to the projection *)

(* HOL4 bvi_to_dataProofScript.sml:527-530: a proof *)

(* HOL4 bvi_to_dataProofScript.sml:817: ML code, not ported *)

(* HOL4 bvi_to_dataProofScript.sml:878-883: a proof *)

(* HOL4 bvi_to_dataProofScript.sml:885-917: a proof *)

(* HOL4 bvi_to_dataProofScript.sml:919-937: a proof *)

(* HOL4 bvi_to_dataProofScript.sml:939-1066: a proof *)

(* HOL4 bvi_to_dataProofScript.sml:1068-1101: a proof *)

(* HOL4 bvi_to_dataProofScript.sml:1103-1124: a proof *)

(* HOL4 bvi_to_dataProofScript.sml:1126-1138: a proof *)

(* HOL4 bvi_to_dataProofScript.sml:1140-1243: a proof *)
   (* single-cut: do_app reads args from full t2.locals (pre-cut); recover
      get_vars over t2.locals from the get_vars over the cut env1 *)
(* HOL4 bvi_to_dataProofScript.sml:1246-1839: a proof *)

(* HOL4 bvi_to_dataProofScript.sml:1841-1857: a proof *)

(* HOL4 bvi_to_dataProofScript.sml:1859-2089: a proof *)

(* HOL4 bvi_to_dataProofScript.sml:2091-2613: a proof *)

(* HOL4 bvi_to_dataProofScript.sml:2615-2890: a proof *)

(* HOL4 bvi_to_dataProofScript.sml:2892: a proof *)

(* HOL4 bvi_to_dataProofScript.sml:2894-2897: ML code, not ported *)

(* observational semantics *)
