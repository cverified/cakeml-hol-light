(* ======================================================== *)
(*  bvi_to_dataProof: ported from HOL4's
    compiler/backend/proofs/bvi_to_dataProofScript.sml
    A proof theory about bvi_to_data.ml, with 5 definitions and 55
    theorems.  Needed by backendProof.ml.  *)
(* ======================================================== *)

(*
  Correctness proof for bvi_to_data
*)

needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/bvi.ml";;
needs "compiler/backend/bvi_to_data.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/data_live.ml";;
needs "compiler/backend/proofs/data_liveProof.ml";;
needs "compiler/backend/proofs/data_simpProof.ml";;
needs "compiler/backend/proofs/data_spaceProof.ml";;
needs "compiler/backend/semantics/bviProps.ml";;
needs "compiler/backend/semantics/bviSem.ml";;
needs "compiler/backend/semantics/bvlProps.ml";;
needs "compiler/backend/semantics/bvlSem.ml";;
needs "compiler/backend/semantics/closSem.ml";;
needs "compiler/backend/semantics/dataProps.ml";;
needs "compiler/backend/semantics/dataSem.ml";;
needs "lib/comparison.ml";;
needs "lib/sptree.ml";;
needs "semantics/ast.ml";;
needs "semantics/evaluate.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/semanticPrimitives.ml";;

cake_hide ["parts"];;

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
let data_to_bvi_v_Unit = cake_theorem "data_to_bvi_v_Unit[simp]"
  (fun () ->
    `data_to_bvi_v Unit' = Unit'`)
  CHEAT_TAC;;

(* Projection for Boolv constant *)
let data_to_bvi_v_Boolv = cake_theorem "data_to_bvi_v_Boolv[simp]"
  (fun () ->
    `!b. data_to_bvi_v (Boolv b) = (Boolv b)`)
  CHEAT_TAC;;

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

let find_code_lemma = cake_theorem "find_code_lemma[local]"
  (fun () ->
    `state_rel r t2 /\
       find_code dest (MAP data_to_bvi_v a) (state_code r) = SOME
         (args,exp) ==> (?args' ss.
          args = MAP data_to_bvi_v args' /\
          dataSem_find_code dest a (state_code t2)
            (dataSem_state_stack_frame_sizes t2) =
            SOME (args',compile_exp (LENGTH args') exp,ss))`)
  CHEAT_TAC;;

let optimise_correct = cake_theorem "optimise_correct"
  (fun () ->
    `!c s. ~(FST (evaluate (c,s)) = SOME (Rerr (Rabort Rtype_error))) /\
  ~(
           FST (evaluate (c,s)) = NONE) ==>
           (?safe peak smx ls.
             evaluate (bvi_to_data_optimise c,s) = (I ## (\x.
               dataSem_state_stack_max_fupd (K smx)
               (dataSem_state_peak_heap_length_fupd (K peak)
               (dataSem_state_safe_for_space_fupd (K safe)
               (dataSem_state_locals_size_fupd (K ls) x)))))
                              (evaluate (c,s)))`)
  CHEAT_TAC;;

let compile_RANGE_lemma = cake_theorem "compile_RANGE_lemma[local]"
  (fun () ->
    `!n env tail live xs.
         EVERY (\v. v < (SND (SND (compile n env tail live xs))))
           (FST (SND (compile n env tail live xs)))`)
  CHEAT_TAC;;

let compile_RANGE = cake_theorem "compile_RANGE[local]"
  (fun () ->
    `(compile n env tail live xs = (ys,vs,k)) ==> EVERY (\v. v < k) vs`)
  CHEAT_TAC;;

(* HOL4 bvi_to_dataProofScript.sml:156: the overload isException,
   which the port expands *)
(* HOL4 bvi_to_dataProofScript.sml:157: the overload isReturn, which
   the port expands *)
(* HOL4 bvi_to_dataProofScript.sml:158: the overload isResult, which
   the port expands *)

(* HOL4 bvi_to_dataProofScript.sml:160: the ML values that the
   definitions below antiquote *)

(* HOL4 bvi_to_dataProofScript.sml:162: ML code, not ported *)

let compile_part_thm = cake_theorem "compile_part_thm[local]"
  (fun () ->
    `compile_part = (\(x,y). (x,(\(a,b). (a,compile_exp a b)) y))`)
  CHEAT_TAC;;

(* Projection for results, injective upto `dataSem$v` *)
let data_to_bvi_result_def = cake_define
  `data_to_bvi_result x1 =
      match x1 with
        Rval vs -> Rval (MAP data_to_bvi_v vs)
      | (Rerr (Rraise v)) -> Rerr (Rraise (Exn (data_to_bvi_v v)))
      | (Rerr (Rabort err)) -> Rerr (Rabort err)`;;

(* All the `dataSem$v` values project to `bvlSem$Boolv b` satisfy `isBool` *)
let isBool_eq = cake_theorem "isBool_eq"
  (fun () ->
    `!z b. isBool b z <=> (Boolv b = data_to_bvi_v z)`)
  CHEAT_TAC;;

(* Lifting `data_to_bvi_v` projection to work over `bvlSem$v list` *)
let v_to_list_eq = cake_theorem "v_to_list_eq[simp]"
  (fun () ->
    `!x. v_to_list (data_to_bvi_v x) = OPTION_MAP (MAP data_to_bvi_v)
  (v_to_list x)`)
  CHEAT_TAC;;

(* Special bijection for `data_to_bvi_v` with `dataSem$Number` + `MAP` *)
let data_to_bvi_number_eq = cake_theorem "data_to_bvi_number_eq"
  (fun () ->
    `!ns.
       MAP data_to_bvi_v' (MAP (Number o (&) o w2n') ns) =
       MAP (Number o (&) o w2n') ns`)
  CHEAT_TAC;;

(* Special bijection for `data_to_bvi_v` with `dataSem$Word64` + `MAP` *)
let data_to_bvi_word_eq = cake_theorem "data_to_bvi_word_eq"
  (fun () ->
    `!ns.
       MAP data_to_bvi_v' (MAP Word64 ns) =
       MAP Word64 ns`)
  CHEAT_TAC;;

(* Bijection of `data_to_bvi_v (Number n)` over multiple maps *)
let MAP_data_to_bvi_Number = cake_theorem "MAP_data_to_bvi_Number"
  (fun () ->
    `!xs ws. MAP data_to_bvi_v (MAP Number xs) = MAP data_to_bvi_v ws
  <=> (MAP Number xs) = ws`)
  CHEAT_TAC;;

(* Bijection of `data_to_bvi_v (Word64 n)` over multiple maps *)
let MAP_data_to_bvi_Word64 = cake_theorem "MAP_data_to_bvi_Word64"
  (fun () ->
    `!xs ws. MAP data_to_bvi_v (MAP Word64 xs) = MAP data_to_bvi_v ws
  <=> (MAP Word64 xs) = ws`)
  CHEAT_TAC;;

(* `data_to_bvi_v_def` is idempotent over `v_to_bytes` *)
let v_to_bytes_eq = cake_theorem "v_to_bytes_eq[simp]"
  (fun () ->
    `!x. v_to_bytes (data_to_bvi_v x) = v_to_bytes x`)
  CHEAT_TAC;;

(* `data_to_bvi_v_def` is idempotent over `v_to_words` *)
let v_to_words_eq = cake_theorem "v_to_words_eq[simp]"
  (fun () ->
    `!x. v_to_words (data_to_bvi_v x) = v_to_words x`)
  CHEAT_TAC;;

(* isBool simplifications *)
let isBool_simps = cake_theorem "isBool_simps"
  (fun () ->
    `(!b z. isBool T (z:dataSem_v) ==> ~isBool F z) /\
     (!b z. isBool F (z:dataSem_v) ==> ~isBool T z)`)
  CHEAT_TAC;;

(* HOL4 bvi_to_dataProofScript.sml:272-273: ML code, not ported *)

(* A variable correspondece (`var_corr`) over projecte values in `t2`
   implies all values in `a` are projections of values in `t2`
 *)
let get_vars_lift_thm = cake_theorem "get_vars_lift_thm"
  (fun () ->
    `!vs a t2.
       var_corr a vs (map data_to_bvi_v t2) ==> (?z. get_vars vs
         t2 = SOME z /\ a = (MAP data_to_bvi_v z))`)
  CHEAT_TAC;;

let var_corr_inter = cake_theorem "var_corr_inter"
  (fun () ->
    `!t p vs z. var_corr z vs (inter p t) ==> var_corr z vs p`)
  CHEAT_TAC;;

let get_vars_mk_wf = cake_theorem "get_vars_mk_wf[simp]"
  (fun () ->
    `!vs t z. get_vars vs (mk_wf t) = SOME z <=> get_vars vs t = SOME
  z`)
  CHEAT_TAC;;

let get_vars_inter = cake_theorem "get_vars_inter"
  (fun () ->
    `!vs p t z. get_vars vs (inter p t) = SOME z ==> get_vars vs p =
  SOME z`)
  CHEAT_TAC;;

(* `data_to_bvi_v` preserves `var_corr` *)
let var_corr_map = cake_theorem "var_corr_map"
  (fun () ->
    `!p f vs z. var_corr z vs p ==> var_corr (MAP f z) vs (map f p)`)
  CHEAT_TAC;;

(* Construction of the pre-image of `data_to_bvi_v`,
   wich in all cases except `Block` is bijective
 *)
let data_to_bvi_v_eq = cake_theorem "data_to_bvi_v_eq[simp]"
  (fun () ->
    `(!v n i. data_to_bvi_v v = Number i <=> v = Number i) /\
     (!v n w. data_to_bvi_v v = Word64 w <=> v = Word64 w) /\
     (!v n p. data_to_bvi_v v = CodePtr p <=> v = CodePtr p) /\
     (!v n r b. data_to_bvi_v v = RefPtr b r <=> v = RefPtr b r) /\
     (!v n l.
       data_to_bvi_v v = Block n l <=> (?ts l'. v = Block ts n l'
         /\ l = MAP data_to_bvi_v l'))`)
  CHEAT_TAC;;
(*flip LHS equalities*)
(* HOL4 bvi_to_dataProofScript.sml:351-353: a theorem that HOL4
   states as the value of an ML expression *)

(* HOL4 bvi_to_dataProofScript.sml:355-361: ML code, not ported *)

let data_to_bvi_ref_eq = cake_theorem "data_to_bvi_ref_eq[simp]"
  (fun () ->
    `(!v fl ds. data_to_bvi_ref v = ByteArray fl ds <=> v = ByteArray fl
  ds) /\
     (!v l.
       data_to_bvi_ref v = ValueArray l <=> (?l'. v = ValueArray l'
         /\ l = MAP data_to_bvi_v l')) /\
     (!v m w.
       data_to_bvi_ref v = Thunk m w <=> (?w'. v = Thunk m w' /\ w
         = data_to_bvi_v w')) /\
     (!v tg fin ls c rs.
       data_to_bvi_ref v = bvlSem_MutBlock tg fin ls c rs <=> (?ls'
         c' rs'. v = bvlSem_MutBlock tg fin ls' c' rs' /\
                        ls = MAP data_to_bvi_v ls' /\ c =
                          data_to_bvi_v c' /\
                        rs = MAP data_to_bvi_v rs'))`)
  CHEAT_TAC;;

(* HOL4 bvi_to_dataProofScript.sml:377-379: a theorem that HOL4
   states as the value of an ML expression *)

(* HOL4 bvi_to_dataProofScript.sml:381-385: ML code, not ported *)

(* Construction of the pre-image of `data_to_bvi_result` *)
let data_to_bvi_result_eq = cake_theorem "data_to_bvi_result_eq[simp]"
  (fun () ->
    `!x v.
      data_to_bvi_result x = Rerr (Rraise v) <=> (?z. x = Rerr
        (Rraise z) /\ Exn (data_to_bvi_v z) = v)`)
  CHEAT_TAC;;

let data_to_bvi_v_list_to_v_Nil =
  cake_theorem "data_to_bvi_v_list_to_v_Nil"
  (fun () ->
    `!z ts.
     data_to_bvi_v (list_to_v ts Block_nil' z) =
     list_to_v (MAP data_to_bvi_v z)`)
  CHEAT_TAC;;

(* `data_to_bvi_v` preservers `do_eq` *)
let data_to_bvi_do_eq = cake_theorem "data_to_bvi_do_eq"
  (fun () ->
    `(!t v1 v2 r.
       (!n. FLOOKUP r n = lookup n (map data_to_bvi_ref t)) ==>
         do_eq r (data_to_bvi_v v1) (data_to_bvi_v v2) =
         do_eq t v1 v2) /\
     (!t l1 l2 r.
       (!n. FLOOKUP r n = lookup n (map data_to_bvi_ref t)) ==>
         do_eq_list r (MAP data_to_bvi_v l1) (MAP data_to_bvi_v l2) =
         do_eq_list t l1 l2)`)
  CHEAT_TAC;;

let data_to_bvi_v_list_to_v_APPEND =
  cake_theorem "data_to_bvi_v_list_to_v_APPEND"
  (fun () ->
    `!l vl v ts.
      v_to_list v = SOME vl ==> data_to_bvi_v (list_to_v ts v l) =
     data_to_bvi_v (list_to_v ts (Block 0 nil_tag []) (l ++ vl))`)
  CHEAT_TAC;;

(* HOL4 bvi_to_dataProofScript.sml:445-452: code that the source has
   in a comment *)

let refs_rel_LEAST_eq = cake_theorem "refs_rel_LEAST_eq[local]"
  (fun () ->
    `!s1 s2.
      (!n. FLOOKUP s1 n = lookup n (map data_to_bvi_ref s2)) ==>
        (LEAST (\ptr. ~(ptr IN FDOM s1))) = LEAST (\ptr. ~(ptr IN
        domain s2))`)
  CHEAT_TAC;;

let do_build_thm = cake_theorem "do_build_thm"
  (fun () ->
    `!parts' m1 m2 k ts r t q rs.
       do_build m1 k parts' r = (q,rs) /\
       (!n. FLOOKUP r n = OPTION_MAP data_to_bvi_ref (lookup n t))
         /\
       (!n. m1 n = data_to_bvi_v (m2 n)) ==>
       (?pres s1 ts1.
         do_build m2 k parts' t ts = (pres,s1,ts1) /\
         q = data_to_bvi_v pres /\
         (!n. FLOOKUP rs n = OPTION_MAP data_to_bvi_ref (lookup n
           s1)))`)
  CHEAT_TAC;;

let data_to_bvi_v_Boolv_IMP =
  cake_theorem "data_to_bvi_v_Boolv_IMP[local]"
  (fun () ->
    `data_to_bvi_v x0 = Boolv b ==> dest_Boolv x0 = SOME b`)
  CHEAT_TAC;;

(* bviSem$finalise_cons is simulated by dataSem$finalise_cons: the extra
   time stamps taken by the dataLang version are invisible to the projection *)
let data_to_bvi_finalise_cons = cake_theorem "data_to_bvi_finalise_cons"
  (fun () ->
    `!v refs ts brefs bv brefs'.
       (!n. FLOOKUP brefs n = OPTION_MAP data_to_bvi_ref (lookup n
         refs)) /\
       bviSem_finalise_cons (data_to_bvi_v v) brefs = SOME
         (bv,brefs') ==> (?pv refs' ts'.
           dataSem_finalise_cons v refs ts = SOME (pv,refs',ts') /\
           bv = data_to_bvi_v pv /\
           (!n. FLOOKUP brefs' n = OPTION_MAP data_to_bvi_ref
             (lookup n refs')))`)
  CHEAT_TAC;;

(* HOL4 bvi_to_dataProofScript.sml:527-530: a proof *)

let data_to_bvi_do_app = cake_theorem "data_to_bvi_do_app"
  (fun () ->
    `!op t r z res s1.
       ~(
       op = Install) /\ ~(
       op = closLang_IntOp Greater) /\ ~(
       op = closLang_IntOp closLang_GreaterEq) /\ ~(
       op = closLang_WordOp (WordTest ast_W8 (ast_Compare ast_Gt)))
         /\ ~(
       op = closLang_WordOp (WordTest ast_W8 (ast_Compare
         ast_Geq))) /\
       (!b. ~(op = closLang_MemOp (closLang_CopyByte b))) /\ ~(
       op = ThunkOp ForceThunk) /\
       state_rel r t /\
       do_app op (MAP data_to_bvi_v z) r = Rval (res,s1) ==> (?s2
         pres.
          do_app_aux op z t = Rval (pres,s2) /\
          res = data_to_bvi_v pres /\
          state_rel s1 s2)`)
  CHEAT_TAC;;

let state_rel_peak_safe = cake_theorem "state_rel_peak_safe"
  (fun () ->
    `!s s' safe peak ls smx.
       state_rel s s' =
         state_rel s (dataSem_state_stack_max_fupd (K smx)
           (dataSem_state_peak_heap_length_fupd (K peak)
           (dataSem_state_safe_for_space_fupd (K safe)
           (dataSem_state_locals_size_fupd (K ls) s'))))`)
  CHEAT_TAC;;

let jump_exc_peak_safe = cake_theorem "jump_exc_peak_safe"
  (fun () ->
    `!s t safe peak ls smx.
       dataSem_jump_exc s = SOME t ==> dataSem_jump_exc
         (dataSem_state_stack_max_fupd (K smx)
         (dataSem_state_locals_size_fupd (K ls)
         (dataSem_state_peak_heap_length_fupd (K peak)
         (dataSem_state_safe_for_space_fupd (K safe) s)))) =
           SOME (dataSem_state_stack_max_fupd (K smx)
             (dataSem_state_peak_heap_length_fupd (K peak)
             (dataSem_state_safe_for_space_fupd (K safe) t)))`)
  CHEAT_TAC;;

let jump_exc_sfs_lss_peak_safe =
  cake_theorem "jump_exc_sfs_lss_peak_safe"
  (fun () ->
    `!s t safe peak ls sfs smx.
       dataSem_jump_exc s = SOME t ==> dataSem_jump_exc
         (dataSem_state_stack_max_fupd (K smx)
         (dataSem_state_stack_frame_sizes_fupd (K sfs)
         (dataSem_state_locals_size_fupd (K ls)
         (dataSem_state_peak_heap_length_fupd (K peak)
         (dataSem_state_safe_for_space_fupd (K safe) s))))) =
           SOME (dataSem_state_stack_max_fupd (K smx)
             (dataSem_state_stack_frame_sizes_fupd (K sfs)
             (dataSem_state_peak_heap_length_fupd (K peak)
             (dataSem_state_safe_for_space_fupd (K safe) t))))`)
  CHEAT_TAC;;

let jump_exc_lss = cake_theorem "jump_exc_lss"
  (fun () ->
    `!s t ls.
       dataSem_jump_exc s = SOME t ==> dataSem_jump_exc
         (dataSem_state_locals_size_fupd (K ls) s) = SOME t`)
  CHEAT_TAC;;

let state_rel_dest_thunk = cake_theorem "state_rel_dest_thunk"
  (fun () ->
    `state_rel s t /\
     dest_thunk (data_to_bvi_v z) (state_refs s) = IsThunk ev v ==>
       (?v'. dest_thunk z (state_refs t) = IsThunk ev v' /\
            data_to_bvi_v v' = v)`)
  CHEAT_TAC;;

let domain_list_insert2 = cake_theorem "domain_list_insert2[local]"
  (fun () ->
    `domain (list_insert xs t) = set_of_list xs UNION domain t`)
  CHEAT_TAC;;

let domain_list_to_num_set2 =
  cake_theorem "domain_list_to_num_set2[local]"
  (fun () ->
    `domain (list_to_num_set xs) = set_of_list xs`)
  CHEAT_TAC;;

let list_insert_list_to_num_set =
  cake_theorem "list_insert_list_to_num_set[simp,local]"
  (fun () ->
    `list_insert xs (list_to_num_set (xs ++ ys ++ zs)) =
     list_to_num_set (xs ++ ys ++ zs)`)
  CHEAT_TAC;;

let state_rel_do_app_FFI_err =
  cake_theorem "state_rel_do_app_FFI_err[local]"
  (fun () ->
    `!i z r t x.
       state_rel r t /\
       do_app (FFI i) (MAP data_to_bvi_v z) r = Rerr (Rabort
         (Rffi_error x)) ==>
       do_app (FFI i) z t = Rerr (Rabort (Rffi_error x))`)
  CHEAT_TAC;;

let evaluate_Return_GENLIST_Var =
  cake_theorem "evaluate_Return_GENLIST_Var[local]"
  (fun () ->
    `!rets ret_vs env s'.
       LENGTH ret_vs = rets ==>
       bviSem_evaluate ([Return (GENLIST Var rets)],ret_vs ++
         env,s') =
       (Rerr (Rraise (Ret ret_vs)),s')`)
  CHEAT_TAC;;

(* HOL4 bvi_to_dataProofScript.sml:817: ML code, not ported *)

let bvi_to_dataProof_compile_correct = cake_theorem "compile_correct"
  (fun () ->
    `!xs env s1 res s2 t1 n corr tail live.
        evaluate (xs,env,s1) = (res,s2) /\ ~(
        res = Rerr (Rabort Rtype_error)) /\
        var_corr env corr (map data_to_bvi_v (dataSem_state_locals
          t1)) /\
        (~(LENGTH xs = 1) ==> ~tail) /\
        (!k. n <= k ==> (lookup k (dataSem_state_locals t1) =
          NONE)) /\
        state_rel s1 t1 /\
        EVERY (\n. ~(lookup n (dataSem_state_locals t1) = NONE))
          live /\
        ((\x. ?v. x = Rerr (Rraise (Exn v))) res ==>
          ~(dataSem_jump_exc t1 = NONE)) ==> (?t2 prog pres vs next_var
          ls.
            compile n corr tail live xs = (prog,vs,next_var) /\
            evaluate (prog,t1) = (pres,t2) /\
            state_rel s2 t2 /\
            (match pres with SOME r ->
                ((~(\x. ?vs. x = Rerr (Rraise (Ret vs))) res ==>
                  data_to_bvi_result r = res) /\
                 ((\x. ?vs. x = Rerr (Rraise (Ret vs))) res ==>
                    (?vs'. r = Rval vs' /\
                          res = Rerr (Rraise (Ret (MAP
                            data_to_bvi_v vs'))))) /\
                 (((\x. ?v. x = Rval v) res \/ (\x. ?vs. x = Rerr
                   (Rraise (Ret vs))) res) ==>
                    (stack t1 = stack t2) /\
                    (dataSem_state_handler t1 =
                      dataSem_state_handler t2)) /\
                 ((\x. ?v. x = Rval v) res ==> tail) /\
                 ((\x. ?v. x = Rerr (Rraise (Exn v))) res ==>
                    (dataSem_jump_exc (dataSem_state_handler_fupd
                      (K (dataSem_state_handler t1)) (stack_fupd (K
                      (stack t1)) t2)) =
                       SOME (dataSem_state_locals_size_fupd (K ls)
                         t2)))) | NONE -> ~tail /\ n <= next_var /\
                       EVERY (\v. v < next_var) vs /\
                       (!k. next_var <= k ==> (lookup k
                         (dataSem_state_locals t2) = NONE)) /\
                       var_corr env corr (map data_to_bvi_v
                         (dataSem_state_locals t2)) /\
                       (!k x. (lookup k (dataSem_state_locals t2) =
                         SOME x) ==> k < next_var) /\
                       (!k x. (lookup k (dataSem_state_locals t1) =
                         SOME x) /\
                              (~MEM k live ==> MEM k corr) ==>
                              (lookup k (dataSem_state_locals t2) =
                                SOME x)) /\
                       (stack t1 = stack t2) /\
                         (dataSem_state_handler t1 =
                         dataSem_state_handler t2) /\
                       (~(dataSem_jump_exc t1 = NONE) ==>
                         ~(dataSem_jump_exc t2 = NONE)) /\
                       (match res with Rval xs -> var_corr xs vs
                         (map data_to_bvi_v (dataSem_state_locals t2))
                         | _3 -> F)))`)
  CHEAT_TAC;;

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

(* HOL4 bvi_to_dataProofScript.sml:2899-2918: a theorem whose
   statement the port cannot state yet *)

let state_rel_dec_clock = cake_theorem "state_rel_dec_clock[local]"
  (fun () ->
    `state_rel s1 t1 ==> state_rel (dec_clock 1 s1) (dec_clock t1)`)
  CHEAT_TAC;;

let compile_part_evaluate = cake_theorem "compile_part_evaluate"
  (fun () ->
    `evaluate ([Call 0 (SOME start) [] NONE],[],s1) = (res,s2) /\ ~(
     res = Rerr (Rabort Rtype_error)) /\ state_rel s1 t1 /\
     (\t. t = LN) (dataSem_state_locals t1) /\ (!x. res = Rerr
       (Rraise x) ==> ~(dataSem_jump_exc t1 = NONE)) ==> (?r t2.
        evaluate ((Call NONE (SOME start) [] NONE),t1) = (SOME
          r,t2) /\
        state_rel s2 t2 /\ data_to_bvi_result r = res)`)
  CHEAT_TAC;;

let MAP_FST_compile_prog = cake_theorem "MAP_FST_compile_prog[simp]"
  (fun () ->
    `!prog. MAP FST' (compile_prog prog) = MAP FST' prog`)
  CHEAT_TAC;;

let compile_prog_evaluate = cake_theorem "compile_prog_evaluate"
  (fun () ->
    `evaluate ([Call 0 (SOME start) [] NONE],[],
       initial_state ffi0 (fromAList prog) co (\cfg prog. cc cfg
         (compile_prog prog)) k) = (r,s) /\ ~(
     r = Rerr (Rabort Rtype_error)) /\ (!x. ~(r = Rerr (Rraise x)))
       ==> (?r2 s2.
         evaluate (Call NONE (SOME start) [] NONE,
           initial_state ffi0 (fromAList (compile_prog prog)) ((I
             ## compile_prog) o co) cc T lims ss k) = (SOME r2,s2) /\
           state_rel s s2 /\ data_to_bvi_result r2 = r)`)
  CHEAT_TAC;;

let FST_compile_part = cake_theorem "FST_compile_part[simp]"
  (fun () ->
    `FST (compile_part a) = (FST a)`)
  CHEAT_TAC;;

(* observational semantics *)

let bvi_to_dataProof_compile_prog_semantics =
  cake_theorem "compile_prog_semantics"
  (fun () ->
    `~(
     semantics (ffi0:'ffi ffi_state)
               (fromAList prog) co
               (\cfg prog. cc cfg (compile_prog prog)) start =
                 Fail) ==> semantics ffi0
                 (fromAList (compile_prog prog))
                 ((I ## compile_prog) o co) cc lim ss start =
       semantics ffi0
                 (fromAList prog) co
                 (\cfg prog. cc cfg (compile_prog prog)) start`)
  CHEAT_TAC;;

let get_code_labels_iAssign =
  cake_theorem "get_code_labels_iAssign[simp]"
  (fun () ->
    `!a b c d e. get_code_labels (iAssign a b c d e) =
  assign_get_code_label b`)
  CHEAT_TAC;;

let bvi_to_dataProof_get_code_labels_compile =
  cake_theorem "get_code_labels_compile"
  (fun () ->
    `!a b c d e. get_code_labels (FST (compile a b c d e)) SUBSET
      BIGUNION (set_of_list (MAP get_code_labels e))`)
  CHEAT_TAC;;

let compile_prog_good_code_labels =
  cake_theorem "compile_prog_good_code_labels"
  (fun () ->
    `!p. good_code_labels p elabs ==> good_code_labels
  (bvi_to_data_compile_prog p) elabs`)
  CHEAT_TAC;;
