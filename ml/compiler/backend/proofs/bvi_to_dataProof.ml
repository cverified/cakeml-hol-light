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
needs "compiler/backend/bvi_to_data.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/proofs/data_liveProof.ml";;
needs "compiler/backend/proofs/data_simpProof.ml";;
needs "compiler/backend/proofs/data_spaceProof.ml";;
needs "compiler/backend/semantics/bviProps.ml";;
needs "compiler/backend/semantics/bviSem.ml";;
needs "compiler/backend/semantics/dataProps.ml";;
needs "compiler/backend/semantics/dataSem.ml";;
needs "lib/sptree.ml";;
needs "semantics/ast.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/semanticPrimitives.ml";;

(* the theories whose names the Ancestors blocks of the source
   bring, which are the ones that its statements read: the
   overloads of every other theory come out of the interface
   while this file loads *)
let _ = hol4_ancestors "bvi_to_dataProof"
  ["bviProps"; "bviSem"; "bvi_to_data"; "dataProps"; "dataSem";
   "data_liveProof"; "data_simpProof"; "data_spaceProof"];;

let _ = do_list hide_constant ["isException"; "isResult"; "parts"];;

(* value relation *)

let code_rel_def = new_definition
  `bvi_to_dataProof_code_rel (bvi_code:(num#bvi_exp) spt)
  (data_code:(num#dataLang_prog) spt) <=>
     sptree_wf bvi_code /\ sptree_wf data_code /\
     (domain bvi_code = domain data_code) /\
     (!n exp arg_count.
       (sptree_lookup n bvi_code = SOME (arg_count,exp)) ==>
       (sptree_lookup n data_code = SOME
         (arg_count,bvi_to_data_compile_exp arg_count exp)))`;;

(* Projection from `dataSem$v` into `bvlSem$v` that basically gets rid of
   timestamp information (note this make the function non-injective)
*)

(* the termination relation that HOL4 gives is
     MEASURE dataSem_v_size
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 bvi_to_dataProofScript.sml:36-48: the tactic that proves the
   termination *)
let data_to_bvi_v_def,data_to_bvi_v_ind = define_shaped_rec
  "nested"
  [`data_to_bvi_v (dataSem_Number i:dataSem_v) = bvlSem_Number i`;
   `data_to_bvi_v (dataSem_Word64 w:dataSem_v) = bvlSem_Word64 w`;
   `data_to_bvi_v (dataSem_CodePtr p:dataSem_v) = bvlSem_CodePtr p`;
   `data_to_bvi_v (dataSem_RefPtr b r:dataSem_v) = bvlSem_RefPtr b r`;
   `data_to_bvi_v (dataSem_Block _2 tag l:dataSem_v) = bvlSem_Block
  tag (MAP data_to_bvi_v l)`];;

(* Projection for Unit constant *)
(* [simp] *)
let data_to_bvi_v_Unit = prove
 (`data_to_bvi_v dataSem_Unit = dataSem_Unit`,
  CHEAT_TAC);;

(* Projection for Boolv constant *)
(* [simp] *)
let data_to_bvi_v_Boolv = prove
 (`!b. data_to_bvi_v (dataSem_Boolv b) = (dataSem_Boolv b)`,
  CHEAT_TAC);;

(* Projection for references, non-injective for value arrays *)
let data_to_bvi_ref_def = define_cases
  [`data_to_bvi_ref (bvlSem_ValueArray l) = bvlSem_ValueArray (MAP
  data_to_bvi_v l)`;
   `data_to_bvi_ref (bvlSem_ByteArray b bl) = (bvlSem_ByteArray b
  bl:'a bvlSem_ref)`;
   `data_to_bvi_ref (bvlSem_Thunk m v) = bvlSem_Thunk m
  (data_to_bvi_v v)`;
   `data_to_bvi_ref (bvlSem_MutBlock tg fin ls c rs) =
        bvlSem_MutBlock tg fin (MAP data_to_bvi_v ls)
          (data_to_bvi_v c) (MAP data_to_bvi_v rs)`];;

(* State relation *)
let bvi_to_dataProof_state_rel_def = new_definition
  `bvi_to_dataProof_state_rel (s:('c,'ffi)bviSem_state)
  (t:('c,'ffi)dataSem_state) <=>
     (bviSem_state_clock s = dataSem_state_clock t) /\
     bvi_to_dataProof_code_rel (bviSem_state_code s)
       (dataSem_state_code t) /\
     (dataSem_state_compile_oracle t = ((I ##
       bvi_to_data_compile_prog) o bviSem_state_compile_oracle s)) /\
     (bviSem_state_compile s = (\cfg prog. dataSem_state_compile t
       cfg (bvi_to_data_compile_prog prog))) /\
     (!n. FLOOKUP (bviSem_state_refs s) n = sptree_lookup n
       (sptree_map data_to_bvi_ref (dataSem_state_refs t))) /\
     (bviSem_state_ffi s = dataSem_state_ffi t) /\
     (bviSem_state_global s = dataSem_state_global t)`;;

(* semantics lemmas *)

(* HOL4 bvi_to_dataProofScript.sml:87-88: an overload that the source
   brings to the front: find_code, written out as bvlSem_find_code *)

(* [local] *)
let find_code_lemma = prove
 (`bvi_to_dataProof_state_rel r t2 /\
     bvlSem_find_code dest (MAP data_to_bvi_v a) (state_code r) =
       SOME (args,exp) ==> (?args' ss.
        args = MAP data_to_bvi_v args' /\
        dataSem_find_code dest a (state_code t2)
          (dataSem_state_stack_frame_sizes t2) =
          SOME (args',bvi_to_data_compile_exp (LENGTH args')
            exp,ss))`,
  CHEAT_TAC);;

let optimise_correct = prove
 (`!c s. ~(FST (dataSem_evaluate (c,s)) = SOME (Rerr (Rabort
  Rtype_error))) /\ ~(FST (dataSem_evaluate (c,s)) = NONE) ==>
         (?safe peak smx ls.
           dataSem_evaluate (bvi_to_data_optimise c,s) = (I ## (\x.
             dataSem_state_stack_max_fupd (K smx)
             (dataSem_state_peak_heap_length_fupd (K peak)
             (dataSem_state_safe_for_space_fupd (K safe)
             (dataSem_state_locals_size_fupd (K ls) x)))))
                              (dataSem_evaluate (c,s)))`,
  CHEAT_TAC);;

(* [local] *)
let compile_RANGE_lemma = prove
 (`!n env tail live xs.
       ALL (\v. v < (SND (SND (bvi_to_data_compile n env tail live
         xs))))
         (FST (SND (bvi_to_data_compile n env tail live xs)))`,
  CHEAT_TAC);;

(* [local] *)
let compile_RANGE = prove
 (`(bvi_to_data_compile n env tail live xs = (ys,vs,k)) ==> ALL (\v. v
  < k) vs`,
  CHEAT_TAC);;

(* HOL4 bvi_to_dataProofScript.sml:156: the overload isException,
   which the port expands *)
(* HOL4 bvi_to_dataProofScript.sml:157: the overload isReturn, which
   the port expands *)
(* HOL4 bvi_to_dataProofScript.sml:158: the overload isResult, which
   the port expands *)

(* HOL4 bvi_to_dataProofScript.sml:160: ML code, not ported *)

(* HOL4 bvi_to_dataProofScript.sml:162: ML code, not ported *)

(* [local] *)
let compile_part_thm = prove
 (`bvi_to_data_compile_part = (\(x,y). (x,(\(a,b).
  (a,bvi_to_data_compile_exp a b)) y))`,
  CHEAT_TAC);;

(* Projection for results, injective upto `dataSem$v` *)
let data_to_bvi_result_def = new_definition
  `data_to_bvi_result x1 =
      match x1 with
        Rval vs -> Rval (MAP data_to_bvi_v vs)
      | (Rerr (Rraise v)) -> Rerr (Rraise (Exn (data_to_bvi_v v)))
      | (Rerr (Rabort err)) -> Rerr (Rabort err)`;;

(* All the `dataSem$v` values project to `bvlSem$Boolv b` satisfy `isBool` *)
let isBool_eq = prove
 (`!z b. isBool b z <=> (dataSem_Boolv b = data_to_bvi_v z)`,
  CHEAT_TAC);;

(* Lifting `data_to_bvi_v` projection to work over `bvlSem$v list` *)
(* [simp] *)
let v_to_list_eq = prove
 (`!x. dataSem_v_to_list (data_to_bvi_v x) = OPTION_MAP (MAP
  data_to_bvi_v) (dataSem_v_to_list x)`,
  CHEAT_TAC);;

(* Special bijection for `data_to_bvi_v` with `dataSem$Number` + `MAP` *)
let data_to_bvi_number_eq = prove
 (`!ns.
     MAP data_to_bvi_v (MAP (dataSem_Number o (&) o w2n) ns) =
     MAP (dataSem_Number o (&) o w2n) ns`,
  CHEAT_TAC);;

(* Special bijection for `data_to_bvi_v` with `dataSem$Word64` + `MAP` *)
let data_to_bvi_word_eq = prove
 (`!ns.
     MAP data_to_bvi_v (MAP dataSem_Word64 ns) =
     MAP dataSem_Word64 ns`,
  CHEAT_TAC);;

(* Bijection of `data_to_bvi_v (Number n)` over multiple maps *)
let MAP_data_to_bvi_Number = prove
 (`!xs ws. MAP data_to_bvi_v (MAP dataSem_Number xs) = MAP
  data_to_bvi_v ws <=> (MAP dataSem_Number xs) = ws`,
  CHEAT_TAC);;

(* Bijection of `data_to_bvi_v (Word64 n)` over multiple maps *)
let MAP_data_to_bvi_Word64 = prove
 (`!xs ws. MAP data_to_bvi_v (MAP dataSem_Word64 xs) = MAP
  data_to_bvi_v ws <=> (MAP dataSem_Word64 xs) = ws`,
  CHEAT_TAC);;

(* `data_to_bvi_v_def` is idempotent over `v_to_bytes` *)
(* [simp] *)
let v_to_bytes_eq = prove
 (`!x. dataSem_v_to_bytes (data_to_bvi_v x) = dataSem_v_to_bytes x`,
  CHEAT_TAC);;

(* `data_to_bvi_v_def` is idempotent over `v_to_words` *)
(* [simp] *)
let v_to_words_eq = prove
 (`!x. dataSem_v_to_words (data_to_bvi_v x) = dataSem_v_to_words x`,
  CHEAT_TAC);;

(* isBool simplifications *)
let isBool_simps = prove
 (`(!b z. isBool T (z:dataSem_v) ==> ~(isBool F z)) /\
   (!b z. isBool F (z:dataSem_v) ==> ~(isBool T z))`,
  CHEAT_TAC);;

(* HOL4 bvi_to_dataProofScript.sml:272-273: ML code, not ported *)

(* A variable correspondece (`var_corr`) over projecte values in `t2`
   implies all values in `a` are projections of values in `t2`
 *)
let get_vars_lift_thm = prove
 (`!vs a t2.
     var_corr a vs (sptree_map data_to_bvi_v t2) ==> (?z.
       dataSem_get_vars vs t2 = SOME z /\ a = (MAP data_to_bvi_v z))`,
  CHEAT_TAC);;

let var_corr_inter = prove
 (`!t p vs z. var_corr z vs (inter p t) ==> var_corr z vs p`,
  CHEAT_TAC);;

(* [simp] *)
let get_vars_mk_wf = prove
 (`!vs t z. dataSem_get_vars vs (mk_wf t) = SOME z <=>
  dataSem_get_vars vs t = SOME z`,
  CHEAT_TAC);;

let get_vars_inter = prove
 (`!vs p t z. dataSem_get_vars vs (inter p t) = SOME z ==>
  dataSem_get_vars vs p = SOME z`,
  CHEAT_TAC);;

(* `data_to_bvi_v` preserves `var_corr` *)
let var_corr_map = prove
 (`!p f vs z. var_corr z vs p ==> var_corr (MAP f z) vs (sptree_map f
  p)`,
  CHEAT_TAC);;

(* Construction of the pre-image of `data_to_bvi_v`,
   wich in all cases except `Block` is bijective
 *)
(* [simp] *)
let data_to_bvi_v_eq = prove
 (`(!v n i. data_to_bvi_v v = dataSem_Number i <=> v = dataSem_Number i)
  /\
   (!v n w. data_to_bvi_v v = dataSem_Word64 w <=> v = dataSem_Word64
     w) /\
   (!v n p. data_to_bvi_v v = dataSem_CodePtr p <=> v =
     dataSem_CodePtr p) /\
   (!v n r b. data_to_bvi_v v = dataSem_RefPtr b r <=> v =
     dataSem_RefPtr b r) /\
   (!v n l.
     data_to_bvi_v v = dataSem_Block n l <=> (?ts l'. v =
       dataSem_Block ts n l' /\ l = MAP data_to_bvi_v l'))`,
  CHEAT_TAC);;
(*flip LHS equalities*)
(* HOL4 bvi_to_dataProofScript.sml:351-353: a theorem that HOL4
   states as the value of an ML expression: data_to_bvi_v_eq' *)

(* HOL4 bvi_to_dataProofScript.sml:355-361: ML code, not ported *)

(* [simp] *)
let data_to_bvi_ref_eq = prove
 (`(!v fl ds. data_to_bvi_ref v = bvlSem_ByteArray fl ds <=> v =
  bvlSem_ByteArray fl ds) /\
   (!v l.
     data_to_bvi_ref v = bvlSem_ValueArray l <=> (?l'. v =
       bvlSem_ValueArray l' /\ l = MAP data_to_bvi_v l')) /\
   (!v m w.
     data_to_bvi_ref v = bvlSem_Thunk m w <=> (?w'. v = bvlSem_Thunk
       m w' /\ w = data_to_bvi_v w')) /\
   (!v tg fin ls c rs.
     data_to_bvi_ref v = bvlSem_MutBlock tg fin ls c rs <=> (?ls' c'
       rs'. v = bvlSem_MutBlock tg fin ls' c' rs' /\
                      ls = MAP data_to_bvi_v ls' /\ c = data_to_bvi_v
                        c' /\
                      rs = MAP data_to_bvi_v rs'))`,
  CHEAT_TAC);;

(* HOL4 bvi_to_dataProofScript.sml:377-379: a theorem that HOL4
   states as the value of an ML expression: data_to_bvi_ref_eq' *)

(* HOL4 bvi_to_dataProofScript.sml:381-385: ML code, not ported *)

(* Construction of the pre-image of `data_to_bvi_result` *)
(* [simp] *)
let data_to_bvi_result_eq = prove
 (`!x v.
    data_to_bvi_result x = Rerr (Rraise v) <=> (?z. x = Rerr
      (Rraise z) /\ Exn (data_to_bvi_v z) = v)`,
  CHEAT_TAC);;

let data_to_bvi_v_list_to_v_Nil = prove
 (`!z ts.
   data_to_bvi_v (dataSem_list_to_v ts (dataSem_Block 0 nil_tag [])
     z) =
   dataSem_list_to_v (MAP data_to_bvi_v z)`,
  CHEAT_TAC);;

(* `data_to_bvi_v` preservers `do_eq` *)
let data_to_bvi_do_eq = prove
 (`(!t v1 v2 r.
     (!n. FLOOKUP r n = sptree_lookup n (sptree_map data_to_bvi_ref
       t)) ==> dataSem_do_eq r (data_to_bvi_v v1) (data_to_bvi_v v2) =
       dataSem_do_eq t v1 v2) /\
   (!t l1 l2 r.
     (!n. FLOOKUP r n = sptree_lookup n (sptree_map data_to_bvi_ref
       t)) ==> dataSem_do_eq_list r (MAP data_to_bvi_v l1) (MAP
       data_to_bvi_v l2) =
       dataSem_do_eq_list t l1 l2)`,
  CHEAT_TAC);;

let data_to_bvi_v_list_to_v_APPEND = prove
 (`!l vl v ts.
    dataSem_v_to_list v = SOME vl ==> data_to_bvi_v
      (dataSem_list_to_v ts v l) =
   data_to_bvi_v (dataSem_list_to_v ts (dataSem_Block 0 nil_tag [])
     (APPEND l vl))`,
  CHEAT_TAC);;

(* HOL4 bvi_to_dataProofScript.sml:445-452: code that the source has
   in a comment *)

(* [local] *)
let refs_rel_LEAST_eq = prove
 (`!s1 s2.
    (!n. FLOOKUP s1 n = sptree_lookup n (sptree_map data_to_bvi_ref
      s2)) ==> (minimal ptr. ~(ptr IN FDOM s1)) = (minimal ptr. ~(ptr
      IN domain s2))`,
  CHEAT_TAC);;

let do_build_thm = prove
 (`!parts' m1 m2 k ts r t q rs.
     dataSem_do_build m1 k parts' r = (q,rs) /\
     (!n. FLOOKUP r n = OPTION_MAP data_to_bvi_ref (sptree_lookup n
       t)) /\
     (!n. m1 n = data_to_bvi_v (m2 n)) ==>
     (?pres s1 ts1.
       dataSem_do_build m2 k parts' t ts = (pres,s1,ts1) /\
       q = data_to_bvi_v pres /\
       (!n. FLOOKUP rs n = OPTION_MAP data_to_bvi_ref
         (sptree_lookup n s1)))`,
  CHEAT_TAC);;

(* [local] *)
let data_to_bvi_v_Boolv_IMP = prove
 (`data_to_bvi_v x0 = dataSem_Boolv b ==> dest_Boolv x0 = SOME b`,
  CHEAT_TAC);;

(* bviSem$finalise_cons is simulated by dataSem$finalise_cons: the extra
   time stamps taken by the dataLang version are invisible to the projection *)
let data_to_bvi_finalise_cons = prove
 (`!v refs ts brefs bv brefs'.
     (!n. FLOOKUP brefs n = OPTION_MAP data_to_bvi_ref (sptree_lookup
       n refs)) /\
     bviSem_finalise_cons (data_to_bvi_v v) brefs = SOME (bv,brefs')
       ==> (?pv refs' ts'.
         dataSem_finalise_cons v refs ts = SOME (pv,refs',ts') /\
         bv = data_to_bvi_v pv /\
         (!n. FLOOKUP brefs' n = OPTION_MAP data_to_bvi_ref
           (sptree_lookup n refs')))`,
  CHEAT_TAC);;

(* HOL4 bvi_to_dataProofScript.sml:527-530: a proof *)

let data_to_bvi_do_app = prove
 (`!op t r z res s1.
     ~(op = wordLang_Install) /\ ~(op = closLang_IntOp
       closLang_Greater) /\ ~(op = closLang_IntOp closLang_GreaterEq) /\
       ~(op = closLang_WordOp (WordTest ast_W8 (ast_Compare ast_Gt))) /\
       ~(op = closLang_WordOp (WordTest ast_W8 (ast_Compare ast_Geq)))
       /\
     (!b. ~(op = closLang_MemOp (closLang_CopyByte b))) /\ ~(op =
       closLang_ThunkOp ForceThunk) /\
     bvi_to_dataProof_state_rel r t /\
     dataSem_do_app op (MAP data_to_bvi_v z) r = Rval (res,s1) ==>
       (?s2 pres.
        dataSem_do_app_aux op z t = Rval (pres,s2) /\
        res = data_to_bvi_v pres /\
        bvi_to_dataProof_state_rel s1 s2)`,
  CHEAT_TAC);;

let state_rel_peak_safe = prove
 (`!s s' safe peak ls smx.
     bvi_to_dataProof_state_rel s s' =
       bvi_to_dataProof_state_rel s (dataSem_state_stack_max_fupd
         (K smx) (dataSem_state_peak_heap_length_fupd (K peak)
         (dataSem_state_safe_for_space_fupd (K safe)
         (dataSem_state_locals_size_fupd (K ls) s'))))`,
  CHEAT_TAC);;

let jump_exc_peak_safe = prove
 (`!s t safe peak ls smx.
     dataSem_jump_exc s = SOME t ==> dataSem_jump_exc
       (dataSem_state_stack_max_fupd (K smx)
       (dataSem_state_locals_size_fupd (K ls)
       (dataSem_state_peak_heap_length_fupd (K peak)
       (dataSem_state_safe_for_space_fupd (K safe) s)))) =
         SOME (dataSem_state_stack_max_fupd (K smx)
           (dataSem_state_peak_heap_length_fupd (K peak)
           (dataSem_state_safe_for_space_fupd (K safe) t)))`,
  CHEAT_TAC);;

let jump_exc_sfs_lss_peak_safe = prove
 (`!s t safe peak ls sfs smx.
     dataSem_jump_exc s = SOME t ==> dataSem_jump_exc
       (dataSem_state_stack_max_fupd (K smx)
       (dataSem_state_stack_frame_sizes_fupd (K sfs)
       (dataSem_state_locals_size_fupd (K ls)
       (dataSem_state_peak_heap_length_fupd (K peak)
       (dataSem_state_safe_for_space_fupd (K safe) s))))) =
         SOME (dataSem_state_stack_max_fupd (K smx)
           (dataSem_state_stack_frame_sizes_fupd (K sfs)
           (dataSem_state_peak_heap_length_fupd (K peak)
           (dataSem_state_safe_for_space_fupd (K safe) t))))`,
  CHEAT_TAC);;

let jump_exc_lss = prove
 (`!s t ls.
     dataSem_jump_exc s = SOME t ==> dataSem_jump_exc
       (dataSem_state_locals_size_fupd (K ls) s) = SOME t`,
  CHEAT_TAC);;

let state_rel_dest_thunk = prove
 (`bvi_to_dataProof_state_rel s t /\
   dataSem_dest_thunk (data_to_bvi_v z) (state_refs s) =
     dataSem_IsThunk ev v ==>
     (?v'. dataSem_dest_thunk z (state_refs t) = dataSem_IsThunk ev
       v' /\
          data_to_bvi_v v' = v)`,
  CHEAT_TAC);;

(* [local] *)
let domain_list_insert2 = prove
 (`domain (list_insert xs t) = set_of_list xs UNION domain t`,
  CHEAT_TAC);;

(* [local] *)
let domain_list_to_num_set2 = prove
 (`domain (list_to_num_set xs) = set_of_list xs`,
  CHEAT_TAC);;

(* [simp,local] *)
let list_insert_list_to_num_set = prove
 (`list_insert xs (list_to_num_set (APPEND (APPEND xs ys) zs)) =
   list_to_num_set (APPEND (APPEND xs ys) zs)`,
  CHEAT_TAC);;

(* [local] *)
let state_rel_do_app_FFI_err = prove
 (`!i z r t x.
     bvi_to_dataProof_state_rel r t /\
     dataSem_do_app (wordLang_FFI i) (MAP data_to_bvi_v z) r = Rerr
       (Rabort (Rffi_error x)) ==>
     dataSem_do_app (wordLang_FFI i) z t = Rerr (Rabort (Rffi_error
       x))`,
  CHEAT_TAC);;

(* [local] *)
let evaluate_Return_GENLIST_Var = prove
 (`!rets ret_vs env s'.
     LENGTH ret_vs = rets ==>
     bviSem_evaluate ([dataLang_Return (list_of_seq bvi_Var
       rets)],APPEND ret_vs env,s') =
     (Rerr (Rraise (Ret ret_vs)),s')`,
  CHEAT_TAC);;

(* HOL4 bvi_to_dataProofScript.sml:817: ML code, not ported *)

(* compile_correct *)
let bvi_to_dataProof_compile_correct = prove
 (`!xs env s1 res s2 t1 n corr tail live.
      dataSem_evaluate (xs,env,s1) = (res,s2) /\ ~(res = Rerr (Rabort
        Rtype_error)) /\
      var_corr env corr (sptree_map data_to_bvi_v
        (dataSem_state_locals t1)) /\
      (~(LENGTH xs = 1) ==> ~tail) /\
      (!k. n <= k ==> (sptree_lookup k (dataSem_state_locals t1) =
        NONE)) /\
      bvi_to_dataProof_state_rel s1 t1 /\
      ALL (\n. ~(sptree_lookup n (dataSem_state_locals t1) = NONE))
        live /\
      ((\x. ?v. x = Rerr (Rraise (Exn v))) res ==> ~(dataSem_jump_exc
        t1 = NONE)) ==> (?t2 prog pres vs next_var ls.
          bvi_to_data_compile n corr tail live xs =
            (prog,vs,next_var) /\
          dataSem_evaluate (prog,t1) = (pres,t2) /\
          bvi_to_dataProof_state_rel s2 t2 /\
          (match pres with SOME r ->
              ((~((\x. ?vs. x = Rerr (Rraise (Ret vs))) res) ==>
                data_to_bvi_result r = res) /\
               ((\x. ?vs. x = Rerr (Rraise (Ret vs))) res ==>
                  (?vs'. r = Rval vs' /\
                        res = Rerr (Rraise (Ret (MAP data_to_bvi_v
                          vs'))))) /\
               (((\x. ?v. x = Rval v) res \/ (\x. ?vs. x = Rerr
                 (Rraise (Ret vs))) res) ==>
                  (stack t1 = stack t2) /\
                  (dataSem_state_handler t1 = dataSem_state_handler
                    t2)) /\
               ((\x. ?v. x = Rval v) res ==> tail) /\
               ((\x. ?v. x = Rerr (Rraise (Exn v))) res ==>
                  (dataSem_jump_exc (dataSem_state_handler_fupd (K
                    (dataSem_state_handler t1)) (stack_fupd (K (stack
                    t1)) t2)) =
                     SOME (dataSem_state_locals_size_fupd (K ls)
                       t2)))) | NONE -> ~tail /\ n <= next_var /\
                     ALL (\v. v < next_var) vs /\
                     (!k. next_var <= k ==> (sptree_lookup k
                       (dataSem_state_locals t2) = NONE)) /\
                     var_corr env corr (sptree_map data_to_bvi_v
                       (dataSem_state_locals t2)) /\
                     (!k x. (sptree_lookup k (dataSem_state_locals
                       t2) = SOME x) ==> k < next_var) /\
                     (!k x. (sptree_lookup k (dataSem_state_locals
                       t1) = SOME x) /\
                            (~(MEM k live) ==> MEM k corr) ==>
                            (sptree_lookup k (dataSem_state_locals
                              t2) = SOME x)) /\
                     (stack t1 = stack t2) /\ (dataSem_state_handler
                       t1 = dataSem_state_handler t2) /\
                     (~(dataSem_jump_exc t1 = NONE) ==>
                       ~(dataSem_jump_exc t2 = NONE)) /\
                     (match res with Rval xs -> var_corr xs vs
                       (sptree_map data_to_bvi_v (dataSem_state_locals
                       t2)) | _3 -> F)))`,
  CHEAT_TAC);;

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
   statement the port cannot state yet: compile_exp_correct *)

(* [local] *)
let state_rel_dec_clock = prove
 (`bvi_to_dataProof_state_rel s1 t1 ==> bvi_to_dataProof_state_rel
  (dataSem_dec_clock 1 s1) (dataSem_dec_clock t1)`,
  CHEAT_TAC);;

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let compile_part_evaluate = prove
 (cake_as_vars (fun () ->
    `dataSem_evaluate ([dataLang_Call 0 (SOME start) [] NONE],[],s1) =
  (res,s2) /\ ~(res = Rerr (Rabort Rtype_error)) /\
  bvi_to_dataProof_state_rel s1 t1 /\
     (\t. t = LN) (dataSem_state_locals t1) /\ (!x. res = Rerr
       (Rraise x) ==> ~(dataSem_jump_exc t1 = NONE)) ==> (?r t2.
        dataSem_evaluate ((dataLang_Call NONE (SOME start) []
          NONE),t1) = (SOME r,t2) /\
        bvi_to_dataProof_state_rel s2 t2 /\ data_to_bvi_result r
          = res)`),
  CHEAT_TAC);;

(* [simp] *)
let MAP_FST_compile_prog = prove
 (`!prog. MAP FST (bvi_to_data_compile_prog prog) = MAP FST prog`,
  CHEAT_TAC);;

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let compile_prog_evaluate = prove
 (cake_as_vars (fun () ->
    `dataSem_evaluate ([dataLang_Call 0 (SOME start) [] NONE],[],
       dataSem_initial_state ffi0 (fromAList prog) co (\cfg prog.
         cc cfg (bvi_to_data_compile_prog prog)) k) = (r,s) /\ ~(r =
         Rerr (Rabort Rtype_error)) /\ (!x. ~(r = Rerr (Rraise x))) ==>
         (?r2 s2.
         dataSem_evaluate (dataLang_Call NONE (SOME start) [] NONE,
           dataSem_initial_state ffi0 (fromAList
             (bvi_to_data_compile_prog prog)) ((I ##
             bvi_to_data_compile_prog) o co) cc T lims ss k) = (SOME
             r2,s2) /\
           bvi_to_dataProof_state_rel s s2 /\ data_to_bvi_result
             r2 = r)`),
  CHEAT_TAC);;

(* [simp] *)
let FST_compile_part = prove
 (`FST (bvi_to_data_compile_part a) = (FST a)`,
  CHEAT_TAC);;

(* observational semantics *)

(* compile_prog_semantics *)
(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let bvi_to_dataProof_compile_prog_semantics = prove
 (cake_as_vars (fun () ->
    `~(dataSem_semantics (ffi0:'ffi ffi_state)
               (fromAList prog) co
               (\cfg prog. cc cfg (bvi_to_data_compile_prog prog))
                 start = ffi_Fail) ==> dataSem_semantics ffi0
                 (fromAList (bvi_to_data_compile_prog prog))
                 ((I ## bvi_to_data_compile_prog) o co) cc lim ss
                   start =
       dataSem_semantics ffi0
                 (fromAList prog) co
                 (\cfg prog. cc cfg (bvi_to_data_compile_prog
                   prog)) start`),
  CHEAT_TAC);;

(* [simp] *)
let get_code_labels_iAssign = prove
 (`!a b c d e. dataProps_get_code_labels (iAssign a b c d e) =
  assign_get_code_label b`,
  CHEAT_TAC);;

(* get_code_labels_compile *)
let bvi_to_dataProof_get_code_labels_compile = prove
 (`!a b c d e. dataProps_get_code_labels (FST (bvi_to_data_compile a b c
  d e)) SUBSET
    UNIONS (set_of_list (MAP dataProps_get_code_labels e))`,
  CHEAT_TAC);;

let compile_prog_good_code_labels = prove
 (`!p. dataProps_good_code_labels p elabs ==>
  dataProps_good_code_labels (bvi_to_data_compile_prog p) elabs`,
  CHEAT_TAC);;

(* and the names that this file reads as variables are constants again *)
let _ = do_list unhide_constant
  ["isException";
   "isResult";
   "parts"];;

(* and the overloads that this file cannot see are back in the
   interface *)
let _ = unhide_overloads ();;
