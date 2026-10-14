(* ======================================================== *)
(*  bviSem: ported from HOL4's
    compiler/backend/semantics/bviSemScript.sml  *)
(* ======================================================== *)

(*
  The formal semantics of BVI
*)

needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/bvi.ml";;
needs "compiler/backend/semantics/bvlSem.ml";;
(* HOL4 ancestors outside the port: backendProps *)

(* HOL4 overload (expanded in the port):
     num_stubs = bvl_num_stubs *)

let exn_or_ret_INDUCT,exn_or_ret_RECURSION = define_datatype
  "exn_or_ret = Exn (bvlSem_v) | Ret (bvlSem_v list)";;

new_type_abbrev("bvi_result",`: (bvlSem_v
   list,exn_or_ret)semanticPrimitives_result`);;

let bviSem_state_FIELDS = define_record "bviSem_state"
  ["refs","(num,bvlSem_v bvlSem_ref)fmap";
   "clock","num";
   "global","num option";
   "compile","'c->(num#num#bvi_exp) list->(word8 list#word64 list#'c) \
   option";
   "compile_oracle","num->'c#(num#num#bvi_exp) list";
   "code","(num#bvi_exp) spt";
   "ffi","'ffi ffi_state"];;

let dec_clock_def = cake_define
  `bviSem_dec_clock x s = ?_clock_fupd (K (?_clock s - x)) s`;;

let bvi_to_bvl_def = cake_define
  `(bvi_to_bvl:('c,'ffi)bviSem_state->('c,'ffi)bvlSem_state) s =
     mk_? (?_refs s) (?_clock s) (sptree_map (K ARB) (?_code s))
       (?_ffi s)`;;

let bvl_to_bvi_def = cake_define
  `(bvl_to_bvi:('c,'ffi)bvlSem_state->('c,'ffi)bviSem_state->('c
  ,'ffi)bviSem_state) s t = ?_ffi_fupd (K (?_ffi s)) (?_clock_fupd (K
  (?_clock s)) (?_refs_fupd (K (?_refs s))
     t))`;;

(* TERMINATION: wf_rel_tac ‘measure $ CARD o FDOM o SND’
  >> simp [finite_mapTheory.FDOM_DOMSUB, FLOOKUP_DEF]
  >> rw []
  >> Cases_on ‘CARD (FDOM refs)’
  >> rw []
  >- fs[finite_setTheory.fCARD_EQ0]
  >> simp [] *)
let finalise_cons_def = cake_define
  `bviSem_finalise_cons v refs =
        match v with
          (bvlSem_RefPtr b ptr) ->
       match FLOOKUP refs ptr with SOME (bvlSem_MutBlock tag
         finalised l c r) ->
           (if ~finalised then
             (match bviSem_finalise_cons c (refs \\ ptr) with SOME
               (c',refs') -> SOME (bvlSem_Block tag (l ++ [c'] ++
               r),refs' |+ (ptr,bvlSem_MutBlock tag T l c r)) | NONE ->
               NONE) else NONE) | SOME res -> SOME (bvlSem_RefPtr b
               ptr,refs) | NONE -> NONE
        | bvlSem_v -> SOME (bvlSem_v,refs)`;;

(* HOL4 ML code, not ported:
val s = ``(s:('c,'ffi) bviSem$state)``;
*)

let do_app_aux_def = cake_define
  `^
     (do_app_aux flatLang_op (vs:bvlSem_v list)) s =
       (match (flatLang_op,vs) with (closLang_IntOp (closLang_Const
         i),xs) ->
         (if small_enough_int i /\ NULL xs then
           SOME (SOME (bvlSem_Number i,s)) else NONE) |
             (closLang_Label l,xs) -> (match xs with [] -> (if l IN
             domain (?_code s) then
                              SOME (SOME (bvlSem_CodePtr l,s)) else
                                NONE) | _1 -> NONE) | (closLang_GlobOp
                                GlobalsPtr,xs) ->
           (match xs with [] -> (match bviSem_state_global s with
             SOME p -> SOME (SOME (bvlSem_RefPtr T p,s)) | NONE -> NONE)
             | _2 -> NONE) | (closLang_GlobOp SetGlobalsPtr,xs) ->
           (match xs with [bvlSem_RefPtr T p] -> SOME (SOME
             (bvlSem_Unit,bviSem_state_global_fupd (K (SOME p)) s)) | _3
             -> NONE) | (closLang_GlobOp (Global n),xs) ->
           (match xs with [] -> (match bviSem_state_global s with
             SOME ptr ->
                          (match FLOOKUP (?_refs s) ptr with SOME
                            (bvlSem_ValueArray xs) ->
                              (if n < LENGTH xs then SOME (SOME (EL n
                                xs,s)) else NONE) | _4 -> NONE) | NONE
                                -> NONE) | _5 -> NONE) |
                                (closLang_GlobOp (SetGlobal n),xs) ->
           (match xs with [x] -> (match bviSem_state_global s with
             SOME ptr ->
                          (match FLOOKUP (?_refs s) ptr with SOME
                            (bvlSem_ValueArray xs) ->
                              (if n < LENGTH xs then SOME (SOME
                                (bvlSem_Unit,?_refs_fupd (K (?_refs s |+
                              (ptr,bvlSem_ValueArray (LUPDATE x n
                                xs)))) s)) else NONE) | _6 -> NONE) |
                                NONE -> NONE) | _7 -> NONE) |
                                (closLang_BlockOp (closLang_FromList
                                n),xs) ->
           (match xs with [len; lv] ->
               (match bvlSem_v_to_list lv with SOME vs -> (if len =
                 bvlSem_Number (&(LENGTH vs)) then SOME (SOME
                 (bvlSem_Block n vs,s)) else NONE) | _8 -> NONE) | _9 ->
                 NONE) | (closLang_MemOp (closLang_RefByte f'),xs) ->
           (match xs with [bvlSem_Number i; bvlSem_Number b] ->
               (if 0 <= i /\ (?(w:word8). b = &(w2n w)) then
                 let ptr = (minimal (\ptr. ~(ptr IN FDOM (?_refs
                   s)))) in
                   SOME (SOME (bvlSem_RefPtr T ptr,?_refs_fupd (K
                     (?_refs s |+
                     (ptr,bvlSem_ByteArray f' (REPLICATE (num_of_int
                       i) (i2w b))))) s)) else NONE) | _10 -> NONE) |
                       (closLang_MemOp (closLang_MutCons tag i),xs) ->
           (let ptr = (minimal (\ptr. ~(ptr IN FDOM (?_refs s)))) in
              if i >= LENGTH xs then NONE else
                let l = TAKE i xs in
                let c = EL i xs in
                let r = DROP (i + 1) xs in
                let b = bvlSem_MutBlock tag F l c r in
                  SOME (SOME (bvlSem_RefPtr F ptr,(?_refs_fupd (K
                    (?_refs s |+ (ptr,b))) s)))) | (closLang_MemOp
                    closLang_UpdateCons,[bvlSem_RefPtr _11 ptr;
                    bvlSem_Number i; x]) ->
           (match FLOOKUP (?_refs s) ptr with SOME (bvlSem_MutBlock
             tag finalised l c r) ->
                (if ~(i = &LENGTH l) \/ finalised then NONE else
                  SOME (SOME (bvlSem_Unit,?_refs_fupd (K (?_refs s |+
                    (ptr,bvlSem_MutBlock tag F l x r))) s))) | _12 ->
                    NONE) | (closLang_MemOp closLang_FinaliseCons,[x])
                    ->
           (match bviSem_finalise_cons x (?_refs s) with SOME
             (bvlSem_v,refs') -> SOME (SOME (bvlSem_v,?_refs_fupd (K
             refs') s)) | NONE -> NONE) | (closLang_GlobOp
             AllocGlobal,_13) -> NONE | (closLang_MemOp
             closLang_FromListByte,_14) -> NONE | (closLang_MemOp
             closLang_ToListByte,_15) -> NONE | (closLang_MemOp
             closLang_ConcatByteVec,_16) -> NONE | (closLang_MemOp
             (closLang_CopyByte T),_17) -> NONE | _18 -> SOME NONE)`;;

let do_install_def = cake_define
  `^
     (do_install vs) s =
         (match vs with [v1; v2; vl1; vl2] ->
              (match (bvlSem_v_to_bytes v1,bvlSem_v_to_words v2) with
                (SOME bytes,SOME data) ->
                  (if ~(vl1 = bvlSem_Number (&LENGTH bytes)) \/ ~(
                     vl2 = bvlSem_Number (&LENGTH data)) then Rerr
                       (Rabort Rtype_error) else
                  let (cfg,progs) = ?_compile_oracle s 0 in
                  let new_oracle = shift_seq 1 (?_compile_oracle s)
                    in
                    if DISJOINT (domain (?_code s)) (set_of_list (MAP
                      FST progs)) /\ ALL_DISTINCT (MAP FST progs) then
                    (match (?_compile s cfg progs,progs) with (SOME
                      (bytes',data',cfg'),(k,prog) :: _19) ->
                         (if bytes = bytes' /\ data = data' /\ FST
                           (new_oracle 0) = cfg' then
                           let s' = ?_compile_oracle_fupd (K
                             new_oracle) (?_code_fupd (K (sptree_union
                             (?_code s) (fromAList progs)))
                             s) in
                             Rval (bvlSem_CodePtr k,s') else Rerr
                               (Rabort Rtype_error)) | _20 -> Rerr
                               (Rabort Rtype_error)) else Rerr
                               (Rabort Rtype_error)) | _21 -> Rerr
                               (Rabort Rtype_error)) | _22 -> Rerr
                               (Rabort Rtype_error))`;;

let do_app_def = cake_define
  `^
     (semanticPrimitives_do_app flatLang_op vs) s =
       (if flatLang_op = closLang_Install then do_install vs s else
       match do_app_aux flatLang_op vs s with NONE -> Rerr (Rabort
         Rtype_error) | SOME (SOME (bvlSem_v,t)) -> Rval (bvlSem_v,t)
         | SOME NONE -> (match semanticPrimitives_do_app flatLang_op
         vs (bvi_to_bvl s) with Rval (bvlSem_v,t) -> Rval
         (bvlSem_v,bvl_to_bvi t s) | Rerr (Rabort a) -> Rerr (Rabort
         a) | Rerr (Rraise bvlSem_v) -> Rerr (Rraise (Exn
         bvlSem_v))))`;;

let bviSem_dest_thunk_ret_INDUCT,bviSem_dest_thunk_ret_RECURSION =
  define_datatype
  "bviSem_dest_thunk_ret = bviSem_BadRef | bviSem_NotThunk | \
   bviSem_IsThunk (thunk_mode) (bvlSem_v)";;

let dest_thunk_def = cake_define
  `bviSem_dest_thunk vs refs =
      match vs with
        (bvlSem_RefPtr b ptr) ->
     (match FLOOKUP refs ptr with NONE -> bviSem_BadRef | SOME
       (bvlSem_Thunk Evaluated bvlSem_v) ->
          (if b then bviSem_BadRef else bviSem_IsThunk Evaluated
            bvlSem_v) | SOME (bvlSem_Thunk NotEvaluated bvlSem_v) ->
          (if b then bviSem_BadRef else bviSem_IsThunk NotEvaluated
            bvlSem_v) | SOME _23 -> bviSem_NotThunk)
      | vs -> bviSem_NotThunk`;;


(* The evaluation is defined as a clocked functional version of
   a conventional big-step operational semantics. *)

let fix_clock_def = cake_define
  `bviSem_fix_clock s (res,s1) = (res,?_clock_fupd (K (MIN (?_clock
  s) (?_clock s1))) s1)`;;

(* The semantics of expression evaluation is defined next. For
   convenience of subsequent proofs, the evaluation function is
   defined to evaluate a list of bvi_exp expressions. *)

(* HOL4 termination: >> rpt strip_tac >> simp[dec_clock_def] >>
   imp_res_tac fix_clock_IMP >> imp_res_tac LESS_EQ_dec_clock >> rw[] *)
let evaluate_def = cake_define_wf
  `(inv_image (MEASURE I LEX MEASURE (list_size exp_size))
                             (\(xs,env,s). (?_clock s,xs)))`
  `(bviSem_evaluate ([],env,s) = ((Rval []:(bvlSem_v
  list,exn_or_ret)semanticPrimitives_result),s)) /\
   (bviSem_evaluate (x :: y :: xs,env,s) =
      (match bviSem_fix_clock s (bviSem_evaluate ([x],env,s)) with
        (Rval v1,s1) ->
          (match bviSem_evaluate (y :: xs,env,s1) with (Rval vs,s2)
            -> (Rval (HD v1 :: vs),s2) | res -> res) | res -> res)) /\
   (bviSem_evaluate ([db_vars_Var n],env,s) =
      (if n < LENGTH env then (Rval [EL n env],s) else (Rerr (Rabort
        Rtype_error),s))) /\
   (bviSem_evaluate ([flatLang_If x1 x2 x3],env,s) =
      (match bviSem_fix_clock s (bviSem_evaluate ([x1],env,s)) with
        (Rval vs,s1) ->
           (if bvlSem_Boolv T = HD vs then bviSem_evaluate
             ([x2],env,s1) else
           if bvlSem_Boolv F = HD vs then bviSem_evaluate
             ([x3],env,s1) else
             (Rerr (Rabort Rtype_error),s1)) | res -> res)) /\
   (bviSem_evaluate ([flatLang_Let xs x2],env,s) =
      (match bviSem_fix_clock s (bviSem_evaluate (xs,env,s)) with
        (Rval vs,s1) -> bviSem_evaluate ([x2],vs ++ env,s1) | res ->
        res)) /\
   (bviSem_evaluate ([flatLang_Raise x1],env,s) =
      (match bviSem_evaluate ([x1],env,s) with (Rval vs,s) -> (Rerr
        (Rraise (Exn (HD vs))),s) | res -> res)) /\
   (bviSem_evaluate ([bvi_Return xs],env,s) =
      (match bviSem_evaluate (xs,env,s) with (Rval vs,s) -> (Rerr
        (Rraise (Ret vs)),s) | res -> res)) /\
   (bviSem_evaluate ([bvl_Op flatLang_op xs],env,s) =
      (match bviSem_fix_clock s (bviSem_evaluate (xs,env,s)) with
        (Rval vs,s) ->
          (match semanticPrimitives_do_app flatLang_op (REVERSE vs) s
            with Rerr e -> (Rerr e,s) | Rval (bvlSem_v,s) -> (Rval
            [bvlSem_v],s)) | res -> res)) /\
   (bviSem_evaluate ([bvl_Tick x],env,s) =
      (if ?_clock s = 0 then (Rerr (Rabort Rtimeout_error),s) else
        bviSem_evaluate ([x],env,bviSem_dec_clock 1 s))) /\
   (bviSem_evaluate ([bvl_Force force_loc n],env,s) =
      (if ~(n < LENGTH env) then (Rerr (Rabort Rtype_error),s) else
        let thunk_v = EL n env in
          match bviSem_dest_thunk thunk_v (?_refs s) with
            bviSem_BadRef -> (Rerr (Rabort Rtype_error),s) |
            bviSem_NotThunk -> (Rerr (Rabort Rtype_error),s) |
            bviSem_IsThunk Evaluated bvlSem_v -> (Rval [bvlSem_v],s) |
            bviSem_IsThunk NotEvaluated f' ->
              (match bvlSem_find_code (SOME force_loc) [thunk_v; f']
                (?_code s) with NONE -> (Rerr (Rabort Rtype_error),s) |
                SOME (args,flatLang_exp) ->
                   (if ?_clock s = 0 then
                     (Rerr (Rabort Rtimeout_error),?_clock_fupd (K 0)
                       s) else
                     (match bviSem_evaluate
                       ([flatLang_exp],args,bviSem_dec_clock 1 s) with
                       (Rerr (Rraise (Ret _24)),s1) -> (Rerr (Rabort
                       Rtype_error),s1) | res -> res))))) /\
   (bviSem_evaluate ([bvl_Call ticks dest xs handler],env,s1) =
      (if IS_NONE dest /\ IS_SOME handler then (Rerr (Rabort
        Rtype_error),s1) else
      match bviSem_fix_clock s1 (bviSem_evaluate (xs,env,s1)) with
        (Rval vs,s) ->
          (match bvlSem_find_code dest vs (?_code s) with NONE ->
            (Rerr (Rabort Rtype_error),s) | SOME (args,flatLang_exp) ->
               (if (?_clock s < ticks + 1) then (Rerr (Rabort
                 Rtimeout_error),?_clock_fupd (K 0) s) else
                 match bviSem_fix_clock (bviSem_dec_clock (ticks + 1)
                   s) (bviSem_evaluate
                   ([flatLang_exp],args,bviSem_dec_clock (ticks + 1) s))
                   with (Rerr (Rraise (Exn bvlSem_v)),s) ->
                      (match handler with SOME x ->
                           (match bviSem_evaluate ([x],bvlSem_v ::
                             env,s) with (Rerr (Rraise (Ret _25)),s1) ->
                             (Rerr (Rabort Rtype_error),s1) | res ->
                             res) | NONE -> (Rerr (Rraise (Exn
                             bvlSem_v)),s)) | (Rerr (Rraise _26),s) ->
                             (Rerr (Rabort Rtype_error),s) | res ->
                             res)) | res -> res)) /\
   (bviSem_evaluate ([bvi_LetCall rets ticks dest xs y],env,s1) =
      (match bviSem_fix_clock s1 (bviSem_evaluate (xs,env,s1)) with
        (Rval vs,s) ->
          (match bvlSem_find_code (SOME dest) vs (?_code s) with NONE
            -> (Rerr (Rabort Rtype_error),s) | SOME (args,flatLang_exp)
            ->
               (if (?_clock s < ticks + 1) then (Rerr (Rabort
                 Rtimeout_error),?_clock_fupd (K 0) s) else
                 match bviSem_fix_clock (bviSem_dec_clock (ticks + 1)
                   s) (bviSem_evaluate
                   ([flatLang_exp],args,bviSem_dec_clock (ticks + 1) s))
                   with (Rval _27,s) -> (Rerr (Rabort Rtype_error),s) |
                   (Rerr (Rraise (Ret ret_vs)),s) ->
                     (if LENGTH ret_vs = rets then bviSem_evaluate
                       ([y],ret_vs ++ env,s) else (Rerr (Rabort
                       Rtype_error),s)) | res -> res)) | res -> res))`;;

(* HOL4 ML code, not ported:
val evaluate_ind = theorem"evaluate_ind";
*)

(* We prove that the clock never increases. *)


(* Finally, we remove fix_clock from the induction and definition
   theorems. *)

(* observational semantics *)

let initial_state_def = cake_define
  `bviSem_initial_state ffi code co cc k = mk_? k ffi code cc co
  FEMPTY NONE`;;

let semantics_def = cake_define
  `bviSem_semantics init_ffi code co cc start =
   (let es = [bvi_Call 0 (SOME start) [] NONE] in
   let init = bviSem_initial_state init_ffi code co cc in
     if ?k e. FST (bviSem_evaluate (es,[],init k)) = Rerr e /\
        ~(e = Rabort Rtimeout_error) /\ (!f'. ~(e = Rabort
          (Rffi_error f'))) then ffi_Fail else
     match some (\res.
       ?k s r outcome.
         bviSem_evaluate (es,[],init k) = (r,s) /\
         (match r with Rerr (Rabort (Rffi_error e)) -> outcome =
           ffi_FFI_outcome e | Rval _28 -> outcome = ffi_Success | _29
           -> F) /\
         res = ffi_Terminate outcome (ffi_state_io_events (?_ffi s)))
           with SOME res -> res | NONE ->
        ffi_Diverge
          (build_lprefix_lub
            (IMAGE (\k. fromList (ffi_state_io_events (?_ffi (SND
               (bviSem_evaluate (es,[],init k)))))) UNIV)))`;;

(* clean up *)

(* HOL4 ML code, not ported:
val _ = map delete_binding ["evaluate_AUX_def",
  "evaluate_primitive_def"];
*)
