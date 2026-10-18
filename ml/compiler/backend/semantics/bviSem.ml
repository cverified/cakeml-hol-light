(* ======================================================== *)
(*  bviSem: ported from HOL4's
    compiler/backend/semantics/bviSemScript.sml
    A definition theory, with 12 definitions, 3 datatypes and 7
    theorems.  Needed by 7 files of the port.  *)
(* ======================================================== *)

(*
  The formal semantics of BVI
*)

needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/bvi.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/clos_annotate.ml";;
needs "compiler/backend/semantics/backendProps.ml";;
needs "compiler/backend/semantics/bvlSem.ml";;
needs "compiler/backend/semantics/closSem.ml";;
needs "lib/errorMonad.ml";;
needs "lib/integer_word.ml";;
needs "lib/lprefix_lub.ml";;
needs "lib/peg.ml";;
needs "lib/sptree.ml";;
needs "semantics/ast.ml";;
needs "semantics/semanticPrimitives.ml";;

(* HOL4 bviSemScript.sml:13: the overload num_stubs, which the port
   expands *)

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
hol4_overload "state_refs" "bviSem_state_refs";;
hol4_overload "state_refs_fupd" "bviSem_state_refs_fupd";;
hol4_overload "state_clock" "bviSem_state_clock";;
hol4_overload "state_clock_fupd" "bviSem_state_clock_fupd";;
hol4_overload "state_global" "bviSem_state_global";;
hol4_overload "state_global_fupd" "bviSem_state_global_fupd";;
hol4_overload "compile" "bviSem_state_compile";;
hol4_overload "compile_fupd" "bviSem_state_compile_fupd";;
hol4_overload "compile_oracle" "bviSem_state_compile_oracle";;
hol4_overload "compile_oracle_fupd" "bviSem_state_compile_oracle_fupd";;
hol4_overload "state_code" "bviSem_state_code";;
hol4_overload "state_code_fupd" "bviSem_state_code_fupd";;
hol4_overload "state_ffi" "bviSem_state_ffi";;
hol4_overload "state_ffi_fupd" "bviSem_state_ffi_fupd";;

let dec_clock_def = cake_define
  `bviSem_dec_clock x s = state_clock_fupd (K (state_clock s - x)) s`;;
hol4_overload "dec_clock" "bviSem_dec_clock";;

let bviSem_LESS_EQ_dec_clock = cake_theorem "LESS_EQ_dec_clock[local]"
  (fun () ->
    `state_clock
       r <= state_clock (dec_clock x s) ==> state_clock r <=
         state_clock s`)
  CHEAT_TAC;;

let bvi_to_bvl_def = cake_define
  `(bvi_to_bvl:('c,'ffi)bviSem_state->('c,'ffi)bvlSem_state) s =
     mk_bvlSem_state ARB (state_refs s) (state_clock s) ARB ARB
       (sptree_map (K ARB) (state_code s)) (state_ffi s)`;;

let bvl_to_bvi_def = cake_define
  `(bvl_to_bvi:('c,'ffi)bvlSem_state->('c,'ffi)bviSem_state->('c
  ,'ffi)bviSem_state) s t = state_ffi_fupd (K (state_ffi s))
  (state_clock_fupd (K (state_clock s)) (state_refs_fupd (K (state_refs
  s))
     t))`;;

(* HOL4 bviSemScript.sml:69-77: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let finalise_cons_def = cake_define_try_tac (fun () ->
  `MEASURE (CARD o FDOM o SND)`)
  CHEAT_TAC
  `bviSem_finalise_cons v refs =
        match v with
          (RefPtr b ptr:bvlSem_v) ->
       (match FLOOKUP refs ptr with SOME (bvlSem_MutBlock tag
         finalised l c r) ->
           (if ~finalised then
             (match bviSem_finalise_cons c (refs \\ ptr) with SOME
               (c',refs') -> SOME (Block tag (l ++ [c'] ++ r),refs' |+
               (ptr,bvlSem_MutBlock tag T l c r)) | NONE -> NONE) else
               NONE) | SOME res -> SOME (RefPtr b ptr,refs) | NONE ->
               NONE)
        | v -> SOME (v,refs)`;;
hol4_overload "finalise_cons" "bviSem_finalise_cons";;

(* HOL4 bviSemScript.sml:79: the ML values that the definitions below
   antiquote *)

let do_app_aux_def = cake_define
  `bviSem_do_app_aux op (vs:bvlSem_v list) (s:('c,'ffi)bviSem_state) =
     (match (op,vs) with (closLang_IntOp (closLang_Const i),xs) ->
       (if small_enough_int i /\ NULL xs then
         SOME (SOME (Number i,s)) else NONE) | (closLang_Label l,xs)
           -> (match xs with [] -> (if l IN domain (state_code s) then
                              SOME (SOME (bvlSem_CodePtr l,s)) else
                                NONE) | _1 -> NONE) | (closLang_GlobOp
                                closLang_GlobalsPtr,xs) ->
         (match xs with [] -> (match bviSem_state_global s with SOME
           p -> SOME (SOME (RefPtr T p,s)) | NONE -> NONE) | _2 -> NONE)
           | (closLang_GlobOp closLang_SetGlobalsPtr,xs) ->
         (match xs with [RefPtr T p] -> SOME (SOME
           (Unit,bviSem_state_global_fupd (K (SOME p)) s)) | _3 -> NONE)
           | (closLang_GlobOp (closLang_Global n),xs) ->
         (match xs with [] -> (match bviSem_state_global s with SOME
           ptr ->
                        (match FLOOKUP (state_refs s) ptr with SOME
                          (ValueArray xs) ->
                             (if n < LENGTH xs then SOME (SOME (EL n
                               xs,s)) else NONE) | _4 -> NONE) | NONE ->
                               NONE) | _5 -> NONE) | (closLang_GlobOp
                               (closLang_SetGlobal n),xs) ->
         (match xs with [x] -> (match bviSem_state_global s with SOME
           ptr ->
                        (match FLOOKUP (state_refs s) ptr with SOME
                          (ValueArray xs) ->
                             (if n < LENGTH xs then SOME (SOME
                               (Unit,state_refs_fupd (K (state_refs s |+
                              (ptr,ValueArray (LUPDATE x n xs)))) s))
                                else NONE) | _6 -> NONE) | NONE -> NONE)
                                | _7 -> NONE) | (closLang_BlockOp
                                (closLang_FromList n),xs) ->
         (match xs with [len; lv] ->
             (match v_to_list lv with SOME vs -> (if len = Number
               (&(LENGTH vs)) then SOME (SOME (Block n vs,s)) else NONE)
               | _8 -> NONE) | _9 -> NONE) | (closLang_MemOp
               (closLang_RefByte f),xs) ->
         (match xs with [Number i; Number b] ->
             (if (&0) <= i /\ (?(w:word8). b = &(w2n w)) then
               let ptr = (LEAST (\ptr. ~(ptr IN FDOM (state_refs
                 s)))) in
                 SOME (SOME (RefPtr T ptr,state_refs_fupd (K
                   (state_refs s |+
                   (ptr,ByteArray f (REPLICATE (num_of_int i) (i2w
                     b))))) s)) else NONE) | _10 -> NONE) |
                     (closLang_MemOp (closLang_MutCons tag i),xs) ->
         (let ptr = (LEAST (\ptr. ~(ptr IN FDOM (state_refs s)))) in
            if i >= LENGTH xs then NONE else
              let l = TAKE i xs in
              let c = EL i xs in
              let r = DROP (i + 1) xs in
              let b = bvlSem_MutBlock tag F l c r in
                SOME (SOME (RefPtr F ptr,(state_refs_fupd (K
                  (state_refs s |+ (ptr,b))) s)))) | (closLang_MemOp
                  closLang_UpdateCons,[RefPtr _11 ptr; Number i; x]) ->
         (match FLOOKUP (state_refs s) ptr with SOME (bvlSem_MutBlock
           tag finalised l c r) ->
              (if ~(i = &(LENGTH l)) \/ finalised then NONE else
                SOME (SOME (Unit,state_refs_fupd (K (state_refs s |+
                  (ptr,bvlSem_MutBlock tag F l x r))) s))) | _12 ->
                  NONE) | (closLang_MemOp closLang_FinaliseCons,[x]) ->
         (match bviSem_finalise_cons x (state_refs s) with SOME
           (v,refs') -> SOME (SOME (v,state_refs_fupd (K refs') s)) |
           NONE -> NONE) | (closLang_GlobOp closLang_AllocGlobal,_13)
           -> NONE | (closLang_MemOp closLang_FromListByte,_14) ->
           NONE | (closLang_MemOp closLang_ToListByte,_15) -> NONE |
           (closLang_MemOp closLang_ConcatByteVec,_16) -> NONE |
           (closLang_MemOp (closLang_CopyByte T),_17) -> NONE | _18
           -> SOME NONE)`;;
hol4_overload "do_app_aux" "bviSem_do_app_aux";;

let do_install_def = cake_define
  `bviSem_do_install vs (s:('c,'ffi)bviSem_state) =
       (match vs with [v1; v2; vl1; vl2] ->
            (match (v_to_bytes v1,v_to_words v2) with (SOME
              bytes,SOME data) ->
                (if ~(vl1 = Number (&(LENGTH bytes))) \/ ~(
                   vl2 = Number (&(LENGTH data))) then Rerr (Rabort
                     Rtype_error) else
                let (cfg,progs) = compile_oracle s 0 in
                let new_oracle = misc_shift_seq 1 (compile_oracle s)
                  in
                  if DISJOINT (domain (state_code s)) (set_of_list
                    (MAP FST progs)) /\ ALL_DISTINCT (MAP FST progs)
                    then
                  (match (compile s cfg progs,progs) with (SOME
                    (bytes',data',cfg'),(k,prog) :: _19) ->
                       (if bytes = bytes' /\ data = data' /\ FST
                         (new_oracle 0) = cfg' then
                         let s' = compile_oracle_fupd (K new_oracle)
                           (state_code_fupd (K (sptree_union (state_code
                           s) (fromAList progs)))
                           s) in
                           Rval (bvlSem_CodePtr k,s') else Rerr
                             (Rabort Rtype_error)) | _20 -> Rerr
                             (Rabort Rtype_error)) else Rerr (Rabort
                             Rtype_error)) | _21 -> Rerr (Rabort
                             Rtype_error)) | _22 -> Rerr (Rabort
                             Rtype_error))`;;
hol4_overload "do_install" "bviSem_do_install";;

let do_app_def = cake_define
  `bviSem_do_app op vs (s:('c,'ffi)bviSem_state) =
     (if op = closLang_Install then do_install vs s else
     match bviSem_do_app_aux op vs s with NONE -> Rerr (Rabort
       Rtype_error) | SOME (SOME (v,t)) -> Rval (v,t) | SOME NONE ->
       (match bvlSem_do_app op vs (bvi_to_bvl s) with Rval (v,t) ->
       Rval (v,bvl_to_bvi t s) | Rerr (Rabort a) -> Rerr (Rabort a) |
       Rerr (Rraise v) -> Rerr (Rraise (Exn v))))`;;
hol4_overload "do_app" "bviSem_do_app";;

let bviSem_dest_thunk_ret_INDUCT,bviSem_dest_thunk_ret_RECURSION =
  define_datatype
  "bviSem_dest_thunk_ret = bviSem_BadRef | bviSem_NotThunk | \
   bviSem_IsThunk (thunk_mode) (bvlSem_v)";;
hol4_overload "BadRef" "bviSem_BadRef";;
hol4_overload "NotThunk" "bviSem_NotThunk";;
hol4_overload "IsThunk" "bviSem_IsThunk";;

let dest_thunk_def = cake_define
  `bviSem_dest_thunk vs refs =
      match vs with
        (RefPtr b ptr:bvlSem_v) ->
     (match FLOOKUP refs ptr with NONE -> BadRef | SOME (Thunk
       Evaluated v) ->
          (if b then BadRef else IsThunk Evaluated v) | SOME (Thunk
            NotEvaluated v) ->
          (if b then BadRef else IsThunk NotEvaluated v) | SOME _23
            -> NotThunk)
      | vs -> NotThunk`;;
hol4_overload "dest_thunk" "bviSem_dest_thunk";;


(* The evaluation is defined as a clocked functional version of
   a conventional big-step operational semantics. *)

let fix_clock_def = cake_define
  `bviSem_fix_clock s (res,s1) = (res,state_clock_fupd (K (MIN
  (state_clock s) (state_clock s1))) s1)`;;
hol4_overload "fix_clock" "bviSem_fix_clock";;

let bviSem_fix_clock_IMP = cake_theorem "fix_clock_IMP[local]"
  (fun () ->
    `fix_clock s x = (res,s1) ==> state_clock s1 <= state_clock s`)
  CHEAT_TAC;;

(* The semantics of expression evaluation is defined next. For
   convenience of subsequent proofs, the evaluation function is
   defined to evaluate a list of bvi_exp expressions. *)

let fix_clock_IMP =
  try prove
   (`!s x res s1. bviSem_fix_clock s x = (res,s1)
                  ==> state_clock s1 <= state_clock s`,
    REWRITE_TAC[FORALL_PAIR_THM; fix_clock_def] THEN
    REWRITE_TAC(PAIR_EQ :: record_thms "bviSem_state") THEN
    REPEAT STRIP_TAC THEN SUBST_VAR_TAC THEN
    REWRITE_TAC(record_thms "bviSem_state") THEN
    REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC)
  with Failure e ->
    (print_string ("\nfix_clock_IMP: " ^ e ^ "\n"); TRUTH);;

(* a fallback TRUTH says nothing, and a fact that says nothing
   is of no use *)
if concl fix_clock_IMP <> `T` then
  cake_term_facts := fix_clock_IMP :: (!cake_term_facts);;

let _ = size_thms "flatLang_exp";;
(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 bviSemScript.sml:339-347: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let evaluate_def = cake_define_list_try_tac (fun () ->
  `(inv_image (MEASURE I LEX MEASURE (list_size flatLang_exp_size))
                              (\(xs,env,s). (state_clock s,xs)))`)
  CHEAT_TAC
  [`bviSem_evaluate ([],env,s) = ((Rval []:(bvlSem_v
  list,exn_or_ret)semanticPrimitives_result),s)`;
   `bviSem_evaluate (x :: y :: xs,env,s) =
         (match fix_clock s (bviSem_evaluate ([x],env,s)) with (Rval
           v1,s1) ->
             (match bviSem_evaluate (y :: xs,env,s1) with (Rval
               vs,s2) -> (Rval (HD v1 :: vs),s2) | res -> res) | res
               -> res)`;
   `bviSem_evaluate ([(Var n:bvi_exp)],env,s) =
         (if n < LENGTH env then (Rval [EL n env],s) else (Rerr
           (Rabort Rtype_error),s))`;
   `bviSem_evaluate ([(If x1 x2 x3:bvi_exp)],env,s) =
         (match fix_clock s (bviSem_evaluate ([x1],env,s)) with
           (Rval vs,s1) ->
              (if Boolv T = HD vs then bviSem_evaluate ([x2],env,s1)
                else
              if Boolv F = HD vs then bviSem_evaluate ([x3],env,s1)
                else
                (Rerr (Rabort Rtype_error),s1)) | res -> res)`;
   `bviSem_evaluate ([(Let xs x2:bvi_exp)],env,s) =
         (match fix_clock s (bviSem_evaluate (xs,env,s)) with
           (Rval vs,s1) -> bviSem_evaluate ([x2],vs ++ env,s1) | res
           -> res)`;
   `bviSem_evaluate ([(Raise x1:bvi_exp)],env,s) =
         (match bviSem_evaluate ([x1],env,s) with (Rval vs,s) ->
           (Rerr (Rraise (Exn (HD vs))),s) | res -> res)`;
   `bviSem_evaluate ([(bvi_Return xs:bvi_exp)],env,s) =
         (match bviSem_evaluate (xs,env,s) with (Rval vs,s) ->
           (Rerr (Rraise (Ret vs)),s) | res -> res)`;
   `bviSem_evaluate ([(Op op xs:bvi_exp)],env,s) =
         (match fix_clock s (bviSem_evaluate (xs,env,s)) with (Rval
           vs,s) ->
             (match do_app op (REVERSE vs) s with Rerr e -> (Rerr
               e,s) | Rval (v,s) -> (Rval [v],s)) | res -> res)`;
   `bviSem_evaluate ([(Tick x:bvi_exp)],env,s) =
         (if state_clock s = 0 then (Rerr (Rabort Rtimeout_error),s)
           else
           bviSem_evaluate ([x],env,dec_clock 1 s))`;
   `bviSem_evaluate ([(Force force_loc n:bvi_exp)],env,s) =
         (if ~(n < LENGTH env) then (Rerr (Rabort Rtype_error),s)
           else
           let thunk_v = EL n env in
             match dest_thunk thunk_v (state_refs s) with BadRef ->
               (Rerr (Rabort Rtype_error),s) | NotThunk -> (Rerr (Rabort
               Rtype_error),s) | IsThunk Evaluated v -> (Rval [v],s) |
               IsThunk NotEvaluated f ->
                 (match find_code (SOME force_loc) [thunk_v; f]
                   (state_code s) with NONE -> (Rerr (Rabort
                   Rtype_error),s) | SOME (args,exp) ->
                      (if state_clock s = 0 then
                        (Rerr (Rabort
                          Rtimeout_error),state_clock_fupd (K 0) s) else
                        (match bviSem_evaluate
                          ([exp],args,dec_clock 1 s) with (Rerr
                          (Rraise (Ret _30)),s1) -> (Rerr (Rabort
                          Rtype_error),s1) | res -> res))))`;
   `bviSem_evaluate ([(Call ticks dest xs handler:bvi_exp)],env,s1) =
         (if IS_NONE dest /\ IS_SOME handler then (Rerr (Rabort
           Rtype_error),s1) else
         match fix_clock s1 (bviSem_evaluate (xs,env,s1)) with (Rval
           vs,s) ->
             (match find_code dest vs (state_code s) with NONE ->
               (Rerr (Rabort Rtype_error),s) | SOME (args,exp) ->
                  (if (state_clock s < ticks + 1) then (Rerr (Rabort
                    Rtimeout_error),state_clock_fupd (K 0) s) else
                    match fix_clock (dec_clock (ticks + 1) s)
                      (bviSem_evaluate ([exp],args,dec_clock (ticks + 1)
                      s)) with (Rerr (Rraise (Exn v)),s) ->
                         (match handler with SOME x ->
                              (match bviSem_evaluate ([x],v ::
                                env,s) with (Rerr (Rraise (Ret
                                _42)),s1) -> (Rerr (Rabort
                                Rtype_error),s1) | res -> res) | NONE
                                -> (Rerr (Rraise (Exn v)),s)) | (Rerr
                                (Rraise _43),s) -> (Rerr (Rabort
                                Rtype_error),s) | res -> res)) | res
                                -> res)`;
   `bviSem_evaluate ([bvi_LetCall rets ticks dest xs y],env,s1) =
         (match fix_clock s1 (bviSem_evaluate (xs,env,s1)) with
           (Rval vs,s) ->
             (match find_code (SOME dest) vs (state_code s) with
               NONE -> (Rerr (Rabort Rtype_error),s) | SOME (args,exp)
               ->
                  (if (state_clock s < ticks + 1) then (Rerr (Rabort
                    Rtimeout_error),state_clock_fupd (K 0) s) else
                    match fix_clock (dec_clock (ticks + 1) s)
                      (bviSem_evaluate ([exp],args,dec_clock (ticks + 1)
                      s)) with (Rval _44,s) -> (Rerr (Rabort
                      Rtype_error),s) | (Rerr (Rraise (Ret ret_vs)),s)
                      ->
                        (if LENGTH ret_vs = rets then
                          bviSem_evaluate ([y],ret_vs ++ env,s)
                          else (Rerr (Rabort Rtype_error),s)) | res
                          -> res)) | res -> res)`];;
hol4_overload "evaluate" "bviSem_evaluate";;

(* HOL4 bviSemScript.sml:349: ML code, not ported *)

(* We prove that the clock never increases. *)

let bviSem_do_app_const = cake_theorem "do_app_const"
  (fun () ->
    `(bviSem_do_app op args s1 = Rval (res,s2)) ==>
      (state_clock s2 = state_clock s1)`)
  CHEAT_TAC;;

let bviSem_evaluate_clock = cake_theorem "evaluate_clock"
  (fun () ->
    `!xs env s1 vs s2.
       (bviSem_evaluate (xs,env,s1) = (vs,s2)) ==> state_clock s2
         <= state_clock s1`)
  CHEAT_TAC;;

let bviSem_fix_clock_evaluate = cake_theorem "fix_clock_evaluate"
  (fun () ->
    `fix_clock s (evaluate (xs,env,s)) = evaluate (xs,env,s)`)
  CHEAT_TAC;;


(* Finally, we remove fix_clock from the induction and definition theorems. *)

(* HOL4 bviSemScript.sml:392-393: a theorem that HOL4 states as the
   value of an ML expression *)

(* HOL4 bviSemScript.sml:395-396: a theorem that HOL4 states as the
   value of an ML expression *)

(* observational semantics *)

let initial_state_def = cake_define
  `bviSem_initial_state ffi code co cc k = mk_bviSem_state FEMPTY k
  NONE cc co code ffi`;;
hol4_overload "initial_state" "bviSem_initial_state";;

let semantics_def = cake_define
  `bviSem_semantics init_ffi code co cc start' =
   (let es = [bvi_Call 0 (SOME start') [] NONE] in
   let init = initial_state init_ffi code co cc in
     if ?k e. FST (evaluate (es,[],init k)) = Rerr e /\
        ~(e = Rabort Rtimeout_error) /\ (!f. ~(e = Rabort (Rffi_error
          f))) then ffi_Fail else
     match some (\res.
       ?k s r outcome.
         evaluate (es,[],init k) = (r,s) /\
         (match r with Rerr (Rabort (Rffi_error e)) -> outcome =
           ffi_FFI_outcome e | Rval _45 -> outcome = ffi_Success | _46
           -> F) /\
         res = ffi_Terminate outcome (ffi_state_io_events (state_ffi
           s))) with SOME res -> res | NONE ->
        ffi_Diverge
          (build_lprefix_lub
            (IMAGE (\k. fromList (ffi_state_io_events (state_ffi (SND
               (evaluate (es,[],init k)))))) UNIV)))`;;
hol4_overload "semantics" "bviSem_semantics";;

(* clean up *)

(* HOL4 bviSemScript.sml:437: ML code, not ported *)
