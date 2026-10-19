(* ======================================================== *)
(*  evaluateProps: ported from HOL4's
    semantics/proofs/evaluatePropsScript.sml
    A proof theory about evaluate.ml, with 5 definitions and 87
    theorems.  Needed by 9 files of the port.  *)
(* ======================================================== *)

(*
  Properties of the operational semantics.
*)

needs "basis/pure/mlstring.ml";;
needs "pancake/panLang.ml";;
needs "semantics/ast.ml";;
needs "semantics/evaluate.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/namespace.ml";;
needs "semantics/proofs/namespaceProps.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;
needs "semantics/semanticPrimitives.ml";;

let call_FFI_LENGTH = cake_theorem "call_FFI_LENGTH"
  (fun () ->
    `(call_FFI st index conf x = FFI_return new_st new_bytes) ==>
      (LENGTH x = LENGTH new_bytes)`)
  CHEAT_TAC;;

let call_FFI_rel_def = cake_define
  `call_FFI_rel s1 s2 <=> (?n conf bytes t. call_FFI s1 n conf bytes
  = FFI_return s2 t)`;;

let call_FFI_rel_consts = cake_theorem "call_FFI_rel_consts"
  (fun () ->
    `call_FFI_rel s1 s2 ==> (oracle s2 = oracle s1)`)
  CHEAT_TAC;;

let RTC_call_FFI_rel_consts = cake_theorem "RTC_call_FFI_rel_consts"
  (fun () ->
    `!s1 s2. RTC call_FFI_rel s1 s2 ==> (oracle s2 = oracle s1)`)
  CHEAT_TAC;;

let dest_IO_event_def = cake_define
  `dest_IO_event (IO_event s c b) = (s,c,b)`;;

let io_events_mono_def = cake_define
  `io_events_mono s1 s2 <=> ffi_state_io_events
     s1 <<= ffi_state_io_events s2 /\
     (ffi_state_io_events s2 = ffi_state_io_events s1 ==> s2 = s1)`;;

let io_events_mono_refl = cake_theorem "io_events_mono_refl[simp]"
  (fun () ->
    `io_events_mono ffi ffi`)
  CHEAT_TAC;;

let io_events_mono_trans = cake_theorem "io_events_mono_trans"
  (fun () ->
    `io_events_mono ffi1 ffi2 /\ io_events_mono ffi2 ffi3 ==>
     io_events_mono ffi1 ffi3`)
  CHEAT_TAC;;

let io_events_mono_antisym = cake_theorem "io_events_mono_antisym"
  (fun () ->
    `io_events_mono s1 s2 /\ io_events_mono s2 s1 ==> s1 = s2`)
  CHEAT_TAC;;

let call_FFI_rel_io_events_mono =
  cake_theorem "call_FFI_rel_io_events_mono"
  (fun () ->
    `!s1 s2.
     RTC call_FFI_rel s1 s2 ==> io_events_mono s1 s2`)
  CHEAT_TAC;;

let do_app_call_FFI_rel = cake_theorem "do_app_call_FFI_rel"
  (fun () ->
    `semanticPrimitives_do_app (r,ffi) op vs = SOME ((r',ffi'),res) ==>
  RTC
     call_FFI_rel ffi ffi'`)
  CHEAT_TAC;;

let evaluate_call_FFI_rel = cake_theorem "evaluate_call_FFI_rel"
  (fun () ->
    `(!(s:'ffi semanticPrimitives_state) e exp.
        RTC call_FFI_rel (semanticPrimitives_state_ffi s)
          (semanticPrimitives_state_ffi (FST (evaluate s e exp)))) /\
     (!(s:'ffi semanticPrimitives_state) e v pes errv.
        RTC call_FFI_rel (semanticPrimitives_state_ffi s)
          (semanticPrimitives_state_ffi (FST (evaluate_evaluate_match s
          e v pes errv)))) /\
     (!(s:'ffi semanticPrimitives_state) e ds.
        RTC call_FFI_rel (semanticPrimitives_state_ffi s)
          (semanticPrimitives_state_ffi (FST (evaluate_evaluate_decs s
          e ds))))`)
  CHEAT_TAC;;

let evaluate_call_FFI_rel_imp = cake_theorem "evaluate_call_FFI_rel_imp"
  (fun () ->
    `(!s e p s' r.
        evaluate s e p = (s',r) ==>
        RTC call_FFI_rel (semanticPrimitives_state_ffi s)
          (semanticPrimitives_state_ffi s')) /\
     (!s e v pes errv s' r.
        evaluate_evaluate_match s e v pes errv = (s',r) ==>
        RTC call_FFI_rel (semanticPrimitives_state_ffi s)
          (semanticPrimitives_state_ffi s')) /\
     (!s e p s' r.
        evaluate_evaluate_decs s e p = (s',r) ==>
        RTC call_FFI_rel (semanticPrimitives_state_ffi s)
          (semanticPrimitives_state_ffi s'))`)
  CHEAT_TAC;;

let evaluate_decs_call_FFI_rel =
  cake_theorem "evaluate_decs_call_FFI_rel[local]"
  (fun () ->
    `!s e d.
        RTC call_FFI_rel (semanticPrimitives_state_ffi s)
          (semanticPrimitives_state_ffi (FST (evaluate_evaluate_decs s
          e d)))`)
  CHEAT_TAC;;

let evaluate_decs_call_FFI_rel_imp =
  cake_theorem "evaluate_decs_call_FFI_rel_imp"
  (fun () ->
    `!s e p s' r.
       evaluate_evaluate_decs s e p = (s',r) ==>
       RTC call_FFI_rel (semanticPrimitives_state_ffi s)
         (semanticPrimitives_state_ffi s')`)
  CHEAT_TAC;;

let evaluateProps_do_app_io_events_mono =
  cake_theorem "do_app_io_events_mono"
  (fun () ->
    `semanticPrimitives_do_app (r,ffi) op vs = SOME ((r',ffi'),res)
  ==> io_events_mono ffi ffi'`)
  CHEAT_TAC;;

let evaluateProps_evaluate_io_events_mono =
  cake_theorem "evaluate_io_events_mono"
  (fun () ->
    `(!(s:'ffi semanticPrimitives_state) e exp.
        io_events_mono (semanticPrimitives_state_ffi s)
          (semanticPrimitives_state_ffi (FST (evaluate s e exp)))) /\
     (!(s:'ffi semanticPrimitives_state) e v pes errv.
        io_events_mono (semanticPrimitives_state_ffi s)
          (semanticPrimitives_state_ffi (FST (evaluate_evaluate_match s
          e v pes errv)))) /\
     (!s e d.
        io_events_mono (semanticPrimitives_state_ffi s)
          (semanticPrimitives_state_ffi (FST (evaluate_evaluate_decs s
          e d))))`)
  CHEAT_TAC;;

let evaluate_io_events_mono_imp =
  cake_theorem "evaluate_io_events_mono_imp"
  (fun () ->
    `(!s e p s' r.
        evaluate s e p = (s',r) ==>
        io_events_mono (semanticPrimitives_state_ffi s)
          (semanticPrimitives_state_ffi s')) /\
     (!s e v pes errv s' r.
        evaluate_evaluate_match s e v pes errv = (s',r) ==>
        io_events_mono (semanticPrimitives_state_ffi s)
          (semanticPrimitives_state_ffi s')) /\
     (!s e p s' r.
       evaluate_evaluate_decs s e p = (s',r) ==>
       io_events_mono (semanticPrimitives_state_ffi s)
         (semanticPrimitives_state_ffi s'))`)
  CHEAT_TAC;;

let is_clock_io_mono_def = cake_define
  `is_clock_io_mono f s = (match f s with (s',r) ->
         io_events_mono (semanticPrimitives_state_ffi s)
           (semanticPrimitives_state_ffi s') /\
         semanticPrimitives_state_clock s' <=
           semanticPrimitives_state_clock s /\
         semanticPrimitives_state_next_type_stamp s <=
           semanticPrimitives_state_next_type_stamp s' /\
         semanticPrimitives_state_next_exn_stamp s <=
           semanticPrimitives_state_next_exn_stamp s' /\
         LENGTH (semanticPrimitives_state_refs s) <= LENGTH
           (semanticPrimitives_state_refs s') /\ (!clk. match f
           (semanticPrimitives_state_clock_fupd (K clk) s) with (s'',r')
           ->
             (
                 ~(r' = Rerr (Rabort Rtimeout_error)) ==>
                 ~(r = Rerr (Rabort Rtimeout_error)) ==>
                     r' = r /\ s'' =
                       (semanticPrimitives_state_clock_fupd (K (clk -
                       (semanticPrimitives_state_clock s -
                       semanticPrimitives_state_clock s'))) s')) /\
             (
                 ~(r = Rerr (Rabort Rtimeout_error)) ==> (
                     clk >= semanticPrimitives_state_clock s -
                       semanticPrimitives_state_clock s' <=> ~(r' = Rerr
                       (Rabort Rtimeout_error)))) /\
             (
                 ~(r' = Rerr (Rabort Rtimeout_error)) ==>
                 clk <= semanticPrimitives_state_clock s ==> ~(r =
                   Rerr (Rabort Rtimeout_error))) /\ (clk <=
                   semanticPrimitives_state_clock s ==>
                   io_events_mono (semanticPrimitives_state_ffi s'')
                   (semanticPrimitives_state_ffi s'))))`;;

let is_clock_io_mono_cong = cake_theorem "is_clock_io_mono_cong"
  (fun () ->
    `s = t ==>
     (!s. semanticPrimitives_state_eval_state s =
       semanticPrimitives_state_eval_state t /\
       semanticPrimitives_state_refs s = semanticPrimitives_state_refs t
       /\ semanticPrimitives_state_ffi s = semanticPrimitives_state_ffi
       t ==>
       f s = g s) ==>
     (is_clock_io_mono f s <=> is_clock_io_mono g t)`)
  CHEAT_TAC;;

let is_clock_io_mono_return = cake_theorem "is_clock_io_mono_return"
  (fun () ->
    `is_clock_io_mono (\s. (s,Rval r)) s`)
  CHEAT_TAC;;

let is_clock_io_mono_err = cake_theorem "is_clock_io_mono_err"
  (fun () ->
    `is_clock_io_mono (\s. (s,Rerr r)) s`)
  CHEAT_TAC;;

let pair_CASE_eq_forall = cake_theorem "pair_CASE_eq_forall"
  (fun () ->
    `(match x with (a,b) -> P a b) = (!a b. x = (a,b) ==> P a b)`)
  CHEAT_TAC;;

let is_clock_io_mono_bind = cake_theorem "is_clock_io_mono_bind"
  (fun () ->
    `is_clock_io_mono f s /\
      (!s' r.
          f s = (s',r) ==> is_clock_io_mono (g r) s') /\ (!s'.
          g (Rerr (Rabort Rtimeout_error)) s' = (s',Rerr (Rabort
            Rtimeout_error))) ==> is_clock_io_mono (\s. match f s with
            (s',r) -> g r s') s`)
  CHEAT_TAC;;

let adj_clock_def = cake_define
  `adj_clock inc dec s = (semanticPrimitives_state_clock_fupd (K
  ((semanticPrimitives_state_clock s + inc) - dec)) s)`;;

let is_clock_io_mono_check = cake_theorem "is_clock_io_mono_check"
  (fun () ->
    `(~(semanticPrimitives_state_clock s = 0) ==>
          is_clock_io_mono (\s. f (adj_clock 1 0 s))
            (evaluate_dec_clock s)) ==> is_clock_io_mono (\s. if
            semanticPrimitives_state_clock s = 0 then (s,Rerr (Rabort
            Rtimeout_error)) else f s) s`)
  CHEAT_TAC;;

let dec_inc_clock = cake_theorem "dec_inc_clock"
  (fun () ->
    `evaluate_dec_clock (adj_clock 1 0 s) = s`)
  CHEAT_TAC;;

let do_app_refs_length = cake_theorem "do_app_refs_length"
  (fun () ->
    `semanticPrimitives_do_app refs_ffi op vs = SOME res ==>
     LENGTH (FST refs_ffi) <= LENGTH (FST (FST res))`)
  CHEAT_TAC;;

let is_clock_io_mono_do_app_simple =
  cake_theorem "is_clock_io_mono_do_app_simple"
  (fun () ->
    `!xs (st:'ffi semanticPrimitives_state).
      is_clock_io_mono (\st'.
       match semanticPrimitives_do_app
         (semanticPrimitives_state_refs st',semanticPrimitives_state_ffi
         st') op xs with
         NONE -> (st',Rerr (Rabort Rtype_error)) | SOME
           ((refs,ffi),r) ->
         (semanticPrimitives_state_ffi_fupd (K ffi)
           (semanticPrimitives_state_refs_fupd (K refs)
           st'),list_result r)) st`)
  CHEAT_TAC;;

let is_clock_io_mono_acc_safe = cake_theorem "is_clock_io_mono_acc_safe"
  (fun () ->
    `!v g. (!st clk. f (semanticPrimitives_state_clock_fupd (K clk) st)
  = f st) /\
     (f st = v \/ ~(f st = v)) /\
     is_clock_io_mono (\st'. g (f st) st') st ==>
     is_clock_io_mono (\st'. g (f st') st') st`)
  CHEAT_TAC;;

(* HOL4 evaluatePropsScript.sml:306-308: a theorem that HOL4 states
   as the value of an ML expression: is_clock_io_mono_if_safe *)
(* HOL4 evaluatePropsScript.sml:309-311: a theorem that HOL4 states
   as the value of an ML expression:
   is_clock_io_mono_option_case_safe *)
(* HOL4 evaluatePropsScript.sml:312-315: a theorem that HOL4 states
   as the value of an ML expression: is_clock_io_mono_match_case_safe *)
(* HOL4 evaluatePropsScript.sml:316-319: a theorem that HOL4 states
   as the value of an ML expression:
   is_clock_io_mono_match_case_pair_safe *)

(* HOL4 evaluatePropsScript.sml:321-326: a proof *)

let is_clock_io_mono_evaluate = cake_theorem "is_clock_io_mono_evaluate"
  (fun () ->
    `(!(s:'ffi semanticPrimitives_state) env es. is_clock_io_mono (\s.
  evaluate s env es) s) /\
     (!(s:'ffi semanticPrimitives_state) env v pes err_v.
          is_clock_io_mono (\s. evaluate_evaluate_match s env v pes
            err_v) s) /\
     (!(s:'ffi semanticPrimitives_state) env ds.
          is_clock_io_mono (\s. evaluate_evaluate_decs s env ds)
            s)`)
  CHEAT_TAC;;

let is_clock_io_mono_evaluate_decs =
  cake_theorem "is_clock_io_mono_evaluate_decs"
  (fun () ->
    `!s e p. is_clock_io_mono (\s. evaluate_evaluate_decs s e p) s`)
  CHEAT_TAC;;

let is_clock_io_mono_extra = cake_theorem "is_clock_io_mono_extra"
  (fun () ->
    `(!s. is_clock_io_mono f s) ==>
      f s = (s',r) /\ ~(r = Rerr (Rabort Rtimeout_error)) ==>
          f (semanticPrimitives_state_clock_fupd (K
            (semanticPrimitives_state_clock s + extra)) s) =
            (semanticPrimitives_state_clock_fupd (K
            (semanticPrimitives_state_clock s' + extra)) s',r)`)
  CHEAT_TAC;;

let is_clock_io_mono_extra_mono =
  cake_theorem "is_clock_io_mono_extra_mono"
  (fun () ->
    `(!s. is_clock_io_mono f s) ==> io_events_mono
  (semanticPrimitives_state_ffi (FST (f s)))
  (semanticPrimitives_state_ffi
       (FST (f (semanticPrimitives_state_clock_fupd (K
         (semanticPrimitives_state_clock s + extra)) s))))`)
  CHEAT_TAC;;

(* HOL4 evaluatePropsScript.sml:407-411: ML code, not ported *)

let evaluate_add_to_clock = cake_theorem "evaluate_add_to_clock"
  (fun () ->
    `!(s:'ffi semanticPrimitives_state) env es s' r extra.
      evaluate s env es = (s',r) /\ ~(r = Rerr (Rabort
        Rtimeout_error)) ==>
      evaluate (semanticPrimitives_state_clock_fupd (K
        (semanticPrimitives_state_clock s + extra)) s) env es =
      (semanticPrimitives_state_clock_fupd (K
        (semanticPrimitives_state_clock s' + extra)) s',r)`)
  CHEAT_TAC;;

let evaluate_match_add_to_clock =
  cake_theorem "evaluate_match_add_to_clock"
  (fun () ->
    `!(s:'ffi semanticPrimitives_state) env v pes err_v s' r extra.
      evaluate_evaluate_match s env v pes err_v = (s',r) /\ ~(r =
        Rerr (Rabort Rtimeout_error)) ==>
      evaluate_evaluate_match (semanticPrimitives_state_clock_fupd
        (K (semanticPrimitives_state_clock s + extra)) s) env v pes
        err_v =
        (semanticPrimitives_state_clock_fupd (K
          (semanticPrimitives_state_clock s' + extra)) s',r)`)
  CHEAT_TAC;;

let list_result_eq_Rval = cake_theorem "list_result_eq_Rval[simp]"
  (fun () ->
    `list_result r = Rval r' <=> (?v. r' = [v] /\ r = Rval v)`)
  CHEAT_TAC;;

let list_result_eq_Rerr = cake_theorem "list_result_eq_Rerr[simp]"
  (fun () ->
    `list_result r = Rerr e <=> r = Rerr e`)
  CHEAT_TAC;;

let result_rel_list_result = cake_theorem "result_rel_list_result[simp]"
  (fun () ->
    `semanticPrimitivesProps_result_rel (LIST_REL R) Q (list_result r1)
  (list_result r2) <=>
     semanticPrimitivesProps_result_rel R Q r1 r2`)
  CHEAT_TAC;;

let list_result_inj = cake_theorem "list_result_inj"
  (fun () ->
    `list_result x = list_result y ==> x = y`)
  CHEAT_TAC;;

let evaluate_length = cake_theorem "evaluate_length"
  (fun () ->
    `(!(s:'ffi semanticPrimitives_state) e p s' r. evaluate s e p =
  (s',Rval r) ==> LENGTH r = LENGTH p) /\
     (!(s:'ffi semanticPrimitives_state) e v p er s' r.
       evaluate_evaluate_match s e v p er = (s',Rval r) ==> LENGTH r =
       1) /\
     (!(s:'ffi semanticPrimitives_state) e ds s' r.
       evaluate_evaluate_decs s e ds = (s',Rval r) ==> T)`)
  CHEAT_TAC;;

let evaluate_nil = cake_theorem "evaluate_nil[simp]"
  (fun () ->
    `!(s:'ffi semanticPrimitives_state) env. evaluate s env [] =
  (s,Rval [])`)
  CHEAT_TAC;;

let evaluate_sing = cake_theorem "evaluate_sing"
  (fun () ->
    `!(s:'ffi semanticPrimitives_state) env e s' vs. evaluate s env
  [e] = (s',Rval vs) ==> (?v. vs = [v])`)
  CHEAT_TAC;;

let evaluate_cons = cake_theorem "evaluate_cons"
  (fun () ->
    `!(s:'ffi semanticPrimitives_state) env e es.
      evaluate s env (e :: es) =
        (match evaluate s env [e] with (s',Rval vs) ->
         (match evaluate s' env es with (s'',Rval vs') ->
           (s'',Rval (vs ++ vs')) | err -> err) | err -> err)`)
  CHEAT_TAC;;

let evaluate_append = cake_theorem "evaluate_append"
  (fun () ->
    `!(s:'ffi semanticPrimitives_state) env xs ys.
      evaluate s env (xs ++ ys) =
        (match evaluate s env xs with (s',Rval vs) ->
         (match evaluate s' env ys with (s'',Rval vs') ->
           (s'',Rval (vs ++ vs')) | err -> err) | err -> err)`)
  CHEAT_TAC;;

let evaluate_decs_nil = cake_theorem "evaluate_decs_nil[simp]"
  (fun () ->
    `!(s:'ffi semanticPrimitives_state) env.
      evaluate_evaluate_decs s env [] = (s,Rval (mk_sem_env
        nsEmpty nsEmpty))`)
  CHEAT_TAC;;

let evaluate_decs_cons = cake_theorem "evaluate_decs_cons"
  (fun () ->
    `!(s:'ffi semanticPrimitives_state) env d ds.
      evaluate_evaluate_decs s env (d :: ds) =
        (match evaluate_evaluate_decs s env [d] with (s1,Rval env1)
          ->
         (match evaluate_evaluate_decs s1 (extend_dec_env env1
           env) ds with (s2,r) -> (s2,combine_dec_result env1 r) | err
           -> err) | err -> err)`)
  CHEAT_TAC;;

let evaluate_decs_append = cake_theorem "evaluate_decs_append"
  (fun () ->
    `!ds1 s env ds2.
       evaluate_evaluate_decs s env (ds1 ++ ds2) =
       (match evaluate_evaluate_decs s env ds1 with
         (s1,Rval env1) ->
           (match evaluate_evaluate_decs s1 (extend_dec_env env1
             env) ds2 with
              (s2,r) -> (s2,combine_dec_result env1 r)) |
                (s1,Rerr v7) -> (s1,Rerr v7))`)
  CHEAT_TAC;;

let evaluate_match_list_result =
  cake_theorem "evaluate_match_list_result"
  (fun () ->
    `evaluate_evaluate_match s e v p er = (s',r) ==>
     (?r'. r = list_result r')`)
  CHEAT_TAC;;

(* HOL4 evaluatePropsScript.sml:586-588: ML code, not ported *)

let evaluate_decs_add_to_clock =
  cake_theorem "evaluate_decs_add_to_clock"
  (fun () ->
    `!s e p s' r extra.
     evaluate_evaluate_decs s e p = (s',r) /\ ~(r = Rerr (Rabort
       Rtimeout_error)) ==>
     evaluate_evaluate_decs (semanticPrimitives_state_clock_fupd (K
       (semanticPrimitives_state_clock s + extra)) s) e p =
     (semanticPrimitives_state_clock_fupd (K
       (semanticPrimitives_state_clock s' + extra)) s',r)`)
  CHEAT_TAC;;

let add_lemma = cake_theorem "add_lemma[local]"
  (fun () ->
    `!(k:num) k'. ?extra. k = k' + extra \/ k' = k + extra`)
  CHEAT_TAC;;

let with_clock_ffi = cake_theorem "with_clock_ffi[local]"
  (fun () ->
    `semanticPrimitives_state_ffi
       (semanticPrimitives_state_clock_fupd (K k) s) =
         semanticPrimitives_state_ffi s`)
  CHEAT_TAC;;

let evaluate_decs_clock_determ =
  cake_theorem "evaluate_decs_clock_determ"
  (fun () ->
    `!s e p s1 r1 s2 r2 k1 k2.
      evaluate_evaluate_decs (semanticPrimitives_state_clock_fupd
        (K k1) s) e p = (s1,r1) /\
      evaluate_evaluate_decs (semanticPrimitives_state_clock_fupd
        (K k2) s) e p = (s2,r2) ==>
      (match (r1,r2) with (Rerr (Rabort Rtimeout_error),Rerr
        (Rabort Rtimeout_error)) ->
        T | (Rerr (Rabort Rtimeout_error),_1) ->
        k1 < k2 | (_2,Rerr (Rabort Rtimeout_error)) ->
        k2 < k1 | _3 -> semanticPrimitives_state_ffi
        s1 = semanticPrimitives_state_ffi s2 /\ r1 = r2)`)
  CHEAT_TAC;;

let evaluateProps_evaluate_add_to_clock_io_events_mono =
  cake_theorem "evaluate_add_to_clock_io_events_mono"
  (fun () ->
    `(!(s:'ffi semanticPrimitives_state) e d extra.
       io_events_mono (semanticPrimitives_state_ffi (FST (evaluate
         s e d))) (semanticPrimitives_state_ffi
       (FST (evaluate (semanticPrimitives_state_clock_fupd (K
         (semanticPrimitives_state_clock s + extra)) s) e d)))) /\
     (!(s:'ffi semanticPrimitives_state) e v d er extra.
       io_events_mono (semanticPrimitives_state_ffi (FST
         (evaluate_evaluate_match s e v d er)))
         (semanticPrimitives_state_ffi
       (FST (evaluate_evaluate_match
         (semanticPrimitives_state_clock_fupd (K
         (semanticPrimitives_state_clock s + extra)) s) e v d er))))`)
  CHEAT_TAC;;

let evaluate_decs_add_to_clock_io_events_mono =
  cake_theorem "evaluate_decs_add_to_clock_io_events_mono"
  (fun () ->
    `!s e d.
      io_events_mono (semanticPrimitives_state_ffi
      (FST (evaluate_evaluate_decs s e d)))
        (semanticPrimitives_state_ffi
      (FST (evaluate_evaluate_decs
        (semanticPrimitives_state_clock_fupd (K
        (semanticPrimitives_state_clock s + extra)) s) e d)))`)
  CHEAT_TAC;;

let evaluate_decs_ffi_mono_clock =
  cake_theorem "evaluate_decs_ffi_mono_clock"
  (fun () ->
    `!k1 k2 s e p.
      k1 <= k2 ==>
      io_events_mono (semanticPrimitives_state_ffi
      (FST (evaluate_evaluate_decs
        (semanticPrimitives_state_clock_fupd (K k1) s) e p)))
        (semanticPrimitives_state_ffi
      (FST (evaluate_evaluate_decs
        (semanticPrimitives_state_clock_fupd (K k2) s) e p)))`)
  CHEAT_TAC;;

(* HOL4 evaluatePropsScript.sml:693-712: code that the source has in
   a comment *)

let evaluate_next_type_stamp_mono =
  cake_theorem "evaluate_next_type_stamp_mono"
  (fun () ->
    `(evaluate (s:'ffi semanticPrimitives_state) env es = (s',res1) ==>
  semanticPrimitives_state_next_type_stamp
      s <= semanticPrimitives_state_next_type_stamp s') /\
     (evaluate_evaluate_match (s:'ffi semanticPrimitives_state) env
       v pes err_v = (s',res2) ==>
       semanticPrimitives_state_next_type_stamp
      s <= semanticPrimitives_state_next_type_stamp s') /\
     (evaluate_evaluate_decs (s:'ffi semanticPrimitives_state) env
       ds = (s',res3) ==> semanticPrimitives_state_next_type_stamp
      s <= semanticPrimitives_state_next_type_stamp s')`)
  CHEAT_TAC;;

let evaluate_next_exn_stamp_mono =
  cake_theorem "evaluate_next_exn_stamp_mono"
  (fun () ->
    `(evaluate (s:'ffi semanticPrimitives_state) env es = (s',res1) ==>
  semanticPrimitives_state_next_exn_stamp
      s <= semanticPrimitives_state_next_exn_stamp s') /\
     (evaluate_evaluate_match (s:'ffi semanticPrimitives_state) env
       v pes err_v = (s',res2) ==>
       semanticPrimitives_state_next_exn_stamp
      s <= semanticPrimitives_state_next_exn_stamp s') /\
     (evaluate_evaluate_decs (s:'ffi semanticPrimitives_state) env
       ds = (s',res3) ==> semanticPrimitives_state_next_exn_stamp
      s <= semanticPrimitives_state_next_exn_stamp s')`)
  CHEAT_TAC;;

(* HOL4 evaluatePropsScript.sml:744-746: a theorem that HOL4 states
   as the value of an ML expression: evaluate_case_eqs *)

let evaluate_set_next_stamps = cake_theorem "evaluate_set_next_stamps"
  (fun () ->
    `(!(s0:'a semanticPrimitives_state) env xs s1 res.
        evaluate s0 env xs = (s1,res) ==>
        (semanticPrimitives_state_next_type_stamp s1 =
          semanticPrimitives_state_next_type_stamp s0 ==>
           (!k. evaluate
             (semanticPrimitives_state_next_type_stamp_fupd (K k) s0)
             env xs =
               (semanticPrimitives_state_next_type_stamp_fupd (K k)
                 s1,res))) /\
        (semanticPrimitives_state_next_exn_stamp s1 =
          semanticPrimitives_state_next_exn_stamp s0 ==>
           (!k. evaluate
             (semanticPrimitives_state_next_exn_stamp_fupd (K k) s0) env
             xs =
               (semanticPrimitives_state_next_exn_stamp_fupd (K k)
                 s1,res)))) /\
     (!(s0:'a semanticPrimitives_state) env v pes errv s1 res.
        evaluate_evaluate_match s0 env v pes errv = (s1,res) ==>
        (semanticPrimitives_state_next_type_stamp s1 =
          semanticPrimitives_state_next_type_stamp s0 ==>
           (!k. evaluate_evaluate_match
             (semanticPrimitives_state_next_type_stamp_fupd (K k) s0)
             env v pes errv =
               (semanticPrimitives_state_next_type_stamp_fupd (K k)
                 s1,res))) /\
        (semanticPrimitives_state_next_exn_stamp s1 =
          semanticPrimitives_state_next_exn_stamp s0 ==>
           (!k. evaluate_evaluate_match
             (semanticPrimitives_state_next_exn_stamp_fupd (K k) s0) env
             v pes errv =
               (semanticPrimitives_state_next_exn_stamp_fupd (K k)
                 s1,res)))) /\
     (!(s0:'a semanticPrimitives_state) env ds s1 res.
        evaluate_evaluate_decs s0 env ds = (s1,res) ==>
        (semanticPrimitives_state_next_type_stamp s1 =
          semanticPrimitives_state_next_type_stamp s0 ==>
           (!k. evaluate_evaluate_decs
             (semanticPrimitives_state_next_type_stamp_fupd (K k) s0)
             env ds =
               (semanticPrimitives_state_next_type_stamp_fupd (K k)
                 s1,res))) /\
        (semanticPrimitives_state_next_exn_stamp s1 =
          semanticPrimitives_state_next_exn_stamp s0 ==>
           (!k. evaluate_evaluate_decs
             (semanticPrimitives_state_next_exn_stamp_fupd (K k) s0) env
             ds =
               (semanticPrimitives_state_next_exn_stamp_fupd (K
                 k) s1,res))))`)
  CHEAT_TAC;;

let call_FFI_return_unchanged = cake_theorem "call_FFI_return_unchanged"
  (fun () ->
    `call_FFI ffi s conf bytes = FFI_return ffi bytes' <=>
     (s = ffi_ExtCall (implode "") /\ bytes' = bytes)`)
  CHEAT_TAC;;

let evaluateProps_do_app_ffi_unchanged =
  cake_theorem "do_app_ffi_unchanged"
  (fun () ->
    `semanticPrimitives_do_app (refs,ffi) op vs = SOME ((refs',ffi),r)
  ==>
     (!outcome. ~(r = Rerr (Rabort (Rffi_error outcome)))) ==>
     (!ffi2. semanticPrimitives_do_app (refs,ffi2) op vs = SOME
       ((refs',ffi2),r))`)
  CHEAT_TAC;;

let evaluate_ffi_intro = cake_theorem "evaluate_ffi_intro"
  (fun () ->
    `(!(s) env e s' r.
        evaluate s env e = (s',r) /\ semanticPrimitives_state_ffi
        s' = semanticPrimitives_state_ffi s /\
        (!outcome. ~(r = Rerr (Rabort (Rffi_error outcome)))) ==>
        (!nffi.
        evaluate (semanticPrimitives_state_ffi_fupd (K nffi) s) env
          e = (semanticPrimitives_state_ffi_fupd (K nffi) s',r))) /\
     (!(s) env v pes errv s' r.
        evaluate_evaluate_match s env v pes errv = (s',r) /\
          semanticPrimitives_state_ffi
        s' = semanticPrimitives_state_ffi s /\
        (!outcome. ~(r = Rerr (Rabort (Rffi_error outcome)))) ==>
        (!nffi.
        evaluate_evaluate_match (semanticPrimitives_state_ffi_fupd
          (K nffi) s) env v pes errv =
           (semanticPrimitives_state_ffi_fupd (K nffi) s',r))) /\
     (!(s) env ds s' r.
        evaluate_evaluate_decs s env ds = (s',r) /\
          semanticPrimitives_state_ffi
        s' = semanticPrimitives_state_ffi s /\
        (!outcome. ~(r = Rerr (Rabort (Rffi_error outcome)))) ==>
        (!nffi.
        evaluate_evaluate_decs (semanticPrimitives_state_ffi_fupd
          (K nffi) s) env ds =
           (semanticPrimitives_state_ffi_fupd (K nffi) s',r)))`)
  CHEAT_TAC;;

let is_clock_io_mono_set_clock =
  cake_theorem "is_clock_io_mono_set_clock"
  (fun () ->
    `is_clock_io_mono f s ==>
      f s = (s',r) /\ ~(r = Rerr (Rabort Rtimeout_error)) ==>
        (?ck0. f (semanticPrimitives_state_clock_fupd (K ck0) s) =
        (semanticPrimitives_state_clock_fupd (K ck1) s',r))`)
  CHEAT_TAC;;

(* HOL4 evaluatePropsScript.sml:899-902: ML code, not ported *)

let evaluate_set_clock = cake_theorem "evaluate_set_clock"
  (fun () ->
    `!(s:'ffi semanticPrimitives_state) env exps s1 res.
        evaluate s env exps = (s1,res) /\ ~(res = Rerr (Rabort
          Rtimeout_error)) ==>
        (!ck. ?ck1. evaluate (semanticPrimitives_state_clock_fupd
          (K ck1) s) env exps =
                     (semanticPrimitives_state_clock_fupd (K ck)
                       s1,res))`)
  CHEAT_TAC;;

let evaluate_decs_set_clock = cake_theorem "evaluate_decs_set_clock"
  (fun () ->
    `!s env decs s1 res.
        evaluate_evaluate_decs s env decs = (s1,res) /\ ~(res =
          Rerr (Rabort Rtimeout_error)) ==>
        (!ck. ?ck1. evaluate_evaluate_decs
          (semanticPrimitives_state_clock_fupd (K ck1) s) env decs =
                     (semanticPrimitives_state_clock_fupd (K ck)
                       s1,res))`)
  CHEAT_TAC;;

let is_clock_io_mono_minimal = cake_theorem "is_clock_io_mono_minimal"
  (fun () ->
    `is_clock_io_mono f s ==>
      f s = (s',r) /\ semanticPrimitives_state_clock s' = 0 /\
          ~(r = Rerr (Rabort Rtimeout_error)) /\
            semanticPrimitives_state_clock s > k ==> (?s''. f
            (semanticPrimitives_state_clock_fupd (K k) s) = (s'',Rerr
            (Rabort Rtimeout_error)) /\
                 io_events_mono (semanticPrimitives_state_ffi
                   s'') (semanticPrimitives_state_ffi s'))`)
  CHEAT_TAC;;

(* HOL4 evaluatePropsScript.sml:937-938: ML code, not ported *)

let evaluate_minimal_clock = cake_theorem "evaluate_minimal_clock"
  (fun () ->
    `(!(s:'ffi semanticPrimitives_state) env es s' r k.
      evaluate s env es = (s',r) /\ semanticPrimitives_state_clock
      s' = 0 /\ ~(r = Rerr (Rabort Rtimeout_error)) /\
        semanticPrimitives_state_clock
      s > k ==>
      (?s''.
        evaluate (semanticPrimitives_state_clock_fupd (K k) s) env
          es =
        (s'',Rerr (Rabort Rtimeout_error)) /\
        io_events_mono (semanticPrimitives_state_ffi s'')
          (semanticPrimitives_state_ffi s')))`)
  CHEAT_TAC;;

let evaluate_match_minimal_clock =
  cake_theorem "evaluate_match_minimal_clock"
  (fun () ->
    `(!(s:'ffi semanticPrimitives_state) env v pes err_v s' r k.
      evaluate_evaluate_match s env v pes err_v = (s',r) /\
        semanticPrimitives_state_clock
      s' = 0 /\ ~(r = Rerr (Rabort Rtimeout_error)) /\
        semanticPrimitives_state_clock
      s > k ==>
      (?s''.
        evaluate_evaluate_match
          (semanticPrimitives_state_clock_fupd (K k) s) env v pes err_v
          =
        (s'',Rerr (Rabort Rtimeout_error)) /\
        io_events_mono (semanticPrimitives_state_ffi s'')
          (semanticPrimitives_state_ffi s')))`)
  CHEAT_TAC;;

let evaluate_set_init_clock = cake_theorem "evaluate_set_init_clock"
  (fun () ->
    `evaluate st env xs = (st',res) /\ ~(res = Rerr (Rabort
  Rtimeout_error)) ==>
     (!k. ?ck res1 st1.
     evaluate (semanticPrimitives_state_clock_fupd (K k) st) env xs
       = (st1,res1) /\
     (res1 = res /\ st1 = (semanticPrimitives_state_clock_fupd (K
       ck) st') \/
      res1 = Rerr (Rabort Rtimeout_error) /\
      io_events_mono (semanticPrimitives_state_ffi st1)
        (semanticPrimitives_state_ffi st')))`)
  CHEAT_TAC;;

let can_pmatch_all_EVERY = cake_theorem "can_pmatch_all_EVERY"
  (fun () ->
    `can_pmatch_all envC refs ps v <=>
     EVERY (\p. ~(semanticPrimitives_pmatch envC refs p v [] =
       Match_type_error)) ps`)
  CHEAT_TAC;;

let same_type_trans = cake_theorem "same_type_trans"
  (fun () ->
    `same_type t1 t2 /\ same_type t1 t3 ==> same_type t2 t3`)
  CHEAT_TAC;;

let evaluate_refs_length_mono = cake_theorem "evaluate_refs_length_mono"
  (fun () ->
    `(!(s:'ffi semanticPrimitives_state) env es s' r.
        evaluate s env es = (s',r) ==> LENGTH
          (semanticPrimitives_state_refs s) <= LENGTH
          (semanticPrimitives_state_refs s')) /\
     (!(s:'ffi semanticPrimitives_state) env v pes err_v s' r.
        evaluate_evaluate_match s env v pes err_v = (s',r) ==>
          LENGTH (semanticPrimitives_state_refs s) <= LENGTH
          (semanticPrimitives_state_refs s'))`)
  CHEAT_TAC;;

let combine_dec_result_eq_Rerr =
  cake_theorem "combine_dec_result_eq_Rerr"
  (fun () ->
    `combine_dec_result env r = Rerr e <=> r = Rerr e`)
  CHEAT_TAC;;

let eval_no_eval_simulation = cake_theorem "eval_no_eval_simulation"
  (fun () ->
    `(!(s:'ffi semanticPrimitives_state) env exps s' res.
        evaluate s env exps = (s',res) /\
          semanticPrimitives_state_eval_state
        s = NONE /\ ~(res = Rerr (Rabort Rtype_error)) ==>
          semanticPrimitives_state_eval_state
        s' = NONE /\
        evaluate (semanticPrimitives_state_eval_state_fupd (K es)
          s) env exps =
        (semanticPrimitives_state_eval_state_fupd (K es) s',res))
          /\
     (!(s:'ffi semanticPrimitives_state) env x pes err_x s' res.
        evaluate_evaluate_match s env x pes err_x = (s',res) /\
          semanticPrimitives_state_eval_state
        s = NONE /\ ~(res = Rerr (Rabort Rtype_error)) ==>
          semanticPrimitives_state_eval_state
        s' = NONE /\
        evaluate_evaluate_match
          (semanticPrimitives_state_eval_state_fupd (K es) s) env x pes
          err_x =
        (semanticPrimitives_state_eval_state_fupd (K es) s',res))
          /\
     (!(s:'ffi semanticPrimitives_state) env decs s' res.
        evaluate_evaluate_decs s env decs = (s',res) /\
          semanticPrimitives_state_eval_state
        s = NONE /\ ~(res = Rerr (Rabort Rtype_error)) ==>
          semanticPrimitives_state_eval_state
        s' = NONE /\
        evaluate_evaluate_decs
          (semanticPrimitives_state_eval_state_fupd (K es) s) env decs =
        (semanticPrimitives_state_eval_state_fupd (K es) s',res))`)
  CHEAT_TAC;;

let evaluate_ffi_etc_intro = cake_theorem "evaluate_ffi_etc_intro"
  (fun () ->
    `evaluate s0 env xs = (s1,res) /\
     (!outcome. ~(res = Rerr (Rabort (Rffi_error outcome)))) /\
       semanticPrimitives_state_ffi
     s1 = semanticPrimitives_state_ffi s0 /\
       semanticPrimitives_state_next_type_stamp
     s1 = semanticPrimitives_state_next_type_stamp s0 /\
       semanticPrimitives_state_next_exn_stamp
     s1 = semanticPrimitives_state_next_exn_stamp s0 /\
       semanticPrimitives_state_eval_state
     s0 = NONE /\ ~(res = Rerr (Rabort Rtype_error)) /\
       semanticPrimitives_state_refs
     s = semanticPrimitives_state_refs s0 ==>
     (?ck1 ck2. evaluate (semanticPrimitives_state_clock_fupd (K
       ck1) s) env xs =
       (semanticPrimitives_state_clock_fupd (K ck2)
         (semanticPrimitives_state_refs_fupd (K
         (semanticPrimitives_state_refs s1)) s),res))`)
  CHEAT_TAC;;

let same_type_sym = cake_theorem "same_type_sym"
  (fun () ->
    `same_type t1 t2 ==> same_type t2 t1`)
  CHEAT_TAC;;

let pmatch_not_type_error_EQ = cake_theorem "pmatch_not_type_error_EQ"
  (fun () ->
    `(~(semanticPrimitives_pmatch envC refs ast_Pany v acc =
  Match_type_error) <=> T) /\
     (~(semanticPrimitives_pmatch envC refs (ast_Pvar n) v acc =
       Match_type_error) <=> T) /\
     (~(semanticPrimitives_pmatch envC refs (ast_Pcon (SOME name)
       xs) v acc = Match_type_error) <=>
      (?ys t l stamp.
        v = semanticPrimitives_Conv (SOME t) ys /\
        nsLookup envC name = SOME (l,stamp) /\ LENGTH xs = l /\
        same_type stamp t /\
        (t = stamp ==> l = LENGTH ys /\
          ~(semanticPrimitives_pmatch_list envC refs xs ys acc =
          Match_type_error)))) /\
     (~(semanticPrimitives_pmatch envC refs (ast_Pcon NONE xs) v
       acc = Match_type_error) <=>
      (?ys. v = semanticPrimitives_Conv NONE ys /\ LENGTH xs =
        LENGTH ys /\ ~(semanticPrimitives_pmatch_list envC refs xs ys
        acc = Match_type_error))) /\
     (~(semanticPrimitives_pmatch_list envC refs [] [] acc =
       Match_type_error) <=> T) /\
     (~(semanticPrimitives_pmatch_list envC refs [] (v :: vs) acc =
       Match_type_error) <=> F) /\
     (~(semanticPrimitives_pmatch_list envC refs (p :: ps) [] acc =
       Match_type_error) <=> F) /\
     (~(semanticPrimitives_pmatch_list envC refs (p :: ps) (v ::
       vs) acc = Match_type_error) <=> ~(semanticPrimitives_pmatch envC
       refs p v acc = Match_type_error) /\
        (!a. semanticPrimitives_pmatch envC refs p v acc = No_match
          ==> ~(semanticPrimitives_pmatch_list envC refs ps vs acc =
          Match_type_error)) /\
        (!a. semanticPrimitives_pmatch envC refs p v acc = Match
          a ==> ~(semanticPrimitives_pmatch_list envC refs ps vs a =
          Match_type_error)))`)
  CHEAT_TAC;;

let do_app_ffi_mono = cake_theorem "do_app_ffi_mono"
  (fun () ->
    `semanticPrimitives_do_app (refs,(ffi:'ffi ffi_state)) op args =
  SOME ((refs',ffi'),r) ==>
      (?l. ffi_state_io_events ffi' = ffi_state_io_events ffi ++
        l)`)
  CHEAT_TAC;;

let do_app_SOME_ffi_same_oracle_state =
  cake_theorem "do_app_SOME_ffi_same_oracle_state"
  (fun () ->
    `semanticPrimitives_do_app (refs,(ffi:'ffi ffi_state)) op args =
  SOME ((refs',ffi'),r) ==>
     semanticPrimitives_do_app (refs,ffi_state_io_events_fupd (K l)
       ffi) op args =
     SOME ((refs',ffi_state_io_events_fupd (K (l ++ DROP (LENGTH
       (ffi_state_io_events ffi)) (ffi_state_io_events ffi')))
       ffi'),r)`)
  CHEAT_TAC;;

let evaluate_history_irrelevance =
  cake_theorem "evaluate_history_irrelevance"
  (fun () ->
    `(!(st:'ffi semanticPrimitives_state) env exp st' res.
       evaluate st env exp = (st',res) ==>
       (?new_io. ffi_state_io_events (semanticPrimitives_state_ffi
         st') = ffi_state_io_events (semanticPrimitives_state_ffi st) ++
         new_io /\
       (!l. evaluate (semanticPrimitives_state_ffi_fupd (K
         (ffi_state_io_events_fupd (K l) (semanticPrimitives_state_ffi
         st))) st) env exp =
       (semanticPrimitives_state_ffi_fupd (K
         (ffi_state_io_events_fupd (K (l ++ new_io))
         (semanticPrimitives_state_ffi st'))) st',res)))) /\
     (!(st:'ffi semanticPrimitives_state) env v pes err_v st' res.
       evaluate_evaluate_match st env v pes err_v = (st',res) ==>
       (?new_io. ffi_state_io_events (semanticPrimitives_state_ffi
         st') = ffi_state_io_events (semanticPrimitives_state_ffi st) ++
         new_io /\
       (!l. evaluate_evaluate_match
         (semanticPrimitives_state_ffi_fupd (K (ffi_state_io_events_fupd
         (K l) (semanticPrimitives_state_ffi st))) st) env
           v pes err_v =
       (semanticPrimitives_state_ffi_fupd (K
         (ffi_state_io_events_fupd (K (l ++ new_io))
         (semanticPrimitives_state_ffi st'))) st',res)))) /\
     (!(st:'ffi semanticPrimitives_state) env ds st' res.
       evaluate_evaluate_decs st env ds = (st',res) ==>
       (?new_io. ffi_state_io_events (semanticPrimitives_state_ffi
         st') = ffi_state_io_events (semanticPrimitives_state_ffi st) ++
         new_io /\
       (!l. evaluate_evaluate_decs
         (semanticPrimitives_state_ffi_fupd (K (ffi_state_io_events_fupd
         (K l) (semanticPrimitives_state_ffi st))) st) env ds =
       (semanticPrimitives_state_ffi_fupd (K
         (ffi_state_io_events_fupd (K (l ++ new_io))
         (semanticPrimitives_state_ffi st'))) st',res))))`)
  CHEAT_TAC;;

let evaluate_add_history = cake_theorem "evaluate_add_history"
  (fun () ->
    `(!(st:'ffi semanticPrimitives_state) env exp st' res.
        evaluate (semanticPrimitives_state_ffi_fupd (K
          (ffi_state_io_events_fupd (K []) (semanticPrimitives_state_ffi
          st))) st) env exp = (st',res) ==>
        evaluate st env exp =
        (semanticPrimitives_state_ffi_fupd (K
          (ffi_state_io_events_fupd (K (ffi_state_io_events
          (semanticPrimitives_state_ffi st) ++ ffi_state_io_events
          (semanticPrimitives_state_ffi st')))
          (semanticPrimitives_state_ffi st'))) st',res)) /\
     (!(st:'ffi semanticPrimitives_state) env v pes err_v st' res.
        evaluate_evaluate_match (semanticPrimitives_state_ffi_fupd
          (K (ffi_state_io_events_fupd (K [])
          (semanticPrimitives_state_ffi st))) st) env v pes err_v =
          (st',res) ==>
        evaluate_evaluate_match st env v pes err_v =
        (semanticPrimitives_state_ffi_fupd (K
          (ffi_state_io_events_fupd (K (ffi_state_io_events
          (semanticPrimitives_state_ffi st) ++ ffi_state_io_events
          (semanticPrimitives_state_ffi st')))
          (semanticPrimitives_state_ffi st'))) st',res))`)
  CHEAT_TAC;;

let apps_append = cake_theorem "Apps_append"
  (fun () ->
    `!xs ys f. Apps f (xs ++ ys) = Apps (Apps f xs) ys`)
  CHEAT_TAC;;

let evaluate_Apps_Rerr = cake_theorem "evaluate_Apps_Rerr"
  (fun () ->
    `!xs f (st:'ffi semanticPrimitives_state) env s1 e.
       evaluate st env xs = (s1,Rerr e) ==>
       evaluate st env [Apps f (REVERSE xs)] = (s1,Rerr e)`)
  CHEAT_TAC;;

let evaluate_Apps_Funs = cake_theorem "evaluate_Apps_Funs"
  (fun () ->
    `!l x ns vs (st:'ffi semanticPrimitives_state) s1 s2 env env1 e.
       evaluate st env l = (s1,Rval vs) /\
       evaluate s1 env [x] = (s2,Rval [semanticPrimitives_Closure
         env1 (HD ns) (Funs (TL ns) e)]) /\
       LENGTH l = LENGTH ns /\ ~(ns = []) /\ LENGTH ns <=
         semanticPrimitives_state_clock s2 ==>
       evaluate st env [Apps x (REVERSE l)] =
       evaluate
         (semanticPrimitives_state_clock_fupd (K
           (semanticPrimitives_state_clock s2 - LENGTH ns)) s2)
         (sem_env_v_fupd (K (nsAppend (alist_to_ns (ZIP (REVERSE
           ns) vs)) (sem_env_v env1))) env1) [e]`)
  CHEAT_TAC;;

let evaluate_Apps_f_err = cake_theorem "evaluate_Apps_f_err"
  (fun () ->
    `!xs vs (st:'ffi semanticPrimitives_state) envs1 f s1 s2.
       evaluate st env xs = (s1,Rval vs) /\
       evaluate s1 env [f] = (s2,Rerr r) ==>
       evaluate st env [Apps f (REVERSE xs)] = (s2,Rerr r)`)
  CHEAT_TAC;;

let evaluate_Apps_Funs_timeout =
  cake_theorem "evaluate_Apps_Funs_timeout"
  (fun () ->
    `!l x ns vs (st:'ffi semanticPrimitives_state) s1 s2 env env1 e.
       evaluate st env l = (s1,Rval vs) /\
       evaluate s1 env [x] = (s2,Rval [semanticPrimitives_Closure
         env1 (HD ns) (Funs (TL ns) e)]) /\
       LENGTH l = LENGTH ns /\ ~(ns = []) /\
         semanticPrimitives_state_clock s2 < LENGTH ns ==>
       evaluate st env [Apps x (REVERSE l)] =
         (semanticPrimitives_state_clock_fupd (K 0) s2,Rerr
           (Rabort Rtimeout_error))`)
  CHEAT_TAC;;

let evaluate_Apps = cake_theorem "evaluate_Apps"
  (fun () ->
    `!xs (st:'ffi semanticPrimitives_state) env s1 s2 vs.
       evaluate st env xs = (s1,Rval vs) /\
       LENGTH xs = SUC (LENGTH ns) /\
       nsLookup (sem_env_v env) n = SOME clos_v /\
       semanticPrimitives_do_opapp [clos_v; LAST vs] = SOME
         (env1,Funs ns e) ==>
       evaluate st env [Apps (ast_Var n) (REVERSE xs)] =
       (if semanticPrimitives_state_clock s1 < LENGTH xs then
         (semanticPrimitives_state_clock_fupd (K 0) s1,Rerr (Rabort
           Rtimeout_error)) else
         evaluate
           (semanticPrimitives_state_clock_fupd (K
             (semanticPrimitives_state_clock s1 - LENGTH xs)) s1)
           (sem_env_v_fupd (K (nsAppend (alist_to_ns (ZIP
             (REVERSE ns) (BUTLAST vs))) (sem_env_v env1))) env1) [e])`)
  CHEAT_TAC;;
