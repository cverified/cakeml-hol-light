(* ======================================================== *)
(*  cfApp: ported from HOL4's
    characteristic/cfAppScript.sml
    A definition theory, with 7 definitions and 37 theorems.  Needed
    by 17 files of the port.  *)
(* ======================================================== *)

(*
  App: [app] is used to give a specification for the application of a
  value to one or multiple value arguments. It is in particular used
  in cf to abstract from the concrete representation of closures.
*)

needs "basis/pure/mlstring.ml";;
needs "characteristic/cfFFIType.ml";;
needs "characteristic/cfHeaps.ml";;
needs "characteristic/cfHeapsBase.ml";;
needs "characteristic/cfNormalise.ml";;
needs "characteristic/cfStore.ml";;
needs "lib/indexedLists.ml";;
needs "lib/lprefix_lub.ml";;
needs "lib/set_sep.ml";;
needs "semantics/evaluate.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/proofs/evaluateProps.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "translator/ml_translator.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "cfApp"
  ["cfHeaps"; "cfHeapsBase"; "cfNormalise"; "cfStore"; "evaluate";
   "evaluateProps"; "semanticPrimitives"];;

let _ = do_list hide_constant ["fv"];;

(* HOL4 cfAppScript.sml:13: the type abbreviation state, which the port
   expands *)

let evaluate_ck_def = new_definition
  `evaluate_ck ck (st:'ffi cfApp_state) = evaluate
  (semanticPrimitives_state_clock_fupd (K ck) st)`;;

(* HOL4 cfAppScript.sml:19-23: the definition *)

let evaluate_to_heap_def = new_definition
  `evaluate_to_heap st env exp p heap (r:res) <=>
     (match r with cfHeapsBase_Val v -> (?ck st'. evaluate_ck ck st env
       [exp] = (st',Rval [v]) /\ semanticPrimitives_state_next_type_stamp
                          st' = semanticPrimitives_state_next_type_stamp st
                            /\ semanticPrimitives_state_next_exn_stamp
                          st' = semanticPrimitives_state_next_exn_stamp st
                            /\
                          st2heap p st' = heap)
     | cfHeapsBase_Exn e -> (?ck st'. evaluate_ck ck st env [exp] =
       (st',Rerr (Rraise e)) /\ semanticPrimitives_state_next_type_stamp
                          st' = semanticPrimitives_state_next_type_stamp st
                            /\ semanticPrimitives_state_next_exn_stamp
                          st' = semanticPrimitives_state_next_exn_stamp st
                            /\
                          st2heap p st' = heap)
     | cfHeapsBase_FFIDiv name conf bytes -> (?ck st'.
       evaluate_ck ck st env [exp] = (st',Rerr (Rabort (Rffi_error
         (Final_event (ffi_ExtCall name) conf bytes FFI_diverged))))
         /\ semanticPrimitives_state_next_type_stamp
       st' = semanticPrimitives_state_next_type_stamp st
         /\ semanticPrimitives_state_next_exn_stamp
       st' = semanticPrimitives_state_next_exn_stamp st /\
       st2heap p st' = heap)
     | cfHeapsBase_Div io ->
                 (
                  // all clocks produce timeout
                  !ck. ?st'. evaluate_ck ck st env [exp] =
                       (st',Rerr (Rabort Rtimeout_error))) /\
                 // io is the limit of the io_events of all states
                 lprefix_lub (IMAGE (\ck. sptree_fromList
                   (ffi_state_io_events (semanticPrimitives_state_ffi (FST
                   (evaluate_ck ck st env [exp])))))
                              UNIV)
                              io)`;;

(* [app_basic]: application with one argument *)
let app_basic_def = new_definition
  `app_basic (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
  list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list)
  (f:semanticPrimitives_v) (x:semanticPrimitives_v) (H:(heap_part->bool)->bool)
  (Q:res->(heap_part->bool)->bool) =
     (!(h_i:heap_part->bool) (h_k:heap_part->bool) (st:'ffi
       semanticPrimitives_state).
       SPLIT (st2heap p st) (h_i,h_k) ==> H h_i ==>
       (?env exp (r:res) (h_f:heap_part->bool) (h_g:heap_part->bool) heap.
         SPLIT3 heap (h_f,h_k,h_g) /\
         semanticPrimitives_do_opapp [f; x] = SOME (env,exp) /\
         Q r h_f /\ evaluate_to_heap st env exp p heap r))`;;

(* [local] *)
let app_basic_local = prove
 (`!f x. is_local (app_basic p f x)`,
  CHEAT_TAC);;

(* [app]: n-ary application *)
let app_def,app_ind = define_guess
  `app x1 f x3 H Q =
   match (x1,f,x3,H,Q) with
     ((p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
       list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option))
       list),(f:semanticPrimitives_v),([]:semanticPrimitives_v
       list),(H:(heap_part->bool)->bool),(Q:res->(heap_part->bool)->bool)) -> F
   | ((p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
     list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option))
     list),f,[x],H,Q) -> app_basic p f x H Q
   | ((p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
     list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list),f,CONS
     x xs,H,Q) ->
     app_basic p f x H
       (POSTv (\g. SEP_EXISTS (\H'. H' * cond (app p g xs H' Q))))`;;

let app_alt_ind = prove
 (`!f xs x H Q. ~(xs = []) ==>
     app (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
       list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list) f
       (APPEND xs [x]) H Q =
     app (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
       list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list) f xs
       H
       (POSTv (\g. SEP_EXISTS (\H'. H' * cond (app_basic p g x H' Q))))`,
  CHEAT_TAC);;

let app_alt_ind_w = prove
 (`!f xs x H Q.
     app (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
       list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list) f
       (APPEND xs [x]) H Q ==> ~(xs = []) ==>
     app (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
       list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list) f xs
       H
       (POSTv (\g. SEP_EXISTS (\H'. H' * cond (app_basic
         (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
         list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list) g
         x H' Q))))`,
  CHEAT_TAC);;

let app_ge_2_unfold = prove
 (`!f x xs H Q. ~(xs = []) ==>
      app (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
        list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list) f
        (CONS x xs) H Q =
      app_basic p f x H (POSTv (\g. SEP_EXISTS (\H'. H' * cond (app p g xs
        H' Q))))`,
  CHEAT_TAC);;

let app_ge_2_unfold_extens = prove
 (`!f x xs. ~(xs = []) ==>
      app (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
        list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list) f
        (CONS x xs) =
      (\H Q. app_basic p f x H (POSTv (\g. SEP_EXISTS (\H'. H' * cond (app
        p g xs H' Q)))))`,
  CHEAT_TAC);;

(* Weaken-frame-gc for [app]; auxiliary lemma for [app_local] *)

let app_wgframe = prove
 (`!f xs H H1 H2 Q1 Q.
      app (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
        list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list) f xs
        H1 Q1 ==> SEP_IMP H (H1 * H2) ==> SEP_IMPPOST (STARPOST Q1 H2)
        (STARPOST Q GC) ==>
      app p f xs H Q`,
  CHEAT_TAC);;

let app_weaken = prove
 (`!f xs H Q Q'.
      app (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
        list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list) f xs
        H Q ==> SEP_IMPPOST Q Q' ==>
      app p f xs H Q'`,
  CHEAT_TAC);;

let app_local = prove
 (`!f xs. ~(xs = []) ==> is_local (app
  (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8 list->word8
  list->ffi->(ffi cfHeapsBase_ffi_result) option)) list) f xs)`,
  CHEAT_TAC);;

(* [curried (p:'ffi ffi_proj) n f] states that [f] is curried [n] times *)
let curried_def,curried_ind = define_guess
  `curried (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
  list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list) (n:num)
  (f:semanticPrimitives_v) =
     match n with 0 -> F
      | SUC 0 -> T
      | SUC n ->
        (!x. app_basic (p:('ffi->(mlstring,ffi)fmap)#(mlstring
          list#(mlstring->word8 list->word8 list->ffi->(ffi
          cfHeapsBase_ffi_result) option)) list) f x emp
              (POSTv (\g. cond (curried
                (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
                list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option))
                list) n g /\
                   (!xs H Q.
                     LENGTH xs = n ==>
                     app (p:('ffi->(mlstring,ffi)fmap)#(mlstring
                       list#(mlstring->word8 list->word8 list->ffi->(ffi
                       cfHeapsBase_ffi_result) option)) list) f (CONS x xs) H Q
                       ==>
                     app (p:('ffi->(mlstring,ffi)fmap)#(mlstring
                       list#(mlstring->word8 list->word8 list->ffi->(ffi
                       cfHeapsBase_ffi_result) option)) list) g xs H Q)))))`;;

let curried_ge_2_unfold = prove
 (`!n f.
      n > 1 ==>
      curried (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
        list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list) n f
        =
      (!x. app_basic p f x emp
            (POSTv (\g. cond (curried p (PRE n) g /\
                 (!xs H Q.
                   LENGTH xs = PRE n ==>
                   app p f (CONS x xs) H Q ==> app p g xs H Q)))))`,
  CHEAT_TAC);;

let app_basic_SEP_EXISTS = prove
 (`app_basic p f h (SEP_EXISTS (\x. P x)) q <=> (!x. app_basic p f h (P x) q)`,
  CHEAT_TAC);;

let app_SEP_EXISTS = prove
 (`!args p f q P.
     app p f args (SEP_EXISTS (\x. P x)) q <=> (!x. app p f args (P x) q)`,
  CHEAT_TAC);;

(* app_over_app / app_over_take *)

(** When [curried n f] holds and the number of the arguments [xs] is less than
    [n], then [app f xs] is a function [g] such that [app g ys] has the same
    behavior as [app f (xs++ys)]. *)
(*
val app_partial = Q.prove (
  `!n xs f. curried (p:'ffi ffi_proj) n f ==> (0 < LENGTH xs /\ LENGTH xs < n) ==>
    app (p:'ffi ffi_proj) f xs emp (\g. cond (
      curried (p:'ffi ffi_proj) (n - LENGTH xs) g /\
      !ys H Q. (LENGTH xs + LENGTH ys = n) ==>
        app (p:'ffi ffi_proj) f (xs ++ ys) H Q ==> app (p:'ffi ffi_proj) g ys H Q))`,
  completeInduct_on `n` \\ Cases_on `n`
  THEN1 (rpt strip_tac \\ fs [])

  THEN1 (
    Cases_on `xs` \\ rpt strip_tac \\ fs [] \\
    rename1 `x::zs` \\ rename1 `LENGTH zs < n` \\
    Cases_on `zs` \\ fs []

    THEN1 (
      (* xs = x :: zs = [x] *)
      fs [app_def] \\ ...
    )
    THEN1 (
      (* xs = x :: zs = [x::y::t] *)
      rename1 `x::y::t` \\ fs [app_def] \\ ..
    )
  )
)
*)

(*------------------------------------------------------------------*)
(** Packaging *)

(* [spec (p:'ffi ffi_proj) f n P] asserts that [curried (p:'ffi ffi_proj) f n] is true and
that [P] is a valid specification for [f]. Useful for conciseness and
tactics. *)
let spec_def = new_definition
  `spec (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
  list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list) f n P =
  (curried (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
  list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list) n f
  /\ P)`;;

(*------------------------------------------------------------------*)
(* Relating [app] to [_ --> _] from the translator *)

let app_basic_weaken = prove
 (`(!x v. P x v ==> Q x v) ==>
    (app_basic p v v1 x P ==>
     app_basic p v v1 x Q)`,
  CHEAT_TAC);;

(* TODO: move to appropriate locations *)

(* FFI_part_NOT_IN_store2heap *)
let cfApp_FFI_part_NOT_IN_store2heap = prove
 (`~(cfHeapsBase_FFI_part x1 x2 x3 x4 IN store2heap refs)`,
  CHEAT_TAC);;

let FFI_full_NOT_IN_store2heap = prove
 (`~(cfHeapsBase_FFI_full x1 IN store2heap refs)`,
  CHEAT_TAC);;

let FFI_split_NOT_IN_store2heap = prove
 (`~(cfHeapsBase_FFI_split IN store2heap refs)`,
  CHEAT_TAC);;

let store2heap_aux_MAPi = prove
 (`!n s. store2heap_aux n s = set_of_list (MAPi (\i v. cfHeapsBase_Mem (n +
  i) v) s)`,
  CHEAT_TAC);;

let store2heap_MAPi = prove
 (`store2heap s = set_of_list (MAPi cfHeapsBase_Mem s)`,
  CHEAT_TAC);;

let store2heap_aux_append_many = prove
 (`!s n x.
    store2heap_aux n (APPEND s x) =
    store2heap_aux (n + LENGTH s) x UNION store2heap_aux n s`,
  CHEAT_TAC);;

let store2heap_append_many = prove
 (`!s x.
    store2heap (APPEND s x) = store2heap s UNION store2heap_aux (LENGTH s)
      x`,
  CHEAT_TAC);;

let st2heap_with_refs_append = prove
 (`st2heap p (semanticPrimitives_state_refs_fupd (K (APPEND r1 r2)) st) =
   st2heap p (semanticPrimitives_state_refs_fupd (K r1) st) UNION
     store2heap_aux (LENGTH r1) r2`,
  CHEAT_TAC);;

let POSTv_cond = prove
 (`(POSTv (\v. &(f v))) r h <=> (?v. r = cfHeapsBase_Val v /\ f v /\ h = {})`,
  CHEAT_TAC);;

(* HOL4 cfAppScript.sml:363-364: ML code, not ported *)

let SPLIT_st2heap_length_leq = prove
 (`SPLIT (st2heap p s') (st2heap p s,h_g) /\
    LENGTH (semanticPrimitives_state_refs s) <= LENGTH
      (semanticPrimitives_state_refs s') /\ semanticPrimitives_state_ffi s' =
      semanticPrimitives_state_ffi s ==> semanticPrimitives_state_refs
    s <<= semanticPrimitives_state_refs s'`,
  CHEAT_TAC);;

(* [local] *)
let forall_cases = prove
 (`(!x. P x) <=> (!x1 x2. P (cfHeapsBase_Mem x1 x2)) /\
                   (P cfHeapsBase_FFI_split) /\
                   (!x3 x4 x2 x1. P (cfHeapsBase_FFI_part x1 x2 x3 x4)) /\
                   (!x1. P (cfHeapsBase_FFI_full x1))`,
  CHEAT_TAC);;

(* [local] *)
let SPLIT_UNION_IMP_SUBSET = prove
 (`SPLIT x (y UNION y1,y2) ==> y1 SUBSET x`,
  CHEAT_TAC);;

(* [local] *)
let FILTER_ffi_has_index_in_EQ_NIL = prove
 (`~(MEM n xs) /\ ALL (ffi_has_index_in xs) ys ==>
     FILTER (ffi_has_index_in [n]) ys = []`,
  CHEAT_TAC);;

(* [local] *)
let FILTER_ffi_has_index_in_MEM = prove
 (`!ys zs xs x.
       MEM x xs /\
       FILTER (ffi_has_index_in xs) ys = FILTER (ffi_has_index_in xs) zs ==>
       FILTER (ffi_has_index_in [x]) ys = FILTER (ffi_has_index_in [x]) zs`,
  CHEAT_TAC);;

(* [local] *)
let LENGTH_FILTER_EQ_IMP_EMPTY = prove
 (`!xs l.
       (!io_ev. MEM io_ev l ==>
         (?s bs bs'. io_ev = IO_event (ffi_ExtCall s) bs bs')) /\
       (!n. LENGTH (FILTER (ffi_has_index_in [n]) (APPEND xs l)) =
            LENGTH (FILTER (ffi_has_index_in [n]) xs)) ==>
       l = []`,
  CHEAT_TAC);;

(* [local] *)
let IN_DISJOINT_LEMMA1 = prove
 (`!s. x IN h_g /\ DISJOINT s h_g ==> ~(x IN s)`,
  CHEAT_TAC);;

(* [local] *)
let FFI_part_EXISTS = prove
 (`parts_ok s1 (p0,p1) /\ parts_ok s2 (p0,p1) /\
     cfHeapsBase_FFI_part x1 x2 x3 x4 IN ffi2heap (p0,p1) s1 ==>
     (?y1 y2 y4. cfHeapsBase_FFI_part y1 y2 x3 y4 IN ffi2heap (p0,p1) s2)`,
  CHEAT_TAC);;

(* [local] *)
let ALL_DISTINCT_FLAT_MEM_IMP = prove
 (`!p1 x x2 y2.
       ALL_DISTINCT (FLAT (MAP FST p1)) /\ ~(x = []) /\
       MEM (x,x2) p1 /\ MEM (x,y2) p1 ==> x2 = y2`,
  CHEAT_TAC);;

(* [local] *)
let FFI_part_11 = prove
 (`parts_ok s1 (p0,p1) /\ parts_ok s2 (p0,p1) /\
     cfHeapsBase_FFI_part x1 x2 x3 x4 IN ffi2heap (p0,p1) s1 /\
     cfHeapsBase_FFI_part y1 y2 x3 y4 IN ffi2heap (p0,p1) s1 ==>
     x1 = y1 /\ x2 = y2 /\ x4 = y4`,
  CHEAT_TAC);;

let SPLIT_st2heap_ffi = prove
 (`SPLIT (st2heap p st') (st2heap p st,h_g) ==>
   (!n. FILTER (ffi_has_index_in [n]) (ffi_state_io_events
     (semanticPrimitives_state_ffi st')) =
       FILTER (ffi_has_index_in [n]) (ffi_state_io_events
         (semanticPrimitives_state_ffi st)))`,
  CHEAT_TAC);;

let Arrow_IMP_app_basic = prove
 (`(Arrow a b) f v ==>
     (!x v1.
       a x v1 ==>
       app_basic (p:('ffi->(mlstring,ffi)fmap)#(mlstring
         list#(mlstring->word8 list->word8 list->ffi->(ffi
         cfHeapsBase_ffi_result) option)) list) v v1 emp (POSTv (\v. &(b (f
         x) v))))`,
  CHEAT_TAC);;

let do_app_io_events_ExtCall = prove
 (`semanticPrimitives_do_app (refs,ffi) op vs = SOME ((refs',ffi'),r) ==>
     (?l. ffi_state_io_events ffi' = APPEND (ffi_state_io_events ffi) l /\
       (!io_ev. MEM io_ev l ==>
         (?s bs bs'. io_ev = IO_event (ffi_ExtCall s) bs bs')))`,
  CHEAT_TAC);;

let evaluate_ExtCall = prove
 (`(!(st:'ffi semanticPrimitives_state) env exp l io_ev.
     !st' res. evaluate st env exp = (st',res) /\ ffi_state_io_events
       (semanticPrimitives_state_ffi
       st') = APPEND (ffi_state_io_events (semanticPrimitives_state_ffi st))
         l /\
       MEM io_ev l ==>
         (?s bs bs'.
           io_ev = IO_event (ffi_ExtCall s) bs bs')) /\
   (!(st:'ffi semanticPrimitives_state) env v pes err_v st' res l io_ev.
     evaluate_evaluate_match st env v pes err_v = (st',res)
       /\ ffi_state_io_events (semanticPrimitives_state_ffi
        st') = APPEND (ffi_state_io_events (semanticPrimitives_state_ffi
          st)) l /\
        MEM io_ev l ==>
         (?s bs bs'.
           io_ev = IO_event (ffi_ExtCall s) bs bs')) /\
   (!(st:'ffi semanticPrimitives_state) env d st' res l io_ev.
     evaluate_evaluate_decs st env d = (st',res) /\ ffi_state_io_events
       (semanticPrimitives_state_ffi
     st') = APPEND (ffi_state_io_events (semanticPrimitives_state_ffi st)) l
       /\
         MEM io_ev l ==>
           (?s bs bs'.
             io_ev = IO_event (ffi_ExtCall s) bs bs'))`,
  CHEAT_TAC);;

let app_basic_IMP_Arrow = prove
 (`(!x v1. a x v1 ==> app_basic p v v1 emp (POSTv (\v. cond (b (f x) v)))) ==>
   Arrow a b f v`,
  CHEAT_TAC);;
(* use evaluate to prove st1.io_events = st2.io_events ++ [ExtCall...] *)

(* Arrow_eq_app_basic *)
let arrow_eq_app_basic = prove
 (`Arrow a b f fv <=> (!x xv. a x xv ==> app_basic p fv xv emp (POSTv (\v'.
  &(b (f x) v'))))`,
  CHEAT_TAC);;

(* and the names it reads as variables are constants again *)
let _ = do_list unhide_constant
  ["fv"];;

(* and the interface *)
let _ = unhide_overloads ();;
