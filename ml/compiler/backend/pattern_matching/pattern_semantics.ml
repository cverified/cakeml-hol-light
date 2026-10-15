(* ======================================================== *)
(*  pattern_semantics: ported from HOL4's
    compiler/backend/pattern_matching/pattern_semanticsScript.sml  *)
(* ======================================================== *)

(*
  The syntax and semantics of the input and output to the
  pattern-match compiler.
*)

needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/bvi_tailrec.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/pattern_matching/pattern_common.ml";;
needs "compiler/backend/reg_alloc/reg_alloc.ml";;
needs "compiler/backend/word_depth.ml";;
needs "semantics/ast.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/semanticPrimitives.ml";;

new_type_abbrev("kind",`: num`);;
new_type_abbrev("pattern_semantics_tag",`: num`);;
new_type_abbrev("siblings",`: ((num#num) list) option`);;

(* input syntax *)

let pattern_semantics_pat_INDUCT,pattern_semantics_pat_RECURSION =
  define_datatype
  "pattern_semantics_pat = pattern_semantics_Any | \
   pattern_semantics_Cons ((num#((num#num) list) option) option) \
   (pattern_semantics_pat list) | pattern_semantics_Or \
   (pattern_semantics_pat) (pattern_semantics_pat) | \
   pattern_semantics_Lit (lit) | pattern_semantics_Ref \
   (pattern_semantics_pat)";;
hol4_overload "Any" "pattern_semantics_Any";;
hol4_overload "Cons" "pattern_semantics_Cons";;
hol4_overload "Or" "pattern_semantics_Or";;
hol4_overload "Lit" "pattern_semantics_Lit";;
hol4_overload "Ref" "pattern_semantics_Ref";;

(* output syntax *)

let dTest_INDUCT,dTest_RECURSION = define_datatype
  "dTest = pattern_semantics_TagLenEq (num) (num) | \
   pattern_semantics_LitEq (lit)";;
hol4_overload "TagLenEq" "pattern_semantics_TagLenEq";;

let dGuard_INDUCT,dGuard_RECURSION = define_datatype
  "dGuard = pattern_semantics_PosTest (position) (dTest) | \
   pattern_semantics_Not (dGuard) | pattern_semantics_Conj (dGuard) \
   (dGuard) | pattern_semantics_Disj (dGuard) (dGuard) | \
   pattern_semantics_True";;
hol4_overload "Not" "pattern_semantics_Not";;

let dTree_INDUCT,dTree_RECURSION = define_datatype
  "dTree = pattern_semantics_Leaf (num) | pattern_semantics_Fail | \
   pattern_semantics_TypeFail | pattern_semantics_If (dGuard) (dTree) \
   (dTree)";;
hol4_overload "Leaf" "pattern_semantics_Leaf";;
hol4_overload "Fail" "pattern_semantics_Fail";;
hol4_overload "If" "pattern_semantics_If";;

(* semantic values *)

let term_INDUCT,term_RECURSION = define_datatype
  "term = pattern_semantics_Term (num option) (term list) | \
   pattern_semantics_Litv (lit) | pattern_semantics_RefPtr (num) | \
   pattern_semantics_Other";;
hol4_overload "Litv" "pattern_semantics_Litv";;
hol4_overload "RefPtr" "pattern_semantics_RefPtr";;
hol4_overload "Other" "pattern_semantics_Other";;

(* semantics of input *)
let is_sibling_def = cake_define
  `is_sibling x NONE = T /\
   is_sibling x (SOME l) = MEM x l`;;

(* HOL4 termination: *)
let pmatch_def = cake_define_wf
  `MEASURE (\x. match x with INL (r,p,_5) -> pat_size p | INR (r,ps,_6)
  -> list_size pat_size ps)`
  `pattern_semantics_pmatch refs ps t =
        match (ps,t) with
          (Any,t) -> PMatchSuccess
        | ((Lit l),(Litv l')) ->
        if ~lit_same_type l l' then PTypeFailure else
        if l = l' then PMatchSuccess else PMatchFailure
        | ((Cons (SOME (tag,siblings)) pargs),(pattern_semantics_Term
          (SOME t) targs)) ->
       if tag = t /\ LENGTH pargs = LENGTH targs then
         pattern_semantics_pmatch_list refs pargs targs else
       if is_sibling (t,LENGTH targs) siblings then PMatchFailure
         else PTypeFailure
        | ((Cons NONE pargs),(pattern_semantics_Term NONE targs)) ->
       pattern_semantics_pmatch_list refs pargs targs
        | ((Ref p),(RefPtr r)) ->
       match FLOOKUP refs r with NONE -> PTypeFailure | SOME v ->
         pattern_semantics_pmatch refs p v
        | ((Or p1 p2),t) ->
       match pattern_semantics_pmatch refs p1 t with
          PMatchSuccess -> (match pattern_semantics_pmatch refs p2 t
            with
                              PTypeFailure -> PTypeFailure | _1 ->
                                PMatchSuccess) | PMatchFailure ->
                                pattern_semantics_pmatch refs p2 t |
                                PTypeFailure -> PTypeFailure
        | (_2,_3) -> PTypeFailure
        | ([],[]) -> PMatchSuccess
        | ([],ts) -> PTypeFailure
        | (ps,[]) -> PTypeFailure
        | ((p :: ps),(t :: ts)) ->
       match pattern_semantics_pmatch refs p t with
         PMatchSuccess -> pattern_semantics_pmatch_list refs ps ts |
           PMatchFailure -> (match pattern_semantics_pmatch_list refs ps
           ts with
                              PTypeFailure -> PTypeFailure | _4 ->
                                PMatchFailure) | PTypeFailure ->
                                PTypeFailure`;;
hol4_overload "pmatch" "pattern_semantics_pmatch";;
hol4_overload "pmatch_list" "pattern_semantics_pmatch_list";;

let match_def = cake_define
  `(match refs [] v = SOME MatchFailure) /\
   (match refs ((p,e) :: rows) v =
     (match pmatch refs p v with
        PMatchSuccess ->
          (match match refs rows v with
            NONE -> NONE | SOME _7 -> SOME (MatchSuccess e)) |
              PMatchFailure -> match refs rows v | PTypeFailure ->
              NONE))`;;

(* semantics of output *)

let dt_test_def = cake_define
  `dt_test x1 x2 =
      match (x1,x2) with
        ((TagLenEq t l),(pattern_semantics_Term (SOME c) args)) ->
     SOME (t = c /\ l = LENGTH args)
      | ((pattern_semantics_LitEq l1),(Litv l2)) ->
     (if lit_same_type l1 l2 then SOME (l1 = l2) else NONE)
      | (_8,_9) -> NONE`;;

let app_pos_def = cake_define
  `app_pos refs x2 v =
        match (x2,v) with
          (EmptyPos,v) -> SOME v
        | ((Pos 0 pos),(RefPtr r)) ->
        match FLOOKUP refs r with NONE -> NONE | SOME v -> app_pos
          refs pos v
        | ((Pos 0 pos),(pattern_semantics_Term c (x :: xs))) ->
          app_pos refs pos x
        | ((Pos (SUC n) pos),(pattern_semantics_Term c (x :: xs))) ->
       app_pos refs (Pos n pos) (pattern_semantics_Term c xs)
        | ((Pos _10 _11),_12) -> NONE`;;

let dt_eval_guard_def = cake_define
  `(dt_eval_guard refs v pattern_semantics_True =
      SOME T) /\
   (dt_eval_guard refs v (pattern_semantics_PosTest pos test) =
      (match app_pos refs pos v with NONE -> NONE | SOME x -> dt_test
        test x)) /\
   (dt_eval_guard refs v (Not g) =
      (match dt_eval_guard refs v g with NONE -> NONE | SOME b ->
        SOME (~b))) /\
   (dt_eval_guard refs v (pattern_semantics_Conj g1 g2) =
      (match dt_eval_guard refs v g1 with NONE -> NONE | SOME T ->
        dt_eval_guard refs v g2 | SOME F -> SOME F)) /\
   (dt_eval_guard refs v (pattern_semantics_Disj g1 g2) =
      (match dt_eval_guard refs v g1 with NONE -> NONE | SOME T ->
        SOME T | SOME F -> dt_eval_guard refs v g2))`;;

let dt_eval_def = cake_define
  `(dt_eval refs _13 (Leaf k) = SOME (MatchSuccess k)) /\
   (dt_eval refs _14 Fail = SOME (MatchFailure)) /\
   (dt_eval refs _15 pattern_semantics_TypeFail = NONE) /\
   (dt_eval refs v (If guard' dt1 dt2) =
      (match dt_eval_guard refs v guard' with NONE -> NONE | SOME
        b -> dt_eval refs v (if b then dt1 else dt2)))`;;
