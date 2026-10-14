(* ======================================================== *)
(*  pattern_semantics: ported from HOL4's
    compiler/backend/pattern_matching/pattern_semanticsScript.sml  *)
(* ======================================================== *)

(*
  The syntax and semantics of the input and output to the
  pattern-match compiler.
*)

needs "compiler/backend/pattern_matching/pattern_common.ml";;
needs "semantics/ast.ml";;
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

(* output syntax *)

let dTest_INDUCT,dTest_RECURSION = define_datatype
  "dTest = pattern_semantics_TagLenEq (num) (num) | \
   pattern_semantics_LitEq (lit)";;

let dGuard_INDUCT,dGuard_RECURSION = define_datatype
  "dGuard = pattern_semantics_PosTest (position) (dTest) | \
   pattern_semantics_Not (dGuard) | pattern_semantics_Conj (dGuard) \
   (dGuard) | pattern_semantics_Disj (dGuard) (dGuard) | \
   pattern_semantics_True";;

let dTree_INDUCT,dTree_RECURSION = define_datatype
  "dTree = pattern_semantics_Leaf (num) | pattern_semantics_Fail | \
   pattern_semantics_TypeFail | pattern_semantics_If (dGuard) (dTree) \
   (dTree)";;

(* semantic values *)

let term_INDUCT,term_RECURSION = define_datatype
  "term = pattern_semantics_Term (num option) (term list) | \
   pattern_semantics_Litv (lit) | pattern_semantics_RefPtr (num) | \
   pattern_semantics_Other";;

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
          (pattern_semantics_Any,t) -> PMatchSuccess
        | ((pattern_semantics_Lit l),(pattern_semantics_Litv l')) ->
        if ~lit_same_type l l' then PTypeFailure else
        if l = l' then PMatchSuccess else PMatchFailure
        | ((pattern_semantics_Cons (SOME
          (pattern_semantics_tag,siblings))
          pargs),(pattern_semantics_Term (SOME t) targs)) ->
       if pattern_semantics_tag = t /\ LENGTH pargs = LENGTH targs
         then pattern_semantics_pmatch_list refs pargs targs else
       if is_sibling (t,LENGTH targs) siblings then PMatchFailure
         else PTypeFailure
        | ((pattern_semantics_Cons NONE
          pargs),(pattern_semantics_Term NONE targs)) ->
       pattern_semantics_pmatch_list refs pargs targs
        | ((pattern_semantics_Ref p),(pattern_semantics_RefPtr r)) ->
       match FLOOKUP refs r with NONE -> PTypeFailure | SOME
         semanticPrimitives_v -> pattern_semantics_pmatch refs p
         semanticPrimitives_v
        | ((pattern_semantics_Or p1 p2),t) ->
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

let match_def = cake_define
  `(match refs [] semanticPrimitives_v = SOME MatchFailure) /\
   (match refs ((p,e) :: rows) semanticPrimitives_v =
     (match pattern_semantics_pmatch refs p semanticPrimitives_v with
        PMatchSuccess ->
          (match match refs rows semanticPrimitives_v with
            NONE -> NONE | SOME _7 -> SOME (MatchSuccess e)) |
              PMatchFailure -> match refs rows semanticPrimitives_v |
              PTypeFailure -> NONE))`;;

(* semantics of output *)

let dt_test_def = cake_define
  `dt_test x1 x2 =
      match (x1,x2) with
        ((pattern_semantics_TagLenEq t l),(pattern_semantics_Term
          (SOME c) args)) ->
     SOME (t = c /\ l = LENGTH args)
      | ((pattern_semantics_LitEq l1),(pattern_semantics_Litv l2)) ->
     (if lit_same_type l1 l2 then SOME (l1 = l2) else NONE)
      | (_8,_9) -> NONE`;;

let app_pos_def = cake_define
  `app_pos refs x2 v =
        match (x2,v) with
          (EmptyPos,semanticPrimitives_v) -> SOME
            semanticPrimitives_v
        | ((Pos 0 pos),(pattern_semantics_RefPtr r)) ->
        match FLOOKUP refs r with NONE -> NONE | SOME
          semanticPrimitives_v -> app_pos refs pos semanticPrimitives_v
        | ((Pos 0 pos),(pattern_semantics_Term c (x :: xs))) ->
          app_pos refs pos x
        | ((Pos (SUC n) pos),(pattern_semantics_Term c (x :: xs))) ->
       app_pos refs (Pos n pos) (pattern_semantics_Term c xs)
        | ((Pos _10 _11),_12) -> NONE`;;

let dt_eval_guard_def = cake_define
  `(dt_eval_guard refs semanticPrimitives_v pattern_semantics_True =
      SOME T) /\
   (dt_eval_guard refs semanticPrimitives_v
     (pattern_semantics_PosTest pos test) =
      (match app_pos refs pos semanticPrimitives_v with NONE -> NONE
        | SOME x -> dt_test test x)) /\
   (dt_eval_guard refs semanticPrimitives_v (pattern_semantics_Not
     g') =
      (match dt_eval_guard refs semanticPrimitives_v g' with NONE ->
        NONE | SOME b -> SOME (~b))) /\
   (dt_eval_guard refs semanticPrimitives_v (pattern_semantics_Conj
     g1 g2) =
      (match dt_eval_guard refs semanticPrimitives_v g1 with NONE ->
        NONE | SOME T -> dt_eval_guard refs semanticPrimitives_v g2 |
        SOME F -> SOME F)) /\
   (dt_eval_guard refs semanticPrimitives_v (pattern_semantics_Disj
     g1 g2) =
      (match dt_eval_guard refs semanticPrimitives_v g1 with NONE
        -> NONE | SOME T -> SOME T | SOME F -> dt_eval_guard refs
        semanticPrimitives_v g2))`;;

let dt_eval_def = cake_define
  `(dt_eval refs _13 (pattern_semantics_Leaf k) = SOME (MatchSuccess k))
  /\
   (dt_eval refs _14 pattern_semantics_Fail = SOME (MatchFailure)) /\
   (dt_eval refs _15 pattern_semantics_TypeFail = NONE) /\
   (dt_eval refs semanticPrimitives_v (pattern_semantics_If guard'
     dt1 dt2) =
      (match dt_eval_guard refs semanticPrimitives_v guard' with
        NONE -> NONE | SOME b -> dt_eval refs semanticPrimitives_v
        (if b then dt1 else dt2)))`;;
