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
hol4_overload "LitEq" "pattern_semantics_LitEq";;

let dGuard_INDUCT,dGuard_RECURSION = define_datatype
  "dGuard = pattern_semantics_PosTest (position) (dTest) | \
   pattern_semantics_Not (dGuard) | pattern_semantics_Conj (dGuard) \
   (dGuard) | pattern_semantics_Disj (dGuard) (dGuard) | \
   pattern_semantics_True";;
hol4_overload "PosTest" "pattern_semantics_PosTest";;
hol4_overload "Not" "pattern_semantics_Not";;
hol4_overload "Conj" "pattern_semantics_Conj";;
hol4_overload "Disj" "pattern_semantics_Disj";;
hol4_overload "True" "pattern_semantics_True";;

let dTree_INDUCT,dTree_RECURSION = define_datatype
  "dTree = pattern_semantics_Leaf (num) | pattern_semantics_Fail | \
   pattern_semantics_TypeFail | pattern_semantics_If (dGuard) (dTree) \
   (dTree)";;
hol4_overload "Leaf" "pattern_semantics_Leaf";;
hol4_overload "Fail" "pattern_semantics_Fail";;
hol4_overload "TypeFail" "pattern_semantics_TypeFail";;
hol4_overload "If" "pattern_semantics_If";;

(* semantic values *)

let term_INDUCT,term_RECURSION = define_datatype
  "term = pattern_semantics_Term (num option) (term list) | \
   pattern_semantics_Litv (lit) | pattern_semantics_RefPtr (num) | \
   pattern_semantics_Other";;
hol4_overload "Term" "pattern_semantics_Term";;
hol4_overload "Litv" "pattern_semantics_Litv";;
hol4_overload "RefPtr" "pattern_semantics_RefPtr";;
hol4_overload "Other" "pattern_semantics_Other";;

(* semantics of input *)
let is_sibling_def = cake_define_list
  [`is_sibling x NONE = T`;
   `is_sibling x (SOME l) = MEM x l`];;

let pmatch_def = cake_define_list
  [`pattern_semantics_pmatch refs
  (pattern_semantics_Any:pattern_semantics_pat) t = PMatchSuccess`;
   `pattern_semantics_pmatch refs (Lit l:pattern_semantics_pat) (Litv
  l':term) =
         (if ~lit_same_type l l' then PTypeFailure else
         if l = l' then PMatchSuccess else PMatchFailure)`;
   `pattern_semantics_pmatch refs (pattern_semantics_Cons (SOME
  (tag,siblings)) pargs:pattern_semantics_pat) (pattern_semantics_Term
  (SOME t) targs) =
        (if tag = t /\ LENGTH pargs = LENGTH targs then
          pattern_semantics_pmatch_list refs pargs targs else
        if is_sibling (t,LENGTH targs) siblings then
          PMatchFailure else PTypeFailure)`;
   `pattern_semantics_pmatch refs (pattern_semantics_Cons NONE
  pargs:pattern_semantics_pat) (pattern_semantics_Term NONE targs) =
        pattern_semantics_pmatch_list refs pargs targs`;
   `pattern_semantics_pmatch refs (pattern_semantics_Ref
  p:pattern_semantics_pat) (pattern_semantics_RefPtr r:term) =
        (match FLOOKUP refs r with NONE -> PTypeFailure | SOME v
          -> pattern_semantics_pmatch refs p v)`;
   `pattern_semantics_pmatch refs (Or p1 p2:pattern_semantics_pat) t =
        (match pattern_semantics_pmatch refs p1 t with
           PMatchSuccess -> (match pattern_semantics_pmatch refs p2
             t with
                              PTypeFailure -> PTypeFailure | _3
                                -> PMatchSuccess) | PMatchFailure ->
                                pattern_semantics_pmatch refs p2 t |
                                PTypeFailure -> PTypeFailure)`;
   `pattern_semantics_pmatch refs _4 _5 = PTypeFailure`;
   `pattern_semantics_pmatch_list refs [] [] = PMatchSuccess`;
   `pattern_semantics_pmatch_list refs [] ts = PTypeFailure`;
   `pattern_semantics_pmatch_list refs ps [] = PTypeFailure`;
   `pattern_semantics_pmatch_list refs (p :: ps) (t :: ts) =
        (match pattern_semantics_pmatch refs p t with
          PMatchSuccess -> pattern_semantics_pmatch_list refs ps ts
            | PMatchFailure -> (match pattern_semantics_pmatch_list refs
            ps ts with
                              PTypeFailure -> PTypeFailure | _6
                                -> PMatchFailure) | PTypeFailure ->
                                PTypeFailure)`];;
hol4_overload "pmatch" "pattern_semantics_pmatch";;
hol4_overload "pmatch_list" "pattern_semantics_pmatch_list";;

let match_def = cake_define_list
  [`pattern_semantics_match refs [] v = SOME MatchFailure`;
   `pattern_semantics_match refs ((p,e) :: rows) v =
        (match pmatch refs p v with
           PMatchSuccess ->
             (match pattern_semantics_match refs rows v with
               NONE -> NONE | SOME _8 -> SOME (MatchSuccess e))
                 | PMatchFailure -> pattern_semantics_match refs
                 rows v | PTypeFailure -> NONE)`];;

(* semantics of output *)

let dt_test_def = cake_define
  `dt_test x1 x2 =
      match (x1,x2) with
        ((pattern_semantics_TagLenEq t
          l:dTest),pattern_semantics_Term (SOME c) args) ->
     SOME (t = c /\ l = LENGTH args)
      | ((pattern_semantics_LitEq l1),(Litv l2)) ->
     (if lit_same_type l1 l2 then SOME (l1 = l2) else NONE)
      | (_9,_10) -> NONE`;;

let app_pos_def = cake_define
  `app_pos refs x2 v =
        match (x2,v) with
          (EmptyPos,v) -> SOME v
        | ((Pos 0 pos),(pattern_semantics_RefPtr r)) ->
        (match FLOOKUP refs r with NONE -> NONE | SOME v -> app_pos
          refs pos v)
        | ((Pos 0 pos),(pattern_semantics_Term c (x :: xs))) ->
          app_pos refs pos x
        | ((Pos (SUC n) pos),(pattern_semantics_Term c (x :: xs))) ->
       app_pos refs (Pos n pos) (pattern_semantics_Term c xs)
        | ((Pos _11 _12),_13) -> NONE`;;

let dt_eval_guard_def = cake_define_list
  [`dt_eval_guard refs v pattern_semantics_True =
         SOME T`;
   `dt_eval_guard refs v (pattern_semantics_PosTest pos test) =
         (match app_pos refs pos v with NONE -> NONE | SOME x ->
           dt_test test x)`;
   `dt_eval_guard refs v (Not g:dGuard) =
         (match dt_eval_guard refs v g with NONE -> NONE | SOME b
           -> SOME (~b))`;
   `dt_eval_guard refs v (pattern_semantics_Conj g1 g2) =
         (match dt_eval_guard refs v g1 with NONE -> NONE | SOME
           T -> dt_eval_guard refs v g2 | SOME F -> SOME F)`;
   `dt_eval_guard refs v (pattern_semantics_Disj g1 g2) =
         (match dt_eval_guard refs v g1 with NONE -> NONE |
           SOME T -> SOME T | SOME F -> dt_eval_guard refs v g2)`];;

let dt_eval_def = cake_define_list
  [`dt_eval refs _14 (pattern_semantics_Leaf k:dTree) = SOME
  (MatchSuccess k)`;
   `dt_eval refs _15 (Fail:dTree) = SOME (MatchFailure)`;
   `dt_eval refs _16 pattern_semantics_TypeFail = NONE`;
   `dt_eval refs v (If guard' dt1 dt2:dTree) =
         (match dt_eval_guard refs v guard' with NONE -> NONE |
           SOME b -> dt_eval refs v (if b then dt1 else dt2))`];;
