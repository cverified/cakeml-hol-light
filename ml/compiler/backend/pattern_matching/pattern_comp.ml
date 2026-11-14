(* ======================================================== *)
(*  pattern_comp: ported from HOL4's
    compiler/backend/pattern_matching/pattern_compScript.sml
    A definition theory, with 16 definitions and 21 theorems.
    Needed by flat_pattern.ml.  *)
(* ======================================================== *)

(*
  A simple pattern compiler that moves constant patterns upwards,
  checks for exhaustiveness, and then converts the pattern rows into
  an if-then-else decision tree.

  The exhaustiveness check itself lives in pattern_exhTheory.
*)

needs "compiler/backend/pattern_matching/pattern_common.ml";;
needs "compiler/backend/pattern_matching/pattern_exh.ml";;
needs "compiler/backend/pattern_matching/pattern_semantics.ml";;
needs "semantics/ast.ml";;
needs "semantics/semanticPrimitives.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "pattern_comp"
  ["ast"; "pattern_common"; "pattern_exh"; "pattern_semantics";
   "semanticPrimitives"];;

(* moving constant patterns up *)

let is_const_row_def = new_definition
  `is_const_row x1 =
      match x1 with
        ((pattern_semantics_Cons _2 pats:pattern_semantics_pat),x) ->
          NULL pats
      | _3 -> F`;;

let is_Any_def,is_Any_ind = define_shaped_rec
  "match"
  [`is_Any x1 =
      match x1 with
        (pattern_semantics_Any:pattern_semantics_pat) -> T
      | (pattern_semantics_Or p1 p2) -> (is_Any p1 \/ is_Any p2)
      | _4 -> F`];;

let is_Or_row_def = new_definition
  `is_Or_row x1 =
      match x1 with
        ((pattern_semantics_Or p1 p2:pattern_semantics_pat),_5) -> T
      | _6 -> F`;;

let take_until_Any_def,take_until_Any_ind = define_rec
  [`take_until_Any [] = []`;
   `take_until_Any (CONS (p,x) xs) =
      (if is_Any p then [(p,x)] else CONS (p,x) (take_until_Any
          xs))`];;

let move_const_up_def = new_definition
  `move_const_up rows =
     (let new_rows = take_until_Any rows in
       if 5 <= LENGTH new_rows \/ EX is_Or_row new_rows then
         new_rows else APPEND
         // long pattern rows should not be changed
         (FILTER is_const_row new_rows)
         (FILTER (\x. ~(is_const_row x)) new_rows))`;;

let is_Any_pmatch = prove
 (`!p. is_Any p ==> ~(pattern_semantics_pmatch refs p v =
  PMatchFailure)`,
  CHEAT_TAC);;

let match_take_until_Any = prove
 (`!rows. ~(pattern_semantics_match refs rows v = NONE) ==>
     pattern_semantics_match refs (take_until_Any rows) v =
       pattern_semantics_match refs rows v`,
  CHEAT_TAC);;

let match_append = prove
 (`!xs ys refs v.
     pattern_semantics_match refs (APPEND xs ys) v =
     (match pattern_semantics_match refs xs v with NONE -> NONE |
       SOME (MatchSuccess e) -> (if ~(pattern_semantics_match refs ys
       v = NONE) then SOME (MatchSuccess e) else NONE) | SOME _7 ->
       pattern_semantics_match refs ys v)`,
  CHEAT_TAC);;

(* [local] *)
let pmatchResult_case_NONE = prove
 (`(match x with PMatchSuccess -> NONE | PMatchFailure -> NONE |
  PTypeFailure -> K NONE NONE) = NONE`,
  CHEAT_TAC);;

(* HOL4 pattern_compScript.sml:92: a theorem that HOL4 states as the
   value of an ML expression: pmatchResult_case_NONE *)

let is_const_row_lemma = prove
 (`(!t. ~(v = pattern_semantics_Term t [])) /\ is_const_row (p_1,p_2) /\
  ~(pattern_semantics_pmatch refs p_1 v = PTypeFailure) ==>
   pattern_semantics_pmatch refs p_1 v = PMatchFailure`,
  CHEAT_TAC);;

let not_is_const_row = prove
 (`~(is_const_row (p,x)) /\ ~(is_Or_row (p,x)) /\ ~(is_Any p) ==>
  ~(pattern_semantics_pmatch refs p (pattern_semantics_Term t []) =
  PMatchSuccess)`,
  CHEAT_TAC);;

let EVERY_take_until_Any = prove
 (`!rows. ALL (\(x,y). ~(is_Any x)) (TL (REVERSE (take_until_Any
  (rows:(pattern_semantics_pat#num) list))))`,
  CHEAT_TAC);;

let matdch_FILTER_NOT_NONE = prove
 (`!xs. ~(pattern_semantics_match refs xs v = NONE) ==>
  ~(pattern_semantics_match refs (FILTER P xs) v = NONE)`,
  CHEAT_TAC);;

let match_move_const_up = prove
 (`~(pattern_semantics_match refs rows v = NONE) ==>
     pattern_semantics_match refs (move_const_up rows) v =
       pattern_semantics_match refs rows v`,
  CHEAT_TAC);;


(* pmatch_list_LENGTH *)
let pattern_comp_pmatch_list_LENGTH = prove
 (`!ps vs. ~(pattern_semantics_pmatch_list refs ps vs = PTypeFailure)
  ==> LENGTH vs = LENGTH ps`,
  CHEAT_TAC);;

(* replace last pattern with Any (used if rows are exhaustive) *)

let _ = size_thms "pattern_semantics_pat";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let insert_Any_def,insert_Any_ind = define_wf
  `MEASURE (\x0. list_size (pair_size pattern_semantics_pat_size (\x.
  0)) x0)`
  [`insert_Any x1 =
      match x1 with
        [] -> []
      | [p,x] -> [(pattern_semantics_Any,x)]
      | (CONS x xs) -> CONS x (insert_Any xs)`];;

let match_insert_Any = prove
 (`!rows. ~(pattern_semantics_match refs rows v = NONE) ==>
  ~(pattern_semantics_match refs (insert_Any rows) v = NONE) /\
     (~(pattern_semantics_match refs rows v = SOME MatchFailure) ==>
      pattern_semantics_match refs (insert_Any rows) v =
        pattern_semantics_match refs rows v)`,
  CHEAT_TAC);;


(* turning the pattern rows into code *)

let is_True_def = new_definition
  `is_True x1 =
      match x1 with
        pattern_semantics_True -> T
      | _8 -> F`;;

let mk_Disj_def = new_definition
  `mk_Disj p q = (if is_True p \/ is_True q then
  pattern_semantics_True else pattern_semantics_Disj p q)`;;

let mk_Conj_def = new_definition
  `mk_Conj p q =
     (if is_True p then q else
     if is_True q then p else pattern_semantics_Conj p q)`;;

let mk_If_def = new_definition
  `mk_If g p q = (if is_True g then p else pattern_semantics_If g p
  q)`;;

let get_pos_def,get_pos_ind = define_rec
  [`get_pos [] = EmptyPos`;
   `get_pos (CONS n ns) = Pos n (get_pos ns)`];;

(* the termination relation that HOL4 gives is
     MEASURE (\x. match x with INL (_11,p) -> pattern_semantics_pat_size
       p | INR (_12,k,p) -> list_size pattern_semantics_pat_size p)
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let pat_to_guard_def,pat_to_guard_ind = define_guess_cheat
  [`pat_to_guard l (pattern_semantics_Any:pattern_semantics_pat) =
    pattern_semantics_True`;
   `pat_to_guard l (pattern_semantics_Lit r:pattern_semantics_pat) =
    pattern_semantics_PosTest (get_pos (REVERSE l))
    (pattern_semantics_LitEq r)`;
   `pat_to_guard l (pattern_semantics_Cons NONE
    pats:pattern_semantics_pat) = pats_to_guard l 0 pats`;
   `pat_to_guard l (pattern_semantics_Cons (SOME (t,_10))
    pats:pattern_semantics_pat) =
      mk_Conj (pattern_semantics_PosTest (get_pos (REVERSE l))
        (pattern_semantics_TagLenEq t (LENGTH pats)))
            (pats_to_guard l 0 pats)`;
   `pat_to_guard l (pattern_semantics_Or p1 p2:pattern_semantics_pat)
    = mk_Disj (pat_to_guard l p1) (pat_to_guard l p2)`;
   `pat_to_guard l (pattern_semantics_Ref p:pattern_semantics_pat) =
    pat_to_guard (CONS 0 l) p`;
   `pats_to_guard l k [] = pattern_semantics_True`;
   `pats_to_guard l k [p] = pat_to_guard (CONS k l) p`;
   `pats_to_guard l k (CONS p ps) = mk_Conj (pat_to_guard (CONS k
    l) p) (pats_to_guard l (k + 1) ps)`];;

let pats_to_code_def,pats_to_code_ind = define_rec
  [`pats_to_code [] = pattern_semantics_Fail`;
   `pats_to_code (CONS (p,x) rows) =
      mk_If (pat_to_guard [] p) (pattern_semantics_Leaf x)
          (pats_to_code rows)`];;

let pattern_comp_walk_def,pattern_comp_walk_ind = define_rec
  [`pattern_comp_walk [] x refs = SOME x`;
   `pattern_comp_walk (CONS n ns) x refs =
      (match x with (pattern_semantics_Term t xs) -> (if n < LENGTH
          xs then pattern_comp_walk ns (EL n xs) refs else NONE) |
          (pattern_semantics_RefPtr p) -> (if ~(n = 0) then NONE else
                        match FLOOKUP refs p with SOME y ->
                            pattern_comp_walk ns y refs | _15 ->
                            NONE) | _16 -> NONE)`];;

let walk_list_def = new_definition
  `walk_list ns x refs =
     (match pattern_comp_walk ns x refs with SOME
       (pattern_semantics_Term _17 vs) -> SOME vs | _18 -> NONE)`;;

let app_pos_Pos = prove
 (`!n xs.
     n < LENGTH xs ==>
     app_pos refs (Pos n x) (pattern_semantics_Term t xs) = app_pos
       refs x (EL n xs)`,
  CHEAT_TAC);;

let walk_thm = prove
 (`!l v refs x.
     pattern_comp_walk l v refs = SOME x ==>
     app_pos refs (get_pos l) v = SOME x`,
  CHEAT_TAC);;

let walk_append = prove
 (`!xs ys v refs.
     pattern_comp_walk (APPEND xs ys) v refs =
     (match pattern_comp_walk xs v refs with NONE -> NONE | SOME v
       -> pattern_comp_walk ys v refs)`,
  CHEAT_TAC);;

(* [local] *)
let is_True_thm = prove
 (`is_True t <=> t = pattern_semantics_True`,
  CHEAT_TAC);;

(* [local] *)
let dt_eval_guard_mk_Conj = prove
 (`dt_eval_guard refs v (mk_Conj p q) =
   dt_eval_guard refs v (pattern_semantics_Conj p q)`,
  CHEAT_TAC);;

let dt_eval_guard_pat_to_guard = prove
 (`(!l p x. ~(pattern_semantics_pmatch refs p x = PTypeFailure) /\
     pattern_comp_walk (REVERSE l) v refs = SOME x ==>
     dt_eval_guard refs v (pat_to_guard l p) =
       SOME (pattern_semantics_pmatch refs p x = PMatchSuccess)) /\
   (!l k ps xs ys. ~(pattern_semantics_pmatch_list refs ps xs =
     PTypeFailure) /\ LENGTH ys = k /\
     walk_list (REVERSE l) v refs = SOME (APPEND ys xs) /\ LENGTH xs
       = LENGTH ps ==>
     dt_eval_guard refs v (pats_to_guard l k ps) =
       SOME (pattern_semantics_pmatch_list refs ps xs =
         PMatchSuccess))`,
  CHEAT_TAC);;

(* [local] *)
let mk_If_thm = prove
 (`dt_eval refs v (mk_If g p q) = dt_eval refs v (pattern_semantics_If
  g p q)`,
  CHEAT_TAC);;

let pat_to_code_thm = prove
 (`!rows. ~(pattern_semantics_match refs rows v = NONE) ==>
     dt_eval refs v (pats_to_code rows) = pattern_semantics_match
       refs rows v`,
  CHEAT_TAC);;


(* plug all the parts together *)

let pattern_comp_comp_def = new_definition
  `pattern_comp_comp rows =
     (let rows0 = move_const_up rows in
     let rows1 = (if exh_rows rows0 then insert_Any rows0 else rows0)
       in
       pats_to_code rows1)`;;

let comp_thm = prove
 (`~(pattern_semantics_match refs rows v = NONE) ==>
     dt_eval refs v (pattern_comp_comp rows) =
       pattern_semantics_match refs rows v`,
  CHEAT_TAC);;
