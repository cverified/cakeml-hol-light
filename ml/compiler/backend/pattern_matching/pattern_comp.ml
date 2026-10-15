(* ======================================================== *)
(*  pattern_comp: ported from HOL4's
    compiler/backend/pattern_matching/pattern_compScript.sml  *)
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
needs "semantics/ffi/ffi.ml";;
needs "semantics/semanticPrimitives.ml";;

(* moving constant patterns up *)

let is_const_row_def = cake_define
  `is_const_row x1 =
      match x1 with
        (pattern_semantics_Cons _1 pats,x) -> NULL pats
      | _2 -> F`;;

let is_Any_def = cake_define
  `is_Any x1 =
      match x1 with
        pattern_semantics_Any -> T
      | (Or p1 p2) -> (is_Any p1 \/ is_Any p2)
      | _3 -> F`;;

let is_Or_row_def = cake_define
  `is_Or_row x1 =
      match x1 with
        ((Or p1 p2:pattern_semantics_pat),_4) -> T
      | _5 -> F`;;

let take_until_Any_def = cake_define_list
  [`take_until_Any [] = []`;
   `take_until_Any ((p,x) :: xs) =
      (if is_Any p then [(p,x)] else (p,x) :: take_until_Any xs)`];;

let move_const_up_def = cake_define
  `move_const_up rows =
     (let new_rows = take_until_Any rows in
       if 5 <= LENGTH new_rows \/ EXISTS is_Or_row new_rows then
         new_rows else
         FILTER is_const_row new_rows ++
         FILTER (\x. ~is_const_row x) new_rows)`;;

(* replace last pattern with Any (used if rows are exhaustive) *)

let insert_Any_def = cake_define
  `insert_Any x1 =
      match x1 with
        [] -> []
      | [(p,x)] -> [(pattern_semantics_Any,x)]
      | (x :: xs) -> x :: insert_Any xs`;;


(* turning the pattern rows into code *)

let is_True_def = cake_define
  `is_True x1 =
      match x1 with
        pattern_semantics_True -> T
      | _6 -> F`;;

let mk_Disj_def = cake_define
  `mk_Disj p q = (if is_True p \/ is_True q then
  pattern_semantics_True else pattern_semantics_Disj p q)`;;

let mk_Conj_def = cake_define
  `mk_Conj p q =
     (if is_True p then q else
     if is_True q then p else pattern_semantics_Conj p q)`;;

let mk_If_def = cake_define
  `mk_If g p q = (if is_True g then p else If g p q)`;;

let get_pos_def = cake_define_list
  [`get_pos [] = EmptyPos`;
   `get_pos (n :: ns) = Pos n (get_pos ns)`];;

let pat_to_guard_def = cake_define_list
  [`pat_to_guard l pattern_semantics_Any = pattern_semantics_True`;
   `pat_to_guard l (Lit r:pattern_semantics_pat) =
  pattern_semantics_PosTest (get_pos (REVERSE l))
  (pattern_semantics_LitEq r)`;
   `pat_to_guard l (pattern_semantics_Cons NONE pats) = pats_to_guard
  l 0 pats`;
   `pat_to_guard l (pattern_semantics_Cons (SOME (t,_7)) pats) =
      mk_Conj (pattern_semantics_PosTest (get_pos (REVERSE l))
        (pattern_semantics_TagLenEq t (LENGTH pats)))
          (pats_to_guard l 0 pats)`;
   `pat_to_guard l (Or p1 p2:pattern_semantics_pat) = mk_Disj
  (pat_to_guard l p1) (pat_to_guard l p2)`;
   `pat_to_guard l (pattern_semantics_Ref p) = pat_to_guard (0 :: l)
  p`;
   `pats_to_guard l k [] = pattern_semantics_True`;
   `pats_to_guard l k [p] = pat_to_guard (k :: l) p`;
   `pats_to_guard l k (p :: ps) = mk_Conj (pat_to_guard (k :: l) p)
  (pats_to_guard l (k + 1) ps)`];;

let pats_to_code_def = cake_define_list
  [`pats_to_code [] = Fail`;
   `pats_to_code ((p,x) :: rows) =
      mk_If (pat_to_guard [] p) (pattern_semantics_Leaf x)
        (pats_to_code rows)`];;

let walk_def = cake_define_list
  [`pattern_comp_walk [] x refs = SOME x`;
   `pattern_comp_walk (n :: ns) x refs =
      (match x with (pattern_semantics_Term t xs) -> (if n < LENGTH
        xs then pattern_comp_walk ns (EL n xs) refs else NONE) |
        (pattern_semantics_RefPtr p) -> (if ~(n = 0) then NONE else
                        match FLOOKUP refs p with SOME y ->
                          pattern_comp_walk ns y refs | _10 -> NONE)
                          | _11 -> NONE)`];;
hol4_overload "walk" "pattern_comp_walk";;

let walk_list_def = cake_define
  `walk_list ns x refs =
     (match pattern_comp_walk ns x refs with SOME
       (pattern_semantics_Term _12 vs) -> SOME vs | _13 -> NONE)`;;


(* plug all the parts together *)

let comp_def = cake_define
  `pattern_comp_comp rows =
     (let rows0 = move_const_up rows in
     let rows1 = (if exh_rows rows0 then insert_Any rows0 else rows0)
       in
       pats_to_code rows1)`;;
hol4_overload "comp" "pattern_comp_comp";;
