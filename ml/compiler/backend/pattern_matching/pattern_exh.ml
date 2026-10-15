(* ======================================================== *)
(*  pattern_exh: ported from HOL4's
    compiler/backend/pattern_matching/pattern_exhScript.sml  *)
(* ======================================================== *)

(*
  An exhaustiveness checker for pattern-match rows, in the style of
  Maranget's usefulness algorithm, but using sibling annotations instead
  of a typing environment.

  The entry point is exh_rows.  It first removes all Or-patterns by
  expanding each row into its Or-free variants, then decides whether the
  resulting one-column pattern matrix covers every value.

  The matrix algorithm (exh_matrix) works on a matrix of pattern
    vectors.
  Looking at the first column it computes, from the sibling information
    in
  the patterns, an over-approximation col_ctors of the set of
    constructors
  a well-typed value can have there.

    - If that set is unknown (NONE) the matrix is exhaustive when the
      default matrix is: only rows starting with a wildcard can match a
      value whose constructor is not mentioned.

    - If the set is known, the matrix is exhaustive when every
      specialised matrix is: each constructor of the set is considered
        in
      turn, and its arguments are pushed onto the front of the vector.

  Only well-typed values matter, i.e. values for which no row of the
  original match yields PTypeFailure.  Since match walks *every* row and
  fails with NONE as soon as one row type-fails, all rows constrain the
  value simultaneously.  Hence the constructor set of a column is the
  *intersection* over the rows of the constructors each head pattern
  allows, which is what col_ctors computes.
*)

needs "compiler/backend/pattern_matching/pattern_common.ml";;
needs "compiler/backend/pattern_matching/pattern_semantics.ml";;
needs "semantics/ast.ml";;
needs "semantics/semanticPrimitives.ml";;


(* --------------------------------------------------------------------
   *
   Constructors of values.

   A well-typed value at a given position is a tagged term (TagC), an
   untagged term, i.e. a tuple (TupC), or a reference (RefC).  Literals
   are deliberately not constructors here: their type is (for all
   practical purposes) infinite, so a column of literals is never a
   complete signature.
 * --------------------------------------------------------------------
   *)

let ctor_INDUCT,ctor_RECURSION = define_datatype
  "ctor = TagC (num) (num) | TupC (num) | RefC";;

let ctor_arity_def = cake_define_list
  [`ctor_arity (TagC t a) = a`;
   `ctor_arity (TupC a) = a`;
   `ctor_arity RefC = 1`];;

let anys_def = cake_define_list
  [`anys 0 = []`;
   `anys (SUC n) = pattern_semantics_Any :: anys n`];;


(* --------------------------------------------------------------------
   *
   Removing Or-patterns.

   expand p is the list of Or-free patterns p can be split into.  Given
   that pmatch does not type-fail, p matches a value exactly when one of
   the patterns in expand p does.
 * --------------------------------------------------------------------
   *)

let add_head_def = cake_define_list
  [`add_head x [] = []`;
   `add_head x (ys :: yss) = (x :: ys) :: add_head x yss`];;

let mk_prods_def = cake_define_list
  [`mk_prods [] ys = []`;
   `mk_prods (x :: xs) ys = add_head x ys ++ mk_prods xs ys`];;

let mk_refs_def = cake_define_list
  [`mk_refs [] = []`;
   `mk_refs (p :: ps) = pattern_semantics_Ref p :: mk_refs ps`];;

let mk_conses_def = cake_define_list
  [`mk_conses t [] = []`;
   `mk_conses t (ps :: pss) = pattern_semantics_Cons t ps ::
  mk_conses t pss`];;

let expand_def = cake_define_list
  [`expand pattern_semantics_Any = [pattern_semantics_Any]`;
   `expand (Lit l:pattern_semantics_pat) = [(Lit
  l:pattern_semantics_pat)]`;
   `expand (Or p q:pattern_semantics_pat) = expand p ++ expand q`;
   `expand (pattern_semantics_Ref p) = mk_refs (expand p)`;
   `expand (pattern_semantics_Cons t ps) = mk_conses t (expand_list
  ps)`;
   `expand_list [] = [[]]`;
   `expand_list (p :: ps) = mk_prods (expand p) (expand_list ps)`];;

let mk_rows_def = cake_define_list
  [`mk_rows [] = []`;
   `mk_rows (p :: ps) = [p] :: mk_rows ps`];;

let or_rows_def = cake_define_list
  [`or_rows [] = []`;
   `or_rows ((p,e) :: rows) = mk_rows (expand p) ++ or_rows rows`];;


(* --------------------------------------------------------------------
   *
   The constructors a head pattern allows a well-typed value to have.

   NONE means "no information", i.e. every constructor is allowed.  Note
   that a missing sibling list (Cons (SOME (t,NONE)) _), which is how
   exceptions are encoded, gives no information, and neither does a
   literal pattern.
 * --------------------------------------------------------------------
   *)

let tag_ctors_def = cake_define_list
  [`tag_ctors [] = []`;
   `tag_ctors ((t,a) :: sibs) = TagC t a :: tag_ctors sibs`];;

let ctor_nub_def = cake_define_list
  [`ctor_nub [] = []`;
   `ctor_nub (x :: xs) = (if MEM x xs then ctor_nub xs else x ::
  ctor_nub xs)`];;

let ctors_of_def = cake_define
  `ctors_of x1 =
      match x1 with
        pattern_semantics_Any -> NONE
      | (Lit _1) -> NONE
      | (Or _2 _3) -> NONE
      | (pattern_semantics_Ref _4) -> SOME [RefC]
      | (pattern_semantics_Cons NONE qs) -> SOME [TupC (LENGTH qs)]
      | (pattern_semantics_Cons (SOME (t,NONE)) qs) -> NONE
      | (pattern_semantics_Cons (SOME (t,SOME sibs)) qs) ->
     SOME (ctor_nub (TagC t (LENGTH qs) :: tag_ctors sibs))`;;

let ctor_keep_def = cake_define_list
  [`ctor_keep [] ys = []`;
   `ctor_keep (x :: xs) ys =
      (if MEM x ys then x :: ctor_keep xs ys else ctor_keep xs
        ys)`];;

let ctor_inter_def = cake_define
  `ctor_inter xs ys =
      match (xs,ys) with
        (NONE,ys) -> ys
      | (xs,NONE) -> xs
      | ((SOME xs),(SOME ys)) -> SOME (ctor_keep xs ys)`;;

let col_ctors_def = cake_define_list
  [`col_ctors [] = NONE`;
   `col_ctors ([] :: rows) = col_ctors rows`;
   `col_ctors ((p :: _5) :: rows) = ctor_inter (ctors_of p)
  (col_ctors rows)`];;


(* --------------------------------------------------------------------
   *
   Specialised and default matrices.

   spec_row c takes the rows that can match a value whose head
   constructor is c, and replaces the head pattern by the patterns for
   the arguments of c.  default_row keeps only the rows that start with
     a
   wildcard, dropping the head pattern.
 * --------------------------------------------------------------------
   *)

let spec_row_def = cake_define
  `spec_row c x2 =
      match x2 with
        [] -> []
      | (pattern_semantics_Any :: rest) -> [anys (ctor_arity c) ++
        rest]
      | ((pattern_semantics_Cons NONE qs) :: rest) ->
     (if c = TupC (LENGTH qs) then [qs ++ rest] else [])
      | ((pattern_semantics_Cons (SOME ts) qs) :: rest) ->
     (if c = TagC (FST ts) (LENGTH qs) then [qs ++ rest] else [])
      | ((pattern_semantics_Ref q) :: rest) -> (if c = RefC then [q
        :: rest] else [])
      | ((Lit l) :: rest) -> []
      | ((Or p q) :: rest) -> []`;;

let spec_mat_def = cake_define_list
  [`spec_mat c [] = []`;
   `spec_mat c (r :: rows) = spec_row c r ++ spec_mat c rows`];;

let spec_mats_def = cake_define_list
  [`spec_mats [] rows = []`;
   `spec_mats (c :: cs) rows = spec_mat c rows :: spec_mats cs rows`];;

let default_row_def = cake_define
  `default_row x1 =
      match x1 with
        (pattern_semantics_Any :: rest) -> [rest]
      | _6 -> []`;;

let default_mat_def = cake_define_list
  [`default_mat [] = []`;
   `default_mat (r :: rows) = default_row r ++ default_mat rows`];;


(* --------------------------------------------------------------------
   *
   Measures used for the termination of exh_matrix.

   Specialising strictly decreases the number of constructor nodes in
     the
   matrix, provided some head pattern is a constructor pattern -- which
   is exactly what col_ctors returning SOME guarantees.  Taking the
   default matrix does not increase that count, and strictly decreases
   the total number of columns.
 * --------------------------------------------------------------------
   *)

let pat_weight_def = cake_define_list
  [`pat_weight pattern_semantics_Any = (0:num)`;
   `pat_weight (Lit l:pattern_semantics_pat) = 0`;
   `pat_weight (Or p q:pattern_semantics_pat) = 1 + pat_weight p +
  pat_weight q`;
   `pat_weight (pattern_semantics_Ref p) = 1 + pat_weight p`;
   `pat_weight (pattern_semantics_Cons t ps) = 1 + pats_weight ps`;
   `pats_weight [] = 0`;
   `pats_weight (p :: ps) = pat_weight p + pats_weight ps`];;

let mat_weight_def = cake_define_list
  [`mat_weight [] = 0`;
   `mat_weight (r :: rows) = pats_weight r + mat_weight rows`];;

let mat_len_def = cake_define_list
  [`mat_len [] = 0`;
   `mat_len (r :: rows) = LENGTH r + mat_len rows`];;

let mats_weight_def = cake_define_list
  [`mats_weight [] = 0`;
   `mats_weight (m :: ms) = MAX (mat_weight m) (mats_weight ms)`];;

let mats_len_def = cake_define_list
  [`mats_len [] = 0`;
   `mats_len (m :: ms) = MAX (mat_len m) (mats_len ms)`];;


(* --------------------------------------------------------------------
   *
   The matrix algorithm and the entry point.
 * --------------------------------------------------------------------
   *)

let exh_matrix_def = cake_define_list
  [`exh_matrix [] = F`;
   `exh_matrix (r :: rows) =
      (if NULL r then T else
         match col_ctors (r :: rows) with NONE -> exh_matrix
           (default_mat (r :: rows)) | SOME cs -> exh_mats (spec_mats
           cs (r :: rows)))`;
   `exh_mats [] = T`;
   `exh_mats (m :: ms) = (exh_matrix m /\ exh_mats ms)`];;

let exh_rows_def = cake_define
  `exh_rows rows = exh_matrix (or_rows rows)`;;


(* --------------------------------------------------------------------
   *
   A tail-recursive version, for execution.

   exh_matrix is a mutual recursion justified by a non-structural
   measure, which cv_translation cannot take.  exh_all is a single
   tail recursion that keeps the matrices still to be checked in a
   worklist.  It computes exactly the same answer -- exh_rows_eq below
     --
   so it is the equation the compiler is run through.

   Its termination is justified by counting the steps the original
   recursion takes: exh_steps has exactly the recursion structure of
   exh_matrix, hence exactly the same termination argument, and every
   step exh_all makes consumes one of those steps.
 * --------------------------------------------------------------------
   *)

let exh_steps_def = cake_define_list
  [`exh_steps [] = (1:num)`;
   `exh_steps (r :: rows) =
      (if NULL r then 1 else
         match col_ctors (r :: rows) with NONE -> 1 + exh_steps
           (default_mat (r :: rows)) | SOME cs -> 1 + exh_steps_list
           (spec_mats cs (r :: rows)))`;
   `exh_steps_list [] = 0`;
   `exh_steps_list (m :: ms) = exh_steps m + exh_steps_list ms`];;

let exh_all_def = cake_define_list
  [`exh_all [] = T`;
   `exh_all ([] :: ms) = F`;
   `exh_all ((r :: rows) :: ms) =
      (if NULL r then exh_all ms else
         match col_ctors (r :: rows) with NONE -> exh_all
           (default_mat (r :: rows) :: ms) | SOME cs -> exh_all
           (spec_mats cs (r :: rows) ++ ms))`];;


(* =====================================================================
   = *
   Soundness

   The theorem to prove is the one that justifies replacing the last row
   by a wildcard:

     match refs rows v <> NONE /\ exh_rows rows ==>
     match refs rows v <> SOME MatchFailure

   Read through match_def that says: if no row type-fails on v, then
     some
   row succeeds on v.  Everything below is phrased in those terms, at
     the
   level of matrices: "ok" means no row type-fails, "hit" means some row
   succeeds.
 * =====================================================================
   = *)


(* ---------------------------------------------------------------------
   - *
   pand combines the results of two matches performed one after the
   other.  It is exactly how pmatch_list glues a row together, and it
   makes the case analysis below disappear into two rewrite rules.
 * ---------------------------------------------------------------------
   - *)

let pand_def = cake_define_list
  [`pand PMatchSuccess y = y`;
   `pand PMatchFailure y = (if y = PTypeFailure then PTypeFailure
  else PMatchFailure)`;
   `pand PTypeFailure y = PTypeFailure`];;

(* From here on pmatch_list is only ever unfolded through these four
   rewrites, never through pmatch_def, the raw clauses of pmatch_def
   would compete with pmatch_list_cons and leave case expressions
   behind. *)

(* Stated with the width as an argument rather than as LENGTH as, so
   that
   it also rewrites the anys (ctor_arity c) that spec_row produces. *)


(* ---------------------------------------------------------------------
   - *
   What the first-order list-building helpers put into their results.
 * ---------------------------------------------------------------------
   - *)


(* ---------------------------------------------------------------------
   - *
   Expanding Or-patterns.

   An expanded pattern never type-fails where the original does not, and
   if an expanded pattern matches then so does the original.  (The
   converse also holds, but soundness does not need it.)
 * ---------------------------------------------------------------------
   - *)


(* ---------------------------------------------------------------------
   - *
   The constructor of a value, and its arguments.

   dest_val is only defined for the values that a constructor pattern
     can
   possibly match; literals and Other have no constructor.  Note that a
   reference has a constructor only when the pointer is in the heap,
   which is exactly when Ref does not type-fail.
 * ---------------------------------------------------------------------
   - *)

let dest_val_def = cake_define
  `dest_val refs x2 =
      match x2 with
        pattern_semantics_Term (SOME t) vs -> SOME (TagC t (LENGTH
          vs),vs)
      | (pattern_semantics_Term NONE vs) -> SOME (TupC (LENGTH
        vs),vs)
      | (pattern_semantics_RefPtr r) -> (match FLOOKUP refs r with
        NONE -> NONE | SOME w -> SOME (RefC,[w]))
      | (Litv l) -> NONE
      | pattern_semantics_Other -> NONE`;;

(* A head pattern that reports a constructor set really does confine a
   value that it does not type-fail on to that set. *)

(* ... and therefore so does the intersection over a whole column. *)


(* ---------------------------------------------------------------------
   - *
   Specialising and defaulting preserve match results.

   This is the one fact that makes the whole induction go through: every
   row of a transformed matrix gives exactly the same three-valued match
   result, against the transformed value vector, as the row it came from
   does against the original one.  Rows that are dropped simply have no
   counterpart, which costs nothing here -- dropping rows can only make
     a
   matrix less exhaustive, and soundness is the direction we need.
 * ---------------------------------------------------------------------
   - *)


(* ---------------------------------------------------------------------
   - *
   Soundness of the matrix algorithm.

   "ok" (no row type-fails) is inherited by the sub-matrices, and "hit"
   (some row succeeds) is reflected back out of them.
 * ---------------------------------------------------------------------
   - *)


(* ---------------------------------------------------------------------
   - *
   From the matrix back to match.
 * ---------------------------------------------------------------------
   - *)


(* ---------------------------------------------------------------------
   - *
   Soundness of exh_rows: the theorem the pattern compiler needs.
 * ---------------------------------------------------------------------
   - *)
