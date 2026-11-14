(* ======================================================== *)
(*  pattern_exh: ported from HOL4's
    compiler/backend/pattern_matching/pattern_exhScript.sml
    A definition theory, with 31 definitions, 1 datatype and 52
    theorems.  Needed by pattern_comp.ml.  *)
(* ======================================================== *)

(*
  An exhaustiveness checker for pattern-match rows, in the style of
  Maranget's usefulness algorithm, but using sibling annotations instead
  of a typing environment.

  The entry point is exh_rows.  It first removes all Or-patterns by
  expanding each row into its Or-free variants, then decides whether the
  resulting one-column pattern matrix covers every value.

  The matrix algorithm (exh_matrix) works on a matrix of pattern vectors.
  Looking at the first column it computes, from the sibling information in
  the patterns, an over-approximation col_ctors of the set of constructors
  a well-typed value can have there.

    - If that set is unknown (NONE) the matrix is exhaustive when the
      default matrix is: only rows starting with a wildcard can match a
      value whose constructor is not mentioned.

    - If the set is known, the matrix is exhaustive when every
      specialised matrix is: each constructor of the set is considered in
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

(* the theories whose names the Ancestors blocks of the source
   bring, which are the ones that its statements read: the
   overloads of every other theory come out of the interface
   while this file loads *)
let _ = hol4_ancestors "pattern_exh"
  ["ast"; "pattern_common"; "pattern_semantics"];;


(* -------------------------------------------------------------------- *
   Constructors of values.

   A well-typed value at a given position is a tagged term (TagC), an
   untagged term, i.e. a tuple (TupC), or a reference (RefC).  Literals
   are deliberately not constructors here: their type is (for all
   practical purposes) infinite, so a column of literals is never a
   complete signature.
 * -------------------------------------------------------------------- *)

let ctor_INDUCT,ctor_RECURSION = define_datatype
  "ctor = TagC (num) (num) \
   // tag and arity of a Term (SOME tag)\n\
   | TupC (num) \
   // arity of a Term NONE\n\
   | RefC \
   // a RefPtr";;

let ctor_arity_def = define_cases
  [`ctor_arity (TagC t a) = a`;
   `ctor_arity (TupC a) = a`;
   `ctor_arity RefC = 1`];;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let anys_def,anys_ind = define_wf
  `MEASURE (\x0. (\n. n) x0)`
  [`anys 0 = []`;
   `anys (SUC n) = CONS pattern_semantics_Any (anys n)`];;


(* -------------------------------------------------------------------- *
   Removing Or-patterns.

   expand p is the list of Or-free patterns p can be split into.  Given
   that pmatch does not type-fail, p matches a value exactly when one of
   the patterns in expand p does.
 * -------------------------------------------------------------------- *)

let add_head_def,add_head_ind = define_rec
  [`add_head x [] = []`;
   `add_head x (CONS ys yss) = CONS (CONS x ys) (add_head x yss)`];;

let mk_prods_def,mk_prods_ind = define_rec
  [`mk_prods [] ys = []`;
   `mk_prods (CONS x xs) ys = APPEND (add_head x ys) (mk_prods xs
  ys)`];;

let mk_refs_def,mk_refs_ind = define_rec
  [`mk_refs [] = []`;
   `mk_refs (CONS p ps) = CONS (pattern_semantics_Ref p) (mk_refs
  ps)`];;

let mk_conses_def,mk_conses_ind = define_rec
  [`mk_conses t [] = []`;
   `mk_conses t (CONS ps pss) = CONS (pattern_semantics_Cons t ps)
  (mk_conses t pss)`];;

(* the termination relation that HOL4 gives is
     MEASURE (\x. match x with INL p -> pattern_semantics_pat_size p |
       INR ps -> list_size pattern_semantics_pat_size ps)
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
let expand_def,expand_ind = define_mutual_rec
  [`expand (pattern_semantics_Any:pattern_semantics_pat) =
  [(pattern_semantics_Any:pattern_semantics_pat)]`;
   `expand (Lit l:pattern_semantics_pat) = [(Lit
  l:pattern_semantics_pat)]`;
   `expand (Or p q:pattern_semantics_pat) = APPEND (expand p) (expand
  q)`;
   `expand (pattern_semantics_Ref p:pattern_semantics_pat) = mk_refs
  (expand p)`;
   `expand (pattern_semantics_Cons t ps:pattern_semantics_pat) =
  mk_conses t (expand_list ps)`;
   `expand_list [] = [[]]`;
   `expand_list (CONS p ps) = mk_prods (expand p) (expand_list ps)`];;

let mk_rows_def,mk_rows_ind = define_rec
  [`mk_rows [] = []`;
   `mk_rows (CONS p ps) = CONS [p] (mk_rows ps)`];;

let or_rows_def,or_rows_ind = define_rec
  [`or_rows [] = []`;
   `or_rows (CONS (p,e) rows) = APPEND (mk_rows (expand p))
  (or_rows rows)`];;


(* -------------------------------------------------------------------- *
   The constructors a head pattern allows a well-typed value to have.

   NONE means "no information", i.e. every constructor is allowed.  Note
   that a missing sibling list (Cons (SOME (t,NONE)) _), which is how
   exceptions are encoded, gives no information, and neither does a
   literal pattern.
 * -------------------------------------------------------------------- *)

let tag_ctors_def,tag_ctors_ind = define_rec
  [`tag_ctors [] = []`;
   `tag_ctors (CONS (t,a) sibs) = CONS (TagC t a) (tag_ctors sibs)`];;

let ctor_nub_def,ctor_nub_ind = define_rec
  [`ctor_nub [] = []`;
   `ctor_nub (CONS x xs) = (if MEM x xs then ctor_nub xs else CONS
  x (ctor_nub xs))`];;

let ctors_of_def = new_definition
  `ctors_of x1 =
      match x1 with
        (pattern_semantics_Any:pattern_semantics_pat) -> NONE
      | (Lit _1) -> NONE
      | (Or _2 _3) -> NONE
      | (pattern_semantics_Ref _4) -> SOME [RefC]
      | (pattern_semantics_Cons NONE qs) -> SOME [TupC (LENGTH qs)]
      | (pattern_semantics_Cons (SOME (t,NONE)) qs) -> NONE
      | (pattern_semantics_Cons (SOME (t,SOME sibs)) qs) ->
     SOME (ctor_nub (CONS (TagC t (LENGTH qs)) (tag_ctors sibs)))`;;

let ctor_keep_def,ctor_keep_ind = define_rec
  [`ctor_keep [] ys = []`;
   `ctor_keep (CONS x xs) ys =
      (if MEM x ys then CONS x (ctor_keep xs ys) else ctor_keep
        xs ys)`];;

let ctor_inter_def = new_definition
  `ctor_inter xs ys =
      match (xs,ys) with
        (NONE,ys) -> ys
      | (xs,NONE) -> xs
      | ((SOME xs),(SOME ys)) -> SOME (ctor_keep xs ys)`;;

let _ = size_thms "pattern_semantics_pat";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let col_ctors_def,col_ctors_ind = define_wf
  `MEASURE (\x0. list_size pattern_semantics_pat_size1 x0)`
  [`col_ctors [] = NONE`;
   `col_ctors (CONS [] rows) = col_ctors rows`;
   `col_ctors (CONS (CONS p _5) rows) = ctor_inter (ctors_of p)
  (col_ctors rows)`];;


(* -------------------------------------------------------------------- *
   Specialised and default matrices.

   spec_row c takes the rows that can match a value whose head
   constructor is c, and replaces the head pattern by the patterns for
   the arguments of c.  default_row keeps only the rows that start with a
   wildcard, dropping the head pattern.
 * -------------------------------------------------------------------- *)

let spec_row_def = new_definition
  `spec_row c x2 =
      match x2 with
        [] -> []
      | CONS (pattern_semantics_Any:pattern_semantics_pat) rest ->
        [APPEND (anys (ctor_arity c)) rest]
      | (CONS (pattern_semantics_Cons NONE qs) rest) ->
     (if c = TupC (LENGTH qs) then [APPEND qs rest] else [])
      | (CONS (pattern_semantics_Cons (SOME ts) qs) rest) ->
     (if c = TagC (FST ts) (LENGTH qs) then [APPEND qs rest] else [])
      | (CONS (pattern_semantics_Ref q) rest) -> (if c = RefC then
        [CONS q rest] else [])
      | (CONS (Lit l) rest) -> []
      | (CONS (Or p q) rest) -> []`;;

let spec_mat_def,spec_mat_ind = define_rec
  [`spec_mat c [] = []`;
   `spec_mat c (CONS r rows) = APPEND (spec_row c r) (spec_mat c
  rows)`];;

let spec_mats_def,spec_mats_ind = define_rec
  [`spec_mats [] rows = []`;
   `spec_mats (CONS c cs) rows = CONS (spec_mat c rows) (spec_mats
  cs rows)`];;

let default_row_def = new_definition
  `default_row x1 =
      match x1 with
        CONS (pattern_semantics_Any:pattern_semantics_pat) rest ->
          [rest]
      | _6 -> []`;;

let default_mat_def,default_mat_ind = define_rec
  [`default_mat [] = []`;
   `default_mat (CONS r rows) = APPEND (default_row r) (default_mat
  rows)`];;


(* -------------------------------------------------------------------- *
   Measures used for the termination of exh_matrix.

   Specialising strictly decreases the number of constructor nodes in the
   matrix, provided some head pattern is a constructor pattern -- which
   is exactly what col_ctors returning SOME guarantees.  Taking the
   default matrix does not increase that count, and strictly decreases
   the total number of columns.
 * -------------------------------------------------------------------- *)

(* the termination relation that HOL4 gives is
     MEASURE (\x. match x with INL p -> pattern_semantics_pat_size p |
       INR ps -> list_size pattern_semantics_pat_size ps)
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
let pat_weight_def,pat_weight_ind = define_mutual_rec
  [`pat_weight (pattern_semantics_Any:pattern_semantics_pat) =
  (0:num)`;
   `pat_weight (Lit l:pattern_semantics_pat) = ((0):num)`;
   `pat_weight (Or p q:pattern_semantics_pat) = ((1 + pat_weight p +
  pat_weight q):num)`;
   `pat_weight (pattern_semantics_Ref p:pattern_semantics_pat) = ((1
  + pat_weight p):num)`;
   `pat_weight (pattern_semantics_Cons t ps:pattern_semantics_pat) =
  ((1 + pats_weight ps):num)`;
   `pats_weight [] = 0`;
   `pats_weight (CONS p ps) = pat_weight p + pats_weight ps`];;

let mat_weight_def,mat_weight_ind = define_rec
  [`mat_weight [] = 0`;
   `mat_weight (CONS r rows) = pats_weight r + mat_weight rows`];;

let mat_len_def,mat_len_ind = define_rec
  [`mat_len [] = 0`;
   `mat_len (CONS r rows) = LENGTH r + mat_len rows`];;

let mats_weight_def,mats_weight_ind = define_rec
  [`mats_weight [] = 0`;
   `mats_weight (CONS m ms) = MAX (mat_weight m) (mats_weight ms)`];;

let mats_len_def,mats_len_ind = define_rec
  [`mats_len [] = 0`;
   `mats_len (CONS m ms) = MAX (mat_len m) (mats_len ms)`];;

(* [local] *)
let pats_weight_append = prove
 (`!xs ys. pats_weight (APPEND xs ys) = pats_weight xs + pats_weight
  ys`,
  (LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[APPEND; pat_weight_def] THEN
    ARITH_TAC));;

(* [local] *)
let pats_weight_anys = prove
 (`!n. pats_weight (anys n) = 0`,
  (INDUCT_TAC THEN ASM_REWRITE_TAC[anys_def; pat_weight_def;
    ADD_CLAUSES]));;

(* [local] *)
let mat_weight_append = prove
 (`!xs ys. mat_weight (APPEND xs ys) = mat_weight xs + mat_weight ys`,
  (LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[APPEND; mat_weight_def] THEN
    ARITH_TAC));;

(* [local] *)
let mat_len_append = prove
 (`!xs ys. mat_len (APPEND xs ys) = mat_len xs + mat_len ys`,
  (LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[APPEND; mat_len_def] THEN
    ARITH_TAC));;

(* [local] *)
let mat_weight_spec_row = prove
 (`!c r. mat_weight (spec_row c r) <= pats_weight r`,
  CHEAT_TAC);;

(* [local] *)
let mat_weight_spec_mat = prove
 (`!c rows. mat_weight (spec_mat c rows) <= mat_weight rows`,
  CHEAT_TAC);;

(* [local] *)
let mat_weight_spec_row_less = prove
 (`!c p r. ~(ctors_of p = NONE) ==>
           mat_weight (spec_row c (CONS p r)) < pats_weight (CONS p
             r)`,
  CHEAT_TAC);;

(* [local] *)
let mat_weight_spec_mat_less = prove
 (`!c rows cs. col_ctors rows = SOME cs ==>
               mat_weight (spec_mat c rows) < mat_weight rows`,
  CHEAT_TAC);;

(* [local] *)
let mat_weight_default_mat = prove
 (`!rows. mat_weight (default_mat rows) <= mat_weight rows`,
  CHEAT_TAC);;

(* [local] *)
let mat_len_default_mat = prove
 (`!rows. mat_len (default_mat rows) <= mat_len rows`,
  CHEAT_TAC);;

(* [local] *)
let mats_weight_spec_mats = prove
 (`!cs rows ds.
     col_ctors rows = SOME ds ==>
     mats_weight (spec_mats cs rows) < mat_weight rows`,
  CHEAT_TAC);;

(* [local] *)
let mat_len_default_mat_less = prove
 (`!r rows. ~(r = []) ==>
            mat_len (default_mat (CONS r rows)) < mat_len (CONS r
              rows)`,
  CHEAT_TAC);;


(* -------------------------------------------------------------------- *
   The matrix algorithm and the entry point.
 * -------------------------------------------------------------------- *)

(* the termination relation that HOL4 gives is
     inv_image ((<) LEX (<) LEX (<))
            (\x. match x with INL rows -> (mat_weight rows,mat_len
              rows,(0:num)) | INR ms -> (mats_weight ms,mats_len ms,LENGTH
              ms + 1))
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 pattern_exhScript.sml:377-389: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let exh_matrix_def,exh_matrix_ind = define_mutual_shaped_rec_cheat
  "maplist>measure"
  [`exh_matrix [] = F`;
   `exh_matrix (CONS r rows) =
      (if NULL r then T else
         match col_ctors (CONS r rows) with NONE -> exh_matrix
           (default_mat (CONS r rows)) | SOME cs -> exh_mats
           (spec_mats cs (CONS r rows)))`;
   `exh_mats [] = T`;
   `exh_mats (CONS m ms) = (exh_matrix m /\ exh_mats ms)`];;

let exh_rows_def = new_definition
  `exh_rows rows = exh_matrix (or_rows rows)`;;


(* -------------------------------------------------------------------- *
   A tail-recursive version, for execution.

   exh_matrix is a mutual recursion justified by a non-structural
   measure, which cv_translation cannot take.  exh_all is a single
   tail recursion that keeps the matrices still to be checked in a
   worklist.  It computes exactly the same answer -- exh_rows_eq below --
   so it is the equation the compiler is run through.

   Its termination is justified by counting the steps the original
   recursion takes: exh_steps has exactly the recursion structure of
   exh_matrix, hence exactly the same termination argument, and every
   step exh_all makes consumes one of those steps.
 * -------------------------------------------------------------------- *)

(* the termination relation that HOL4 gives is
     inv_image ((<) LEX (<) LEX (<))
            (\x. match x with INL rows -> (mat_weight rows,mat_len
              rows,(0:num)) | INR ms -> (mats_weight ms,mats_len ms,LENGTH
              ms + 1))
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 pattern_exhScript.sml:420-432: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let exh_steps_def,exh_steps_ind = define_mutual_guess_cheat
  [`exh_steps [] = (1:num)`;
   `exh_steps (CONS r rows) =
      (((if NULL r then 1 else
         match col_ctors (CONS r rows) with NONE -> 1 + exh_steps
           (default_mat (CONS r rows)) | SOME cs -> 1 +
           exh_steps_list (spec_mats cs (CONS r rows)))):num)`;
   `exh_steps_list [] = 0`;
   `exh_steps_list (CONS m ms) = exh_steps m + exh_steps_list ms`];;

(* [local] *)
let exh_steps_list_append = prove
 (`!xs ys. exh_steps_list (APPEND xs ys) = exh_steps_list xs +
  exh_steps_list ys`,
  (LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[APPEND; exh_steps_def] THEN
    ARITH_TAC));;

(* the termination relation that HOL4 gives is
     MEASURE exh_steps_list
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 pattern_exhScript.sml:448-452: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let exh_all_def,exh_all_ind = define_guess_cheat
  [`exh_all [] = T`;
   `exh_all (CONS [] ms) = F`;
   `exh_all (CONS (CONS r rows) ms) =
      (if NULL r then exh_all ms else
         match col_ctors (CONS r rows) with NONE -> exh_all
           (CONS (default_mat (CONS r rows)) ms) | SOME cs ->
           exh_all (APPEND (spec_mats cs (CONS r rows)) ms))`];;

(* [local] *)
let exh_mats_append = prove
 (`!xs ys. exh_mats (APPEND xs ys) <=> exh_mats xs /\ exh_mats ys`,
  (LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[APPEND; exh_matrix_def;
    CONJ_ASSOC]));;

(* [local] *)
let exh_all_thm = prove
 (`!ms. exh_all ms <=> exh_mats ms`,
  CHEAT_TAC);;

let exh_rows_eq = prove
 (`exh_rows rows <=> exh_all [or_rows rows]`,
  (REWRITE_TAC[exh_rows_def; exh_all_thm; exh_matrix_def]));;


(* ====================================================================== *
   Soundness

   The theorem to prove is the one that justifies replacing the last row
   by a wildcard:

     match refs rows v <> NONE /\ exh_rows rows ==>
     match refs rows v <> SOME MatchFailure

   Read through match_def that says: if no row type-fails on v, then some
   row succeeds on v.  Everything below is phrased in those terms, at the
   level of matrices: "ok" means no row type-fails, "hit" means some row
   succeeds.
 * ====================================================================== *)


(* ---------------------------------------------------------------------- *
   pand combines the results of two matches performed one after the
   other.  It is exactly how pmatch_list glues a row together, and it
   makes the case analysis below disappear into two rewrite rules.
 * ---------------------------------------------------------------------- *)

let pand_def = define_cases
  [`pand PMatchSuccess y = y`;
   `pand PMatchFailure y = (if y = PTypeFailure then PTypeFailure
  else PMatchFailure)`;
   `pand PTypeFailure y = PTypeFailure`];;

(* [local,simp] *)
let pand_simps = prove
 (`pand PMatchSuccess y = y /\
   pand x PMatchSuccess = x /\
   pand PTypeFailure y = PTypeFailure /\
   pand x PTypeFailure = PTypeFailure`,
  CHEAT_TAC);;

(* [local,simp] *)
let pand_eq_PTypeFailure = prove
 (`(pand x y = PTypeFailure) <=> x = PTypeFailure \/ y = PTypeFailure`,
  CHEAT_TAC);;

(* [local,simp] *)
let pand_eq_PMatchSuccess = prove
 (`(pand x y = PMatchSuccess) <=> x = PMatchSuccess /\ y =
  PMatchSuccess`,
  CHEAT_TAC);;

(* [local] *)
let pand_assoc = prove
 (`pand (pand x y) z = pand x (pand y z)`,
  CHEAT_TAC);;

(* From here on pmatch_list is only ever unfolded through these four
   rewrites, never through pmatch_def, the raw clauses of pmatch_def
   would compete with pmatch_list_cons and leave case expressions
   behind. *)

(* [local,simp] *)
let pmatch_Any = prove
 (`pmatch refs (pattern_semantics_Any:pattern_semantics_pat) v =
  PMatchSuccess`,
  (REWRITE_TAC[pattern_semantics_pmatch_def]));;

(* [local,simp] *)
let pmatch_list_nil = prove
 (`pmatch_list refs [] [] = PMatchSuccess /\
   pmatch_list refs [] (CONS v vs) = PTypeFailure /\
   pmatch_list refs (CONS p ps) [] = PTypeFailure`,
  (REWRITE_TAC[pattern_semantics_pmatch_def]));;

(* [local,simp] *)
let pmatch_list_cons = prove
 (`pmatch_list refs (CONS p ps) (CONS v vs) =
   pand (pmatch refs p v) (pmatch_list refs ps vs)`,
  CHEAT_TAC);;

(* [local] *)
let pmatch_list_LENGTH = prove
 (`!ps vs. ~(pmatch_list refs ps vs = PTypeFailure) ==> LENGTH ps =
  LENGTH vs`,
  CHEAT_TAC);;

(* [local] *)
let pmatch_list_append = prove
 (`!ps us qs ws refs.
     LENGTH ps = LENGTH us ==>
     pmatch_list refs (APPEND ps qs) (APPEND us ws) =
     pand (pmatch_list refs ps us) (pmatch_list refs qs ws)`,
  CHEAT_TAC);;

(* [local,simp] *)
let LENGTH_anys = prove
 (`!n. LENGTH (anys n) = n`,
  (INDUCT_TAC THEN ASM_REWRITE_TAC[anys_def; LENGTH]));;

(* Stated with the width as an argument rather than as LENGTH as, so that
   it also rewrites the anys (ctor_arity c) that spec_row produces. *)
(* [local,simp] *)
let pmatch_list_anys = prove
 (`!n as refs.
     pmatch_list refs (anys n) as =
     (if LENGTH as = n then PMatchSuccess else PTypeFailure)`,
  CHEAT_TAC);;


(* ---------------------------------------------------------------------- *
   What the first-order list-building helpers put into their results.
 * ---------------------------------------------------------------------- *)

(* [local,simp] *)
let MEM_ctor_nub = prove
 (`!l x. MEM x (ctor_nub l) <=> MEM x l`,
  (LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ctor_nub_def; MEM] THEN
   GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[MEM] THEN
     ASM_MESON_TAC[]));;

(* [local,simp] *)
let MEM_ctor_keep = prove
 (`!xs ys x. MEM x (ctor_keep xs ys) <=> MEM x xs /\ MEM x ys`,
  (LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ctor_keep_def; MEM] THEN
   REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[MEM] THEN
   ASM_MESON_TAC[]));;

(* [local] *)
let MEM_tag_ctors = prove
 (`!sibs t a. MEM (TagC t a) (tag_ctors sibs) <=> MEM (t,a) sibs`,
  CHEAT_TAC);;

(* [local] *)
let MEM_spec_mats = prove
 (`!cs c rows. MEM c cs ==> MEM (spec_mat c rows) (spec_mats cs rows)`,
  (LIST_INDUCT_TAC THEN REWRITE_TAC[spec_mats_def; MEM] THEN
   REPEAT STRIP_TAC THEN ASM_SIMP_TAC[]));;

(* [local,simp] *)
let MEM_add_head = prove
 (`!yss x ys. MEM ys (add_head x yss) <=> (?zs. MEM zs yss /\ ys =
  CONS x zs)`,
  (LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[add_head_def; MEM] THEN
    MESON_TAC[]));;

(* [local,simp] *)
let MEM_mk_prods = prove
 (`!xs yss zs. MEM zs (mk_prods xs yss) <=>
               (?x ys. MEM x xs /\ MEM ys yss /\ zs = CONS x ys)`,
  (LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[mk_prods_def; MEM;
    MEM_APPEND; MEM_add_head] THEN
   MESON_TAC[]));;

(* [local,simp] *)
let MEM_mk_refs = prove
 (`!ps q. MEM q (mk_refs ps) <=> (?p. MEM p ps /\ q =
  pattern_semantics_Ref p)`,
  (LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[mk_refs_def; MEM] THEN
    MESON_TAC[]));;

(* [local,simp] *)
let MEM_mk_conses = prove
 (`!pss t q. MEM q (mk_conses t pss) <=> (?ps. MEM ps pss /\ q =
  pattern_semantics_Cons t ps)`,
  (LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[mk_conses_def; MEM] THEN
    MESON_TAC[]));;

(* [local,simp] *)
let MEM_mk_rows = prove
 (`!ps r. MEM r (mk_rows ps) <=> (?p. MEM p ps /\ r = [p])`,
  (LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[mk_rows_def; MEM] THEN
    MESON_TAC[]));;


(* ---------------------------------------------------------------------- *
   Expanding Or-patterns.

   An expanded pattern never type-fails where the original does not, and
   if an expanded pattern matches then so does the original.  (The
   converse also holds, but soundness does not need it.)
 * ---------------------------------------------------------------------- *)

(* [local] *)
let LENGTH_expand_list = prove
 (`!ps qs. MEM qs (expand_list ps) ==> LENGTH qs = LENGTH ps`,
  (LIST_INDUCT_TAC THEN REWRITE_TAC[expand_def; MEM; MEM_mk_prods]
    THEN
   REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[LENGTH] THEN (ASSUM_LIST
     (MAP_EVERY (fun th ->
      TRY (IMP_RES_THEN ASSUME_TAC th)))) THEN
   ASM_REWRITE_TAC[]));;

(* [local] *)
let expand_thm = prove
 (`(!p q refs v.
      MEM q (expand p) /\ ~(pmatch refs p v = PTypeFailure) ==>
        ~(pmatch refs q v = PTypeFailure) /\
      (pmatch refs q v = PMatchSuccess ==> pmatch refs p v =
        PMatchSuccess)) /\
   (!ps qs refs vs.
      MEM qs (expand_list ps) /\ ~(pmatch_list refs ps vs =
        PTypeFailure) ==> ~(pmatch_list refs qs vs = PTypeFailure) /\
      (pmatch_list refs qs vs = PMatchSuccess ==>
       pmatch_list refs ps vs = PMatchSuccess))`,
  CHEAT_TAC);;


(* ---------------------------------------------------------------------- *
   The constructor of a value, and its arguments.

   dest_val is only defined for the values that a constructor pattern can
   possibly match; literals and Other have no constructor.  Note that a
   reference has a constructor only when the pointer is in the heap,
   which is exactly when Ref does not type-fail.
 * ---------------------------------------------------------------------- *)

let dest_val_def = new_definition
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

(* [local] *)
let dest_val_eq_SOME = prove
 (`dest_val refs v = SOME (c,as) <=>
   (?t. v = pattern_semantics_Term (SOME t) as /\ c = TagC t (LENGTH
     as)) \/
   (v = pattern_semantics_Term NONE as /\ c = TupC (LENGTH as)) \/
   (?r w. v = pattern_semantics_RefPtr r /\ FLOOKUP refs r = SOME w
     /\ as = [w] /\ c = RefC)`,
  CHEAT_TAC);;

(* [local] *)
let LENGTH_dest_val = prove
 (`dest_val refs v = SOME (c,as) ==> LENGTH as = ctor_arity c`,
  (REWRITE_TAC[dest_val_eq_SOME] THEN REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC[ctor_arity_def; LENGTH; ONE]));;

(* A head pattern that reports a constructor set really does confine a
   value that it does not type-fail on to that set. *)

(* [local] *)
let ctors_of_thm = prove
 (`ctors_of p = SOME xs /\ ~(pmatch refs p v = PTypeFailure) ==>
   (?c as. dest_val refs v = SOME (c,as) /\ MEM c xs)`,
  CHEAT_TAC);;

(* ... and therefore so does the intersection over a whole column. *)

(* [local] *)
let col_ctors_thm = prove
 (`!M cs refs v vs.
     col_ctors M = SOME cs /\
     ALL (\r. ~(pmatch_list refs r (CONS v vs) = PTypeFailure)) M ==>
     (?c as. dest_val refs v = SOME (c,as) /\ MEM c cs)`,
  CHEAT_TAC);;


(* ---------------------------------------------------------------------- *
   Specialising and defaulting preserve match results.

   This is the one fact that makes the whole induction go through: every
   row of a transformed matrix gives exactly the same three-valued match
   result, against the transformed value vector, as the row it came from
   does against the original one.  Rows that are dropped simply have no
   counterpart, which costs nothing here -- dropping rows can only make a
   matrix less exhaustive, and soundness is the direction we need.
 * ---------------------------------------------------------------------- *)

(* [local] *)
let spec_row_thm = prove
 (`!c r row refs v vs as.
     dest_val refs v = SOME (c,as) /\ MEM row (spec_row c r) ==>
     pmatch_list refs row (APPEND as vs) = pmatch_list refs r (CONS
       v vs)`,
  CHEAT_TAC);;

(* [local] *)
let spec_mat_MEM = prove
 (`!M c as refs v vs row.
     dest_val refs v = SOME (c,as) /\ MEM row (spec_mat c M) ==>
     (?r. MEM r M /\
         pmatch_list refs row (APPEND as vs) = pmatch_list refs r
           (CONS v vs))`,
  CHEAT_TAC);;

(* [local] *)
let default_row_thm = prove
 (`!r row refs v vs.
     MEM row (default_row r) ==>
     pmatch_list refs row vs = pmatch_list refs r (CONS v vs)`,
  CHEAT_TAC);;

(* [local] *)
let default_mat_MEM = prove
 (`!M refs v vs row.
     MEM row (default_mat M) ==>
     (?r. MEM r M /\ pmatch_list refs row vs = pmatch_list refs r
       (CONS v vs))`,
  (LIST_INDUCT_TAC THEN REWRITE_TAC[default_mat_def; MEM; MEM_APPEND]
    THEN
   REPEAT STRIP_TAC THENL
    [EXISTS_TAC `h:(pattern_semantics_pat)list` THEN REWRITE_TAC[]
      THEN
     MATCH_MP_TAC default_row_thm THEN ASM_REWRITE_TAC[];
     FIRST_X_ASSUM (MP_TAC o SPECL
       [`refs:(num,pattern_semantics_term)fmap`;
       `v:pattern_semantics_term`;
       `vs:pattern_semantics_term list`;
       `row:(pattern_semantics_pat)list`]) THEN
     ASM_REWRITE_TAC[] THEN MESON_TAC[]]));;


(* ---------------------------------------------------------------------- *
   Soundness of the matrix algorithm.

   "ok" (no row type-fails) is inherited by the sub-matrices, and "hit"
   (some row succeeds) is reflected back out of them.
 * ---------------------------------------------------------------------- *)

(* [local] *)
let exh_matrix_thm = prove
 (`(!M refs vs.
      exh_matrix M /\ ALL (\r. ~(pmatch_list refs r vs =
        PTypeFailure)) M ==>
      EX (\r. pmatch_list refs r vs = PMatchSuccess) M) /\
   (!ms m refs vs.
      exh_mats ms /\ MEM m ms /\
      ALL (\r. ~(pmatch_list refs r vs = PTypeFailure)) m ==>
      EX (\r. pmatch_list refs r vs = PMatchSuccess) m)`,
  CHEAT_TAC);;


(* ---------------------------------------------------------------------- *
   From the matrix back to match.
 * ---------------------------------------------------------------------- *)

(* [local] *)
let match_no_PTypeFailure = prove
 (`!rows. ~(pattern_semantics_match refs rows v = NONE) ==>
          ALL (\(p,e). ~(pmatch refs p v = PTypeFailure)) rows`,
  CHEAT_TAC);;

(* [local] *)
let match_EXISTS = prove
 (`!rows. ~(pattern_semantics_match refs rows v = NONE) /\
          EX (\(p,e). pmatch refs p v = PMatchSuccess) rows ==>
            ~(pattern_semantics_match refs rows v = SOME MatchFailure)`,
  CHEAT_TAC);;

(* [local] *)
let or_rows_ok = prove
 (`!rows. ALL (\(p,e). ~(pmatch refs p v = PTypeFailure)) rows ==>
          ALL (\r. ~(pmatch_list refs r [v] = PTypeFailure))
            (or_rows rows)`,
  CHEAT_TAC);;

(* [local] *)
let or_rows_hit = prove
 (`!rows. ALL (\(p,e). ~(pmatch refs p v = PTypeFailure)) rows /\
          EX (\r. pmatch_list refs r [v] = PMatchSuccess) (or_rows
            rows) ==>
          EX (\(p,e). pmatch refs p v = PMatchSuccess) rows`,
  CHEAT_TAC);;


(* ---------------------------------------------------------------------- *
   Soundness of exh_rows: the theorem the pattern compiler needs.
 * ---------------------------------------------------------------------- *)

let exh_rows_thm = prove
 (`~(pattern_semantics_match refs rows v = NONE) /\ exh_rows rows ==>
  ~(pattern_semantics_match refs rows v = SOME MatchFailure)`,
  CHEAT_TAC);;

(* and the overloads that this file cannot see are back in the
   interface *)
let _ = unhide_overloads ();;
