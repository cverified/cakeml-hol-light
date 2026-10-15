(* ======================================================== *)
(*  misc: ported from HOL4's
    misc/miscScript.sml  *)
(* ======================================================== *)

(*
   Miscellaneous definitions and minor lemmas used throughout the
   development.
*)

(* Misc. lemmas (without any compiler constants) *)

needs "lib/alignment.ml";;
needs "lib/binary_ieee.ml";;
needs "lib/bitstring.ml";;
needs "lib/byte.ml";;
needs "lib/comparison.ml";;
needs "lib/indexedLists.ml";;
needs "lib/integer_word.ml";;
needs "lib/lprefix_lub.ml";;
needs "lib/machine_ieee.ml";;
needs "lib/set_sep.ml";;
needs "lib/sorting.ml";;
needs "lib/sptree.ml";;
needs "lib/ternaryComparisons.ml";;
(* HOL4 ancestors outside the port: alist arithmetic blast bag combin
   container list pred_set finite_map rich_list llist option pair
   relation toto bit words string address path res_quan *)

(* Total version of THE *)
let the_def = cake_define_list
  [`the _1 (SOME x) = x`;
   `the x NONE = x`];;

let opt_bind_def = cake_define
  `opt_bind n v e =
     (match n with NONE -> e | SOME n' -> (n',v) :: e)`;;

(* Note: This globally hides constants over the reals that gets imported
   through machine_ieeeTheory *)

(* this is copied in preamble.sml, but needed here to avoid cyclic dep
   *)
(* HOL4 ML code, not ported:
fun drule th =
  first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]
    th))
val rveq = rpt BasicProvers.VAR_EQ_TAC
val match_exists_tac = part_match_exists_tac (hd o strip_conj)
val asm_exists_tac = first_assum(match_exists_tac o concl)
*)
(* -- *)

(* TODO: move/categorize *)

(* theorem behind impl_tac *)

(* used elsewhere in cakeml *)

(* this is
     read_bytearray a c gb = OPT_MMAP gb (GENLIST (λi. a + n2w i) c)
*)
let read_bytearray_def = cake_define_list
  [`read_bytearray a 0 get_byte' = SOME []`;
   `read_bytearray a (SUC n) get_byte' =
         (match get_byte' a with NONE -> NONE | SOME b -> (match
           read_bytearray (a + (n2w 1)) n get_byte' with NONE -> NONE
           | SOME bs -> SOME (b :: bs)))`];;

(* HOL to have OPT_MMAP f l1 = SOME l2 ==> (LENGTH l2 = LENGTH l1) *)

let shift_seq_def = cake_define
  `misc_shift_seq k s = (\i. s (i + (k:num)))`;;
hol4_overload "shift_seq" "misc_shift_seq";;

(* TODO: Used once in all of CakeML: could probably be pushed back to
   use-site*)

(* only used in proof of tlookup_bij_iff *)

(* never used *)

(* used only in clos_callProof -
   HOL has DISJOINT_IMAGE:
     |- (!x y. f x = f y <=> x = y) ==>
        (DISJOINT (IMAGE f x) (IMAGE f y) <=> DISJOINT x y
*)

(* disgusting and used only in clos_callProof *)

(* HOL4 overload (expanded in the port):
     LLOOKUP = λl n. oEL n l *)

(* app_list stuff should be in an app_list theory *)
let app_list_INDUCT,app_list_RECURSION = define_datatype
  "app_list = misc_List ('a list) | misc_Append (app_list) (app_list) \
   | misc_Nil";;
hol4_overload "List" "misc_List";;
hol4_overload "Append" "misc_Append";;
hol4_overload "Nil" "misc_Nil";;

let append_aux_def = cake_define_list
  [`append_aux Nil aux = aux`;
   `append_aux (List xs:'a app_list) aux = xs ++ aux`;
   `append_aux (Append l1 l2:'a app_list) aux = append_aux l1
  (append_aux l2 aux)`];;

let append_def = cake_define
  `append l = append_aux l []`;;

let SmartAppend_def = cake_define
  `SmartAppend l1 l2 =
        match (l1,l2) with
          (Nil,l2) -> l2
        | (l1,Nil) -> l1
        | (l1,l2) -> Append l1 l2`;;

(* instant derivation from LIST_EQ_REWRITE *)

(* TODO - already in HOL as ZIP_GENLIST *)

(* used once *)

(* used three times, once with MIN_DEF alongside, which turns it into
   LENGTH_TAKE_EQ
*)

(* should be switched in orientation; looks like an attempt to get
   congruence
   rule *)

(* only used in theorem immediately below *)

(* only used in bvi_to_dataProof *)

(* only used in examples/stackProg; oriented badly *)

let lookup_any_def = cake_define
  `lookup_any x sp d =
     (match lookup x sp with NONE -> d | SOME m -> m)`;;

let fromList2_def = cake_define
  `fromList2 l = SND (FOLDL (\(i,t) a. (i + 2,insert i a t)) (0,LN)
  l)`;;

(* used in only one place: stack_to_labProof *)

let zlookup_def = cake_define
  `zlookup m k = (match lookup k m with NONE -> 0 | SOME k -> k)`;;

let tlookup_def = cake_define
  `tlookup m k = (match lookup k m with NONE -> k | SOME k -> k)`;;

(* should be composition of oEL and as-yet-undefined "THE default" *)
let any_el_def = cake_define_list
  [`any_el n [] d = d`;
   `any_el n (x :: xs) d = (if n = 0 then x else any_el (n - (1:num))
  xs d)`];;

let update_resize_def = cake_define
  `update_resize ls default v n =
     (if n < LENGTH ls then
       LUPDATE v n ls else
       LUPDATE v n (ls ++ REPLICATE ((n * 2 + 1) - LENGTH ls)
         default))`;;

(*TODO upstream*)

(*Or should it be MAX x (MAX_LIST xs)*)

(* never used *)
let list_inter_def = cake_define
  `list_inter xs ys = FILTER (\y. MEM y xs) ys`;;

let max3_def = cake_define
  `max3 (x:num) y z = (if x > y then (if z > x then z else x) else
  (if z > y then z else y))`;;

(* TODO - candidate for move to HOL, but in simpler form without
   accumulator *)
(* only used in inferProg *)
let anub_def = cake_define_list
  [`anub [] acc = []`;
   `anub ((k,v) :: ls) acc =
       (if MEM k acc then anub ls acc else
       (k,v) :: (anub ls (k :: acc)))`];;

(* HOL4 ML code, not ported:
val anub_ind = theorem"anub_ind"
*)

(* terrible rewrite *)

new_type_abbrev("misc_num_set",`: 1 spt`);;
(* HOL4 type abbreviation (expanded in the port):
     num_map = 'a spt *)

(* only used below in proof of theorem that is in turn used just twice
   *)

(* only used below in proof of theorem that is in turn used just twice
   *)

(* used only twice, both times in candle/set-theory *)

let least_from_def = cake_define
  `least_from P n = (if (?x. P x /\ n <= x) then LEAST (\x. P x /\ n
  <= x) else LEAST P)`;;

(* used just once; better as
     transitive R ==> transitive (OPTREL R)
   or that with transitive expanded out *)

let UPDATE_LIST_def = cake_define
  `UPDATE_LIST = FOLDL (C (UNCURRY UPDATE))`;;

(* should be using indexedLists$findi, or INDEX_OF *)
let find_index_def = cake_define_list
  [`find_index _2 [] _3 = NONE`;
   `find_index y (x :: xs) n = (if x = y then SOME n else find_index
  y xs (n + 1))`];;

(* HOL4 ML code, not ported:
val ALOOKUP_find_index_SOME = Q.prove(
  `∀env. (ALOOKUP env k = SOME v) ⇒
      ∀m. ∃i. (find_index k (MAP FST env) m = SOME (m+i)) ∧
          (v = EL i (MAP SND env))`,
  Induct >> simp[] >> Cases >>
  srw_tac[][find_index_def] >> full_simp_tac(srw_ss())[] >>
  first_x_assum(qspec_then`m+1`mp_tac)>>srw_tac[][]>>srw_tac[][]>>
  qexists_tac`SUC i`>>simp[])
|> SPEC_ALL |> UNDISCH_ALL |> Q.SPEC`0` |> DISCH_ALL |> SIMP_RULE
  (srw_ss())[]
*)

(* surely better with UNZIP rather than ZIP: i.e., UNZIP l1 = (a,b)...
   *)

(* never used *)

(* never used *)

(* used twice, and only in source_to_flatProof *)

(* never used *)

let between_def = cake_define
  `between x y z <=> (x:num) <= z /\ z < y`;;

(* never used *)

(* never used *)
let fmap_linv_def = cake_define
  `fmap_linv f1 f2 <=> (FDOM f2 = FRANGE f1) /\ (!x. x IN FDOM f1 ==>
  (FLOOKUP f2 (FAPPLY f1 x) = SOME x))`;;

(* never used *)

(* never used *)

(* never used *)

(* never used *)

(* TODO - candidate for move to HOL *)

(* TODO: move elsewhere? export as rewrite? *)
(* never used *)

(* never used *)

(* Re-expressing folds *)

(* only used in flat_elimProof *)

(* never used *)

(* never used *)

(* Re-expressing curried lambdas *)

(* never used *)

(* never used *)

(* never used *)

(* never used *)

(* never used *)

(* Specialisations to identity function *)

(* never used *)

(* Specialisations to FEMPTY *)

(* FUPDATE_LIST stuff *)

(* Misc. *)


  (* --------- SO additions --------- *)

(* use INJ_MAP_EQ_IFF and INJ_DEF *)

(* never used *)

(* HOL4 ML code, not ported:
val _ = augment_srw_ss [rewrites [map_some_eq,map_some_eq_append]];
*)


(* list misc *)
(*
NB: this is weaker:
Theorem MAP_EQ_MAP_IMP =
  INJ_MAP_EQ |> SIMP_RULE (srw_ss()) [INJ_DEF]
*)

(* move into HOL? *)

let word_list_def = cake_define_list
  [`misc_word_list a [] = emp`;
   `misc_word_list a (x :: xs) = set_sep_one (a,x) * misc_word_list
  (a + bytes_in_word) xs`];;
hol4_overload "word_list" "misc_word_list";;

let word_list_exists_def = cake_define
  `word_list_exists a n =
     SEP_EXISTS (\xs. word_list a xs * cond (LENGTH xs = n))`;;

(* lookup_vars vs env = OPT_MMAP (\i. oEL i env) vs *)
let lookup_vars_def = cake_define_list
  [`lookup_vars [] env = SOME []`;
   `lookup_vars (v :: vs) env =
         (if v < LENGTH env then
           match lookup_vars vs env with SOME xs -> SOME (EL v
             env :: xs) | NONE -> NONE else NONE)`];;

(* TODO - candidate for move to HOL *)

(* TODO - candidate for move to HOL *)

(* TODO - candidate for move to HOL - though
     enumerate i0 l = MAPi (λx i. (i + i0, x)) l
*)
let enumerate_def = cake_define_list
  [`enumerate n [] = []`;
   `enumerate n (x :: xs) = (n,x) :: enumerate (n + 1) xs`];;

(* TODO - candidate for move to HOL *)

(* n.b. used in hol-reflection *)


(* TODO - candidate for move to HOL *)

let option_fold_def = cake_define_list
  [`option_fold f x NONE = x`;
   `option_fold f x (SOME y) = f y x`];;

let shift_left_def = cake_define
  `shift_left (a:'a word) n =
   (if n = 0 then a else if (a = (n2w 0)) \/ n > dimindex (:'a)
     then (n2w 0) else if n > 32 then shift_left (a << 32) (n - 32)
     else if n > 16 then shift_left (a << 16) (n - 16) else if n > 8
     then shift_left (a << 8) (n - 8) else shift_left (a << 1) (n -
     1))`;;

let shift_right_def = cake_define
  `shift_right (a:'a word) n =
   (if n = 0 then a else if (a = (n2w 0)) \/ n > dimindex (:'a)
     then (n2w 0) else if n > 32 then shift_right (a >>> 32) (n - 32)
     else if n > 16 then shift_right (a >>> 16) (n - 16) else if n >
     8 then shift_right (a >>> 8) (n - 8) else shift_right (a >>> 1)
     (n - 1))`;;

let arith_shift_right_def = cake_define
  `arith_shift_right (a:'a word) n =
   (if n = 0 then a else if (a = (n2w 0)) \/ n > dimindex (:'a) /\
     ~word_msb a then (n2w 0) else if (a = --(n2w 1)) \/ n > dimindex
     (:'a) /\ word_msb a then --(n2w 1) else if n > 32 then
     arith_shift_right (a >> 32) (n - 32) else if n > 16 then
     arith_shift_right (a >> 16) (n - 16) else if n > 8 then
     arith_shift_right (a >> 8) (n - 8) else arith_shift_right (a >>
     1) (n - 1))`;;

let any_word64_ror_def = cake_define
  `any_word64_ror (w:word64) (n:num) =
     (if 64 <= n then any_word64_ror w (n - 64) else
     if 32 <= n then any_word64_ror (word_ror w 32) (n - 32) else
     if 16 <= n then any_word64_ror (word_ror w 16) (n - 16) else
     if 8 <= n then any_word64_ror (word_ror w 8) (n - 8) else
     if 4 <= n then any_word64_ror (word_ror w 4) (n - 4) else
     if 2 <= n then any_word64_ror (word_ror w 2) (n - 2) else
     if 1 <= n then word_ror w 1 else w)`;;

let splitlines_def = cake_define
  `splitlines ls =
   (let lines = FIELDS ((=) (CHR 10)) ls in
   if NULL (LAST lines) then FRONT lines else lines)`;;

(* used once *)

(* should be made an iff in conclusion *)

(* should be set l1 ⊆ set l2 *)
let list_subset_def = cake_define
  `list_subset l1 l2 = EVERY (\x. MEM x l2) l1`;;

let list_set_eq_def = cake_define
  `list_set_eq l1 l2 <=> list_subset l1 l2 /\ list_subset l2 l1`;;

(* TODO: candidate for move to HOL;
         subspt_domain exists already but is specialised to unit *)

(* Some temporal logic definitions based on lazy lists *)
(* move into llistTheory? *)

(* computes the next position for which P holds *)
let lnext_def =
  let th = prove
   (`?Lnext. !P (ll:A llist).
       Lnext P ll = if eventually P ll then
                      if P ll then 0
                      else SUC (Lnext P (THE (LTL ll)))
                    else ARB`,
    EXISTS_TAC
     `\P (ll:A llist).
        if eventually P ll
        then minimal n. ?u. LDROP n ll = SOME u /\ P u
        else ARB` THEN
    REWRITE_TAC[] THEN REPEAT GEN_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN COND_CASES_TAC THENL
     [MATCH_MP_TAC MINIMAL_UNIQUE THEN BETA_TAC THEN CONJ_TAC THENL
       [EXISTS_TAC `ll:A llist` THEN ASM_REWRITE_TAC[LDROP_0];
        REWRITE_TAC[LT]];
      MP_TAC(SPECL [`P:A llist->bool`; `ll:A llist`]
                   eventually_LTL) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `t:A llist` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[THE] THEN
      MP_TAC(SPEC `\n. ?u. LDROP n (ll:A llist) = SOME u /\ P u`
                  MINIMAL_SUC) THEN
      REWRITE_TAC[] THEN ANTS_TAC THENL
       [CONJ_TAC THENL
         [UNDISCH_TAC `eventually (P:A llist->bool) ll` THEN
          REWRITE_TAC[eventually] THEN MESON_TAC[];
          REWRITE_TAC[LDROP_0; injectivity "option"] THEN
          ASM_MESON_TAC[]];
        ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
      ASM_MESON_TAC[LDROP_SUC]]) in
  new_specification ["Lnext"] th;;

let lnext_pos_def = cake_define
  `Lnext_pos (ll:num llist) = Lnext (\ll. ?k. LHD ll = SOME k /\ ~(k
  = 0)) ll`;;

(* insert a string (l1) at specified index (n) in a list (l2) *)
let insert_atI_def = cake_define
  `insert_atI l1 n l2 =
     TAKE n l2 ++ l1 ++ DROP (n + LENGTH l1) l2`;;

(* TODO - candidate for move to HOL *)
(* N.B.: there is a different is_subsequence defined in lcsTheory; these
   should be merged *)
let is_subseq_def = cake_define_list
  [`is_subseq ls [] <=> T`;
   `is_subseq [] (x :: xs) <=> F`;
   `is_subseq (y :: ys) (x :: xs) <=>
       (x = y /\ is_subseq ys xs) \/
       (is_subseq ys (x :: xs))`];;

(* TODO - candidate for move to HOL *)
(* HOL4 ML code, not ported:
val is_subseq_ind = theorem"is_subseq_ind";
*)

(* TODO - candidate for move to HOL *)

(* TODO - candidate for move to HOL *)

(* TODO - candidate for move to HOL *)

(* TODO - candidate for move to HOL *)

(* TODO - candidate for move to HOL *)

(* TODO - candidate for move to HOL *)

(* TODO - candidate for move to HOL *)

(* TODO - candidate for move to HOL *)

(* TODO - candidate for move to HOL *)

(* TODO - candidate for move to HOL *)

(* TODO - candidate for move to HOL *)

(* TODO - candidate for move to HOL *)

(* TODO - candidate for move to HOL *)

let make_even_def = cake_define
  `make_even n = (if EVEN n then n else n + 1)`;;

let steps_def = cake_define_list
  [`steps f x [] = []`;
   `steps f x (j :: js) =
       (let y = f x j in
       let tr = steps f y js in
         ((j,y) :: tr))`];;

let steps_rel_def = cake_define_list
  [`steps_rel R x [] <=> T`;
   `steps_rel R x ((j,y) :: tr) <=>
        R x j y /\
        steps_rel R y tr`];;

(* HOL4 ML code, not ported:
val steps_rel_ind = theorem"steps_rel_ind";
*)

let all_words_def = cake_define_list
  [`all_words base 0 = {}`;
   `all_words base (SUC n) = base INSERT (all_words (base + (n2w 1))
  n)`];;

let asm_write_bytearray_def = cake_define_list
  [`asm_write_bytearray a [] (m:'a word->word8) = m`;
   `asm_write_bytearray a (x :: xs) m = (a =+ x) (asm_write_bytearray
  (a + (n2w 1)) xs m)`];;

(* TODO: move to sptTheory *)

let eq_shape_def = cake_define
  `eq_shape x1 x2 =
      match (x1,x2) with
        (LN,LN) -> T
      | ((LS _4),(LS _5)) -> T
      | ((BN t1 t2),(BN u1 u2)) -> (eq_shape t1 u1 /\ eq_shape t2 u2)
      | ((BS t1 _6 t2),(BS u1 _7 u2)) -> (eq_shape t1 u1 /\ eq_shape
        t2 u2)
      | (_8,_9) -> F`;;

let copy_shape_def = cake_define_list
  [`copy_shape LN LN = LN`;
   `copy_shape LN (LS y:'a spt) = LN`;
   `copy_shape LN (BN t1 t2:'a spt) = BN (copy_shape LN t1)
  (copy_shape LN t2)`;
   `copy_shape LN (BS t1 y t2:'a spt) = LN`;
   `copy_shape (LS x:'a spt) LN = LS x`;
   `copy_shape (LS x:'a spt) (LS y:'a spt) = LS x`;
   `copy_shape (LS x:'a spt) (BN t1 t2:'a spt) = LS x`;
   `copy_shape (LS x:'a spt) (BS t1 y t2:'a spt) = BS (copy_shape LN
  t1) x (copy_shape LN t2)`;
   `copy_shape (BN u1 u2:'a spt) LN = (if domain (BN u1 u2) = {} then
  LN else BN u1 u2)`;
   `copy_shape (BN u1 u2:'a spt) (LS y:'a spt) = BN u1 u2`;
   `copy_shape (BN u1 u2:'a spt) (BN t1 t2:'a spt) = BN (copy_shape
  u1 t1) (copy_shape u2 t2)`;
   `copy_shape (BN u1 u2:'a spt) (BS t1 y t2:'a spt) = BN u1 u2`;
   `copy_shape (BS u1 x u2:'a spt) LN = BS u1 x u2`;
   `copy_shape (BS u1 x u2:'a spt) (LS y:'a spt) =
       (if domain (BN u1 u2) = {} then LS x else BS u1 x u2)`;
   `copy_shape (BS u1 x u2:'a spt) (BN t1 t2:'a spt) = BS u1 x u2`;
   `copy_shape (BS u1 x u2:'a spt) (BS t1 y t2:'a spt) = BS
  (copy_shape u1 t1) x (copy_shape u2 t2)`];;

(* / TODO *)

(* BEGIN TODO: move to sptreeTheory *)

(* The range is the set of values taken on by an sptree.
  Not sure if these are worth moving. *)
let range_def = cake_define
  `range s = {v | ?n. lookup n s = SOME v}`;;

(* END TODO *)

(* see #521 *)

let bytes_in_memory_def = cake_define_list
  [`bytes_in_memory a [] m dm <=> T`;
   `bytes_in_memory a ((x:word8) :: xs) m dm <=>
         (m a = x) /\ a IN dm /\ bytes_in_memory (a + (n2w 1)) xs
           m dm`];;

let bytes_in_mem_def = cake_define_list
  [`bytes_in_mem a [] m md k <=> T`;
   `bytes_in_mem a (b :: bs) m md k <=>
         a IN md /\ ~(a IN k) /\ (m a = b) /\
         bytes_in_mem (a + (n2w 1)) bs m md k`];;


let good_dimindex_def = cake_define
  `good_dimindex (:'a) <=> dimindex (:'a) = 32 \/ dimindex (:'a) = 64`;;

(* HOL4 ML code, not ported:
val LESS4 = DECIDE ``n < 4 <=> (n = 0) \/ (n = 1) \/ (n = 2) \/ (n =
  3:num)``
val LESS8 = DECIDE ``n < 8 <=> (n = 0) \/ (n = 1) \/ (n = 2) \/ (n =
  3:num) \/
                               (n = 4) \/ (n = 5) \/ (n = 6) \/ (n =
                                 7)``
*)

(* helpful theorems for _size *)

(* must be used instead of FUPDATE in defitions that go through
   translation *)
let fmap_update_def = cake_define
  `fmap_update f k v = f |+ (k,v)`;;

(* TODO: move to HOL? *)
let sum_cmp_def = cake_define
  `sum_cmp c1 c2 x1 x2 =
     (match x1 with INL n1 ->
         (match x2 with INL n2 -> c1 n1 n2 | INR _10 -> LESS) | INR
           n1 ->
         (match x2 with INL _11 -> GREATER | INR n2 -> c2 n1 n2))`;;

(* the shape num_cmp shares with mlint$int_cmp *)
