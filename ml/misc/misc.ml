(* ======================================================== *)
(*  misc: ported from HOL4's
    misc/miscScript.sml
    A definition theory, with 50 definitions, 1 datatype and 393
    theorems.  Needed by 94 files of the port.  *)
(* ======================================================== *)

(*
   Miscellaneous definitions and minor lemmas used throughout the
   development.
*)

(* Misc. lemmas (without any compiler constants) *)

needs "lib/ASCIInumbers.ml";;
needs "lib/alignment.ml";;
needs "lib/binary_ieee.ml";;
needs "lib/bitstring.ml";;
needs "lib/byte.ml";;
needs "lib/comparison.ml";;
needs "lib/indexedLists.ml";;
needs "lib/integer_word.ml";;
needs "lib/lprefix_lub.ml";;
needs "lib/machine_ieee.ml";;
needs "lib/numposrep.ml";;
needs "lib/set_sep.ml";;
needs "lib/sorting.ml";;
needs "lib/sptree.ml";;
needs "lib/ternaryComparisons.ml";;
needs "lib/toto.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "misc" [];;

let _ = do_list hide_constant ["C"; "num_cmp"];;
(* HOL4 ancestors outside the port: alist arithmetic blast bag combin
   container list pred_set finite_map rich_list llist option pair
   relation bit words string address path res_quan *)

(* Total version of THE *)
let the_def = define_cases
  [`the _1 (SOME x) = x`;
   `the x NONE = x`];;

let opt_bind_def = new_definition
  `opt_bind n v e =
     (match n with NONE -> e | SOME n' -> CONS (n',v) e)`;;

(* Note: This globally hides constants over the reals that gets imported through machine_ieeeTheory *)

(* this is copied in preamble.sml, but needed here to avoid cyclic dep *)
(* HOL4 miscScript.sml:42-46: ML code, not ported *)
(* -- *)

(* TODO: move/categorize *)

(* theorem behind impl_tac *)
(* IMP_IMP *)
let misc_IMP_IMP = prove
 (`(P /\ (Q ==> R)) ==> ((P ==> Q) ==> R)`,
  CHEAT_TAC);;

(* used elsewhere in cakeml *)
let SUBSET_IMP = prove
 (`s SUBSET t ==> (x IN s ==> x IN t)`,
  CHEAT_TAC);;

let DROP_NIL = prove
 (`!n xs. DROP n xs = [] <=> LENGTH xs <= n`,
  CHEAT_TAC);;

let revdroprev = prove
 (`!l n.
     n <= LENGTH l ==> (REVERSE (DROP n (REVERSE l)) = TAKE (LENGTH
       l - n) l)`,
  CHEAT_TAC);;

let revtakerev = prove
 (`!n l. n <= LENGTH l ==> REVERSE (TAKE n (REVERSE l)) = DROP (LENGTH
  l - n) l`,
  CHEAT_TAC);;

let times_add_o = prove
 (`(\(n:num). k * n + x) = ((+) x) o ((*) k)`,
  CHEAT_TAC);;

let SORTED_inv_image_LESS_PLUS = prove
 (`SORTED (inv_image (<) ((+) k)) = SORTED (<)`,
  CHEAT_TAC);;

let SORTED_GENLIST_TIMES = prove
 (`0 < k ==> (!n. SORTED (<) (list_of_seq ((*) k) n))`,
  CHEAT_TAC);;

(* this is
     read_bytearray a c gb = OPT_MMAP gb (GENLIST (λi. a + n2w i) c)
*)
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let read_bytearray_def,read_bytearray_ind = define_wf
  `MEASURE (\(x0,x1,x2). (\n. n) x1)`
  [`read_bytearray a 0 get_byte' = SOME []`;
   `read_bytearray a (SUC n) get_byte' =
         (match get_byte' a with NONE -> NONE | SOME b ->
             (match read_bytearray (a + (n2w 1)) n get_byte' with
             NONE -> NONE | SOME bs -> SOME (CONS b bs)))`];;

(* HOL to have OPT_MMAP f l1 = SOME l2 ==> (LENGTH l2 = LENGTH l1) *)
let read_bytearray_LENGTH = prove
 (`!n a f x.
      (read_bytearray a n f = SOME x) ==> (LENGTH x = n)`,
  CHEAT_TAC);;

let shift_seq_def = new_definition
  `misc_shift_seq k s = (\i. s (i + (k:num)))`;;

(* TODO: Used once in all of CakeML: could probably be pushed back to use-site*)
let SUM_SET_IN_LT = prove
 (`!s x y. FINITE s /\ x IN s /\ y < x ==> y < SUM_SET s`,
  CHEAT_TAC);;

(* only used in proof of tlookup_bij_iff *)
let CARD_IMAGE_ID_BIJ = prove
 (`!s. FINITE s ==> (!x. x IN s ==> f x IN s) /\ CARD (IMAGE f s) =
  CARD s ==> BIJ f s s`,
  CHEAT_TAC);;

(* never used *)
let CARD_IMAGE_EQ_BIJ = prove
 (`!s. FINITE s ==> CARD (IMAGE f s) = CARD s ==> BIJ f s (IMAGE f s)`,
  CHEAT_TAC);;

(* used only in clos_callProof -
   HOL has DISJOINT_IMAGE:
     |- (!x y. f x = f y <=> x = y) ==>
        (DISJOINT (IMAGE f x) (IMAGE f y) <=> DISJOINT x y
*)
let DISJOINT_IMAGE_SUC = prove
 (`DISJOINT (IMAGE SUC x) (IMAGE SUC y) <=> DISJOINT x y`,
  CHEAT_TAC);;

(* disgusting and used only in clos_callProof *)
let IMAGE_SUC_SUBSET_UNION = prove
 (`IMAGE SUC x SUBSET IMAGE SUC y UNION IMAGE SUC z <=>
    x SUBSET y UNION z`,
  CHEAT_TAC);;

(* HOL4 miscScript.sml:182: the overload LLOOKUP, which the port
   expands *)

(* HOL4 miscScript.sml:184-185: a theorem that HOL4 states as the
   value of an ML expression: LLOOKUP_def *)
(* HOL4 miscScript.sml:186-187: a theorem that HOL4 states as the
   value of an ML expression: LLOOKUP_EQ_EL *)
(* HOL4 miscScript.sml:188-189: a theorem that HOL4 states as the
   value of an ML expression: LLOOKUP_THM *)
(* HOL4 miscScript.sml:190-191: a theorem that HOL4 states as the
   value of an ML expression: LLOOKUP_DROP *)
(* HOL4 miscScript.sml:192-193: a theorem that HOL4 states as the
   value of an ML expression: LLOOKUP_TAKE_IMP *)
(* HOL4 miscScript.sml:194-195: a theorem that HOL4 states as the
   value of an ML expression: LLOOKUP_LUPDATE *)

(* app_list stuff should be in an app_list theory *)
let app_list_INDUCT,app_list_RECURSION = define_datatype
  "app_list =
     misc_List ('a list)
   | misc_Append app_list app_list
   | misc_Nil";;

let append_aux_def,append_aux_ind = define_rec
  [`append_aux misc_Nil aux = aux`;
   `append_aux (misc_List xs) aux = APPEND xs aux`;
   `append_aux (misc_Append l1 l2) aux = append_aux l1 (append_aux
    l2 aux)`];;

let append_def = new_definition
  `append l = append_aux l []`;;

let append_aux_thm = prove
 (`!l xs. append_aux l xs = APPEND (append_aux l []) xs`,
  CHEAT_TAC);;

let append_thm = prove
 (`append (misc_Append l1 l2) = APPEND (append l1) (append l2) /\
    append (misc_List xs) = xs /\
    append misc_Nil = []`,
  CHEAT_TAC);;
add_simp append_thm;;

let SmartAppend_def = new_definition
  `SmartAppend l1 l2 =
        match (l1,l2) with
          (misc_Nil,l2) -> l2
        | (l1,misc_Nil) -> l1
        | (l1,l2) -> misc_Append l1 l2`;;
add_simp SmartAppend_def;;

let SmartAppend_thm = prove
 (`!l1 l2.
    SmartAppend l1 l2 =
      (if l1 = misc_Nil then l2 else
      if l2 = misc_Nil then l1 else misc_Append l1 l2)`,
  CHEAT_TAC);;

let SmartAppend_Nil = prove
 (`SmartAppend l misc_Nil = l /\
   SmartAppend misc_Nil l = l`,
  CHEAT_TAC);;

let append_SmartAppend = prove
 (`append (SmartAppend l1 l2) = APPEND (append l1) (append l2)`,
  CHEAT_TAC);;
add_simp append_SmartAppend;;

(* instant derivation from LIST_EQ_REWRITE *)
let GENLIST_eq_MAP = prove
 (`list_of_seq f n = MAP g ls <=>
   LENGTH ls = n /\ (!m. m < n ==> f m = g (EL m ls))`,
  CHEAT_TAC);;

(* TODO - already in HOL as ZIP_GENLIST *)
let ZIP_GENLIST1 = prove
 (`!l f n. LENGTH l = n ==> ZIP (list_of_seq f n) l = list_of_seq (\x.
  (f x,EL x l)) n`,
  CHEAT_TAC);;

(* used once *)
let MAP_REVERSE_STEP = prove
 (`!x f. ~(x = []) ==> MAP f (REVERSE x) = CONS (f (LAST x)) (MAP f
  (REVERSE (BUTLAST x)))`,
  CHEAT_TAC);;

(* used three times, once with MIN_DEF alongside, which turns it into
   LENGTH_TAKE_EQ
*)
let LENGTH_TAKE_EQ_MIN = prove
 (`!n xs. LENGTH (TAKE n xs) = MIN n (LENGTH xs)`,
  CHEAT_TAC);;

(* should be switched in orientation; looks like an attempt to get congruence
   rule *)
let LIST_REL_MEM = prove
 (`!xs ys P. ALL2 P xs ys <=>
              ALL2 (\x y. MEM x xs /\ MEM y ys ==> P x y) xs ys`,
  CHEAT_TAC);;

(* only used in theorem immediately below *)
let LIST_REL_GENLIST_I = prove
 (`!xs. ALL2 P (list_of_seq I (LENGTH xs)) xs =
         (!n. n < LENGTH xs ==> P n (EL n xs))`,
  CHEAT_TAC);;

(* only used in bvi_to_dataProof *)
let LIST_REL_lookup_fromList = prove
 (`ALL2 (\v x. sptree_lookup v (sptree_fromList args) = SOME x)
     (list_of_seq I (LENGTH args)) args`,
  CHEAT_TAC);;

let LIST_REL_lookup_fromList_MAP = prove
 (`ALL2 (\v x. ?z. sptree_lookup v (sptree_fromList args) = SOME z /\ x
  = f z)
    (list_of_seq I (LENGTH args)) (MAP f args)`,
  CHEAT_TAC);;

(* only used in examples/stackProg; oriented badly *)
let LIST_REL_FRONT_LAST = prove
 (`~(l1 = []) /\ ~(l2 = []) ==>
       (ALL2 A l1 l2 <=>
        ALL2 A (BUTLAST l1) (BUTLAST l2) /\ A (LAST l1) (LAST l2))`,
  CHEAT_TAC);;

(* [local] *)
let lemmas = prove
 (`((2 + 2 * n) - 1 = 2 * n + (1:num)) /\
     (2 + 2 * n' = 2 * n'' + 2 <=> n' = (n'':num)) /\
     (2 * m = 2 * n <=> (m = n)) /\
     ((2 * n'' + 1) DIV 2 = n'') /\
     ((2 * n) DIV 2 = n) /\
     (~(2 + 2 * n' = 2 * n'' + 1)) /\
     (~(2 * m + 1 = 2 * n' + 2))`,
  CHEAT_TAC);;

let lookup_any_def = new_definition
  `lookup_any x sp d =
     (match sptree_lookup x sp with NONE -> d | SOME m -> m)`;;

let fromList2_def = new_definition
  `fromList2 l = SND (FOLDL (\(i,t) a. (i + 2,sptree_insert i a t))
  (0,LN) l)`;;

(* [local] *)
let EVEN_fromList2_lemma = prove
 (`!l n t.
       EVEN n /\ (!x. x IN domain t ==> EVEN x) ==>
       (!x. x IN domain (SND (FOLDL (\(i,t) a. (i + 2,sptree_insert
         i a t)) (n,t) l)) ==> EVEN x)`,
  CHEAT_TAC);;

let EVEN_fromList2 = prove
 (`!l n. n IN domain (fromList2 l) ==> EVEN n`,
  CHEAT_TAC);;

let SUBMAP_mono_FUPDATE_LIST = prove
 (`!ls f g.
   DRESTRICT f (COMPL (set_of_list (MAP FST ls))) SUBMAP
   DRESTRICT g (COMPL (set_of_list (MAP FST ls))) ==> f |++ ls
     SUBMAP g |++ ls`,
  CHEAT_TAC);;

let INJ_FAPPLY_FUPDATE = prove
 (`INJ (FAPPLY f) (FDOM f) (FRANGE f) /\
   s = k INSERT FDOM f /\ ~(v IN FRANGE f) /\
   t = v INSERT FRANGE f ==>
   INJ (FAPPLY (f |+ (k,v))) s t`,
  CHEAT_TAC);;

(* used in only one place: stack_to_labProof *)
let BIJ_FLOOKUP_MAP_KEYS = prove
 (`BIJ bij UNIV UNIV ==>
    FLOOKUP (MAP_KEYS (LINV bij UNIV) f) n = FLOOKUP f (bij n)`,
  CHEAT_TAC);;

let SPLIT_LIST = prove
 (`!xs.
      ?ys zs. (xs = APPEND ys zs) /\
              (LENGTH xs DIV 2 = LENGTH ys)`,
  CHEAT_TAC);;

let EXISTS_ZIP = prove
 (`!l f. EX (\(x,y). f x) l = EX f (MAP FST l)`,
  CHEAT_TAC);;

let EVERY_ZIP = prove
 (`!l f. ALL (\(x,y). f x) l = ALL f (MAP FST l)`,
  CHEAT_TAC);;

let every_zip_split = prove
 (`!l1 l2 P Q.
    LENGTH l1 = LENGTH l2 ==>
    (ALL (\(x,y). P x /\ Q y) (ZIP l1 l2) <=> ALL P l1 /\ ALL Q l2)`,
  CHEAT_TAC);;

let every_shim = prove
 (`!l P. ALL (\(x,y). P y) l = ALL P (MAP SND l)`,
  CHEAT_TAC);;

let every_shim2 = prove
 (`!l P Q. ALL (\(x,y). P x /\ Q y) l = (ALL (\x. P (FST x)) l /\ ALL
  (\x. Q (SND x)) l)`,
  CHEAT_TAC);;

let MEM_ZIP2 = prove
 (`!l1 l2 x.
   MEM x (ZIP l1 l2) ==>
   (?n. n < LENGTH l1 /\ n < LENGTH l2 /\ x = (EL n l1,EL n l2))`,
  CHEAT_TAC);;

let ZIP_MAP_FST_SND_EQ = prove
 (`!ls. ZIP (MAP FST ls) (MAP SND ls) = ls`,
  CHEAT_TAC);;

let MAP_FST_I_PAIR_MAP = prove
 (`!xs. MAP FST (MAP (I ## f) xs) = MAP FST xs`,
  CHEAT_TAC);;
add_simp MAP_FST_I_PAIR_MAP;;

let EVERY_FST_SND = prove
 (`ALL (\(a,b). P a /\ Q b) ls <=> ALL P (MAP FST ls) /\ ALL Q (MAP
  SND ls)`,
  CHEAT_TAC);;

let zlookup_def = new_definition
  `zlookup m k = (match sptree_lookup k m with NONE -> 0 | SOME k ->
  k)`;;

let tlookup_def = new_definition
  `tlookup m k = (match sptree_lookup k m with NONE -> k | SOME k ->
  k)`;;

let tlookup_id = prove
 (`~(x IN domain names) ==> tlookup names x = x`,
  CHEAT_TAC);;

let tlookup_bij_suff = prove
 (`set_of_list (sptree_toList names) = domain names ==>
   BIJ (tlookup names) UNIV UNIV`,
  CHEAT_TAC);;

let tlookup_bij_iff = prove
 (`BIJ (tlookup names) UNIV UNIV <=>
   set_of_list (sptree_toList names) = domain names`,
  CHEAT_TAC);;

(* should be composition of oEL and as-yet-undefined "THE default" *)
let any_el_def,any_el_ind = define_rec
  [`any_el n [] d = d`;
   `any_el n (CONS x xs) d = (if n = 0 then x else any_el (n -
    (1:num)) xs d)`];;

let update_resize_def = new_definition
  `update_resize ls default v n =
     (if n < LENGTH ls then
       LUPDATE v n ls else
       LUPDATE v n (APPEND ls (REPLICATE ((n * 2 + 1) - LENGTH ls)
         default)))`;;

(*TODO upstream*)
let MAX_LIST_APPEND = prove
 (`MAX_LIST (APPEND xs ys) = MAX (MAX_LIST xs) (MAX_LIST ys)`,
  CHEAT_TAC);;
add_simp MAX_LIST_APPEND;;

(*Or should it be MAX x (MAX_LIST xs)*)
let MAX_LIST_SNOC = prove
 (`MAX_LIST (SNOC x xs) = MAX (MAX_LIST xs) x`,
  CHEAT_TAC);;
add_simp MAX_LIST_SNOC;;

let MAX_LIST_intro = prove
 (`!ls.
   P 0 /\ ALL P ls ==> P (MAX_LIST ls)`,
  CHEAT_TAC);;

let MAX_LIST_max = prove
 (`!ls. ALL (\x. x <= MAX_LIST ls) ls`,
  CHEAT_TAC);;

let FOLDR_MAX_0_MAX_LIST = prove
 (`!ls. ITLIST MAX ls 0 = MAX_LIST ls`,
  CHEAT_TAC);;

(* never used *)
let list_inter_def = new_definition
  `list_inter xs ys = FILTER (\y. MEM y xs) ys`;;

let max3_def = new_definition
  `max3 (x:num) y z = (if x > y then (if z > x then z else x) else
  (if z > y then z else y))`;;
add_simp max3_def;;

let ALOOKUP_SNOC = prove
 (`!ls p k. ALOOKUP (SNOC p ls) k =
      (match ALOOKUP ls k with SOME v -> SOME v |
        NONE -> (if k = FST p then SOME (SND p) else NONE))`,
  CHEAT_TAC);;

let ALOOKUP_GENLIST = prove
 (`!f n k. ALOOKUP (list_of_seq (\i. (i,f i)) n) k = (if k < n then
  SOME (f k) else NONE)`,
  CHEAT_TAC);;

let ALOOKUP_ZIP_FAIL = prove
 (`!A B x.
   LENGTH A = LENGTH B ==>
   (ALOOKUP (ZIP A B) x = NONE <=> ~(MEM x A))`,
  CHEAT_TAC);;

let MEM_ALOOKUP = prove
 (`!xs x v.
      ALL_DISTINCT (MAP FST xs) ==>
      (MEM (x,v) xs <=> ALOOKUP xs x = SOME v)`,
  CHEAT_TAC);;

(* TODO - candidate for move to HOL, but in simpler form without accumulator *)
(* only used in inferProg *)
let anub_def,anub_ind = define_rec
  [`anub [] acc = []`;
   `anub (CONS (k,v) ls) acc =
       (if MEM k acc then anub ls acc else CONS (k,v) (anub ls
           (CONS k acc)))`];;

(* HOL4 miscScript.sml:691: ML code, not ported *)

let EVERY_anub_imp = prove
 (`!ls acc x y.
      ALL P (anub (CONS (x,y) ls) acc) /\ ~(x IN set_of_list acc) ==>
      P (x,y) /\ ALL P (anub ls (CONS x acc))`,
  CHEAT_TAC);;

(* terrible rewrite *)
let ALOOKUP_anub = prove
 (`ALOOKUP (anub ls acc) k =
    (if MEM k acc then ALOOKUP (anub ls acc) k else ALOOKUP ls k)`,
  CHEAT_TAC);;

let anub_eq_nil = prove
 (`anub x y = [] <=> ALL (hol4_C MEM y) (MAP FST x)`,
  CHEAT_TAC);;

let EVERY_anub_suff = prove
 (`!ls acc.
    (!x. ~(MEM x acc) ==> (match ALOOKUP ls x with SOME v -> P
      (x,v) | NONE -> T)) ==> ALL P (anub ls acc)`,
  CHEAT_TAC);;

let anub_notin_acc = prove
 (`!ls acc. MEM x acc ==> ~(MEM x (MAP FST (anub ls acc)))`,
  CHEAT_TAC);;

let anub_tl_anub = prove
 (`!x y h t. anub x y = CONS h t ==> (?a b. t = anub a b /\
  set_of_list a SUBSET set_of_list x /\ set_of_list b SUBSET
  set_of_list (CONS (FST h) y))`,
  CHEAT_TAC);;

let anub_all_distinct_keys = prove
 (`!ls acc.
    ALL_DISTINCT acc ==>
    ALL_DISTINCT (APPEND (MAP FST (anub ls acc)) acc)`,
  CHEAT_TAC);;

let MEM_anub_ALOOKUP = prove
 (`MEM (k,v) (anub ls []) ==>
    ALOOKUP ls k = SOME v`,
  CHEAT_TAC);;

new_type_abbrev("misc_num_set",`:1 spt`);;
(* HOL4 miscScript.sml:788: the type abbreviation num_map, which the
   port expands *)

let toAList_domain = prove
 (`!x. MEM x (MAP FST (toAList t)) <=> x IN domain t`,
  CHEAT_TAC);;

let domain_nat_set_from_list = prove
 (`!ls ns. domain (FOLDL (\s n. sptree_insert n one s) ns ls) = domain
  ns UNION set_of_list ls`,
  CHEAT_TAC);;
add_simp domain_nat_set_from_list;;

let wf_nat_set_from_list = prove
 (`!ls ns. sptree_wf ns ==> sptree_wf (FOLDL (\s n. sptree_insert n z
  s) ns ls)`,
  CHEAT_TAC);;

let BIT_11 = prove
 (`!n m. (BIT n = BIT m) <=> (n = m)`,
  CHEAT_TAC);;

let BIT_11_2 = prove
 (`!n m. (!z. (z < 2 EXP (MAX n m)) ==> (BIT n z <=> BIT m z)) <=> (n
  = m)`,
  CHEAT_TAC);;

(* only used below in proof of theorem that is in turn used just twice *)
let LOG2_TIMES2 = prove
 (`0 < n ==> (LOG2 (2 * n) = SUC (LOG2 n))`,
  CHEAT_TAC);;

(* only used below in proof of theorem that is in turn used just twice *)
let LOG2_TIMES2_1 = prove
 (`!n. 0 < n ==> (LOG2 (2 * n + 1) = LOG2 (2 * n))`,
  CHEAT_TAC);;

(* used only twice, both times in candle/set-theory *)
let C_BIT_11 = prove
 (`!n m. (!z. (z <= LOG2 (MAX n m)) ==> (BIT z n <=> BIT z m)) <=> (n
  = m)`,
  CHEAT_TAC);;

let BIT_num_from_bin_list_leading = prove
 (`!l x. ALL ((>) 2) l /\ LENGTH l <= x ==> ~(BIT x (num_from_bin_list
  l))`,
  CHEAT_TAC);;

let least_from_def = new_definition
  `least_from P n = (if (?x. P x /\ n <= x) then minimal x. P x /\ n
  <= x else (minimal) P)`;;

let LEAST_thm = prove
 (`(minimal) P = least_from P 0`,
  CHEAT_TAC);;

let least_from_thm = prove
 (`least_from P n = (if P n then n else least_from P (n + 1))`,
  CHEAT_TAC);;

let FUNPOW_mono = prove
 (`(!x y. R1 x y ==> R2 x y) /\
    (!R1 R2. (!x y. R1 x y ==> R2 x y) ==> (!x y. f R1 x y ==> f R2 x
      y)) ==>
    (!n x y. ITER n f R1 x y ==> ITER n f R2 x y)`,
  CHEAT_TAC);;

let FUNPOW_SUC_PLUS = prove
 (`!n a. ITER n SUC = (+) n`,
  CHEAT_TAC);;

(* used just once; better as
     transitive R ==> transitive (OPTREL R)
   or that with transitive expanded out *)
let OPTREL_trans = prove
 (`!R x y z.
    (!a b c. (x = SOME a) /\ (y = SOME b) /\ (z = SOME c) /\ R a b
      /\ R b c ==> R a c) /\ OPTREL R x y /\ OPTREL R y z ==> OPTREL R
      x z`,
  CHEAT_TAC);;

let UPDATE_LIST_def = new_definition
  `UPDATE_LIST = FOLDL (hol4_C (UNCURRY UPDATE))`;;

(* HOL4 miscScript.sml:1038: the overload =++, which the port writes
   as an application of UPDATE_LIST *)

let UPDATE_LIST_THM = prove
 (`!f. (UPDATE_LIST f [] = f) /\ (!h t. (UPDATE_LIST f (CONS h t) =
  UPDATE_LIST ((FST h =+ SND h) f) t))`,
  CHEAT_TAC);;

let APPLY_UPDATE_LIST_ALOOKUP = prove
 (`!ls f x. (UPDATE_LIST f ls) x = (match ALOOKUP (REVERSE ls) x with
  NONE -> f x | SOME y -> y)`,
  CHEAT_TAC);;

(* should be using indexedLists$findi, or INDEX_OF *)
let find_index_def,find_index_ind = define_rec
  [`find_index _2 [] _3 = NONE`;
   `find_index y (CONS x xs) n = (if x = y then SOME n else
    find_index y xs (n + 1))`];;

let INDEX_FIND_CONS_EQ_SOME = prove
 (`(INDEX_FIND n f (CONS x xs) = SOME y) <=>
    (f x /\ (y = (n,x))) \/
    (~(f x) /\ (INDEX_FIND (n + 1) f xs = SOME y))`,
  CHEAT_TAC);;

let find_index_INDEX_FIND = prove
 (`!y xs n. find_index y xs n = OPTION_MAP FST (INDEX_FIND n ((=) y)
  xs)`,
  CHEAT_TAC);;

let find_index_INDEX_OF = prove
 (`find_index y xs 0 = INDEX_OF y xs`,
  CHEAT_TAC);;

let find_index_NOT_MEM = prove
 (`!ls x n. ~(MEM x ls) = (find_index x ls n = NONE)`,
  CHEAT_TAC);;

let find_index_MEM = prove
 (`!ls x n. MEM x ls ==> (?i. (find_index x ls n = SOME (n + i)) /\ i
  < LENGTH ls /\ (EL i ls = x))`,
  CHEAT_TAC);;

let find_index_LEAST_EL = prove
 (`!ls x n. find_index x ls n = (if MEM x ls then SOME (n + (minimal
  n. x = EL n ls)) else NONE)`,
  CHEAT_TAC);;

let find_index_LESS_LENGTH = prove
 (`!ls n m i. (find_index n ls m = SOME i) ==> (m <= i) /\ (i < m +
  LENGTH ls)`,
  CHEAT_TAC);;

let ALOOKUP_find_index_NONE = prove
 (`(ALOOKUP env k = NONE) ==> (find_index k (MAP FST env) m = NONE)`,
  CHEAT_TAC);;

(* HOL4 miscScript.sml:1138-1146: a theorem that HOL4 states as the
   value of an ML expression: ALOOKUP_find_index_SOME *)

let ALOOKUP_find_index_SOME = prove
 (`(ALOOKUP env k = SOME v) ==>
    (?i. (find_index k (MAP FST env) 0 = SOME i) /\
        i < LENGTH env /\ (v = SND (EL i env)))`,
  CHEAT_TAC);;

let find_index_ALL_DISTINCT_EL = prove
 (`!ls n m. ALL_DISTINCT ls /\ n < LENGTH ls ==> (find_index (EL n ls)
  ls m = SOME (m + n))`,
  CHEAT_TAC);;
add_simp find_index_ALL_DISTINCT_EL;;

let find_index_ALL_DISTINCT_EL_eq = prove
 (`!ls. ALL_DISTINCT ls ==> (!x m i. (find_index x ls m = SOME i) =
      (?j. (i = m + j) /\ j < LENGTH ls /\ (x = EL j ls)))`,
  CHEAT_TAC);;

let find_index_APPEND_same = prove
 (`!l1 n m i l2. (find_index n l1 m = SOME i) ==> (find_index n
  (APPEND l1 l2) m = SOME i)`,
  CHEAT_TAC);;

let find_index_ALL_DISTINCT_REVERSE = prove
 (`!ls x m j. ALL_DISTINCT ls /\ (find_index x ls m = SOME j) ==>
  (find_index x (REVERSE ls) m = SOME ((m + LENGTH ls + m) - j - 1))`,
  CHEAT_TAC);;

let THE_find_index_suff = prove
 (`!P x ls n. (!m. m < LENGTH ls ==> P (m + n)) /\ MEM x ls ==>
    P (THE (find_index x ls n))`,
  CHEAT_TAC);;

let find_index_APPEND1 = prove
 (`!l1 n l2 m i. (find_index n (APPEND l1 l2) m = SOME i) /\ (i < m +
  LENGTH l1) ==> (find_index n l1 m = SOME i)`,
  CHEAT_TAC);;

let find_index_APPEND2 = prove
 (`!l1 n l2 m i. (find_index n (APPEND l1 l2) m = SOME i) /\ (m +
  LENGTH l1 <= i) ==> (find_index n l2 (m + LENGTH l1) = SOME i)`,
  CHEAT_TAC);;

let find_index_is_MEM = prove
 (`!x ls n j. (find_index x ls n = SOME j) ==> MEM x ls`,
  CHEAT_TAC);;

let find_index_MAP_inj = prove
 (`!ls x n f. (!y. MEM y ls ==> (f x = f y) ==> x = y) ==> (find_index
  (f x) (MAP f ls) n = find_index x ls n)`,
  CHEAT_TAC);;

let find_index_shift_0 = prove
 (`!ls x k. find_index x ls k = OPTION_MAP (\x. x + k) (find_index x
  ls 0)`,
  CHEAT_TAC);;

let find_index_shift = prove
 (`!ls x k j. (find_index x ls k = SOME j) ==> j >= k /\ (!n.
  find_index x ls n = SOME (j - k + n))`,
  CHEAT_TAC);;

let find_index_APPEND = prove
 (`!l1 l2 x n. find_index x (APPEND l1 l2) n =
    (match find_index x l1 n with NONE -> find_index x l2 (n +
      LENGTH l1) | SOME x -> SOME x)`,
  CHEAT_TAC);;

let find_index_in_FILTER_ZIP_EQ = prove
 (`!P l1 l2 x n1 n2 v1 j1 j2.
      (LENGTH l1 = LENGTH v1) /\
      (FILTER (P o FST) (ZIP l1 v1) = l2) /\
      (find_index x l1 n1 = SOME (n1 + j1)) /\
      (find_index x (MAP FST l2) n2 = SOME (n2 + j2)) /\
      P x ==>
      j1 < LENGTH l1 /\ j2 < LENGTH l2 /\
      (EL j1 (ZIP l1 v1) = EL j2 l2)`,
  CHEAT_TAC);;

let ALL_DISTINCT_PERM_ALOOKUP_ZIP = prove
 (`!l1 l2 l3.
    ALL_DISTINCT (MAP FST l1) /\ PERM (MAP FST l1) l2 ==>
      (set_of_list l1 = set_of_list (ZIP l2 (MAP (THE o ALOOKUP
      (APPEND l1 l3)) l2)))`,
  CHEAT_TAC);;

(* surely better with UNZIP rather than ZIP: i.e., UNZIP l1 = (a,b)...  *)
let PERM_ZIP = prove
 (`!l1 l2. PERM l1 l2 ==> (!a b c d. (l1 = ZIP a b) /\ (l2 = ZIP c d) /\
  (LENGTH a = LENGTH b) /\ (LENGTH c = LENGTH d) ==>
    PERM a c /\ PERM b d)`,
  CHEAT_TAC);;

(* never used *)
let RTC_invariant = prove
 (`!R P. (!x y. P x /\ R x y ==> P y) ==> (!x y. RTC R x y ==> P x ==>
  RTC (RINTER R (\x y. P x /\ P y)) x y)`,
  CHEAT_TAC);;

(* never used *)
let RTC_RSUBSET = prove
 (`!R1 R2. RSUBSET R1 R2 ==> RSUBSET (RTC R1) (RTC R2)`,
  CHEAT_TAC);;

let PERM_PART = prove
 (`!P L l1 l2 p q. ((p,q) = PART P L l1 l2) ==> PERM (APPEND L (APPEND
  l1 l2)) (APPEND p q)`,
  CHEAT_TAC);;

let PERM_PARTITION = prove
 (`!P L A B. ((A,B) = PARTITION P L) ==> PERM L (APPEND A B)`,
  CHEAT_TAC);;

let option_case_NONE_F = prove
 (`(match X with NONE -> F | SOME x -> P x) = (?x. (X = SOME x) /\ P
  x)`,
  CHEAT_TAC);;

let IS_PREFIX_THM = prove
 (`!l2 l1. IS_PREFIX l1 l2 <=> (LENGTH l2 <= LENGTH l1) /\ (!n. n <
  LENGTH l2 ==> (EL n l2 = EL n l1))`,
  CHEAT_TAC);;

let EVERY2_RC_same = prove
 (`ALL2 (RC R) l l`,
  CHEAT_TAC);;
add_simp EVERY2_RC_same;;

(* used twice, and only in source_to_flatProof *)
let FOLDL_invariant = prove
 (`!P f ls a. (P a) /\ (!x y. MEM y ls /\ P x ==> P (f x y)) ==> P
  (FOLDL f a ls)`,
  CHEAT_TAC);;

(* never used *)
let FOLDL_invariant_rest = prove
 (`!P f ls a. P ls a /\ (!x n. n < LENGTH ls /\ P (DROP n ls) x ==> P
  (DROP (SUC n) ls) (f x (EL n ls))) ==> P [] (FOLDL f a ls)`,
  CHEAT_TAC);;

let between_def = new_definition
  `between x y z <=> (x:num) <= z /\ z < y`;;

let IN_between = prove
 (`x IN between y z <=> y <= x /\ x < z`,
  CHEAT_TAC);;

(* never used *)
let SUC_LEAST = prove
 (`!x. P x ==> (SUC ((minimal) P) = (minimal x. 0 < x /\ P (PRE x)))`,
  CHEAT_TAC);;

(* never used *)
let fmap_linv_def = new_definition
  `fmap_linv f1 f2 <=> (FDOM f2 = FRANGE f1) /\ (!x. x IN FDOM f1 ==>
  (FLOOKUP f2 (FAPPLY f1 x) = SOME x))`;;

(* never used *)
let fmap_linv_unique = prove
 (`!f f1 f2. fmap_linv f f1 /\ fmap_linv f f2 ==> (f1 = f2)`,
  CHEAT_TAC);;

(* never used *)
let INJ_has_fmap_linv = prove
 (`INJ (FAPPLY f) (FDOM f) (FRANGE f) ==> (?g. fmap_linv f g)`,
  CHEAT_TAC);;

(* never used *)
let has_fmap_linv_inj = prove
 (`(?g. fmap_linv f g) = (INJ (FAPPLY f) (FDOM f) (FRANGE f))`,
  CHEAT_TAC);;

(* never used *)
let fmap_linv_FAPPLY = prove
 (`fmap_linv f g /\ x IN FDOM f ==> (FAPPLY g (FAPPLY f x) = x)`,
  CHEAT_TAC);;

(* TODO - candidate for move to HOL *)
let plus_compose = prove
 (`!(n:num) m. (+) n o (+) m = (+) (n + m)`,
  CHEAT_TAC);;

(* TODO: move elsewhere? export as rewrite? *)
(* never used *)
let IN_option_rwt = prove
 (`(x IN (match opt with NONE -> {} | SOME y -> Q y)) <=>
    (?y. (opt = SOME y) /\ x IN Q y)`,
  CHEAT_TAC);;

(* never used *)
let IN_option_rwt2 = prove
 (`x IN option_CASE opt {} s <=> (?y. (opt = SOME y) /\ x IN s y)`,
  CHEAT_TAC);;

(* Re-expressing folds *)

(* only used in flat_elimProof *)
let FOLDR_CONS_triple = prove
 (`!f ls a. ITLIST (\(x,y,z) w. CONS (f x y z) w) ls a = APPEND (MAP
  (\(x,y,z). f x y z) ls) a`,
  CHEAT_TAC);;

(* never used *)
let FOLDR_CONS_5tup = prove
 (`!f ls a. ITLIST (\(c,d,x,y,z) w. CONS (f c d x y z) w) ls a =
  APPEND (MAP (\(c,d,x,y,z). f c d x y z) ls) a`,
  CHEAT_TAC);;

(* never used *)
let FOLDR_transitive_property = prove
 (`!P ls f a. P [] a /\ (!n a. n < LENGTH ls /\ P (DROP (SUC n) ls) a
  ==> P (DROP n ls) (f (EL n ls) a)) ==> P ls (ITLIST f ls a)`,
  CHEAT_TAC);;

(* Re-expressing curried lambdas *)

let FST_triple = prove
 (`(\(n,ns,b). n) = FST`,
  CHEAT_TAC);;

(* never used *)
let FST_5tup = prove
 (`(\(n,ns,b,x,y). n) = FST`,
  CHEAT_TAC);;

(* never used *)
let SND_triple = prove
 (`(\(n,ns,b). f ns b) = UNCURRY f o SND`,
  CHEAT_TAC);;

let FST_pair = prove
 (`(\(n,v). n) = FST`,
  CHEAT_TAC);;

(* never used *)
let SND_pair = prove
 (`(\(n,v). v) = SND`,
  CHEAT_TAC);;

(* never used *)
let SND_FST_pair = prove
 (`(\((n,m),c). m) = SND o FST`,
  CHEAT_TAC);;

(* never used *)
let MAP_ZIP_SND_triple = prove
 (`(LENGTH l1 = LENGTH l2) ==> (MAP (\(x,y,z). f y z) (ZIP l1 l2) =
  MAP (UNCURRY f) l2)`,
  CHEAT_TAC);;

(* Specialisations to identity function *)

let I_PERMUTES = prove
 (`I PERMUTES s`,
  CHEAT_TAC);;
add_simp I_PERMUTES;;

(* never used *)
let INJ_I = prove
 (`!s t. INJ I s t <=> s SUBSET t`,
  CHEAT_TAC);;


let MAP_EQ_ID = prove
 (`!f ls. (MAP f ls = ls) = (!x. MEM x ls ==> (f x = x))`,
  CHEAT_TAC);;

(* Specialisations to FEMPTY *)

let FUN_FMAP_FAPPLY_FEMPTY_FAPPLY = prove
 (`FINITE s ==> (FAPPLY (FUN_FMAP (FAPPLY FEMPTY) s) x = FAPPLY FEMPTY
  x)`,
  CHEAT_TAC);;
add_simp FUN_FMAP_FAPPLY_FEMPTY_FAPPLY;;

(* FUPDATE_LIST stuff *)

let NOT_MEM_FLOOKUP_ZIP = prove
 (`!ys xs zs. ~(MEM n ys) ==> FLOOKUP (xs |++ ZIP ys zs) n = FLOOKUP
  xs n`,
  CHEAT_TAC);;

(* Misc. *)

let LESS_1 = prove
 (`x < 1 <=> (x = (0:num))`,
  CHEAT_TAC);;
add_simp LESS_1;;


  (* --------- SO additions --------- *)

let map_fst = prove
 (`!l f. MAP FST (MAP (\(x,y). (x,f y)) l) = MAP FST l`,
  CHEAT_TAC);;

(* use INJ_MAP_EQ_IFF and INJ_DEF *)
let map_some_eq = prove
 (`!l1 l2. (MAP SOME l1 = MAP SOME l2) <=> (l1 = l2)`,
  CHEAT_TAC);;

(* never used *)
let map_some_eq_append = prove
 (`!l1 l2 l3. (APPEND (MAP SOME l1) (MAP SOME l2) = MAP SOME l3) <=>
  (APPEND l1 l2 = l3)`,
  CHEAT_TAC);;

(* HOL4 miscScript.sml:1766: ML code, not ported *)


(* list misc *)

let LASTN_LEMMA = prove
 (`(LASTN (LENGTH xs + 1 + 1) (CONS x (CONS y xs)) = CONS x (CONS y xs))
  /\
    (LASTN (LENGTH xs + 1) (CONS x xs) = CONS x xs)`,
  CHEAT_TAC);;

(* HOL4 miscScript.sml:1779-1782: a theorem that HOL4 states as the
   value of an ML expression: LASTN_TL *)

let LASTN_LENGTH_LESS_EQ = prove
 (`!xs n. LENGTH xs <= n ==> LASTN n xs = xs`,
  CHEAT_TAC);;

let LASTN_ALT = prove
 (`(LASTN n [] = []) /\
    (LASTN n (CONS x xs) = (if LENGTH (CONS x xs) <= n then CONS x
      xs else LASTN n xs))`,
  CHEAT_TAC);;

let LENGTH_LASTN_LESS = prove
 (`!xs n. LENGTH (LASTN n xs) <= LENGTH xs`,
  CHEAT_TAC);;

let MAP_EQ_MAP_IMP = prove
 (`!xs ys f.
      (!x y. MEM x xs /\ MEM y ys /\ (f x = f y) ==> (x = y)) ==>
      (MAP f xs = MAP f ys) ==> (xs = ys)`,
  CHEAT_TAC);;
(*
NB: this is weaker:
Theorem MAP_EQ_MAP_IMP =
  INJ_MAP_EQ |> SIMP_RULE (srw_ss()) [INJ_DEF]
*)

let INJ_MAP_EQ_2 = prove
 (`!f l1 l2.
   (!x y. x IN set_of_list l1 /\ y IN set_of_list l2 /\ f x = f y ==>
     x = y) /\
   MAP f l1 = MAP f l2 ==>
   l1 = l2`,
  CHEAT_TAC);;

let LENGTH_EQ_FILTER_FILTER = prove
 (`!xs. ALL (\x. (P x \/ Q x) /\ ~(P x /\ Q x)) xs ==>
         (LENGTH xs = LENGTH (FILTER P xs) + LENGTH (FILTER Q xs))`,
  CHEAT_TAC);;

let LIST_REL_MAP_FILTER_NEQ = prove
 (`!P f1 f2 z1 z2 l1 l2.
      ALL2 P (MAP f1 l1) (MAP f2 l2) /\
      (!y1 y2. MEM (y1,y2) (ZIP l1 l2) ==> (~(SND y1 = z1) <=> ~(SND
        y2 = z2)) /\ (P (f1 y1) (f2 y2))) ==>
      ALL2 P (MAP f1 (FILTER (\(x,y). ~(y = z1)) l1)) (MAP f2
        (FILTER (\(x,y). ~(y = z2)) l2))`,
  CHEAT_TAC);;

(* move into HOL? *)

let word_list_def,word_list_ind = define_guess
  [`misc_word_list a [] = emp`;
   `misc_word_list a (CONS x xs) = set_sep_one (a,x) *
    misc_word_list (a + bytes_in_word) xs`];;

let word_list_exists_def = new_definition
  `word_list_exists a n =
     SEP_EXISTS (\xs. misc_word_list a xs * cond (LENGTH xs = n))`;;

(* lookup_vars vs env = OPT_MMAP (\i. oEL i env) vs *)
let lookup_vars_def,lookup_vars_ind = define_rec
  [`lookup_vars [] env = SOME []`;
   `lookup_vars (CONS v vs) env =
         (if v < LENGTH env then
           match lookup_vars vs env with SOME xs -> SOME (CONS
               (EL v env) xs) | NONE -> NONE else NONE)`];;

let EVERY_lookup_vars = prove
 (`!vs env env'. ALL P env /\ lookup_vars vs env = SOME env' ==> ALL P
  env'`,
  CHEAT_TAC);;

let EVERY_LAST = prove
 (`!P l. ~(l = []) /\ ALL P l ==> P (LAST l)`,
  CHEAT_TAC);;

(* TODO - candidate for move to HOL *)
let num_to_hex_string_length_1 = prove
 (`!x. x < 16 ==> (LENGTH (num_to_hex_string x) = 1)`,
  CHEAT_TAC);;

(* TODO - candidate for move to HOL *)
let num_to_hex_string_length_2 = prove
 (`!x. 16 <= x /\ x < 256 ==> (LENGTH (num_to_hex_string x) = 2)`,
  CHEAT_TAC);;

let num_from_hex_string_length_2 = prove
 (`num_from_hex_string [d1; d2] < 256`,
  CHEAT_TAC);;

let num_from_hex_string_leading_0 = prove
 (`!ls. ~(ls = []) ==> (num_from_hex_string (CONS (CHR 48) ls) =
  num_from_hex_string ls)`,
  CHEAT_TAC);;

let num_from_hex_string_length_2_less_16 = prove
 (`!h1 h2. isHexDigit h1 ==> num_from_hex_string [h1; h2] < 16 ==> h1
  = (CHR 48)`,
  CHEAT_TAC);;

let num_from_hex_string_num_to_hex_string = prove
 (`num_from_hex_string (num_to_hex_string n) = n`,
  CHEAT_TAC);;
add_simp num_from_hex_string_num_to_hex_string;;

let MAPi_ID = prove
 (`MAPi (\x y. y) = I`,
  CHEAT_TAC);;
add_simp MAPi_ID;;

(* TODO - candidate for move to HOL - though
     enumerate i0 l = MAPi (λx i. (i + i0, x)) l
*)
let enumerate_def,enumerate_ind = define_rec
  [`enumerate n [] = []`;
   `enumerate n (CONS x xs) = CONS (n,x) (enumerate (n + 1) xs)`];;

(* TODO - candidate for move to HOL *)
let LENGTH_enumerate = prove
 (`!xs k. LENGTH (enumerate k xs) = LENGTH xs`,
  CHEAT_TAC);;

let EL_enumerate = prove
 (`!xs n k.
   n < LENGTH xs ==>
   EL n (enumerate k xs) = (n + k,EL n xs)`,
  CHEAT_TAC);;

let MAP_enumerate_MAPi = prove
 (`!f xs.
   MAP f (enumerate 0 xs) = MAPi (\n e. f (n,e)) xs`,
  CHEAT_TAC);;

let MAPi_enumerate_MAP = prove
 (`!f xs.
   MAPi f xs = MAP (\(i,e). f i e) (enumerate 0 xs)`,
  CHEAT_TAC);;

let MEM_enumerate = prove
 (`!xs i e.
   i < LENGTH xs ==>
   (MEM (i,e) (enumerate 0 xs) <=> EL i xs = e)`,
  CHEAT_TAC);;

let MEM_enumerate_IMP = prove
 (`!ls k.
   MEM (i,e) (enumerate k ls) ==> MEM e ls`,
  CHEAT_TAC);;

let MAP_FST_enumerate = prove
 (`MAP FST (enumerate k ls) = list_of_seq ((+) k) (LENGTH ls)`,
  CHEAT_TAC);;

let ALL_DISTINCT_MAP_FST_enumerate = prove
 (`ALL_DISTINCT (MAP FST (enumerate k ls))`,
  CHEAT_TAC);;

let ALOOKUP_enumerate = prove
 (`!ls k x.
   ALOOKUP (enumerate k ls) x =
   (if k <= x /\ x < LENGTH ls + k then SOME (EL (x - k) ls) else
     NONE)`,
  CHEAT_TAC);;

let SUM_MAP_LENGTH_REPLICATE = prove
 (`!n ls. SUM (MAP LENGTH (REPLICATE n ls)) = n * LENGTH ls`,
  CHEAT_TAC);;

let SUM_MAP_COUNT_LIST = prove
 (`!n k. SUM (MAP ((+) k) (COUNT_LIST n)) = (n * ((2 * k + n) - 1))
  DIV 2`,
  CHEAT_TAC);;

let SUM_REPLICATE = prove
 (`!n m. SUM (REPLICATE n m) = n * m`,
  CHEAT_TAC);;

let SUM_MAP_BOUND = prove
 (`(!x. f x <= c) ==> (SUM (MAP f ls) <= LENGTH ls * c)`,
  CHEAT_TAC);;

let SUM_MOD = prove
 (`k > 0 ==>
   (SUM ls MOD k = (SUM (MAP (\n. n MOD k) ls)) MOD k)`,
  CHEAT_TAC);;

let MOD_SUB_LEMMA = prove
 (`n MOD k = 0 /\ m MOD k = 0 /\ 0 < k ==> (n - m) MOD k = 0`,
  CHEAT_TAC);;

let FLAT_REPLICATE_NIL = prove
 (`!n. FLAT (REPLICATE n []) = []`,
  CHEAT_TAC);;

let MEM_REPLICATE_EQ = prove
 (`!n x y. MEM x (REPLICATE n y) <=> x = y /\ ~(n = 0)`,
  CHEAT_TAC);;

(* n.b. used in hol-reflection *)

let FDOM_FLOOKUP = prove
 (`x IN FDOM f <=> (?v. FLOOKUP f x = SOME v)`,
  CHEAT_TAC);;

let FLAT_MAP_SING = prove
 (`!ls. FLAT (MAP (\x. [f x]) ls) = MAP f ls`,
  CHEAT_TAC);;

let FLAT_MAP_NIL = prove
 (`FLAT (MAP (\x. []) ls) = []`,
  CHEAT_TAC);;

let UPDATE_LIST_NOT_MEM = prove
 (`!ls f x. ~(MEM x (MAP FST ls)) ==> (UPDATE_LIST f ls) x = f x`,
  CHEAT_TAC);;

let MAP_ZIP_UPDATE_LIST_ALL_DISTINCT_same = prove
 (`!ks vs f. LENGTH ks = LENGTH vs /\ ALL_DISTINCT ks ==> (MAP
  (UPDATE_LIST f (ZIP ks vs)) ks = vs)`,
  CHEAT_TAC);;

let flookup_update_list_none = prove
 (`!x m l.
    (FLOOKUP (m |++ l) x = NONE) =
    ((FLOOKUP m x = NONE) /\ (ALOOKUP l x = NONE))`,
  CHEAT_TAC);;

let flookup_update_list_some = prove
 (`!x m l y.
    (FLOOKUP (m |++ l) x = SOME y) =
    ((ALOOKUP (REVERSE l) x = SOME y) \/
     ((ALOOKUP l x = NONE) /\ (FLOOKUP m x = SOME y)))`,
  CHEAT_TAC);;

let MULT_LE_EXP = prove
 (`!(a:num) b. ~(a = 1) ==> a * b <= a EXP b`,
  CHEAT_TAC);;

let domain_rrestrict_subset = prove
 (`set_relation_domain (rrestrict r s) SUBSET set_relation_domain r
  INTER s`,
  CHEAT_TAC);;

let range_rrestrict_subset = prove
 (`set_relation_range (rrestrict r s) SUBSET set_relation_range r
  INTER s`,
  CHEAT_TAC);;

let PERM_MAP_BIJ = prove
 (`!f l1 l2.
    BIJ f UNIV UNIV ==>
    (PERM l1 l2 <=> PERM (MAP f l1) (MAP f l2))`,
  CHEAT_TAC);;

let lookup_fromList2 = prove
 (`!l n. sptree_lookup n (fromList2 l) =
          (if EVEN n then sptree_lookup (n DIV 2) (sptree_fromList
            l) else NONE)`,
  CHEAT_TAC);;

let domain_fromList2 = prove
 (`!q. domain (fromList2 q) = set_of_list (list_of_seq (\x. 2 * x)
  (LENGTH q))`,
  CHEAT_TAC);;

let UNCURRY_eq_pair = prove
 (`UNCURRY f v = z <=> (?a b. v = (a,b) /\ f a b = z)`,
  CHEAT_TAC);;

let OLEAST_SOME_IMP = prove
 (`OLEAST P = SOME i ==> P i /\ (!n. n < i ==> ~(P n))`,
  CHEAT_TAC);;

let EXP2_EVEN = prove
 (`!n. EVEN (2 EXP n) <=> ~(n = 0)`,
  CHEAT_TAC);;

let FST_UNZIP_MAPi = prove
 (`!l f. FST (UNZIP (MAPi f l)) = MAPi ((o) ((o) FST) f) l`,
  CHEAT_TAC);;

let SND_UNZIP_MAPi = prove
 (`!l f. SND (UNZIP (MAPi f l)) = MAPi ((o) ((o) SND) f) l`,
  CHEAT_TAC);;

let ALL_DISTINCT_FLAT = prove
 (`!l. ALL_DISTINCT (FLAT l) <=>
        (!l0. MEM l0 l ==> ALL_DISTINCT l0) /\
        (!i j. i < j /\ j < LENGTH l ==>
               (!e. MEM e (EL i l) ==> ~(MEM e (EL j l))))`,
  CHEAT_TAC);;

let ALL_DISTINCT_FLAT_EVERY = prove
 (`!ls. ALL_DISTINCT (FLAT ls) ==> ALL ALL_DISTINCT ls`,
  CHEAT_TAC);;

let ALL_DISTINCT_APPEND_APPEND_IMP = prove
 (`ALL_DISTINCT (APPEND (APPEND xs ys) zs) ==>
    ALL_DISTINCT (APPEND xs ys) /\ ALL_DISTINCT (APPEND xs zs) /\
      ALL_DISTINCT (APPEND ys zs)`,
  CHEAT_TAC);;

let GSPEC_o = prove
 (`hol4_GSPEC f o g = {x | ?y. (g x,T) = f y}`,
  CHEAT_TAC);;


(* TODO - candidate for move to HOL *)
let o_PAIR_MAP = prove
 (`FST o (f ## g) = f o FST /\
   SND o (f ## g) = g o SND`,
  CHEAT_TAC);;

let any_el_ALT = prove
 (`!l n d. any_el n l d = (if n < LENGTH l then EL n l else d)`,
  CHEAT_TAC);;

let MOD_MINUS = prove
 (`0 < p /\ 0 < k ==> (p * k - n MOD (p * k)) MOD k = (k - n MOD k)
  MOD k`,
  CHEAT_TAC);;

let option_fold_def = define_cases
  [`option_fold f x NONE = x`;
   `option_fold f x (SOME y) = f y x`];;

let SPLITP_CONS_IMP = prove
 (`!ls l' r. (SPLITP P ls = (l',r)) /\ (~(r = [])) ==> (EX P ls)`,
  CHEAT_TAC);;


let LAST_CONS_alt = prove
 (`P x ==> ((~(ls = []) ==> P (LAST ls)) <=> (P (LAST (CONS x ls))))`,
  CHEAT_TAC);;

let EL_CONS_IF = prove
 (`EL n (CONS x xs) = (if n = 0 then x else EL (PRE n) xs)`,
  CHEAT_TAC);;

let EVERY_TOKENS = prove
 (`!P ls. ALL (ALL ((~) o P)) (TOKENS P ls)`,
  CHEAT_TAC);;

let TOKENS_START = prove
 (`!l a. TOKENS (\x. x = a) (CONS a l) = TOKENS (\x. x = a) l`,
  CHEAT_TAC);;

let TOKENS_END = prove
 (`!l a.
      TOKENS (\x. x = a) (APPEND l [a]) = TOKENS (\x. x = a) l`,
  CHEAT_TAC);;


let TOKENS_LENGTH_END = prove
 (`!l a.
      LENGTH (TOKENS (\x. x = a) (APPEND l [a])) = LENGTH (TOKENS
        (\x. x = a) l)`,
  CHEAT_TAC);;

let TOKENS_LENGTH_START = prove
 (`!l a.
      LENGTH (TOKENS (\x. x = a) (CONS a l)) = LENGTH (TOKENS (\x.
        x = a) l)`,
  CHEAT_TAC);;


let DROP_EMPTY = prove
 (`!ls n. (DROP n ls = []) ==> (n >= LENGTH ls)`,
  CHEAT_TAC);;

(* [local] *)
let FRONT_APPEND' = prove
 (`!l h a b t. l = APPEND (APPEND h [a; b]) t ==>
       BUTLAST l = APPEND h (BUTLAST (APPEND [a; b] t))`,
  CHEAT_TAC);;


(* [local] *)
let EVERY_NOT_IMP = prove
 (`!ls a. (ALL ((~) o (\x. x = a)) ls) ==> (LIST_ELEM_COUNT a ls = 0)`,
  CHEAT_TAC);;

(* [local] *)
let LIST_ELEM_COUNT_CONS = prove
 (`!h t a. LIST_ELEM_COUNT a (CONS h t) = LIST_ELEM_COUNT a [h] +
  LIST_ELEM_COUNT a t`,
  CHEAT_TAC);;

(* [local] *)
let FRONT_COUNT_IMP = prove
 (`!l1 l2 a. ~(l1 = []) /\ BUTLAST l1 = l2 ==> (LIST_ELEM_COUNT a l2 =
  LIST_ELEM_COUNT a l1) \/ (LIST_ELEM_COUNT a l2 + 1 = LIST_ELEM_COUNT
  a l1)`,
  CHEAT_TAC);;

let OPT_MMAP_MAP_o = prove
 (`!ls. OPT_MMAP f (MAP g ls) = OPT_MMAP (f o g) ls`,
  CHEAT_TAC);;

let OPT_MMAP_SOME = prove
 (`OPT_MMAP SOME ls = SOME ls`,
  CHEAT_TAC);;
add_simp OPT_MMAP_SOME;;

(* [defncong] *)
let OPT_MMAP_CONG = prove
 (`!l1 l2 f f'.
     (l1 = l2) /\
     (!x. MEM x l2 ==> (f x = f' x)) ==> (OPT_MMAP f l1 = OPT_MMAP
       f' l2)`,
  CHEAT_TAC);;

let IMP_OPT_MMAP_EQ = prove
 (`!l1 l2. (MAP f1 l1 = MAP f2 l2) ==> (OPT_MMAP f1 l1 = OPT_MMAP f2
  l2)`,
  CHEAT_TAC);;

let DISJOINT_set_simp = prove
 (`DISJOINT (set_of_list []) s /\
    (DISJOINT (set_of_list (CONS x xs)) s <=> ~(x IN s) /\ DISJOINT
      (set_of_list xs) s)`,
  CHEAT_TAC);;

let DISJOINT_INTER = prove
 (`DISJOINT b c ==> DISJOINT (a INTER b) (a INTER c)`,
  CHEAT_TAC);;

let ALOOKUP_EXISTS_IFF = prove
 (`(?v. ALOOKUP alist k = SOME v) <=> (?v. MEM (k,v) alist)`,
  CHEAT_TAC);;

let LUPDATE_commutes = prove
 (`!m n e1 e2 l. ~(m = n) ==>
    LUPDATE e1 m (LUPDATE e2 n l) = LUPDATE e2 n (LUPDATE e1 m l)`,
  CHEAT_TAC);;

let LUPDATE_APPEND = prove
 (`!xs n ys x.
      LUPDATE x n (APPEND xs ys) =
      (if n < LENGTH xs then APPEND (LUPDATE x n xs) ys else APPEND
        xs (LUPDATE x (n - LENGTH xs) ys))`,
  CHEAT_TAC);;

let FILTER_EL_EQ = prove
 (`!l1 l2.
   LENGTH l1 = LENGTH l2 /\
   (!n. n < LENGTH l1 /\ (P (EL n l1) \/ P (EL n l2)) ==> (EL n l1 =
     EL n l2)) ==>
   FILTER P l1 = FILTER P l2`,
  CHEAT_TAC);;

let FST_EL_AFUPDKEY = prove
 (`!n. n < LENGTH ls ==> FST (EL n (AFUPDKEY k f ls)) = FST (EL n ls)`,
  CHEAT_TAC);;

let EL_AFUPDKEY_unchanged = prove
 (`!n. n < LENGTH ls /\ ~(FST (EL n ls) = k) ==> EL n (AFUPDKEY k f
  ls) = EL n ls`,
  CHEAT_TAC);;

let findi_APPEND = prove
 (`!l1 l2 x.
      indexedLists_findi x (APPEND l1 l2) =
        (let n0 = indexedLists_findi x l1 in
          if n0 = LENGTH l1 then n0 + indexedLists_findi x l2 else
            n0)`,
  CHEAT_TAC);;

let NOT_MEM_findi_IFF = prove
 (`~(MEM e l) <=> indexedLists_findi e l = LENGTH l`,
  CHEAT_TAC);;

(* HOL4 miscScript.sml:2585-2586: a theorem that HOL4 states as the
   value of an ML expression: NOT_MEM_findi *)

let ORD_eq_0 = prove
 (`(ORD c = 0 <=> c = CHR 0) /\ (0 = ORD c <=> c = CHR 0)`,
  CHEAT_TAC);;

let HD_LUPDATE = prove
 (`0 < LENGTH l ==> HD (LUPDATE x p l) = (if p = 0 then x else HD l)`,
  CHEAT_TAC);;

let DROP_LUPDATE = prove
 (`!n x m l. n <= m ==> DROP n (LUPDATE x m l) = LUPDATE x (m - n)
  (DROP n l)`,
  CHEAT_TAC);;

(* HOL4 miscScript.sml:2608-2610: a theorem that HOL4 states as the
   value of an ML expression: w2n_lt_256 *)

let CHR_w2n_n2w_ORD = prove
 (`(CHR o w2n o (n2w:num->word8) o ORD) = I`,
  CHEAT_TAC);;

let n2w_ORD_CHR_w2n = prove
 (`((n2w:num->word8) o ORD o CHR o w2n) = I`,
  CHEAT_TAC);;

let CHR_w2n_n2w_ORD_simp = prove
 (`!c. CHR (w2n ((n2w:num->word8) (ORD c))) = c`,
  CHEAT_TAC);;
add_simp CHR_w2n_n2w_ORD_simp;;

let n2w_ORD_CHR_w2n_simp = prove
 (`!w. n2w (ORD (CHR (w2n w))) = (w:word8)`,
  CHEAT_TAC);;
add_simp n2w_ORD_CHR_w2n_simp;;

let MAP_CHR_w2n_11 = prove
 (`!ws1 (ws2:word8 list).
      MAP (CHR o w2n) ws1 = MAP (CHR o w2n) ws2 <=> ws1 = ws2`,
  CHEAT_TAC);;

let MAP_K_REPLICATE = prove
 (`MAP (K x) ls = REPLICATE (LENGTH ls) x`,
  CHEAT_TAC);;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let shift_left_def,shift_left_ind = define_wf
  `MEASURE (\(x0,x1). (\n. n) x1)`
  [`shift_left (a:'a word) n =
   (if n = 0 then a else if (a = (n2w 0)) \/ n > dimindex (:'a)
     then (n2w 0) else if n > 32 then shift_left (a << 32) (n - 32)
     else if n > 16 then shift_left (a << 16) (n - 16) else if n >
     8 then shift_left (a << 8) (n - 8) else shift_left (a << 1) (n
     - 1))`];;

let shift_left_rwt = prove
 (`!a n. a << n = shift_left a n`,
  CHEAT_TAC);;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let shift_right_def,shift_right_ind = define_wf
  `MEASURE (\(x0,x1). (\n. n) x1)`
  [`shift_right (a:'a word) n =
   (if n = 0 then a else if (a = (n2w 0)) \/ n > dimindex (:'a)
     then (n2w 0) else if n > 32 then shift_right (a >>> 32) (n -
     32) else if n > 16 then shift_right (a >>> 16) (n - 16) else
     if n > 8 then shift_right (a >>> 8) (n - 8) else shift_right
     (a >>> 1) (n - 1))`];;

let shift_right_rwt = prove
 (`!a n. a >>> n = shift_right a n`,
  CHEAT_TAC);;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let arith_shift_right_def,arith_shift_right_ind = define_wf
  `MEASURE (\(x0,x1). (\n. n) x1)`
  [`arith_shift_right (a:'a word) n =
   (if n = 0 then a else if (a = (n2w 0)) \/ n > dimindex (:'a)
     /\ ~(word_msb a) then (n2w 0) else if (a = --(n2w 1)) \/ n >
     dimindex (:'a) /\ word_msb a then --(n2w 1) else if n > 32
     then arith_shift_right (a >> 32) (n - 32) else if n > 16 then
     arith_shift_right (a >> 16) (n - 16) else if n > 8 then
     arith_shift_right (a >> 8) (n - 8) else arith_shift_right (a
     >> 1) (n - 1))`];;

let arith_shift_right_rwt = prove
 (`!a n. a >> n = arith_shift_right a n`,
  CHEAT_TAC);;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let any_word64_ror_def,any_word64_ror_ind = define_wf
  `MEASURE (\(x0,x1). (\n. n) x1)`
  [`any_word64_ror (w:word64) (n:num) =
     (if 64 <= n then any_word64_ror w (n - 64) else
     if 32 <= n then any_word64_ror (word_ror w 32) (n - 32) else
     if 16 <= n then any_word64_ror (word_ror w 16) (n - 16) else
     if 8 <= n then any_word64_ror (word_ror w 8) (n - 8) else
     if 4 <= n then any_word64_ror (word_ror w 4) (n - 4) else
     if 2 <= n then any_word64_ror (word_ror w 2) (n - 2) else
     if 1 <= n then word_ror w 1 else w)`];;

let word_ror_eq_any_word64_ror = prove
 (`!a n. word_ror a n = any_word64_ror a n`,
  CHEAT_TAC);;

let TL_DROP_SUC = prove
 (`!x ls. x < LENGTH ls ==> TL (DROP x ls) = DROP (SUC x) ls`,
  CHEAT_TAC);;

let DROP_IMP_LESS_LENGTH = prove
 (`!xs n y ys. DROP n xs = CONS y ys ==> n < LENGTH xs`,
  CHEAT_TAC);;

let DROP_EQ_CONS_IMP_DROP_SUC = prove
 (`!xs n y ys. DROP n xs = CONS y ys ==> DROP (SUC n) xs = ys`,
  CHEAT_TAC);;

let DROP_IMP_EL = prove
 (`!xs n h t. DROP n xs = CONS h t ==> (EL n xs = h)`,
  CHEAT_TAC);;

let LENGTH_FIELDS = prove
 (`!ls. LENGTH (FIELDS P ls) = LENGTH (FILTER P ls) + 1`,
  CHEAT_TAC);;

let FIELDS_NEQ_NIL = prove
 (`~(FIELDS P ls = [])`,
  CHEAT_TAC);;
add_simp FIELDS_NEQ_NIL;;

let CONCAT_FIELDS = prove
 (`!ls. FLAT (FIELDS P ls) = FILTER ((~) o P) ls`,
  CHEAT_TAC);;

let FIELDS_next = prove
 (`!ls l1 l2.
   FIELDS P ls = CONS l1 l2 ==>
   LENGTH l1 < LENGTH ls ==>
   FIELDS P (DROP (SUC (LENGTH l1)) ls) = l2 /\
   (?c. APPEND l1 [c] <<= ls /\ P c)`,
  CHEAT_TAC);;

let FIELDS_full = prove
 (`!P ls l1 l2.
   FIELDS P ls = CONS l1 l2 /\ LENGTH ls <= LENGTH l1 ==>
   l1 = ls /\ l2 = []`,
  CHEAT_TAC);;

let FLAT_MAP_TOKENS_FIELDS = prove
 (`!P' ls P.
    (!x. P' x ==> P x) ==>
     FLAT (MAP (TOKENS P) (FIELDS P' ls)) =
     TOKENS P ls`,
  CHEAT_TAC);;

let the_nil_eq_cons = prove
 (`(the [] x = CONS y z) <=> x = SOME (CONS y z)`,
  CHEAT_TAC);;

let splitlines_def = new_definition
  `splitlines ls =
   (let lines = FIELDS ((=) (CHR 10)) ls in
   // discard trailing newline
   if NULL (LAST lines) then BUTLAST lines else lines)`;;

let splitlines_next = prove
 (`splitlines ls = CONS ln lns ==>
   splitlines (DROP (SUC (LENGTH ln)) ls) = lns /\
   ln <<= ls /\ (LENGTH ln < LENGTH ls ==> APPEND ln "\n" <<= ls)`,
  CHEAT_TAC);;

(* HOL4 miscScript.sml:2935: a theorem that HOL4 states as the value
   of an ML expression: splitlines_nil *)

let splitlines_eq_nil = prove
 (`splitlines ls = [] <=> (ls = [])`,
  CHEAT_TAC);;
add_simp splitlines_eq_nil;;

let splitlines_CONS_FST_SPLITP = prove
 (`splitlines ls = CONS ln lns ==> FST (SPLITP ((=) (CHR 10)) ls) = ln`,
  CHEAT_TAC);;

let n2l_DIV_MOD = prove
 (`!b n k. 1 < b /\ 0 < k /\ b EXP k <= n ==>
   (APPEND (APPEND (n2l b (n MOD (b EXP k))) (REPLICATE (k - LENGTH
     (n2l b (n MOD (b EXP k)))) 0))
    (n2l b (n DIV (b EXP k))) = n2l b n)`,
  CHEAT_TAC);;

let irreflexive_inv_image = prove
 (`!R f. irreflexive R ==> irreflexive (inv_image R f)`,
  CHEAT_TAC);;

let trichotomous_inv_image = prove
 (`!R f. trichotomous R /\ (INJ f UNIV UNIV) ==> trichotomous
  (inv_image R f)`,
  CHEAT_TAC);;

let MEM_REPLICATE_IMP = prove
 (`MEM x (REPLICATE n y) ==> x = y`,
  CHEAT_TAC);;

let plus_0_I = prove
 (`(+) 0 = I`,
  CHEAT_TAC);;
add_simp plus_0_I;;

(* used once *)
(* HOL4 miscScript.sml:3037-3038: a theorem that HOL4 states as the
   value of an ML expression: SUM_COUNT_LIST *)

let OPTION_MAP_I = prove
 (`OPTION_MAP I x = x`,
  CHEAT_TAC);;
add_simp OPTION_MAP_I;;

(* should be made an iff in conclusion *)
let OPTION_MAP_INJ = prove
 (`(!x y. f x = f y ==> x = y) ==> (!o1 o2.
     OPTION_MAP f o1 = OPTION_MAP f o2 ==> o1 = o2)`,
  CHEAT_TAC);;

let the_OPTION_MAP = prove
 (`!f d opt.
   f d = d ==>
   the d (OPTION_MAP f opt) = f (the d opt)`,
  CHEAT_TAC);;

let TAKE_FLAT_REPLICATE_LEQ = prove
 (`!j k ls len.
    len = LENGTH ls /\ k <= j ==>
    TAKE (k * len) (FLAT (REPLICATE j ls)) = FLAT (REPLICATE k ls)`,
  CHEAT_TAC);;

let MOD_2EXP_0_EVEN = prove
 (`!x y. 0 < x /\ MOD_2EXP x y = 0 ==> EVEN y`,
  CHEAT_TAC);;

let ADD_MOD_EQ_LEMMA = prove
 (`k MOD d = 0 /\ n < d ==> (k + n) MOD d = n`,
  CHEAT_TAC);;

(* should be set l1 ⊆ set l2 *)
let list_subset_def = new_definition
  `list_subset l1 l2 = ALL (\x. MEM x l2) l1`;;

let list_set_eq_def = new_definition
  `list_set_eq l1 l2 <=> list_subset l1 l2 /\ list_subset l2 l1`;;

let list_subset_LENGTH = prove
 (`!l1 l2. ALL_DISTINCT l1 /\
   list_subset l1 l2 ==>
   LENGTH l1 <= LENGTH l2`,
  CHEAT_TAC);;

let BIJ_UPDATE = prove
 (`!f s t x y. BIJ f s t /\ ~(x IN s) /\ ~(y IN t) ==>
    BIJ ((x =+ y) f) (x INSERT s) (y INSERT t)`,
  CHEAT_TAC);;

let INJ_UPDATE = prove
 (`INJ f s t /\ ~(x IN s) /\ ~(y IN t) ==>
    INJ ((x =+ y) f) (x INSERT s) (y INSERT t)`,
  CHEAT_TAC);;

(* TODO: candidate for move to HOL;
         subspt_domain exists already but is specialised to unit *)
let subspt_domain_SUBSET = prove
 (`subspt t1 t2 ==> domain t1 SUBSET domain t2`,
  CHEAT_TAC);;

(* Some temporal logic definitions based on lazy lists *)
(* move into llistTheory? *)

let SPLITP_TAKE_DROP = prove
 (`!P i l. ALL ((~) o P) (TAKE i l) ==>
   P (EL i l) ==>
   SPLITP P l = (TAKE i l,DROP i l)`,
  CHEAT_TAC);;

let SND_SPLITP_DROP = prove
 (`!P n l. ALL ((~) o P) (TAKE n l) ==>
    SND (SPLITP P (DROP n l)) = SND (SPLITP P l)`,
  CHEAT_TAC);;

let FST_SPLITP_DROP = prove
 (`!P n l. ALL ((~) o P) (TAKE n l) ==>
    FST (SPLITP P l) = APPEND (TAKE n l) (FST (SPLITP P (DROP n
      l)))`,
  CHEAT_TAC);;

let TAKE_DROP_SUBLIST = prove
 (`ll <<= (DROP n ls) /\ n < LENGTH ls /\ (nlll = n + LENGTH ll) ==>
   (APPEND (APPEND (TAKE n ls) ll) (DROP nlll ls) = ls)`,
  CHEAT_TAC);;

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

let lnext_pos_def = new_definition
  `Lnext_pos (ll:num llist) = Lnext (\ll. ?k. LHD ll = SOME k /\ ~(k
  = 0)) ll`;;

let OPTION_CHOICE_EQUALS_OPTION = prove
 (`!(x:'a option) y z. (OPTION_CHOICE x y = SOME z) <=>
                       ((x = SOME z) \/ ((x = NONE) /\ (y = SOME
                         z)))`,
  CHEAT_TAC);;

(* HOL4 miscScript.sml:3210-3214: a theorem that HOL4 states as the
   value of an ML expression: option_eq_some *)

let ALL_DISTINCT_alist_to_fmap_REVERSE = prove
 (`ALL_DISTINCT (MAP FST ls) ==> alist_to_fmap (REVERSE ls) =
  alist_to_fmap ls`,
  CHEAT_TAC);;

let FUPDATE_LIST_alist_to_fmap = prove
 (`!ls fm. fm |++ ls = FUNION (alist_to_fmap (REVERSE ls)) fm`,
  CHEAT_TAC);;

let DISTINCT_FUPDATE_LIST_UNION = prove
 (`ALL_DISTINCT (MAP FST ls) /\
   DISJOINT (FDOM f) (set_of_list (MAP FST ls)) ==>
   f |++ ls = FUNION f (alist_to_fmap ls)`,
  CHEAT_TAC);;

let fevery_to_drestrict = prove
 (`!P m s.
    FEVERY P m ==> FEVERY P (DRESTRICT m s)`,
  CHEAT_TAC);;

let SUM_MAP_K = prove
 (`!f ls c. (!x. f x = c) ==> SUM (MAP f ls) = LENGTH ls * c`,
  CHEAT_TAC);;

let LAST_FLAT = prove
 (`!ls. ~(NULL (FLAT ls)) ==> (LAST (FLAT ls) = LAST (LAST (FILTER
  ((~) o NULL) ls)))`,
  CHEAT_TAC);;

let TOKENS_unchanged = prove
 (`ALL ((~) o P) ls ==> TOKENS P ls = (if NULL ls then [] else [ls])`,
  CHEAT_TAC);;

let TOKENS_FLAT_MAP_SNOC = prove
 (`ALL (ALL ((\x y. ~(x = y)) x)) ls /\ ALL ((~) o NULL) ls ==>
   TOKENS ((=) x) (FLAT (MAP (SNOC x) ls)) = ls`,
  CHEAT_TAC);;

(* insert a string (l1) at specified index (n) in a list (l2) *)
let insert_atI_def = new_definition
  `insert_atI l1 n l2 = APPEND (APPEND (TAKE n l2) l1) (DROP (n +
  LENGTH l1) l2)`;;

let insert_atI_NIL = prove
 (`!n l. insert_atI [] n l = l`,
  CHEAT_TAC);;

let insert_atI_CONS = prove
 (`!n l h t.
     n + LENGTH t < LENGTH l ==>
     insert_atI (CONS h t) n l = LUPDATE h n (insert_atI t (n + 1)
       l)`,
  CHEAT_TAC);;

let LENGTH_insert_atI = prove
 (`p + LENGTH l1 <= LENGTH l2 ==> LENGTH (insert_atI l1 p l2) = LENGTH
  l2`,
  CHEAT_TAC);;

let insert_atI_app = prove
 (`!n l c1 c2. n + LENGTH c1 + LENGTH c2 <= LENGTH l ==>
     insert_atI (APPEND c1 c2) n l =
     insert_atI c1 n (insert_atI c2 (n + LENGTH c1) l)`,
  CHEAT_TAC);;

let insert_atI_end = prove
 (`insert_atI l1 (LENGTH l2) l2 = APPEND l2 l1`,
  CHEAT_TAC);;

let insert_atI_insert_atI = prove
 (`pos2 = pos1 + LENGTH c1 ==>
    insert_atI c2 pos2 (insert_atI c1 pos1 l) = insert_atI (APPEND
      c1 c2) pos1 l`,
  CHEAT_TAC);;

let LUPDATE_insert_commute = prove
 (`!ws pos1 pos2 a w.
     pos2 < pos1 /\ pos1 + LENGTH ws <= LENGTH a ==>
     insert_atI ws pos1 (LUPDATE w pos2 a) =
       LUPDATE w pos2 (insert_atI ws pos1 a)`,
  CHEAT_TAC);;

let LESS_EQ_LENGTH = prove
 (`!xs k. k <= LENGTH xs ==> (?ys1 ys2. (xs = APPEND ys1 ys2) /\
  (LENGTH ys1 = k))`,
  CHEAT_TAC);;

let LESS_LENGTH = prove
 (`!xs k. k < LENGTH xs ==>
           (?ys1 y ys2. (xs = APPEND ys1 (CONS y ys2)) /\ (LENGTH
             ys1 = k))`,
  CHEAT_TAC);;

(* HOL4 miscScript.sml:3372-3373: a theorem that HOL4 states as the
   value of an ML expression: IN_EVEN *)

let FOLDL_OPTION_CHOICE_EQ_SOME_IMP_MEM = prove
 (`FOLDL OPTION_CHOICE x ls = SOME y ==> MEM (SOME y) (CONS x ls)`,
  CHEAT_TAC);;

let BAG_ALL_DISTINCT_FOLDR_BAG_UNION = prove
 (`!ls b0.
   BAG_ALL_DISTINCT (ITLIST (BAG_UNION) ls b0) <=>
   BAG_ALL_DISTINCT b0 /\
   (!n. n < LENGTH ls ==>
        BAG_DISJOINT (EL n ls) b0 /\ BAG_ALL_DISTINCT (EL n ls) /\
        (!m. m < n ==> BAG_DISJOINT (EL n ls) (EL m ls)))`,
  CHEAT_TAC);;

(* TODO - candidate for move to HOL *)
(* N.B.: there is a different is_subsequence defined in lcsTheory; these should be merged *)
let is_subseq_def,is_subseq_ind = define_guess
  [`is_subseq ls [] <=> T`;
   `is_subseq [] (CONS x xs) <=> F`;
   `is_subseq (CONS y ys) (CONS x xs) <=>
       (x = y /\ is_subseq ys xs) \/
       (is_subseq ys (CONS x xs))`];;

(* TODO - candidate for move to HOL *)
(* HOL4 miscScript.sml:3413: ML code, not ported *)

(* TODO - candidate for move to HOL *)
let is_subseq_refl = prove
 (`!ls. is_subseq ls ls`,
  CHEAT_TAC);;
add_simp is_subseq_refl;;

(* TODO - candidate for move to HOL *)
let is_subseq_nil = prove
 (`is_subseq [] ls <=> ls = []`,
  CHEAT_TAC);;
add_simp is_subseq_nil;;

(* TODO - candidate for move to HOL *)
let is_subseq_cons = prove
 (`!l1 l2 x. is_subseq l1 l2 ==> is_subseq (CONS x l1) l2`,
  CHEAT_TAC);;

(* TODO - candidate for move to HOL *)
let is_subseq_snoc = prove
 (`!l1 l2 x. is_subseq l1 l2 ==> is_subseq (SNOC x l1) l2`,
  CHEAT_TAC);;

(* TODO - candidate for move to HOL *)
let is_subseq_append1 = prove
 (`!l3 l1 l2. is_subseq l1 l2 ==> is_subseq (APPEND l3 l1) l2`,
  CHEAT_TAC);;

(* TODO - candidate for move to HOL *)
let is_subseq_append2 = prove
 (`!l4 l1 l2. is_subseq l1 l2 ==> is_subseq (APPEND l1 l4) l2`,
  CHEAT_TAC);;

(* TODO - candidate for move to HOL *)
let is_subseq_IS_SUBLIST = prove
 (`is_subseq l1 l2 /\ IS_SUBLIST l3 l1 ==> is_subseq l3 l2`,
  CHEAT_TAC);;

(* TODO - candidate for move to HOL *)
let is_subseq_MEM = prove
 (`!l1 l2 x. is_subseq l1 l2 /\ MEM x l2 ==> MEM x l1`,
  CHEAT_TAC);;

(* TODO - candidate for move to HOL *)
let IS_PREFIX_is_subseq = prove
 (`!l1 l2. IS_PREFIX l1 l2 ==> is_subseq l1 l2`,
  CHEAT_TAC);;

(* TODO - candidate for move to HOL *)
let IS_SUBLIST_is_subseq = prove
 (`!l1 l2. IS_SUBLIST l1 l2 ==> is_subseq l1 l2`,
  CHEAT_TAC);;

(* TODO - candidate for move to HOL *)
let is_subseq_ALL_DISTINCT = prove
 (`!l1 l2. ALL_DISTINCT l1 /\ is_subseq l1 l2 ==> ALL_DISTINCT l2`,
  CHEAT_TAC);;

(* TODO - candidate for move to HOL *)
let is_subseq_append_suff = prove
 (`!l1 l3 l2 l4.
   is_subseq l1 l3 /\ is_subseq l2 l4 ==>
   is_subseq (APPEND l1 l2) (APPEND l3 l4)`,
  CHEAT_TAC);;

(* TODO - candidate for move to HOL *)
let is_subseq_FLAT_suff = prove
 (`!ls1 ls2. ALL2 is_subseq ls1 ls2 ==> is_subseq (FLAT ls1) (FLAT
  ls2)`,
  CHEAT_TAC);;

let LIST_REL_IMP_LAST = prove
 (`!P xs ys.
      ALL2 P xs ys /\ (~(xs = []) \/ ~(ys = [])) ==> P (LAST xs)
        (LAST ys)`,
  CHEAT_TAC);;

let make_even_def = new_definition
  `make_even n = (if EVEN n then n else n + 1)`;;

let EVEN_make_even = prove
 (`EVEN (make_even x)`,
  CHEAT_TAC);;
add_simp EVEN_make_even;;

let ALOOKUP_MAP_FST_INJ_SOME = prove
 (`!ls x y.
    ALOOKUP ls x = SOME y /\ (!x'. IS_SOME (ALOOKUP ls x') /\ f x' =
      f x ==> x = x') ==>
    ALOOKUP (MAP (f ## g) ls) (f x) = SOME (g y)`,
  CHEAT_TAC);;

let v2w_32_F = prove
 (`(v2w [F]:word32) = (n2w 0)`,
  CHEAT_TAC);;
add_simp v2w_32_F;;

let v2w_32_T = prove
 (`(v2w [T]:word32) = (n2w 1)`,
  CHEAT_TAC);;
add_simp v2w_32_T;;

let v2w_sing = prove
 (`v2w [b] = (if b then (n2w 1) else (n2w 0))`,
  CHEAT_TAC);;

let FOLDR_FUNPOW = prove
 (`ITLIST (\x. f) ls x = ITER (LENGTH ls) f x`,
  CHEAT_TAC);;

let FUNPOW_refl_trans_chain = prove
 (`transitive P /\ reflexive P ==>
   (!n x. (!j. j < n ==> P (ITER j f x) (f (ITER j f x))) ==>
     P x (ITER n f x))`,
  CHEAT_TAC);;

let byte_align_extract = prove
 (`byte_align (x:word32) = (((31 >< 2) x):word30) @@ ((n2w 0):word2)`,
  CHEAT_TAC);;

let byte_align_IN_IMP_IN_range = prove
 (`byte_align a IN dm /\
   (dm = {w | low <=+ w /\ w <+ hi}) /\
   byte_aligned low /\ byte_aligned hi ==>
   a IN dm`,
  CHEAT_TAC);;

let MULT_DIV_MULT_LEMMA = prove
 (`!m l k. 0 < m /\ 0 < l ==> (m * k) DIV (l * m) = k DIV l`,
  CHEAT_TAC);;

let IMP_MULT_DIV_LESS = prove
 (`~(m = 0) /\ d < k ==> m * (d DIV m) < k`,
  CHEAT_TAC);;

let DIV_LESS_DIV = prove
 (`n MOD k = 0 /\ m MOD k = 0 /\ n < m /\ 0 < k ==> n DIV k < m DIV k`,
  CHEAT_TAC);;

let toPath_fromList = prove
 (`(toPath (x,fromList []) = stopped_at x) /\
   (toPath (x,fromList (CONS (y,z) t)) = pcons x y (toPath
     (z,fromList t)))`,
  CHEAT_TAC);;

let steps_def,steps_ind = define_rec
  [`steps f x [] = []`;
   `steps f x (CONS j js) =
       (let y = f x j in
       let tr = steps f y js in
         (CONS (j,y) tr))`];;

let steps_rel_def,steps_rel_ind = define_rec
  [`steps_rel R x [] <=> T`;
   `steps_rel R x (CONS (j,y) tr) <=>
        R x j y /\
        steps_rel R y tr`];;

(* HOL4 miscScript.sml:3681: ML code, not ported *)

let steps_rel_okpath = prove
 (`!R x tr.
    steps_rel R x tr <=> okpath R (toPath (x,fromList tr))`,
  CHEAT_TAC);;

let steps_rel_LRC = prove
 (`!R x tr.
    steps_rel R x tr ==>
    LRC (\x y. ?i. R x i y)
      (BUTLAST (CONS x (MAP SND tr))) x (LAST (CONS x (MAP SND
        tr)))`,
  CHEAT_TAC);;

let LAST_MAP_SND_steps_FOLDL = prove
 (`!f x ls. LAST (CONS x (MAP SND (steps f x ls))) = FOLDL f x ls`,
  CHEAT_TAC);;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let all_words_def,all_words_ind = define_wf
  `MEASURE (\(x0,x1). (\n. n) x1)`
  [`all_words base 0 = {}`;
   `all_words base (SUC n) = base INSERT (all_words (base + (n2w
    1)) n)`];;

let IN_all_words = prove
 (`x IN all_words base n <=> (?i. i < n /\ x = base + n2w i)`,
  CHEAT_TAC);;

let read_bytearray_IMP_mem_SOME = prove
 (`!p n m ba.
   (read_bytearray p n m = SOME ba) ==>
   (!k. k IN all_words p n ==> IS_SOME (m k))`,
  CHEAT_TAC);;

let read_bytearray_no_wrap = prove
 (`!ptr len.
   IS_SOME (read_bytearray ptr len (m:'a word->'b option)) /\
   (!x. IS_SOME (m x) ==> w2n x < dimword (:'a) - 1) /\
   w2n ptr < dimword (:'a) ==>
   w2n ptr + len < dimword (:'a)`,
  CHEAT_TAC);;

let asm_write_bytearray_def,asm_write_bytearray_ind = define_guess
  [`asm_write_bytearray a [] (m:'a word->word8) = m`;
   `asm_write_bytearray a (CONS x xs) (m:'a word->word8) = (a =+ x)
    (asm_write_bytearray (a + (n2w 1)) xs m)`];;

let mem_eq_imp_asm_write_bytearray_eq = prove
 (`!a bs.
    (m1 k = m2 k) ==>
    (asm_write_bytearray a bs m1 k = asm_write_bytearray a bs m2 k)`,
  CHEAT_TAC);;

let asm_write_bytearray_unchanged = prove
 (`!a bs m z.
   (x <+ a \/ a + n2w (LENGTH bs) <=+ x) /\
    (w2n a + LENGTH bs < dimword (:'a)) /\ (z = m x) ==>
      (asm_write_bytearray (a:'a word) bs m x = z)`,
  CHEAT_TAC);;

let asm_write_bytearray_id = prove
 (`!a bs m.
    (!j. j < LENGTH bs ==> (m (a + n2w j) = EL j bs)) ==>
      (asm_write_bytearray (a:'a word) bs m x = m x)`,
  CHEAT_TAC);;

let asm_write_bytearray_unchanged_alt = prove
 (`!a bs m z.
      (z = m x) /\ ~(x IN {a + n2w k | k < LENGTH bs}) ==>
      (asm_write_bytearray a bs m x = z)`,
  CHEAT_TAC);;

let asm_write_bytearray_unchanged_all_words = prove
 (`!a bs m z x.
    ~(x IN all_words a (LENGTH bs)) /\ (z = m x) ==>
    (asm_write_bytearray (a:'a word) bs m x = z)`,
  CHEAT_TAC);;

let asm_write_bytearray_append = prove
 (`!a l1 l2 m.
   w2n a + LENGTH l1 + LENGTH l2 < dimword (:'a) ==>
   (asm_write_bytearray (a:'a word) (APPEND l1 l2) m =
    asm_write_bytearray (a + n2w (LENGTH l1)) l2
      (asm_write_bytearray a l1 m))`,
  CHEAT_TAC);;

let asm_write_bytearray_EL = prove
 (`!a bs m x. x < LENGTH bs /\ LENGTH bs < dimword (:'a) ==>
   (asm_write_bytearray (a:'a word) bs m (a + n2w x) = EL x bs)`,
  CHEAT_TAC);;

(* TODO: move to sptTheory *)

let _ = size_thms "spt";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let eq_shape_def,eq_shape_ind = define_wf
  `MEASURE (\(x0,x1). spt_size (\x. 0) x0 + spt_size (\x. 0) x1)`
  [`eq_shape x1 x2 =
      match (x1,x2) with
        (LN,LN) -> T
      | ((LS _4),(LS _5)) -> T
      | ((BN t1 t2),(BN u1 u2)) -> (eq_shape t1 u1 /\ eq_shape t2
        u2)
      | ((BS t1 _6 t2),(BS u1 _7 u2)) -> (eq_shape t1 u1 /\ eq_shape
        t2 u2)
      | (_8,_9) -> F`];;

let spt_eq = prove
 (`!t1 t2.
      t1 = t2 <=>
      (eq_shape t1 t2 /\ (!k v. sptree_lookup k t1 = SOME v ==>
        sptree_lookup k t2 = SOME v))`,
  CHEAT_TAC);;

let eq_shape_map = prove
 (`!t1 t2 f. eq_shape (sptree_map f t1) t2 <=> eq_shape t1 t2`,
  CHEAT_TAC);;

let eq_shape_IMP_domain = prove
 (`!t1 t2. eq_shape t1 t2 ==> domain t1 = domain t2`,
  CHEAT_TAC);;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let copy_shape_def,copy_shape_ind = define_wf
  `MEASURE (\(x0,x1). spt_size (\x. 0) x0 + spt_size (\x. 0) x1)`
  [`copy_shape LN LN = LN`;
   `copy_shape LN (LS y) = LN`;
   `copy_shape LN (BN t1 t2) = BN (copy_shape LN t1) (copy_shape LN
    t2)`;
   `copy_shape LN (BS t1 y t2) = LN`;
   `copy_shape (LS x) LN = LS x`;
   `copy_shape (LS x) (LS y) = LS x`;
   `copy_shape (LS x) (BN t1 t2) = LS x`;
   `copy_shape (LS x) (BS t1 y t2) = BS (copy_shape LN t1) x
    (copy_shape LN t2)`;
   `copy_shape (BN u1 u2) LN = (if domain (BN u1 u2) = {} then LN
    else BN u1 u2)`;
   `copy_shape (BN u1 u2) (LS y) = BN u1 u2`;
   `copy_shape (BN u1 u2) (BN t1 t2) = BN (copy_shape u1 t1)
    (copy_shape u2 t2)`;
   `copy_shape (BN u1 u2) (BS t1 y t2) = BN u1 u2`;
   `copy_shape (BS u1 x u2) LN = BS u1 x u2`;
   `copy_shape (BS u1 x u2) (LS y) =
       (if domain (BN u1 u2) = {} then LS x else BS u1 x u2)`;
   `copy_shape (BS u1 x u2) (BN t1 t2) = BS u1 x u2`;
   `copy_shape (BS u1 x u2) (BS t1 y t2) = BS (copy_shape u1 t1) x
    (copy_shape u2 t2)`];;

(* [local] *)
let eq_shape_copy_shape = prove
 (`!s. domain s = {} ==> eq_shape (copy_shape LN s) s`,
  CHEAT_TAC);;

(* [local] *)
let num_lemma = prove
 (`(!n. ~(0 = 2 * n + 2) /\ ~(0 = 2 * n + (1:num))) /\
   (!n m. 2 * n + 2 = 2 * m + 2 <=> (m = n)) /\
   (!n m. 2 * n + 1 = 2 * m + 1 <=> (m = n)) /\
   (!n m. ~(2 * n + 2 = 2 * m + 1))`,
  CHEAT_TAC);;

let shape_eq_copy_shape = prove
 (`!t1 t2. domain t1 = domain t2 ==> eq_shape (copy_shape t1 t2) t2`,
  CHEAT_TAC);;

(* [local] *)
let lookup_copy_shape_LN = prove
 (`!s n. sptree_lookup n (copy_shape LN s) = NONE`,
  CHEAT_TAC);;

(* [local] *)
let domain_EMPTY_lookup = prove
 (`domain t = EMPTY ==> (!x. sptree_lookup x t = NONE)`,
  CHEAT_TAC);;

let lookup_copy_shape = prove
 (`!t1 t2 n. sptree_lookup n (copy_shape t1 t2) = sptree_lookup n t1`,
  CHEAT_TAC);;

(* / TODO *)

(* BEGIN TODO: move to sptreeTheory *)

let lookup_zero = prove
 (`!n t x. (sptree_lookup n t = SOME x) ==> (~(sptree_size t = 0))`,
  CHEAT_TAC);;

let empty_sub = prove
 (`(\t. t = LN) (difference a b) /\ (subspt b a) ==> (domain a =
  domain b)`,
  CHEAT_TAC);;

let subspt_delete = prove
 (`!a b x. subspt a b ==> subspt (sptree_delete x a) b`,
  CHEAT_TAC);;

let inter_union_empty = prove
 (`!a b c.
   (\t. t = LN) (inter (sptree_union a b) c) <=> (\t. t = LN)
     (inter a c) /\ (\t. t = LN) (inter b c)`,
  CHEAT_TAC);;

let inter_insert_empty = prove
 (`!n t1 t2.
   (\t. t = LN) (inter (sptree_insert n one t1) t2) ==> ~(n IN
     domain t2) /\ (\t. t = LN) (inter t1 t2)`,
  CHEAT_TAC);;

let fromList2_value = prove
 (`!e l t n. MEM e l <=> (?n. sptree_lookup n (fromList2 l) = SOME e)`,
  CHEAT_TAC);;

(* The range is the set of values taken on by an sptree.
  Not sure if these are worth moving. *)
let range_def = new_definition
  `range s = {v | ?n. sptree_lookup n s = SOME v}`;;

let range_delete = prove
 (`range (sptree_delete h v) SUBSET range v`,
  CHEAT_TAC);;

let range_insert = prove
 (`~(n IN domain fml) ==>
     range (sptree_insert n l fml) = l INSERT range fml`,
  CHEAT_TAC);;

let range_insert_2 = prove
 (`C IN range (sptree_insert n l fml) ==> C IN range fml \/ C = l`,
  CHEAT_TAC);;

let range_insert_SUBSET = prove
 (`range (sptree_insert n l fml) SUBSET l INSERT range fml`,
  CHEAT_TAC);;

(* END TODO *)

let TWOxDIV2 = prove
 (`(
      2 * x) DIV 2 = x`,
  CHEAT_TAC);;

let alist_insert_REVERSE = prove
 (`!xs ys s.
   ALL_DISTINCT xs /\ LENGTH xs = LENGTH ys ==>
   alist_insert (REVERSE xs) (REVERSE ys) s = alist_insert xs ys s`,
  CHEAT_TAC);;

let alist_insert_ALL_DISTINCT = prove
 (`!xs ys t ls.
   ALL_DISTINCT xs /\
   LENGTH xs = LENGTH ys /\
   PERM (ZIP xs ys) ls ==>
   alist_insert xs ys t = alist_insert (MAP FST ls) (MAP SND ls) t`,
  CHEAT_TAC);;

let n2w_lt = prove
 (`((n2w 0):'a word) < n2w a /\ ((n2w 0):'a word) < n2w b /\
   a < dimword (:'a) /\ b < dimword (:'a) ==>
   ((n2w a:'a word) < (n2w b:'a word) <=> a < b)`,
  CHEAT_TAC);;

let n2w_le = prove
 (`((n2w 0):'a word) < n2w a /\ ((n2w 0):'a word) < n2w b /\
   a < dimword (:'a) /\ b < dimword (:'a) ==>
   ((n2w a:'a word) <= (n2w b:'a word) <=> a <= b)`,
  CHEAT_TAC);;

let word_lt_0w = prove
 (`2 * n < dimword (:'a) ==> (((n2w 0):'a word) < n2w n <=> 0 < n)`,
  CHEAT_TAC);;

let word_sub_lt = prove
 (`(n2w 0) < n /\ (n2w 0) < m /\ n <= m ==> m - n < m`,
  CHEAT_TAC);;

(* see #521 *)

let bytes_in_memory_def,bytes_in_memory_ind = define_rec
  [`bytes_in_memory a [] m dm <=> T`;
   `bytes_in_memory a (CONS (x:word8) xs) m dm <=>
         (m a = x) /\ a IN dm /\ bytes_in_memory (a + (n2w 1))
             xs m dm`];;

let bytes_in_memory_APPEND = prove
 (`!l1 l2 pc' mem' mem_domain'.
      bytes_in_memory pc' (APPEND l1 l2) mem' mem_domain' <=>
      bytes_in_memory pc' l1 mem' mem_domain' /\
      bytes_in_memory (pc' + n2w (LENGTH l1)) l2 mem' mem_domain'`,
  CHEAT_TAC);;

let bytes_in_memory_change_domain = prove
 (`!a bs m md1 md2.
    bytes_in_memory a bs m md1 /\
   (!n. n < LENGTH bs /\ a + n2w n IN md1 ==> a + n2w n IN md2) ==>
     bytes_in_memory a bs m md2`,
  CHEAT_TAC);;

let bytes_in_memory_change_mem = prove
 (`!a bs m1 m2 md.
    bytes_in_memory a bs m1 md /\
   (!n. n < LENGTH bs ==> (m1 (a + n2w n) = m2 (a + n2w n))) ==>
     bytes_in_memory a bs m2 md`,
  CHEAT_TAC);;

let bytes_in_memory_EL = prove
 (`!a bs m md k. bytes_in_memory a bs m md /\ k < LENGTH bs ==> (m (a
  + n2w k) = EL k bs)`,
  CHEAT_TAC);;

let bytes_in_memory_in_domain = prove
 (`!a bs m md k. bytes_in_memory a bs m md /\ k < LENGTH bs ==> ((a +
  n2w k) IN md)`,
  CHEAT_TAC);;

let bytes_in_mem_def,bytes_in_mem_ind = define_rec
  [`bytes_in_mem a [] m md k <=> T`;
   `bytes_in_mem a (CONS b bs) m md k <=>
         a IN md /\ ~(a IN k) /\ (m a = b) /\
         bytes_in_mem (a + (n2w 1)) bs m md k`];;

let bytes_in_mem_IMP = prove
 (`!xs p. bytes_in_mem p xs m dm dm1 ==> bytes_in_memory p xs m dm`,
  CHEAT_TAC);;

let fun2set_disjoint_union = prove
 (`DISJOINT d1 d2 /\
   p (fun2set (m,d1)) /\
   q (fun2set (m,d2)) ==> (p * q) (fun2set (m,d1 UNION d2))`,
  CHEAT_TAC);;

let WORD_LS_IMP = prove
 (`a <=+ b ==>
    (?k. Abbrev (b = a + n2w k) /\
        w2n (b - a) = k /\
        (!w. a <=+ w /\ w <+ b <=> (?i. w = a + n2w i /\ i < k)))`,
  CHEAT_TAC);;

let size_fromAList = prove
 (`// TODO: move to HOL
   !xs. ALL_DISTINCT (MAP FST xs) ==> sptree_size (fromAList xs) =
     LENGTH xs`,
  CHEAT_TAC);;

let ALL_DISTINCT_MAP_FST_toSortedAList = prove
 (`ALL_DISTINCT (MAP FST (toSortedAList t))`,
  CHEAT_TAC);;


let good_dimindex_def = new_definition
  `good_dimindex (:'a) <=> dimindex (:'a) = 32 \/ dimindex (:'a) = 64`;;

let good_dimindex_get_byte_set_byte = prove
 (`good_dimindex (:'a) ==>
     (get_byte a (set_byte (a:'a word) b w be) be = b)`,
  CHEAT_TAC);;

(* [local] *)
let byte_index_LESS_IMP = prove
 (`(dimindex (:'a) = 32 \/ dimindex (:'a) = 64) /\
     byte_index (a:'a word) be < byte_index (a':'a word) be /\ i < 8
       ==>
     byte_index a be + i < byte_index a' be /\
     byte_index a be <= i + byte_index a' be /\
     byte_index a be + 8 <= i + byte_index a' be /\
     i + byte_index a' be < byte_index a be + dimindex (:'a)`,
  CHEAT_TAC);;

(* [local] *)
let NOT_w2w_bit = prove
 (`8 <= i /\ i < dimindex (:'b) ==> ~(FAPPLY ((w2w:word8->'b word) w)
  i)`,
  CHEAT_TAC);;

(* HOL4 miscScript.sml:4351-4353: the ML values that the definitions
   below antiquote *)

(* [local] *)
let DIV_EQ_DIV_IMP = prove
 (`0 < d /\ ~(n = n') /\ (n DIV d * d = n' DIV d * d) ==> ~(n MOD d =
  n' MOD d)`,
  CHEAT_TAC);;

let get_byte_set_byte_diff = prove
 (`good_dimindex (:'a) /\ ~(a = a') /\ (byte_align a = byte_align a')
  ==>
    (get_byte a (set_byte (a':'a word) b w be) be = get_byte a w
      be)`,
  CHEAT_TAC);;

(* helpful theorems for _size *)
let list_size_pair_size_MAP_FST_SND = prove
 (`list_size (pair_size f g) ls =
   list_size f (MAP FST ls) +
   list_size g (MAP SND ls)`,
  CHEAT_TAC);;

(* MEM_list_size *)
let misc_MEM_list_size = prove
 (`MEM x ls ==>
   f x <= list_size f ls`,
  CHEAT_TAC);;

(* must be used instead of FUPDATE in defitions that go through translation *)
let fmap_update_def = new_definition
  `fmap_update f k v = f |+ (k,v)`;;
add_simp fmap_update_def;;

(* TODO: move to HOL? *)
let sum_cmp_def = new_definition
  `sum_cmp c1 c2 x1 x2 =
     (match x1 with INL n1 ->
         (match x2 with INL n2 -> c1 n1 n2 | INR _10 -> LESS) | INR
           n1 ->
         (match x2 with INL _11 -> GREATER | INR n2 -> c2 n1 n2))`;;

let TotOrd_sum = prove
 (`TotOrd c1 /\ TotOrd c2 ==>
   TotOrd (sum_cmp c1 c2)`,
  CHEAT_TAC);;

let TotOrd_num_cmp = prove
 (`TotOrd comparison_num_cmp`,
  CHEAT_TAC);;

(* the shape num_cmp shares with mlint$int_cmp *)
let num_cmp_thm = prove
 (`comparison_num_cmp n1 n2 =
     (if n1 < n2 then LESS else
     if n2 < n1 then GREATER else EQUAL)`,
  CHEAT_TAC);;

let TotOrd_pair_cmp = prove
 (`TotOrd c1 /\ TotOrd c2 ==>
   TotOrd (pair_compare c1 c2)`,
  CHEAT_TAC);;

(* and the names it reads as variables are constants again *)
let _ = do_list unhide_constant
  ["C";
   "num_cmp"];;

(* and the interface *)
let _ = unhide_overloads ();;
