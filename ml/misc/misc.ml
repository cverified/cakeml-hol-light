(* ======================================================== *)
(*  misc: ported from HOL4's
    misc/miscScript.sml
    A definition theory, with 50 definitions, 1 datatype and 393
    theorems.  Needed by 95 files of the port.  *)
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

(* Note: This globally hides constants over the reals that gets imported through machine_ieeeTheory *)

(* this is copied in preamble.sml, but needed here to avoid cyclic dep *)
(* HOL4 miscScript.sml:42-46: ML code, not ported *)
(* -- *)

(* TODO: move/categorize *)

(* theorem behind impl_tac *)
(* HOL4 miscScript.sml:54-55: a theorem that HOL4 states as the value
   of an ML expression *)

(* used elsewhere in cakeml *)
let SUBSET_IMP = cake_theorem "SUBSET_IMP"
  (fun () ->
    `s SUBSET t ==> (x IN s ==> x IN t)`)
  CHEAT_TAC;;

let DROP_NIL = cake_theorem "DROP_NIL"
  (fun () ->
    `!n xs. DROP n xs = [] <=> LENGTH xs <= n`)
  CHEAT_TAC;;

let revdroprev = cake_theorem "revdroprev"
  (fun () ->
    `!l n.
       n <= LENGTH l ==> (REVERSE (DROP n (REVERSE l)) = TAKE
         (LENGTH l - n) l)`)
  CHEAT_TAC;;

let revtakerev = cake_theorem "revtakerev"
  (fun () ->
    `!n l. n <= LENGTH l ==> REVERSE (TAKE n (REVERSE l)) = DROP
  (LENGTH l - n) l`)
  CHEAT_TAC;;

let times_add_o = cake_theorem "times_add_o"
  (fun () ->
    `(\(n:num). k * n + x) = ((+) x) o ((*) k)`)
  CHEAT_TAC;;

let SORTED_inv_image_LESS_PLUS =
  cake_theorem "SORTED_inv_image_LESS_PLUS"
  (fun () ->
    `SORTED (inv_image (<) (arithmetic (+) k)) = SORTED (<)`)
  CHEAT_TAC;;

let SORTED_GENLIST_TIMES = cake_theorem "SORTED_GENLIST_TIMES"
  (fun () ->
    `0 < k ==> (!n. SORTED prim_rec (<) (GENLIST ((*) k) n))`)
  CHEAT_TAC;;

(* this is
     read_bytearray a c gb = OPT_MMAP gb (GENLIST (λi. a + n2w i) c)
*)
let read_bytearray_def = cake_define_list
  [`read_bytearray a 0 get_byte' = SOME []`;
   `read_bytearray a (SUC n) get_byte' =
         (match get_byte' a with NONE -> NONE | SOME b ->
           (match read_bytearray (a + (n2w 1)) n get_byte' with
           NONE -> NONE | SOME bs -> SOME (b :: bs)))`];;

(* HOL to have OPT_MMAP f l1 = SOME l2 ==> (LENGTH l2 = LENGTH l1) *)
let read_bytearray_LENGTH = cake_theorem "read_bytearray_LENGTH"
  (fun () ->
    `!n a f x.
        (read_bytearray a n f = SOME x) ==> (LENGTH x = n)`)
  CHEAT_TAC;;

let shift_seq_def = cake_define
  `misc_shift_seq k s = (\i. s (i + (k:num)))`;;
hol4_overload "shift_seq" "misc_shift_seq";;

(* TODO: Used once in all of CakeML: could probably be pushed back to use-site*)
let SUM_SET_IN_LT = cake_theorem "SUM_SET_IN_LT"
  (fun () ->
    `!s x y. FINITE s /\ x IN s /\ y < x ==> y < SUM_SET s`)
  CHEAT_TAC;;

(* only used in proof of tlookup_bij_iff *)
let CARD_IMAGE_ID_BIJ = cake_theorem "CARD_IMAGE_ID_BIJ"
  (fun () ->
    `!s. FINITE s ==> (!x. x IN s ==> f x IN s) /\ CARD (IMAGE f s) =
  CARD s ==> BIJ f s s`)
  CHEAT_TAC;;

(* never used *)
let CARD_IMAGE_EQ_BIJ = cake_theorem "CARD_IMAGE_EQ_BIJ"
  (fun () ->
    `!s. FINITE s ==> CARD (IMAGE f s) = CARD s ==> BIJ f s (IMAGE f
  s)`)
  CHEAT_TAC;;

(* used only in clos_callProof -
   HOL has DISJOINT_IMAGE:
     |- (!x y. f x = f y <=> x = y) ==>
        (DISJOINT (IMAGE f x) (IMAGE f y) <=> DISJOINT x y
*)
let DISJOINT_IMAGE_SUC = cake_theorem "DISJOINT_IMAGE_SUC"
  (fun () ->
    `DISJOINT (IMAGE SUC' x) (IMAGE SUC' y) <=> DISJOINT x y`)
  CHEAT_TAC;;

(* disgusting and used only in clos_callProof *)
let IMAGE_SUC_SUBSET_UNION = cake_theorem "IMAGE_SUC_SUBSET_UNION"
  (fun () ->
    `IMAGE SUC x SUBSET IMAGE SUC y UNION IMAGE SUC z <=>
      x SUBSET y UNION z`)
  CHEAT_TAC;;

(* HOL4 miscScript.sml:182: the overload LLOOKUP, which the port
   expands *)

(* HOL4 miscScript.sml:184-185: a theorem that HOL4 states as the
   value of an ML expression *)
(* HOL4 miscScript.sml:186-187: a theorem that HOL4 states as the
   value of an ML expression *)
(* HOL4 miscScript.sml:188-189: a theorem that HOL4 states as the
   value of an ML expression *)
(* HOL4 miscScript.sml:190-191: a theorem that HOL4 states as the
   value of an ML expression *)
(* HOL4 miscScript.sml:192-193: a theorem that HOL4 states as the
   value of an ML expression *)
(* HOL4 miscScript.sml:194-195: a theorem that HOL4 states as the
   value of an ML expression *)

(* app_list stuff should be in an app_list theory *)
let app_list_INDUCT,app_list_RECURSION = define_datatype
  "app_list = misc_List ('a list) | misc_Append (app_list) (app_list) \
   | misc_Nil";;
hol4_overload "List" "misc_List";;
hol4_overload "Append" "misc_Append";;
hol4_overload "Nil" "misc_Nil";;

let append_aux_def = cake_define_list
  [`append_aux misc_Nil aux = aux`;
   `append_aux (misc_List xs) aux = xs ++ aux`;
   `append_aux (misc_Append l1 l2) aux = append_aux l1 (append_aux
  l2 aux)`];;

let append_def = cake_define
  `append l = append_aux l []`;;

let append_aux_thm = cake_theorem "append_aux_thm"
  (fun () ->
    `!l xs. append_aux l xs = append_aux l [] ++ xs`)
  CHEAT_TAC;;

let append_thm = cake_theorem "append_thm[simp]"
  (fun () ->
    `append (misc_Append l1 l2) = append l1 ++ append l2 /\
      append (misc_List xs) = xs /\
      append misc_Nil = []`)
  CHEAT_TAC;;

let SmartAppend_def = cake_define
  `SmartAppend l1 l2 =
        match (l1,l2) with
          (misc_Nil,l2) -> l2
        | (l1,misc_Nil) -> l1
        | (l1,l2) -> misc_Append l1 l2`;;

let SmartAppend_thm = cake_theorem "SmartAppend_thm"
  (fun () ->
    `!l1 l2.
      SmartAppend l1 l2 =
        (if l1 = misc_Nil then l2 else
        if l2 = misc_Nil then l1 else misc_Append l1 l2)`)
  CHEAT_TAC;;

let SmartAppend_Nil = cake_theorem "SmartAppend_Nil"
  (fun () ->
    `SmartAppend l misc_Nil = l /\
     SmartAppend misc_Nil l = l`)
  CHEAT_TAC;;

let append_SmartAppend = cake_theorem "append_SmartAppend[simp]"
  (fun () ->
    `append (SmartAppend l1 l2) = append l1 ++ append l2`)
  CHEAT_TAC;;

(* instant derivation from LIST_EQ_REWRITE *)
let GENLIST_eq_MAP = cake_theorem "GENLIST_eq_MAP"
  (fun () ->
    `GENLIST f n = MAP g ls <=>
     LENGTH ls = n /\ (!m. m < n ==> f m = g (EL m ls))`)
  CHEAT_TAC;;

(* TODO - already in HOL as ZIP_GENLIST *)
let ZIP_GENLIST1 = cake_theorem "ZIP_GENLIST1"
  (fun () ->
    `!l f n. LENGTH l = n ==> ZIP (GENLIST f n) l = GENLIST (\x. (f
  x,EL x l)) n`)
  CHEAT_TAC;;

(* used once *)
let MAP_REVERSE_STEP = cake_theorem "MAP_REVERSE_STEP"
  (fun () ->
    `!x f. ~(x = []) ==> MAP f (REVERSE x) = f (LAST x) :: MAP f
  (REVERSE (FRONT x))`)
  CHEAT_TAC;;

(* used three times, once with MIN_DEF alongside, which turns it into
   LENGTH_TAKE_EQ
*)
let LENGTH_TAKE_EQ_MIN = cake_theorem "LENGTH_TAKE_EQ_MIN"
  (fun () ->
    `!n xs. LENGTH (TAKE n xs) = MIN n (LENGTH xs)`)
  CHEAT_TAC;;

(* should be switched in orientation; looks like an attempt to get congruence
   rule *)
let LIST_REL_MEM = cake_theorem "LIST_REL_MEM"
  (fun () ->
    `!xs ys P. LIST_REL P xs ys <=>
                LIST_REL (\x y. MEM x xs /\ MEM y ys ==> P x y)
                  xs ys`)
  CHEAT_TAC;;

(* only used in theorem immediately below *)
let LIST_REL_GENLIST_I = cake_theorem "LIST_REL_GENLIST_I"
  (fun () ->
    `!xs. LIST_REL P (GENLIST I' (LENGTH xs)) xs =
           (!n. n < LENGTH xs ==> P n (EL n xs))`)
  CHEAT_TAC;;

(* only used in bvi_to_dataProof *)
let LIST_REL_lookup_fromList = cake_theorem "LIST_REL_lookup_fromList"
  (fun () ->
    `LIST_REL (\v x. sptree_lookup v (fromList args) = SOME x)
       (GENLIST I (LENGTH args)) args`)
  CHEAT_TAC;;

let LIST_REL_lookup_fromList_MAP =
  cake_theorem "LIST_REL_lookup_fromList_MAP"
  (fun () ->
    `LIST_REL (\v x. ?z. sptree_lookup v (fromList args) = SOME z /\ x =
  f z)
      (GENLIST I (LENGTH args)) (MAP f args)`)
  CHEAT_TAC;;

(* only used in examples/stackProg; oriented badly *)
let LIST_REL_FRONT_LAST = cake_theorem "LIST_REL_FRONT_LAST"
  (fun () ->
    `~(
        l1 = []) /\ ~(l2 = []) ==>
         (LIST_REL A l1 l2 <=>
          LIST_REL A (FRONT l1) (FRONT l2) /\ A (LAST l1) (LAST
            l2))`)
  CHEAT_TAC;;

let lemmas = cake_theorem "lemmas[local]"
  (fun () ->
    `((2 + 2 * n) - 1 = 2 * n + (1:num)) /\
       (2 + 2 * n' = 2 * n'' + 2 <=> n' = (n'':num)) /\
       (2 * m = 2 * n <=> (m = n)) /\
       ((2 * n'' + 1) DIV 2 = n'') /\
       ((2 * n) DIV 2 = n) /\
       (~(2 + 2 * n' = 2 * n'' + 1)) /\
       (~(2 * m + 1 = 2 * n' + 2))`)
  CHEAT_TAC;;

let lookup_any_def = cake_define
  `lookup_any x sp d =
     (match sptree_lookup x sp with NONE -> d | SOME m -> m)`;;

let fromList2_def = cake_define
  `fromList2 l = SND (FOLDL (\(i,t) a. (i + 2,sptree_insert i a t))
  (0,LN) l)`;;

let EVEN_fromList2_lemma = cake_theorem "EVEN_fromList2_lemma[local]"
  (fun () ->
    `!l n t.
         EVEN n /\ (!x. x IN domain t ==> EVEN x) ==>
         (!x. x IN domain (SND (FOLDL (\(i,t) a. (i +
           2,sptree_insert i a t)) (n,t) l)) ==> EVEN x)`)
  CHEAT_TAC;;

let EVEN_fromList2 = cake_theorem "EVEN_fromList2"
  (fun () ->
    `!l n. n IN domain (fromList2 l) ==> EVEN n`)
  CHEAT_TAC;;

let SUBMAP_mono_FUPDATE_LIST = cake_theorem "SUBMAP_mono_FUPDATE_LIST"
  (fun () ->
    `!ls f g.
     DRESTRICT f (COMPL (set_of_list (MAP FST ls))) SUBMAP
     DRESTRICT g (COMPL (set_of_list (MAP FST ls))) ==> f |++ ls
       SUBMAP g |++ ls`)
  CHEAT_TAC;;

let INJ_FAPPLY_FUPDATE = cake_theorem "INJ_FAPPLY_FUPDATE"
  (fun () ->
    `INJ ((FAPPLY) f) (FDOM f) (FRANGE f) /\
     s = k INSERT FDOM f /\ ~(v IN FRANGE f) /\
     t = v INSERT FRANGE f ==>
     INJ ((FAPPLY) (f |+ (k,v))) s t`)
  CHEAT_TAC;;

(* used in only one place: stack_to_labProof *)
let BIJ_FLOOKUP_MAP_KEYS = cake_theorem "BIJ_FLOOKUP_MAP_KEYS"
  (fun () ->
    `BIJ bij UNIV UNIV ==>
      FLOOKUP (MAP_KEYS (LINV bij UNIV) f) n = FLOOKUP f (bij n)`)
  CHEAT_TAC;;

let SPLIT_LIST = cake_theorem "SPLIT_LIST"
  (fun () ->
    `!xs.
        ?ys zs. (xs = ys ++ zs) /\
                (LENGTH xs DIV 2 = LENGTH ys)`)
  CHEAT_TAC;;

let EXISTS_ZIP = cake_theorem "EXISTS_ZIP"
  (fun () ->
    `!l f. EXISTS (\(x,y). f x) l = EXISTS f (MAP FST l)`)
  CHEAT_TAC;;

let EVERY_ZIP = cake_theorem "EVERY_ZIP"
  (fun () ->
    `!l f. EVERY (\(x,y). f x) l = EVERY f (MAP FST l)`)
  CHEAT_TAC;;

let every_zip_split = cake_theorem "every_zip_split"
  (fun () ->
    `!l1 l2 P Q.
      LENGTH l1 = LENGTH l2 ==>
      (EVERY (\(x,y). P x /\ Q y) (ZIP l1 l2) <=> EVERY P l1 /\
        EVERY Q l2)`)
  CHEAT_TAC;;

let every_shim = cake_theorem "every_shim"
  (fun () ->
    `!l P. EVERY (\(x,y). P y) l = EVERY P (MAP SND l)`)
  CHEAT_TAC;;

let every_shim2 = cake_theorem "every_shim2"
  (fun () ->
    `!l P Q. EVERY (\(x,y). P x /\ Q y) l = (EVERY (\x. P (FST x)) l
  /\ EVERY (\x. Q (SND x)) l)`)
  CHEAT_TAC;;

let MEM_ZIP2 = cake_theorem "MEM_ZIP2"
  (fun () ->
    `!l1 l2 x.
     MEM x (ZIP l1 l2) ==>
     (?n. n < LENGTH l1 /\ n < LENGTH l2 /\ x = (EL n l1,EL n
       l2))`)
  CHEAT_TAC;;

let ZIP_MAP_FST_SND_EQ = cake_theorem "ZIP_MAP_FST_SND_EQ"
  (fun () ->
    `!ls. ZIP (MAP FST' ls) (MAP SND' ls) = ls`)
  CHEAT_TAC;;

let MAP_FST_I_PAIR_MAP = cake_theorem "MAP_FST_I_PAIR_MAP[simp]"
  (fun () ->
    `!xs. MAP FST' (MAP (I' ## f) xs) = MAP FST' xs`)
  CHEAT_TAC;;

let EVERY_FST_SND = cake_theorem "EVERY_FST_SND"
  (fun () ->
    `EVERY (\(a,b). P a /\ Q b) ls <=> EVERY P (MAP FST ls) /\ EVERY Q
  (MAP SND ls)`)
  CHEAT_TAC;;

let zlookup_def = cake_define
  `zlookup m k = (match sptree_lookup k m with NONE -> 0 | SOME k ->
  k)`;;

let tlookup_def = cake_define
  `tlookup m k = (match sptree_lookup k m with NONE -> k | SOME k ->
  k)`;;

let tlookup_id = cake_theorem "tlookup_id"
  (fun () ->
    `~(
     x IN domain names) ==> tlookup names x = x`)
  CHEAT_TAC;;

let tlookup_bij_suff = cake_theorem "tlookup_bij_suff"
  (fun () ->
    `set_of_list (toList names) = domain names ==>
     BIJ (tlookup names) UNIV UNIV`)
  CHEAT_TAC;;

let tlookup_bij_iff = cake_theorem "tlookup_bij_iff"
  (fun () ->
    `BIJ (tlookup names) UNIV' UNIV' <=>
     set_of_list (toList names) = domain names`)
  CHEAT_TAC;;

(* should be composition of oEL and as-yet-undefined "THE default" *)
let any_el_def = cake_define_list
  [`any_el n [] d = d`;
   `any_el n (x :: xs) d = (if n = 0 then x else any_el (n -
  (1:num)) xs d)`];;

let update_resize_def = cake_define
  `update_resize ls default v n =
     (if n < LENGTH ls then
       LUPDATE v n ls else
       LUPDATE v n (ls ++ REPLICATE ((n * 2 + 1) - LENGTH ls)
         default))`;;

(*TODO upstream*)
let MAX_LIST_APPEND = cake_theorem "MAX_LIST_APPEND[simp]"
  (fun () ->
    `MAX_LIST (xs ++ ys) = MAX (MAX_LIST xs) (MAX_LIST ys)`)
  CHEAT_TAC;;

(*Or should it be MAX x (MAX_LIST xs)*)
let MAX_LIST_SNOC = cake_theorem "MAX_LIST_SNOC[simp]"
  (fun () ->
    `MAX_LIST (SNOC x xs) = MAX (MAX_LIST xs) x`)
  CHEAT_TAC;;

let MAX_LIST_intro = cake_theorem "MAX_LIST_intro"
  (fun () ->
    `!ls.
     P 0 /\ EVERY P ls ==> P (MAX_LIST ls)`)
  CHEAT_TAC;;

let MAX_LIST_max = cake_theorem "MAX_LIST_max"
  (fun () ->
    `!ls. EVERY (\x. x <= MAX_LIST ls) ls`)
  CHEAT_TAC;;

let FOLDR_MAX_0_MAX_LIST = cake_theorem "FOLDR_MAX_0_MAX_LIST"
  (fun () ->
    `!ls. ITLIST MAX' ls 0 = MAX_LIST ls`)
  CHEAT_TAC;;

(* never used *)
let list_inter_def = cake_define
  `list_inter xs ys = FILTER (\y. MEM y xs) ys`;;

let max3_def = cake_define
  `max3 (x:num) y z = (if x > y then (if z > x then z else x) else
  (if z > y then z else y))`;;

let ALOOKUP_SNOC = cake_theorem "ALOOKUP_SNOC"
  (fun () ->
    `!ls p k. ALOOKUP (SNOC p ls) k =
        (match ALOOKUP ls k with SOME v -> SOME v |
          NONE -> (if k = FST p then SOME (SND p) else NONE))`)
  CHEAT_TAC;;

let ALOOKUP_GENLIST = cake_theorem "ALOOKUP_GENLIST"
  (fun () ->
    `!f n k. ALOOKUP (GENLIST (\i. (i,f i)) n) k = (if k < n then SOME
  (f k) else NONE)`)
  CHEAT_TAC;;

let ALOOKUP_ZIP_FAIL = cake_theorem "ALOOKUP_ZIP_FAIL"
  (fun () ->
    `!A B x.
     LENGTH A = LENGTH B ==>
     (ALOOKUP (ZIP A B) x = NONE <=> ~MEM x A)`)
  CHEAT_TAC;;

let MEM_ALOOKUP = cake_theorem "MEM_ALOOKUP"
  (fun () ->
    `!xs x v.
        ALL_DISTINCT (MAP FST xs) ==>
        (MEM (x,v) xs <=> ALOOKUP xs x = SOME v)`)
  CHEAT_TAC;;

(* TODO - candidate for move to HOL, but in simpler form without accumulator *)
(* only used in inferProg *)
let anub_def = cake_define_list
  [`anub [] acc = []`;
   `anub ((k,v) :: ls) acc =
       (if MEM k acc then anub ls acc else
       (k,v) :: (anub ls (k :: acc)))`];;

(* HOL4 miscScript.sml:691: ML code, not ported *)

let EVERY_anub_imp = cake_theorem "EVERY_anub_imp"
  (fun () ->
    `!ls acc x y.
        EVERY P (anub ((x,y) :: ls) acc) /\ ~(x IN set_of_list acc)
          ==>
        P (x,y) /\ EVERY P (anub ls (x :: acc))`)
  CHEAT_TAC;;

(* terrible rewrite *)
let ALOOKUP_anub = cake_theorem "ALOOKUP_anub"
  (fun () ->
    `ALOOKUP (anub ls acc) k =
      (if MEM k acc then ALOOKUP (anub ls acc) k else ALOOKUP ls
        k)`)
  CHEAT_TAC;;

let anub_eq_nil = cake_theorem "anub_eq_nil"
  (fun () ->
    `anub x y = [] <=> EVERY (C MEM y) (MAP FST x)`)
  CHEAT_TAC;;

let EVERY_anub_suff = cake_theorem "EVERY_anub_suff"
  (fun () ->
    `!ls acc.
      (!x. ~MEM x acc ==> (match ALOOKUP ls x with SOME v -> P
        (x,v) | NONE -> T)) ==> EVERY P (anub ls acc)`)
  CHEAT_TAC;;

let anub_notin_acc = cake_theorem "anub_notin_acc"
  (fun () ->
    `!ls acc. MEM x acc ==> ~MEM x (MAP FST (anub ls acc))`)
  CHEAT_TAC;;

let anub_tl_anub = cake_theorem "anub_tl_anub"
  (fun () ->
    `!x y h t. anub x y = h :: t ==> (?a b. t = anub a b /\
  set_of_list a SUBSET set_of_list x /\ set_of_list b SUBSET
  set_of_list ((FST h) :: y))`)
  CHEAT_TAC;;

let anub_all_distinct_keys = cake_theorem "anub_all_distinct_keys"
  (fun () ->
    `!ls acc.
      ALL_DISTINCT acc ==>
      ALL_DISTINCT ((MAP FST (anub ls acc)) ++ acc)`)
  CHEAT_TAC;;

let MEM_anub_ALOOKUP = cake_theorem "MEM_anub_ALOOKUP"
  (fun () ->
    `MEM (k,v) (anub ls []) ==>
      ALOOKUP ls k = SOME v`)
  CHEAT_TAC;;

new_type_abbrev("misc_num_set",`: 1 spt`);;
(* HOL4 miscScript.sml:788: the type abbreviation num_map, which the
   port expands *)

let toAList_domain = cake_theorem "toAList_domain"
  (fun () ->
    `!x. MEM x (MAP FST' (toAList t)) <=> x IN domain t`)
  CHEAT_TAC;;

let domain_nat_set_from_list =
  cake_theorem "domain_nat_set_from_list[simp]"
  (fun () ->
    `!ls ns. domain (FOLDL (\s n. sptree_insert n one s) ns ls) =
  domain ns UNION set_of_list ls`)
  CHEAT_TAC;;

let wf_nat_set_from_list = cake_theorem "wf_nat_set_from_list"
  (fun () ->
    `!ls ns. sptree_wf ns ==> sptree_wf (FOLDL (\s n. sptree_insert n
  z s) ns ls)`)
  CHEAT_TAC;;

let BIT_11 = cake_theorem "BIT_11"
  (fun () ->
    `!n m. (BIT n = BIT m) <=> (n = m)`)
  CHEAT_TAC;;

let BIT_11_2 = cake_theorem "BIT_11_2"
  (fun () ->
    `!n m. (!z. (z < 2 EXP (MAX n m)) ==> (BIT n z <=> BIT m z)) <=>
  (n = m)`)
  CHEAT_TAC;;

(* only used below in proof of theorem that is in turn used just twice *)
let LOG2_TIMES2 = cake_theorem "LOG2_TIMES2"
  (fun () ->
    `0 < n ==> (LOG2 (2 * n) = SUC (LOG2 n))`)
  CHEAT_TAC;;

(* only used below in proof of theorem that is in turn used just twice *)
let LOG2_TIMES2_1 = cake_theorem "LOG2_TIMES2_1"
  (fun () ->
    `!n. 0 < n ==> (LOG2 (2 * n + 1) = LOG2 (2 * n))`)
  CHEAT_TAC;;

(* used only twice, both times in candle/set-theory *)
let C_BIT_11 = cake_theorem "C_BIT_11"
  (fun () ->
    `!n m. (!z. (z <= LOG2 (MAX n m)) ==> (BIT z n <=> BIT z m)) <=>
  (n = m)`)
  CHEAT_TAC;;

let BIT_num_from_bin_list_leading =
  cake_theorem "BIT_num_from_bin_list_leading"
  (fun () ->
    `!l x. EVERY ((>) 2) l /\ LENGTH l <= x ==> ~BIT x
  (num_from_bin_list l)`)
  CHEAT_TAC;;

let least_from_def = cake_define
  `least_from P n = (if (?x. P x /\ n <= x) then LEAST (\x. P x /\ n
  <= x) else LEAST P)`;;

let LEAST_thm = cake_theorem "LEAST_thm"
  (fun () ->
    `LEAST P = least_from P 0`)
  CHEAT_TAC;;

let least_from_thm = cake_theorem "least_from_thm"
  (fun () ->
    `least_from P n = (if P n then n else least_from P (n + 1))`)
  CHEAT_TAC;;

let FUNPOW_mono = cake_theorem "FUNPOW_mono"
  (fun () ->
    `(!x y. R1 x y ==> R2 x y) /\
      (!R1 R2. (!x y. R1 x y ==> R2 x y) ==> (!x y. f R1 x y ==> f
        R2 x y)) ==>
      (!n x y. FUNPOW f n R1 x y ==> FUNPOW f n R2 x y)`)
  CHEAT_TAC;;

let FUNPOW_SUC_PLUS = cake_theorem "FUNPOW_SUC_PLUS"
  (fun () ->
    `!n a. FUNPOW SUC' n = (+) n`)
  CHEAT_TAC;;

(* used just once; better as
     transitive R ==> transitive (OPTREL R)
   or that with transitive expanded out *)
let OPTREL_trans = cake_theorem "OPTREL_trans"
  (fun () ->
    `!R x y z.
      (!a b c. (x = SOME a) /\ (y = SOME b) /\ (z = SOME c) /\ R
        a b /\ R b c ==> R a c) /\ OPTREL R x y /\ OPTREL R y z ==>
        OPTREL R x z`)
  CHEAT_TAC;;

let UPDATE_LIST_def = cake_define
  `UPDATE_LIST = FOLDL (C (UNCURRY UPDATE))`;;

let UPDATE_LIST_THM = cake_theorem "UPDATE_LIST_THM"
  (fun () ->
    `!f. (UPDATE_LIST f [] = f) /\ (!h t. (UPDATE_LIST f (h :: t) =
  UPDATE_LIST ((FST h =+ SND h) f) t))`)
  CHEAT_TAC;;

let APPLY_UPDATE_LIST_ALOOKUP = cake_theorem "APPLY_UPDATE_LIST_ALOOKUP"
  (fun () ->
    `!ls f x. (UPDATE_LIST f ls) x = (match ALOOKUP (REVERSE ls) x
  with NONE -> f x | SOME y -> y)`)
  CHEAT_TAC;;

(* should be using indexedLists$findi, or INDEX_OF *)
let find_index_def = cake_define_list
  [`find_index _2 [] _3 = NONE`;
   `find_index y (x :: xs) n = (if x = y then SOME n else
  find_index y xs (n + 1))`];;

let INDEX_FIND_CONS_EQ_SOME = cake_theorem "INDEX_FIND_CONS_EQ_SOME"
  (fun () ->
    `(INDEX_FIND n f (x :: xs) = SOME y) <=>
      (f x /\ (y = (n,x))) \/
      (~f x /\ (INDEX_FIND (n + 1) f xs = SOME y))`)
  CHEAT_TAC;;

let find_index_INDEX_FIND = cake_theorem "find_index_INDEX_FIND"
  (fun () ->
    `!y xs n. find_index y xs n = OPTION_MAP FST (INDEX_FIND n ((=) y)
  xs)`)
  CHEAT_TAC;;

let find_index_INDEX_OF = cake_theorem "find_index_INDEX_OF"
  (fun () ->
    `find_index y xs 0 = INDEX_OF y xs`)
  CHEAT_TAC;;

let find_index_NOT_MEM = cake_theorem "find_index_NOT_MEM"
  (fun () ->
    `!ls x n. ~MEM x ls = (find_index x ls n = NONE)`)
  CHEAT_TAC;;

let find_index_MEM = cake_theorem "find_index_MEM"
  (fun () ->
    `!ls x n. MEM x ls ==> (?i. (find_index x ls n = SOME (n + i)) /\
  i < LENGTH ls /\ (EL i ls = x))`)
  CHEAT_TAC;;

let find_index_LEAST_EL = cake_theorem "find_index_LEAST_EL"
  (fun () ->
    `!ls x n. find_index x ls n = (if MEM x ls then SOME (n + (LEAST
  (\n. x = EL n ls))) else NONE)`)
  CHEAT_TAC;;

let find_index_LESS_LENGTH = cake_theorem "find_index_LESS_LENGTH"
  (fun () ->
    `!ls n m i. (find_index n ls m = SOME i) ==> (m <= i) /\ (i < m +
  LENGTH ls)`)
  CHEAT_TAC;;

let ALOOKUP_find_index_NONE = cake_theorem "ALOOKUP_find_index_NONE"
  (fun () ->
    `(ALOOKUP env k = NONE) ==> (find_index k (MAP FST env) m = NONE)`)
  CHEAT_TAC;;

(* HOL4 miscScript.sml:1138-1146: a proof *)

let ALOOKUP_find_index_SOME = cake_theorem "ALOOKUP_find_index_SOME"
  (fun () ->
    `(ALOOKUP env k = SOME v) ==>
      (?i. (find_index k (MAP FST env) 0 = SOME i) /\
          i < LENGTH env /\ (v = SND (EL i env)))`)
  CHEAT_TAC;;

let find_index_ALL_DISTINCT_EL =
  cake_theorem "find_index_ALL_DISTINCT_EL[simp]"
  (fun () ->
    `!ls n m. ALL_DISTINCT ls /\ n < LENGTH ls ==> (find_index (EL n
  ls) ls m = SOME (m + n))`)
  CHEAT_TAC;;

let find_index_ALL_DISTINCT_EL_eq =
  cake_theorem "find_index_ALL_DISTINCT_EL_eq"
  (fun () ->
    `!ls. ALL_DISTINCT ls ==> (!x m i. (find_index x ls m = SOME i) =
        (?j. (i = m + j) /\ j < LENGTH ls /\ (x = EL j ls)))`)
  CHEAT_TAC;;

let find_index_APPEND_same = cake_theorem "find_index_APPEND_same"
  (fun () ->
    `!l1 n m i l2. (find_index n l1 m = SOME i) ==> (find_index n (l1
  ++ l2) m = SOME i)`)
  CHEAT_TAC;;

let find_index_ALL_DISTINCT_REVERSE =
  cake_theorem "find_index_ALL_DISTINCT_REVERSE"
  (fun () ->
    `!ls x m j. ALL_DISTINCT ls /\ (find_index x ls m = SOME j) ==>
  (find_index x (REVERSE ls) m = SOME ((m + LENGTH ls + m) - j - 1))`)
  CHEAT_TAC;;

let THE_find_index_suff = cake_theorem "THE_find_index_suff"
  (fun () ->
    `!P x ls n. (!m. m < LENGTH ls ==> P (m + n)) /\ MEM x ls ==>
      P (THE (find_index x ls n))`)
  CHEAT_TAC;;

let find_index_APPEND1 = cake_theorem "find_index_APPEND1"
  (fun () ->
    `!l1 n l2 m i. (find_index n (l1 ++ l2) m = SOME i) /\ (i < m +
  LENGTH l1) ==> (find_index n l1 m = SOME i)`)
  CHEAT_TAC;;

let find_index_APPEND2 = cake_theorem "find_index_APPEND2"
  (fun () ->
    `!l1 n l2 m i. (find_index n (l1 ++ l2) m = SOME i) /\ (m + LENGTH
  l1 <= i) ==> (find_index n l2 (m + LENGTH l1) = SOME i)`)
  CHEAT_TAC;;

let find_index_is_MEM = cake_theorem "find_index_is_MEM"
  (fun () ->
    `!x ls n j. (find_index x ls n = SOME j) ==> MEM x ls`)
  CHEAT_TAC;;

let find_index_MAP_inj = cake_theorem "find_index_MAP_inj"
  (fun () ->
    `!ls x n f. (!y. MEM y ls ==> (f x = f y) ==> x = y) ==>
  (find_index (f x) (MAP f ls) n = find_index x ls n)`)
  CHEAT_TAC;;

let find_index_shift_0 = cake_theorem "find_index_shift_0"
  (fun () ->
    `!ls x k. find_index x ls k = OPTION_MAP (\x. x + k) (find_index x
  ls 0)`)
  CHEAT_TAC;;

let find_index_shift = cake_theorem "find_index_shift"
  (fun () ->
    `!ls x k j. (find_index x ls k = SOME j) ==> j >= k /\ (!n.
  find_index x ls n = SOME (j - k + n))`)
  CHEAT_TAC;;

let find_index_APPEND = cake_theorem "find_index_APPEND"
  (fun () ->
    `!l1 l2 x n. find_index x (l1 ++ l2) n =
      (match find_index x l1 n with NONE -> find_index x l2 (n +
        LENGTH l1) | SOME x -> SOME x)`)
  CHEAT_TAC;;

let find_index_in_FILTER_ZIP_EQ =
  cake_theorem "find_index_in_FILTER_ZIP_EQ"
  (fun () ->
    `!P l1 l2 x n1 n2 v1 j1 j2.
        (LENGTH l1 = LENGTH v1) /\
        (FILTER (P o FST) (ZIP l1 v1) = l2) /\
        (find_index x l1 n1 = SOME (n1 + j1)) /\
        (find_index x (MAP FST l2) n2 = SOME (n2 + j2)) /\
        P x ==>
        j1 < LENGTH l1 /\ j2 < LENGTH l2 /\
        (EL j1 (ZIP l1 v1) = EL j2 l2)`)
  CHEAT_TAC;;

let ALL_DISTINCT_PERM_ALOOKUP_ZIP =
  cake_theorem "ALL_DISTINCT_PERM_ALOOKUP_ZIP"
  (fun () ->
    `!l1 l2 l3.
      ALL_DISTINCT (MAP FST l1) /\ PERM (MAP FST l1) l2 ==>
        (set_of_list l1 = set_of_list (ZIP l2 (MAP (THE o ALOOKUP (l1
        ++ l3)) l2)))`)
  CHEAT_TAC;;

(* surely better with UNZIP rather than ZIP: i.e., UNZIP l1 = (a,b)...  *)
let PERM_ZIP = cake_theorem "PERM_ZIP"
  (fun () ->
    `!l1 l2. PERM l1 l2 ==> (!a b c d. (l1 = ZIP a b) /\ (l2 = ZIP c d)
  /\ (LENGTH a = LENGTH b) /\ (LENGTH c = LENGTH d) ==>
      PERM a c /\ PERM b d)`)
  CHEAT_TAC;;

(* never used *)
let RTC_invariant = cake_theorem "RTC_invariant"
  (fun () ->
    `!R P. (!x y. P x /\ R x y ==> P y) ==> (!x y. RTC R x y ==> P x
  ==> RTC (R RINTER (\x y. P x /\ P y)) x y)`)
  CHEAT_TAC;;

(* never used *)
let RTC_RSUBSET = cake_theorem "RTC_RSUBSET"
  (fun () ->
    `!R1 R2. R1 RSUBSET R2 ==> (RTC R1) RSUBSET (RTC R2)`)
  CHEAT_TAC;;

let PERM_PART = cake_theorem "PERM_PART"
  (fun () ->
    `!P L l1 l2 p q. ((p,q) = PART P L l1 l2) ==> PERM (L ++ (l1 ++
  l2)) (p ++ q)`)
  CHEAT_TAC;;

let PERM_PARTITION = cake_theorem "PERM_PARTITION"
  (fun () ->
    `!P L A B. ((A,B) = PARTITION P L) ==> PERM L (A ++ B)`)
  CHEAT_TAC;;

let option_case_NONE_F = cake_theorem "option_case_NONE_F"
  (fun () ->
    `(match X with NONE -> F | SOME x -> P x) = (?x. (X = SOME x) /\ P
  x)`)
  CHEAT_TAC;;

let IS_PREFIX_THM = cake_theorem "IS_PREFIX_THM"
  (fun () ->
    `!l2 l1. IS_PREFIX l1 l2 <=> (LENGTH l2 <= LENGTH l1) /\ (!n. n <
  LENGTH l2 ==> (EL n l2 = EL n l1))`)
  CHEAT_TAC;;

let EVERY2_RC_same = cake_theorem "EVERY2_RC_same[simp]"
  (fun () ->
    `EVERY2 (RC R) l l`)
  CHEAT_TAC;;

(* used twice, and only in source_to_flatProof *)
let FOLDL_invariant = cake_theorem "FOLDL_invariant"
  (fun () ->
    `!P f ls a. (P a) /\ (!x y. MEM y ls /\ P x ==> P (f x y)) ==> P
  (FOLDL f a ls)`)
  CHEAT_TAC;;

(* never used *)
let FOLDL_invariant_rest = cake_theorem "FOLDL_invariant_rest"
  (fun () ->
    `!P f ls a. P ls a /\ (!x n. n < LENGTH ls /\ P (DROP n ls) x ==>
  P (DROP (SUC n) ls) (f x (EL n ls))) ==> P [] (FOLDL f a ls)`)
  CHEAT_TAC;;

let between_def = cake_define
  `between x y z <=> (x:num) <= z /\ z < y`;;

let IN_between = cake_theorem "IN_between"
  (fun () ->
    `x IN between y z <=> y <= x /\ x < z`)
  CHEAT_TAC;;

(* never used *)
let SUC_LEAST = cake_theorem "SUC_LEAST"
  (fun () ->
    `!x. P x ==> (SUC (LEAST P) = LEAST (\x. 0 < x /\ P (PRE x)))`)
  CHEAT_TAC;;

(* never used *)
let fmap_linv_def = cake_define
  `fmap_linv f1 f2 <=> (FDOM f2 = FRANGE f1) /\ (!x. x IN FDOM f1 ==>
  (FLOOKUP f2 (FAPPLY f1 x) = SOME x))`;;

(* never used *)
let fmap_linv_unique = cake_theorem "fmap_linv_unique"
  (fun () ->
    `!f f1 f2. fmap_linv f f1 /\ fmap_linv f f2 ==> (f1 = f2)`)
  CHEAT_TAC;;

(* never used *)
let INJ_has_fmap_linv = cake_theorem "INJ_has_fmap_linv"
  (fun () ->
    `INJ (FAPPLY f) (FDOM f) (FRANGE f) ==> (?g. fmap_linv f g)`)
  CHEAT_TAC;;

(* never used *)
let has_fmap_linv_inj = cake_theorem "has_fmap_linv_inj"
  (fun () ->
    `(?g. fmap_linv f g) = (INJ (FAPPLY f) (FDOM f) (FRANGE f))`)
  CHEAT_TAC;;

(* never used *)
let fmap_linv_FAPPLY = cake_theorem "fmap_linv_FAPPLY"
  (fun () ->
    `fmap_linv f g /\ x IN FDOM f ==> (FAPPLY g (FAPPLY f x) = x)`)
  CHEAT_TAC;;

(* TODO - candidate for move to HOL *)
let plus_compose = cake_theorem "plus_compose"
  (fun () ->
    `!(n:num) m. (+) n o (+) m = (+) (n + m)`)
  CHEAT_TAC;;

(* TODO: move elsewhere? export as rewrite? *)
(* never used *)
let IN_option_rwt = cake_theorem "IN_option_rwt"
  (fun () ->
    `(x IN (match opt with NONE -> {} | SOME y -> Q y)) <=>
      (?y. (opt = SOME y) /\ x IN Q y)`)
  CHEAT_TAC;;

(* never used *)
let IN_option_rwt2 = cake_theorem "IN_option_rwt2"
  (fun () ->
    `x IN option_CASE opt {} s <=> (?y. (opt = SOME y) /\ x IN s y)`)
  CHEAT_TAC;;

(* Re-expressing folds *)

(* only used in flat_elimProof *)
let FOLDR_CONS_triple = cake_theorem "FOLDR_CONS_triple"
  (fun () ->
    `!f ls a. ITLIST (\(x,y,z) w. f x y z :: w) ls a = (MAP (\(x,y,z).
  f x y z) ls) ++ a`)
  CHEAT_TAC;;

(* never used *)
let FOLDR_CONS_5tup = cake_theorem "FOLDR_CONS_5tup"
  (fun () ->
    `!f ls a. ITLIST (\(c,d,x,y,z) w. f c d x y z :: w) ls a = (MAP
  (\(c,d,x,y,z). f c d x y z) ls) ++ a`)
  CHEAT_TAC;;

(* never used *)
let FOLDR_transitive_property = cake_theorem "FOLDR_transitive_property"
  (fun () ->
    `!P ls f a. P [] a /\ (!n a. n < LENGTH ls /\ P (DROP (SUC n) ls)
  a ==> P (DROP n ls) (f (EL n ls) a)) ==> P ls (ITLIST f ls a)`)
  CHEAT_TAC;;

(* Re-expressing curried lambdas *)

let FST_triple = cake_theorem "FST_triple"
  (fun () ->
    `(\(n,ns,b). n) = FST`)
  CHEAT_TAC;;

(* never used *)
let FST_5tup = cake_theorem "FST_5tup"
  (fun () ->
    `(\(n,ns,b,x,y). n) = FST`)
  CHEAT_TAC;;

(* never used *)
let SND_triple = cake_theorem "SND_triple"
  (fun () ->
    `(\(n,ns,b). f ns b) = UNCURRY f o SND`)
  CHEAT_TAC;;

let FST_pair = cake_theorem "FST_pair"
  (fun () ->
    `(\(n,v). n) = FST`)
  CHEAT_TAC;;

(* never used *)
let SND_pair = cake_theorem "SND_pair"
  (fun () ->
    `(\(n,v). v) = SND`)
  CHEAT_TAC;;

(* never used *)
let SND_FST_pair = cake_theorem "SND_FST_pair"
  (fun () ->
    `(\((n,m),c). m) = SND o FST`)
  CHEAT_TAC;;

(* never used *)
let MAP_ZIP_SND_triple = cake_theorem "MAP_ZIP_SND_triple"
  (fun () ->
    `(LENGTH l1 = LENGTH l2) ==> (MAP (\(x,y,z). f y z) (ZIP l1 l2) =
  MAP (UNCURRY f) l2)`)
  CHEAT_TAC;;

(* Specialisations to identity function *)

let I_PERMUTES = cake_theorem "I_PERMUTES[simp]"
  (fun () ->
    `I PERMUTES s`)
  CHEAT_TAC;;

(* never used *)
let INJ_I = cake_theorem "INJ_I"
  (fun () ->
    `!s t. INJ I' s t <=> s SUBSET t`)
  CHEAT_TAC;;


let MAP_EQ_ID = cake_theorem "MAP_EQ_ID"
  (fun () ->
    `!f ls. (MAP f ls = ls) = (!x. MEM x ls ==> (f x = x))`)
  CHEAT_TAC;;

(* Specialisations to FEMPTY *)

let FUN_FMAP_FAPPLY_FEMPTY_FAPPLY =
  cake_theorem "FUN_FMAP_FAPPLY_FEMPTY_FAPPLY[simp]"
  (fun () ->
    `FINITE s ==> (FAPPLY (FUN_FMAP (FAPPLY FEMPTY) s) x = FAPPLY
  FEMPTY x)`)
  CHEAT_TAC;;

(* FUPDATE_LIST stuff *)

let NOT_MEM_FLOOKUP_ZIP = cake_theorem "NOT_MEM_FLOOKUP_ZIP"
  (fun () ->
    `!ys xs zs. ~MEM n ys ==> FLOOKUP (xs |++ ZIP ys zs) n = FLOOKUP
  xs n`)
  CHEAT_TAC;;

(* Misc. *)

let LESS_1 = cake_theorem "LESS_1[simp]"
  (fun () ->
    `x < 1 <=> (x = (0:num))`)
  CHEAT_TAC;;


  (* --------- SO additions --------- *)

let map_fst = cake_theorem "map_fst"
  (fun () ->
    `!l f. MAP FST' (MAP (\(x,y). (x,f y)) l) = MAP FST' l`)
  CHEAT_TAC;;

(* use INJ_MAP_EQ_IFF and INJ_DEF *)
let map_some_eq = cake_theorem "map_some_eq"
  (fun () ->
    `!l1 l2. (MAP SOME l1 = MAP SOME l2) <=> (l1 = l2)`)
  CHEAT_TAC;;

(* never used *)
let map_some_eq_append = cake_theorem "map_some_eq_append"
  (fun () ->
    `!l1 l2 l3. (MAP SOME l1 ++ MAP SOME l2 = MAP SOME l3) <=> (l1 ++
  l2 = l3)`)
  CHEAT_TAC;;

(* HOL4 miscScript.sml:1766: ML code, not ported *)


(* list misc *)

let LASTN_LEMMA = cake_theorem "LASTN_LEMMA"
  (fun () ->
    `(LASTN (LENGTH xs + 1 + 1) (x :: y :: xs) = x :: y :: xs) /\
      (LASTN (LENGTH xs + 1) (x :: xs) = x :: xs)`)
  CHEAT_TAC;;

(* HOL4 miscScript.sml:1779-1782: a theorem that HOL4 states as the
   value of an ML expression *)

let LASTN_LENGTH_LESS_EQ = cake_theorem "LASTN_LENGTH_LESS_EQ"
  (fun () ->
    `!xs n. LENGTH xs <= n ==> LASTN n xs = xs`)
  CHEAT_TAC;;

let LASTN_ALT = cake_theorem "LASTN_ALT"
  (fun () ->
    `(LASTN n [] = []) /\
      (LASTN n (x :: xs) = (if LENGTH (x :: xs) <= n then x :: xs
        else LASTN n xs))`)
  CHEAT_TAC;;

let LENGTH_LASTN_LESS = cake_theorem "LENGTH_LASTN_LESS"
  (fun () ->
    `!xs n. LENGTH (LASTN n xs) <= LENGTH xs`)
  CHEAT_TAC;;

let MAP_EQ_MAP_IMP = cake_theorem "MAP_EQ_MAP_IMP"
  (fun () ->
    `!xs ys f.
        (!x y. MEM x xs /\ MEM y ys /\ (f x = f y) ==> (x = y)) ==>
        (MAP f xs = MAP f ys) ==> (xs = ys)`)
  CHEAT_TAC;;
(* HOL4 miscScript.sml:1817-1821: code that the source has in a
   comment *)

let INJ_MAP_EQ_2 = cake_theorem "INJ_MAP_EQ_2"
  (fun () ->
    `!f l1 l2.
     (!x y. x IN set_of_list l1 /\ y IN set_of_list l2 /\ f x = f y
       ==> x = y) /\
     MAP f l1 = MAP f l2 ==>
     l1 = l2`)
  CHEAT_TAC;;

let LENGTH_EQ_FILTER_FILTER = cake_theorem "LENGTH_EQ_FILTER_FILTER"
  (fun () ->
    `!xs. EVERY (\x. (P x \/ Q x) /\ ~(P x /\ Q x)) xs ==>
           (LENGTH xs = LENGTH (FILTER P xs) + LENGTH (FILTER Q
             xs))`)
  CHEAT_TAC;;

let LIST_REL_MAP_FILTER_NEQ = cake_theorem "LIST_REL_MAP_FILTER_NEQ"
  (fun () ->
    `!P f1 f2 z1 z2 l1 l2.
        LIST_REL P (MAP f1 l1) (MAP f2 l2) /\
        (!y1 y2. MEM (y1,y2) (ZIP l1 l2) ==> (~(SND y1 = z1) <=>
          ~(SND y2 = z2)) /\ (P (f1 y1) (f2 y2))) ==>
        LIST_REL P (MAP f1 (FILTER (\(x,y). ~(y = z1)) l1)) (MAP
          f2 (FILTER (\(x,y). ~(y = z2)) l2))`)
  CHEAT_TAC;;

(* move into HOL? *)

let word_list_def = cake_define_list
  [`misc_word_list a [] = emp`;
   `misc_word_list a (x :: xs) = set_sep_one (a,x) * misc_word_list
  (a + bytes_in_word) xs`];;
hol4_overload "word_list" "misc_word_list";;

let word_list_exists_def = cake_define
  `word_list_exists a n =
     SEP_EXISTS (\xs. misc_word_list a xs * cond (LENGTH xs = n))`;;

(* lookup_vars vs env = OPT_MMAP (\i. oEL i env) vs *)
let lookup_vars_def = cake_define_list
  [`lookup_vars [] env = SOME []`;
   `lookup_vars (v :: vs) env =
         (if v < LENGTH env then
           match lookup_vars vs env with SOME xs -> SOME (EL v
             env :: xs) | NONE -> NONE else NONE)`];;

let EVERY_lookup_vars = cake_theorem "EVERY_lookup_vars"
  (fun () ->
    `!vs env env'. EVERY P env /\ lookup_vars vs env = SOME env' ==>
  EVERY P env'`)
  CHEAT_TAC;;

let EVERY_LAST = cake_theorem "EVERY_LAST"
  (fun () ->
    `!P l. ~(l = []) /\ EVERY P l ==> P (LAST l)`)
  CHEAT_TAC;;

(* TODO - candidate for move to HOL *)
let num_to_hex_string_length_1 =
  cake_theorem "num_to_hex_string_length_1"
  (fun () ->
    `!x. x < 16 ==> (LENGTH (num_to_hex_string x) = 1)`)
  CHEAT_TAC;;

(* TODO - candidate for move to HOL *)
let num_to_hex_string_length_2 =
  cake_theorem "num_to_hex_string_length_2"
  (fun () ->
    `!x. 16 <= x /\ x < 256 ==> (LENGTH (num_to_hex_string x) = 2)`)
  CHEAT_TAC;;

let num_from_hex_string_length_2 =
  cake_theorem "num_from_hex_string_length_2"
  (fun () ->
    `num_from_hex_string [d1; d2] < 256`)
  CHEAT_TAC;;

let num_from_hex_string_leading_0 =
  cake_theorem "num_from_hex_string_leading_0"
  (fun () ->
    `!ls. ~(ls = []) ==> (num_from_hex_string ((CHR 48) :: ls) =
  num_from_hex_string ls)`)
  CHEAT_TAC;;

let num_from_hex_string_length_2_less_16 =
  cake_theorem "num_from_hex_string_length_2_less_16"
  (fun () ->
    `!h1 h2. isHexDigit h1 ==> num_from_hex_string [h1; h2] < 16 ==>
  h1 = (CHR 48)`)
  CHEAT_TAC;;

let num_from_hex_string_num_to_hex_string =
  cake_theorem "num_from_hex_string_num_to_hex_string[simp]"
  (fun () ->
    `num_from_hex_string (num_to_hex_string n) = n`)
  CHEAT_TAC;;

let MAPi_ID = cake_theorem "MAPi_ID[simp]"
  (fun () ->
    `MAPi (\x y. y) = I`)
  CHEAT_TAC;;

(* TODO - candidate for move to HOL - though
     enumerate i0 l = MAPi (λx i. (i + i0, x)) l
*)
let enumerate_def = cake_define_list
  [`enumerate n [] = []`;
   `enumerate n (x :: xs) = (n,x) :: enumerate (n + 1) xs`];;

(* TODO - candidate for move to HOL *)
let LENGTH_enumerate = cake_theorem "LENGTH_enumerate"
  (fun () ->
    `!xs k. LENGTH (enumerate k xs) = LENGTH xs`)
  CHEAT_TAC;;

let EL_enumerate = cake_theorem "EL_enumerate"
  (fun () ->
    `!xs n k.
     n < LENGTH xs ==>
     EL n (enumerate k xs) = (n + k,EL n xs)`)
  CHEAT_TAC;;

let MAP_enumerate_MAPi = cake_theorem "MAP_enumerate_MAPi"
  (fun () ->
    `!f xs.
     MAP f (enumerate 0 xs) = MAPi (\n e. f (n,e)) xs`)
  CHEAT_TAC;;

let MAPi_enumerate_MAP = cake_theorem "MAPi_enumerate_MAP"
  (fun () ->
    `!f xs.
     MAPi f xs = MAP (\(i,e). f i e) (enumerate 0 xs)`)
  CHEAT_TAC;;

let MEM_enumerate = cake_theorem "MEM_enumerate"
  (fun () ->
    `!xs i e.
     i < LENGTH xs ==>
     (MEM (i,e) (enumerate 0 xs) <=> EL i xs = e)`)
  CHEAT_TAC;;

let MEM_enumerate_IMP = cake_theorem "MEM_enumerate_IMP"
  (fun () ->
    `!ls k.
     MEM (i,e) (enumerate k ls) ==> MEM e ls`)
  CHEAT_TAC;;

let MAP_FST_enumerate = cake_theorem "MAP_FST_enumerate"
  (fun () ->
    `MAP FST' (enumerate k ls) = GENLIST ((+) k) (LENGTH ls)`)
  CHEAT_TAC;;

let ALL_DISTINCT_MAP_FST_enumerate =
  cake_theorem "ALL_DISTINCT_MAP_FST_enumerate"
  (fun () ->
    `ALL_DISTINCT (MAP FST (enumerate k ls))`)
  CHEAT_TAC;;

let ALOOKUP_enumerate = cake_theorem "ALOOKUP_enumerate"
  (fun () ->
    `!ls k x.
     ALOOKUP (enumerate k ls) x =
     (if k <= x /\ x < LENGTH ls + k then SOME (EL (x - k) ls)
       else NONE)`)
  CHEAT_TAC;;

let SUM_MAP_LENGTH_REPLICATE = cake_theorem "SUM_MAP_LENGTH_REPLICATE"
  (fun () ->
    `!n ls. SUM (MAP LENGTH' (REPLICATE n ls)) = n * LENGTH' ls`)
  CHEAT_TAC;;

let SUM_MAP_COUNT_LIST = cake_theorem "SUM_MAP_COUNT_LIST"
  (fun () ->
    `!n k. SUM (MAP ((+) k) (COUNT_LIST n)) = (n * ((2 * k + n) - 1))
  DIV 2`)
  CHEAT_TAC;;

let SUM_REPLICATE = cake_theorem "SUM_REPLICATE"
  (fun () ->
    `!n m. SUM (REPLICATE n m) = n * m`)
  CHEAT_TAC;;

let SUM_MAP_BOUND = cake_theorem "SUM_MAP_BOUND"
  (fun () ->
    `(!x. f x <= c) ==> (SUM (MAP f ls) <= LENGTH ls * c)`)
  CHEAT_TAC;;

let SUM_MOD = cake_theorem "SUM_MOD"
  (fun () ->
    `k > 0 ==>
     (SUM ls MOD k = (SUM (MAP (\n. n MOD k) ls)) MOD k)`)
  CHEAT_TAC;;

let MOD_SUB_LEMMA = cake_theorem "MOD_SUB_LEMMA"
  (fun () ->
    `n MOD k = 0 /\ m MOD k = 0 /\ 0 < k ==> (n - m) MOD k = 0`)
  CHEAT_TAC;;

let FLAT_REPLICATE_NIL = cake_theorem "FLAT_REPLICATE_NIL"
  (fun () ->
    `!n. FLAT (REPLICATE n []) = []`)
  CHEAT_TAC;;

let MEM_REPLICATE_EQ = cake_theorem "MEM_REPLICATE_EQ"
  (fun () ->
    `!n x y. MEM x (REPLICATE n y) <=> x = y /\ ~(n = 0)`)
  CHEAT_TAC;;

(* n.b. used in hol-reflection *)

let FDOM_FLOOKUP = cake_theorem "FDOM_FLOOKUP"
  (fun () ->
    `x IN FDOM f <=> (?v. FLOOKUP f x = SOME v)`)
  CHEAT_TAC;;

let FLAT_MAP_SING = cake_theorem "FLAT_MAP_SING"
  (fun () ->
    `!ls. FLAT (MAP (\x. [f x]) ls) = MAP f ls`)
  CHEAT_TAC;;

let FLAT_MAP_NIL = cake_theorem "FLAT_MAP_NIL"
  (fun () ->
    `FLAT (MAP (\x. []) ls) = []`)
  CHEAT_TAC;;

let UPDATE_LIST_NOT_MEM = cake_theorem "UPDATE_LIST_NOT_MEM"
  (fun () ->
    `!ls f x. ~MEM x (MAP FST ls) ==> (UPDATE_LIST f ls) x = f x`)
  CHEAT_TAC;;

let MAP_ZIP_UPDATE_LIST_ALL_DISTINCT_same =
  cake_theorem "MAP_ZIP_UPDATE_LIST_ALL_DISTINCT_same"
  (fun () ->
    `!ks vs f. LENGTH ks = LENGTH vs /\ ALL_DISTINCT ks ==> (MAP
  (UPDATE_LIST f (ZIP ks vs)) ks = vs)`)
  CHEAT_TAC;;

let flookup_update_list_none = cake_theorem "flookup_update_list_none"
  (fun () ->
    `!x m l.
      (FLOOKUP (m |++ l) x = NONE) =
      ((FLOOKUP m x = NONE) /\ (ALOOKUP l x = NONE))`)
  CHEAT_TAC;;

let flookup_update_list_some = cake_theorem "flookup_update_list_some"
  (fun () ->
    `!x m l y.
      (FLOOKUP (m |++ l) x = SOME y) =
      ((ALOOKUP (REVERSE l) x = SOME y) \/
       ((ALOOKUP l x = NONE) /\ (FLOOKUP m x = SOME y)))`)
  CHEAT_TAC;;

let MULT_LE_EXP = cake_theorem "MULT_LE_EXP"
  (fun () ->
    `!(a:num) b. ~(a = 1) ==> a * b <= a EXP b`)
  CHEAT_TAC;;

let domain_rrestrict_subset = cake_theorem "domain_rrestrict_subset"
  (fun () ->
    `domain (rrestrict r s) SUBSET domain r INTER s`)
  CHEAT_TAC;;

let range_rrestrict_subset = cake_theorem "range_rrestrict_subset"
  (fun () ->
    `range (rrestrict r s) SUBSET range r INTER s`)
  CHEAT_TAC;;

let PERM_MAP_BIJ = cake_theorem "PERM_MAP_BIJ"
  (fun () ->
    `!f l1 l2.
      BIJ f UNIV UNIV ==>
      (PERM l1 l2 <=> PERM (MAP f l1) (MAP f l2))`)
  CHEAT_TAC;;

let lookup_fromList2 = cake_theorem "lookup_fromList2"
  (fun () ->
    `!l n. sptree_lookup n (fromList2 l) =
            (if EVEN n then sptree_lookup (n DIV 2) (fromList l)
              else NONE)`)
  CHEAT_TAC;;

let domain_fromList2 = cake_theorem "domain_fromList2"
  (fun () ->
    `!q. domain (fromList2 q) = set_of_list (GENLIST (\x. 2 * x)
  (LENGTH q))`)
  CHEAT_TAC;;

let UNCURRY_eq_pair = cake_theorem "UNCURRY_eq_pair"
  (fun () ->
    `UNCURRY f v = z <=> (?a b. v = (a,b) /\ f a b = z)`)
  CHEAT_TAC;;

let OLEAST_SOME_IMP = cake_theorem "OLEAST_SOME_IMP"
  (fun () ->
    `OLEAST P = SOME i ==> P i /\ (!n. n < i ==> ~P n)`)
  CHEAT_TAC;;

let EXP2_EVEN = cake_theorem "EXP2_EVEN"
  (fun () ->
    `!n. EVEN (2 EXP n) <=> ~(n = 0)`)
  CHEAT_TAC;;

let FST_UNZIP_MAPi = cake_theorem "FST_UNZIP_MAPi"
  (fun () ->
    `!l f. FST (UNZIP (MAPi f l)) = MAPi ((o) ((o) FST) f) l`)
  CHEAT_TAC;;

let SND_UNZIP_MAPi = cake_theorem "SND_UNZIP_MAPi"
  (fun () ->
    `!l f. SND (UNZIP (MAPi f l)) = MAPi ((o) ((o) SND) f) l`)
  CHEAT_TAC;;

let ALL_DISTINCT_FLAT = cake_theorem "ALL_DISTINCT_FLAT"
  (fun () ->
    `!l. ALL_DISTINCT (FLAT l) <=>
          (!l0. MEM l0 l ==> ALL_DISTINCT l0) /\
          (!i j. i < j /\ j < LENGTH l ==>
                 (!e. MEM e (EL i l) ==> ~MEM e (EL j l)))`)
  CHEAT_TAC;;

let ALL_DISTINCT_FLAT_EVERY = cake_theorem "ALL_DISTINCT_FLAT_EVERY"
  (fun () ->
    `!ls. ALL_DISTINCT (FLAT ls) ==> EVERY ALL_DISTINCT ls`)
  CHEAT_TAC;;

let ALL_DISTINCT_APPEND_APPEND_IMP =
  cake_theorem "ALL_DISTINCT_APPEND_APPEND_IMP"
  (fun () ->
    `ALL_DISTINCT (xs ++ ys ++ zs) ==>
      ALL_DISTINCT (xs ++ ys) /\ ALL_DISTINCT (xs ++ zs) /\
        ALL_DISTINCT (ys ++ zs)`)
  CHEAT_TAC;;

let GSPEC_o = cake_theorem "GSPEC_o"
  (fun () ->
    `GSPEC f o g = {x | ?y. (g x,T) = f y}`)
  CHEAT_TAC;;


(* TODO - candidate for move to HOL *)
let o_PAIR_MAP = cake_theorem "o_PAIR_MAP"
  (fun () ->
    `FST o (f ## g) = f o FST /\
     SND o (f ## g) = g o SND`)
  CHEAT_TAC;;

let any_el_ALT = cake_theorem "any_el_ALT"
  (fun () ->
    `!l n d. any_el n l d = (if n < LENGTH l then EL n l else d)`)
  CHEAT_TAC;;

let MOD_MINUS = cake_theorem "MOD_MINUS"
  (fun () ->
    `0 < p /\ 0 < k ==> (p * k - n MOD (p * k)) MOD k = (k - n MOD k)
  MOD k`)
  CHEAT_TAC;;

let option_fold_def = cake_define_list
  [`option_fold f x NONE = x`;
   `option_fold f x (SOME y) = f y x`];;

let SPLITP_CONS_IMP = cake_theorem "SPLITP_CONS_IMP"
  (fun () ->
    `!ls l' r. (SPLITP P ls = (l',r)) /\ (~(r = [])) ==> (EXISTS P ls)`)
  CHEAT_TAC;;


let LAST_CONS_alt = cake_theorem "LAST_CONS_alt"
  (fun () ->
    `P x ==> ((~(ls = []) ==> P (LAST ls)) <=> (P (LAST (CONS x ls))))`)
  CHEAT_TAC;;

let EL_CONS_IF = cake_theorem "EL_CONS_IF"
  (fun () ->
    `EL n (x :: xs) = (if n = 0 then x else EL (PRE n) xs)`)
  CHEAT_TAC;;

let EVERY_TOKENS = cake_theorem "EVERY_TOKENS"
  (fun () ->
    `!P ls. EVERY (EVERY ((~) o P)) (TOKENS P ls)`)
  CHEAT_TAC;;

let TOKENS_START = cake_theorem "TOKENS_START"
  (fun () ->
    `!l a. TOKENS (\x. x = a) (a :: l) = TOKENS (\x. x = a) l`)
  CHEAT_TAC;;

let TOKENS_END = cake_theorem "TOKENS_END"
  (fun () ->
    `!l a.
        TOKENS (\x. x = a) (l ++ [a]) = TOKENS (\x. x = a) l`)
  CHEAT_TAC;;


let TOKENS_LENGTH_END = cake_theorem "TOKENS_LENGTH_END"
  (fun () ->
    `!l a.
        LENGTH (TOKENS (\x. x = a) (l ++ [a])) = LENGTH (TOKENS
          (\x. x = a) l)`)
  CHEAT_TAC;;

let TOKENS_LENGTH_START = cake_theorem "TOKENS_LENGTH_START"
  (fun () ->
    `!l a.
        LENGTH (TOKENS (\x. x = a) (a :: l)) = LENGTH (TOKENS
          (\x. x = a) l)`)
  CHEAT_TAC;;


let DROP_EMPTY = cake_theorem "DROP_EMPTY"
  (fun () ->
    `!ls n. (DROP n ls = []) ==> (n >= LENGTH ls)`)
  CHEAT_TAC;;

let FRONT_APPEND' = cake_theorem "FRONT_APPEND'[local]"
  (fun () ->
    `!l h a b t. l = h ++ [a; b] ++ t ==>
         FRONT l = h ++ FRONT ([a; b] ++ t)`)
  CHEAT_TAC;;


let EVERY_NOT_IMP = cake_theorem "EVERY_NOT_IMP[local]"
  (fun () ->
    `!ls a. (EVERY ((~) o (\x. x = a)) ls) ==> (LIST_ELEM_COUNT a ls =
  0)`)
  CHEAT_TAC;;

let LIST_ELEM_COUNT_CONS = cake_theorem "LIST_ELEM_COUNT_CONS[local]"
  (fun () ->
    `!h t a. LIST_ELEM_COUNT a (h :: t) = LIST_ELEM_COUNT a [h] +
  LIST_ELEM_COUNT a t`)
  CHEAT_TAC;;

let FRONT_COUNT_IMP = cake_theorem "FRONT_COUNT_IMP[local]"
  (fun () ->
    `!l1 l2 a. ~(l1 = []) /\ FRONT l1 = l2 ==> (LIST_ELEM_COUNT a l2 =
  LIST_ELEM_COUNT a l1) \/ (LIST_ELEM_COUNT a l2 + 1 = LIST_ELEM_COUNT
  a l1)`)
  CHEAT_TAC;;

let OPT_MMAP_MAP_o = cake_theorem "OPT_MMAP_MAP_o"
  (fun () ->
    `!ls. OPT_MMAP f (MAP g ls) = OPT_MMAP (f o g) ls`)
  CHEAT_TAC;;

let OPT_MMAP_SOME = cake_theorem "OPT_MMAP_SOME[simp]"
  (fun () ->
    `OPT_MMAP SOME ls = SOME ls`)
  CHEAT_TAC;;

let OPT_MMAP_CONG = cake_theorem "OPT_MMAP_CONG[defncong]"
  (fun () ->
    `!l1 l2 f f'.
       (l1 = l2) /\
       (!x. MEM x l2 ==> (f x = f' x)) ==> (OPT_MMAP f l1 =
         OPT_MMAP f' l2)`)
  CHEAT_TAC;;

let IMP_OPT_MMAP_EQ = cake_theorem "IMP_OPT_MMAP_EQ"
  (fun () ->
    `!l1 l2. (MAP f1 l1 = MAP f2 l2) ==> (OPT_MMAP f1 l1 = OPT_MMAP f2
  l2)`)
  CHEAT_TAC;;

let DISJOINT_set_simp = cake_theorem "DISJOINT_set_simp"
  (fun () ->
    `DISJOINT (set_of_list []) s /\
      (DISJOINT (set_of_list (x :: xs)) s <=> ~(x IN s) /\
        DISJOINT (set_of_list xs) s)`)
  CHEAT_TAC;;

let DISJOINT_INTER = cake_theorem "DISJOINT_INTER"
  (fun () ->
    `DISJOINT b c ==> DISJOINT (a INTER b) (a INTER c)`)
  CHEAT_TAC;;

let ALOOKUP_EXISTS_IFF = cake_theorem "ALOOKUP_EXISTS_IFF"
  (fun () ->
    `(?v. ALOOKUP alist k = SOME v) <=> (?v. MEM (k,v) alist)`)
  CHEAT_TAC;;

let LUPDATE_commutes = cake_theorem "LUPDATE_commutes"
  (fun () ->
    `!m n e1 e2 l. ~(
      m = n) ==>
      LUPDATE e1 m (LUPDATE e2 n l) = LUPDATE e2 n (LUPDATE e1 m
        l)`)
  CHEAT_TAC;;

let LUPDATE_APPEND = cake_theorem "LUPDATE_APPEND"
  (fun () ->
    `!xs n ys x.
        LUPDATE x n (xs ++ ys) =
        (if n < LENGTH xs then LUPDATE x n xs ++ ys else xs ++
          LUPDATE x (n - LENGTH xs) ys)`)
  CHEAT_TAC;;

let FILTER_EL_EQ = cake_theorem "FILTER_EL_EQ"
  (fun () ->
    `!l1 l2.
     LENGTH l1 = LENGTH l2 /\
     (!n. n < LENGTH l1 /\ (P (EL n l1) \/ P (EL n l2)) ==> (EL n
       l1 = EL n l2)) ==>
     FILTER P l1 = FILTER P l2`)
  CHEAT_TAC;;

let FST_EL_AFUPDKEY = cake_theorem "FST_EL_AFUPDKEY"
  (fun () ->
    `!n. n < LENGTH ls ==> FST (EL n (AFUPDKEY k f ls)) = FST (EL n
  ls)`)
  CHEAT_TAC;;

let EL_AFUPDKEY_unchanged = cake_theorem "EL_AFUPDKEY_unchanged"
  (fun () ->
    `!n. n < LENGTH ls /\ ~(FST (EL n ls) = k) ==> EL n (AFUPDKEY k f
  ls) = EL n ls`)
  CHEAT_TAC;;

let findi_APPEND = cake_theorem "findi_APPEND"
  (fun () ->
    `!l1 l2 x.
        indexedLists_findi x (l1 ++ l2) =
          (let n0 = indexedLists_findi x l1 in
            if n0 = LENGTH l1 then n0 + indexedLists_findi x l2
              else n0)`)
  CHEAT_TAC;;

let NOT_MEM_findi_IFF = cake_theorem "NOT_MEM_findi_IFF"
  (fun () ->
    `~MEM e l <=> indexedLists_findi e l = LENGTH l`)
  CHEAT_TAC;;

(* HOL4 miscScript.sml:2585-2586: a theorem that HOL4 states as the
   value of an ML expression *)

let ORD_eq_0 = cake_theorem "ORD_eq_0"
  (fun () ->
    `(ORD c = 0 <=> c = CHR 0) /\ (0 = ORD c <=> c = CHR 0)`)
  CHEAT_TAC;;

let HD_LUPDATE = cake_theorem "HD_LUPDATE"
  (fun () ->
    `0 < LENGTH l ==> HD (LUPDATE x p l) = (if p = 0 then x else HD l)`)
  CHEAT_TAC;;

let DROP_LUPDATE = cake_theorem "DROP_LUPDATE"
  (fun () ->
    `!n x m l. n <= m ==> DROP n (LUPDATE x m l) = LUPDATE x (m - n)
  (DROP n l)`)
  CHEAT_TAC;;

(* HOL4 miscScript.sml:2608-2610: a theorem that HOL4 states as the
   value of an ML expression *)

let CHR_w2n_n2w_ORD = cake_theorem "CHR_w2n_n2w_ORD"
  (fun () ->
    `(CHR o w2n o (n2w:num->word8) o ORD) = I`)
  CHEAT_TAC;;

let n2w_ORD_CHR_w2n = cake_theorem "n2w_ORD_CHR_w2n"
  (fun () ->
    `((n2w:num->word8) o ORD o CHR o w2n) = I`)
  CHEAT_TAC;;

let CHR_w2n_n2w_ORD_simp = cake_theorem "CHR_w2n_n2w_ORD_simp[simp]"
  (fun () ->
    `!c. CHR (w2n ((n2w:num->word8) (ORD c))) = c`)
  CHEAT_TAC;;

let n2w_ORD_CHR_w2n_simp = cake_theorem "n2w_ORD_CHR_w2n_simp[simp]"
  (fun () ->
    `!w. n2w (ORD (CHR (w2n w))) = (w:word8)`)
  CHEAT_TAC;;

let MAP_CHR_w2n_11 = cake_theorem "MAP_CHR_w2n_11"
  (fun () ->
    `!ws1 (ws2:word8 list).
        MAP (CHR o w2n) ws1 = MAP (CHR o w2n) ws2 <=> ws1 = ws2`)
  CHEAT_TAC;;

let MAP_K_REPLICATE = cake_theorem "MAP_K_REPLICATE"
  (fun () ->
    `MAP (K x) ls = REPLICATE (LENGTH ls) x`)
  CHEAT_TAC;;

let shift_left_def = cake_define
  `shift_left (a:'a word) n =
   (if n = 0 then a else if (a = (n2w 0)) \/ n > dimindex (:'a)
     then (n2w 0) else if n > 32 then shift_left (a << 32) (n - 32)
     else if n > 16 then shift_left (a << 16) (n - 16) else if n > 8
     then shift_left (a << 8) (n - 8) else shift_left (a << 1) (n -
     1))`;;

let shift_left_rwt = cake_theorem "shift_left_rwt"
  (fun () ->
    `!a n. a << n = shift_left a n`)
  CHEAT_TAC;;

let shift_right_def = cake_define
  `shift_right (a:'a word) n =
   (if n = 0 then a else if (a = (n2w 0)) \/ n > dimindex (:'a)
     then (n2w 0) else if n > 32 then shift_right (a >>> 32) (n - 32)
     else if n > 16 then shift_right (a >>> 16) (n - 16) else if n >
     8 then shift_right (a >>> 8) (n - 8) else shift_right (a >>> 1)
     (n - 1))`;;

let shift_right_rwt = cake_theorem "shift_right_rwt"
  (fun () ->
    `!a n. a >>> n = shift_right a n`)
  CHEAT_TAC;;

let arith_shift_right_def = cake_define
  `arith_shift_right (a:'a word) n =
   (if n = 0 then a else if (a = (n2w 0)) \/ n > dimindex (:'a) /\
     ~word_msb a then (n2w 0) else if (a = --(n2w 1)) \/ n > dimindex
     (:'a) /\ word_msb a then --(n2w 1) else if n > 32 then
     arith_shift_right (a >> 32) (n - 32) else if n > 16 then
     arith_shift_right (a >> 16) (n - 16) else if n > 8 then
     arith_shift_right (a >> 8) (n - 8) else arith_shift_right (a >>
     1) (n - 1))`;;

let arith_shift_right_rwt = cake_theorem "arith_shift_right_rwt"
  (fun () ->
    `!a n. a >> n = arith_shift_right a n`)
  CHEAT_TAC;;

let any_word64_ror_def = cake_define
  `any_word64_ror (w:word64) (n:num) =
     (if 64 <= n then any_word64_ror w (n - 64) else
     if 32 <= n then any_word64_ror (word_ror w 32) (n - 32) else
     if 16 <= n then any_word64_ror (word_ror w 16) (n - 16) else
     if 8 <= n then any_word64_ror (word_ror w 8) (n - 8) else
     if 4 <= n then any_word64_ror (word_ror w 4) (n - 4) else
     if 2 <= n then any_word64_ror (word_ror w 2) (n - 2) else
     if 1 <= n then word_ror w 1 else w)`;;

let word_ror_eq_any_word64_ror =
  cake_theorem "word_ror_eq_any_word64_ror"
  (fun () ->
    `!a n. word_ror a n = any_word64_ror a n`)
  CHEAT_TAC;;

let TL_DROP_SUC = cake_theorem "TL_DROP_SUC"
  (fun () ->
    `!x ls. x < LENGTH ls ==> TL (DROP x ls) = DROP (SUC x) ls`)
  CHEAT_TAC;;

let DROP_IMP_LESS_LENGTH = cake_theorem "DROP_IMP_LESS_LENGTH"
  (fun () ->
    `!xs n y ys. DROP n xs = y :: ys ==> n < LENGTH xs`)
  CHEAT_TAC;;

let DROP_EQ_CONS_IMP_DROP_SUC = cake_theorem "DROP_EQ_CONS_IMP_DROP_SUC"
  (fun () ->
    `!xs n y ys. DROP n xs = y :: ys ==> DROP (SUC n) xs = ys`)
  CHEAT_TAC;;

let DROP_IMP_EL = cake_theorem "DROP_IMP_EL"
  (fun () ->
    `!xs n h t. DROP n xs = h :: t ==> (EL n xs = h)`)
  CHEAT_TAC;;

let LENGTH_FIELDS = cake_theorem "LENGTH_FIELDS"
  (fun () ->
    `!ls. LENGTH (FIELDS P ls) = LENGTH (FILTER P ls) + 1`)
  CHEAT_TAC;;

let FIELDS_NEQ_NIL = cake_theorem "FIELDS_NEQ_NIL[simp]"
  (fun () ->
    `~(
        FIELDS P ls = [])`)
  CHEAT_TAC;;

let CONCAT_FIELDS = cake_theorem "CONCAT_FIELDS"
  (fun () ->
    `!ls. CONCAT (FIELDS P ls) = FILTER ((~) o P) ls`)
  CHEAT_TAC;;

let FIELDS_next = cake_theorem "FIELDS_next"
  (fun () ->
    `!ls l1 l2.
     FIELDS P ls = l1 :: l2 ==>
     LENGTH l1 < LENGTH ls ==>
     FIELDS P (DROP (SUC (LENGTH l1)) ls) = l2 /\
     (?c. l1 ++ [c] <<= ls /\ P c)`)
  CHEAT_TAC;;

let FIELDS_full = cake_theorem "FIELDS_full"
  (fun () ->
    `!P ls l1 l2.
     FIELDS P ls = l1 :: l2 /\ LENGTH ls <= LENGTH l1 ==>
     l1 = ls /\ l2 = []`)
  CHEAT_TAC;;

let FLAT_MAP_TOKENS_FIELDS = cake_theorem "FLAT_MAP_TOKENS_FIELDS"
  (fun () ->
    `!P' ls P.
      (!x. P' x ==> P x) ==>
       FLAT (MAP (TOKENS P) (FIELDS P' ls)) =
       TOKENS P ls`)
  CHEAT_TAC;;

let the_nil_eq_cons = cake_theorem "the_nil_eq_cons"
  (fun () ->
    `(the [] x = y :: z) <=> x = SOME (y :: z)`)
  CHEAT_TAC;;

let splitlines_def = cake_define
  `splitlines ls =
   (let lines = FIELDS ((=) (CHR 10)) ls in
   if NULL (LAST lines) then FRONT lines else lines)`;;

let splitlines_next = cake_theorem "splitlines_next"
  (fun () ->
    `splitlines ls = ln :: lns ==>
     splitlines (DROP (SUC (LENGTH ln)) ls) = lns /\
     ln <<= ls /\ (LENGTH ln < LENGTH ls ==> ln ++ "\n" <<= ls)`)
  CHEAT_TAC;;

(* HOL4 miscScript.sml:2935: a theorem that HOL4 states as the value
   of an ML expression *)

let splitlines_eq_nil = cake_theorem "splitlines_eq_nil[simp]"
  (fun () ->
    `splitlines ls = [] <=> (ls = [])`)
  CHEAT_TAC;;

let splitlines_CONS_FST_SPLITP =
  cake_theorem "splitlines_CONS_FST_SPLITP"
  (fun () ->
    `splitlines ls = ln :: lns ==> FST (SPLITP ((=) (CHR 10)) ls) = ln`)
  CHEAT_TAC;;

let n2l_DIV_MOD = cake_theorem "n2l_DIV_MOD"
  (fun () ->
    `!b n k. 1 < b /\ 0 < k /\ b EXP k <= n ==>
     (n2l b (n MOD (b EXP k)) ++ REPLICATE (k - LENGTH (n2l b (n
       MOD (b EXP k)))) 0 ++
      n2l b (n DIV (b EXP k)) = n2l b n)`)
  CHEAT_TAC;;

let irreflexive_inv_image = cake_theorem "irreflexive_inv_image"
  (fun () ->
    `!R f. irreflexive R ==> irreflexive (inv_image R f)`)
  CHEAT_TAC;;

let trichotomous_inv_image = cake_theorem "trichotomous_inv_image"
  (fun () ->
    `!R f. trichotomous R /\ (INJ f UNIV UNIV) ==> trichotomous
  (inv_image R f)`)
  CHEAT_TAC;;

let MEM_REPLICATE_IMP = cake_theorem "MEM_REPLICATE_IMP"
  (fun () ->
    `MEM x (REPLICATE n y) ==> x = y`)
  CHEAT_TAC;;

let plus_0_I = cake_theorem "plus_0_I[simp]"
  (fun () ->
    `(+) 0 = I`)
  CHEAT_TAC;;

(* used once *)
(* HOL4 miscScript.sml:3037-3038: a theorem that HOL4 states as the
   value of an ML expression *)

let OPTION_MAP_I = cake_theorem "OPTION_MAP_I[simp]"
  (fun () ->
    `OPTION_MAP I' x = x`)
  CHEAT_TAC;;

(* should be made an iff in conclusion *)
let OPTION_MAP_INJ = cake_theorem "OPTION_MAP_INJ"
  (fun () ->
    `(!x y. f x = f y ==> x = y) ==> (!o1 o2.
       OPTION_MAP f o1 = OPTION_MAP f o2 ==> o1 = o2)`)
  CHEAT_TAC;;

let the_OPTION_MAP = cake_theorem "the_OPTION_MAP"
  (fun () ->
    `!f d opt.
     f d = d ==>
     the d (OPTION_MAP f opt) = f (the d opt)`)
  CHEAT_TAC;;

let TAKE_FLAT_REPLICATE_LEQ = cake_theorem "TAKE_FLAT_REPLICATE_LEQ"
  (fun () ->
    `!j k ls len.
      len = LENGTH ls /\ k <= j ==>
      TAKE (k * len) (FLAT (REPLICATE j ls)) = FLAT (REPLICATE k
        ls)`)
  CHEAT_TAC;;

let MOD_2EXP_0_EVEN = cake_theorem "MOD_2EXP_0_EVEN"
  (fun () ->
    `!x y. 0 < x /\ MOD_2EXP x y = 0 ==> EVEN y`)
  CHEAT_TAC;;

let ADD_MOD_EQ_LEMMA = cake_theorem "ADD_MOD_EQ_LEMMA"
  (fun () ->
    `k MOD d = 0 /\ n < d ==> (k + n) MOD d = n`)
  CHEAT_TAC;;

(* should be set l1 ⊆ set l2 *)
let list_subset_def = cake_define
  `list_subset l1 l2 = EVERY (\x. MEM x l2) l1`;;

let list_set_eq_def = cake_define
  `list_set_eq l1 l2 <=> list_subset l1 l2 /\ list_subset l2 l1`;;

let list_subset_LENGTH = cake_theorem "list_subset_LENGTH"
  (fun () ->
    `!l1 l2. ALL_DISTINCT l1 /\
     list_subset l1 l2 ==>
     LENGTH l1 <= LENGTH l2`)
  CHEAT_TAC;;

let BIJ_UPDATE = cake_theorem "BIJ_UPDATE"
  (fun () ->
    `!f s t x y. BIJ f s t /\ ~(x IN s) /\ ~(y IN t) ==>
      BIJ ((x =+ y) f) (x INSERT s) (y INSERT t)`)
  CHEAT_TAC;;

let INJ_UPDATE = cake_theorem "INJ_UPDATE"
  (fun () ->
    `INJ f s t /\ ~(x IN s) /\ ~(y IN t) ==>
      INJ ((x =+ y) f) (x INSERT s) (y INSERT t)`)
  CHEAT_TAC;;

(* TODO: candidate for move to HOL;
         subspt_domain exists already but is specialised to unit *)
let subspt_domain_SUBSET = cake_theorem "subspt_domain_SUBSET"
  (fun () ->
    `subspt t1 t2 ==> domain t1 SUBSET domain t2`)
  CHEAT_TAC;;

(* Some temporal logic definitions based on lazy lists *)
(* move into llistTheory? *)

let SPLITP_TAKE_DROP = cake_theorem "SPLITP_TAKE_DROP"
  (fun () ->
    `!P i l. EVERY ((~) o P) (TAKE i l) ==>
     P (EL i l) ==>
     SPLITP P l = (TAKE i l,DROP i l)`)
  CHEAT_TAC;;

let SND_SPLITP_DROP = cake_theorem "SND_SPLITP_DROP"
  (fun () ->
    `!P n l. EVERY ((~) o P) (TAKE n l) ==>
      SND (SPLITP P (DROP n l)) = SND (SPLITP P l)`)
  CHEAT_TAC;;

let FST_SPLITP_DROP = cake_theorem "FST_SPLITP_DROP"
  (fun () ->
    `!P n l. EVERY ((~) o P) (TAKE n l) ==>
      FST (SPLITP P l) = (TAKE n l) ++ FST (SPLITP P (DROP n l))`)
  CHEAT_TAC;;

let TAKE_DROP_SUBLIST = cake_theorem "TAKE_DROP_SUBLIST"
  (fun () ->
    `ll <<= (DROP n ls) /\ n < LENGTH ls /\ (nlll = n + LENGTH ll) ==>
     (TAKE n ls ++ ll ++ DROP nlll ls = ls)`)
  CHEAT_TAC;;

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

let OPTION_CHOICE_EQUALS_OPTION =
  cake_theorem "OPTION_CHOICE_EQUALS_OPTION"
  (fun () ->
    `!(x:'a option) y z. (OPTION_CHOICE x y = SOME z) <=>
                         ((x = SOME z) \/ ((x = NONE) /\ (y =
                           SOME z)))`)
  CHEAT_TAC;;

(* HOL4 miscScript.sml:3210-3214: a theorem that HOL4 states as the
   value of an ML expression *)

let ALL_DISTINCT_alist_to_fmap_REVERSE =
  cake_theorem "ALL_DISTINCT_alist_to_fmap_REVERSE"
  (fun () ->
    `ALL_DISTINCT (MAP FST ls) ==> alist_to_fmap (REVERSE ls) =
  alist_to_fmap ls`)
  CHEAT_TAC;;

let FUPDATE_LIST_alist_to_fmap =
  cake_theorem "FUPDATE_LIST_alist_to_fmap"
  (fun () ->
    `!ls fm. fm |++ ls = FUNION (alist_to_fmap (REVERSE ls)) fm`)
  CHEAT_TAC;;

let DISTINCT_FUPDATE_LIST_UNION =
  cake_theorem "DISTINCT_FUPDATE_LIST_UNION"
  (fun () ->
    `ALL_DISTINCT (MAP FST ls) /\
     DISJOINT (FDOM f) (set_of_list (MAP FST ls)) ==>
     f |++ ls = FUNION f (alist_to_fmap ls)`)
  CHEAT_TAC;;

let fevery_to_drestrict = cake_theorem "fevery_to_drestrict"
  (fun () ->
    `!P m s.
      FEVERY P m ==> FEVERY P (DRESTRICT m s)`)
  CHEAT_TAC;;

let SUM_MAP_K = cake_theorem "SUM_MAP_K"
  (fun () ->
    `!f ls c. (!x. f x = c) ==> SUM (MAP f ls) = LENGTH ls * c`)
  CHEAT_TAC;;

let LAST_FLAT = cake_theorem "LAST_FLAT"
  (fun () ->
    `!ls. ~NULL (FLAT ls) ==> (LAST (FLAT ls) = LAST (LAST (FILTER
  ((~) o NULL) ls)))`)
  CHEAT_TAC;;

let TOKENS_unchanged = cake_theorem "TOKENS_unchanged"
  (fun () ->
    `EVERY ((~) o P) ls ==> TOKENS P ls = (if NULL ls then [] else
  [ls])`)
  CHEAT_TAC;;

let TOKENS_FLAT_MAP_SNOC = cake_theorem "TOKENS_FLAT_MAP_SNOC"
  (fun () ->
    `EVERY (EVERY ((\x y. ~(x = y)) x)) ls /\ EVERY ((~) o NULL) ls ==>
     TOKENS ((=) x) (FLAT (MAP (SNOC x) ls)) = ls`)
  CHEAT_TAC;;

(* insert a string (l1) at specified index (n) in a list (l2) *)
let insert_atI_def = cake_define
  `insert_atI l1 n l2 =
     TAKE n l2 ++ l1 ++ DROP (n + LENGTH l1) l2`;;

let insert_atI_NIL = cake_theorem "insert_atI_NIL"
  (fun () ->
    `!n l. insert_atI [] n l = l`)
  CHEAT_TAC;;

let insert_atI_CONS = cake_theorem "insert_atI_CONS"
  (fun () ->
    `!n l h t.
       n + LENGTH t < LENGTH l ==>
       insert_atI (h :: t) n l = LUPDATE h n (insert_atI t (n +
         1) l)`)
  CHEAT_TAC;;

let LENGTH_insert_atI = cake_theorem "LENGTH_insert_atI"
  (fun () ->
    `p + LENGTH l1 <= LENGTH l2 ==> LENGTH (insert_atI l1 p l2) =
  LENGTH l2`)
  CHEAT_TAC;;

let insert_atI_app = cake_theorem "insert_atI_app"
  (fun () ->
    `!n l c1 c2. n + LENGTH c1 + LENGTH c2 <= LENGTH l ==>
       insert_atI (c1 ++ c2) n l =
       insert_atI c1 n (insert_atI c2 (n + LENGTH c1) l)`)
  CHEAT_TAC;;

let insert_atI_end = cake_theorem "insert_atI_end"
  (fun () ->
    `insert_atI l1 (LENGTH l2) l2 = l2 ++ l1`)
  CHEAT_TAC;;

let insert_atI_insert_atI = cake_theorem "insert_atI_insert_atI"
  (fun () ->
    `pos2 = pos1 + LENGTH c1 ==>
      insert_atI c2 pos2 (insert_atI c1 pos1 l) = insert_atI (c1
        ++ c2) pos1 l`)
  CHEAT_TAC;;

let LUPDATE_insert_commute = cake_theorem "LUPDATE_insert_commute"
  (fun () ->
    `!ws pos1 pos2 a w.
       pos2 < pos1 /\ pos1 + LENGTH ws <= LENGTH a ==>
       insert_atI ws pos1 (LUPDATE w pos2 a) =
         LUPDATE w pos2 (insert_atI ws pos1 a)`)
  CHEAT_TAC;;

let LESS_EQ_LENGTH = cake_theorem "LESS_EQ_LENGTH"
  (fun () ->
    `!xs k. k <= LENGTH xs ==> (?ys1 ys2. (xs = ys1 ++ ys2) /\ (LENGTH
  ys1 = k))`)
  CHEAT_TAC;;

let LESS_LENGTH = cake_theorem "LESS_LENGTH"
  (fun () ->
    `!xs k. k < LENGTH xs ==>
             (?ys1 y ys2. (xs = ys1 ++ (y :: ys2)) /\ (LENGTH ys1
               = k))`)
  CHEAT_TAC;;

(* HOL4 miscScript.sml:3372-3373: a theorem that HOL4 states as the
   value of an ML expression *)

let FOLDL_OPTION_CHOICE_EQ_SOME_IMP_MEM =
  cake_theorem "FOLDL_OPTION_CHOICE_EQ_SOME_IMP_MEM"
  (fun () ->
    `FOLDL OPTION_CHOICE x ls = SOME y ==> MEM (SOME y) (x :: ls)`)
  CHEAT_TAC;;

let BAG_ALL_DISTINCT_FOLDR_BAG_UNION =
  cake_theorem "BAG_ALL_DISTINCT_FOLDR_BAG_UNION"
  (fun () ->
    `!ls b0.
     BAG_ALL_DISTINCT ((BAG_UNION) FOLDR' (b0 ls)) <=>
     BAG_ALL_DISTINCT b0 /\
     (!n. n < LENGTH ls ==>
          BAG_DISJOINT (EL n ls) b0 /\ BAG_ALL_DISTINCT (EL n ls)
            /\
          (!m. m < n ==> BAG_DISJOINT (EL n ls) (EL m ls)))`)
  CHEAT_TAC;;

(* TODO - candidate for move to HOL *)
(* N.B.: there is a different is_subsequence defined in lcsTheory; these should be merged *)
let is_subseq_def = cake_define_list
  [`is_subseq ls [] <=> T`;
   `is_subseq [] (x :: xs) <=> F`;
   `is_subseq (y :: ys) (x :: xs) <=>
       (x = y /\ is_subseq ys xs) \/
       (is_subseq ys (x :: xs))`];;

(* TODO - candidate for move to HOL *)
(* HOL4 miscScript.sml:3413: ML code, not ported *)

(* TODO - candidate for move to HOL *)
let is_subseq_refl = cake_theorem "is_subseq_refl[simp]"
  (fun () ->
    `!ls. is_subseq ls ls`)
  CHEAT_TAC;;

(* TODO - candidate for move to HOL *)
let is_subseq_nil = cake_theorem "is_subseq_nil[simp]"
  (fun () ->
    `is_subseq [] ls <=> ls = []`)
  CHEAT_TAC;;

(* TODO - candidate for move to HOL *)
let is_subseq_cons = cake_theorem "is_subseq_cons"
  (fun () ->
    `!l1 l2 x. is_subseq l1 l2 ==> is_subseq (x :: l1) l2`)
  CHEAT_TAC;;

(* TODO - candidate for move to HOL *)
let is_subseq_snoc = cake_theorem "is_subseq_snoc"
  (fun () ->
    `!l1 l2 x. is_subseq l1 l2 ==> is_subseq (SNOC x l1) l2`)
  CHEAT_TAC;;

(* TODO - candidate for move to HOL *)
let is_subseq_append1 = cake_theorem "is_subseq_append1"
  (fun () ->
    `!l3 l1 l2. is_subseq l1 l2 ==> is_subseq (l3 ++ l1) l2`)
  CHEAT_TAC;;

(* TODO - candidate for move to HOL *)
let is_subseq_append2 = cake_theorem "is_subseq_append2"
  (fun () ->
    `!l4 l1 l2. is_subseq l1 l2 ==> is_subseq (l1 ++ l4) l2`)
  CHEAT_TAC;;

(* TODO - candidate for move to HOL *)
let is_subseq_IS_SUBLIST = cake_theorem "is_subseq_IS_SUBLIST"
  (fun () ->
    `is_subseq l1 l2 /\ IS_SUBLIST l3 l1 ==> is_subseq l3 l2`)
  CHEAT_TAC;;

(* TODO - candidate for move to HOL *)
let is_subseq_MEM = cake_theorem "is_subseq_MEM"
  (fun () ->
    `!l1 l2 x. is_subseq l1 l2 /\ MEM x l2 ==> MEM x l1`)
  CHEAT_TAC;;

(* TODO - candidate for move to HOL *)
let IS_PREFIX_is_subseq = cake_theorem "IS_PREFIX_is_subseq"
  (fun () ->
    `!l1 l2. IS_PREFIX l1 l2 ==> is_subseq l1 l2`)
  CHEAT_TAC;;

(* TODO - candidate for move to HOL *)
let IS_SUBLIST_is_subseq = cake_theorem "IS_SUBLIST_is_subseq"
  (fun () ->
    `!l1 l2. IS_SUBLIST l1 l2 ==> is_subseq l1 l2`)
  CHEAT_TAC;;

(* TODO - candidate for move to HOL *)
let is_subseq_ALL_DISTINCT = cake_theorem "is_subseq_ALL_DISTINCT"
  (fun () ->
    `!l1 l2. ALL_DISTINCT l1 /\ is_subseq l1 l2 ==> ALL_DISTINCT l2`)
  CHEAT_TAC;;

(* TODO - candidate for move to HOL *)
let is_subseq_append_suff = cake_theorem "is_subseq_append_suff"
  (fun () ->
    `!l1 l3 l2 l4.
     is_subseq l1 l3 /\ is_subseq l2 l4 ==>
     is_subseq (l1 ++ l2) (l3 ++ l4)`)
  CHEAT_TAC;;

(* TODO - candidate for move to HOL *)
let is_subseq_FLAT_suff = cake_theorem "is_subseq_FLAT_suff"
  (fun () ->
    `!ls1 ls2. LIST_REL is_subseq ls1 ls2 ==> is_subseq (FLAT ls1)
  (FLAT ls2)`)
  CHEAT_TAC;;

let LIST_REL_IMP_LAST = cake_theorem "LIST_REL_IMP_LAST"
  (fun () ->
    `!P xs ys.
        LIST_REL P xs ys /\ (~(xs = []) \/ ~(ys = [])) ==> P
          (LAST xs) (LAST ys)`)
  CHEAT_TAC;;

let make_even_def = cake_define
  `make_even n = (if EVEN n then n else n + 1)`;;

let EVEN_make_even = cake_theorem "EVEN_make_even[simp]"
  (fun () ->
    `EVEN (make_even x)`)
  CHEAT_TAC;;

let ALOOKUP_MAP_FST_INJ_SOME = cake_theorem "ALOOKUP_MAP_FST_INJ_SOME"
  (fun () ->
    `!ls x y.
      ALOOKUP ls x = SOME y /\ (!x'. IS_SOME (ALOOKUP ls x') /\ f
        x' = f x ==> x = x') ==>
      ALOOKUP (MAP (f ## g) ls) (f x) = SOME (g y)`)
  CHEAT_TAC;;

let v2w_32_F = cake_theorem "v2w_32_F[simp]"
  (fun () ->
    `(v2w [F]:word32) = (n2w 0)`)
  CHEAT_TAC;;

let v2w_32_T = cake_theorem "v2w_32_T[simp]"
  (fun () ->
    `(v2w [T]:word32) = (n2w 1)`)
  CHEAT_TAC;;

let v2w_sing = cake_theorem "v2w_sing"
  (fun () ->
    `v2w [b] = (if b then (n2w 1) else (n2w 0))`)
  CHEAT_TAC;;

let FOLDR_FUNPOW = cake_theorem "FOLDR_FUNPOW"
  (fun () ->
    `ITLIST (\x. f) ls x = FUNPOW f (LENGTH ls) x`)
  CHEAT_TAC;;

let FUNPOW_refl_trans_chain = cake_theorem "FUNPOW_refl_trans_chain"
  (fun () ->
    `transitive P /\ reflexive P ==>
     (!n x. (!j. j < n ==> P (FUNPOW f j x) (f (FUNPOW f j x))) ==>
       P x (FUNPOW f n x))`)
  CHEAT_TAC;;

let byte_align_extract = cake_theorem "byte_align_extract"
  (fun () ->
    `byte_align (x:word32) = (((31 >< 2) x):word30) @@ ((n2w 0):word2)`)
  CHEAT_TAC;;

let byte_align_IN_IMP_IN_range =
  cake_theorem "byte_align_IN_IMP_IN_range"
  (fun () ->
    `byte_align a IN dm /\
     (dm = {w | low <=+ w /\ w <+ hi}) /\
     byte_aligned low /\ byte_aligned hi ==>
     a IN dm`)
  CHEAT_TAC;;

let MULT_DIV_MULT_LEMMA = cake_theorem "MULT_DIV_MULT_LEMMA"
  (fun () ->
    `!m l k. 0 < m /\ 0 < l ==> (m * k) DIV (l * m) = k DIV l`)
  CHEAT_TAC;;

let IMP_MULT_DIV_LESS = cake_theorem "IMP_MULT_DIV_LESS"
  (fun () ->
    `~(
        m = 0) /\ d < k ==> m * (d DIV m) < k`)
  CHEAT_TAC;;

let DIV_LESS_DIV = cake_theorem "DIV_LESS_DIV"
  (fun () ->
    `n MOD k = 0 /\ m MOD k = 0 /\ n < m /\ 0 < k ==> n DIV k < m DIV
  k`)
  CHEAT_TAC;;

let toPath_fromList = cake_theorem "toPath_fromList"
  (fun () ->
    `(toPath (x,fromList []) = stopped_at x) /\
     (toPath (x,fromList ((y,z) :: t)) = pcons x y (toPath
       (z,fromList t)))`)
  CHEAT_TAC;;

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

(* HOL4 miscScript.sml:3681: ML code, not ported *)

let steps_rel_okpath = cake_theorem "steps_rel_okpath"
  (fun () ->
    `!R x tr.
      steps_rel R x tr <=> okpath R (toPath (x,fromList tr))`)
  CHEAT_TAC;;

let steps_rel_LRC = cake_theorem "steps_rel_LRC"
  (fun () ->
    `!R x tr.
      steps_rel R x tr ==>
      LRC (\x y. ?i. R x i y)
        (FRONT (x :: (MAP SND tr))) x (LAST (x :: (MAP SND tr)))`)
  CHEAT_TAC;;

let LAST_MAP_SND_steps_FOLDL = cake_theorem "LAST_MAP_SND_steps_FOLDL"
  (fun () ->
    `!f x ls. LAST (x :: MAP SND' (steps f x ls)) = FOLDL f x ls`)
  CHEAT_TAC;;

let all_words_def = cake_define_list
  [`all_words base 0 = {}`;
   `all_words base (SUC n) = base INSERT (all_words (base + (n2w
  1)) n)`];;

let IN_all_words = cake_theorem "IN_all_words"
  (fun () ->
    `x IN all_words base n <=> (?i. i < n /\ x = base + n2w i)`)
  CHEAT_TAC;;

let read_bytearray_IMP_mem_SOME =
  cake_theorem "read_bytearray_IMP_mem_SOME"
  (fun () ->
    `!p n m ba.
     (read_bytearray p n m = SOME ba) ==>
     (!k. k IN all_words p n ==> IS_SOME (m k))`)
  CHEAT_TAC;;

let read_bytearray_no_wrap = cake_theorem "read_bytearray_no_wrap"
  (fun () ->
    `!ptr len.
     IS_SOME (read_bytearray ptr len (m:'a word->'b option)) /\
     (!x. IS_SOME (m x) ==> w2n x < dimword (:'a) - 1) /\
     w2n ptr < dimword (:'a) ==>
     w2n ptr + len < dimword (:'a)`)
  CHEAT_TAC;;

let asm_write_bytearray_def = cake_define_list
  [`asm_write_bytearray a [] (m:'a word->word8) = m`;
   `asm_write_bytearray a (x :: xs) (m:'a word->word8) = (a =+ x)
  (asm_write_bytearray (a + (n2w 1)) xs m)`];;

let mem_eq_imp_asm_write_bytearray_eq =
  cake_theorem "mem_eq_imp_asm_write_bytearray_eq"
  (fun () ->
    `!a bs.
      (m1 k = m2 k) ==>
      (asm_write_bytearray a bs m1 k = asm_write_bytearray a bs
        m2 k)`)
  CHEAT_TAC;;

let asm_write_bytearray_unchanged =
  cake_theorem "asm_write_bytearray_unchanged"
  (fun () ->
    `!a bs m z.
     (x <+ a \/ a + n2w (LENGTH bs) <=+ x) /\
      (w2n a + LENGTH bs < dimword (:'a)) /\ (z = m x) ==>
        (asm_write_bytearray (a:'a word) bs m x = z)`)
  CHEAT_TAC;;

let asm_write_bytearray_id = cake_theorem "asm_write_bytearray_id"
  (fun () ->
    `!a bs m.
      (!j. j < LENGTH bs ==> (m (a + n2w j) = EL j bs)) ==>
        (asm_write_bytearray (a:'a word) bs m x = m x)`)
  CHEAT_TAC;;

let asm_write_bytearray_unchanged_alt =
  cake_theorem "asm_write_bytearray_unchanged_alt"
  (fun () ->
    `!a bs m z.
        (z = m x) /\ ~(x IN {a + n2w k | k < LENGTH bs}) ==>
        (asm_write_bytearray a bs m x = z)`)
  CHEAT_TAC;;

let asm_write_bytearray_unchanged_all_words =
  cake_theorem "asm_write_bytearray_unchanged_all_words"
  (fun () ->
    `!a bs m z x.
      ~(x IN all_words a (LENGTH bs)) /\ (z = m x) ==>
      (asm_write_bytearray (a:'a word) bs m x = z)`)
  CHEAT_TAC;;

let asm_write_bytearray_append =
  cake_theorem "asm_write_bytearray_append"
  (fun () ->
    `!a l1 l2 m.
     w2n a + LENGTH l1 + LENGTH l2 < dimword (:'a) ==>
     (asm_write_bytearray (a:'a word) (l1 ++ l2) m =
      asm_write_bytearray (a + n2w (LENGTH l1)) l2
        (asm_write_bytearray a l1 m))`)
  CHEAT_TAC;;

let asm_write_bytearray_EL = cake_theorem "asm_write_bytearray_EL"
  (fun () ->
    `!a bs m x. x < LENGTH bs /\ LENGTH bs < dimword (:'a) ==>
     (asm_write_bytearray (a:'a word) bs m (a + n2w x) = EL x bs)`)
  CHEAT_TAC;;

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

let spt_eq = cake_theorem "spt_eq"
  (fun () ->
    `!t1 t2.
        t1 = t2 <=>
        (eq_shape t1 t2 /\ (!k v. sptree_lookup k t1 = SOME v ==>
          sptree_lookup k t2 = SOME v))`)
  CHEAT_TAC;;

let eq_shape_map = cake_theorem "eq_shape_map"
  (fun () ->
    `!t1 t2 f. eq_shape (sptree_map f t1) t2 <=> eq_shape t1 t2`)
  CHEAT_TAC;;

let eq_shape_IMP_domain = cake_theorem "eq_shape_IMP_domain"
  (fun () ->
    `!t1 t2. eq_shape t1 t2 ==> domain t1 = domain t2`)
  CHEAT_TAC;;

let copy_shape_def = cake_define_list
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

let eq_shape_copy_shape = cake_theorem "eq_shape_copy_shape[local]"
  (fun () ->
    `!s. domain s = {} ==> eq_shape (copy_shape LN s) s`)
  CHEAT_TAC;;

let num_lemma = cake_theorem "num_lemma[local]"
  (fun () ->
    `(!n. ~(0 = 2 * n + 2) /\ ~(0 = 2 * n + (1:num))) /\
     (!n m. 2 * n + 2 = 2 * m + 2 <=> (m = n)) /\
     (!n m. 2 * n + 1 = 2 * m + 1 <=> (m = n)) /\
     (!n m. ~(2 * n + 2 = 2 * m + 1))`)
  CHEAT_TAC;;

let shape_eq_copy_shape = cake_theorem "shape_eq_copy_shape"
  (fun () ->
    `!t1 t2. domain t1 = domain t2 ==> eq_shape (copy_shape t1 t2) t2`)
  CHEAT_TAC;;

let lookup_copy_shape_LN = cake_theorem "lookup_copy_shape_LN[local]"
  (fun () ->
    `!s n. sptree_lookup n (copy_shape LN s) = NONE`)
  CHEAT_TAC;;

let domain_EMPTY_lookup = cake_theorem "domain_EMPTY_lookup[local]"
  (fun () ->
    `domain t = EMPTY ==> (!x. sptree_lookup x t = NONE)`)
  CHEAT_TAC;;

let lookup_copy_shape = cake_theorem "lookup_copy_shape"
  (fun () ->
    `!t1 t2 n. sptree_lookup n (copy_shape t1 t2) = sptree_lookup n t1`)
  CHEAT_TAC;;

(* / TODO *)

(* BEGIN TODO: move to sptreeTheory *)

let lookup_zero = cake_theorem "lookup_zero"
  (fun () ->
    `!n t x. (sptree_lookup n t = SOME x) ==> (~(sptree_size t = 0))`)
  CHEAT_TAC;;

let empty_sub = cake_theorem "empty_sub"
  (fun () ->
    `(\t. t = LN) (difference a b) /\ (subspt b a) ==> (domain a =
  domain b)`)
  CHEAT_TAC;;

let subspt_delete = cake_theorem "subspt_delete"
  (fun () ->
    `!a b x. subspt a b ==> subspt (sptree_delete x a) b`)
  CHEAT_TAC;;

let inter_union_empty = cake_theorem "inter_union_empty"
  (fun () ->
    `!a b c.
     (\t. t = LN) (inter (sptree_union a b) c) <=> (\t. t = LN)
       (inter a c) /\ (\t. t = LN) (inter b c)`)
  CHEAT_TAC;;

let inter_insert_empty = cake_theorem "inter_insert_empty"
  (fun () ->
    `!n t1 t2.
     (\t. t = LN) (inter (sptree_insert n one t1) t2) ==> ~(n IN
       domain t2) /\ (\t. t = LN) (inter t1 t2)`)
  CHEAT_TAC;;

let fromList2_value = cake_theorem "fromList2_value"
  (fun () ->
    `!e l t n. MEM e l <=> (?n. sptree_lookup n (fromList2 l) = SOME
  e)`)
  CHEAT_TAC;;

(* The range is the set of values taken on by an sptree.
  Not sure if these are worth moving. *)
let range_def = cake_define
  `range s = {v | ?n. sptree_lookup n s = SOME v}`;;

let range_delete = cake_theorem "range_delete"
  (fun () ->
    `range (sptree_delete h v) SUBSET range v`)
  CHEAT_TAC;;

let range_insert = cake_theorem "range_insert"
  (fun () ->
    `~(
       n IN domain fml) ==>
       range (sptree_insert n l fml) = l INSERT range fml`)
  CHEAT_TAC;;

let range_insert_2 = cake_theorem "range_insert_2"
  (fun () ->
    `C IN range (sptree_insert n l fml) ==> C IN range fml \/ C = l`)
  CHEAT_TAC;;

let range_insert_SUBSET = cake_theorem "range_insert_SUBSET"
  (fun () ->
    `range (sptree_insert n l fml) SUBSET l INSERT range fml`)
  CHEAT_TAC;;

(* END TODO *)

let TWOxDIV2 = cake_theorem "TWOxDIV2"
  (fun () ->
    `(
        2 * x) DIV 2 = x`)
  CHEAT_TAC;;

let alist_insert_REVERSE = cake_theorem "alist_insert_REVERSE"
  (fun () ->
    `!xs ys s.
     ALL_DISTINCT xs /\ LENGTH xs = LENGTH ys ==>
     alist_insert (REVERSE xs) (REVERSE ys) s = alist_insert xs
       ys s`)
  CHEAT_TAC;;

let alist_insert_ALL_DISTINCT = cake_theorem "alist_insert_ALL_DISTINCT"
  (fun () ->
    `!xs ys t ls.
     ALL_DISTINCT xs /\
     LENGTH xs = LENGTH ys /\
     PERM (ZIP xs ys) ls ==>
     alist_insert xs ys t = alist_insert (MAP FST ls) (MAP SND
       ls) t`)
  CHEAT_TAC;;

let n2w_lt = cake_theorem "n2w_lt"
  (fun () ->
    `((n2w 0):'a word) < n2w a /\ ((n2w 0):'a word) < n2w b /\
     a < dimword (:'a) /\ b < dimword (:'a) ==>
     ((n2w a:'a word) < (n2w b:'a word) <=> a < b)`)
  CHEAT_TAC;;

let n2w_le = cake_theorem "n2w_le"
  (fun () ->
    `((n2w 0):'a word) < n2w a /\ ((n2w 0):'a word) < n2w b /\
     a < dimword (:'a) /\ b < dimword (:'a) ==>
     ((n2w a:'a word) <= (n2w b:'a word) <=> a <= b)`)
  CHEAT_TAC;;

let word_lt_0w = cake_theorem "word_lt_0w"
  (fun () ->
    `2 * n < dimword (:'a) ==> (((n2w 0):'a word) < n2w n <=> 0 < n)`)
  CHEAT_TAC;;

let word_sub_lt = cake_theorem "word_sub_lt"
  (fun () ->
    `(n2w 0) < n /\ (n2w 0) < m /\ n <= m ==> m - n < m`)
  CHEAT_TAC;;

(* see #521 *)

let bytes_in_memory_def = cake_define_list
  [`bytes_in_memory a [] m dm <=> T`;
   `bytes_in_memory a ((x:word8) :: xs) m dm <=>
         (m a = x) /\ a IN dm /\ bytes_in_memory (a + (n2w 1))
           xs m dm`];;

let bytes_in_memory_APPEND = cake_theorem "bytes_in_memory_APPEND"
  (fun () ->
    `!l1 l2 pc' mem' mem_domain'.
        bytes_in_memory pc' (l1 ++ l2) mem' mem_domain' <=>
        bytes_in_memory pc' l1 mem' mem_domain' /\
        bytes_in_memory (pc' + n2w (LENGTH l1)) l2 mem'
          mem_domain'`)
  CHEAT_TAC;;

let bytes_in_memory_change_domain =
  cake_theorem "bytes_in_memory_change_domain"
  (fun () ->
    `!a bs m md1 md2.
      bytes_in_memory a bs m md1 /\
     (!n. n < LENGTH bs /\ a + n2w n IN md1 ==> a + n2w n IN md2)
       ==> bytes_in_memory a bs m md2`)
  CHEAT_TAC;;

let bytes_in_memory_change_mem =
  cake_theorem "bytes_in_memory_change_mem"
  (fun () ->
    `!a bs m1 m2 md.
      bytes_in_memory a bs m1 md /\
     (!n. n < LENGTH bs ==> (m1 (a + n2w n) = m2 (a + n2w n)))
       ==> bytes_in_memory a bs m2 md`)
  CHEAT_TAC;;

let bytes_in_memory_EL = cake_theorem "bytes_in_memory_EL"
  (fun () ->
    `!a bs m md k. bytes_in_memory a bs m md /\ k < LENGTH bs ==> (m
  (a + n2w k) = EL k bs)`)
  CHEAT_TAC;;

let bytes_in_memory_in_domain = cake_theorem "bytes_in_memory_in_domain"
  (fun () ->
    `!a bs m md k. bytes_in_memory a bs m md /\ k < LENGTH bs ==> ((a
  + n2w k) IN md)`)
  CHEAT_TAC;;

let bytes_in_mem_def = cake_define_list
  [`bytes_in_mem a [] m md k <=> T`;
   `bytes_in_mem a (b :: bs) m md k <=>
         a IN md /\ ~(a IN k) /\ (m a = b) /\
         bytes_in_mem (a + (n2w 1)) bs m md k`];;

let bytes_in_mem_IMP = cake_theorem "bytes_in_mem_IMP"
  (fun () ->
    `!xs p. bytes_in_mem p xs m dm dm1 ==> bytes_in_memory p xs m dm`)
  CHEAT_TAC;;

let fun2set_disjoint_union = cake_theorem "fun2set_disjoint_union"
  (fun () ->
    `DISJOINT d1 d2 /\
     p (fun2set (m,d1)) /\
     q (fun2set (m,d2)) ==> (p * q) (fun2set (m,d1 UNION d2))`)
  CHEAT_TAC;;

let WORD_LS_IMP = cake_theorem "WORD_LS_IMP"
  (fun () ->
    `a <=+ b ==>
      (?k. Abbrev (b = a + n2w k) /\
          w2n (b - a) = k /\
          (!w. a <=+ w /\ w <+ b <=> (?i. w = a + n2w i /\ i <
            k)))`)
  CHEAT_TAC;;

let size_fromAList = cake_theorem "size_fromAList"
  (fun () ->
    `!xs. ALL_DISTINCT (MAP FST xs) ==> sptree_size (fromAList xs) =
  LENGTH xs`)
  CHEAT_TAC;;

let ALL_DISTINCT_MAP_FST_toSortedAList =
  cake_theorem "ALL_DISTINCT_MAP_FST_toSortedAList"
  (fun () ->
    `ALL_DISTINCT (MAP FST (toSortedAList t))`)
  CHEAT_TAC;;


let good_dimindex_def = cake_define
  `good_dimindex (:'a) <=> dimindex (:'a) = 32 \/ dimindex (:'a) = 64`;;

let good_dimindex_get_byte_set_byte =
  cake_theorem "good_dimindex_get_byte_set_byte"
  (fun () ->
    `good_dimindex (:'a) ==>
       (get_byte a (set_byte (a:'a word) b w be) be = b)`)
  CHEAT_TAC;;

let byte_index_LESS_IMP = cake_theorem "byte_index_LESS_IMP[local]"
  (fun () ->
    `(dimindex (:'a) = 32 \/ dimindex (:'a) = 64) /\
       byte_index (a:'a word) be < byte_index (a':'a word) be /\ i
         < 8 ==>
       byte_index a be + i < byte_index a' be /\
       byte_index a be <= i + byte_index a' be /\
       byte_index a be + 8 <= i + byte_index a' be /\
       i + byte_index a' be < byte_index a be + dimindex (:'a)`)
  CHEAT_TAC;;

let NOT_w2w_bit = cake_theorem "NOT_w2w_bit[local]"
  (fun () ->
    `8 <= i /\ i < dimindex (:'b) ==> ~(FAPPLY ((w2w:word8->'b word)
  w) i)`)
  CHEAT_TAC;;

(* HOL4 miscScript.sml:4351-4353: the ML values that the definitions
   below antiquote *)

let DIV_EQ_DIV_IMP = cake_theorem "DIV_EQ_DIV_IMP[local]"
  (fun () ->
    `0 < d /\ ~(n = n') /\ (n DIV d * d = n' DIV d * d) ==> ~(n MOD d
  = n' MOD d)`)
  CHEAT_TAC;;

let get_byte_set_byte_diff = cake_theorem "get_byte_set_byte_diff"
  (fun () ->
    `good_dimindex (:'a) /\ ~(a = a') /\ (byte_align a = byte_align a')
  ==>
      (get_byte a (set_byte (a':'a word) b w be) be = get_byte a
        w be)`)
  CHEAT_TAC;;

(* helpful theorems for _size *)
let list_size_pair_size_MAP_FST_SND =
  cake_theorem "list_size_pair_size_MAP_FST_SND"
  (fun () ->
    `list_size (pair_size f g) ls =
     list_size f (MAP FST ls) +
     list_size g (MAP SND ls)`)
  CHEAT_TAC;;

let MEM_list_size = cake_theorem "MEM_list_size"
  (fun () ->
    `MEM x ls ==>
     f x <= list_size f ls`)
  CHEAT_TAC;;

(* must be used instead of FUPDATE in defitions that go through translation *)
let fmap_update_def = cake_define
  `fmap_update f k v = f |+ (k,v)`;;

(* TODO: move to HOL? *)
let sum_cmp_def = cake_define
  `sum_cmp c1 c2 x1 x2 =
     (match x1 with INL n1 ->
         (match x2 with INL n2 -> c1 n1 n2 | INR _10 -> LESS) | INR
           n1 ->
         (match x2 with INL _11 -> GREATER | INR n2 -> c2 n1 n2))`;;

let TotOrd_sum = cake_theorem "TotOrd_sum"
  (fun () ->
    `TotOrd c1 /\ TotOrd c2 ==>
     TotOrd (sum_cmp c1 c2)`)
  CHEAT_TAC;;

let TotOrd_num_cmp = cake_theorem "TotOrd_num_cmp"
  (fun () ->
    `TotOrd comparison_num_cmp`)
  CHEAT_TAC;;

(* the shape num_cmp shares with mlint$int_cmp *)
let num_cmp_thm = cake_theorem "num_cmp_thm"
  (fun () ->
    `comparison_num_cmp n1 n2 =
       (if n1 < n2 then LESS else
       if n2 < n1 then GREATER else EQUAL)`)
  CHEAT_TAC;;

let TotOrd_pair_cmp = cake_theorem "TotOrd_pair_cmp"
  (fun () ->
    `TotOrd c1 /\ TotOrd c2 ==>
     TotOrd (pair_compare c1 c2)`)
  CHEAT_TAC;;
