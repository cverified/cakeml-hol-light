(* ================================================================== *)
(*  Finite maps, which HOL Light does not have.                       *)
(*                                                                    *)
(*  The same notion as HOL4's finite_mapTheory: a finite map is a     *)
(*  function                                                          *)
(*  to an option type with a finite domain. The definitions below are *)
(*  the                                                               *)
(*  HOL4 ones, phrased with the representing function.                *)
(* ================================================================== *)

let fmap_tybij =
  let th = prove
   (`?f:A->B option. FINITE {x | ~(f x = NONE)}`,
    EXISTS_TAC `\x:A. (NONE:B option)` THEN
    REWRITE_TAC[EMPTY_GSPEC; FINITE_EMPTY]) in
  new_type_definition "fmap" ("mk_fmap","fmap_fn") th;;

(* the domain, the application and the lookup of a finite map *)

let FDOM = new_definition
  `FDOM (fm:(A,B)fmap) = {x | ~(fmap_fn fm x = NONE)}`;;

(* HOL4 writes the application of a finite map as fm ' x, and the
   bit of a word as w ' i; the port writes both as FAPPLY, which
   is therefore overloaded (the word one is in ml/lib/words4.ml) *)

let fmap_apply = new_definition
  `fmap_apply (fm:(A,B)fmap) x = THE (fmap_fn fm x)`;;

make_overloadable "FAPPLY" `:A->B->C`;;
overload_interface("FAPPLY",`fmap_apply:(A,B)fmap->A->B`);;
overload_interface("FAPPLY",`word_index:(N)word->num->bool`);;

let FAPPLY = fmap_apply;;

let FLOOKUP = new_definition
  `FLOOKUP (fm:(A,B)fmap) x = fmap_fn fm x`;;

(* the empty map and the update, which HOL4 writes fm |+ (k,v) *)

let FEMPTY = new_definition
  `FEMPTY = mk_fmap (\x:A. (NONE:B option))`;;

parse_as_infix("|+",(15,"left"));;

let FUPDATE = new_definition
  `(fm:(A,B)fmap) |+ (kv:A#B) =
   mk_fmap (\x. if x = FST kv then SOME (SND kv) else fmap_fn fm x)`;;

parse_as_infix("|++",(15,"left"));;

let FUPDATE_LIST = new_definition
  `(fm:(A,B)fmap) |++ l = FOLDL (|+) fm l`;;

(* removing a key, which HOL4 writes fm \\ k *)

(* HOL4 writes this fold as FUPDATE_LIST as well *)
override_interface("FUPDATE_LIST",
  `(|++):(A,B)fmap->(A#B)list->(A,B)fmap`);;

parse_as_infix("\\\\",(21,"left"));;

let DOMSUB = new_definition
  `(fm:(A,B)fmap) \\ k =
   mk_fmap (\x. if x = k then NONE else fmap_fn fm x)`;;

(* the union of two finite maps, which takes the first one first *)

let FUNION = new_definition
  `FUNION (f:(A,B)fmap) g =
   mk_fmap (\x. if x IN FDOM f then fmap_fn f x else fmap_fn g x)`;;

let FDIFF = new_definition
  `FDIFF (f:(A,B)fmap) s =
   mk_fmap (\x. if x IN s then NONE else fmap_fn f x)`;;

let DRESTRICT = new_definition
  `DRESTRICT (f:(A,B)fmap) s =
   mk_fmap (\x. if x IN s then fmap_fn f x else NONE)`;;

let FRANGE = new_definition
  `FRANGE (f:(A,B)fmap) = {v | ?k. fmap_fn f k = SOME v}`;;

(* the map of the values, which HOL4 writes g o_f fm *)

parse_as_infix("o_f",(26,"right"));;

let o_f = new_definition
  `(g:B->C) o_f (fm:(A,B)fmap) = mk_fmap (\x. OPTION_MAP g (fmap_fn fm
    x))`;;

let FMERGE = new_definition
  `FMERGE (m:B->B->B) (f:(A,B)fmap) g =
   mk_fmap (\x. if x IN FDOM f then
                  (if x IN FDOM g then SOME (m (FAPPLY f x) (FAPPLY g
                    x))
                   else fmap_fn f x)
                else fmap_fn g x)`;;

let FUN_FMAP = new_definition
  `FUN_FMAP (f:A->B) s = mk_fmap (\x. if x IN s then SOME (f x) else
    NONE)`;;

(* the map of the keys (HOL4 gives MAP_KEYS by a specification, of
   which this is the witness that finite_mapTheory proves) *)

let MAP_KEYS = new_definition
  `MAP_KEYS (f:A->B) (fm:(A,C)fmap) =
   mk_fmap (\y. if y IN IMAGE f (FDOM fm)
                then (if INJ f (FDOM fm) UNIV
                      then fmap_fn fm (LINV f (FDOM fm) y)
                      else SOME ARB)
                else NONE)`;;

let FCARD = new_definition
  `FCARD (fm:(A,B)fmap) = CARD (FDOM fm)`;;

let FEVERY = new_definition
  `FEVERY P (fm:(A,B)fmap) <=>
   !k v. FLOOKUP fm k = SOME v ==> P (k,v)`;;

parse_as_infix("SUBMAP",(12,"right"));;

let SUBMAP = new_definition
  `(f:(A,B)fmap) SUBMAP g <=>
   !x. x IN FDOM f ==> x IN FDOM g /\ FAPPLY f x = FAPPLY g x`;;

(* folding over a finite map (HOL4's ITFMAP of finite_mapTheory,
   named by analogy with ITSET): the relation that says what a
   fold of a map gives, and the fold itself, which is a value
   that the relation gives (for a function whose applications
   commute there is exactly one) *)

let ITFMAPR_RULES,ITFMAPR_INDUCT,ITFMAPR_CASES =
  new_inductive_definition
  `(!a. ITFMAPR (f:A->B->C->C) FEMPTY a a) /\
   (!a1 a2 k v fm.
      ~(k IN FDOM fm) /\ ITFMAPR f fm a1 a2
      ==> ITFMAPR f (fm |+ (k,v)) a1 (f k v a2))`;;

let ITFMAP = new_definition
  `ITFMAP (f:A->B->C->C) fm a0 = @a. ITFMAPR f fm a0 a`;;

(* the finite map of an association list, and back *)

let alist_to_fmap = new_definition
  `alist_to_fmap (l:(A#B)list) = ITLIST (\kv fm. fm |+ kv) l FEMPTY`;;

let fmap_to_alist = new_definition
  `fmap_to_alist (fm:(A,B)fmap) =
   MAP (\k. (k,FAPPLY fm k)) (list_of_set (FDOM fm))`;;

let fmap_size = new_definition
  `fmap_size (f:A->num) (g:B->num) (fm:(A,B)fmap) =
   CARD (FDOM fm) +
   ITLIST (\kv n. f (FST kv) + g (SND kv) + n) (fmap_to_alist fm) 0`;;
