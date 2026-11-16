(* ======================================================== *)
(*  ListProg: ported from HOL4's
    basis/ListProgScript.sml
    A definition theory, with 7 definitions and 23 theorems.  Needed
    by VectorProg.ml.  *)
(* ======================================================== *)

(*
  Module about the built-in list type.
*)

needs "basis/OptionProg.ml";;
needs "basis/pure/mllist.ml";;
needs "lib/mergesort.ml";;
needs "translator/ml_translator.ml";;
needs "translator/std_prelude.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "ListProg"
  ["OptionProg"; "cf"; "ml_prog"; "ml_translator"; "mllist"; "std_prelude"];;

let _ = do_list hide_constant ["fv"];;

(* HOL4 ListProgScript.sml:10: ML code, not ported *)

(* HOL4 ListProgScript.sml:12: ML code, not ported *)

(* HOL4 ListProgScript.sml:14: ML code, not ported *)

(* HOL4 ListProgScript.sml:16-17: ML code, not ported *)

(* HOL4 ListProgScript.sml:19: ML code, not ported *)

(* HOL4 ListProgScript.sml:21-23: ML code, not ported *)

(* HOL4 ListProgScript.sml:25-26: ML code, not ported *)

(* HOL4 ListProgScript.sml:28-33: ML code, not ported *)

(* HOL4 ListProgScript.sml:35-42: ML code, not ported *)

(* New list-append translation *)
(* HOL4 ListProgScript.sml:45: ML code, not ported *)
(* HOL4 ListProgScript.sml:46-47: a theorem that HOL4 states as the value of
   an ML expression: append_v_thm *)

(* Old list-append translation *)
(* HOL4 ListProgScript.sml:50: code that the source has in a comment *)
(* Theorem append_v_thm = append_v_thm *)

(* HOL4 ListProgScript.sml:53-57: a theorem that HOL4 states as the value of
   an ML expression: hd_side_def *)

(* HOL4 ListProgScript.sml:59: ML code, not ported *)

(* HOL4 ListProgScript.sml:61: ML code, not ported *)

(* HOL4 ListProgScript.sml:63-64: ML code, not ported *)

(* [local] *)
let nth_thm = prove
 (`mllist_nth l 0 = HD l /\
   mllist_nth l (SUC n) = mllist_nth (TL l) n`,
  CHEAT_TAC);;

(* HOL4 ListProgScript.sml:73-74: ML code, not ported *)

(* HOL4 ListProgScript.sml:76-77: ML code, not ported *)

(* HOL4 ListProgScript.sml:79-81: ML code, not ported *)

(* HOL4 ListProgScript.sml:83-84: ML code, not ported *)

(* HOL4 ListProgScript.sml:86-87: ML code, not ported *)

(* HOL4 ListProgScript.sml:89-90: ML code, not ported *)

(* the let is introduced to produce slight better code (smaller stack frames) *)
(* [local] *)
let MAP_let = prove
 (`MAP f xs =
   match xs with [] -> []
   | (CONS y ys) -> let z = f y in CONS z (MAP f ys)`,
  CHEAT_TAC);;

let MAP_ind = prove
 (`!P. (!f xs. (!y ys z. xs = CONS y ys /\ z = f y ==> P f ys) ==> P f xs) ==>
       (!f xs. P f xs)`,
  CHEAT_TAC);;

(* HOL4 ListProgScript.sml:109: ML code, not ported *)

(* HOL4 ListProgScript.sml:111-112: ML code, not ported *)

(* HOL4 ListProgScript.sml:114-116: ML code, not ported *)

(* HOL4 ListProgScript.sml:118-120: ML code, not ported *)

(* HOL4 ListProgScript.sml:122-125: ML code, not ported *)

(* HOL4 ListProgScript.sml:127: ML code, not ported *)

(* HOL4 ListProgScript.sml:129: ML code, not ported *)

(* HOL4 ListProgScript.sml:131-133: ML code, not ported *)

(* HOL4 ListProgScript.sml:135-136: ML code, not ported *)

(* HOL4 ListProgScript.sml:138: ML code, not ported *)

(* HOL4 ListProgScript.sml:140-142: ML code, not ported *)

(* HOL4 ListProgScript.sml:144-145: ML code, not ported *)

(* HOL4 ListProgScript.sml:147-149: ML code, not ported *)

(* HOL4 ListProgScript.sml:151: ML code, not ported *)

(* HOL4 ListProgScript.sml:153-154: ML code, not ported *)

(* HOL4 ListProgScript.sml:156: ML code, not ported *)

(* HOL4 ListProgScript.sml:158: ML code, not ported *)

(* HOL4 ListProgScript.sml:160: ML code, not ported *)

(* HOL4 ListProgScript.sml:162: ML code, not ported *)

(* HOL4 ListProgScript.sml:164-165: ML code, not ported *)

(* HOL4 ListProgScript.sml:167-168: ML code, not ported *)

(* HOL4 ListProgScript.sml:170-172: ML code, not ported *)
(* HOL4 ListProgScript.sml:173-217: a theorem whose statement the port
   cannot state yet: tabulate_aux_inv_spec *)
(* HOL4 ListProgScript.sml:218: ML code, not ported *)

(* HOL4 ListProgScript.sml:220-221: ML code, not ported *)

(* HOL4 ListProgScript.sml:223-225: ML code, not ported *)
(* HOL4 ListProgScript.sml:226-241: a theorem whose statement the port
   cannot state yet: tabulate_inv_spec *)
(* HOL4 ListProgScript.sml:242: ML code, not ported *)

(* HOL4 ListProgScript.sml:244: ML code, not ported *)

let ZIP_ind = prove
 (`!P. (!v. (!x4 x3 x2 x1. v = (CONS x4 x3,CONS x2 x1) ==> P (x3,x1)) ==> P
  v) ==> (!v. P v)`,
  CHEAT_TAC);;

let ZIP_eq = prove
 (`UNCURRY ZIP x =
     match x with (CONS x xs,CONS y ys) -> CONS (x,y) (ZIP xs ys)
     | _ -> []`,
  CHEAT_TAC);;

(* HOL4 ListProgScript.sml:262: ML code, not ported *)

(* HOL4 ListProgScript.sml:264: ML code, not ported *)

(* HOL4 ListProgScript.sml:266: ML code, not ported *)

let UNZIP_eq = prove
 (`!xs.
     UNZIP xs =
       match xs with
         [] -> ([],[])
       | CONS (y,z) xs ->
           let (ys,zs) = UNZIP xs in
             (CONS y ys,CONS z zs)`,
  CHEAT_TAC);;

let UNZIP_ind = prove
 (`!P. (!v. (!x4 x3. v = CONS x4 x3 ==> (!x2 x1. x4 = (x2,x1) ==> P x3)) ==>
  P v) ==> (!v. P v)`,
  CHEAT_TAC);;

(* HOL4 ListProgScript.sml:288: ML code, not ported *)

(* HOL4 ListProgScript.sml:290-295: ML code, not ported *)

(* HOL4 ListProgScript.sml:297-298: ML code, not ported *)

(* [local] *)
let SPLITP_alt = prove
 (`SPLITP P [] = ([],[]) /\
   SPLITP P (CONS x l) =
   (if P x then ([],CONS x l) else let (l',l'') = SPLITP P l in
       (CONS x l',l''))`,
  CHEAT_TAC);;
(* HOL4 ListProgScript.sml:309-310: ML code, not ported *)

(* HOL4 ListProgScript.sml:312-316: a theorem that HOL4 states as the value
   of an ML expression: last_side_def *)

(* HOL4 ListProgScript.sml:318-322: a theorem that HOL4 states as the value
   of an ML expression: nth_side_def *)

let LUPDATE_ind = prove
 (`!P. (!e n. P e n []) /\ (!e n x xs. (!e n. P e n xs) ==> P e n (CONS x
  xs)) ==> (!e n xs. P e n xs)`,
  CHEAT_TAC);;

let LUPDATE_eq = prove
 (`LUPDATE e n xs =
     match xs with [] -> []
     | CONS y ys -> if n = 0 then CONS e ys else CONS y (LUPDATE e (n - 1)
       ys)`,
  CHEAT_TAC);;

(* HOL4 ListProgScript.sml:339-340: ML code, not ported *)

(* HOL4 ListProgScript.sml:342-343: ML code, not ported *)

(* HOL4 ListProgScript.sml:345: ML code, not ported *)

(* HOL4 ListProgScript.sml:347-353: ML code, not ported *)

(* [local] *)
let mergesortn_tail_ind = prove
 (`mergesortn_tail_ind (:'a)`,
  CHEAT_TAC);;

(* HOL4 ListProgScript.sml:368: ML code, not ported *)

(* [local] *)
let mergesortn_tail_side = prove
 (`!w x y z. mergesortn_tail_side w x y z`,
  CHEAT_TAC);;

(* HOL4 ListProgScript.sml:392-393: ML code, not ported *)

(* HOL4 ListProgScript.sml:395: ML code, not ported *)

(* HOL4 ListProgScript.sml:397: ML code, not ported *)

(* HOL4 ListProgScript.sml:399: ML code, not ported *)

(* HOL4 ListProgScript.sml:401-402: ML code, not ported *)

(* finite maps -- depend on lists *)

(* HOL4 ListProgScript.sml:406: ML code, not ported *)

let FMAP_EQ_ALIST_def = new_definition
  `FMAP_EQ_ALIST f l <=> (ALOOKUP l = FLOOKUP f)`;;

let FMAP_TYPE_def = new_definition
  `ListProg_FMAP_TYPE (a:'a->semanticPrimitives_v->bool)
  (b:'b->semanticPrimitives_v->bool) (f:('a,'b)fmap) =
     (\v. ?l. LIST_TYPE (PAIR_TYPE a b) l v /\ FMAP_EQ_ALIST f l)`;;

(* HOL4 ListProgScript.sml:417-418: the ML values that the definitions below
   antiquote *)

(* HOL4 ListProgScript.sml:420-421: ML code, not ported *)

(* HOL4 ListProgScript.sml:423-430: a theorem that HOL4 states as the value
   of an ML expression: Eval_FLOOKUP *)

(* HOL4 ListProgScript.sml:432: ML code, not ported *)
let AUPDATE_def = new_definition
  `AUPDATE l ((x:'a),(y:'b)) = CONS (x,y) l`;;
(* HOL4 ListProgScript.sml:436: ML code, not ported *)

(* [local] *)
let FMAP_EQ_ALIST_UPDATE = prove
 (`FMAP_EQ_ALIST f l ==> FMAP_EQ_ALIST (FUPDATE f (x,y)) (AUPDATE l (x,y))`,
  CHEAT_TAC);;

(* HOL4 ListProgScript.sml:446-455: a theorem that HOL4 states as the value
   of an ML expression: Eval_FUPDATE *)

(* HOL4 ListProgScript.sml:457: the ML values that the definitions below
   antiquote *)

(* HOL4 ListProgScript.sml:459-467: a theorem that HOL4 states as the value
   of an ML expression: Eval_FEMPTY *)

let AEVERY_AUX_def,AEVERY_AUX_ind = define_guess
  `(AEVERY_AUX aux P [] = T) /\
   (AEVERY_AUX aux P (CONS ((x:'a),(y:'b)) xs) =
         if MEMBER x aux then AEVERY_AUX aux P xs else P (x,y)
             /\ AEVERY_AUX (CONS x aux) P xs)`;;
let AEVERY_def = new_definition
  `AEVERY = AEVERY_AUX []`;;
(* HOL4 ListProgScript.sml:478-480: ML code, not ported *)

(* [local] *)
let AEVERY_AUX_THM = prove
 (`!l aux P. AEVERY_AUX aux P l <=>
               (!x y. (ALOOKUP l x = SOME y) /\ ~(MEM x aux) ==> P (x,y))`,
  CHEAT_TAC);;

(* [local] *)
let AEVERY_THM = prove
 (`AEVERY P l <=> (!x y. (ALOOKUP l x = SOME y) ==> P (x,y))`,
  CHEAT_TAC);;

(* [local] *)
let AEVERY_EQ_FEVERY = prove
 (`FMAP_EQ_ALIST f l ==> (AEVERY P l <=> FEVERY P f)`,
  CHEAT_TAC);;

(* HOL4 ListProgScript.sml:505-515: a theorem that HOL4 states as the value
   of an ML expression: Eval_FEVERY *)

(* HOL4 ListProgScript.sml:517: ML code, not ported *)
let AMAP_def,AMAP_ind = define_guess
  `(AMAP f [] = []) /\
   (AMAP f (CONS ((x:'a),(y:'b)) xs) = CONS (x,((f y):'c)) (AMAP f xs))`;;
(* HOL4 ListProgScript.sml:522: ML code, not ported *)

(* [local] *)
let ALOOKUP_AMAP = prove
 (`!l. ALOOKUP (AMAP f l) a =
         match ALOOKUP l a with NONE -> NONE | SOME x -> SOME (f x)`,
  CHEAT_TAC);;

(* [local] *)
let FMAP_EQ_ALIST_o_f = prove
 (`FMAP_EQ_ALIST m l ==> FMAP_EQ_ALIST (x o_f m) (AMAP x l)`,
  CHEAT_TAC);;

(* HOL4 ListProgScript.sml:539-548: a theorem that HOL4 states as the value
   of an ML expression: Eval_o_f *)

(* TODO: quick fix on account of hol2deep not accepting ``$++`` *)
(* HOL4 ListProgScript.sml:551-561: the ML values that the definitions below
   antiquote *)

(* HOL4 ListProgScript.sml:563-577: a theorem that HOL4 states as the value
   of an ML expression: Eval_FUNION *)

(* HOL4 ListProgScript.sml:579: ML code, not ported *)
let ADEL_def,ADEL_ind = define_guess
  `(ADEL [] z = []) /\
   (ADEL (CONS ((x:'a),(y:'b)) xs) z = if x = z then ADEL xs z else CONS
    (x,y) (ADEL xs z))`;;
(* HOL4 ListProgScript.sml:584: ML code, not ported *)

(* [local] *)
let ALOOKUP_ADEL = prove
 (`!l a x. ALOOKUP (ADEL l a) x = if x = a then NONE else ALOOKUP l x`,
  CHEAT_TAC);;

(* [local] *)
let FMAP_EQ_ALIST_ADEL = prove
 (`!x l. FMAP_EQ_ALIST x l ==>
           FMAP_EQ_ALIST (x \\ a) (ADEL l a)`,
  CHEAT_TAC);;

(* HOL4 ListProgScript.sml:602-610: a theorem that HOL4 states as the value
   of an ML expression: Eval_fmap_domsub *)

(* HOL4 ListProgScript.sml:612: ML code, not ported *)

(* and the names it reads as variables are constants again *)
let _ = do_list unhide_constant
  ["fv"];;

(* and the interface *)
let _ = unhide_overloads ();;
