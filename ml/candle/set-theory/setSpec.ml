(* ======================================================== *)
(*  setSpec: ported from HOL4's
    candle/set-theory/setSpecScript.sml
    A definition theory, with 30 definitions and 42 theorems.
    Needed by 10 files of the port.  *)
(* ======================================================== *)

(*
  Specification of (roughly) Zermelo's set theory.
  Two main definitions:
    is_set_theory (mem : 'U -> 'U -> bool), and
    is_model (mem, indset, ch)
*)

needs "lib/cardinal.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "setSpec" [];;

let _ = do_list hide_constant ["One"; "True"; "Unit"];;

(* http://www.lemma-one.com/ProofPower/specs/spc002.pdf *)

let _ = do_list hide_constant ["mem"];;

(* HOL4 setSpecScript.sml:20: the ML values that the definitions below
   antiquote *)
(* HOL4 setSpecScript.sml:23: the overload <:, which the port expands *)

let extensional_def = new_definition
  `extensional (mem':'U->'U->bool) <=> (!x y. x = y <=> (!a. mem' a x <=>
  mem' a y))`;;

let is_separation_def = new_definition
  `is_separation (mem':'U->'U->bool) sub' <=> (!x P. !a. mem' a (sub' x P)
  <=> mem' a x /\ P a)`;;

let is_power_def = new_definition
  `is_power (mem':'U->'U->bool) power' <=> (!x. !a. mem' a (power' x) <=>
  (!b. mem' b a ==> mem' b x))`;;

let is_union_def = new_definition
  `is_union (mem':'U->'U->bool) union' <=> (!x. !a. mem' a (union' x) <=>
  (?b. mem' a b /\ mem' b x))`;;

let is_upair_def = new_definition
  `is_upair (mem':'U->'U->bool) upair' <=> (!x y. !a. mem' a (upair' x y)
  <=> a = x \/ a = y)`;;

let is_set_theory_def = new_definition
  `is_set_theory (mem':'U->'U->bool) <=>
     extensional mem' /\
     (?sub'. is_separation mem' sub') /\
     (?power'. is_power mem' power') /\
     (?union'. is_union mem' union') /\
     (?upair'. is_upair mem' upair')`;;

let separation_unique = prove
 (`extensional (mem:'U->'U->bool) ==>
    (!sub1 sub2. is_separation mem sub1 /\ is_separation mem sub2 ==> sub1
      = sub2)`,
  CHEAT_TAC);;

let power_unique = prove
 (`extensional (mem:'U->'U->bool) ==>
    (!power1 power2. is_power mem power1 /\ is_power mem power2 ==> power1
      = power2)`,
  CHEAT_TAC);;

let union_unique = prove
 (`extensional (mem:'U->'U->bool) ==>
    (!union1 union2. is_union mem union1 /\ is_union mem union2 ==> union1
      = union2)`,
  CHEAT_TAC);;

let upair_unique = prove
 (`extensional (mem:'U->'U->bool) ==>
    (!upair1 upair2. is_upair mem upair1 /\ is_upair mem upair2 ==> upair1
      = upair2)`,
  CHEAT_TAC);;

let setSpec_sub_def = new_definition
  `sub' (mem':'U->'U->bool) = (@sub'. is_separation mem' sub')`;;

let power_def,power_ind = define_guess
  `power' (mem':'U->'U->bool) = (@power'. is_power mem' power')`;;

let setSpec_union_def = new_definition
  `union' (mem':'U->'U->bool) = (@union'. is_union mem' union')`;;

let upair_def,upair_ind = define_guess
  `upair' (mem':'U->'U->bool) = (@upair'. is_upair mem' upair')`;;

let is_extensional = prove
 (`is_set_theory (mem:'U->'U->bool) ==> extensional mem`,
  CHEAT_TAC);;

let is_separation_sub = prove
 (`is_set_theory (mem:'U->'U->bool) ==> is_separation mem (setSpec_sub mem)`,
  CHEAT_TAC);;

let is_power_power = prove
 (`is_set_theory (mem:'U->'U->bool) ==> is_power mem (power mem)`,
  CHEAT_TAC);;

let is_union_union = prove
 (`is_set_theory (mem:'U->'U->bool) ==> is_union mem (setSpec_union mem)`,
  CHEAT_TAC);;

let is_upair_upair = prove
 (`is_set_theory (mem:'U->'U->bool) ==> is_upair mem (upair mem)`,
  CHEAT_TAC);;
(* HOL4 setSpecScript.sml:129: the overload suchthat, which the port expands *)
(* HOL4 setSpecScript.sml:130: the overload Pow, which the port expands *)
(* HOL4 setSpecScript.sml:131: the overload +, which the port expands *)

let mem_sub = prove
 (`is_set_theory (mem:'U->'U->bool) ==> (!x s P. mem:'U->'U->bool x
  (setSpec_sub mem s P) <=> mem:'U->'U->bool x s /\ P x)`,
  CHEAT_TAC);;

let mem_power = prove
 (`is_set_theory (mem:'U->'U->bool) ==>
    (!x y. mem:'U->'U->bool x ((power mem) y) <=> (!b. mem:'U->'U->bool b
      x ==> mem:'U->'U->bool b y))`,
  CHEAT_TAC);;

let mem_union = prove
 (`is_set_theory (mem:'U->'U->bool) ==>
    (!x s. mem:'U->'U->bool x (setSpec_union mem s) <=> (?a.
      mem:'U->'U->bool x a /\ mem:'U->'U->bool a s))`,
  CHEAT_TAC);;

let mem_upair = prove
 (`is_set_theory (mem:'U->'U->bool) ==> (!a x y. mem:'U->'U->bool a (upair
  mem x y) <=> a = x \/ a = y)`,
  CHEAT_TAC);;

let setSpec_empty_def = new_definition
  `setSpec_empty (mem':'U->'U->bool) = setSpec_sub mem' ARB (K F)`;;

(* HOL4 setSpecScript.sml:163: the overload ∅, which the port expands *)

let mem_empty = prove
 (`is_set_theory (mem:'U->'U->bool) ==> (!x. ~(mem:'U->'U->bool x
  (setSpec_empty (mem:'U->'U->bool))))`,
  CHEAT_TAC);;

let setSpec_unit_def = new_definition
  `unit (mem':'U->'U->bool) x = upair mem x x`;;

(* HOL4 setSpecScript.sml:176: the overload Unit, which the port expands *)

let mem_unit = prove
 (`is_set_theory (mem:'U->'U->bool) ==>
    (!x y. mem:'U->'U->bool x ((unit mem) y) <=> x = y)`,
  CHEAT_TAC);;

let unit_inj = prove
 (`is_set_theory (mem:'U->'U->bool) ==>
    (!x y. (unit mem) x = (unit mem) y <=> x = y)`,
  CHEAT_TAC);;

let setSpec_one_def = new_definition
  `setSpec_one (mem':'U->'U->bool) = (unit mem) (setSpec_empty
  (mem':'U->'U->bool))`;;

(* HOL4 setSpecScript.sml:200: the overload One, which the port expands *)

let mem_one = prove
 (`is_set_theory (mem:'U->'U->bool) ==>
    (!x. mem:'U->'U->bool x (setSpec_one mem) <=> x = (setSpec_empty
      (mem:'U->'U->bool)))`,
  CHEAT_TAC);;

let two_def = new_definition
  `two (mem':'U->'U->bool) = upair mem (setSpec_empty (mem':'U->'U->bool))
  (setSpec_one mem)`;;

(* HOL4 setSpecScript.sml:213: the overload Two, which the port expands *)

let mem_two = prove
 (`is_set_theory (mem:'U->'U->bool) ==>
    (!x. mem:'U->'U->bool x (two mem) <=> x = (setSpec_empty
      (mem:'U->'U->bool)) \/ x = (setSpec_one mem))`,
  CHEAT_TAC);;

let pair_def = new_definition
  `setSpec_pair (mem':'U->'U->bool) x y = upair mem ((unit mem) x) (upair
  mem x y)`;;

(* HOL4 setSpecScript.sml:226: the overload ,, which the port expands *)

let upair_inj = prove
 (`is_set_theory (mem:'U->'U->bool) ==>
    (!a b c d. upair mem a b = upair mem c d <=> a = c /\ b = d \/ a = d
      /\ b = c)`,
  CHEAT_TAC);;

let unit_eq_upair = prove
 (`is_set_theory (mem:'U->'U->bool) ==>
    (!x y z. (unit mem) x = upair mem y z <=> x = y /\ y = z)`,
  CHEAT_TAC);;

let pair_inj = prove
 (`is_set_theory (mem:'U->'U->bool) ==>
    (!a b c d. (setSpec_pair mem a b) = (setSpec_pair mem c d) <=> a = c
      /\ b = d)`,
  CHEAT_TAC);;

let binary_union_def = new_definition
  `binary_union (mem':'U->'U->bool) x y = setSpec_union mem' (upair mem' x
  y)`;;

(* HOL4 setSpecScript.sml:261: the overload UNION, which the port expands *)

let mem_binary_union = prove
 (`is_set_theory (mem:'U->'U->bool) ==>
    (!a x y. mem:'U->'U->bool a (binary_union mem x y) <=>
      mem:'U->'U->bool a x \/ mem:'U->'U->bool a y)`,
  CHEAT_TAC);;

let product_def = new_definition
  `setSpec_product (mem':'U->'U->bool) x y =
     (setSpec_sub mem ((power mem) ((power mem) (binary_union mem x y)))
      (\a. ?b c. mem:'U->'U->bool b x /\ mem:'U->'U->bool c y /\ a =
        (setSpec_pair mem b c)))`;;

(* HOL4 setSpecScript.sml:277: the overload CROSS, which the port expands *)

let mem_product = prove
 (`is_set_theory (mem:'U->'U->bool) ==>
    (!a x y. mem:'U->'U->bool a (x * y) <=> (?b c. a = (setSpec_pair mem b
      c) /\ mem:'U->'U->bool b x /\ mem:'U->'U->bool c y))`,
  CHEAT_TAC);;

let relspace_def = new_definition
  `relspace (mem':'U->'U->bool) x y = (power mem) (x * y)`;;

(* HOL4 setSpecScript.sml:294: the overload Relspace, which the port expands *)

let funspace_def = new_definition
  `funspace (mem':'U->'U->bool) x y =
     (setSpec_sub mem ((relspace mem) x y)
      (\f. !a. mem:'U->'U->bool a x ==> (?!b. mem:'U->'U->bool
        (setSpec_pair mem a b) f)))`;;

(* HOL4 setSpecScript.sml:302: the overload Funspace, which the port expands *)

let apply_def = new_definition
  `apply (mem':'U->'U->bool) x y = (@a. mem:'U->'U->bool (setSpec_pair mem y
  a) x)`;;
(* HOL4 setSpecScript.sml:309: the overload ', which the port expands *)

(* HOL4 setSpecScript.sml:311: the overload boolset, which the port expands *)

let true_def = new_definition
  `setSpec_true (mem':'U->'U->bool) = (setSpec_empty (mem':'U->'U->bool))`;;

let false_def = new_definition
  `setSpec_false (mem':'U->'U->bool) = (setSpec_one mem)`;;

(* HOL4 setSpecScript.sml:321: the overload True, which the port expands *)
(* HOL4 setSpecScript.sml:322: the overload False, which the port expands *)

let true_neq_false = prove
 (`is_set_theory (mem:'U->'U->bool) ==> ~((setSpec_true mem) = (setSpec_false
  mem))`,
  CHEAT_TAC);;

let mem_boolset = prove
 (`is_set_theory (mem:'U->'U->bool) ==>
    (!x. mem:'U->'U->bool x ((two mem)) <=> ((x = (setSpec_true mem)) \/
      (x = (setSpec_false mem))))`,
  CHEAT_TAC);;

let boolean_def = new_definition
  `boolean (mem':'U->'U->bool) b = if b then (setSpec_true mem) else
  (setSpec_false mem)`;;

(* HOL4 setSpecScript.sml:345: the overload Boolean, which the port expands *)

let boolean_in_boolset = prove
 (`is_set_theory (mem:'U->'U->bool) ==>
    (!b. mem:'U->'U->bool ((boolean mem) b) ((two mem)))`,
  CHEAT_TAC);;

let boolean_eq_true = prove
 (`is_set_theory (mem:'U->'U->bool) ==> (!b. (boolean mem) b = (setSpec_true
  mem) <=> b)`,
  CHEAT_TAC);;

let holds_def = new_definition
  `holds (mem':'U->'U->bool) s x <=> apply mem s x = (setSpec_true mem)`;;

(* HOL4 setSpecScript.sml:365: the overload Holds, which the port expands *)

let abstract_def = new_definition
  `abstract (mem':'U->'U->bool) dom rng f = (setSpec_sub mem (dom * rng)
  (\x. ?a. x = (setSpec_pair mem a (f a))))`;;

(* HOL4 setSpecScript.sml:371: the overload Abstract, which the port expands *)

let apply_abstract = prove
 (`is_set_theory (mem:'U->'U->bool) ==>
    (!f x s t. mem:'U->'U->bool x s /\ mem:'U->'U->bool (f x) t ==> apply
      mem ((abstract mem) s t f) x = f x)`,
  CHEAT_TAC);;

let apply_abstract_matchable = prove
 (`!f x s t u. mem:'U->'U->bool x s /\ mem:'U->'U->bool (f x) t
  /\ is_set_theory (mem:'U->'U->bool) /\ f x = u ==> apply mem ((abstract
  mem) s t f) x = u`,
  CHEAT_TAC);;

let apply_in_rng = prove
 (`is_set_theory (mem:'U->'U->bool) ==>
    (!f x s t. mem:'U->'U->bool x s /\ mem:'U->'U->bool f ((funspace mem)
      s t) ==> mem:'U->'U->bool (apply mem f x) t)`,
  CHEAT_TAC);;

let abstract_in_funspace = prove
 (`is_set_theory (mem:'U->'U->bool) ==>
    (!f s t. (!x. mem:'U->'U->bool x s ==> mem:'U->'U->bool (f x) t) ==>
      mem:'U->'U->bool ((abstract mem) s t f) ((funspace mem) s t))`,
  CHEAT_TAC);;

let abstract_in_funspace_matchable = prove
 (`is_set_theory (mem:'U->'U->bool) ==>
    (!f s t fs. (!x. mem:'U->'U->bool x s ==> mem:'U->'U->bool (f x) t)
      /\ fs = (funspace mem) s t ==> mem:'U->'U->bool ((abstract mem) s t f)
      fs)`,
  CHEAT_TAC);;

let abstract_eq = prove
 (`is_set_theory (mem:'U->'U->bool) ==>
    (!s t1 t2 f g.
    (!x. mem:'U->'U->bool x s ==> mem:'U->'U->bool (f x) t1
      /\ mem:'U->'U->bool (g x) t2 /\ f x = g x) ==> (abstract mem) s t1 f =
      (abstract mem) s t2 g)`,
  CHEAT_TAC);;

let in_funspace_abstract = prove
 (`is_set_theory (mem:'U->'U->bool) ==>
    (!z s t. mem:'U->'U->bool z ((funspace mem) s t) ==>
    (?f. z = (abstract mem) s t f /\ (!x. mem:'U->'U->bool x s ==>
      mem:'U->'U->bool (f x) t)))`,
  CHEAT_TAC);;

(* HOL4 setSpecScript.sml:452-467: a theorem that HOL4 states as the value
   of an ML expression: axiom_of_choice *)

(* HOL4 setSpecScript.sml:469-471: the ML values that the definitions below
   antiquote *)

(* HOL4 setSpecScript.sml:473: the overload M, which the port expands *)

let is_choice_def = new_definition
  `is_choice (mem':'U->'U->bool) ch = (!x. (?a. mem:'U->'U->bool a x) ==>
  mem:'U->'U->bool (ch x) x)`;;

let is_infinite_def = new_definition
  `is_infinite (mem':'U->'U->bool) s = INFINITE {a | mem:'U->'U->bool a s}`;;

let is_model_def = new_definition
  `is_model (setSpec_pair mem (mem':'U->'U->bool) (setSpec_pair mem (indset:'U)
  (ch:'U->'U))) <=>
     is_set_theory mem' /\
     is_infinite mem' indset /\
     is_choice mem' ch`;;

let is_model_is_set_theory = prove
 (`is_model ((mem,indset,ch)) ==> is_set_theory (mem:'U->'U->bool)`,
  CHEAT_TAC);;

let indset_inhabited = prove
 (`is_infinite (mem:'U->'U->bool) indset ==> (?i. mem:'U->'U->bool i indset)`,
  CHEAT_TAC);;

let funspace_inhabited = prove
 (`is_set_theory (mem:'U->'U->bool) ==> (!s t. (?x. mem:'U->'U->bool x s)
  /\ (?x. mem:'U->'U->bool x t) ==> (?f. mem:'U->'U->bool f ((funspace mem) s
  t)))`,
  CHEAT_TAC);;

let tuple_def,tuple_ind = define_guess
  `(tuple0 (mem':'U->'U->bool) [] = {}) /\
   (tuple0 (mem':'U->'U->bool) (CONS a as) = (setSpec_pair mem a (tuple0
    (mem':'U->'U->bool) as)))`;;
(* HOL4 setSpecScript.sml:515: the overload tuple, which the port expands *)

let pair_not_empty = prove
 (`is_set_theory (mem:'U->'U->bool) ==> ~((setSpec_pair mem x y) =
  (setSpec_empty (mem:'U->'U->bool)))`,
  CHEAT_TAC);;

let tuple_empty = prove
 (`is_set_theory (mem:'U->'U->bool) ==> (!ls. (tuple0 mem) ls =
  (setSpec_empty (mem:'U->'U->bool)) <=> ls = [])`,
  CHEAT_TAC);;

let tuple_inj = prove
 (`is_set_theory (mem:'U->'U->bool) ==>
    (!l1 l2. (tuple0 mem) l1 = (tuple0 mem) l2 <=> l1 = l2)`,
  CHEAT_TAC);;

let bigcross_def,bigcross_ind = define_guess
  `(bigcross0 (mem':'U->'U->bool) [] = (setSpec_one mem)) /\
   (bigcross0 (mem':'U->'U->bool) (CONS a as) = a * (bigcross0
    (mem':'U->'U->bool) as))`;;
(* HOL4 setSpecScript.sml:549: the overload bigcross, which the port expands *)

let mem_bigcross = prove
 (`is_set_theory (mem:'U->'U->bool) ==>
    (!ls x. (mem x ((bigcross0 mem) ls) <=> (?xs. x = (tuple0 mem) xs
      /\ ALL2 mem xs ls)))`,
  CHEAT_TAC);;

(* and the names it reads as variables are constants again *)
let _ = do_list unhide_constant
  ["One";
   "True";
   "Unit";
   "mem"];;

(* and the interface *)
let _ = unhide_overloads ();;
