(* ======================================================== *)
(*  cfLetAuto: ported from HOL4's
    characteristic/cfLetAutoScript.sml
    A definition theory, with 4 definitions and 72 theorems.  Needed
    by CommandLineProof.ml, RuntimeProof.ml and TextIOProof.ml.  *)
(* ======================================================== *)

(*
  Definitions and lemmas that support the implementation of the
  xlet_auto tactic.
*)

needs "basis/pure/mlstring.ml";;
needs "characteristic/cfFFIType.ml";;
needs "characteristic/cfHeapsBase.ml";;
needs "characteristic/cfStore.ml";;
needs "lib/set_sep.ml";;
needs "translator/ml_translator.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "cfLetAuto"
  ["cfHeapsBase"; "cfStore"; "cfTactics"; "ml_translator"];;

(* Rewrite rules for the int_of_num & operator*)
(* INT_OF_NUM_ADD *)
let cfLetAuto_INT_OF_NUM_ADD = prove
 (`!(x:num) (y:num). (&x) + &y = &(x + y)`,
  CHEAT_TAC);;
let INT_OF_NUM_TIMES = prove
 (`!(x:num) (y:num). (&x) * &y = &(x * y)`,
  CHEAT_TAC);;
(* INT_OF_NUM_LE *)
let cfLetAuto_INT_OF_NUM_LE = prove
 (`!(x:num) (y:num). (&x <= ((&y):int)) = (x <= y)`,
  CHEAT_TAC);;
let INT_OF_NUM_LESS = prove
 (`!(x:num) (y:num). (&x < ((&y):int)) = (x < y)`,
  CHEAT_TAC);;
(* INT_OF_NUM_GE *)
let cfLetAuto_INT_OF_NUM_GE = prove
 (`!(x:num) (y:num). (&x >= ((&y):int)) = (x >= y)`,
  CHEAT_TAC);;
let INT_OF_NUM_GREAT = prove
 (`!(x:num) (y:num). (&x > ((&y):int)) = (x > y)`,
  CHEAT_TAC);;
(* INT_OF_NUM_EQ *)
let cfLetAuto_INT_OF_NUM_EQ = prove
 (`!(x:num) (y:num). (&x = ((&y):int)) = (x = y)`,
  CHEAT_TAC);;
let INT_OF_NUM_SUBS = prove
 (`!(x:num) (y:num) (z:num). (&x - ((&y):int) = &z) <=> (x - y = z) /\ y <= x`,
  CHEAT_TAC);;
let INT_OF_NUM_SUBS_2 = prove
 (`!(x:num) (y:num). y <= x ==> (&x - ((&y):int) = &(x - y))`,
  CHEAT_TAC);;

(* TODO: move that *)
let SPLIT_SUBSET = prove
 (`SPLIT s (u,v) ==> u SUBSET s /\ v SUBSET s`,
  CHEAT_TAC);;

(* Predicate stating that a heap is valid *)
let HEAP_FROM_STATE_def = new_definition
  `HEAP_FROM_STATE s = (?(f:(ffi->(mlstring,ffi)fmap)#(mlstring
  list#(mlstring->word8 list->word8 list->ffi->(ffi cfHeapsBase_ffi_result)
  option)) list) st. s = (st2heap f st))`;;

let VALID_HEAP_def = new_definition
  `VALID_HEAP s = (?(f:(ffi->(mlstring,ffi)fmap)#(mlstring
  list#(mlstring->word8 list->word8 list->ffi->(ffi cfHeapsBase_ffi_result)
  option)) list) st. s SUBSET (st2heap f st))`;;

let VALID_HEAP_SUBSET = prove
 (`VALID_HEAP s1 ==> s2 SUBSET s1 ==> VALID_HEAP s2`,
  CHEAT_TAC);;

(* A theorem to remove the pure facts from the heap predicates *)
let HCOND_EXTRACT = prove
 (`((&A * H) s <=> A /\ H s) /\ ((H * &A) s <=> H s /\ A) /\ ((H * &A * H') s
  <=> (H * H') s /\ A)`,
  CHEAT_TAC);;

(* Definitions and theorems used to compare two heap conditions *)
let HPROP_INJ_def = new_definition
  `HPROP_INJ H1 H2 PF <=>
   (!s. VALID_HEAP s ==> (!G1 G2. (H1 * G1) s ==> ((H2 * G2) s <=> (&PF *
     H1 * G2) s)))`;;

(* TODO: use that *)
(* HOL4 cfLetAutoScript.sml:96-106: code that the source has in a comment *)

(* The following lemmas aim to prove that a valid heap can not have one pointer pointing to two different values *)
(* [local] *)
let PTR_MEM_LEM = prove
 (`!s l xv H. (cell l xv * H) s ==> cfHeapsBase_Mem l xv IN s`,
  CHEAT_TAC);;

(* Intermediate lemma to reason on subsets of heaps *)
(* [local] *)
let HEAP_SUBSET_GC = prove
 (`!s s' H. s SUBSET s' ==> H s ==> (H * GC) s'`,
  CHEAT_TAC);;

(* UNIQUE_PTRS property for a heap converted from a state *)
(* [local] *)
let UNIQUE_PTRS_HFS = prove
 (`!s. HEAP_FROM_STATE s ==> (!l xv xv' H H'. (cell l xv * H) s /\ (cell l
  xv' * H') s ==> xv' = xv)`,
  CHEAT_TAC);;

let UNIQUE_PTRS = prove
 (`!s. VALID_HEAP s ==> (!l xv xv' H H'. (cell l xv * H) s /\ (cell l xv' *
  H') s ==> xv' = xv)`,
  CHEAT_TAC);;

let PTR_IN_HEAP = prove
 (`!l xv H s. (REF (semanticPrimitives_Loc T l) xv * H) s ==> cfHeapsBase_Mem
  l (semanticPrimitives_Refv xv) IN s`,
  CHEAT_TAC);;

(* HOL4 cfLetAutoScript.sml:158-159: a proof *)

let PTR_HPROP_INJ = prove
 (`!l xv xv'. HPROP_INJ (cell l xv) (cell l xv') (xv' = xv)`,
  CHEAT_TAC);;

(* Unicity results for pointers *)
(* HOL4 cfLetAutoScript.sml:168-171: a proof *)

let UNIQUE_REFS = prove
 (`!s r xv xv' H H'. VALID_HEAP s ==> (REF r xv * H) s /\ (REF r xv' * H') s
  ==> xv' = xv`,
  CHEAT_TAC);;

let UNIQUE_ARRAYS = prove
 (`!s a av av' H H'. VALID_HEAP s ==> (ARRAY a av * H) s /\ (ARRAY a av' *
  H') s ==> av' = av`,
  CHEAT_TAC);;

let UNIQUE_W8ARRAYS = prove
 (`!s a av av' H H'. VALID_HEAP s ==> (W8ARRAY a av * H) s /\ (W8ARRAY a av'
  * H') s ==> av' = av`,
  CHEAT_TAC);;

let REF_HPROP_INJ = prove
 (`!r xv xv'. HPROP_INJ (REF r xv) (REF r xv') (xv' = xv)`,
  CHEAT_TAC);;

let ARRAY_HPROP_INJ = prove
 (`!a av av'. HPROP_INJ (ARRAY a av) (ARRAY a av') (av' = av)`,
  CHEAT_TAC);;

let W8ARRAY_HPROP_INJ = prove
 (`!a av av'. HPROP_INJ (W8ARRAY a av) (W8ARRAY a av') (av' = av)`,
  CHEAT_TAC);;

(* A valid heap must have proper ffi partitions *)
(* [local] *)
let NON_OVERLAP_FFI_PART_HFS = prove
 (`!s. HEAP_FROM_STATE s ==>
   (!s1 u1 ns1 ts1 s2 u2 ns2 ts2. cfHeapsBase_FFI_part s1 u1 ns1 ts1 IN s
     /\ cfHeapsBase_FFI_part s2 u2 ns2 ts2 IN s /\ (?p. MEM p ns1 /\ MEM p ns2)
     ==>
   s2 = s1 /\ u2 = u1 /\ ns2 = ns1 /\ ts2 = ts1)`,
  CHEAT_TAC);;

let NON_OVERLAP_FFI_PART = prove
 (`!s. VALID_HEAP s ==>
   (!s1 u1 ns1 ts1 s2 u2 ns2 ts2. cfHeapsBase_FFI_part s1 u1 ns1 ts1 IN s
     /\ cfHeapsBase_FFI_part s2 u2 ns2 ts2 IN s /\ (?p. MEM p ns1 /\ MEM p ns2)
     ==>
   s2 = s1 /\ u2 = u1 /\ ns2 = ns1 /\ ts2 = ts1)`,
  CHEAT_TAC);;

(* A minor lemma *)
(* [local] *)
let FFI_PORT_IN_HEAP_LEM = prove
 (`!s u ns events H h. (set_sep_one (cfHeapsBase_FFI_part s u ns events) * H)
  h ==> cfHeapsBase_FFI_part s u ns events IN h`,
  CHEAT_TAC);;

(* Another important theorem *)
let FRAME_UNIQUE_IO = prove
 (`!s. VALID_HEAP s ==>
   (!s1 u1 ns1 s2 u2 ns2 H1 H2.
   (IO s1 u1 ns1 * H1) s /\ (IO s2 u2 ns2 * H2) s ==>
   (?pn. MEM pn ns1 /\ MEM pn ns2) ==>
   s2 = s1 /\ u2 = u1 /\ ns2 = ns1)`,
  CHEAT_TAC);;

let IO_HPROP_INJ = prove
 (`!s1 u1 ns1 s2 u2 ns2 H1 H2. (?pn. MEM pn ns1 /\ MEM pn ns2) ==>
   HPROP_INJ (IO s1 u1 ns1) (IO s2 u2 ns2) (s2 = s1 /\ u2 = u1 /\ ns2 =
     ns1)`,
  CHEAT_TAC);;

(* Theorems and rewrites for REPLICATE and LIST_REL *)
let APPEND_LENGTH_INEQ = prove
 (`!l1 l2. LENGTH (l1) <= LENGTH (APPEND l1 l2) /\ LENGTH (l2) <= LENGTH
  (APPEND l1 l2)`,
  CHEAT_TAC);;

(* [local] *)
let REPLICATE_APPEND_RIGHT = prove
 (`APPEND a b = REPLICATE n x ==> b = REPLICATE (LENGTH b) x`,
  CHEAT_TAC);;

(* [local] *)
let REPLICATE_APPEND_LEFT = prove
 (`APPEND a b = REPLICATE n x ==> a = REPLICATE (LENGTH a) x`,
  CHEAT_TAC);;

let REPLICATE_APPEND_DECOMPOSE = prove
 (`APPEND a b = REPLICATE n x <=>
   a = REPLICATE (LENGTH a) x /\ b = REPLICATE (LENGTH b) x /\ LENGTH a +
     LENGTH b = n`,
  CHEAT_TAC);;

(* HOL4 cfLetAutoScript.sml:340-341: a theorem that HOL4 states as the value
   of an ML expression: REPLICATE_APPEND_DECOMPOSE_SYM *)

let REPLICATE_PLUS_ONE = prove
 (`REPLICATE (n + 1) x = CONS x (REPLICATE n x)`,
  CHEAT_TAC);;

(* [local] *)
let LIST_REL_DECOMPOSE_RIGHT_recip = prove
 (`!R'. ALL2 R' (APPEND a b) x ==> ALL2 R' a (TAKE (LENGTH a) x) /\ ALL2 R' b
  (DROP (LENGTH a) x)`,
  CHEAT_TAC);;

(* [local] *)
let LIST_REL_DECOMPOSE_RIGHT_imp = prove
 (`!R'. ALL2 R' a (TAKE (LENGTH a) x) /\ ALL2 R' b (DROP (LENGTH a) x) ==>
  ALL2 R' (APPEND a b) x`,
  CHEAT_TAC);;

let LIST_REL_DECOMPOSE_RIGHT = prove
 (`!R'. ALL2 R' (APPEND a b) x <=> ALL2 R' a (TAKE (LENGTH a) x) /\ ALL2 R' b
  (DROP (LENGTH a) x)`,
  CHEAT_TAC);;

(* [local] *)
let LIST_REL_DECOMPOSE_LEFT_recip = prove
 (`!R'. ALL2 R' x (APPEND a b) ==> ALL2 R' (TAKE (LENGTH a) x) a /\ ALL2 R'
  (DROP (LENGTH a) x) b`,
  CHEAT_TAC);;

(* [local] *)
let LIST_REL_DECOMPOSE_LEFT_imp = prove
 (`!R'. ALL2 R' (TAKE (LENGTH a) x) a /\ ALL2 R' (DROP (LENGTH a) x) b ==>
  ALL2 R' x (APPEND a b)`,
  CHEAT_TAC);;

let LIST_REL_DECOMPOSE_LEFT = prove
 (`!R'. ALL2 R' x (APPEND a b) <=> ALL2 R' (TAKE (LENGTH a) x) a /\ ALL2 R'
  (DROP (LENGTH a) x) b`,
  CHEAT_TAC);;

let HEAD_TAIL = prove
 (`~(l = []) ==> CONS (HD l) (TL l) = l`,
  CHEAT_TAC);;

let HEAD_TAIL_DECOMPOSE_RIGHT = prove
 (`CONS x a = b <=> ~(b = []) /\ x = HD b /\ a = TL b`,
  CHEAT_TAC);;

let HEAD_TAIL_DECOMPOSE_LEFT = prove
 (`b = CONS x a <=> ~(b = []) /\ x = HD b /\ a = TL b`,
  CHEAT_TAC);;

(* Theorems used as rewrites for the refinement invariants *)
(* HOL4 cfLetAutoScript.sml:424-429: the ML values that the definitions
   below antiquote *)

let EQTYPE_UNICITY_R = prove
 (`!abs' x y1 y2. EqualityType abs' ==> abs' x y1 ==> (abs' x y2 <=> y2 = y1)`,
  CHEAT_TAC);;

let EQTYPE_UNICITY_L = prove
 (`!abs' x1 x2 y. EqualityType abs' ==> abs' x1 y ==> (abs' x2 y <=> x2 = x1)`,
  CHEAT_TAC);;

(* Theorems to use LIST_REL A "as a" refinement invariant *)
let InjectiveRel_def = new_definition
  `InjectiveRel A = (!x1 y1 x2 y2. A x1 y1 /\ A x2 y2 ==> (x1 = x2 <=> y1 =
  y2))`;;

(* [local] *)
let EQTYPE_INJECTIVEREL = prove
 (`EqualityType A ==> InjectiveRel A`,
  CHEAT_TAC);;

let LIST_REL_INJECTIVE_REL = prove
 (`!A. InjectiveRel A ==> InjectiveRel (ALL2 A)`,
  CHEAT_TAC);;

let LIST_REL_INJECTIVE_EQTYPE = prove
 (`!A. EqualityType A ==> InjectiveRel (ALL2 A)`,
  CHEAT_TAC);;

let LIST_REL_UNICITY_RIGHT = prove
 (`EqualityType A ==> ALL2 A a b ==> (ALL2 A a b' <=> b' = b)`,
  CHEAT_TAC);;

let LIST_REL_UNICITY_LEFT = prove
 (`EqualityType A ==> ALL2 A a b ==> (ALL2 A a' b <=> a' = a)`,
  CHEAT_TAC);;

(* EqualityType proofs *)
let EqualityType_PAIR_TYPE = prove
 (`EqualityType A ==> EqualityType B ==> EqualityType (PAIR_TYPE A B)`,
  CHEAT_TAC);;

(* [local] *)
let LIST_TYPE_no_closure = prove
 (`!A x xv. EqualityType A ==> LIST_TYPE A x xv ==> no_closures xv`,
  CHEAT_TAC);;

(* [local] *)
let LIST_TYPE_inj = prove
 (`!A x1 x2 v1 v2. EqualityType A ==> LIST_TYPE A x1 v1 ==> LIST_TYPE A x2 v2
  ==>
   (v1 = v2 <=> x1 = x2)`,
  CHEAT_TAC);;

(* HOL4 cfLetAutoScript.sml:534: a proof *)
(* [local] *)
let LIST_TYPE_types_match = prove
 (`!A x1 x2 v1 v2. EqualityType A ==> LIST_TYPE A x1 v1 ==> LIST_TYPE A x2 v2
  ==>
   types_match v1 v2`,
  CHEAT_TAC);;

let EqualityType_LIST_TYPE = prove
 (`EqualityType A ==> EqualityType (LIST_TYPE A)`,
  CHEAT_TAC);;

(* Some theorems for rewrite rules with the refinement invariants *)

(* Need to write the expand and retract theorems for UNIT_TYPE by hand - otherwise the retract theorem might introduce a variable, for example *)
let UNIT_TYPE_RETRACT = prove
 (`!v. v = semanticPrimitives_Conv NONE [] <=> UNIT_TYPE one v`,
  CHEAT_TAC);;

let UNIT_TYPE_EXPAND = prove
 (`!u v. UNIT_TYPE u v <=> u = one /\ v = semanticPrimitives_Conv NONE []`,
  CHEAT_TAC);;

let NUM_INT_EQ = prove
 (`(!x y v. INT x v ==> (NUM y v <=> x = &y)) /\
   (!x y v. NUM y v ==> (INT x v <=> x = &y)) /\
   (!x v w. INT (&x) v ==> (NUM x w <=> w = v)) /\
   (!x v w. NUM x v ==> (INT (&x) w <=> w = v))`,
  CHEAT_TAC);;

(* Some rules used to simplify arithmetic equations (not happy with that: write a conversion instead? *)

(* [local] *)
let NUM_EQ_lem = prove
 (`!(a1:num) (a2:num) (b:num). b <= a1 ==> b <= a2 ==> (a1 = a2 <=> a1 - b =
  a2 - b)`,
  CHEAT_TAC);;

let NUM_EQ_SIMP1 = prove
 (`a1 + (NUMERAL n1) * b = a2 + (NUMERAL n2) * b <=>
   a1 + (NUMERAL n1 - (MIN (NUMERAL n1) (NUMERAL n2))) * b = a2 + (NUMERAL
     n2 - (MIN (NUMERAL n1) (NUMERAL n2))) * b`,
  CHEAT_TAC);;

let NUM_EQ_SIMP2 = prove
 (`(NUMERAL n1) * b + a1 = (NUMERAL n2) * b + a2 <=>
   (NUMERAL n1 - (MIN (NUMERAL n1) (NUMERAL n2))) * b + a1 = (NUMERAL n2 -
     (MIN (NUMERAL n1) (NUMERAL n2))) * b + a2`,
  CHEAT_TAC);;

let NUM_EQ_SIMP3 = prove
 (`a1 + (NUMERAL n1) * b = (NUMERAL n2) * b + a2 <=>
   a1 + (NUMERAL n1 - (MIN (NUMERAL n1) (NUMERAL n2))) * b = (NUMERAL n2 -
     (MIN (NUMERAL n1) (NUMERAL n2))) * b + a2`,
  CHEAT_TAC);;

let NUM_EQ_SIMP4 = prove
 (`(NUMERAL n1) * b + a1 = a2 + (NUMERAL n2) * b <=>
   (NUMERAL n1 - (MIN (NUMERAL n1) (NUMERAL n2))) * b + a1 = (NUMERAL n2 -
     (MIN (NUMERAL n1) (NUMERAL n2))) * b + a2`,
  CHEAT_TAC);;

let NUM_EQ_SIMP5 = prove
 (`a1 + b = a2 + (NUMERAL n2) * b <=>
   a1 + (1 - (MIN 1 (NUMERAL n2))) * b = a2 + (NUMERAL n2 - (MIN 1
     (NUMERAL n2))) * b`,
  CHEAT_TAC);;

let NUM_EQ_SIMP6 = prove
 (`a1 + (NUMERAL n1) * b = a2 + b <=>
   a1 + (NUMERAL n1 - (MIN 1 (NUMERAL n1))) * b = a2 + (1 - (MIN 1
     (NUMERAL n1))) * b`,
  CHEAT_TAC);;

let NUM_EQ_SIMP7 = prove
 (`b + a1 = (NUMERAL n2) * b + a2 <=>
   (1 - (MIN 1 (NUMERAL n2))) * b + a1 = (NUMERAL n2 - (MIN 1 (NUMERAL
     n2))) * b + a2`,
  CHEAT_TAC);;

let NUM_EQ_SIMP8 = prove
 (`(NUMERAL n1) * b + a1 = b + a2 <=>
   (NUMERAL n1 - (MIN 1 (NUMERAL n1))) * b + a1 = (1 - (MIN 1 (NUMERAL
     n1))) * b + a2`,
  CHEAT_TAC);;

let NUM_EQ_SIMP9 = prove
 (`a1 + b = (NUMERAL n2) * b + a2 <=>
   a1 + (1 - (MIN 1 (NUMERAL n2))) * b = (NUMERAL n2 - (MIN 1 (NUMERAL
     n2))) * b + a2`,
  CHEAT_TAC);;

let NUM_EQ_SIMP10 = prove
 (`b + a1 = a2 + (NUMERAL n2) * b <=>
   (1 - (MIN 1 (NUMERAL n2))) * b + a1 = a2 + (NUMERAL n2 - (MIN 1
     (NUMERAL n2))) * b`,
  CHEAT_TAC);;

let NUM_EQ_SIMP11 = prove
 (`a1 + (NUMERAL n1) * b = b + a2 <=>
   a1 + (NUMERAL n1 - (MIN 1 (NUMERAL n1))) * b = (1 - (MIN 1 (NUMERAL
     n1))) * b + a2`,
  CHEAT_TAC);;

let NUM_EQ_SIMP12 = prove
 (`(NUMERAL n1) * b + a1 = a2 + b <=>
   (NUMERAL n1 - (MIN 1 (NUMERAL n1))) * b + a1 = a2 + (1 - (MIN 1
     (NUMERAL n1))) * b`,
  CHEAT_TAC);;

(* and the interface *)
let _ = unhide_overloads ();;
