(* ======================================================== *)
(*  namespaceProps: ported from HOL4's
    semantics/proofs/namespacePropsScript.sml
    A proof theory about namespace.ml, with 3 definitions and 96
    theorems.  Needed by 18 files of the port.  *)
(* ======================================================== *)

(*
  Proofs about the namespace datatype.
*)

needs "semantics/ast.ml";;
needs "semantics/namespace.ml";;

(* the theories whose names the Ancestors blocks of the source
   bring, which are the ones that its statements read: the
   overloads of every other theory come out of the interface
   while this file loads *)
let _ = hol4_ancestors "namespaceProps"
  ["ast"; "namespace"];;

let _ = do_list hide_constant ["id"; "path"];;

(* [simp] *)
let mk_id_11 = prove
 (`!a b c d. mk_id a b = mk_id c d <=> (a = c) /\ (b = d)`,
  CHEAT_TAC);;

(* [simp] *)
let id_to_mods_mk_id = prove
 (`!mn x. id_to_mods (mk_id mn x) = mn`,
  CHEAT_TAC);;

(* [simp] *)
let id_to_namemods_mk_id = prove
 (`!mn x. id_to_n (mk_id mn x) = x`,
  CHEAT_TAC);;

let mk_id_surj = prove
 (`!id'. ?p n. id' = mk_id p n`,
  CHEAT_TAC);;

let mk_id_thm = prove
 (`!id'. mk_id (id_to_mods id') (id_to_n id') = id'`,
  CHEAT_TAC);;

(* ----------- Monotonicity for ind rel ------------ *)

(* [mono] *)
let nsAll_mono = prove
 (`(!id' x. P id' x ==> Q id' x) ==> nsAll P e ==> nsAll Q e`,
  CHEAT_TAC);;

(* [mono] *)
let nsSub_mono = prove
 (`(!x y z. R1 x y z ==> R2 x y z) ==> (nsSub R1 e1 e2 ==> nsSub R2 e1
  e2)`,
  CHEAT_TAC);;

let nsSub_mono2 = prove
 (`(!x y z. nsLookup e1 x = SOME y /\ nsLookup e2 x = SOME z /\ R1 x y
  z ==> R2 x y z) ==> (nsSub R1 e1 e2 ==> nsSub R2 e1 e2)`,
  CHEAT_TAC);;

(* [mono] *)
let nsAll2_mono = prove
 (`(!x y z. R1 x y z ==> R2 x y z) ==> nsAll2 R1 e1 e2 ==> nsAll2 R2
  e1 e2`,
  CHEAT_TAC);;

(* ---------- Automatic simps involving empty envs -------------- *)

(* [simp] *)
let nsLookup_nsEmpty = prove
 (`!id'. nsLookup nsEmpty id' = NONE`,
  CHEAT_TAC);;

(* [simp] *)
let nsLookupMod_nsEmpty = prove
 (`!x y. nsLookupMod nsEmpty (CONS x y) = NONE`,
  CHEAT_TAC);;

(* [simp] *)
let nsAppend_nsEmpty = prove
 (`!env. nsAppend env nsEmpty = env /\ nsAppend nsEmpty env = env`,
  CHEAT_TAC);;

(* [simp] *)
let alist_to_ns_nil = prove
 (`alist_to_ns [] = nsEmpty`,
  CHEAT_TAC);;

(* [simp] *)
let nsSub_nsEmpty = prove
 (`!r env. nsSub r nsEmpty env`,
  CHEAT_TAC);;

(* [simp] *)
let nsAll_nsEmpty = prove
 (`!f. nsAll f nsEmpty`,
  CHEAT_TAC);;

(* [simp] *)
let nsAll2_nsEmpty = prove
 (`!f. nsAll2 f nsEmpty nsEmpty`,
  CHEAT_TAC);;

(* [simp] *)
let nsDom_nsEmpty = prove
 (`nsDom nsEmpty = {}`,
  CHEAT_TAC);;

(* [simp] *)
let nsDomMod_nsEmpty = prove
 (`nsDomMod nsEmpty = {[]}`,
  CHEAT_TAC);;

(* [simp] *)
let nsMap_nsEmpty = prove
 (`!f. nsMap f nsEmpty = nsEmpty`,
  CHEAT_TAC);;

(* [simp] *)
let nsBind_nsEmpty = prove
 (`!x y env. ~(nsBind x y env = nsEmpty)`,
  CHEAT_TAC);;

let nsLookup_Bind_v_some = prove
 (`nsLookup (Bind v []) k = SOME x <=>
   (?y. k = Short y /\ ALOOKUP v y = SOME x)`,
  CHEAT_TAC);;

(* ------------- Other simple automatic theorems --------- *)

(* [simp] *)
let alist_to_ns_cons = prove
 (`!k v l. alist_to_ns (CONS (k,v) l) = nsBind k v (alist_to_ns l)`,
  CHEAT_TAC);;

(* [simp] *)
let nsAppend_nsBind = prove
 (`!k v e1 e2. nsAppend (nsBind k v e1) e2 = nsBind k v (nsAppend e1
  e2)`,
  CHEAT_TAC);;

(* [simp] *)
let nsAppend_alist_to_ns = prove
 (`!al1 al2. nsAppend (alist_to_ns al1) (alist_to_ns al2) =
  alist_to_ns (APPEND al1 al2)`,
  CHEAT_TAC);;

(* [simp] *)
let nsAppend_assoc = prove
 (`!e1 e2 e3. nsAppend e1 (nsAppend e2 e3) = nsAppend (nsAppend e1 e2)
  e3`,
  CHEAT_TAC);;

(* [simp] *)
let nsLookup_nsBind = prove
 (`(!n v e. nsLookup (nsBind n v e) (Short n) = SOME v) /\
   (!n n' v e. ~(n = Short n') ==> nsLookup (nsBind n' v e) n =
     nsLookup e n)`,
  CHEAT_TAC);;

(* [simp] *)
let nsAppend_nsSing = prove
 (`!n x e. nsAppend (nsSing n x) e = nsBind n x e`,
  CHEAT_TAC);;

(* [simp] *)
let nsLookup_nsSing = prove
 (`!n v id'. nsLookup (nsSing n v) id' = (if id' = Short n then SOME v
  else NONE)`,
  CHEAT_TAC);;

(* [simp] *)
let nsAll_nsSing = prove
 (`!R n v. nsAll R (nsSing n v) <=> R (Short n) v`,
  CHEAT_TAC);;

(* [simp] *)
let nsAll2_nsSing = prove
 (`!R n1 v1 n2 v2. nsAll2 R (nsSing n1 v1) (nsSing n2 v2) <=> n1 = n2
  /\ R (Short n1) v1 v2`,
  CHEAT_TAC);;

(* [simp] *)
let nsMap_nsSing = prove
 (`!f x v. nsMap f (nsSing x v) = nsSing x (f v)`,
  CHEAT_TAC);;

(* [simp] *)
let nsLookupMod_nsSing = prove
 (`!n1 n2 v. nsLookupMod (nsSing n2 v) n1 = (if n1 = [] then SOME
  (nsSing n2 v) else NONE)`,
  CHEAT_TAC);;

(* [simp] *)
let nsBind_11 = prove
 (`!x y n x' y' n'. nsBind x y n = nsBind x' y' n' <=> x = x' /\ y =
  y' /\ n = n'`,
  CHEAT_TAC);;

(* [simp] *)
let nsDom_nsBind = prove
 (`!x y n. nsDom (nsBind x y n) = Short x INSERT nsDom n`,
  CHEAT_TAC);;

(* [simp] *)
let nsDom_nsSing = prove
 (`!x y. nsDom (nsSing x y) = {Short x}`,
  CHEAT_TAC);;

(* [simp] *)
let nsDomMod_nsBind = prove
 (`!x y n. nsDomMod (nsBind x y n) = nsDomMod n`,
  CHEAT_TAC);;

(* [simp] *)
let nsDomMod_nsSing = prove
 (`!x y. nsDomMod (nsSing x y) = {[]}`,
  CHEAT_TAC);;

(* [simp] *)
let nsLookupMod_alist_to_ns = prove
 (`!l x y. nsLookupMod (alist_to_ns l) (CONS x y) = NONE`,
  CHEAT_TAC);;

(* [simp] *)
let alist_to_ns_11 = prove
 (`!l1 l2. alist_to_ns l1 = alist_to_ns l2 <=> l1 = l2`,
  CHEAT_TAC);;

(* -------------- nsLookup ------------------ *)

let nsLookup_to_nsLookupMod = prove
 (`!n v t.
    nsLookup n v = SOME t ==>
    (?m. nsLookupMod n (id_to_mods v) = SOME m /\ nsLookup m (Short
      (id_to_n v)) = SOME t)`,
  CHEAT_TAC);;

(* -------------- alist_to_ns --------------- *)

let nsLookup_alist_to_ns_some = prove
 (`!l id' v. nsLookup (alist_to_ns l) id' = SOME v <=> (?x'. id' =
  Short x' /\ ALOOKUP l x' = SOME v)`,
  CHEAT_TAC);;

let nsLookup_alist_to_ns_none = prove
 (`!l id'. nsLookup (alist_to_ns l) id' = NONE <=> (!x'. id' = Short
  x' ==> ALOOKUP l x' = NONE)`,
  CHEAT_TAC);;

(* [simp] *)
let nsDom_alist_to_ns = prove
 (`!l. nsDom (alist_to_ns l) = set_of_list (MAP (Short o FST) l)`,
  CHEAT_TAC);;

(* -------------- nsLift --------------- *)

let nsLookup_nsLift = prove
 (`!mn e id'.
    nsLookup (nsLift mn e) id' =
    (match id' with Long mn' id' ->
      (if mn = mn' then
        nsLookup e id' else
        NONE) | Short _1 -> NONE)`,
  CHEAT_TAC);;

let nsLookupMod_nsLift = prove
 (`!mn e path'.
    nsLookupMod (nsLift mn e) path' =
    (match path' with [] -> SOME (nsLift mn e) | (CONS mn' path') ->
      (if mn = mn' then
        nsLookupMod e path' else
        NONE))`,
  CHEAT_TAC);;

(* [simp] *)
let nsLookup_nsLift_append = prove
 (`!m ns ns' m' id' n.
   nsLookup (nsAppend (nsLift m ns) ns') (Short n) = nsLookup ns'
     (Short n) /\
   nsLookup (nsAppend (nsLift m ns) ns') (Long m' id') =
     (if m = m' then nsLookup ns id' else nsLookup ns' (Long m'
       id'))`,
  CHEAT_TAC);;

(* --------------- nsAppend ------------- *)

let nsLookup_nsAppend_none = prove
 (`!e1 id' e2.
    nsLookup (nsAppend e1 e2) id' = NONE <=>
    (nsLookup e1 id' = NONE /\
     (nsLookup e2 id' = NONE \/
      (?p1 p2 e3. ~(p1 = []) /\ id_to_mods id' = APPEND p1 p2 /\
        nsLookupMod e1 p1 = SOME e3)))`,
  CHEAT_TAC);;

let nsLookup_nsAppend_some = prove
 (`!e1 id' e2 v.
    nsLookup (nsAppend e1 e2) id' = SOME v <=>
    nsLookup e1 id' = SOME v \/
    (nsLookup e1 id' = NONE /\ nsLookup e2 id' = SOME v /\
     (!p1 p2. ~(p1 = []) /\ id_to_mods id' = APPEND p1 p2 ==>
       nsLookupMod e1 p1 = NONE))`,
  CHEAT_TAC);;

let nsAppend_to_nsBindList = prove
 (`!l. nsAppend (alist_to_ns l) e = nsBindList l e`,
  CHEAT_TAC);;

let nsLookupMod_nsAppend_none = prove
 (`!e1 e2 path'.
    nsLookupMod (nsAppend e1 e2) path' = NONE <=>
    (nsLookupMod e1 path' = NONE /\
     (nsLookupMod e2 path' = NONE \/
      (?p1 p2 e3. ~(p1 = []) /\ path' = APPEND p1 p2 /\ nsLookupMod
        e1 p1 = SOME e3)))`,
  CHEAT_TAC);;

let nsLookupMod_nsAppend_some = prove
 (`!e1 e2 path'.
    (
     nsLookupMod (nsAppend e1 e2) path' = SOME x <=>
     (if path' = [] then x = nsAppend e1 e2 else
     nsLookupMod e1 path' = SOME x \/
      (nsLookupMod e2 path' = SOME x /\
      (!p1 p2. ~(p1 = []) /\ path' = APPEND p1 p2 ==> nsLookupMod
        e1 p1 = NONE))))`,
  CHEAT_TAC);;

(* [simp] *)
let nsDom_nsAppend_alist = prove
 (`!x y. nsDom (nsAppend (alist_to_ns x) y) = set_of_list (MAP (Short
  o FST) x) UNION nsDom y`,
  CHEAT_TAC);;

(* -------------- nsAll ---------------- *)

(* [simp] *)
let eALL_T = prove
 (`!e. nsAll (\n x. T) e`,
  CHEAT_TAC);;

let nsLookup_nsAll = prove
 (`!env x P v. nsAll P env /\ nsLookup env x = SOME v ==> P x v`,
  CHEAT_TAC);;

let nsAll_nsAppend = prove
 (`!f e1 e2. nsAll f e1 /\ nsAll f e2 ==> nsAll f (nsAppend e1 e2)`,
  CHEAT_TAC);;

let nsAll_nsBind = prove
 (`!P x v e. P (Short x) v /\ nsAll P e ==> nsAll P (nsBind x v e)`,
  CHEAT_TAC);;

let nsAll_nsOptBind = prove
 (`!P x v e. (x = NONE \/ (?n. x = SOME n /\ P (Short n) v)) /\ nsAll
  P e ==> nsAll P (nsOptBind x v e)`,
  CHEAT_TAC);;

let nsAll_alist_to_ns = prove
 (`!R l. ALL (\(n,v). R (Short n) v) l ==> nsAll R (alist_to_ns l)`,
  CHEAT_TAC);;

(* [simp] *)
let nsAll_nsLift = prove
 (`!R mn e. nsAll R (nsLift mn e) <=> nsAll (\id'. R (Long mn id')) e`,
  CHEAT_TAC);;

let nsAll_nsAppend_left = prove
 (`!P n1 n2. nsAll P (nsAppend n1 n2) ==> nsAll P n1`,
  CHEAT_TAC);;

(* -------------- nsSub ---------------- *)

let nsSub_conj = prove
 (`!P Q e1 e2. nsSub (\id' x y. P id' x y /\ Q id' x y) e1 e2 <=> nsSub
  P e1 e2 /\
   nsSub Q e1 e2`,
  CHEAT_TAC);;

let nsSub_refl = prove
 (`!P R. (!n x. P n x ==> R n x x) ==> (!e. nsAll P e ==> nsSub R e e)`,
  CHEAT_TAC);;

let nsSub_nsBind = prove
 (`!R x v1 v2 e1 e2.
     R (Short x) v1 v2 /\ nsSub R e1 e2 ==> nsSub R (nsBind x v1
       e1) (nsBind x v2 e2)`,
  CHEAT_TAC);;

let nsSub_nsAppend2 = prove
 (`!R e1 e2 e2'. nsSub R e1 e1 /\ nsSub R e2 e2' ==> nsSub R (nsAppend
  e1 e2) (nsAppend e1 e2')`,
  CHEAT_TAC);;

let nsSub_nsAppend_lift = prove
 (`!R mn e1 e1' e2 e2'.
    nsSub (\id'. R (Long mn id')) e1 e1' /\
    nsSub R e2 e2' ==>
    nsSub R (nsAppend (nsLift mn e1) e2) (nsAppend (nsLift mn e1')
      e2')`,
  CHEAT_TAC);;

let alist_rel_restr_def,alist_rel_restr_ind = define_rec
  [`alist_rel_restr R l1 l2 [] <=> T`;
   `alist_rel_restr R l1 l2 (CONS k1 keys) <=>
        (match ALOOKUP l1 k1 with NONE -> F | SOME v1 ->
          (match ALOOKUP l2 k1 with NONE -> F | SOME v2 -> R k1
            v1 v2 /\ alist_rel_restr R l1 l2 keys))`];;

let alist_rel_restr_thm = prove
 (`!R e1 e2 keys.
    alist_rel_restr R e1 e2 keys <=>
      (!k. MEM k keys ==> (?v1 v2. ALOOKUP e1 k = SOME v1 /\
        ALOOKUP e2 k = SOME v2 /\ R k v1 v2))`,
  CHEAT_TAC);;

let alistSub_def = new_definition
  `alistSub R e1 e2 <=> alist_rel_restr R e1 e2 (MAP FST e1)`;;

let alistSub_cong = prove
 (`!l1 l2 l1' l2' R R'.
    l1 = l1' /\ l2 = l2' /\ (!n x y. ALOOKUP l1' n = SOME x /\
      ALOOKUP l2' n = SOME y ==> R n x y = R' n x y) ==>
    (alistSub R l1 l2 <=> alistSub R' l1' l2')`,
  CHEAT_TAC);;

(* HOL4 namespacePropsScript.sml:785: ML code, not ported *)

(* the termination relation that HOL4 gives is
     MEASURE (\(p,r,env,_2). namespace_size (\x. 0) (\x. 0) (\x. 0) env)
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 namespacePropsScript.sml:791-801: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let nsSub_compute_def,nsSub_compute_ind = define_guess_cheat
  [`nsSub_compute path' R (Bind e1V e1M) (Bind e2V e2M) <=>
     alistSub (\k v1 v2. R (mk_id (REVERSE path') k) v1 v2) e1V e2V
       /\
     alistSub (\k v1 v2. nsSub_compute (CONS k path') R v1 v2)
       e1M e2M`];;

let nsLookup_FOLDR_nsLift = prove
 (`!e p k. nsLookup (ITLIST nsLift p e) (mk_id p k) = nsLookup e
  (Short k)`,
  CHEAT_TAC);;

let nsLookup_FOLDR_nsLift_some = prove
 (`!e p id' v.
    nsLookup (ITLIST nsLift p e) id' = SOME v <=>
    (p = [] /\ nsLookup e id' = SOME v) \/
    (~(p = []) /\ (?p2 n. id' = mk_id (APPEND p p2) n /\ nsLookup e
      (mk_id p2 n) = SOME v))`,
  CHEAT_TAC);;

let nsLookupMod_FOLDR_nsLift_none = prove
 (`!e p1 p2. nsLookupMod (ITLIST nsLift p1 e) p2 = NONE <=>
    (IS_PREFIX p1 p2 \/ IS_PREFIX p2 p1) ==>
    (?p3. p2 = APPEND p1 p3 /\ nsLookupMod e p3 = NONE)`,
  CHEAT_TAC);;

(* HOL4 namespacePropsScript.sml:841-989: code that the source has in
   a comment *)

(* -------------- nsAll2 ---------------- *)

let nsAll2_conj = prove
 (`!P Q e1 e2. nsAll2 (\id' x y. P id' x y /\ Q id' x y) e1 e2 <=>
  nsAll2 P e1 e2 /\ nsAll2 Q e1 e2`,
  CHEAT_TAC);;

let nsAll2_nsLookup1 = prove
 (`!R e1 e2 n v1.
    nsLookup e1 n = SOME v1 /\
    nsAll2 R e1 e2 ==>
    (?v2. nsLookup e2 n = SOME v2 /\ R n v1 v2)`,
  CHEAT_TAC);;

let nsAll2_nsLookup2 = prove
 (`!R e1 e2 n v2.
    nsLookup e2 n = SOME v2 /\
    nsAll2 R e1 e2 ==>
    (?v1. nsLookup e1 n = SOME v1 /\ R n v1 v2)`,
  CHEAT_TAC);;

let nsAll2_nsLookup_none = prove
 (`!R e1 e2 n.
    nsAll2 R e1 e2 ==>
    (nsLookup e1 n = NONE <=> nsLookup e2 n = NONE)`,
  CHEAT_TAC);;

let nsAll2_nsBind = prove
 (`!R x v1 v2 e1 e2.
     R (Short x) v1 v2 /\ nsAll2 R e1 e2 ==> nsAll2 R (nsBind x v1
       e1) (nsBind x v2 e2)`,
  CHEAT_TAC);;

let nsAll2_nsBindList = prove
 (`!R l1 l2 e1 e2.
     ALL2 (\(x,y) (x',y'). x = x' /\ R (Short x) y y') l1 l2 /\
       nsAll2 R e1 e2 ==>
     nsAll2 R (nsBindList l1 e1) (nsBindList l2 e2)`,
  CHEAT_TAC);;

let nsAll2_nsAppend = prove
 (`!R e1 e1' e2 e2'.
    nsAll2 R e1 e2 /\ nsAll2 R e1' e2' ==> nsAll2 R (nsAppend e1
      e1') (nsAppend e2 e2')`,
  CHEAT_TAC);;

let nsAll2_alist_to_ns = prove
 (`!R l1 l2. ALL2 (\(x,y) (x',y'). x = x' /\ R (Short x) y y') l1 l2
  ==> nsAll2 R (alist_to_ns l1) (alist_to_ns l2)`,
  CHEAT_TAC);;

(* [simp] *)
let nsAll2_nsLift = prove
 (`!R mn e1 e2. nsAll2 R (nsLift mn e1) (nsLift mn e2) <=> nsAll2
  (\id'. R (Long mn id')) e1 e2`,
  CHEAT_TAC);;

(* -------------- nsMap --------------- *)

(* [simp] *)
let nsMap_alist_to_ns = prove
 (`!f l. nsMap f (alist_to_ns l) = alist_to_ns (MAP (\(k,v). (k,f v))
  l)`,
  CHEAT_TAC);;

let nsMap_compose = prove
 (`!g e f. nsMap f (nsMap g e) = nsMap (f o g) e`,
  CHEAT_TAC);;

(* [simp] *)
let nsMap_I = prove
 (`!ns. nsMap I ns = ns`,
  CHEAT_TAC);;

let nsMap_nsAppend = prove
 (`!n1 n2 f. nsMap f (nsAppend n1 n2) = nsAppend (nsMap f n1) (nsMap f
  n2)`,
  CHEAT_TAC);;

let nsLookupMod_nsMap = prove
 (`!n x f. nsLookupMod (nsMap f n) x = OPTION_MAP (nsMap f)
  (nsLookupMod n x)`,
  CHEAT_TAC);;

let nsLookup_nsMap = prove
 (`!n x f. nsLookup (nsMap f n) x = OPTION_MAP f (nsLookup n x)`,
  CHEAT_TAC);;

let nsAll_nsMap = prove
 (`!f n P. nsAll P (nsMap f n) <=> nsAll (\x y. P x (f y)) n`,
  CHEAT_TAC);;

let nsLift_nsMap = prove
 (`!f n mn. nsLift mn (nsMap f n) = nsMap f (nsLift mn n)`,
  CHEAT_TAC);;

let nsSub_nsMap = prove
 (`!R f n1 n2.
    nsSub R (nsMap f n1) (nsMap f n2) <=> nsSub (\id' x y. R id' (f
      x) (f y)) n1 n2`,
  CHEAT_TAC);;

(* --------------- nsDom --------------- *)
let nsLookup_nsDom = prove
 (`!x n. x IN nsDom n <=> (?v. nsLookup n x = SOME v)`,
  CHEAT_TAC);;

(* [simp] *)
let nsDomMod_alist_to_ns = prove
 (`!l. nsDomMod (alist_to_ns l) = {[]}`,
  CHEAT_TAC);;

(* [local] *)
let lemma = prove
 (`(?x. y = SOME x) <=> ~(y = NONE)`,
  CHEAT_TAC);;

let nsDom_nsAppend_equal = prove
 (`!n1 n2 n3 n4.
    nsDom n1 = nsDom n3 /\
    nsDom n2 = nsDom n4 /\
    nsDomMod n1 = nsDomMod n3 /\
    nsDomMod n2 = nsDomMod n4 ==>
    nsDom (nsAppend n1 n2) = nsDom (nsAppend n3 n4) /\
    nsDomMod (nsAppend n1 n2) = nsDomMod (nsAppend n3 n4)`,
  CHEAT_TAC);;

let nsDom_nsLift = prove
 (`!mn n. nsDom (nsLift mn n) = IMAGE (Long mn) (nsDom n)`,
  CHEAT_TAC);;

let nsDomMod_nsLift = prove
 (`!mn n. nsDomMod (nsLift mn n) = [] INSERT IMAGE (CONS mn) (nsDomMod
  n)`,
  CHEAT_TAC);;

let nsDom_nsAppend_flat = prove
 (`!n1 n2. nsDomMod n1 = {[]} ==> nsDom (nsAppend n1 n2) = nsDom n1
  UNION nsDom n2`,
  CHEAT_TAC);;

let nsDomMod_nsAppend_flat = prove
 (`!n1 n2. nsDomMod n1 = {[]} ==> nsDomMod (nsAppend n1 n2) = nsDomMod
  n2`,
  CHEAT_TAC);;

(* and the names that this file reads as variables are constants again *)
let _ = do_list unhide_constant
  ["id";
   "path"];;

(* and the overloads that this file cannot see are back in the
   interface *)
let _ = unhide_overloads ();;
