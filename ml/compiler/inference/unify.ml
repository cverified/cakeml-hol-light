(* ======================================================== *)
(*  unify: ported from HOL4's
    compiler/inference/unifyScript.sml  *)
(* ======================================================== *)

(*
  Defines a unification algorithm for use in the type inferencer.
  Based on the triangular unification algorithm in
  HOL/examples/unification/triangular/first-order.  We encode our
  CakeML types into the term structure used there and them bring over
  those definitions and theorems.
*)

needs "compiler/inference/infer_t.ml";;
needs "lib/collapse.ml";;
needs "lib/fmsp.ml";;
needs "lib/rmfmap.ml";;
needs "lib/sptree.ml";;
needs "lib/subst.ml";;
needs "lib/tcallUnif.ml";;
needs "lib/term.ml";;
needs "lib/unifDef.ml";;
needs "lib/walk.ml";;
needs "lib/walkstar.ml";;
(* HOL4 ancestors outside the port: unifProps transfer cps *)

hol4_overload "++" "OPTION_CHOICE";;

(* HOL4 ML code, not ported:
val option_map_case = optionTheory.OPTION_MAP_CASE
val option_bind_thm = oneline optionTheory.OPTION_BIND_def
*)

let atom_INDUCT,atom_RECURSION = define_datatype
  "atom = TC_tag (num) | DB_tag (num) | Tapp_tag | Null_tag";;

let encode_infer_t_def = cake_define_list
  [`encode_infer_t (Infer_Tvar_db n) =
      term_Const (DB_tag n)`;
   `encode_infer_t (Infer_Tapp ts tc) =
      term_Pair (term_Const Tapp_tag) (term_Pair (term_Const
        (TC_tag tc)) (encode_infer_ts ts))`;
   `encode_infer_t (Infer_Tuvar n) =
      term_Var n`;
   `encode_infer_ts [] =
      term_Const Null_tag`;
   `encode_infer_ts (t :: ts) =
      term_Pair (encode_infer_t t) (encode_infer_ts ts)`];;

(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let decode_infer_t_def = cake_define_list_cheat CHEAT_TAC
  [`decode_infer_t (term_Var n) =
      Infer_Tuvar n`;
   `decode_infer_t (term_Const (DB_tag n)) =
      Infer_Tvar_db n`;
   `decode_infer_t (term_Pair (term_Const Tapp_tag) (term_Pair
  (term_Const (TC_tag tc)) s)) =
      Infer_Tapp (decode_infer_ts s) tc`;
   `decode_infer_t _1 = Infer_Tuvar 5`;
   `decode_infer_ts (term_Const Null_tag) =
      []`;
   `decode_infer_ts (term_Pair s1 s2) =
      decode_infer_t s1 :: decode_infer_ts s2`;
   `decode_infer_ts _2 = []`];;

(* "Ramana Kumar unification type to CakeML type" relation *)
let RKC_def = cake_define
  `RKC rkt ct <=> encode_infer_t ct = rkt`;;

let substR_def = cake_define
  `substR fm sp <=> wfs fm /\ sptree_wf sp /\ fm = encode_infer_t o_f
  sp2fm sp`;;

let cwfs_def = cake_define
  `cwfs s <=> swfs (sptree_map encode_infer_t s) /\ sptree_wf s`;;

(*
Theorem RKC_FORALL[transfer_rule]:
  ((RKC |==> (==>)) |==> (==>)) $! $!
Proof
  irule transferTheory.ALL_surj_imp_imp >> simp[surj_RKC]
QED
*)

let cvwalk_def = cake_define
  `cvwalk s n = decode_infer_t (svwalk (sptree_map encode_infer_t s)
  n)`;;

let cwalk_def = cake_define
  `cwalk s it = decode_infer_t (swalk (sptree_map encode_infer_t s)
  (encode_infer_t it))`;;

(* HOL4 ML code, not ported:
val cwf = ASSUME “cwfs s” |> SRULE[cwfs_def] |> cj 2
val cwfs = ASSUME “cwfs s” |> SRULE[cwfs_def] |> cj 1
*)

let coc_def = cake_define
  `coc s it n = soc (sptree_map encode_infer_t s) (encode_infer_t it)
  n`;;

let t_vars_def = cake_define
  `t_vars t = vars (encode_infer_t t)`;;

let cunify_def = cake_define
  `cunify s t1 t2 = OPTION_MAP (sptree_map decode_infer_t)
                              (sunify (sptree_map encode_infer_t s)
                                (encode_infer_t t1)
                              (encode_infer_t t2))`;;

let cunifyl_def = cake_define
  `cunifyl s ts1 ts2 =
   OPTION_MAP (sptree_map decode_infer_t)
              (sunify (sptree_map encode_infer_t s)
                      (encode_infer_ts ts1)
                      (encode_infer_ts ts2))`;;

let _ = size_thms "infer_t";;
(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
let capply_subst_def = cake_define_list_try (fun () ->
  `MEASURE (infer_t_size o SND)`)
  [`capply_subst s (Infer_Tuvar n) = (match sptree_lookup n s with
                              NONE -> Infer_Tuvar n | SOME it ->
                                it)`;
   `capply_subst s (Infer_Tapp ts tc) = Infer_Tapp (MAP (capply_subst
  s) ts) tc`;
   `capply_subst s (Infer_Tvar_db n) = Infer_Tvar_db n`];;

let cwalkstar_def = cake_define
  `cwalkstar s it =
   decode_infer_t (walkstar (encode_infer_t o_f sp2fm s)
     (encode_infer_t it))`;;

(* HOL4 ML code, not ported:
fun tcallify_th fixedvs th =
  let val (l,r) = dest_eq (concl th)
      val (lf0, args0) = strip_comb l
      val args = op_set_diff aconv args0 fixedvs
      val lf = list_mk_comb(lf0, fixedvs)
      val atup = pairSyntax.list_mk_pair args
      val inty = type_of atup
      val body_t = tailrecLib.mk_sum_term lf inty r
  in
      pairSyntax.mk_pabs(atup, body_t)
  end
*)

(* HOL4 ML code, not ported:
val cvwalk_code = tcallify_th [“s:infer_t num_map”] cvwalk_thm
*)

(* PENDING: tcallify_th makes it with ML code
Definition cvwalk_code_def:
  cvwalk_code s = ^cvwalk_code
End *)

let cvwalkR_def = cake_define
  `cvwalkR sigma = (\v v0. vR (encode_infer_t o_f sp2fm sigma) v v0)`;;

(* PENDING: the tail recursion of cvwalk
Definition tcvwalk_def:
  tcvwalk s n = TAILREC (cvwalk_code s) n
End *)

(* PENDING: the tail recursion of cwalk
Definition tcwalk_def:
  tcwalk s it = case it of
                  Infer_Tvar_db c => Infer_Tvar_db c
                | Infer_Tapp l n => Infer_Tapp l n
                | Infer_Tuvar v => tcvwalk s v
End *)

let cocl_def = cake_define_list
  [`cocl s [] n <=> F`;
   `cocl s (i :: is) n <=> coc s i n \/ cocl s is n`];;

let kcoc_def = cake_define
  `kcoc s it n k = cwc (coc s it n) k`;;

let kcocl_def = cake_define
  `kcocl s its n k = cwc (cocl s its n) k`;;

new_type_abbrev("kcockont",`: (infer_t list) list`);;

let apply_kcockont_def = cake_define_list
  [`apply_kcockont s n [] b = b`;
   `apply_kcockont s n (ts :: rest) b =
    (if b then apply_kcockont s n rest T else kcocl s ts n
      (apply_kcockont s n rest))`];;

let dfkcoc_def = cake_define
  `dfkcoc s t n k = kcoc s t n (apply_kcockont s n k)`;;

let dfkcocl_def = cake_define
  `dfkcocl s ts n k = kcocl s ts n (apply_kcockont s n k)`;;

(* HOL4 ML code, not ported:
val remove = CONV_RULE (RAND_CONV (REWRITE_CONV[dfkcocl_removed]))
*)

(* HOL4 overload (expanded in the port):
     kcocwl0 = apply_kcockont *)

let kcocwl_def = cake_define
  `kcocwl s n ts = apply_kcockont s n ts F`;;

(* HOL4 ML code, not ported:
val kcocwl_code =
tcallify_th [“s:infer_t num_map”, “n:num”]
            (DefnBase.one_line_ify NONE
                     (kcocwl_thm |> CONJUNCTS
                                 |> map SPEC_ALL
                                 |> LIST_CONJ
                                 |> Q.INST [‘s'’ |-> ‘s’]))
*)

(* PENDING: tcallify_th makes it with ML code
Definition kcocwl_code_def:
  kcocwl_code s n = ^kcocwl_code
End *)

let kcocwlR_def = cake_define
  `kcocwlR (s:infer_t spt) (n:num) =
   inv_image (mlt1 (walkstarR (sp2fm (sptree_map encode_infer_t s)))
     LEX (<))
             (\(ts:(infer_t list) list).
                ((FOLDR BAG_INSERT EMPTY_BAG) (MAP encode_infer_t
                  (FLAT ts)),LENGTH ts))`;;

let subterm_def = cake_define
  `subterm = TC (\a b. (?t. b = term_Pair a t) \/ (?t. b = term_Pair
  t a))`;;

(* PENDING: the tail recursion of cocwl
Definition tcocwl_def:
  tcocwl s n is = TAILREC (kcocwl_code s n) is
End *)

(* ---------------------------------------------------------------------
   -
    tail-recursification of cwalkstar
   ---------------------------------------------------------------------
     - *)

let cwalkstarl_def = cake_define_list
  [`cwalkstarl s [] = []`;
   `cwalkstarl s (it :: its) = cwalkstar s it :: cwalkstarl s its`];;

let kcwalkstar_def = cake_define
  `kcwalkstar s it k = cwc (cwalkstar s it) k`;;

let kcwalkstarl_def = cake_define
  `kcwalkstarl s its k = cwc (cwalkstarl s its) k`;;

let kclkont_INDUCT,kclkont_RECURSION = define_datatype
  "kclkont = DBk (num) | APPk (infer_t list) (num) | UVk (num) | \
   CONSk (infer_t list) (num)";;

(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let apply_kclkont_def = cake_define_list_cheat CHEAT_TAC
  [`apply_kclkont s [] its = its`;
   `apply_kclkont s (DBk n :: k) its = apply_kclkont s k
  (Infer_Tvar_db n :: its)`;
   `apply_kclkont s (APPk aits n :: k) its =
      apply_kclkont s k (Infer_Tapp aits n :: its)`;
   `apply_kclkont s (UVk n :: k) its = apply_kclkont s k (Infer_Tuvar
  n :: its)`;
   `apply_kclkont s (CONSk cits n :: k) its =
    kcwalkstarl s cits (\xk'. apply_kclkont s k (Infer_Tapp its
      n :: xk'))`];;

let dfkcwalkstarl_def = cake_define
  `dfkcwalkstarl s t k = kcwalkstarl s t (apply_kclkont s k)`;;

let kcwalkstarwl_def = cake_define_list
  [`kcwalkstarwl s T t k = apply_kclkont s k t`;
   `kcwalkstarwl s F t k = dfkcwalkstarl s t k`];;

(* kcwalkstarwl_thm is the target for tailcallification *)

let star_kwork_def = cake_define
  `star_kwork x1 =
      match x1 with
        [] -> EMPTY_BAG
      | (CONSk its n :: ks) -> (BAG_UNION) ((FOLDR BAG_INSERT
        EMPTY_BAG) its) (star_kwork ks)
      | (_3 :: ks) -> star_kwork ks`;;

let star_workbag_def = cake_define
  `star_workbag v its k =
   (if v then star_kwork k else (BAG_UNION) ((FOLDR BAG_INSERT
     EMPTY_BAG) its) (star_kwork k))`;;

let isCONSk_def = cake_define
  `isCONSk x1 =
      match x1 with
        CONSk _4 _5 -> T
      | _6 -> F`;;

let kcwalkstarwlR_def = cake_define
  `kcwalkstarwlR s =
   inv_image (mlt (inv_image
                    (walkstarR (encode_infer_t o_f sp2fm s))
                    encode_infer_t) LEX
              (<) LEX
              MEASURE (LENGTH o FILTER isCONSk) LEX
              MEASURE (\b. if b then 0 else 1))
             (\(v,its,k). (star_workbag v its k,LENGTH k,k,v))`;;

(* HOL4 ML code, not ported:
val kcwalkstarwl_code = tcallify_th [“s:infer_t num_map”] $
  kcwalkstarwl_thm
*)
(* PENDING: tcallify_th makes it with ML code
Definition kcwalkstarwl_code_def:
  kcwalkstarwl_code s = ^kcwalkstarwl_code
End *)

(* PENDING: the tail recursion of cwalkstarwl
Definition tcwalkstarwl_def:
  tcwalkstarwl s v its k = TAILREC (kcwalkstarwl_code s) (v,its,k)
End *)

(* PENDING: the tail recursion of cwalkstar
Definition tcwalkstar_p1_def:
  tcwalkstar_p1 s its k = tcwalkstarwl s F its k
End *)

(* PENDING: the tail recursion of cwalkstar
Definition tcwalkstar_p2_def:
  tcwalkstar_p2 s its k = tcwalkstarwl s T its k
End *)


(* handle tail-recursification of unify *)

let kcunifyl_def = cake_define
  `kcunifyl s ts us k = cwc (cunifyl s ts us) k`;;

new_type_abbrev("kcunifkont",`: (infer_t list#infer_t list) list`);;
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let apply_cunifk_def = cake_define_list_cheat CHEAT_TAC
  [`apply_cunifk [] x = x`;
   `apply_cunifk ((ts,us) :: k) NONE = apply_cunifk k NONE`;
   `apply_cunifk ((ts,us) :: k) (SOME m) = kcunifyl m ts us
  (apply_cunifk k)`];;

let dfkcunifyl_def = cake_define
  `dfkcunifyl s ts us k = kcunifyl s ts us (apply_cunifk k)`;;

let kcunifywl_def = cake_define
  `kcunifywl s k = apply_cunifk k (SOME s)`;;

(* HOL4 ML code, not ported:
val cunify_code = DefnBase.one_line_ify NONE kcunifywl_thm |>
  tcallify_th []
*)
(* PENDING: tcallify_th makes it with ML code
Definition cunify_code_def:
  cunify_code = ^cunify_code
End *)

let isvars_def = cake_define_list
  [`isvars [] = {}`;
   `isvars (t :: ts) = vars (encode_infer_t t) UNION isvars ts`];;


let cplist_vars_def = cake_define_list
  [`cplist_vars [] = {}`;
   `cplist_vars ((ts,us) :: rest) = isvars ts UNION isvars us UNION
  cplist_vars rest`];;

(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let PFLAT_def = cake_define_list_cheat CHEAT_TAC
  [`PFLAT [] = EMPTY_BAG`;
   `PFLAT (([],[]) :: ps) = PFLAT ps`;
   `PFLAT (([],j :: js) :: ps) =
      BAG_INSERT (encode_infer_t j) (PFLAT (([],js) :: ps))`;
   `PFLAT ((i :: is,js) :: ps) =
      BAG_INSERT (encode_infer_t i) (PFLAT ((is,js) :: ps))`];;

let kcunifywlR_def = cake_define
  `kcunifywlR ((s:infer_t spt),(wl:(infer_t list#infer_t list) list))
  (s0,wl0) <=>
     cwfs s /\ cwfs s0 /\ sp2fm s0 SUBMAP sp2fm s /\
     substvars (encode_infer_t o_f sp2fm s) UNION cplist_vars wl
       SUBSET
     substvars (encode_infer_t o_f sp2fm s0) UNION cplist_vars wl0 /\
     (mlt (walkstarR (sp2fm (sptree_map encode_infer_t s))) LEX (<))
          (PFLAT wl,LENGTH wl)
          (PFLAT wl0,LENGTH wl0)`;;

(* HOL4 overload (expanded in the port):
     kcuR = kcunifywlR *)

(* PENDING: the tail recursion of cunify
Definition tcunify_def:
  tcunify s wl = TAILREC cunify_code (s,wl)
End *)

let t_wfs_def = cake_define
  `t_wfs s = wfs (encode_infer_t o_f s)`;;

let t_vwalk_def = cake_define
  `t_vwalk s v = decode_infer_t (vwalk (encode_infer_t o_f s) v)`;;

let t_walk_def = cake_define
  `t_walk s t = decode_infer_t (walk (encode_infer_t o_f s)
  (encode_infer_t t))`;;

let t_oc_def = cake_define
  `t_oc s t v = oc (encode_infer_t o_f s) (encode_infer_t t) v`;;

(*
Theorem t_oc_ind'[local]:
  ∀s oc'.
  t_wfs s ∧
  (∀t v. v ∈ t_vars t ∧ v ∉ FDOM s ⇒ oc' t v) ∧
  (∀t v u t'. u ∈ t_vars t ∧ (t_vwalk s u = t') ∧ oc' t' v ⇒ oc' t v) ⇒
  (∀a0 a1. oc (FMAP_MAP2 (λ(n,t). encode_infer_t t) s) a0 a1 ⇒ !a0'. (a0
    = encode_infer_t a0') ⇒ oc' a0' a1)
Proof
  NTAC 3 STRIP_TAC >>
ho_match_mp_tac oc_ind >>
rw [] >|
[qpat_x_assum `∀t v. v ∈ t_vars t ∧ v ∉ FDOM s ⇒ oc' t v`
  ho_match_mp_tac >>
     fs [t_vars_def, FMAP_MAP2_THM],
 qpat_x_assum `∀t v u t'. u ∈ t_vars t ∧ (t_vwalk s u = t') ∧ oc' t' v ⇒
   oc' t v` ho_match_mp_tac >>
     rw [t_vars_def] >>
     qexists_tac `u` >>
     rw [] >>
     pop_assum ho_match_mp_tac >>
     rw [encode_vwalk]]
QED

Theorem t_oc_ind:
 ∀s oc'.
  t_wfs s ∧
  (∀t v. v ∈ t_vars t ∧ v ∉ FDOM s ⇒ oc' t v) ∧
  (∀t v u t'. u ∈ t_vars t ∧ (t_vwalk s u = t') ∧ oc' t' v ⇒ oc' t v) ⇒
  (∀a0 a1. t_oc s a0 a1 ⇒ oc' a0 a1)
Proof
rw [t_oc_def] >>
metis_tac [t_oc_ind', FMAP2_FMAP2, FMAP2_id, decode_left_inverse]
QED
*)

let t_ext_s_check_def = cake_define
  `t_ext_s_check s v t =
     OPTION_MAP
       ((o_f) decode_infer_t)
       (ext_s_check (encode_infer_t o_f s) v (encode_infer_t t))`;;

let t_unify_def = cake_define
  `t_unify s t1 t2 =
     OPTION_MAP
       ((o_f) decode_infer_t)
       (unify (encode_infer_t o_f s) (encode_infer_t t1)
         (encode_infer_t t2))`;;

let ts_unify_def = cake_define
  `ts_unify s x2 x3 =
        match (x2,x3) with
          ([],[]) -> SOME s
        | ((t1 :: ts1),(t2 :: ts2)) ->
     (match t_unify s t1 t2 with NONE -> NONE | SOME s' -> ts_unify
       s' ts1 ts2)
        | (_7,_8) -> NONE`;;

let apply_subst_t_def = cake_define
  `apply_subst_t s t = decode_infer_t (subst_APPLY (encode_infer_t
  o_f s) (encode_infer_t t))`;;

let t_walkstar_def = cake_define
  `t_walkstar s t =
     decode_infer_t (walkstar (encode_infer_t o_f s)
       (encode_infer_t t))`;;

let t_collapse_def = cake_define
  `t_collapse s =
     decode_infer_t o_f collapse (encode_infer_t o_f s)`;;

let t_vR_def = cake_define
  `t_vR s = vR (encode_infer_t o_f s)`;;

let t_rangevars_def = cake_define
  `t_rangevars s = rangevars (encode_infer_t o_f s)`;;

(* ---------- Lemmas about unification that don't need to go into the
   encoding ----------*)

(*Theorems about unification for completeness proof*)

(* HOL4 ML code, not ported:
val encode_walkstar_reverse = encode_walkstar |>
                              REWRITE_RULE [t_walkstar_def] |>
                              SPEC_ALL|>UNDISCH|>SYM |>
                              DISCH_ALL |> GEN_ALL;
*)

(*t_compat theorems*)
let t_compat_def = cake_define
  `t_compat s s' <=>
   t_wfs s /\ t_wfs s' /\
   (!t. t_walkstar s' (t_walkstar s t) = t_walkstar s' t)`;;

(*t_compat is preserved under certain types of unification
  Proof basically from HOL*)

hol4_only "++" "APPEND";;
