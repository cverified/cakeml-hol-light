(* ======================================================== *)
(*  unify: ported from HOL4's
    compiler/inference/unifyScript.sml
    A definition theory, with 65 definitions, 2 datatypes and 224
    theorems.  Needed by 9 files of the port.  *)
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
needs "lib/tailrec.ml";;
needs "lib/tcallUnif.ml";;
needs "lib/term.ml";;
needs "lib/unifDef.ml";;
needs "lib/walk.ml";;
needs "lib/walkstar.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "unify"
  ["infer_t"];;
(* HOL4 ancestors outside the port: unifProps transfer cps *)

(* HOL4 unifyScript.sml:20-21: ML code, not ported *)

(* I_o_f[local] *)
let i_o_f = prove
 (`!m. I o_f m = m`,
  CHEAT_TAC);;
add_simp i_o_f;;

let atom_INDUCT,atom_RECURSION = define_datatype
  "atom =
     TC_tag type_ident
   | DB_tag num
   | Tapp_tag
   | Null_tag";;

let encode_infer_t_def,encode_infer_t_ind = define_rec
  [`encode_infer_t (Infer_Tvar_db n) =
      term_Const (DB_tag n)`;
   `encode_infer_t (Infer_Tapp ts tc) =
      term_Pair (term_Const Tapp_tag) (term_Pair (term_Const
          (TC_tag tc)) (encode_infer_ts ts))`;
   `encode_infer_t (Infer_Tuvar n) =
      term_Var n`;
   `encode_infer_ts [] =
      term_Const Null_tag`;
   `encode_infer_ts (CONS t ts) =
      term_Pair (encode_infer_t t) (encode_infer_ts ts)`];;

let encode_infer_t_11 = prove
 (`(!it1 it2. encode_infer_t it1 = encode_infer_t it2 <=> it1 = it2) /\
   (!its1 its2. encode_infer_ts its1 = encode_infer_ts its2 <=>
     its1 = its2)`,
  CHEAT_TAC);;
add_simp encode_infer_t_11;;

(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let decode_infer_t_def,decode_infer_t_ind = define_guess_cheat
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
   `decode_infer_ts (term_Pair s1 s2) = CONS (decode_infer_t s1)
    (decode_infer_ts s2)`;
   `decode_infer_ts _2 = []`];;

let decode_left_inverse = prove
 (`(!t. decode_infer_t (encode_infer_t t) = t) /\
   (!ts. decode_infer_ts (encode_infer_ts ts) = ts)`,
  CHEAT_TAC);;
add_simp decode_left_inverse;;

let decode_left_inverse_I = prove
 (`decode_infer_t o encode_infer_t = I`,
  CHEAT_TAC);;
add_simp decode_left_inverse_I;;

let encode_eq_var = prove
 (`(ast_Var n = encode_infer_t i <=> i = Infer_Tuvar n) /\
   (encode_infer_t i = ast_Var n <=> i = Infer_Tuvar n)`,
  CHEAT_TAC);;
add_simp encode_eq_var;;

(* [local] *)
let decode_right_inverse = prove
 (`(!t. (?t'. t = encode_infer_t t') ==> (encode_infer_t (decode_infer_t
  t) = t)) /\
   (!ts. (?ts'. ts = encode_infer_ts ts') ==> (encode_infer_ts
     (decode_infer_ts ts) = ts))`,
  CHEAT_TAC);;

let option_CASE_MAP = prove
 (`option_CASE (OPTION_MAP f v) n sf =
   option_CASE v n (sf o f)`,
  CHEAT_TAC);;

let list_CASE_MAP = prove
 (`list_CASE (MAP f l) n cf =
   list_CASE l n (\h t. cf (f h) (MAP f t))`,
  CHEAT_TAC);;


(* [local] *)
let decode_option_CASE = prove
 (`decode_infer_t (option_CASE v n sf) =
   option_CASE v (decode_infer_t n) (decode_infer_t o sf)`,
  CHEAT_TAC);;

(* [local] *)
let decode_infer_t_CASE = prove
 (`decode_infer_t (infer_t_CASE it dbf appf uvf) =
   infer_t_CASE it (decode_infer_t o dbf)
                   (\l n. decode_infer_t (appf l n))
                   (decode_infer_t o uvf)`,
  CHEAT_TAC);;

(* "Ramana Kumar unification type to CakeML type" relation *)
let RKC_def = new_definition
  `RKC rkt ct <=> encode_infer_t ct = rkt`;;

(* [transfer_simp] *)
let surj_RKC = prove
 (`surj RKC`,
  CHEAT_TAC);;

let substR_def = new_definition
  `substR fm sp <=> wfs fm /\ sptree_wf sp /\ fm = encode_infer_t o_f
  sp2fm sp`;;

(* [transfer_rule] *)
let substR_FDOM = prove
 (`(FUN_REL substR (=)) FDOM domain`,
  CHEAT_TAC);;

(* [transfer_rule] *)
let substR_FLOOKUP = prove
 (`(FUN_REL substR (FUN_REL (=) (OPTREL RKC))) FLOOKUP (C
  sptree_lookup)`,
  CHEAT_TAC);;

let cwfs_def = new_definition
  `cwfs s <=> swfs (sptree_map encode_infer_t s) /\ sptree_wf s`;;

let sp2fm_map = prove
 (`sp2fm (sptree_map f sp) = f o_f sp2fm sp`,
  CHEAT_TAC);;

(* [transfer_rule] *)
let substR_RFORALL = prove
 (`(FUN_REL (FUN_REL substR (==>)) (==>)) (RES_FORALL wfs) (RES_FORALL
  cwfs)`,
  CHEAT_TAC);;

(* HOL4 unifyScript.sml:185-191: code that the source has in a
   comment *)

(* [transfer_rule] *)
let wfs_rule = prove
 (`(FUN_REL substR (=)) wfs cwfs`,
  CHEAT_TAC);;

let svwalk_result_encodable = prove
 (`sptree_wf fm /\ swfs (sptree_map f fm) /\ (!n. ?y. ast_Var n = f y)
  ==>
   (!x. ?y. svwalk (sptree_map f fm) x = f y)`,
  CHEAT_TAC);;

let cvwalk_def = new_definition
  `cvwalk s n = decode_infer_t (svwalk (sptree_map encode_infer_t s)
  n)`;;

(* [transfer_rule] *)
let cvwalk_rule = prove
 (`(FUN_REL substR (FUN_REL (=) RKC)) vwalk cvwalk`,
  CHEAT_TAC);;

let term_CASE_encode = prove
 (`term_CASE (encode_infer_t v) vf pf cf =
   infer_t_CASE v
                (cf o DB_tag)
                (\l n. pf (term_Const Tapp_tag)
                          (term_Pair (term_Const (TC_tag n))
                            (encode_infer_ts l)))
                vf`,
  CHEAT_TAC);;

(* HOL4 unifyScript.sml:239-247: a theorem that HOL4 states as the
   value of an ML expression: cvwalk_thm *)

let cwalk_def = new_definition
  `cwalk s it = decode_infer_t (swalk (sptree_map encode_infer_t s)
  (encode_infer_t it))`;;

let swalk_result_encodable = prove
 (`!s it. cwfs s ==>
          (?it'. swalk (sptree_map encode_infer_t s) (encode_infer_t
            it) =
                encode_infer_t it')`,
  CHEAT_TAC);;

let swalk_elim = prove
 (`cwfs s ==>
   swalk (sptree_map encode_infer_t s) (encode_infer_t it) =
   encode_infer_t (cwalk s it)`,
  CHEAT_TAC);;

(* [transfer_rule] *)
let substR_walk = prove
 (`(FUN_REL substR (FUN_REL RKC RKC)) walk cwalk`,
  CHEAT_TAC);;

(* HOL4 unifyScript.sml:286-287: the ML values that the definitions
   below antiquote *)
(* HOL4 unifyScript.sml:288-293: a theorem that HOL4 states as the
   value of an ML expression: cwalk_thm *)

let coc_def = new_definition
  `coc s it n = soc (sptree_map encode_infer_t s) (encode_infer_t it)
  n`;;

let soc_encode_ts = prove
 (`cwfs s ==>
   (soc (sptree_map encode_infer_t s) (encode_infer_ts its) n <=>
      EX (\i. soc (sptree_map encode_infer_t s) (encode_infer_t i)
        n) its)`,
  CHEAT_TAC);;

(* [transfer_rule] *)
let substR_oc = prove
 (`(FUN_REL substR (FUN_REL RKC (FUN_REL (=) (=)))) oc coc`,
  CHEAT_TAC);;

(* HOL4 unifyScript.sml:315-321: a theorem that HOL4 states as the
   value of an ML expression: coc_thm *)

let t_vars_def = new_definition
  `t_vars t = vars (encode_infer_t t)`;;

let cunify_def = new_definition
  `cunify s t1 t2 = OPTION_MAP (sptree_map decode_infer_t)
                              (sunify (sptree_map encode_infer_t s)
                                (encode_infer_t t1)
                              (encode_infer_t t2))`;;


let fm2sp_delete = prove
 (`fm2sp (fm \\ k) = sptree_delete k (fm2sp fm)`,
  CHEAT_TAC);;

let domain_fm2sp = prove
 (`!fm. domain (fm2sp fm) = FDOM fm`,
  CHEAT_TAC);;

let swalk_encode_infer_ts_EQ_VAR = prove
 (`swfs s /\ sptree_wf s ==> ~(swalk s (encode_infer_ts ts) = ast_Var
  v)`,
  CHEAT_TAC);;

let encode_t_vs_ts = prove
 (`~(encode_infer_t x = encode_infer_ts l)`,
  CHEAT_TAC);;

let swalk_encode_infer_ts = prove
 (`sptree_wf s ==> swalk s (encode_infer_ts ts) = encode_infer_ts ts`,
  CHEAT_TAC);;

let sunify_wf = prove
 (`!s t1 t2 s'. swfs s /\ sptree_wf s /\ sunify s t1 t2 = SOME s' ==>
  sptree_wf s'`,
  CHEAT_TAC);;

let sunify_constconst = prove
 (`sptree_wf s /\ swfs s ==>
   sunify s (term_Const c1) (term_Const c2) = (if c1 = c2 then SOME
     s else NONE)`,
  CHEAT_TAC);;

let sunify_pairconstconst = prove
 (`sptree_wf s /\ swfs s ==>
   sunify s (term_Pair (term_Const c1) t1) (term_Pair (term_Const c2)
     t2) =
   (if c1 = c2 then sunify s t1 t2 else NONE)`,
  CHEAT_TAC);;

let sunify_result_encodable = prove
 (`!st1t2 s pt1 pt2 s'.
     st1t2 = (s,pt1,pt2) /\ swfs (sptree_map encode_infer_t s) /\
       sptree_wf s /\
     ((?t1 t2. pt1 = encode_infer_t t1 /\ pt2 = encode_infer_t t2) \/
      (?ts1 ts2. pt1 = encode_infer_ts ts1 /\ pt2 = encode_infer_ts
        ts2)) /\
     sunify (sptree_map encode_infer_t s) pt1 pt2 = SOME s' ==>
     (?m. s' = sptree_map encode_infer_t m)`,
  CHEAT_TAC);;

let map_decode_encode = prove
 (`cwfs s ==> sptree_map decode_infer_t (sptree_map encode_infer_t s)
  = s`,
  CHEAT_TAC);;

let sunify_t_elim = prove
 (`cwfs s ==>
   sunify (sptree_map encode_infer_t s) (encode_infer_t t1)
     (encode_infer_t t2) =
   OPTION_MAP (sptree_map encode_infer_t) (cunify s t1 t2)`,
  CHEAT_TAC);;

let option_map_itcase = prove
 (`OPTION_MAP f (infer_t_CASE arg x y z) =
   infer_t_CASE arg (OPTION_MAP f o x) (\l n. OPTION_MAP f (y l n))
                (OPTION_MAP f o z)`,
  CHEAT_TAC);;

let option_map_COND = prove
 (`OPTION_MAP f (COND g t e) = COND g (OPTION_MAP f t) (OPTION_MAP f
  e)`,
  CHEAT_TAC);;

let sptree_map_COND = prove
 (`sptree_map f (COND g t e) = COND g (sptree_map f t) (sptree_map f
  e)`,
  CHEAT_TAC);;

let SOME_COND = prove
 (`SOME (COND g t e) = COND g (SOME t) (SOME e)`,
  CHEAT_TAC);;

let OPTION_MAP_BIND = prove
 (`OPTION_MAP f (OPTION_BIND m mf) =
   OPTION_BIND m (OPTION_MAP f o mf)`,
  CHEAT_TAC);;

let OPTION_BIND_MAP = prove
 (`OPTION_BIND (OPTION_MAP f m) mf =
   OPTION_BIND m (mf o f)`,
  CHEAT_TAC);;

let cunifyl_def = new_definition
  `cunifyl s ts1 ts2 =
   OPTION_MAP (sptree_map decode_infer_t)
              (sunify (sptree_map encode_infer_t s)
                      (encode_infer_ts ts1)
                      (encode_infer_ts ts2))`;;

let sunify_preserves_swfs = prove
 (`swfs s /\ sunify s t1 t2 = SOME s' ==> swfs s'`,
  CHEAT_TAC);;

let substR_unify = prove
 (`(FUN_REL substR (FUN_REL RKC (FUN_REL RKC (OPTREL substR)))) unify
  cunify`,
  CHEAT_TAC);;

(* the termination relation that HOL4 gives is
     MEASURE (infer_t_size o SND)
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
let capply_subst_def,capply_subst_ind = define_shaped_rec
  "nested"
  [`capply_subst s (Infer_Tuvar n) = (match sptree_lookup n s with
                              NONE -> Infer_Tuvar n | SOME it ->
                                  it)`;
   `capply_subst s (Infer_Tapp ts tc) = Infer_Tapp (MAP (capply_subst
    s) ts) tc`;
   `capply_subst s (Infer_Tvar_db n) = Infer_Tvar_db n`];;

(* HOL4 unifyScript.sml:579: a theorem that HOL4 states as the value
   of an ML expression: capply_subst_thm *)

(* HOL4 unifyScript.sml:581-592: a theorem that HOL4 states as the
   value of an ML expression: cunify_thm *)

(* HOL4 unifyScript.sml:594-601: a theorem that HOL4 states as the
   value of an ML expression: cunifyl_NIL2 *)
(* HOL4 unifyScript.sml:602-609: a theorem that HOL4 states as the
   value of an ML expression: cunifyl_NILCONS *)
(* HOL4 unifyScript.sml:610-617: a theorem that HOL4 states as the
   value of an ML expression: cunifyl_CONSNIL *)

(* HOL4 unifyScript.sml:619-630: a theorem that HOL4 states as the
   value of an ML expression: cunifyl_CONS2 *)

let cunify_preserves_cwfs = prove
 (`cwfs s0 /\ cunify s0 t1 t2 = SOME s ==> cwfs s`,
  CHEAT_TAC);;

let cunifyl_thm = prove
 (`cwfs s ==>
   cunifyl s ts1 ts2 =
   (match (ts1,ts2) with
     ([],[]) -> SOME s | (CONS t1 ts1,CONS t2 ts2) -> OPTION_BIND
       (cunify s t1 t2) (\s'. cunifyl s' ts1 ts2) | _3 -> NONE)`,
  CHEAT_TAC);;

let cwalkstar_def = new_definition
  `cwalkstar s it =
   decode_infer_t (walkstar (encode_infer_t o_f sp2fm s)
     (encode_infer_t it))`;;

(* HOL4 unifyScript.sml:660-664: a theorem that HOL4 states as the
   value of an ML expression: walkstar1 *)
(* HOL4 unifyScript.sml:665-668: a theorem that HOL4 states as the
   value of an ML expression: walkstar2 *)

let cvwalk_rwt = prove
 (`sptree_wf s ==> wfs (encode_infer_t o_f sp2fm s) ==>
   vwalk (encode_infer_t o_f sp2fm s) v =
   encode_infer_t (cvwalk s v)`,
  CHEAT_TAC);;

let decode_infer_ts_walkstar = prove
 (`wfs (encode_infer_t o_f sp2fm s) ==>
   decode_infer_ts (walkstar (encode_infer_t o_f sp2fm s)
     (encode_infer_ts l)) =
   MAP (cwalkstar s) l`,
  CHEAT_TAC);;

(* HOL4 unifyScript.sml:692-704: a theorem that HOL4 states as the
   value of an ML expression: cwalkstar_thm *)

(* HOL4 unifyScript.sml:706-709: a theorem that HOL4 states as the
   value of an ML expression: walkstar_def' *)
(* HOL4 unifyScript.sml:710-713: a theorem that HOL4 states as the
   value of an ML expression: walkstar_thm' *)
let infer_t_CASE_RAND = prove
 (`f (infer_t_CASE it tvf taf tuf) =
   infer_t_CASE it (f o tvf) (\l n. f (taf l n)) (f o tuf)`,
  CHEAT_TAC);;

let cunify_unifier = prove
 (`cwfs s /\ cunify s t1 t2 = SOME sx ==>
   cwfs sx /\ subspt s sx /\ cwalkstar sx t1 = cwalkstar sx t2`,
  CHEAT_TAC);;

(* HOL4 unifyScript.sml:750-760: ML code, not ported *)

(* HOL4 unifyScript.sml:762: the ML values that the definitions below
   antiquote *)

cake_declare "cvwalk_code" `:infer_t spt -> num -> num + infer_t`;;

(* PENDING: tcallify_th makes it with ML code *)
(* HOL4 unifyScript.sml:764-766: the definition *)

let sum_CASE_infer_CASE = prove
 (`sum_CASE (infer_t_CASE i vf af uf) lf rf =
   infer_t_CASE i (\v. sum_CASE (vf v) lf rf)
              (\l n. sum_CASE (af l n) lf rf)
              (\u. sum_CASE (uf u) lf rf)`,
  CHEAT_TAC);;

let cvwalk_preserves_precond = prove
 (`!x y.
   (\n. cwfs s) x /\ cvwalk_code s x = INL y ==> (\n. cwfs s) y`,
  CHEAT_TAC);;

let cvwalkR_def = new_definition
  `cvwalkR sigma = (\v v0. vR (encode_infer_t o_f sp2fm sigma) v v0)`;;

let cvwalk_ensures_decrease = prove
 (`!x y. (\n. cwfs s) x /\ cvwalk_code s x = INL y ==> cvwalkR s y x`,
  CHEAT_TAC);;

let WF_cvwalkR = prove
 (`!x. (\n. cwfs s) x ==> WF (cvwalkR s)`,
  CHEAT_TAC);;

let cvwalk_tcallish = prove
 (`!x. (\n. cwfs s) x ==>
       cvwalk s x = TAILCALL (cvwalk_code s) (cvwalk s) x`,
  CHEAT_TAC);;

let cvwalk_cleaned = prove
 (`!x. (\n. cwfs s) x ==> cvwalk s x = TAILREC (cvwalk_code s) x`,
  CHEAT_TAC);;

let tcvwalk_def = new_definition
  `tcvwalk s n = TAILREC (cvwalk_code s) n`;;

(* [local] *)
let cvwalk_eta = prove
 (`(\n. cvwalk_code s n) = cvwalk_code s`,
  CHEAT_TAC);;

(* HOL4 unifyScript.sml:833-837: a theorem that HOL4 states as the
   value of an ML expression: tcvwalk_thm *)

(* HOL4 unifyScript.sml:839-840: a theorem that HOL4 states as the
   value of an ML expression: tcvwalk_correct *)

let tcwalk_def = new_definition
  `tcwalk s it = (match it with
                   Infer_Tvar_db c -> Infer_Tvar_db c | Infer_Tapp
                     l n -> Infer_Tapp l n | Infer_Tuvar v -> tcvwalk
                     s v)`;;

let tcwalk_correct = prove
 (`!s it. cwfs s ==> cwalk s it = tcwalk s it`,
  CHEAT_TAC);;

let cocl_def,cocl_ind = define_rec
  [`cocl s [] n <=> F`;
   `cocl s (CONS i is) n <=> coc s i n \/ cocl s is n`];;

let cocl_EXISTS = prove
 (`cocl s its n <=> EX (\i. coc s i n) its`,
  CHEAT_TAC);;

(* HOL4 unifyScript.sml:866: a theorem that HOL4 states as the value
   of an ML expression: coc_thm' *)

let kcoc_def = new_definition
  `kcoc s it n k = cwc (coc s it n) k`;;

let kcocl_def = new_definition
  `kcocl s its n k = cwc (cocl s its n) k`;;

let contify_infer_case = prove
 (`contify k (infer_t_CASE it cf af uf) =
   contify (\it. match it with Infer_Tvar_db c -> contify k (cf c) |
     Infer_Tapp l n -> contify k (af l n) | Infer_Tuvar v -> contify k
     (uf v))
           it`,
  CHEAT_TAC);;

(* HOL4 unifyScript.sml:886-893: a theorem that HOL4 states as the
   value of an ML expression: kcoc_thm *)

let cwc_OR = prove
 (`cwc (bool (\/) b) k = (if b then k (K T) else k I)`,
  CHEAT_TAC);;

let kcocl_Ky = prove
 (`kcocl s t n (\x. y) = y`,
  CHEAT_TAC);;

(* HOL4 unifyScript.sml:907-916: a theorem that HOL4 states as the
   value of an ML expression: kcocl_thm *)

new_type_abbrev("kcockont",`:(infer_t list) list`);;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let apply_kcockont_def,apply_kcockont_ind = define_wf
  `MEASURE (\(x0,x1,x2,x3). list_size infer_t_size1 x2)`
  [`apply_kcockont s n [] b = b`;
   `apply_kcockont s n (CONS ts rest) b =
    (if b then apply_kcockont s n rest T else kcocl s ts n
        (apply_kcockont s n rest))`];;

let apply_kcockontT = prove
 (`apply_kcockont s n ts T = T`,
  CHEAT_TAC);;
add_simp apply_kcockontT;;

let dfkcoc_def = new_definition
  `dfkcoc s t n k = kcoc s t n (apply_kcockont s n k)`;;

let dfkcocl_def = new_definition
  `dfkcocl s ts n k = kcocl s ts n (apply_kcockont s n k)`;;

(* HOL4 unifyScript.sml:941-942: a theorem that HOL4 states as the
   value of an ML expression: apply_kcockont_thm *)

(* HOL4 unifyScript.sml:944-947: a theorem that HOL4 states as the
   value of an ML expression: dfkcoc_thm *)

(* HOL4 unifyScript.sml:949-953: a theorem that HOL4 states as the
   value of an ML expression: dfkcocl_thm *)

let apply_kcockont_HDNIL = prove
 (`apply_kcockont s n (CONS [] k) = apply_kcockont s n k`,
  CHEAT_TAC);;

let dfkcocl_HDNIL = prove
 (`dfkcocl s ts n (CONS [] k) = dfkcocl s ts n k`,
  CHEAT_TAC);;

let dfkcocl_removed = prove
 (`dfkcocl s ts n k = apply_kcockont s n (CONS ts k) F`,
  CHEAT_TAC);;

(* HOL4 unifyScript.sml:975: ML code, not ported *)
(* HOL4 unifyScript.sml:976: a theorem that HOL4 states as the value
   of an ML expression: dfkcocl_nonrecursive0 *)

(* HOL4 unifyScript.sml:978-983: a theorem that HOL4 states as the
   value of an ML expression: dfkcocl_nonrecursive *)

(* HOL4 unifyScript.sml:985: the overload kcocwl0, which the port
   expands *)

(* HOL4 unifyScript.sml:987-991: a theorem that HOL4 states as the
   value of an ML expression: kcocwl0_thm *)

let kcocwl_def = new_definition
  `kcocwl s n ts = apply_kcockont s n ts F`;;

let kcocwl0_varcheck = prove
 (`apply_kcockont s n ts b = (if b then T else kcocwl s n ts)`,
  CHEAT_TAC);;

(* HOL4 unifyScript.sml:1001-1006: a theorem that HOL4 states as the
   value of an ML expression: kcocwl_thm *)

(* HOL4 unifyScript.sml:1008-1014: the ML values that the definitions
   below antiquote *)

cake_declare "kcocwl_code"
  `:infer_t spt -> num -> kcockont -> kcockont + bool`;;

(* PENDING: tcallify_th makes it with ML code *)
(* HOL4 unifyScript.sml:1016-1018: the definition *)

let kcocwl_preserves_precond = prove
 (`!x y. (\ts. cwfs s) x /\ kcocwl_code s n x = INL y ==>
         (\ts. cwfs s) y`,
  CHEAT_TAC);;

let kcocwlR_def = new_definition
  `kcocwlR (s:infer_t spt) (n:num) =
   inv_image (mlt1 (walkstarR (sp2fm (sptree_map encode_infer_t s)))
     LEX (<))
             (\(ts:(infer_t list) list).
                ((FOLDR BAG_INSERT EMPTY_BAG) (MAP encode_infer_t
                  (FLAT ts)),LENGTH ts))`;;

let WF_kcocwlR = prove
 (`cwfs s ==> WF (kcocwlR s n)`,
  CHEAT_TAC);;

let FINITE_BAG_FOLDR_INSERT = prove
 (`FINITE_BAG (ITLIST BAG_INSERT xs b) = FINITE_BAG b`,
  CHEAT_TAC);;
add_simp FINITE_BAG_FOLDR_INSERT;;

let FOLDR_BAG_INSERT_UNION = prove
 (`ITLIST BAG_INSERT xs b = (BAG_UNION) b ((FOLDR BAG_INSERT
  EMPTY_BAG) xs)`,
  CHEAT_TAC);;

let BAG_IN_BAG_OF_LIST = prove
 (`BAG_IN e ((FOLDR BAG_INSERT EMPTY_BAG) xs) = MEM e xs`,
  CHEAT_TAC);;

let sum_CASE_list_CASE = prove
 (`sum_CASE (list_CASE l n cf) lf rf =
   list_CASE l (sum_CASE n lf rf) (\h t. sum_CASE (cf h t) lf rf)`,
  CHEAT_TAC);;

let walkstarR_trans = prove
 (`walkstarR s t1 t2 /\ walkstarR s t2 t3 ==> walkstarR s t1 t3`,
  CHEAT_TAC);;

let subterm_def = new_definition
  `subterm = TC (\a b. (?t. b = term_Pair a t) \/ (?t. b = term_Pair
  t a))`;;

let subterm_thm = prove
 (`(subterm t (term_Pair u v) <=> t = u \/ t = v \/ subterm t u \/
  subterm t v) /\
   (subterm t (ast_Var vnm) <=> F) /\
   (subterm t (term_Const c) <=> F)`,
  CHEAT_TAC);;
add_simp subterm_thm;;

let subterm_pair_count = prove
 (`!t u. subterm t u ==> pair_count t < pair_count u`,
  CHEAT_TAC);;

let subterm_REFL = prove
 (`~(subterm t t)`,
  CHEAT_TAC);;
add_simp subterm_REFL;;

let subterm_TRANS = prove
 (`subterm t u /\ subterm u v ==> subterm t v`,
  CHEAT_TAC);;

let subterm_walkstarR = prove
 (`!t u. subterm t u ==> walkstarR s t u`,
  CHEAT_TAC);;

let MEM_subterm_encode = prove
 (`!i is. MEM i is ==> subterm (encode_infer_t i) (encode_infer_ts is)`,
  CHEAT_TAC);;

let walkstar_opth = prove
 (`cwfs s /\ tcwalk s i = Infer_Tapp is nm /\ MEM i0 is ==>
   walkstarR (sp2fm (sptree_map encode_infer_t s))
             (encode_infer_t i0)
             (encode_infer_t i)`,
  CHEAT_TAC);;

let kcocwl_ensures_decrease = prove
 (`!x y. (\v. cwfs s) x /\ kcocwl_code s n x = INL y ==>
         kcocwlR s n y x`,
  CHEAT_TAC);;

let kcocwl_tcallish = prove
 (`!x. (\v. cwfs s) x ==>
       kcocwl s n x = TAILCALL (kcocwl_code s n) (kcocwl s n) x`,
  CHEAT_TAC);;

let kcocwl_cleaned = prove
 (`!x. (\v. cwfs s) x ==> kcocwl s n x = TAILREC (kcocwl_code s n) x`,
  CHEAT_TAC);;

let tcocwl_def = new_definition
  `tcocwl s n is = TAILREC (kcocwl_code s n) is`;;

(* HOL4 unifyScript.sml:1207-1208: a theorem that HOL4 states as the
   value of an ML expression: tcocwl_correct0 *)
let tcocwl_correct = prove
 (`cwfs s ==> cocl s ts n = tcocwl s n [ts]`,
  CHEAT_TAC);;
(* [local] *)
let disj2cond = prove
 (`p \/ q <=> (if p then T else q)`,
  CHEAT_TAC);;

(* HOL4 unifyScript.sml:1217-1222: a theorem that HOL4 states as the
   value of an ML expression: tcocwl_thm *)

(* ----------------------------------------------------------------------
    tail-recursification of cwalkstar
   ---------------------------------------------------------------------- *)

let cwalkstarl_def,cwalkstarl_ind = define_rec
  [`cwalkstarl s [] = []`;
   `cwalkstarl s (CONS it its) = CONS (cwalkstar s it) (cwalkstarl
    s its)`];;
add_simp cwalkstarl_def;;

let MAP_cwalkstar = prove
 (`MAP (cwalkstar s) l = cwalkstarl s l`,
  CHEAT_TAC);;

let kcwalkstar_def = new_definition
  `kcwalkstar s it k = cwc (cwalkstar s it) k`;;

let kcwalkstarl_def = new_definition
  `kcwalkstarl s its k = cwc (cwalkstarl s its) k`;;

(* HOL4 unifyScript.sml:1247-1252: a theorem that HOL4 states as the
   value of an ML expression: cwalkstar_thm' *)

(* HOL4 unifyScript.sml:1254-1263: a theorem that HOL4 states as the
   value of an ML expression: kcwalkstar_thm *)

(* HOL4 unifyScript.sml:1265-1274: a theorem that HOL4 states as the
   value of an ML expression: kcwalkstarl_thm0 *)

(* HOL4 unifyScript.sml:1276-1277: a theorem that HOL4 states as the
   value of an ML expression: kcwalkstarl_thm *)

let kclkont_INDUCT,kclkont_RECURSION = define_datatype
  "kclkont =
     DBk num
   | APPk (infer_t list) num
   | UVk num
   | CONSk (infer_t list) num";;

let _ = size_thms "kclkont";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let apply_kclkont_def,apply_kclkont_ind = define_wf
  `MEASURE (\(x0,x1,x2). list_size kclkont_size x1)`
  [`apply_kclkont s [] its = its`;
   `apply_kclkont s (CONS (DBk n) k) its = apply_kclkont s k (CONS
    (Infer_Tvar_db n) its)`;
   `apply_kclkont s (CONS (APPk aits n) k) its =
      apply_kclkont s k (CONS (Infer_Tapp aits n) its)`;
   `apply_kclkont s (CONS (UVk n) k) its = apply_kclkont s k (CONS
    (Infer_Tuvar n) its)`;
   `apply_kclkont s (CONS (CONSk cits n) k) its =
    kcwalkstarl s cits (\xk'. apply_kclkont s k (CONS
        (Infer_Tapp its n) xk'))`];;

(* HOL4 unifyScript.sml: the case constant that its Datatype makes
   for the continuation of the walk *)

let kclkont_CASE = new_recursive_definition kclkont_RECURSION
  `(kclkont_CASE (DBk n) dbf appf uvf consf = dbf n) /\
   (kclkont_CASE (APPk its n) dbf appf uvf consf = appf its n) /\
   (kclkont_CASE (UVk n) dbf appf uvf consf = uvf n) /\
   (kclkont_CASE (CONSk its n) dbf appf uvf consf = consf its n)`;;

let dfkcwalkstarl_def = new_definition
  `dfkcwalkstarl s t k = kcwalkstarl s t (apply_kclkont s k)`;;

(* HOL4 unifyScript.sml:1298-1299: a theorem that HOL4 states as the
   value of an ML expression: apply_kclkont5 *)

(* HOL4 unifyScript.sml:1301-1306: a theorem that HOL4 states as the
   value of an ML expression: apply_kclkont_thm *)

(* HOL4 unifyScript.sml:1308-1313: a theorem that HOL4 states as the
   value of an ML expression: dfkcwalkstarl_thm *)

let kcwalkstarwl_def = define_general
  [`kcwalkstarwl s T t k = apply_kclkont s k t`;
   `kcwalkstarwl s F t k = dfkcwalkstarl s t k`];;

(* HOL4 unifyScript.sml:1320-1324: a theorem that HOL4 states as the
   value of an ML expression: kcwalkstarwl_thm *)

(* HOL4 unifyScript.sml:1326: a theorem that HOL4 states as the value
   of an ML expression: dfkcwalkstarl_removed *)
let apply_kclkont_ID = prove
 (`apply_kclkont s [] = I`,
  CHEAT_TAC);;
add_simp apply_kclkont_ID;;

let cwalkstar_to_dfkcwalkstarl = prove
 (`cwalkstar s t = HD (dfkcwalkstarl s [t] [])`,
  CHEAT_TAC);;

(* kcwalkstarwl_thm is the target for tailcallification *)

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let star_kwork_def,star_kwork_ind = define_wf
  `MEASURE (\x0. list_size kclkont_size x0)`
  [`star_kwork x1 =
      match x1 with
        [] -> EMPTY_BAG
      | CONS (CONSk its n) ks -> (BAG_UNION) ((FOLDR BAG_INSERT
        EMPTY_BAG) its) (star_kwork ks)
      | (CONS _4 ks) -> star_kwork ks`];;
add_simp star_kwork_def;;

let star_workbag_def = new_definition
  `star_workbag v its k =
   (if v then star_kwork k else (BAG_UNION) ((FOLDR BAG_INSERT
     EMPTY_BAG) its) (star_kwork k))`;;

let FINITE_star_kwork = prove
 (`FINITE_BAG (star_kwork ks)`,
  CHEAT_TAC);;
add_simp FINITE_star_kwork;;

let FINITE_star_workbag = prove
 (`FINITE_BAG (star_workbag v its k)`,
  CHEAT_TAC);;
add_simp FINITE_star_workbag;;

let isCONSk_def = new_definition
  `isCONSk x1 =
      match x1 with
        CONSk _5 _6 -> T
      | _7 -> F`;;
add_simp isCONSk_def;;

let kcwalkstarwlR_def = new_definition
  `kcwalkstarwlR s =
   inv_image (mlt (inv_image
                    (walkstarR (encode_infer_t o_f sp2fm s))
                    encode_infer_t) LEX
              (<) LEX
              MEASURE (LENGTH o FILTER isCONSk) LEX
              MEASURE (\b. if b then 0 else 1))
             (\(v,its,k). (star_workbag v its k,LENGTH k,k,v))`;;

let WF_kcwalkstarwlR = prove
 (`cwfs s ==> WF (kcwalkstarwlR s)`,
  CHEAT_TAC);;

(* HOL4 unifyScript.sml:1391: the ML values that the definitions
   below antiquote *)
cake_declare "kcwalkstarwl_code"
  `:infer_t spt -> bool#infer_t list#kclkont list ->
    (bool#infer_t list#kclkont list) + infer_t list`;;

(* PENDING: tcallify_th makes it with ML code *)
(* HOL4 unifyScript.sml:1392-1394: the definition *)

let kcwalkstarwl_preserves_precond = prove
 (`!x y. (\(v,t,k). cwfs s) x /\ kcwalkstarwl_code s x = INL y ==>
         (\(v,t,k). cwfs s) y`,
  CHEAT_TAC);;

let kcwalkstarwl_ensures_decrease = prove
 (`!x y. (\(v,its,k). cwfs s) x /\ kcwalkstarwl_code s x = INL y ==>
         kcwalkstarwlR s y x`,
  CHEAT_TAC);;

let sum_CASE_wstarcont_CASE = prove
 (`sum_CASE (kclkont_CASE k dbf appf uvf consf) lf rf =
   kclkont_CASE k
                (\n. sum_CASE (dbf n) lf rf)
                (\its n. sum_CASE (appf its n) lf rf)
                (\n. sum_CASE (uvf n) lf rf)
                (\its n. sum_CASE (consf its n) lf rf)`,
  CHEAT_TAC);;

let kcwalkstarwl_tcallish = prove
 (`!x. (\(v,its,k). cwfs s) x ==>
       (\(v,its,k). kcwalkstarwl s v its k) x =
       TAILCALL (kcwalkstarwl_code s) (\(v,its,k). kcwalkstarwl s v
         its k) x`,
  CHEAT_TAC);;

let kcwalkstarwl_cleaned = prove
 (`!x. (\(v,its,k). cwfs s) x ==>
       (\(v,its,k). kcwalkstarwl s v its k) x = TAILREC
         (kcwalkstarwl_code s) x`,
  CHEAT_TAC);;

let tcwalkstarwl_def = new_definition
  `tcwalkstarwl s v its k = TAILREC (kcwalkstarwl_code s) (v,its,k)`;;

let tcwalkstar_p1_def = new_definition
  `tcwalkstar_p1 s its k = tcwalkstarwl s F its k`;;

let tcwalkstar_p2_def = new_definition
  `tcwalkstar_p2 s its k = tcwalkstarwl s T its k`;;

(* HOL4 unifyScript.sml:1492-1503: a theorem that HOL4 states as the
   value of an ML expression: tcwalkstarwl_thm *)

(* HOL4 unifyScript.sml:1505-1506: a theorem that HOL4 states as the
   value of an ML expression: tcwalkstarwl_correct0 *)

let tcwalkstarwl_correct = prove
 (`cwfs s ==> cwalkstar s it = HD (tcwalkstar_p1 s [it] [])`,
  CHEAT_TAC);;


(* handle tail-recursification of unify *)

let kcunifyl_def = new_definition
  `kcunifyl s ts us k = cwc (cunifyl s ts us) k`;;

(* HOL4 unifyScript.sml:1523-1525: a theorem that HOL4 states as the
   value of an ML expression: cunifyl_thm' *)

(* HOL4 unifyScript.sml:1527-1541: a theorem that HOL4 states as the
   value of an ML expression: kcunifyl_thm *)

new_type_abbrev("kcunifkont",`:(infer_t list#infer_t list) list`);;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let apply_cunifk_def,apply_cunifk_ind = define_wf
  `MEASURE (\(x0,x1). list_size (pair_size infer_t_size1 infer_t_size1)
  x0)`
  [`apply_cunifk [] x = x`;
   `apply_cunifk (CONS (ts,us) k) NONE = apply_cunifk k NONE`;
   `apply_cunifk (CONS (ts,us) k) (SOME m) = kcunifyl m ts us
    (apply_cunifk k)`];;

let apply_cunif_NONE = prove
 (`apply_cunifk k NONE = NONE`,
  CHEAT_TAC);;
add_simp apply_cunif_NONE;;

let dfkcunifyl_def = new_definition
  `dfkcunifyl s ts us k = kcunifyl s ts us (apply_cunifk k)`;;

let abs_EQ_apply_cunifk = prove
 (`(\ov. match ov with NONE -> NONE | SOME x -> dfkcunifyl x ts us k) =
   apply_cunifk (CONS (ts,us) k)`,
  CHEAT_TAC);;

(* HOL4 unifyScript.sml:1568-1569: a theorem that HOL4 states as the
   value of an ML expression: apply_cunifk_thm *)

(* HOL4 unifyScript.sml:1571-1577: a theorem that HOL4 states as the
   value of an ML expression: dfkcunifyl_thm *)

(* HOL4 unifyScript.sml:1579-1582: a theorem that HOL4 states as the
   value of an ML expression: cunifywl0 *)

let kcunifywl_def = new_definition
  `kcunifywl s k = apply_cunifk k (SOME s)`;;

(* HOL4 unifyScript.sml:1588-1591: a theorem that HOL4 states as the
   value of an ML expression: kcunifywl_thm *)

(* HOL4 unifyScript.sml:1593: ML code, not ported *)
cake_declare "cunify_code"
  `:(infer_t spt)#kcunifkont ->
    ((infer_t spt)#kcunifkont) + (infer_t spt)option`;;

(* PENDING: tcallify_th makes it with ML code *)
(* HOL4 unifyScript.sml:1594-1596: the definition *)

let kcunifywl_tcallish = prove
 (`!x. (\(s,k). cwfs s) x ==>
       (\(s,k). kcunifywl s k) x =
       TAILCALL cunify_code (\(s,k). kcunifywl s k) x`,
  CHEAT_TAC);;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let isvars_def,isvars_ind = define_wf
  `MEASURE (\x0. infer_t_size1 x0)`
  [`isvars [] = {}`;
   `isvars (CONS t ts) = vars (encode_infer_t t) UNION isvars ts`];;
add_simp isvars_def;;

let FINITE_isvars = prove
 (`FINITE (isvars ts)`,
  CHEAT_TAC);;
add_simp FINITE_isvars;;


(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let cplist_vars_def,cplist_vars_ind = define_wf
  `MEASURE (\x0. list_size (pair_size infer_t_size1 infer_t_size1) x0)`
  [`cplist_vars [] = {}`;
   `cplist_vars (CONS (ts,us) rest) = isvars ts UNION isvars us
    UNION cplist_vars rest`];;
add_simp cplist_vars_def;;

let FINITE_cplist_vars = prove
 (`FINITE (cplist_vars wl)`,
  CHEAT_TAC);;
add_simp FINITE_cplist_vars;;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let PFLAT_def,PFLAT_ind = define_wf
  `MEASURE (\x0. list_size (pair_size infer_t_size1 infer_t_size1) x0)`
  [`PFLAT [] = EMPTY_BAG`;
   `PFLAT (CONS ([],[]) ps) = PFLAT ps`;
   `PFLAT (CONS ([],CONS j js) ps) =
      BAG_INSERT (encode_infer_t j) (PFLAT (CONS ([],js) ps))`;
   `PFLAT (CONS (CONS i is,js) ps) =
      BAG_INSERT (encode_infer_t i) (PFLAT (CONS (is,js) ps))`];;
add_simp PFLAT_def;;

let FINITE_BAG_PFLAT = prove
 (`!ps. FINITE_BAG (PFLAT ps)`,
  CHEAT_TAC);;
add_simp FINITE_BAG_PFLAT;;

let kcunifywlR_def = new_definition
  `kcunifywlR ((s:infer_t spt),(wl:(infer_t list#infer_t list) list))
  (s0,wl0) <=>
     cwfs s /\ cwfs s0 /\ sp2fm s0 SUBMAP sp2fm s /\
     substvars (encode_infer_t o_f sp2fm s) UNION cplist_vars wl
       SUBSET
     substvars (encode_infer_t o_f sp2fm s0) UNION cplist_vars wl0 /\
     (mlt (walkstarR (sp2fm (sptree_map encode_infer_t s))) LEX (<))
          (PFLAT wl,LENGTH wl)
          (PFLAT wl0,LENGTH wl0)`;;

(* HOL4 unifyScript.sml:1659: the overload kcuR, which the port
   expands *)

let WF_kcunifywlR = prove
 (`WF kcunifywlR`,
  CHEAT_TAC);;

let PFLAT_CONS2 = prove
 (`PFLAT (CONS (l1,CONS h2 t2) rest) =
   BAG_INSERT (encode_infer_t h2) (PFLAT (CONS (l1,t2) rest))`,
  CHEAT_TAC);;
add_simp PFLAT_CONS2;;

let mlt_BAG_INSERT2 = prove
 (`FINITE_BAG b ==>
   mlt R b (BAG_INSERT x (BAG_INSERT y b))`,
  CHEAT_TAC);;

let cwfs_insert_tvar_db = prove
 (`~(v IN domain s) /\ cwfs s ==> cwfs (sptree_insert v (Infer_Tvar_db
  c) s)`,
  CHEAT_TAC);;

let tcwalk_EQ_Infer_Tuvar = prove
 (`cwfs s /\ tcwalk s t = Infer_Tuvar v ==> ~(v IN domain s) /\ (?u. t
  = Infer_Tuvar u)`,
  CHEAT_TAC);;

(* HOL4 unifyScript.sml:1814-1818: a theorem that HOL4 states as the
   value of an ML expression: svwalk_result_encodable' *)

let tcvwalk_substvars = prove
 (`cwfs s /\ tcvwalk s v = t ==>
   t = Infer_Tuvar v /\ ~(v IN domain s) \/
   vars (encode_infer_t t) SUBSET substvars (encode_infer_t o_f
     sp2fm s)`,
  CHEAT_TAC);;

let tcwalk_rangevars = prove
 (`cwfs s /\ tcwalk s t = u ==>
   vars (encode_infer_t u) SUBSET rangevars (encode_infer_t o_f sp2fm
     s) UNION
                             vars (encode_infer_t t)`,
  CHEAT_TAC);;

let cwfs_var2_extend = prove
 (`cwfs s /\ ~(v1 = v2) /\ ~(v1 IN domain s) /\ ~(v2 IN domain s) ==>
   cwfs (sptree_insert v1 (Infer_Tuvar v2) s)`,
  CHEAT_TAC);;

let vars_encode_infer_ts = prove
 (`vars (encode_infer_ts is) = isvars is`,
  CHEAT_TAC);;

let PFLAT_NIL1 = prove
 (`PFLAT (CONS ([],l2) rest) =
   (BAG_UNION) ((FOLDR BAG_INSERT EMPTY_BAG) (MAP encode_infer_t
     l2)) (PFLAT rest)`,
  CHEAT_TAC);;
add_simp PFLAT_NIL1;;

let PFLAT_eqn = prove
 (`!l1 l2.
     PFLAT (CONS (l1,l2) rest) =
     (BAG_UNION) ((FOLDR BAG_INSERT EMPTY_BAG) (MAP encode_infer_t
       l1))
               ((BAG_UNION) ((FOLDR BAG_INSERT EMPTY_BAG) (MAP
                 encode_infer_t l2)) (PFLAT rest))`,
  CHEAT_TAC);;

let vars_walkstar_encode_infer_ts = prove
 (`wfs s ==>
   vars (walkstar s (encode_infer_ts L)) =
   UNIONS {vars (walkstar s (encode_infer_t e)) | MEM e L}`,
  CHEAT_TAC);;

let kcunifywl_ensures_decrease = prove
 (`!x. (\(s,k). cwfs s) x /\ cunify_code x = INL y ==> kcunifywlR y x`,
  CHEAT_TAC);;

let kcunifywl_preserves_precond = prove
 (`!x y. (\(s,k). cwfs s) x /\ cunify_code x = INL y ==> (\(s,k). cwfs
  s) y`,
  CHEAT_TAC);;

let kcunifywl_cleaned = prove
 (`!x. (\(s,wl). cwfs s) x ==>
       (\(s,wl). kcunifywl s wl) x = TAILREC cunify_code x`,
  CHEAT_TAC);;

let tcunify_def = new_definition
  `tcunify s wl = TAILREC cunify_code (s,wl)`;;

(* HOL4 unifyScript.sml:2007-2012: a theorem that HOL4 states as the
   value of an ML expression: tcunify_thm *)

(* HOL4 unifyScript.sml:2014-2015: a theorem that HOL4 states as the
   value of an ML expression: tcunify_correct0 *)

let tcunify_correct = prove
 (`cwfs s ==> cunify s t1 t2 = tcunify s [([t1],[t2])]`,
  CHEAT_TAC);;

(* decode_right_inverse[local] *)
let unify_decode_right_inverse = prove
 (`(!t. (?t'. t = encode_infer_t t') ==> (encode_infer_t (decode_infer_t
  t) = t)) /\
   (!ts. (?ts'. ts = encode_infer_ts ts') ==> (encode_infer_ts
     (decode_infer_ts ts) = ts))`,
  CHEAT_TAC);;

let t_wfs_def = new_definition
  `t_wfs s = wfs (encode_infer_t o_f s)`;;

let t_vwalk_def = new_definition
  `t_vwalk s v = decode_infer_t (vwalk (encode_infer_t o_f s) v)`;;

(* [local] *)
let t_vwalk_ind' = prove
 (`!s'. t_wfs s' ==>
    (!P.
      (!v. (!v1 u. (FLOOKUP s' v = SOME v1) /\ (v1 = Infer_Tuvar u)
        ==> P u) ==> P v) ==>
      (!v. P v))`,
  CHEAT_TAC);;

(* HOL4 unifyScript.sml:2064-2065: a theorem that HOL4 states as the
   value of an ML expression: t_vwalk_ind *)

let t_vwalk_eqn = prove
 (`!s.
    t_wfs s ==>
    (!v.
      t_vwalk s v =
      (match FLOOKUP s v with NONE -> Infer_Tuvar v | SOME
        (Infer_Tuvar u) -> t_vwalk s u | SOME (Infer_Tapp ts tc) ->
        Infer_Tapp ts tc | SOME (Infer_Tvar_db n) -> Infer_Tvar_db n))`,
  CHEAT_TAC);;

let t_walk_def = new_definition
  `t_walk s t = decode_infer_t (walk (encode_infer_t o_f s)
  (encode_infer_t t))`;;

let t_walk_eqn = prove
 (`(!s v. t_walk s (Infer_Tuvar v) = t_vwalk s v) /\
   (!s ts tc. t_walk s (Infer_Tapp ts tc) = Infer_Tapp ts tc) /\
   (!s n. t_walk s (Infer_Tvar_db n) = Infer_Tvar_db n)`,
  CHEAT_TAC);;

let t_oc_def = new_definition
  `t_oc s t v = oc (encode_infer_t o_f s) (encode_infer_t t) v`;;

(* HOL4 unifyScript.sml:2110-2141: code that the source has in a
   comment *)

(* [local] *)
let encode_vwalk = prove
 (`!s. t_wfs s ==> (!u. vwalk (encode_infer_t o_f s) u =
  encode_infer_t (t_vwalk s u))`,
  CHEAT_TAC);;

(* [local] *)
let t_oc_eqn_help = prove
 (`!l v s.
   oc (encode_infer_t o_f s) (encode_infer_ts l) v <=>
   EX (\t. oc (encode_infer_t o_f s) (encode_infer_t t) v) l`,
  CHEAT_TAC);;

let t_oc_eqn = prove
 (`!s. t_wfs s ==>
    (!t v. t_oc s t v =
      (match t_walk s t with Infer_Tuvar u -> v = u | Infer_Tapp ts
        tc -> EX (\t. t_oc s t v) ts | Infer_Tvar_db n -> F))`,
  CHEAT_TAC);;

let t_ext_s_check_def = new_definition
  `t_ext_s_check s v t =
     OPTION_MAP
       ((o_f) decode_infer_t)
       (ext_s_check (encode_infer_t o_f s) v (encode_infer_t t))`;;

let t_ext_s_check_eqn = prove
 (`!s v t.
    t_ext_s_check s v t = (if t_oc s t v then NONE else SOME (s |+
      (v,t)))`,
  CHEAT_TAC);;

let t_unify_def = new_definition
  `t_unify s t1 t2 =
     OPTION_MAP
       ((o_f) decode_infer_t)
       (unify (encode_infer_t o_f s) (encode_infer_t t1)
         (encode_infer_t t2))`;;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let ts_unify_def,ts_unify_ind = define_wf
  `MEASURE (\(x0,x1,x2). infer_t_size1 x1 + infer_t_size1 x2)`
  [`ts_unify s x2 x3 =
        match (x2,x3) with
          ([],[]) -> SOME s
        | ((CONS t1 ts1),(CONS t2 ts2)) ->
     (match t_unify s t1 t2 with NONE -> NONE | SOME s' -> ts_unify
       s' ts1 ts2)
        | (_8,_9) -> NONE`];;

(* [local] *)
let encode_walk = prove
 (`!s. t_wfs s ==>
       (!t. walk (encode_infer_t o_f s) (encode_infer_t t) =
         encode_infer_t (t_walk s t))`,
  CHEAT_TAC);;

(* [local] *)
let encode_pair_cases = prove
 (`(!t t1 t2.
     (encode_infer_t t = term_Pair t1 t2) ==>
       ((t1 = term_Const Tapp_tag) /\
        (?tc ts. t2 = term_Pair (term_Const (TC_tag tc))
          (encode_infer_ts ts))))`,
  CHEAT_TAC);;

(* [local] *)
let encode_unify_lemma = prove
 (`!s t1 t2 s' t1' t2'.
   (s = (encode_infer_t o_f s')) /\
   (((t1 = encode_infer_t t1') /\ (t2 = encode_infer_t t2')) \/
    (?c. (t1 = term_Const c) /\ (t2 = term_Const c) /\ (t1' = t2'))
      \/
    (?c ts1 ts2.
      (t1 = term_Pair (term_Const c) (encode_infer_ts ts1)) /\
      (t2 = term_Pair (term_Const c) (encode_infer_ts ts2)) /\
      (t1' = Infer_Tapp ts1 ARB) /\
      (t2' = Infer_Tapp ts2 ARB)) \/
    (?ts1 ts2.
       (t1 = encode_infer_ts ts1) /\
       (t2 = encode_infer_ts ts2) /\
       (t1' = Infer_Tapp ts1 ARB) /\
       (t2' = Infer_Tapp ts2 ARB))) /\
   t_wfs s' ==>
   (
    unify s t1 t2 =
    OPTION_MAP ((o_f) encode_infer_t) (t_unify s' t1' t2'))`,
  CHEAT_TAC);;

(* [local] *)
let encode_unify = prove
 (`!s t1 t2 s' t1' t2'.
   (s = encode_infer_t o_f s') /\
   (t1 = encode_infer_t t1') /\ (t2 = encode_infer_t t2') /\
   t_wfs s' ==>
   (
    unify s t1 t2 =
    OPTION_MAP ((o_f) encode_infer_t) (t_unify s' t1' t2'))`,
  (MESON_TAC[encode_unify_lemma]));;

(* [local] *)
let wfs_unify = prove
 (`!s t1 t2 s'. wfs s /\ (unify s t1 t2 = SOME s') ==> wfs s'`,
  CHEAT_TAC);;

(* [local] *)
let ts_unify_thm = prove
 (`!s l1 l2.
     t_wfs s ==>
     (ts_unify s l1 l2 =
      OPTION_MAP
      ((o_f) decode_infer_t)
      (unify (encode_infer_t o_f s) (encode_infer_ts l1)
        (encode_infer_ts l2)))`,
  CHEAT_TAC);;

let t_unify_eqn = prove
 (`(!t1 t2 s.
    t_wfs s ==>
    (t_unify s t1 t2 =
     (match (t_walk s t1,t_walk s t2) with
        (Infer_Tuvar v1,Infer_Tuvar v2) ->
          SOME (if v1 = v2 then s else s |+ (v1,Infer_Tuvar v2)) |
            (Infer_Tuvar v1,t2) -> t_ext_s_check s v1 t2 |
            (t1,Infer_Tuvar v2) -> t_ext_s_check s v2 t1 | (Infer_Tapp
            ts1 tc1,Infer_Tapp ts2 tc2) ->
          (if tc1 = tc2 then
            ts_unify s ts1 ts2 else
            NONE) | (Infer_Tvar_db n1,Infer_Tvar_db n2) ->
          (if n1 = n2 then
            SOME s else
            NONE) | _10 -> NONE)))`,
  CHEAT_TAC);;

let t_unify_ind = prove
 (`!P0 P1.
      (!s t1 t2.
         (!ts1 ts2 tc2.
            t_walk s t1 = Infer_Tapp ts1 tc2 /\
            t_walk s t2 = Infer_Tapp ts2 tc2 ==>
            P1 s ts1 ts2) ==>
         P0 s t1 t2) /\
      (!s ts1 ts2.
         (!t1 ts1' t2 ts2' s'.
            (ts1 = CONS t1 ts1' /\ ts2 = CONS t2 ts2') /\
            t_unify s t1 t2 = SOME s' ==>
            P1 s' ts1' ts2') /\
         (!t1 ts1' t2 ts2'.
            ts1 = CONS t1 ts1' /\ ts2 = CONS t2 ts2' ==> P0 s t1 t2)
              ==>
         P1 s ts1 ts2) ==>
      (!s t1 t2. t_wfs s ==> P0 s t1 t2) /\
      (!s ts1 ts2. t_wfs s ==> P1 s ts1 ts2)`,
  CHEAT_TAC);;

let apply_subst_t_def = new_definition
  `apply_subst_t s t = decode_infer_t (subst_APPLY (encode_infer_t
  o_f s) (encode_infer_t t))`;;

let apply_subst_t_eqn = prove
 (`(!s n.
    apply_subst_t s (Infer_Tuvar n) =
     (match FLOOKUP s n with NONE -> Infer_Tuvar n | SOME t -> t)) /\
   (!s ts tc.
    apply_subst_t s (Infer_Tapp ts tc) =
      Infer_Tapp (MAP (apply_subst_t s) ts) tc) /\
   (!s n.
    apply_subst_t s (Infer_Tvar_db n) =
      Infer_Tvar_db n)`,
  CHEAT_TAC);;

let t_walkstar_def = new_definition
  `t_walkstar s t =
     decode_infer_t (walkstar (encode_infer_t o_f s)
       (encode_infer_t t))`;;

let t_walkstar_cwalkstar = prove
 (`t_walkstar s t = cwalkstar (fm2sp s) t`,
  CHEAT_TAC);;

(* [local] *)
let ts_walkstar_thm = prove
 (`!l s.
   t_wfs s ==>
   (decode_infer_ts (walkstar (encode_infer_t o_f s) (encode_infer_ts
     l)) =
    MAP (t_walkstar s) l)`,
  CHEAT_TAC);;

let t_walkstar_eqn = prove
 (`!s. t_wfs s ==>
    (!t.
      t_walkstar s t =
      (match t_walk s t with Infer_Tuvar v -> Infer_Tuvar v |
        Infer_Tapp ts tctor -> Infer_Tapp (MAP (t_walkstar s) ts)
        tctor | Infer_Tvar_db n -> Infer_Tvar_db n))`,
  CHEAT_TAC);;

let t_walkstar_ind = prove
 (`!s. t_wfs s ==>
       (!P.
         (!t.
            (!ts tt a. (t_walk s t = Infer_Tapp ts tt) /\ MEM a ts
              ==> P a) ==>
            P t) ==>
         (!t. P t))`,
  CHEAT_TAC);;

let t_collapse_def = new_definition
  `t_collapse s =
     decode_infer_t o_f collapse (encode_infer_t o_f s)`;;

let t_collapse_eqn = prove
 (`!s. t_collapse s = FUN_FMAP (\v. t_walkstar s (Infer_Tuvar v))
  (FDOM s)`,
  CHEAT_TAC);;

let t_unify_unifier = prove
 (`t_wfs s /\ (t_unify s t1 t2 = SOME sx) ==> t_wfs sx /\ s SUBMAP sx
  /\ (t_walkstar sx t1 = t_walkstar sx t2)`,
  CHEAT_TAC);;

(* [local] *)
let t_unify_strongind' = prove
 (`!P0 P1.
     (!s t1 t2.
        t_wfs s /\
        (!ts1 ts2 tc2.
           t_walk s t1 = Infer_Tapp ts1 tc2 /\
           t_walk s t2 = Infer_Tapp ts2 tc2 ==>
           P1 s ts1 ts2) ==>
        P0 s t1 t2) /\
     (!s ts1 ts2.
        t_wfs s /\
        (!t1 ts1' t2 ts2' s'.
           (ts1 = CONS t1 ts1' /\ ts2 = CONS t2 ts2') /\
           t_unify s t1 t2 = SOME s' ==>
           P1 s' ts1' ts2') /\
        (!t1 ts1' t2 ts2'.
           ts1 = CONS t1 ts1' /\ ts2 = CONS t2 ts2' ==> P0 s t1 t2)
             ==>
        P1 s ts1 ts2) ==>
     (!s t1 t2. t_wfs s ==> (t_wfs s ==> P0 s t1 t2)) /\
     (!s ts1 ts2. t_wfs s ==> (t_wfs s ==> P1 s ts1 ts2))`,
  (REPEAT GEN_TAC THEN
   DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "H0") (LABEL_TAC "H1")) THEN
   MATCH_MP_TAC t_unify_ind THEN CONJ_TAC THEN REPEAT GEN_TAC THEN
   DISCH_THEN(LABEL_TAC "ih") THEN DISCH_TAC THENL
    [USE_THEN "H0" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
     REPEAT STRIP_TAC THEN
     USE_THEN "ih" (MATCH_MP_TAC o REWRITE_RULE[IMP_IMP] o SPEC_ALL)
       THEN
     ASM_MESON_TAC[];
     USE_THEN "H1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC
       THEN
     REPEAT STRIP_TAC THENL
      [USE_THEN "ih" (MATCH_MP_TAC o CONJUNCT1 o
        REWRITE_RULE[IMP_IMP; FORALL_AND_THM;
                                         TAUT `a ==> b /\ c <=> (a
                                           ==> b) /\ (a ==> c)`]);
       USE_THEN "ih" (MATCH_MP_TAC o CONJUNCT2 o
         REWRITE_RULE[IMP_IMP; FORALL_AND_THM;
                                         TAUT `a ==> b /\ c <=> (a
                                           ==> b) /\ (a ==> c)`])]
                                           THEN
     ASM_MESON_TAC[t_unify_unifier]]));;

(* HOL4 unifyScript.sml:2778-2779: a theorem that HOL4 states as the
   value of an ML expression: t_unify_strongind *)

(* [local] *)
let encode_walkstar = prove
 (`!s t.
   t_wfs s ==>
   walkstar (encode_infer_t o_f s) (encode_infer_t t) =
   encode_infer_t (t_walkstar s t)`,
  CHEAT_TAC);;

let t_walkstar_FEMPTY = prove
 (`!t. (t_walkstar FEMPTY t = t)`,
  CHEAT_TAC);;

let t_wfs_SUBMAP = prove
 (`!s1 s2. t_wfs s2 /\ s1 SUBMAP s2 ==> t_wfs s1`,
  CHEAT_TAC);;

let t_walkstar_SUBMAP = prove
 (`!s1 s2 t. s1 SUBMAP s2 /\ t_wfs s2 ==> (t_walkstar s2 t =
  t_walkstar s2 (t_walkstar s1 t))`,
  CHEAT_TAC);;

let t_vR_def = new_definition
  `t_vR s = vR (encode_infer_t o_f s)`;;

let t_vR_eqn = prove
 (`!s x y. t_vR s y x = (match FLOOKUP s x with SOME t -> y IN t_vars
  t | _11 -> F)`,
  CHEAT_TAC);;

let t_wfs_eqn = prove
 (`!s. t_wfs s = WF (t_vR s)`,
  (REWRITE_TAC[t_wfs_def; wfs_def; t_vR_def]));;

let t_rangevars_def = new_definition
  `t_rangevars s = rangevars (encode_infer_t o_f s)`;;

let t_rangevars_eqn = prove
 (`!s. t_rangevars s = UNIONS (IMAGE t_vars (FRANGE s))`,
  CHEAT_TAC);;

let t_vars_eqn = prove
 (`(!x. t_vars (Infer_Tvar_db x) = {}) /\
   (!ts tc. t_vars (Infer_Tapp ts tc) = UNIONS (set_of_list (MAP
     t_vars ts))) /\
   (!u. t_vars (Infer_Tuvar u) = {u})`,
  CHEAT_TAC);;

let t_vwalk_to_var = prove
 (`t_wfs s ==> (!v u. (t_vwalk s v = Infer_Tuvar u) ==> ~(u IN FDOM
  s))`,
  CHEAT_TAC);;

let t_walkstar_vars_notin = prove
 (`!s. t_wfs s ==>
    (!t x. x IN t_vars (t_walkstar s t) ==> ~(x IN FDOM s))`,
  CHEAT_TAC);;

let t_walkstar_vars_in = prove
 (`!s. t_wfs s ==> (!t. t_vars (t_walkstar s t) SUBSET t_vars t UNION
  UNIONS (FRANGE (t_vars o_f s)))`,
  CHEAT_TAC);;

let t_walkstar_idempotent = prove
 (`!s. t_wfs s ==> (!t. t_walkstar s (t_walkstar s t) = t_walkstar s
  t)`,
  CHEAT_TAC);;

(* ---------- Lemmas about unification that don't need to go into the encoding ----------*)

let t_unify_apply = prove
 (`!s1 s2 t1 t2.
    t_wfs s1 /\
    (t_unify s1 t1 t2 = SOME s2) ==>
    (t_walkstar s2 t1 = t_walkstar s2 t2)`,
  (MESON_TAC[t_unify_unifier]));;

let t_unify_apply2 = prove
 (`!s1 s2 t1' t2' t1 t2.
    t_wfs s1 /\
    (t_unify s1 t1' t2' = SOME s2) /\
    (t_walkstar s1 t1 = t_walkstar s1 t2) ==>
    (t_walkstar s2 t1 = t_walkstar s2 t2)`,
  (REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `t_wfs (s2:(num,infer_t)fmap) /\ s1 SUBMAP s2`
     STRIP_ASSUME_TAC THENL
    [ASM_MESON_TAC[t_unify_unifier]; ALL_TAC] THEN
   MP_TAC(SPECL [`s1:(num,infer_t)fmap`; `s2:(num,infer_t)fmap`]
     t_walkstar_SUBMAP) THEN
   ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> ONCE_REWRITE_TAC[th])
     THEN
   ASM_REWRITE_TAC[]));;

let t_unify_wfs = prove
 (`!s1 t1 t2 s2.
    t_wfs s1 /\
    (t_unify s1 t1 t2 = SOME s2) ==>
    t_wfs s2`,
  (MESON_TAC[t_unify_unifier]));;

let finite_t_rangevars = prove
 (`!t. FINITE (t_rangevars t)`,
  CHEAT_TAC);;

let t_walkstar_eqn1 = prove
 (`!s idx ts tc.
    t_wfs s ==>
    (t_walkstar s (Infer_Tvar_db idx) = Infer_Tvar_db idx) /\
    (t_walkstar s (Infer_Tapp ts tc) = Infer_Tapp (MAP (t_walkstar
      s) ts) tc)`,
  CHEAT_TAC);;

let oc_tvar_db = prove
 (`!s uv tvs. t_wfs s ==> ~(t_oc s (Infer_Tvar_db tvs) uv)`,
  CHEAT_TAC);;

let oc_unit = prove
 (`!s uv tc. t_wfs s ==> ~(t_oc s (Infer_Tapp [] tc) uv)`,
  CHEAT_TAC);;

let no_vars_lem = prove
 (`!e l f.
    MEM e l /\ set_of_list (MAP f l) = {{}} ==>
    (f e = {})`,
  CHEAT_TAC);;

let no_vars_extend_subst_vwalk = prove
 (`!s. t_wfs s ==>
     (!n s'.
           t_wfs (s |++ s') /\
           DISJOINT (FDOM s) (FDOM (FEMPTY |++ s')) /\
           (!n'. ~(t_vwalk s n = Infer_Tuvar n')) ==>
           t_vwalk (s |++ s') n = t_vwalk s n)`,
  CHEAT_TAC);;

let no_vars_extend_subst = prove
 (`!s. t_wfs s ==>
    (!t s'.
           t_wfs (s |++ s') /\
           DISJOINT (FDOM s) (FDOM (FEMPTY |++ s')) /\
           (t_vars (t_walkstar s t) = {}) ==>
           t_walkstar (s |++ s') t = t_walkstar s t)`,
  CHEAT_TAC);;

(*Theorems about unification for completeness proof*)

let t_walk_vwalk_id = prove
 (`t_wfs s ==>
    (!n. t_walk s (t_vwalk s n) = t_vwalk s n)`,
  CHEAT_TAC);;

let t_walk_walk_id = prove
 (`t_wfs s ==>
    t_walk s (t_walk s h) = t_walk s h`,
  CHEAT_TAC);;

let eqs_t_unify = prove
 (`t_wfs s /\ t_wfs s2 /\
    t_walkstar s2 (t_walkstar s t1) = t_walkstar s2 (t_walkstar s t2)
      ==>
    (?sx. t_unify s t1 t2 = SOME sx)`,
  CHEAT_TAC);;

(* HOL4 unifyScript.sml:3129-3132: ML code, not ported *)

let t_unify_mgu = prove
 (`!s t1 t2 sx s2.
    t_wfs s /\ (t_unify s t1 t2 = SOME sx) /\ t_wfs s2 /\
    (t_walkstar s2 (t_walkstar s t1)) = t_walkstar s2 (t_walkstar s
      t2) ==>
    (!t. t_walkstar s2 (t_walkstar sx t) = t_walkstar s2
      (t_walkstar s t))`,
  CHEAT_TAC);;

let t_walkstar_tuvar_props = prove
 (`t_wfs s ==>
    (~(uv IN FDOM s) <=> t_walkstar s (Infer_Tuvar uv) =
      Infer_Tuvar uv)`,
  CHEAT_TAC);;

(*t_compat theorems*)
let t_compat_def = new_definition
  `t_compat s s' <=>
   t_wfs s /\ t_wfs s' /\
   (!t. t_walkstar s' (t_walkstar s t) = t_walkstar s' t)`;;

let t_compat_refl = prove
 (`t_wfs s ==> t_compat s s`,
  (REWRITE_TAC[t_compat_def] THEN MESON_TAC[t_walkstar_SUBMAP;
    SUBMAP_REFL]));;

let t_compat_trans = prove
 (`t_compat a b /\ t_compat b c ==> t_compat a c`,
  (REWRITE_TAC[t_compat_def] THEN MESON_TAC[]));;

let SUBMAP_t_compat = prove
 (`t_wfs s' /\ s SUBMAP s' ==> t_compat s s'`,
  (REWRITE_TAC[t_compat_def] THEN MESON_TAC[t_wfs_SUBMAP;
    t_walkstar_SUBMAP]));;

(*t_compat is preserved under certain types of unification
  Proof basically from HOL*)
let t_compat_eqs_t_unify = prove
 (`!s t1 t2 sx.
      t_compat s sx /\ (t_walkstar sx t1 = t_walkstar sx t2) ==>
      (?si. (t_unify s t1 t2 = SOME si) /\ t_compat si sx)`,
  CHEAT_TAC);;
