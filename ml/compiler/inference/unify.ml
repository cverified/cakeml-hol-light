(* ======================================================== *)
(*  unify: ported from HOL4's
    compiler/inference/unifyScript.sml
    A definition theory, with 65 definitions, 2 datatypes and 224
    theorems.  Needed by 8 files of the port.  *)
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
(* HOL4 ancestors outside the port: unifProps transfer cps *)

hol4_overload "++" "OPTION_CHOICE";;

(* HOL4 unifyScript.sml:20-21: ML code, not ported *)

let i_o_f = cake_theorem "I_o_f[local,simp]"
  (fun () ->
    `!m. I o_f' m = m`)
  CHEAT_TAC;;

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

let encode_infer_t_11 = cake_theorem "encode_infer_t_11[simp]"
  (fun () ->
    `(!it1 it2. encode_infer_t it1 = encode_infer_t it2 <=> it1 = it2)
  /\
     (!its1 its2. encode_infer_ts its1 = encode_infer_ts its2 <=>
       its1 = its2)`)
  CHEAT_TAC;;

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

let decode_left_inverse = cake_theorem "decode_left_inverse[simp]"
  (fun () ->
    `(!t. decode_infer_t (encode_infer_t t) = t) /\
     (!ts. decode_infer_ts (encode_infer_ts ts) = ts)`)
  CHEAT_TAC;;

let decode_left_inverse_I = cake_theorem "decode_left_inverse_I[simp]"
  (fun () ->
    `decode_infer_t o encode_infer_t = I`)
  CHEAT_TAC;;

let encode_eq_var = cake_theorem "encode_eq_var[simp]"
  (fun () ->
    `(Var n = encode_infer_t i <=> i = Infer_Tuvar n) /\
     (encode_infer_t i = Var n <=> i = Infer_Tuvar n)`)
  CHEAT_TAC;;

let decode_right_inverse = cake_theorem "decode_right_inverse[local]"
  (fun () ->
    `(!t. (?t'. t = encode_infer_t t') ==> (encode_infer_t
  (decode_infer_t t) = t)) /\
     (!ts. (?ts'. ts = encode_infer_ts ts') ==> (encode_infer_ts
       (decode_infer_ts ts) = ts))`)
  CHEAT_TAC;;

let option_CASE_MAP = cake_theorem "option_CASE_MAP"
  (fun () ->
    `option_CASE (OPTION_MAP f v) n sf =
     option_CASE v n (sf o f)`)
  CHEAT_TAC;;

let list_CASE_MAP = cake_theorem "list_CASE_MAP"
  (fun () ->
    `list_CASE (MAP f l) n cf =
     list_CASE l n (\h t. cf (f h) (MAP f t))`)
  CHEAT_TAC;;


let decode_option_CASE = cake_theorem "decode_option_CASE[local]"
  (fun () ->
    `decode_infer_t (option_CASE v n sf) =
     option_CASE v (decode_infer_t n) (decode_infer_t o sf)`)
  CHEAT_TAC;;

let decode_infer_t_CASE = cake_theorem "decode_infer_t_CASE[local]"
  (fun () ->
    `decode_infer_t (infer_t_CASE it dbf appf uvf) =
     infer_t_CASE it (decode_infer_t o dbf)
                     (\l n. decode_infer_t (appf l n))
                     (decode_infer_t o uvf)`)
  CHEAT_TAC;;

(* "Ramana Kumar unification type to CakeML type" relation *)
let RKC_def = cake_define
  `RKC rkt ct <=> encode_infer_t ct = rkt`;;

let surj_RKC = cake_theorem "surj_RKC[transfer_simp]"
  (fun () ->
    `surj RKC`)
  CHEAT_TAC;;

let substR_def = cake_define
  `substR fm sp <=> wfs fm /\ sptree_wf sp /\ fm = encode_infer_t o_f
  sp2fm sp`;;

(* HOL4 unifyScript.sml:153-157: a theorem whose statement the port
   cannot state yet *)

(* HOL4 unifyScript.sml:159-164: a theorem whose statement the port
   cannot state yet *)

let cwfs_def = cake_define
  `cwfs s <=> swfs (sptree_map encode_infer_t s) /\ sptree_wf s`;;

let sp2fm_map = cake_theorem "sp2fm_map"
  (fun () ->
    `sp2fm (sptree_map f sp) = f o_f sp2fm sp`)
  CHEAT_TAC;;

(* HOL4 unifyScript.sml:178-183: a theorem whose statement the port
   cannot state yet *)

(* HOL4 unifyScript.sml:185-191: code that the source has in a
   comment *)

(* HOL4 unifyScript.sml:193-198: a theorem whose statement the port
   cannot state yet *)

let svwalk_result_encodable = cake_theorem "svwalk_result_encodable"
  (fun () ->
    `sptree_wf fm /\ swfs (sptree_map f fm) /\ (!n. ?y. Var n = f y) ==>
     (!x. ?y. svwalk (sptree_map f fm) x = f y)`)
  CHEAT_TAC;;

let cvwalk_def = cake_define
  `cvwalk s n = decode_infer_t (svwalk (sptree_map encode_infer_t s)
  n)`;;

(* HOL4 unifyScript.sml:217-226: a theorem whose statement the port
   cannot state yet *)

let term_CASE_encode = cake_theorem "term_CASE_encode"
  (fun () ->
    `term_CASE (encode_infer_t v) vf pf cf =
     infer_t_CASE v
                  (cf o DB_tag)
                  (\l n. pf (term_Const Tapp_tag)
                            (term_Pair (term_Const (TC_tag n))
                              (encode_infer_ts l)))
                  vf`)
  CHEAT_TAC;;

(* HOL4 unifyScript.sml:239-247: a theorem that HOL4 states as the
   value of an ML expression *)

let cwalk_def = cake_define
  `cwalk s it = decode_infer_t (swalk (sptree_map encode_infer_t s)
  (encode_infer_t it))`;;

let swalk_result_encodable = cake_theorem "swalk_result_encodable"
  (fun () ->
    `!s it. cwfs s ==>
            (?it'. swalk (sptree_map encode_infer_t s)
              (encode_infer_t it) =
                  encode_infer_t it')`)
  CHEAT_TAC;;

let swalk_elim = cake_theorem "swalk_elim"
  (fun () ->
    `cwfs s ==>
     swalk (sptree_map encode_infer_t s) (encode_infer_t it) =
     encode_infer_t (cwalk s it)`)
  CHEAT_TAC;;

(* HOL4 unifyScript.sml:276-284: a theorem whose statement the port
   cannot state yet *)

(* HOL4 unifyScript.sml:286-287: the ML values that the definitions
   below antiquote *)
(* HOL4 unifyScript.sml:288-293: a theorem that HOL4 states as the
   value of an ML expression *)

let coc_def = cake_define
  `coc s it n = soc (sptree_map encode_infer_t s) (encode_infer_t it)
  n`;;

let soc_encode_ts = cake_theorem "soc_encode_ts"
  (fun () ->
    `cwfs s ==>
     (soc (sptree_map encode_infer_t s) (encode_infer_ts its) n <=>
        EXISTS (\i. soc (sptree_map encode_infer_t s)
          (encode_infer_t i) n) its)`)
  CHEAT_TAC;;

(* HOL4 unifyScript.sml:309-313: a theorem whose statement the port
   cannot state yet *)

(* HOL4 unifyScript.sml:315-321: a theorem that HOL4 states as the
   value of an ML expression *)

let t_vars_def = cake_define
  `t_vars t = vars (encode_infer_t t)`;;

let cunify_def = cake_define
  `cunify s t1 t2 = OPTION_MAP (sptree_map decode_infer_t)
                              (sunify (sptree_map encode_infer_t s)
                                (encode_infer_t t1)
                              (encode_infer_t t2))`;;


let fm2sp_delete = cake_theorem "fm2sp_delete"
  (fun () ->
    `fm2sp (fm \\ k) = sptree_delete k (fm2sp fm)`)
  CHEAT_TAC;;

let domain_fm2sp = cake_theorem "domain_fm2sp"
  (fun () ->
    `!fm. domain (fm2sp fm) = FDOM fm`)
  CHEAT_TAC;;

let swalk_encode_infer_ts_EQ_VAR =
  cake_theorem "swalk_encode_infer_ts_EQ_VAR"
  (fun () ->
    `swfs s /\ sptree_wf s ==> ~(swalk s (encode_infer_ts ts) = Var v)`)
  CHEAT_TAC;;

let encode_t_vs_ts = cake_theorem "encode_t_vs_ts"
  (fun () ->
    `~(
       encode_infer_t x = encode_infer_ts l)`)
  CHEAT_TAC;;

let swalk_encode_infer_ts = cake_theorem "swalk_encode_infer_ts"
  (fun () ->
    `sptree_wf s ==> swalk s (encode_infer_ts ts) = encode_infer_ts ts`)
  CHEAT_TAC;;

let sunify_wf = cake_theorem "sunify_wf"
  (fun () ->
    `!s t1 t2 s'. swfs s /\ sptree_wf s /\ sunify s t1 t2 = SOME s'
  ==> sptree_wf s'`)
  CHEAT_TAC;;

let sunify_constconst = cake_theorem "sunify_constconst"
  (fun () ->
    `sptree_wf s /\ swfs s ==>
     sunify s (term_Const c1) (term_Const c2) = (if c1 = c2 then
       SOME s else NONE)`)
  CHEAT_TAC;;

let sunify_pairconstconst = cake_theorem "sunify_pairconstconst"
  (fun () ->
    `sptree_wf s /\ swfs s ==>
     sunify s (term_Pair (term_Const c1) t1) (term_Pair (term_Const
       c2) t2) =
     (if c1 = c2 then sunify s t1 t2 else NONE)`)
  CHEAT_TAC;;

let sunify_result_encodable = cake_theorem "sunify_result_encodable"
  (fun () ->
    `!st1t2 s pt1 pt2 s'.
       st1t2 = (s,pt1,pt2) /\ swfs (sptree_map encode_infer_t s) /\
         sptree_wf s /\
       ((?t1 t2. pt1 = encode_infer_t t1 /\ pt2 = encode_infer_t
         t2) \/
        (?ts1 ts2. pt1 = encode_infer_ts ts1 /\ pt2 =
          encode_infer_ts ts2)) /\
       sunify (sptree_map encode_infer_t s) pt1 pt2 = SOME s' ==>
       (?m. s' = sptree_map encode_infer_t m)`)
  CHEAT_TAC;;

let map_decode_encode = cake_theorem "map_decode_encode"
  (fun () ->
    `cwfs s ==> sptree_map decode_infer_t (sptree_map encode_infer_t
  s) = s`)
  CHEAT_TAC;;

let sunify_t_elim = cake_theorem "sunify_t_elim"
  (fun () ->
    `cwfs s ==>
     sunify (sptree_map encode_infer_t s) (encode_infer_t t1)
       (encode_infer_t t2) =
     OPTION_MAP (sptree_map encode_infer_t) (cunify s t1 t2)`)
  CHEAT_TAC;;

let option_map_itcase = cake_theorem "option_map_itcase"
  (fun () ->
    `OPTION_MAP f (infer_t_CASE arg x y z) =
     infer_t_CASE arg (OPTION_MAP f o x) (\l n. OPTION_MAP f (y l
       n))
                  (OPTION_MAP f o z)`)
  CHEAT_TAC;;

let option_map_COND = cake_theorem "option_map_COND"
  (fun () ->
    `OPTION_MAP f (COND g t e) = COND g (OPTION_MAP f t) (OPTION_MAP f
  e)`)
  CHEAT_TAC;;

let sptree_map_COND = cake_theorem "sptree_map_COND"
  (fun () ->
    `sptree_map f (COND g t e) = COND g (sptree_map f t) (sptree_map f
  e)`)
  CHEAT_TAC;;

let SOME_COND = cake_theorem "SOME_COND"
  (fun () ->
    `SOME (COND g t e) = COND g (SOME t) (SOME e)`)
  CHEAT_TAC;;

let OPTION_MAP_BIND = cake_theorem "OPTION_MAP_BIND"
  (fun () ->
    `OPTION_MAP f (OPTION_BIND m mf) =
     OPTION_BIND m (OPTION_MAP f o mf)`)
  CHEAT_TAC;;

let OPTION_BIND_MAP = cake_theorem "OPTION_BIND_MAP"
  (fun () ->
    `OPTION_BIND (OPTION_MAP f m) mf =
     OPTION_BIND m (mf o f)`)
  CHEAT_TAC;;

let cunifyl_def = cake_define
  `cunifyl s ts1 ts2 =
   OPTION_MAP (sptree_map decode_infer_t)
              (sunify (sptree_map encode_infer_t s)
                      (encode_infer_ts ts1)
                      (encode_infer_ts ts2))`;;

let sunify_preserves_swfs = cake_theorem "sunify_preserves_swfs"
  (fun () ->
    `swfs s /\ sunify s t1 t2 = SOME s' ==> swfs s'`)
  CHEAT_TAC;;

(* HOL4 unifyScript.sml:543-567: a theorem whose statement the port
   cannot state yet *)

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

(* HOL4 unifyScript.sml:579: a theorem that HOL4 states as the value
   of an ML expression *)

(* HOL4 unifyScript.sml:581-592: a theorem that HOL4 states as the
   value of an ML expression *)

(* HOL4 unifyScript.sml:594-601: a theorem that HOL4 states as the
   value of an ML expression *)
(* HOL4 unifyScript.sml:602-609: a theorem that HOL4 states as the
   value of an ML expression *)
(* HOL4 unifyScript.sml:610-617: a theorem that HOL4 states as the
   value of an ML expression *)

(* HOL4 unifyScript.sml:619-630: a theorem that HOL4 states as the
   value of an ML expression *)

let cunify_preserves_cwfs = cake_theorem "cunify_preserves_cwfs"
  (fun () ->
    `cwfs s0 /\ cunify s0 t1 t2 = SOME s ==> cwfs s`)
  CHEAT_TAC;;

let cunifyl_thm = cake_theorem "cunifyl_thm"
  (fun () ->
    `cwfs s ==>
     cunifyl s ts1 ts2 =
     (match (ts1,ts2) with
       ([],[]) -> SOME s | (t1 :: ts1,t2 :: ts2) -> OPTION_BIND
         (cunify s t1 t2) (\s'. cunifyl s' ts1 ts2) | _3 -> NONE)`)
  CHEAT_TAC;;

let cwalkstar_def = cake_define
  `cwalkstar s it =
   decode_infer_t (walkstar (encode_infer_t o_f sp2fm s)
     (encode_infer_t it))`;;

(* HOL4 unifyScript.sml:660-664: a theorem that HOL4 states as the
   value of an ML expression *)
(* HOL4 unifyScript.sml:665-668: a theorem that HOL4 states as the
   value of an ML expression *)

let cvwalk_rwt = cake_theorem "cvwalk_rwt"
  (fun () ->
    `sptree_wf s ==> wfs (encode_infer_t o_f sp2fm s) ==>
     vwalk (encode_infer_t o_f sp2fm s) v =
     encode_infer_t (cvwalk s v)`)
  CHEAT_TAC;;

let decode_infer_ts_walkstar = cake_theorem "decode_infer_ts_walkstar"
  (fun () ->
    `wfs (encode_infer_t o_f sp2fm s) ==>
     decode_infer_ts (walkstar (encode_infer_t o_f sp2fm s)
       (encode_infer_ts l)) =
     MAP (cwalkstar s) l`)
  CHEAT_TAC;;

(* HOL4 unifyScript.sml:692-704: a theorem that HOL4 states as the
   value of an ML expression *)

(* HOL4 unifyScript.sml:706-709: a theorem that HOL4 states as the
   value of an ML expression *)
(* HOL4 unifyScript.sml:710-713: a theorem that HOL4 states as the
   value of an ML expression *)
let infer_t_CASE_RAND = cake_theorem "infer_t_CASE_RAND"
  (fun () ->
    `f (infer_t_CASE it tvf taf tuf) =
     infer_t_CASE it (f o tvf) (\l n. f (taf l n)) (f o tuf)`)
  CHEAT_TAC;;

let cunify_unifier = cake_theorem "cunify_unifier"
  (fun () ->
    `cwfs s /\ cunify s t1 t2 = SOME sx ==>
     cwfs sx /\ subspt s sx /\ cwalkstar sx t1 = cwalkstar sx t2`)
  CHEAT_TAC;;

(* HOL4 unifyScript.sml:750-760: ML code, not ported *)

(* HOL4 unifyScript.sml:762: the ML values that the definitions below
   antiquote *)

cake_declare "cvwalk_code" `:infer_t spt -> num -> num + infer_t`;;

(* PENDING: tcallify_th makes it with ML code *)
(* HOL4 unifyScript.sml:764-766: the definition *)

let sum_CASE_infer_CASE = cake_theorem "sum_CASE_infer_CASE"
  (fun () ->
    `sum_CASE (infer_t_CASE i vf af uf) lf rf =
     infer_t_CASE i (\v. sum_CASE (vf v) lf rf)
                (\l n. sum_CASE (af l n) lf rf)
                (\u. sum_CASE (uf u) lf rf)`)
  CHEAT_TAC;;

let cvwalk_preserves_precond = cake_theorem "cvwalk_preserves_precond"
  (fun () ->
    `!x y.
     (\n. cwfs s) x /\ cvwalk_code s x = INL y ==> (\n. cwfs s) y`)
  CHEAT_TAC;;

let cvwalkR_def = cake_define
  `cvwalkR sigma = (\v v0. vR (encode_infer_t o_f sp2fm sigma) v v0)`;;

let cvwalk_ensures_decrease = cake_theorem "cvwalk_ensures_decrease"
  (fun () ->
    `!x y. (\n. cwfs s) x /\ cvwalk_code s x = INL y ==> cvwalkR s y x`)
  CHEAT_TAC;;

let WF_cvwalkR = cake_theorem "WF_cvwalkR"
  (fun () ->
    `!x. (\n. cwfs s) x ==> WF (cvwalkR s)`)
  CHEAT_TAC;;

let cvwalk_tcallish = cake_theorem "cvwalk_tcallish"
  (fun () ->
    `!x. (\n. cwfs s) x ==>
         cvwalk s x = TAILCALL (cvwalk_code s) (cvwalk s) x`)
  CHEAT_TAC;;

let cvwalk_cleaned = cake_theorem "cvwalk_cleaned"
  (fun () ->
    `!x. (\n. cwfs s) x ==> cvwalk s x = TAILREC (cvwalk_code s) x`)
  CHEAT_TAC;;

let tcvwalk_def = cake_define
  `tcvwalk s n = TAILREC (cvwalk_code s) n`;;

let cvwalk_eta = cake_theorem "cvwalk_eta[local]"
  (fun () ->
    `(\n. cvwalk_code s n) = cvwalk_code s`)
  CHEAT_TAC;;

(* HOL4 unifyScript.sml:833-837: a theorem that HOL4 states as the
   value of an ML expression *)

(* HOL4 unifyScript.sml:839-840: a theorem that HOL4 states as the
   value of an ML expression *)

let tcwalk_def = cake_define
  `tcwalk s it = (match it with
                   Infer_Tvar_db c -> Infer_Tvar_db c | Infer_Tapp
                     l n -> Infer_Tapp l n | Infer_Tuvar v -> tcvwalk
                     s v)`;;

let tcwalk_correct = cake_theorem "tcwalk_correct"
  (fun () ->
    `!s it. cwfs s ==> cwalk s it = tcwalk s it`)
  CHEAT_TAC;;

let cocl_def = cake_define_list
  [`cocl s [] n <=> F`;
   `cocl s (i :: is) n <=> coc s i n \/ cocl s is n`];;

let cocl_EXISTS = cake_theorem "cocl_EXISTS"
  (fun () ->
    `cocl s its n <=> EXISTS (\i. coc s i n) its`)
  CHEAT_TAC;;

(* HOL4 unifyScript.sml:866: a theorem that HOL4 states as the value
   of an ML expression *)

let kcoc_def = cake_define
  `kcoc s it n k = cwc (coc s it n) k`;;

let kcocl_def = cake_define
  `kcocl s its n k = cwc (cocl s its n) k`;;

let contify_infer_case = cake_theorem "contify_infer_case"
  (fun () ->
    `contify k (infer_t_CASE it cf af uf) =
     contify (\it. match it with Infer_Tvar_db c -> contify k (cf
       c) | Infer_Tapp l n -> contify k (af l n) | Infer_Tuvar v ->
       contify k (uf v))
             it`)
  CHEAT_TAC;;

(* HOL4 unifyScript.sml:886-893: a theorem that HOL4 states as the
   value of an ML expression *)

let cwc_OR = cake_theorem "cwc_OR"
  (fun () ->
    `cwc (bool (\/) b) k = (if b then k (K T) else k I)`)
  CHEAT_TAC;;

let kcocl_Ky = cake_theorem "kcocl_Ky"
  (fun () ->
    `kcocl s t n (\x. y) = y`)
  CHEAT_TAC;;

(* HOL4 unifyScript.sml:907-916: a theorem that HOL4 states as the
   value of an ML expression *)

new_type_abbrev("kcockont",`: (infer_t list) list`);;

let apply_kcockont_def = cake_define_list
  [`apply_kcockont s n [] b = b`;
   `apply_kcockont s n (ts :: rest) b =
    (if b then apply_kcockont s n rest T else kcocl s ts n
      (apply_kcockont s n rest))`];;

let apply_kcockontT = cake_theorem "apply_kcockontT[simp]"
  (fun () ->
    `apply_kcockont s n ts T = T`)
  CHEAT_TAC;;

let dfkcoc_def = cake_define
  `dfkcoc s t n k = kcoc s t n (apply_kcockont s n k)`;;

let dfkcocl_def = cake_define
  `dfkcocl s ts n k = kcocl s ts n (apply_kcockont s n k)`;;

(* HOL4 unifyScript.sml:941-942: a theorem that HOL4 states as the
   value of an ML expression *)

(* HOL4 unifyScript.sml:944-947: a theorem that HOL4 states as the
   value of an ML expression *)

(* HOL4 unifyScript.sml:949-953: a theorem that HOL4 states as the
   value of an ML expression *)

let apply_kcockont_HDNIL = cake_theorem "apply_kcockont_HDNIL"
  (fun () ->
    `apply_kcockont s n ([] :: k) = apply_kcockont s n k`)
  CHEAT_TAC;;

let dfkcocl_HDNIL = cake_theorem "dfkcocl_HDNIL"
  (fun () ->
    `dfkcocl s ts n ([] :: k) = dfkcocl s ts n k`)
  CHEAT_TAC;;

let dfkcocl_removed = cake_theorem "dfkcocl_removed"
  (fun () ->
    `dfkcocl s ts n k = apply_kcockont s n (ts :: k) F`)
  CHEAT_TAC;;

(* HOL4 unifyScript.sml:975: ML code, not ported *)
(* HOL4 unifyScript.sml:976: a theorem that HOL4 states as the value
   of an ML expression *)

(* HOL4 unifyScript.sml:978-983: a theorem that HOL4 states as the
   value of an ML expression *)

(* HOL4 unifyScript.sml:985: the overload kcocwl0, which the port
   expands *)

(* HOL4 unifyScript.sml:987-991: a theorem that HOL4 states as the
   value of an ML expression *)

let kcocwl_def = cake_define
  `kcocwl s n ts = apply_kcockont s n ts F`;;

let kcocwl0_varcheck = cake_theorem "kcocwl0_varcheck"
  (fun () ->
    `apply_kcockont s n ts b = (if b then T else kcocwl s n ts)`)
  CHEAT_TAC;;

(* HOL4 unifyScript.sml:1001-1006: a theorem that HOL4 states as the
   value of an ML expression *)

(* HOL4 unifyScript.sml:1008-1014: the ML values that the definitions
   below antiquote *)

cake_declare "kcocwl_code"
  `:infer_t spt -> num -> kcockont -> kcockont + bool`;;

(* PENDING: tcallify_th makes it with ML code *)
(* HOL4 unifyScript.sml:1016-1018: the definition *)

let kcocwl_preserves_precond = cake_theorem "kcocwl_preserves_precond"
  (fun () ->
    `!x y. (\ts. cwfs s) x /\ kcocwl_code s n x = INL y ==>
           (\ts. cwfs s) y`)
  CHEAT_TAC;;

let kcocwlR_def = cake_define
  `kcocwlR (s:infer_t spt) (n:num) =
   inv_image (mlt1 (walkstarR (sp2fm (sptree_map encode_infer_t s)))
     LEX (<))
             (\(ts:(infer_t list) list).
                ((FOLDR BAG_INSERT EMPTY_BAG) (MAP encode_infer_t
                  (FLAT ts)),LENGTH ts))`;;

let WF_kcocwlR = cake_theorem "WF_kcocwlR"
  (fun () ->
    `cwfs s ==> WF (kcocwlR s n)`)
  CHEAT_TAC;;

let FINITE_BAG_FOLDR_INSERT =
  cake_theorem "FINITE_BAG_FOLDR_INSERT[simp]"
  (fun () ->
    `FINITE_BAG (ITLIST BAG_INSERT' xs b) = FINITE_BAG b`)
  CHEAT_TAC;;

let FOLDR_BAG_INSERT_UNION = cake_theorem "FOLDR_BAG_INSERT_UNION"
  (fun () ->
    `ITLIST BAG_INSERT' xs b = (BAG_UNION) b ((FOLDR BAG_INSERT
  EMPTY_BAG) xs)`)
  CHEAT_TAC;;

let BAG_IN_BAG_OF_LIST = cake_theorem "BAG_IN_BAG_OF_LIST"
  (fun () ->
    `BAG_IN e ((FOLDR BAG_INSERT EMPTY_BAG) xs) = MEM e xs`)
  CHEAT_TAC;;

let sum_CASE_list_CASE = cake_theorem "sum_CASE_list_CASE"
  (fun () ->
    `sum_CASE (list_CASE l n cf) lf rf =
     list_CASE l (sum_CASE n lf rf) (\h t. sum_CASE (cf h t) lf
       rf)`)
  CHEAT_TAC;;

let walkstarR_trans = cake_theorem "walkstarR_trans"
  (fun () ->
    `walkstarR s t1 t2 /\ walkstarR s t2 t3 ==> walkstarR s t1 t3`)
  CHEAT_TAC;;

let subterm_def = cake_define
  `subterm = TC (\a b. (?t. b = term_Pair a t) \/ (?t. b = term_Pair
  t a))`;;

let subterm_thm = cake_theorem "subterm_thm[simp]"
  (fun () ->
    `(subterm t (term_Pair u v) <=> t = u \/ t = v \/ subterm t u \/
  subterm t v) /\
     (subterm t (Var vnm) <=> F) /\
     (subterm t (term_Const c) <=> F)`)
  CHEAT_TAC;;

let subterm_pair_count = cake_theorem "subterm_pair_count"
  (fun () ->
    `!t u. subterm t u ==> pair_count t < pair_count u`)
  CHEAT_TAC;;

let subterm_REFL = cake_theorem "subterm_REFL[simp]"
  (fun () ->
    `~subterm t t`)
  CHEAT_TAC;;

let subterm_TRANS = cake_theorem "subterm_TRANS"
  (fun () ->
    `subterm t u /\ subterm u v ==> subterm t v`)
  CHEAT_TAC;;

let subterm_walkstarR = cake_theorem "subterm_walkstarR"
  (fun () ->
    `!t u. subterm t u ==> walkstarR s t u`)
  CHEAT_TAC;;

let MEM_subterm_encode = cake_theorem "MEM_subterm_encode"
  (fun () ->
    `!i is. MEM i is ==> subterm (encode_infer_t i) (encode_infer_ts
  is)`)
  CHEAT_TAC;;

let walkstar_opth = cake_theorem "walkstar_opth"
  (fun () ->
    `cwfs s /\ tcwalk s i = Infer_Tapp is nm /\ MEM i0 is ==>
     walkstarR (sp2fm (sptree_map encode_infer_t s))
               (encode_infer_t i0)
               (encode_infer_t i)`)
  CHEAT_TAC;;

let kcocwl_ensures_decrease = cake_theorem "kcocwl_ensures_decrease"
  (fun () ->
    `!x y. (\v. cwfs s) x /\ kcocwl_code s n x = INL y ==>
           kcocwlR s n y x`)
  CHEAT_TAC;;

let kcocwl_tcallish = cake_theorem "kcocwl_tcallish"
  (fun () ->
    `!x. (\v. cwfs s) x ==>
         kcocwl s n x = TAILCALL (kcocwl_code s n) (kcocwl s n) x`)
  CHEAT_TAC;;

let kcocwl_cleaned = cake_theorem "kcocwl_cleaned"
  (fun () ->
    `!x. (\v. cwfs s) x ==> kcocwl s n x = TAILREC (kcocwl_code s n) x`)
  CHEAT_TAC;;

let tcocwl_def = cake_define
  `tcocwl s n is = TAILREC (kcocwl_code s n) is`;;

(* HOL4 unifyScript.sml:1207-1208: a theorem that HOL4 states as the
   value of an ML expression *)
let tcocwl_correct = cake_theorem "tcocwl_correct"
  (fun () ->
    `cwfs s ==> cocl s ts n = tcocwl s n [ts]`)
  CHEAT_TAC;;
(* HOL4 unifyScript.sml:1215: a theorem that HOL4 states as the value
   of an ML expression *)

(* HOL4 unifyScript.sml:1217-1222: a theorem that HOL4 states as the
   value of an ML expression *)

(* ----------------------------------------------------------------------
    tail-recursification of cwalkstar
   ---------------------------------------------------------------------- *)

let cwalkstarl_def = cake_define_list
  [`cwalkstarl s [] = []`;
   `cwalkstarl s (it :: its) = cwalkstar s it :: cwalkstarl s its`];;

let MAP_cwalkstar = cake_theorem "MAP_cwalkstar"
  (fun () ->
    `MAP (cwalkstar s) l = cwalkstarl s l`)
  CHEAT_TAC;;

let kcwalkstar_def = cake_define
  `kcwalkstar s it k = cwc (cwalkstar s it) k`;;

let kcwalkstarl_def = cake_define
  `kcwalkstarl s its k = cwc (cwalkstarl s its) k`;;

(* HOL4 unifyScript.sml:1247-1252: a theorem that HOL4 states as the
   value of an ML expression *)

(* HOL4 unifyScript.sml:1254-1263: a theorem that HOL4 states as the
   value of an ML expression *)

(* HOL4 unifyScript.sml:1265-1274: a theorem that HOL4 states as the
   value of an ML expression *)

(* HOL4 unifyScript.sml:1276-1277: a theorem that HOL4 states as the
   value of an ML expression *)

let kclkont_INDUCT,kclkont_RECURSION = define_datatype
  "kclkont = DBk (num) | APPk (infer_t list) (num) | UVk (num) | \
   CONSk (infer_t list) (num)";;

let apply_kclkont_def = cake_define_list
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

(* HOL4 unifyScript.sml:1298-1299: a theorem that HOL4 states as the
   value of an ML expression *)

(* HOL4 unifyScript.sml:1301-1306: a theorem that HOL4 states as the
   value of an ML expression *)

(* HOL4 unifyScript.sml:1308-1313: a theorem that HOL4 states as the
   value of an ML expression *)

let kcwalkstarwl_def = cake_define_list
  [`kcwalkstarwl s T t k = apply_kclkont s k t`;
   `kcwalkstarwl s F t k = dfkcwalkstarl s t k`];;

(* HOL4 unifyScript.sml:1320-1324: a theorem that HOL4 states as the
   value of an ML expression *)

(* HOL4 unifyScript.sml:1326: a theorem that HOL4 states as the value
   of an ML expression *)
let apply_kclkont_ID = cake_theorem "apply_kclkont_ID[simp]"
  (fun () ->
    `apply_kclkont s [] = I`)
  CHEAT_TAC;;

let cwalkstar_to_dfkcwalkstarl =
  cake_theorem "cwalkstar_to_dfkcwalkstarl"
  (fun () ->
    `cwalkstar s t = HD (dfkcwalkstarl s [t] [])`)
  CHEAT_TAC;;

(* kcwalkstarwl_thm is the target for tailcallification *)

let star_kwork_def = cake_define
  `star_kwork x1 =
      match x1 with
        [] -> EMPTY_BAG
      | (CONSk its n :: ks) -> (BAG_UNION) ((FOLDR BAG_INSERT
        EMPTY_BAG) its) (star_kwork ks)
      | (_4 :: ks) -> star_kwork ks`;;

let star_workbag_def = cake_define
  `star_workbag v its k =
   (if v then star_kwork k else (BAG_UNION) ((FOLDR BAG_INSERT
     EMPTY_BAG) its) (star_kwork k))`;;

let FINITE_star_kwork = cake_theorem "FINITE_star_kwork[simp]"
  (fun () ->
    `FINITE_BAG (star_kwork ks)`)
  CHEAT_TAC;;

let FINITE_star_workbag = cake_theorem "FINITE_star_workbag[simp]"
  (fun () ->
    `FINITE_BAG (star_workbag v its k)`)
  CHEAT_TAC;;

let isCONSk_def = cake_define
  `isCONSk x1 =
      match x1 with
        CONSk _5 _6 -> T
      | _7 -> F`;;

let kcwalkstarwlR_def = cake_define
  `kcwalkstarwlR s =
   inv_image (mlt (inv_image
                    (walkstarR (encode_infer_t o_f sp2fm s))
                    encode_infer_t) LEX
              (<) LEX
              MEASURE (LENGTH o FILTER isCONSk) LEX
              MEASURE (\b. if b then 0 else 1))
             (\(v,its,k). (star_workbag v its k,LENGTH k,k,v))`;;

let WF_kcwalkstarwlR = cake_theorem "WF_kcwalkstarwlR"
  (fun () ->
    `cwfs s ==> WF (kcwalkstarwlR s)`)
  CHEAT_TAC;;

(* HOL4 unifyScript.sml:1391: the ML values that the definitions
   below antiquote *)
cake_declare "kcwalkstarwl_code"
  `:infer_t spt -> bool#infer_t list#kclkont list ->
    (bool#infer_t list#kclkont list) + infer_t list`;;

(* PENDING: tcallify_th makes it with ML code *)
(* HOL4 unifyScript.sml:1392-1394: the definition *)

let kcwalkstarwl_preserves_precond =
  cake_theorem "kcwalkstarwl_preserves_precond"
  (fun () ->
    `!x y. (\(v,t,k). cwfs s) x /\ kcwalkstarwl_code s x = INL y ==>
           (\(v,t,k). cwfs s) y`)
  CHEAT_TAC;;

let kcwalkstarwl_ensures_decrease =
  cake_theorem "kcwalkstarwl_ensures_decrease"
  (fun () ->
    `!x y. (\(v,its,k). cwfs s) x /\ kcwalkstarwl_code s x = INL y ==>
           kcwalkstarwlR s y x`)
  CHEAT_TAC;;

let sum_CASE_wstarcont_CASE = cake_theorem "sum_CASE_wstarcont_CASE"
  (fun () ->
    `sum_CASE (kclkont_CASE k dbf appf uvf consf) lf rf =
     kclkont_CASE k
                  (\n. sum_CASE (dbf n) lf rf)
                  (\its n. sum_CASE (appf its n) lf rf)
                  (\n. sum_CASE (uvf n) lf rf)
                  (\its n. sum_CASE (consf its n) lf rf)`)
  CHEAT_TAC;;

let kcwalkstarwl_tcallish = cake_theorem "kcwalkstarwl_tcallish"
  (fun () ->
    `!x. (\(v,its,k). cwfs s) x ==>
         (\(v,its,k). kcwalkstarwl s v its k) x =
         TAILCALL (kcwalkstarwl_code s) (\(v,its,k). kcwalkstarwl
           s v its k) x`)
  CHEAT_TAC;;

let kcwalkstarwl_cleaned = cake_theorem "kcwalkstarwl_cleaned"
  (fun () ->
    `!x. (\(v,its,k). cwfs s) x ==>
         (\(v,its,k). kcwalkstarwl s v its k) x = TAILREC
           (kcwalkstarwl_code s) x`)
  CHEAT_TAC;;

let tcwalkstarwl_def = cake_define
  `tcwalkstarwl s v its k = TAILREC (kcwalkstarwl_code s) (v,its,k)`;;

let tcwalkstar_p1_def = cake_define
  `tcwalkstar_p1 s its k = tcwalkstarwl s F its k`;;

let tcwalkstar_p2_def = cake_define
  `tcwalkstar_p2 s its k = tcwalkstarwl s T its k`;;

(* HOL4 unifyScript.sml:1492-1503: a theorem that HOL4 states as the
   value of an ML expression *)

(* HOL4 unifyScript.sml:1505-1506: a theorem that HOL4 states as the
   value of an ML expression *)

let tcwalkstarwl_correct = cake_theorem "tcwalkstarwl_correct"
  (fun () ->
    `cwfs s ==> cwalkstar s it = HD (tcwalkstar_p1 s [it] [])`)
  CHEAT_TAC;;


(* handle tail-recursification of unify *)

let kcunifyl_def = cake_define
  `kcunifyl s ts us k = cwc (cunifyl s ts us) k`;;

(* HOL4 unifyScript.sml:1523-1525: a theorem that HOL4 states as the
   value of an ML expression *)

(* HOL4 unifyScript.sml:1527-1541: a theorem that HOL4 states as the
   value of an ML expression *)

new_type_abbrev("kcunifkont",`: (infer_t list#infer_t list) list`);;
let apply_cunifk_def = cake_define_list
  [`apply_cunifk [] x = x`;
   `apply_cunifk ((ts,us) :: k) NONE = apply_cunifk k NONE`;
   `apply_cunifk ((ts,us) :: k) (SOME m) = kcunifyl m ts us
  (apply_cunifk k)`];;

let apply_cunif_NONE = cake_theorem "apply_cunif_NONE[simp]"
  (fun () ->
    `apply_cunifk k NONE = NONE`)
  CHEAT_TAC;;

let dfkcunifyl_def = cake_define
  `dfkcunifyl s ts us k = kcunifyl s ts us (apply_cunifk k)`;;

let abs_EQ_apply_cunifk = cake_theorem "abs_EQ_apply_cunifk"
  (fun () ->
    `(\ov. match ov with NONE -> NONE | SOME x -> dfkcunifyl x ts us k)
  =
     apply_cunifk ((ts,us) :: k)`)
  CHEAT_TAC;;

(* HOL4 unifyScript.sml:1568-1569: a theorem that HOL4 states as the
   value of an ML expression *)

(* HOL4 unifyScript.sml:1571-1577: a theorem that HOL4 states as the
   value of an ML expression *)

(* HOL4 unifyScript.sml:1579-1582: a theorem that HOL4 states as the
   value of an ML expression *)

let kcunifywl_def = cake_define
  `kcunifywl s k = apply_cunifk k (SOME s)`;;

(* HOL4 unifyScript.sml:1588-1591: a theorem that HOL4 states as the
   value of an ML expression *)

(* HOL4 unifyScript.sml:1593: ML code, not ported *)
cake_declare "cunify_code"
  `:(infer_t spt)#kcunifkont ->
    ((infer_t spt)#kcunifkont) + (infer_t spt)option`;;

(* PENDING: tcallify_th makes it with ML code *)
(* HOL4 unifyScript.sml:1594-1596: the definition *)

let kcunifywl_tcallish = cake_theorem "kcunifywl_tcallish"
  (fun () ->
    `!x. (\(s,k). cwfs s) x ==>
         (\(s,k). kcunifywl s k) x =
         TAILCALL cunify_code (\(s,k). kcunifywl s k) x`)
  CHEAT_TAC;;

let isvars_def = cake_define_list
  [`isvars [] = {}`;
   `isvars (t :: ts) = vars (encode_infer_t t) UNION isvars ts`];;

let FINITE_isvars = cake_theorem "FINITE_isvars[simp]"
  (fun () ->
    `FINITE (isvars ts)`)
  CHEAT_TAC;;


let cplist_vars_def = cake_define_list
  [`cplist_vars [] = {}`;
   `cplist_vars ((ts,us) :: rest) = isvars ts UNION isvars us UNION
  cplist_vars rest`];;

let FINITE_cplist_vars = cake_theorem "FINITE_cplist_vars[simp]"
  (fun () ->
    `FINITE (cplist_vars wl)`)
  CHEAT_TAC;;

let PFLAT_def = cake_define_list
  [`PFLAT [] = EMPTY_BAG`;
   `PFLAT (([],[]) :: ps) = PFLAT ps`;
   `PFLAT (([],j :: js) :: ps) =
      BAG_INSERT (encode_infer_t j) (PFLAT (([],js) :: ps))`;
   `PFLAT ((i :: is,js) :: ps) =
      BAG_INSERT (encode_infer_t i) (PFLAT ((is,js) :: ps))`];;

let FINITE_BAG_PFLAT = cake_theorem "FINITE_BAG_PFLAT[simp]"
  (fun () ->
    `!ps. FINITE_BAG (PFLAT ps)`)
  CHEAT_TAC;;

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

(* HOL4 unifyScript.sml:1659: the overload kcuR, which the port
   expands *)

let WF_kcunifywlR = cake_theorem "WF_kcunifywlR"
  (fun () ->
    `WF kcunifywlR`)
  CHEAT_TAC;;

let PFLAT_CONS2 = cake_theorem "PFLAT_CONS2[simp]"
  (fun () ->
    `PFLAT ((l1,h2 :: t2) :: rest) =
     BAG_INSERT (encode_infer_t h2) (PFLAT ((l1,t2) :: rest))`)
  CHEAT_TAC;;

let mlt_BAG_INSERT2 = cake_theorem "mlt_BAG_INSERT2"
  (fun () ->
    `FINITE_BAG b ==>
     mlt R b (BAG_INSERT x (BAG_INSERT y b))`)
  CHEAT_TAC;;

let cwfs_insert_tvar_db = cake_theorem "cwfs_insert_tvar_db"
  (fun () ->
    `~(
       v IN domain s) /\ cwfs s ==> cwfs (sptree_insert v
         (Infer_Tvar_db c) s)`)
  CHEAT_TAC;;

let tcwalk_EQ_Infer_Tuvar = cake_theorem "tcwalk_EQ_Infer_Tuvar"
  (fun () ->
    `cwfs s /\ tcwalk s t = Infer_Tuvar v ==> ~(
     v IN domain s) /\ (?u. t = Infer_Tuvar u)`)
  CHEAT_TAC;;

(* HOL4 unifyScript.sml:1814-1818: a theorem that HOL4 states as the
   value of an ML expression *)

let tcvwalk_substvars = cake_theorem "tcvwalk_substvars"
  (fun () ->
    `cwfs s /\ tcvwalk s v = t ==>
     t = Infer_Tuvar v /\ ~(v IN domain s) \/
     vars (encode_infer_t t) SUBSET substvars (encode_infer_t o_f
       sp2fm s)`)
  CHEAT_TAC;;

let tcwalk_rangevars = cake_theorem "tcwalk_rangevars"
  (fun () ->
    `cwfs s /\ tcwalk s t = u ==>
     vars (encode_infer_t u) SUBSET rangevars (encode_infer_t o_f
       sp2fm s) UNION
                              vars (encode_infer_t t)`)
  CHEAT_TAC;;

let cwfs_var2_extend = cake_theorem "cwfs_var2_extend"
  (fun () ->
    `cwfs s /\ ~(v1 = v2) /\ ~(v1 IN domain s) /\ ~(v2 IN domain s) ==>
     cwfs (sptree_insert v1 (Infer_Tuvar v2) s)`)
  CHEAT_TAC;;

let vars_encode_infer_ts = cake_theorem "vars_encode_infer_ts"
  (fun () ->
    `vars (encode_infer_ts is) = isvars is`)
  CHEAT_TAC;;

let PFLAT_NIL1 = cake_theorem "PFLAT_NIL1[simp]"
  (fun () ->
    `PFLAT (([],l2) :: rest) =
     (BAG_UNION) ((FOLDR BAG_INSERT EMPTY_BAG) (MAP
       encode_infer_t l2)) (PFLAT rest)`)
  CHEAT_TAC;;

let PFLAT_eqn = cake_theorem "PFLAT_eqn"
  (fun () ->
    `!l1 l2.
       PFLAT ((l1,l2) :: rest) =
       (BAG_UNION) ((FOLDR BAG_INSERT EMPTY_BAG) (MAP
         encode_infer_t l1))
                 ((BAG_UNION) ((FOLDR BAG_INSERT EMPTY_BAG) (MAP
                   encode_infer_t l2)) (PFLAT rest))`)
  CHEAT_TAC;;

(* HOL4 unifyScript.sml:1876-1884: a theorem whose statement the port
   cannot state yet *)

let kcunifywl_ensures_decrease =
  cake_theorem "kcunifywl_ensures_decrease"
  (fun () ->
    `!x. (\(s,k). cwfs s) x /\ cunify_code x = INL y ==> kcunifywlR y
  x`)
  CHEAT_TAC;;

let kcunifywl_preserves_precond =
  cake_theorem "kcunifywl_preserves_precond"
  (fun () ->
    `!x y. (\(s,k). cwfs s) x /\ cunify_code x = INL y ==> (\(s,k).
  cwfs s) y`)
  CHEAT_TAC;;

let kcunifywl_cleaned = cake_theorem "kcunifywl_cleaned"
  (fun () ->
    `!x. (\(s,wl). cwfs s) x ==>
         (\(s,wl). kcunifywl s wl) x = TAILREC cunify_code x`)
  CHEAT_TAC;;

let tcunify_def = cake_define
  `tcunify s wl = TAILREC cunify_code (s,wl)`;;

(* HOL4 unifyScript.sml:2007-2012: a theorem that HOL4 states as the
   value of an ML expression *)

(* HOL4 unifyScript.sml:2014-2015: a theorem that HOL4 states as the
   value of an ML expression *)

let tcunify_correct = cake_theorem "tcunify_correct"
  (fun () ->
    `cwfs s ==> cunify s t1 t2 = tcunify s [([t1],[t2])]`)
  CHEAT_TAC;;

let unify_decode_right_inverse =
  cake_theorem "decode_right_inverse[local]"
  (fun () ->
    `(!t. (?t'. t = encode_infer_t t') ==> (encode_infer_t
  (decode_infer_t t) = t)) /\
     (!ts. (?ts'. ts = encode_infer_ts ts') ==> (encode_infer_ts
       (decode_infer_ts ts) = ts))`)
  CHEAT_TAC;;

let t_wfs_def = cake_define
  `t_wfs s = wfs (encode_infer_t o_f s)`;;

let t_vwalk_def = cake_define
  `t_vwalk s v = decode_infer_t (vwalk (encode_infer_t o_f s) v)`;;

let t_vwalk_ind' = cake_theorem "t_vwalk_ind'[local]"
  (fun () ->
    `!s'. t_wfs s' ==>
      (!P.
        (!v. (!v1 u. (FLOOKUP s' v = SOME v1) /\ (v1 = Infer_Tuvar
          u) ==> P u) ==> P v) ==>
        (!v. P v))`)
  CHEAT_TAC;;

(* HOL4 unifyScript.sml:2064-2065: a theorem that HOL4 states as the
   value of an ML expression *)

let t_vwalk_eqn = cake_theorem "t_vwalk_eqn"
  (fun () ->
    `!s.
      t_wfs s ==>
      (!v.
        t_vwalk s v =
        (match FLOOKUP s v with NONE -> Infer_Tuvar v | SOME
          (Infer_Tuvar u) -> t_vwalk s u | SOME (Infer_Tapp ts tc) ->
          Infer_Tapp ts tc | SOME (Infer_Tvar_db n) -> Infer_Tvar_db
          n))`)
  CHEAT_TAC;;

let t_walk_def = cake_define
  `t_walk s t = decode_infer_t (walk (encode_infer_t o_f s)
  (encode_infer_t t))`;;

let t_walk_eqn = cake_theorem "t_walk_eqn"
  (fun () ->
    `(!s v. t_walk s (Infer_Tuvar v) = t_vwalk s v) /\
     (!s ts tc. t_walk s (Infer_Tapp ts tc) = Infer_Tapp ts tc) /\
     (!s n. t_walk s (Infer_Tvar_db n) = Infer_Tvar_db n)`)
  CHEAT_TAC;;

let t_oc_def = cake_define
  `t_oc s t v = oc (encode_infer_t o_f s) (encode_infer_t t) v`;;

(* HOL4 unifyScript.sml:2110-2141: code that the source has in a
   comment *)

let encode_vwalk = cake_theorem "encode_vwalk[local]"
  (fun () ->
    `!s. t_wfs s ==> (!u. vwalk (encode_infer_t o_f s) u =
  encode_infer_t (t_vwalk s u))`)
  CHEAT_TAC;;

let t_oc_eqn_help = cake_theorem "t_oc_eqn_help[local]"
  (fun () ->
    `!l v s.
     oc (encode_infer_t o_f' s) (encode_infer_ts l) v <=>
     EXISTS (\t. oc (encode_infer_t o_f' s) (encode_infer_t t) v)
       l`)
  CHEAT_TAC;;

let t_oc_eqn = cake_theorem "t_oc_eqn"
  (fun () ->
    `!s. t_wfs s ==>
      (!t v. t_oc s t v =
        (match t_walk s t with Infer_Tuvar u -> v = u |
          Infer_Tapp ts tc -> EXISTS (\t. t_oc s t v) ts |
          Infer_Tvar_db n -> F))`)
  CHEAT_TAC;;

let t_ext_s_check_def = cake_define
  `t_ext_s_check s v t =
     OPTION_MAP
       ((o_f) decode_infer_t)
       (ext_s_check (encode_infer_t o_f s) v (encode_infer_t t))`;;

let t_ext_s_check_eqn = cake_theorem "t_ext_s_check_eqn"
  (fun () ->
    `!s v t.
      t_ext_s_check s v t = (if t_oc s t v then NONE else SOME (s
        |+ (v,t)))`)
  CHEAT_TAC;;

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
        | (_8,_9) -> NONE`;;

let encode_walk = cake_theorem "encode_walk[local]"
  (fun () ->
    `!s. t_wfs s ==>
         (!t. walk (encode_infer_t o_f s) (encode_infer_t t) =
           encode_infer_t (t_walk s t))`)
  CHEAT_TAC;;

let encode_pair_cases = cake_theorem "encode_pair_cases[local]"
  (fun () ->
    `(!t t1 t2.
       (encode_infer_t t = term_Pair t1 t2) ==>
         ((t1 = term_Const Tapp_tag) /\
          (?tc ts. t2 = term_Pair (term_Const (TC_tag tc))
            (encode_infer_ts ts))))`)
  CHEAT_TAC;;

let encode_unify_lemma = cake_theorem "encode_unify_lemma[local]"
  (fun () ->
    `!s t1 t2 s' t1' t2'.
     (s = (encode_infer_t o_f s')) /\
     (((t1 = encode_infer_t t1') /\ (t2 = encode_infer_t t2')) \/
      (?c. (t1 = term_Const c) /\ (t2 = term_Const c) /\ (t1' =
        t2')) \/
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
      OPTION_MAP ((o_f) encode_infer_t) (t_unify s' t1' t2'))`)
  CHEAT_TAC;;

let encode_unify = cake_theorem "encode_unify[local]"
  (fun () ->
    `!s t1 t2 s' t1' t2'.
     (s = encode_infer_t o_f s') /\
     (t1 = encode_infer_t t1') /\ (t2 = encode_infer_t t2') /\
     t_wfs s' ==>
     (
      unify s t1 t2 =
      OPTION_MAP ((o_f) encode_infer_t) (t_unify s' t1' t2'))`)
  CHEAT_TAC;;

let wfs_unify = cake_theorem "wfs_unify[local]"
  (fun () ->
    `!s t1 t2 s'. wfs s /\ (unify s t1 t2 = SOME s') ==> wfs s'`)
  CHEAT_TAC;;

let ts_unify_thm = cake_theorem "ts_unify_thm[local]"
  (fun () ->
    `!s l1 l2.
       t_wfs s ==>
       (ts_unify s l1 l2 =
        OPTION_MAP
        ((o_f) decode_infer_t)
        (unify (encode_infer_t o_f s) (encode_infer_ts l1)
          (encode_infer_ts l2)))`)
  CHEAT_TAC;;

let t_unify_eqn = cake_theorem "t_unify_eqn"
  (fun () ->
    `(!t1 t2 s.
      t_wfs s ==>
      (t_unify s t1 t2 =
       (match (t_walk s t1,t_walk s t2) with
          (Infer_Tuvar v1,Infer_Tuvar v2) ->
            SOME (if v1 = v2 then s else s |+ (v1,Infer_Tuvar v2))
              | (Infer_Tuvar v1,t2) -> t_ext_s_check s v1 t2 |
              (t1,Infer_Tuvar v2) -> t_ext_s_check s v2 t1 | (Infer_Tapp
              ts1 tc1,Infer_Tapp ts2 tc2) ->
            (if tc1 = tc2 then
              ts_unify s ts1 ts2 else
              NONE) | (Infer_Tvar_db n1,Infer_Tvar_db n2) ->
            (if n1 = n2 then
              SOME s else
              NONE) | _10 -> NONE)))`)
  CHEAT_TAC;;

let t_unify_ind = cake_theorem "t_unify_ind"
  (fun () ->
    `!P0 P1.
        (!s t1 t2.
           (!ts1 ts2 tc2.
              t_walk s t1 = Infer_Tapp ts1 tc2 /\
              t_walk s t2 = Infer_Tapp ts2 tc2 ==>
              P1 s ts1 ts2) ==>
           P0 s t1 t2) /\
        (!s ts1 ts2.
           (!t1 ts1' t2 ts2' s'.
              (ts1 = t1 :: ts1' /\ ts2 = t2 :: ts2') /\
              t_unify s t1 t2 = SOME s' ==>
              P1 s' ts1' ts2') /\
           (!t1 ts1' t2 ts2'.
              ts1 = t1 :: ts1' /\ ts2 = t2 :: ts2' ==> P0 s t1 t2)
                ==>
           P1 s ts1 ts2) ==>
        (!s t1 t2. t_wfs s ==> P0 s t1 t2) /\
        (!s ts1 ts2. t_wfs s ==> P1 s ts1 ts2)`)
  CHEAT_TAC;;

let apply_subst_t_def = cake_define
  `apply_subst_t s t = decode_infer_t (subst_APPLY (encode_infer_t
  o_f s) (encode_infer_t t))`;;

let apply_subst_t_eqn = cake_theorem "apply_subst_t_eqn"
  (fun () ->
    `(!s n.
      apply_subst_t s (Infer_Tuvar n) =
       (match FLOOKUP s n with NONE -> Infer_Tuvar n | SOME t ->
         t)) /\
     (!s ts tc.
      apply_subst_t s (Infer_Tapp ts tc) =
        Infer_Tapp (MAP (apply_subst_t s) ts) tc) /\
     (!s n.
      apply_subst_t s (Infer_Tvar_db n) =
        Infer_Tvar_db n)`)
  CHEAT_TAC;;

let t_walkstar_def = cake_define
  `t_walkstar s t =
     decode_infer_t (walkstar (encode_infer_t o_f s)
       (encode_infer_t t))`;;

let t_walkstar_cwalkstar = cake_theorem "t_walkstar_cwalkstar"
  (fun () ->
    `t_walkstar s t = cwalkstar (fm2sp s) t`)
  CHEAT_TAC;;

(* HOL4 unifyScript.sml:2657-2666: a theorem whose statement the port
   cannot state yet *)

let t_walkstar_eqn = cake_theorem "t_walkstar_eqn"
  (fun () ->
    `!s. t_wfs s ==>
      (!t.
        t_walkstar s t =
        (match t_walk s t with Infer_Tuvar v -> Infer_Tuvar v |
          Infer_Tapp ts tctor -> Infer_Tapp (MAP (t_walkstar s) ts)
          tctor | Infer_Tvar_db n -> Infer_Tvar_db n))`)
  CHEAT_TAC;;

let t_walkstar_ind = cake_theorem "t_walkstar_ind"
  (fun () ->
    `!s. t_wfs s ==>
         (!P.
           (!t.
              (!ts tt a. (t_walk s t = Infer_Tapp ts tt) /\ MEM a
                ts ==> P a) ==>
              P t) ==>
           (!t. P t))`)
  CHEAT_TAC;;

let t_collapse_def = cake_define
  `t_collapse s =
     decode_infer_t o_f collapse (encode_infer_t o_f s)`;;

let t_collapse_eqn = cake_theorem "t_collapse_eqn"
  (fun () ->
    `!s. t_collapse s = FUN_FMAP (\v. t_walkstar s (Infer_Tuvar v))
  (FDOM s)`)
  CHEAT_TAC;;

let t_unify_unifier = cake_theorem "t_unify_unifier"
  (fun () ->
    `t_wfs s /\ (t_unify s t1 t2 = SOME sx) ==> t_wfs sx /\ s SUBMAP
  sx /\ (t_walkstar sx t1 = t_walkstar sx t2)`)
  CHEAT_TAC;;

let t_unify_strongind' = cake_theorem "t_unify_strongind'[local]"
  (fun () ->
    `!P0 P1.
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
             (ts1 = t1 :: ts1' /\ ts2 = t2 :: ts2') /\
             t_unify s t1 t2 = SOME s' ==>
             P1 s' ts1' ts2') /\
          (!t1 ts1' t2 ts2'.
             ts1 = t1 :: ts1' /\ ts2 = t2 :: ts2' ==> P0 s t1 t2)
               ==>
          P1 s ts1 ts2) ==>
       (!s t1 t2. t_wfs s ==> (t_wfs s ==> P0 s t1 t2)) /\
       (!s ts1 ts2. t_wfs s ==> (t_wfs s ==> P1 s ts1 ts2))`)
  CHEAT_TAC;;

(* HOL4 unifyScript.sml:2778-2779: a theorem that HOL4 states as the
   value of an ML expression *)

let encode_walkstar = cake_theorem "encode_walkstar[local]"
  (fun () ->
    `!s t.
     t_wfs s ==>
     walkstar (encode_infer_t o_f s) (encode_infer_t t) =
     encode_infer_t (t_walkstar s t)`)
  CHEAT_TAC;;

let t_walkstar_FEMPTY = cake_theorem "t_walkstar_FEMPTY"
  (fun () ->
    `!t. (t_walkstar FEMPTY' t = t)`)
  CHEAT_TAC;;

let t_wfs_SUBMAP = cake_theorem "t_wfs_SUBMAP"
  (fun () ->
    `!s1 s2. t_wfs s2 /\ s1 SUBMAP s2 ==> t_wfs s1`)
  CHEAT_TAC;;

let t_walkstar_SUBMAP = cake_theorem "t_walkstar_SUBMAP"
  (fun () ->
    `!s1 s2 t. s1 SUBMAP s2 /\ t_wfs s2 ==> (t_walkstar s2 t =
  t_walkstar s2 (t_walkstar s1 t))`)
  CHEAT_TAC;;

let t_vR_def = cake_define
  `t_vR s = vR (encode_infer_t o_f s)`;;

let t_vR_eqn = cake_theorem "t_vR_eqn"
  (fun () ->
    `!s x y. t_vR s y x = (match FLOOKUP s x with SOME t -> y IN
  t_vars t | _11 -> F)`)
  CHEAT_TAC;;

let t_wfs_eqn = cake_theorem "t_wfs_eqn"
  (fun () ->
    `!s. t_wfs s = WF (t_vR s)`)
  CHEAT_TAC;;

let t_rangevars_def = cake_define
  `t_rangevars s = rangevars (encode_infer_t o_f s)`;;

let t_rangevars_eqn = cake_theorem "t_rangevars_eqn"
  (fun () ->
    `!s. t_rangevars s = BIGUNION (IMAGE t_vars (FRANGE s))`)
  CHEAT_TAC;;

let t_vars_eqn = cake_theorem "t_vars_eqn"
  (fun () ->
    `(!x. t_vars (Infer_Tvar_db x) = {}) /\
     (!ts tc. t_vars (Infer_Tapp ts tc) = BIGUNION (set_of_list
       (MAP t_vars ts))) /\
     (!u. t_vars (Infer_Tuvar u) = {u})`)
  CHEAT_TAC;;

let t_vwalk_to_var = cake_theorem "t_vwalk_to_var"
  (fun () ->
    `t_wfs s ==> (!v u. (t_vwalk s v = Infer_Tuvar u) ==> ~(u IN FDOM
  s))`)
  CHEAT_TAC;;

let t_walkstar_vars_notin = cake_theorem "t_walkstar_vars_notin"
  (fun () ->
    `!s. t_wfs s ==>
      (!t x. x IN t_vars (t_walkstar s t) ==> ~(x IN FDOM s))`)
  CHEAT_TAC;;

let t_walkstar_vars_in = cake_theorem "t_walkstar_vars_in"
  (fun () ->
    `!s. t_wfs s ==> (!t. t_vars (t_walkstar s t) SUBSET t_vars t
  UNION BIGUNION (FRANGE (t_vars o_f s)))`)
  CHEAT_TAC;;

let t_walkstar_idempotent = cake_theorem "t_walkstar_idempotent"
  (fun () ->
    `!s. t_wfs s ==> (!t. t_walkstar s (t_walkstar s t) = t_walkstar s
  t)`)
  CHEAT_TAC;;

(* ---------- Lemmas about unification that don't need to go into the encoding ----------*)

let t_unify_apply = cake_theorem "t_unify_apply"
  (fun () ->
    `!s1 s2 t1 t2.
      t_wfs s1 /\
      (t_unify s1 t1 t2 = SOME s2) ==>
      (t_walkstar s2 t1 = t_walkstar s2 t2)`)
  CHEAT_TAC;;

let t_unify_apply2 = cake_theorem "t_unify_apply2"
  (fun () ->
    `!s1 s2 t1' t2' t1 t2.
      t_wfs s1 /\
      (t_unify s1 t1' t2' = SOME s2) /\
      (t_walkstar s1 t1 = t_walkstar s1 t2) ==>
      (t_walkstar s2 t1 = t_walkstar s2 t2)`)
  CHEAT_TAC;;

let t_unify_wfs = cake_theorem "t_unify_wfs"
  (fun () ->
    `!s1 t1 t2 s2.
      t_wfs s1 /\
      (t_unify s1 t1 t2 = SOME s2) ==>
      t_wfs s2`)
  CHEAT_TAC;;

let finite_t_rangevars = cake_theorem "finite_t_rangevars"
  (fun () ->
    `!t. FINITE (t_rangevars t)`)
  CHEAT_TAC;;

let t_walkstar_eqn1 = cake_theorem "t_walkstar_eqn1"
  (fun () ->
    `!s idx ts tc.
      t_wfs s ==>
      (t_walkstar s (Infer_Tvar_db idx) = Infer_Tvar_db idx) /\
      (t_walkstar s (Infer_Tapp ts tc) = Infer_Tapp (MAP
        (t_walkstar s) ts) tc)`)
  CHEAT_TAC;;

let oc_tvar_db = cake_theorem "oc_tvar_db"
  (fun () ->
    `!s uv tvs. t_wfs s ==> ~t_oc s (Infer_Tvar_db tvs) uv`)
  CHEAT_TAC;;

let oc_unit = cake_theorem "oc_unit"
  (fun () ->
    `!s uv tc. t_wfs s ==> ~t_oc s (Infer_Tapp [] tc) uv`)
  CHEAT_TAC;;

let no_vars_lem = cake_theorem "no_vars_lem"
  (fun () ->
    `!e l f.
      MEM e l /\ set_of_list (MAP f l) = {{}} ==>
      (f e = {})`)
  CHEAT_TAC;;

let no_vars_extend_subst_vwalk =
  cake_theorem "no_vars_extend_subst_vwalk"
  (fun () ->
    `!s. t_wfs s ==>
       (!n s'.
             t_wfs (s |++ s') /\
             DISJOINT (FDOM s) (FDOM (FEMPTY |++ s')) /\
             (!n'. ~(t_vwalk s n = Infer_Tuvar n')) ==>
             t_vwalk (s |++ s') n = t_vwalk s n)`)
  CHEAT_TAC;;

let no_vars_extend_subst = cake_theorem "no_vars_extend_subst"
  (fun () ->
    `!s. t_wfs s ==>
      (!t s'.
             t_wfs (s |++ s') /\
             DISJOINT (FDOM s) (FDOM (FEMPTY |++ s')) /\
             (t_vars (t_walkstar s t) = {}) ==>
             t_walkstar (s |++ s') t = t_walkstar s t)`)
  CHEAT_TAC;;

(*Theorems about unification for completeness proof*)

let t_walk_vwalk_id = cake_theorem "t_walk_vwalk_id"
  (fun () ->
    `t_wfs s ==>
      (!n. t_walk s (t_vwalk s n) = t_vwalk s n)`)
  CHEAT_TAC;;

let t_walk_walk_id = cake_theorem "t_walk_walk_id"
  (fun () ->
    `t_wfs s ==>
      t_walk s (t_walk s h) = t_walk s h`)
  CHEAT_TAC;;

let eqs_t_unify = cake_theorem "eqs_t_unify"
  (fun () ->
    `t_wfs s /\ t_wfs s2 /\
      t_walkstar s2 (t_walkstar s t1) = t_walkstar s2 (t_walkstar s
        t2) ==>
      (?sx. t_unify s t1 t2 = SOME sx)`)
  CHEAT_TAC;;

(* HOL4 unifyScript.sml:3129-3132: ML code, not ported *)

let t_unify_mgu = cake_theorem "t_unify_mgu"
  (fun () ->
    `!s t1 t2 sx s2.
      t_wfs s /\ (t_unify s t1 t2 = SOME sx) /\ t_wfs s2 /\
      (t_walkstar s2 (t_walkstar s t1)) = t_walkstar s2 (t_walkstar
        s t2) ==>
      (!t. t_walkstar s2 (t_walkstar sx t) = t_walkstar s2
        (t_walkstar s t))`)
  CHEAT_TAC;;

let t_walkstar_tuvar_props = cake_theorem "t_walkstar_tuvar_props"
  (fun () ->
    `t_wfs s ==>
      (~(uv IN FDOM s) <=> t_walkstar s (Infer_Tuvar uv) =
        Infer_Tuvar uv)`)
  CHEAT_TAC;;

(*t_compat theorems*)
let t_compat_def = cake_define
  `t_compat s s' <=>
   t_wfs s /\ t_wfs s' /\
   (!t. t_walkstar s' (t_walkstar s t) = t_walkstar s' t)`;;

let t_compat_refl = cake_theorem "t_compat_refl"
  (fun () ->
    `t_wfs s ==> t_compat s s`)
  CHEAT_TAC;;

let t_compat_trans = cake_theorem "t_compat_trans"
  (fun () ->
    `t_compat a b /\ t_compat b c ==> t_compat a c`)
  CHEAT_TAC;;

let SUBMAP_t_compat = cake_theorem "SUBMAP_t_compat"
  (fun () ->
    `t_wfs s' /\ s SUBMAP s' ==> t_compat s s'`)
  CHEAT_TAC;;

(*t_compat is preserved under certain types of unification
  Proof basically from HOL*)
let t_compat_eqs_t_unify = cake_theorem "t_compat_eqs_t_unify"
  (fun () ->
    `!s t1 t2 sx.
        t_compat s sx /\ (t_walkstar sx t1 = t_walkstar sx t2) ==>
        (?si. (t_unify s t1 t2 = SOME si) /\ t_compat si sx)`)
  CHEAT_TAC;;

hol4_only "++" "APPEND";;
