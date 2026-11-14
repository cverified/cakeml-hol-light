(* ======================================================== *)
(*  flat_pattern: ported from HOL4's
    compiler/backend/flat_patternScript.sml
    A definition theory, with 20 definitions, 1 datatype and 5
    theorems.  Needed by backendProof.ml, backend_passes.ml,
    flat_patternProof.ml and source_to_flat.ml.  *)
(* ======================================================== *)

(*
  Interface between flatLang and pattern compiler.

  - ensures every case match is on a variable
  - sends case matches to pattern compiler to get a decision tree
  - decodes decision tree to if-tree
  - encodes the variable bindings of each case as let-bindings
*)

needs "basis/pure/mlstring.ml";;
needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/flatLang.ml";;
needs "compiler/backend/pattern_matching/pattern_common.ml";;
needs "compiler/backend/pattern_matching/pattern_comp.ml";;
needs "compiler/backend/pattern_matching/pattern_semantics.ml";;
needs "lib/indexedLists.ml";;
needs "lib/sptree.ml";;
needs "misc/misc.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "flat_pattern"
  ["flatLang"; "misc"; "pattern_comp"; "pattern_semantics"];;


let flat_pattern_config_FIELDS = define_record "flat_pattern_config"
  ["pat_heuristic","num"
   (* pattern_matching$branch list *)
   (* unit -> *)
  ];;

let init_config_def = new_definition
  `flat_pattern_init_config ph = mk_flat_pattern_config ph`;;

(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
let sum_string_ords_def,sum_string_ords_ind = define_wf
  `MEASURE (\(i,str). strlen str - i)`
  [`sum_string_ords i str = (if i < strlen str then (ORD (strsub str
  i) - 35) + sum_string_ords (i + 1) str else 0)`];;

let dec_name_to_num_def = new_definition
  `dec_name_to_num name = (if strlen name < 2 then 0 else if strsub
  name 0 = (CHR 46) /\ strsub name 1 = (CHR 46) then sum_string_ords
  2 name else 0)`;;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let enc_num_to_name_aux_def,enc_num_to_name_aux_ind = define_wf
  `MEASURE (\(x0,x1). (\n. n) x0)`
  [`enc_num_to_name_aux i xs = (if i < 90 then CONS (CHR 46) (CONS
  (CHR 46) (CONS (CHR (i + 35)) xs)) else enc_num_to_name_aux (i -
  90) (CONS (CHR 125) xs))`];;

let enc_num_to_name_def = new_definition
  `enc_num_to_name i = implode (enc_num_to_name_aux i [])`;;

(* HOL4 flat_patternScript.sml:48-52: a theorem whose statement the
   port cannot state yet: pat1_size *)

let MAPi_eq_MAP = prove
 (`MAPi (\n x. f x) xs = MAP f xs`,
  CHEAT_TAC);;

let compile_pat_bindings_def,compile_pat_bindings_ind =
  assume_definition_rec
  "termination (CHEAT_TAC)"
  [`compile_pat_bindings _1 _2 [] exp = (LN,exp)`;
   `compile_pat_bindings t i (CONS ((flatLang_Pany:flatLang_pat),_3,_4)
    m) exp =
      compile_pat_bindings t i m exp`;
   `compile_pat_bindings t i (CONS ((flatLang_Pvar s:flatLang_pat),k,x)
    m) exp = (
      let (spt,exp2) = compile_pat_bindings t i m exp in
      (sptree_insert k one spt,flatLang_Let t (SOME s) x exp2))`;
   `compile_pat_bindings t i (CONS ((flatLang_Plit
    _6:flatLang_pat),_7,_8) m) exp =
      compile_pat_bindings t i m exp`;
   `compile_pat_bindings t i (CONS ((flatLang_Pcon _36
    ps:flatLang_pat),k,x) m) exp = (
      let j_nms = MAP (\(j,p). let k = i + 1 + j in
          let nm = enc_num_to_name k in
          ((j,nm),(p,k,flatLang_Var_local t nm))) (enumerate 0 ps)
              in
      let (spt,exp2) = compile_pat_bindings t (i + 2 + LENGTH ps)
          (APPEND (MAP SND j_nms) m) exp in
      let j_nms_used = FILTER (\(_37,(_38,k,_39)). IS_SOME
          (sptree_lookup k spt)) j_nms in
      let exp3 = ITLIST (\((j,nm),_40) exp.
          flatLang_Let t (SOME nm) (flatLang_App t (flatLang_El j)
              [x]) exp) j_nms_used exp2 in
      let spt2 = (if NULL j_nms_used then spt else sptree_insert k
          one spt) in
      (spt2,exp3))`;
   `compile_pat_bindings t i (CONS ((flatLang_Pas p v:flatLang_pat),k,x)
    m) exp = (
      let nm = enc_num_to_name (i + 1) in
      let (spt,exp2) = compile_pat_bindings t (i + 2)
                        (CONS (p,i + 1,flatLang_Var_local t nm) m)
                            exp in
      (sptree_insert k one spt,flatLang_Let t (SOME v) x
                              (flatLang_Let t (SOME nm)
                                  (flatLang_Var_local t v) exp2)))`;
   `compile_pat_bindings t i (CONS ((flatLang_Pref p:flatLang_pat),k,x)
    m) exp = (
      let nm = enc_num_to_name (i + 1) in
      let (spt,exp2) = compile_pat_bindings t (i + 2)
          (CONS (p,i + 1,flatLang_Var_local t nm) m) exp in
      (sptree_insert k one spt,flatLang_Let t (SOME nm)
          (flatLang_App t (flatLang_El 0) [x]) exp2))`];;

let compile_pat_rhs_def = new_definition
  `compile_pat_rhs t i v (p,exp) =
   SND (compile_pat_bindings t (i + 1) [(p,i,v)] exp)`;;

let decode_pos_def,decode_pos_ind = define_rec
  [`decode_pos t v EmptyPos = v`;
   `decode_pos t v (Pos i pos) = decode_pos t (flatLang_App t
    (flatLang_El i) [v]) pos`];;

let decode_test_def = define_cases
  [`flat_pattern_decode_test t (pattern_semantics_TagLenEq tag
    l:dTest) v = flatLang_App t (flatLang_TagLenEq tag l) [v]`;
   `flat_pattern_decode_test t (pattern_semantics_LitEq lit) v =
    flatLang_App t (flatLang_Src ast_Equality) [v; flatLang_Lit t
    lit]`];;

let simp_guard_def,simp_guard_ind = define_shaped_rec
  "match"
  [`simp_guard x =
      match x with
        pattern_semantics_Conj x y ->
     (let v = simp_guard x in
      let w = simp_guard y in
      if v = pattern_semantics_Not pattern_semantics_True \/ w =
        pattern_semantics_Not pattern_semantics_True then
        pattern_semantics_Not pattern_semantics_True else if v =
          pattern_semantics_True then w else if w =
          pattern_semantics_True then v else pattern_semantics_Conj v
          w)
      | (pattern_semantics_Disj x y) ->
     (let v = simp_guard x in
      let w = simp_guard y in
      if v = pattern_semantics_True \/ w = pattern_semantics_True
        then
        pattern_semantics_True else if v = pattern_semantics_Not
          pattern_semantics_True then w else if w =
          pattern_semantics_Not pattern_semantics_True then v else
          pattern_semantics_Disj v w)
      | (pattern_semantics_Not x) ->
     (let v = simp_guard x in
      match v with
        pattern_semantics_Not pattern_semantics_True ->
          pattern_semantics_True | pattern_semantics_Not w -> w | _41
          -> pattern_semantics_Not v)
      | x -> x`];;

let decode_guard_def,decode_guard_ind = define_rec
  [`decode_guard t v (pattern_semantics_Not gd:dGuard) = flatLang_App
    t (flatLang_Src ast_Equality) [decode_guard t v gd; flatLang_Bool
    t F]`;
   `decode_guard t v (pattern_semantics_Conj gd1 gd2) = SmartIf t
    (decode_guard t v gd1)
      (decode_guard t v gd2) (flatLang_Bool t F)`;
   `decode_guard t v (pattern_semantics_Disj gd1 gd2) = SmartIf t
    (decode_guard t v gd1) (flatLang_Bool t T)
      (decode_guard t v gd2)`;
   `decode_guard t v pattern_semantics_True = flatLang_Bool t T`;
   `decode_guard t v (pattern_semantics_PosTest pos test) =
    flat_pattern_decode_test t test (decode_pos t v pos)`];;

let decode_dtree_def,decode_dtree_ind = define_shaped_rec
  "match"
  [`decode_dtree t br_spt v df x5 =
      match x5 with
        (pattern_semantics_Leaf n:dTree) -> (match sptree_lookup n
          br_spt with SOME br -> br | NONE -> df)
      | pattern_semantics_Fail -> df
      | pattern_semantics_TypeFail -> flatLang_Var_local t (implode
        "impossible-case")
      | (pattern_semantics_If guard' dt1 dt2) ->
   (let guard' = simp_guard guard' in
   let dec1 = decode_dtree t br_spt v df dt1 in
   let dec2 = decode_dtree t br_spt v df dt2 in
   if guard' = pattern_semantics_True then dec1 else if guard' =
     pattern_semantics_Not pattern_semantics_True then dec2 else
     SmartIf t (decode_guard t v guard') dec1 dec2)`];;

let _ = size_thms "flatLang_pat";;
(* the termination relation that HOL4 gives is
     MEASURE pattern_semantics_pat_size
   which is not one that HOL Light takes here; the one
   below is what the port found for it *)
(* HOL4 flat_patternScript.sml:173-177: the tactic that proves the
   termination *)
let encode_pat_def,encode_pat_ind = define_wf
  `MEASURE (\x0. flatLang_pat_size x0)`
  [`encode_pat x1 =
      match x1 with
        flatLang_Pany -> pattern_semantics_Any
      | (flatLang_Plit l) -> pattern_semantics_Lit l
      | (flatLang_Pvar _42) -> pattern_semantics_Any
      | (flatLang_Pcon stmp ps) -> pattern_semantics_Cons
     (match stmp with NONE -> NONE | SOME (i,NONE) -> SOME (i,NONE)
       | SOME (i,SOME (ty,ctors)) -> SOME (i,SOME ctors))
     (MAP encode_pat ps)
      | (flatLang_Pas p v) -> encode_pat p
      | (flatLang_Pref p) -> pattern_semantics_Ref (encode_pat
        p)`];;

(* the termination relation that HOL4 gives is
     MEASURE (\x. SUM (MAP (pattern_semantics_pat_size o FST) (SND x)) +
       LENGTH (SND x))
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 flat_patternScript.sml:197-202: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let naive_pattern_match_def,naive_pattern_match_ind = define_guess_cheat
  [`naive_pattern_match t x2 =
      match x2 with
        [] -> flatLang_Bool t T
      | CONS (flatLang_Pany,_43) mats -> naive_pattern_match t mats
      | (CONS (flatLang_Pvar _44,_45) mats) -> naive_pattern_match t
        mats
      | (CONS (flatLang_Plit l,v) mats) -> SmartIf t
     (flatLang_App t (flatLang_Src ast_Equality) [v; flatLang_Lit t
       l]) (naive_pattern_match t mats) (flatLang_Bool t F)
      | (CONS (flatLang_Pcon NONE ps,v) mats) ->
     naive_pattern_match t (APPEND (MAPi (\i p. (p,flatLang_App t
       (flatLang_El i) [v])) ps) mats)
      | (CONS (flatLang_Pas p i,v) mats) ->
     naive_pattern_match t (CONS (p,v) mats)
      | (CONS (flatLang_Pcon (SOME stmp) ps,v) mats) ->
     SmartIf t (flatLang_App t (flatLang_TagLenEq (FST stmp) (LENGTH
       ps)) [v])
       (naive_pattern_match t (APPEND (MAPi (\i p. (p,flatLang_App t
         (flatLang_El i) [v])) ps) mats))
       (flatLang_Bool t F)
      | (CONS (flatLang_Pref p,v) mats) ->
     naive_pattern_match t (CONS (p,flatLang_App t (flatLang_El
       0) [v]) mats)`];;

let naive_pattern_matches_def,naive_pattern_matches_ind = define_rec
  [`naive_pattern_matches t v [] dflt_x = dflt_x`;
   `naive_pattern_matches t v (CONS (p,x) ps) dflt_x =
    SmartIf t (naive_pattern_match t [(p,v)]) x
        (naive_pattern_matches t v ps dflt_x)`];;

let compile_pats_def = new_definition
  `compile_pats (cfg:flat_pattern_config) naive t i v default_x ps =
   (let branches = MAP (compile_pat_rhs t i v) ps in
   if naive then
   naive_pattern_matches t v (ZIP (MAP FST ps) branches) default_x
     else let pats = MAPi (\j (p,_46). (encode_pat p,j)) ps in
   let dt = pattern_comp_comp
         // cfg.pat_heuristic
         pats in decode_dtree t (sptree_fromList branches) v
           default_x dt)`;;

let max_dec_name_def,max_dec_name_ind = define_rec
  [`max_dec_name [] = 0`;
   `max_dec_name (CONS nm nms) = MAX (dec_name_to_num nm)
    (max_dec_name nms)`];;

let op_sets_globals_def = new_definition
  `op_sets_globals x1 =
      match x1 with
        flatLang_GlobalVarInit n -> T
      | _47 -> F`;;

let op_sets_globals_EX = prove
 (`op_sets_globals op = (?n. op = flatLang_GlobalVarInit n)`,
  CHEAT_TAC);;

let flat_pattern_compile_exp_def,flat_pattern_compile_exp_ind =
  assume_definition_rec
  "termination (CHEAT_TAC)"
  [`flat_pattern_compile_exp cfg (flatLang_Var_local t vid) =
        (dec_name_to_num vid,F,flatLang_Var_local t vid)`;
   `flat_pattern_compile_exp cfg (flatLang_Raise t x:flatLang_exp) =
        (let (i,sg,y) = flat_pattern_compile_exp cfg x in
        (i,sg,flatLang_Raise t y))`;
   `flat_pattern_compile_exp cfg (flatLang_Handle t x ps:flatLang_exp) =
        (let (i,sgx,y) = flat_pattern_compile_exp cfg x in
        let (j,sgp,ps2) = compile_match cfg ps in
        let k = MAX i j + 2 in
        let nm = enc_num_to_name k in
        let v = flatLang_Var_local t nm in
        let r = flatLang_Raise t v in
        let exp = compile_pats cfg sgp t k v r ps2 in
        (k,(sgx \/ sgp),flatLang_Handle t y [(flatLang_Pvar
            nm,exp)]))`;
   `flat_pattern_compile_exp cfg (flatLang_Con t ts xs:flatLang_exp) =
        (let (i,sg,ys) = flat_pattern_compile_exps cfg (REVERSE xs)
            in
        (i,sg,flatLang_Con t ts (REVERSE ys)))`;
   `flat_pattern_compile_exp cfg (flatLang_Fun t vs x:flatLang_exp) =
        (let (i,sg,y) = flat_pattern_compile_exp cfg x in
        (i,sg,flatLang_Fun t vs y))`;
   `flat_pattern_compile_exp cfg (flatLang_App t op xs:flatLang_exp) =
        (let (i,sg,ys) = flat_pattern_compile_exps cfg (REVERSE xs)
            in
        (i,(sg \/ op_sets_globals op),flatLang_App t op (REVERSE
            ys)))`;
   `flat_pattern_compile_exp cfg (flatLang_Mat t x ps:flatLang_exp) =
        (let (i,sgx,y) = flat_pattern_compile_exp cfg x in
        let (j,sgp,ps2) = compile_match cfg ps in
        let k = MAX i j + 2 in
        let nm = enc_num_to_name k in
        let v = flatLang_Var_local t nm in
        let r = flatLang_Raise t (flatLang_Con t (SOME
            (bind_tag,NONE)) []) in
        let exp = compile_pats cfg sgp t k v r ps2 in
        (k,(sgx \/ sgp),flatLang_Let t (SOME nm) y exp))`;
   `flat_pattern_compile_exp cfg (flatLang_Let t v x1 x2:flatLang_exp) =
        (let (i,sg1,y1) = flat_pattern_compile_exp cfg x1 in
        let (j,sg2,y2) = flat_pattern_compile_exp cfg x2 in
        let k = (match v with NONE -> 0 | SOME vid ->
            dec_name_to_num vid) in
        (MAX i (MAX j k),(sg1 \/ sg2),flatLang_Let t v y1 y2))`;
   `flat_pattern_compile_exp cfg (flatLang_Letrec t fs x) =
        (let ys = MAP (\(a,b,c). (a,b,flat_pattern_compile_exp cfg
            c)) fs in
        let (i,sgx,y) = flat_pattern_compile_exp cfg x in
        let j = MAX_LIST (MAP (\(_48,_49,(j,_50,_51)). j) ys) in
        let sgfs = EX (\(_52,_53,(_54,sg,_55)). sg) ys in
        let fs2 = MAP (\(a,b,(_56,_57,exp)). (a,b,exp)) ys in
        (MAX i j,(sgfs \/ sgx),flatLang_Letrec t fs2 y))`;
   `flat_pattern_compile_exp cfg (flatLang_If t x1 x2 x3:flatLang_exp) =
        (let (i,sg1,y1) = flat_pattern_compile_exp cfg x1 in
        let (j,sg2,y2) = flat_pattern_compile_exp cfg x2 in
        let (k,sg3,y3) = flat_pattern_compile_exp cfg x3 in
        (MAX i (MAX j k),(sg1 \/ sg2 \/ sg3),SmartIf t y1 y2 y3))`;
   `flat_pattern_compile_exp cfg exp = (0,F,exp)`;
   `flat_pattern_compile_exps cfg [] = (0,F,[])`;
   `flat_pattern_compile_exps cfg (CONS x xs) =
        (let (i,sgx,y) = flat_pattern_compile_exp cfg x in
        let (j,sgy,ys) = flat_pattern_compile_exps cfg xs in
        (MAX i j,(sgx \/ sgy),CONS y ys))`;
   `compile_match cfg [] = (0,F,[])`;
   `compile_match cfg (CONS (p,x) ps) =
        (let (i,sgx,y) = flat_pattern_compile_exp cfg x in
        let j = max_dec_name (flatLang_pat_bindings p) in
        let (k,sgp,ps2) = compile_match cfg ps in
        (MAX i (MAX j k),(sgx \/ sgp),(CONS (p,y) ps2)))`];;

let LENGTH_compile_exps_IMP = prove
 (`(!cfg x. let v = flat_pattern_compile_exp cfg x in T) /\
   (!cfg xs i sg ys. flat_pattern_compile_exps cfg xs = (i,sg,ys) ==>
     LENGTH ys = LENGTH xs) /\
   (!cfg ps i sg ps2. compile_match cfg ps = (i,sg,ps2) ==>
     LENGTH ps2 = LENGTH ps)`,
  CHEAT_TAC);;

let LENGTH_SND_compile_exps = prove
 (`LENGTH (SND (SND (flat_pattern_compile_exps cfg xs))) = LENGTH xs /\
   LENGTH (SND (SND (compile_match cfg ps))) = LENGTH ps`,
  (CONJ_TAC THENL
    [MATCH_MP_TAC (CONJUNCT1 (CONJUNCT2 LENGTH_compile_exps_IMP))
      THEN
     MAP_EVERY EXISTS_TAC
       [`cfg:flat_pattern_config`; `FST (flat_pattern_compile_exps
         cfg xs)`;
        `FST (SND (flat_pattern_compile_exps cfg xs))`];
     MATCH_MP_TAC (CONJUNCT2 (CONJUNCT2 LENGTH_compile_exps_IMP))
       THEN
     MAP_EVERY EXISTS_TAC
       [`cfg:flat_pattern_config`; `FST (compile_match cfg ps)`;
        `FST (SND (compile_match cfg ps))`]] THEN
   REWRITE_TAC[PAIR]));;

let compile_dec_def = new_definition
  `compile_dec cfg exp = SND (SND (flat_pattern_compile_exp cfg exp))`;;
