(* ======================================================== *)
(*  flat_pattern: ported from HOL4's
    compiler/backend/flat_patternScript.sml
    A definition theory, with 20 definitions, 1 datatype and 5
    theorems.  Needed by backendProof.ml, backend_passes.ml,
    flat_patternProof.ml, source_to_flat.ml and to_data_cv.ml.  *)
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
needs "lib/sum.ml";;
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
  `sum_string_ords i str = if i < strlen str then (ORD (strsub str i) - 35) +
  sum_string_ords (i + 1) str
     else 0`;;

let dec_name_to_num_def = new_definition
  `dec_name_to_num name = if strlen name < 2 then 0
     else if strsub name 0 = (CHR 46) /\ strsub name 1 = (CHR 46) then
       sum_string_ords 2 name else 0`;;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let enc_num_to_name_aux_def,enc_num_to_name_aux_ind = define_wf
  `MEASURE (\(x0,x1). (\n. n) x0)`
  `enc_num_to_name_aux i xs = if i < 90 then CONS (CHR 46) (CONS (CHR 46) (CONS
  (CHR (i + 35)) xs))
     else enc_num_to_name_aux (i - 90) (CONS (CHR 125) xs)`;;

let enc_num_to_name_def = new_definition
  `enc_num_to_name i = implode (enc_num_to_name_aux i [])`;;

make_size "flat_pat";;
let pat1_size = prove
 (`list_size flat_pat_size xs = LENGTH xs + SUM (MAP flat_pat_size xs)`,
  CHEAT_TAC);;

let MAPi_eq_MAP = prove
 (`MAPi (\n x. f x) xs = MAP f xs`,
  CHEAT_TAC);;

let compile_pat_bindings_def,compile_pat_bindings_ind = assume_definition_rec
  "termination (CHEAT_TAC)"
  `(compile_pat_bindings _ _ [] exp = (LN,exp)) /\
   (compile_pat_bindings t i (CONS (flat_Pany,_,_) m) exp =
      compile_pat_bindings t i m exp) /\
   (compile_pat_bindings t i (CONS (flat_Pvar s,k,x) m) exp = (
      let (spt,exp2) = compile_pat_bindings t i m exp in
      (sptree_insert k one spt,flat_Let t (SOME s) x exp2))) /\
   (compile_pat_bindings t i (CONS (flat_Plit _,_,_) m) exp =
      compile_pat_bindings t i m exp) /\
   (compile_pat_bindings t i (CONS (flat_Pcon _ ps,k,x) m) exp = (
      let j_nms = MAP (\(j,p). let k = i + 1 + j in
          let nm = enc_num_to_name k in
          ((j,nm),(p,k,flat_Var_local t nm))) (enumerate 0 ps) in
      let (spt,exp2) = compile_pat_bindings t (i + 2 + LENGTH ps)
          (APPEND (MAP SND j_nms) m) exp in
      let j_nms_used = FILTER (\(_,(_,k,_)). IS_SOME (sptree_lookup k spt))
          j_nms in
      let exp3 = ITLIST (\((j,nm),_) exp.
          flat_Let t (SOME nm) (flat_App t (flat_El j) [x]) exp) j_nms_used
              exp2 in
      let spt2 = (if NULL j_nms_used then spt else sptree_insert k one spt)
          in
      (spt2,exp3))) /\
   (compile_pat_bindings t i (CONS (flat_Pas p v,k,x) m) exp = (
      let nm = enc_num_to_name (i + 1) in
      let (spt,exp2) = compile_pat_bindings t (i + 2)
                        (CONS (p,i + 1,flat_Var_local t nm) m) exp in
      (sptree_insert k one spt,flat_Let t (SOME v) x
                              (flat_Let t (SOME nm) (flat_Var_local t
                                  v) exp2)))) /\
   (compile_pat_bindings t i (CONS (flat_Pref p,k,x) m) exp = (
      let nm = enc_num_to_name (i + 1) in
      let (spt,exp2) = compile_pat_bindings t (i + 2)
          (CONS (p,i + 1,flat_Var_local t nm) m) exp in
      (sptree_insert k one spt,flat_Let t (SOME nm) (flat_App t
          (flat_El 0) [x]) exp2)))`;;

let compile_pat_rhs_def = new_definition
  `compile_pat_rhs t i v (p,exp) =
   SND (compile_pat_bindings t (i + 1) [(p,i,v)] exp)`;;

let decode_pos_def,decode_pos_ind = define_rec
  `(decode_pos t v EmptyPos = v) /\
   (decode_pos t v (Pos i pos) = decode_pos t (flat_App t (flat_El i) [v])
    pos)`;;

let decode_test_def = define_cases
  `(flat_pattern_decode_test t (pattern_semantics_TagLenEq tag l) v =
    flat_App t (flat_TagLenEq tag l) [v]) /\
   (flat_pattern_decode_test t (pattern_semantics_LitEq lit) v = flat_App
    t (flat_Src ast_Equality) [v; flat_Lit t lit])`;;

let simp_guard_def,simp_guard_ind = define_shaped_rec
  "match"
  `simp_guard x =
   match x with
     pattern_semantics_Conj x y ->
     (let v = simp_guard x in
      let w = simp_guard y in
      if v = pattern_semantics_Not pattern_semantics_True \/ w =
        pattern_semantics_Not pattern_semantics_True then
        pattern_semantics_Not pattern_semantics_True
      else if v = pattern_semantics_True then w
      else if w = pattern_semantics_True then v
      else pattern_semantics_Conj v w)
   | pattern_semantics_Disj x y ->
     (let v = simp_guard x in
      let w = simp_guard y in
      if v = pattern_semantics_True \/ w = pattern_semantics_True then
        pattern_semantics_True
      else if v = pattern_semantics_Not pattern_semantics_True then w
      else if w = pattern_semantics_Not pattern_semantics_True then v
      else pattern_semantics_Disj v w)
   | pattern_semantics_Not x ->
     (let v = simp_guard x in
      match v with
        pattern_semantics_Not pattern_semantics_True ->
          pattern_semantics_True
      | pattern_semantics_Not w -> w
      | _ -> pattern_semantics_Not v)
   | x -> x`;;

let decode_guard_def,decode_guard_ind = define_rec
  `(decode_guard t v (pattern_semantics_Not gd) = flat_App t (flat_Src
    ast_Equality) [decode_guard t v gd; flat_Bool t F]) /\
   (decode_guard t v (pattern_semantics_Conj gd1 gd2) = SmartIf t (decode_guard
    t v gd1)
      (decode_guard t v gd2) (flat_Bool t F)) /\
   (decode_guard t v (pattern_semantics_Disj gd1 gd2) = SmartIf t (decode_guard
    t v gd1) (flat_Bool t T)
      (decode_guard t v gd2)) /\
   (decode_guard t v pattern_semantics_True = flat_Bool t T) /\
   (decode_guard t v (pattern_semantics_PosTest pos test) =
    flat_pattern_decode_test t test (decode_pos t v pos))`;;

let decode_dtree_def,decode_dtree_ind = define_shaped_rec
  "match"
  `decode_dtree t br_spt v df x5 =
   match x5 with
     pattern_semantics_Leaf n -> (match sptree_lookup n br_spt with SOME br
       -> br | NONE -> df)
   | pattern_semantics_Fail -> df
   | pattern_semantics_TypeFail -> flat_Var_local t (implode
     "impossible-case")
   | pattern_semantics_If guard dt1 dt2 ->
   let guard = simp_guard guard in
   let dec1 = decode_dtree t br_spt v df dt1 in
   let dec2 = decode_dtree t br_spt v df dt2 in
   if guard = pattern_semantics_True then dec1
   else if guard = pattern_semantics_Not pattern_semantics_True then dec2
   else SmartIf t (decode_guard t v guard) dec1 dec2`;;

(* the termination relation that HOL4 gives is
     MEASURE flat_pat_size
   which is not one that HOL Light takes here; the one
   below is what the port found for it *)
(* HOL4 flat_patternScript.sml:173-177: the tactic that proves the
   termination *)
let encode_pat_def,encode_pat_ind = define_wf
  `MEASURE (\x0. flat_pat_size x0)`
  `encode_pat x1 =
   match x1 with
     flat_Pany -> pattern_semantics_Any
   | flat_Plit l -> pattern_semantics_Lit l
   | flat_Pvar _ -> pattern_semantics_Any
   | flat_Pcon stmp ps -> pattern_semantics_Cons
     (match stmp with NONE -> NONE | SOME (i,NONE) -> SOME (i,NONE)
         | SOME (i,SOME (ty,ctors)) -> SOME (i,SOME ctors))
     (MAP encode_pat ps)
   | flat_Pas p v -> encode_pat p
   | flat_Pref p -> pattern_semantics_Ref (encode_pat p)`;;

(* the termination relation that HOL4 gives is
     MEASURE (\x. SUM (MAP (flat_pat_size o FST) (SND x)) + LENGTH (SND x))
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 flat_patternScript.sml:197-202: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let naive_pattern_match_def,naive_pattern_match_ind = define_guess_cheat
  `naive_pattern_match t x2 =
   match x2 with
     [] -> flat_Bool t T
   | CONS (flat_Pany,_) mats -> naive_pattern_match t mats
   | CONS (flat_Pvar _,_) mats -> naive_pattern_match t mats
   | CONS (flat_Plit l,v) mats -> SmartIf t
     (flat_App t (flat_Src ast_Equality) [v; flat_Lit t l])
       (naive_pattern_match t mats) (flat_Bool t F)
   | CONS (flat_Pcon NONE ps,v) mats ->
     naive_pattern_match t (APPEND (MAPi (\i p. (p,flat_App t (flat_El i)
       [v])) ps) mats)
   | CONS (flat_Pas p i,v) mats ->
     naive_pattern_match t (CONS (p,v) mats)
   | CONS (flat_Pcon (SOME stmp) ps,v) mats ->
     SmartIf t (flat_App t (flat_TagLenEq (FST stmp) (LENGTH ps)) [v])
       (naive_pattern_match t (APPEND (MAPi (\i p. (p,flat_App t (flat_El i)
         [v])) ps) mats))
       (flat_Bool t F)
   | CONS (flat_Pref p,v) mats ->
     naive_pattern_match t (CONS (p,flat_App t (flat_El 0) [v]) mats)`;;

let naive_pattern_matches_def,naive_pattern_matches_ind = define_rec
  `(naive_pattern_matches t v [] dflt_x = dflt_x) /\
   (naive_pattern_matches t v (CONS (p,x) ps) dflt_x =
    SmartIf t (naive_pattern_match t [(p,v)]) x (naive_pattern_matches
        t v ps dflt_x))`;;

let compile_pats_def = new_definition
  `compile_pats (cfg:flat_pattern_config) naive t i v default_x ps =
   let branches = MAP (compile_pat_rhs t i v) ps in
   if naive then
   naive_pattern_matches t v (ZIP (MAP FST ps) branches) default_x
   else let pats = MAPi (\j (p,_). (encode_pat p,j)) ps in
   let dt = pattern_comp_comp
         // cfg.pat_heuristic
         pats in decode_dtree t (sptree_fromList branches) v default_x dt`;;

let max_dec_name_def,max_dec_name_ind = define_rec
  `(max_dec_name [] = 0) /\
   (max_dec_name (CONS nm nms) = MAX (dec_name_to_num nm) (max_dec_name
    nms))`;;

let op_sets_globals_def = new_definition
  `op_sets_globals x1 =
   match x1 with
     flat_GlobalVarInit n -> T
   | _ -> F`;;

let op_sets_globals_EX = prove
 (`op_sets_globals op = (?n. op = flat_GlobalVarInit n)`,
  CHEAT_TAC);;

(* the clauses in two quotations: fs is ((varN # varN # exp) list) and
   (_#_#_)list; ps is ((pat # exp) list), (_)list and (_#_)list; t is tra and
   varN; xs is (exp list) and (_)list, which one quotation cannot typecheck
   *)
let flat_pattern_compile_exp_def,flat_pattern_compile_exp_ind =
  assume_definition_rec_clauses
  "termination (CHEAT_TAC)"
  [`(flat_pattern_compile_exp cfg (flat_Var_local t vid) =
        (dec_name_to_num vid,F,flat_Var_local t vid)) /\
    (flat_pattern_compile_exp cfg (flat_Raise t x) =
        let (i,sg,y) = flat_pattern_compile_exp cfg x in
        (i,sg,flat_Raise t y)) /\
    (flat_pattern_compile_exp cfg (flat_Handle t x ps) =
        let (i,sgx,y) = flat_pattern_compile_exp cfg x in
        let (j,sgp,ps2) = compile_match cfg ps in
        let k = MAX i j + 2 in
        let nm = enc_num_to_name k in
        let v = flat_Var_local t nm in
        let r = flat_Raise t v in
        let exp = compile_pats cfg sgp t k v r ps2 in
        (k,(sgx \/ sgp),flat_Handle t y [(flat_Pvar nm,exp)])) /\
    (flat_pattern_compile_exp cfg (flat_Con t ts xs) =
        let (i,sg,ys) = flat_pattern_compile_exps cfg (REVERSE xs) in
        (i,sg,flat_Con t ts (REVERSE ys))) /\
    (flat_pattern_compile_exp cfg (flat_App t op xs) =
        let (i,sg,ys) = flat_pattern_compile_exps cfg (REVERSE xs) in
        (i,(sg \/ op_sets_globals op),flat_App t op (REVERSE ys))) /\
    (flat_pattern_compile_exp cfg (flat_Mat t x ps) =
        let (i,sgx,y) = flat_pattern_compile_exp cfg x in
        let (j,sgp,ps2) = compile_match cfg ps in
        let k = MAX i j + 2 in
        let nm = enc_num_to_name k in
        let v = flat_Var_local t nm in
        let r = flat_Raise t (flat_Con t (SOME (bind_tag,NONE)) []) in
        let exp = compile_pats cfg sgp t k v r ps2 in
        (k,(sgx \/ sgp),flat_Let t (SOME nm) y exp)) /\
    (flat_pattern_compile_exp cfg (flat_Let t v x1 x2) =
        let (i,sg1,y1) = flat_pattern_compile_exp cfg x1 in
        let (j,sg2,y2) = flat_pattern_compile_exp cfg x2 in
        let k = (match v with NONE -> 0 | SOME vid -> dec_name_to_num vid)
            in
        (MAX i (MAX j k),(sg1 \/ sg2),flat_Let t v y1 y2)) /\
    (flat_pattern_compile_exp cfg (flat_If t x1 x2 x3) =
        let (i,sg1,y1) = flat_pattern_compile_exp cfg x1 in
        let (j,sg2,y2) = flat_pattern_compile_exp cfg x2 in
        let (k,sg3,y3) = flat_pattern_compile_exp cfg x3 in
        (MAX i (MAX j k),(sg1 \/ sg2 \/ sg3),SmartIf t y1 y2 y3)) /\
    (flat_pattern_compile_exp cfg exp = (0,F,exp)) /\
    (flat_pattern_compile_exps cfg [] = (0,F,[])) /\
    (compile_match cfg [] = (0,F,[])) /\
    (compile_match cfg (CONS (p,x) ps) =
        let (i,sgx,y) = flat_pattern_compile_exp cfg x in
        let j = max_dec_name (flat_pat_bindings p) in
        let (k,sgp,ps2) = compile_match cfg ps in
        (MAX i (MAX j k),(sgx \/ sgp),(CONS (p,y) ps2)))`;
   `(flat_pattern_compile_exp cfg (flat_Fun t vs x) =
        let (i,sg,y) = flat_pattern_compile_exp cfg x in
        (i,sg,flat_Fun t vs y)) /\
    (flat_pattern_compile_exp cfg (flat_Letrec t fs x) =
        let ys = MAP (\(a,b,c). (a,b,flat_pattern_compile_exp cfg c)) fs in
        let (i,sgx,y) = flat_pattern_compile_exp cfg x in
        let j = MAX_LIST (MAP (\(_,_,(j,_,_)). j) ys) in
        let sgfs = EX (\(_,_,(_,sg,_)). sg) ys in
        let fs2 = MAP (\(a,b,(_,_,exp)). (a,b,exp)) ys in
        (MAX i j,(sgfs \/ sgx),flat_Letrec t fs2 y)) /\
    (flat_pattern_compile_exps cfg (CONS x xs) =
        let (i,sgx,y) = flat_pattern_compile_exp cfg x in
        let (j,sgy,ys) = flat_pattern_compile_exps cfg xs in
        (MAX i j,(sgx \/ sgy),CONS y ys))`];;

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
  CHEAT_TAC);;

let compile_dec_def = new_definition
  `compile_dec cfg exp = SND (SND (flat_pattern_compile_exp cfg exp))`;;

(* and the interface *)
let _ = unhide_overloads ();;
