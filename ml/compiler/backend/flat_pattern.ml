(* ======================================================== *)
(*  flat_pattern: ported from HOL4's
    compiler/backend/flat_patternScript.sml  *)
(* ======================================================== *)

(*
  Interface between flatLang and pattern compiler.

  - ensures every case match is on a variable
  - sends case matches to pattern compiler to get a decision tree
  - decodes decision tree to if-tree
  - encodes the variable bindings of each case as let-bindings
*)

needs "compiler/backend/flatLang.ml";;
needs "compiler/backend/pattern_matching/pattern_comp.ml";;
needs "compiler/backend/pattern_matching/pattern_semantics.ml";;
needs "lib/sptree.ml";;
needs "misc/misc.ml";;


let flat_pattern_config_FIELDS = define_record "flat_pattern_config"
  ["pat_heuristic","num"];;

let init_config_def = cake_define
  `flat_pattern_init_config ph = mk_flat_pattern_config ph`;;

(* HOL4 termination: *)
let sum_string_ords_def = cake_define_wf
  `MEASURE (\(i,str). strlen str - i)`
  `sum_string_ords i str = (if i < strlen str then (ORD (strsub str
  i) - 35) + sum_string_ords (i + 1) str else 0)`;;

let dec_name_to_num_def = cake_define
  `dec_name_to_num name = (if strlen name < 2 then 0 else if strsub
  name 0 = (CHR 46) /\ strsub name 1 = (CHR 46) then sum_string_ords
  2 name else 0)`;;

let enc_num_to_name_aux_def = cake_define
  `enc_num_to_name_aux i xs = (if i < 90 then (CHR 46) :: (CHR 46) ::
  CHR (i + 35) :: xs else enc_num_to_name_aux (i - 90) (CHR 125 ::
  xs))`;;

let enc_num_to_name_def = cake_define
  `enc_num_to_name i = implode (enc_num_to_name_aux i [])`;;

(* HOL4 termination: \\ simp [flatLangTheory.pat_size_def] \\ rw
   [MAP_MAP_o, o_DEF, UNCURRY, SUM_APPEND, pat1_size] \\ simp
   [LENGTH_enumerate, MAP_enumerate_MAPi, MAPi_eq_MAP] *)
let compile_pat_bindings_def = cake_define_wf
  `MEASURE (\(t,i,m,flatLang_exp). SUM (MAP (pat_size o FST) m) +
  LENGTH m)`
  `compile_pat_bindings _1 _2 [] flatLang_exp = (LN,flatLang_exp) /\
   compile_pat_bindings t i ((flatLang_Pany,_3,_4) :: m) flatLang_exp
     =
     compile_pat_bindings t i m flatLang_exp /\
   compile_pat_bindings t i ((flatLang_Pvar s,k,x) :: m) flatLang_exp
     = (
     let (spt,exp2) = compile_pat_bindings t i m flatLang_exp in
     (sptree_insert k one spt,flatLang_Let t (SOME s) x exp2)) /\
   compile_pat_bindings t i ((flatLang_Plit _5,_6,_7) :: m)
     flatLang_exp =
     compile_pat_bindings t i m flatLang_exp /\
   compile_pat_bindings t i ((flatLang_Pcon _8 ps,k,x) :: m)
     flatLang_exp = (
     let j_nms = MAP (\(j,p). let k = i + 1 + j in
         let nm = enc_num_to_name k in
         ((j,nm),(p,k,flatLang_Var_local t nm))) (enumerate 0 ps) in
     let (spt,exp2) = compile_pat_bindings t (i + 2 + LENGTH ps)
         (MAP SND j_nms ++ m) flatLang_exp in
     let j_nms_used = FILTER (\(_9,(_10,k,_11)). IS_SOME
       (sptree_lookup k spt)) j_nms in
     let exp3 = ITLIST (\((j,nm),_12) flatLang_exp.
         flatLang_Let t (SOME nm) (flatLang_App t (flatLang_El j)
           [x]) flatLang_exp) j_nms_used exp2 in
     let spt2 = if NULL j_nms_used then spt else sptree_insert k one
       spt in
     (spt2,exp3)) /\
   compile_pat_bindings t i ((flatLang_Pas p
     semanticPrimitives_v,k,x) :: m) flatLang_exp = (
     let nm = enc_num_to_name (i + 1) in
     let (spt,exp2) = compile_pat_bindings t (i + 2)
                       ((p,i + 1,flatLang_Var_local t nm) :: m)
                         flatLang_exp in
     (sptree_insert k one spt,flatLang_Let t (SOME
       semanticPrimitives_v) x
                             (flatLang_Let t (SOME nm)
                               (flatLang_Var_local t
                               semanticPrimitives_v) exp2))) /\
   compile_pat_bindings t i ((flatLang_Pref p,k,x) :: m) flatLang_exp
     = (
     let nm = enc_num_to_name (i + 1) in
     let (spt,exp2) = compile_pat_bindings t (i + 2)
         ((p,i + 1,flatLang_Var_local t nm) :: m) flatLang_exp in
     (sptree_insert k one spt,flatLang_Let t (SOME nm)
       (flatLang_App t (flatLang_El 0) [x]) exp2))`;;

let compile_pat_rhs_def = cake_define
  `compile_pat_rhs t i semanticPrimitives_v (p,flatLang_exp) =
   SND (compile_pat_bindings t (i + 1)
     [(p,i,semanticPrimitives_v)] flatLang_exp)`;;

let decode_pos_def = cake_define
  `decode_pos t semanticPrimitives_v EmptyPos = semanticPrimitives_v /\
   decode_pos t semanticPrimitives_v (Pos i pos) = decode_pos t
     (flatLang_App t (flatLang_El i) [semanticPrimitives_v]) pos`;;

let decode_test_def = cake_define
  `flat_pattern_decode_test t (pattern_semantics_TagLenEq
  pattern_semantics_tag l) semanticPrimitives_v = flatLang_App t
  (pattern_semantics_TagLenEq pattern_semantics_tag l)
  [semanticPrimitives_v] /\
   flat_pattern_decode_test t (pattern_semantics_LitEq lit)
     semanticPrimitives_v = flatLang_App t (flatLang_Src
     ast_Equality) [semanticPrimitives_v; pattern_semantics_Lit t
     lit]`;;

let simp_guard_def = cake_define
  `simp_guard x =
      match x with
        (pattern_semantics_Conj x y) ->
     (let semanticPrimitives_v = simp_guard x in
      let w = simp_guard y in
      if semanticPrimitives_v = pattern_semantics_Not
        pattern_semantics_True \/ w = pattern_semantics_Not
        pattern_semantics_True then
        pattern_semantics_Not pattern_semantics_True else if
          semanticPrimitives_v = pattern_semantics_True then w else if w
          = pattern_semantics_True then semanticPrimitives_v else
          pattern_semantics_Conj semanticPrimitives_v w)
      | (pattern_semantics_Disj x y) ->
     (let semanticPrimitives_v = simp_guard x in
      let w = simp_guard y in
      if semanticPrimitives_v = pattern_semantics_True \/ w =
        pattern_semantics_True then
        pattern_semantics_True else if semanticPrimitives_v =
          pattern_semantics_Not pattern_semantics_True then w else if w
          = pattern_semantics_Not pattern_semantics_True then
          semanticPrimitives_v else pattern_semantics_Disj
          semanticPrimitives_v w)
      | (pattern_semantics_Not x) ->
     (let semanticPrimitives_v = simp_guard x in
      match semanticPrimitives_v with
        pattern_semantics_Not pattern_semantics_True ->
          pattern_semantics_True | pattern_semantics_Not w -> w | _13 ->
          pattern_semantics_Not semanticPrimitives_v)
      | x -> x`;;

let decode_guard_def = cake_define
  `decode_guard t semanticPrimitives_v (pattern_semantics_Not gd) =
  flatLang_App t (flatLang_Src ast_Equality) [decode_guard t
  semanticPrimitives_v gd; flatLang_Bool t F] /\
   decode_guard t semanticPrimitives_v (pattern_semantics_Conj gd1
     gd2) = SmartIf t (decode_guard t semanticPrimitives_v gd1)
     (decode_guard t semanticPrimitives_v gd2) (flatLang_Bool t F) /\
   decode_guard t semanticPrimitives_v (pattern_semantics_Disj gd1
     gd2) = SmartIf t (decode_guard t semanticPrimitives_v gd1)
     (flatLang_Bool t T)
     (decode_guard t semanticPrimitives_v gd2) /\
   decode_guard t semanticPrimitives_v pattern_semantics_True =
     flatLang_Bool t T /\
   decode_guard t semanticPrimitives_v (pattern_semantics_PosTest
     pos test) = flat_pattern_decode_test t test (decode_pos t
     semanticPrimitives_v pos)`;;

let decode_dtree_def = cake_define
  `decode_dtree t br_spt v df pattern_semantics$Fail =
      match pattern_semantics$Fail with
        (pattern_semantics_Leaf n) -> (match sptree_lookup n br_spt
          with SOME br -> br | NONE -> df)
      | pattern_semantics_Fail -> df
      | pattern_semantics_TypeFail -> flatLang_Var_local t (strlit
        "impossible-case")
      | (pattern_semantics_If guard dt1 dt2) ->
   let guard = simp_guard guard in
   let dec1 = decode_dtree t br_spt semanticPrimitives_v df dt1 in
   let dec2 = decode_dtree t br_spt semanticPrimitives_v df dt2 in
   if guard = pattern_semantics_True then dec1 else if guard =
     pattern_semantics_Not pattern_semantics_True then dec2 else
     SmartIf t (decode_guard t semanticPrimitives_v guard) dec1 dec2`;;

(* HOL4 termination: \\ rw [pat1_size] \\ fs [MEM_SPLIT, SUM_APPEND] *)
let encode_pat_def = cake_define_wf
  `MEASURE pat_size`
  `encode_pat x1 =
      match x1 with
        (flatLang_Pany) -> pattern_semantics_Any
      | (flatLang_Plit l) -> pattern_semantics_Lit l
      | (flatLang_Pvar _14) -> pattern_semantics_Any
      | (flatLang_Pcon stmp ps) -> pattern_semantics_Cons
     (match stmp with NONE -> NONE | SOME (i,NONE) -> SOME (i,NONE) |
       SOME (i,SOME (ty,ctors)) -> SOME (i,SOME ctors))
     (MAP encode_pat ps)
      | (flatLang_Pas p semanticPrimitives_v) -> encode_pat p
      | (flatLang_Pref p) -> pattern_semantics_Ref (encode_pat p)`;;

(* HOL4 termination: \\ simp [flatLangTheory.pat_size_def] \\ rw []
   \\ simp [o_DEF, MAPi_eq_MAP, SUM_APPEND, pat1_size] *)
let naive_pattern_match_def = cake_define_wf
  `MEASURE (\x. SUM (MAP (pat_size o FST) (SND x)) + LENGTH (SND x))`
  `naive_pattern_match t x2 =
      match x2 with
        [] -> flatLang_Bool t T
      | ((flatLang_Pany,_15) :: mats) -> naive_pattern_match t mats
      | ((flatLang_Pvar _16,_17) :: mats) -> naive_pattern_match t
        mats
      | ((flatLang_Plit l,semanticPrimitives_v) :: mats) -> SmartIf t
     (flatLang_App t (flatLang_Src ast_Equality)
       [semanticPrimitives_v; pattern_semantics_Lit t l])
       (naive_pattern_match t mats) (flatLang_Bool t F)
      | ((flatLang_Pcon NONE ps,semanticPrimitives_v) :: mats) ->
     naive_pattern_match t (MAPi (\i p. (p,flatLang_App t
       (flatLang_El i) [semanticPrimitives_v])) ps ++ mats)
      | ((flatLang_Pas p i,semanticPrimitives_v) :: mats) ->
     naive_pattern_match t ((p,semanticPrimitives_v) :: mats)
      | ((flatLang_Pcon (SOME stmp) ps,semanticPrimitives_v) :: mats)
        ->
     SmartIf t (flatLang_App t (pattern_semantics_TagLenEq (FST stmp)
       (LENGTH ps)) [semanticPrimitives_v])
       (naive_pattern_match t (MAPi (\i p. (p,flatLang_App t
         (flatLang_El i) [semanticPrimitives_v])) ps ++ mats))
       (flatLang_Bool t F)
      | ((flatLang_Pref p,semanticPrimitives_v) :: mats) ->
     naive_pattern_match t ((p,flatLang_App t (flatLang_El 0)
       [semanticPrimitives_v]) :: mats)`;;

let naive_pattern_matches_def = cake_define
  `naive_pattern_matches t semanticPrimitives_v [] dflt_x = dflt_x /\
   naive_pattern_matches t semanticPrimitives_v ((p,x) :: ps) dflt_x
     =
   SmartIf t (naive_pattern_match t [(p,semanticPrimitives_v)]) x
     (naive_pattern_matches t semanticPrimitives_v ps dflt_x)`;;

let compile_pats_def = cake_define
  `compile_pats (cfg:flat_pattern_config) naive t i semanticPrimitives_v
  default_x ps =
   (let branches = MAP (compile_pat_rhs t i semanticPrimitives_v) ps
     in
   if naive then
   naive_pattern_matches t semanticPrimitives_v (ZIP (MAP FST
     ps,branches)) default_x else let pats = MAPi (\j (p,_18).
     (encode_pat p,j)) ps in
   let dt = pattern_comp_comp pats in decode_dtree t (fromList
     branches) semanticPrimitives_v default_x dt)`;;

let max_dec_name_def = cake_define
  `max_dec_name [] = 0 /\
   max_dec_name (nm :: nms) = MAX (dec_name_to_num nm)
     (max_dec_name nms)`;;

let op_sets_globals_def = cake_define
  `op_sets_globals x1 =
      match x1 with
        (flatLang_GlobalVarInit n) -> T
      | _19 -> F`;;

let compile_exp_def = cake_define
  `flat_pattern_compile_exp cfg exp =
        match exp with
          (flatLang_Var_local t vid) ->
       (dec_name_to_num vid,F,flatLang_Var_local t vid)
        | (flatLang_Raise t x) ->
       let (i,sg,y) = flat_pattern_compile_exp cfg x in
       (i,sg,flatLang_Raise t y)
        | (flatLang_Handle t x ps) ->
       let (i,sgx,y) = flat_pattern_compile_exp cfg x in
       let (j,sgp,ps2) = compile_match cfg ps in
       let k = MAX i j + 2 in
       let nm = enc_num_to_name k in
       let semanticPrimitives_v = flatLang_Var_local t nm in
       let r = flatLang_Raise t semanticPrimitives_v in
       let flatLang_exp = compile_pats cfg sgp t k
         semanticPrimitives_v r ps2 in
       (k,(sgx \/ sgp),flatLang_Handle t y [(flatLang_Pvar
         nm,flatLang_exp)])
        | (flatLang_Con t ts xs) ->
       let (i,sg,ys) = flat_pattern_compile_exps cfg (REVERSE xs) in
       (i,sg,flatLang_Con t ts (REVERSE ys))
        | (flatLang_Fun t vs x) ->
       let (i,sg,y) = flat_pattern_compile_exp cfg x in
       (i,sg,flatLang_Fun t vs y)
        | (flatLang_App t flatLang_op xs) ->
       let (i,sg,ys) = flat_pattern_compile_exps cfg (REVERSE xs) in
       (i,(sg \/ op_sets_globals flatLang_op),flatLang_App t
         flatLang_op (REVERSE ys))
        | (flatLang_Mat t x ps) ->
       let (i,sgx,y) = flat_pattern_compile_exp cfg x in
       let (j,sgp,ps2) = compile_match cfg ps in
       let k = MAX i j + 2 in
       let nm = enc_num_to_name k in
       let semanticPrimitives_v = flatLang_Var_local t nm in
       let r = flatLang_Raise t (flatLang_Con t (SOME
         (bind_tag,NONE)) []) in
       let flatLang_exp = compile_pats cfg sgp t k
         semanticPrimitives_v r ps2 in
       (k,(sgx \/ sgp),flatLang_Let t (SOME nm) y flatLang_exp)
        | (flatLang_Let t semanticPrimitives_v x1 x2) ->
       let (i,sg1,y1) = flat_pattern_compile_exp cfg x1 in
       let (j,sg2,y2) = flat_pattern_compile_exp cfg x2 in
       let k = (match semanticPrimitives_v with NONE -> 0 | SOME vid
         -> dec_name_to_num vid) in
       (MAX i (MAX j k),(sg1 \/ sg2),flatLang_Let t
         semanticPrimitives_v y1 y2)
        | (flatLang_Letrec t fs x) ->
       let ys = MAP (\(a,b,c). (a,b,flat_pattern_compile_exp cfg c))
         fs in
       let (i,sgx,y) = flat_pattern_compile_exp cfg x in
       let j = MAX_LIST (MAP (\(_20,_21,(j,_22,_23)). j) ys) in
       let sgfs = EXISTS (\(_24,_25,(_26,sg,_27)). sg) ys in
       let fs2 = MAP (\(a,b,(_28,_29,flatLang_exp)).
         (a,b,flatLang_exp)) ys in
       (MAX i j,(sgfs \/ sgx),flatLang_Letrec t fs2 y)
        | (pattern_semantics_If t x1 x2 x3) ->
       let (i,sg1,y1) = flat_pattern_compile_exp cfg x1 in
       let (j,sg2,y2) = flat_pattern_compile_exp cfg x2 in
       let (k,sg3,y3) = flat_pattern_compile_exp cfg x3 in
       (MAX i (MAX j k),(sg1 \/ sg2 \/ sg3),SmartIf t y1 y2 y3)
        | flatLang_exp -> (0,F,flatLang_exp)
        | [] -> (0,F,[])
        | (x :: xs) ->
       let (i,sgx,y) = flat_pattern_compile_exp cfg x in
       let (j,sgy,ys) = flat_pattern_compile_exps cfg xs in
       (MAX i j,(sgx \/ sgy),y :: ys)
        | [] -> (0,F,[])
        | ((p,x) :: ps) ->
       let (i,sgx,y) = flat_pattern_compile_exp cfg x in
       let j = max_dec_name (flatLang_pat_bindings p) in
       let (k,sgp,ps2) = compile_match cfg ps in
       (MAX i (MAX j k),(sgx \/ sgp),((p,y) :: ps2))`;;

let compile_dec_def = cake_define
  `compile_dec cfg flatLang_exp = SND (SND (flat_pattern_compile_exp
  cfg flatLang_exp))`;;
